import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域 (优先级：环境变量 > 代码硬编码)
// =============================================================================
const UUID = ""; // 默认 UUID (建议在环境变量中设置)
const WEB_PASSWORD = "";  // 后台管理密码 (必填，否则无法进入后台)
const SUB_PASSWORD = "";  // 订阅路径密码 (可选，建议设置)
const DEFAULT_PROXY_IP = "";  // 默认优选 IP/域名
const ROOT_REDIRECT_URL = "https://www.google.com"; // 根路径重定向地址

// =============================================================================
// ⚡️ 核心逻辑区 (无状态版)
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

// 解析 ProxyIP 列表
async function parseProxyList(str) {
    if (!str) return [];
    const list = str.split(/[,\n]/).map(s => s.trim()).filter(Boolean);
    const result = [];
    for (const item of list) {
        try {
            const [address, port] = await parseIP(item);
            result.push({ address, port });
        } catch(e) {}
    }
    return result;
}

// 协议头 (保持原协议名，但在UI中不显示)
const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

// 简易环境变量获取
function getEnv(env, key, fallback) {
    return env[key] || fallback;
}

async function parseIP(p){
    p=p.toLowerCase();
    let a=p,o=443;
    if(p.includes('.tp')){
        const m=p.match(/\.tp(\d+)/);
        if(m)o=parseInt(m[1],10);
        return[a,o]
    }
    if(p.includes(']:')){
        const s=p.split(']:');
        a=s[0]+']';
        o=parseInt(s[1],10)||o
    } else if(p.includes(':')&&!p.startsWith('[')){
        const i=p.lastIndexOf(':');
        a=p.slice(0,i);
        o=parseInt(p.slice(i+1),10)||o
    }
    return[a,o]
}

class Pool{constructor(){this.b=new ArrayBuffer(16384);this.p=0;this.l=[];this.m=8}alloc(s){if(s<=4096&&s<=16384-this.p){const v=new Uint8Array(this.b,this.p,s);this.p+=s;return v}const r=this.l.pop();return r&&r.byteLength>=s?new Uint8Array(r.buffer,0,s):new Uint8Array(s)}free(b){if(b.buffer===this.b)this.p=Math.max(0,this.p-b.length);else if(this.l.length<this.m&&b.byteLength>=1024)this.l.push(b)}reset(){this.p=0;this.l=[]}}

async function getDynamicUUID(key, refresh = 86400) {
    const time = Math.floor(Date.now() / 1000 / refresh);
    const msg = new TextEncoder().encode(`${key}-${time}`);
    const hash = await crypto.subtle.digest('SHA-256', msg);
    const b = new Uint8Array(hash);
    return [...b.slice(0, 16)].map(n => n.toString(16).padStart(2, '0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/, '$1-$2-$3-$4-$5');
}

const handle = (ws, pc, uuid, proxyIPList = []) => {
  const pool = new Pool();
  let s, w, r, inf, fst = true, rx = 0, stl = 0, cnt = 0, lact = Date.now(), con = false, rd = false, wt = false, tm = {}, pd = [], pb = 0, scr = 1.0, lck = Date.now(), lrx = 0, md = 'buf', asz = 0, tp = [], st = { t: 0, c: 0, ts: Date.now() };
  const upd = sz => {
    st.t += sz; st.c++;
    asz = asz * 0.9 + sz * 0.1; const n = Date.now();
    if (n - st.ts > 1000) { const rt = st.t; tp.push(rt); if (tp.length > 5) tp.shift(); st.t = 0;
    st.ts = n; const av = tp.reduce((a, b) => a + b, 0) / tp.length;
    if (st.c >= 20) { if (av > 2e7 && asz > 16384) md = 'dir';
    else if (av < 1e7 || asz < 8192) md = 'buf'; else md = 'adp' } }
  };
  const rdL = async () => {
    if (rd) return; rd = true;
    let b = [], bz = 0, tm = null;
    const fl = () => { if (!bz) return;
    const m = new Uint8Array(bz); let p = 0; for (const x of b) { m.set(x, p);
    p += x.length } if (ws.readyState === 1) ws.send(m); b = []; bz = 0; if (tm) clearTimeout(tm);
    tm = null };
    try { while (1) { if (pb > MAX_PENDING) { await new Promise(r => setTimeout(r, 100));
    continue } const { done, value: v } = await r.read(); if (v?.length) { rx += v.length; lact = Date.now();
    stl = 0; upd(v.length); const n = Date.now(); if (n - lck > 5000) { const el = n - lck, by = rx - lrx, r = by / el;
    if (r > 500) scr = Math.min(1, scr + 0.05);
    else if (r < 50) scr = Math.max(0.1, scr - 0.05); lck = n;
    lrx = rx } if (md === 'buf') { if (v.length < 32768) { b.push(v); bz += v.length;
    if (bz >= 131072) fl(); else if (!tm) tm = setTimeout(fl, asz > 16384 ? 5 : 20) } else { fl();
    if (ws.readyState === 1) ws.send(v) } } else { fl();
    if (ws.readyState === 1) ws.send(v) } } if (done) { fl(); rd = false; rcn();
    break } } } catch { fl(); rd = false; rcn() }
  };
  const wtL = async () => { if (wt) return; wt = true;
  try { while (wt) { if (!w) { await new Promise(r => setTimeout(r, 100));
  continue } if (!pd.length) { await new Promise(r => setTimeout(r, 20)); continue } const b = pd.shift(); await w.write(b);
  pb -= b.length; pool.free(b) } } catch { wt = false } };
  const est = async () => { try { s = await cn(); w = s.writable.getWriter(); r = s.readable.getReader();
  con = false; cnt = 0; scr = Math.min(1, scr + 0.15); lact = Date.now(); rdL();
  wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2); rcn() } };
  
  // 连接逻辑
  const cn = async () => {
    try {
        const direct = connect({ hostname: inf.host, port: inf.port });
        await direct.opened;
        return direct;
    } catch (e) {}

    if (pc && pc.address) {
        try {
            const specific = connect({ hostname: pc.address, port: pc.port });
            await specific.opened;
            return specific;
        } catch (e) {}
    }

    if (proxyIPList && proxyIPList.length > 0) {
        for (const proxy of proxyIPList) {
            try {
                const socket = connect({ hostname: proxy.address, port: proxy.port });
                await socket.opened;
                return socket;
            } catch (e) {
                continue;
            }
        }
    }
    throw new Error('All connection attempts failed');
 };
  const rcn = async () => { if (!inf || ws.readyState !== 1) { cln(); ws.close(1011);
  return } if (cnt >= MAX_RECONN) { cln(); ws.close(1011); return } if (con) return; cnt++;
  let d = Math.min(50 * Math.pow(1.5, cnt - 1), 3000) * (1.5 - scr * 0.5); d = Math.max(50, Math.floor(d));
  try { csk(); if (pb > MAX_PENDING * 2) while (pb > MAX_PENDING && pd.length > 5) { const k = pd.shift();
  pb -= k.length; pool.free(k) } await new Promise(r => setTimeout(r, d)); con = true; s = await cn();
  w = s.writable.getWriter(); r = s.readable.getReader(); con = false; cnt = 0; scr = Math.min(1, scr + 0.15);
  stl = 0; lact = Date.now(); rdL(); wtL() } catch { con = false; scr = Math.max(0.1, scr - 0.2);
  if (cnt < MAX_RECONN && ws.readyState === 1) setTimeout(rcn, 500); else { cln(); ws.close(1011) } } };
  const stT = () => { tm.ka = setInterval(async () => { if (!con && w && Date.now() - lact > KEEPALIVE) try { await w.write(new Uint8Array(0)); lact = Date.now() } catch { rcn() } }, KEEPALIVE / 3);
  tm.hc = setInterval(() => { if (!con && st.t > 0 && Date.now() - lact > STALL_TO) { stl++; if (stl >= MAX_STALL) { if (cnt < MAX_RECONN) { stl = 0; rcn() } else { cln(); ws.close(1011) } } } }, STALL_TO / 2) };
  const csk = () => { rd = false; wt = false; try { w?.releaseLock(); r?.releaseLock();
  s?.close() } catch { } }; 
  const cln = () => { Object.values(tm).forEach(clearInterval); csk(); while (pd.length) pool.free(pd.shift()); pb = 0;
  st = { t: 0, c: 0, ts: Date.now() }; md = 'buf'; asz = 0; tp = [];
  pool.reset() };
  ws.addEventListener('message', async e => { try { if (fst) { fst = false; const b = new Uint8Array(e.data); if (buildUUID(b, 1).toLowerCase() !== uuid.toLowerCase()) throw 0; ws.send(new Uint8Array([0, 0])); const { host, port, payload } = extractAddr(b); inf = { host, port }; con = true; if (payload.length) { const z = pool.alloc(payload.length); z.set(payload); pd.push(z); pb += z.length } stT(); est() } else { lact = Date.now(); if (pb > MAX_PENDING * 2) return; const z = pool.alloc(e.data.byteLength); z.set(new Uint8Array(e.data)); pd.push(z); pb += z.length } } catch { cln(); ws.close(1006) } });
  ws.addEventListener('close', cln); ws.addEventListener('error', cln)
};

// =============================================================================
// 🖥️ 现代化面板代码 (玻璃拟态 + 动态背景 + 全中文)
// =============================================================================
const COMMON_STYLE = `
    :root {
        --bg-color: #0f172a;
        --card-bg: rgba(30, 41, 59, 0.6);
        --card-border: rgba(255, 255, 255, 0.08);
        --text-primary: #f1f5f9;
        --text-secondary: #94a3b8;
        --accent-gradient: linear-gradient(135deg, #06b6d4 0%, #3b82f6 100%);
        --accent-glow: rgba(59, 130, 246, 0.3);
        --success: #10b981;
    }
    body {
        font-family: 'SF Pro SC', 'HanHei SC', 'Inter', system-ui, -apple-system, sans-serif;
        background-color: var(--bg-color);
        /* 动态背景 */
        background-image: 
            radial-gradient(at 0% 0%, rgba(59, 130, 246, 0.15) 0px, transparent 50%),
            radial-gradient(at 100% 100%, rgba(6, 182, 212, 0.15) 0px, transparent 50%);
        background-attachment: fixed;
        color: var(--text-primary);
        margin: 0;
        min-height: 100vh;
        display: flex;
        justify-content: center;
        align-items: center;
    }
    /* 玻璃拟态卡片 */
    .glass-card {
        background: var(--card-bg);
        backdrop-filter: blur(16px);
        -webkit-backdrop-filter: blur(16px);
        border: 1px solid var(--card-border);
        border-radius: 16px;
        box-shadow: 0 8px 32px rgba(0, 0, 0, 0.2);
    }
    .btn {
        background: var(--accent-gradient);
        color: white;
        border: none;
        padding: 10px 20px;
        border-radius: 8px;
        cursor: pointer;
        font-weight: 500;
        transition: all 0.2s;
        box-shadow: 0 4px 15px var(--accent-glow);
    }
    .btn:hover { transform: translateY(-1px); box-shadow: 0 6px 20px var(--accent-glow); opacity: 0.95; }
    .btn:active { transform: translateY(0); }
    
    input {
        background: rgba(0, 0, 0, 0.2);
        border: 1px solid var(--card-border);
        color: var(--text-primary);
        padding: 12px;
        border-radius: 8px;
        outline: none;
        transition: border-color 0.2s;
    }
    input:focus { border-color: #3b82f6; }
    
    /* 动画 */
    @keyframes fadeIn { from { opacity: 0; transform: translateY(10px); } to { opacity: 1; transform: translateY(0); } }
    .animate-in { animation: fadeIn 0.4s ease-out forwards; }
`;

function loginPage() {
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>系统接入</title>
    <style>
        ${COMMON_STYLE}
        .login-box {
            padding: 40px;
            width: 100%;
            max-width: 340px;
            text-align: center;
        }
        .logo-area {
            margin-bottom: 25px;
            font-size: 3rem;
            background: var(--accent-gradient);
            -webkit-background-clip: text;
            color: transparent;
        }
        .subtitle { color: var(--text-secondary); font-size: 0.9rem; margin-bottom: 30px; }
        input { width: 100%; box-sizing: border-box; text-align: center; margin-bottom: 20px; }
        button { width: 100%; padding: 12px; }
    </style>
</head>
<body>
    <div class="glass-card login-box animate-in">
        <div class="logo-area">⚡️</div>
        <h2 style="margin: 0 0 10px 0;">控制台访问</h2>
        <div class="subtitle">请输入管理员密钥以继续</div>
        
        <input type="password" id="pwd" placeholder="身份验证密钥" autofocus onkeypress="if(event.keyCode===13)verify()">
        <button onclick="verify()">验证身份</button>
    </div>
    <script>
        function verify(){
            const p=document.getElementById("pwd").value;
            if(!p)return;
            const btn = document.querySelector('button');
            btn.innerHTML = '验证中...';
            setTimeout(() => {
                document.cookie="auth="+p+"; path=/; Max-Age=31536000; SameSite=Lax";
                location.reload();
            }, 300);
        }
    </script>
</body></html>`;
}

function dashPage(host, uuid, proxyip, subpass) {
    const defaultSubLink = `https://${host}/${subpass}`;
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>服务概览</title>
    <link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet">
    <style>
        ${COMMON_STYLE}
        body { align-items: flex-start; padding-top: 50px; }
        .container { width: 90%; max-width: 800px; display: flex; flex-direction: column; gap: 24px; }
        
        /* 头部 */
        .header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; padding: 0 10px; }
        .brand { font-size: 1.4rem; font-weight: 700; display: flex; align-items: center; gap: 10px; }
        .badge { background: rgba(16, 185, 129, 0.15); color: var(--success); padding: 4px 10px; border-radius: 20px; font-size: 0.75rem; border: 1px solid rgba(16, 185, 129, 0.2); }
        
        /* 卡片内容 */
        .card-body { padding: 25px; }
        .section-title {
            font-size: 0.85rem;
            color: var(--text-secondary);
            text-transform: uppercase;
            letter-spacing: 1.5px;
            margin-bottom: 18px;
            display: flex;
            align-items: center;
            gap: 8px;
        }
        
        .input-group { display: flex; gap: 12px; }
        input { flex: 1; font-family: monospace; font-size: 0.9rem; }
        
        .btn-ghost { background: transparent; border: 1px solid var(--card-border); box-shadow: none; color: var(--text-secondary); padding: 8px 12px; }
        .btn-ghost:hover { border-color: var(--text-primary); color: var(--text-primary); transform: none; }
        
        /* 信息行 */
        .info-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 20px; }
        .info-item { background: rgba(0,0,0,0.2); padding: 15px; border-radius: 10px; border: 1px solid var(--card-border); }
        .info-label { font-size: 0.8rem; color: var(--text-secondary); margin-bottom: 5px; }
        .info-val { font-family: monospace; font-size: 0.95rem; color: #fff; word-break: break-all; }

        /* Toast 提示 */
        #toast {
            position: fixed; bottom: 30px; left: 50%; transform: translateX(-50%) translateY(50px);
            background: var(--text-primary); color: #000; padding: 10px 24px; border-radius: 50px;
            opacity: 0; transition: all 0.3s cubic-bezier(0.68, -0.55, 0.27, 1.55); pointer-events: none;
            font-weight: 600; box-shadow: 0 10px 20px rgba(0,0,0,0.3);
        }
        #toast.show { opacity: 1; transform: translateX(-50%) translateY(0); }
    </style>
</head>
<body>
    <div class="container animate-in">
        <div class="header">
            <div class="brand">
                <i class="ri-cloud-windy-line"></i> 
                <span>边缘网络控制台</span>
                <span class="badge">运行中</span>
            </div>
            <button class="btn btn-ghost" onclick="logout()" title="退出登录">
                <i class="ri-logout-box-r-line"></i>
            </button>
        </div>

        <div class="glass-card card-body">
            <div class="section-title"><i class="ri-link-m"></i> 配置同步链接</div>
            <div class="input-group">
                <input type="text" id="subLink" value="${defaultSubLink}" readonly onclick="this.select()">
                <button class="btn" onclick="copyId('subLink')"><i class="ri-file-copy-line"></i> 复制</button>
            </div>
            <p style="margin-top: 15px; font-size: 0.85rem; color: var(--text-secondary);">
                <i class="ri-information-line"></i> 请将此链接导入兼容的客户端以完成配置同步。
            </p>
        </div>

        <div class="glass-card card-body">
            <div class="section-title"><i class="ri-settings-4-line"></i> 高级参数设置</div>
            
            <div class="info-grid">
                <div class="info-item">
                    <div class="info-label">身份密钥 (UUID)</div>
                    <div class="info-val">${uuid.split('-')[0]}****${uuid.split('-')[4]}</div>
                </div>
                <div class="info-item">
                    <div class="info-label">当前服务域</div>
                    <div class="info-val">${host}</div>
                </div>
            </div>

            <div style="margin-top: 25px;">
                <label class="info-label" style="display:block; margin-bottom: 10px;">
                    自定义加速源 (Address Override)
                </label>
                <div class="input-group">
                    <input type="text" id="customIP" value="${proxyip}" placeholder="例如: data.example.com">
                    <button class="btn btn-ghost" onclick="updateLink()">更新配置</button>
                </div>
            </div>
        </div>
    </div>

    <div id="toast">已复制到剪贴板</div>

    <script>
        function showToast(msg) {
            const t = document.getElementById('toast');
            t.innerText = msg;
            t.classList.add('show');
            setTimeout(() => t.classList.remove('show'), 2000);
        }
        function copyId(id){
            const el=document.getElementById(id);el.select();
            navigator.clipboard.writeText(el.value).then(()=>showToast('已复制配置链接'));
        }
        function updateLink(){
            const ip = document.getElementById('customIP').value;
            const host = window.location.hostname;
            const pass = "${subpass}";
            let url = "https://" + host + "/" + pass;
            if(ip) url += "?proxyip=" + ip;
            document.getElementById('subLink').value = url;
            showToast('链接已更新');
        }
        function logout(){
            document.cookie="auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";
            location.reload();
        }
    </script>
</body></html>`;
}

// =============================================================================
// 🟢 主处理函数
// =============================================================================
export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      
      // 加载配置
      const _UUID = env.KEY ? await getDynamicUUID(env.KEY) : getEnv(env, 'UUID', UUID);
      const _WEB_PW = getEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = getEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      const _PROXY_IP = getEnv(env, 'PROXYIP', DEFAULT_PROXY_IP);
      const _PS = getEnv(env, 'PS', ""); 
      
      // 根路径重定向
      let _ROOT_REDIRECT = getEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (!_ROOT_REDIRECT.includes('://')) _ROOT_REDIRECT = 'https://' + _ROOT_REDIRECT;

      // 1. 订阅接口处理
      const isSubPath = (_SUB_PW && url.pathname === `/${_SUB_PW}`);
      const isNormalSub = (url.pathname === '/sub' && url.searchParams.get('uuid') === _UUID);

      if (isSubPath || isNormalSub) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 2. HTTP 请求处理 (面板与重定向)
      if (r.headers.get('Upgrade') !== 'websocket') {
          // 根路径 -> 重定向
          if (url.pathname === '/') {
              return Response.redirect(_ROOT_REDIRECT, 302);
          }
          
          // 管理面板逻辑 /admin
          if (url.pathname === '/admin' || url.pathname === '/admin/') {
              if (_WEB_PW) {
                  const cookie = r.headers.get('Cookie') || "";
                  if (!cookie.includes(`auth=${_WEB_PW}`)) {
                      return new Response(loginPage(), { status: 200, headers: {'Content-Type': 'text/html'} });
                  }
              }
              // 已登录或无密码
              return new Response(dashPage(host, _UUID, _PROXY_IP, _SUB_PW), { status: 200, headers: {'Content-Type': 'text/html'} });
          }
          
          return new Response('Not Found', { status: 404 });
      }

      // 3. WebSocket 代理处理
      // 解析路径中的 proxyip
      let proxyIPConfig = null;
      if (url.pathname.includes('/proxyip=')) {
        try {
          const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
          const [address, port] = await parseIP(proxyParam); 
          proxyIPConfig = { address, port: +port }; 
        } catch (e) {}
      }

      const globalProxyIPs = await parseProxyList(_PROXY_IP);
      const { 0: c, 1: s } = new WebSocketPair();
      s.accept();
      handle(s, proxyIPConfig, _UUID, globalProxyIPs);
      return new Response(null, { status: 101, webSocket: c });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  }
};

// =============================================================================
// 🔧 辅助工具函数
// =============================================================================
async function getCustomIPs(env) {
    let ips = getEnv(env, 'ADD', "");
    const addApi = getEnv(env, 'ADDAPI', "");
    const addCsv = getEnv(env, 'ADDCSV', "");
    
    if (addApi) {
        const urls = addApi.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); ips += "\n" + text; } } catch (e) {}
        }
    }
    
    if (addCsv) {
        const urls = addCsv.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); const lines = text.split('\n'); for (let line of lines) { const parts = line.split(','); if (parts.length >= 2) ips += `\n${parts[0].trim()}:443#${parts[1].trim()}`; } } } catch (e) {}
        }
    }
    return ips;
}

function genNodes(h, u, p, ipsText, ps = "") {
    let l = ipsText.split('\n').filter(line => line.trim() !== "");
    const cleanedProxyIP = p ? p.replace(/\n/g, ',') : '';
    const P = cleanedProxyIP ? `/proxyip=${cleanedProxyIP.trim()}` : "/";
    const E = encodeURIComponent(P);
    return l.map(L => {
        const [a, n] = L.split('#'); if (!a) return "";
        const I = a.trim(); 
        // 使用通用名称
        let N = n ? n.trim() : 'Edge-Instance';
        if (ps) N = `${N} ${ps}`;
        let i = I, pt = "443"; if (I.includes(':') && !I.includes('[')) { const s = I.split(':'); i = s[0]; pt = s[1]; }
        return `${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${E}#${encodeURIComponent(N)}`
    }).join('\n');
}

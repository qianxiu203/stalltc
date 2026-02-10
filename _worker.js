import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域 (优先级: 环境变量 > 代码硬编码)
// =============================================================================
const UUID = "06b65903-406d-4a41-8463-6fd5c0ee7798"; // 默认 UUID
const WEB_PASSWORD = "";  // 自定义登录密码
const SUB_PASSWORD = "";  // 自定义订阅路径密码
const DEFAULT_PROXY_IP = "cf.090227.xyz";  // 默认优选 IP
const ROOT_REDIRECT_URL = ""; // 根路径重定向地址
const DEFAULT_CONVERTER = "https://subapi.cmliussss.net"; // 订阅转换后端
const PROXY_CHECK_URL = "https://kaic.hidns.co/";

// 协议类型
const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

// =============================================================================
// ⚡️ 核心逻辑区 (Core Logic)
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

// 简单环境变量获取 (无数据库)
async function getSafeEnv(env, key, fallback) {
    if (env[key] && env[key].trim() !== "") return env[key];
    return fallback;
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
            } catch (e) { continue; }
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

// 简易登录页
function loginPage() {
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <title>系统访问控制</title>
    <style>
        body { font-family: sans-serif; background: #0f172a; color: white; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }
        .card { background: #1e293b; padding: 2rem; border-radius: 1rem; text-align: center; width: 300px; }
        input { width: 100%; padding: 10px; margin: 10px 0; border-radius: 5px; border: none; text-align: center; }
        button { width: 100%; padding: 10px; background: #3b82f6; color: white; border: none; border-radius: 5px; cursor: pointer; }
        button:hover { background: #2563eb; }
    </style>
</head>
<body>
    <div class="card">
        <h3>访问受限</h3>
        <input type="password" id="pwd" placeholder="输入密码" onkeypress="if(event.keyCode===13)verify()">
        <button onclick="verify()">进入</button>
    </div>
    <script>
        function verify(){
            const p = document.getElementById("pwd").value;
            if(!p) return;
            document.cookie = "auth=" + p + "; path=/; Max-Age=31536000; SameSite=Lax";
            setTimeout(() => location.reload(), 300);
        }
    </script>
</body>
</html>`;
}

// 美化版管理面板 - 包含二维码、客户端下载和毛玻璃特效
function dashPage(host, uuid, proxyip, subpass) {
    const defaultSubLink = `https://${host}/${subpass}`;
    const subLinkB64 = btoa(defaultSubLink); // 用于部分一键导入
    
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>StallTCP Lite - 订阅管理</title>
    <link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet">
    <script src="https://cdnjs.cloudflare.com/ajax/libs/qrcodejs/1.0.0/qrcode.min.js"></script>
    <style>
        :root {
            --primary: #6366f1;
            --secondary: #a855f7;
            --bg-dark: #0f172a;
            --glass-bg: rgba(30, 41, 59, 0.7);
            --glass-border: rgba(255, 255, 255, 0.1);
            --text-main: #f8fafc;
            --text-muted: #94a3b8;
        }

        body {
            margin: 0;
            padding: 0;
            font-family: 'Inter', -apple-system, BlinkMacSystemFont, sans-serif;
            background-color: var(--bg-dark);
            background-image: 
                radial-gradient(at 0% 0%, rgba(99, 102, 241, 0.15) 0px, transparent 50%),
                radial-gradient(at 100% 0%, rgba(168, 85, 247, 0.15) 0px, transparent 50%);
            color: var(--text-main);
            min-height: 100vh;
            display: flex;
            justify-content: center;
            align-items: center;
            padding: 20px;
            box-sizing: border-box;
        }

        .container {
            width: 100%;
            max-width: 480px;
            display: flex;
            flex-direction: column;
            gap: 24px;
            animation: fadeIn 0.6s ease-out;
        }

        /* 毛玻璃卡片 */
        .card {
            background: var(--glass-bg);
            backdrop-filter: blur(12px);
            -webkit-backdrop-filter: blur(12px);
            border: 1px solid var(--glass-border);
            border-radius: 20px;
            padding: 24px;
            box-shadow: 0 8px 32px rgba(0, 0, 0, 0.2);
            transition: transform 0.2s;
        }
        .card:hover { transform: translateY(-2px); }

        .header { text-align: center; margin-bottom: 20px; }
        .logo-icon { 
            font-size: 3rem; 
            background: linear-gradient(135deg, var(--primary), var(--secondary));
            -webkit-background-clip: text;
            color: transparent;
            margin-bottom: 10px;
            display: inline-block;
        }
        .title { font-size: 1.5rem; font-weight: 700; margin: 0; }
        .subtitle { color: var(--text-muted); font-size: 0.9rem; margin-top: 5px; }

        /* 输入框区域 */
        .field-label { font-size: 0.85rem; color: var(--text-muted); margin-bottom: 8px; display: block; }
        .input-group {
            display: flex;
            background: rgba(15, 23, 42, 0.6);
            border: 1px solid var(--glass-border);
            border-radius: 12px;
            padding: 4px;
            transition: border-color 0.3s;
        }
        .input-group:focus-within { border-color: var(--primary); }
        
        input {
            flex: 1;
            background: transparent;
            border: none;
            color: var(--text-main);
            padding: 12px;
            font-size: 0.95rem;
            outline: none;
            min-width: 0;
        }

        .btn {
            padding: 10px 16px;
            border-radius: 8px;
            border: none;
            font-weight: 600;
            cursor: pointer;
            transition: all 0.2s;
            display: flex;
            align-items: center;
            gap: 6px;
            font-size: 0.9rem;
        }
        .btn-primary { background: var(--primary); color: white; }
        .btn-primary:hover { background: #4f46e5; }
        .btn-copy { background: #334155; color: white; margin: 4px; }
        .btn-copy:hover { background: #475569; }

        /* 二维码区域 */
        .qr-section {
            display: flex;
            flex-direction: column;
            align-items: center;
            margin-top: 20px;
            padding-top: 20px;
            border-top: 1px solid var(--glass-border);
        }
        #qrcode {
            background: white;
            padding: 10px;
            border-radius: 12px;
            margin-top: 10px;
        }
        #qrcode img { display: block; }

        /* 快捷操作区 */
        .actions-grid {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 12px;
            margin-top: 15px;
        }
        .action-btn {
            background: rgba(255,255,255,0.05);
            border: 1px solid var(--glass-border);
            color: var(--text-muted);
            padding: 12px;
            border-radius: 12px;
            text-decoration: none;
            text-align: center;
            font-size: 0.85rem;
            transition: all 0.2s;
            display: flex;
            flex-direction: column;
            align-items: center;
            gap: 5px;
        }
        .action-btn i { font-size: 1.2rem; color: var(--text-main); }
        .action-btn:hover { background: rgba(255,255,255,0.1); color: var(--text-main); transform: translateY(-2px); }

        /* 底部信息 */
        .footer {
            text-align: center;
            margin-top: 10px;
        }
        .btn-logout {
            background: transparent;
            color: #ef4444;
            border: 1px solid rgba(239, 68, 68, 0.3);
            width: 100%;
            justify-content: center;
        }
        .btn-logout:hover { background: rgba(239, 68, 68, 0.1); }

        /* Toast 提示 */
        #toast {
            position: fixed;
            bottom: 30px;
            left: 50%;
            transform: translateX(-50%) translateY(50px);
            background: #10b981;
            color: white;
            padding: 10px 24px;
            border-radius: 50px;
            box-shadow: 0 10px 20px rgba(0,0,0,0.2);
            opacity: 0;
            transition: all 0.3s cubic-bezier(0.68, -0.55, 0.27, 1.55);
            pointer-events: none;
            display: flex;
            align-items: center;
            gap: 8px;
            z-index: 100;
        }
        #toast.show { opacity: 1; transform: translateX(-50%) translateY(0); }

        @keyframes fadeIn { from { opacity: 0; transform: translateY(10px); } to { opacity: 1; transform: translateY(0); } }
    </style>
</head>
<body>

    <div class="container">
        <div class="header">
            <i class="ri-radar-fill logo-icon"></i>
            <h1 class="title">StallTCP Lite</h1>
            <p class="subtitle">无状态 · 轻量级 · 节点订阅管理</p>
        </div>

        <div class="card">
            <label class="field-label">通用订阅链接 (Clash / Sing-box / V2ray)</label>
            <div class="input-group">
                <input type="text" id="subLink" value="${defaultSubLink}" readonly onclick="this.select()">
                <button class="btn btn-copy" onclick="copyLink()"><i class="ri-file-copy-line"></i> 复制</button>
            </div>
            
            <div class="qr-section">
                <label class="field-label" style="margin-bottom:0">扫码订阅</label>
                <div id="qrcode"></div>
            </div>
        </div>

        <div class="card">
            <label class="field-label">快捷导入 & 客户端下载</label>
            <div class="actions-grid">
                <a href="clash://install-config?url=${encodeURIComponent(defaultSubLink)}" class="action-btn">
                    <i class="ri-speed-mini-fill"></i> 导入 Clash
                </a>
                <a href="shadowrocket://add/sub://${subLinkB64}" class="action-btn">
                    <i class="ri-rocket-2-fill"></i> 导入 Shadowrocket
                </a>
                <a href="https://github.com/2dust/v2rayNG/releases" target="_blank" class="action-btn">
                    <i class="ri-android-fill"></i> 下载 v2rayNG
                </a>
                <a href="https://github.com/SagerNet/sing-box/releases" target="_blank" class="action-btn">
                    <i class="ri-box-3-fill"></i> 下载 Sing-box
                </a>
            </div>
        </div>

        <div class="footer">
            <button class="btn btn-logout" onclick="logout()">
                <i class="ri-shut-down-line"></i> 退出登录
            </button>
            <p style="font-size:0.75rem; color:#475569; margin-top:15px; font-family:monospace">UUID: ${uuid.substring(0,8)}***</p>
        </div>
    </div>

    <div id="toast"><i class="ri-check-line"></i> 复制成功</div>

    <script>
        // 生成二维码
        new QRCode(document.getElementById("qrcode"), {
            text: "${defaultSubLink}",
            width: 140,
            height: 140,
            colorDark : "#000000",
            colorLight : "#ffffff",
            correctLevel : QRCode.CorrectLevel.M
        });

        // 复制功能
        function copyLink() {
            const el = document.getElementById('subLink');
            el.select();
            navigator.clipboard.writeText(el.value).then(() => {
                showToast();
            }).catch(() => {
                alert('复制失败，请手动复制');
            });
        }

        // 登出功能
        function logout() {
            if(confirm('确定要退出登录吗？')) {
                document.cookie = "auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";
                location.reload();
            }
        }

        // Toast 动画
        function showToast() {
            const t = document.getElementById('toast');
            t.classList.add('show');
            setTimeout(() => t.classList.remove('show'), 2000);
        }
    </script>
</body>
</html>`;
}

export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      const clientIP = r.headers.get('cf-connecting-ip');

      // 加载变量
      const _UUID = env.KEY ? await getDynamicUUID(env.KEY, env.UUID_REFRESH || 86400) : (await getSafeEnv(env, 'UUID', UUID));
      const _WEB_PW = await getSafeEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = await getSafeEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      const _PROXY_IP = await getSafeEnv(env, 'PROXYIP', DEFAULT_PROXY_IP);
      const _PS = await getSafeEnv(env, 'PS', ""); 
      
      let _ROOT_REDIRECT_URL = await getSafeEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (_ROOT_REDIRECT_URL && !_ROOT_REDIRECT_URL.includes('://')) _ROOT_REDIRECT_URL = 'https://' + _ROOT_REDIRECT_URL;

      // 身份鉴权 (用于面板访问)
      let isAuthorized = false;
      if (_WEB_PW) {
        const cookie = r.headers.get('Cookie') || "";
        const regex = new RegExp(`auth=${_WEB_PW.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(;|$)`);
        if (regex.test(cookie)) isAuthorized = true;
      }

      if (url.pathname === '/favicon.ico') return new Response(null, { status: 404 });

      // 根路径重定向
      if (url.pathname === '/' && r.headers.get('Upgrade') !== 'websocket') {
          if(_ROOT_REDIRECT_URL) return Response.redirect(_ROOT_REDIRECT_URL, 302);
          // 如果没有重定向链接，且有密码，跳转到 admin
          if(_WEB_PW) return Response.redirect(`https://${host}/admin`, 302);
      }

      // 🟢 订阅接口 (通过 Path 访问)
      if (_SUB_PW && url.pathname === `/${_SUB_PW}`) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 🟢 订阅接口 (通过 /sub 访问)
      if (url.pathname === '/sub') {
          const requestUUID = url.searchParams.get('uuid');
          if (requestUUID !== _UUID) return new Response('Invalid UUID', { status: 403 });
          
          let proxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, proxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 🟢 简易面板逻辑 (HTTP)
      if (url.pathname === '/admin' && r.headers.get('Upgrade') !== 'websocket') {
        const noCacheHeaders = { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' };
        if (_WEB_PW && !isAuthorized) {
            return new Response(loginPage(), { status: 200, headers: noCacheHeaders });
        }
        return new Response(dashPage(host, _UUID, _PROXY_IP, _SUB_PW), { status: 200, headers: noCacheHeaders });
      }
      
      // 🟣 代理逻辑 (WebSocket)
      let proxyIPConfig = null;
      if (url.pathname.includes('/proxyip=')) {
        try {
          const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
          const [address, port] = await parseIP(proxyParam); 
          proxyIPConfig = { address, port: +port }; 
        } catch (e) {}
      }

      // 解析全局 ProxyIP 列表
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

async function getCustomIPs(env) {
    let ips = await getSafeEnv(env, 'ADD', "");
    const addApi = await getSafeEnv(env, 'ADDAPI', "");
    const addCsv = await getSafeEnv(env, 'ADDCSV', "");
    
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
        let N = n ? n.trim() : 'Worker-Node';
        if (ps) N = `${N} ${ps}`;
        let i = I, pt = "443"; if (I.includes(':') && !I.includes('[')) { const s = I.split(':'); i = s[0]; pt = s[1]; }
        return `${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${E}#${encodeURIComponent(N)}`
    }).join('\n');
}

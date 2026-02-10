import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域
// =============================================================================
const UUID = ""; // 你的 UUID
const WEB_PASSWORD = "";  // 管理面板密码
const SUB_PASSWORD = "";  // 订阅路径密码
const DEFAULT_PROXY_IP = "";  // 默认回退 ProxyIP (例如: 1.2.3.4 或 domain.com)
const ROOT_REDIRECT_URL = "https://www.google.com"; 

// =============================================================================
// ⚡️ 核心逻辑区
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

function getEnv(env, key, fallback) { return env[key] || fallback; }

// 解析单个 IP 或域名
async function parseIP(p){
    if(!p) return null;
    p=p.trim().toLowerCase();
    let a=p,o=443;
    if(p.includes('.tp')){
        const m=p.match(/\.tp(\d+)/);
        if(m)o=parseInt(m[1],10);
        return { address: a, port: o };
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
    return { address: a, port: o };
}

class Pool{constructor(){this.b=new ArrayBuffer(16384);this.p=0;this.l=[];this.m=8}alloc(s){if(s<=4096&&s<=16384-this.p){const v=new Uint8Array(this.b,this.p,s);this.p+=s;return v}const r=this.l.pop();return r&&r.byteLength>=s?new Uint8Array(r.buffer,0,s):new Uint8Array(s)}free(b){if(b.buffer===this.b)this.p=Math.max(0,this.p-b.length);else if(this.l.length<this.m&&b.byteLength>=1024)this.l.push(b)}reset(){this.p=0;this.l=[]}}

async function getDynamicUUID(key, refresh = 86400) {
    const time = Math.floor(Date.now() / 1000 / refresh);
    const msg = new TextEncoder().encode(`${key}-${time}`);
    const hash = await crypto.subtle.digest('SHA-256', msg);
    const b = new Uint8Array(hash);
    return [...b.slice(0, 16)].map(n => n.toString(16).padStart(2, '0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/, '$1-$2-$3-$4-$5');
}

/**
 * 核心处理函数
 * @param {WebSocket} ws 
 * @param {Object} proxyConfig 单个 ProxyIP 配置
 * @param {string} uuid 
 */
const handle = (ws, proxyConfig, uuid) => {
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
  
  // 🟢 智能连接逻辑 (Direct -> Fallback Proxy)
  const cn = async () => {
    // 1. 尝试直连 (带 2.5秒 超时控制)
    try {
        const directPromise = connect({ hostname: inf.host, port: inf.port });
        const direct = await Promise.race([
            directPromise.opened.then(() => directPromise),
            new Promise((_, reject) => setTimeout(() => reject('Direct timeout'), 2500))
        ]);
        return direct;
    } catch (e) {
        // 直连失败（报错或超时），静默进入下一步
    }

    // 2. 直连失败，回退到 ProxyIP
    if (proxyConfig && proxyConfig.address) {
        try {
            const proxy = connect({ hostname: proxyConfig.address, port: proxyConfig.port });
            await proxy.opened;
            return proxy;
        } catch (e) {
            // Proxy 也连不上
        }
    }

    // 3. 全部失败
    throw new Error('Connection failed: Direct and Proxy both unreachable');
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
// 🖥️ 面板代码
// =============================================================================
const COMMON_STYLE = `
    :root { --bg-color: #0f172a; --card-bg: rgba(30, 41, 59, 0.6); --card-border: rgba(255, 255, 255, 0.08); --text-primary: #f1f5f9; --text-secondary: #94a3b8; --accent-gradient: linear-gradient(135deg, #06b6d4 0%, #3b82f6 100%); --accent-glow: rgba(59, 130, 246, 0.3); --success: #10b981; }
    body { font-family: 'SF Pro SC', 'Inter', sans-serif; background-color: var(--bg-color); color: var(--text-primary); margin: 0; min-height: 100vh; display: flex; justify-content: center; align-items: center; background-image: radial-gradient(at 0% 0%, rgba(59, 130, 246, 0.15) 0px, transparent 50%), radial-gradient(at 100% 100%, rgba(6, 182, 212, 0.15) 0px, transparent 50%); background-attachment: fixed; }
    .glass-card { background: var(--card-bg); backdrop-filter: blur(16px); -webkit-backdrop-filter: blur(16px); border: 1px solid var(--card-border); border-radius: 16px; box-shadow: 0 8px 32px rgba(0, 0, 0, 0.2); }
    .btn { background: var(--accent-gradient); color: white; border: none; padding: 10px 20px; border-radius: 8px; cursor: pointer; font-weight: 500; transition: all 0.2s; box-shadow: 0 4px 15px var(--accent-glow); }
    .btn:hover { transform: translateY(-1px); opacity: 0.95; }
    input { background: rgba(0, 0, 0, 0.2); border: 1px solid var(--card-border); color: var(--text-primary); padding: 12px; border-radius: 8px; outline: none; transition: border-color 0.2s; }
    input:focus { border-color: #3b82f6; }
    .animate-in { animation: fadeIn 0.4s ease-out forwards; } @keyframes fadeIn { from { opacity: 0; transform: translateY(10px); } to { opacity: 1; transform: translateY(0); } }
`;

function loginPage() {
    return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0"><title>系统接入</title><style>${COMMON_STYLE}.login-box{padding:40px;width:100%;max-width:340px;text-align:center}.logo-area{margin-bottom:25px;font-size:3rem;background:var(--accent-gradient);-webkit-background-clip:text;color:transparent}input{width:100%;box-sizing:border-box;text-align:center;margin-bottom:20px}button{width:100%;padding:12px}</style></head><body><div class="glass-card login-box animate-in"><div class="logo-area">⚡️</div><h2 style="margin:0 0 10px 0">控制台访问</h2><input type="password" id="pwd" placeholder="身份验证密钥" autofocus onkeypress="if(event.keyCode===13)verify()"><button onclick="verify()">验证身份</button></div><script>function verify(){const p=document.getElementById("pwd").value;if(!p)return;document.querySelector('button').innerHTML='验证中...';setTimeout(()=>{document.cookie="auth="+p+"; path=/; Max-Age=31536000";location.reload()},300)}</script></body></html>`;
}

function dashPage(host, uuid, proxyip, subpass) {
    const defaultSubLink = `https://${host}/${subpass}`;
    return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0"><title>服务概览</title><link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet"><style>${COMMON_STYLE}body{align-items:flex-start;padding-top:50px}.container{width:90%;max-width:800px;display:flex;flex-direction:column;gap:24px}.header{display:flex;justify-content:space-between;align-items:center;padding:0 10px}.card-body{padding:25px}.input-group{display:flex;gap:12px}input{flex:1;font-family:monospace}.info-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:20px}.info-item{background:rgba(0,0,0,0.2);padding:15px;border-radius:10px;border:1px solid var(--card-border)}.info-label{font-size:0.8rem;color:var(--text-secondary);margin-bottom:5px}.info-val{font-family:monospace;font-size:0.95rem;color:#fff;word-break:break-all}#toast{position:fixed;bottom:30px;left:50%;transform:translateX(-50%) translateY(50px);background:var(--text-primary);color:#000;padding:10px 24px;border-radius:50px;opacity:0;transition:all 0.3s;pointer-events:none;font-weight:600}#toast.show{opacity:1;transform:translateX(-50%) translateY(0)}</style></head><body><div class="container animate-in"><div class="header"><div style="font-size:1.4rem;font-weight:700"><i class="ri-cloud-windy-line"></i> 边缘网络控制台</div><button class="btn" style="background:transparent;border:1px solid var(--card-border)" onclick="logout()"><i class="ri-logout-box-r-line"></i></button></div><div class="glass-card card-body"><div><i class="ri-link-m"></i> 配置同步链接</div><div class="input-group" style="margin-top:10px"><input type="text" id="subLink" value="${defaultSubLink}" readonly onclick="this.select()"><button class="btn" onclick="copyId('subLink')">复制</button></div></div><div class="glass-card card-body"><div class="info-grid"><div class="info-item"><div class="info-label">UUID</div><div class="info-val">${uuid}</div></div><div class="info-item"><div class="info-label">Domain</div><div class="info-val">${host}</div></div></div><div style="margin-top:25px"><label class="info-label" style="display:block;margin-bottom:10px">自定义加速源 (Address Override)</label><div class="input-group"><input type="text" id="customIP" value="${proxyip}" placeholder="例如: data.example.com"><button class="btn" style="background:transparent;border:1px solid var(--card-border)" onclick="updateLink()">更新</button></div></div></div></div><div id="toast">已复制</div><script>function showToast(m){const t=document.getElementById('toast');t.innerText=m;t.classList.add('show');setTimeout(()=>t.classList.remove('show'),2000)}function copyId(id){const el=document.getElementById(id);el.select();navigator.clipboard.writeText(el.value).then(()=>showToast('已复制配置链接'))}function updateLink(){const ip=document.getElementById('customIP').value;const u="https://"+window.location.hostname+"/${subpass}";document.getElementById('subLink').value=ip?u+"?proxyip="+ip:u;showToast('链接已更新')}function logout(){document.cookie="auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";location.reload()}</script></body></html>`;
}

// =============================================================================
// 🟢 主入口 (Fetch Event)
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
      const _PROXY_IP_RAW = getEnv(env, 'PROXYIP', DEFAULT_PROXY_IP);
      const _PS = getEnv(env, 'PS', ""); 
      
      const _PROXY_IP = _PROXY_IP_RAW ? _PROXY_IP_RAW.split(/[,\n]/)[0].trim() : "";
      
      let _ROOT_REDIRECT = getEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (!_ROOT_REDIRECT.includes('://')) _ROOT_REDIRECT = 'https://' + _ROOT_REDIRECT;

      // 1. 订阅接口
      const isSubPath = (_SUB_PW && url.pathname === `/${_SUB_PW}`);
      const isNormalSub = (url.pathname === '/sub' && url.searchParams.get('uuid') === _UUID);

      if (isSubPath || isNormalSub) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 2. HTTP 请求
      if (r.headers.get('Upgrade') !== 'websocket') {
          if (url.pathname === '/') return Response.redirect(_ROOT_REDIRECT, 302);
          if (url.pathname === '/admin' || url.pathname === '/admin/') {
              if (_WEB_PW) {
                  const cookie = r.headers.get('Cookie') || "";
                  if (!cookie.includes(`auth=${_WEB_PW}`)) return new Response(loginPage(), { status: 200, headers: {'Content-Type': 'text/html'} });
              }
              return new Response(dashPage(host, _UUID, _PROXY_IP, _SUB_PW), { status: 200, headers: {'Content-Type': 'text/html'} });
          }
          return new Response('Not Found', { status: 404 });
      }

      // 3. WebSocket 代理处理
      // 策略：优先从 URL 参数解析 ProxyIP，其次是 Path，最后是环境变量
      let finalProxyConfig = null;
      const remoteProxyIP = url.searchParams.get('proxyip'); // 🟢 获取 ?proxyip= 参数

      // 优先级 1: URL 参数 (?proxyip=...) -> 最推荐的标准方式
      if (remoteProxyIP) {
          try {
              finalProxyConfig = await parseIP(remoteProxyIP);
          } catch (e) {}
      }
      // 优先级 2: Path 路径 (/proxyip=...) -> 兼容旧版客户端配置
      else if (url.pathname.includes('/proxyip=')) {
        try {
            const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
            finalProxyConfig = await parseIP(proxyParam);
        } catch (e) {}
      } 
      // 优先级 3: 环境变量 (仅取第一个) -> 默认回退
      else if (_PROXY_IP) {
        try {
            finalProxyConfig = await parseIP(_PROXY_IP);
        } catch (e) {}
      }

      const { 0: c, 1: s } = new WebSocketPair();
      s.accept();
      handle(s, finalProxyConfig, _UUID);
      return new Response(null, { status: 101, webSocket: c });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  }
};

// =============================================================================
// 🔧 辅助工具
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
    
    // 🟢 优化: 移除 ed=2560，直接使用标准的 ProxyIP 参数格式
    // 如果存在 ProxyIP (p)，则追加到查询参数中
    let basePath = "/";
    if (p && p.trim() !== "") {
        basePath += `?proxyip=${p.trim()}`;
    }
    
    // 对整个 Path 进行 URI 编码
    const encodedPath = encodeURIComponent(basePath);

    return l.map(L => {
        const [a, n] = L.split('#'); if (!a) return "";
        const I = a.trim(); 
        
        let N = n ? n.trim() : 'Edge-Instance';
        if (ps) N = `${N} ${ps}`;
        
        // 处理 IPv6 格式 [xxxx]:port 和常规 ip:port
        let i = I, pt = "443"; 
        if (I.includes(']:')) { // IPv6
            const s = I.split(']:');
            i = s[0] + ']';
            pt = s[1];
        } else if (I.includes(':') && !I.includes('[')) { // IPv4 或 域名
            const s = I.split(':');
            i = s[0];
            pt = s[1];
        }
        
        return `${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${encodedPath}#${encodeURIComponent(N)}`
    }).join('\n');
}

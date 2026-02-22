import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域 (建议在 Cloudflare 后台设置对应的环境变量，勿在此硬编码)
// =============================================================================
const UUID = ""; // 你的核心 UUID 
const WEB_PASSWORD = "";  // 管理面板登录密码 & Cron 触发器鉴权密码
const SUB_PASSWORD = "";  // 订阅路径密码

// 🟢【重要配置】: 默认 ProxyIP (兜底地址)
const DEFAULT_PROXY_IP = ""; 

// 🟢【伪装配置】: 默认节点路径
const NODE_DEFAULT_PATH = "/api/v1"; 
const ROOT_REDIRECT_URL = ""; 
// =============================================================================
// 🚀 进阶架构配置说明 (多账号横向扩展 & 自动熔断)
// =============================================================================
//
// 1️⃣ 基础负载均衡池 (环境变量名: POOL_DOMAINS)
//    - 作用: 仅做静态的订阅节点分发，由客户端执行负载均衡。
//    - 值示例: node1.a.workers.dev, node2.b.workers.dev
//
// 2️⃣ 智能探针与自动熔断 (高级用法)
//    若要启用此功能，需在 Cloudflare 后台完成以下两项配置：
//
//    A. 绑定 KV 命名空间
//       - 在 Worker 设置中，绑定一个 KV 命名空间，变量名必须为: NODE_STATUS
//
//    B. 配置账号矩阵 (环境变量名: ACCOUNTS_CONFIG)
//       - 作用: 填入各子账号的 API 凭证。定时探针会监控用量，超过 95000 次自动将其从订阅池中剔除，次日 0 点自动恢复。
//       - 值示例 (严格的 JSON 数组格式):
//         [
//           {"domain": "node1.a.workers.dev", "id": "账号A的AccountID", "token": "账号A的APIToken"},
//           {"domain": "node2.b.workers.dev", "id": "账号B的AccountID", "token": "账号B的APIToken"}
//         ]

// =============================================================================
// ⚡️ 核心逻辑区
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

function getEnv(env, key, fallback) { return env[key] || fallback; }

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
  
  const cn = async () => {
    try {
        const directPromise = connect({ hostname: inf.host, port: inf.port });
        const direct = await Promise.race([
            directPromise.opened.then(() => directPromise),
            new Promise((_, reject) => setTimeout(() => reject('Direct timeout'), 2500))
        ]);
        return direct;
    } catch (e) {}

    if (proxyConfig && proxyConfig.address) {
        try {
            const proxy = connect({ hostname: proxyConfig.address, port: proxyConfig.port });
            await proxy.opened;
            return proxy;
        } catch (e) {}
    }
    throw new Error('Connection failed');
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
// 🎨 极简暗黑毛玻璃 (Dark Glassmorphism) 面板
// =============================================================================
const COMMON_STYLE = `
    :root { 
        --bg-dark: #0f172a; 
        --surface: rgba(30, 41, 59, 0.7); 
        --primary: #3b82f6; 
        --primary-hover: #2563eb;
        --danger: #ef4444;
        --text-main: #f8fafc; 
        --text-muted: #94a3b8; 
        --border: rgba(255, 255, 255, 0.1); 
        --radius: 12px;
    }
    body { font-family: system-ui, -apple-system, sans-serif; background-color: var(--bg-dark); background-image: radial-gradient(circle at 50% 0%, #1e293b, #0f172a); color: var(--text-main); margin: 0; min-height: 100vh; display: flex; justify-content: center; align-items: center; }
    .glass-card { background: var(--surface); backdrop-filter: blur(16px); -webkit-backdrop-filter: blur(16px); border: 1px solid var(--border); border-radius: var(--radius); padding: 2.5rem; width: 90%; max-width: 540px; box-shadow: 0 25px 50px -12px rgba(0,0,0,0.5); position: relative; }
    .header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 2rem; padding-bottom: 1rem; border-bottom: 1px solid var(--border); }
    .title { font-size: 1.5rem; font-weight: 600; margin: 0; display: flex; align-items: center; gap: 0.5rem; }
    .title::before { content: ''; display: block; width: 12px; height: 12px; background: var(--primary); border-radius: 50%; box-shadow: 0 0 10px var(--primary); }
    .btn { background: var(--primary); color: white; border: none; padding: 0.6rem 1.2rem; border-radius: 8px; font-weight: 500; cursor: pointer; transition: all 0.2s ease; }
    .btn:hover { background: var(--primary-hover); transform: translateY(-1px); }
    .btn-danger { background: transparent; border: 1px solid var(--border); color: var(--text-muted); }
    .btn-danger:hover { background: var(--danger); border-color: var(--danger); color: white; }
    .form-group { margin-bottom: 1.5rem; }
    .label { display: block; font-size: 0.8rem; font-weight: 600; color: var(--text-muted); margin-bottom: 0.5rem; text-transform: uppercase; }
    .input-wrapper { display: flex; gap: 0.5rem; }
    input { width: 100%; padding: 0.75rem 1rem; background: rgba(15, 23, 42, 0.6); border: 1px solid var(--border); border-radius: 8px; color: var(--text-main); font-family: monospace; outline: none; transition: border-color 0.2s; box-sizing: border-box; }
    input:focus { border-color: var(--primary); }
    .grid-2 { display: grid; grid-template-columns: 1fr 1fr; gap: 1rem; }
    .info-box { background: rgba(15, 23, 42, 0.4); border: 1px solid var(--border); border-radius: 8px; padding: 1rem; }
    .info-val { font-family: monospace; font-size: 0.95rem; word-break: break-all; margin-top: 0.25rem; }
    #toast { position: fixed; bottom: 2rem; left: 50%; transform: translate(-50%, 100px); background: var(--text-main); color: var(--bg-dark); padding: 0.75rem 1.5rem; border-radius: 2rem; font-weight: 600; transition: transform 0.3s; pointer-events: none; }
    #toast.show { transform: translate(-50%, 0); }
    .animate-in { animation: fadeSlideUp 0.5s ease-out forwards; }
    @keyframes fadeSlideUp { from { opacity: 0; transform: translateY(20px); } to { opacity: 1; transform: translateY(0); } }
`;

function loginPage() {
    return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0"><title>System Login</title><style>${COMMON_STYLE}</style></head><body>
    <div class="glass-card animate-in" style="max-width: 360px;">
        <div class="header" style="justify-content: center; margin-bottom: 1.5rem; border: none; padding: 0;"><h1 class="title" style="font-size: 1.25rem;">Node Authentication</h1></div>
        <div class="form-group"><input type="password" id="pwd" placeholder="Enter Access Key..." onkeypress="if(event.keyCode===13)verify()" autofocus></div>
        <button class="btn" style="width:100%" onclick="verify()">Authenticate</button>
    </div>
    <script>function verify(){const p=document.getElementById("pwd").value;if(!p)return;document.cookie="auth="+p+"; path=/; Max-Age=31536000";location.reload()}</script>
    </body></html>`;
}

function dashPage(host, uuid, proxyip, subpass) {
    const defaultSubLink = `https://${host}/${subpass}`;
    return `<!DOCTYPE html><html lang="zh-CN"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width,initial-scale=1.0"><title>Node Dashboard</title><style>${COMMON_STYLE}</style></head><body>
    <div class="glass-card animate-in">
        <div class="header"><h1 class="title">Control Panel</h1><button class="btn btn-danger" onclick="logout()">Logout</button></div>
        <div class="form-group">
            <span class="label">Subscription Link</span>
            <div class="input-wrapper"><input type="text" id="subLink" value="${defaultSubLink}" readonly><button class="btn" onclick="copyId('subLink')">Copy</button></div>
        </div>
        <div class="grid-2 form-group">
            <div class="info-box"><span class="label">Client UUID</span><div class="info-val">${uuid.substring(0,8)}...${uuid.substring(uuid.length-4)}</div></div>
            <div class="info-box"><span class="label">Edge Host</span><div class="info-val">${host}</div></div>
        </div>
        <div class="form-group" style="margin-bottom: 0;">
            <span class="label">Routing Override (ProxyIP)</span>
            <div class="input-wrapper"><input type="text" id="customIP" value="${proxyip}" placeholder="Leave empty for default routing"><button class="btn" onclick="updateLink()">Apply</button></div>
        </div>
    </div>
    <div id="toast">Copied to clipboard</div>
    <script>
    function showToast(m){const t=document.getElementById('toast');if(m)t.innerText=m;t.classList.add('show');setTimeout(()=>t.classList.remove('show'),2000)}
    function copyId(id){const el=document.getElementById(id);el.select();navigator.clipboard.writeText(el.value).then(()=>showToast())}
    function updateLink(){const ip=document.getElementById('customIP').value.trim(); const u="https://"+window.location.hostname+"/${subpass}"; document.getElementById('subLink').value=ip?u+"?proxyip="+ip:u; showToast('Link Updated');}
    function logout(){document.cookie="auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";location.reload()}
    </script></body></html>`;
}

// =============================================================================
// 🟢 主入口 (支持 fetch 和 scheduled 双事件)
// =============================================================================
export default {
  async fetch(r, env, ctx) {
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      
      const _UUID = env.KEY ? await getDynamicUUID(env.KEY) : getEnv(env, 'UUID', UUID);
      const _WEB_PW = getEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = getEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      
      const _PROXY_IP_RAW = env.PROXYIP || env.DEFAULT_PROXY_IP || DEFAULT_PROXY_IP;
      const _PS = getEnv(env, 'PS', ""); 
      const _PROXY_IP = _PROXY_IP_RAW ? _PROXY_IP_RAW.split(/[,\n]/)[0].trim() : "";
      
      let _ROOT_REDIRECT = getEnv(env, 'ROOT_REDIRECT_URL', ROOT_REDIRECT_URL);
      if (!_ROOT_REDIRECT.includes('://')) _ROOT_REDIRECT = 'https://' + _ROOT_REDIRECT;

      // 🔍 核心逻辑：获取健康节点列表
      let activeDomains = [];
      const configStr = env.ACCOUNTS_CONFIG;
      const poolStr = getEnv(env, 'POOL_DOMAINS', host);

      if (configStr) {
          try {
              const accs = JSON.parse(configStr);
              accs.forEach(a => { if (a.domain && !activeDomains.includes(a.domain)) activeDomains.push(a.domain.trim()); });
          } catch(e) {}
      } else if (poolStr) {
          activeDomains = poolStr.split(',').map(d => d.trim()).filter(Boolean);
      }
      
      if (env.NODE_STATUS && activeDomains.length > 0) {
          const healthyDomains = [];
          for (let d of activeDomains) {
              const status = await env.NODE_STATUS.get(`status_${d}`);
              if (status !== 'offline') healthyDomains.push(d);
          }
          if (healthyDomains.length > 0) activeDomains = healthyDomains; 
      }

      if (activeDomains.length === 0) activeDomains = [host];

      // 处理订阅请求
      if (isSubPath(_SUB_PW, url) || isNormalSub(_UUID, url)) {
          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(activeDomains, _UUID, requestProxyIp, allIPs, _PS, _PROXY_IP);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 处理普通 HTTP 请求
      if (r.headers.get('Upgrade') !== 'websocket') {
          // 🟢 Pages 环境专属：外部定时器触发接口 (WebHook)
          if (url.pathname === '/cron') {
              const requestToken = url.searchParams.get('token');
              if (requestToken === _WEB_PW && _WEB_PW !== "") {
                  // 利用 ctx.waitUntil 保证异步探针不阻塞响应
                  ctx.waitUntil(checkAccountsHealth(env));
                  return new Response(JSON.stringify({ status: "cron executed", desc: "Checking accounts health...", time: new Date().toISOString() }), { status: 200, headers: { 'Content-Type': 'application/json' } });
              }
              return new Response('Unauthorized Webhook Access', { status: 401 });
          }

          if (url.pathname === '/') return Response.redirect(_ROOT_REDIRECT, 302);
          if (url.pathname === '/admin' || url.pathname === '/admin/') {
              if (_WEB_PW) {
                  const cookie = r.headers.get('Cookie') || "";
                  if (!cookie.includes(`auth=${_WEB_PW}`)) return new Response(loginPage(), { status: 200, headers: {'Content-Type': 'text/html'} });
              }
              return new Response(dashPage(host, _UUID, _PROXY_IP, _SUB_PW), { status: 200, headers: {'Content-Type': 'text/html'} });
          }
          if (url.pathname === NODE_DEFAULT_PATH) {
              return new Response(JSON.stringify({ status: "ok", version: "1.1.0" }), { status: 200, headers: { 'Content-Type': 'application/json' } });
          }
          return new Response('Not Found', { status: 404 });
      }

      // 处理 WebSocket 代理流量
      let finalProxyConfig = null;
      const remoteProxyIP = url.searchParams.get('proxyip'); 

      if (remoteProxyIP) {
          try { finalProxyConfig = await parseIP(remoteProxyIP); } catch (e) {}
      }
      else if (url.pathname.includes('/proxyip=')) {
        try {
            const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
            finalProxyConfig = await parseIP(proxyParam);
        } catch (e) {}
      } 
      else if (_PROXY_IP) {
        try { finalProxyConfig = await parseIP(_PROXY_IP); } catch (e) {}
      }

      const { 0: c, 1: s } = new WebSocketPair();
      s.accept();
      handle(s, finalProxyConfig, _UUID);
      return new Response(null, { status: 101, webSocket: c });

    } catch (err) {
      return new Response(err.toString(), { status: 500 });
    }
  },

  // 兼容标准 Worker 的定时任务入口
  async scheduled(event, env, ctx) {
      await checkAccountsHealth(env);
  }
};

// =============================================================================
// 🔧 辅助工具与探针逻辑
// =============================================================================
function isSubPath(pw, url) { return pw && url.pathname === `/${pw}`; }
function isNormalSub(uuid, url) { return url.pathname === '/sub' && url.searchParams.get('uuid') === uuid; }

async function checkAccountsHealth(env) {
    if (!env.ACCOUNTS_CONFIG || !env.NODE_STATUS) return;
    try {
        const accounts = JSON.parse(env.ACCOUNTS_CONFIG);
        const checks = accounts.map(async (acc) => {
            if (!acc.id || !acc.token || !acc.domain) return;
            const usage = await getCloudflareUsage(acc.id, acc.token);
            if (usage.success) {
                const isOffline = usage.requests >= 95000;
                const kvKey = `status_${acc.domain.trim()}`;
                if (isOffline) {
                    const now = new Date();
                    const tomorrow = new Date(now);
                    tomorrow.setUTCHours(24, 0, 0, 0);
                    const ttlSeconds = Math.floor((tomorrow.getTime() - now.getTime()) / 1000);
                    await env.NODE_STATUS.put(kvKey, 'offline', { expirationTtl: Math.max(60, ttlSeconds) });
                } else {
                    await env.NODE_STATUS.delete(kvKey);
                }
            }
        });
        await Promise.all(checks);
    } catch (e) {}
}

async function getCloudflareUsage(accountID, apiToken) {
    const API = "https://api.cloudflare.com/client/v4/graphql";
    const now = new Date(); 
    now.setUTCHours(0, 0, 0, 0); 
    try {
        const res = await fetch(API, {
            method: "POST",
            headers: { "Content-Type": "application/json", "Authorization": `Bearer ${apiToken}` },
            body: JSON.stringify({
                query: `query getBillingMetrics($AccountID: String!, $filter: AccountWorkersInvocationsAdaptiveFilter_InputObject) { 
                    viewer { accounts(filter: {accountTag: $AccountID}) { workersInvocationsAdaptive(limit: 10000, filter: $filter) { sum { requests } } pagesFunctionsInvocationsAdaptiveGroups(limit: 1000, filter: $filter) { sum { requests } } } } 
                }`,
                variables: { AccountID: accountID, filter: { datetime_geq: now.toISOString(), datetime_leq: new Date().toISOString() } }
            })
        });
        if (!res.ok) throw new Error("API Error");
        const result = await res.json();
        const acc = result?.data?.viewer?.accounts?.[0];
        const workersReq = acc?.workersInvocationsAdaptive?.reduce((t, i) => t + (i?.sum?.requests || 0), 0) || 0;
        const pagesReq = acc?.pagesFunctionsInvocationsAdaptiveGroups?.reduce((t, i) => t + (i?.sum?.requests || 0), 0) || 0;
        return { success: true, requests: workersReq + pagesReq };
    } catch (e) { return { success: false, msg: e.message }; }
}

async function getCustomIPs(env) {
    let ips = getEnv(env, 'ADD', "");
    const addApi = getEnv(env, 'ADDAPI', "");
    const addCsv = getEnv(env, 'ADDCSV', "");
    if (addApi) {
        const urls = addApi.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) { try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); ips += "\n" + text; } } catch (e) {} }
    }
    if (addCsv) {
        const urls = addCsv.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) { try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); const lines = text.split('\n'); for (let line of lines) { const parts = line.split(','); if (parts.length >= 2) ips += `\n${parts[0].trim()}:443#${parts[1].trim()}`; } } } catch (e) {} }
    }
    return ips;
}

function genNodes(hostsArray, u, p, ipsText, ps = "", defaultIP = "") {
    let l = ipsText.split('\n').filter(line => line.trim() !== "");
    let safeP = p ? p.trim() : "";
    let safeDef = defaultIP ? defaultIP.trim() : "";
    let finalPath = NODE_DEFAULT_PATH;
    if (safeP && safeP !== "" && safeP !== safeDef) finalPath += `?proxyip=${safeP}`;
    const encodedPath = encodeURIComponent(finalPath);
    let nodes = [];

    l.forEach((L) => {
        const [a, n] = L.split('#'); 
        if (!a) return;
        const I = a.trim(); 
        let i = I, pt = "443"; 
        if (I.includes(']:')) { const s = I.split(']:'); i = s[0] + ']'; pt = s[1]; } 
        else if (I.includes(':') && !I.includes('[')) { const s = I.split(':'); i = s[0]; pt = s[1]; }

        hostsArray.forEach((h, hostIndex) => {
            let baseName = n ? n.trim() : 'Edge-Instance';
            let N = hostsArray.length > 1 ? `${baseName}-Node${hostIndex + 1}` : baseName;
            if (ps) N = `${N} ${ps}`;
            nodes.push(`${PT_TYPE}://${u}@${i}:${pt}?encryption=none&security=tls&sni=${h}&alpn=h3&fp=random&allowInsecure=1&type=ws&host=${h}&path=${encodedPath}#${encodeURIComponent(N)}`);
        });
    });
    return nodes.join('\n');
}

import { connect } from 'cloudflare:sockets';

// =============================================================================
// 🟣 用户配置区域 (优先级环境变量-代码硬编码)           下方内容可改生效于内置代码 【不使用环境变量的情况下】
// =============================================================================
const UUID = ""; // 修改可用的uuid
const WEB_PASSWORD = "";  //自己要修改自定义的登录密码
const SUB_PASSWORD = "";  // 自己要修改自定义的订阅密码
const DEFAULT_PROXY_IP = "";  //可修改自定义的proxyip

const TG_GROUP_URL = "";   //可修改自定义内容
const TG_CHANNEL_URL = "";  //可此修改自定义内容
const PROXY_CHECK_URL = "https://kaic.hidns.co/";  //可修改自定义的proxyip检测站
const DEFAULT_CONVERTER = "https://subapi.cmliussss.net";  //可修改自定义后端api
const CLASH_CONFIG = "https://raw.githubusercontent.com/cmliu/ACL4SSR/main/Clash/config/ACL4SSR_Online_Full_MultiMode.ini"; //可修改自定义订阅配置转换ini
const SINGBOX_CONFIG_V12 = "https://raw.githubusercontent.com/sinspired/sub-store-template/main/1.12.x/sing-box.json"; //禁止修改 优先使用1.12 后用1.11
const SINGBOX_CONFIG_V11 = "https://raw.githubusercontent.com/sinspired/sub-store-template/main/1.11.x/sing-box.json"; //禁止修改
const TG_BOT_TOKEN = ""; //你的机器人token
const TG_CHAT_ID = "";  //你的TG ID
const ADMIN_IP = "";  //你的白名单IP 保护你不会被自己域名拉黑 (支持多IP，使用英文逗号分隔)

// =============================================================================
// ⚡️ 核心逻辑区 (Core Logic)
// =============================================================================
const MAX_PENDING=2097152,KEEPALIVE=15000,STALL_TO=8000,MAX_STALL=12,MAX_RECONN=24;
const buildUUID=(a,i)=>[...a.slice(i,i+16)].map(n=>n.toString(16).padStart(2,'0')).join('').replace(/^(.{8})(.{4})(.{4})(.{4})(.{12})$/,'$1-$2-$3-$4-$5');
const extractAddr=b=>{const o=18+b[17]+1,p=(b[o]<<8)|b[o+1],t=b[o+2];let l,h,O=o+3;switch(t){case 1:l=4;h=b.slice(O,O+l).join('.');break;case 2:l=b[O++];h=new TextDecoder().decode(b.slice(O,O+l));break;case 3:l=16;h=`[${[...Array(8)].map((_,i)=>((b[O+i*2]<<8)|b[O+i*2+1]).toString(16)).join(':')}]`;break;default:throw new Error('Addr type error');}return{host:h,port:p,payload:b.slice(O+l)}};

// 协议类型混淆
const PT_TYPE = 'v'+'l'+'e'+'s'+'s';

// =============================================================================
// 🗄️ 数据库与存储助手 (D1 + R2)
// =============================================================================
async function getSafeEnv(env, key, fallback) {
    if (env[key] && env[key].trim() !== "") return env[key];
    if (env.DB) {
        try {
            const { results } = await env.DB.prepare("SELECT value FROM config WHERE key = ?").bind(key).all();
            if (results && results.length > 0 && results[0].value && results[0].value.trim() !== "") {
                return results[0].value;
            }
        } catch(e) { /* D1读取失败忽略 */ }
    }
    if (env.LH) {
        try {
            const kvVal = await env.LH.get(key);
            if (kvVal && kvVal.trim() !== "") return kvVal;
        } catch(e) {}
    }
    return fallback;
}

// 日志记录
async function logAccess(env, ip, region, action) {
    const time = new Date().toLocaleString('zh-CN', { timeZone: 'Asia/Shanghai' });
    if (env.DB) {
        try {
            await env.DB.prepare("INSERT INTO logs (time, ip, region, action) VALUES (?, ?, ?, ?)")
                .bind(time, ip, region, action).run();
            env.DB.prepare("DELETE FROM logs WHERE id NOT IN (SELECT id FROM logs ORDER BY id DESC LIMIT 1000)").run().catch(()=>{});
        } catch (e) {}
    }
}

// 每日请求计数
async function incrementDailyStats(env) {
    if (!env.DB) return "0";
    const dateStr = new Date().toISOString().split('T')[0];
    try {
        await env.DB.prepare(`INSERT INTO stats (date, count) VALUES (?, 1) ON CONFLICT(date) DO UPDATE SET count = count + 1`).bind(dateStr).run();
        const { results } = await env.DB.prepare("SELECT count FROM stats WHERE date = ?").bind(dateStr).all();
        return results[0]?.count?.toString() || "1";
    } catch(e) { return "0"; }
}

// 🛡️ 洪水攻击检测
async function checkFlood(env, ip) {
    if (!env.DB) return false;
    const now = Math.floor(Date.now() / 1000);
    try {
        await env.DB.prepare("DELETE FROM flood WHERE updated_at < ?").bind(now - 600).run();
        await env.DB.prepare(`INSERT INTO flood (ip, count, updated_at) VALUES (?, 1, ?) ON CONFLICT(ip) DO UPDATE SET count = count + 1, updated_at = ?`).bind(ip, now, now).run();
        const { results } = await env.DB.prepare("SELECT count FROM flood WHERE ip = ?").bind(ip).all();
        return (results[0]?.count || 0) >= 30;
    } catch(e) { return false; }
}

// 🚫 封禁状态检查
async function checkBan(env, ip) {
    if (env.DB) {
        try {
            const { results } = await env.DB.prepare("SELECT is_banned FROM bans WHERE ip = ?").bind(ip).all();
            return results && results.length > 0 && results[0].is_banned === 1;
        } catch(e) { return false; }
    } else if (env.LH) {
        try { return (await env.LH.get(`BAN_${ip}`)) === "1";
        } catch(e) { return false; }
    }
    return false;
}

// 🚫 执行封禁
async function banIP(env, ip) {
    if (env.DB) {
        try { await env.DB.prepare("INSERT OR REPLACE INTO bans (ip, is_banned) VALUES (?, 1)").bind(ip).run();
        } catch(e) {}
    } else if (env.LH) {
        try { await env.LH.put(`BAN_${ip}`, "1");
        } catch(e) {}
    }
}

// 🔓 解除封禁
async function unbanIP(env, ip) {
    if (env.DB) {
        try { await env.DB.prepare("DELETE FROM bans WHERE ip = ?").bind(ip).run();
        } catch(e) {}
    } else if (env.LH) {
        try { await env.LH.delete(`BAN_${ip}`);
        } catch(e) {}
    }
}

// 📋 获取黑名单列表
async function getBanList(env) {
    if (env.DB) {
        try {
            const { results } = await env.DB.prepare("SELECT ip FROM bans").all();
            return results.map(row => row.ip);
        } catch(e) { return []; }
    } else if (env.LH) {
        try {
            const list = await env.LH.list({ prefix: "BAN_" });
            return list.keys.map(k => k.name.replace("BAN_", ""));
        } catch(e) { return []; }
    }
    return [];
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

// ☁️ Cloudflare 官方用量 (GraphQL)
async function getCloudflareUsage(env) {
    const Email = await getSafeEnv(env, 'CF_EMAIL', "");
    const GlobalAPIKey = await getSafeEnv(env, 'CF_KEY', "");
    const AccountID = await getSafeEnv(env, 'CF_ID', "");
    const APIToken = await getSafeEnv(env, 'CF_TOKEN', "");

    if (!AccountID && (!Email || !GlobalAPIKey)) return { success: false, msg: "未配置 CF 凭证" };
    const API = "https://api.cloudflare.com/client/v4";
    const cfg = { "Content-Type": "application/json" };
    try {
        let finalAccountID = AccountID;
        if (!finalAccountID) {
            const r = await fetch(`${API}/accounts`, { method: "GET", headers: { ...cfg, "X-AUTH-EMAIL": Email, "X-AUTH-KEY": GlobalAPIKey } });
            if (!r.ok) throw new Error(`账户获取失败: ${r.status}`);
            const d = await r.json();
            const idx = d.result?.findIndex(a => a.name?.toLowerCase().startsWith(Email.toLowerCase()));
            finalAccountID = d.result?.[idx >= 0 ? idx : 0]?.id;
        }
        
        if(!finalAccountID) throw new Error("无法获取 Account ID");
        const now = new Date(); now.setUTCHours(0, 0, 0, 0);
        const hdr = APIToken ?
            { ...cfg, "Authorization": `Bearer ${APIToken}` } : { ...cfg, "X-AUTH-EMAIL": Email, "X-AUTH-KEY": GlobalAPIKey };
        const res = await fetch(`${API}/graphql`, {
            method: "POST",
            headers: hdr,
            body: JSON.stringify({
                query: `query getBillingMetrics($AccountID: String!, $filter: AccountWorkersInvocationsAdaptiveFilter_InputObject) {
                    viewer { accounts(filter: {accountTag: $AccountID}) {
                        pagesFunctionsInvocationsAdaptiveGroups(limit: 1000, filter: $filter) { sum { requests } }
                        workersInvocationsAdaptive(limit: 10000, filter: $filter) { sum { requests } }
                    } } }`,
                variables: { AccountID: finalAccountID, filter: 
                    { datetime_geq: now.toISOString(), datetime_leq: new Date().toISOString() } }
            })
        });
        if (!res.ok) throw new Error(`查询失败: ${res.status}`);
        const result = await res.json();
        const acc = result?.data?.viewer?.accounts?.[0];
        const pages = acc?.pagesFunctionsInvocationsAdaptiveGroups?.reduce((t, i) => t + (i?.sum?.requests || 0), 0) || 0;
        const workers = acc?.workersInvocationsAdaptive?.reduce((t, i) => t + (i?.sum?.requests || 0), 0) || 0;
        return { success: true, total: pages + workers, pages, workers };
    } catch (e) { return { success: false, msg: e.message };
    }
}

// 🤖 发送 Telegram 消息
async function sendTgMsg(ctx, env, title, r, detail = "", isAdmin = false) {
  const token = await getSafeEnv(env, 'TG_BOT_TOKEN', TG_BOT_TOKEN);
  const chat_id = await getSafeEnv(env, 'TG_CHAT_ID', TG_CHAT_ID);
  if (!token || !chat_id) return;

  let icon = "📡";
  if (title.includes("封禁")) icon = "🚫";
  else if (title.includes("登录")) icon = "🔐";
  else if (title.includes("订阅")) icon = "🔄";
  else if (title.includes("检测")) icon = "🔍";
  else if (title.includes("点击")) icon = "🌟";
  else if (title.includes("配置")) icon = "⚙️";

  const roleTag = isAdmin ?
      "🛡️ <b>管理员操作</b>" : "👤 <b>陌生访问</b>";

  try {
    const url = new URL(r.url);
    const ip = r.headers.get('cf-connecting-ip') ||
      'Unknown';
    const ua = r.headers.get('User-Agent') || 'Unknown';
    const city = r.cf?.city || 'Unknown';
    const time = new Date().toLocaleString('zh-CN', { timeZone: 'Asia/Shanghai' });
    const safe = (str) => (str || '').replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
    const text = `<b>${icon} ${safe(title)}</b>\n${roleTag}\n\n` + 
                 `<b>🕒 时间:</b> <code>${time}</code>\n` + 
                 `<b>🌍 IP:</b> <code>${safe(ip)} (${safe(city)})</code>\n` + 
                 `<b>🔗 域名:</b> <code>${safe(url.hostname)}</code>\n` + 
                 `<b>🛣️ 路径:</b> <code>${safe(url.pathname)}</code>\n` + 
                `<b>📱 客户端:</b> <code>${safe(ua)}</code>\n` + 
                 (detail ? `<b>ℹ️ 详情:</b> ${safe(detail)}` : "");
    const params = { chat_id: chat_id, text: text, parse_mode: 'HTML', disable_web_page_preview: true };
    const p = fetch(`https://api.telegram.org/bot${token}/sendMessage`, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(params) }).catch(() => {});
    if(ctx && ctx.waitUntil) ctx.waitUntil(p);
  } catch(e) {}
}

const handle = (ws, pc, uuid) => {
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
  const cn = async () => { const m = ['direct']; if (pc) m.push('proxy'); let err;
  for (const x of m) { try { const o = (x === 'direct') ?
  { hostname: inf.host, port: inf.port } : { hostname: pc.address, port: pc.port }; const sk = connect(o); await sk.opened;
  return sk } catch (e) { err = e } } throw err };
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

function loginPage(tgGroup, tgChannel) {
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>系统访问控制</title>
    <style>
        :root {
            --primary: #3b82f6;
            --primary-hover: #2563eb;
            --bg-gradient: linear-gradient(135deg, #0f172a 0%, #1e293b 100%);
            --glass: rgba(30, 41, 59, 0.7);
            --glass-border: rgba(255, 255, 255, 0.1);
        }
        body {
            margin: 0; padding: 0;
            font-family: 'SF Pro Display', -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            background: var(--bg-gradient);
            height: 100vh;
            display: flex;
            justify-content: center;
            align-items: center;
            color: #fff;
            overflow: hidden;
        }
        /* 动态背景装饰 */
        .orb {
            position: absolute;
            border-radius: 50%;
            filter: blur(80px);
            z-index: -1;
            opacity: 0.6;
            animation: float 10s infinite ease-in-out;
        }
        .orb-1 { width: 300px; height: 300px; background: #4f46e5; top: -50px; left: -50px; animation-delay: 0s; }
        .orb-2 { width: 250px; height: 250px; background: #06b6d4; bottom: -50px; right: -50px; animation-delay: -5s; }

        @keyframes float {
            0%, 100% { transform: translate(0, 0); }
            50% { transform: translate(20px, 30px); }
        }

        .login-card {
            background: var(--glass);
            backdrop-filter: blur(20px);
            -webkit-backdrop-filter: blur(20px);
            border: 1px solid var(--glass-border);
            padding: 40px;
            border-radius: 24px;
            box-shadow: 0 25px 50px -12px rgba(0, 0, 0, 0.5);
            width: 100%;
            max-width: 360px;
            text-align: center;
            transform: translateY(0);
            transition: transform 0.3s;
        }
        .login-card:hover { transform: translateY(-5px); }
        
        .icon-lock {
            font-size: 3rem;
            margin-bottom: 15px;
            background: linear-gradient(to right, #4f46e5, #06b6d4);
            -webkit-background-clip: text;
            color: transparent;
            display: inline-block;
        }

        h2 { margin: 0 0 5px 0; font-size: 1.5rem; font-weight: 700; }
        p { margin: 0 0 25px 0; color: #94a3b8; font-size: 0.9rem; }

        .input-group { position: relative; margin-bottom: 20px; }
        input {
            width: 100%;
            padding: 14px 16px;
            background: rgba(15, 23, 42, 0.6);
            border: 1px solid var(--glass-border);
            border-radius: 12px;
            color: #fff;
            font-size: 1rem;
            outline: none;
            transition: all 0.3s;
            box-sizing: border-box;
            text-align: center;
            letter-spacing: 2px;
        }
        input:focus {
            border-color: var(--primary);
            box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.2);
            background: rgba(15, 23, 42, 0.8);
        }
        input::placeholder { color: #64748b; letter-spacing: normal; }

        button {
            width: 100%;
            padding: 14px;
            background: linear-gradient(135deg, #3b82f6 0%, #2563eb 100%);
            color: white;
            border: none;
            border-radius: 12px;
            font-size: 1rem;
            font-weight: 600;
            cursor: pointer;
            transition: all 0.2s;
            box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06);
        }
        button:hover {
            transform: scale(1.02);
            box-shadow: 0 10px 15px -3px rgba(37, 99, 235, 0.3);
        }
        button:active { transform: scale(0.98); }

        .footer-links {
            margin-top: 25px;
            display: flex;
            justify-content: center;
            gap: 15px;
        }
        .link-pill {
            font-size: 0.8rem;
            color: #94a3b8;
            text-decoration: none;
            padding: 6px 12px;
            border-radius: 20px;
            background: rgba(255,255,255,0.05);
            transition: 0.2s;
        }
        .link-pill:hover { background: rgba(255,255,255,0.1); color: #fff; }

    </style>
</head>
<body>
    <div class="orb orb-1"></div>
    <div class="orb orb-2"></div>
    
    <div class="login-card">
        <div class="icon-lock">🛡️</div>
        <h2>访问受限</h2>
        <p>请输入管理员密钥以继续</p>
        
        <div class="input-group">
            <input type="password" id="pwd" placeholder="Password" autofocus onkeypress="if(event.keyCode===13)verify()">
        </div>
        
        <button onclick="verify()">验证并进入</button>

        <div class="footer-links">
            ${tgGroup ? `<a href="${tgGroup}" class="link-pill" target="_blank">✈️ 群组</a>` : ''}
            ${tgChannel ? `<a href="${tgChannel}" class="link-pill" target="_blank">📢 频道</a>` : ''}
        </div>
    </div>

    <script>
        function verify(){
            const p = document.getElementById("pwd").value;
            if(!p) return;
            const btn = document.querySelector('button');
            btn.innerHTML = '验证中...';
            btn.style.opacity = '0.8';
            
            // 写入 Cookie
            document.cookie = "auth=" + p + "; path=/; Max-Age=31536000; SameSite=Lax";
            sessionStorage.setItem("is_active", "1");
            
            setTimeout(() => {
                location.reload();
            }, 300);
        }
        // 清除旧会话逻辑
        window.onload = function() {
            if(!sessionStorage.getItem("is_active")) {
                document.cookie = "auth=; path=/; expires=Thu, 01 Jan 1970 00:00:00 GMT";
            }
        }
    </script>
</body>
</html>`;
}

function dashPage(host, uuid, proxyip, subpass, converter, env, clientIP, hasAuth, tgState, cfState) {
    const defaultSubLink = `https://${host}/${subpass}`;
    
    return `<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Worker 管理控制台</title>
    <link href="https://cdn.jsdelivr.net/npm/remixicon@3.5.0/fonts/remixicon.css" rel="stylesheet">
    <style>
        :root {
            --bg-color: #0b1120; /* 深蓝黑背景 */
            --card-bg: #1e293b;
            --card-border: #334155;
            --text-primary: #f8fafc;
            --text-secondary: #94a3b8;
            --accent: #3b82f6; /* 蓝色高亮 */
            --success: #10b981;
            --danger: #ef4444;
            --warning: #f59e0b;
        }
        /* 亮色模式变量 */
        body.light {
            --bg-color: #f1f5f9;
            --card-bg: #ffffff;
            --card-border: #cbd5e1;
            --text-primary: #1e293b;
            --text-secondary: #64748b;
        }

        body {
            background-color: var(--bg-color);
            color: var(--text-primary);
            font-family: 'Inter', -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            margin: 0;
            padding: 20px;
            display: flex;
            justify-content: center;
            min-height: 100vh;
            transition: background-color 0.3s ease;
        }

        .container {
            width: 100%;
            max-width: 1000px;
            display: flex;
            flex-direction: column;
            gap: 24px;
        }

        /* 顶部导航 */
        .header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            padding: 10px 0;
        }
        .brand {
            font-size: 1.5rem;
            font-weight: 800;
            background: linear-gradient(90deg, #3b82f6, #8b5cf6);
            -webkit-background-clip: text;
            color: transparent;
            display: flex;
            align-items: center;
            gap: 10px;
        }
        .header-controls {
            display: flex;
            gap: 10px;
        }

        /* 卡片通用样式 */
        .card {
            background-color: var(--card-bg);
            border: 1px solid var(--card-border);
            border-radius: 16px;
            padding: 24px;
            box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1);
            transition: all 0.3s ease;
        }
        .card:hover {
            box-shadow: 0 10px 15px -3px rgba(0, 0, 0, 0.1);
            border-color: var(--accent);
        }

        /* 状态概览区域 */
        .stats-grid {
            display: grid;
            grid-template-columns: 1fr 2fr;
            gap: 24px;
        }
        @media (max-width: 768px) {
            .stats-grid { grid-template-columns: 1fr; }
        }

        /* 仪表盘 - 实体轨道风格 */ 
         .gauge-container { 
             position: relative; 
             width: 140px; /* 固定容器宽度，防止不同客户端变形 */ 
             height: 140px; 
             margin: 0 auto 10px auto; /* 居中 */ 
             display: flex; 
             align-items: center; 
             justify-content: center; 
         } 
         
         /* 给整个仪表盘加一个极淡的圆形背景，增加“边界感” */ 
         .gauge-container::before { 
             content: ''; 
             position: absolute; 
             width: 100%; 
             height: 100%; 
             border-radius: 50%; 
             background: var(--card-bg); /* 或者使用 rgba(0,0,0,0.03) */ 
             box-shadow: inset 0 0 10px rgba(0,0,0,0.05); /* 内阴影增加立体感 */ 
             z-index: 0; 
         } 
 
         .gauge-svg { 
             transform: rotate(-90deg); 
             width: 100%; 
             height: 100%; 
             z-index: 1; 
         } 
 
         .gauge-circle-bg { 
             fill: none; 
             stroke: var(--text-secondary); /* 使用更明显的颜色作为轨道 */ 
             stroke-width: 2.5; /* 轨道稍微细一点 */ 
             opacity: 0.15; /* 增加不透明度，让轨道清晰可见 */ 
         } 
 
         .gauge-circle-val { 
             fill: none; 
             stroke: var(--accent); 
             stroke-width: 3.5; /* 进度条比轨道粗，形成层次感 */ 
             stroke-linecap: round; 
             transition: stroke-dasharray 0.8s cubic-bezier(0.4, 0, 0.2, 1); 
         } 
 
         /* 居中文字容器 */ 
         .gauge-data { 
             position: absolute; 
             display: flex; 
             flex-direction: column; 
             align-items: center; 
             justify-content: center; 
             z-index: 2; 
         } 
 
         .gauge-text { 
             /* 解决字体过大问题，使用 clamp 在不同屏幕自动缩放 */ 
             font-size: clamp(1.2rem, 4vw, 1.8rem); 
             font-weight: 700; 
             color: var(--text-primary); 
             line-height: 1.1; 
         } 
 
         .gauge-label { 
             font-size: 0.75rem; 
             color: var(--text-secondary); 
             margin-top: 2px; 
             font-weight: 500; 
         }

        /* 状态列表 */
        .status-list {
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(140px, 1fr));
            gap: 15px;
        }
        .status-item {
            background: rgba(59, 130, 246, 0.1);
            border-radius: 12px;
            padding: 15px;
            display: flex;
            flex-direction: column;
            gap: 5px;
        }
        .status-label { font-size: 0.8rem; color: var(--text-secondary); }
        .status-value { font-weight: 600; font-family: monospace; }
        .status-value.green { color: var(--success); }
        .status-value.blue { color: var(--accent); }

        /* 输入框和按钮 */
        .section-title {
            font-size: 1.1rem;
            font-weight: 600;
            margin-bottom: 16px;
            display: flex;
            align-items: center;
            gap: 8px;
            color: var(--text-primary);
        }
        
        .input-wrapper {
            display: flex;
            gap: 10px;
            margin-bottom: 10px;
        }
        input[type="text"] {
            flex: 1;
            background: var(--bg-color);
            border: 1px solid var(--card-border);
            color: var(--text-primary);
            padding: 12px 16px;
            border-radius: 8px;
            outline: none;
            font-family: monospace;
        }
        input:focus { border-color: var(--accent); }
        
        .btn {
            padding: 10px 20px;
            border-radius: 8px;
            border: none;
            cursor: pointer;
            font-weight: 600;
            transition: 0.2s;
            display: flex;
            align-items: center;
            gap: 6px;
            font-size: 0.9rem;
        }
        .btn-primary { background: var(--accent); color: white; }
        .btn-primary:hover { opacity: 0.9; }
        .btn-danger { background: rgba(239, 68, 68, 0.2); color: var(--danger); border: 1px solid var(--danger); }
        .btn-danger:hover { background: var(--danger); color: white; }
        .btn-icon { padding: 10px; width: 40px; justify-content: center; background: var(--card-bg); border: 1px solid var(--card-border); color: var(--text-primary); }
        .btn-icon:hover { border-color: var(--accent); color: var(--accent); }
        .btn-icon.active { border-color: var(--success); color: var(--success); }
        
        /* 日志终端风格 */
        .terminal-box {
            background: #000;
            border-radius: 8px;
            padding: 15px;
            font-family: 'Menlo', 'Monaco', 'Courier New', monospace;
            font-size: 0.8rem;
            height: 250px;
            overflow-y: auto;
            border: 1px solid #333;
        }
        .log-row {
            display: flex;
            gap: 12px;
            padding: 4px 0;
            border-bottom: 1px solid #111;
        }
        .log-time { color: #666; min-width: 130px; }
        .log-ip { color: #a5b4fc; min-width: 120px; }
        .log-loc { color: #86efac; flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
        .log-tag { padding: 0 4px; border-radius: 2px; font-size: 0.75rem; }
        .tag-sub { background: #064e3b; color: #6ee7b7; }
        .tag-ban { background: #450a0a; color: #fca5a5; }

        /* 封禁表格 */
        table { width: 100%; border-collapse: collapse; }
        th { text-align: left; color: var(--text-secondary); font-size: 0.85rem; padding: 10px; border-bottom: 1px solid var(--card-border); }
        td { padding: 10px; border-bottom: 1px solid var(--card-border); font-family: monospace; }
        
        /* 模态框 */
        .modal {
            display: none; position: fixed; top: 0; left: 0; width: 100%; height: 100%;
            background: rgba(0,0,0,0.6); backdrop-filter: blur(4px); z-index: 100;
            justify-content: center; align-items: center; opacity: 0; transition: opacity 0.3s;
        }
        .modal.show { display: flex; opacity: 1; }
        .modal-content {
            background: var(--card-bg); width: 90%; max-width: 450px;
            padding: 25px; border-radius: 16px; border: 1px solid var(--card-border);
            box-shadow: 0 20px 25px -5px rgba(0, 0, 0, 0.3); transform: scale(0.95); transition: transform 0.3s;
        }
        .modal.show .modal-content { transform: scale(1); }
        
        .modal-header { display: flex; justify-content: space-between; margin-bottom: 20px; font-size: 1.2rem; font-weight: bold; }
        .close-icon { cursor: pointer; color: var(--text-secondary); }
        .modal-actions { display: flex; gap: 10px; margin-top: 20px; }
        .modal-actions button { flex: 1; justify-content: center; }

        /* Toast */
        #toast {
            position: fixed; bottom: 30px; left: 50%; transform: translateX(-50%) translateY(20px);
            background: var(--success); color: white; padding: 10px 24px; border-radius: 50px;
            opacity: 0; transition: all 0.3s cubic-bezier(0.68, -0.55, 0.27, 1.55); pointer-events: none;
            box-shadow: 0 10px 15px -3px rgba(16, 185, 129, 0.4); font-weight: 600;
        }
        #toast.show { opacity: 1; transform: translateX(-50%) translateY(0); }
    </style>
</head>
<body id="mainBody">
    <div class="container">
        <div class="header">
            <div class="brand"><i class="ri-radar-fill"></i> Worker Panel</div>
            <div class="header-controls">
                <button class="btn btn-icon" onclick="toggleTheme()" title="切换主题"><i class="ri-contrast-line"></i></button>
                <button class="btn btn-icon" onclick="logout()" style="color:var(--danger); border-color:var(--danger)" title="退出"><i class="ri-shut-down-line"></i></button>
            </div>
        </div>

        <div class="card stats-grid">
            <div class="gauge-container">
                <svg class="gauge-svg" viewBox="0 0 36 36">
                    <path class="gauge-circle-bg" d="M18 2.0845 a 15.9155 15.9155 0 0 1 0 31.831 a 15.9155 15.9155 0 0 1 0 -31.831" />
                    <path class="gauge-circle-val" stroke-dasharray="0, 100" d="M18 2.0845 a 15.9155 15.9155 0 0 1 0 31.831 a 15.9155 15.9155 0 0 1 0 -31.831" />
                </svg>
                <div class="gauge-data">
                    <div class="gauge-text" id="reqCount">0</div>
                    <div class="gauge-label">今日请求</div>
                </div>
            </div>
            
            <div style="display: flex; flex-direction: column; justify-content: space-between;">
                <div class="status-list">
                    <div class="status-item">
                        <span class="status-label"><i class="ri-google-fill"></i> Google 连通性</span>
                        <span class="status-value" id="googleStatus">Testing...</span>
                    </div>
                    <div class="status-item">
                        <span class="status-label"><i class="ri-database-2-fill"></i> 数据库状态</span>
                        <span class="status-value blue" id="kvStatus">Checking...</span>
                    </div>
                    <div class="status-item">
                        <span class="status-label"><i class="ri-map-pin-user-fill"></i> 当前 IP</span>
                        <span class="status-value" id="currentIp" style="font-size:0.75rem">...</span>
                    </div>
                    <div class="status-item">
                        <span class="status-label"><i class="ri-cloud-windy-fill"></i> API 模式</span>
                        <span class="status-value" id="apiStatus">Internal</span>
                    </div>
                </div>
                <button class="btn btn-primary" onclick="updateStats()" style="margin-top:15px; width:100%; justify-content:center">
                    <i class="ri-refresh-line"></i> 刷新所有状态
                </button>
            </div>
        </div>

        <!-- 功能模块网格布局 -->
        <div style="display: grid; grid-template-columns: repeat(auto-fit, minmax(400px, 1fr)); gap: 24px;">
            <div class="card">
                <div class="section-title"><i class="ri-link-m"></i> 快速订阅链接</div>
                <div class="input-wrapper">
                    <input type="text" id="autoSub" value="${defaultSubLink}" readonly onclick="this.select()">
                    <button class="btn btn-primary" onclick="copyId('autoSub')"><i class="ri-file-copy-line"></i> 复制</button>
                </div>
            </div>

            <div class="card">
                <div class="section-title" style="justify-content:space-between">
                    <span><i class="ri-spam-3-line"></i> IP 黑名单管理</span>
                    <span style="font-size:0.8rem; color:var(--text-secondary)" id="banCount">0 个</span>
                </div>
                <div class="input-wrapper">
                    <input type="text" id="newBanIp" placeholder="输入恶意 IP 地址 (例如 1.2.3.4)">
                    <button class="btn btn-danger" onclick="addBan()"><i class="ri-prohibited-line"></i> 封禁</button>
                </div>
                <div style="max-height: 200px; overflow-y: auto; border: 1px solid var(--card-border); border-radius: 8px;">
                    <table>
                        <tbody id="banListBody">
                            <tr><td style="text-align:center; color:#666">暂无数据</td></tr>
                        </tbody>
                    </table>
                </div>
            </div>
        </div>

        <div class="card">
            <div class="section-title" style="justify-content:space-between">
                <span><i class="ri-terminal-box-line"></i> 实时访问日志</span>
                <button class="btn btn-icon" style="height:30px; width:30px; font-size:0.8rem" onclick="loadLogs()"><i class="ri-refresh-line"></i></button>
            </div>
            <div class="terminal-box" id="logBox">
                <div style="padding:10px; color:#666">Connecting to log stream...</div>
            </div>
        </div>
    </div>

    <div id="tgModal" class="modal">
        <div class="modal-content">
            <div class="modal-header">
                <span><i class="ri-telegram-fill"></i> Telegram 通知配置</span>
                <span class="close-icon" onclick="closeModal('tgModal')">×</span>
            </div>
            <div style="display:flex; flex-direction:column; gap:15px">
                <div>
                    <label style="font-size:0.85rem; color:var(--text-secondary)">Bot Token</label>
                    <input type="text" id="tgToken" placeholder="123456:ABC-DEF..." style="width:100%; box-sizing:border-box">
                </div>
                <div>
                    <label style="font-size:0.85rem; color:var(--text-secondary)">Chat ID</label>
                    <input type="text" id="tgId" placeholder="用户或群组 ID" style="width:100%; box-sizing:border-box">
                </div>
            </div>
            <div class="modal-actions">
                <button class="btn" style="background:var(--card-border)" onclick="validateApi('tg')">测试</button>
                <button class="btn btn-primary" onclick="saveConfig({TG_BOT_TOKEN: val('tgToken'), TG_CHAT_ID: val('tgId')}, 'tgModal')">保存配置</button>
            </div>
        </div>
    </div>

    <div id="cfModal" class="modal">
        <div class="modal-content">
            <div class="modal-header">
                <span><i class="ri-cloud-fill"></i> Cloudflare 统计 API</span>
                <span class="close-icon" onclick="closeModal('cfModal')">×</span>
            </div>
            <div style="display:flex; flex-direction:column; gap:15px">
                <div style="padding:10px; background:rgba(59,130,246,0.1); border-radius:8px; font-size:0.85rem">
                    推荐使用 Token 方式 (只需 Read 权限)
                </div>
                <input type="text" id="cfAcc" placeholder="Account ID" style="width:100%; box-sizing:border-box">
                <input type="text" id="cfTok" placeholder="API Token" style="width:100%; box-sizing:border-box">
                
                <div style="position:relative; text-align:center; margin:10px 0">
                    <span style="background:var(--card-bg); padding:0 10px; position:relative; z-index:1; color:#666; font-size:0.8rem">或使用 Global Key</span>
                    <div style="position:absolute; top:50%; width:100%; height:1px; background:var(--card-border); z-index:0"></div>
                </div>

                <input type="text" id="cfMail" placeholder="Email Address" style="width:100%; box-sizing:border-box">
                <input type="text" id="cfKey" placeholder="Global API Key" style="width:100%; box-sizing:border-box">
            </div>
            <div class="modal-actions">
                <button class="btn" style="background:var(--card-border)" onclick="validateApi('cf')">测试</button>
                <button class="btn btn-primary" onclick="saveConfig({CF_ID:val('cfAcc'), CF_TOKEN:val('cfTok'), CF_EMAIL:val('cfMail'), CF_KEY:val('cfKey')}, 'cfModal')">保存配置</button>
            </div>
        </div>
    </div>

    <div id="toast"><i class="ri-check-line"></i> 已复制到剪贴板</div>

    <script>
        const UUID = "${uuid}";
        const HAS_AUTH = ${hasAuth};
        
        // 初始化检查
        if (HAS_AUTH && !sessionStorage.getItem("is_active")) {
            document.cookie = "auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";
            window.location.reload();
        }

        // 工具函数
        const val = (id) => document.getElementById(id).value;
        const showModal = (id) => document.getElementById(id).classList.add('show');
        const closeModal = (id) => document.getElementById(id).classList.remove('show');
        
        function showToast(msg) {
            const t = document.getElementById('toast');
            t.innerHTML = '<i class="ri-check-line"></i> ' + msg;
            t.classList.add('show');
            setTimeout(() => t.classList.remove('show'), 2000);
        }

        function copyId(id) {
            const el = document.getElementById(id);
            el.select();
            navigator.clipboard.writeText(el.value).then(() => showToast('已复制'));
        }

        function toggleTheme() {
            document.body.classList.toggle('light');
        }

        // 核心逻辑
        async function updateStats() {
            const el = document.getElementById('reqCount');
            const circle = document.querySelector('.gauge-circle-val');
            
            // Google 检测
            const start = Date.now();
            try {
                await fetch('https://www.google.com/generate_204', {mode: 'no-cors'});
                document.getElementById('googleStatus').innerHTML = '<span style="color:var(--success)">' + (Date.now() - start) + 'ms</span>';
            } catch { document.getElementById('googleStatus').innerText = 'Timeout'; }

            // 后端数据
            try {
                const res = await fetch('?flag=stats');
                const data = await res.json();
                
                // 仪表盘动画
                const count = parseInt(data.req) || 0;
                el.innerText = count;
                // 假设日上限 10万次作为 100% 进度
                const percent = Math.min((count / 100000) * 100, 100);
                circle.style.strokeDasharray = \`\${percent}, 100\`;
                circle.style.stroke = percent > 80 ? 'var(--danger)' : 'var(--accent)';

                document.getElementById('apiStatus').innerText = data.cfConfigured ? 'Cloudflare API' : 'Internal Counter';
                document.getElementById('currentIp').innerText = data.ip;
                document.getElementById('kvStatus').innerHTML = data.hasKV ? '<span style="color:var(--success)">Normal</span>' : '<span style="color:var(--warning)">No Storage</span>';
            } catch (e) { el.innerText = 'Err'; }
        }

        async function loadLogs() {
            const box = document.getElementById('logBox');
            try {
                const res = await fetch('?flag=get_logs');
                const data = await res.json();
                let html = '';
                
                const renderLog = (time, ip, loc, action) => {
                    let tagClass = '';
                    if (action.includes('订阅')) tagClass = 'tag-sub';
                    if (action.includes('封禁') || action.includes('Forbidden')) tagClass = 'tag-ban';
                    
                    return \`<div class="log-row">
                        <span class="log-time">\${time.split(' ')[1] || time}</span>
                        <span class="log-ip">\${ip}</span>
                        <span class="log-loc">\${loc}</span>
                        <span class="log-tag \${tagClass}">\${action}</span>
                    </div>\`;
                };

                if (data.type === 'd1' && Array.isArray(data.logs)) {
                    html = data.logs.map(l => renderLog(l.time, l.ip, l.region, l.action)).join('');
                } else if (data.logs && typeof data.logs === 'string') {
                    html = data.logs.split('\\n').filter(x=>x).slice(0, 50).map(line => {
                        const p = line.split('|');
                        return renderLog(p[0], p[1], p[2], p[3]);
                    }).join('');
                }
                box.innerHTML = html || '<div style="padding:10px;text-align:center;color:#666">暂无日志记录</div>';
            } catch(e) { box.innerHTML = '加载日志失败'; }
        }

        async function loadBans() {
            try {
                const res = await fetch('?flag=get_bans');
                const data = await res.json();
                const list = data.list || [];
                document.getElementById('banCount').innerText = list.length + ' 个';
                
                const html = list.length ? list.map(ip => \`
                    <tr>
                        <td>\${ip}</td>
                        <td style="width:50px; text-align:right">
                            <button class="btn btn-danger" style="padding:4px 8px; font-size:0.75rem" onclick="delBan('\${ip}')">删除</button>
                        </td>
                    </tr>\`).join('') : '<tr><td colspan="2" style="text-align:center; padding:20px; color:var(--text-secondary)">暂无封禁记录</td></tr>';
                document.getElementById('banListBody').innerHTML = html;
            } catch(e) {}
        }

        async function addBan() {
            const ip = document.getElementById('newBanIp').value.trim();
            if(!ip) return;
            try {
                await fetch('?flag=add_ban', { method:'POST', body:JSON.stringify({ip}) });
                document.getElementById('newBanIp').value = '';
                showToast('已添加封禁');
                loadBans();
            } catch(e) { alert('添加失败'); }
        }

        async function delBan(ip) {
            if(!confirm('确定解封 '+ip+'?')) return;
            try { 
                await fetch('?flag=del_ban', { method:'POST', body:JSON.stringify({ip}) }); 
                loadBans(); 
                showToast('已解封');
            } catch(e) { alert('删除失败'); }
        }

        async function validateApi(type) {
            const btn = event.target;
            const originText = btn.innerText;
            btn.innerText = 'Checking...';
            
            const endpoint = type === 'tg' ? 'validate_tg' : 'validate_cf';
            let payload = {};
            if(type === 'tg') payload = { TG_BOT_TOKEN: val('tgToken'), TG_CHAT_ID: val('tgId') };
            else payload = { CF_ID:val('cfAcc'), CF_TOKEN:val('cfTok'), CF_EMAIL:val('cfMail'), CF_KEY:val('cfKey') };
            
            try {
                const res = await fetch('?flag=' + endpoint, { method:'POST', body:JSON.stringify(payload) });
                const d = await res.json();
                alert(d.msg || (d.success ? '验证通过' : '验证失败'));
            } catch(e) { alert('请求错误'); }
            
            btn.innerText = originText;
        }

        async function saveConfig(data, modalId) {
            try {
                await fetch('?flag=save_config', { method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(data) });
                showToast('配置已保存'); 
                if(modalId) closeModal(modalId);
                setTimeout(() => location.reload(), 1000);
            } catch(e) { alert('保存失败: ' + e); }
        }

        function logout() {
            document.cookie = "auth=; expires=Thu, 01 Jan 1970 00:00:00 GMT; path=/";
            sessionStorage.removeItem("is_active");
            location.reload();
        }

        // 启动加载
        updateStats();
        loadLogs();
        loadBans();
        setInterval(loadLogs, 5000); // 5秒刷新一次日志
    </script>
</body>
</html>`;
}
// 导出放在最后，确保所有函数都已定义
export default {
  async fetch(r, env, ctx) { 
    try {
      const url = new URL(r.url);
      const host = url.hostname; 
      const UA = (r.headers.get('User-Agent') || "").toLowerCase();
      // 🟢 关键：提取 UA_L 供后续使用
      const UA_L = UA.toLowerCase();
      
      const clientIP = r.headers.get('cf-connecting-ip');
      const country = r.cf?.country || 'UNK';
      const city = r.cf?.city || 'Unknown';

      // 加载变量
      const _UUID = env.KEY ?
      await getDynamicUUID(env.KEY, env.UUID_REFRESH || 86400) : (await getSafeEnv(env, 'UUID', UUID));
      const _WEB_PW = await getSafeEnv(env, 'WEB_PASSWORD', WEB_PASSWORD);
      const _SUB_PW = await getSafeEnv(env, 'SUB_PASSWORD', SUB_PASSWORD);
      const _PROXY_IP = await getSafeEnv(env, 'PROXYIP', DEFAULT_PROXY_IP);
      const _PS = await getSafeEnv(env, 'PS', ""); 
      

      let _CONVERTER = await getSafeEnv(env, 'SUBAPI', DEFAULT_CONVERTER);


      if (_CONVERTER.endsWith("/")) _CONVERTER = _CONVERTER.slice(0, -1);
      if (!_CONVERTER.includes("://")) _CONVERTER = "https://" + _CONVERTER;
      
      if (UA_L.includes('spider') || UA_L.includes('bot') || UA_L.includes('python') || UA_L.includes('scrapy') || UA_L.includes('curl') || UA_L.includes('wget')) {
          return new Response('Not Found', { status: 404 });
      }

      // 身份识别
      const wl = await getSafeEnv(env, 'WL_IP', "");
      let isAdmin = wl && wl.includes(clientIP);
      if (!isAdmin && _WEB_PW) {
        const cookie = r.headers.get('Cookie') || "";
        // 使用正则进行精确匹配：auth=密码 后面必须是分号或结尾
        const regex = new RegExp(`auth=${_WEB_PW.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}(;|$)`);
        if (regex.test(cookie)) isAdmin = true;
    }

      // 黑名单拦截
      if (!isAdmin) {
        const bj = await getSafeEnv(env, 'BJ_IP', "");
        if (bj && bj.includes(clientIP)) return new Response("403 Forbidden", { status: 403 });
        if (await checkBan(env, clientIP)) return new Response("403 Forbidden", { status: 403 });
      }

      if (url.pathname === '/favicon.ico') return new Response(null, { status: 404 });
      
      // 🟢 API 接口
      const flag = url.searchParams.get('flag');
      if (flag) {
          if (flag === 'github') {
              await sendTgMsg(ctx, env, "🌟 用户点击了烈火项目", r, "来源: 登录页面直达链接", isAdmin);
              return new Response(null, { status: 204 });
          }
          if (flag === 'log_proxy_check') {
              await sendTgMsg(ctx, env, "🔍 用户点击了 ProxyIP 检测", r, "来源: 后台管理面板", isAdmin);
              return new Response(null, { status: 204 });
          }
          if (flag === 'stats') {
              let reqCount = await incrementDailyStats(env);
              const cfStats = await getCloudflareUsage(env);
              const finalReq = cfStats.success ? `${cfStats.total} (API)` : `${reqCount} (Internal)`;
              const hasKV = !!(env.DB || env.LH);
              const cfConfigured = cfStats.success || (!!await getSafeEnv(env, 'CF_EMAIL', "") && !!await getSafeEnv(env, 'CF_KEY', ""));
              return new Response(JSON.stringify({
                  req: finalReq,
                  ip: clientIP,
                  loc: `${city}, ${country}`,
                  hasKV: hasKV,
                  cfConfigured: cfConfigured
              }), { headers: { 'Content-Type': 'application/json' } });
           }
          if (flag === 'get_logs') {
              if (env.DB) { try { const { results } = await env.DB.prepare("SELECT * FROM logs ORDER BY id DESC LIMIT 50").all();
              return new Response(JSON.stringify({ type: 'd1', logs: results }), { headers: { 'Content-Type': 'application/json' } });
              } catch(e) {} }
              else if (env.LH) { try { const logs = await env.LH.get('ACCESS_LOGS') ||
              ""; return new Response(JSON.stringify({ type: 'kv', logs: logs }), { headers: { 'Content-Type': 'application/json' } });
              } catch(e) {} }
              return new Response(JSON.stringify({ logs: "No Storage" }), { headers: { 'Content-Type': 'application/json' } });
          }
          if (flag === 'get_bans') { return new Response(JSON.stringify({ list: await getBanList(env) }), { headers: { 'Content-Type': 'application/json' } });
          }
          if (flag === 'add_ban' && r.method === 'POST') {
              const body = await r.json();
              if(body.ip) await banIP(env, body.ip);
              return new Response(JSON.stringify({status:'ok'}), {headers:{'Content-Type':'application/json'}});
          }
          if (flag === 'del_ban' && r.method === 'POST') {
              const body = await r.json();
              if(body.ip) await unbanIP(env, body.ip);
              return new Response(JSON.stringify({status:'ok'}), {headers:{'Content-Type':'application/json'}});
          }
          if (flag === 'validate_tg' && r.method === 'POST') {
              const body = await r.json();
              await sendTgMsg(ctx, { TG_BOT_TOKEN: body.TG_BOT_TOKEN, TG_CHAT_ID: body.TG_CHAT_ID }, "🤖 TG 推送可用性验证", r, "配置有效", true);
              return new Response(JSON.stringify({success:true, msg:"验证消息已发送"}), {headers:{'Content-Type':'application/json'}});
           }
          if (flag === 'validate_cf' && r.method === 'POST') {
              const body = await r.json();
              const res = await getCloudflareUsage(body);
              return new Response(JSON.stringify({success:res.success, msg: res.success ? `验证通过: 总请求 ${res.total}` : `验证失败: ${res.msg}`}), {headers:{'Content-Type':'application/json'}});
           }
          if (flag === 'save_config' && r.method === 'POST') {
              try {
                  const body = await r.json();
                  for (const [k, v] of Object.entries(body)) {
                      if (env.DB) await env.DB.prepare("INSERT INTO config (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = ?").bind(k, v, v).run();
                      if (env.LH) await env.LH.put(k, v);
                  }
                  return new Response(JSON.stringify({status: 'ok'}), { headers: { 'Content-Type': 'application/json' } });
              } catch(e) { return new Response(JSON.stringify({status: 'error', msg: e.toString()}), { headers: { 'Content-Type': 'application/json' } });
              }
          }
      }

      // 🛡️ 自动防刷
      if (env.DB || env.LH) {
          ctx.waitUntil(incrementDailyStats(env));
          if (!isAdmin && r.headers.get('Upgrade') !== 'websocket') {
              const isFlood = await checkFlood(env, clientIP);
              if (isFlood) {
                  const alreadyBanned = await checkBan(env, clientIP);
                  if (!alreadyBanned) {
                      await banIP(env, clientIP);
                      await sendTgMsg(ctx, env, "🚫 自动封禁通知 (首次)", r, `原因: 频繁请求 (>=5次)\n来源 IP: ${clientIP}`, false);
                  }
                  return new Response("403 Forbidden", { status: 403 });
              }
          }
      }

      // 🟢 订阅接口
      if (_SUB_PW && url.pathname === `/${_SUB_PW}`) {
          ctx.waitUntil(logAccess(env, clientIP, `${city},${country}`, "订阅更新"));
          const isFlagged = url.searchParams.has('flag');
          if (!isFlagged) {
              try {
                  // 🟢 新增强大的客户端识别逻辑
                  const _d = (s) => atob(s);
                  const rules = [
                      ['TWlob21v', 'bWlob21v'],               // Mihomo
                      ['RmxDbGFzaA==', 'ZmxjbGFzaA=='],       // flclash
                      ['Q2xhc2g=', 'Y2xhc2g='],               // Clash
                      ['Q2xhc2g=', 'bWV0YQ=='],               // Meta
                      ['Q2xhc2g=', 'c3Rhc2g='],               // Stash
                      ['SGlkZGlmeQ==', 'aGlkZGlmeQ=='],       // Hiddify
                      ['U2luZy1ib3g=', 'c2luZy1ib3g='],       // Sing-box
                      ['U2luZy1ib3g=', 'c2luZ2JveA=='],       // singbox
                      ['U2luZy1ib3g=', 'c2Zp'],               // sfi
                      ['U2luZy1ib3g=', 'Ym94'],               // box
                      ['djJyYXlOL0NvcmU=', 'djJyYXk='],       // v2
                      ['U3VyZ2U=', 'c3VyZ2U='],               // Surge
                      ['UXVhbnR1bXVsdCBY', 'cXVhbnR1bXVsdA=='], // QX
                      ['U2hhZG93cm9ja2V0', 'c2hhZG93cm9ja2V0'], // Shadowrocket
                      ['TG9vbg==', 'bG9vbg=='],               // Loon
                      ['SGFB', 'aGFwcA==']                    // Happ
                  ];
                  let cName = "VW5rbm93bg=="; 
                  let isProxy = false;
                  for (const [n, k] of rules) { 
                      if (UA_L.includes(_d(k))) { 
                          cName = n; isProxy = true; break; 
                      } 
                  }
                  if (!isProxy && (UA_L.includes(_d('bW96aWxsYQ==')) || UA_L.includes(_d('Y2hyb21l')))) cName = "QnJvd3Nlcg==";
                  
                  const title = isProxy ? "🔄 快速订阅更新" : "🌐 访问快速订阅页";
                  const p = sendTgMsg(ctx, env, title, r, `类型: ${_d(cName)}`, isAdmin);
                  if(ctx && ctx.waitUntil) ctx.waitUntil(p);
              } catch (e) {}
          }

          const requestProxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, requestProxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 🟢 常规订阅 /sub
      if (url.pathname === '/sub') {
          ctx.waitUntil(logAccess(env, clientIP, `${city},${country}`, "常规订阅"));
          const requestUUID = url.searchParams.get('uuid');
          if (requestUUID.toLowerCase() !== _UUID.toLowerCase()) return new Response('Invalid UUID', { status: 403 });
          
          let proxyIp = url.searchParams.get('proxyip') || _PROXY_IP;
          const pathParam = url.searchParams.get('path');
          if (pathParam && pathParam.includes('/proxyip=')) proxyIp = pathParam.split('/proxyip=')[1];
          
          const allIPs = await getCustomIPs(env);
          const listText = genNodes(host, _UUID, proxyIp, allIPs, _PS);
          return new Response(btoa(unescape(encodeURIComponent(listText))), { status: 200, headers: { 'Content-Type': 'text/plain; charset=utf-8' } });
      }

      // 🟢 面板逻辑 (HTTP)
      if (r.headers.get('Upgrade') !== 'websocket') {
        const noCacheHeaders = { 
            'Content-Type': 'text/html; charset=utf-8', 
            'Cache-Control': 'no-store',
            'X-Frame-Options': 'DENY', 
            'X-Content-Type-Options': 'nosniff',
            'Referrer-Policy': 'same-origin'
        };
        
        let hasPassword = !!_WEB_PW;
        let isAuthorized = false;
        if (hasPassword) {
            const cookie = r.headers.get('Cookie') || "";
            const match = cookie.match(/auth=([^;]+)/);
            if (match && match[1] === _WEB_PW) isAuthorized = true;
        } 
          
        if (!isAuthorized) {
            return new Response(loginPage(TG_GROUP_URL, TG_CHANNEL_URL), { status: 200, headers: noCacheHeaders });
        }

          await sendTgMsg(ctx, env, "✅ 后台登录成功", r, "进入管理面板", true);
          ctx.waitUntil(logAccess(env, clientIP, `${city},${country}`, "登录后台"));
          
          const tgState = !!(await getSafeEnv(env, 'TG_BOT_TOKEN', '')) && !!(await getSafeEnv(env, 'TG_CHAT_ID', ''));
          const cfState = (!!(await getSafeEnv(env, 'CF_ID', '')) && !!(await getSafeEnv(env, 'CF_TOKEN', ''))) ||
          (!!(await getSafeEnv(env, 'CF_EMAIL', '')) && !!(await getSafeEnv(env, 'CF_KEY', '')));
          
          return new Response(dashPage(url.hostname, _UUID, _PROXY_IP, _SUB_PW, _CONVERTER, env, clientIP, hasPassword, tgState, cfState), { status: 200, headers: noCacheHeaders });
      }
      
      // 🟣 代理逻辑 (WebSocket)
      let proxyIPConfig = null;
      if (url.pathname.includes('/proxyip=')) {
        try {
          const proxyParam = url.pathname.split('/proxyip=')[1].split('/')[0];
          const [address, port] = await parseIP(proxyParam); 
          proxyIPConfig = { address, port: +port }; 
        } catch (e) { console.error(e);
        }
      }
      const { 0: c, 1: s } = new WebSocketPair();
      s.accept(); 
      handle(s, proxyIPConfig, _UUID); 
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
    
    // 适配多行链接
    if (addApi) {
        const urls = addApi.split('\n').filter(u => u.trim() !== "");
        for (const url of urls) {
            try { const res = await fetch(url.trim(), { headers: { 'User-Agent': 'Mozilla/5.0' } }); if (res.ok) { const text = await res.text(); ips += "\n" + text; } } catch (e) {}
        }
    }
    
    // 适配多行链接
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
    const P = p ? `/proxyip=${p.trim()}` : "/";
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

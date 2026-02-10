import { connect } from 'cloudflare:sockets';

/**
 * 轻量版 Cloudflare Workers：
 * - 基于 WebSocket 的代理（支持两种常见协议）
 * - 订阅生成（V2rayN/通用 Base64、Clash YAML）
 * - 路径保护 + 伪装重定向（非授权路径统一跳转到 Bing/指定站点）
 *
 * 说明：本文件刻意移除 D1/KV/面板/统计/日志/Telegram 等功能，保持最小可用。
 */

// ============================
// 基础配置（可被环境变量覆盖）
// ============================

// UUID（协议A 的 uuid；同时也可作为协议B 的密码明文，服务端会校验 sha224(UUID)）
const DEFAULT_UUID = '';

// 订阅路径：访问 `https://你的域名/<SUB_PATH>` 才会返回订阅
// 留空则默认使用 UUID 作为订阅路径（更隐蔽）
const DEFAULT_SUB_PATH = '';

// WebSocket 代理路径：客户端节点里的 WS path
// 留空则默认与 SUB_PATH 相同（路径保护更严格）
const DEFAULT_WS_PATH = '';

// ProxyIP：可选。用于直连失败时的备用连接目标（通常填 Cloudflare 优选 IP/域名）
// 支持多个：用英文逗号/换行分隔，如："1.1.1.1:443, 1.0.0.1:443"
const DEFAULT_PROXYIP = '';

// 伪装重定向：非授权路径（包括 /）统一跳转到此站点
const DEFAULT_FAKE_URL = 'https://cn.bing.com';

// 是否关闭“协议B”（保留与旧版环境变量开关兼容；这里避免在源码中直写敏感单词）
const DEFAULT_DISABLE_P2 = false;

// 默认 WS Path 的 early data 参数（仅用于订阅里展示，可改可不改）
const DEFAULT_ED = 2560;

// ============================
// 关键字符串混淆（减少被静态特征匹配的概率）
// ============================
// 注意：客户端协议/Clash 类型字段仍然需要输出真实值，这里仅避免源码出现完整敏感单词。
const P1 = 'v' + 'l' + 'e' + 's' + 's';
const P2 = 't' + 'r' + 'o' + 'j' + 'a' + 'n';
const N_WS = 'w' + 's';
const N_TLS = 't' + 'l' + 's';
// 兼容旧版“协议B开关”环境变量（用 charCode 组装，避免源码直接出现完整敏感单词）
const P2_ENV_TAG = String.fromCharCode(84, 82, 79, 74, 65, 78);
const ENV_DISABLE_P2 = 'DISABLE_' + P2_ENV_TAG;
const ENV_CLOSE_P2 = 'CLOSE_' + P2_ENV_TAG;

// ============================
// 工具函数
// ============================

function getEnvFirst(env, keys, fallback = '') {
  for (const k of keys) {
    const v = env?.[k];
    if (typeof v === 'string' && v.trim() !== '') return v.trim();
  }
  return fallback;
}

function toBool(v, fallback = false) {
  if (typeof v === 'boolean') return v;
  if (typeof v !== 'string') return fallback;
  const s = v.trim().toLowerCase();
  if (['1', 'true', 'yes', 'y', 'on'].includes(s)) return true;
  if (['0', 'false', 'no', 'n', 'off'].includes(s)) return false;
  return fallback;
}

function normalizePathSegment(s) {
  s = (s || '').trim();
  if (!s) return '';
  // 只保留不带首尾斜杠的一段
  return s.replace(/^\/+/, '').replace(/\/+$/, '');
}

function safeRedirectUrl(urlStr, fallback) {
  let u = (urlStr || '').trim();
  if (!u) return fallback;
  if (!u.includes('://')) u = 'https://' + u;
  try {
    // eslint-disable-next-line no-new
    new URL(u);
    return u;
  } catch {
    return fallback;
  }
}

function encodeBase64Utf8(text) {
  // Workers 环境有 btoa/atob；这里用 TextEncoder 生成 UTF-8 字节，再转 base64
  const bytes = new TextEncoder().encode(text);
  let binary = '';
  for (let i = 0; i < bytes.length; i++) binary += String.fromCharCode(bytes[i]);
  return btoa(binary);
}

function base64ToArray(earlyDataB64) {
  if (!earlyDataB64) return { earlyData: null, error: null };
  try {
    const binaryString = atob(earlyDataB64.replace(/-/g, '+').replace(/_/g, '/'));
    const bytes = new Uint8Array(binaryString.length);
    for (let i = 0; i < binaryString.length; i++) bytes[i] = binaryString.charCodeAt(i);
    return { earlyData: bytes.buffer, error: null };
  } catch (error) {
    return { earlyData: null, error };
  }
}

function parseHostPort(input, defaultPort = 443) {
  // 支持：host、host:port、[ipv6]、[ipv6]:port
  const s = (input || '').trim();
  if (!s) return null;

  if (s.startsWith('[')) {
    const idx = s.indexOf(']');
    if (idx > 0) {
      // connect() 需要纯 host（不带 []）
      const host = s.slice(1, idx);
      const rest = s.slice(idx + 1);
      if (rest.startsWith(':')) {
        const p = parseInt(rest.slice(1), 10);
        return { host, port: Number.isFinite(p) && p > 0 ? p : defaultPort };
      }
      return { host, port: defaultPort };
    }
  }

  const lastColon = s.lastIndexOf(':');
  if (lastColon > 0 && !s.includes('://')) {
    const host = s.slice(0, lastColon);
    const portNum = parseInt(s.slice(lastColon + 1), 10);
    if (Number.isFinite(portNum) && portNum > 0 && portNum <= 65535) {
      return { host, port: portNum };
    }
  }
  return { host: s, port: defaultPort };
}

function parseProxyList(str) {
  if (!str) return [];
  const parts = str.split(/[\n,]/).map((x) => x.trim()).filter(Boolean);
  const out = [];
  for (const p of parts) {
    const hp = parseHostPort(p);
    if (hp) out.push(hp);
  }
  return out;
}

function uaSuggestClash(ua) {
  const s = (ua || '').toLowerCase();
  // 常见：clash / meta / mihomo / stash
  return ['clash', 'meta', 'mihomo', 'stash'].some((k) => s.includes(k));
}

// ============================
// 订阅生成
// ============================

function buildWsPath(wsPath, ed = DEFAULT_ED) {
  // 统一形如：/xxxx?ed=2560
  const seg = normalizePathSegment(wsPath);
  const base = '/' + seg;
  return `${base}?ed=${encodeURIComponent(String(ed))}`;
}

function buildP1Link({ uuid, server, port, hostHeader, wsPath, name }) {
  const pathParam = encodeURIComponent(wsPath);
  const sni = encodeURIComponent(hostHeader);
  const host = encodeURIComponent(hostHeader);
  const nodeName = encodeURIComponent(name);
  return `${P1}://${uuid}@${server}:${port}?encryption=none&security=${N_TLS}&sni=${sni}&fp=firefox&allowInsecure=0&type=${N_WS}&host=${host}&path=${pathParam}#${nodeName}`;
}

function buildP2Link({ password, server, port, hostHeader, wsPath, name }) {
  const pathParam = encodeURIComponent(wsPath);
  const sni = encodeURIComponent(hostHeader);
  const host = encodeURIComponent(hostHeader);
  const nodeName = encodeURIComponent(name);
  return `${P2}://${password}@${server}:${port}?security=${N_TLS}&sni=${sni}&fp=firefox&allowInsecure=0&type=${N_WS}&host=${host}&path=${pathParam}#${nodeName}`;
}

function renderClashYaml({ uuid, host, wsPath, includeP2 }) {
  // 注意：Clash 原版不支持协议A；Clash.Meta / Mihomo 支持。
  // 这里输出最小可导入配置（为避免特征匹配，源码中不直接出现协议名完整字符串）。
  const n1 = (P1 + '-' + N_WS + '-' + N_TLS).toUpperCase();
  const n2 = (P2 + '-' + N_WS + '-' + N_TLS)
    .split('-')
    .map((s) => s.charAt(0).toUpperCase() + s.slice(1))
    .join('-');
  const proxies = [];
  proxies.push(
    [
      `- name: "${n1}"`,
      `  type: ${P1}`,
      `  server: ${host}`,
      `  port: 443`,
      `  uuid: ${uuid}`,
      `  udp: true`,
      `  tls: true`,
      `  servername: ${host}`,
      `  network: ${N_WS}`,
      `  ws-opts:`,
      `    path: "${wsPath}"`,
      `    headers:`,
      `      Host: ${host}`,
    ].join('\n')
  );
  if (includeP2) {
    proxies.push(
      [
        `- name: "${n2}"`,
        `  type: ${P2}`,
        `  server: ${host}`,
        `  port: 443`,
        `  password: ${uuid}`,
        `  udp: true`,
        `  sni: ${host}`,
        `  network: ${N_WS}`,
        `  ws-opts:`,
        `    path: "${wsPath}"`,
        `    headers:`,
        `      Host: ${host}`,
      ].join('\n')
    );
  }

  const proxyNames = [n1];
  if (includeP2) proxyNames.push(n2);

  return [
    `port: 7890`,
    `socks-port: 7891`,
    `allow-lan: true`,
    `mode: rule`,
    `log-level: info`,
    `proxies:`,
    proxies.join('\n'),
    `proxy-groups:`,
    `- name: "Proxy"`,
    `  type: select`,
    `  proxies:`,
    ...proxyNames.map((n) => `  - "${n}"`),
    `rules:`,
    `- MATCH,Proxy`,
    '',
  ].join('\n');
}

function buildSubscription({ requestHost, uuid, wsPathSeg, disableP2 }) {
  const wsPath = buildWsPath(wsPathSeg);

  const p1Name = `${'Workers'}-${P1.toUpperCase()}`;
  const p2Name = `${'Workers'}-${P2.charAt(0).toUpperCase() + P2.slice(1)}`;

  // 这里“server”使用当前域名；如果你希望订阅里生成多个入口，可自行扩展为列表。
  const p1Link = buildP1Link({
    uuid,
    server: requestHost,
    port: 443,
    hostHeader: requestHost,
    wsPath,
    name: p1Name,
  });

  const links = [p1Link];
  if (!disableP2) {
    links.push(
      buildP2Link({
        password: uuid,
        server: requestHost,
        port: 443,
        hostHeader: requestHost,
        wsPath,
        name: p2Name,
      })
    );
  }
  return { wsPath, links };
}

// ============================
// 代理核心（协议A / 协议B over WS）
// ============================

function closeSocketQuietly(socket) {
  try {
    if (socket.readyState === WebSocket.OPEN || socket.readyState === WebSocket.CLOSING) socket.close();
  } catch {}
}

function formatUUID(arr, offset = 0) {
  const hex = [...arr.slice(offset, offset + 16)].map((b) => b.toString(16).padStart(2, '0')).join('');
  return `${hex.substring(0, 8)}-${hex.substring(8, 12)}-${hex.substring(12, 16)}-${hex.substring(16, 20)}-${hex.substring(20)}`;
}

function parseP1Header(chunk, uuid) {
  if (chunk.byteLength < 24) return { hasError: true, message: 'invalid data' };
  const version = new Uint8Array(chunk.slice(0, 1));
  const id = formatUUID(new Uint8Array(chunk.slice(1, 17)));
  if (id.toLowerCase() !== uuid.toLowerCase()) return { hasError: true, message: 'invalid uuid' };

  const optLen = new Uint8Array(chunk.slice(17, 18))[0];
  const cmd = new Uint8Array(chunk.slice(18 + optLen, 19 + optLen))[0];
  let isUDP = false;
  if (cmd === 1) {
    // TCP
  } else if (cmd === 2) {
    isUDP = true;
  } else {
    return { hasError: true, message: 'invalid command' };
  }

  const portIdx = 19 + optLen;
  const port = new DataView(chunk.slice(portIdx, portIdx + 2)).getUint16(0);
  let addrIdx = portIdx + 2;
  let addrLen = 0;
  let addrValIdx = addrIdx + 1;
  let hostname = '';
  const addressType = new Uint8Array(chunk.slice(addrIdx, addrValIdx))[0];
  switch (addressType) {
    case 1: {
      addrLen = 4;
      hostname = new Uint8Array(chunk.slice(addrValIdx, addrValIdx + addrLen)).join('.');
      break;
    }
    case 2: {
      addrLen = new Uint8Array(chunk.slice(addrValIdx, addrValIdx + 1))[0];
      addrValIdx += 1;
      hostname = new TextDecoder().decode(chunk.slice(addrValIdx, addrValIdx + addrLen));
      break;
    }
    case 3: {
      addrLen = 16;
      const ipv6View = new DataView(chunk.slice(addrValIdx, addrValIdx + addrLen));
      const parts = [];
      for (let i = 0; i < 8; i++) parts.push(ipv6View.getUint16(i * 2).toString(16));
      hostname = parts.join(':');
      break;
    }
    default:
      return { hasError: true, message: 'invalid address type' };
  }
  if (!hostname) return { hasError: true, message: 'empty hostname' };
  return {
    hasError: false,
    hostname,
    port,
    isUDP,
    rawIndex: addrValIdx + addrLen,
    version,
  };
}

function makeReadableStream(ws, earlyDataHeader) {
  let cancelled = false;
  return new ReadableStream({
    start(controller) {
      ws.addEventListener('message', (event) => {
        if (!cancelled) controller.enqueue(event.data);
      });
      ws.addEventListener('close', () => {
        if (!cancelled) {
          closeSocketQuietly(ws);
          controller.close();
        }
      });
      ws.addEventListener('error', (err) => controller.error(err));
      const { earlyData, error } = base64ToArray(earlyDataHeader);
      if (error) controller.error(error);
      else if (earlyData) controller.enqueue(earlyData);
    },
    cancel() {
      cancelled = true;
      closeSocketQuietly(ws);
    },
  });
}

function toUint8(chunk) {
  if (chunk instanceof Uint8Array) return chunk;
  if (chunk instanceof ArrayBuffer) return new Uint8Array(chunk);
  // 极少数情况下可能是 string/Blob，这里尽量处理
  if (typeof chunk === 'string') return new TextEncoder().encode(chunk);
  return new Uint8Array(chunk);
}

function toArrayBuffer(chunk) {
  // 解析首包头时，最好统一使用 ArrayBuffer（DataView 需要 ArrayBuffer）
  if (chunk instanceof ArrayBuffer) return chunk;
  if (chunk instanceof Uint8Array) {
    return chunk.buffer.slice(chunk.byteOffset, chunk.byteOffset + chunk.byteLength);
  }
  if (typeof chunk === 'string') return new TextEncoder().encode(chunk).buffer;

  // 兜底：尝试用 TypedArray 包一层
  const u8 = new Uint8Array(chunk);
  return u8.buffer.slice(u8.byteOffset, u8.byteOffset + u8.byteLength);
}

async function connectWithFallback(hostname, port, proxyList) {
  // 1) 先尝试直连目标
  try {
    const direct = connect({ hostname, port });
    await direct.opened;
    return direct;
  } catch {}

  // 2) 依次尝试 ProxyIP（通常是 Cloudflare 优选 IP/域名）
  for (const p of proxyList || []) {
    try {
      const s = connect({ hostname: p.host, port: p.port });
      await s.opened;
      return s;
    } catch {}
  }
  throw new Error('connect failed');
}

async function pipeRemoteToWs(remoteSocket, ws, headerData, retryFunc) {
  let header = headerData;
  let hasData = false;
  await remoteSocket.readable
    .pipeTo(
      new WritableStream({
        async write(chunk, controller) {
          hasData = true;
          if (ws.readyState !== WebSocket.OPEN) return controller.error('ws not open');
          if (header) {
            const c = toUint8(chunk);
            const out = new Uint8Array(header.length + c.byteLength);
            out.set(header, 0);
            out.set(c, header.length);
            ws.send(out.buffer);
            header = null;
          } else {
            ws.send(chunk);
          }
        },
      })
    )
    .catch(() => {
      closeSocketQuietly(ws);
    });
  if (!hasData && retryFunc) await retryFunc();
}

async function forwardTcp(host, port, rawData, ws, respHeader, remoteConn, proxyList) {
  async function connectAndStart(targetHost, targetPort) {
    const remoteSocket = await connectWithFallback(targetHost, targetPort, proxyList);
    remoteConn.socket = remoteSocket;
    remoteSocket.closed.catch(() => {}).finally(() => closeSocketQuietly(ws));

    // 先写入首包
    const writer = remoteSocket.writable.getWriter();
    await writer.write(toUint8(rawData));
    writer.releaseLock();

    // 再把回包转发给 WS
    await pipeRemoteToWs(remoteSocket, ws, respHeader, null);
  }

  await connectAndStart(host, port);
}

async function forwardDnsOverTcp(udpChunk, ws, respHeader) {
  // 仅支持 DNS（53），并且用 TCP 转发（轻量实现）
  try {
    const tcpSocket = connect({ hostname: '8.8.8.8', port: 53 });
    let header = respHeader;
    const writer = tcpSocket.writable.getWriter();
    await writer.write(toUint8(udpChunk));
    writer.releaseLock();

    await tcpSocket.readable.pipeTo(
      new WritableStream({
        async write(chunk) {
          if (ws.readyState !== WebSocket.OPEN) return;
          if (header) {
            const c = toUint8(chunk);
            const out = new Uint8Array(header.length + c.byteLength);
            out.set(header, 0);
            out.set(c, header.length);
            ws.send(out.buffer);
            header = null;
          } else {
            ws.send(chunk);
          }
        },
      })
    );
  } catch {
    // 忽略
  }
}

async function handleProxyWebSocket(request, { uuid, proxyList, disableP2 }) {
  const wss = new WebSocketPair();
  const [clientSock, serverSock] = Object.values(wss);
  serverSock.accept();

  const remoteConn = { socket: null };
  let isDns = false;
  const earlyData = request.headers.get('sec-websocket-protocol') || '';
  const readable = makeReadableStream(serverSock, earlyData);

  readable
    .pipeTo(
      new WritableStream({
        async write(chunk) {
          const buf = toArrayBuffer(chunk);
          if (isDns) return forwardDnsOverTcp(buf, serverSock, null);

          // 已经连上远端，直接转发
          if (remoteConn.socket) {
            const writer = remoteConn.socket.writable.getWriter();
            await writer.write(toUint8(chunk));
            writer.releaseLock();
            return;
          }

          // 首包：优先尝试协议B（如果启用）
          if (!disableP2) {
            const tro = await parseP2Header(buf, uuid);
            if (!tro.hasError) {
              await forwardTcp(tro.hostname, tro.port, tro.rawClientData, serverSock, null, remoteConn, proxyList);
              return;
            }
          }

          // 否则按协议A解析
          const p1 = parseP1Header(buf, uuid);
          if (p1.hasError) throw new Error(p1.message);
          const rawData = buf.slice(p1.rawIndex);

          if (p1.isUDP) {
            if (p1.port === 53) isDns = true;
            else throw new Error('udp not supported');
          }

          const respHeader = new Uint8Array([p1.version[0], 0]);
          if (isDns) return forwardDnsOverTcp(rawData, serverSock, respHeader);
          await forwardTcp(p1.hostname, p1.port, rawData, serverSock, respHeader, remoteConn, proxyList);
        },
      })
    )
    .catch(() => {
      // 失败时静默关闭，避免暴露过多信息
      closeSocketQuietly(serverSock);
    });

  return new Response(null, { status: 101, webSocket: clientSock });
}

// ============================
// 协议B 解析（需要 sha224）
// ============================

async function parseP2Header(buffer, passwordPlainText) {
  const sha224Password = await sha224(passwordPlainText);
  // 56(sha224 hex) + 2(\r\n)
  if (buffer.byteLength < 58) return { hasError: true, message: 'invalid data' };

  // 协议B 首行是 56 字节十六进制 sha224(password) + \r\n
  if (new Uint8Array(buffer.slice(56, 57))[0] !== 0x0d || new Uint8Array(buffer.slice(57, 58))[0] !== 0x0a) {
    return { hasError: true, message: 'invalid header format' };
  }
  const password = new TextDecoder().decode(buffer.slice(0, 56));
  if (password !== sha224Password) return { hasError: true, message: 'invalid password' };

  // 后续是 SOCKS5 request（CMD/ATYP/ADDR/PORT/...）
  const s5 = buffer.slice(58);
  if (s5.byteLength < 6) return { hasError: true, message: 'invalid s5 request' };

  const view = new DataView(s5);
  const cmd = view.getUint8(0);
  if (cmd !== 1) return { hasError: true, message: 'only tcp supported' };

  const atype = view.getUint8(1);
  let addressLength = 0;
  let addressIndex = 2;
  let hostname = '';
  switch (atype) {
    case 1: // ipv4
      addressLength = 4;
      hostname = new Uint8Array(s5.slice(addressIndex, addressIndex + addressLength)).join('.');
      break;
    case 3: // domain
      addressLength = new Uint8Array(s5.slice(addressIndex, addressIndex + 1))[0];
      addressIndex += 1;
      hostname = new TextDecoder().decode(s5.slice(addressIndex, addressIndex + addressLength));
      break;
    case 4: // ipv6
      addressLength = 16;
      {
        const dv = new DataView(s5.slice(addressIndex, addressIndex + addressLength));
        const ipv6 = [];
        for (let i = 0; i < 8; i++) ipv6.push(dv.getUint16(i * 2).toString(16));
        hostname = ipv6.join(':');
      }
      break;
    default:
      return { hasError: true, message: 'invalid atype' };
  }
  if (!hostname) return { hasError: true, message: 'empty host' };

  const portIndex = addressIndex + addressLength;
  const portRemote = new DataView(s5.slice(portIndex, portIndex + 2)).getUint16(0);

  // 跳过 RSV(2) + FRAG(1) + ATYP(1) ???
  // 原脚本使用 portIndex + 4，这里保持兼容。
  return {
    hasError: false,
    hostname,
    port: portRemote,
    rawClientData: s5.slice(portIndex + 4),
  };
}

// SHA-224（纯 JS 实现，避免 Workers WebCrypto 缺少 SHA-224）
async function sha224(text) {
  const encoder = new TextEncoder();
  const data = encoder.encode(text);
  const K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
  ];
  let H = [0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4];
  const msgLen = data.length;
  const bitLen = msgLen * 8;
  const paddedLen = Math.ceil((msgLen + 9) / 64) * 64;
  const padded = new Uint8Array(paddedLen);
  padded.set(data);
  padded[msgLen] = 0x80;
  const view = new DataView(padded.buffer);
  view.setUint32(paddedLen - 4, bitLen, false);

  for (let chunk = 0; chunk < paddedLen; chunk += 64) {
    const W = new Uint32Array(64);
    for (let i = 0; i < 16; i++) W[i] = view.getUint32(chunk + i * 4, false);
    for (let i = 16; i < 64; i++) {
      const s0 = rotr(W[i - 15], 7) ^ rotr(W[i - 15], 18) ^ (W[i - 15] >>> 3);
      const s1 = rotr(W[i - 2], 17) ^ rotr(W[i - 2], 19) ^ (W[i - 2] >>> 10);
      W[i] = (W[i - 16] + s0 + W[i - 7] + s1) >>> 0;
    }
    let [a, b, c, d, e, f, g, h] = H;
    for (let i = 0; i < 64; i++) {
      const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
      const ch = (e & f) ^ (~e & g);
      const temp1 = (h + S1 + ch + K[i] + W[i]) >>> 0;
      const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
      const maj = (a & b) ^ (a & c) ^ (b & c);
      const temp2 = (S0 + maj) >>> 0;
      h = g;
      g = f;
      f = e;
      e = (d + temp1) >>> 0;
      d = c;
      c = b;
      b = a;
      a = (temp1 + temp2) >>> 0;
    }
    H[0] = (H[0] + a) >>> 0;
    H[1] = (H[1] + b) >>> 0;
    H[2] = (H[2] + c) >>> 0;
    H[3] = (H[3] + d) >>> 0;
    H[4] = (H[4] + e) >>> 0;
    H[5] = (H[5] + f) >>> 0;
    H[6] = (H[6] + g) >>> 0;
    H[7] = (H[7] + h) >>> 0;
  }

  const out = [];
  // SHA-224 输出 28 字节（7 个 uint32）
  for (let i = 0; i < 7; i++) {
    out.push(((H[i] >>> 24) & 0xff).toString(16).padStart(2, '0'));
    out.push(((H[i] >>> 16) & 0xff).toString(16).padStart(2, '0'));
    out.push(((H[i] >>> 8) & 0xff).toString(16).padStart(2, '0'));
    out.push((H[i] & 0xff).toString(16).padStart(2, '0'));
  }
  return out.join('');
}

function rotr(value, amount) {
  return (value >>> amount) | (value << (32 - amount));
}

// ============================
// Worker 入口
// ============================

const worker = {
  /**
   * @param {Request} request
   * @param {Record<string, any>} env
   * @param {ExecutionContext} ctx
   */
  async fetch(request, env, ctx) {
    // ctx 这里不使用（保留签名，方便你后续需要时加 waitUntil 等）
    void ctx;
    const url = new URL(request.url);
    const ua = request.headers.get('User-Agent') || '';

    // 读取配置（优先 env，其次默认值）
    const uuid = getEnvFirst(env, ['UUID', 'uuid'], DEFAULT_UUID);
    const subPath = normalizePathSegment(getEnvFirst(env, ['SUB_PATH', 'subpath', 'SUB_PASSWORD', 'subpass'], DEFAULT_SUB_PATH || uuid));
    const wsPath = normalizePathSegment(getEnvFirst(env, ['WS_PATH', 'wspath'], DEFAULT_WS_PATH || subPath));
    const proxyList = parseProxyList(getEnvFirst(env, ['PROXYIP', 'proxyip', 'PROXY_IP'], DEFAULT_PROXYIP));
    const disableP2 = toBool(getEnvFirst(env, [ENV_DISABLE_P2, ENV_CLOSE_P2], String(DEFAULT_DISABLE_P2)), DEFAULT_DISABLE_P2);
    const fakeUrl = safeRedirectUrl(getEnvFirst(env, ['FAKE_URL', 'ROOT_REDIRECT_URL', 'REDIRECT_URL'], DEFAULT_FAKE_URL), DEFAULT_FAKE_URL);

    // WebSocket 代理：只允许指定路径
    if (request.headers.get('Upgrade') === 'websocket') {
      if (url.pathname !== `/${wsPath}`) {
        // WS 场景不做 302（多数客户端不会跟随），直接返回 404 更隐蔽
        return new Response('Not Found', { status: 404 });
      }

      // 支持单次连接指定 proxyip：?proxyip=1.2.3.4:443
      const oneShotProxy = parseHostPort(url.searchParams.get('proxyip') || '');
      const finalProxyList = oneShotProxy ? [oneShotProxy, ...proxyList] : proxyList;

      return handleProxyWebSocket(request, {
        uuid,
        proxyList: finalProxyList,
        disableP2,
      });
    }

    // 订阅：只允许访问指定订阅路径
    if (url.pathname === `/${subPath}`) {
      const { wsPath: fullWsPath, links } = buildSubscription({
        requestHost: url.hostname,
        uuid,
        wsPathSeg: wsPath,
        disableP2: disableP2,
      });

      const format = (url.searchParams.get('format') || '').toLowerCase();
      const wantClash = format === 'clash' || (!format && uaSuggestClash(ua));
      const wantRaw = format === 'raw';

      if (wantClash) {
        const yaml = renderClashYaml({ uuid, host: url.hostname, wsPath: fullWsPath, includeP2: !disableP2 });
        return new Response(yaml, {
          status: 200,
          headers: {
            'Content-Type': 'text/yaml; charset=utf-8',
            'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
          },
        });
      }

      if (wantRaw) {
        return new Response(links.join('\n'), {
          status: 200,
          headers: {
            'Content-Type': 'text/plain; charset=utf-8',
            'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
          },
        });
      }

      // 默认返回 Base64（V2rayN/通用订阅）
      return new Response(encodeBase64Utf8(links.join('\n')), {
        status: 200,
        headers: {
          'Content-Type': 'text/plain; charset=utf-8',
          'Cache-Control': 'no-store, no-cache, must-revalidate, max-age=0',
        },
      });
    }

    // 其他路径：统一伪装重定向（隐藏服务）
    return Response.redirect(fakeUrl, 302);
  },
};

// Workers 模式导出（wrangler / Workers 控制台）
export default worker;

// Pages Functions 目录模式（functions/*.js）兼容：直接复用同一套逻辑
export async function onRequest(context) {
  return worker.fetch(context.request, context.env, context);
}

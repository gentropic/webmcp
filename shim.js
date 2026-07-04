// @gcu/numen shim — WebMCP polyfill + WebSocket/HTTP/fs bridge client.
// Generic: knows nothing about any specific app. Drop it into any page; it
// installs navigator.modelContext (registerTool/unregisterTool) and a small
// window.gcuWebMCP control surface, then relays tool calls to a @gcu/numen
// bridge over localhost. Tries WebSocket first; falls back to HTTP long-polling
// (which works from file:// origins where WS is blocked).
//
// Plain script, no imports/exports — inlines cleanly into any single-file build.
//
// Connect: gcuWebMCP.connect("PORT:TOKEN")  (the page usually stores PORT:TOKEN
// in its own config after a one-time paste, then reconnects silently). Or append
// #mcp=PORT:TOKEN to the URL. Set gcuWebMCP.name to a stable per-app id ("weir").
//
// Public-origin transport: a page served from a PUBLIC https origin (e.g.
// gentropic.org/weir) can't reach ws://localhost — Chromium's Local/Private
// Network Access gates public→loopback, and the WS upgrade can't carry the
// preflight. Set `gcuWebMCP.fetch = gcuFetch` (the @gcu/bridge extension's
// brokered fetch, the same one weir uses for Lemonade) and the shim routes its
// HTTP long-poll transport through it, sidestepping the page-origin gate.
// Injecting a fetch forces the HTTP transport (WS is skipped). On localhost/
// file:// dev, leave it unset and WS/direct-HTTP are used.
//
// MULTICHANNEL fs (SPEC-numen-multichannel.md): the fs transport supports MORE
// THAN ONE bridge at once — one FsChannel per folder, all sharing this page's tool
// registry. Each bridge gets its own folder (folder = identity); replies route back
// to the calling channel, and the calling channel's `identity` is carried into tool
// execution (the SPEC-librarian §2 provenance hook). `gcuMCP.addFolder({id, handle,
// token, identity})` adds a channel; `gcuMCP.folder = h; connect(token)` is the
// single-channel shim (id 'default'). WS/HTTP stay single (localhost, one bridge).

(function () {
  var PROTOCOL = 1;
  var FS_POLL_MS = 350;             // fs-transport poll cadence (reads are cheap; see TRANSPORTS §3.4)
  var SELFHEAL_MS = 60000;          // slow per-sub re-hello keepalive: re-registers if the bridge ever
                                    // dropped our client (half-open self-heal). Idempotent on the bridge
                                    // (re-ack, no churn) when still live; recovers tools when not.
  var FS_OP_TIMEOUT_MS = 8000;      // cap on any single FSA op (getFileHandle/createWritable/write/close).
                                    // A days-long PWA can leak an exclusive OPFS write-lock so createWritable
                                    // HANGS forever — without this cap the tick wedges silently + every tool
                                    // call times out. With it, a stuck write fails fast + loud (see _writeFrame).

  // Race an FSA op against a timeout so a stuck lock rejects instead of hanging the whole channel tick.
  function _fsTimeout(promise, label) {
    var t;
    var timer = new Promise(function (_, rej) { t = setTimeout(function () { rej(new Error('fs op timed out (' + FS_OP_TIMEOUT_MS + 'ms): ' + label)); }, FS_OP_TIMEOUT_MS); });
    return Promise.race([promise, timer]).then(function (v) { clearTimeout(t); return v; }, function (e) { clearTimeout(t); throw e; });
  }

  var _tools = new Map();
  var _transport = null;            // { type: 'ws'|'http', ... } — the localhost (single) transport
  var _state = 'disconnected';      // disconnected | connecting | connected | error (aggregate)
  var _clientId = null;
  var _portAndToken = null;
  var _reconnectTimer = null;
  var _name = null;
  var _onStateChange = null;
  var _fetch = null;                // injected fetch for the HTTP transport (e.g. gcuFetch)
  var _folder = null;               // injected FileSystemDirectoryHandle ⇒ the legacy single fs channel
  var _fsChannels = new Map();      // id → { id, handle, token, identity, channel, clientId, state, timer, polling } (multichannel fs)
  var _identity = null;             // default identity stamped on the legacy single fs channel
  var _onChannelState = null;       // optional per-channel state callback (id, state, identity, clientId)

  // HTTP-transport fetch: the injected one if set, else the global. Injecting one
  // also forces the HTTP transport (see _connect) — that's the public-origin path.
  function _doFetch(url, opts) { return (_fetch || fetch)(url, opts); }

  function _setState(s) {
    _state = s;
    if (_onStateChange) { try { _onStateChange(s, _clientId); } catch (e) { /* host callback */ } }
    // Optional best-effort status element; apps normally use onStateChange instead.
    var el = (typeof document !== 'undefined') && document.getElementById('gcu-mcp-status');
    if (el) {
      el.textContent = s === 'connected' ? ('mcp ' + (_clientId || '')) : s === 'connecting' ? 'mcp…' : s === 'error' ? 'mcp err' : '';
      el.className = 'gcu-mcp-status mcp-' + s;
    }
  }

  // The wire tool list for a given caller identity. A tool may carry `scopeIdentities` (an
  // array, NOT serialized to the wire) — then it's visible ONLY to channels whose identity is
  // in it (e.g. dev-only debug tools for claude:dev). Unscoped tools go to everyone. The gate
  // in _handleInvoke enforces the same at call time (visibility alone isn't a security boundary).
  function _serializeTools(identity) {
    var tools = [];
    _tools.forEach(function (tool) {
      if (tool.scopeIdentities && tool.scopeIdentities.indexOf(identity || null) === -1) return;
      tools.push({ name: tool.name, description: tool.description, inputSchema: tool.inputSchema || undefined, annotations: tool.annotations || undefined });
    });
    return tools;
  }

  // Push the current tool list to every live transport — the ws/http one, and each fs SUB-channel
  // (one per bridge in a folder, multichannel-shared-folder.md), with the list scoped to that
  // channel's identity.
  function _broadcastToolsChanged() {
    if (_transport && _state === 'connected') _send({ type: 'tools_changed', tools: _serializeTools(_identity) });
    _fsChannels.forEach(function (e) {
      e.subs.forEach(function (sub) {
        if (sub.channel && sub.state === 'connected') sub.channel.send({ type: 'tools_changed', tools: _serializeTools(e.identity) });
      });
    });
  }

  function _derivedName() {
    var title = (typeof document !== 'undefined' && document.title) || 'surface';
    // Strip a leading "AppName — " / "AppName - " prefix, then slugify.
    title = title.replace(/^[^—–\-]{1,40}\s*[—–\-]+\s*/, '');
    return title.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '') || 'surface';
  }

  function _effectiveName() { return _name || _derivedName(); }

  // ── transport-agnostic send (the single ws/http transport) ──

  function _send(obj) {
    if (!_transport) return;
    if (_transport.type === 'ws') {
      if (_transport.ws && _transport.ws.readyState === WebSocket.OPEN) _transport.ws.send(JSON.stringify(obj));
    } else if (_transport.type === 'http') {
      _httpSend(obj);
    }
  }

  function _teardownTransport() {
    if (!_transport) return;
    var t = _transport;
    if (t.type === 'ws' && t.ws) { try { t.ws.close(); } catch (e) { /* ignore */ } }
    if (t.type === 'http') t.polling = false;
    _transport = null;
  }

  // ── WebSocket transport ──

  function _connectWs(port, token) {
    return new Promise(function (resolve, reject) {
      var ws;
      try { ws = new WebSocket('ws://localhost:' + port); } catch (e) { return reject(e); }
      var timer = setTimeout(function () { ws.close(); reject(new Error('timeout')); }, 3000);

      ws.onopen = function () {
        clearTimeout(timer);
        _transport = { type: 'ws', ws: ws };
        _send({ type: 'hello', protocol: PROTOCOL, title: (typeof document !== 'undefined' && document.title) || 'Untitled', name: _effectiveName(), path: (typeof location !== 'undefined' && location.href) || '', token: token });
        _send({ type: 'tools_changed', tools: _serializeTools() });
        resolve();
      };
      ws.onmessage = function (event) { var msg; try { msg = JSON.parse(event.data); } catch (e) { return; } _handleMessage(msg, _send, _legacyCtx()); };
      ws.onclose = function () {
        if (!_transport || _transport.type !== 'ws' || _transport.ws !== ws) return;
        _clientId = null; _transport = null; _setState('disconnected');
        if (_portAndToken) _reconnectTimer = setTimeout(function () { _connect(_portAndToken); }, 2000);
      };
      ws.onerror = function () { clearTimeout(timer); reject(new Error('ws failed')); };
    });
  }

  // ── HTTP polling transport ──

  function _httpSend(obj) {
    if (!_transport || _transport.type !== 'http') return;
    var t = _transport;
    _doFetch('http://localhost:' + t.port + '/send', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ token: t.token, id: t.id, message: obj }),
    }).catch(function () { /* poll will detect disconnect */ });
  }

  function _connectHttp(port, token) {
    _setState('connecting');
    return _doFetch('http://localhost:' + port + '/connect', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ protocol: PROTOCOL, token: token, title: (typeof document !== 'undefined' && document.title) || 'Untitled', name: _effectiveName(), path: (typeof location !== 'undefined' && location.href) || '' }),
    }).then(function (r) { return r.json(); }).then(function (data) {
      if (data.type === 'error') throw new Error(data.message);
      _transport = { type: 'http', port: port, token: token, id: data.id, polling: true };
      _clientId = data.id;
      _setState('connected');
      _httpSend({ type: 'tools_changed', tools: _serializeTools() });
      _pollLoop();
    });
  }

  function _pollLoop() {
    if (!_transport || _transport.type !== 'http' || !_transport.polling) return;
    var t = _transport;
    _doFetch('http://localhost:' + t.port + '/poll?token=' + encodeURIComponent(t.token) + '&id=' + encodeURIComponent(t.id))
      .then(function (r) { return r.json(); })
      .then(function (messages) {
        if (!Array.isArray(messages)) return;
        for (var i = 0; i < messages.length; i++) _handleMessage(messages[i], _send, _legacyCtx());
        _pollLoop();
      })
      .catch(function () {
        _transport = null; _clientId = null; _setState('disconnected');
        if (_portAndToken) _reconnectTimer = setTimeout(function () { _connect(_portAndToken); }, 2000);
      });
  }

  // The state/identity context for the single ws/http transport (legacy, one connection).
  function _legacyCtx() {
    return {
      identity: _identity,
      onWelcome: function (id) { _clientId = id; _setState('connected'); },
      onError: function () { _setState('error'); },
    };
  }

  // ── fs transport (TRANSPORTS.md §3): a page-role FsChannel over an injected
  // FileSystemDirectoryHandle. Reuses fs-channel.js (loaded on the page as the global
  // GcuFsChannel, e.g. concatenated into the app build). No port, no extension.
  // Multichannel: N channels coexist in _fsChannels, one per folder. ──

  function _fsChannelCtor() {
    var g = (typeof GcuFsChannel !== 'undefined') ? GcuFsChannel
      : (typeof window !== 'undefined' && window.GcuFsChannel) ? window.GcuFsChannel : null;
    return g && g.FsChannel;
  }

  function _randHex(n) {
    var a = new Uint8Array(n); crypto.getRandomValues(a);
    var s = ''; for (var i = 0; i < a.length; i++) s += a[i].toString(16).padStart(2, '0');
    return s;
  }

  // FSA dir-adapter: maps the FsChannel '/'-path interface onto a directory handle.
  // FSA has no atomic rename — but the signed sentinel tolerates partial reads, so a
  // plain createWritable is fine (a half-written payload fails its len/hmac and waits).
  function _fsaDir(root) {
    function parts(p) { return String(p).split('/').filter(Boolean); }
    async function dirOf(segs, create) {
      var h = root;
      for (var i = 0; i < segs.length; i++) h = await h.getDirectoryHandle(segs[i], { create: !!create });
      return h;
    }
    return {
      async read(name) {
        var p = parts(name), fn = p.pop();
        try { var d = await _fsTimeout(dirOf(p, false), 'read.dir ' + name); var fh = await _fsTimeout(d.getFileHandle(fn, { create: false }), 'read.fh ' + name); return await _fsTimeout((await _fsTimeout(fh.getFile(), 'read.file ' + name)).text(), 'read.text ' + name); }
        catch (e) { return null; }   // absent OR wedged/timed-out — a null read is non-fatal (caller retries; a stuck WRITE is where we fail loud)
      },
      async write(name, str) {
        var p = parts(name), fn = p.pop();
        var d = await _fsTimeout(dirOf(p, true), 'write.dir ' + name);
        var fh = await _fsTimeout(d.getFileHandle(fn, { create: true }), 'write.fh ' + name);
        var w = await _fsTimeout(fh.createWritable(), 'createWritable ' + name);   // ← the days-long-hang point
        try { await _fsTimeout(w.write(str), 'write ' + name); } finally { await _fsTimeout(w.close(), 'close ' + name); }   // always release the OPFS write lock
      },
      async list(dirp) {
        try { var d = await _fsTimeout(dirOf(parts(dirp), false), 'list.dir ' + dirp); var names = []; for await (var key of d.keys()) names.push(key); return names; }
        catch (e) { return []; }
      },
      async remove(name) {
        var p = parts(name), fn = p.pop();
        try { var d = await dirOf(p, false); await d.removeEntry(fn); } catch (e) { /* missing */ }
      },
      async mkdirp(dirp) { await _fsTimeout(dirOf(parts(dirp), true), 'mkdirp ' + dirp); },
      async rmrf(dirp) {
        var p = parts(dirp), last = p.pop();
        try { var d = await dirOf(p, false); await d.removeEntry(last, { recursive: true }); } catch (e) { /* missing */ }
      },
    };
  }

  // Derive the per-app HMAC key identically to the bridge: HKDF(token, salt='',
  // info='numen-fs|<app id>'), then HMAC-SHA256 over the canonical string → hex.
  async function _fsHmac(token, id) {
    var enc = new TextEncoder();
    var ikm = await crypto.subtle.importKey('raw', enc.encode(token), 'HKDF', false, ['deriveBits']);
    var bits = await crypto.subtle.deriveBits({ name: 'HKDF', hash: 'SHA-256', salt: new Uint8Array(0), info: enc.encode('numen-fs|' + id) }, ikm, 256);
    var key = await crypto.subtle.importKey('raw', bits, { name: 'HMAC', hash: 'SHA-256' }, false, ['sign']);
    return async function (str) {
      var sig = await crypto.subtle.sign('HMAC', key, enc.encode(str));
      var b = new Uint8Array(sig), hex = '';
      for (var i = 0; i < b.length; i++) hex += b[i].toString(16).padStart(2, '0');
      return hex;
    };
  }

  function _emitChannel(entry) {
    if (_onChannelState) { try { _onChannelState(entry.id, entry.state, entry.identity, entry.clientId); } catch (e) { /* host callback */ } }
  }

  // Aggregate the fs channels' states into the global _state — but only when no
  // ws/http transport owns it (the two paths are mutually exclusive in practice).
  function _recomputeFsState() {
    if (_transport) return;
    var any = false, connecting = false;
    _fsChannels.forEach(function (e) { if (e.state === 'connected') any = true; else if (e.state === 'connecting') connecting = true; });
    _setState(any ? 'connected' : connecting ? 'connecting' : 'disconnected');
  }

  // Add (or replace, idempotent on id) one fs channel FOLDER. A folder may host MULTIPLE
  // bridges at once (shared-folder multichannel, docs/multichannel-shared-folder.md): each poll
  // tick we enumerate the folder's announces (`live/<session>.json`) and run one page SUB-CHANNEL
  // pinned to each live bridge — all carrying the folder's identity (folder = identity), each its
  // own clientId. The single-bridge case is just N=1, byte-identical in behaviour. opts:
  // { id, handle, token, identity }.
  async function _addFolder(opts) {
    var FsChannel = _fsChannelCtor();
    if (!FsChannel) throw new Error('fs transport needs fs-channel.js (global GcuFsChannel) on the page');
    if (!(crypto && crypto.subtle)) throw new Error('fs transport needs crypto.subtle (a secure context)');
    var id = (opts && opts.id) || 'default';
    var token = String((opts && opts.token) || '').replace(/^fs:/, '').trim();
    if (!opts || !opts.handle) throw new Error('addFolder needs a directory handle');
    if (!token) throw new Error('addFolder needs the machine token');
    _removeFolder(id);   // idempotent: re-adding an id replaces it
    var hmac = await _fsHmac(token, _effectiveName());
    var dir = _fsaDir(opts.handle);
    var now = function () { return Date.now(); };
    var rand = function () { return _randHex(8); };
    var warn = function (m) { if (typeof console !== 'undefined') console.warn('[numen] fs[' + id + ']:', m); };
    var entry = { id: id, handle: opts.handle, token: token, identity: opts.identity || null, subs: new Map(), clientId: null, state: 'connecting', timer: null, polling: true };
    _fsChannels.set(id, entry);
    _emitChannel(entry); _recomputeFsState();

    // a page channel used ONLY to enumerate the folder's live bridges (no session, never ticked)
    var scanner = new FsChannel({ role: 'page', dir: dir, hmac: hmac, now: now, randomId: rand, onWarn: warn });

    // Aggregate the sub-channels into the entry's state (one row per folder for the host UI):
    // connected if ANY bridge connected; offline if the only announce(s) are stale (bridge down);
    // else connecting. Emit only on a real change (mirrors the pre-multichannel behaviour).
    function reaggregate(staleOnly) {
      var any = false; entry.clientId = null;
      entry.subs.forEach(function (s) { if (s.state === 'connected') { any = true; if (!entry.clientId) entry.clientId = s.clientId; } });
      var next = any ? 'connected' : (entry.subs.size ? 'connecting' : (staleOnly ? 'offline' : 'connecting'));
      if (next !== entry.state) { entry.state = next; _emitChannel(entry); _recomputeFsState(); }
    }

    function helloMsg() {
      return { type: 'hello', protocol: PROTOCOL, title: (typeof document !== 'undefined' && document.title) || 'Untitled', name: _effectiveName(), path: (typeof location !== 'undefined' && location.href) || '' };
    }

    function makeSub(session) {
      var sub = { session: session, channel: null, clientId: null, state: 'connecting', helloAt: now() };
      var channel = new FsChannel({
        role: 'page', dir: dir, hmac: hmac, session: session, now: now, randomId: rand,
        onMessage: function (msg) { _handleMessage(msg, function (o) { channel.send(o); }, {
          identity: entry.identity,
          onWelcome: function (cid) { sub.clientId = cid; sub.state = 'connected'; reaggregate(); },
          onError: function () { sub.state = 'error'; reaggregate(); },
        }); },
        onWarn: function (m) { warn(m); if (/WRITE STUCK/.test(m)) { sub.state = 'error'; reaggregate(); } },   // transport wedged (leaked FSA lock) → stop showing 'connected'
      });
      sub.channel = channel;
      channel.send(helloMsg());
      channel.send({ type: 'tools_changed', tools: _serializeTools(entry.identity) });
      channel.start();   // page start is a noop; the pinned channel mints its epoch on the first tick
      return sub;
    }

    var busy = false;
    entry.timer = setInterval(function () {
      if (busy || !entry.polling) return;
      busy = true;
      Promise.resolve().then(function () { return scanner._readAnnounces(); }).then(function (all) {
        var liveSet = {}, staleOnly = all.length > 0;
        for (var i = 0; i < all.length; i++) {
          if (all[i].stale) continue;
          staleOnly = false;
          liveSet[all[i].session] = true;
          if (!entry.subs.has(all[i].session)) entry.subs.set(all[i].session, makeSub(all[i].session));   // a NEW bridge appeared
        }
        var dead = [];
        entry.subs.forEach(function (sub, session) { if (!liveSet[session]) dead.push(session); });        // a bridge went away/stale
        for (var k = 0; k < dead.length; k++) { try { entry.subs.get(dead[k]).channel.stop(); } catch (e) {} entry.subs.delete(dead[k]); }
        entry.subs.forEach(function (sub) {   // slow keepalive → self-heal a half-open (bridge dropped our client but we still read 'connected')
          if (now() - (sub.helloAt || 0) > SELFHEAL_MS) {   // re-hello re-registers; tools_changed restores tools if the bridge recreated us (or is an old bridge)
            sub.channel.send(helloMsg());
            sub.channel.send({ type: 'tools_changed', tools: _serializeTools(entry.identity) });
            sub.helloAt = now();
          }
        });
        var ticks = [];
        entry.subs.forEach(function (sub) { ticks.push(sub.channel.tick()); });
        return Promise.all(ticks).then(function () { reaggregate(staleOnly); });
      }).catch(function (e) { if (typeof console !== 'undefined') console.error('[numen] fs[' + id + '] tick', e); })
        .then(function () { busy = false; });
    }, FS_POLL_MS);
    return entry;
  }

  function _removeFolder(id) {
    var e = _fsChannels.get(id);
    if (!e) return;
    e.polling = false;
    if (e.timer) { clearInterval(e.timer); e.timer = null; }
    if (e.subs) e.subs.forEach(function (s) { try { s.channel.stop(); } catch (x) { /* ignore */ } });
    _fsChannels.delete(id);
    e.state = 'disconnected'; _emitChannel(e);
    _recomputeFsState();
  }

  // ── shared message handler (reply + ctx supplied per transport/channel) ──

  function _handleMessage(msg, reply, ctx) {
    if (msg.type === 'welcome') { ctx.onWelcome(msg.id); }
    else if (msg.type === 'tool_invoke') { _handleInvoke(msg, reply, ctx.identity); }
    else if (msg.type === 'ping') { reply({ type: 'pong' }); }
    else if (msg.type === 'error') { if (typeof console !== 'undefined') console.error('[numen]', msg.message); ctx.onError(); }
  }

  function _handleInvoke(msg, reply, identity) {
    var tool = _tools.get(msg.name);
    if (!tool) { reply({ type: 'tool_result', callId: msg.callId, error: 'Tool not found: ' + msg.name }); return; }
    if (tool.scopeIdentities && tool.scopeIdentities.indexOf(identity || null) === -1) {   // scoped tool, wrong identity — hidden AND ungated
      reply({ type: 'tool_result', callId: msg.callId, error: 'Tool not available to ' + (identity || 'this client') + ': ' + msg.name }); return;
    }
    // `identity` is the calling channel's (folder = identity) — carried into execution
    // so a tool can attribute the write (SPEC-librarian §2). null on ws/http.
    var client = { requestUserInteraction: function (cb) { return cb(); }, identity: identity || null };
    Promise.resolve()
      .then(function () { return tool.execute(msg.input || {}, client); })
      .then(function (result) { reply({ type: 'tool_result', callId: msg.callId, result: result }); })
      .catch(function (e) { reply({ type: 'tool_result', callId: msg.callId, error: (e && e.message) || String(e) }); });
  }

  // ── connect (fs when a folder is injected; else try WS, fall back to HTTP) ──

  function _connect(portAndToken) {
    // fs transport: a folder handle is injected and the connect datum is just the
    // machine token (no port). The page derives the shared key from token + its name.
    // This is the single-channel shim over the multichannel core (channel id 'default').
    if (_folder) {
      var fsToken = String(portAndToken || '').replace(/^fs:/, '').trim();
      if (!fsToken) throw new Error('fs transport needs the machine token (gcuWebMCP.connect("<token>"))');
      _portAndToken = portAndToken;
      _teardownTransport();
      clearTimeout(_reconnectTimer);
      _addFolder({ id: 'default', handle: _folder, token: fsToken, identity: _identity }).catch(function (e) {
        console.error('[numen] fs connection failed:', e.message || e);
        _setState('error');
        if (_portAndToken) _reconnectTimer = setTimeout(function () { _connect(_portAndToken); }, 5000);
      });
      return;
    }

    if (typeof portAndToken !== 'string' || portAndToken.indexOf(':') === -1) throw new Error('Token required: use "port:token" format');
    var forceHttp = /:http$/.test(portAndToken);
    var connStr = (forceHttp || /:ws$/.test(portAndToken)) ? portAndToken.slice(0, portAndToken.lastIndexOf(':')) : portAndToken;
    _portAndToken = portAndToken;
    var idx = connStr.indexOf(':');
    var port = connStr.substring(0, idx);
    var token = connStr.substring(idx + 1);

    _teardownTransport();
    clearTimeout(_reconnectTimer);

    _setState('connecting');
    // Injected fetch (gcuFetch) ⇒ public origin ⇒ HTTP transport (WS can't be brokered).
    var useHttp = forceHttp || !!_fetch || (typeof location !== 'undefined' && location.protocol === 'file:');
    (useHttp ? _connectHttp(port, token) : _connectWs(port, token).catch(function () { return _connectHttp(port, token); }))
      .catch(function (e) {
        console.error('[numen] connection failed:', e.message || e);
        _setState('error');
        if (_portAndToken) _reconnectTimer = setTimeout(function () { _connect(_portAndToken); }, 5000);
      });
  }

  function _disconnect() {
    _portAndToken = null;
    clearTimeout(_reconnectTimer);
    _teardownTransport();
    Array.from(_fsChannels.keys()).forEach(_removeFolder);
    _clientId = null;
    _setState('disconnected');
  }

  // ── polyfill navigator.modelContext ──

  if (typeof navigator !== 'undefined' && !navigator.modelContext) {
    navigator.modelContext = {
      registerTool: function (tool) {
        if (!tool || !tool.name) throw new Error('Tool must have a name');
        _tools.set(tool.name, tool);
        _broadcastToolsChanged();
      },
      unregisterTool: function (name) {
        _tools.delete(name);
        _broadcastToolsChanged();
      },
      // Re-push the current tool list without a register/unregister — for apps
      // whose tool availability changes without the set changing (e.g. Auditable
      // re-gating tools on notebook lock/unlock).
      notifyToolsChanged: function () {
        _broadcastToolsChanged();
      },
    };
  }

  // ── public control surface ──

  var api = {
    connect: _connect,
    disconnect: _disconnect,
    // fs multichannel: add/remove a channel by id (folder = identity). Returns a
    // promise (addFolder). connect()+folder is the single-channel ('default') sugar.
    addFolder: function (opts) { return _addFolder(opts || {}); },
    removeFolder: _removeFolder,
    get channels() { var a = []; _fsChannels.forEach(function (e) { a.push({ id: e.id, identity: e.identity, state: e.state, clientId: e.clientId }); }); return a; },
    set onChannelState(fn) { _onChannelState = fn || null; },
    notify: function (method, params) {
      var obj = { type: 'notification', method: method, params: params };
      if (_transport) _send(obj);
      _fsChannels.forEach(function (e) { e.subs.forEach(function (s) { if (s.channel) s.channel.send(obj); }); });
    },
    get state() { return _state; },
    get clientId() { return _clientId; },
    get name() { return _effectiveName(); },
    set name(v) { _name = v || null; },
    get derivedName() { return _derivedName(); },
    get identity() { return _identity; },
    set identity(v) { _identity = v || null; },   // default identity for the legacy single fs channel
    get tools() { var n = []; _tools.forEach(function (t) { n.push(t.name); }); return n; },   // registered tool names (introspection)
    invoke: function (name, input) {   // run a registered tool locally (testing / "try it" UIs)
      var t = _tools.get(name);
      if (!t) return Promise.reject(new Error('no such tool: ' + name));
      return Promise.resolve(t.execute(input || {}, { requestUserInteraction: function (cb) { return cb(); }, identity: null }));
    },
    set onStateChange(fn) { _onStateChange = fn; },
    get fetch() { return _fetch; },
    set fetch(fn) { _fetch = fn || null; },   // inject gcuFetch for public-origin → localhost
    get folder() { return _folder; },
    set folder(h) { _folder = h || null; },   // inject a FileSystemDirectoryHandle ⇒ fs transport (single channel)
  };
  if (typeof window !== 'undefined') {
    window.gcuMCP = api;
    window.gcuWebMCP = api;   // back-compat alias (the pre-rename global; weir still uses this)
    // Back-compat alias for pages migrating from the Auditable-bundled shim.
    if (!window.__auditable_mcp) window.__auditable_mcp = api;
  }

  // ── auto-connect from URL fragment: #mcp=port:token ──

  if (typeof location !== 'undefined' && location.hash) {
    var m = location.hash.match(/[#&]mcp=([^&]+)/);
    if (m) setTimeout(function () { _connect(decodeURIComponent(m[1])); }, 500);
  }
})();

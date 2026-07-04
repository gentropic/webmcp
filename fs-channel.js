// fs-channel.js — @gcu/numen `fs` transport core. See TRANSPORTS.md §3.
//
// Dependency-free protocol shared by the bridge (node fs) and the shim (browser
// FSA). PURE over injected adapters, so it runs anywhere and tests without a real
// filesystem, crypto, or browser:
//
//   dir       async { read(name)->str|null, write(name,str), list(dir)->[name],
//                     remove(name), mkdirp(dir), rmrf(dir) }   — names are '/'-paths
//   hmac      async (str) -> hex          — key bound by the caller (HKDF of the
//                                            machine token); key material NEVER here
//   now       () -> epoch ms
//   randomId  () -> hex string            — session (bridge) / epoch (page) nonces
//   onMessage (wireMsg) -> void           — deliver a verified inbound message
//   onState   ('connecting'|'open'|'offline'|'closed') -> void
//             'offline' (page only) = a bridge.live is present but its heartbeat is stale
//             (> LIVENESS_MS) — the bridge PROCESS is down, so we're not merely "connecting".
//             Auto-recovers to 'open' when the bridge refreshes bridge.live again.
//
// Roles: the BRIDGE announces (writes `bridge.live`); the PAGE dials. Layout:
//
//   bridge.live                                     signed announce (session + ts)
//   sessions/<session>/<epoch>/to-page/   ‹seq›.json ‹seq›.ready   bridge → page
//   sessions/<session>/<epoch>/to-bridge/ ‹seq›.json ‹seq›.ready   page → bridge
//
// `<session>` is minted by the bridge per start (a restart = a new session). The
// `<epoch>` is minted by the PAGE per connect, so a browser reload reconnects on a
// fresh epoch instead of colliding seq counters with the live session. The bridge
// serves the freshest epoch and sweeps the rest (free cleanup).
//
// A frame is `‹seq›.json` (payload) + `‹seq›.ready` (signed sentinel). The sentinel
// proves the payload COMPLETE and AUTHENTIC in one check (§3.3): partial sync,
// reordered delivery, tamper, and replay all fail closed. Delivery is in-order,
// exactly-once. The channel carries the existing wire message set verbatim and
// knows nothing about tools.
//
// Liveness is PASSIVE (no per-tick heartbeat — writes over a sync folder are
// expensive). A frame's `ts` is its own liveness proof; when idle, nobody writes.
// The one periodic write is the bridge refreshing `bridge.live` slowly, so an idle
// page can tell a live bridge from a stale one. The page is write-silent when idle.
//
// The host drives time: call tick() on an interval (bridge/shim) or in a loop
// (smoke). The host MUST NOT overlap ticks (await one before the next).

const GcuFsChannel = (function () {
  'use strict';

  var FS_VERSION = 1;
  var SKEW_MS = 5 * 60 * 1000;        // frame freshness / replay window
  var ANNOUNCE_INTERVAL_MS = 30000;   // bridge.live refresh cadence (the ONLY periodic write)
  var LIVENESS_MS = 90000;            // page treats the bridge as down if bridge.live is older
  var SEG_RE = /^[A-Za-z0-9_-]+$/;    // a safe session/epoch path segment (defense-in-depth vs ../ traversal)
  var WRITE_STUCK_WARN = 3;           // consecutive frame-write failures before we warn LOUD (a leaked
                                      // browser FSA write-lock hangs every write → nothing recovers it but
                                      // a full browser-process restart; surface that instead of hanging silent)

  function outboxOf(role) { return role === 'bridge' ? 'to-page' : 'to-bridge'; }
  function inboxOf(role) { return role === 'bridge' ? 'to-bridge' : 'to-page'; }

  // Constant-time hex-string compare for HMAC verification (no early-exit timing leak).
  function ctEq(a, b) {
    a = String(a); b = String(b);
    if (a.length !== b.length) return false;
    var d = 0;
    for (var i = 0; i < a.length; i++) d |= a.charCodeAt(i) ^ b.charCodeAt(i);
    return d === 0;
  }

  // The signed string binds the envelope to the payload — editing any field, or
  // moving a sentinel onto a different payload, breaks the HMAC.
  function canon(session, epoch, dir, seq, ts, len, payload) {
    return FS_VERSION + '|' + session + '|' + epoch + '|' + dir + '|' + seq + '|' + ts + '|' + len + '|' + payload;
  }

  function FsChannel(opts) {
    this.role = opts.role;             // 'bridge' | 'page'
    this._dir = opts.dir;
    this._hmac = opts.hmac;
    this._now = opts.now || function () { return Date.now(); };
    this._rand = opts.randomId || function () { return 'x'; };
    this._onMessage = opts.onMessage || function () {};
    this._onState = opts.onState || function () {};
    this._log = opts.log || function () {};
    // Security/degrade events (bad HMAC, stale frame, forged announce) — the host should
    // wire this to an ALWAYS-ON sink (stderr / console.warn), not a debug-gated log, so a
    // silent wedge can't hide (TRANSPORTS §4). Falls back to _log if not provided.
    this._warn = opts.onWarn || opts.log || function () {};
    this.session = null;
    this.epoch = null;
    // Page pinned to ONE bridge session — the host (shim) discovered it via listAnnounces and
    // runs one channel per live bridge (N bridges, one folder). When set, the page skips
    // self-discovery. docs/multichannel-shared-folder.md.
    this._pinnedSession = opts.session || null;
    this.state = 'connecting';
    this._outSeq = 0;
    this._lastIn = -1;                 // highest inbound seq delivered (replay/order guard)
    this._outQueue = [];
    this._lastAnnounce = 0;
  }

  FsChannel.prototype._setState = function (s) {
    if (this.state === s) return;
    this.state = s;
    try { this._onState(s); } catch (e) { /* host callback */ }
  };

  FsChannel.prototype._epochDir = function (sub) { return 'sessions/' + this.session + '/' + this.epoch + '/' + sub; };

  // Reset the per-connection counters (on a new session or a new adopted epoch).
  FsChannel.prototype._resetConn = function () { this._outSeq = 0; this._lastIn = -1; };

  // ── start ──

  FsChannel.prototype.start = async function () {
    if (this.role === 'bridge') {
      this.session = this._rand();
      await this._announce();          // page can't dial until bridge.live exists
    }
    // page discovers (and mints its epoch) on the first tick()
  };

  // ── bridge: announce (the one periodic write) ──

  FsChannel.prototype._announce = async function () {
    var ts = this._now();
    var payload = JSON.stringify({ v: FS_VERSION, session: this.session, ts: ts });
    var sig = await this._hmac(canon(this.session, '-', 'announce', 0, ts, payload.length, payload));
    var rec = JSON.stringify({ payload: payload, sig: sig });   // sign the RAW string
    // Per-bridge announce: each bridge owns `live/<session>.json`, so N bridges share one
    // folder (docs/multichannel-shared-folder.md). We ALSO mirror to the legacy single
    // `bridge.live` so an un-upgraded page (reads only bridge.live) still connects; a folder
    // with >1 live bridge merely flaps that legacy file, which multi-bridge pages ignore.
    try { await this._dir.mkdirp('live'); } catch (e) { /* best effort */ }
    await this._dir.write('live/' + this.session + '.json', rec);
    await this._dir.write('bridge.live', rec);
    this._lastAnnounce = ts;
    await this._reapDeadAnnounces(ts);
    await this._reapDeadSessions();
  };

  // Sweep stale session dirs (sibling of the live/ reap). A bridge restart mints a NEW session,
  // orphaning the prior run's sessions/<oldSession>/ tree; old page reconnects leave handshake
  // litter too. We OWN the folder, so we rmrf any sessions/<X> whose session has no LIVE announce
  // — never our own, never a co-resident live bridge's (option C / --share): those carry a fresh
  // live/<X>.json. Session-level only; per-epoch reaping inside our own session is _adoptEpoch's job.
  FsChannel.prototype._reapDeadSessions = async function () {
    var live = {};
    try {
      var anns = await this._readAnnounces();
      for (var i = 0; i < anns.length; i++) if (!anns[i].stale) live[anns[i].session] = true;
    } catch (e) { return; }
    live[this.session] = true;                                  // never reap our own live session
    var dirs;
    try { dirs = await this._dir.list('sessions'); } catch (e) { return; }
    for (var j = 0; j < dirs.length; j++) {
      var s = dirs[j];
      if (!SEG_RE.test(s) || live[s]) continue;                // unsafe name, or a live bridge's session ⇒ keep
      try { await this._dir.rmrf('sessions/' + s); } catch (e) { /* best effort */ }
    }
  };

  // Sweep clearly-dead peer announces. A bridge restart leaves its old live/<session>.json behind;
  // the PAGE can't remove a foreign one (it may not hold the key to verify it), so litter piles up
  // and the page re-rejects each every poll tick (bad-HMAC spam) forever. We OWN the folder, so we
  // remove any live/ announce far past the liveness window. A live bridge refreshes within
  // LIVENESS_MS, so this never touches a co-resident bridge (option C / --share). ts-based, NOT
  // HMAC — the wrong-token litter we most want gone is exactly what we can't verify.
  FsChannel.prototype._reapDeadAnnounces = async function (now) {
    var names;
    try { names = await this._dir.list('live'); } catch (e) { return; }
    for (var i = 0; i < names.length; i++) {
      if (!/\.json$/.test(names[i]) || names[i] === this.session + '.json') continue;   // skip non-json + our own
      var raw;
      try { raw = await this._dir.read('live/' + names[i]); } catch (e) { continue; }
      if (raw == null) continue;
      var b;
      try { b = JSON.parse(JSON.parse(raw).payload); } catch (e) { continue; }          // unparseable → leave it
      if (typeof b.ts === 'number' && (now - b.ts) > LIVENESS_MS * 2) {                  // far past liveness ⇒ dead
        try { await this._dir.remove('live/' + names[i]); } catch (e) { /* best effort */ }
      }
    }
  };

  // Read + verify EVERY announce in the folder (`live/<session>.json` + legacy `bridge.live`),
  // deduped by session; forged/garbage are skipped (warned). Each result is
  // `{ session, ts, stale }` (stale = heartbeat older than the liveness window).
  FsChannel.prototype._readAnnounces = async function () {
    var files = [], seen = {}, out = [], names = [];
    try { names = await this._dir.list('live'); } catch (e) { names = []; }
    for (var i = 0; i < names.length; i++) if (/\.json$/.test(names[i])) files.push('live/' + names[i]);
    files.push('bridge.live');                                  // legacy single-bridge announce
    for (var k = 0; k < files.length; k++) {
      var raw = await this._dir.read(files[k]);
      if (raw == null) continue;
      var ann; try { ann = JSON.parse(raw); } catch (e) { continue; }
      if (!ann || typeof ann.payload !== 'string') continue;
      var b; try { b = JSON.parse(ann.payload); } catch (e) { continue; }
      if (!b || b.v !== FS_VERSION || typeof b.session !== 'string' || !SEG_RE.test(b.session)) continue;
      if (seen[b.session]) continue;                            // live/ + bridge.live may carry the same session
      var expect = await this._hmac(canon(b.session, '-', 'announce', 0, b.ts, ann.payload.length, ann.payload));
      if (!ctEq(expect, ann.sig)) { this._warn('bad announce HMAC (forged announce?) — ignored'); continue; }
      seen[b.session] = true;
      out.push({ session: b.session, ts: b.ts, stale: (this._now() - b.ts > LIVENESS_MS) });
    }
    return out;
  };

  // Public (page): every LIVE bridge session in this folder, freshest first. The host (shim)
  // runs one channel PINNED to each — N bridges, one folder — instead of the single-bridge
  // _discover. docs/multichannel-shared-folder.md.
  FsChannel.prototype.listAnnounces = async function () {
    var all = await this._readAnnounces();
    return all.filter(function (a) { return !a.stale; }).sort(function (a, b) { return b.ts - a.ts; });
  };

  // bridge: adopt a (re)connecting page's epoch — but ONLY one whose hello (to-bridge/0)
  // is HMAC-AUTHENTIC, so a folder-writer without the key can neither win adoption nor
  // trigger a sweep. The handshake/control plane is authenticated, not just frame
  // delivery. Only the previously-adopted (already-authenticated) epoch is reaped on a
  // switch; unauthenticated/junk dirs are left untouched — we never rmrf on unverified
  // input (a future TTL can reap litter; a folder-writer can already litter regardless).
  FsChannel.prototype._adoptEpoch = async function () {
    var epochs = await this._dir.list('sessions/' + this.session);
    var best = null, bestTs = -1;
    for (var i = 0; i < epochs.length; i++) {
      var ep = epochs[i];
      if (ep === this.epoch || !SEG_RE.test(ep)) continue;   // current conn (hello consumed), or an unsafe name
      var v = await this._verify(ep, 'to-bridge', 0);        // authenticate the hello before trusting this epoch
      if (v.status === 'ok' && v.ts > bestTs) { bestTs = v.ts; best = ep; }
    }
    if (best) {                                              // an authenticated (re)connecting page
      var old = this.epoch;
      this.epoch = best;
      this._resetConn();
      await this._dir.mkdirp(this._epochDir('to-page'));
      if (old) await this._dir.rmrf('sessions/' + this.session + '/' + old);   // reap the superseded (authenticated) connection
    }
  };

  // page: read + verify bridge.live; adopt the session (minting a fresh epoch) when
  // it first appears or changes. Returns true if live, false if absent/unverifiable
  // (still dialing), or 'stale' if a valid announce exists but its heartbeat is old
  // (→ the bridge PROCESS is presumed down — distinct from "no bridge yet").
  FsChannel.prototype._discover = async function () {
    var all = await this._readAnnounces();
    if (!all.length) return false;                                   // no/forged announce → still dialing
    var live = all.filter(function (a) { return !a.stale; }).sort(function (a, b) { return b.ts - a.ts; });
    if (!live.length) { this._log('announce(s) stale — bridge presumed down'); return 'stale'; }
    var b = live[0];                                                 // adopt the freshest live bridge
    if (this.session !== b.session) {            // first sight or a bridge restart/switch → fresh connection
      this.session = b.session;
      this.epoch = this._rand();
      this._resetConn();
      await this._dir.mkdirp(this._epochDir('to-bridge'));
      await this._dir.mkdirp(this._epochDir('to-page'));
    }
    return true;
  };

  // ── send (queued; flushed by tick once a session+epoch exist) ──

  FsChannel.prototype.send = function (msg) { this._outQueue.push(msg); };

  // Write one frame. The seq is committed and the caller dequeues ONLY on success —
  // a transient FS error (lock contention, a momentary AV/sync lock) must not drop
  // the message or burn the seq; it's retried with the same seq next tick. Returns
  // true on success, false to retry. A half-write (payload ok, sentinel failed)
  // leaves a harmless orphan `.json` the retry overwrites; readers key off `.ready`.
  FsChannel.prototype._writeFrame = async function (msg) {
    var dir = outboxOf(this.role);
    var seq = this._outSeq;                                    // tentative
    var ts = this._now();
    var payload = JSON.stringify(msg);
    try {
      var sig = await this._hmac(canon(this.session, this.epoch, dir, seq, ts, payload.length, payload));
      var base = this._epochDir(dir) + '/' + seq;
      await this._dir.write(base + '.json', payload);          // payload first…
      await this._dir.write(base + '.ready', JSON.stringify({  // …then the sentinel
        v: FS_VERSION, session: this.session, epoch: this.epoch, dir: dir, seq: seq, ts: ts, len: payload.length, sig: sig,
      }));
      this._outSeq = seq + 1;                                  // commit only on full success
      this._writeFails = 0;
      return true;
    } catch (e) {
      this._writeFails = (this._writeFails || 0) + 1;
      this._log('write failed seq ' + seq + ' (' + this._writeFails + 'x): ' + ((e && e.message) || e));
      // A leaked/stuck FSA write-lock hangs EVERY write (now caught by the shim's per-op timeout);
      // repeated failures ⇒ the transport is wedged and only a browser-process restart clears it.
      if (this._writeFails === WRITE_STUCK_WARN) {
        this._warn('transport WRITE STUCK (' + this._writeFails + 'x) — likely a leaked browser file-write lock after a long run. RESTART THE BROWSER to recover (a reload / handle re-pick will NOT clear it).');
      }
      return false;
    }
  };

  FsChannel.prototype._remove = async function (base) {
    await this._dir.remove(base + '.json');
    await this._dir.remove(base + '.ready');
  };

  // The single authentication chokepoint: read + cryptographically verify frame `seq`
  // in (`epoch`,`dir`). Used by BOTH delivery (_drainInbox) and bridge epoch adoption
  // (_adoptEpoch), so a control-plane decision is never made on unverified input.
  // Returns { status, msg, ts }:
  //   'wait'   — not yet fully present/synced (missing/torn sentinel, or short payload) → retry
  //   'reject' — present but bad (wrong fields, stale ts, or bad HMAC) → caller removes it
  //   'ok'     — verified; `msg` is the parsed wire message, `ts` its timestamp
  FsChannel.prototype._verify = async function (epoch, dir, seq) {
    var base = 'sessions/' + this.session + '/' + epoch + '/' + dir + '/' + seq;
    var rawR = await this._dir.read(base + '.ready');
    if (rawR == null) return { status: 'wait' };
    var sent; try { sent = JSON.parse(rawR); } catch (e) { return { status: 'wait' }; }   // torn sentinel mid-sync
    if (!sent || sent.v !== FS_VERSION || sent.session !== this.session || sent.epoch !== epoch || sent.dir !== dir || sent.seq !== seq) return { status: 'reject' };
    if (Math.abs(this._now() - sent.ts) > SKEW_MS) { this._warn('stale frame ' + dir + '/' + seq + ' (clock skew > ' + (SKEW_MS / 1000) + 's, or replay)'); return { status: 'reject' }; }
    var payload = await this._dir.read(base + '.json');
    if (payload == null || payload.length !== sent.len) return { status: 'wait' };          // not fully synced yet
    var expect = await this._hmac(canon(this.session, epoch, dir, seq, sent.ts, sent.len, payload));
    if (!ctEq(expect, sent.sig)) { this._warn('bad frame HMAC ' + dir + '/' + seq + ' (forged or tampered) — dropped'); return { status: 'reject' }; }
    var msg; try { msg = JSON.parse(payload); } catch (e) { return { status: 'reject' }; }
    return { status: 'ok', msg: msg, ts: sent.ts };
  };

  // Consume the peer's outbox: verify + deliver in seq order, exactly once.
  FsChannel.prototype._drainInbox = async function () {
    var dir = inboxOf(this.role);
    var dpath = this._epochDir(dir);
    var names = await this._dir.list(dpath);
    var readys = [];
    for (var i = 0; i < names.length; i++) {
      var m = /^(\d+)\.ready$/.exec(names[i]);
      if (m) readys.push(parseInt(m[1], 10));
    }
    readys.sort(function (a, b) { return a - b; });

    for (var j = 0; j < readys.length; j++) {
      var seq = readys[j];
      var base = dpath + '/' + seq;
      if (seq <= this._lastIn) { await this._remove(base); continue; }   // already delivered → sweep
      if (seq !== this._lastIn + 1) break;                               // gap → wait for the missing seq

      var v = await this._verify(this.epoch, dir, seq);
      if (v.status === 'wait') break;                                    // not fully synced → retry next tick
      if (v.status === 'reject') { await this._remove(base); break; }    // forged/stale → drop it, retry the slot

      this._lastIn = seq;
      if (this.role === 'bridge') this._setState('open');               // a page is talking
      await this._remove(base);
      try { this._onMessage(v.msg); } catch (e) { this._log('onMessage threw'); }
    }
  };

  // ── tick: one poll cycle (host schedules it; must not overlap) ──

  FsChannel.prototype.tick = async function () {
    if (this.state === 'closed') return;
    if (this.role === 'bridge') {
      if (this._now() - this._lastAnnounce > ANNOUNCE_INTERVAL_MS) await this._announce();  // slow refresh — the only periodic write
      await this._adoptEpoch();
      if (!this.epoch) return;                                           // no page has dialled yet
    } else if (this._pinnedSession) {                                    // host pinned us to one bridge (multi-bridge folder)
      if (this.session !== this._pinnedSession) {                        // first tick → mint the epoch, dial in
        this.session = this._pinnedSession;
        this.epoch = this._rand();
        this._resetConn();
        await this._dir.mkdirp(this._epochDir('to-bridge'));
        await this._dir.mkdirp(this._epochDir('to-page'));
      }
      this._setState('open');                                           // liveness is the host's job (it drops us when the announce goes stale)
    } else {
      var ok = await this._discover();
      if (ok === 'stale') { this._setState('offline'); return; }         // announce present but heartbeat dead → bridge process down (not just dialing)
      if (!ok) { this._setState('connecting'); return; }                 // no/forged announce → still dialing
      this._setState('open');                                            // the bridge is announcing
    }
    if (!this.session || !this.epoch) return;
    while (this._outQueue.length) {
      var wrote = await this._writeFrame(this._outQueue[0]);
      if (!wrote) break;                  // transient write failure → keep it queued, retry next tick
      this._outQueue.shift();
    }
    await this._drainInbox();
  };

  FsChannel.prototype.stop = function () { this._setState('closed'); this._outQueue.length = 0; };

  return { FsChannel: FsChannel, FS_VERSION: FS_VERSION };
})();

// ESM exports for node / Deno / JSR. The IIFE above keeps the internal helpers
// (canon, ctEq, outboxOf, …) scoped, so app builds that flat-concat this file (e.g.
// weir strips the `export`s and inlines the rest) gain no extra top-level names.
export const FsChannel = GcuFsChannel.FsChannel;
export const FS_VERSION = GcuFsChannel.FS_VERSION;
// Browser: the shim loads this as a plain inlined script and reads this global.
if (typeof globalThis !== 'undefined') globalThis.GcuFsChannel = GcuFsChannel;

// smoke-fs.mjs — proves the `fs` transport core (fs-channel.js) end to end, zero
// deps, no browser, no port. Two FsChannel peers share one temp dir: a BRIDGE peer
// and a PAGE peer. Drives the full handshake + a tool round-trip, attacks the
// signed-sentinel framing (tamper, partial sync, replay) asserting each fails
// closed, then reconnects a fresh page (the browser-reload case) and asserts the
// stale epoch is swept. See TRANSPORTS.md §3–4.
//
// NOTE: one shared dir with atomic rename — this proves the protocol LOGIC, not a
// real sync engine. The cross-machine hazards (partial/reordered/replayed frames)
// are exercised by hand-crafting them below.
//
// Run: node tools/smoke-fs.mjs   (exit 0 = pass)

import { mkdtemp, readFile, writeFile, rename, readdir, rm, mkdir } from 'node:fs/promises';
import { createHmac, randomBytes } from 'node:crypto';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { FsChannel, FS_VERSION } from '../fs-channel.js';

let failed = 0;
function ok(cond, msg) { if (cond) { console.log('  ✓ ' + msg); } else { failed++; console.log('  ✗ ' + msg); } }

// ── node adapters (the bridge/shim provide their own; the smoke provides these) ──

const SECRET = Buffer.from('shared-cluster-secret-for-the-smoke');
const hmac = async (str) => createHmac('sha256', SECRET).update(str).digest('hex');
const randomId = () => randomBytes(8).toString('hex');

function makeNodeDir(root) {
  const P = (name) => join(root, name);
  return {
    async read(name) { try { return await readFile(P(name), 'utf8'); } catch { return null; } },
    // atomic on a single fs: write a temp then rename (a reader never sees a partial file)
    async write(name, str) { const f = P(name); await writeFile(f + '.tmp', str); await rename(f + '.tmp', f); },
    async list(dir) { try { return await readdir(P(dir)); } catch { return []; } },
    async remove(name) { try { await rm(P(name)); } catch { /* missing */ } },
    async mkdirp(dir) { await mkdir(P(dir), { recursive: true }); },
    async rmrf(dir) { try { await rm(P(dir), { recursive: true, force: true }); } catch { /* missing */ } },
  };
}

async function pump(a, b, done, max = 60) {
  for (let i = 0; i < max; i++) { await a.tick(); await b.tick(); if (done()) return true; }
  return done();
}

async function main() {
  const root = await mkdtemp(join(tmpdir(), 'numen-fs-'));
  const dir = makeNodeDir(root);
  let results = 0;   // tool_results the bridge has received (across connections)

  function makeBridge() {
    const b = new FsChannel({
      role: 'bridge', dir, hmac, randomId,
      onMessage(m) {
        if (m.type === 'hello') b.send({ type: 'welcome', id: 'page-1', protocol: FS_VERSION });
        else if (m.type === 'tools_changed') b.send({ type: 'tool_invoke', callId: 'c' + results, name: 'ping', input: { n: 7 } });
        else if (m.type === 'tool_result') { b._lastResult = m; results++; }
      },
    });
    return b;
  }
  function makePage(tag) {
    const seen = [];
    const p = new FsChannel({
      role: 'page', dir, hmac, randomId,
      onMessage(m) {
        seen.push(m.type);
        if (m.type === 'welcome') p.send({ type: 'tools_changed', tools: [{ name: 'ping' }] });
        else if (m.type === 'tool_invoke') p.send({ type: 'tool_result', callId: m.callId, result: { pong: m.input.n * 2 } });
      },
    });
    p._seen = seen;
    return p;
  }

  // ── 1. full round-trip ──
  console.log('round-trip:');
  const bridge = makeBridge();
  const page = makePage('p1');
  await bridge.start();
  page.send({ type: 'hello', name: 'weir', path: 'test' });   // queued before session/epoch exist
  await page.start();
  await pump(bridge, page, () => results >= 1);
  ok(page._seen.includes('welcome'), 'page received welcome');
  ok(page._seen.includes('tool_invoke'), 'page received tool_invoke');
  ok(bridge._lastResult && bridge._lastResult.result.pong === 14, 'payload round-tripped intact (7 → 14)');
  ok(JSON.stringify(page._seen) === JSON.stringify(['welcome', 'tool_invoke']), 'page delivered in order, exactly once');
  ok(page.state === 'open' && bridge.state === 'open', 'both peers reached state=open');

  const sess = page.session, ep = page.epoch;
  const toPage = `sessions/${sess}/${ep}/to-page`;           // bridge's outbox → the page reads it
  const nextSeq = page._lastIn + 1;                          // the next seq the page will accept

  // helper: craft a frame straight into the page's inbox (simulating the bridge).
  // Uses a live ts so the freshness gate passes — the attacks under test are bad
  // sig / short payload / replayed seq, NOT staleness.
  async function craft(seq, msgObj, { sig, len } = {}) {
    const payload = JSON.stringify(msgObj);
    const ts = Date.now();
    const realSig = await hmac(`${FS_VERSION}|${sess}|${ep}|to-page|${seq}|${ts}|${payload.length}|${payload}`);
    await dir.write(`${toPage}/${seq}.json`, len === 'short' ? payload.slice(0, -2) : payload);
    await dir.write(`${toPage}/${seq}.ready`, JSON.stringify({ v: FS_VERSION, session: sess, epoch: ep, dir: 'to-page', seq, ts, len: payload.length, sig: sig || realSig }));
  }

  // ── 2. tamper: bad signature at the next expected seq → not delivered ──
  console.log('tamper rejection:');
  await craft(nextSeq, { type: 'tool_invoke', callId: 'evil', name: 'ping', input: {} }, { sig: 'deadbeef' });
  const beforeTamper = page._seen.length;
  await page.tick();
  ok(page._seen.length === beforeTamper, 'forged frame (bad HMAC) was not delivered');
  ok(page._lastIn + 1 === nextSeq, 'cursor did not advance past the forged frame');

  // ── 3. partial sync: sentinel + short payload → wait; complete → deliver ──
  console.log('partial-sync tolerance:');
  await craft(nextSeq, { type: 'ping' }, { len: 'short' });
  const beforePartial = page._seen.length;
  await page.tick();
  ok(page._seen.length === beforePartial, 'short payload held back (len mismatch)');
  await craft(nextSeq, { type: 'ping' });                    // payload finishes syncing (full + good sig)
  await page.tick();
  ok(page._seen[page._seen.length - 1] === 'ping', 'frame delivered once the payload completed');

  // ── 4. replay: re-materialize the consumed frame → not re-delivered ──
  console.log('replay rejection:');
  const pingsNow = page._seen.filter((t) => t === 'ping').length;
  await craft(nextSeq, { type: 'ping' });                    // same (already-consumed) seq reappears
  await page.tick();
  ok(page._seen.filter((t) => t === 'ping').length === pingsNow, 'replayed (already-consumed seq) frame was not re-delivered');
  ok(!(await dir.list(toPage)).includes(`${nextSeq}.ready`), 'replayed frame was swept');

  // ── 5. reconnect: a fresh page (browser reload) handshakes anew; stale epoch swept ──
  console.log('reconnect:');
  const page2 = makePage('p2');
  page2.send({ type: 'hello', name: 'weir', path: 'test' });
  await page2.start();
  await pump(bridge, page2, () => results >= 2);
  ok(results >= 2, 'second connection completed a fresh tool round-trip');
  ok(page2.epoch !== ep, 'reconnect minted a new epoch');
  ok(!(await dir.list(`sessions/${sess}`)).includes(ep), 'bridge swept the stale (old-reload) epoch dir');

  // ── 6. forged epoch: a bad-HMAC hello must NOT win adoption or sweep the real one ──
  // (a folder-writer without the key trying a pre-auth handshake hijack/DoS)
  console.log('forged-epoch rejection:');
  const realEpoch = bridge.epoch;                         // page2's authenticated epoch
  const fbase = `sessions/${bridge.session}/forgedepoch/to-bridge`;
  await dir.mkdirp(fbase);
  const fpay = JSON.stringify({ type: 'hello', name: 'evil' });
  // fresh ts (would win ts-ranking) but signed with the WRONG key — bad HMAC
  await dir.write(`${fbase}/0.json`, fpay);
  await dir.write(`${fbase}/0.ready`, JSON.stringify({ v: FS_VERSION, session: bridge.session, epoch: 'forgedepoch', dir: 'to-bridge', seq: 0, ts: Date.now(), len: fpay.length, sig: 'deadbeef'.repeat(8) }));
  await bridge.tick(); await bridge.tick();
  ok(bridge.epoch === realEpoch, 'forged epoch (bad HMAC) was NOT adopted');
  ok((await dir.list(`sessions/${bridge.session}`)).includes(realEpoch), 'the authenticated epoch was NOT swept by the forgery');

  // ── stuck-write warning: a leaked FSA write-lock makes every frame-write fail; after a few
  // consecutive failures the channel warns LOUD (restart the browser) instead of hanging silent ──
  console.log('stuck-write warning:');
  {
    const warns = [];
    const stuckRoot = await mkdtemp(join(tmpdir(), 'numen-stuck-'));
    const badDir = makeNodeDir(stuckRoot);
    badDir.write = async () => { throw new Error('createWritable hung (simulated stuck lock)'); };
    const stuck = new FsChannel({ role: 'page', dir: badDir, hmac, now: () => Date.now(), randomId, session: 'stucksess', onWarn: (m) => warns.push(m) });
    stuck.send({ type: 'hello' });
    for (let i = 0; i < 6; i++) await stuck.tick();            // each tick tries the write, fails
    const stuckWarns = warns.filter((w) => /WRITE STUCK/.test(w));
    ok(stuckWarns.length === 1, 'warns exactly ONCE at the threshold (not every tick — no spam)');
    ok(stuckWarns.length && /restart the browser/i.test(stuckWarns[0]), 'the warning tells the user to RESTART THE BROWSER');
    await rm(stuckRoot, { recursive: true, force: true });
  }

  await rm(root, { recursive: true, force: true });
}

main().then(() => {
  console.log(failed ? `\nFAIL (${failed})` : '\nPASS');
  process.exit(failed ? 1 : 0);
}).catch((e) => { console.error(e); process.exit(1); });

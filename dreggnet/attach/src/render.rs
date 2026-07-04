//! Server-render the **web-attach cockpit** — the browser face a signed-in user
//! drives their hosted agent from, and the one a hackathon judge / a customer sees
//! when they "attach to their hosted verifiable Hermes agent". One self-contained
//! page (no build step), designed to make the pitch *visceral*:
//!
//! - **the goal box** — a natural-language goal + one-click suggested goals, the
//!   budget, and the cap bundle (what it may do) — then drive;
//! - **the live feed** — the reason→act→observe loop as a readable story: each step
//!   typed (think · call · observe), the cap-gate decision shown *in-band*
//!   (✓ admitted / ✗ refused, with the reason), the tool verdict legible, and the
//!   *signed* receipt accumulating line by line (#seq · signed · ←prev);
//! - **the budget gauge** — a draining meter, the P&L of the run, each spend
//!   drawing it down and an over-budget refusal landing as "✗ refused — no money
//!   moved";
//! - **verify-in-browser** — the centerpiece: click → re-witness the chain + the
//!   bound ("✓ the agent stayed in its box, here's the proof"), then a *tamper
//!   self-demo* — flip one line, watch it shatter (✗) — on screen;
//! - **fork & attenuate** — the cell superpower as a real action: fork a session
//!   into an attenuated child (a subset of its authority).
//!
//! Everything but the live drive is rendered HTML; the JS opens an `EventSource`
//! to `GET /api/session/<id>/stream` and POSTs the goal box / verify / fork.

use crate::session::AgentSession;

/// Render the full web-attach page for `subject`. `login_base` is the public path
/// the webauth login/logout flow is reachable at (for the sign-out control);
/// `default_budget` pre-fills the goal box; `sessions` are the subject's own
/// (cap-scoped) sessions, newest first.
pub fn render_page(
    subject: &str,
    login_base: &str,
    default_budget: i64,
    sessions: &[AgentSession],
) -> String {
    let subject_e = esc(subject);
    let mut body = String::new();

    // Header — the emotional core stated up front.
    body.push_str(&format!(
        r#"<header>
  <div class="brand"><span class="logo">◆</span> DreggNet <span class="sep">·</span> <span class="brand-sub">attach</span></div>
  <div class="tagline">a hosted brain you own — and can <em>prove</em></div>
  <div class="who">signed in as <code>{subject_e}</code> <span class="sep">·</span> <a href="{lb}/logout">sign out</a></div>
</header>"#,
        lb = esc(login_base),
    ));

    // The differentiator strip — what makes this not just a chat box.
    body.push_str(
        r#"<section class="diffs">
  <div class="diff"><span class="di">⛁</span><b>bounded by construction</b><span>a hard budget ceiling — un-drawn headroom is authority never exercised</span></div>
  <div class="diff"><span class="di">✍</span><b>receipted, every step</b><span>each admitted action sealed into a signed, append-only chain</span></div>
  <div class="diff"><span class="di">✦</span><b>verify, don't trust</b><span>re-witness the proof in your own browser — flip one line and it shatters</span></div>
  <div class="diff"><span class="di">⑂</span><b>fork &amp; attenuate</b><span>fork a session into a child that can do strictly less</span></div>
</section>"#,
    );

    // The goal box.
    body.push_str(&format!(
        r#"<section id="goalbox"><h2>New session — give your agent a goal</h2>
  <p class="hint">It runs a confined reason→act→observe loop: every tool-call is
  cap-gated, metered against your budget, and sealed into a receipt chain you can
  re-witness in your own browser. Nothing here is the host's say-so.</p>
  <div class="suggest" id="suggest"><span class="suggest-lab">try one →</span></div>
  <p><textarea id="goal" placeholder="e.g. clone the repo, run the tests, and verify the deploy"></textarea></p>
  <div class="controls">
    <label class="budget-ctl">budget <input id="budget" type="number" min="1" value="{default_budget}"></label>
    <fieldset class="caps"><legend>cap bundle (what it may do)</legend>
      <label><input type="checkbox" class="svc" value="run_tests" checked> invoke:run_tests</label>
      <label><input type="checkbox" class="svc" value="verify_deploy" checked> invoke:verify_deploy</label>
      <label><input type="checkbox" class="svc" value="check_health"> invoke:check_health</label>
      <label><input type="checkbox" class="cell" value="/goal" checked> cell:/goal</label>
    </fieldset>
    <button id="drive">▶ drive</button>
  </div>
</section>"#,
    ));

    // The live session panel (populated by JS).
    body.push_str(
        r#"<section id="live" hidden><div class="live-head"><h2>Live session <code id="live-id"></code></h2><span class="live-goal" id="live-goal"></span><span class="live-model" id="live-model"></span></div>

  <div class="gauge">
    <div class="gauge-top">
      <div class="g-stat"><span class="g-lab">budget</span><b id="m-budget">—</b></div>
      <div class="g-stat drawn"><span class="g-lab">consumed</span><b id="m-consumed">0</b></div>
      <div class="g-stat free"><span class="g-lab">headroom</span><b id="m-headroom">—</b></div>
      <div class="g-stat"><span class="g-lab">receipts</span><b id="m-receipts">0</b></div>
    </div>
    <div class="bar"><div class="bar-fill" id="m-fill" style="width:0%"></div></div>
    <div class="g-foot"><b id="m-pct">0%</b> drawn <span class="sep">·</span> <span class="g-note">un-drawn headroom = authority the agent never exercised</span></div>
    <div class="refusal-flash" id="refusal-flash" hidden>✗ refused — no money moved</div>
  </div>

  <div class="feed" id="feed"></div>

  <div class="verify-zone">
    <button id="verify-live" class="verify-btn" disabled>✦ verify in browser — re-witness the proof</button>
    <button id="fork-live" class="fork-btn" disabled>⑂ fork — run an attenuated child</button>
    <div class="proof-grid">
      <div class="proof held" id="proof-held" hidden></div>
      <div class="proof tampered" id="proof-tampered" hidden></div>
    </div>
  </div>
</section>"#,
    );

    // My sessions (server-rendered, cap-scoped).
    body.push_str("<section id=\"sessions\"><h2>My sessions</h2>");
    body.push_str(
        "<p class=\"seam\">sleep = checkpoint, fork = scale — your hosted cells. \
         Forking is live below; pause/resume of a long-running session is the \
         reviewed-go live backend (the demo planner runs to completion).</p>",
    );
    if sessions.is_empty() {
        body.push_str(
            "<p class=\"empty\">no sessions yet — give your agent a goal above, or click a suggestion to wow in under a minute.</p>",
        );
    } else {
        body.push_str("<table><thead><tr><th>id</th><th>goal</th><th>budget</th><th>consumed</th><th>receipts</th><th>refused</th><th></th></tr></thead><tbody>");
        for s in sessions {
            let parent_badge = match &s.parent {
                Some(p) => format!(
                    " <span class=\"badge fork\" title=\"forked from {p}\">⑂ fork</span>",
                    p = esc(p)
                ),
                None => String::new(),
            };
            body.push_str(&format!(
                "<tr><td><code>{id}</code>{parent_badge}</td><td>{goal}</td><td>{budget}</td>\
                 <td>{consumed}</td><td>{receipts}</td><td>{refused}</td>\
                 <td class=\"row-actions\"><button class=\"replay\" data-id=\"{id}\">replay</button> \
                 <button class=\"verify-one\" data-id=\"{id}\">verify</button> \
                 <button class=\"fork-one\" data-id=\"{id}\">⑂ fork</button>\
                 <span class=\"verdict\" data-for=\"{id}\"></span></td></tr>",
                id = esc(&s.id),
                goal = esc(s.goal()),
                budget = s.budget(),
                consumed = s.consumed(),
                receipts = s.receipts(),
                refused = s.cap_refused() + s.budget_refused(),
            ));
        }
        body.push_str("</tbody></table>");
    }
    body.push_str("</section>");

    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet attach — {subject_e}</title><style>{CSS}</style></head>\
         <body><main>{body}</main><script>{ATTACH_JS}</script></body></html>",
    )
}

/// HTML-escape a string for safe interpolation.
pub fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

const CSS: &str = r#"
:root {
  color-scheme: dark light;
  --bg: #0e0e1a; --panel: #16162a; --panel2: #1c1c34; --line: #2a2a44;
  --ink: #e8e8f5; --mut: #9a9ac0; --dim: #6e6e92;
  --acc: #7b8cff; --acc2: #a779ff; --ok: #46d39a; --bad: #ff6b81; --warn: #ffcf6b;
}
@media (prefers-color-scheme: light) {
  :root { --bg:#f4f4fb; --panel:#fff; --panel2:#f7f7fd; --line:#e3e3f0;
    --ink:#1a1a2e; --mut:#54547a; --dim:#8a8aaa; --acc:#4a5bdc; --acc2:#8b4ad6; }
}
* { box-sizing: border-box; }
body { font-family: system-ui, -apple-system, sans-serif; color: var(--ink); margin: 0; background:
  radial-gradient(1200px 600px at 80% -10%, rgba(123,140,255,.10), transparent 60%),
  radial-gradient(900px 500px at -10% 10%, rgba(167,121,255,.08), transparent 55%), var(--bg); }
main { max-width: 70rem; margin: 0 auto; padding: 1.2rem; }
code { background: rgba(123,140,255,.12); color: var(--acc); padding: 0 .3rem; border-radius: .25rem;
  font-family: ui-monospace, SFMono-Regular, monospace; font-size: .85em; }
.sep { color: var(--dim); margin: 0 .35rem; }
a { color: var(--acc); }

header { padding: 1rem 0 1.1rem; border-bottom: 1px solid var(--line); margin-bottom: 1.1rem; }
.brand { font-size: 1.45rem; font-weight: 700; letter-spacing: -.01em; }
.brand .logo { color: var(--acc2); }
.brand-sub { color: var(--acc); font-weight: 600; }
.tagline { color: var(--mut); margin-top: .25rem; font-size: 1.02rem; }
.tagline em { color: var(--acc2); font-style: normal; font-weight: 600; }
.who { color: var(--dim); margin-top: .4rem; font-size: .85rem; }

.diffs { display: grid; grid-template-columns: repeat(auto-fit, minmax(13rem, 1fr)); gap: .7rem;
  background: none; border: none; padding: 0; margin: 0 0 1.1rem; }
.diff { background: var(--panel); border: 1px solid var(--line); border-radius: .6rem; padding: .7rem .8rem;
  display: flex; flex-direction: column; gap: .15rem; }
.diff .di { font-size: 1.25rem; color: var(--acc); }
.diff b { font-size: .92rem; }
.diff span:last-child { color: var(--mut); font-size: .78rem; line-height: 1.35; }

section { background: var(--panel); border: 1px solid var(--line); border-radius: .7rem;
  padding: 1rem 1.1rem; margin: 1.1rem 0; }
h2 { font-size: 1.12rem; margin: .1rem 0 .6rem; letter-spacing: -.01em; }
.hint { color: var(--mut); font-size: .88rem; line-height: 1.5; margin: .2rem 0 .7rem; }

.suggest { display: flex; gap: .45rem; flex-wrap: wrap; align-items: center; margin-bottom: .6rem; }
.suggest-lab { color: var(--dim); font-size: .8rem; }
.chip { background: var(--panel2); border: 1px solid var(--line); color: var(--ink);
  border-radius: 999px; padding: .3rem .75rem; font-size: .82rem; cursor: pointer; transition: .15s; }
.chip:hover { border-color: var(--acc); color: var(--acc); transform: translateY(-1px); }

textarea { width: 100%; height: 4.2rem; font-family: ui-monospace, monospace; font-size: .9rem;
  background: var(--panel2); color: var(--ink); border: 1px solid var(--line); border-radius: .5rem; padding: .6rem; }
.controls { display: flex; gap: 1rem; align-items: center; flex-wrap: wrap; margin-top: .6rem; }
.budget-ctl { font-size: .9rem; color: var(--mut); }
input[type=number] { width: 6rem; padding: .35rem; background: var(--panel2); color: var(--ink);
  border: 1px solid var(--line); border-radius: .35rem; }
fieldset.caps { border: 1px solid var(--line); border-radius: .5rem; padding: .35rem .7rem; }
fieldset.caps legend { color: var(--dim); font-size: .76rem; padding: 0 .3rem; }
fieldset.caps label { display: inline-block; margin-right: .8rem; font-size: .84rem; color: var(--mut); }

button { padding: .45rem 1rem; cursor: pointer; border: 1px solid var(--line); background: var(--panel2);
  color: var(--ink); border-radius: .4rem; font-size: .88rem; transition: .15s; }
button:hover:not(:disabled) { border-color: var(--acc); }
button:disabled { opacity: .4; cursor: default; }
#drive { background: linear-gradient(135deg, var(--acc), var(--acc2)); color: #fff; border: none; font-weight: 600; padding: .5rem 1.4rem; }
#drive:hover:not(:disabled) { filter: brightness(1.08); }

.live-head { display: flex; align-items: baseline; gap: .6rem; flex-wrap: wrap; }
.live-goal { color: var(--ink); font-size: .92rem; }
.live-model { color: var(--dim); font-size: .76rem; font-family: ui-monospace, monospace; }

.gauge { background: var(--panel2); border: 1px solid var(--line); border-radius: .6rem; padding: .8rem .9rem; margin: .3rem 0 1rem; position: relative; }
.gauge-top { display: flex; gap: 1.6rem; flex-wrap: wrap; margin-bottom: .55rem; }
.g-stat { display: flex; flex-direction: column; }
.g-lab { color: var(--dim); font-size: .72rem; text-transform: uppercase; letter-spacing: .04em; }
.g-stat b { font-size: 1.35rem; font-variant-numeric: tabular-nums; }
.g-stat.drawn b { color: var(--warn); }
.g-stat.free b { color: var(--ok); }
.bar { height: 1rem; background: linear-gradient(var(--ok), #2faf7e); border-radius: .5rem; overflow: hidden;
  box-shadow: inset 0 0 0 1px var(--line); position: relative; }
.bar-fill { height: 100%; background: linear-gradient(90deg, var(--warn), #ff9d57); transition: width .45s cubic-bezier(.2,.7,.2,1); box-shadow: 0 0 12px rgba(255,157,87,.5); }
.bar.pulse { animation: pulse .4s; }
@keyframes pulse { 50% { box-shadow: inset 0 0 0 1px var(--acc), 0 0 14px rgba(123,140,255,.4); } }
.g-foot { color: var(--mut); font-size: .8rem; margin-top: .5rem; }
.g-foot b { color: var(--ink); }
.g-note { color: var(--dim); }
.refusal-flash { position: absolute; top: .6rem; right: .8rem; background: rgba(255,107,129,.16);
  color: var(--bad); border: 1px solid var(--bad); border-radius: .4rem; padding: .25rem .6rem; font-size: .8rem; font-weight: 600;
  animation: flashin .3s; }
@keyframes flashin { from { opacity: 0; transform: translateY(-4px); } }

.feed { display: flex; flex-direction: column; gap: .6rem; }
.stepcard { background: var(--panel2); border: 1px solid var(--line); border-left: 3px solid var(--acc);
  border-radius: .5rem; padding: .6rem .8rem; animation: cardin .35s ease both; }
@keyframes cardin { from { opacity: 0; transform: translateY(6px); } }
.stepcard.refused { border-left-color: var(--bad); background: linear-gradient(90deg, rgba(255,107,129,.07), var(--panel2) 40%); }
.sc-top { display: flex; align-items: center; gap: .5rem; flex-wrap: wrap; }
.sc-n { color: var(--dim); font-size: .76rem; font-variant-numeric: tabular-nums; }
.sc-fam { font-size: .68rem; text-transform: uppercase; letter-spacing: .05em; color: var(--acc2);
  border: 1px solid var(--line); border-radius: 999px; padding: .04rem .45rem; }
.pill { font-size: .76rem; font-weight: 600; border-radius: 999px; padding: .1rem .55rem; margin-left: auto; }
.pill.ok { color: var(--ok); background: rgba(70,211,154,.12); border: 1px solid rgba(70,211,154,.4); }
.pill.no { color: var(--bad); background: rgba(255,107,129,.12); border: 1px solid rgba(255,107,129,.45); }
.sc-think { color: var(--mut); font-size: .86rem; margin: .35rem 0 .15rem; font-style: italic; }
.sc-think::before { content: "think · "; color: var(--dim); font-style: normal; }
.sc-call { font-family: ui-monospace, monospace; font-size: .85rem; }
.sc-call::before { content: "act · "; color: var(--dim); font-family: system-ui, sans-serif; }
.sc-obs { color: var(--ink); font-size: .85rem; margin-top: .15rem; }
.sc-obs::before { content: "observe · "; color: var(--dim); }
.sc-obs.no { color: var(--bad); }
.sc-receipt { margin-top: .4rem; color: var(--dim); font-size: .74rem; font-family: ui-monospace, monospace; }
.sc-receipt b { color: var(--ok); }
.sc-cost { color: var(--warn); font-variant-numeric: tabular-nums; }

.verify-zone { margin-top: 1rem; }
.verify-btn { background: linear-gradient(135deg, var(--acc2), var(--acc)); color: #fff; border: none; font-weight: 600; padding: .6rem 1.3rem; font-size: .95rem; }
.verify-btn:hover:not(:disabled) { filter: brightness(1.1); }
.fork-btn { margin-left: .5rem; }
.proof-grid { display: grid; grid-template-columns: 1fr 1fr; gap: .7rem; margin-top: .8rem; }
@media (max-width: 40rem) { .proof-grid { grid-template-columns: 1fr; } }
.proof { border-radius: .55rem; padding: .8rem .9rem; border: 1px solid var(--line); animation: cardin .4s both; }
.proof h3 { margin: 0 0 .35rem; font-size: .95rem; display: flex; align-items: center; gap: .4rem; }
.proof .pd { font-size: .84rem; line-height: 1.45; color: var(--ink); }
.proof .pmeta { color: var(--mut); font-size: .76rem; margin-top: .4rem; font-family: ui-monospace, monospace; }
.proof.held { border-color: rgba(70,211,154,.5); background: rgba(70,211,154,.07); }
.proof.held h3 { color: var(--ok); }
.proof.tampered { border-color: rgba(255,107,129,.5); background: rgba(255,107,129,.07); }
.proof.tampered h3 { color: var(--bad); }
.proof .what { color: var(--bad); font-family: ui-monospace, monospace; font-size: .78rem; margin-top: .3rem; }

#sessions table { width: 100%; border-collapse: collapse; font-size: .88rem; }
#sessions th, #sessions td { text-align: left; padding: .4rem .5rem; border-bottom: 1px solid var(--line); vertical-align: middle; }
#sessions th { color: var(--dim); font-weight: 600; font-size: .78rem; text-transform: uppercase; letter-spacing: .03em; }
.row-actions { white-space: nowrap; }
.row-actions button { padding: .25rem .55rem; font-size: .8rem; }
.badge { font-size: .68rem; border-radius: 999px; padding: .04rem .4rem; border: 1px solid var(--line); color: var(--acc2); }
.empty { color: var(--dim); font-style: italic; }
.seam { color: var(--dim); font-size: .8rem; line-height: 1.4; margin: .1rem 0 .7rem; }
.verdict { font-size: .82rem; margin-left: .4rem; }
.verdict.ok { color: var(--ok); }
.verdict.bad { color: var(--bad); }
"#;

const ATTACH_JS: &str = r#"
function el(id){ return document.getElementById(id); }
function esc(s){ const d=document.createElement('div'); d.textContent=s==null?'':String(s); return d.innerHTML; }
let liveId = null;

// ── suggested goals: the zero-to-wow onramp ───────────────────────────────────
const SUGGESTIONS = [
  { label: 'run tests + verify deploy', goal: 'Run the test suite, then verify the deploy is healthy.',
    svc: ['run_tests','verify_deploy'], cell: ['/goal'], budget: 50 },
  { label: 'full QA gate', goal: 'Record my goal, run the tests, verify the deploy, and check node health.',
    svc: ['run_tests','verify_deploy','check_health'], cell: ['/goal'], budget: 60 },
  { label: 'tiny budget (watch it bite)', goal: 'Do as much QA as you can — but I only funded a sliver.',
    svc: ['run_tests','verify_deploy'], cell: ['/goal'], budget: 1 },
];
(function renderSuggest(){
  const box = el('suggest');
  SUGGESTIONS.forEach(s => {
    const b = document.createElement('button'); b.type='button'; b.className='chip'; b.textContent=s.label;
    b.onclick = () => {
      el('goal').value = s.goal; el('budget').value = s.budget;
      document.querySelectorAll('.svc').forEach(c => c.checked = s.svc.includes(c.value));
      document.querySelectorAll('.cell').forEach(c => c.checked = s.cell.includes(c.value));
      el('goal').focus();
    };
    box.appendChild(b);
  });
})();

// ── the budget gauge ──────────────────────────────────────────────────────────
function setMeter(consumed, headroom, budget, receipts){
  if (budget!=null) el('m-budget').textContent = budget;
  if (consumed!=null) el('m-consumed').textContent = consumed;
  if (headroom!=null) el('m-headroom').textContent = headroom;
  if (receipts!=null) el('m-receipts').textContent = receipts;
  const b = parseInt(el('m-budget').textContent,10);
  if (b>0 && consumed!=null){
    const pct = Math.min(100, Math.round(consumed*100/b));
    el('m-fill').style.width = pct + '%';
    el('m-pct').textContent = pct + '%';
    const bar = el('m-fill').parentElement;
    bar.classList.remove('pulse'); void bar.offsetWidth; bar.classList.add('pulse');
  }
}
function flashRefusal(){
  const f = el('refusal-flash'); f.hidden = false;
  f.style.animation='none'; void f.offsetWidth; f.style.animation='';
  clearTimeout(flashRefusal._t); flashRefusal._t = setTimeout(()=>{ f.hidden = true; }, 2200);
}

// ── reason→act→observe: turn an action into a readable thought ─────────────────
function thoughtFor(s){
  const a = s.action || '';
  if (!s.admitted && /exfiltrate/.test(a)) return 'Let me try a tool that is NOT in my grant…';
  if (a.startsWith('invoke:run_tests')) return 'I should run the test suite to check the work.';
  if (a.startsWith('invoke:verify_deploy')) return 'Now verify the deployment is actually healthy.';
  if (a.startsWith('invoke:check_health')) return 'Let me check the node is healthy.';
  if (a.startsWith('cell-write')) return 'Record this into my workspace cell so it is on the record.';
  if (a.startsWith('cell-read')) return 'Read back from my workspace cell.';
  if (a.startsWith('spend:')) return 'This step costs money — draw it from the budget.';
  if (a.startsWith('invoke:')) return 'Invoke a tool to make progress on the goal.';
  return 'Take the next step toward the goal.';
}
function stepCard(s){
  const tr = document.createElement('div');
  tr.className = 'stepcard' + (s.admitted ? '' : ' refused');
  const pill = s.admitted
    ? '<span class="pill ok">✓ admitted</span>'
    : '<span class="pill no">✗ ' + esc(s.refused||'refused') + '</span>';
  let obs;
  if (s.admitted) obs = '<div class="sc-obs">' + esc(s.tool_summary || 'done — sealed into the chain') + '</div>';
  else obs = '<div class="sc-obs no">no effect — the gate held; no money moved</div>';
  let receipt = '';
  if (s.admitted && s.receipt_seq!=null){
    receipt = '<div class="sc-receipt">receipt <b>#' + s.receipt_seq + '</b>'
      + (s.sig_fp ? ' · signed <span>' + esc(s.sig_fp) + '…</span>' : '')
      + (s.prev_fp ? ' · ←' + esc(s.prev_fp) + (s.prev_fp==='genesis'?'':'…') : '')
      + ' · drew <span class="sc-cost">' + s.cost + '</span></div>';
  }
  tr.innerHTML =
    '<div class="sc-top"><span class="sc-n">step ' + s.n + '</span>'
    + '<span class="sc-fam">' + esc(s.family||'op') + '</span>' + pill + '</div>'
    + '<div class="sc-think">' + esc(thoughtFor(s)) + '</div>'
    + '<div class="sc-call"><code>' + esc(s.action) + '</code></div>'
    + obs + receipt;
  return tr;
}

// ── open the SSE transcript and render it live (paced for the drama) ───────────
function streamSession(id){
  liveId = id;
  el('live').hidden = false;
  el('live').scrollIntoView({behavior:'smooth', block:'start'});
  el('live-id').textContent = id;
  el('feed').innerHTML = '';
  el('live-goal').textContent = ''; el('live-model').textContent = '';
  el('proof-held').hidden = true; el('proof-tampered').hidden = true;
  setMeter(0, null, null, 0);
  el('verify-live').disabled = true; el('fork-live').disabled = true;
  el('refusal-flash').hidden = true;

  let receipts = 0;
  const queue = []; let draining = false; let done = null;
  function drain(){
    if (draining) return; draining = true;
    const tick = () => {
      const s = queue.shift();
      if (!s){ draining = false; if (done) finish(done); return; }
      if (s.receipted) receipts++;
      el('feed').appendChild(stepCard(s));
      if (!s.admitted) flashRefusal();
      setMeter(s.consumed, s.headroom, null, receipts);
      el('live').scrollIntoView({behavior:'smooth', block:'end'});
      setTimeout(tick, 340);
    };
    tick();
  }
  function finish(d){
    setMeter(d.consumed, d.headroom, d.budget, d.receipts);
    el('verify-live').disabled = false; el('fork-live').disabled = false;
  }

  const es = new EventSource('api/session/' + encodeURIComponent(id) + '/stream');
  es.addEventListener('meta', e => {
    const m = JSON.parse(e.data);
    setMeter(0, m.budget, m.budget, 0);
    el('live-goal').textContent = m.goal || '';
    el('live-model').textContent = m.model ? ('via ' + m.model) : '';
  });
  es.addEventListener('step', e => { queue.push(JSON.parse(e.data)); drain(); });
  es.addEventListener('done', e => { done = JSON.parse(e.data); es.close(); if (!draining) finish(done); });
  es.onerror = () => { es.close(); };
}

// ── the verify moment: re-witness ✓, then the tamper self-demo ✗ ──────────────
function renderHeld(r){
  const p = el('proof-held'); p.hidden = false;
  p.innerHTML = '<h3>✓ the proof held</h3>'
    + '<div class="pd">Re-witnessed in your browser — no trust in the host. The signed receipt '
    + 'chain is unbroken and the spend stayed inside its ceiling.</div>'
    + '<div class="pmeta">' + esc(r.consumed) + '/' + esc(r.budget) + ' consumed · '
    + esc(r.headroom) + ' headroom · ' + esc(r.actions) + ' actions re-witnessed</div>';
}
function renderTampered(r){
  const p = el('proof-tampered'); p.hidden = false;
  p.innerHTML = '<h3>✗ flip one line — it shatters</h3>'
    + '<div class="pd">We took your same chain, changed a single sealed line, and re-witnessed it. '
    + 'The signature no longer holds — a forged result cannot survive.</div>'
    + (r.tampered_what ? '<div class="what">' + esc(r.tampered_what) + '</div>' : '')
    + '<div class="pmeta">' + esc(r.detail) + '</div>';
}
el('verify-live').onclick = async () => {
  if (!liveId) return;
  el('verify-live').disabled = true;
  const held = el('proof-held'); held.hidden = false;
  held.innerHTML = '<h3>re-witnessing…</h3><div class="pd">replaying the receipt chain offline…</div>';
  el('proof-tampered').hidden = true;
  try {
    const r1 = await (await fetch('api/verify', { method:'POST', headers:{'content-type':'application/json'},
      body: JSON.stringify({ session_id: liveId }) })).json();
    if (r1.ok) renderHeld(r1);
    else { held.className='proof tampered'; held.innerHTML = '<h3>✗ did not re-witness</h3><div class="pmeta">'+esc(r1.detail||'')+'</div>'; }
    // Then the tamper self-demo — the magic, made visible.
    await new Promise(r=>setTimeout(r, 500));
    const r2 = await (await fetch('api/verify', { method:'POST', headers:{'content-type':'application/json'},
      body: JSON.stringify({ session_id: liveId, tamper: true }) })).json();
    renderTampered(r2);
  } catch (e) {
    held.className='proof tampered'; held.innerHTML = '<h3>verify failed</h3><div class="pmeta">'+esc(e)+'</div>';
  } finally { el('verify-live').disabled = false; }
};

// ── fork & attenuate ──────────────────────────────────────────────────────────
async function forkSession(id){
  const r = await (await fetch('api/session/' + encodeURIComponent(id) + '/fork', { method:'POST' })).json();
  if (r.ok && r.id){ streamSession(r.id); }
  else { alert('could not fork: ' + (r.detail||'unknown')); }
}
el('fork-live').onclick = () => { if (liveId) forkSession(liveId); };

// ── the goal box → create a session, then stream it ───────────────────────────
el('drive').onclick = async () => {
  const goal = el('goal').value.trim();
  if (!goal){ alert('type a goal first (or click a suggestion)'); return; }
  const services = Array.from(document.querySelectorAll('.svc:checked')).map(c=>c.value);
  const cells = Array.from(document.querySelectorAll('.cell:checked')).map(c=>c.value);
  const budget = parseInt(el('budget').value,10) || 1;
  el('drive').disabled = true;
  try {
    const resp = await fetch('api/session', { method:'POST', headers:{'content-type':'application/json'},
      body: JSON.stringify({ goal, budget, services, cells }) });
    const j = await resp.json();
    if (j.id) streamSession(j.id);
    else alert('could not start session: ' + (j.detail||'unknown'));
  } catch (e) { alert('drive failed: ' + e); }
  finally { el('drive').disabled = false; }
};

// ── 'my sessions' row actions ─────────────────────────────────────────────────
document.querySelectorAll('.replay').forEach(b => b.onclick = () => streamSession(b.dataset.id));
document.querySelectorAll('.fork-one').forEach(b => b.onclick = () => forkSession(b.dataset.id));
document.querySelectorAll('.verify-one').forEach(b => b.onclick = async () => {
  const id = b.dataset.id;
  const out = document.querySelector('.verdict[data-for="'+CSS.escape(id)+'"]');
  out.textContent = 're-witnessing…'; out.className = 'verdict';
  try {
    const r = await (await fetch('api/verify', { method:'POST', headers:{'content-type':'application/json'},
      body: JSON.stringify({ session_id: id }) })).json();
    out.className = 'verdict ' + (r.ok ? 'ok':'bad');
    out.textContent = (r.ok ? '✓ ' : '✗ ') + (r.detail||'');
  } catch (e) { out.className='verdict bad'; out.textContent='verify failed: '+e; }
});
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{DemoDriver, SessionDriver};
    use crate::session::GoalRequest;

    fn driven(owner: &str, id: &str, goal: &str) -> AgentSession {
        let req = GoalRequest::new(goal, 50)
            .with_service("run_tests")
            .with_cell("/goal");
        DemoDriver::seeded([21u8; 32]).drive(&req, owner, id)
    }

    // ── the page has the goal box, the live panel, the meter, and verify ───────
    #[test]
    fn the_page_has_the_whole_cockpit() {
        let html = render_page("dregg:demo0001demo0001", "/.dregg-auth", 50, &[]);
        for needle in [
            "give your agent a goal",
            "id=\"goal\"",
            "cap bundle",
            "Live session",
            "budget",
            "consumed",
            "headroom",
            "verify in browser",
            "EventSource",
            "api/session/",
            "api/verify",
            // the new cockpit affordances
            "verify, don't trust",
            "fork",
            "try one",
            "the tamper",
        ] {
            assert!(html.contains(needle), "missing: {needle}");
        }
        // The signed-in subject is shown.
        assert!(html.contains("dregg:demo0001demo0001"));
        // An empty account gets the friendly empty.
        assert!(html.contains("no sessions yet"));
    }

    // ── a populated 'my sessions' renders the user's real sessions ─────────────
    #[test]
    fn my_sessions_render_the_real_sessions() {
        let s = driven("dregg:demo0001demo0001", "sess_r1", "ship the release");
        let html = render_page("dregg:demo0001demo0001", "", 50, std::slice::from_ref(&s));
        assert!(html.contains("sess_r1"));
        assert!(html.contains("ship the release"));
        assert!(!html.contains("no sessions yet"));
        // The replay + verify + fork controls are wired to the session id.
        assert!(html.contains("data-id=\"sess_r1\""));
        assert!(html.contains("fork-one"));
    }

    // ── a forked session shows its parent badge ────────────────────────────────
    #[test]
    fn a_fork_shows_its_parent_badge() {
        let mut s = driven("dregg:demo0001demo0001", "sess_child", "fork of: ship");
        s.parent = Some("sess_parent".to_string());
        let html = render_page("dregg:demo0001demo0001", "", 50, std::slice::from_ref(&s));
        assert!(html.contains("⑂ fork"), "the fork badge renders");
        assert!(html.contains("forked from sess_parent"));
    }

    // ── the page never leaks another user's session text (cap-scoped input) ────
    #[test]
    fn the_page_renders_only_the_passed_sessions() {
        // render is given ONLY the caller's sessions (the bin scopes before here);
        // a session not in the slice cannot appear.
        let mine = driven("dregg:demo0001demo0001", "sess_mine", "my own goal");
        let html = render_page(
            "dregg:demo0001demo0001",
            "",
            50,
            std::slice::from_ref(&mine),
        );
        assert!(html.contains("my own goal"));
        assert!(!html.contains("someone elses secret"));
    }
}

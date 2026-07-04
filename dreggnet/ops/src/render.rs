//! The self-contained ops dashboard HTML.
//!
//! One page, no external assets: it fetches `/api/snapshot` (the aggregated
//! [`crate::CloudSnapshot`]) on an interval and `/api/logs` on demand, and renders
//! the four asks — whole-cloud health, all-activity, status tables, and logs —
//! as tabs. Served behind the Caddy admin-password gate; same-origin `fetch`
//! inherits that auth automatically.

/// The dashboard page (static HTML/CSS/JS).
pub fn dashboard_html() -> &'static str {
    PAGE
}

const PAGE: &str = r##"<!doctype html>
<html lang="en"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>DreggNet Cloud — Ops</title>
<style>
:root{--bg:#0e1116;--panel:#161b22;--panel2:#1c2330;--bd:#2a3340;--fg:#d7dde6;--mut:#8b97a7;--acc:#5cc8ff;--ok:#34d058;--warn:#f0b429;--bad:#f24e4e;}
*{box-sizing:border-box}
body{margin:0;font:14px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;background:var(--bg);color:var(--fg)}
header{display:flex;align-items:center;gap:1rem;padding:.7rem 1.1rem;background:var(--panel);border-bottom:1px solid var(--bd);position:sticky;top:0;z-index:5}
header h1{font-size:1rem;margin:0;font-weight:600;letter-spacing:.02em}
.pill{padding:.15rem .55rem;border-radius:1rem;font-size:.8rem;font-weight:600}
.pill.healthy{background:rgba(52,208,88,.16);color:var(--ok)}
.pill.degraded{background:rgba(240,180,41,.16);color:var(--warn)}
.pill.down{background:rgba(242,78,78,.16);color:var(--bad)}
.spacer{flex:1}
.meta{color:var(--mut);font-size:.8rem}
nav{display:flex;gap:.25rem;padding:.4rem 1.1rem 0;background:var(--panel);border-bottom:1px solid var(--bd)}
nav button{background:none;border:none;border-bottom:2px solid transparent;color:var(--mut);padding:.5rem .8rem;cursor:pointer;font:inherit}
nav button.active{color:var(--fg);border-bottom-color:var(--acc)}
main{padding:1.1rem;max-width:1400px;margin:0 auto}
section{display:none}
section.active{display:block}
.tiles{display:grid;grid-template-columns:repeat(auto-fill,minmax(180px,1fr));gap:.7rem;margin-bottom:1.1rem}
.tile{background:var(--panel);border:1px solid var(--bd);border-radius:.5rem;padding:.8rem}
.tile .k{color:var(--mut);font-size:.75rem;text-transform:uppercase;letter-spacing:.04em}
.tile .v{font-size:1.5rem;font-weight:600;margin-top:.2rem}
.tile .v.ok{color:var(--ok)}.tile .v.bad{color:var(--bad)}.tile .v.warn{color:var(--warn)}
.svc{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:.6rem;margin-bottom:1.1rem}
.svc .s{background:var(--panel);border:1px solid var(--bd);border-radius:.5rem;padding:.6rem .8rem;display:flex;justify-content:space-between;align-items:center}
.dot{width:.6rem;height:.6rem;border-radius:50%;display:inline-block;margin-right:.4rem}
.dot.up{background:var(--ok)}.dot.down{background:var(--bad)}.dot.other{background:var(--mut)}
h2{font-size:.95rem;color:var(--fg);border-bottom:1px solid var(--bd);padding-bottom:.35rem;margin:1.4rem 0 .7rem}
table{width:100%;border-collapse:collapse;font-size:.82rem;background:var(--panel);border:1px solid var(--bd);border-radius:.5rem;overflow:hidden}
th,td{text-align:left;padding:.4rem .6rem;border-bottom:1px solid var(--bd);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;max-width:380px}
th{color:var(--mut);font-weight:600;background:var(--panel2);text-transform:uppercase;font-size:.7rem;letter-spacing:.04em}
tr:last-child td{border-bottom:none}
.mono{color:var(--mut)}
.tag{padding:.05rem .4rem;border-radius:.3rem;background:var(--panel2);font-size:.72rem}
.tag.ok{color:var(--ok)}.tag.bad{color:var(--bad)}.tag.warn{color:var(--warn)}.tag.active{color:var(--acc)}
.empty{color:var(--mut);padding:.8rem;font-style:italic}
.feed{background:var(--panel);border:1px solid var(--bd);border-radius:.5rem}
.feed .row{display:flex;gap:.7rem;padding:.45rem .7rem;border-bottom:1px solid var(--bd);align-items:baseline}
.feed .row:last-child{border-bottom:none}
.feed .when{color:var(--mut);font-size:.75rem;min-width:8.5rem}
.feed .src{font-size:.72rem;min-width:5rem}
.logbar{display:flex;gap:.5rem;align-items:center;margin-bottom:.6rem;flex-wrap:wrap}
.logbar select,.logbar button,.logbar input{background:var(--panel2);color:var(--fg);border:1px solid var(--bd);border-radius:.35rem;padding:.35rem .5rem;font:inherit}
pre.logs{background:#0a0d12;border:1px solid var(--bd);border-radius:.5rem;padding:.7rem;max-height:70vh;overflow:auto;font-size:.78rem;white-space:pre-wrap;word-break:break-word}
.note{color:var(--mut);font-size:.8rem;margin:.4rem 0}
a{color:var(--acc)}
.alerts{margin:0 0 1rem}
.alert{display:flex;gap:.6rem;align-items:baseline;padding:.5rem .8rem;border-radius:.5rem;margin-bottom:.4rem;border:1px solid var(--bd)}
.alert.page{background:rgba(242,78,78,.12);border-color:rgba(242,78,78,.5)}
.alert.warn{background:rgba(240,180,41,.10);border-color:rgba(240,180,41,.45)}
.alert .sev{font-weight:700;text-transform:uppercase;font-size:.7rem;letter-spacing:.05em;min-width:3.2rem}
.alert.page .sev{color:var(--bad)}.alert.warn .sev{color:var(--warn)}
.alert .key{color:var(--mut);font-size:.72rem;min-width:11rem}
.pill.page{background:rgba(242,78,78,.22);color:var(--bad)}
header .badge{padding:.1rem .45rem;border-radius:1rem;font-size:.72rem;font-weight:700}
header .badge.page{background:var(--bad);color:#fff}header .badge.warn{background:var(--warn);color:#000}
header a.meta{text-decoration:none}
.hbar{display:flex;gap:.45rem;align-items:center;margin-bottom:.6rem;flex-wrap:wrap}
.hbar input,.hbar select,.hbar button{background:var(--panel2);color:var(--fg);border:1px solid var(--bd);border-radius:.35rem;padding:.35rem .5rem;font:inherit}
.hbar button{cursor:pointer}
.chip{padding:.2rem .6rem;border-radius:1rem;border:1px solid var(--bd);background:var(--panel2);color:var(--mut);cursor:pointer;font-size:.78rem}
.chip.active{color:var(--fg);border-color:var(--acc);background:rgba(92,200,255,.12)}
.chip .c{color:var(--acc);font-weight:600;margin-left:.35rem}
.fchip{padding:.12rem .5rem;border-radius:.3rem;background:var(--panel2);color:var(--mut);cursor:pointer;font-size:.72rem;border:1px solid var(--bd)}
.fchip:hover{color:var(--fg);border-color:var(--acc)}
td.cat{text-transform:uppercase;font-size:.68rem;letter-spacing:.03em;color:var(--acc)}
td.cons{color:var(--ok);font-size:.74rem}
td.cons.bad{color:var(--bad)}
</style></head>
<body>
<header>
  <h1>◆ DreggNet Cloud · Ops</h1>
  <span id="overall" class="pill down">…</span>
  <span id="alertbadge"></span>
  <span class="spacer"></span>
  <span id="whoami" class="meta" style="display:none"></span>
  <a id="grafanalink" class="meta" style="display:none" target="_blank" rel="noopener">Grafana ↗</a>
  <span class="meta" id="generated">loading…</span>
  <label class="meta"><input type="checkbox" id="auto" checked> auto</label>
</header>
<nav>
  <button data-tab="overview" class="active">Overview</button>
  <button data-tab="history">History</button>
  <button data-tab="activity">Activity</button>
  <button data-tab="status">Status</button>
  <button data-tab="durable">Durable / Economy</button>
  <button data-tab="bridge">Bridge</button>
  <button data-tab="logs">Logs</button>
</nav>
<main>
  <div class="alerts" id="alerts"></div>
  <section id="overview" class="active">
    <div class="tiles" id="tiles"></div>
    <h2>Services</h2>
    <div class="svc" id="svc"></div>
    <h2>Upstream sources</h2>
    <div id="sources"></div>
  </section>

  <section id="history">
    <h2>Historical log — what happened</h2>
    <p class="note">The browsable, filterable ledger across every service. Pick a viewer, then narrow by who / effect / text / time. Newest first.</p>
    <div class="hbar" id="hcats"></div>
    <div class="hbar">
      <input id="hwho" placeholder="who (agent / cell / lease / rail)" style="min-width:14rem">
      <input id="hwhat" placeholder="effect / action" style="min-width:10rem">
      <input id="htext" placeholder="free text" style="min-width:10rem">
      <select id="hsince" title="time window">
        <option value="">all time</option>
        <option value="1h">last 1h</option>
        <option value="6h" selected>last 6h</option>
        <option value="24h">last 24h</option>
        <option value="7d">last 7d</option>
        <option value="30d">last 30d</option>
      </select>
      <input id="hlimit" type="number" value="500" min="1" max="5000" style="width:5.5rem" title="row cap">
      <button id="hgo">apply</button>
      <button id="hclear" title="clear filters">clear</button>
      <span class="meta" id="hmeta"></span>
    </div>
    <div class="hbar" id="hfacets"></div>
    <div id="hrows"></div>
  </section>

  <section id="activity">
    <h2>Unified activity feed</h2>
    <p class="note">Newest first — receipts &amp; committed events (node), machines (gateway), durable charges (postgres), app activity (bot).</p>
    <div class="feed" id="feed"></div>
  </section>

  <section id="status">
    <h2>Federation &amp; consensus (node)</h2><div id="federation"></div>
    <h2>Machines (gateway)</h2><div id="machines"></div>
    <h2>Recent receipts / turns (node)</h2><div id="receipts"></div>
    <h2>Committed events (node)</h2><div id="events"></div>
    <h2>Bot cells &amp; app activity</h2><div id="bot"></div>
  </section>

  <section id="durable">
    <h2>Lease economy</h2><div class="tiles" id="econtiles"></div>
    <p class="note" id="econnote"></p>
    <h2>Spend by resource (hosting vs compute)</h2>
    <p class="note">The $DREGG meter splits across compute leases and the hosting bills (bandwidth · uptime · publish · cert · build). Every charge is a conserving <span class="mono">payer → beneficiary</span> move (Σδ=0).</p>
    <div id="byresource"></div>
    <h2>Durable jobs (from the dreggnet_meter outbox)</h2><div id="jobs"></div>
    <h2>Recent charges (the per-event ledger)</h2><div id="charges"></div>
  </section>

  <section id="bridge">
    <h2>Solana / coin-BRIDGE</h2>
    <div class="svc" id="bridgesvc"></div>
    <div class="tiles" id="bridgetiles"></div>
    <p class="note" id="bridgenote"></p>
    <h2>Conservation ledgers (live ≤ locked/backing)</h2>
    <p class="note">The key invariant: circulating mirror asset never exceeds what is locked on Solana / cleared by Stripe. A breach pages. Observed only when a relayer status endpoint (<span class="mono">OPS_BRIDGE_URL</span>) is configured.</p>
    <div id="bridgeledgers"></div>
    <h2>Recent lock→mint / redeem activity</h2>
    <p class="note">Node-derived from the committed-event feed: <span class="mono">mint</span>/<span class="mono">bridgemint</span> = a lock→mint, <span class="mono">burn</span> = a redeem. Mint amounts are not carried by the events feed today (burn summaries are).</p>
    <div class="feed" id="bridgefeed"></div>
  </section>

  <section id="logs">
    <div class="logbar">
      <select id="logsvc"></select>
      <input id="logtail" type="number" value="200" min="10" max="2000" style="width:5rem" title="lines">
      <button id="logfetch">tail</button>
      <span class="meta" id="logmeta"></span>
    </div>
    <pre class="logs" id="logout">pick a service and press tail.</pre>
  </section>
</main>
<script>
const $=s=>document.querySelector(s), $$=s=>[...document.querySelectorAll(s)];
let SNAP=null;

$$("nav button").forEach(b=>b.onclick=()=>{
  $$("nav button").forEach(x=>x.classList.remove("active"));
  $$("main section").forEach(x=>x.classList.remove("active"));
  b.classList.add("active"); $("#"+b.dataset.tab).classList.add("active");
  // Load the historical log the first time its tab is opened (it is heavier than
  // the live snapshot, so it is fetched on demand rather than on every refresh).
  if(b.dataset.tab==="history"&&!HLOADED)applyHistory();
});

function esc(s){return String(s==null?"":s).replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"}[c]));}
function short(s,n){s=String(s==null?"":s);return s.length>n?s.slice(0,n)+"…":s;}
function ts(t){if(t==null)return"";if(typeof t==="number"){let d=new Date(t<2e10?t*1000:t);return d.toISOString().replace("T"," ").replace(/\.\d+Z/,"Z");}return String(t).replace("T"," ").replace(/\.\d+Z/,"Z");}
function tile(k,v,cls){return `<div class="tile"><div class="k">${esc(k)}</div><div class="v ${cls||""}">${v}</div></div>`;}
// cols: [header, rowFn, optionalTdClass]
function tbl(cols,rows){if(!rows||!rows.length)return `<div class="empty">none</div>`;
  return `<table><thead><tr>${cols.map(c=>`<th>${esc(c[0])}</th>`).join("")}</tr></thead><tbody>`+
    rows.map(r=>`<tr>${cols.map(c=>`<td class="${c[2]||""}">${c[1](r)}</td>`).join("")}</tr>`).join("")+`</tbody></table>`;}

function render(s){
  SNAP=s;
  const h=s.health||{};
  const op=$("#overall"); op.className="pill "+(h.overall||"down"); op.textContent=(h.overall||"?").toUpperCase();
  $("#generated").textContent="updated "+ts(s.generated_at);

  // Alerts — banner (all tabs) + a header badge with the page/warn counts.
  const al=Array.isArray(h.alerts)?h.alerts:[];
  const pages=al.filter(a=>a.severity==="page"), warns=al.filter(a=>a.severity==="warn");
  $("#alerts").innerHTML = al.length
    ? al.map(a=>`<div class="alert ${esc(a.severity)}"><span class="sev">${esc(a.severity)}</span><span class="key">${esc(a.key)}</span><span>${esc(a.message)}</span></div>`).join("")
    : "";
  const badge=$("#alertbadge");
  if(pages.length){badge.className="badge page";badge.textContent="⚠ "+pages.length+" PAGE";}
  else if(warns.length){badge.className="badge warn";badge.textContent=warns.length+" warn";}
  else{badge.className="";badge.textContent="";}

  // Overview tiles
  const div=h.consensus_divergence;
  $("#tiles").innerHTML=[
    tile("Overall",(h.overall||"?").toUpperCase(),h.overall==="healthy"?"ok":h.overall==="down"?"bad":"warn"),
    tile("Federation members",h.federation_members??"—"),
    tile("Consensus",h.consensus_live==null?"—":(h.consensus_live?"live":"stalled"),h.consensus_live?"ok":h.consensus_live===false?"bad":""),
    tile("Finalizing",h.node_finalizing==null?"—":(h.node_finalizing?"yes":"no"),h.node_finalizing?"ok":h.node_finalizing===false?"bad":""),
    tile("Rust↔Lean divergence",div==null?"—":div,div>0?"bad":"ok"),
    tile("Gossip rejections",h.gossip_stream_rejected==null?"—":h.gossip_stream_rejected,h.gossip_stream_rejected>0?"bad":"ok"),
    tile("Finality latency",h.finality_latency_avg==null?"—":(Number(h.finality_latency_avg).toFixed(2)+"s"),h.finality_latency_avg>10?"warn":"ok"),
    tile("Reorg-by-catchup (τ shifts)",h.tau_prefix_shifts??"—"),
    tile("Block height",h.block_height??"—"),
    tile("Peers",h.peers??"—"),
    tile("Gossip messages",h.gossip_messages??"—"),
    tile("Machines",h.machines??"—"),
    tile("Durable jobs in flight",h.durable_jobs_in_flight??0,h.durable_jobs_in_flight>0?"ok":""),
    tile("Units spent (lease economy)",h.total_units_spent??0),
    tile("PG connections",(h.pg_active_connections!=null&&h.pg_max_connections!=null)?(h.pg_active_connections+"/"+h.pg_max_connections):"—"),
    tile("Bridge conservation",h.bridge_conservation_ok==null?"—":(h.bridge_conservation_ok?"OK":"BREACH"),h.bridge_conservation_ok==null?"":(h.bridge_conservation_ok?"ok":"bad")),
    tile("Bridge mints",h.bridge_mints_observed??0),
  ].join("");

  // Services
  const sd=(label,st)=>{const up=st==="up";const cls=up?"up":(st==="down"?"down":"other");
    return `<div class="s"><span><span class="dot ${cls}"></span>${esc(label)}</span><span class="tag ${up?'ok':st==='down'?'bad':''}">${esc(st)}</span></div>`;};
  $("#svc").innerHTML=[sd("dregg node",h.node),sd("gateway",h.gateway),sd("discord bot",h.bot),sd("postgres / durable",h.postgres),sd("compute backend",h.backend),
    sd("bridge relayer",h.bridge_relayer),sd("solana cluster",h.bridge_solana),sd("stripe receiver",h.bridge_stripe)].join("");

  // Sources
  $("#sources").innerHTML=tbl(
    [["source",r=>esc(r.name)],["target",r=>`<span class="mono">${esc(short(r.target,60))}</span>`],
     ["reachable",r=>`<span class="tag ${r.reachable?'ok':'bad'}">${r.reachable?'yes':'no'}</span>`],
     ["http",r=>r.http_status??"—"],["ms",r=>r.latency_ms??""],["error",r=>`<span class="mono">${esc(short(r.error||"",70))}</span>`]],
    s.sources||[]);

  // Federation
  const feds=s.node&&s.node.federations||[];
  $("#federation").innerHTML=tbl(
    [["federation",r=>esc(short(r.federation_id||r.id,20))],["members",r=>r.member_count],["threshold",r=>r.threshold],
     ["epoch",r=>r.committee_epoch],["height",r=>r.latest_height],["finalized roots",r=>r.num_finalized_roots]],
    Array.isArray(feds)?feds:[]);

  // Machines
  const ms=(s.gateway&&s.gateway.machines)||[];
  $("#machines").innerHTML=tbl(
    [["app",r=>esc(r.app||"")],["id",r=>`<span class="mono">${esc(short(r.id,14))}</span>`],["name",r=>esc(r.name)],
     ["state",r=>`<span class="tag ${r.state==='started'?'ok':r.state==='failed'?'bad':''}">${esc(r.state)}</span>`],
     ["region",r=>esc(r.region)],["meter",r=>r.dregg&&r.dregg.meter_units!=null?r.dregg.meter_units:"—"]],
    ms);

  // Receipts
  const rc=(s.node&&s.node.recent_receipts)||[];
  $("#receipts").innerHTML=tbl(
    [["#",r=>r.chain_index],["turn",r=>`<span class="mono">${esc(short(r.turn_hash,14))}</span>`],["agent",r=>`<span class="mono">${esc(short(r.agent,12))}</span>`],
     ["when",r=>ts(r.timestamp)],["computrons",r=>r.computrons_used],["actions",r=>r.action_count],
     ["finality",r=>`<span class="tag">${esc(r.finality)}</span>`],["proof",r=>r.has_proof?"✓":"—"]],
    Array.isArray(rc)?rc:[]);

  // Events
  const ev=(s.node&&s.node.recent_events)||[];
  $("#events").innerHTML=tbl(
    [["height",r=>r.height],["turn",r=>`<span class="mono">${esc(short(r.turn_hash,14))}</span>`],["cell",r=>`<span class="mono">${esc(short(r.cell_id,12))}</span>`],
     ["status",r=>`<span class="tag">${esc(JSON.stringify(r.status).replace(/"/g,''))}</span>`],["effects",r=>esc(short((r.effects||[]).join(","),40))]],
    Array.isArray(ev)?ev:[]);

  // Bot
  const bot=s.bot||{};
  let bothtml="";
  if(!bot.configured){bothtml=`<div class="empty">bot not deployed (OPS_BOT_URL unset)</div>`;}
  else{
    const acts=Array.isArray(bot.activity)?bot.activity:[];
    bothtml=tbl([["when",r=>ts(r.timestamp)],["app",r=>esc(r.app)],["action",r=>esc(r.action)],
      ["actor",r=>`<span class="mono">${esc(short(r.actor_discord_id,16))}</span>`],["subject",r=>esc(short(r.subject||"",24))],
      ["status",r=>`<span class="tag">${esc(r.status)}</span>`]],acts);
  }
  $("#bot").innerHTML=bothtml;

  // Durable / economy
  const d=s.durable||{};
  $("#econtiles").innerHTML=[
    tile("Total leases metered",d.total_leases??0),
    tile("Units spent",d.total_units_spent??0),
    tile("Jobs in flight",d.jobs_in_flight??0,d.jobs_in_flight>0?"ok":""),
    tile("Postgres",d.configured?(d.reachable?"reachable":"unreachable"):"not configured",d.reachable?"ok":d.configured?"bad":""),
  ].join("");
  $("#econnote").innerHTML = (d.error?("⚠ "+esc(d.error)+" · "):"")+
    "Spent is read live from the <span class='mono'>dreggnet_meter</span> transactional outbox. "+
    "Minted/conserved live in the dregg lease-cell ledger on the node (per-cell, not a single endpoint).";
  $("#byresource").innerHTML=tbl(
    [["resource",r=>`<span class="tag ${r.resource==='compute'?'active':''}">${esc(r.resource)}</span>`],
     ["charges",r=>r.charges],["units billed",r=>r.units]],
    d.resource_totals||[]);
  $("#jobs").innerHTML=tbl(
    [["lease / instance",r=>`<span class="mono">${esc(short(r.lease_id,32))}</span>`],["steps",r=>r.periods],["units charged",r=>r.units_charged],
     ["last charge",r=>ts(r.last_charge_at)],["status",r=>`<span class="tag ${r.status==='active'?'active':''}">${esc(r.status)}</span>`]],
    d.jobs||[]);
  $("#charges").innerHTML=tbl(
    [["when",r=>ts(r.charged_at)],["lease / instance",r=>`<span class="mono">${esc(short(r.lease_id,28))}</span>`],
     ["resource",r=>`<span class="tag ${r.resource==='compute'?'active':''}">${esc(r.resource)}</span>`],
     ["step",r=>r.period],["amount",r=>r.amount],["running",r=>r.running_total]],
    (d.charges||[]).slice(0,200));

  // Bridge (Solana / coin-BRIDGE)
  const br=s.bridge||{};
  const bsd=(label,st)=>{const up=st==="up";const cls=up?"up":(st==="down"?"down":"other");
    return `<div class="s"><span><span class="dot ${cls}"></span>${esc(label)}</span><span class="tag ${up?'ok':st==='down'?'bad':''}">${esc(st)}</span></div>`;};
  $("#bridgesvc").innerHTML=[bsd("relayer status",h.bridge_relayer),bsd("solana cluster (devnet)",h.bridge_solana),bsd("stripe receiver",h.bridge_stripe)].join("");
  const consTxt=h.bridge_conservation_ok==null?"un-observed":(h.bridge_conservation_ok?"OK":"BREACH");
  const consCls=h.bridge_conservation_ok==null?"":(h.bridge_conservation_ok?"ok":"bad");
  $("#bridgetiles").innerHTML=[
    tile("Conservation",consTxt,consCls),
    tile("Mints observed",br.mints_observed??0),
    tile("Redeems (burns) observed",br.burns_observed??0),
    tile("Last mint",br.last_mint_at!=null?ts(br.last_mint_at):"—"),
    tile("Double-mints rejected",br.double_mint_rejected??0,(br.double_mint_rejected>0)?"warn":""),
    tile("Breach detected",br.breach_detected?"YES":"no",br.breach_detected?"bad":"ok"),
  ].join("");
  $("#bridgenote").innerHTML=(Array.isArray(br.notes)?br.notes:[]).map(n=>"• "+esc(n)).join("<br>");
  $("#bridgeledgers").innerHTML=tbl(
    [["rail",r=>`<span class="tag">${esc(r.rail)}</span>`],["asset",r=>`<span class="mono">${esc(r.asset)}</span>`],
     ["live supply",r=>r.live_supply],["backing",r=>`${r.locked_or_backing} <span class="mono">(${esc(r.backing_label)})</span>`],
     ["conserved",r=>`<span class="tag ${r.conserved?'ok':'bad'}">${r.conserved?'yes':'NO'}</span>`],["locks consumed",r=>r.locks_consumed]],
    Array.isArray(br.ledgers)?br.ledgers:[]);
  const bacts=Array.isArray(br.recent)?br.recent:[];
  $("#bridgefeed").innerHTML=bacts.length?bacts.slice(0,100).map(a=>
    `<div class="row"><span class="when">${esc(ts(a.when))}</span><span class="src tag ${a.kind==='burn'?'warn':'active'}">${esc(a.kind)}</span><span>${esc(a.rail)}${a.amount!=null?(" · "+a.amount):""}${a.cell?(" · cell "+esc(a.cell)):""} · ${esc(a.status)}</span></div>`).join("")
    :`<div class="empty">no bridge activity in the node event window</div>`;

  // Unified feed
  const feed=[];
  (Array.isArray(rc)?rc:[]).forEach(r=>feed.push({t:r.timestamp,src:"receipt",txt:`turn ${short(r.turn_hash,12)} · ${r.action_count} action(s) · ${r.finality}`}));
  (Array.isArray(ev)?ev:[]).forEach(r=>feed.push({t:r.timestamp,src:"event",txt:`h${r.height} cell ${short(r.cell_id,10)} · ${(r.effects||[]).join(",")}`}));
  ms.forEach(r=>feed.push({t:r.updated_at||r.created_at,src:"machine",txt:`${r.app}/${r.name} → ${r.state}`}));
  (d.jobs||[]).forEach(r=>feed.push({t:r.last_charge_at,src:"durable",txt:`lease ${short(r.lease_id,16)} · ${r.units_charged}u · ${r.periods} step(s)`}));
  if(bot.configured&&Array.isArray(bot.activity))bot.activity.forEach(r=>feed.push({t:r.timestamp,src:"bot",txt:`${r.app}.${r.action} by ${short(r.actor_discord_id,12)}`}));
  feed.sort((a,b)=>{const x=Date.parse(ts(b.t))||0,y=Date.parse(ts(a.t))||0;return x-y;});
  $("#feed").innerHTML=feed.length?feed.slice(0,200).map(f=>
    `<div class="row"><span class="when">${esc(ts(f.t))}</span><span class="src tag">${esc(f.src)}</span><span>${esc(f.txt)}</span></div>`).join("")
    :`<div class="empty">no activity yet</div>`;
}

async function refresh(){
  try{const r=await fetch("api/snapshot",{headers:{"accept":"application/json"}});
    if(!r.ok){$("#generated").textContent="snapshot HTTP "+r.status;return;}
    render(await r.json());
  }catch(e){$("#generated").textContent="snapshot error: "+e;}
}

// ── Historical-log viewer ─────────────────────────────────────────────────
// The category facet maps a viewer to a friendly label and a Grafana board uid
// (for the "deep metrics" cross-link when OPS_GRAFANA_URL is configured).
const CATMETA={turn:["Turns / receipts","dreggnet-protocol"],event:["Committed effects","dreggnet-protocol"],
  machine:["Leases & machines","dreggnet-compute"],compute:["Compute runs","dreggnet-compute"],
  economy:["$DREGG economy","dreggnet-economy"],bridge:["Bridge activity","dreggnet-bridge"]};
let GRAFANA="";
let HCAT="";   // the selected category ("" = all viewers)
let HLOADED=false;

function hquery(){
  const p=new URLSearchParams();
  if(HCAT)p.set("category",HCAT);
  const who=$("#hwho").value.trim(); if(who)p.set("who",who);
  const what=$("#hwhat").value.trim(); if(what)p.set("what",what);
  const text=$("#htext").value.trim(); if(text)p.set("q",text);
  const since=$("#hsince").value; if(since)p.set("since",since);
  const lim=$("#hlimit").value; if(lim)p.set("limit",lim);
  return p.toString();
}
async function applyHistory(){
  HLOADED=true;
  $("#hmeta").textContent="loading…";
  try{
    const r=await fetch("api/history?"+hquery());
    if(!r.ok){$("#hmeta").textContent="HTTP "+r.status;return;}
    renderHistory(await r.json());
  }catch(e){$("#hmeta").textContent="error: "+e;}
}
function gdeep(uid){return GRAFANA?` <a href="${GRAFANA}/d/${uid}" target="_blank" rel="noopener" class="mono">metrics ↗</a>`:"";}
function renderHistory(v){
  v=v||{}; const facets=v.facets||{}; const cats=facets.categories||[];
  // Category quick-filter buttons (zero-filled, every viewer always shown).
  $("#hcats").innerHTML=
    `<span class="chip ${HCAT===''?'active':''}" data-cat="">All<span class="c">${facets.total??0}</span></span>`+
    cats.map(c=>{const meta=CATMETA[c.key]||[c.key,""];
      return `<span class="chip ${HCAT===c.key?'active':''}" data-cat="${esc(c.key)}">${esc(meta[0])}<span class="c">${c.count}</span></span>`;}).join("");
  $$("#hcats .chip").forEach(ch=>ch.onclick=()=>{HCAT=ch.dataset.cat;applyHistory();});
  // The "showing N of M" line + a deep link to the matching Grafana board.
  const uid=HCAT&&CATMETA[HCAT]?CATMETA[HCAT][1]:"dreggnet-cloud-health";
  $("#hmeta").innerHTML=`showing ${(v.events||[]).length} of ${v.matched??0} matched · ${v.total??0} total${gdeep(uid)}`;
  // Top actors + effects as click-to-filter chips.
  const af=(facets.actors||[]).slice(0,12).map(f=>`<span class="fchip" data-who="${esc(f.key)}">${esc(short(f.key,22))} ·${f.count}</span>`).join("");
  const ef=(facets.effects||[]).slice(0,12).map(f=>`<span class="fchip" data-what="${esc(f.key)}">${esc(short(f.key,22))} ·${f.count}</span>`).join("");
  $("#hfacets").innerHTML=(af||ef)?(`<span class="meta">actors:</span> ${af} &nbsp; <span class="meta">effects:</span> ${ef}`):"";
  $$("#hfacets .fchip[data-who]").forEach(c=>c.onclick=()=>{$("#hwho").value=c.dataset.who;applyHistory();});
  $$("#hfacets .fchip[data-what]").forEach(c=>c.onclick=()=>{$("#hwhat").value=c.dataset.what;applyHistory();});
  // The rows.
  $("#hrows").innerHTML=tbl(
    [["when",r=>ts(r.when)],["viewer",r=>`<span class="cat">${esc(r.category)}</span>`,"cat"],
     ["who",r=>`<span class="mono">${esc(short(r.who,28))}</span>`],["what",r=>esc(short(r.what,40))],
     ["result",r=>`<span class="tag ${r.result==='finalized'||r.result==='committed'||r.result==='active'?'ok':(r.result==='failed'||r.result==='lapsed'?'bad':'')}">${esc(r.result)}</span>`],
     ["detail",r=>esc(short(r.detail,60))],
     ["conservation",r=>r.conservation?`<span class="cons ${/BREACH/.test(r.conservation)?'bad':''}">${esc(r.conservation)}</span>`:""]],
    v.events||[]);
}
// tbl() supports an optional 3rd element on a column = a <td> class.

$("#hgo").onclick=applyHistory;
$("#hclear").onclick=()=>{HCAT="";$("#hwho").value="";$("#hwhat").value="";$("#htext").value="";$("#hsince").value="6h";$("#hlimit").value="500";applyHistory();};
["hwho","hwhat","htext"].forEach(id=>$("#"+id).addEventListener("keydown",e=>{if(e.key==="Enter")applyHistory();}));
$("#hsince").onchange=applyHistory;

let LOGINBASE="/.dregg-auth";
async function loadConfig(){
  try{const r=await fetch("api/config");if(!r.ok)return;const c=await r.json();
    GRAFANA=(c.grafana_url||"").replace(/\/+$/,"");
    if(c.login_base)LOGINBASE=c.login_base.replace(/\/+$/,"");
    if(GRAFANA){const a=$("#grafanalink");a.href=GRAFANA+"/d/dreggnet-federation";a.style.display="";a.title="open the Federation (n=5) live board — gossip · finality · differential · conservation";}
  }catch(e){}
  // The authenticated dregg identity (from the webauth forward-auth). Shows who is
  // signed in + the cap that admitted them, with a sign-out link.
  try{const r=await fetch("api/whoami");if(!r.ok)return;const w=await r.json();
    if(w&&w.subject){const el=$("#whoami");
      const cap=w.cap?(" · <span class='mono'>"+esc(w.cap)+"</span>"):"";
      el.innerHTML="◇ "+esc(short(w.subject,28))+cap+" · <a href='"+LOGINBASE+"/logout'>sign out</a>";
      el.style.display="";el.title="signed in via dregg capability ("+esc(w.how||"")+")";}
  }catch(e){}
}

// Logs
async function loadContainers(){
  try{const r=await fetch("api/containers");if(!r.ok)return;
    const cs=await r.json();const sel=$("#logsvc");sel.innerHTML="";
    (cs||[]).forEach(c=>{const o=document.createElement("option");o.value=c.id;o.textContent=(c.service||c.name)+" — "+c.state;sel.appendChild(o);});
  }catch(e){}
}
$("#logfetch").onclick=async()=>{
  const id=$("#logsvc").value,tail=$("#logtail").value;
  $("#logout").textContent="loading…";
  try{const r=await fetch(`api/logs?container=${encodeURIComponent(id)}&tail=${encodeURIComponent(tail)}`);
    const t=await r.text();$("#logout").textContent=t||"(empty)";$("#logmeta").textContent=r.ok?"":("HTTP "+r.status);
    $("#logout").scrollTop=$("#logout").scrollHeight;
  }catch(e){$("#logout").textContent="error: "+e;}
};

refresh();loadContainers();loadConfig();
setInterval(()=>{if($("#auto").checked)refresh();},5000);
</script>
</body></html>
"##;

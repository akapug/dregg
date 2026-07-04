//! Server-render a [`ConsoleView`] into one self-contained HTML page — the
//! signed-in "my stuff" home. Same shape as the `dreggnet-ops` dashboard (a
//! single page, no build step), but the data is baked in server-side so the
//! page shows the user's *real, cap-scoped* resources on first paint.
//!
//! Panels: $DREGG (balance + spend) · My sites · My servers · My agents (the
//! budget bound + the QA proof + a re-verify button) · My domains · My storage ·
//! Verify-anything (paste a run report → re-witness in-page). The little bit of
//! JS only drives the verify buttons; everything else is rendered HTML.

use crate::model::ConsoleView;

/// Render the full console page for `view`. `login_base` is the public path the
/// webauth login/logout flow is reachable at (for the sign-out control).
pub fn render_page(view: &ConsoleView, login_base: &str) -> String {
    let subject = esc(&view.subject);
    let dregg = &view.dregg;
    let mut body = String::new();

    // Header.
    body.push_str(&format!(
        r#"<header>
  <h1>DreggNet console</h1>
  <div class="who">signed in as <code>{subject}</code> · <a href="{lb}/logout">sign out</a></div>
  <div class="gen">cap-scoped to your cells · generated {gen}</div>
</header>"#,
        lb = esc(login_base),
        gen = esc(&view.generated_at),
    ));

    // $DREGG.
    body.push_str(&format!(
        r#"<section id="dregg"><h2>My $DREGG</h2>
  <div class="tiles">
    <div class="tile"><span class="n">{bal}</span><span class="l">balance</span></div>
    <div class="tile"><span class="n">{spent}</span><span class="l">total spent</span></div>
    <div class="tile"><span class="n">{lines}</span><span class="l">spend lines</span></div>
  </div>"#,
        bal = dregg.balance,
        spent = dregg.total_spent,
        lines = dregg.entries.len(),
    ));
    if dregg.entries.is_empty() {
        body.push_str("<p class=\"empty\">no charges yet.</p>");
    } else {
        body.push_str("<table><tr><th>resource</th><th>id</th><th>period</th><th>units</th></tr>");
        for e in &dregg.entries {
            body.push_str(&format!(
                "<tr><td>{}</td><td><code>{}</code></td><td>{}</td><td>{}</td></tr>",
                esc(&e.resource_kind),
                esc(&e.resource_id),
                esc(&e.period),
                e.units
            ));
        }
        body.push_str("</table>");
    }
    body.push_str("</section>");

    // My sites.
    body.push_str("<section id=\"sites\"><h2>My sites</h2>");
    if view.sites.is_empty() {
        body.push_str("<p class=\"empty\">no published sites yet.</p>");
    } else {
        body.push_str("<table><tr><th>name</th><th>status</th><th>domain</th><th>content root</th><th>size</th><th></th></tr>");
        for s in &view.sites {
            body.push_str(&format!(
                "<tr><td><b>{}</b></td><td><span class=\"pill {}\">{}</span></td><td>{}</td>\
                 <td><code class=\"root\">{}</code></td><td>{} B</td>\
                 <td><button class=\"verify-site\" data-root=\"{}\">verify</button></td></tr>",
                esc(&s.name),
                if s.status == "published" {
                    "ok"
                } else {
                    "warn"
                },
                esc(&s.status),
                s.domain.as_deref().map(esc).unwrap_or_else(|| "—".into()),
                esc(&s.content_root),
                s.bytes,
                esc(&s.content_root),
            ));
        }
        body.push_str("</table>");
    }
    body.push_str("</section>");

    // My servers.
    body.push_str("<section id=\"servers\"><h2>My servers</h2>");
    if view.servers.is_empty() {
        body.push_str("<p class=\"empty\">no persistent servers yet.</p>");
    } else {
        body.push_str("<table><tr><th>name</th><th>id</th><th>state</th><th>region</th><th>size</th><th>uptime spent</th><th>headroom</th></tr>");
        for s in &view.servers {
            body.push_str(&format!(
                "<tr><td><b>{}</b></td><td><code>{}</code></td><td><span class=\"pill {}\">{}</span></td>\
                 <td>{}</td><td>{}</td><td>{} / {}</td><td>{}</td></tr>",
                esc(&s.name),
                esc(&s.id),
                if s.state == "running" { "ok" } else if s.state == "reaped" { "warn" } else { "" },
                esc(&s.state),
                esc(&s.region),
                esc(&s.size),
                s.settled_units(),
                s.budget_units,
                s.headroom_units(),
            ));
        }
        body.push_str("</table>");
    }
    body.push_str("</section>");

    // My agents — the centerpiece: budget bound + QA proof + re-verify.
    body.push_str("<section id=\"agents\"><h2>My agents</h2>");
    if view.agents.is_empty() {
        body.push_str("<p class=\"empty\">no deployed agents yet.</p>");
    } else {
        for a in &view.agents {
            let qa = a.qa_passed();
            body.push_str(&format!(
                r#"<div class="agent">
  <div class="agent-head"><b>{id}</b>
    <span class="pill {qcls}">QA {qword}</span>
    <button class="verify-agent" data-agent="{id}">re-verify</button>
  </div>
  <div class="bound">budget <b>{budget}</b> · consumed <b>{consumed}</b> · headroom <b>{headroom}</b>
    (the bound: it could have done at most {headroom} more) · {receipts} receipts</div>"#,
                id = esc(&a.id),
                qcls = if qa { "ok" } else { "warn" },
                qword = if qa { "✓ passed" } else { "see results" },
                budget = a.budget(),
                consumed = a.consumed(),
                headroom = a.headroom(),
                receipts = a.receipts(),
            ));
            // The QA verdicts (the proof the declared tests ran on the deployed code).
            let results = a.qa_results();
            if results.is_empty() {
                body.push_str("<div class=\"qa\">no execution-QA in this run.</div>");
            } else {
                body.push_str(
                    "<table class=\"qa\"><tr><th>tool</th><th>verdict</th><th>summary</th></tr>",
                );
                for (action, ok, summary) in &results {
                    body.push_str(&format!(
                        "<tr><td><code>{}</code></td><td><span class=\"pill {}\">{}</span></td><td>{}</td></tr>",
                        esc(action),
                        if *ok { "ok" } else { "warn" },
                        if *ok { "✓" } else { "✗" },
                        esc(summary),
                    ));
                }
                body.push_str("</table>");
            }
            body.push_str(&format!(
                "<div class=\"caps\">caps: {}</div>",
                a.caps
                    .iter()
                    .map(|c| format!("<code>{}</code>", esc(c)))
                    .collect::<Vec<_>>()
                    .join(" ")
            ));
            body.push_str("<div class=\"verdict\" data-for=\"");
            body.push_str(&esc(&a.id));
            body.push_str("\"></div></div>");
        }
    }
    body.push_str("</section>");

    // My domains.
    body.push_str("<section id=\"domains\"><h2>My domains</h2>");
    if view.domains.is_empty() {
        body.push_str("<p class=\"empty\">no custom domains bound yet.</p>");
    } else {
        body.push_str("<table><tr><th>domain</th><th>site</th><th>state</th></tr>");
        for d in &view.domains {
            body.push_str(&format!(
                "<tr><td><b>{}</b></td><td>{}</td><td><span class=\"pill {}\">{}</span></td></tr>",
                esc(&d.domain),
                esc(&d.site),
                if d.state == "verified" { "ok" } else { "warn" },
                esc(&d.state),
            ));
        }
        body.push_str("</table>");
    }
    body.push_str("</section>");

    // My storage.
    body.push_str("<section id=\"storage\"><h2>My storage</h2>");
    if view.buckets.is_empty() {
        body.push_str("<p class=\"empty\">no storage buckets yet.</p>");
    } else {
        body.push_str(
            "<table><tr><th>bucket</th><th>objects</th><th>bytes</th><th>content root</th></tr>",
        );
        for b in &view.buckets {
            body.push_str(&format!(
                "<tr><td><b>{}</b></td><td>{}</td><td>{}</td><td><code class=\"root\">{}</code></td></tr>",
                esc(&b.name),
                b.objects,
                b.bytes,
                esc(&b.content_root),
            ));
        }
        body.push_str("</table>");
    }
    body.push_str("</section>");

    // Verify-anything.
    body.push_str(
        r#"<section id="verify"><h2>Verify anything</h2>
  <p class="hint">Paste an agent-run report (JSON) and the deployed content root to
  re-witness it in your browser — chain ✓ · budget bound ✓ · QA ran on the deployed
  code ✓. Verify-don't-trust: the console proves it, you don't take its word.</p>
  <p><input id="vroot" placeholder="deployed content root (e.g. the site's content_root)"></p>
  <p><textarea id="vreport" placeholder='{"agent":"…","budget":…,"receipts":[…],…}'></textarea></p>
  <p><button id="verify-paste">Re-witness</button></p>
  <div class="verdict" id="paste-verdict"></div>
</section>"#,
    );

    let script = VERIFY_JS;
    format!(
        "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">\
         <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\
         <title>DreggNet console — {subject}</title><style>{CSS}</style></head>\
         <body><main>{body}</main><script>{script}</script></body></html>",
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
:root { color-scheme: light dark; }
body { font-family: system-ui, sans-serif; color: #1a1a2e; margin: 0; background: #fafaff; }
main { max-width: 60rem; margin: 0 auto; padding: 1rem; }
header { padding: 1rem 0; border-bottom: 2px solid #e0e0ef; margin-bottom: 1rem; }
header h1 { margin: 0; font-size: 1.5rem; }
.who { color: #444; margin-top: .25rem; }
.gen { color: #888; font-size: .8rem; margin-top: .2rem; }
section { background: #fff; border: 1px solid #e6e6f0; border-radius: .5rem; padding: .8rem 1rem; margin: 1rem 0; }
h2 { font-size: 1.1rem; margin: .2rem 0 .6rem; }
table { width: 100%; border-collapse: collapse; font-size: .9rem; }
th, td { text-align: left; padding: .35rem .5rem; border-bottom: 1px solid #f0f0f5; }
th { color: #666; font-weight: 600; }
code { background: #f0f0f5; padding: 0 .25rem; border-radius: .2rem; font-size: .85em; }
code.root { font-size: .72em; color: #555; }
.tiles { display: flex; gap: 1rem; margin-bottom: .6rem; flex-wrap: wrap; }
.tile { background: #f4f4fb; border-radius: .4rem; padding: .5rem .9rem; min-width: 6rem; }
.tile .n { display: block; font-size: 1.4rem; font-weight: 700; }
.tile .l { color: #777; font-size: .8rem; }
.pill { padding: 0 .4rem; border-radius: .8rem; font-size: .78rem; background: #eee; }
.pill.ok { background: #d6f5d6; color: #176117; }
.pill.warn { background: #fde9c8; color: #8a5500; }
.empty { color: #999; font-style: italic; }
.agent { border: 1px solid #ececf5; border-radius: .4rem; padding: .6rem .8rem; margin: .6rem 0; }
.agent-head { display: flex; align-items: center; gap: .6rem; }
.bound { color: #333; margin: .4rem 0; font-size: .9rem; }
.caps { color: #666; font-size: .8rem; margin-top: .4rem; }
.qa { margin: .3rem 0; }
button { padding: .35rem .8rem; cursor: pointer; border: 1px solid #b9b9d6; background: #fff; border-radius: .3rem; }
button:hover { background: #f0f0ff; }
textarea { width: 100%; height: 8rem; font-family: ui-monospace, monospace; font-size: .8rem; }
input { width: 100%; padding: .4rem; font-family: ui-monospace, monospace; }
.hint { color: #555; font-size: .9rem; }
.verdict { margin-top: .4rem; font-size: .9rem; }
.verdict.ok { color: #176117; }
.verdict.bad { color: #a11; }
"#;

const VERIFY_JS: &str = r#"
function showVerdict(el, r) {
  el.className = 'verdict ' + (r.ok ? 'ok' : 'bad');
  el.textContent = (r.ok ? '✓ ' : '✗ ') + r.detail;
}
async function verifyAgent(id, target) {
  target.textContent = 're-witnessing…';
  try {
    const resp = await fetch('api/verify', { method: 'POST',
      headers: {'content-type':'application/json'}, body: JSON.stringify({ agent_id: id }) });
    showVerdict(target, await resp.json());
  } catch (e) { target.className='verdict bad'; target.textContent = 'verify failed: ' + e; }
}
document.querySelectorAll('.verify-agent').forEach(btn => {
  btn.onclick = () => {
    const id = btn.dataset.agent;
    const target = document.querySelector('.verdict[data-for="' + CSS.escape(id) + '"]');
    verifyAgent(id, target);
  };
});
document.querySelectorAll('.verify-site').forEach(btn => {
  btn.onclick = async () => {
    btn.textContent = '…';
    try {
      const resp = await fetch('api/verify', { method:'POST',
        headers:{'content-type':'application/json'}, body: JSON.stringify({ site_root: btn.dataset.root }) });
      const r = await resp.json();
      btn.textContent = r.ok ? 'verified ✓' : 'failed ✗';
    } catch (e) { btn.textContent = 'error'; }
  };
});
const vp = document.getElementById('verify-paste');
if (vp) vp.onclick = async () => {
  const out = document.getElementById('paste-verdict');
  out.textContent = 're-witnessing…';
  let report;
  try { report = JSON.parse(document.getElementById('vreport').value); }
  catch (e) { out.className='verdict bad'; out.textContent='not valid JSON'; return; }
  try {
    const resp = await fetch('api/verify', { method:'POST', headers:{'content-type':'application/json'},
      body: JSON.stringify({ report, deployed_root: document.getElementById('vroot').value }) });
    showVerdict(out, await resp.json());
  } catch (e) { out.className='verdict bad'; out.textContent='verify failed: ' + e; }
};
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fixtures, scope::Catalog};

    fn demo_view() -> ConsoleView {
        ConsoleView::for_subject(
            &fixtures::demo_catalog(),
            fixtures::DEMO_SUBJECT,
            "t".into(),
        )
    }

    #[test]
    fn the_page_renders_the_users_real_resources() {
        let html = render_page(&demo_view(), "/.dregg-auth");
        // Every panel heading is present.
        for h in [
            "My $DREGG",
            "My sites",
            "My servers",
            "My agents",
            "My domains",
            "My storage",
            "Verify anything",
        ] {
            assert!(html.contains(h), "missing panel: {h}");
        }
        // The user's real data appears.
        assert!(html.contains("demo-site"));
        assert!(html.contains("api-server"));
        assert!(html.contains("agent:deploy-bot"));
        assert!(html.contains("demo.example"));
        assert!(html.contains(fixtures::DEMO_SUBJECT));
        // The agent panel shows the budget bound + the QA proof.
        assert!(html.contains("budget"));
        assert!(html.contains("headroom"));
        assert!(html.contains("verify_deploy"));
    }

    #[test]
    fn the_page_never_leaks_another_users_resources() {
        let html = render_page(&demo_view(), "/.dregg-auth");
        // The second user's private resources must NOT appear in the demo user's page.
        assert!(!html.contains("other-private"));
        assert!(!html.contains("srv_other99"));
        assert!(!html.contains("other-bucket"));
        assert!(!html.contains(fixtures::OTHER_SUBJECT));
    }

    #[test]
    fn an_empty_account_renders_friendly_empties() {
        let view =
            ConsoleView::for_subject(&Catalog::default(), "dregg:newbie0000000000", "t".into());
        let html = render_page(&view, "");
        assert!(html.contains("no published sites yet"));
        assert!(html.contains("no deployed agents yet"));
    }
}

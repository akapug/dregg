//! Server-render the public landing page into one self-contained HTML document.
//!
//! No external assets, no build step. The page tells a first-time visitor what
//! DreggNet Cloud IS, shows the LIVE status banner (filled client-side from the
//! status page's `/status.json` — honest "checking…" until it lands), and gives
//! the three-step quickstart with the verify-it-yourself promise.

use crate::config::LandingConfig;

/// Render the full landing HTML page.
pub fn page_html(cfg: &LandingConfig) -> String {
    let status_url = esc(&cfg.status_url);
    let console_url = esc(&cfg.console_url);
    let docs_url = esc(&cfg.docs_url);
    let repo_url = esc(&cfg.repo_url);

    let mut h = String::with_capacity(12 * 1024);
    h.push_str("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">");
    h.push_str("<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">");
    h.push_str("<title>DreggNet Cloud — the verifiable agent cloud</title>");
    h.push_str("<meta name=\"description\" content=\"DreggNet Cloud: deploy and run with an agent, bounded and proven. Every action carries a receipt you can verify yourself — don't trust the cloud, check it.\">");
    h.push_str(STYLE);
    h.push_str("</head><body><div class=\"wrap\">");

    // ── Nav ──────────────────────────────────────────────────────────────────
    h.push_str(&format!(
        "<nav><span class=\"brand\">DreggNet<span class=\"brand-c\">Cloud</span></span>\
         <span class=\"nav-links\">\
         <a href=\"{status}\">Status</a>\
         <a href=\"{docs}\">Docs</a>\
         <a href=\"{repo}\">Source</a>\
         <a class=\"cta-sm\" href=\"{console}\">Sign in</a></span></nav>",
        status = status_url,
        docs = docs_url,
        repo = repo_url,
        console = console_url,
    ));

    // ── Live status banner (filled client-side; honest "checking…") ───────────
    h.push_str(&format!(
        "<a class=\"livebar unknown\" id=\"livebar\" href=\"{status}\">\
         <span class=\"dot\"></span><span class=\"lbl\" id=\"livebar-lbl\">checking live status…</span>\
         <span class=\"go\">view status →</span></a>",
        status = status_url,
    ));

    // ── Hero ─────────────────────────────────────────────────────────────────
    h.push_str(
        "<header class=\"hero\">\
         <h1>The verifiable agent cloud.</h1>\
         <p class=\"tag\">Deploy a site, rent a server, run an agent — with a hard budget bound and \
         a cryptographic receipt for every action. Then <b>verify it yourself</b>. \
         Don't trust the cloud; check it.</p>",
    );
    h.push_str(&format!(
        "<div class=\"hero-cta\">\
         <a class=\"cta\" href=\"{console}\">Open the console</a>\
         <a class=\"cta ghost\" href=\"{docs}\">Quickstart</a></div></header>",
        console = console_url,
        docs = docs_url,
    ));

    // ── What it IS ─────────────────────────────────────────────────────────────
    h.push_str("<section><h2>What DreggNet Cloud is</h2><div class=\"cards\">");
    for (icon, title, body) in [
        (
            "◇",
            "Bounded by capability",
            "An agent runs against a capability you mint — a hard ceiling on everything it could ever do. \
             It cannot amplify its own authority, and the bound is enforced in the protocol, not by trust.",
        ),
        (
            "✓",
            "Proven, not promised",
            "Every turn leaves a signed, re-witnessable receipt. A light client — not the cloud — can \
             confirm a genuine kernel transition happened. The federation's Rust and Lean executors \
             cross-check each other; any disagreement is surfaced, never hidden.",
        ),
        (
            "↻",
            "Verify it yourself",
            "Re-witness any deploy or agent run in your own browser: the chain checks, the budget bound \
             holds, the tests ran on the deployed code. The math speaks — you never take the console's \
             word for your own resources.",
        ),
        (
            "⊞",
            "A real cloud, on a real chain",
            "Sites on *.example.com, persistent servers, custom domains, content-addressed storage, and a \
             $DREGG meter — all owned by your dregg identity, all cap-scoped to you, settled on a live \
             federated chain.",
        ),
    ] {
        h.push_str(&format!(
            "<div class=\"card\"><div class=\"card-i\">{icon}</div>\
             <div class=\"card-t\">{title}</div><div class=\"card-b\">{body}</div></div>",
            icon = esc(icon),
            title = esc(title),
            body = esc(body),
        ));
    }
    h.push_str("</div></section>");

    // ── Quickstart ─────────────────────────────────────────────────────────────
    h.push_str("<section><h2>Quickstart</h2><div class=\"steps\">");
    for (n, title, body, code) in [
        (
            "1",
            "Deploy a site",
            "Publish static content to a verifiable, content-addressed cell on *.example.com.",
            "dregg-cloud login\ndregg-cloud deploy ./site --name my-site",
        ),
        (
            "2",
            "Run the agent",
            "Give an agent a capability and a budget; it deploys, runs tests, and seals a receipt chain — \
             it can never exceed the bound you set.",
            "dregg-cloud agent run ./plan.toml \\\n  --budget 50 --cap deploy",
        ),
        (
            "3",
            "Verify it",
            "Re-witness the run yourself — chain ✓, budget bound ✓, QA ran on the deployed code ✓. \
             No trust in the cloud required.",
            "dregg-cloud verify --agent my-agent\n# or paste the report into the console",
        ),
    ] {
        h.push_str(&format!(
            "<div class=\"step\"><div class=\"step-n\">{n}</div>\
             <div class=\"step-body\"><div class=\"step-t\">{title}</div>\
             <div class=\"step-d\">{body}</div><pre><code>{code}</code></pre></div></div>",
            n = esc(n),
            title = esc(title),
            body = esc(body),
            code = esc(code),
        ));
    }
    h.push_str("</div></section>");

    // ── Verify-it-yourself strip ───────────────────────────────────────────────
    h.push_str(&format!(
        "<section class=\"verify-strip\">\
         <h2>Don't trust. Verify.</h2>\
         <p>Every resource carries the commitment a light client checks. Open the \
         <a href=\"{console}\">console</a> and hit <b>re-verify</b> on any agent run — \
         the chain, the budget bound, and the QA proof are re-witnessed in your browser, \
         against the deployed code. The <a href=\"{status}\">status page</a> shows the live \
         federation, the Rust↔Lean differential, and gossip-storm visibility — and any \
         surface it can't reach is shown <em>Unknown</em>, never falsely green.</p></section>",
        console = console_url,
        status = status_url,
    ));

    // ── Footer ─────────────────────────────────────────────────────────────────
    h.push_str(&format!(
        "<footer>DreggNet Cloud — the verifiable agent cloud. \
         <a href=\"{status}\">Live status</a> · <a href=\"{docs}\">Docs</a> · \
         <a href=\"{repo}\">Source</a>. \
         A surface we can't reach is shown <em>Unknown</em>, never falsely green.</footer>",
        status = status_url,
        docs = docs_url,
        repo = repo_url,
    ));

    h.push_str("</div>");
    h.push_str(&live_status_script(&cfg.status_url));
    h.push_str("</body></html>");
    h
}

/// The progressive-enhancement script that fetches the status page's
/// `/status.json` and paints the live banner. JS-encoded URL is the only dynamic
/// bit; on any failure the banner stays honest ("status unavailable", not green).
fn live_status_script(status_url: &str) -> String {
    let js_url = js_string(status_url.trim_end_matches('/'));
    format!(
        "<script>\
(function(){{\
  var base={js_url};\
  var bar=document.getElementById('livebar');\
  var lbl=document.getElementById('livebar-lbl');\
  if(!bar||!lbl)return;\
  var heads={{operational:'All systems operational',degraded:'Partial service degradation',\
down:'Major service outage',unknown:'Status unknown'}};\
  fetch(base+'/status.json',{{cache:'no-store'}}).then(function(r){{\
    if(!r.ok)throw new Error('http '+r.status);return r.json();\
  }}).then(function(d){{\
    var o=(d&&d.overall)||'unknown';\
    bar.className='livebar '+(heads[o]?o:'unknown');\
    lbl.textContent=heads[o]||'Status unknown';\
  }}).catch(function(){{\
    bar.className='livebar unknown';\
    lbl.textContent='Live status unavailable';\
  }});\
}})();\
</script>"
    )
}

/// JSON/JS-encode a string for safe embedding in a `<script>` literal.
fn js_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '<' => out.push_str("\\u003c"),
            '>' => out.push_str("\\u003e"),
            '&' => out.push_str("\\u0026"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Minimal HTML-escaping for embedded text.
pub fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

const STYLE: &str = r#"<style>
:root{--bg:#0d1117;--card:#161b22;--line:#30363d;--ink:#e6edf3;--mut:#8b949e;--acc:#58a6ff;
--op:#2ea043;--dg:#d29922;--dn:#f85149;--un:#6e7681;}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);
font:16px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
a{color:var(--acc);text-decoration:none} a:hover{text-decoration:underline}
.wrap{max-width:960px;margin:0 auto;padding:20px 20px 80px}
nav{display:flex;align-items:center;justify-content:space-between;padding:8px 0 22px}
.brand{font-size:20px;font-weight:800;letter-spacing:-.01em}
.brand-c{color:var(--acc);margin-left:2px}
.nav-links{display:flex;gap:18px;align-items:center;font-size:14px}
.nav-links a{color:var(--mut)} .nav-links a:hover{color:var(--ink)}
.cta-sm{padding:6px 14px;border:1px solid var(--line);border-radius:8px;color:var(--ink)!important}
.cta-sm:hover{border-color:var(--acc);text-decoration:none}
.livebar{display:flex;align-items:center;gap:12px;padding:12px 16px;border-radius:10px;
border:1px solid var(--line);background:var(--card);margin-bottom:36px;color:var(--ink)}
.livebar:hover{text-decoration:none;border-color:var(--acc)}
.livebar .dot{width:11px;height:11px;border-radius:50%;flex:none;background:var(--un)}
.livebar .lbl{font-weight:600;font-size:14px}
.livebar .go{margin-left:auto;color:var(--mut);font-size:13px}
.livebar.operational{border-color:var(--op)} .livebar.operational .dot{background:var(--op)}
.livebar.degraded{border-color:var(--dg)} .livebar.degraded .dot{background:var(--dg)}
.livebar.down{border-color:var(--dn)} .livebar.down .dot{background:var(--dn)}
.livebar.unknown .dot{background:var(--un)}
.hero{padding:18px 0 30px}
.hero h1{font-size:46px;line-height:1.08;margin:0 0 16px;letter-spacing:-.02em;font-weight:800}
.hero .tag{font-size:19px;color:var(--mut);max-width:680px;margin:0 0 26px}
.hero .tag b{color:var(--ink)}
.hero-cta{display:flex;gap:12px;flex-wrap:wrap}
.cta{display:inline-block;padding:12px 22px;border-radius:10px;font-weight:600;
background:var(--acc);color:#0d1117!important}
.cta:hover{text-decoration:none;filter:brightness(1.08)}
.cta.ghost{background:transparent;color:var(--ink)!important;border:1px solid var(--line)}
.cta.ghost:hover{border-color:var(--acc)}
h2{font-size:14px;text-transform:uppercase;letter-spacing:.07em;color:var(--mut);
margin:46px 0 16px;font-weight:600}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(240px,1fr));gap:14px}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:18px 18px 20px}
.card-i{font-size:22px;color:var(--acc);margin-bottom:8px}
.card-t{font-weight:700;font-size:16px;margin-bottom:6px}
.card-b{color:var(--mut);font-size:14px}
.steps{display:flex;flex-direction:column;gap:12px}
.step{display:flex;gap:16px;background:var(--card);border:1px solid var(--line);
border-radius:12px;padding:18px 18px}
.step-n{flex:none;width:34px;height:34px;border-radius:50%;background:rgba(88,166,255,.14);
color:var(--acc);font-weight:800;display:flex;align-items:center;justify-content:center}
.step-body{flex:1;min-width:0}
.step-t{font-weight:700;font-size:16px}
.step-d{color:var(--mut);font-size:14px;margin:4px 0 10px}
pre{margin:0;background:#0b0e13;border:1px solid var(--line);border-radius:8px;
padding:12px 14px;overflow-x:auto}
code{font:13px/1.5 ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;color:#c9d1d9}
.verify-strip{background:linear-gradient(180deg,var(--card),#11151c);
border:1px solid var(--line);border-radius:12px;padding:8px 22px 22px;margin-top:46px}
.verify-strip h2{color:var(--ink);text-transform:none;letter-spacing:-.01em;font-size:22px;font-weight:800}
.verify-strip p{color:var(--mut);font-size:15px;max-width:760px}
.verify-strip b{color:var(--ink)}
footer{margin-top:48px;color:var(--mut);font-size:13px;border-top:1px solid var(--line);padding-top:18px}
footer a{color:var(--acc)}
em{color:var(--mut);font-style:italic}
@media(max-width:560px){.hero h1{font-size:34px}}
</style>"#;

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg() -> LandingConfig {
        LandingConfig {
            status_url: "https://status.example".into(),
            console_url: "https://console.example".into(),
            docs_url: "https://docs.example".into(),
            repo_url: "https://repo.example/x".into(),
            ..LandingConfig::default()
        }
    }

    #[test]
    fn renders_the_pitch_status_and_quickstart() {
        let html = page_html(&cfg());
        // The pitch.
        assert!(html.contains("verifiable agent cloud"));
        assert!(html.contains("Verify it yourself") || html.contains("verify it yourself"));
        // What it IS.
        assert!(html.contains("Bounded by capability"));
        assert!(html.contains("Proven, not promised"));
        // The quickstart (deploy / run / verify).
        assert!(html.contains("Deploy a site"));
        assert!(html.contains("Run the agent"));
        assert!(html.contains("dregg-cloud deploy"));
        assert!(html.contains("dregg-cloud verify") || html.contains("dregg-cloud agent"));
        // The honesty law is on the front door too.
        assert!(html.contains("never falsely green"));
    }

    #[test]
    fn links_point_at_the_configured_public_urls() {
        let html = page_html(&cfg());
        assert!(html.contains("https://status.example"));
        assert!(html.contains("https://console.example"));
        assert!(html.contains("https://docs.example"));
        assert!(html.contains("https://repo.example/x"));
    }

    #[test]
    fn the_live_status_script_embeds_the_status_json_url() {
        let html = page_html(&cfg());
        // The client-side live banner fetches /status.json from the status URL.
        assert!(html.contains("/status.json"));
        assert!(html.contains("\"https://status.example\""));
        // The banner starts honest-unknown (never a false green at first paint).
        assert!(html.contains("class=\"livebar unknown\""));
        assert!(html.contains("checking live status"));
    }

    #[test]
    fn status_url_is_js_escaped_not_raw_injected() {
        let mut c = cfg();
        c.status_url = "https://x/\"</script><script>alert(1)//".into();
        let html = page_html(&c);
        // The raw closing tag must not appear verbatim inside the script literal.
        assert!(!html.contains("\"</script><script>alert(1)"));
        assert!(html.contains("\\u003c/script"));
    }

    #[test]
    fn escapes_html_in_config() {
        let mut c = cfg();
        c.docs_url = "https://x?a=1&b=2".into();
        let html = page_html(&c);
        assert!(html.contains("https://x?a=1&amp;b=2"));
    }
}

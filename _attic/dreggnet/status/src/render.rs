//! Server-render the public [`StatusPage`] into one self-contained HTML page.
//!
//! No external assets, no JS required — a single document anyone can load to see
//! "is the cloud up?". The same [`StatusPage`] serializes verbatim as
//! `/status.json` for machine consumers.

use crate::model::*;

/// Render the full HTML page.
pub fn page_html(page: &StatusPage) -> String {
    let overall = page.overall;
    let mut html = String::with_capacity(8 * 1024);

    html.push_str("<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\">");
    html.push_str("<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">");
    html.push_str("<meta http-equiv=\"refresh\" content=\"30\">");
    html.push_str("<title>DreggNet Status</title>");
    html.push_str(STYLE);
    html.push_str("</head><body><div class=\"wrap\">");

    // Header.
    html.push_str("<header><h1>DreggNet Status</h1>");
    html.push_str(&format!(
        "<span class=\"ts\">updated {}</span></header>",
        esc(&page.generated_at)
    ));

    // Overall banner.
    html.push_str(&format!(
        "<div class=\"banner {cls}\"><span class=\"dot\"></span><div><div class=\"head\">{head}</div>\
         <div class=\"sub\">{sub}</div></div></div>",
        cls = overall.slug(),
        head = esc(overall.headline()),
        sub = esc(&page.overall_detail),
    ));

    // Per-service rows.
    html.push_str("<section><h2>Services</h2><div class=\"svc\">");
    for s in &page.services {
        html.push_str(&format!(
            "<div class=\"row\"><span class=\"name\">{name}<span class=\"tier\">{tier}</span></span>\
             <span class=\"detail\">{detail}</span>\
             <span class=\"pill {cls}\">{label}</span></div>",
            name = esc(&s.name),
            tier = if s.tier == Tier::Core { "core" } else { "optional" },
            detail = esc(&s.detail),
            cls = s.state.slug(),
            label = esc(s.state.label()),
        ));
    }
    html.push_str("</div></section>");

    // Federation panel.
    html.push_str(&federation_html(&page.federation));

    // Uptime.
    if !page.uptime.is_empty() {
        html.push_str("<section><h2>Uptime</h2><div class=\"uptime\">");
        for u in &page.uptime {
            html.push_str(&format!(
                "<div class=\"uw\"><div class=\"pct\">{:.3}%</div><div class=\"lbl\">{}</div></div>",
                u.uptime_pct,
                esc(&u.label),
            ));
        }
        html.push_str("</div></section>");
    }

    // Incidents.
    html.push_str("<section><h2>Recent incidents</h2>");
    if page.incidents.is_empty() {
        html.push_str("<p class=\"none\">No incidents reported.</p>");
    } else {
        html.push_str("<div class=\"incidents\">");
        for inc in &page.incidents {
            let status = if inc.is_open() { "ongoing" } else { "resolved" };
            html.push_str(&format!(
                "<div class=\"inc sev-{sev}\"><div class=\"inc-head\">\
                 <span class=\"inc-title\">{title}</span>\
                 <span class=\"inc-pill {sevc}\">{sevlabel}</span>\
                 <span class=\"inc-status {st}\">{status}</span></div>\
                 <div class=\"inc-meta\">{started}{resolved} · affects {affected}</div>\
                 <div class=\"inc-body\">{body}</div></div>",
                sev = esc(&inc.severity),
                sevc = severity_class(&inc.severity),
                sevlabel = esc(&inc.severity),
                title = esc(&inc.title),
                st = status,
                status = status,
                started = esc(&inc.started_at),
                resolved = inc
                    .resolved_at
                    .as_ref()
                    .map(|r| format!(" → {}", esc(r)))
                    .unwrap_or_default(),
                affected = esc(&inc.affected.join(", ")),
                body = esc(&inc.body),
            ));
        }
        html.push_str("</div>");
    }
    html.push_str("</section>");

    html.push_str(
        "<footer>This is the public status page. \
         <a href=\"/status.json\">/status.json</a> is the machine-readable view. \
         A surface we cannot reach is shown <em>Unknown</em>, never falsely green.</footer>",
    );
    html.push_str("</div></body></html>");
    html
}

/// The federation panel block.
fn federation_html(f: &FederationPanel) -> String {
    let mut h = String::new();
    h.push_str("<section><h2>Federation</h2>");
    h.push_str(&format!(
        "<div class=\"fed-summary\"><span><b>{}/{}</b> up</span>\
         <span><b>{}</b> finalizing</span>\
         <span>quorum <b>{}</b></span>\
         <span class=\"diff {dc}\">{diff}</span></div>",
        f.up,
        f.expected,
        f.finalizing,
        f.quorum_needed,
        dc = match &f.differential {
            Differential::Agreeing => "operational",
            Differential::Diverged { .. } => "down",
            Differential::Unknown => "unknown",
        },
        diff = esc(&f.differential.label()),
    ));
    if let (Some(h_), Some(age)) = (f.last_finalized_height, f.last_finalized_age_secs) {
        h.push_str(&format!(
            "<div class=\"fed-fin\">last finalized height <b>{h_}</b>, <b>{age}s</b> ago</div>"
        ));
    }
    // Gossip storm-backpressure visibility — honest Unknown when the node does
    // not export the rejected-stream metric (never a false "no storm").
    h.push_str(&match f.gossip_rejected {
        Some(0) => "<div class=\"fed-fin\">gossip backpressure: <b>no streams rejected</b></div>"
            .to_string(),
        Some(n) => format!(
            "<div class=\"fed-fin\">gossip backpressure: <b>{n}</b> inbound streams rejected \
             (storm limit engaging)</div>"
        ),
        None => "<div class=\"fed-fin\">gossip backpressure: <b>unknown</b> \
                 (rejected-stream metric not exported)</div>"
            .to_string(),
    });
    h.push_str("<div class=\"fed-nodes\">");
    for n in &f.nodes {
        h.push_str(&format!(
            "<div class=\"fn\"><span class=\"fn-name\">{name}</span>\
             <span class=\"fn-meta\">{height}{age}</span>\
             <span class=\"pill {cls}\">{label}</span></div>",
            name = esc(&n.name),
            height = n
                .height
                .map(|x| format!("h{x}"))
                .unwrap_or_else(|| "—".into()),
            age = n
                .finality_age_secs
                .map(|a| format!(" · {a}s"))
                .unwrap_or_default(),
            cls = n.state.slug(),
            label = esc(n.state.label()),
        ));
    }
    h.push_str("</div></section>");
    h
}

/// Map an incident severity to a pill CSS class.
fn severity_class(sev: &str) -> &'static str {
    match sev {
        "down" => "down",
        "degraded" => "degraded",
        _ => "info",
    }
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
:root{--bg:#0d1117;--card:#161b22;--line:#30363d;--ink:#e6edf3;--mut:#8b949e;
--op:#2ea043;--dg:#d29922;--dn:#f85149;--un:#6e7681;}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);
font:15px/1.5 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif}
.wrap{max-width:820px;margin:0 auto;padding:28px 18px 60px}
header{display:flex;align-items:baseline;justify-content:space-between;gap:12px;margin-bottom:18px}
h1{font-size:22px;margin:0}
h2{font-size:14px;text-transform:uppercase;letter-spacing:.06em;color:var(--mut);
margin:28px 0 10px;font-weight:600}
.ts{color:var(--mut);font-size:13px}
.banner{display:flex;align-items:center;gap:14px;padding:18px 20px;border-radius:12px;
border:1px solid var(--line);background:var(--card)}
.banner .dot{width:14px;height:14px;border-radius:50%;flex:none}
.banner .head{font-size:18px;font-weight:700}
.banner .sub{color:var(--mut);font-size:13px}
.banner.operational{border-color:var(--op)} .banner.operational .dot{background:var(--op)}
.banner.degraded{border-color:var(--dg)} .banner.degraded .dot{background:var(--dg)}
.banner.down{border-color:var(--dn)} .banner.down .dot{background:var(--dn)}
.banner.unknown{border-color:var(--un)} .banner.unknown .dot{background:var(--un)}
.svc,.incidents,.fed-nodes{display:flex;flex-direction:column;gap:8px}
.row,.fn{display:flex;align-items:center;gap:12px;padding:12px 16px;background:var(--card);
border:1px solid var(--line);border-radius:10px}
.name{font-weight:600;min-width:180px}
.tier{display:inline-block;margin-left:8px;font-size:10px;color:var(--mut);
text-transform:uppercase;letter-spacing:.05em;font-weight:500;vertical-align:middle}
.detail{color:var(--mut);font-size:13px;flex:1}
.pill{font-size:12px;font-weight:600;padding:3px 10px;border-radius:999px;white-space:nowrap}
.pill.operational{color:var(--op);background:rgba(46,160,67,.12)}
.pill.degraded{color:var(--dg);background:rgba(210,153,34,.14)}
.pill.down{color:var(--dn);background:rgba(248,81,73,.14)}
.pill.unknown{color:var(--un);background:rgba(110,118,129,.18)}
.pill.not_configured{color:var(--un);background:rgba(110,118,129,.10)}
.fed-summary{display:flex;gap:18px;flex-wrap:wrap;padding:12px 16px;background:var(--card);
border:1px solid var(--line);border-radius:10px;margin-bottom:8px;font-size:14px}
.fed-summary b{color:var(--ink)} .fed-summary span{color:var(--mut)}
.diff.operational{color:var(--op)} .diff.down{color:var(--dn)} .diff.unknown{color:var(--un)}
.fed-fin{color:var(--mut);font-size:13px;margin-bottom:8px}
.fn-name{font-weight:600;min-width:90px} .fn-meta{color:var(--mut);font-size:13px;flex:1}
.uptime{display:flex;gap:12px;flex-wrap:wrap}
.uw{flex:1;min-width:120px;background:var(--card);border:1px solid var(--line);
border-radius:10px;padding:14px 16px;text-align:center}
.uw .pct{font-size:22px;font-weight:700} .uw .lbl{color:var(--mut);font-size:12px;margin-top:2px}
.inc{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:14px 16px;
border-left:4px solid var(--un)}
.inc.sev-down{border-left-color:var(--dn)} .inc.sev-degraded{border-left-color:var(--dg)}
.inc.sev-info{border-left-color:var(--un)}
.inc-head{display:flex;align-items:center;gap:10px;flex-wrap:wrap}
.inc-title{font-weight:600}
.inc-pill{font-size:11px;font-weight:600;padding:2px 8px;border-radius:999px}
.inc-pill.down{color:var(--dn);background:rgba(248,81,73,.14)}
.inc-pill.degraded{color:var(--dg);background:rgba(210,153,34,.14)}
.inc-pill.info{color:var(--un);background:rgba(110,118,129,.18)}
.inc-status{font-size:11px;color:var(--mut);margin-left:auto}
.inc-status.ongoing{color:var(--dn);font-weight:600}
.inc-meta{color:var(--mut);font-size:12px;margin:6px 0}
.inc-body{font-size:13px}
.none{color:var(--mut)}
footer{margin-top:36px;color:var(--mut);font-size:12px;border-top:1px solid var(--line);padding-top:14px}
footer a{color:#58a6ff}
</style>"#;

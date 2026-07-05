//! `dreggnet-console` — the serving binary for the signed-in customer console.
//!
//! A pure-std thread-per-connection HTTP/1.1 server (the same shape as
//! `dreggnet-ops` / `dreggnet-webauth` — no `httpe`/Elide closure, cross-builds
//! trivially) that resolves the authenticated subject from the webauth
//! forward-auth headers, cap-scopes the resource catalog to that subject, and
//! serves the "my stuff" page + the read/verify APIs:
//!
//! | Method + path     | Serves                                                       |
//! |-------------------|--------------------------------------------------------------|
//! | `GET /`           | the server-rendered, cap-scoped console page                 |
//! | `GET /api/me`     | the authenticated subject's [`ConsoleView`] JSON             |
//! | `GET /api/whoami` | the subject / cap / how, from the forward-auth headers       |
//! | `POST /api/verify`| re-witness an agent run / site root in-page (verify-don't-trust) |
//! | `GET /healthz`    | liveness (always open)                                       |
//!
//! Auth: the subject is taken from the *verified* `X-Dregg-Subject` the
//! `dreggnet-webauth` forward-auth resolved and Caddy copied on (NEVER a query
//! param — a user cannot widen their view to another's cells). When
//! `CONSOLE_REQUIRE_CAP` is set the dashboard additionally fails closed if the
//! cap header is absent (internalizes the edge gate); a break-glass admit is
//! always honored.
//!
//!   cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-console

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

use dreggnet_console::source::{FixtureSource, LiveSource, ResourceSource, view_for};
use dreggnet_console::{ConsoleConfig, render, verify};

const MAX_HEADER_BYTES: usize = 64 * 1024;
const MAX_BODY_BYTES: usize = 4 * 1024 * 1024; // an agent run report can be sizeable.

fn main() -> std::io::Result<()> {
    let cfg = Arc::new(ConsoleConfig::from_env());
    // Serve from the live aggregator when a read-API surface is wired (the
    // reviewed-go deploy step), else the deterministic fixtures. Either way the
    // cap-scoping in `for_subject` narrows the catalog to the authenticated
    // subject — the teeth hold against live data exactly as over fixtures.
    let live = cfg.read_api.is_live();
    let source: Arc<dyn ResourceSource> = if live {
        Arc::new(LiveSource::new(cfg.read_api.clone()))
    } else {
        Arc::new(FixtureSource)
    };

    let listener = TcpListener::bind(&cfg.bind)?;
    eprintln!(
        "dreggnet-console: serving the customer console on http://{}",
        cfg.bind
    );
    eprintln!(
        "  source:   {}",
        if live {
            "live (aggregating the real resource surfaces)"
        } else {
            "fixture (set CONSOLE_READ_API / CONSOLE_LIVE=1 to go live)"
        }
    );
    eprintln!(
        "  cap-gate: {}",
        match cfg.require_cap.as_deref() {
            Some(c) => format!("REQUIRED `{c}` (X-Dregg-Cap + X-Dregg-Subject; fail-closed)"),
            None => "trust the edge (set CONSOLE_REQUIRE_CAP to fail closed)".to_string(),
        }
    );
    eprintln!(
        "  dev-subject: {}",
        cfg.dev_subject
            .as_deref()
            .unwrap_or("(none — needs the webauth X-Dregg-Subject header)")
    );

    for stream in listener.incoming() {
        let Ok(stream) = stream else { continue };
        let cfg = Arc::clone(&cfg);
        let source = Arc::clone(&source);
        std::thread::spawn(move || {
            if let Err(e) = serve(stream, &cfg, source.as_ref()) {
                eprintln!("dreggnet-console: connection error: {e}");
            }
        });
    }
    Ok(())
}

fn serve(
    mut stream: TcpStream,
    cfg: &ConsoleConfig,
    source: &dyn ResourceSource,
) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(15))).ok();

    // Read the head (request line + headers).
    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        if let Some(pos) = find(&buf, b"\r\n\r\n") {
            break pos + 4;
        }
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
        if buf.len() > MAX_HEADER_BYTES {
            return write_resp(&mut stream, 431, "text/plain", b"header too large");
        }
    };
    let head_text = String::from_utf8_lossy(&buf[..header_end]).into_owned();
    let request_line = head_text.lines().next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/");
    let path = target.split('?').next().unwrap_or("/");

    // Liveness is always open.
    if path == "/healthz" {
        return write_resp(
            &mut stream,
            200,
            "application/json",
            br#"{"ok":true,"service":"dreggnet-console"}"#,
        );
    }

    // App-layer cap enforcement (fail-closed when CONSOLE_REQUIRE_CAP is set).
    if let Some(required) = cfg.require_cap.as_deref() {
        if !cap_satisfied(&head_text, required) {
            return write_resp(
                &mut stream,
                403,
                "text/plain",
                format!(
                    "the `{required}` dregg capability is required for the console (via the webauth \
                     forward-auth). Sign in at {}/login.\n",
                    cfg.login_base
                )
                .as_bytes(),
            );
        }
    }

    // Resolve WHO is signed in — strictly from the verified forward-auth header
    // (a query param can never widen the scope to another subject's cells).
    let header_subject = header_value(&head_text, "x-dregg-subject");
    let Some(subject) = resolve_subject(cfg, header_subject.as_deref()) else {
        return write_resp(
            &mut stream,
            401,
            "text/plain",
            format!(
                "not signed in: no dregg identity on this request. Sign in at {}/login to see your \
                 console.\n",
                cfg.login_base
            )
            .as_bytes(),
        );
    };

    match (method, path) {
        ("GET", "/") | ("GET", "/index.html") => {
            let view = view_for(source, &subject);
            let html = render::render_page(&view, &cfg.login_base);
            write_resp(
                &mut stream,
                200,
                "text/html; charset=utf-8",
                html.as_bytes(),
            )
        }
        ("GET", "/api/me") => {
            let view = view_for(source, &subject);
            let body = serde_json::to_vec(&view).unwrap_or_default();
            write_resp(&mut stream, 200, "application/json", &body)
        }
        ("GET", "/api/whoami") => {
            let cap = header_value(&head_text, "x-dregg-cap").unwrap_or_default();
            let how = header_value(&head_text, "x-dregg-auth").unwrap_or_default();
            let body = format!(
                r#"{{"subject":{},"cap":{},"how":{}}}"#,
                json_str(&subject),
                json_str(&cap),
                json_str(&how)
            );
            write_resp(&mut stream, 200, "application/json", body.as_bytes())
        }
        ("POST", "/api/verify") => {
            let body = read_body(&mut stream, &buf, header_end, &head_text)?;
            let result = handle_verify(&body, &subject, source);
            write_resp(&mut stream, 200, "application/json", result.as_bytes())
        }
        _ => write_resp(&mut stream, 404, "text/plain", b"not found"),
    }
}

/// Resolve the signed-in subject. Production (`require_cap` set): ONLY the
/// verified `X-Dregg-Subject` header — never the dev fallback, never a param.
/// Dev (`require_cap` unset): the header if present, else the configured
/// `dev_subject` so the page is browsable without the live edge.
fn resolve_subject(cfg: &ConsoleConfig, header_subject: Option<&str>) -> Option<String> {
    if let Some(s) = header_subject.map(str::trim).filter(|s| !s.is_empty()) {
        return Some(s.to_string());
    }
    if cfg.require_cap.is_some() {
        return None; // production fail-closed: an identity is mandatory.
    }
    cfg.dev_subject.clone()
}

/// Handle a POST /api/verify body (an agent re-verify, a pasted report, or a
/// site-root check). Returns the verdict JSON.
fn handle_verify(body: &str, subject: &str, source: &dyn ResourceSource) -> String {
    let Ok(req) = serde_json::from_str::<serde_json::Value>(body) else {
        return r#"{"ok":false,"detail":"request body is not valid JSON"}"#.to_string();
    };

    // (a) the scoped "re-verify my agent" button.
    if let Some(agent_id) = req.get("agent_id").and_then(|v| v.as_str()) {
        let catalog = source.catalog();
        let found = catalog
            .agents
            .iter()
            .find(|a| a.id == agent_id && a.owner == subject);
        return match found {
            Some(a) => {
                let r = verify::verify_agent_report(
                    &a.report,
                    &a.deployed_root,
                    Some((subject, &a.owner)),
                );
                serde_json::to_string(&r).unwrap_or_default()
            }
            None => format!(
                r#"{{"ok":false,"detail":{}}}"#,
                json_str(&format!(
                    "no agent `{agent_id}` owned by you — you can only re-verify your own agents"
                ))
            ),
        };
    }

    // (b) the open "paste any report" path — a self-contained proof verifies for
    //     anyone (verify-don't-trust); no scoping needed.
    if let Some(report_val) = req.get("report") {
        return match serde_json::from_value::<dreggnet_exec::agent::AgentRunReport>(
            report_val.clone(),
        ) {
            Ok(report) => {
                let deployed_root = req
                    .get("deployed_root")
                    .and_then(|v| v.as_str())
                    .unwrap_or("");
                let r = verify::verify_agent_report(&report, deployed_root, None);
                serde_json::to_string(&r).unwrap_or_default()
            }
            Err(e) => format!(
                r#"{{"ok":false,"detail":{}}}"#,
                json_str(&format!(
                    "the pasted report did not parse as an agent run report: {e}"
                ))
            ),
        };
    }

    // (c) a site-root check — owner-scoped: you can only verify a content root
    //     that belongs to one of YOUR sites/buckets.
    if let Some(root) = req.get("site_root").and_then(|v| v.as_str()) {
        let catalog = source.catalog();
        let owns = catalog
            .sites
            .iter()
            .any(|s| s.owner == subject && s.content_root == root)
            || catalog
                .buckets
                .iter()
                .any(|b| b.owner == subject && b.content_root == root);
        return format!(
            r#"{{"ok":{},"kind":"content-root","detail":{}}}"#,
            owns,
            json_str(&if owns {
                format!("content root {root} is committed to one of your published cells ✓")
            } else {
                format!("no published cell of yours commits to content root {root}")
            })
        );
    }

    r#"{"ok":false,"detail":"verify request: expected one of agent_id / report / site_root"}"#
        .to_string()
}

/// Read the request body using Content-Length (the bytes after the head plus any
/// already buffered).
fn read_body(
    stream: &mut TcpStream,
    buf: &[u8],
    header_end: usize,
    head_text: &str,
) -> std::io::Result<String> {
    let len = header_value(head_text, "content-length")
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or(0)
        .min(MAX_BODY_BYTES);
    let mut body = buf[header_end..].to_vec();
    while body.len() < len {
        let mut tmp = [0u8; 8192];
        let n = stream.read(&mut tmp)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&tmp[..n]);
    }
    body.truncate(len);
    Ok(String::from_utf8_lossy(&body).into_owned())
}

/// Whether the request satisfies `required` — the cap webauth verified is present
/// (`X-Dregg-Cap`, possibly an AnyOf set) or a break-glass admit. Fails closed.
fn cap_satisfied(head_text: &str, required: &str) -> bool {
    if let Some(how) = header_value(head_text, "x-dregg-auth") {
        if how.to_ascii_lowercase().contains("break-glass") {
            return true;
        }
    }
    match header_value(head_text, "x-dregg-cap") {
        Some(caps) => caps
            .split(|c: char| c == ',' || c.is_whitespace())
            .any(|c| c.eq_ignore_ascii_case(required)),
        None => false,
    }
}

/// The value of a request header by case-insensitive name, trimmed.
fn header_value(head_text: &str, name: &str) -> Option<String> {
    head_text.lines().find_map(|l| {
        let (k, v) = l.split_once(':')?;
        if k.trim().eq_ignore_ascii_case(name) {
            Some(v.trim().to_string())
        } else {
            None
        }
    })
}

/// JSON-encode a string for embedding in a hand-built body.
fn json_str(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_string())
}

/// Write a full HTTP/1.1 response and close the connection.
fn write_resp(
    stream: &mut TcpStream,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> std::io::Result<()> {
    let reason = match status {
        200 => "OK",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        431 => "Request Header Fields Too Large",
        _ => "OK",
    };
    let header = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\n\
         Cache-Control: no-store\r\nConnection: close\r\n\r\n",
        body.len()
    );
    stream.write_all(header.as_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

/// First index of `needle` in `haystack`.
fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() || haystack.len() < needle.len() {
        return None;
    }
    haystack.windows(needle.len()).position(|w| w == needle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_console::fixtures;

    fn prod_cfg() -> ConsoleConfig {
        ConsoleConfig {
            require_cap: Some("console-user".into()),
            dev_subject: Some("dregg:devonly000000000".into()),
            ..ConsoleConfig::default()
        }
    }

    // ── TOOTH: the subject is the verified header, never a spoofable fallback ──
    #[test]
    fn production_requires_the_verified_subject_header() {
        let cfg = prod_cfg();
        // No header in production → no identity (fail-closed), dev_subject IGNORED.
        assert_eq!(resolve_subject(&cfg, None), None);
        // The verified header is honored — and it, not the dev fallback, wins.
        assert_eq!(
            resolve_subject(&cfg, Some("dregg:realuser00000000")),
            Some("dregg:realuser00000000".to_string())
        );
    }

    #[test]
    fn dev_mode_falls_back_to_the_configured_subject() {
        let cfg = ConsoleConfig {
            dev_subject: Some("dregg:dev0000000000000".into()),
            ..ConsoleConfig::default()
        };
        assert_eq!(
            resolve_subject(&cfg, None),
            Some("dregg:dev0000000000000".to_string())
        );
        // A present header still wins in dev.
        assert_eq!(
            resolve_subject(&cfg, Some("dregg:hdr")),
            Some("dregg:hdr".to_string())
        );
    }

    #[test]
    fn cap_gate_fails_closed_without_the_cap() {
        assert!(cap_satisfied(
            "X-Dregg-Cap: console-user\r\n",
            "console-user"
        ));
        assert!(cap_satisfied(
            "X-Dregg-Cap: a, console-user, b\r\n",
            "console-user"
        ));
        assert!(!cap_satisfied("X-Dregg-Cap: other\r\n", "console-user"));
        assert!(!cap_satisfied("\r\n", "console-user"));
        assert!(cap_satisfied(
            "X-Dregg-Auth: break-glass override\r\n",
            "console-user"
        ));
    }

    // ── the scoped re-verify only re-witnesses YOUR agent ──────────────────────
    #[test]
    fn scoped_reverify_refuses_another_users_agent() {
        let src = FixtureSource;
        // The demo user re-verifies their own agent → a real verdict.
        let ok = handle_verify(
            r#"{"agent_id":"agent:deploy-bot"}"#,
            fixtures::DEMO_SUBJECT,
            &src,
        );
        assert!(ok.contains("\"ok\":true"), "{ok}");
        // A different subject cannot re-verify the demo user's agent (it isn't theirs).
        let denied = handle_verify(
            r#"{"agent_id":"agent:deploy-bot"}"#,
            "dregg:notthedemo00000",
            &src,
        );
        assert!(denied.contains("only re-verify your own"), "{denied}");
    }

    // ── the open paste path re-witnesses a self-contained report ───────────────
    #[test]
    fn the_paste_path_re_witnesses_a_report() {
        let src = FixtureSource;
        let (report, root) = fixtures::demo_agent_report();
        let req = serde_json::json!({ "report": report, "deployed_root": root }).to_string();
        let out = handle_verify(&req, "dregg:anyone0000000000", &src);
        assert!(out.contains("\"ok\":true"), "{out}");
        assert!(out.contains("\"chain_ok\":true"));
    }

    // ── the site-root check is owner-scoped ────────────────────────────────────
    #[test]
    fn site_root_check_is_owner_scoped() {
        let src = FixtureSource;
        let mine = handle_verify(
            &serde_json::json!({ "site_root": fixtures::DEMO_CONTENT_ROOT }).to_string(),
            fixtures::DEMO_SUBJECT,
            &src,
        );
        assert!(mine.contains("\"ok\":true"), "{mine}");
        // Another subject does not own that content root.
        let not_mine = handle_verify(
            &serde_json::json!({ "site_root": fixtures::DEMO_CONTENT_ROOT }).to_string(),
            "dregg:somebodyelse0000",
            &src,
        );
        assert!(not_mine.contains("\"ok\":false"), "{not_mine}");
    }
}

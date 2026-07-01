//! `dreggnet-attach` — the serving binary for the **portal web attach**.
//!
//! A pure-std thread-per-connection HTTP/1.1 + SSE server (the same shape as
//! `dreggnet-console` / `dreggnet-ops` — no `httpe`/Elide closure, cross-builds
//! trivially) that resolves the authenticated subject from the webauth
//! forward-auth headers, cap-scopes every session to that subject, and serves the
//! attach cockpit + the drive/stream/verify APIs:
//!
//! | Method + path                     | Serves                                            |
//! |-----------------------------------|---------------------------------------------------|
//! | `GET /`                           | the server-rendered, cap-scoped attach page       |
//! | `GET /api/whoami`                 | the subject / cap / how, from the forward-auth    |
//! | `GET /api/sessions`               | the subject's own sessions (JSON)                 |
//! | `POST /api/session`               | drive a goal into a NEW session owned by subject  |
//! | `GET /api/session/<id>`           | one of the subject's sessions (scoped; 404 else)  |
//! | `GET /api/session/<id>/stream`    | the reason→act→observe transcript as SSE (scoped) |
//! | `POST /api/session/<id>/fork`     | fork a session into an attenuated child (scoped)  |
//! | `POST /api/verify`                | re-witness a session in-browser (scoped; tamper)  |
//! | `GET /healthz`                    | liveness (always open)                            |
//!
//! Auth: the subject is taken from the *verified* `X-Dregg-Subject` the
//! `dreggnet-webauth` forward-auth resolved and Caddy copied on (NEVER a body or
//! query field — a user can neither drive a session as someone else nor reach
//! another's by id). When `ATTACH_REQUIRE_CAP` is set the surface additionally
//! fails closed if the cap header is absent. Break-glass is a server-secret escape
//! hatch (`ATTACH_BREAK_GLASS` + `X-Dregg-Break-Glass: <secret>`), NOT a header a
//! tenant can forge — disabled entirely when no secret is configured.
//!
//!   cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-attach

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

use dreggnet_attach::session::GoalRequest;
use dreggnet_attach::store::SessionStore;
use dreggnet_attach::{AttachConfig, render, stream, verify};

const MAX_HEADER_BYTES: usize = 64 * 1024;
const MAX_BODY_BYTES: usize = 1024 * 1024;

fn main() -> std::io::Result<()> {
    let cfg = Arc::new(AttachConfig::from_env());
    let store = Arc::new(SessionStore::new());

    let listener = TcpListener::bind(&cfg.bind)?;
    eprintln!(
        "dreggnet-attach: serving the portal web attach on http://{}",
        cfg.bind
    );
    eprintln!(
        "  driver:   {}",
        match cfg.live_backend.as_deref() {
            Some(b) => format!("LIVE backend named at {b} (reviewed-go; demo planner shipped)"),
            None => "demo planner (scripted brain; the genuine cap/budget/receipt braid)".into(),
        }
    );
    eprintln!(
        "  cap-gate: {}",
        match cfg.require_cap.as_deref() {
            Some(c) => format!("REQUIRED `{c}` (X-Dregg-Cap + X-Dregg-Subject; fail-closed)"),
            None => "trust the edge (set ATTACH_REQUIRE_CAP to fail closed)".to_string(),
        }
    );
    eprintln!(
        "  dev-subject: {}",
        cfg.dev_subject
            .as_deref()
            .unwrap_or("(none — needs the webauth X-Dregg-Subject header)")
    );

    for conn in listener.incoming() {
        let Ok(conn) = conn else { continue };
        let cfg = Arc::clone(&cfg);
        let store = Arc::clone(&store);
        std::thread::spawn(move || {
            if let Err(e) = serve(conn, &cfg, &store) {
                eprintln!("dreggnet-attach: connection error: {e}");
            }
        });
    }
    Ok(())
}

fn serve(
    mut stream_conn: TcpStream,
    cfg: &AttachConfig,
    store: &SessionStore,
) -> std::io::Result<()> {
    stream_conn
        .set_read_timeout(Some(Duration::from_secs(15)))
        .ok();

    let mut buf: Vec<u8> = Vec::with_capacity(4096);
    let mut tmp = [0u8; 4096];
    let header_end = loop {
        if let Some(pos) = find(&buf, b"\r\n\r\n") {
            break pos + 4;
        }
        let n = stream_conn.read(&mut tmp)?;
        if n == 0 {
            return Ok(());
        }
        buf.extend_from_slice(&tmp[..n]);
        if buf.len() > MAX_HEADER_BYTES {
            return write_resp(&mut stream_conn, 431, "text/plain", b"header too large");
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
            &mut stream_conn,
            200,
            "application/json",
            br#"{"ok":true,"service":"dreggnet-attach"}"#,
        );
    }

    // App-layer cap enforcement (fail-closed when ATTACH_REQUIRE_CAP is set).
    if let Some(required) = cfg.require_cap.as_deref() {
        if !cap_satisfied(&head_text, required, cfg.break_glass.as_deref()) {
            return write_resp(
                &mut stream_conn,
                403,
                "text/plain",
                format!(
                    "the `{required}` dregg capability is required to attach (via the webauth \
                     forward-auth). Sign in at {}/login.\n",
                    cfg.login_base
                )
                .as_bytes(),
            );
        }
    }

    // Resolve WHO is signed in — strictly from the verified forward-auth header
    // (a body/query field can never widen the scope to another subject's session).
    let header_subject = header_value(&head_text, "x-dregg-subject");
    let Some(subject) = resolve_subject(cfg, header_subject.as_deref()) else {
        return write_resp(
            &mut stream_conn,
            401,
            "text/plain",
            format!(
                "not signed in: no dregg identity on this request. Sign in at {}/login to attach.\n",
                cfg.login_base
            )
            .as_bytes(),
        );
    };

    // /api/session/<id>[/stream|/fork] routing.
    if let Some(rest) = path.strip_prefix("/api/session/") {
        // POST /api/session/<id>/fork — the attenuation superpower (cap-scoped):
        // fork one of the subject's OWN sessions into an attenuated child.
        if let Some(id) = rest.strip_suffix("/fork") {
            if method != "POST" {
                return write_resp(&mut stream_conn, 405, "text/plain", b"method not allowed");
            }
            return match store.fork_for(id, &subject) {
                Some(child) => {
                    let body = format!(
                        r#"{{"ok":true,"id":{},"parent":{},"goal":{},"budget":{},"consumed":{},"receipts":{}}}"#,
                        json_str(&child.id),
                        json_str(id),
                        json_str(child.goal()),
                        child.budget(),
                        child.consumed(),
                        child.receipts(),
                    );
                    write_resp(&mut stream_conn, 200, "application/json", body.as_bytes())
                }
                None => write_resp(&mut stream_conn, 404, "text/plain", b"no such session"),
            };
        }

        let (id, is_stream) = match rest.strip_suffix("/stream") {
            Some(id) => (id, true),
            None => (rest, false),
        };
        if method != "GET" {
            return write_resp(&mut stream_conn, 405, "text/plain", b"method not allowed");
        }
        // The cap-scoping teeth: a session not owned by the subject resolves to
        // 404 — indistinguishable from a non-existent id (no existence oracle).
        let Some(session) = store.get_for_subject(id, &subject) else {
            return write_resp(&mut stream_conn, 404, "text/plain", b"no such session");
        };
        if is_stream {
            let body = stream::transcript_stream(&session);
            return write_resp(&mut stream_conn, 200, "text/event-stream", body.as_bytes());
        }
        let body = serde_json::to_vec(&session).unwrap_or_default();
        return write_resp(&mut stream_conn, 200, "application/json", &body);
    }

    match (method, path) {
        ("GET", "/") | ("GET", "/index.html") => {
            let sessions = store.list_for(&subject);
            let html =
                render::render_page(&subject, &cfg.login_base, cfg.default_budget, &sessions);
            write_resp(
                &mut stream_conn,
                200,
                "text/html; charset=utf-8",
                html.as_bytes(),
            )
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
            write_resp(&mut stream_conn, 200, "application/json", body.as_bytes())
        }
        ("GET", "/api/sessions") => {
            let sessions = store.list_for(&subject);
            let body = serde_json::to_vec(&sessions).unwrap_or_default();
            write_resp(&mut stream_conn, 200, "application/json", &body)
        }
        ("POST", "/api/session") => {
            let body = read_body(&mut stream_conn, &buf, header_end, &head_text)?;
            let resp = handle_create(&body, &subject, store);
            write_resp(&mut stream_conn, 200, "application/json", resp.as_bytes())
        }
        ("POST", "/api/verify") => {
            let body = read_body(&mut stream_conn, &buf, header_end, &head_text)?;
            let resp = handle_verify(&body, &subject, store);
            write_resp(&mut stream_conn, 200, "application/json", resp.as_bytes())
        }
        _ => write_resp(&mut stream_conn, 404, "text/plain", b"not found"),
    }
}

/// Resolve the signed-in subject. Production (`require_cap` set): ONLY the
/// verified `X-Dregg-Subject` header. Dev (`require_cap` unset): the header if
/// present, else the configured `dev_subject` so the page is drivable locally.
fn resolve_subject(cfg: &AttachConfig, header_subject: Option<&str>) -> Option<String> {
    if let Some(s) = header_subject.map(str::trim).filter(|s| !s.is_empty()) {
        return Some(s.to_string());
    }
    if cfg.require_cap.is_some() {
        return None; // production fail-closed: an identity is mandatory.
    }
    cfg.dev_subject.clone()
}

/// Drive a goal into a NEW session owned by the *verified* subject.
fn handle_create(body: &str, subject: &str, store: &SessionStore) -> String {
    let Ok(req) = serde_json::from_str::<GoalRequest>(body) else {
        return r#"{"ok":false,"detail":"request body is not a valid goal request"}"#.to_string();
    };
    let clean = req.sanitized();
    if clean.goal.is_empty() {
        return r#"{"ok":false,"detail":"a goal is required"}"#.to_string();
    }
    // The owner is the verified subject — NEVER a field in the body. The create is
    // quota-bounded: a subject at its session ceiling (or the server at its global
    // cap) is refused, closing the resource-exhaustion vector.
    match store.create(&clean, subject) {
        Ok(session) => format!(
            r#"{{"ok":true,"id":{},"goal":{},"budget":{},"consumed":{},"receipts":{}}}"#,
            json_str(&session.id),
            json_str(session.goal()),
            session.budget(),
            session.consumed(),
            session.receipts(),
        ),
        Err(e) => format!(r#"{{"ok":false,"detail":{}}}"#, json_str(&e.to_string())),
    }
}

/// Handle a POST /api/verify body: a scoped "verify my session" (`session_id`) or
/// the open "paste any run record" path (`run`) — a self-contained proof.
fn handle_verify(body: &str, subject: &str, store: &SessionStore) -> String {
    let Ok(req) = serde_json::from_str::<serde_json::Value>(body) else {
        return r#"{"ok":false,"detail":"request body is not valid JSON"}"#.to_string();
    };

    // (a) the scoped "verify my session" button. With `"tamper":true` it runs the
    //     tamper SELF-DEMO instead — flip one line of YOUR OWN chain on a private
    //     clone and show it shatters (✗). Verify-don't-trust, made visceral.
    if let Some(id) = req.get("session_id").and_then(|v| v.as_str()) {
        let tamper = req.get("tamper").and_then(|v| v.as_bool()).unwrap_or(false);
        return match store.get_for_subject(id, subject) {
            Some(session) => {
                let r = if tamper {
                    verify::tamper_demo(&session)
                } else {
                    verify::verify_session(&session, subject)
                };
                serde_json::to_string(&r).unwrap_or_default()
            }
            None => format!(
                r#"{{"ok":false,"detail":{}}}"#,
                json_str(&format!(
                    "no session `{id}` owned by you — you can only verify your own sessions"
                ))
            ),
        };
    }

    // (b) the open "paste any run record" path — a self-contained proof verifies
    //     for anyone (verify-don't-trust); no scoping needed.
    if let Some(run_val) = req.get("run") {
        return match serde_json::from_value::<dreggnet_exec::live::LiveRun>(run_val.clone()) {
            Ok(run) => {
                let r = verify::verify_live_run(&run, None);
                serde_json::to_string(&r).unwrap_or_default()
            }
            Err(e) => format!(
                r#"{{"ok":false,"detail":{}}}"#,
                json_str(&format!("the pasted run record did not parse: {e}"))
            ),
        };
    }

    r#"{"ok":false,"detail":"send {session_id} to verify your session, or {run} to paste a record"}"#
        .to_string()
}

// ── HTTP plumbing (mirrors dreggnet-console) ──────────────────────────────────

fn read_body(
    stream_conn: &mut TcpStream,
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
        let mut tmp = [0u8; 4096];
        let n = stream_conn.read(&mut tmp)?;
        if n == 0 {
            break;
        }
        body.extend_from_slice(&tmp[..n]);
    }
    body.truncate(len);
    Ok(String::from_utf8_lossy(&body).into_owned())
}

fn cap_satisfied(head_text: &str, required: &str, break_glass: Option<&str>) -> bool {
    // Break-glass: an operator escape hatch a TENANT CANNOT FORGE. It admits ONLY
    // when the server holds a `break_glass` secret AND the request presents that
    // exact secret in `X-Dregg-Break-Glass`. With no server secret configured,
    // break-glass is disabled — there is NO client header that bypasses the gate.
    // (Previously `X-Dregg-Auth: break-glass` self-admitted; that value is a plain
    // header any client could set, so it was a cap-bypass and has been removed.)
    if let Some(secret) = break_glass.filter(|s| !s.is_empty()) {
        if header_value(head_text, "x-dregg-break-glass").as_deref() == Some(secret) {
            return true;
        }
    }
    let has_subject = header_value(head_text, "x-dregg-subject")
        .map(|s| !s.trim().is_empty())
        .unwrap_or(false);
    let cap_ok = header_value(head_text, "x-dregg-cap")
        .map(|c| c.split([' ', ',']).any(|t| t.trim() == required))
        .unwrap_or(false);
    has_subject && cap_ok
}

fn header_value(head_text: &str, name_lower: &str) -> Option<String> {
    for line in head_text.lines().skip(1) {
        if let Some((k, v)) = line.split_once(':') {
            if k.trim().eq_ignore_ascii_case(name_lower) {
                return Some(v.trim().to_string());
            }
        }
    }
    None
}

fn json_str(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_string())
}

fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

fn write_resp(
    stream_conn: &mut TcpStream,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> std::io::Result<()> {
    let reason = match status {
        200 => "OK",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        405 => "Method Not Allowed",
        431 => "Request Header Fields Too Large",
        _ => "OK",
    };
    let mut head = format!(
        "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\n\
         Cache-Control: no-store\r\nConnection: close\r\n\r\n",
        body.len()
    )
    .into_bytes();
    head.extend_from_slice(body);
    stream_conn.write_all(&head)?;
    stream_conn.flush()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn head(lines: &[&str]) -> String {
        let mut s = String::from("GET / HTTP/1.1\r\n");
        for l in lines {
            s.push_str(l);
            s.push_str("\r\n");
        }
        s.push_str("\r\n");
        s
    }

    // ── TOOTH: the forgeable `X-Dregg-Auth: break-glass` self-admit is gone ────
    // It used to admit ANY client past the cap gate. Now break-glass requires the
    // server's `ATTACH_BREAK_GLASS` secret in `X-Dregg-Break-Glass`.
    #[test]
    fn break_glass_is_not_a_forgeable_header() {
        // A tenant tries the old bypass + spoofs a subject — must NOT satisfy.
        let forged = head(&[
            "X-Dregg-Auth: break-glass",
            "X-Dregg-Subject: dregg:victim0000victim",
        ]);
        assert!(
            !cap_satisfied(&forged, "attach-user", Some("s3cr3t")),
            "the literal break-glass header must NOT bypass the cap gate"
        );
        // With NO server secret configured, break-glass is disabled entirely.
        assert!(
            !cap_satisfied(
                &head(&["X-Dregg-Break-Glass: anything", "X-Dregg-Subject: dregg:x"]),
                "attach-user",
                None
            ),
            "break-glass disabled when no server secret is set"
        );
        // A wrong secret does not admit.
        assert!(!cap_satisfied(
            &head(&["X-Dregg-Break-Glass: wrong", "X-Dregg-Subject: dregg:x"]),
            "attach-user",
            Some("s3cr3t")
        ));
        // The CORRECT server secret admits (the genuine operator escape hatch).
        assert!(cap_satisfied(
            &head(&["X-Dregg-Break-Glass: s3cr3t"]),
            "attach-user",
            Some("s3cr3t")
        ));
    }

    // ── the normal path still works: a verified subject + the required cap ─────
    #[test]
    fn a_verified_subject_with_the_cap_satisfies() {
        let ok = head(&[
            "X-Dregg-Subject: dregg:aaaa0000aaaa0000",
            "X-Dregg-Cap: attach-user, console-read",
        ]);
        assert!(cap_satisfied(&ok, "attach-user", None));
        // Missing the cap → refused even with a subject.
        let no_cap = head(&["X-Dregg-Subject: dregg:aaaa0000aaaa0000"]);
        assert!(!cap_satisfied(&no_cap, "attach-user", None));
        // The cap without a subject → refused (both halves required).
        let no_subj = head(&["X-Dregg-Cap: attach-user"]);
        assert!(!cap_satisfied(&no_subj, "attach-user", None));
    }
}

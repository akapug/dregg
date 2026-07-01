//! `dreggnet-ops` — the serving binary for the ops/admin dashboard.
//!
//! A pure-std thread-per-connection HTTP/1.1 server (the same shape as the
//! gateway's serving binary) that routes to the aggregation + render surfaces:
//!
//! | Method + path            | Serves                                            |
//! |--------------------------|---------------------------------------------------|
//! | `GET /`                  | the self-contained HTML dashboard                 |
//! | `GET /api/snapshot`      | the full aggregated [`CloudSnapshot`] JSON        |
//! | `GET /api/health`        | the whole-cloud health rollup JSON                |
//! | `GET /api/alerts`        | the active page/warn/info alerts JSON             |
//! | `GET /api/history?...`   | the browsable, filterable historical-log viewer   |
//! | `GET /api/config`        | the dashboard's non-secret config (Grafana URL)   |
//! | `GET /api/whoami`        | the authenticated dregg identity (subject/cap)    |
//! | `GET /api/containers`    | the running containers (Docker Engine API)        |
//! | `GET /api/logs?...`      | a service's tailed logs (text)                     |
//! | `GET /healthz`           | ops liveness (always open, for probes)            |
//!
//! Auth: the dashboard is gated by a SEPARATE admin password at the Caddy edge. An
//! OPTIONAL [`OpsConfig::admin_token`] adds an app-layer Bearer/`?token=` check
//! underneath (defence in depth); unset (default) leaves the app open so the
//! normal browser-behind-Caddy flow works.
//!
//!   cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-ops

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::Duration;

use dreggnet_ops::aggregate::CloudSnapshot;
use dreggnet_ops::{OpsConfig, docker, render};

const MAX_HEADER_BYTES: usize = 64 * 1024;

fn main() -> std::io::Result<()> {
    let mut cfg = OpsConfig::from_env();
    // CLI overrides for --bind/--port (compose passes them; env is the main path).
    let args: Vec<String> = std::env::args().collect();
    if let Some(bind) = parse_bind(&args) {
        cfg.bind = bind;
    }
    let cfg = Arc::new(cfg);

    // One shared runtime to drive the (async) Postgres reads from the synchronous
    // connection loop.
    let runtime = Arc::new(
        tokio::runtime::Builder::new_multi_thread()
            .worker_threads(2)
            .enable_all()
            .build()?,
    );

    // The background alerter: re-evaluates the whole-cloud health on an interval and
    // logs (always) + webhooks (if configured) any page/warn alert, de-duplicated so
    // a steady-state condition is not spammed. The on-demand /api/alerts endpoint and
    // the dashboard banner are the pull side; this thread is the push side.
    spawn_alerter(Arc::clone(&cfg), Arc::clone(&runtime));

    let listener = TcpListener::bind(&cfg.bind)?;
    eprintln!(
        "dreggnet-ops: serving the ops dashboard on http://{}",
        cfg.bind
    );
    eprintln!("  node:     {}", cfg.node_url);
    eprintln!("  gateway:  {}", cfg.gateway_url);
    eprintln!(
        "  bot:      {}",
        cfg.bot_url.as_deref().unwrap_or("(not configured)")
    );
    eprintln!(
        "  postgres: {}",
        if cfg.database_url.is_some() {
            "configured"
        } else {
            "(not configured)"
        }
    );
    eprintln!(
        "  docker:   {}",
        cfg.docker_socket.as_deref().unwrap_or("(no log socket)")
    );
    eprintln!(
        "  app-auth: {}",
        if cfg.admin_token.is_some() {
            "token required (defence-in-depth under Caddy)"
        } else {
            "open at app layer (Caddy admin-password is the gate)"
        }
    );
    eprintln!(
        "  grafana:  {}",
        cfg.grafana_url
            .as_deref()
            .unwrap_or("(not linked — set OPS_GRAFANA_URL)")
    );
    eprintln!(
        "  cap-gate: {}",
        match cfg.require_cap.as_deref() {
            Some(cap) => format!("REQUIRED `{cap}` (X-Dregg-Cap; internalizes the webauth gate)"),
            None => "trust the edge (set OPS_REQUIRE_CAP=ops-admin to fail closed)".to_string(),
        }
    );

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                let cfg = Arc::clone(&cfg);
                let runtime = Arc::clone(&runtime);
                std::thread::spawn(move || {
                    if let Err(e) = serve(stream, &cfg, &runtime) {
                        eprintln!("dreggnet-ops: connection error: {e}");
                    }
                });
            }
            Err(e) => eprintln!("dreggnet-ops: accept error: {e}"),
        }
    }
    Ok(())
}

/// Spawn the background alerter: on `cfg.alert_interval`, rebuild the snapshot and
/// emit each page/warn alert to the log (always) + the webhook (if `OPS_ALERT_WEBHOOK`
/// is set). De-duplicated by alert key so a steady-state condition fires once and
/// re-fires at most every 10 minutes; a resolved condition clears so a recurrence
/// re-alerts. Info-level alerts are not pushed (they live as dashboard tiles).
fn spawn_alerter(cfg: Arc<OpsConfig>, runtime: Arc<tokio::runtime::Runtime>) {
    use std::collections::HashMap;
    use std::time::Instant;
    const REFIRE_AFTER: Duration = Duration::from_secs(600);
    std::thread::spawn(move || {
        let mut last_fired: HashMap<String, Instant> = HashMap::new();
        loop {
            let snap = CloudSnapshot::build(&cfg, &runtime);
            for a in &snap.health.alerts {
                if a.severity == "info" {
                    continue;
                }
                let refire = last_fired
                    .get(&a.key)
                    .map(|t| t.elapsed() >= REFIRE_AFTER)
                    .unwrap_or(true);
                if !refire {
                    continue;
                }
                last_fired.insert(a.key.clone(), Instant::now());
                eprintln!(
                    "dreggnet-ops ALERT [{}] {}: {}",
                    a.severity, a.key, a.message
                );
                if let Some(hook) = cfg.alert_webhook.as_deref() {
                    // Slack uses `text`, Discord uses `content`; send both so a
                    // single plain-http sink shape works for either.
                    let text = format!("[DreggNet {}] {}", a.severity.to_uppercase(), a.message);
                    let body = serde_json::json!({ "text": text, "content": text }).to_string();
                    if let Err(e) = dreggnet_ops::client::http_post(
                        hook,
                        body.as_bytes(),
                        "application/json",
                        cfg.timeout,
                    ) {
                        eprintln!("dreggnet-ops: alert webhook POST failed: {e}");
                    }
                }
            }
            // Drop keys whose condition cleared so a recurrence re-alerts promptly.
            let active: std::collections::HashSet<&str> =
                snap.health.alerts.iter().map(|a| a.key.as_str()).collect();
            last_fired.retain(|k, _| active.contains(k.as_str()));
            std::thread::sleep(cfg.alert_interval);
        }
    });
}

/// Parse `--bind host` / `--port N` into a bind string, if either is present.
fn parse_bind(args: &[String]) -> Option<String> {
    let mut host: Option<String> = None;
    let mut port: Option<u16> = None;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--bind" | "-b" => {
                host = args.get(i + 1).cloned();
                i += 2;
            }
            "--port" | "-p" => {
                port = args.get(i + 1).and_then(|s| s.parse().ok());
                i += 2;
            }
            _ => i += 1,
        }
    }
    if host.is_none() && port.is_none() {
        return None;
    }
    Some(format!(
        "{}:{}",
        host.unwrap_or_else(|| "0.0.0.0".into()),
        port.unwrap_or(8090)
    ))
}

/// Serve one connection: read the request line + headers, route, write, close.
fn serve(
    mut stream: TcpStream,
    cfg: &OpsConfig,
    runtime: &tokio::runtime::Runtime,
) -> std::io::Result<()> {
    stream.set_read_timeout(Some(Duration::from_secs(15))).ok();

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

    let head = &buf[..header_end];
    let head_text = String::from_utf8_lossy(head);
    let request_line = head_text.lines().next().unwrap_or("");
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("");
    let target = parts.next().unwrap_or("/");
    let (path, query) = match target.split_once('?') {
        Some((p, q)) => (p, q),
        None => (target, ""),
    };

    // Liveness probe is always open (for compose/Caddy health checks).
    if path == "/healthz" {
        return write_resp(
            &mut stream,
            200,
            "application/json",
            br#"{"ok":true,"service":"dreggnet-ops"}"#,
        );
    }

    // App-layer cap enforcement (defence-in-depth; internalizes the edge gate).
    // When OPS_REQUIRE_CAP is set, every non-liveness request must arrive carrying
    // the `X-Dregg-Cap` the `dreggnet-webauth` forward-auth verified (the cap was
    // already cryptographically checked there; here we require its PRESENCE so the
    // dashboard fails closed if the Caddy forward_auth is ever removed). A
    // break-glass admit (`X-Dregg-Auth: break-glass override`) is always honored so
    // the operator is never locked out.
    if let Some(required) = cfg.require_cap.as_deref() {
        if !cap_satisfied(&head_text, required) {
            return write_resp(
                &mut stream,
                403,
                "text/plain",
                format!(
                    "ops-admin capability required: this surface needs the `{required}` dregg cap \
                     (via the webauth forward-auth). Sign in at {}/login.\n",
                    cfg.login_base
                )
                .as_bytes(),
            );
        }
    }

    // App-layer defence-in-depth (optional; Caddy is the primary gate).
    if let Some(expected) = cfg.admin_token.as_deref() {
        if !authorized(&head_text, query, expected) {
            return write_resp(
                &mut stream,
                401,
                "text/plain",
                b"admin authentication required (Bearer token or ?token=)",
            );
        }
    }

    if method != "GET" {
        return write_resp(&mut stream, 405, "text/plain", b"method not allowed");
    }

    match path {
        "/" | "/index.html" => write_resp(
            &mut stream,
            200,
            "text/html; charset=utf-8",
            render::dashboard_html().as_bytes(),
        ),
        "/api/snapshot" => {
            let snap = CloudSnapshot::build(cfg, runtime);
            let body = serde_json::to_vec(&snap).unwrap_or_default();
            write_resp(&mut stream, 200, "application/json", &body)
        }
        "/api/health" => {
            let snap = CloudSnapshot::build(cfg, runtime);
            let body = serde_json::to_vec(&snap.health).unwrap_or_default();
            write_resp(&mut stream, 200, "application/json", &body)
        }
        "/api/alerts" => {
            // The active alerts only — the lightweight pull path for an external
            // poller (cron + curl) that forwards to an https sink the in-process
            // http-only webhook cannot reach.
            let snap = CloudSnapshot::build(cfg, runtime);
            let body = serde_json::to_vec(&snap.health.alerts).unwrap_or_default();
            write_resp(&mut stream, 200, "application/json", &body)
        }
        "/api/history" => {
            // The browsable, filterable historical-log viewer. Builds the snapshot,
            // normalizes every historical surface into one stream, then applies the
            // query filter (category / who / what / q / since / until / limit).
            let snap = CloudSnapshot::build(cfg, runtime);
            let now = now_epoch();
            let view = dreggnet_ops::history::build_view(&snap, query, now);
            let body = serde_json::to_vec(&view).unwrap_or_default();
            write_resp(&mut stream, 200, "application/json", &body)
        }
        "/api/config" => {
            // The small slice of config the dashboard JS needs (Grafana base URL
            // for cross-links + the login base for the sign-out control). No secrets.
            let body = format!(
                r#"{{"grafana_url":{},"login_base":{},"require_cap":{}}}"#,
                json_str(cfg.grafana_url.as_deref().unwrap_or("")),
                json_str(&cfg.login_base),
                json_str(cfg.require_cap.as_deref().unwrap_or(""))
            );
            write_resp(&mut stream, 200, "application/json", body.as_bytes())
        }
        "/api/whoami" => {
            // The authenticated identity, as the `dreggnet-webauth` forward-auth
            // resolved it and Caddy copied onto this request (X-Dregg-Subject /
            // X-Dregg-Cap / X-Dregg-Auth). Lets the dashboard show "signed in as …".
            let (subject, cap, how) = request_identity(&head_text);
            let body = format!(
                r#"{{"subject":{},"cap":{},"how":{}}}"#,
                json_str(&subject.unwrap_or_default()),
                json_str(&cap.unwrap_or_default()),
                json_str(&how.unwrap_or_default())
            );
            write_resp(&mut stream, 200, "application/json", body.as_bytes())
        }
        "/api/containers" => match &cfg.docker_socket {
            Some(sock) => match docker::list_containers(sock, cfg.timeout) {
                Ok(cs) => {
                    let body = serde_json::to_vec(&cs).unwrap_or_default();
                    write_resp(&mut stream, 200, "application/json", &body)
                }
                Err(e) => write_resp(
                    &mut stream,
                    200,
                    "application/json",
                    format!(r#"{{"error":{}}}"#, json_str(&e)).as_bytes(),
                ),
            },
            None => write_resp(&mut stream, 200, "application/json", b"[]"),
        },
        "/api/logs" => {
            let container = query_param(query, "container").unwrap_or_default();
            let tail = query_param(query, "tail")
                .and_then(|s| s.parse::<usize>().ok())
                .unwrap_or(200)
                .min(2000);
            match &cfg.docker_socket {
                Some(sock) if !container.is_empty() => {
                    // Accept a name/service substring too, not just an id.
                    let id = docker::list_containers(sock, cfg.timeout)
                        .ok()
                        .and_then(|cs| docker::resolve_container(&cs, &container))
                        .unwrap_or(container);
                    match docker::tail_logs(sock, &id, tail, cfg.timeout) {
                        Ok(t) => write_resp(&mut stream, 200, "text/plain; charset=utf-8", t.as_bytes()),
                        Err(e) => write_resp(&mut stream, 502, "text/plain", e.as_bytes()),
                    }
                }
                Some(_) => write_resp(&mut stream, 400, "text/plain", b"missing ?container="),
                None => write_resp(
                    &mut stream,
                    503,
                    "text/plain",
                    b"logs unavailable: no Docker socket mounted (set OPS_DOCKER_SOCKET / mount /var/run/docker.sock)",
                ),
            }
        }
        _ => write_resp(&mut stream, 404, "text/plain", b"not found"),
    }
}

/// Whether the request carries the expected token via `Authorization: Bearer` or
/// a `?token=` query param. Constant-time-ish (length + byte compare).
fn authorized(head_text: &str, query: &str, expected: &str) -> bool {
    let bearer = head_text.lines().find_map(|l| {
        let (k, v) = l.split_once(':')?;
        if k.trim().eq_ignore_ascii_case("authorization") {
            v.trim()
                .strip_prefix("Bearer ")
                .map(|s| s.trim().to_string())
        } else {
            None
        }
    });
    let presented = bearer.or_else(|| query_param(query, "token"));
    match presented {
        Some(t) => ct_eq(t.as_bytes(), expected.as_bytes()),
        None => false,
    }
}

/// Constant-time byte comparison.
fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        diff |= x ^ y;
    }
    diff == 0
}

/// Extract a query parameter (minimal, `+`/`%20` not decoded — ids/tokens are
/// plain). Returns the first match.
fn query_param(query: &str, key: &str) -> Option<String> {
    query.split('&').find_map(|kv| {
        let (k, v) = kv.split_once('=')?;
        if k == key {
            Some(percent_decode(v))
        } else {
            None
        }
    })
}

/// Minimal percent-decoding for query values (enough for container ids/names).
fn percent_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' && i + 2 < bytes.len() {
            if let Ok(b) = u8::from_str_radix(&s[i + 1..i + 3], 16) {
                out.push(b);
                i += 3;
                continue;
            }
        }
        out.push(if bytes[i] == b'+' { b' ' } else { bytes[i] });
        i += 1;
    }
    String::from_utf8_lossy(&out).to_string()
}

/// JSON-encode a string (for embedding an error in a hand-built body).
fn json_str(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_else(|_| "\"\"".to_string())
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

/// The authenticated identity the webauth forward-auth resolved (and Caddy copied
/// onto this request): `(subject, cap, how)`.
fn request_identity(head_text: &str) -> (Option<String>, Option<String>, Option<String>) {
    (
        header_value(head_text, "x-dregg-subject"),
        header_value(head_text, "x-dregg-cap"),
        header_value(head_text, "x-dregg-auth"),
    )
}

/// Whether the request satisfies the `required` ops cap. The cap was already
/// verified by `dreggnet-webauth`; here we require its presence on the request
/// (`X-Dregg-Cap`) so the dashboard fails closed if the edge gate is removed. A
/// break-glass admit (`X-Dregg-Auth` mentioning break-glass) is always honored.
fn cap_satisfied(head_text: &str, required: &str) -> bool {
    if let Some(how) = header_value(head_text, "x-dregg-auth") {
        if how.to_ascii_lowercase().contains("break-glass") {
            return true;
        }
    }
    match header_value(head_text, "x-dregg-cap") {
        // The header can carry a comma/space-separated set (an AnyOf token); the
        // required cap must be one of them.
        Some(caps) => caps
            .split(|c: char| c == ',' || c.is_whitespace())
            .any(|c| c.eq_ignore_ascii_case(required)),
        None => false,
    }
}

/// The current time as Unix epoch seconds (for relative history-window filters).
fn now_epoch() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() as i64)
        .unwrap_or(0)
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
        400 => "Bad Request",
        401 => "Unauthorized",
        404 => "Not Found",
        405 => "Method Not Allowed",
        431 => "Request Header Fields Too Large",
        500 => "Internal Server Error",
        502 => "Bad Gateway",
        403 => "Forbidden",
        503 => "Service Unavailable",
        _ => "OK",
    };
    let header = format!(
        "HTTP/1.1 {status} {reason}\r\n\
         Content-Type: {content_type}\r\n\
         Content-Length: {}\r\n\
         Cache-Control: no-store\r\n\
         Connection: close\r\n\r\n",
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

    #[test]
    fn bind_override_parsing() {
        assert_eq!(parse_bind(&["ops".into()]), None);
        assert_eq!(
            parse_bind(&["ops".into(), "--port".into(), "9000".into()]),
            Some("0.0.0.0:9000".into())
        );
        assert_eq!(
            parse_bind(&[
                "ops".into(),
                "--bind".into(),
                "127.0.0.1".into(),
                "-p".into(),
                "8091".into()
            ]),
            Some("127.0.0.1:8091".into())
        );
    }

    #[test]
    fn query_params_and_token_auth() {
        assert_eq!(
            query_param("container=abc&tail=50", "tail"),
            Some("50".into())
        );
        assert_eq!(query_param("token=sekret", "token"), Some("sekret".into()));
        let head = "GET /x HTTP/1.1\r\nAuthorization: Bearer sekret\r\n\r\n";
        assert!(authorized(head, "", "sekret"));
        assert!(!authorized("GET /x HTTP/1.1\r\n\r\n", "", "sekret"));
        assert!(authorized(
            "GET /x HTTP/1.1\r\n\r\n",
            "token=sekret",
            "sekret"
        ));
    }

    #[test]
    fn percent_decode_basic() {
        assert_eq!(percent_decode("a%2Fb"), "a/b");
        assert_eq!(percent_decode("plain"), "plain");
    }

    #[test]
    fn cap_gate_requires_the_verified_cap_header() {
        // The cap webauth verified is present → admitted.
        let ok = "GET / HTTP/1.1\r\nX-Dregg-Cap: ops-admin\r\nX-Dregg-Subject: dregg:alice\r\n\r\n";
        assert!(cap_satisfied(ok, "ops-admin"));
        // A multi-cap (AnyOf) header containing the required cap → admitted.
        let multi = "GET / HTTP/1.1\r\nX-Dregg-Cap: grafana-view, ops-admin\r\n\r\n";
        assert!(cap_satisfied(multi, "ops-admin"));
        // No cap header → refused (this is the fail-closed case).
        assert!(!cap_satisfied("GET / HTTP/1.1\r\n\r\n", "ops-admin"));
        // The wrong cap → refused (a grafana-view cap can't reach ops-admin).
        let wrong = "GET / HTTP/1.1\r\nX-Dregg-Cap: grafana-view\r\n\r\n";
        assert!(!cap_satisfied(wrong, "ops-admin"));
        // Break-glass is always honored so the operator is never locked out.
        let bg = "GET / HTTP/1.1\r\nX-Dregg-Auth: break-glass override\r\n\r\n";
        assert!(cap_satisfied(bg, "ops-admin"));
    }

    #[test]
    fn identity_parsed_from_forwarded_headers() {
        let head = "GET / HTTP/1.1\r\nX-Dregg-Subject: dregg:alice\r\nX-Dregg-Cap: ops-admin\r\nX-Dregg-Auth: dregg credential\r\n\r\n";
        let (subject, cap, how) = request_identity(head);
        assert_eq!(subject.as_deref(), Some("dregg:alice"));
        assert_eq!(cap.as_deref(), Some("ops-admin"));
        assert_eq!(how.as_deref(), Some("dregg credential"));
    }
}

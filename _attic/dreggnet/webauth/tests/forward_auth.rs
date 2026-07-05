//! End-to-end: spawn the real `dreggnet-webauth` server and drive the
//! `forward_auth` decision over HTTP with raw TCP requests — the same shape
//! Caddy's `forward_auth` makes. Proves: a valid cap → 2xx, a missing/invalid
//! cap → deny, attenuation holds (a grafana-view cap cannot reach ops-admin),
//! the break-glass override admits, and the login flow sets the session cookie.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::Duration;

use dreggnet_webauth::config::WebAuthConfig;
use dreggnet_webauth::cred::RootKey;
use dreggnet_webauth::grant::{attenuate_caps, mint_caps};

/// Spawn the server on an ephemeral port; return its `host:port`.
fn spawn(cfg: WebAuthConfig) -> String {
    // Grab a free port, then hand the address to the server.
    let probe = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = probe.local_addr().unwrap();
    drop(probe);
    let mut cfg = cfg;
    cfg.bind = addr.to_string();
    std::thread::spawn(move || {
        let _ = dreggnet_webauth::server::serve(cfg);
    });
    // Wait for the listener to come up.
    for _ in 0..100 {
        if TcpStream::connect(addr).is_ok() {
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    addr.to_string()
}

/// Make a raw HTTP/1.1 request; return (status_line, full_response).
fn request(addr: &str, raw: &str) -> (String, String) {
    let mut stream = TcpStream::connect(addr).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    stream.write_all(raw.as_bytes()).unwrap();
    let mut buf = String::new();
    let _ = stream.read_to_string(&mut buf);
    let status = buf.lines().next().unwrap_or("").to_string();
    (status, buf)
}

fn status_code(status_line: &str) -> u16 {
    status_line
        .split_whitespace()
        .nth(1)
        .and_then(|c| c.parse().ok())
        .unwrap_or(0)
}

fn base_cfg(root: &RootKey) -> WebAuthConfig {
    let mut host_caps = std::collections::BTreeMap::new();
    host_caps.insert("ops.example".to_string(), "ops-admin".to_string());
    host_caps.insert("grafana.example".to_string(), "grafana-view".to_string());
    WebAuthConfig {
        root_pubkey_hex: Some(root.public().to_hex()),
        break_glass: Some("break-glass-token".to_string()),
        host_caps,
        ..WebAuthConfig::default()
    }
}

#[test]
fn valid_cap_authorizes_invalid_refused() {
    let root = RootKey::from_seed([42u8; 32]);
    let addr = spawn(base_cfg(&root));
    let token = mint_caps(&root, ["ops-admin"], None).encode();

    // Valid cap via cookie + explicit ?cap= → 2xx.
    let (status, body) = request(
        &addr,
        &format!(
            "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nCookie: dregg_session={token}\r\nAccept: */*\r\nConnection: close\r\n\r\n"
        ),
    );
    assert_eq!(
        status_code(&status),
        200,
        "valid cap must authorize: {body}"
    );
    assert!(
        body.contains("X-Dregg-Subject"),
        "identity header echoed: {body}"
    );

    // No credential, API client (no text/html) → 401.
    let (status, _) = request(
        &addr,
        "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nAccept: */*\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(
        status_code(&status),
        401,
        "missing credential must be refused"
    );

    // Garbage credential → 401.
    let (status, _) = request(
        &addr,
        "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nX-Dregg-Credential: dga1_garbage\r\nAccept: */*\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(status_code(&status), 401);
}

#[test]
fn cap_resolved_from_host_map() {
    let root = RootKey::from_seed([43u8; 32]);
    let addr = spawn(base_cfg(&root));
    let token = mint_caps(&root, ["grafana-view"], None).encode();
    // No ?cap= — the cap is resolved from X-Forwarded-Host (the forward_auth shape).
    let (status, body) = request(
        &addr,
        &format!(
            "GET /auth HTTP/1.1\r\nHost: internal\r\nX-Forwarded-Host: grafana.example\r\nX-Dregg-Credential: {token}\r\nAccept: */*\r\nConnection: close\r\n\r\n"
        ),
    );
    assert_eq!(
        status_code(&status),
        200,
        "host-mapped cap must authorize: {body}"
    );
}

#[test]
fn attenuation_holds_over_http() {
    let root = RootKey::from_seed([44u8; 32]);
    let addr = spawn(base_cfg(&root));
    // Wide cap narrowed to grafana-view only.
    let wide = mint_caps(&root, ["ops-admin", "grafana-view"], None);
    let narrowed = attenuate_caps(wide, ["grafana-view"], None).encode();

    // grafana-view surface → 2xx.
    let (status, _) = request(
        &addr,
        &format!(
            "GET /auth?cap=grafana-view HTTP/1.1\r\nHost: grafana.example\r\nX-Dregg-Credential: {narrowed}\r\nAccept: */*\r\nConnection: close\r\n\r\n"
        ),
    );
    assert_eq!(
        status_code(&status),
        200,
        "grafana-view must admit the narrowed cap"
    );

    // ops-admin surface with the SAME narrowed cap → 403 (no amplification).
    // The narrowed credential is a GENUINE, live session (chain verifies, not
    // revoked, not expired) that simply lacks `ops-admin` — authenticated but not
    // authorized, so the edge answers 403 (re-login cannot widen the cap), NOT the
    // 401 an unauthenticated presenter gets.
    let (status, body) = request(
        &addr,
        &format!(
            "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nX-Dregg-Credential: {narrowed}\r\nAccept: */*\r\nConnection: close\r\n\r\n"
        ),
    );
    assert_eq!(
        status_code(&status),
        403,
        "grafana-only cap must NOT reach ops-admin (403 forbidden): {body}"
    );
}

#[test]
fn break_glass_admits() {
    let root = RootKey::from_seed([45u8; 32]);
    let addr = spawn(base_cfg(&root));
    let (status, _) = request(
        &addr,
        "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nX-Dregg-Break-Glass: break-glass-token\r\nAccept: */*\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(status_code(&status), 200, "break-glass override must admit");

    // Wrong break-glass token → 401.
    let (status, _) = request(
        &addr,
        "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nX-Dregg-Break-Glass: wrong\r\nAccept: */*\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(status_code(&status), 401);
}

#[test]
fn browser_deny_redirects_to_login() {
    let root = RootKey::from_seed([46u8; 32]);
    let addr = spawn(base_cfg(&root));
    // A browser (Accept: text/html) with no credential → 302 to /login.
    let (status, body) = request(
        &addr,
        "GET /auth HTTP/1.1\r\nHost: ops.example\r\nX-Forwarded-Host: ops.example\r\nX-Forwarded-Uri: /dashboard\r\nAccept: text/html\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(
        status_code(&status),
        302,
        "browser deny should redirect to login"
    );
    assert!(
        body.contains("Location: /login"),
        "redirects to the login page: {body}"
    );
}

#[test]
fn login_flow_sets_session_cookie() {
    let root = RootKey::from_seed([47u8; 32]);
    let addr = spawn(base_cfg(&root));
    let token = mint_caps(&root, ["ops-admin"], None).encode();

    // GET /login serves the form.
    let (status, body) = request(
        &addr,
        "GET /login HTTP/1.1\r\nHost: ops.example\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(status_code(&status), 200);
    assert!(body.contains("Present capability"), "login form served");

    // POST /login with the credential → 302 + Set-Cookie.
    let form = format!("credential={token}&rd=%2Fdashboard");
    let (status, body) = request(
        &addr,
        &format!(
            "POST /login HTTP/1.1\r\nHost: ops.example\r\nContent-Type: application/x-www-form-urlencoded\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{form}",
            form.len()
        ),
    );
    assert_eq!(status_code(&status), 302, "login submit redirects: {body}");
    assert!(
        body.contains("Set-Cookie: dregg_session="),
        "sets the session cookie: {body}"
    );
    assert!(
        body.contains("Location: /dashboard"),
        "redirects to rd: {body}"
    );
}

#[test]
fn healthz_open() {
    let root = RootKey::from_seed([48u8; 32]);
    let addr = spawn(base_cfg(&root));
    let (status, _) = request(
        &addr,
        "GET /healthz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(status_code(&status), 200);
}

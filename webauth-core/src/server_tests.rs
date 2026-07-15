// Included inside `mod tests` in server.rs (so `super::` is the server module).
use super::*;
use crate::config::WebAuthConfig;
use crate::credext::{CredentialExt, hex};
use crate::grant::{mint_caps, mint_session_for};
use dregg_agent::cred::RootKey;
use std::io::{Read as _, Write as _};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Harness.
// ---------------------------------------------------------------------------

fn cfg_for(root: &RootKey) -> WebAuthConfig {
    let mut c = WebAuthConfig {
        root_pubkey_hex: Some(root.public().to_hex()),
        break_glass: Some("rescue-me".to_string()),
        login_base: "/.auth".to_string(),
        ..WebAuthConfig::default()
    };
    c.host_caps
        .insert("ops.example".to_string(), "ops-admin".to_string());
    c
}

fn req(method: &str, target: &str, headers: &[(&str, &str)], body: &str) -> Request {
    let (path, query) = split_target(target);
    Request {
        method: method.to_string(),
        path,
        version: "HTTP/1.1".to_string(),
        query,
        headers: headers
            .iter()
            .map(|(k, v)| (k.to_ascii_lowercase(), v.to_string()))
            .collect(),
        body: body.to_string(),
    }
}

/// Build a per-request context at a fixed clock (so rate/lockout time is stable).
fn ctx_at<'a>(rt: &'a Runtime, client: &'a Client, now: u64) -> Ctx<'a> {
    Ctx {
        rt,
        client,
        keep_alive: false,
        now,
        now_ms: now * 1000,
        t0: Instant::now(),
    }
}

/// Drive one request through `route` against a shared runtime + client at `now`.
fn drive(rt: &Runtime, client: &Client, request: &Request, now: u64) -> Vec<u8> {
    let ctx = ctx_at(rt, client, now);
    route(request, &ctx)
}

fn parse_resp(bytes: &[u8]) -> (u16, Vec<(String, String)>, String) {
    let text = String::from_utf8_lossy(bytes);
    let (head, body) = text.split_once("\r\n\r\n").unwrap_or((&text, ""));
    let mut lines = head.split("\r\n");
    let status = lines
        .next()
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let headers = lines
        .filter_map(|l| l.split_once(": "))
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect();
    (status, headers, body.to_string())
}

fn header<'a>(hs: &'a [(String, String)], name: &str) -> Option<&'a str> {
    hs.iter().find(|(k, _)| k == name).map(|(_, v)| v.as_str())
}

// ---------------------------------------------------------------------------
// Routing + the 200/401/403 split (migrated from the prior suite).
// ---------------------------------------------------------------------------

#[test]
fn healthz_is_open() {
    let root = RootKey::from_seed([1u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let (status, _, body) = parse_resp(&drive(&rt, &c, &req("GET", "/healthz", &[], ""), 1000));
    assert_eq!(status, 200);
    assert_eq!(body, "ok");
}

#[test]
fn auth_admits_valid_cap_and_echoes_verified_subject() {
    let root = RootKey::from_seed([2u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    let r = req(
        "GET",
        "/auth?cap=ops-admin",
        &[
            ("Authorization", &format!("Bearer {token}")),
            ("X-Dregg-Subject", "dregg:attacker"),
        ],
        "",
    );
    let (status, hs, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 200);
    let subject = header(&hs, "X-Dregg-Subject").unwrap();
    assert!(subject.starts_with("dregg:"));
    assert_ne!(subject, "dregg:attacker", "forged subject header ignored");
    assert_eq!(header(&hs, "X-Dregg-Cap"), Some("ops-admin"));
}

#[test]
fn auth_resolves_cap_from_host_map() {
    let root = RootKey::from_seed([3u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    let r = req(
        "GET",
        "/auth",
        &[
            ("X-Forwarded-Host", "ops.example"),
            ("Authorization", &format!("Bearer {token}")),
        ],
        "",
    );
    let (status, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 200);
}

#[test]
fn auth_missing_credential_is_401() {
    let root = RootKey::from_seed([4u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let (status, hs, _) = parse_resp(&drive(
        &rt,
        &c,
        &req("GET", "/auth?cap=ops-admin", &[], ""),
        1000,
    ));
    assert_eq!(status, 401);
    assert_eq!(header(&hs, "WWW-Authenticate"), Some("Dregg-Cap"));
}

#[test]
fn auth_genuine_but_uncapped_is_403_not_bounced() {
    let root = RootKey::from_seed([5u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&root, ["grafana-view"], None).encode();
    let r = req(
        "GET",
        "/auth?cap=ops-admin",
        &[
            ("Authorization", &format!("Bearer {token}")),
            ("Accept", "text/html"),
        ],
        "",
    );
    let (status, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 403);
}

#[test]
fn auth_unauthenticated_browser_is_bounced_to_login() {
    let root = RootKey::from_seed([6u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let r = req(
        "GET",
        "/auth?cap=ops-admin",
        &[("Accept", "text/html"), ("X-Forwarded-Uri", "/dash")],
        "",
    );
    let (status, hs, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 302);
    assert!(
        header(&hs, "Location")
            .unwrap()
            .starts_with("/.auth/login?rd=")
    );
}

#[test]
fn break_glass_admits() {
    let root = RootKey::from_seed([7u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let r = req(
        "GET",
        "/auth?cap=ops-admin",
        &[("X-Dregg-Break-Glass", "rescue-me")],
        "",
    );
    let (status, hs, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 200);
    assert_eq!(header(&hs, "X-Dregg-Subject"), Some("dregg:break-glass"));
}

#[test]
fn whoami_reports_verified_identity_and_ignores_forgery() {
    let root = RootKey::from_seed([8u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let (status, _, body) = parse_resp(&drive(&rt, &c, &req("GET", "/whoami", &[], ""), 1000));
    assert_eq!(status, 200);
    assert!(body.contains("\"authenticated\":false"), "{body}");

    let pk = [0x33u8; 32];
    let token = mint_session_for(&root, &pk, ["ops-admin"], 0, 10_000_000_000).encode();
    let r = req(
        "GET",
        "/whoami",
        &[
            ("Authorization", &format!("Bearer {token}")),
            ("X-Dregg-Subject", "dregg:attacker"),
        ],
        "",
    );
    let (_, _, body) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert!(body.contains("\"authenticated\":true"), "{body}");
    let want = crate::account_id::account_subject(&pk);
    assert!(body.contains(&want), "{body}");
    assert!(!body.contains("attacker"), "{body}");
}

#[test]
fn whoami_rejects_forged_credential() {
    let root = RootKey::from_seed([9u8; 32]);
    let attacker = RootKey::from_seed([99u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&attacker, ["ops-admin"], None).encode();
    let r = req(
        "GET",
        "/whoami",
        &[("Authorization", &format!("Bearer {token}"))],
        "",
    );
    let (_, _, body) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert!(body.contains("\"authenticated\":false"), "{body}");
}

#[test]
fn login_challenge_is_fresh_json() {
    let root = RootKey::from_seed([10u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let (status, hs, body) = parse_resp(&drive(
        &rt,
        &c,
        &req("GET", "/login/challenge", &[], ""),
        1000,
    ));
    assert_eq!(status, 200);
    assert_eq!(
        header(&hs, "Content-Type"),
        Some("application/json; charset=utf-8")
    );
    assert!(body.contains("\"challenge\":\""), "{body}");
    assert!(body.contains("\"alg\":\"ed25519-pop\""), "{body}");
}

fn form(headers: Vec<(&str, &str)>, body: &str) -> Request {
    let mut h = vec![("Content-Type", "application/x-www-form-urlencoded")];
    h.extend(headers);
    req("POST", "/login", &h, body)
}

#[test]
fn login_sets_cookie_that_admits_at_auth() {
    let root = RootKey::from_seed([11u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    let r = form(vec![], &format!("credential={token}&format=json"));
    let (status, hs, json) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 200, "{json}");
    let set_cookie = header(&hs, "Set-Cookie").expect("a session cookie is set");
    assert!(
        set_cookie.contains("HttpOnly")
            && set_cookie.contains("Secure")
            && set_cookie.contains("SameSite=Lax")
    );
    let cookie_val = set_cookie
        .split(';')
        .next()
        .unwrap()
        .split_once('=')
        .unwrap()
        .1;
    let r2 = req(
        "GET",
        "/auth?cap=ops-admin",
        &[("Cookie", &format!("{}={}", rt.cfg.cookie_name, cookie_val))],
        "",
    );
    let (status2, _, _) = parse_resp(&drive(&rt, &c, &r2, 1000));
    assert_eq!(status2, 200);
}

#[test]
fn login_requires_form_content_type() {
    let root = RootKey::from_seed([40u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    // No Content-Type header at all → 415.
    let r = req("POST", "/login", &[], &format!("credential={token}"));
    let (status, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 415, "missing content-type is rejected");
    // A JSON content-type (not a form) → 415.
    let r = req(
        "POST",
        "/login",
        &[("Content-Type", "application/json")],
        "{}",
    );
    let (status, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 415);
}

#[test]
fn login_refuses_forged_credential() {
    let root = RootKey::from_seed([12u8; 32]);
    let attacker = RootKey::from_seed([98u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&attacker, ["ops-admin"], None).encode();
    let r = form(vec![], &format!("credential={token}&format=json"));
    let (status, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 401);
}

#[test]
fn login_open_redirect_is_neutralized() {
    let root = RootKey::from_seed([13u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    let r = form(
        vec![],
        &format!("credential={token}&rd=https://evil.example/pwn"),
    );
    let (status, hs, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(status, 302);
    assert_eq!(header(&hs, "Location"), Some("/"));
}

#[test]
fn unknown_route_is_404() {
    let root = RootKey::from_seed([14u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let (status, _, _) = parse_resp(&drive(&rt, &c, &req("GET", "/nope", &[], ""), 1000));
    assert_eq!(status, 404);
}

// ---------------------------------------------------------------------------
// New behavior: JSON injection resistance, metrics, rate limiting, lockout,
// single-use PoP, hot revocation, not-yet-valid, chunked, keep-alive, socket.
// ---------------------------------------------------------------------------

#[test]
fn whoami_json_is_injection_safe() {
    // A malicious `acct` caveat carrying a quote must NOT break the JSON framing.
    let root = RootKey::from_seed([50u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let evil = "x\",\"authenticated\":\"pwned";
    let token = crate::grant::mint_session(&root, evil, ["ops-admin"], 0, 10_000_000_000).encode();
    let r = req(
        "GET",
        "/whoami",
        &[("Authorization", &format!("Bearer {token}"))],
        "",
    );
    let (_, _, body) = parse_resp(&drive(&rt, &c, &r, 1000));
    // The whole hostile string is escaped inside the subject value; no second
    // `authenticated` field is smuggled in.
    assert!(body.contains("\"authenticated\":true"), "{body}");
    assert!(
        !body.contains("\"authenticated\":\"pwned"),
        "injection escaped: {body}"
    );
    assert!(body.contains("\\\""), "quote escaped: {body}");
}

#[test]
fn metrics_endpoint_reports_counters() {
    let root = RootKey::from_seed([51u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    // One admit, one 401.
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    drive(
        &rt,
        &c,
        &req(
            "GET",
            "/auth?cap=ops-admin",
            &[("Authorization", &format!("Bearer {token}"))],
            "",
        ),
        1000,
    );
    drive(&rt, &c, &req("GET", "/auth?cap=ops-admin", &[], ""), 1000);
    let (status, hs, body) = parse_resp(&drive(&rt, &c, &req("GET", "/metrics", &[], ""), 1000));
    assert_eq!(status, 200);
    assert!(
        header(&hs, "Content-Type")
            .unwrap()
            .starts_with("text/plain; version=0.0.4")
    );
    assert!(body.contains("webauth_admit_total 1"), "{body}");
    assert!(body.contains("webauth_deny_401_total 1"), "{body}");
    assert!(
        body.contains("# TYPE webauth_requests_total counter"),
        "{body}"
    );
}

#[test]
fn rate_limit_throttles_a_flooding_client() {
    let root = RootKey::from_seed([52u8; 32]);
    let mut cfg = cfg_for(&root);
    cfg.rate_burst = 3;
    cfg.rate_per_min = 60; // 1/sec refill; at a fixed clock, only the burst passes
    let rt = Runtime::for_test(cfg);
    let c = Client::test();
    let r = req("GET", "/auth?cap=ops-admin", &[], "");
    // First 3 within the burst are served (401s), the 4th is throttled (429).
    for _ in 0..3 {
        let (s, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
        assert_eq!(s, 401);
    }
    let (s, _, _) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert_eq!(s, 429, "the flood is throttled");
    // A different client has its own budget.
    let other = Client {
        ip: "10.0.0.9".to_string(),
    };
    let (s, _, _) = parse_resp(&drive(&rt, &other, &r, 1000));
    assert_eq!(s, 401);
}

#[test]
fn failed_break_glass_arms_lockout() {
    let root = RootKey::from_seed([53u8; 32]);
    let mut cfg = cfg_for(&root);
    cfg.lockout_threshold = 2;
    cfg.lockout_base_secs = 10;
    cfg.rate_per_min = 0; // disable the rate bucket so we isolate the lockout
    let rt = Runtime::for_test(cfg);
    let c = Client::test();
    let bad = req(
        "GET",
        "/auth?cap=ops-admin",
        &[("X-Dregg-Break-Glass", "wrong")],
        "",
    );
    // Two failed break-glass attempts arm the lockout.
    assert_eq!(parse_resp(&drive(&rt, &c, &bad, 1000)).0, 401);
    assert_eq!(parse_resp(&drive(&rt, &c, &bad, 1000)).0, 401);
    // Now even a well-formed sensitive request from this client is locked out.
    let (s, _, _) = parse_resp(&drive(
        &rt,
        &c,
        &req("GET", "/auth?cap=ops-admin", &[], ""),
        1000,
    ));
    assert_eq!(s, 429, "locked out after repeated failed break-glass");
    // The correct break-glass, after the lockout window elapses, clears it.
    let ok = req(
        "GET",
        "/auth?cap=ops-admin",
        &[("X-Dregg-Break-Glass", "rescue-me")],
        "",
    );
    let (s, _, _) = parse_resp(&drive(&rt, &c, &ok, 1011)); // 11s later
    assert_eq!(s, 200);
    // And the client is no longer locked.
    let (s, _, _) = parse_resp(&drive(
        &rt,
        &c,
        &req("GET", "/auth?cap=ops-admin", &[], ""),
        1011,
    ));
    assert_eq!(s, 401);
}

fn pop_login(cred: &dregg_agent::cred::Credential, challenge: &str) -> Request {
    let msg = crate::challenge::signing_message(challenge);
    let sig = hex(&cred.sign_challenge(&msg));
    let body = format!(
        "credential={}&challenge={}&signature={}&format=json",
        cred.encode(),
        challenge,
        sig
    );
    form(vec![("Accept", "application/json")], &body)
}

#[test]
fn pop_login_is_single_use() {
    let root = RootKey::from_seed([54u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    let cred = mint_caps(&root, ["ops-admin"], None);
    let challenge = crate::challenge::issue(&rt.cfg.challenge_key, 1000, rt.cfg.challenge_ttl_secs);
    // First PoP login with a fresh challenge succeeds.
    let r1 = pop_login(&cred, &challenge);
    let (s1, _, b1) = parse_resp(&drive(&rt, &c, &r1, 1000));
    assert_eq!(s1, 200, "{b1}");
    // Replaying the SAME challenge (even though its MAC still validates within
    // the TTL) is rejected as a replay.
    let r2 = pop_login(&cred, &challenge);
    let (s2, _, b2) = parse_resp(&drive(&rt, &c, &r2, 1000));
    assert_eq!(s2, 401, "replay rejected: {b2}");
    assert!(b2.contains("replay"), "{b2}");
}

#[test]
fn pop_single_use_can_be_disabled() {
    let root = RootKey::from_seed([55u8; 32]);
    let mut cfg = cfg_for(&root);
    cfg.pop_single_use = false;
    let rt = Runtime::for_test(cfg);
    let c = Client::test();
    let cred = mint_caps(&root, ["ops-admin"], None);
    let challenge = crate::challenge::issue(&rt.cfg.challenge_key, 1000, rt.cfg.challenge_ttl_secs);
    assert_eq!(
        parse_resp(&drive(&rt, &c, &pop_login(&cred, &challenge), 1000)).0,
        200
    );
    // With single-use disabled, the same challenge replays within its TTL.
    assert_eq!(
        parse_resp(&drive(&rt, &c, &pop_login(&cred, &challenge), 1000)).0,
        200
    );
}

#[test]
fn hot_revocation_kills_a_live_token_without_restart() {
    let root = RootKey::from_seed([56u8; 32]);
    let cfg = cfg_for(&root);
    // The Revocations handle inside cfg is shared; simulate the reload thread's
    // live update by inserting into it and observing the next /auth flip.
    let revoked = cfg.revoked.clone();
    let rt = Runtime::for_test(cfg);
    let c = Client::test();
    let token = crate::grant::mint_session(&root, "acct-z", ["ops-admin"], 0, 100_000).encode();
    let r = req(
        "GET",
        "/auth?cap=ops-admin",
        &[("Authorization", &format!("Bearer {token}"))],
        "",
    );
    assert_eq!(
        parse_resp(&drive(&rt, &c, &r, 1000)).0,
        200,
        "fresh token admits"
    );
    // Operator revokes by tail — no restart.
    let tail = dregg_agent::cred::Credential::decode(&token)
        .unwrap()
        .tail_hex();
    revoked.insert(tail);
    assert_eq!(parse_resp(&drive(&rt, &c, &r, 1000)).0, 401, "revoked live");
}

#[test]
fn not_yet_valid_session_is_not_authenticated_at_whoami() {
    use dregg_agent::cred::{Caveat, Pred};
    let root = RootKey::from_seed([57u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let c = Client::test();
    // A credential that only becomes valid at t=5000.
    let cred = root
        .mint([Caveat::FirstParty(Pred::NotBefore { at: 5000 })])
        .encode();
    let r = req(
        "GET",
        "/whoami",
        &[("Authorization", &format!("Bearer {cred}"))],
        "",
    );
    let (_, _, body) = parse_resp(&drive(&rt, &c, &r, 1000));
    assert!(
        body.contains("\"authenticated\":false"),
        "not-yet-valid is not a live session: {body}"
    );
    // Once its window opens, it authenticates.
    let (_, _, body) = parse_resp(&drive(&rt, &c, &r, 6000));
    assert!(body.contains("\"authenticated\":true"), "{body}");
}

// ---------------------------------------------------------------------------
// Real-socket integration: raw HTTP bytes through handle_conn (keep-alive,
// chunked, oversized).
// ---------------------------------------------------------------------------

/// Serve exactly one connection on a fresh loopback socket and return the raw
/// bytes the server wrote back for the given raw request bytes.
fn socket_round_trip(rt: Arc<Runtime>, raw: &[u8]) -> Vec<u8> {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = listener.local_addr().unwrap();
    let server = std::thread::spawn(move || {
        let (stream, peer) = listener.accept().unwrap();
        let client = Client::from_peer(Some(peer));
        let _ = handle_conn(stream, &rt, client);
    });
    let mut conn = TcpStream::connect(addr).unwrap();
    conn.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
    conn.write_all(raw).unwrap();
    let mut out = Vec::new();
    // handle_conn closes the socket when done (Connection: close or budget),
    // so read_to_end terminates.
    let _ = conn.read_to_end(&mut out);
    server.join().unwrap();
    out
}

#[test]
fn socket_healthz_round_trip() {
    let root = RootKey::from_seed([60u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let raw = b"GET /healthz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
    let out = socket_round_trip(rt, raw);
    let (status, _, body) = parse_resp(&out);
    assert_eq!(status, 200);
    assert_eq!(body, "ok");
}

#[test]
fn socket_keep_alive_serves_two_requests() {
    let root = RootKey::from_seed([61u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    // Two pipelined requests; the second asks to close so read_to_end terminates.
    let raw = b"GET /healthz HTTP/1.1\r\nHost: x\r\n\r\n\
                GET /healthz HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
    let out = socket_round_trip(rt, raw);
    let text = String::from_utf8_lossy(&out);
    let n = text.matches("HTTP/1.1 200 OK").count();
    assert_eq!(
        n, 2,
        "both keep-alive requests were served on one connection:\n{text}"
    );
    assert!(
        text.contains("Connection: keep-alive"),
        "first response advertised keep-alive:\n{text}"
    );
}

#[test]
fn socket_chunked_login_body_is_decoded() {
    let root = RootKey::from_seed([62u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    let token = mint_caps(&root, ["ops-admin"], None).encode();
    let body = format!("credential={token}&format=json");
    // Split the body into two chunks to exercise the dechunker.
    let (a, b) = body.split_at(body.len() / 2);
    let raw = format!(
        "POST /login HTTP/1.1\r\nHost: x\r\nContent-Type: application/x-www-form-urlencoded\r\n\
         Transfer-Encoding: chunked\r\nConnection: close\r\n\r\n\
         {:x}\r\n{}\r\n{:x}\r\n{}\r\n0\r\n\r\n",
        a.len(),
        a,
        b.len(),
        b
    );
    let out = socket_round_trip(rt, raw.as_bytes());
    let (status, _, json) = parse_resp(&out);
    assert_eq!(status, 200, "chunked login body decoded: {json}");
    assert!(json.contains("\"session\""), "{json}");
}

#[test]
fn socket_oversized_headers_are_rejected_not_panicked() {
    let root = RootKey::from_seed([63u8; 32]);
    let rt = Runtime::for_test(cfg_for(&root));
    // A single header far larger than MAX_HEADER_BYTES.
    let big = "x".repeat(70 * 1024);
    let raw = format!("GET /healthz HTTP/1.1\r\nHost: x\r\nX-Big: {big}\r\n\r\n");
    let out = socket_round_trip(rt, raw.as_bytes());
    let (status, _, _) = parse_resp(&out);
    assert_eq!(status, 400, "oversized headers → clean 400, no panic");
}

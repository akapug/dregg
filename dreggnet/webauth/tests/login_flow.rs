//! End-to-end PROOF of the cap-auth login + forward-auth flow, over real TCP —
//! the same shape Caddy's `forward_auth` + the login page/extension drive.
//!
//! The teeth (the deploy-readiness "cap-auth flow proven"):
//!  * a valid `dga1_` → challenge → sign → session → `/auth` ADMITS with the
//!    correct `X-Dregg-Subject`;
//!  * a FORGED (wrong-issuer), EXPIRED, REVOKED, or MISSING session → 401;
//!  * a session WITHOUT the route's cap → 403 (authenticated, not authorized);
//!  * NO-FORGE: a client-supplied `X-Dregg-Subject` is ignored — webauth sets the
//!    subject from the verified credential, never from the request;
//!  * a stale challenge / a bad proof-of-possession signature → 401.

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::time::Duration;

use dreggnet_webauth::challenge;
use dreggnet_webauth::config::WebAuthConfig;
use dreggnet_webauth::cred::{Credential, RootKey};
use dreggnet_webauth::grant::{mint_caps, mint_session};

fn spawn(cfg: WebAuthConfig) -> String {
    let probe = TcpListener::bind("127.0.0.1:0").unwrap();
    let addr = probe.local_addr().unwrap();
    drop(probe);
    let mut cfg = cfg;
    cfg.bind = addr.to_string();
    std::thread::spawn(move || {
        let _ = dreggnet_webauth::server::serve(cfg);
    });
    for _ in 0..100 {
        if TcpStream::connect(addr).is_ok() {
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    addr.to_string()
}

fn request(addr: &str, raw: &str) -> (u16, String) {
    let mut stream = TcpStream::connect(addr).unwrap();
    stream
        .set_read_timeout(Some(Duration::from_secs(5)))
        .unwrap();
    stream.write_all(raw.as_bytes()).unwrap();
    let mut buf = String::new();
    let _ = stream.read_to_string(&mut buf);
    let status = buf
        .lines()
        .next()
        .unwrap_or("")
        .split_whitespace()
        .nth(1)
        .and_then(|c| c.parse().ok())
        .unwrap_or(0);
    (status, buf)
}

fn post_form(addr: &str, path: &str, host: &str, body: &str) -> (u16, String) {
    request(
        addr,
        &format!(
            "POST {path} HTTP/1.1\r\nHost: {host}\r\nContent-Type: application/x-www-form-urlencoded\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{body}",
            body.len()
        ),
    )
}

fn header_value<'a>(resp: &'a str, name: &str) -> Option<&'a str> {
    let name = name.to_ascii_lowercase();
    resp.lines()
        .find(|l| l.to_ascii_lowercase().starts_with(&format!("{name}:")))
        .and_then(|l| l.split_once(':'))
        .map(|(_, v)| v.trim())
}

/// Pull the `dregg_session=<value>` out of a `Set-Cookie` line.
fn session_cookie(resp: &str) -> String {
    let sc = header_value(resp, "Set-Cookie").expect("a Set-Cookie header");
    let kv = sc.split(';').next().unwrap();
    kv.trim()
        .strip_prefix("dregg_session=")
        .unwrap()
        .to_string()
}

/// Extract `"challenge":"<...>"` from the JSON challenge response body.
fn challenge_from_json(resp: &str) -> String {
    let body = resp.split("\r\n\r\n").nth(1).unwrap_or("");
    let anchor = "\"challenge\":\"";
    let start = body.find(anchor).unwrap() + anchor.len();
    let rest = &body[start..];
    let end = rest.find('"').unwrap();
    rest[..end].to_string()
}

/// Current wall-clock seconds — the server verifies against this, so a "live"
/// session must be minted with `issued_at = now()` (not 0, which would put its
/// NotAfter back in 1970).
fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs()
}

fn hex(bytes: &[u8]) -> String {
    const LUT: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        s.push(LUT[(b >> 4) as usize] as char);
        s.push(LUT[(b & 0x0f) as usize] as char);
    }
    s
}

fn base_cfg(root: &RootKey) -> WebAuthConfig {
    let mut host_caps = std::collections::BTreeMap::new();
    host_caps.insert("ops.example".to_string(), "ops-admin".to_string());
    host_caps.insert("grafana.example".to_string(), "grafana-view".to_string());
    WebAuthConfig {
        root_pubkey_hex: Some(root.public().to_hex()),
        // A FIXED challenge key so a challenge issued to the test verifies on POST.
        challenge_key: [0x5Au8; 32],
        host_caps,
        ..WebAuthConfig::default()
    }
}

/// The FULL cap-login: GET a challenge, sign it with the credential's bearer
/// key, POST {credential, challenge, signature}, return the session cookie.
fn cap_login(addr: &str, cred: &Credential) -> String {
    let (cs, cbody) = request(
        addr,
        "GET /login/challenge HTTP/1.1\r\nHost: ops.example\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(cs, 200, "challenge issued: {cbody}");
    let ch = challenge_from_json(&cbody);
    let sig = cred.sign_challenge(&challenge::signing_message(&ch));
    let enc = cred.encode();
    let form = format!(
        "credential={}&challenge={}&signature={}&rd=%2Fdashboard",
        enc,
        ch,
        hex(&sig)
    );
    let (ps, pbody) = post_form(addr, "/login", "ops.example", &form);
    assert_eq!(ps, 302, "PoP login redirects with a cookie: {pbody}");
    session_cookie(&pbody)
}

fn auth(addr: &str, host: &str, cap: &str, cookie: &str, extra: &str) -> (u16, String) {
    request(
        addr,
        &format!(
            "GET /auth?cap={cap} HTTP/1.1\r\nHost: {host}\r\nCookie: dregg_session={cookie}\r\n{extra}Accept: */*\r\nConnection: close\r\n\r\n"
        ),
    )
}

// ===========================================================================
// The happy path: valid dga1_ → PoP login → session → /auth admits + subject.
// ===========================================================================

#[test]
fn full_pop_login_then_auth_admits_with_subject() {
    let root = RootKey::from_seed([60u8; 32]);
    let addr = spawn(base_cfg(&root));
    // A session for a real account (carries the stable `acct` subject).
    let session = mint_session(&root, "acct-alice", ["ops-admin"], now(), 100_000);
    let want_subject = dreggnet_webauth::subject_of(&session.encode()).unwrap();

    let cookie = cap_login(&addr, &session);
    let (status, body) = auth(&addr, "ops.example", "ops-admin", &cookie, "");
    assert_eq!(status, 200, "admitted after login: {body}");
    assert_eq!(
        header_value(&body, "X-Dregg-Subject"),
        Some(want_subject.as_str()),
        "the verified subject is echoed: {body}"
    );
    assert_eq!(header_value(&body, "X-Dregg-Cap"), Some("ops-admin"));
}

// ===========================================================================
// NO-FORGE: a client cannot spoof its identity via X-Dregg-Subject.
// ===========================================================================

#[test]
fn client_supplied_subject_is_ignored() {
    let root = RootKey::from_seed([61u8; 32]);
    let addr = spawn(base_cfg(&root));
    let session = mint_session(&root, "acct-honest", ["ops-admin"], now(), 100_000);
    let real = dreggnet_webauth::subject_of(&session.encode()).unwrap();
    let cookie = cap_login(&addr, &session);

    // The client injects a forged identity header on the /auth request.
    let (status, body) = auth(
        &addr,
        "ops.example",
        "ops-admin",
        &cookie,
        "X-Dregg-Subject: dregg:attacker\r\n",
    );
    assert_eq!(status, 200);
    let echoed = header_value(&body, "X-Dregg-Subject").unwrap();
    assert_eq!(
        echoed, real,
        "webauth sets the REAL subject, not the forgery"
    );
    assert_ne!(
        echoed, "dregg:attacker",
        "the forged subject never survives"
    );
}

// ===========================================================================
// Refusals: forged / expired / revoked / missing → 401; wrong cap → 403.
// ===========================================================================

#[test]
fn forged_issuer_session_is_401() {
    let root = RootKey::from_seed([62u8; 32]);
    let attacker = RootKey::from_seed([0xEEu8; 32]);
    let addr = spawn(base_cfg(&root));
    // A well-formed credential, but minted by an attacker's root.
    let forged = mint_caps(&attacker, ["ops-admin"], None).encode();
    let (status, body) = auth(&addr, "ops.example", "ops-admin", &forged, "");
    assert_eq!(
        status, 401,
        "a foreign-issuer credential is unauthenticated: {body}"
    );
}

#[test]
fn expired_session_is_401() {
    let root = RootKey::from_seed([63u8; 32]);
    let addr = spawn(base_cfg(&root));
    // Expired far in the past (issued_at 0, ttl 10 → NotAfter 10, now ≫ 10).
    let expired = mint_session(&root, "acct-x", ["ops-admin"], 0, 10).encode();
    let (status, body) = auth(&addr, "ops.example", "ops-admin", &expired, "");
    assert_eq!(
        status, 401,
        "an expired session is unauthenticated (re-login): {body}"
    );
}

#[test]
fn revoked_session_is_401() {
    let root = RootKey::from_seed([64u8; 32]);
    let mut cfg = base_cfg(&root);
    let session = mint_session(&root, "acct-leaked", ["ops-admin"], now(), 100_000);
    cfg.revoked.insert(session.tail_hex()); // kill this exact token
    let addr = spawn(cfg);
    let (status, body) = auth(&addr, "ops.example", "ops-admin", &session.encode(), "");
    assert_eq!(status, 401, "a revoked session is refused: {body}");
}

#[test]
fn missing_session_is_401() {
    let root = RootKey::from_seed([65u8; 32]);
    let addr = spawn(base_cfg(&root));
    let (status, _) = request(
        &addr,
        "GET /auth?cap=ops-admin HTTP/1.1\r\nHost: ops.example\r\nAccept: */*\r\nConnection: close\r\n\r\n",
    );
    assert_eq!(status, 401, "no session at all is unauthenticated");
}

#[test]
fn valid_session_without_route_cap_is_403() {
    let root = RootKey::from_seed([66u8; 32]);
    let addr = spawn(base_cfg(&root));
    // A genuine, live session for grafana-view only.
    let session = mint_session(&root, "acct-viewer", ["grafana-view"], now(), 100_000);
    let cookie = cap_login(&addr, &session);
    // It admits at its own surface …
    let (g, _) = auth(&addr, "grafana.example", "grafana-view", &cookie, "");
    assert_eq!(g, 200, "grafana-view admits at grafana");
    // … but is FORBIDDEN (403, not 401) at ops-admin: authenticated, not authorized.
    let (o, body) = auth(&addr, "ops.example", "ops-admin", &cookie, "");
    assert_eq!(
        o, 403,
        "a live session lacking ops-admin is forbidden: {body}"
    );
}

// ===========================================================================
// The proof-of-possession handshake itself.
// ===========================================================================

#[test]
fn bad_pop_signature_is_rejected() {
    let root = RootKey::from_seed([67u8; 32]);
    let addr = spawn(base_cfg(&root));
    let session = mint_session(&root, "acct-a", ["ops-admin"], now(), 100_000);

    let (_, cbody) = request(
        &addr,
        "GET /login/challenge HTTP/1.1\r\nHost: ops.example\r\nConnection: close\r\n\r\n",
    );
    let ch = challenge_from_json(&cbody);
    // Sign a DIFFERENT credential's key over the challenge (proof-of-possession
    // fails: the signature does not verify under the presented credential).
    let wrong = mint_session(&root, "acct-b", ["ops-admin"], now(), 100_000);
    let sig = wrong.sign_challenge(&challenge::signing_message(&ch));
    let form = format!(
        "credential={}&challenge={}&signature={}",
        session.encode(),
        ch,
        hex(&sig)
    );
    let (status, body) = post_form(&addr, "/login", "ops.example", &form);
    assert_eq!(status, 401, "a mismatched PoP signature is refused: {body}");
}

#[test]
fn stale_challenge_is_rejected() {
    let root = RootKey::from_seed([68u8; 32]);
    let mut cfg = base_cfg(&root);
    cfg.challenge_ttl_secs = 0; // every issued challenge is already expired
    let addr = spawn(cfg);
    let session = mint_session(&root, "acct-a", ["ops-admin"], now(), 100_000);
    let (_, cbody) = request(
        &addr,
        "GET /login/challenge HTTP/1.1\r\nHost: ops.example\r\nConnection: close\r\n\r\n",
    );
    let ch = challenge_from_json(&cbody);
    let sig = session.sign_challenge(&challenge::signing_message(&ch));
    std::thread::sleep(Duration::from_millis(1100)); // let wall-clock pass the 0s ttl
    let form = format!(
        "credential={}&challenge={}&signature={}",
        session.encode(),
        ch,
        hex(&sig)
    );
    let (status, body) = post_form(&addr, "/login", "ops.example", &form);
    assert_eq!(status, 401, "a stale challenge is refused: {body}");
}

#[test]
fn paste_of_forged_credential_is_rejected_at_login() {
    let root = RootKey::from_seed([69u8; 32]);
    let attacker = RootKey::from_seed([0xABu8; 32]);
    let addr = spawn(base_cfg(&root));
    // Paste path (no challenge/signature): a foreign-issuer credential must not
    // mint a session — the chain-verify gate at login rejects it.
    let forged = mint_caps(&attacker, ["ops-admin"], None).encode();
    let form = format!("credential={forged}");
    let (status, body) = post_form(&addr, "/login", "ops.example", &form);
    assert_eq!(
        status, 401,
        "paste of a forged credential is refused: {body}"
    );
}

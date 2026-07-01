//! The pure-std, thread-per-connection HTTP/1.1 server — the same shape as the
//! `dreggnet-ops` serving binary (no `httpe`/Elide closure, cross-builds
//! trivially). It exposes the surfaces Caddy's `forward_auth` and the login flow
//! ride:
//!
//! | Method + path     | Serves                                                    |
//! |-------------------|-----------------------------------------------------------|
//! | `GET /auth`       | the forward-auth decision (2xx admit / 302→login on deny) |
//! | `GET /login`      | the login page (paste / wallet-sign a `dga1_…` credential)|
//! | `POST /login`     | accept the credential → set the session cookie → redirect |
//! | `GET /logout`     | clear the session cookie                                  |
//! | `GET /healthz`    | liveness (always open)                                    |
//!
//! Caddy maps `/login`, `/logout`, `/healthz` to this service as PUBLIC paths
//! (no forward_auth) and gates everything else through `/auth`.

use std::io::{BufRead, BufReader, Read, Write};
use std::net::{TcpListener, TcpStream};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::config::WebAuthConfig;
use crate::{AuthInput, Verdict, decide, subject_of};

const MAX_HEADER_BYTES: usize = 64 * 1024;
const MAX_BODY_BYTES: usize = 256 * 1024;

/// Run the server forever on the configured bind address.
pub fn serve(cfg: WebAuthConfig) -> std::io::Result<()> {
    let listener = TcpListener::bind(&cfg.bind)?;
    eprintln!("dreggnet-webauth: forward-auth on http://{}", cfg.bind);
    eprintln!(
        "  root pubkey: {}",
        cfg.root_pubkey_hex
            .as_deref()
            .unwrap_or("(NONE — every cap check will DENY)")
    );
    eprintln!(
        "  break-glass: {}",
        if cfg.break_glass.is_some() {
            "configured"
        } else {
            "(disabled)"
        }
    );
    eprintln!("  host→cap map: {} entries", cfg.host_caps.len());
    let cfg = Arc::new(cfg);
    for stream in listener.incoming() {
        let stream = match stream {
            Ok(s) => s,
            Err(_) => continue,
        };
        let cfg = Arc::clone(&cfg);
        std::thread::spawn(move || {
            let _ = handle_conn(stream, &cfg);
        });
    }
    Ok(())
}

/// A parsed request: method, path, query, headers (lowercased keys), body.
struct Request {
    method: String,
    path: String,
    query: Vec<(String, String)>,
    headers: Vec<(String, String)>,
    body: String,
}

impl Request {
    fn header(&self, name: &str) -> Option<&str> {
        let name = name.to_ascii_lowercase();
        self.headers
            .iter()
            .find(|(k, _)| *k == name)
            .map(|(_, v)| v.as_str())
    }
    fn query_get(&self, key: &str) -> Option<&str> {
        self.query
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v.as_str())
    }
    /// Extract a named cookie from the `Cookie` header.
    fn cookie(&self, name: &str) -> Option<String> {
        let raw = self.header("cookie")?;
        for part in raw.split(';') {
            let part = part.trim();
            if let Some((k, v)) = part.split_once('=') {
                if k.trim() == name {
                    return Some(v.trim().to_string());
                }
            }
        }
        None
    }
}

fn handle_conn(mut stream: TcpStream, cfg: &WebAuthConfig) -> std::io::Result<()> {
    let req = match read_request(&mut stream)? {
        Some(r) => r,
        None => return Ok(()),
    };
    let resp = route(&req, cfg);
    stream.write_all(&resp)?;
    stream.flush()
}

fn read_request(stream: &mut TcpStream) -> std::io::Result<Option<Request>> {
    let mut reader = BufReader::new(stream);
    let mut request_line = String::new();
    if reader.read_line(&mut request_line)? == 0 {
        return Ok(None);
    }
    let mut parts = request_line.split_whitespace();
    let method = parts.next().unwrap_or("").to_string();
    let target = parts.next().unwrap_or("/").to_string();
    let (path, query) = split_target(&target);

    let mut headers = Vec::new();
    let mut total = request_line.len();
    loop {
        let mut line = String::new();
        let n = reader.read_line(&mut line)?;
        if n == 0 {
            break;
        }
        total += n;
        if total > MAX_HEADER_BYTES {
            break;
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            break;
        }
        if let Some((k, v)) = trimmed.split_once(':') {
            headers.push((k.trim().to_ascii_lowercase(), v.trim().to_string()));
        }
    }

    // Read the body iff Content-Length says so (POST /login).
    let mut body = String::new();
    if let Some((_, len)) = headers.iter().find(|(k, _)| k == "content-length") {
        if let Ok(len) = len.parse::<usize>() {
            let len = len.min(MAX_BODY_BYTES);
            let mut buf = vec![0u8; len];
            reader.read_exact(&mut buf)?;
            body = String::from_utf8_lossy(&buf).into_owned();
        }
    }

    Ok(Some(Request {
        method,
        path,
        query,
        headers,
        body,
    }))
}

fn split_target(target: &str) -> (String, Vec<(String, String)>) {
    match target.split_once('?') {
        Some((p, q)) => (p.to_string(), parse_query(q)),
        None => (target.to_string(), Vec::new()),
    }
}

fn parse_query(q: &str) -> Vec<(String, String)> {
    q.split('&')
        .filter(|s| !s.is_empty())
        .map(|pair| match pair.split_once('=') {
            Some((k, v)) => (url_decode(k), url_decode(v)),
            None => (url_decode(pair), String::new()),
        })
        .collect()
}

fn url_decode(s: &str) -> String {
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'%' if i + 2 < bytes.len() => {
                let hi = (bytes[i + 1] as char).to_digit(16);
                let lo = (bytes[i + 2] as char).to_digit(16);
                if let (Some(hi), Some(lo)) = (hi, lo) {
                    out.push((hi * 16 + lo) as u8);
                    i += 3;
                    continue;
                }
                out.push(b'%');
                i += 1;
            }
            b'+' => {
                out.push(b' ');
                i += 1;
            }
            b => {
                out.push(b);
                i += 1;
            }
        }
    }
    String::from_utf8_lossy(&out).into_owned()
}

fn now_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

fn route(req: &Request, cfg: &WebAuthConfig) -> Vec<u8> {
    match (req.method.as_str(), req.path.as_str()) {
        ("GET", "/healthz") => text(200, "ok"),
        ("GET", "/auth") => handle_auth(req, cfg),
        ("GET", "/login") => login_page(req, cfg),
        ("GET", "/login/challenge") => login_challenge(cfg),
        ("POST", "/login") => login_submit(req, cfg),
        ("GET", "/logout") => logout(cfg),
        _ => text(404, "not found"),
    }
}

// ---------------------------------------------------------------------------
// /auth — the forward-auth decision
// ---------------------------------------------------------------------------

fn extract_credential(req: &Request, cfg: &WebAuthConfig) -> Option<String> {
    if let Some(c) = req.cookie(&cfg.cookie_name) {
        if !c.is_empty() {
            return Some(c);
        }
    }
    if let Some(h) = req.header("x-dregg-credential") {
        if !h.is_empty() {
            return Some(h.to_string());
        }
    }
    if let Some(auth) = req.header("authorization") {
        if let Some(tok) = auth.strip_prefix("Bearer ") {
            if tok.starts_with("dga1_") {
                return Some(tok.trim().to_string());
            }
        }
    }
    None
}

fn extract_break_glass(req: &Request) -> Option<String> {
    if let Some(h) = req.header("x-dregg-break-glass") {
        if !h.is_empty() {
            return Some(h.to_string());
        }
    }
    None
}

fn handle_auth(req: &Request, cfg: &WebAuthConfig) -> Vec<u8> {
    // Caddy's forward_auth passes the original Host as X-Forwarded-Host and the
    // original path as X-Forwarded-Uri; the surface's required cap is either an
    // explicit ?cap= or resolved from the host map.
    let query_cap = req.query_get("cap");
    let fwd_host = req
        .header("x-forwarded-host")
        .or_else(|| req.header("host"));
    let required_cap = cfg.required_cap(query_cap, fwd_host);

    let input = AuthInput {
        credential: extract_credential(req, cfg),
        break_glass: extract_break_glass(req),
        required_cap: required_cap.clone(),
        now: now_secs(),
    };

    let verdict = decide(cfg, &input);
    match &verdict {
        Verdict::Admit { how, cap } => {
            // The subject is derived FROM THE VERIFIED CREDENTIAL ONLY — never
            // from a client-supplied header. `decide` has already verified the
            // credential chain, so the subject webauth sets here is the authentic
            // cap holder; any inbound X-Dregg-Subject the client sent is ignored
            // (and the Caddy edge additionally strips it before this subrequest).
            let subject = input
                .credential
                .as_deref()
                .and_then(subject_of)
                .unwrap_or_else(|| "dregg:break-glass".to_string());
            let mut headers = vec![
                ("X-Dregg-Auth".to_string(), how.clone()),
                ("X-Dregg-Subject".to_string(), subject),
            ];
            if let Some(cap) = cap {
                headers.push(("X-Dregg-Cap".to_string(), cap.clone()));
            }
            response(200, "text/plain; charset=utf-8", "authorized", &headers)
        }
        Verdict::Deny {
            reason,
            authenticated,
        } => {
            let status = verdict.status();
            // A browser that is NOT YET authenticated (401) is bounced to the
            // login page so the flow is usable. A browser that IS authenticated
            // but lacks the capability (403) is NOT bounced — re-login cannot
            // grant a wider cap; it gets an honest 403.
            let wants_html = req
                .header("accept")
                .map(|a| a.contains("text/html"))
                .unwrap_or(false);
            if wants_html && !*authenticated {
                let rd = req.header("x-forwarded-uri").unwrap_or("/");
                let loc = format!("{}/login?rd={}", cfg.login_base, url_encode(rd));
                redirect(302, &loc, &[])
            } else if status == 403 {
                response(
                    403,
                    "text/plain; charset=utf-8",
                    &format!("dregg-webauth: forbidden — {reason}\n"),
                    &[],
                )
            } else {
                response(
                    401,
                    "text/plain; charset=utf-8",
                    &format!("dregg-webauth: {reason}\n"),
                    &[("WWW-Authenticate".to_string(), "Dregg-Cap".to_string())],
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// /login — the login flow
// ---------------------------------------------------------------------------

/// `GET /login/challenge` — issue a fresh proof-of-possession challenge. The
/// client signs `challenge::signing_message(challenge)` with the credential's
/// bearer tail key and posts `{credential, challenge, signature}` back to
/// `/login`. Stateless (see [`crate::challenge`]); always public.
fn login_challenge(cfg: &WebAuthConfig) -> Vec<u8> {
    let now = now_secs();
    let challenge = crate::challenge::issue(&cfg.challenge_key, now, cfg.challenge_ttl_secs);
    let not_after = now + cfg.challenge_ttl_secs;
    // Hand-built JSON (no serde_json in the closure). The `context` is the hex of
    // the domain tag the client must prepend before signing.
    let ctx_hex = crate::cred::hex(crate::challenge::LOGIN_CHALLENGE_CTX);
    let body = format!(
        "{{\"challenge\":\"{challenge}\",\"not_after\":{not_after},\"alg\":\"ed25519-pop\",\"context_hex\":\"{ctx_hex}\"}}"
    );
    response(200, "application/json; charset=utf-8", &body, &[])
}

fn login_page(req: &Request, cfg: &WebAuthConfig) -> Vec<u8> {
    let rd = req.query_get("rd").unwrap_or("/");
    let rd_attr = html_escape(rd);
    let action = format!("{}/login", cfg.login_base);
    // The login base as a JS string literal for the client-side challenge fetch.
    let login_base_js = format!("\"{}\"", cfg.login_base.replace('"', ""));
    let page = format!(
        r#"<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>DreggNet — sign in with your dregg capability</title>
<style>
  body {{ font-family: system-ui, sans-serif; max-width: 40rem; margin: 4rem auto; padding: 0 1rem; color: #1a1a2e; }}
  h1 {{ font-size: 1.4rem; }}
  textarea {{ width: 100%; height: 7rem; font-family: ui-monospace, monospace; font-size: 0.85rem; }}
  button {{ padding: 0.6rem 1.2rem; font-size: 1rem; cursor: pointer; }}
  .hint {{ color: #555; font-size: 0.9rem; }}
  code {{ background: #f0f0f5; padding: 0 0.2rem; }}
</style>
</head>
<body>
<h1>Sign in with your dregg capability</h1>
<p class="hint">Paste the <code>dga1_…</code> capability your cipherclerk wallet holds
for this surface. It is verified offline against the surface's required capability;
no password, no node round-trip. Attenuated capabilities only reach the surfaces
they were narrowed to.</p>
<form method="POST" action="{action}" id="loginform">
  <input type="hidden" name="rd" value="{rd_attr}">
  <input type="hidden" name="challenge" id="challenge">
  <input type="hidden" name="signature" id="signature">
  <p><textarea name="credential" id="credential" placeholder="dga1_..." autofocus></textarea></p>
  <p><button type="submit">Present capability</button></p>
</form>
<p class="hint" id="wallet"></p>
<script>
// One-click PROOF-OF-POSSESSION login when a cipherclerk wallet is injected:
//   1. ask the wallet for its dga1_ capability for this origin,
//   2. GET /login/challenge for a fresh server nonce,
//   3. ask the wallet to sign the domain-tagged challenge with the credential's
//      bearer key, and
//   4. submit {{credential, challenge, signature}}.
// If no wallet is present the plain paste form above still works.
const base = {login_base_js};
if (window.dregg && typeof window.dregg.presentCredential === 'function') {{
  const el = document.getElementById('wallet');
  const btn = document.createElement('button');
  btn.textContent = 'Sign in with cipherclerk wallet';
  btn.onclick = async () => {{
    try {{
      const credential = await window.dregg.presentCredential({{ origin: location.host }});
      const chal = await (await fetch(base + '/login/challenge')).json();
      let signature = '';
      if (typeof window.dregg.signChallenge === 'function') {{
        signature = await window.dregg.signChallenge({{ credential, challenge: chal.challenge }});
      }}
      document.getElementById('credential').value = credential;
      document.getElementById('challenge').value = signature ? chal.challenge : '';
      document.getElementById('signature').value = signature;
      document.getElementById('loginform').submit();
    }} catch (e) {{ el.textContent = 'wallet declined: ' + e; }}
  }};
  el.appendChild(btn);
}}
</script>
</body>
</html>
"#
    );
    response(200, "text/html; charset=utf-8", &page, &[])
}

fn field<'a>(form: &'a [(String, String)], key: &str) -> Option<&'a str> {
    form.iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
        .filter(|v| !v.trim().is_empty())
}

/// `POST /login` — present a `dga1_` capability and receive a session cookie.
///
/// Two modes, both form-encoded (`application/x-www-form-urlencoded`):
///
///  * **Proof-of-possession** (the extension contract, and what the login page
///    uses when a wallet is present): `credential`, `challenge`, `signature`
///    (hex) — webauth verifies the challenge is fresh + this-service-issued, then
///    verifies the signature over the domain-tagged challenge under the
///    credential's bearer tail key. Proves *active* possession, anti-replay.
///  * **Paste** (the no-extension fallback): `credential` only.
///
/// In BOTH modes, if a root pubkey is configured webauth verifies the
/// credential's signature CHAIN under the issuer root and refuses an expired one
/// before setting the cookie — junk / forged / stale tokens never mint a session
/// (the per-surface capability meet still runs on every `/auth`).
///
/// Returns `302` + `Set-Cookie` for a browser, or `200` + a JSON
/// `{session, subject, expires}` when the caller asks for JSON (the extension).
fn login_submit(req: &Request, cfg: &WebAuthConfig) -> Vec<u8> {
    let form = parse_query(&req.body);
    let wants_json = req
        .header("accept")
        .map(|a| a.contains("application/json"))
        .unwrap_or(false)
        || field(&form, "format") == Some("json");

    let rd = field(&form, "rd").unwrap_or("/").to_string();

    let Some(cred_str) = field(&form, "credential") else {
        return login_error(wants_json, 400, "no credential presented");
    };
    let cred_str = cred_str.trim();

    // Structural decode.
    let credential = match crate::cred::Credential::decode(cred_str) {
        Ok(c) => c,
        Err(_) => {
            return login_error(wants_json, 400, "that is not a valid dga1_ capability");
        }
    };

    let now = now_secs();

    // Proof-of-possession, if a challenge + signature were supplied.
    match (field(&form, "challenge"), field(&form, "signature")) {
        (Some(challenge), Some(sig_hex)) => {
            if let Err(e) = crate::challenge::verify(&cfg.challenge_key, challenge, now) {
                return login_error(wants_json, 401, &format!("challenge rejected: {e}"));
            }
            let Some(sig) = decode_sig64(sig_hex) else {
                return login_error(wants_json, 400, "signature is not 64 hex-encoded bytes");
            };
            let msg = crate::challenge::signing_message(challenge);
            if !crate::cred::verify_pop(&credential.proof_public(), &msg, &sig) {
                return login_error(
                    wants_json,
                    401,
                    "proof-of-possession failed: signature does not verify under the credential's tail key",
                );
            }
        }
        (Some(_), None) | (None, Some(_)) => {
            return login_error(
                wants_json,
                400,
                "both `challenge` and `signature` are required for proof-of-possession login",
            );
        }
        (None, None) => { /* paste fallback — no PoP */ }
    }

    // Genuine-issuance gate: if a root pubkey is configured, the credential's
    // signature chain must verify under it, and it must not be expired. This
    // rejects forged / foreign / stale tokens at login (the per-surface cap meet
    // still runs on every /auth).
    if let Some(pk_hex) = &cfg.root_pubkey_hex {
        match crate::cred::PublicKey::from_hex(pk_hex) {
            Ok(root) => {
                if credential.verify_chain(&root).is_err() {
                    return login_error(
                        wants_json,
                        401,
                        "credential is not genuine under this service's issuer root",
                    );
                }
            }
            Err(_) => { /* misconfigured root — /auth will fail closed anyway */ }
        }
    }
    if credential.is_expired(now) {
        return login_error(wants_json, 401, "credential has already expired");
    }

    let subject = subject_of(cred_str).unwrap_or_else(|| "dregg:unknown".to_string());
    let max_age = cfg.session_ttl_secs.unwrap_or(86_400);
    let cookie = set_cookie(
        &cfg.cookie_name,
        cred_str,
        cfg.cookie_domain.as_deref(),
        max_age,
    );

    if wants_json {
        let expires = now + max_age;
        let body = format!(
            "{{\"session\":\"{cred_str}\",\"subject\":\"{subject}\",\"expires\":{expires}}}"
        );
        response(
            200,
            "application/json; charset=utf-8",
            &body,
            &[("Set-Cookie".to_string(), cookie)],
        )
    } else {
        redirect(
            302,
            &safe_redirect(&rd),
            &[("Set-Cookie".to_string(), cookie)],
        )
    }
}

/// A login failure, as JSON for the extension or HTML for the browser.
fn login_error(wants_json: bool, status: u16, reason: &str) -> Vec<u8> {
    if wants_json {
        let body = format!("{{\"error\":\"{}\"}}", reason.replace('"', "'"));
        response(status, "application/json; charset=utf-8", &body, &[])
    } else {
        let page = format!(
            "<p>Login failed: {}. <a href=\"/login\">try again</a></p>",
            html_escape(reason)
        );
        response(status, "text/html; charset=utf-8", &page, &[])
    }
}

/// Decode a 64-byte ed25519 signature from hex.
fn decode_sig64(s: &str) -> Option<[u8; 64]> {
    let s = s.trim();
    if s.len() != 128 || !s.is_ascii() {
        return None;
    }
    let mut out = [0u8; 64];
    for (i, chunk) in s.as_bytes().chunks_exact(2).enumerate() {
        let hi = (chunk[0] as char).to_digit(16)?;
        let lo = (chunk[1] as char).to_digit(16)?;
        out[i] = ((hi << 4) | lo) as u8;
    }
    Some(out)
}

fn logout(cfg: &WebAuthConfig) -> Vec<u8> {
    let cookie = clear_cookie(&cfg.cookie_name, cfg.cookie_domain.as_deref());
    let loc = format!("{}/login", cfg.login_base);
    redirect(302, &loc, &[("Set-Cookie".to_string(), cookie)])
}

/// Only allow same-site relative redirects (defeat open-redirect via `rd`).
fn safe_redirect(rd: &str) -> String {
    if rd.starts_with('/') && !rd.starts_with("//") {
        rd.to_string()
    } else {
        "/".to_string()
    }
}

// ---------------------------------------------------------------------------
// Cookie + response helpers
// ---------------------------------------------------------------------------

fn set_cookie(name: &str, value: &str, domain: Option<&str>, max_age: u64) -> String {
    // HttpOnly (no JS read) + Secure (TLS only) + SameSite=Lax (no cross-site
    // send) + a bounded Max-Age so the browser session self-expires even if the
    // credential itself carries a longer life.
    let mut c =
        format!("{name}={value}; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age={max_age}");
    if let Some(d) = domain {
        c.push_str(&format!("; Domain={d}"));
    }
    c
}

fn clear_cookie(name: &str, domain: Option<&str>) -> String {
    let mut c = format!("{name}=; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age=0");
    if let Some(d) = domain {
        c.push_str(&format!("; Domain={d}"));
    }
    c
}

fn text(status: u16, body: &str) -> Vec<u8> {
    response(status, "text/plain; charset=utf-8", body, &[])
}

fn redirect(status: u16, location: &str, extra: &[(String, String)]) -> Vec<u8> {
    let mut headers = vec![("Location".to_string(), location.to_string())];
    headers.extend_from_slice(extra);
    response(status, "text/plain; charset=utf-8", "redirecting", &headers)
}

fn response(status: u16, content_type: &str, body: &str, headers: &[(String, String)]) -> Vec<u8> {
    let reason = status_reason(status);
    let mut out = format!("HTTP/1.1 {status} {reason}\r\n");
    out.push_str(&format!("Content-Type: {content_type}\r\n"));
    out.push_str(&format!("Content-Length: {}\r\n", body.len()));
    out.push_str("Connection: close\r\n");
    for (k, v) in headers {
        out.push_str(&format!("{k}: {v}\r\n"));
    }
    out.push_str("\r\n");
    let mut bytes = out.into_bytes();
    bytes.extend_from_slice(body.as_bytes());
    bytes
}

fn status_reason(status: u16) -> &'static str {
    match status {
        200 => "OK",
        302 => "Found",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        404 => "Not Found",
        _ => "Status",
    }
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
        .replace('\'', "&#39;")
}

fn url_encode(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for &b in s.as_bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'_' | b'.' | b'~' | b'/' => {
                out.push(b as char)
            }
            _ => out.push_str(&format!("%{b:02X}")),
        }
    }
    out
}

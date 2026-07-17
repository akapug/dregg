//! **The reqwest-backed [`HttpPost`] — the ONE place this crate touches the real network.**
//!
//! Everything above the [`HttpPost`] byte seam is pure ([`crate::transport::RawBotApi`] composes
//! URLs + JSON bodies; the [`crate::runtime`] loop composes `getUpdates` calls); this module fills
//! the seam with a thin blocking reqwest POST so a real deploy can talk to
//! `https://api.telegram.org`. It mirrors the `dregg-ipfs` `StdHttpPost` shape (a dependency-thin
//! transport under an injected trait) with reqwest + rustls because the Bot API requires TLS.
//!
//! Blocking on purpose: the runtime shell is ONE synchronous long-poll loop (`getUpdates` with a
//! server-held timeout) — no tokio, no async plumbing, nothing for the verified core to absorb.

use std::time::Duration;

use crate::transport::HttpPost;

/// How long the HTTP client waits for a response. The Bot API holds a `getUpdates` long-poll open
/// for up to [`crate::runtime::POLL_TIMEOUT_SECS`] (50s), so the client timeout sits safely above
/// it — a genuinely dead connection still errors out instead of hanging forever.
const HTTP_TIMEOUT: Duration = Duration::from_secs(70);

/// **A blocking reqwest [`HttpPost`]** — POSTs a JSON body, returns the response body verbatim
/// (the Bot API answers errors as `{"ok":false,"description":…}` JSON with a non-2xx status, so
/// the body is returned regardless of status and the envelope parser above decides). Cheaply
/// [`Clone`] (a reqwest `Client` is an `Arc` inside), so the send transport and the update-poll
/// client share one connection pool.
///
/// Error strings NEVER include the request URL: a Bot API URL carries the bot token
/// (`/bot<token>/…`), and an error that echoed it would leak the token into logs/journal.
#[derive(Clone, Debug)]
pub struct ReqwestHttpPost {
    client: reqwest::blocking::Client,
}

impl ReqwestHttpPost {
    /// A client with the long-poll-safe timeout. Errors only if the TLS backend fails to
    /// initialize (a broken build environment, not a runtime condition).
    pub fn new() -> Result<Self, String> {
        let client = reqwest::blocking::Client::builder()
            .timeout(HTTP_TIMEOUT)
            .build()
            .map_err(|e| format!("build the HTTP client: {e}"))?;
        Ok(ReqwestHttpPost { client })
    }
}

impl HttpPost for ReqwestHttpPost {
    fn post_json(&self, url: &str, body: &str) -> Result<String, String> {
        let resp = self
            .client
            .post(url)
            .header(reqwest::header::CONTENT_TYPE, "application/json")
            .body(body.to_string())
            .send()
            // `without_url()`: the URL embeds the bot token — never let it reach a log line.
            .map_err(|e| format!("telegram POST failed: {}", e.without_url()))?;
        resp.text()
            .map_err(|e| format!("read telegram response body: {}", e.without_url()))
    }
}

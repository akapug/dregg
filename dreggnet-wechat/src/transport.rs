//! **The INJECTED transport seam** — the ONLY thing that touches the network. All frontend logic
//! (identity, Surface→numbered reply, reply→Action) is built against this trait, so it is fully
//! driven in a test with [`MockTransport`]: NO access-token, NO network. This mirrors the telegram
//! frontend's pure/live split — the [`crate::api`] request builders are pure; a `Transport` is the
//! live edge.
//!
//! Two levels of injection are provided:
//! - [`Transport`] — the logic seam. [`MockTransport`] records every [`CustomSendRequest`] and
//!   acknowledges success; the driven test asserts against the recorded requests.
//! - [`HttpPost`] — the byte seam under the live [`RawWeChatApi`]: `RawWeChatApi` still does PURE
//!   work (compose the `custom/send?access_token=…` URL + the JSON body) and delegates only the raw
//!   POST to an injected [`HttpPost`]. A real deploy supplies a reqwest-backed `HttpPost` + a valid
//!   access-token; a test could supply a recording `HttpPost`. So even the "live" client stays
//!   token/network-free until its byte seam is filled (honest scope).

use crate::api::CustomSendRequest;

/// A transport error (a WeChat API error, a network failure, or a mock-configured failure).
#[derive(Debug, Clone)]
pub struct TransportError(pub String);

impl std::fmt::Display for TransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "wechat transport error: {}", self.0)
    }
}

impl std::error::Error for TransportError {}

/// **The transport seam.** Sends a [`CustomSendRequest`] to WeChat. Unlike Telegram's `sendMessage`
/// (which returns a `message_id`), WeChat's `custom/send` returns only `{errcode, errmsg}` — there
/// is no server message id to edit later — so a successful send is just `Ok(())`. Frontend logic is
/// generic over this; the test drives it with [`MockTransport`].
pub trait Transport {
    /// Send a `custom/send` request. `Ok(())` on `errcode == 0`; `Err` otherwise.
    fn send_message(&mut self, req: &CustomSendRequest) -> Result<(), TransportError>;
}

/// **A recording, network-free transport** — the frontend-agnostic proof for WeChat. It records
/// every [`CustomSendRequest`] it was asked to send (so a test asserts the exact request shape:
/// touser, msgtype, the numbered-reply text content) and acknowledges success. NO access-token, NO
/// HTTP — the same role [`dreggnet_offerings::mock::MockFrontend`] plays for the core, one layer
/// down at the transport.
#[derive(Debug, Default)]
pub struct MockTransport {
    /// Every request sent, in order (the wire bodies a live OA would POST).
    pub sent: Vec<CustomSendRequest>,
    /// If set, the next `send_message` fails with this reason (to drive the error path).
    fail_next: Option<String>,
}

impl MockTransport {
    /// A fresh recording transport with nothing sent.
    pub fn new() -> Self {
        MockTransport {
            sent: Vec::new(),
            fail_next: None,
        }
    }

    /// The last request sent, if any (the current surface a session shows).
    pub fn last(&self) -> Option<&CustomSendRequest> {
        self.sent.last()
    }

    /// Arm the next `send_message` to fail (drives the [`TransportError`] path in a test).
    pub fn fail_next(&mut self, why: impl Into<String>) {
        self.fail_next = Some(why.into());
    }
}

impl Transport for MockTransport {
    fn send_message(&mut self, req: &CustomSendRequest) -> Result<(), TransportError> {
        if let Some(why) = self.fail_next.take() {
            return Err(TransportError(why));
        }
        self.sent.push(req.clone());
        Ok(())
    }
}

/// **The raw byte seam under the live client.** A live [`RawWeChatApi`] composes the request URL +
/// JSON body purely, and delegates only the raw POST to this. A real deploy fills it with reqwest;
/// this crate ships no HTTP dependency, keeping the whole thing token/network-free by default.
pub trait HttpPost {
    /// POST `body` (a JSON string) to `url`; return the response body (JSON) or an error string.
    fn post_json(&self, url: &str, body: &str) -> Result<String, String>;
}

/// **A live-shaped WeChat API client** — composes the real `https://api.weixin.qq.com/cgi-bin/
/// message/custom/send?access_token=<TOKEN>` URL and the JSON body (both PURE), then delegates the
/// raw POST to an injected [`HttpPost`]. It parses the WeChat envelope (`{ errcode, errmsg }`). With
/// a reqwest-backed `HttpPost` + a valid access-token this is a working transport; with no
/// `HttpPost` impl it cannot reach the network — the injection point where "needs a live token/cert"
/// lives (WeChat access-tokens are themselves fetched from `cgi-bin/token` with the OA
/// AppID/AppSecret, and refreshed ~every 2h; that fetch is out of scope for this pure/logic layer).
pub struct RawWeChatApi<H: HttpPost> {
    access_token: String,
    base_url: String,
    http: H,
}

impl<H: HttpPost> RawWeChatApi<H> {
    /// A live client bearing `access_token`, POSTing through `http`. `base_url` defaults to the
    /// public WeChat API host; a proxy / test double passes its own.
    pub fn new(access_token: impl Into<String>, http: H) -> Self {
        RawWeChatApi {
            access_token: access_token.into(),
            base_url: "https://api.weixin.qq.com".to_string(),
            http,
        }
    }

    /// Override the WeChat API host (a proxy, or a test double).
    pub fn with_base_url(mut self, base_url: impl Into<String>) -> Self {
        self.base_url = base_url.into();
        self
    }

    /// The `custom/send` endpoint URL (pure). Token-bearing (the access-token is a query param, as
    /// WeChat requires), so kept private-ish to this client.
    fn custom_send_url(&self) -> String {
        format!(
            "{}/cgi-bin/message/custom/send?access_token={}",
            self.base_url, self.access_token
        )
    }
}

impl<H: HttpPost> Transport for RawWeChatApi<H> {
    fn send_message(&mut self, req: &CustomSendRequest) -> Result<(), TransportError> {
        let url = self.custom_send_url();
        let body = serde_json::to_string(req)
            .map_err(|e| TransportError(format!("encode custom/send body: {e}")))?;
        let resp = self.http.post_json(&url, &body).map_err(TransportError)?;
        // The WeChat envelope: { "errcode": 0, "errmsg": "ok" }. A missing errcode is treated as
        // success (some endpoints omit it on ok); a non-zero errcode is the error.
        let v: serde_json::Value = serde_json::from_str(&resp)
            .map_err(|e| TransportError(format!("decode WeChat response: {e}")))?;
        let errcode = v.get("errcode").and_then(|c| c.as_i64()).unwrap_or(0);
        if errcode != 0 {
            let errmsg = v
                .get("errmsg")
                .and_then(|m| m.as_str())
                .unwrap_or("WeChat returned a non-zero errcode");
            return Err(TransportError(format!("errcode {errcode}: {errmsg}")));
        }
        Ok(())
    }
}

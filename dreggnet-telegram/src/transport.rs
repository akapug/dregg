//! **The INJECTED transport seam** — the ONLY thing that touches the network. All frontend logic
//! (identity, Surface→keyboard, callback→Action) is built against this trait, so it is fully
//! driven in a test with [`MockTransport`]: NO token, NO network. This mirrors the discord-bot's
//! pure/live split — the [`crate::api`] request builders are pure; a `Transport` is the live edge.
//!
//! Two levels of injection are provided:
//! - [`Transport`] — the logic seam. [`MockTransport`] records every [`SendMessageRequest`] and
//!   hands back synthetic message ids; the driven test asserts against the recorded requests.
//! - [`HttpPost`] — the byte seam under the live [`RawBotApi`]: `RawBotApi` still does PURE work
//!   (compose the `bot<token>/sendMessage` URL + the JSON body) and delegates only the raw POST to
//!   an injected [`HttpPost`]. A real deploy supplies a reqwest-backed `HttpPost` + a token; a test
//!   could supply a recording `HttpPost`. So even the "live" client stays token/network-free until
//!   its byte seam is filled (honest scope).

use crate::api::SendMessageRequest;

/// A sent message's server-assigned id (the Bot API `message_id`) — held so a re-present can EDIT
/// the message in place (`editMessageText`) rather than spamming a new one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MessageId(pub i64);

/// A transport error (a Bot API error, a network failure, or a mock-configured failure).
#[derive(Debug, Clone)]
pub struct TransportError(pub String);

impl std::fmt::Display for TransportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "telegram transport error: {}", self.0)
    }
}

impl std::error::Error for TransportError {}

/// **The transport seam.** Sends a [`SendMessageRequest`] to Telegram and returns the new
/// message's id. Frontend logic is generic over this; the test drives it with [`MockTransport`].
pub trait Transport {
    /// Send a `sendMessage` request, returning the created message's id.
    fn send_message(&mut self, req: &SendMessageRequest) -> Result<MessageId, TransportError>;

    /// EDIT a previously sent message in place (`editMessageText`) to show `req`'s text +
    /// keyboard — how a re-present keeps ONE live surface message per session instead of
    /// spamming the chat. **Default: fall back to sending a NEW message** — a transport that
    /// cannot edit (the recording [`MockTransport`], a minimal impl) still presents the current
    /// surface, and the frontend records whichever message id came back. [`RawBotApi`]
    /// overrides this with the real `editMessageText` call.
    fn edit_message(
        &mut self,
        message_id: MessageId,
        req: &SendMessageRequest,
    ) -> Result<MessageId, TransportError> {
        let _ = message_id;
        self.send_message(req)
    }
}

/// **A recording, network-free transport** — the frontend-agnostic proof for Telegram. It records
/// every [`SendMessageRequest`] it was asked to send (so a test asserts the exact request shape:
/// chat id, text, the inline-keyboard payload) and hands back monotonically increasing synthetic
/// message ids. NO token, NO HTTP — the same role [`dreggnet_offerings::mock::MockFrontend`] plays
/// for the core, one layer down at the transport.
#[derive(Debug, Default)]
pub struct MockTransport {
    /// Every request sent, in order (the wire bodies a live bot would POST).
    pub sent: Vec<SendMessageRequest>,
    /// The next synthetic message id to hand out.
    next_id: i64,
    /// If set, the next `send_message` fails with this reason (to drive the error path).
    fail_next: Option<String>,
}

impl MockTransport {
    /// A fresh recording transport with nothing sent.
    pub fn new() -> Self {
        MockTransport {
            sent: Vec::new(),
            next_id: 1,
            fail_next: None,
        }
    }

    /// The last request sent, if any (the current surface a session shows).
    pub fn last(&self) -> Option<&SendMessageRequest> {
        self.sent.last()
    }

    /// Arm the next `send_message` to fail (drives the [`TransportError`] path in a test).
    pub fn fail_next(&mut self, why: impl Into<String>) {
        self.fail_next = Some(why.into());
    }
}

impl Transport for MockTransport {
    fn send_message(&mut self, req: &SendMessageRequest) -> Result<MessageId, TransportError> {
        if let Some(why) = self.fail_next.take() {
            return Err(TransportError(why));
        }
        self.sent.push(req.clone());
        let id = self.next_id;
        self.next_id += 1;
        Ok(MessageId(id))
    }
}

/// **The raw byte seam under the live client.** A live [`RawBotApi`] composes the request URL +
/// JSON body purely, and delegates only the raw POST to this. A real deploy fills it with reqwest;
/// this crate ships no HTTP dependency, keeping the whole thing token/network-free by default.
pub trait HttpPost {
    /// POST `body` (a JSON string) to `url`; return the response body (JSON) or an error string.
    fn post_json(&self, url: &str, body: &str) -> Result<String, String>;
}

/// **A live-shaped Bot API client** — composes the real `https://api.telegram.org/bot<token>/
/// sendMessage` URL and the JSON body (both PURE), then delegates the raw POST to an injected
/// [`HttpPost`]. It parses the Bot API envelope (`{ ok, result: { message_id } }`). With a
/// reqwest-backed `HttpPost` + a real token this is a working transport; with no `HttpPost` impl
/// it cannot reach the network — the injection point where "needs a live token" lives.
pub struct RawBotApi<H: HttpPost> {
    token: String,
    base_url: String,
    http: H,
}

impl<H: HttpPost> RawBotApi<H> {
    /// A live client for `token`, POSTing through `http`. `base_url` defaults to the public Bot
    /// API host; a self-hosted Bot API server passes its own.
    pub fn new(token: impl Into<String>, http: H) -> Self {
        RawBotApi {
            token: token.into(),
            base_url: "https://api.telegram.org".to_string(),
            http,
        }
    }

    /// Override the Bot API host (a local Bot API server, or a test double).
    pub fn with_base_url(mut self, base_url: impl Into<String>) -> Self {
        self.base_url = base_url.into();
        self
    }

    /// The `sendMessage` endpoint URL (pure). Token-bearing, so kept private-ish to this client.
    fn method_url(&self, method: &str) -> String {
        format!("{}/bot{}/{}", self.base_url, self.token, method)
    }
}

impl<H: HttpPost> Transport for RawBotApi<H> {
    fn send_message(&mut self, req: &SendMessageRequest) -> Result<MessageId, TransportError> {
        let url = self.method_url("sendMessage");
        let body = serde_json::to_string(req)
            .map_err(|e| TransportError(format!("encode sendMessage body: {e}")))?;
        let resp = self.http.post_json(&url, &body).map_err(TransportError)?;
        // The Bot API envelope: { "ok": true, "result": { "message_id": N, ... } }.
        let v: serde_json::Value = serde_json::from_str(&resp)
            .map_err(|e| TransportError(format!("decode Bot API response: {e}")))?;
        if v.get("ok").and_then(|b| b.as_bool()) != Some(true) {
            let desc = v
                .get("description")
                .and_then(|d| d.as_str())
                .unwrap_or("Bot API returned ok=false");
            return Err(TransportError(desc.to_string()));
        }
        let message_id = v
            .get("result")
            .and_then(|r| r.get("message_id"))
            .and_then(|m| m.as_i64())
            .ok_or_else(|| TransportError("Bot API response missing message_id".to_string()))?;
        Ok(MessageId(message_id))
    }

    /// The real `editMessageText`: the same pure composition (URL + the `sendMessage` body plus
    /// the `message_id` field — `editMessageText` takes a superset of the fields), the same
    /// injected [`HttpPost`]. Telegram refuses a NO-OP edit (`"message is not modified"`); that
    /// is an identical re-present, not a failure, so it maps to `Ok` with the message kept.
    fn edit_message(
        &mut self,
        message_id: MessageId,
        req: &SendMessageRequest,
    ) -> Result<MessageId, TransportError> {
        let url = self.method_url("editMessageText");
        let mut body = serde_json::to_value(req)
            .map_err(|e| TransportError(format!("encode editMessageText body: {e}")))?;
        body.as_object_mut()
            .expect("a SendMessageRequest serializes to a JSON object")
            .insert("message_id".to_string(), serde_json::json!(message_id.0));
        let resp = self
            .http
            .post_json(&url, &body.to_string())
            .map_err(TransportError)?;
        let v: serde_json::Value = serde_json::from_str(&resp)
            .map_err(|e| TransportError(format!("decode Bot API response: {e}")))?;
        if v.get("ok").and_then(|b| b.as_bool()) != Some(true) {
            let desc = v
                .get("description")
                .and_then(|d| d.as_str())
                .unwrap_or("Bot API returned ok=false");
            // An identical re-present: the message already shows this exact surface. Keep it.
            if desc.contains("message is not modified") {
                return Ok(message_id);
            }
            return Err(TransportError(desc.to_string()));
        }
        // The edited message keeps its id (the `result` echoes the same message).
        Ok(message_id)
    }
}

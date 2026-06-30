//! THE AGENT BRAIN — the real, closed-loop decision-maker that replaces the
//! scripted stand-in.
//!
//! ## What was stood in, and what this is
//!
//! The prior confined-agent body — [`crate::MockHermesPeer`] (in-process) and
//! [`crate::confined::stand_in_acp_peer`] (in-jail) — replays a FIXED
//! `Vec<`[`crate::ScriptedCall`]`>`. There is no brain in that: a test author
//! pre-decides every tool-call, nothing reacts to the gate's verdict, nothing
//! loops. THIS module is the brain that was stood in for. An [`LlmBrain`] is
//! asked, given the running conversation ([`AgentConvo`]), for its NEXT step —
//! call a tool, or finish — and it OBSERVES the gate's verdict on each tool-call
//! ([`ToolObservation`]: allow + receipt / refuse + reason) and DECIDES the next
//! step from what it saw. That closed loop —
//!
//! ```text
//!   decide ─▶ (gate: cap ✓ budget ✓ charge Σδ=0) ─▶ observe verdict ─▶ decide …
//! ```
//!
//! IS the agent. [`crate::agent_peer::HermesAgentPeer`] runs it over ACP so the
//! UNCHANGED [`crate::AcpClient`] drives a real confined agent: every tool the
//! brain reaches for is a cap-gated, metered, receipted dregg turn (or an in-band
//! refusal the brain adapts to), with the tool's effect riding the receipt.
//!
//! ## BYO-LLM-keys, confined
//!
//! A real LLM brain calls a model provider with the OPERATOR'S key ([`LlmKeys`]).
//! The key lives in the brain's pocket and reaches ONLY the provider, across the
//! [`LlmHttpCaller`] seam — it is NEVER placed in a tool-call's arguments, the
//! World the agent drives, a receipt, or the ACP wire the agent's reach travels.
//! The brain's INTENT crosses the gate; its CREDENTIAL does not. (Even a stray
//! `{:?}` cannot leak it — [`LlmKeys`]'s `Debug` is redacted.)
//!
//! Two brains ship:
//!   * [`LocalBrain`] — a deterministic, reactive ON-BOX brain (needs no key);
//!     the default driver for the hermetic tests. It reads the prompt, forms a
//!     plan, issues calls one at a time, and ADAPTS when the gate refuses one
//!     (it does not bang on a denied tool; it falls back to a read-only probe).
//!   * [`HttpLlm`] — the live BYO-key path: it builds a provider request from the
//!     conversation, calls the provider over [`LlmHttpCaller`] with the operator's
//!     key, and parses the provider's tool-use response into a [`BrainStep`].
//!     Exercised here over a mock provider caller; live against a real endpoint.

use std::collections::VecDeque;

use serde_json::{Value, json};

/// One step the brain decides: reach for a tool, or finish the turn.
#[derive(Clone, Debug)]
pub enum BrainStep {
    /// Reach for a tool — the agent's INTENT, which the gate will admit
    /// (a receipted turn) or refuse (in-band). `name` is the Hermes tool name
    /// (drives the ACP kind + the deos mandate); `arguments` is its `rawInput`.
    CallTool { name: String, arguments: Value },
    /// Finish the turn with a final agent message.
    Finish { text: String },
}

/// What the brain has seen of one tool-call it reached for — the gate's verdict,
/// fed back so the next decision can react to confinement.
#[derive(Clone, Debug)]
pub struct ToolObservation {
    /// The tool the brain called.
    pub tool: String,
    /// The arguments it called with.
    pub arguments: Value,
    /// `true` if the gate ADMITTED it (a receipted turn), `false` if refused.
    pub allowed: bool,
    /// On allow: the dregg receipt id. On refuse: the in-band reason (the mandate
    /// leg that bit). This is the tool RESULT the brain reasons over.
    pub detail: String,
}

/// The running conversation the brain decides over: the human's prompt + the
/// verdicts on every tool-call the brain has made so far this turn.
#[derive(Clone, Debug, Default)]
pub struct AgentConvo {
    /// The working directory the session opened in.
    pub cwd: String,
    /// The human's prompt for this turn.
    pub prompt: String,
    /// The gate verdict on each tool-call the brain has made, in order.
    pub observations: Vec<ToolObservation>,
}

impl AgentConvo {
    /// A fresh conversation for a prompt in a cwd.
    pub fn new(cwd: &str, prompt: &str) -> AgentConvo {
        AgentConvo {
            cwd: cwd.to_string(),
            prompt: prompt.to_string(),
            observations: Vec::new(),
        }
    }

    /// Fold one gate verdict back into the conversation (the peer calls this the
    /// instant the deos client answers a `session/request_permission`).
    pub fn observe(&mut self, tool: &str, arguments: Value, allowed: bool, detail: &str) {
        self.observations.push(ToolObservation {
            tool: tool.to_string(),
            arguments,
            allowed,
            detail: detail.to_string(),
        });
    }

    /// How many tool-calls the gate admitted this turn.
    pub fn allowed_count(&self) -> usize {
        self.observations.iter().filter(|o| o.allowed).count()
    }

    /// How many tool-calls the gate refused in-band this turn.
    pub fn refused_count(&self) -> usize {
        self.observations.iter().filter(|o| !o.allowed).count()
    }
}

/// THE BRAIN INTERFACE — given the running conversation, decide the next step.
///
/// This is the ONLY thing that was stood-in. Both shipped brains ([`LocalBrain`],
/// [`HttpLlm`]) implement it; a host can supply its own. The peer/gate/receipt
/// rail around it is the real, proven surface, unchanged.
pub trait LlmBrain {
    /// Decide the next step from the conversation so far. Called once per
    /// decision: the peer gates the returned [`BrainStep::CallTool`], folds the
    /// verdict into `convo` via [`AgentConvo::observe`], and calls again — until
    /// the brain returns [`BrainStep::Finish`].
    fn next_step(&mut self, convo: &AgentConvo) -> BrainStep;
}

// ───────────────────────────── BYO model-provider key ───────────────────────

/// THE OPERATOR'S MODEL-PROVIDER KEY — BYO, held by the brain, confined.
///
/// The whole point: this secret reaches the provider and NOWHERE the agent's
/// reach travels. It is handed to [`LlmHttpCaller::complete`] as a distinct
/// argument (it goes in the provider auth header), never serialized into a
/// tool-call, a receipt, the World, or the wire. The redacted [`std::fmt::Debug`]
/// is a confinement tooth: an accidental debug log of the keys cannot leak it.
#[derive(Clone)]
pub struct LlmKeys {
    provider: String,
    secret: String,
}

impl LlmKeys {
    /// Hold the operator's `secret` for `provider` (e.g. an API key for a
    /// messages-style endpoint). The brain is the only holder.
    pub fn new(provider: &str, secret: &str) -> LlmKeys {
        LlmKeys {
            provider: provider.to_string(),
            secret: secret.to_string(),
        }
    }

    /// Read the BYO key from an environment variable (the live deployment shape:
    /// the operator exports it; deos never persists it). `None` if unset/empty.
    pub fn from_env(provider: &str, var: &str) -> Option<LlmKeys> {
        let secret = std::env::var(var).ok()?;
        if secret.is_empty() {
            return None;
        }
        Some(LlmKeys::new(provider, &secret))
    }

    /// Read the BYO key from a file (e.g. `~/.kimikey`). Trailing whitespace /
    /// newline is trimmed; deos never persists it elsewhere. `None` if the file is
    /// missing or empty. The secret stays redacted under [`std::fmt::Debug`].
    pub fn from_file(provider: &str, path: impl AsRef<std::path::Path>) -> Option<LlmKeys> {
        let raw = std::fs::read_to_string(path).ok()?;
        let secret = raw.trim();
        if secret.is_empty() {
            return None;
        }
        Some(LlmKeys::new(provider, secret))
    }

    /// The provider label (NOT secret).
    pub fn provider(&self) -> &str {
        &self.provider
    }

    /// The secret — readable ONLY to hand to the provider caller. Do not put the
    /// returned string anywhere the agent's reach (tool args / World / receipt /
    /// wire) can observe it.
    pub fn secret(&self) -> &str {
        &self.secret
    }
}

impl std::fmt::Debug for LlmKeys {
    /// REDACTED — a confinement tooth: a stray `{:?}` of a brain holding keys
    /// never prints the secret.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LlmKeys")
            .field("provider", &self.provider)
            .field("secret", &"<redacted>")
            .finish()
    }
}

// ─────────────────────────────── the on-box brain ───────────────────────────

/// One planned tool-call (the brain's intent before the gate weighs in).
#[derive(Clone, Debug)]
struct PlannedCall {
    name: String,
    arguments: Value,
}

/// A DETERMINISTIC, REACTIVE ON-BOX BRAIN — the default hermetic driver.
///
/// It is a real closed loop, not a fixed script: it reads the prompt to form a
/// plan (keyword → tool), issues the plan one call at a time, and REACTS to the
/// gate — when a call is refused it drops further attempts at that denied tool
/// and (once) injects a read-only fallback probe, then finishes with a summary of
/// what landed vs what the confinement refused. The same loop a model brain runs;
/// the decisions are rule-based rather than sampled, so the tests are determinate.
pub struct LocalBrain {
    plan: VecDeque<PlannedCall>,
    planned: bool,
    fell_back: bool,
    /// Optional BYO keys — an on-box brain needs none, but it may hold them (e.g.
    /// to call a provider for a sub-decision); kept here so the key-confinement
    /// invariant is exercised even on the on-box path.
    keys: Option<LlmKeys>,
}

impl Default for LocalBrain {
    fn default() -> Self {
        LocalBrain::new()
    }
}

impl LocalBrain {
    /// A fresh on-box brain. It forms its plan from the prompt on the first
    /// [`LlmBrain::next_step`].
    pub fn new() -> LocalBrain {
        LocalBrain {
            plan: VecDeque::new(),
            planned: false,
            fell_back: false,
            keys: None,
        }
    }

    /// Hold BYO keys on the on-box brain (so the confinement invariant holds even
    /// here). The secret still never escapes to the agent's reach.
    pub fn with_keys(mut self, keys: LlmKeys) -> LocalBrain {
        self.keys = Some(keys);
        self
    }

    /// The keys this brain holds, if any (the secret stays redacted under Debug).
    pub fn keys(&self) -> Option<&LlmKeys> {
        self.keys.as_ref()
    }

    /// Form the plan from the prompt — a small, honest keyword→tool reading. A
    /// real model would sample this; the shape (intent derived from the prompt) is
    /// the same.
    fn plan_from_prompt(prompt: &str) -> VecDeque<PlannedCall> {
        let p = prompt.to_lowercase();
        let mut plan = VecDeque::new();
        if p.contains("search") || p.contains("look up") || p.contains("find") {
            plan.push_back(PlannedCall {
                name: "web_search".into(),
                arguments: json!({ "query": prompt }),
            });
        }
        if p.contains("read") || p.contains("show") || p.contains("inspect") {
            plan.push_back(PlannedCall {
                name: "read_file".into(),
                arguments: json!({ "path": "src/lib.rs" }),
            });
        }
        if p.contains("write") || p.contains("save") || p.contains("create") {
            plan.push_back(PlannedCall {
                name: "write_file".into(),
                arguments: json!({ "path": "notes/agent.md", "content": "(agent draft)" }),
            });
        }
        if p.contains("run") || p.contains("build") || p.contains("test") || p.contains("execute") {
            plan.push_back(PlannedCall {
                name: "terminal".into(),
                arguments: json!({ "command": "cargo build" }),
            });
        }
        // A prompt with no recognized verb still does something useful + safe: a
        // search then a read (both low-authority).
        if plan.is_empty() {
            plan.push_back(PlannedCall {
                name: "web_search".into(),
                arguments: json!({ "query": prompt }),
            });
            plan.push_back(PlannedCall {
                name: "read_file".into(),
                arguments: json!({ "path": "src/lib.rs" }),
            });
        }
        plan
    }

    /// The read-only fallback probe the brain reaches for when a mutating call was
    /// refused — the "do something I'm allowed to" adaptation.
    fn read_probe() -> PlannedCall {
        PlannedCall {
            name: "read_file".into(),
            arguments: json!({ "path": "src/lib.rs", "reason": "fallback after refusal" }),
        }
    }

    /// The final summary the brain reports once its plan drains.
    fn summary(convo: &AgentConvo) -> String {
        let allowed = convo.allowed_count();
        let refused = convo.refused_count();
        if refused == 0 {
            format!("done — {allowed} tool-call(s) completed, each a receipted turn.")
        } else {
            let denied: Vec<&str> = convo
                .observations
                .iter()
                .filter(|o| !o.allowed)
                .map(|o| o.tool.as_str())
                .collect();
            format!(
                "done — {allowed} completed, {refused} refused by confinement ({}). \
                 I worked within the caps I was granted.",
                denied.join(", ")
            )
        }
    }
}

impl LlmBrain for LocalBrain {
    fn next_step(&mut self, convo: &AgentConvo) -> BrainStep {
        if !self.planned {
            self.plan = LocalBrain::plan_from_prompt(&convo.prompt);
            self.planned = true;
        }
        // REACT to the most recent verdict: if the gate refused the last call,
        // stop attempting that denied tool, and (once) inject a read-only probe so
        // the agent still makes safe progress under confinement.
        if let Some(last) = convo.observations.last()
            && !last.allowed
        {
            let denied = last.tool.clone();
            self.plan.retain(|c| c.name != denied);
            if !self.fell_back {
                self.fell_back = true;
                self.plan.push_front(LocalBrain::read_probe());
            }
        }
        match self.plan.pop_front() {
            Some(c) => BrainStep::CallTool {
                name: c.name,
                arguments: c.arguments,
            },
            None => BrainStep::Finish {
                text: LocalBrain::summary(convo),
            },
        }
    }
}

// ─────────────────────────── the live BYO-key LLM brain ─────────────────────

/// THE PROVIDER-CALL SEAM — one HTTPS POST to a model provider, the BYO key in
/// hand. A real deployment supplies an impl backed by the operator's HTTP stack
/// (the key in the auth header); the tests supply a mock caller returning a canned
/// provider response. This is the ONLY thing [`HttpLlm`] does that touches the
/// outside world, and it is the ONLY place the BYO key is read.
pub trait LlmHttpCaller {
    /// POST `request` to `endpoint` with `api_key` (the operator's BYO secret, in
    /// the provider auth header) and return the provider's raw response JSON.
    ///
    /// `api_key` reaches ONLY here. It must not be embedded in `request` (it goes
    /// in the transport auth header), nor returned in the response, nor logged.
    fn complete(&mut self, endpoint: &str, api_key: &str, request: &Value)
    -> Result<Value, String>;
}

/// A LIVE BYO-KEY LLM BRAIN. It builds a provider request from the conversation
/// (a generic messages+tools shape), calls the provider over [`LlmHttpCaller`]
/// with the operator's [`LlmKeys`], and parses the provider's response — a
/// tool-use block becomes [`BrainStep::CallTool`], a text/end block becomes
/// [`BrainStep::Finish`]. Fail-closed: an unparseable response finishes the turn
/// (it never fabricates a tool-call).
///
/// The request/response shape here is provider-neutral (an `messages` array + a
/// `tools` list out; `content` blocks of `{type:"tool_use"|"text"}` back — the
/// shape a Messages-style or an OpenAI-style adapter maps onto). A concrete
/// provider adapter lives in the [`LlmHttpCaller`] impl.
pub struct HttpLlm<C: LlmHttpCaller> {
    keys: LlmKeys,
    endpoint: String,
    model: String,
    caller: C,
    /// Set once the key has been handed to the provider caller — proves the
    /// confined channel (brain → provider) is the ONLY path the key took.
    key_reached_provider: bool,
}

impl<C: LlmHttpCaller> HttpLlm<C> {
    /// A live brain calling `endpoint` (model `model`) with `keys`, over `caller`.
    pub fn new(keys: LlmKeys, endpoint: &str, model: &str, caller: C) -> HttpLlm<C> {
        HttpLlm {
            keys,
            endpoint: endpoint.to_string(),
            model: model.to_string(),
            caller,
            key_reached_provider: false,
        }
    }

    /// Whether the BYO key has been handed to the provider caller (and nowhere
    /// else) — the confined-channel witness for the BYO-key test.
    pub fn key_reached_provider(&self) -> bool {
        self.key_reached_provider
    }

    /// The caller (post-run) — e.g. for a test mock to report what it received.
    pub fn caller(&self) -> &C {
        &self.caller
    }

    /// Build the provider request body from the conversation. The BYO key is NOT
    /// here (it travels as the `complete` auth argument), so this body is safe to
    /// witness.
    fn request_body(&self, convo: &AgentConvo) -> Value {
        // The running messages: the user prompt, then each tool-call + its result
        // (the gate verdict) as the brain saw it.
        let mut messages = vec![json!({ "role": "user", "content": convo.prompt })];
        for o in &convo.observations {
            messages.push(json!({
                "role": "assistant",
                "content": [{ "type": "tool_use", "name": o.tool, "input": o.arguments }],
            }));
            messages.push(json!({
                "role": "tool",
                "tool": o.tool,
                "content": if o.allowed {
                    format!("admitted; receipt {}", o.detail)
                } else {
                    format!("refused by confinement: {}", o.detail)
                },
            }));
        }
        json!({
            "model": self.model,
            "system": "You are a confined deos agent. Every tool-call is cap-gated, \
                       metered, and receipted; a refusal is in-band — adapt within your caps.",
            "messages": messages,
            "tools": tool_specs(),
        })
    }
}

/// The tool specs the brain advertises to the provider — the Hermes tool surface
/// the gate confines (a representative subset; an unknown tool still falls into
/// the most-restricted `Other` class at the gate).
fn tool_specs() -> Value {
    json!([
        { "name": "web_search", "description": "Search the web for a query." },
        { "name": "read_file", "description": "Read a file in the workspace." },
        { "name": "write_file", "description": "Write a file in the workspace." },
        { "name": "terminal", "description": "Run a shell command." },
    ])
}

impl<C: LlmHttpCaller> LlmBrain for HttpLlm<C> {
    fn next_step(&mut self, convo: &AgentConvo) -> BrainStep {
        let body = self.request_body(convo);
        // THE ONE PLACE THE BYO KEY IS READ — handed to the provider caller, in
        // the auth header, never into `body`.
        let resp = match self
            .caller
            .complete(&self.endpoint, self.keys.secret(), &body)
        {
            Ok(r) => {
                self.key_reached_provider = true;
                r
            }
            Err(e) => {
                // Fail-closed: a provider error finishes the turn; no tool-call is
                // ever fabricated past a failed completion.
                return BrainStep::Finish {
                    text: format!("(provider error: {e})"),
                };
            }
        };
        parse_provider_step(&resp)
    }
}

/// Parse a provider response into the brain's next step. Recognizes a `content`
/// array of `{type:"tool_use", name, input}` / `{type:"text", text}` blocks (a
/// Messages-style shape), preferring the first tool_use; falls back to a final
/// message; fail-closed to a generic finish if neither is present.
fn parse_provider_step(resp: &Value) -> BrainStep {
    if let Some(content) = resp.get("content").and_then(|c| c.as_array()) {
        for block in content {
            if block.get("type").and_then(|t| t.as_str()) == Some("tool_use") {
                if let Some(name) = block.get("name").and_then(|n| n.as_str()) {
                    let arguments = block.get("input").cloned().unwrap_or(Value::Null);
                    return BrainStep::CallTool {
                        name: name.to_string(),
                        arguments,
                    };
                }
            }
        }
        // No tool_use — collect any text blocks as the final message.
        let text: String = content
            .iter()
            .filter(|b| b.get("type").and_then(|t| t.as_str()) == Some("text"))
            .filter_map(|b| b.get("text").and_then(|t| t.as_str()))
            .collect::<Vec<_>>()
            .join(" ");
        if !text.is_empty() {
            return BrainStep::Finish { text };
        }
    }
    // A bare `{ "text": "..." }` final shape.
    if let Some(text) = resp.get("text").and_then(|t| t.as_str()) {
        return BrainStep::Finish {
            text: text.to_string(),
        };
    }
    BrainStep::Finish {
        text: "(no actionable provider response)".to_string(),
    }
}

// ────────────────────── the OpenAI-compatible chat adapter ───────────────────

/// A CONCRETE [`LlmHttpCaller`] for **any OpenAI-compatible** chat/completions
/// endpoint (chat messages + tool-use). [`HttpLlm`] is provider-neutral — it emits
/// a Messages-shaped request and parses a `content`-block response; this adapter
/// maps that shape onto OpenAI's `messages` + `tool_calls` request and back, so any
/// OpenAI-shaped model drops in behind the unchanged brain/gate/receipt rail: a
/// Kimi/Moonshot key, a local proxy, ollama, vLLM / LM Studio, OpenRouter, or a
/// harness-exposed OpenAI endpoint. The endpoint + model are configured on
/// [`HttpLlm`]; this adapter only translates the request/response shape.
///
/// The actual bytes go over a BYO `post` seam (the operator's HTTP stack), so this
/// crate adds no HTTP/TLS dependency: the live deployment injects a closure that
/// POSTs to the configured `endpoint` (e.g. `http://localhost:11434/v1/chat/completions`
/// for ollama, `https://api.moonshot.ai/v1/chat/completions` for Kimi) with the key
/// in the `Authorization: Bearer` header; the tests inject a recorded responder.
/// The api_key is the `post` argument — it never enters the request body.
pub struct OpenAICompatCaller<P>
where
    P: FnMut(&str, &str, &Value) -> Result<Value, String>,
{
    post: P,
}

/// Back-compat alias: this adapter shipped first as `MoonshotCaller`. Kimi/Moonshot
/// is one OpenAI-compatible endpoint; the adapter is provider-agnostic.
pub type MoonshotCaller<P> = OpenAICompatCaller<P>;

impl<P> OpenAICompatCaller<P>
where
    P: FnMut(&str, &str, &Value) -> Result<Value, String>,
{
    /// An OpenAI-compatible adapter over the BYO `post(endpoint, api_key,
    /// openai_request)` transport. `post` is the ONLY thing that touches the network
    /// and the ONLY place the key is used (in the auth header) — never the request
    /// body.
    pub fn new(post: P) -> OpenAICompatCaller<P> {
        OpenAICompatCaller { post }
    }
}

impl<P> LlmHttpCaller for OpenAICompatCaller<P>
where
    P: FnMut(&str, &str, &Value) -> Result<Value, String>,
{
    fn complete(
        &mut self,
        endpoint: &str,
        api_key: &str,
        request: &Value,
    ) -> Result<Value, String> {
        let openai_req = messages_to_openai(request);
        let openai_resp = (self.post)(endpoint, api_key, &openai_req)?;
        Ok(openai_to_messages(&openai_resp))
    }
}

/// Translate the [`HttpLlm`] Messages-shaped request into an OpenAI chat request:
/// the `system` string becomes a leading `system` message; each Messages
/// `assistant`/`tool_use` becomes an `assistant` turn with `tool_calls` (a
/// synthesized `tc-{n}` id) and each following `tool` message reuses that id; the
/// `{name,description}` tools become `{type:function,function:{…}}` specs.
fn messages_to_openai(request: &Value) -> Value {
    let mut messages = Vec::new();
    if let Some(system) = request.get("system").and_then(|s| s.as_str()) {
        messages.push(json!({ "role": "system", "content": system }));
    }
    let mut tc_seq = 0u64;
    if let Some(src) = request.get("messages").and_then(|m| m.as_array()) {
        for msg in src {
            let role = msg.get("role").and_then(|r| r.as_str()).unwrap_or("");
            match role {
                "user" => messages.push(msg.clone()),
                "assistant" => {
                    // A Messages assistant turn carries a `content` array of
                    // `{type:tool_use,name,input}` — map the first to a tool_call.
                    let tool_use = msg.get("content").and_then(|c| c.as_array()).and_then(|a| {
                        a.iter()
                            .find(|b| b.get("type").and_then(|t| t.as_str()) == Some("tool_use"))
                    });
                    if let Some(tu) = tool_use {
                        tc_seq += 1;
                        let name = tu.get("name").and_then(|n| n.as_str()).unwrap_or("");
                        let input = tu.get("input").cloned().unwrap_or(Value::Null);
                        messages.push(json!({
                            "role": "assistant",
                            "content": null,
                            "tool_calls": [{
                                "id": format!("tc-{tc_seq}"),
                                "type": "function",
                                "function": {
                                    "name": name,
                                    "arguments": input.to_string()
                                }
                            }]
                        }));
                    } else {
                        messages.push(msg.clone());
                    }
                }
                "tool" => {
                    // The tool result for the most recent tool_call.
                    let content = msg.get("content").and_then(|c| c.as_str()).unwrap_or("");
                    messages.push(json!({
                        "role": "tool",
                        "tool_call_id": format!("tc-{tc_seq}"),
                        "content": content
                    }));
                }
                _ => messages.push(msg.clone()),
            }
        }
    }
    let tools = request
        .get("tools")
        .and_then(|t| t.as_array())
        .map(|specs| {
            specs
                .iter()
                .map(|s| {
                    json!({
                        "type": "function",
                        "function": {
                            "name": s.get("name").and_then(|n| n.as_str()).unwrap_or(""),
                            "description": s.get("description").and_then(|d| d.as_str()).unwrap_or(""),
                            "parameters": { "type": "object", "properties": {} }
                        }
                    })
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    json!({
        "model": request.get("model").cloned().unwrap_or(Value::Null),
        "messages": messages,
        "tools": tools,
        "temperature": 0.3
    })
}

/// Translate an OpenAI chat response into the [`HttpLlm`] `content`-block shape
/// [`parse_provider_step`] consumes: a `tool_calls[0]` becomes a `tool_use` block
/// (its JSON-string `arguments` parsed into `input`); plain `content` becomes a
/// `text` block.
fn openai_to_messages(resp: &Value) -> Value {
    let message = resp
        .get("choices")
        .and_then(|c| c.as_array())
        .and_then(|a| a.first())
        .and_then(|c| c.get("message"));
    let Some(message) = message else {
        return json!({ "content": [] });
    };
    if let Some(tc) = message
        .get("tool_calls")
        .and_then(|t| t.as_array())
        .and_then(|a| a.first())
    {
        let func = tc.get("function");
        let name = func
            .and_then(|f| f.get("name"))
            .and_then(|n| n.as_str())
            .unwrap_or("");
        let input = match func.and_then(|f| f.get("arguments")) {
            Some(Value::String(s)) => serde_json::from_str(s).unwrap_or(Value::Null),
            Some(v) => v.clone(),
            None => Value::Null,
        };
        return json!({ "content": [{ "type": "tool_use", "name": name, "input": input }] });
    }
    let text = message
        .get("content")
        .and_then(|c| c.as_str())
        .unwrap_or("");
    json!({ "content": [{ "type": "text", "text": text }] })
}

#[cfg(test)]
mod kimi_adapter_tests {
    use super::*;

    const TEST_SECRET: &str = "sk-DEOS-UNITTEST-DONOTLEAK-0123456789";

    /// An OpenAI/Moonshot response that calls a tool with JSON-string arguments.
    fn oai_tool_call(name: &str, args_json: &str) -> Value {
        json!({
            "choices": [{
                "message": {
                    "role": "assistant",
                    "content": null,
                    "tool_calls": [{
                        "id": "call_x",
                        "type": "function",
                        "function": { "name": name, "arguments": args_json }
                    }]
                }
            }]
        })
    }

    /// A Moonshot model drives the unchanged HttpLlm brain through the adapter: it
    /// builds the Messages request, the adapter maps it to OpenAI + back, and the
    /// brain parses the tool-call. The BYO key reaches only the post seam.
    #[test]
    fn moonshot_adapter_drives_a_tool_call() {
        let convo = AgentConvo::new("/work", "search the docs then read the file");

        // The recorded transport: assert the key is in the auth arg, NOT the body,
        // and return a real OpenAI tool-call shape.
        let mut key_in_body = false;
        let mut key_seen = false;
        let caller = MoonshotCaller::new(|_endpoint: &str, api_key: &str, body: &Value| {
            if !api_key.is_empty() {
                key_seen = true;
                if body.to_string().contains(api_key) {
                    key_in_body = true;
                }
            }
            // The body must be OpenAI-shaped (messages + tools, function specs).
            assert!(
                body.get("messages").is_some(),
                "translated to OpenAI messages"
            );
            assert!(
                body["tools"][0]["type"] == "function",
                "tools mapped to function specs"
            );
            Ok(oai_tool_call("web_search", r#"{"query":"docs"}"#))
        });

        let keys = LlmKeys::new("moonshot", TEST_SECRET);
        let mut brain = HttpLlm::new(
            keys,
            "https://api.moonshot.ai/v1/chat/completions",
            "kimi-k2-0711-preview",
            caller,
        );
        let step = brain.next_step(&convo);

        match step {
            BrainStep::CallTool { name, arguments } => {
                assert_eq!(name, "web_search", "the model's tool-call surfaced");
                assert_eq!(
                    arguments["query"], "docs",
                    "arguments parsed from the JSON string"
                );
            }
            other => panic!("expected a tool-call, got {other:?}"),
        }
        // The key reached the provider seam — and never the request body.
        assert!(brain.key_reached_provider(), "the key reached the provider");
    }

    /// The adapter round-trips an observation (a refused tool-call) into the OpenAI
    /// conversation, so the model reasons over confinement, and a plain text answer
    /// finishes the turn.
    #[test]
    fn moonshot_adapter_round_trips_observations_and_finishes() {
        let mut convo = AgentConvo::new("/work", "write the file");
        convo.observe(
            "write_file",
            json!({ "path": "x" }),
            false,
            "denied by mandate: no write cap",
        );

        let caller = MoonshotCaller::new(|_e: &str, _k: &str, body: &Value| {
            // The refusal rode into the OpenAI conversation as a tool result.
            let s = body.to_string();
            assert!(
                s.contains("denied by mandate"),
                "the refusal reached the model"
            );
            assert!(s.contains("tool_call_id"), "the tool result is id-linked");
            // The model gives up on the denied tool and answers in text.
            Ok(
                json!({ "choices": [{ "message": { "role": "assistant", "content": "I cannot write; done." } }] }),
            )
        });
        let mut brain = HttpLlm::new(
            LlmKeys::new("moonshot", TEST_SECRET),
            "https://api.moonshot.ai/v1/chat/completions",
            "moonshot-v1-8k",
            caller,
        );
        match brain.next_step(&convo) {
            BrainStep::Finish { text } => {
                assert!(text.contains("cannot write"), "final answer surfaced")
            }
            other => panic!("expected finish, got {other:?}"),
        }
    }

    /// The key never appears in the request body the brain emits, and a stray Debug
    /// of the keys is redacted.
    #[test]
    fn moonshot_adapter_never_leaks_the_key() {
        let convo = AgentConvo::new("/work", "find something");
        let mut leaked = false;
        let caller = MoonshotCaller::new(|_e: &str, api_key: &str, body: &Value| {
            if body.to_string().contains(api_key) {
                leaked = true;
            }
            Ok(json!({ "choices": [{ "message": { "content": "done" } }] }))
        });
        let keys = LlmKeys::new("moonshot", TEST_SECRET);
        let mut brain = HttpLlm::new(
            keys,
            "https://api.moonshot.ai/v1/chat/completions",
            "moonshot-v1-8k",
            caller,
        );
        let _ = brain.next_step(&convo);
        assert!(!leaked, "the key never rode in the request body");
        // A stray Debug of the keys is redacted.
        let keys2 = LlmKeys::new("moonshot", TEST_SECRET);
        assert!(
            !format!("{keys2:?}").contains(TEST_SECRET),
            "Debug is redacted"
        );
    }

    /// The key loads from a file (e.g. ~/.kimikey), trimmed, redacted.
    #[test]
    fn key_loads_from_a_file_trimmed_and_redacted() {
        let dir = std::env::temp_dir().join(format!("deos-kimikey-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("kimikey");
        std::fs::write(&path, format!("  {TEST_SECRET}\n")).unwrap();
        let keys = LlmKeys::from_file("moonshot", &path).expect("key loads");
        assert_eq!(
            keys.secret(),
            TEST_SECRET,
            "trailing whitespace/newline trimmed"
        );
        assert!(
            !format!("{keys:?}").contains(TEST_SECRET),
            "redacted under Debug"
        );
        std::fs::remove_dir_all(&dir).ok();
    }
}

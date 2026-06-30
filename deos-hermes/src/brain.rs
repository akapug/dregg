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

//! The demo's bridge to `dregg-narrator` — a shared HOSTED narrator (the model tier: Bedrock
//! Claude/Nova, then local Ollama), plus the demo-local typed-effect parsing that used to live in
//! the hand-rolled `ollama` module.
//!
//! The hosted narrator is the MODEL tier only (no scripted backend): when every hosted/local
//! model is unavailable OR the hard USD budget is exhausted, `narrate_*` returns `Err`, and each
//! caller drops to ITS OWN deterministic scripted narration — preserving the existing demo
//! behavior and its honest `scripted:*` labels. Every hosted call is metered against
//! `dregg-narrator`'s [`dregg_narrator::BudgetLedger`], so the demo cannot spend past the ceiling.

use std::sync::Arc;

use dregg_narrator::Narrator;
use serde_json::Value;

/// A world-effect the model proposed this turn (the OUTPUT-side typed channel). Unchanged from
/// the old `ollama` module — the caller maps it to a real `attested_dm::WorldEffect` and runs it
/// through `DmCaps::authorize` (proposing is not power).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProposedEffect {
    Grant(String),
    Advance(String),
    SetFlag(String, i64),
}

/// The shared hosted narrator (cheap to clone — it is an `Arc` over one metered narrator).
#[derive(Clone)]
pub struct Hosted {
    narrator: Arc<Narrator>,
}

/// The output ceiling for a narration turn (1-2 sentences). Also what the ledger reserves at the
/// output rate before each hosted call.
const NARRATION_MAX_TOKENS: u32 = 256;

impl Hosted {
    /// Build the shared model-tier narrator (Bedrock Haiku → Bedrock Nova → Ollama), metered
    /// against the env-configured [`dregg_narrator::BudgetLedger`].
    pub fn new() -> Hosted {
        Hosted {
            narrator: Arc::new(Narrator::models_from_env()),
        }
    }

    /// The boot label: `model:<id>` for the first model backend (what WOULD narrate first), or
    /// `None` when there is no model tier at all (→ the caller's scripted label).
    pub fn base_model_kind(&self) -> Option<String> {
        self.narrator.primary_kind()
    }

    /// Narrate `prompt` as the user turn (under `system`, which may be empty), returning the raw
    /// model TEXT plus the honest `kind` that ACTUALLY produced it. `Err` when every model is
    /// unavailable or the budget is exhausted.
    pub fn narrate_text(&self, system: &str, prompt: &str) -> Result<(String, String), String> {
        match self.narrator.narrate(system, prompt, NARRATION_MAX_TOKENS) {
            Ok(n) => Ok((n.text, n.kind)),
            Err(e) => Err(e.to_string()),
        }
    }

    /// Narrate, then parse the model's reply as a JSON object (lenient), returning `(object,
    /// kind)`. The demo prompts instruct the model to answer with a JSON object; a model that
    /// wraps or pads it is recovered by pulling the first balanced `{...}`.
    pub fn narrate_json(&self, system: &str, prompt: &str) -> Result<(Value, String), String> {
        let (text, kind) = self.narrate_text(system, prompt)?;
        let obj = parse_json_object(&text).ok_or_else(|| {
            format!(
                "model reply was not a JSON object: {}",
                truncate(&text, 160)
            )
        })?;
        Ok((obj, kind))
    }
}

/// Interpret the model's `effect` value into a [`ProposedEffect`]. Fail-closed: anything
/// unrecognized → `None` (pure narration), never an invented grant. (Ported verbatim from the
/// old `ollama` module — this is demo logic, not the narrator's.)
pub fn parse_effect(effect: Option<&Value>) -> Option<ProposedEffect> {
    let obj = effect?.as_object()?;
    if let Some(item) = obj.get("grant").and_then(Value::as_str) {
        let item = item.trim().to_ascii_lowercase();
        if !item.is_empty() {
            return Some(ProposedEffect::Grant(item));
        }
    }
    if let Some(scene) = obj.get("advance").and_then(Value::as_str) {
        let scene = scene.trim();
        if !scene.is_empty() {
            return Some(ProposedEffect::Advance(scene.to_string()));
        }
    }
    if let Some(arr) = obj.get("setFlag").and_then(Value::as_array) {
        if let (Some(k), Some(v)) = (
            arr.first().and_then(Value::as_str),
            arr.get(1).and_then(Value::as_i64),
        ) {
            if !k.trim().is_empty() {
                return Some(ProposedEffect::SetFlag(k.trim().to_string(), v));
            }
        }
    }
    None
}

/// Parse `s` as a JSON object, leniently — first as-is, else the first balanced `{...}` slice.
fn parse_json_object(s: &str) -> Option<Value> {
    if let Ok(v @ Value::Object(_)) = serde_json::from_str::<Value>(s.trim()) {
        return Some(v);
    }
    let start = s.find('{')?;
    let end = s.rfind('}').map(|i| i + 1)?;
    if end <= start {
        return None;
    }
    match serde_json::from_str::<Value>(&s[start..end]) {
        Ok(v @ Value::Object(_)) => Some(v),
        _ => None,
    }
}

fn truncate(s: &str, n: usize) -> String {
    let t: String = s.chars().take(n).collect();
    t.replace('\n', " ")
}

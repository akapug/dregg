//! The metered-call seam: a backend-agnostic Converse request/response, the
//! [`ConverseBackend`] trait a hosted model implements, and [`metered_converse`] — the ONE
//! function that enforces the reservation → true-up ordering around any backend.
//!
//! The trait exists so the ordering can be tested WITHOUT the network: a test backend that
//! panics on call proves the reservation refuses an over-cap request BEFORE the backend is ever
//! reached, and a canned-usage backend proves the true-up records the exact cost.

use serde_json::Value;

use crate::ledger::BudgetLedger;
use crate::models::ModelRegistry;
use crate::NarratorError;

/// A conversation role in a Converse message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Role {
    User,
    Assistant,
}

/// One message in a Converse turn.
#[derive(Clone, Debug)]
pub struct ConverseMessage {
    pub role: Role,
    pub text: String,
}

impl ConverseMessage {
    pub fn user(text: impl Into<String>) -> ConverseMessage {
        ConverseMessage {
            role: Role::User,
            text: text.into(),
        }
    }
    pub fn assistant(text: impl Into<String>) -> ConverseMessage {
        ConverseMessage {
            role: Role::Assistant,
            text: text.into(),
        }
    }
}

/// A tool the model may call — the Converse `toolConfig` teeth. `input_schema` is a JSON-Schema
/// object describing the tool's arguments (Nova supports the Converse `toolConfig`).
#[derive(Clone, Debug)]
pub struct ToolDef {
    pub name: String,
    pub description: String,
    pub input_schema: Value,
}

/// A tool the model asked to call, parsed out of the response.
#[derive(Clone, Debug, PartialEq)]
pub struct ToolCall {
    pub id: String,
    pub name: String,
    pub input: Value,
}

/// A backend-agnostic Converse request. Carries its own model id so one client can serve several
/// models and the ledger can price/gate each call by the model it actually targets.
#[derive(Clone, Debug)]
pub struct ConverseRequest {
    /// The model id this call targets (must be priced in the registry, or it is refused).
    pub model: String,
    /// The system prompt (the DM's committed rules).
    pub system: String,
    /// The conversation so far.
    pub messages: Vec<ConverseMessage>,
    /// The output ceiling for this call — also what the reservation charges at the output rate.
    pub max_tokens: u32,
    /// Optional tools (the `toolConfig`); empty = plain narration.
    pub tools: Vec<ToolDef>,
}

impl ConverseRequest {
    /// A plain single-user-turn request with no tools.
    pub fn plain(
        model: impl Into<String>,
        system: impl Into<String>,
        user: impl Into<String>,
        max_tokens: u32,
    ) -> ConverseRequest {
        ConverseRequest {
            model: model.into(),
            system: system.into(),
            messages: vec![ConverseMessage::user(user)],
            max_tokens,
            tools: Vec::new(),
        }
    }

    /// The total prompt byte length — the reservation's conservative input estimate is
    /// `ceil(prompt_bytes / 3)`.
    pub fn prompt_bytes(&self) -> usize {
        self.system.len() + self.messages.iter().map(|m| m.text.len()).sum::<usize>()
    }
}

/// A backend-agnostic Converse response.
#[derive(Clone, Debug)]
pub struct ConverseResponse {
    /// The concatenated text blocks (the narration).
    pub text: String,
    /// Any tool calls the model made this turn.
    pub tool_calls: Vec<ToolCall>,
    /// The model's stop reason (`end_turn`, `max_tokens`, `tool_use`, …).
    pub stop_reason: String,
    /// The REAL input-token count from the response usage — what the true-up prices.
    pub input_tokens: u32,
    /// The REAL output-token count from the response usage.
    pub output_tokens: u32,
}

/// A hosted model that can run a Converse turn. Implemented by the real Bedrock client; a test
/// double implements it to exercise the ledger ordering offline.
pub trait ConverseBackend {
    /// Run one Converse turn, returning the usage-bearing response, or a human-readable error.
    fn converse(&self, req: &ConverseRequest) -> Result<ConverseResponse, String>;
}

/// Run `req` against `backend`, enforcing the hard ceiling. The order is the whole point:
///
/// 1. **Price the model** — look it up in `registry`. An UNPRICED model is refused
///    ([`NarratorError::UnpricedModel`]) here, BEFORE the backend is ever touched: we do not
///    enforce a budget on a cost we do not know.
/// 2. **Reserve** — an upper-bound cost is held against the cap; this may return
///    [`NarratorError::BudgetExhausted`], again BEFORE the backend is called (no network).
/// 3. **Call** the backend.
/// 4. **True up** the reservation with the response's REAL token usage (or **refund** on failure).
pub fn metered_converse(
    ledger: &BudgetLedger,
    registry: &ModelRegistry,
    backend: &(dyn ConverseBackend + Send + Sync),
    req: &ConverseRequest,
) -> Result<ConverseResponse, NarratorError> {
    // (1) PRICE — fail-closed on an unpriced model, before anything else.
    let pricing = registry
        .pricing_for(&req.model)
        .ok_or_else(|| NarratorError::UnpricedModel {
            model: req.model.clone(),
        })?;

    // (2) RESERVE — a refusal here short-circuits, so `backend.converse` is NEVER reached.
    let reservation = ledger.reserve(&req.model, req.prompt_bytes(), req.max_tokens, &pricing)?;

    // (3) CALL.
    match backend.converse(req) {
        Ok(resp) => {
            // (4) TRUE-UP — replace the reservation with the exact usage-priced cost.
            ledger.true_up(reservation, resp.input_tokens, resp.output_tokens, &pricing)?;
            Ok(resp)
        }
        Err(e) => {
            // The call never landed — release the reservation; it cost nothing.
            let _ = ledger.refund(reservation);
            Err(NarratorError::Backend(e))
        }
    }
}

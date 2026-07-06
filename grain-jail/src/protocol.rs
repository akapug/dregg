//! The confined-body line protocol — a minimal newline-delimited JSON exchange
//! between a jailed agent body and the grain that hosts it.
//!
//! The body proposes tool-calls; the host replies with the braid's verdict
//! (admitted / refused, and any tool result). One proposal, one verdict, in
//! lockstep — the exact shape the [`AgentBrain`](dregg_agent::agent::AgentBrain)
//! seam already drives (`next_action` → `observe`). It is deliberately smaller
//! than ACP and maps onto it: an ACP `ToolCallRequest` is a [`Proposal`], an ACP
//! `request_permission` response is a [`Verdict`].

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// A message FROM the jailed body TO the host.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BodyMsg {
    /// The body wants to make a tool-call. The host cap-gates + meters it and
    /// replies with a [`Verdict`].
    Propose(Proposal),
    /// The body is finished — no more proposals. Ends the drive.
    Done(DoneNote),
}

/// One proposed tool-call. `tool` is the grain-cap vocabulary; the optional
/// fields carry the arguments the structured actions need.
///
/// Recognised `tool` shapes (mapped to `AgentAction` in [`crate::map_proposal`]):
/// - any `tool` WITH `args` set → a generic operator tool-call `Op` (e.g.
///   `fs_write` with `{path, content}`) — the shape the grain's real toolkit
///   consumes; the grain performs it host-side, cap-gated, so a jailed body with
///   no ambient file access can still request file work through the seam.
/// - any `tool` WITH `amount_cents` set → the priced `Spend` rail.
/// - `cell-write` (needs `path` + `value`) → `CellWrite`.
/// - `cell-read` (needs `path`) → `CellRead`.
/// - `invoke:<service>` or a bare `<service>` → `Invoke`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proposal {
    /// The tool / service the body wants to call.
    pub tool: String,
    /// A generic operator tool-call's string args (`path`/`content` for
    /// `fs_write`, `url`/`dest` for http/git, …). Present ⇒ a generic `Op`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub args: Option<BTreeMap<String, String>>,
    /// The priced-spend amount (USD-cents). Present ⇒ the proposal is a `Spend`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub amount_cents: Option<i64>,
    /// The cell path for `cell-read` / `cell-write`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    /// The value to commit for `cell-write`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub value: Option<String>,
}

impl Proposal {
    /// A bare tool-call proposal (`invoke:<service>`).
    pub fn invoke(tool: impl Into<String>) -> Proposal {
        Proposal {
            tool: tool.into(),
            args: None,
            amount_cents: None,
            path: None,
            value: None,
        }
    }

    /// A generic operator tool-call (`Op`) — a `tool` plus its string args (e.g.
    /// `fs_write` with `path`/`content`).
    pub fn op(
        tool: impl Into<String>,
        args: impl IntoIterator<Item = (String, String)>,
    ) -> Proposal {
        Proposal {
            tool: tool.into(),
            args: Some(args.into_iter().collect()),
            amount_cents: None,
            path: None,
            value: None,
        }
    }
}

/// The body's closing note.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct DoneNote {
    /// An optional final summary the body reports.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
}

/// The host's verdict on one proposal — a serialized
/// [`ActionObservation`](dregg_agent::agent::ActionObservation): whether the
/// braid admitted the call (cap ✓ · budget ✓ · receipted), the refusal reason if
/// not, and the tool's own result if it ran.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Verdict {
    /// `true` iff the braid admitted the call.
    pub admitted: bool,
    /// On refusal: the reason (missing cap, over-budget, or an unmappable
    /// proposal the host refused in-band).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refusal: Option<String>,
    /// For an admitted call dispatched to a live tool: the tool's ok/fail.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub tool_ok: Option<bool>,
    /// The tool's summary, if any (also bound into the turn receipt).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub summary: Option<String>,
}

impl Verdict {
    /// A host-side in-band refusal (the proposal never reached the braid — e.g.
    /// an unmappable `tool`, or a `cell-write` missing its `value`).
    pub fn refuse(reason: impl Into<String>) -> Verdict {
        Verdict {
            admitted: false,
            refusal: Some(reason.into()),
            tool_ok: None,
            summary: None,
        }
    }
}

//! THE MANDATE INSPECTOR — an agent's live confinement made legible.
//!
//! The ADOS thesis is "every agent action is a receipted turn." The mandate
//! inspector is that thesis made VISIBLE: for a confined Hermes session it
//! renders, per mandate, the GRANT deos pinned (scope / rate ceiling / deadline /
//! executor verb), how much of the budget has been SPENT, and the RECEIPTS
//! (turn hashes) of the calls that committed — or the REFUSALS that bit.
//!
//! It reads only from the live [`HermesGateway`] + [`GrantRegistry`] and an
//! accumulated verdict log, so it is a pure VIEW: no enforcement, no state of its
//! own. A deos dock surface ([`crate::surface`]) renders it; a CLI prints it.

use crate::acp::PermissionOutcome;
use crate::bridge::HermesGateway;
use crate::grant_registry::MandateKey;

/// One mandate's live state for the inspector: the grant deos pinned, the budget
/// spent, and the calls that rode it.
#[derive(Clone, Debug)]
pub struct MandateRow {
    /// The mandate key (a per-tool grant or a per-kind floor).
    pub key: MandateKey,
    /// The granted rate ceiling.
    pub rate_limit: i64,
    /// The granted deadline (clock/height expiry).
    pub deadline: i64,
    /// The executor verb the worker's credential is scoped to.
    pub tool_method: String,
    /// Calls committed on this mandate so far.
    pub calls_made: i64,
    /// Calls remaining (`rate_limit - calls_made`, clamped at 0).
    pub remaining: i64,
    /// Receipt ids (turn hashes, hex) of committed calls on this mandate.
    pub receipts: Vec<String>,
    /// Refusal reasons recorded against this mandate (in-band rejects).
    pub refusals: Vec<String>,
}

/// The whole live mandate of a confined session — one row per mandate that has a
/// grant, plus the running verdict tallies.
#[derive(Clone, Debug)]
pub struct Mandate {
    /// The session this mandate confines.
    pub session_id: String,
    /// One row per mandate key with a grant (every kind floor + every per-tool grant).
    pub rows: Vec<MandateRow>,
    /// Total committed (allowed) calls across the session.
    pub total_allowed: usize,
    /// Total refused (in-band rejected) calls across the session.
    pub total_refused: usize,
}

impl Mandate {
    /// Build the live mandate view from a gateway and the session's verdict log
    /// (the `(call, outcome)` pairs an [`crate::acp_client::AcpClient`] run
    /// produced, or that a driver accumulated).
    pub fn from_session<'rt>(
        session_id: &str,
        gateway: &HermesGateway<'rt>,
        verdicts: &[(crate::acp::ToolCallRequest, PermissionOutcome)],
    ) -> Mandate {
        let registry = gateway.registry();
        let mut rows: Vec<MandateRow> = registry
            .all_keys()
            .into_iter()
            .map(|key| {
                let grant = registry.grant_for_key(&key);
                let calls_made = gateway.calls_made_for_key(&key);
                MandateRow {
                    key,
                    rate_limit: grant.rate_limit,
                    deadline: grant.deadline,
                    tool_method: grant.tool_method.clone(),
                    calls_made,
                    remaining: (grant.rate_limit - calls_made).max(0),
                    receipts: Vec::new(),
                    refusals: Vec::new(),
                }
            })
            .collect();

        let mut total_allowed = 0;
        let mut total_refused = 0;
        for (call, outcome) in verdicts {
            let key = registry.key_for_tool(&call.name);
            let row = rows.iter_mut().find(|r| r.key == key);
            match outcome {
                PermissionOutcome::Allow { receipt, .. } => {
                    total_allowed += 1;
                    if let Some(r) = row {
                        r.receipts.push(receipt.clone());
                    }
                }
                PermissionOutcome::Reject { reason, .. } => {
                    total_refused += 1;
                    if let Some(r) = row {
                        r.refusals.push(reason.clone());
                    }
                }
            }
        }

        Mandate {
            session_id: session_id.to_string(),
            rows,
            total_allowed,
            total_refused,
        }
    }

    /// A human-readable rendering of the live mandate (the CLI / dock text view).
    pub fn render_text(&self) -> String {
        let mut s = String::new();
        s.push_str(&format!(
            "MANDATE — session {} | {} allowed, {} refused\n",
            self.session_id, self.total_allowed, self.total_refused
        ));
        s.push_str(
            "  mandate                 rate   spent  left  method        receipts/refusals\n",
        );
        for r in &self.rows {
            // Skip never-touched kind floors with no receipts to keep it legible,
            // UNLESS it's a per-tool grant (always show pinned tightenings).
            let touched = r.calls_made > 0 || !r.refusals.is_empty();
            let is_per_tool = matches!(r.key, MandateKey::Tool(_));
            if !touched && !is_per_tool {
                continue;
            }
            let detail = if !r.receipts.is_empty() {
                format!(
                    "{} receipt(s) e.g. {}…",
                    r.receipts.len(),
                    &r.receipts[0][..16.min(r.receipts[0].len())]
                )
            } else if !r.refusals.is_empty() {
                format!("{} refusal(s): {}", r.refusals.len(), r.refusals[0])
            } else {
                "(pinned, unused)".to_string()
            };
            s.push_str(&format!(
                "  {:<22}  {:>4}   {:>4}  {:>4}  {:<12}  {}\n",
                r.key.label(),
                r.rate_limit,
                r.calls_made,
                r.remaining,
                r.tool_method,
                detail,
            ));
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HermesGateway;
    use crate::acp::ToolCallRequest;
    use crate::grant_registry::GrantRegistry;
    use dregg_sdk::{AgentCipherclerk, AgentRuntime};
    use std::sync::{Arc, RwLock};

    fn grantor() -> (AgentRuntime, dregg_sdk::HeldToken) {
        let mut cclerk = AgentCipherclerk::new();
        let root = cclerk.mint_token(&[7u8; 32], "deos");
        let rt = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "deos");
        (rt, root)
    }

    #[test]
    fn mandate_inspector_shows_receipts_and_budgets() {
        let (rt, root) = grantor();
        let registry = GrantRegistry::default_for_session(1000).with_standard_tool_grants(1000);
        let mut gw = HermesGateway::new(&rt, root, registry);

        let mut verdicts = Vec::new();
        for (id, name, args) in [
            ("a", "web_search", serde_json::json!({"query": "x"})),
            ("b", "terminal", serde_json::json!({"command": "ls"})),
        ] {
            let call = ToolCallRequest::new("s1", id, name, args);
            let outcome = gw.admit_call(&call, 50);
            verdicts.push((call, outcome));
        }

        let mandate = Mandate::from_session("s1", &gw, &verdicts);
        assert_eq!(mandate.total_allowed, 2);
        assert_eq!(mandate.total_refused, 0);

        // The per-tool terminal grant has a receipt and spent 1 of its rate-5.
        let term = mandate
            .rows
            .iter()
            .find(|r| r.key == MandateKey::Tool("terminal".into()))
            .expect("terminal per-tool row present");
        assert_eq!(term.rate_limit, 5);
        assert_eq!(term.calls_made, 1);
        assert_eq!(term.receipts.len(), 1);
        assert_eq!(term.receipts[0].len(), 64, "a real hex turn hash receipt");

        let text = mandate.render_text();
        assert!(
            text.contains("tool:terminal"),
            "renders the terminal mandate"
        );
    }
}

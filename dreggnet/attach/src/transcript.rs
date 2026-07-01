//! The **streamable transcript**: the reason→act→observe loop the browser renders
//! live, plus the running budget meter — both derived from the session's *signed*
//! run log + receipts, so every line traces to a receipt or a refusal (nothing
//! the page shows is the host's say-so).
//!
//! [`dreggnet_exec::live::transcript_of`] already pairs each admitted log entry
//! with its receipt (verdict + cost). This module enriches each step with the
//! facts the live UI needs — the cap-gate verdict (✓ admitted / ✗ refused) and
//! the *running* consumed/headroom after the step — so the budget meter draws
//! down and the receipts accumulate per action, exactly as they happen.

use serde::{Deserialize, Serialize};

use crate::session::AgentSession;

/// One enriched step of the reason→act→observe loop, as the browser renders it.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct TranscriptStep {
    /// The 1-based step ordinal.
    pub n: u64,
    /// The action label the brain decided (`shell:…`, `invoke:run_tests`, …).
    pub action: String,
    /// `true` iff the braid admitted it (cap ✓ · budget ✓ · receipted). `false`
    /// for a cap-refused / budget-refused step — the visible ✗.
    pub admitted: bool,
    /// On refusal: the reason (the missing cap, or budget-exhausted). `None` on admit.
    pub refused: Option<String>,
    /// For an admitted tool call: the real tool verdict summary, if any.
    pub tool_summary: Option<String>,
    /// The budget units this step drew (0 for a refusal).
    pub cost: i64,
    /// The running consumed budget after this step.
    pub consumed: i64,
    /// The running headroom after this step (`budget - consumed`).
    pub headroom: i64,
    /// Whether this admitted step sealed a receipt (the chain grew by one).
    pub receipted: bool,
    /// The action *family* (`cell` · `invoke` · `spend` · `op`), parsed from the
    /// action label — the cockpit renders each kind distinctly (the reason→act→
    /// observe legibility).
    pub family: String,
    /// For an admitted step: the sealed receipt's chain position (`seq`). `None`
    /// for a refusal (which seals nothing).
    pub receipt_seq: Option<u64>,
    /// For an admitted step: a short fingerprint of the ed25519 signature over the
    /// receipt — so the *signed* chain accumulating is visible, line by line.
    pub sig_fp: Option<String>,
    /// For an admitted step: a short fingerprint of the previous receipt hash this
    /// one links back to (`"genesis"` for the first) — the append-only chain made
    /// visible (each receipt names its parent).
    pub prev_fp: Option<String>,
}

/// The budget meter the page draws: the ceiling, the consumed draw-down, and the
/// un-drawn headroom (the could-have bound).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct BudgetMeter {
    /// The asset the budget is denominated in.
    pub asset: String,
    /// The budget ceiling (the hard bound).
    pub budget: i64,
    /// The total consumed over the run.
    pub consumed: i64,
    /// The un-drawn headroom.
    pub headroom: i64,
    /// Consumed as a 0–100 percentage of the ceiling (for the meter bar).
    pub pct: u8,
}

impl BudgetMeter {
    /// The budget meter for a session.
    pub fn of(session: &AgentSession) -> BudgetMeter {
        let budget = session.budget();
        let consumed = session.consumed();
        let pct = if budget > 0 {
            ((consumed.max(0) as i128 * 100) / budget as i128).clamp(0, 100) as u8
        } else {
            0
        };
        BudgetMeter {
            asset: session.run.run.asset.clone(),
            budget,
            consumed,
            headroom: session.headroom(),
            pct,
        }
    }
}

/// The whole transcript of a session — the ordered reason→act→observe steps with
/// a running budget draw-down. Derived from the signed log + receipts; the live
/// SSE stream replays exactly these frames.
pub fn transcript_of(session: &AgentSession) -> Vec<TranscriptStep> {
    let budget = session.budget();
    let mut consumed = 0i64;
    let receipts = &session.run.run.receipts;
    // Admitted steps pair 1:1, in order, with the receipt chain (exactly the
    // pairing `transcript_of_slices` uses) — so we can surface each step's sealed
    // receipt position + its signature/prev-hash fingerprints as the chain grows.
    let mut ri = 0usize;
    dreggnet_exec::live::transcript_of(&session.run.run)
        .into_iter()
        .map(|s| {
            let admitted = s.outcome == "admitted";
            consumed += s.cost;
            let family = action_family(&s.action);
            let (receipt_seq, sig_fp, prev_fp) = if admitted {
                let facts = receipts.get(ri).map(|r| {
                    let (sig, prev) = match &r.attestation {
                        Some(a) => (
                            Some(hex_fp(&a.signature)),
                            Some(
                                a.prev_receipt_hash
                                    .map(|h| hex_fp(&h))
                                    .unwrap_or_else(|| "genesis".to_string()),
                            ),
                        ),
                        None => (None, None),
                    };
                    (Some(r.seq), sig, prev)
                });
                ri += 1;
                facts.unwrap_or((None, None, None))
            } else {
                (None, None, None)
            };
            TranscriptStep {
                n: s.n,
                action: s.action,
                admitted,
                refused: if admitted {
                    None
                } else {
                    Some(s.outcome.clone())
                },
                tool_summary: s.tool_summary,
                cost: s.cost,
                consumed,
                headroom: (budget - consumed).max(0),
                receipted: admitted,
                family,
                receipt_seq,
                sig_fp,
                prev_fp,
            }
        })
        .collect()
}

/// Parse an action label into its family — the cockpit colours/labels each kind.
fn action_family(action: &str) -> String {
    let head = action.split([':', ' ']).next().unwrap_or("op");
    match head {
        "invoke" => "invoke",
        "spend" => "spend",
        "cell-write" | "cell-read" | "cell" => "cell",
        _ => "op",
    }
    .to_string()
}

/// A short hex fingerprint (first 4 bytes) of a hash/signature — enough to *see*
/// the signed, linked chain without dumping 64-byte blobs into the feed.
fn hex_fp(bytes: &[u8]) -> String {
    bytes
        .iter()
        .take(4)
        .map(|b| format!("{b:02x}"))
        .collect::<String>()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{DemoDriver, SessionDriver};
    use crate::session::GoalRequest;

    fn driven() -> AgentSession {
        let req = GoalRequest::new("ship the site: run the tests then verify the deploy", 50)
            .with_service("run_tests")
            .with_service("verify_deploy");
        DemoDriver::seeded([3u8; 32]).drive(&req, "dregg:demo0001demo0001", "sess_t")
    }

    // ── the transcript IS the reason→act→observe loop, traced to receipts ──────
    #[test]
    fn the_transcript_streams_reason_act_observe_steps() {
        let session = driven();
        let steps = transcript_of(&session);
        assert!(!steps.is_empty(), "the run produced steps");
        // Ordinals are 1-based and contiguous.
        for (i, s) in steps.iter().enumerate() {
            assert_eq!(s.n, (i + 1) as u64);
        }
        // At least one admitted tool step carries a real verdict summary.
        assert!(
            steps.iter().any(|s| s.admitted && s.tool_summary.is_some()),
            "an admitted tool call surfaced its verdict"
        );
    }

    // ── the budget draws DOWN, monotonically, never past the ceiling ───────────
    #[test]
    fn the_budget_draws_down_monotonically_within_the_ceiling() {
        let session = driven();
        let steps = transcript_of(&session);
        let mut last = 0i64;
        for s in &steps {
            assert!(s.consumed >= last, "consumed only grows");
            assert!(s.consumed <= session.budget(), "never past the ceiling");
            assert_eq!(
                s.consumed + s.headroom,
                session.budget(),
                "the could-have bound holds per step"
            );
            last = s.consumed;
        }
        // The final running consumed agrees with the report total.
        assert_eq!(last, session.consumed());
    }

    // ── the cap-gate ✗ shows up as a refused step (non-vacuous teeth) ──────────
    #[test]
    fn a_cap_refused_action_shows_as_a_refused_step() {
        let session = driven();
        let steps = transcript_of(&session);
        let refused: Vec<_> = steps.iter().filter(|s| !s.admitted).collect();
        assert!(
            !refused.is_empty(),
            "the demo agent attempts an out-of-bundle tool and is refused"
        );
        for r in &refused {
            assert_eq!(r.cost, 0, "a refusal draws nothing");
            assert!(!r.receipted, "a refusal seals no receipt");
            assert!(r.refused.is_some());
        }
        // The receipted steps == the report's receipt count.
        let receipted = steps.iter().filter(|s| s.receipted).count();
        assert_eq!(receipted, session.receipts());
    }

    // ── each admitted step carries its sealed, signed, linked receipt facts ────
    #[test]
    fn admitted_steps_surface_the_signed_chain() {
        let session = driven();
        let steps = transcript_of(&session);
        let admitted: Vec<_> = steps.iter().filter(|s| s.admitted).collect();
        assert!(!admitted.is_empty());
        // The receipt seqs are strictly increasing along the chain.
        let mut last_seq = None;
        for s in &admitted {
            let seq = s.receipt_seq.expect("an admitted step seals a receipt");
            if let Some(prev) = last_seq {
                assert!(seq > prev, "the chain position grows");
            }
            last_seq = Some(seq);
            assert!(
                s.sig_fp.is_some(),
                "the receipt is signed (fingerprint shown)"
            );
            assert!(s.prev_fp.is_some(), "the receipt links to its parent");
            assert!(!s.family.is_empty(), "the action has a family");
        }
        // The first admitted receipt links to genesis.
        assert_eq!(admitted[0].prev_fp.as_deref(), Some("genesis"));
        // A refusal seals nothing.
        for r in steps.iter().filter(|s| !s.admitted) {
            assert!(r.receipt_seq.is_none());
            assert!(r.sig_fp.is_none());
        }
    }

    // ── the budget meter projects the ceiling / consumed / headroom ────────────
    #[test]
    fn the_budget_meter_projects_the_bound() {
        let session = driven();
        let m = BudgetMeter::of(&session);
        assert_eq!(m.budget, session.budget());
        assert_eq!(m.consumed + m.headroom, m.budget);
        assert!(m.pct <= 100);
    }
}

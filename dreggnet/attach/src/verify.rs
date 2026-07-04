//! **Verify-in-browser.** The verify-don't-trust moment: re-witness the session's
//! receipt chain + the budget bound *in the browser*, so a user never takes the
//! attach's word that their agent stayed in its box.
//!
//! This reuses the SSH attach's own re-witness — [`dreggnet_exec::live::verify_live`]:
//! (1) the receipt chain verifies (signed, unbroken, tamper-evident — a forged
//! action / verdict / spliced receipt breaks the ed25519 signature or the
//! prev-hash link); (2) the consumed budget stays at/under the ceiling and the
//! report's total agrees with the chain tip (the proof and the bound agree);
//! (3) the funded budget matches the run's ceiling; (4) the sub-agent chain (if
//! any) re-witnesses too. Needs only the session record — no trust in the host.
//!
//! The result is a flat [`SessionVerifyResult`] the page renders as a verdict:
//! "✓ the agent stayed in its box, here's the proof" — or the reason it did not.

use serde::Serialize;

use dreggnet_exec::live::{LiveRun, verify_live};

use crate::session::AgentSession;

/// The in-browser verify verdict for a hosted agent session.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SessionVerifyResult {
    /// What was verified (`"agent-session"`).
    pub kind: String,
    /// The natural-language goal the session pursued.
    pub goal: String,
    /// Whether the caller owns the session (the owner == the signed-in subject).
    /// `None` for the open "paste any run" path (a self-contained proof needs no
    /// scoping — the math speaks for itself).
    pub owner_scope_ok: Option<bool>,
    /// The whole re-witness held: chain ✓ · bound ✓ · funded-budget ✓ · subagent ✓.
    pub ok: bool,
    /// The budget ceiling.
    pub budget: i64,
    /// The consumed total the chain attests.
    pub consumed: i64,
    /// The un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// Admitted actions re-witnessed in the main chain.
    pub actions: usize,
    /// Admitted actions in the sub-agent chain (0 if none).
    pub subagent_actions: usize,
    /// A human-readable one-liner (the reason, on failure).
    pub detail: String,
    /// `true` when this result is the **tamper self-demo**: the same chain, with a
    /// single line flipped, re-witnessed on purpose to show it shatters (✗). The
    /// cockpit shows the genuine ✓ beside this ✗ — verify-don't-trust, made visible.
    #[serde(default)]
    pub tamper_demo: bool,
    /// For the tamper self-demo: a one-line description of exactly what was flipped.
    #[serde(default)]
    pub tampered_what: Option<String>,
}

/// Re-witness a [`LiveRun`] session record. `owner_scope`, when
/// `Some((requesting_subject, owner))`, records whether the caller owns the
/// session — used by the scoped "verify my session" button. The crypto verdict is
/// computed regardless (a self-contained record verifies for anyone — that is the
/// whole point of verify-don't-trust); `owner_scope_ok` just reports the fact.
pub fn verify_live_run(run: &LiveRun, owner_scope: Option<(&str, &str)>) -> SessionVerifyResult {
    let owner_scope_ok = owner_scope.map(|(req, owner)| req == owner);
    match verify_live(run) {
        Ok(v) => SessionVerifyResult {
            kind: "agent-session".to_string(),
            goal: run.goal.clone(),
            owner_scope_ok,
            ok: true,
            budget: v.budget,
            consumed: v.consumed,
            headroom: v.headroom,
            actions: v.actions,
            subagent_actions: v.subagent_actions,
            detail: format!(
                "re-witnessed: chain ✓ · bound ✓ ({consumed}/{budget} consumed, {headroom} headroom) \
                 · the agent stayed in its box",
                consumed = v.consumed,
                budget = v.budget,
                headroom = v.headroom,
            ),
            tamper_demo: false,
            tampered_what: None,
        },
        Err(e) => SessionVerifyResult {
            kind: "agent-session".to_string(),
            goal: run.goal.clone(),
            owner_scope_ok,
            ok: false,
            budget: run.run.budget,
            consumed: run.run.consumed,
            headroom: run.run.headroom,
            actions: run.run.receipts.len(),
            subagent_actions: 0,
            detail: format!("did NOT re-witness (forged / tampered / bound violated): {e}"),
            tamper_demo: false,
            tampered_what: None,
        },
    }
}

/// The **tamper self-demo** — the verify-don't-trust magic made visceral. Take the
/// caller's own session, flip exactly ONE sealed line (a tool verdict, or failing
/// that a receipt's cost), and re-witness the result: it MUST fail. The cockpit
/// runs this right after the genuine ✓ so a judge SEES that a single forged line
/// shatters the proof — the chain is tamper-evident, not trusted.
///
/// The mutation is on a private clone; the stored session is never touched.
pub fn tamper_demo(session: &AgentSession) -> SessionVerifyResult {
    let mut t = session.clone();
    let what = if let Some(i) = t.run.run.receipts.iter().position(|r| r.tool_ok.is_some()) {
        let was = t.run.run.receipts[i].tool_ok;
        let now = Some(!was.unwrap_or(true));
        let seq = t.run.run.receipts[i].seq;
        t.run.run.receipts[i].tool_ok = now;
        format!("flipped receipt #{seq}: tool verdict {was:?} → {now:?} (a forged \"it passed\")")
    } else if let Some(r) = t.run.run.receipts.first_mut() {
        let seq = r.seq;
        r.cost += 1;
        format!("bumped receipt #{seq} cost by 1 unit (a forged charge)")
    } else {
        "no sealed receipt to tamper".to_string()
    };
    let mut res = verify_live_run(&t.run, None);
    res.tamper_demo = true;
    res.tampered_what = Some(what);
    res
}

/// Re-witness a session for `requesting_subject` (the scoped "verify my session"
/// button): the crypto verdict + the owner-scoping fact.
pub fn verify_session(session: &AgentSession, requesting_subject: &str) -> SessionVerifyResult {
    verify_live_run(
        &session.run,
        Some((requesting_subject, session.owner.as_str())),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::driver::{DemoDriver, SessionDriver};
    use crate::session::GoalRequest;

    const OWNER: &str = "dregg:demo0001demo0001";

    fn driven() -> AgentSession {
        let req = GoalRequest::new("run the tests then verify the deploy", 50)
            .with_service("run_tests")
            .with_service("verify_deploy")
            .with_cell("/goal");
        DemoDriver::seeded([11u8; 32]).drive(&req, OWNER, "sess_v")
    }

    // ── the happy path: a real session re-witnesses in-browser ─────────────────
    #[test]
    fn a_real_session_re_witnesses() {
        let s = driven();
        let v = verify_session(&s, OWNER);
        assert!(v.ok, "{}", v.detail);
        assert_eq!(v.owner_scope_ok, Some(true));
        assert_eq!(v.consumed + v.headroom, v.budget, "the could-have bound");
        assert!(v.actions >= 2);
    }

    // ── TOOTH: a tampered receipt is caught (✗) ────────────────────────────────
    #[test]
    fn a_tampered_receipt_is_caught() {
        let mut s = driven();
        // Flip a sealed tool verdict from pass → fail after the fact.
        let i = s
            .run
            .run
            .receipts
            .iter()
            .position(|r| r.tool_ok.is_some())
            .expect("a receipt with a verdict");
        s.run.run.receipts[i].tool_ok = Some(false);
        let v = verify_session(&s, OWNER);
        assert!(!v.ok, "the forged verdict breaks the receipt signature");
        assert!(v.detail.contains("did NOT re-witness"));
    }

    // ── TOOTH: a spliced/dropped receipt is caught ─────────────────────────────
    #[test]
    fn a_dropped_receipt_is_caught() {
        let mut s = driven();
        s.run.run.receipts.pop();
        let v = verify_session(&s, OWNER);
        assert!(!v.ok, "a broken chain does not re-witness");
    }

    // ── the tamper self-demo always shatters (✗) and says what it flipped ──────
    #[test]
    fn the_tamper_demo_shatters_a_genuine_chain() {
        let s = driven();
        // The genuine chain holds.
        assert!(verify_session(&s, OWNER).ok);
        // The tamper demo, on the SAME session, fails — and names what it flipped.
        let d = tamper_demo(&s);
        assert!(d.tamper_demo);
        assert!(!d.ok, "a single flipped line shatters the proof");
        assert!(d.tampered_what.is_some());
        assert!(d.detail.contains("did NOT re-witness"));
        // The original is untouched (the demo worked on a clone).
        assert!(
            verify_session(&s, OWNER).ok,
            "the stored session is unharmed"
        );
    }

    // ── the owner-scoping fact is reported; the crypto holds for anyone ─────────
    #[test]
    fn owner_scoping_is_reported_but_the_proof_is_self_contained() {
        let s = driven();
        let not_mine = verify_session(&s, "dregg:somebodyelse00");
        assert_eq!(not_mine.owner_scope_ok, Some(false));
        // A self-contained proof still verifies for anyone — verify-don't-trust.
        assert!(not_mine.ok);
    }
}

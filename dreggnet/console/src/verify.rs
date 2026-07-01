//! **Verify-anything, signed-in.** The console's verify-don't-trust surface:
//! paste / select a deploy or an agent-run and re-witness it *in-page* — the
//! same crypto `dregg-cloud verify` runs, so a customer never has to trust the
//! console's say-so about their own resources.
//!
//! For an agent run this re-witnesses the real [`AgentRunReport`] the agent panel
//! carries:
//!
//! 1. **the receipt chain** — signed, unbroken, tamper-evident
//!    ([`verify_agent_run`]). A forged action label / verdict / spliced receipt
//!    breaks the ed25519 signature or the prev-hash link.
//! 2. **the budget bound** — consumed ≤ the ceiling, and the chain's final
//!    attested consumption agrees with the report's total (the proof and the
//!    bound agree).
//! 3. **the QA proof** — for every receipt carrying a `WitnessedRun`, the tests
//!    ran against the *deployed* `content_root` (`code_root == deployed_root` —
//!    the [`WitnessVerifyError::CodeRootMismatch`] tooth), and the verdict the
//!    chain sealed is authentic (a flipped pass/fail breaks the signature, caught
//!    by leg 1). The remaining operator-independence — a pure light client, not
//!    the substrate, re-executing each run — is the federation-attested rung
//!    (`dreggnet_exec::federation_qa`), named, not faked.
//!
//! The result is a flat [`ConsoleVerifyResult`] the page renders as a verdict.
//! Re-witness needs only the report — no trust in the console host.

use serde::Serialize;

use dreggnet_exec::agent::{AgentRunReport, AgentVerifyError, verify_agent_run};

/// The in-page verify verdict for an agent run.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct ConsoleVerifyResult {
    /// What was verified (`"agent-run"`).
    pub kind: String,
    /// The agent id the report names.
    pub agent: String,
    /// Whether the caller is scoped to this resource (the owner == the signed-in
    /// subject). `None` when the verify is the open "paste any report" path (a
    /// self-contained proof needs no scoping — the math speaks for itself).
    pub owner_scope_ok: Option<bool>,
    /// The receipt chain re-witnessed (signed, unbroken, tamper-evident).
    pub chain_ok: bool,
    /// The budget bound holds (consumed ≤ ceiling, proof/bound agree).
    pub bound_ok: bool,
    /// The budget ceiling.
    pub budget: i64,
    /// The consumed total the chain attests.
    pub consumed: i64,
    /// The un-drawn headroom (the could-have bound).
    pub headroom: i64,
    /// The number of execution-witnessing (`run_tests`/`verify_deploy`) verdicts.
    pub witnessed: usize,
    /// How many of them passed (exit 0).
    pub passed: usize,
    /// Every witnessed run's `code_root` equals the deployed `content_root` (the
    /// tests ran on the deployed code, not arbitrary code).
    pub code_root_ok: bool,
    /// The at-a-glance verdict: chain ✓ AND bound ✓ AND (no QA, or QA ran on the
    /// deployed code).
    pub ok: bool,
    /// A human-readable one-liner (the reason, on failure).
    pub detail: String,
}

/// Re-witness an [`AgentRunReport`] against the deployed `content_root`.
///
/// `owner_scope`, when `Some((requesting_subject, owner))`, records whether the
/// caller owns the resource — used by the scoped "re-verify my agent" button so
/// the console never re-verifies on behalf of one user a report that names
/// another's resource. The crypto verdict is computed regardless (a pasted,
/// self-contained report verifies for anyone — that is the whole point of
/// verify-don't-trust); `owner_scope_ok` just reports the scoping fact.
pub fn verify_agent_report(
    report: &AgentRunReport,
    deployed_root: &str,
    owner_scope: Option<(&str, &str)>,
) -> ConsoleVerifyResult {
    let owner_scope_ok = owner_scope.map(|(req, owner)| req == owner);

    // Legs 1 + 2: the receipt chain + the budget bound.
    let (chain_ok, bound_ok, consumed, headroom, mut detail) = match verify_agent_run(report) {
        Ok(v) => (
            true,
            true,
            v.consumed,
            v.headroom,
            "re-witnessed: chain ✓ · bound ✓".to_string(),
        ),
        Err(AgentVerifyError::Chain(e)) => (
            false,
            false,
            report.consumed,
            report.headroom,
            format!("receipt chain did NOT verify (forged / tampered / spliced): {e:?}"),
        ),
        Err(AgentVerifyError::BoundViolated { consumed, budget }) => (
            true,
            false,
            consumed,
            report.headroom,
            format!("budget bound VIOLATED: consumed {consumed} exceeds the ceiling {budget}"),
        ),
        Err(AgentVerifyError::ConsumedMismatch { report: r, chain }) => (
            true,
            false,
            r,
            report.headroom,
            format!("proof/bound MISMATCH: report claims {r} consumed, the chain attests {chain}"),
        ),
    };

    // Leg 3: the QA proof — every witnessed run ran on the deployed code, and
    // passed/failed as the (signed) chain records. `code_root_ok` is the
    // CodeRootMismatch tooth; the verdict authenticity rides leg 1 (a forged
    // verdict breaks the signature there).
    let mut witnessed = 0usize;
    let mut passed = 0usize;
    let mut code_root_ok = true;
    for r in &report.receipts {
        let Some(w) = &r.witnessed else { continue };
        witnessed += 1;
        if w.code_root != deployed_root {
            code_root_ok = false;
        }
        if w.passed() {
            passed += 1;
        }
    }

    let ok = chain_ok && bound_ok && code_root_ok;
    if chain_ok && bound_ok {
        if witnessed == 0 {
            detail = "re-witnessed: chain ✓ · bound ✓ · (no execution-QA in this run)".to_string();
        } else if code_root_ok {
            detail = format!(
                "re-witnessed: chain ✓ · bound ✓ · QA {passed}/{witnessed} passed on the deployed code ✓"
            );
        } else {
            detail = format!(
                "QA MISMATCH: a witnessed run's code_root ≠ the deployed content_root \
                 ({deployed_root}) — the tests did NOT run on the deployed code"
            );
        }
    }

    ConsoleVerifyResult {
        kind: "agent-run".to_string(),
        agent: report.agent.clone(),
        owner_scope_ok,
        chain_ok,
        bound_ok,
        budget: report.budget,
        consumed,
        headroom,
        witnessed,
        passed,
        code_root_ok,
        ok,
        detail,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures;

    // ── the happy path: a real deployed agent re-witnesses in-page ─────────────
    #[test]
    fn a_real_agent_run_re_witnesses() {
        let (report, root) = fixtures::demo_agent_report();
        let v = verify_agent_report(&report, &root, None);
        assert!(v.ok, "{}", v.detail);
        assert!(v.chain_ok && v.bound_ok && v.code_root_ok);
        assert_eq!(v.consumed + v.headroom, v.budget, "the could-have bound");
        assert!(v.witnessed >= 1, "the run carries a QA proof");
        assert_eq!(v.passed, v.witnessed, "the demo QA all passed");
    }

    // ── TOOTH: a forged verdict is caught (the chain signature breaks) ─────────
    #[test]
    fn a_forged_qa_verdict_is_caught() {
        let (mut report, root) = fixtures::demo_agent_report();
        // Flip a sealed tool verdict from pass → fail after the fact.
        let i = report
            .receipts
            .iter()
            .position(|r| r.tool_ok.is_some())
            .unwrap();
        report.receipts[i].tool_ok = Some(false);
        let v = verify_agent_report(&report, &root, None);
        assert!(
            !v.chain_ok,
            "the forged verdict breaks the receipt signature"
        );
        assert!(!v.ok);
    }

    // ── TOOTH: QA run against NON-deployed code is caught (code_root mismatch) ──
    #[test]
    fn qa_on_the_wrong_code_is_caught() {
        let (report, _root) = fixtures::demo_agent_report();
        // Verify against a DIFFERENT deployed root than the run's code_root.
        let v = verify_agent_report(&report, "some-other-content-root", None);
        assert!(v.chain_ok, "the chain itself is fine");
        assert!(!v.code_root_ok, "the QA did not run on this deployed code");
        assert!(!v.ok);
    }

    // ── the owner-scoping fact is reported for the 'my agent' button ───────────
    #[test]
    fn owner_scoping_is_reported() {
        let (report, root) = fixtures::demo_agent_report();
        let owner = fixtures::DEMO_SUBJECT;
        let mine = verify_agent_report(&report, &root, Some((owner, owner)));
        assert_eq!(mine.owner_scope_ok, Some(true));
        let not_mine = verify_agent_report(&report, &root, Some(("dregg:somebodyelse00", owner)));
        assert_eq!(not_mine.owner_scope_ok, Some(false));
        // The crypto verdict still holds — a self-contained proof verifies for anyone.
        assert!(not_mine.ok);
    }
}

//! **Drive a goal into a session.** The seam between the web attach and whatever
//! actually runs the agent — given a [`GoalRequest`] (a natural-language goal + a
//! budget + a cap bundle) and an owner subject, a [`SessionDriver`] deploys the
//! agent, runs the reason→act→observe loop confined (every action cap-gated +
//! metered + receipted), and returns the [`AgentSession`] (the re-witnessable
//! `LiveRun` + its owner).
//!
//! The shipped [`DemoDriver`] runs the **scripted planner** path: it maps the goal
//! + the granted bundle into a real plan and drives it through the *genuine*
//! `dreggnet_exec::agent` braid (deploy → run-with-toolkit → seal a signed receipt
//! chain), so the transcript, the budget draw, the receipts, and the in-browser
//! re-witness are all real — only the *brain* is scripted rather than a live model.
//! It deliberately attempts ONE out-of-bundle tool so the cap-gate ✗ is visible
//! and the teeth are non-vacuous.
//!
//! The **reviewed-go** swap is a `SessionDriver` backed by the live hosted session
//! backend (the sibling SSH/Hermes lane's live Kimi/OpenAI-compatible brain over a
//! real confined workdir, `dregg_agent::brain` + `dregg_agent::tools`). The driver
//! seam is the only thing that changes; the cap-scoping, the stream, the budget
//! meter, and the verify here are brain-agnostic and complete.

use std::collections::BTreeMap;

use dreggnet_exec::agent::{
    AgentAction, AgentCloud, AgentSpec, PlannedBrain, ToolKit, ToolOutcome, WitnessedRun,
};
use dreggnet_exec::live::{LiveRun, transcript_of};

use crate::session::{AgentSession, GoalRequest};

/// Deploy + run a goal into a hosted session. The single seam the demo planner
/// and the live Hermes brain both implement.
pub trait SessionDriver: Send + Sync {
    /// Drive `req` for `owner`, returning the session under the stable `id`.
    fn drive(&self, req: &GoalRequest, owner: &str, id: &str) -> AgentSession;
}

/// The deterministic demo planner — the shipped, green-standalone drive path.
pub struct DemoDriver {
    /// `Some(seed)` makes every drive reproducible (per-session clouds are derived
    /// from this base seed + the session id); `None` uses a fresh random root.
    base_seed: Option<[u8; 32]>,
}

impl Default for DemoDriver {
    fn default() -> Self {
        DemoDriver::new()
    }
}

impl DemoDriver {
    /// A driver with a fresh random root per session.
    pub fn new() -> DemoDriver {
        DemoDriver { base_seed: None }
    }

    /// A driver whose drives are reproducible from `seed` (tests / fixtures).
    pub fn seeded(seed: [u8; 32]) -> DemoDriver {
        DemoDriver {
            base_seed: Some(seed),
        }
    }

    /// The cloud for one drive: a fresh meter so sessions are independent, with a
    /// per-session root seed derived deterministically when seeded.
    fn cloud_for(&self, id: &str) -> AgentCloud {
        match self.base_seed {
            Some(base) => AgentCloud::from_seed(mix_seed(base, id)),
            None => AgentCloud::new(),
        }
    }
}

impl SessionDriver for DemoDriver {
    fn drive(&self, req: &GoalRequest, owner: &str, id: &str) -> AgentSession {
        let req = req.sanitized();
        let agent_id = format!("agent:{id}");

        // (1) the spec: the budget the user set + the cap bundle they chose.
        let mut spec = AgentSpec::new(&agent_id, req.budget.max(1));
        for s in &req.services {
            spec = spec.with_service(s);
        }
        for c in &req.cells {
            spec = spec.with_cell(c);
        }

        // (2) the plan the scripted brain emits from the goal + bundle.
        let plan = goal_to_plan(&req);

        // (3) deploy + run confined through the genuine braid.
        let cloud = self.cloud_for(id);
        let handle = cloud
            .deploy(&spec)
            .expect("deploy the demo session agent (budget > 0)");
        let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &DemoToolkit);

        let run = LiveRun {
            goal: req.goal.clone(),
            model: "dregg-demo-planner (scripted; live Hermes/Kimi brain is the reviewed-go swap)"
                .to_string(),
            endpoint: "(none — scripted demo planner)".to_string(),
            // Not a live model call — the plan is scripted. Mark it so `run.json` is honest
            // standalone (the tools/braid ran for real; the brain decisions did not).
            brain_mode: "replay".to_string(),
            funding: "operator allowance (demo)".to_string(),
            budget_cents: req.budget.max(1),
            caps: handle.caps.clone(),
            workdir: "(invoke-only demo; the live confined workdir is the reviewed-go backend)"
                .to_string(),
            transcript: transcript_of(&report),
            run: report,
            subagent_run: None,
        };

        AgentSession {
            id: id.to_string(),
            owner: owner.to_string(),
            created_at: crate::now_rfc3339(),
            parent: None,
            run,
        }
    }
}

/// Map a goal + its granted bundle into a concrete plan: record the goal (if a
/// cell is granted), exercise each granted service in turn, and deliberately
/// attempt ONE out-of-bundle tool so the cap-gate refusal is visible (the teeth).
fn goal_to_plan(req: &GoalRequest) -> Vec<AgentAction> {
    let mut plan = Vec::new();
    if let Some(cell) = req.cells.first() {
        plan.push(AgentAction::CellWrite {
            path: cell.clone(),
            value: format!("goal: {}", req.goal),
        });
    }
    for s in &req.services {
        plan.push(AgentAction::Invoke { service: s.clone() });
    }
    // The reason→act→observe agent probes a tool it was NOT granted — and is
    // refused before any effect. This makes the ✗ in the transcript real, not
    // decorative: the cap-gate, exercised non-vacuously every run.
    plan.push(AgentAction::Invoke {
        service: "exfiltrate".to_string(),
    });
    plan
}

/// A demo toolkit: an admitted `invoke` returns a **canned** verdict. The
/// QA-shaped services (`run_tests` / `verify_deploy`) carry a [`WitnessedRun`]
/// execution binding, but the in-browser re-witness (`verify_live`) only checks the
/// receipt chain (signatures + budget bound) — it does NOT re-execute the
/// `WitnessedRun` (that is `verify_witnessed_qa`, not on this path). So the signature
/// proves only "the host recorded this verdict and didn't edit it," NOT that any
/// tests actually ran. The verdict strings therefore say so out loud (a demo/canned
/// verdict), so the cockpit's green pill does not overstate what it attests. Wiring
/// `verify_witnessed_qa` into `verify_live` (re-running the bound `(command,
/// code_root)`) is the named step that would let these read as truly verified.
struct DemoToolkit;

impl ToolKit for DemoToolkit {
    fn invoke(
        &self,
        service: &str,
        _amount_cents: Option<i64>,
        _cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        match service {
            "run_tests" => ToolOutcome::pass(
                "demo verdict (canned — not re-witnessed): tests 34 passed, 0 failed",
            )
            .with_witness(WitnessedRun {
                command: "run_tests[lang=wat,tier=Sandboxed,entry=run]".to_string(),
                code_root: "demo-session-code-root".to_string(),
                exit: 0,
                output_digest: [9u8; 32],
            }),
            "verify_deploy" => ToolOutcome::pass(
                "demo verdict (canned — not re-witnessed): deploy 12/12 checks green",
            )
            .with_witness(WitnessedRun {
                command: "verify_deploy[lang=wat,tier=Sandboxed,entry=run]".to_string(),
                code_root: "demo-session-code-root".to_string(),
                exit: 0,
                output_digest: [7u8; 32],
            }),
            other => ToolOutcome::pass(format!("{other}: ok (demo — not re-witnessed)")),
        }
    }
}

/// Derive a deterministic per-session seed from a base seed + the session id, so
/// each session in a seeded store has an independent-but-reproducible root.
fn mix_seed(base: [u8; 32], id: &str) -> [u8; 32] {
    let mut out = base;
    let idb = id.as_bytes();
    for (i, b) in out.iter_mut().enumerate() {
        let k = idb.get(i % idb.len().max(1)).copied().unwrap_or(0);
        *b = b.wrapping_add(k).wrapping_add(i as u8);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_exec::live::verify_live;

    fn demo_req() -> GoalRequest {
        GoalRequest::new("deploy my site and prove the tests pass", 50)
            .with_service("run_tests")
            .with_service("verify_deploy")
            .with_cell("/goal")
    }

    // ── a goal drives a REAL, re-witnessable session ───────────────────────────
    #[test]
    fn a_goal_drives_a_re_witnessable_session() {
        let s =
            DemoDriver::seeded([1u8; 32]).drive(&demo_req(), "dregg:demo0001demo0001", "sess_a");
        assert_eq!(s.id, "sess_a");
        assert_eq!(s.owner, "dregg:demo0001demo0001");
        assert_eq!(s.goal(), "deploy my site and prove the tests pass");
        // The receipts accumulated + the budget drew.
        assert!(s.receipts() >= 2, "the granted invokes sealed receipts");
        assert!(s.consumed() > 0, "the budget drew down");
        assert_eq!(s.consumed() + s.headroom(), s.budget());
        // The cap-gate refused the out-of-bundle probe (the teeth, non-vacuous).
        assert!(s.cap_refused() >= 1, "the exfiltrate probe was refused");
        // The whole thing re-witnesses with the SSH attach's own verify.
        let v = verify_live(&s.run).expect("the session re-witnesses");
        assert_eq!(v.consumed, s.consumed());
    }

    // ── the granted bundle is exactly what the goal request asked for ──────────
    #[test]
    fn the_granted_bundle_matches_the_request() {
        let s =
            DemoDriver::seeded([2u8; 32]).drive(&demo_req(), "dregg:demo0001demo0001", "sess_b");
        let caps = s.caps().join(" ");
        assert!(caps.contains("invoke:run_tests"));
        assert!(caps.contains("invoke:verify_deploy"));
        assert!(caps.contains("cell-write:/goal"));
        // It was NOT granted exfiltrate — hence the refusal.
        assert!(!caps.contains("invoke:exfiltrate"));
    }

    // ── a tiny budget CONTAINS the run (the bound bites) ───────────────────────
    #[test]
    fn a_tiny_budget_contains_the_run() {
        // Budget 1 admits exactly one action; the rest are budget-refused.
        let req = GoalRequest::new("do a lot", 1)
            .with_service("run_tests")
            .with_service("verify_deploy")
            .with_cell("/goal");
        let s = DemoDriver::seeded([5u8; 32]).drive(&req, "dregg:demo0001demo0001", "sess_c");
        assert!(s.consumed() <= s.budget(), "never past the ceiling");
        assert!(
            s.budget_refused() >= 1,
            "the over-budget actions were contained"
        );
        assert!(verify_live(&s.run).is_ok(), "still re-witnesses");
    }
}

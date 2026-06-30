//! `session` — the **hosted, persistent, multi-goal agent session**: the
//! interactive twin of the one-shot [`live`](crate::live) run, and the unit a
//! hosting layer rents out per user.
//!
//! A one-shot run ([`AgentCloud::run_with_toolkit`](crate::agent::AgentCloud::run_with_toolkit))
//! takes ONE goal, runs it to completion, and emits one receipt chain. A
//! **session** is the generalization a *hosted* agent needs: a user attaches
//! (over SSH, or the portal), types a goal, watches it run, types the next goal —
//! and across the whole conversation:
//!
//! 1. **the budget draws down** — the session's [`AgentCloud`] meter cell is keyed
//!    by the agent id, so each goal's draws accumulate against the one ceiling; an
//!    exhausted session refuses further actions in-band (no per-goal budget reset
//!    a runaway could exploit);
//! 2. **the receipt chain accumulates** — goal 2's first receipt links to goal 1's
//!    last (the [`SessionState`] holds the [`ReceiptChain`](crate::receipt::ReceiptChain)
//!    across goals), so the whole session is ONE re-witnessable artifact and a
//!    spliced-out goal breaks the chain;
//! 3. **the cap bundle is fixed** — minted once at [`Session::open`] and never
//!    widened; every goal's every tool call is cap-gated against it.
//!
//! ## The firmament framing: a session is a cell you attach to
//!
//! Each session owns its **own** [`AgentCloud`] — its own root authority + its own
//! meter. So two users' sessions are isolated by construction: user A's `dga1_`
//! bundle is minted under root A and *cannot verify* under root B, and the two
//! budget cells are separate. The attach (SSH / portal) is then "one cap across
//! distance" — the user drives a confined cell that runs server-side, and walks
//! away with a proof of everything it did and a hard bound on everything it could
//! have done. Multi-user isolation is not a policy the host enforces; it is the
//! shape of the construction.
//!
//! ## What stays a host concern
//!
//! This type is the substrate session core (std-only, no HTTP, no SSH). The host
//! maps an SSH key / token → an account id + a budget + a cap bundle and opens a
//! [`Session`] for it; the brain (Hermes / Nemotron) and the operator tools run
//! server-side behind the [`AgentBrain`] / [`ToolKit`] seams. The SSH attach is a
//! forced-command that drops the connecting user into [`Session::run_goal`] over
//! stdin/stdout — see the `dregg-agent attach` bin (and the hosting layer's
//! `HOSTED-AGENT-SESSIONS.md`).

use serde::{Deserialize, Serialize};

use crate::agent::{
    AgentBrain, AgentCloud, AgentError, AgentHandle, AgentRunReport, AgentSpec, AgentVerified,
    AgentVerifyError, SessionState, ToolKit, op, verify_agent_run,
};
use crate::grant::CapGrant;
use crate::live::{LiveStep, transcript_of_slices};

/// A parsed cap bundle: the [`AgentSpec`] (budget + the signed grants) plus the
/// advertised tool/service/cell vocabulary the brain is told it may call. The
/// reusable string → bundle parser a host or a REPL builds a session from — the
/// product's one place that turns `"shell,fs,http:api.github.com,pay:openai"`
/// into a deployable, attenuable authority.
#[derive(Clone, Debug)]
pub struct CapBundle {
    /// The deployable spec (the budget ceiling + the resource-scoped grants).
    pub spec: AgentSpec,
    /// The flat `invoke` services advertised to the brain.
    pub services: Vec<String>,
    /// The operator-tool names advertised to the brain (`shell`, `http_get`, …).
    pub op_tools: Vec<String>,
    /// The cells the agent may read/write.
    pub cells: Vec<String>,
}

/// Parse a comma-separated cap string into a [`CapBundle`] for `id` with `budget`,
/// resolving fs grants against `workdir`. The grammar (each token a per-tool /
/// per-resource grant a sub-agent can only narrow):
///
/// - `shell` — a real shell (workdir-confined by the runner);
/// - `fs` — read+write under `workdir`;
/// - `http:HOST` / `git:HOST` — egress to one host;
/// - `pay:VENDOR` — the Stripe Link skill for one vendor; `spend` — any vendor;
/// - `provision:PROVIDER` — the Stripe Projects skill for one provider;
/// - `cell:/path` — read+write a named cell;
/// - any bare token — a flat `invoke` service (e.g. `run_tests`).
pub fn parse_caps(caps: &str, id: &str, budget: i64, workdir: &str) -> Result<CapBundle, String> {
    let mut spec = AgentSpec::new(id, budget);
    let mut services = Vec::new();
    let mut op_tools = Vec::new();
    let mut cells = Vec::new();
    for tok in caps.split(',').map(str::trim).filter(|t| !t.is_empty()) {
        match tok {
            "shell" => {
                spec = spec.with_shell();
                op_tools.push(op::SHELL.to_string());
            }
            "fs" => {
                spec = spec.with_workdir_fs(workdir);
                for t in [op::FS_READ, op::FS_WRITE, op::LIST_DIR, op::MKDIR] {
                    op_tools.push(t.to_string());
                }
            }
            t if t.starts_with("pay:") => {
                let vendor = &t["pay:".len()..];
                spec = spec.with_stripe_pay(vendor);
                op_tools.push(op::STRIPE_PAY.to_string());
            }
            "spend" => {
                spec = spec.with_grant(CapGrant::Prefix("pay:".to_string()));
                op_tools.push(op::STRIPE_PAY.to_string());
            }
            t if t.starts_with("provision:") => {
                let provider = &t["provision:".len()..];
                spec = spec.with_stripe_provision(provider);
                op_tools.push(op::STRIPE_PROVISION.to_string());
            }
            t if t.starts_with("http:") => {
                let host = &t["http:".len()..];
                spec = spec.with_http_host(host);
                op_tools.push(op::HTTP_GET.to_string());
            }
            t if t.starts_with("git:") => {
                let host = &t["git:".len()..];
                spec = spec.with_http_host(host);
                op_tools.push(op::GIT_CLONE.to_string());
            }
            t if t.starts_with("cell:") => {
                let path = &t["cell:".len()..];
                spec = spec.with_cell(path);
                cells.push(path.to_string());
            }
            other => {
                spec = spec.with_service(other);
                services.push(other.to_string());
            }
        }
    }
    op_tools.sort();
    op_tools.dedup();
    Ok(CapBundle {
        spec,
        services,
        op_tools,
        cells,
    })
}

/// What one typed goal did — the **delta** the session added for it: only the
/// steps this goal produced (not the whole session), plus the running totals
/// after it. The REPL prints this per goal; the cumulative proof is the session's
/// [`report`](Session::report).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GoalReport {
    /// The natural-language goal the user typed.
    pub goal: String,
    /// The narrated reason → act → observe steps THIS goal added (cap-gated ·
    /// metered · receipted), each tracing to a receipt or a refusal.
    pub steps: Vec<LiveStep>,
    /// Actions this goal got admitted.
    pub admitted: u64,
    /// Actions this goal got cap-refused (outside the fixed bundle).
    pub cap_refused: u64,
    /// Actions this goal got budget-refused (the session ceiling bit).
    pub budget_refused: u64,
    /// The session's total consumed budget AFTER this goal (the running meter).
    pub consumed: i64,
    /// The session's remaining headroom AFTER this goal (the could-still-do bound).
    pub headroom: i64,
}

/// A **hosted, persistent agent session** — one user's confined agent on the
/// cloud, scoped to their account + budget + cap bundle, driven goal by goal.
///
/// Open it once ([`open`](Session::open)); feed it goals
/// ([`run_goal`](Session::run_goal)) each of which runs a real reason → act →
/// observe loop bounded by the *remaining* budget and gated by the fixed bundle;
/// re-witness the whole thing at any time ([`verify`](Session::verify)). Its own
/// [`AgentCloud`] is what makes two sessions provably isolated.
pub struct Session {
    /// The owner account this session is scoped to (a `dga1_`/webauth account id,
    /// or any stable per-user tag). Bound into the agent id, so the receipts name
    /// whose session it was.
    account: String,
    /// This session's OWN cloud — its own root authority + its own meter cell. The
    /// isolation boundary: another session's bundle does not verify under this root.
    cloud: AgentCloud,
    /// The deployed agent (the cap bundle as a `dga1_` credential + the ceiling).
    handle: AgentHandle,
    /// The persistent run state (the chain · cells · counts · seq) across goals.
    state: SessionState,
    /// One [`GoalReport`] per goal run, in order — the session history.
    history: Vec<GoalReport>,
}

impl Session {
    /// **Open a session** for `account` with `spec` (the budget ceiling + the cap
    /// bundle the host granted). Mints a fresh root + meter for THIS session (the
    /// isolation boundary) and deploys the agent under it. The `spec.id` is
    /// overridden to bind the agent to the account.
    pub fn open(account: impl Into<String>, spec: AgentSpec) -> Result<Session, AgentError> {
        Session::open_in(AgentCloud::new(), account, spec)
    }

    /// [`open`](Session::open) with a deterministic root seed — reproducible
    /// sessions for tests / recorded demos (the credential + signer are stable).
    pub fn open_seeded(
        seed: [u8; 32],
        account: impl Into<String>,
        spec: AgentSpec,
    ) -> Result<Session, AgentError> {
        Session::open_in(AgentCloud::from_seed(seed), account, spec)
    }

    fn open_in(
        cloud: AgentCloud,
        account: impl Into<String>,
        mut spec: AgentSpec,
    ) -> Result<Session, AgentError> {
        let account = account.into();
        // Bind the agent id to the account, so the meter subject + the receipt
        // identity name WHOSE session it is — and two accounts' sessions get
        // distinct receipt-chain signers (the chain seed is derived from the id).
        spec.id = format!("agent:session:{account}");
        let handle = cloud.deploy(&spec)?;
        let state = SessionState::new(&handle.id);
        Ok(Session {
            account,
            cloud,
            handle,
            state,
            history: Vec::new(),
        })
    }

    /// **Run one typed goal** through the session: drive `brain` (a live model, a
    /// confined Hermes harness, or a recorded transport) against `toolkit` (the
    /// real shell / fs / http / Stripe tools), bounded by the session's *remaining*
    /// budget and gated by its fixed bundle. The receipt chain keeps linking and
    /// the budget keeps drawing down. Returns the delta [`GoalReport`] for this
    /// goal (also pushed onto the session [`history`](Session::history)).
    pub fn run_goal(
        &mut self,
        goal: impl Into<String>,
        brain: &mut dyn AgentBrain,
        toolkit: &dyn ToolKit,
    ) -> GoalReport {
        let goal = goal.into();
        // Mark the cumulative log/receipt lengths + counts BEFORE the goal, so the
        // delta (just this goal's steps) can be sliced out afterward.
        let prev_log = self.state.log().len();
        let prev_receipts = self.state.receipts().len();
        let prev_admitted = self.state.admitted();
        let prev_cap = self.state.cap_refused();
        let prev_budget = self.state.budget_refused();

        let report = self
            .cloud
            .run_goal(&self.handle, &mut self.state, brain, toolkit);

        let steps = transcript_of_slices(
            &self.state.log()[prev_log..],
            &self.state.receipts()[prev_receipts..],
        );
        let gr = GoalReport {
            goal,
            steps,
            admitted: self.state.admitted() - prev_admitted,
            cap_refused: self.state.cap_refused() - prev_cap,
            budget_refused: self.state.budget_refused() - prev_budget,
            consumed: report.consumed,
            headroom: report.headroom,
        };
        self.history.push(gr.clone());
        gr
    }

    /// **Re-witness the whole session, trusting no host** — the cumulative receipt
    /// chain is signed + unbroken + tamper-evident across every goal, the consumed
    /// budget stays at/under the ceiling, and the chain tip agrees with the total.
    /// The same `verify_agent_run` a non-witness runs; a tampered receipt in ANY
    /// goal breaks it.
    pub fn verify(&self) -> Result<AgentVerified, AgentVerifyError> {
        verify_agent_run(&self.report())
    }

    /// The cumulative run report — the whole session as one re-witnessable
    /// artifact (every goal's receipts in one chain + the current bound).
    pub fn report(&self) -> AgentRunReport {
        self.cloud.session_report(&self.handle, &self.state)
    }

    /// The owner account this session is scoped to.
    pub fn account(&self) -> &str {
        &self.account
    }

    /// The agent id (the meter subject + receipt identity).
    pub fn agent_id(&self) -> &str {
        &self.handle.id
    }

    /// The granted cap bundle (display form; a resource prefix renders with `*`).
    pub fn caps(&self) -> &[String] {
        &self.handle.caps
    }

    /// The session's `dga1_` bearer credential (the cap bundle on the wire).
    pub fn credential(&self) -> &str {
        &self.handle.credential
    }

    /// The budget ceiling (the hard bound on the whole session).
    pub fn budget(&self) -> i64 {
        self.handle.budget
    }

    /// The asset the budget is denominated in.
    pub fn asset(&self) -> &str {
        &self.handle.asset
    }

    /// Total budget consumed across the session so far.
    pub fn consumed(&self) -> i64 {
        self.report().consumed
    }

    /// The remaining headroom — the bound on everything the session could still do.
    pub fn headroom(&self) -> i64 {
        (self.budget() - self.consumed()).max(0)
    }

    /// `true` iff the session has spent its whole ceiling (no headroom left — any
    /// further priced action is refused in-band).
    pub fn exhausted(&self) -> bool {
        self.headroom() <= 0
    }

    /// The per-goal history, in order.
    pub fn history(&self) -> &[GoalReport] {
        &self.history
    }

    /// How many goals have been run.
    pub fn goal_count(&self) -> usize {
        self.history.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{AgentAction, ToolCall};
    use crate::receipt::ChainError;
    use crate::toolkit::Toolkit;
    use crate::tools::{OperatorTools, ShellOut};
    use std::path::Path;

    /// A deterministic, side-effect-light toolkit: a `shell` that echoes its cmd.
    fn echo_toolkit(wd: &Path) -> OperatorTools {
        OperatorTools::new(Toolkit::new(), wd).with_shell(|cmd: &str, _cwd: &Path| {
            Ok(ShellOut {
                exit: 0,
                stdout: format!("ran: {cmd}"),
                stderr: String::new(),
                new_cwd: None,
            })
        })
    }

    /// A recorded brain: a fixed plan of shell ops (the "model" decided these). One
    /// per goal — the REPL hands a fresh brain per typed goal.
    fn shell_plan(cmds: &[&str]) -> crate::agent::PlannedBrain {
        let plan = cmds
            .iter()
            .map(|c| AgentAction::Op(ToolCall::new("shell", [("cmd".to_string(), c.to_string())])))
            .collect();
        crate::agent::PlannedBrain::new(plan)
    }

    fn wd() -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!(
            "dregg-session-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    // ── the budget draws down ACROSS goals (the persistent meter) ─────────────

    #[test]
    fn the_budget_draws_down_across_goals() {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", 10).with_shell();
        let mut sess = Session::open_seeded([11u8; 32], "dga1_alice", spec).unwrap();

        // Goal 1: three shell ops → 3 drawn.
        let g1 = sess.run_goal("do three things", &mut shell_plan(&["a", "b", "c"]), &tk);
        assert_eq!(g1.admitted, 3);
        assert_eq!(g1.consumed, 3);
        assert_eq!(g1.headroom, 7, "10 − 3");
        assert_eq!(g1.steps.len(), 3);

        // Goal 2: four more → the budget CONTINUES from 3 (does not reset).
        let g2 = sess.run_goal("do four more", &mut shell_plan(&["d", "e", "f", "g"]), &tk);
        assert_eq!(g2.admitted, 4);
        assert_eq!(g2.consumed, 7, "3 + 4 — the meter persisted across goals");
        assert_eq!(g2.headroom, 3);

        // Goal 3: a runaway of 100 ops → only the remaining 3 are admitted, the
        // rest refused in-band by the SESSION ceiling (no per-goal reset).
        let many: Vec<&str> = (0..100).map(|_| "x").collect();
        let g3 = sess.run_goal("runaway", &mut shell_plan(&many), &tk);
        assert_eq!(g3.admitted, 3, "only the session's remaining headroom");
        assert!(g3.budget_refused >= 1, "the rest are contained in-band");
        assert_eq!(sess.consumed(), 10, "the ceiling is fully drawn");
        assert!(sess.exhausted());

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── the receipt chain ACCUMULATES + re-witnesses as ONE artifact ──────────

    #[test]
    fn the_session_re_witnesses_as_one_chain_and_a_tamper_is_caught() {
        let dir = wd();
        let tk = echo_toolkit(&dir);
        let spec = AgentSpec::new("ignored", 20).with_shell();
        let mut sess = Session::open_seeded([12u8; 32], "dga1_bob", spec).unwrap();

        sess.run_goal("g1", &mut shell_plan(&["a", "b"]), &tk);
        sess.run_goal("g2", &mut shell_plan(&["c", "d", "e"]), &tk);

        // The whole session is ONE chain of 5 admitted actions.
        let v = sess.verify().expect("the session re-witnesses");
        assert_eq!(v.actions, 5, "both goals in one chain");
        assert_eq!(v.consumed, 5);

        // Tamper a receipt from the FIRST goal → the cumulative chain breaks.
        let mut report = sess.report();
        report.receipts[0].action = "shell:forged".into();
        assert!(matches!(
            verify_agent_run(&report),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));

        // Splice out a whole goal's receipt → the chain link breaks.
        let mut spliced = sess.report();
        spliced.receipts.remove(2);
        assert!(matches!(
            verify_agent_run(&spliced),
            Err(AgentVerifyError::Chain(ChainError::BrokenLink { .. }))
        ));

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── a cap outside the FIXED bundle is refused (every goal) ────────────────

    #[test]
    fn an_out_of_bundle_tool_is_refused_in_every_goal() {
        let dir = wd();
        // The bundle grants shell + http:api.github.com, but NOT http:evil.example.
        let tk = OperatorTools::new(Toolkit::new(), &dir)
            .with_shell(|cmd: &str, _| {
                Ok(ShellOut {
                    exit: 0,
                    stdout: cmd.into(),
                    stderr: String::new(),
                    new_cwd: None,
                })
            })
            .with_http(|_url| {
                Ok(crate::tools::HttpResp {
                    status: 200,
                    body: "ok".into(),
                })
            });
        let spec = AgentSpec::new("ignored", 20)
            .with_shell()
            .with_http_host("api.github.com");
        let mut sess = Session::open_seeded([13u8; 32], "dga1_carol", spec).unwrap();

        // A goal that tries to reach an UN-granted host → cap-refused, no receipt.
        let plan = crate::agent::PlannedBrain::new(vec![
            AgentAction::Op(ToolCall::new(
                "http_get",
                [("url".to_string(), "https://evil.example/x".to_string())],
            )),
            AgentAction::Op(ToolCall::new(
                "shell",
                [("cmd".to_string(), "echo ok".to_string())],
            )),
        ]);
        let mut brain = plan;
        let g = sess.run_goal("try to exfiltrate", &mut brain, &tk);
        assert_eq!(g.cap_refused, 1, "the un-granted host is refused");
        assert_eq!(g.admitted, 1, "the in-bundle shell still runs");
        // The refusal left no receipt; the session still re-witnesses.
        sess.verify().expect("session still verifies");

        std::fs::remove_dir_all(&dir).ok();
    }

    // ── multi-user ISOLATION: two sessions cannot touch each other ────────────

    #[test]
    fn two_sessions_are_isolated_by_construction() {
        let dir = wd();
        let tk = echo_toolkit(&dir);

        let mut alice = Session::open_seeded(
            [21u8; 32],
            "dga1_alice",
            AgentSpec::new("ignored", 5).with_shell(),
        )
        .unwrap();
        let mut bob = Session::open_seeded(
            [22u8; 32],
            "dga1_bob",
            AgentSpec::new("ignored", 100).with_shell(),
        )
        .unwrap();

        // Alice burns her whole (small) budget.
        let many: Vec<&str> = (0..50).map(|_| "x").collect();
        alice.run_goal("burn", &mut shell_plan(&many), &tk);
        assert_eq!(alice.consumed(), 5, "alice bounded by HER ceiling");
        assert!(alice.exhausted());

        // Bob is untouched — his budget + his chain are entirely separate.
        assert_eq!(bob.consumed(), 0, "bob's budget is his own");
        bob.run_goal("work", &mut shell_plan(&["a", "b"]), &tk);
        assert_eq!(bob.consumed(), 2);
        assert!(!bob.exhausted());

        // The isolation is cryptographic: each session's credential verifies ONLY
        // under its own root. Bob's bundle is not Alice's bundle.
        assert_ne!(alice.credential(), bob.credential());
        // Their receipt chains have different signers (different roots/seeds).
        assert_ne!(alice.report().signer, bob.report().signer);

        std::fs::remove_dir_all(&dir).ok();
    }
}

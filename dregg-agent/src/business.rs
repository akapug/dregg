//! `business` — the **autonomous business you can audit**, end to end.
//!
//! "Acme Test-as-a-Service, run by an agent." This module wires the five beats of
//! the hackathon demo into one deterministic, offline-by-default run that emits a
//! [`BusinessRun`] (the `run.json` P&L) and re-witnesses it host-untrusted:
//!
//! 1. **EARN** — a customer pays Acme: the genuine Stripe verify+mint
//!    ([`crate::stripe`]) over a recorded signed webhook mints conserved,
//!    receipted USD-credit. A retry is deduped; a forged signature is refused.
//! 2. **FUND** — the minted cents become the agent's [`AgentSpec`] budget ceiling
//!    (USD-cents denominated), closing the P&L loop: earned money is spendable.
//! 3. **OPERATE** — the brain ([`OpenAICompatBrain`] on the recorded transport,
//!    "Hermes/Nemotron") runs the customer's test job; the verdict is bound into
//!    the receipt with a [`WitnessedRun`] re-checked by [`verify_witnessed_qa`].
//! 4. **SPEND** — the agent pays its vendors through the **budget-gated,
//!    variable-amount** `stripe_pay` rail: two spends succeed, an over-ceiling
//!    spend is refused **in-band before any money moves** (the budget is a theorem
//!    about the cell, not a watchdog).
//! 5. **SCALE** — `deploy_subagent` forks a sub-agent with an attenuated budget +
//!    cap bundle it provably cannot exceed (over-budget AND out-of-bundle refused).
//!
//! [`verify_business`] re-witnesses the WHOLE P&L offline (the earn mint chain, the
//! agent + sub-agent receipt chains, the witnessed QA, and the P&L arithmetic), so
//! `dregg-agent verify run.json` needs only the file.

use serde::{Deserialize, Serialize};

use crate::agent::{AgentAction, AgentBrain, PlannedBrain};
use crate::agent::{
    AgentCloud, AgentRunReport, AgentSpec, WitnessedRun, verify_agent_run, verify_witnessed_qa,
};
use crate::brain::{OpenAICompatBrain, ProviderKey, RecordedOpenAICaller};
use crate::receipt::verify_chain;
use crate::stripe::{MintReceipt, StripeMirror, StripeWebhook, payment_intent_succeeded};
use crate::toolkit::{HealthSnapshot, RunReport, Toolkit, code_root, rewitness_run_tests};

/// The webhook signing secret the demo's recorded Stripe events are signed under
/// (a fixture `whsec_` — NOT a real key). Verification is genuine HMAC-SHA256.
pub const DEMO_WEBHOOK_SECRET: &[u8] = b"whsec_dregg_demo_fixture_secret_v1";

/// The asset the USD-credit mirror + the agent budget are denominated in (1 = 1¢).
pub const USD_CENTS: &str = "USD-CENTS";

/// The customer's test suite (a tiny WAT module reporting `0` = green). Its
/// `code_root` is the deployed root the witnessed QA ties to.
pub const SUITE_SRC: &str = "(module (func (export \"run\") (result i32) (i32.const 0)))";

/// One earn-side event and what the verify+mint did with it.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EarnEvent {
    /// A human label for the beat (`customer payment`, `webhook retry`, …).
    pub label: String,
    /// The Stripe payment-intent id.
    pub intent_id: String,
    /// The cents the webhook claimed.
    pub amount_cents: i64,
    /// The outcome: `MINTED`, `REFUSED (double-mint)`, `REFUSED (forged signature)`.
    pub outcome: String,
}

/// The EARN ledger: the conserved mint receipts + the events that produced them.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EarnReport {
    /// The minted asset (USD-cents mirror).
    pub asset: String,
    /// The net cents minted (the sum that funds the budget).
    pub minted_cents: i64,
    /// Every earn event (minted / deduped / forged).
    pub events: Vec<EarnEvent>,
    /// The conserved, chained mint receipts (re-witnessable with [`verify_chain`]).
    pub receipts: Vec<MintReceipt>,
    /// The mint-chain signer public key.
    pub signer: [u8; 32],
}

/// The P&L summary — every figure recomputable from the chains.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Pnl {
    /// Revenue: the cents earned (minted) from the customer.
    pub earned_cents: i64,
    /// Vendor outflow: the cents paid out through the budget-gated spend rail.
    pub vendor_spend_cents: i64,
    /// Operations metering: the in-budget draws for the work (deploy + test).
    pub ops_metering_cents: i64,
    /// Net margin = budget − consumed = the un-drawn headroom (the could-have bound).
    pub net_cents: i64,
    /// The budget ceiling (= earned cents; the funded allowance).
    pub budget_cents: i64,
    /// The un-spent headroom — the hard bound on everything the agent could still do.
    pub headroom_cents: i64,
}

/// The whole run — the `run.json` artifact a non-witness re-verifies offline.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BusinessRun {
    /// The business name (for display).
    pub business: String,
    /// The EARN ledger (verify+mint over the recorded webhooks).
    pub earn: EarnReport,
    /// The customer's test-suite source (so the witnessed QA can be re-executed).
    pub suite_src: String,
    /// The deployed code root the witnessed QA ties to (= `code_root(suite_src)`).
    pub deployed_root: String,
    /// The main agent run (OPERATE + SPEND), one re-witnessable receipt chain.
    pub agent_run: AgentRunReport,
    /// The forked sub-agent run (SCALE), attenuated + bounded.
    pub subagent_run: AgentRunReport,
    /// The P&L summary.
    pub pnl: Pnl,
}

// ── EARN ──────────────────────────────────────────────────────────────────────

/// Run the EARN beat: verify+mint a genuine signed webhook, then show a retry
/// deduped and a forged-signature webhook refused. Returns the ledger + the net
/// minted cents that fund the agent.
pub fn earn(recipient: &str) -> EarnReport {
    // A deterministic clock just inside the replay window.
    let signed_at = 1_700_000_000u64;
    let now = Some(signed_at + 5);
    let mut mirror = StripeMirror::new(
        USD_CENTS,
        DEMO_WEBHOOK_SECRET,
        "usd",
        50,
        100_000_000,
        [0xEAu8; 32],
    );

    let mut events = Vec::new();
    let mut receipts = Vec::new();

    // (1) the customer pays Acme $50.00 — a genuine signed webhook.
    let body = payment_intent_succeeded("pi_acme_invoice_42", 5000, "usd");
    let webhook = StripeWebhook::sign(&body, DEMO_WEBHOOK_SECRET, signed_at);
    match mirror.mint_against_webhook(&webhook, recipient, now) {
        Ok(r) => {
            events.push(EarnEvent {
                label: "customer payment".into(),
                intent_id: r.payment_intent_id.clone(),
                amount_cents: r.amount_cents,
                outcome: "MINTED".into(),
            });
            receipts.push(r);
        }
        Err(e) => events.push(EarnEvent {
            label: "customer payment".into(),
            intent_id: "pi_acme_invoice_42".into(),
            amount_cents: 5000,
            outcome: format!("REFUSED ({e})"),
        }),
    }

    // (2) Stripe retries the SAME event — refused (double-mint prevented).
    let retry = mirror.mint_against_webhook(&webhook, recipient, now);
    events.push(EarnEvent {
        label: "webhook retry".into(),
        intent_id: "pi_acme_invoice_42".into(),
        amount_cents: 5000,
        outcome: match retry {
            Err(e) => format!("REFUSED ({e})"),
            Ok(_) => "MINTED (BUG: retry double-minted)".into(),
        },
    });

    // (3) an attacker forges a $9,999.99 webhook (signs $0.01, swaps the body) —
    //     refused: the v1 signature no longer matches the body.
    let small = payment_intent_succeeded("pi_attacker", 1, "usd");
    let big = payment_intent_succeeded("pi_attacker", 999_999, "usd");
    let forged = StripeWebhook::sign(&small, DEMO_WEBHOOK_SECRET, signed_at).with_forged_body(&big);
    let forged_res = mirror.mint_against_webhook(&forged, recipient, now);
    events.push(EarnEvent {
        label: "forged webhook".into(),
        intent_id: "pi_attacker".into(),
        amount_cents: 999_999,
        outcome: match forged_res {
            Err(e) => format!("REFUSED ({e})"),
            Ok(_) => "MINTED (BUG: forged accepted)".into(),
        },
    });

    EarnReport {
        asset: USD_CENTS.into(),
        minted_cents: mirror.live_supply(),
        events,
        receipts,
        signer: mirror.signer(),
    }
}

// ── the toolkit (operate + spend) ───────────────────────────────────────────

/// A deterministic green compute runner (the recorded sandbox stand-in): every
/// sandbox behind this seam; the demo's offline path uses this.
fn green_runner(_lang: &str, _src: &str) -> Result<RunReport, String> {
    Ok(RunReport::new(["0"], "WasmSandbox"))
}

/// The agent's toolkit: a witnessed `run_tests` (OPERATE) + a budget-gated
/// `stripe_pay` outbound payout (SPEND) + a `check_health` probe (for the
/// sub-agent cap-narrowing tooth). The payout is a deterministic recorded
/// stand-in (the live path shells the Stripe Link CLI / payout API).
fn build_toolkit() -> Toolkit {
    Toolkit::new()
        .with_run_tests("run_tests", "wat", SUITE_SRC, green_runner)
        .with_stripe_pay("stripe_pay", |amount_cents| {
            // The recorded payout: a deterministic payout id. (Live: a Stripe call.)
            Ok(format!("py_demo_{amount_cents}"))
        })
        .with_check_health("check_health", || HealthSnapshot::healthy("node up · Σδ=0"))
}

/// The recorded "Hermes/Nemotron" transcript driving the OPERATE + SPEND beats:
/// accept the job, run the customer's tests, pay two vendors, then attempt an
/// over-ceiling spend (refused in-band).
fn recorded_main_brain() -> OpenAICompatBrain<RecordedOpenAICaller> {
    let caller = RecordedOpenAICaller::new(vec![
        tool_call(
            "cell_write",
            r#"{"path":"/job","value":"customer=acme-co;suite=commit-7f3"}"#,
        ),
        tool_call("invoke", r#"{"service":"run_tests"}"#),
        tool_call(
            "stripe_pay",
            r#"{"vendor":"nvidia-nim-compute","amount_cents":1800}"#,
        ),
        tool_call(
            "stripe_pay",
            r#"{"vendor":"neon-postgres","amount_cents":1200}"#,
        ),
        tool_call(
            "stripe_pay",
            r#"{"vendor":"twilio-sms","amount_cents":2500}"#,
        ),
        finish("Tested the customer's suite (green) and paid the compute + SaaS vendors."),
    ]);
    OpenAICompatBrain::with_defaults(
        "Run the customer's test job, then pay the compute and SaaS vendors you used.",
        vec![
            "run_tests".into(),
            "stripe_pay".into(),
            "check_health".into(),
        ],
        vec!["/job".into()],
        // The recorded transport ignores the key; the live path supplies a real one.
        ProviderKey::unauthenticated(),
        caller,
    )
}

/// An OpenAI tool-call response (the exact provider wire shape).
fn tool_call(name: &str, args: &str) -> serde_json::Value {
    serde_json::json!({
        "choices": [{
            "message": {
                "role": "assistant", "content": null,
                "tool_calls": [{
                    "id": format!("call_{name}"),
                    "type": "function",
                    "function": { "name": name, "arguments": args }
                }]
            },
            "finish_reason": "tool_calls"
        }]
    })
}

fn finish(text: &str) -> serde_json::Value {
    serde_json::json!({
        "choices": [{ "message": { "role": "assistant", "content": text }, "finish_reason": "stop" }]
    })
}

// ── the whole run ───────────────────────────────────────────────────────────

/// Run the whole business **offline** with the deterministic recorded brain — the
/// default filmable path (no key, no network).
pub fn run_offline_demo(seed: [u8; 32]) -> BusinessRun {
    let mut brain = recorded_main_brain();
    run_demo(seed, &mut brain)
}

/// Run the whole business, driving the OPERATE + SPEND beats with `main_brain`
/// (the recorded brain offline; a live Nemotron/Hermes brain under `--live`). The
/// EARN, FUND, and SCALE beats are deterministic regardless of the brain.
pub fn run_demo(seed: [u8; 32], main_brain: &mut dyn AgentBrain) -> BusinessRun {
    let cloud = AgentCloud::from_seed(seed);
    let agent_id = "agent:acme-tester";

    // 1+2. EARN → FUND: the minted cents become the budget ceiling.
    let earn = earn(agent_id);
    let budget = earn.minted_cents;

    let parent_spec = AgentSpec::new(agent_id, budget)
        .with_service("run_tests")
        .with_service("stripe_pay")
        .with_service("check_health")
        .with_cell("/job");
    let handle = cloud
        .deploy(&parent_spec)
        .expect("the funded agent deploys");

    // 3+4. OPERATE + SPEND: one re-witnessable receipt chain.
    let toolkit = build_toolkit();
    let agent_run = cloud.run_with_toolkit(&handle, main_brain, &toolkit);

    // 5. SCALE: a sub-agent with an attenuated budget + a NARROWER cap bundle
    //    (drops check_health) that it provably cannot exceed.
    let child_spec = AgentSpec::new("agent:acme-tester/burst", 1000)
        .with_service("run_tests")
        .with_service("stripe_pay");
    let child = cloud
        .deploy_subagent(&handle, &child_spec)
        .expect("the sub-agent attenuates off the parent");
    let child_plan = vec![
        // admitted within the narrower budget
        AgentAction::Invoke {
            service: "run_tests".into(),
        },
        // over the child's 1000¢ ceiling → BudgetRefused (budget no-amplify)
        AgentAction::Spend {
            service: "stripe_pay".into(),
            amount_cents: 1500,
        },
        // a capability the parent held but the child does not → CapRefused
        AgentAction::Invoke {
            service: "check_health".into(),
        },
    ];
    let subagent_run = cloud.run_with_toolkit(&child, &mut PlannedBrain::new(child_plan), &toolkit);

    // The P&L (every figure recomputable from the chains).
    let vendor_spend = agent_run.spent_total();
    let consumed = agent_run.consumed;
    let pnl = Pnl {
        earned_cents: earn.minted_cents,
        vendor_spend_cents: vendor_spend,
        ops_metering_cents: consumed - vendor_spend,
        net_cents: budget - consumed,
        budget_cents: budget,
        headroom_cents: agent_run.headroom,
    };

    BusinessRun {
        business: "Acme Test-as-a-Service".into(),
        earn,
        suite_src: SUITE_SRC.into(),
        deployed_root: code_root(SUITE_SRC),
        agent_run,
        subagent_run,
        pnl,
    }
}

// ── PROVE: re-witness the whole P&L, host untrusted ─────────────────────────

/// What re-witnessing a [`BusinessRun`] confirmed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BusinessVerified {
    /// Mint receipts re-witnessed (the earn chain).
    pub mints: usize,
    /// Cents earned (= the funded budget).
    pub earned_cents: i64,
    /// Admitted actions in the main agent chain.
    pub agent_actions: usize,
    /// Witnessed QA runs re-executed and confirmed.
    pub witnessed_qa: usize,
    /// Admitted actions in the sub-agent chain.
    pub subagent_actions: usize,
    /// Cents paid to vendors (traced to spend receipts).
    pub vendor_spend_cents: i64,
    /// Net margin = budget − consumed (the could-have bound).
    pub net_cents: i64,
}

/// **Re-witness the whole business run offline, trusting no host.** Checks, in
/// order: the EARN mint chain is signed + intact and sums to the funded budget;
/// the main agent receipt chain re-witnesses (chain + budget bound); the witnessed
/// QA re-executes on the deployed code; the sub-agent chain re-witnesses; and the
/// P&L arithmetic agrees with the chains. Returns the audited figures or the first
/// failure as a human string (the `chain ✓ · budget ✓ · …` the CLI prints).
pub fn verify_business(run: &BusinessRun) -> Result<BusinessVerified, String> {
    // (1) EARN: the mint chain is signed + unbroken, and the minted total agrees.
    verify_chain(&run.earn.receipts)
        .map_err(|e| format!("earn mint chain did not verify: {e:?}"))?;
    let minted: i64 = run.earn.receipts.iter().map(|r| r.amount_cents).sum();
    if minted != run.earn.minted_cents {
        return Err(format!(
            "earn total mismatch: receipts sum {minted} != reported {}",
            run.earn.minted_cents
        ));
    }
    if run.earn.minted_cents != run.pnl.budget_cents {
        return Err(format!(
            "FUND mismatch: minted {} was not the funded budget {}",
            run.earn.minted_cents, run.pnl.budget_cents
        ));
    }

    // (2) the main agent run re-witnesses (chain + bound + consumed agreement).
    let agent = verify_agent_run(&run.agent_run).map_err(|e| format!("agent run: {e}"))?;

    // (3) the witnessed QA re-executes on the deployed code (the operate verdict
    //     was really produced by running these tests on this code).
    let suite = run.suite_src.clone();
    let qa = verify_witnessed_qa(&run.agent_run, &run.deployed_root, |w: &WitnessedRun| {
        rewitness_run_tests("wat", &suite, w, green_runner)
    })
    .map_err(|e| format!("witnessed QA: {e}"))?;

    // (4) the sub-agent run re-witnesses too.
    let sub = verify_agent_run(&run.subagent_run).map_err(|e| format!("sub-agent run: {e}"))?;

    // (5) the P&L arithmetic agrees with the chains.
    let vendor_spend = run.agent_run.spent_total();
    if vendor_spend != run.pnl.vendor_spend_cents {
        return Err(format!(
            "P&L spend mismatch: receipts {vendor_spend} != reported {}",
            run.pnl.vendor_spend_cents
        ));
    }
    if run.pnl.net_cents != run.pnl.budget_cents - run.agent_run.consumed {
        return Err(format!(
            "P&L net mismatch: net {} != budget {} − consumed {}",
            run.pnl.net_cents, run.pnl.budget_cents, run.agent_run.consumed
        ));
    }
    if run.pnl.net_cents != agent.headroom {
        return Err(format!(
            "P&L net {} != the budget-cell headroom bound {}",
            run.pnl.net_cents, agent.headroom
        ));
    }

    Ok(BusinessVerified {
        mints: run.earn.receipts.len(),
        earned_cents: run.earn.minted_cents,
        agent_actions: agent.actions,
        witnessed_qa: qa.witnessed,
        subagent_actions: sub.actions,
        vendor_spend_cents: vendor_spend,
        net_cents: run.pnl.net_cents,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent::{ActionOutcome, AgentVerifyError};
    use crate::receipt::ChainError;

    #[test]
    fn the_offline_demo_runs_all_five_beats_and_re_witnesses() {
        let run = run_offline_demo([7u8; 32]);

        // EARN: one mint (5000¢), a retry refused, a forged webhook refused.
        assert_eq!(run.earn.minted_cents, 5000);
        assert_eq!(
            run.earn.receipts.len(),
            1,
            "only the genuine payment minted"
        );
        assert!(run.earn.events.iter().any(|e| e.outcome == "MINTED"));
        assert_eq!(
            run.earn
                .events
                .iter()
                .filter(|e| e.outcome.contains("REFUSED"))
                .count(),
            2,
            "the retry and the forged webhook are both refused"
        );

        // OPERATE + SPEND: deploy cell + run_tests + 2 spends admitted; the
        // over-ceiling spend refused; vendor outflow 3000¢; net 1998¢.
        assert_eq!(run.agent_run.admitted, 4);
        assert_eq!(
            run.agent_run.budget_refused, 1,
            "the over-ceiling spend is refused"
        );
        assert_eq!(run.pnl.vendor_spend_cents, 3000);
        assert_eq!(run.pnl.net_cents, 1998);
        assert_eq!(run.pnl.net_cents, run.agent_run.headroom);

        // SCALE: the sub-agent ran one action, then was refused on BOTH axes.
        assert_eq!(run.subagent_run.admitted, 1);
        assert_eq!(
            run.subagent_run.budget_refused, 1,
            "over its attenuated budget"
        );
        assert_eq!(
            run.subagent_run.cap_refused, 1,
            "outside its narrowed bundle"
        );
        assert!(
            run.subagent_run
                .log
                .iter()
                .any(|r| matches!(r.outcome, ActionOutcome::CapRefused { .. }))
        );

        // PROVE: the whole P&L re-witnesses offline.
        let v = verify_business(&run).expect("the whole run re-witnesses");
        assert_eq!(v.mints, 1);
        assert_eq!(v.earned_cents, 5000);
        assert_eq!(v.witnessed_qa, 1, "the operate QA re-executed");
        assert_eq!(v.vendor_spend_cents, 3000);
        assert_eq!(v.net_cents, 1998);
    }

    #[test]
    fn tampering_a_spend_amount_is_caught_on_re_witness() {
        let mut run = run_offline_demo([8u8; 32]);
        verify_business(&run).expect("clean run re-witnesses");
        // Forge "I paid $1.00 not $18.00" on a spend receipt → BadSignature.
        let idx = run
            .agent_run
            .receipts
            .iter()
            .position(|r| r.action.starts_with("spend:"))
            .expect("a spend receipt exists");
        run.agent_run.receipts[idx].cost = 100;
        let err = verify_business(&run).expect_err("the tamper is caught");
        assert!(err.contains("agent run"), "{err}");
        // And the underlying error is a signature break.
        assert!(matches!(
            verify_agent_run(&run.agent_run),
            Err(AgentVerifyError::Chain(ChainError::BadSignature { .. }))
        ));
    }

    #[test]
    fn tampering_a_mint_amount_is_caught() {
        let mut run = run_offline_demo([9u8; 32]);
        run.earn.receipts[0].amount_cents = 500_000; // "the customer paid $5,000"
        let err = verify_business(&run).expect_err("the forged mint is caught");
        assert!(err.contains("earn mint chain"), "{err}");
    }
}

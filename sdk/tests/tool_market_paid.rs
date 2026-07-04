//! ORGAN 4 — THE METERED, PAID GATEWAY: pay to access another agent's tools.
//!
//! The free [`ToolGateway`] cap-gates + rate-meters a consumer's tool-calls. The
//! PAID gateway ([`ToolGateway::admit_priced`]) adds the market half: a provider
//! agent B offers a tool through the gateway with a per-call PRICE and the
//! consumer A is given a value BUDGET. Each admitted call is then
//!
//!   1. cap-checked + rate-metered (the proven [`ToolGrant`] / `delegAdmit`), AND
//!   2. CHARGED — a real conserving [`Effect::Transfer`] of `price` from A (the
//!      worker cell) to B (the provider cell), riding the SAME metered turn.
//!
//! These tests prove, on the REAL Rust executor:
//!
//! * GENUINE — a granted, within-budget call commits; the provider is credited
//!   exactly `price` (the charge is CONSERVED A → B), the meter advances, the
//!   spend debits, and the receipt records `paid`.
//! * OVER-BUDGET — a call whose price would exceed the consumer's allowance is
//!   REFUSED IN-BAND as `OverBudget` (no turn, no spend, no charge).
//! * INSOLVENT — even with budget head-room, a consumer that cannot actually pay
//!   has its metered turn REJECTED by the kernel's conservation check (the
//!   conserved backstop under the in-band budget cap).
//! * ROUTED — the data-plane (enqueue → drive → resolve) charges identically,
//!   and an over-budget routed call is refused at the on-ramp.

use std::sync::{Arc, RwLock};

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, Charge, Effect, GatewayRefusal, ToolCallError, ToolGateway,
    ToolGrant,
};
use dregg_token::Attenuation;

/// Build a runtime + a root token the grantor delegates from.
fn runtime_with_root() -> (AgentRuntime, dregg_sdk::HeldToken) {
    let mut cclerk = AgentCipherclerk::new();
    let root_token = cclerk.mint_token(&[7u8; 32], "compute");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
    (runtime, root_token)
}

/// The demo grant: tool 77, rate 3, deadline 100, method `search`.
fn demo_grant() -> ToolGrant {
    ToolGrant {
        tool_id: 77,
        rate_limit: 3,
        deadline: 100,
        tool_method: "search".to_string(),
    }
}

/// Spawn a PROVIDER cell (agent B) in the shared ledger — the cell paid for tool
/// access.
fn spawn_provider(runtime: &AgentRuntime, root: &dregg_sdk::HeldToken) -> dregg_sdk::CellId {
    runtime
        .spawn_sub_agent_scoped(&Attenuation::default(), root, &["provide"])
        .expect("spawn provider")
        .cell_id()
}

fn balance(runtime: &AgentRuntime, cell: dregg_sdk::CellId) -> i64 {
    let l = runtime.ledger().lock().unwrap();
    l.get(&cell).map(|c| c.state.balance()).unwrap_or(0)
}

#[test]
fn gateway_charge_is_a_real_payable_pay_not_a_hand_rolled_transfer() {
    // GAP 1 ✓ — the metered gateway charge is the desugar of a REAL `Payable::pay`
    // routed through the canonical `payable_descriptor` (verified DFA → Signature
    // cap-gate → conserving Transfer), the SAME path the app-framework apps pay
    // over — NOT a parallel hand-built `Effect::Transfer`.
    let (runtime, root) = runtime_with_root();
    let provider = spawn_provider(&runtime, &root);

    let price = 1_000u64;
    let mut gw = ToolGateway::admit_priced(
        &runtime,
        &root,
        demo_grant(),
        Some(Charge::new(price, provider, 10_000)),
    )
    .expect("admit paid worker");

    // The charge RESOLVES through the Payable interface — assert the method and the
    // interface id, the proof it goes through `Payable::pay`, not a raw Transfer.
    let (action, sig) = gw
        .charge_invocation()
        .expect("a paid mandate has a charge")
        .expect("the charge routes through the Payable interface");
    assert_eq!(
        action.method,
        dregg_sdk::pay_method_sig().symbol,
        "the charge goes through the Payable `pay` method"
    );
    assert!(
        dregg_sdk::payable_descriptor()
            .route_method(&action.method)
            .is_some(),
        "the charge routes through the canonical Payable interface (interface_id)"
    );
    assert_eq!(
        sig,
        dregg_sdk::pay_method_sig(),
        "the matched MethodSig is the canonical Payable `pay` sig (Signature-gated, Replayable)"
    );
    // It desugars to EXACTLY ONE conserving Transfer consumer -> provider.
    assert_eq!(action.effects.len(), 1, "pay desugars to one effect");
    match action.effects[0] {
        Effect::Transfer { from, to, amount } => {
            assert_eq!(from, gw.worker_cell(), "from = the consumer spend account");
            assert_eq!(to, provider, "to = the provider");
            assert_eq!(amount, price, "amount = the per-call price");
        }
        ref other => panic!("the charge must desugar to a Transfer, got {other:?}"),
    }

    // And a committed call moves EXACTLY `price` A -> B (conserved through the same
    // path).
    let p0 = balance(&runtime, provider);
    let r = gw.invoke(77, 50, vec![]).expect("the charged call commits");
    assert_eq!(r.paid, price);
    assert_eq!(
        balance(&runtime, provider),
        p0 + price as i64,
        "the Payable-routed charge is conserved A -> B"
    );
}

#[test]
fn consumer_funds_spend_account_then_pays_from_real_funds() {
    // GAP 3 ✓ — the charge debits a REAL funded account, not a magic birth-balance.
    // The worker (consumer spend account) is born with a fixed balance that affords
    // ONE call but not two; a second call is rejected by conservation (insolvent).
    // The consumer then FUNDS the spend account with a real conserving Transfer from
    // its own account, after which the second call commits — paid from funds the
    // consumer genuinely transferred in.
    let (runtime, root) = runtime_with_root();
    let provider = spawn_provider(&runtime, &root);

    // A consumer-owned funding account (a real cell with its own balance, same
    // asset/domain as the worker so a funding Transfer conserves).
    let funder = runtime
        .spawn_sub_agent(&Attenuation::default(), &root)
        .expect("spawn consumer funding account");

    // Price chosen so the worker's birth balance affords call 1 but NOT call 2.
    let price = 80_000u64;
    let budget = 1_000_000u64; // the in-band value budget is not the binding limit here.
    let mut gw = ToolGateway::admit_priced(
        &runtime,
        &root,
        demo_grant(),
        Some(Charge::new(price, provider, budget)),
    )
    .expect("admit paid worker");
    let worker = gw.worker_cell();

    let p0 = balance(&runtime, provider);
    let funder0 = balance(&runtime, funder.cell_id());

    // Call 1: paid from the birth balance.
    gw.invoke(77, 50, vec![]).expect("call 1 commits");
    assert_eq!(balance(&runtime, provider), p0 + price as i64);

    // Call 2 from the depleted birth balance is INSOLVENT — rejected by the
    // kernel's conservation check (not an in-band budget refusal).
    let err = gw
        .invoke(77, 50, vec![])
        .expect_err("call 2 cannot be paid from the depleted birth balance");
    assert!(
        matches!(err, ToolCallError::Sdk(_)),
        "an unfunded over-spend is a conservation rejection: {err:?}"
    );
    assert_eq!(gw.calls_made(), 1, "the insolvent call did not meter");

    // FUND the spend account for real: the consumer transfers value from its own
    // account into the worker cell (a conserving Transfer the funder authorizes).
    let fund_amount = 90_000u64;
    gw.fund(&funder, fund_amount).expect("funding commits");
    assert_eq!(
        balance(&runtime, worker) >= price as i64,
        true,
        "the spend account is now funded enough for another call"
    );
    assert!(
        balance(&runtime, funder.cell_id()) <= funder0 - fund_amount as i64,
        "the consumer's own account was debited by the funded amount"
    );

    // Call 2 now COMMITS — paid from the funds the consumer transferred in.
    gw.invoke(77, 50, vec![])
        .expect("call 2 commits after funding");
    assert_eq!(gw.calls_made(), 2, "the funded call metered");
    let pn = balance(&runtime, provider);
    assert_eq!(
        pn,
        p0 + 2 * price as i64,
        "the provider received 2x price — and 2x price exceeds the worker's birth balance, \
         so the second payment provably came from the funded Transfer"
    );
    // Load-bearing: the provider received MORE than the worker was ever born with.
    assert!(
        pn - p0 > 100_000,
        "the value paid out exceeds the birth balance, so funding was load-bearing"
    );
}

#[test]
fn agent_a_pays_agent_b_per_tool_call_conserved() {
    // GENUINE ✓ — A invokes B's tool: cap-checked + rate-metered + CHARGED. The
    // provider (B) is credited EXACTLY the price on each call (the charge is
    // conserved A → B), the meter advances, the spend debits, and the receipt
    // records the payment.
    let (runtime, root) = runtime_with_root();
    let provider = spawn_provider(&runtime, &root);

    let price = 1_000u64;
    let budget = 2_500u64; // affords two calls (2_000), refuses the third.
    let mut gw = ToolGateway::admit_priced(
        &runtime,
        &root,
        demo_grant(),
        Some(Charge::new(price, provider, budget)),
    )
    .expect("admit paid worker");
    let consumer = gw.worker_cell();

    let c0 = balance(&runtime, consumer);
    let p0 = balance(&runtime, provider);

    // Call 1: metered + charged.
    let r1 = gw
        .invoke(77, 50, vec![])
        .expect("call 1 within budget commits");
    assert_eq!(r1.calls_made, 1, "the rate meter advanced 0 -> 1");
    assert_eq!(r1.paid, price, "the receipt records the per-call charge");
    assert_eq!(gw.spent(), price, "cumulative spend tracks the charge");
    assert_eq!(gw.budget_remaining(), Some(budget - price));

    // The charge LANDED, conserved A -> B: provider credited exactly `price`.
    let p1 = balance(&runtime, provider);
    assert_eq!(
        p1,
        p0 + price as i64,
        "provider B credited exactly the price"
    );
    // The consumer paid the price (plus the turn's computron fee, a separate
    // pre-existing system debit).
    let c1 = balance(&runtime, consumer);
    assert!(
        c1 <= c0 - price as i64,
        "consumer A debited at least the price"
    );

    // Call 2: charged again, spend accumulates.
    let r2 = gw
        .invoke(77, 50, vec![])
        .expect("call 2 within budget commits");
    assert_eq!(r2.calls_made, 2);
    assert_eq!(gw.spent(), 2 * price);
    let p2 = balance(&runtime, provider);
    assert_eq!(
        p2,
        p0 + 2 * price as i64,
        "two calls credited the provider 2x price — the charge is conserved A -> B"
    );

    // Call 3: OVER-BUDGET (spent 2_000 + price 1_000 > budget 2_500) — refused
    // IN-BAND. No turn, no spend, no charge.
    let err = gw
        .invoke(77, 50, vec![])
        .expect_err("the 3rd call exceeds the value budget and MUST be refused in-band");
    match err {
        ToolCallError::Refused(GatewayRefusal::OverBudget {
            spent,
            price: p,
            budget: b,
        }) => {
            assert_eq!(spent, 2 * price);
            assert_eq!(p, price);
            assert_eq!(b, budget);
        }
        other => panic!("expected an in-band OverBudget refusal, got {other:?}"),
    }
    // The refusal moved nothing: spend, meter, and the provider balance unchanged.
    assert_eq!(
        gw.spent(),
        2 * price,
        "an over-budget refusal does not spend"
    );
    assert_eq!(gw.calls_made(), 2, "an over-budget refusal does not meter");
    assert_eq!(
        balance(&runtime, provider),
        p2,
        "an over-budget refusal pays the provider nothing"
    );
}

#[test]
fn insolvent_consumer_charge_rejected_by_conservation_backstop() {
    // INSOLVENT ✗ — the value budget admits the call in-band, but the consumer
    // cannot actually pay (price exceeds its balance). The kernel's per-asset
    // conservation check REJECTS the metered turn: no commit, no meter advance,
    // no spend. The conserved backstop under the in-band budget cap.
    let (runtime, root) = runtime_with_root();
    let provider = spawn_provider(&runtime, &root);

    let consumer_balance = balance(
        &runtime,
        ToolGateway::admit(&runtime, &root, demo_grant())
            .expect("probe")
            .worker_cell(),
    );
    // Price far beyond any worker balance, budget generous enough to pass in-band.
    let price = (consumer_balance as u64) + 1_000_000;
    let mut gw = ToolGateway::admit_priced(
        &runtime,
        &root,
        demo_grant(),
        Some(Charge::new(price, provider, u64::MAX)),
    )
    .expect("admit paid worker");

    let p0 = balance(&runtime, provider);
    let err = gw
        .invoke(77, 50, vec![])
        .expect_err("an insolvent consumer's charged turn MUST be rejected");
    assert!(
        matches!(err, ToolCallError::Sdk(_)),
        "insolvency is a conservation rejection (Sdk error), not an in-band refusal: {err:?}"
    );
    // Nothing moved: no meter, no spend, no payment.
    assert_eq!(gw.calls_made(), 0, "a rejected charge does not meter");
    assert_eq!(gw.spent(), 0, "a rejected charge does not spend");
    assert_eq!(
        balance(&runtime, provider),
        p0,
        "a rejected charge pays the provider nothing"
    );
}

#[test]
fn free_mandate_charges_nothing() {
    // A free (unpriced) mandate behaves exactly as before: paid == 0, the
    // provider concept is absent, and nothing but the counter moves.
    let (runtime, root) = runtime_with_root();
    let mut gw = ToolGateway::admit(&runtime, &root, demo_grant()).expect("admit free worker");
    assert!(gw.charge().is_none(), "a free mandate has no charge");
    assert_eq!(gw.budget_remaining(), None);

    let out = gw.invoke(77, 50, vec![]).expect("free call commits");
    assert_eq!(out.paid, 0, "a free call charges nothing");
    assert_eq!(gw.spent(), 0);
}

#[test]
fn routed_paid_call_charges_and_over_budget_refused_at_on_ramp() {
    // ROUTED ✓/✗ — the data plane charges identically: enqueue (reserves the
    // spend) → drive (settles the charge) → resolve (the paid receipt). An
    // over-budget routed call is refused at the on-ramp (nothing enqueued).
    let (runtime, root) = runtime_with_root();
    let provider = spawn_provider(&runtime, &root);

    let price = 1_000u64;
    let budget = 1_500u64; // affords exactly one routed call.
    let mut gw = ToolGateway::admit_priced(
        &runtime,
        &root,
        demo_grant(),
        Some(Charge::new(price, provider, budget)),
    )
    .expect("admit paid worker");

    let p0 = balance(&runtime, provider);

    // Enqueue reserves the spend immediately (so a second enqueue gates on it).
    let h1 = gw
        .enqueue(77, 50, vec![])
        .expect("first routed call enqueues");
    assert_eq!(gw.spent(), price, "enqueue reserves the value budget");
    // Provider not yet paid — the work has not drained.
    assert_eq!(
        balance(&runtime, provider),
        p0,
        "enqueue does not settle the charge"
    );

    // A second enqueue would push reserved spend (1_000 + 1_000) past 1_500 —
    // refused at the on-ramp, nothing enqueued, no further reservation.
    let err = gw
        .enqueue(77, 50, vec![])
        .expect_err("the second routed call exceeds the budget at the on-ramp");
    assert!(matches!(
        err,
        ToolCallError::Refused(GatewayRefusal::OverBudget { .. })
    ));
    assert_eq!(gw.inbox_depth(), 1, "the over-budget enqueue added nothing");
    assert_eq!(
        gw.spent(),
        price,
        "the over-budget enqueue reserved nothing"
    );

    // Drive the executor: the routed charge settles (provider credited price).
    let drained = gw.drive_executor(60);
    assert_eq!(drained, vec![h1.routed_hash()]);
    let result = gw.resolve(&h1).expect("the routed call delivers");
    assert_eq!(
        result.tool_receipt.paid, price,
        "the routed receipt records the charge"
    );
    assert_eq!(
        balance(&runtime, provider),
        p0 + price as i64,
        "the routed charge is conserved A -> B on drain"
    );
}

#[test]
fn broken_routed_charge_releases_the_reserved_spend() {
    // A routed call that breaks on drain (the executor rejects it — here because
    // the consumer cannot pay) RELEASES its reserved spend, so the value budget
    // is not leaked by a failed route.
    let (runtime, root) = runtime_with_root();
    let provider = spawn_provider(&runtime, &root);

    let consumer_balance = balance(
        &runtime,
        ToolGateway::admit(&runtime, &root, demo_grant())
            .expect("probe")
            .worker_cell(),
    );
    let price = (consumer_balance as u64) + 1_000_000; // unpayable
    let mut gw = ToolGateway::admit_priced(
        &runtime,
        &root,
        demo_grant(),
        Some(Charge::new(price, provider, u64::MAX)),
    )
    .expect("admit paid worker");

    let h = gw
        .enqueue(77, 50, vec![])
        .expect("enqueues (in-band budget passes)");
    assert_eq!(gw.spent(), price, "reserved at enqueue");
    let _ = gw.drive_executor(60);
    // The drain failed (insolvent): the reservation is released.
    assert_eq!(gw.spent(), 0, "a broken route releases the reserved spend");
    assert!(
        gw.resolve(&h).is_err(),
        "a broken route resolves to an error"
    );
}

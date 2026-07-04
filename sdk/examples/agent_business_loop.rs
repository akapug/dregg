//! The agent business loop — earn, fund, run, pay-per-use, read your receipts.
//!
//! This is the runnable companion to `docs/guide/AGENT-QUICKSTART.md`. It walks
//! an autonomous agent through the whole service-economy loop, using ONLY the
//! real `dregg-sdk` service-economy facade — every call here desugars to a
//! primitive the kernel already verifies (one conserving `Effect::Transfer`, a
//! `FieldLte ∧ Monotonic`-metered checkpoint, a cap-gated worker), and every step
//! returns a `TurnReceipt` you can pin, chain, and verify.
//!
//!   1. spin up an agent identity + a root capability token,
//!   2. FUND a spend account (here, an in-domain Transfer — in production this is
//!      where bridged $DREGG / Stripe USD-credit lands; see the quickstart),
//!   3. PAY another agent (the canonical `Payable` pay → one conserving Transfer),
//!   4. open + fund + RUN a durable, metered EXECUTION LEASE (the checkpoint
//!      advances under an executor-enforced ceiling),
//!   5. PAY-PER-USE through a metered, capability-gated `ToolGateway` (each call
//!      is rate-metered AND charged, conserved consumer → provider),
//!   6. READ the receipts — every committed turn left verifiable proof.
//!
//! Run:
//!   cargo run -p dregg-sdk --example agent_business_loop

use std::sync::{Arc, RwLock};

use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, Attenuation, CellId, Charge, Effect, ExecutionLease, HeldToken,
    LeaseTerms, ToolGateway, ToolGrant,
};
use dregg_turn::TurnReceipt;

/// Read a cell's balance out of the runtime's shared ledger (for narration).
fn balance(runtime: &AgentRuntime, cell: CellId) -> i64 {
    let l = runtime.ledger().lock().unwrap();
    l.get(&cell).map(|c| c.state.balance()).unwrap_or(0)
}

/// First 8 bytes of a 32-byte hash as hex (compact display).
fn short(bytes: &[u8; 32]) -> String {
    bytes[..8].iter().map(|b| format!("{b:02x}")).collect()
}

/// Print the headline fields of a committed turn's receipt.
fn show_receipt(label: &str, r: &TurnReceipt) {
    println!(
        "    [{label}] turn={} pre={} post={} computrons={} actions={}",
        short(&r.turn_hash),
        short(&r.pre_state_hash),
        short(&r.post_state_hash),
        r.computrons_used,
        r.action_count,
    );
}

fn main() {
    println!("=== dregg agent business loop ===\n");

    // -------------------------------------------------------------------------
    // 1. Identity + a root capability token. The cipherclerk holds the agent's
    //    Ed25519 key; the root token is the unattenuated capability we delegate
    //    workers from. "compute" is the service domain.
    // -------------------------------------------------------------------------
    let mut cclerk = AgentCipherclerk::new();
    let root: HeldToken = cclerk.mint_token(&[7u8; 32], "compute");
    let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
    let asset = runtime.native_asset(); // this cell's token_id — the asset it spends in
    println!("[1] agent cell: {}", runtime.cell_id());
    println!("    native asset (token_id): {}\n", short(&asset));

    // -------------------------------------------------------------------------
    // 2. Get credit. In production this is where value enters the agent's
    //    economy from the outside world: a Stripe payment mirror-minted to
    //    USD-credit, or bridged $DREGG from Solana — each an ordinary in-dregg
    //    `AssetId` (see `bridge/src/{stripe_mirror,solana_mirror}.rs`). Here we
    //    model the funded source as a sibling worker in the same asset/domain so
    //    a funding Transfer conserves.
    // -------------------------------------------------------------------------
    let funder = runtime
        .spawn_sub_agent(&Attenuation::default(), &root)
        .expect("spawn a funded spend account");
    println!("[2] funded spend account: {}", funder.cell_id());
    println!("    balance: {}\n", balance(&runtime, funder.cell_id()));

    // -------------------------------------------------------------------------
    // 3. Pay another agent. `pay` routes through the canonical `Payable` `pay`
    //    method (verified DFA router → Signature cap-gate) and desugars to
    //    EXACTLY ONE conserving `Effect::Transfer` (per-asset Σδ=0). It is the
    //    same value rail the whole economy transacts over.
    // -------------------------------------------------------------------------
    let provider = runtime
        .spawn_sub_agent(&Attenuation::default(), &root)
        .expect("spawn a counterparty/provider cell")
        .cell_id();
    let pre = balance(&runtime, provider);
    let pay_receipt = runtime
        .pay_native(provider, 1_000)
        .expect("pay commits through the Payable rail");
    println!("[3] paid 1000 to {} (one conserving Transfer)", provider);
    println!(
        "    provider credited: {}",
        balance(&runtime, provider) - pre
    );
    show_receipt("pay", &pay_receipt);
    println!();

    // -------------------------------------------------------------------------
    // 4. A durable, metered EXECUTION LEASE. `open` spawns a cap-gated worker
    //    scoped to the run verb and installs the meter program
    //    `FieldLte { step ≤ max_steps } ∧ Monotonic { step }` on the lease cell.
    //    `fund` moves value in (conserving Transfer). `run` advances the durable
    //    checkpoint and meters the workload on ONE turn — a run past the ceiling
    //    is rejected by the EXECUTOR, not merely an in-memory check.
    // -------------------------------------------------------------------------
    let mut lease = ExecutionLease::open(&runtime, &root, LeaseTerms::new(3)).expect("open lease");
    let _funding = lease.fund(&funder, 5_000).expect("fund the lease");
    println!(
        "[4] opened lease cell {} (max_steps=3), funded 5000",
        lease.lease_cell()
    );
    for i in 1..=2 {
        // The workload's own effects ride the metered turn; here a state write
        // standing in for the unit of work this checkpoint did.
        let work = vec![Effect::SetField {
            cell: lease.lease_cell(),
            index: 5,
            value: [i as u8; 32],
        }];
        let step = lease.run(work).expect("metered run commits");
        println!(
            "    run {} -> checkpoint step={} remaining={}",
            i, step.step, step.remaining
        );
        show_receipt(&format!("lease.run {i}"), &step.receipt);
    }
    println!();

    // -------------------------------------------------------------------------
    // 5. PAY-PER-USE through a metered, capability-gated ToolGateway. The
    //    grantor pins a mandate (scope `tool_id` + `deadline` + `rate_limit`) and
    //    a per-call `Charge` (price → provider, capped at a budget). Each
    //    admitted `invoke` is rate-metered AND charged: a real conserving
    //    Transfer consumer → provider rides the same metered turn. An
    //    out-of-mandate call is an in-band refusal (no turn, no spend).
    // -------------------------------------------------------------------------
    let tool_provider = runtime
        .spawn_sub_agent_scoped(&Attenuation::default(), &root, &["provide"])
        .expect("spawn the tool provider")
        .cell_id();
    let grant = ToolGrant {
        tool_id: 77,
        rate_limit: 3,
        deadline: 100,
        tool_method: "search".to_string(),
    };
    let price = 500u64;
    let mut gateway = ToolGateway::admit_priced(
        &runtime,
        &root,
        grant,
        Some(Charge::new(price, tool_provider, 10_000)),
    )
    .expect("admit a paid, rate-metered tool worker");
    println!("[5] admitted paid tool gateway (tool 77, rate 3, price {price}/call)");
    let provider_pre = balance(&runtime, tool_provider);
    // `tool` = the presented tool id, `now` = the presentation height/clock,
    // `work` = the tool's actual effects (empty here = a pure metered call).
    for _ in 0..2 {
        let receipt = gateway
            .invoke(77, 50, vec![])
            .expect("a granted, within-budget call commits");
        println!(
            "    invoke -> paid={} calls_made={} remaining={}",
            receipt.paid, receipt.calls_made, receipt.remaining
        );
        show_receipt("tool.invoke", &receipt.receipt);
    }
    println!(
        "    provider earned: {} (conserved consumer -> provider)",
        balance(&runtime, tool_provider) - provider_pre
    );
    // An out-of-scope call is refused IN-BAND — no turn, no spend.
    match gateway.invoke(99, 50, vec![]) {
        Ok(_) => unreachable!("an out-of-scope tool id must be refused"),
        Err(e) => println!("    out-of-scope call refused in-band: {e}"),
    }
    println!();

    // -------------------------------------------------------------------------
    // 6. Read the receipts. Every committed turn the AGENT itself authored chains
    //    into its receipt chain (each entry's `receipt_hash` is the next turn's
    //    `previous_receipt_hash`). Worker turns (lease/gateway) chain on their own
    //    worker cells; the receipts above are their proofs.
    // -------------------------------------------------------------------------
    let cclerk = runtime.cipherclerk().read().unwrap();
    let chain = cclerk.receipt_chain();
    println!("[6] agent receipt chain (len {}):", chain.len());
    for (i, r) in chain.iter().enumerate() {
        println!(
            "    [{i}] turn={} receipt={} prev={}",
            short(&r.turn_hash),
            short(&r.receipt_hash()),
            match r.previous_receipt_hash {
                Some(h) => short(&h),
                None => "(genesis)".to_string(),
            },
        );
    }

    println!("\n=== loop complete — earned, funded, ran, paid-per-use, all receipted ===");
}

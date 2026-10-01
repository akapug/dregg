//! settle_append_refusal_e2e.rs — a REFUSED durable receipt append, on every
//! MCP handler family.
//!
//! The settle (`mcp::settle_mcp_turn`) owns the receipt append: it appends a
//! committed turn's receipt and only then commits the ledger restore point. On
//! a refused append it rolls the ledger back and returns
//! `SettleError::AppendRefused`, which each handler renders as an `isError`
//! result with `activity_status: "not_applied"`.
//!
//! Before that, the settle committed the ledger first and each handler then
//! called `append_receipt(..).expect(..)` under the node write lock: a refused
//! append panicked with the ledger change already kept and no receipt behind it.
//!
//! Each test injects a failing `set_receipt_persist` sink, drives a real tool
//! through `dispatch_tool`, and checks (1) the refusal shape, (2) that the whole
//! ledger root, the cell count, the solo height and nullifier log, and the
//! receipt chain are unchanged, and (3) that the SAME request on the SAME node
//! commits once the sink is restored — which also shows the write lock was not
//! poisoned — and that this commit moves the ledger root (so the unchanged root
//! in (2) is a rollback, not a request that would never have mutated anything).

#![cfg(test)]

use serde_json::{Value, json};

use super::dispatch::dispatch_tool;
use super::hex_encode;
use crate::state::NodeState;

const INJECTED: &str = "injected: durable receipt store refused the append";

async fn funded_node() -> (NodeState, dregg_cell::CellId, tempfile::TempDir) {
    let _ = rustls::crypto::ring::default_provider().install_default();
    let tmp = tempfile::tempdir().expect("tempdir");
    let mut seed = [0u8; 32];
    seed[0] = 0xB8;
    let state = NodeState::with_cclerk(tmp.path(), vec![], seed).expect("NodeState::with_cclerk");
    let agent = {
        let mut s = state.write().await;
        s.unlocked = true;
        let pk = s.cclerk.public_key().0;
        let cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], 1_000_000);
        let agent = cell.id();
        assert_eq!(agent, dregg_cell::CellId::derive_raw(&pk, &[0u8; 32]));
        s.ledger.insert_cell(cell).expect("insert MCP agent cell");
        agent
    };
    (state, agent, tmp)
}

async fn insert_cell(state: &NodeState, owner: [u8; 32]) -> dregg_cell::CellId {
    let mut s = state.write().await;
    let cell = dregg_cell::Cell::new(owner, [0u8; 32]);
    let id = cell.id();
    s.ledger.insert_cell(cell).expect("insert cell");
    id
}

/// Everything a settle could have moved.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Snapshot {
    ledger_root: [u8; 32],
    cell_count: usize,
    has_restore_point: bool,
    solo: Option<(u64, usize)>,
    receipt_chain_len: usize,
    agent_head: Option<[u8; 32]>,
}

async fn snapshot(state: &NodeState, agent: &dregg_cell::CellId) -> Snapshot {
    let mut s = state.write().await;
    Snapshot {
        ledger_root: s.ledger.root(),
        cell_count: s.ledger.iter().count(),
        has_restore_point: s.ledger.has_restore_point(),
        solo: s
            .solo_consensus
            .as_ref()
            .map(|solo| (solo.height, solo.nullifier_log.len())),
        receipt_chain_len: s.cclerk.receipt_chain_length(),
        agent_head: s.cclerk.agent_receipt_head_hash(agent),
    }
}

/// Inject a refusing sink, call `tool` with `params`, check the refusal and the
/// unchanged snapshot; restore the sink, call again with the same params, and
/// check `committed` on the response plus a moved ledger and a +1 chain.
async fn refused_then_retried(
    state: &NodeState,
    agent: &dregg_cell::CellId,
    tool: &str,
    params: Value,
    committed: impl Fn(&Value) -> bool,
) {
    let before = {
        state
            .write()
            .await
            .cclerk
            .set_receipt_persist(std::sync::Arc::new(|_, _| Err(INJECTED.to_string())));
        snapshot(state, agent).await
    };
    assert!(
        !before.has_restore_point,
        "precondition: no armed restore point"
    );

    let refused = dispatch_tool(tool, params.clone(), state).await;
    assert_eq!(
        refused.is_error,
        Some(true),
        "{tool}: a refused append must render as an isError result: {:?}",
        refused.structured_content
    );
    let j = refused
        .structured_content
        .clone()
        .expect("the refusal carries structuredContent");
    assert_eq!(j["activity_status"], "not_applied", "{tool}: {j}");
    assert_eq!(j["refusal"], "receipt_append_refused", "{tool}: {j}");
    let error = j["error"].as_str().expect("error string");
    assert!(
        error.starts_with("receipt append refused: ") && error.contains(INJECTED),
        "{tool}: {j}"
    );
    assert_eq!(
        snapshot(state, agent).await,
        before,
        "{tool}: a refused append must leave the ledger, the solo height and nullifier \
         log, and the receipt chain exactly as they were, with no restore point armed"
    );

    state
        .write()
        .await
        .cclerk
        .set_receipt_persist(std::sync::Arc::new(|_, _| Ok(())));
    let retried = dispatch_tool(tool, params, state).await;
    let j = retried
        .structured_content
        .clone()
        .unwrap_or_else(|| json!({ "text": retried.content.first().map(|c| c.text.clone()) }));
    assert!(
        retried.is_error != Some(true) && committed(&j),
        "{tool}: the same request must commit once the sink accepts: {j}"
    );
    let after = snapshot(state, agent).await;
    assert_eq!(
        after.receipt_chain_len,
        before.receipt_chain_len + 1,
        "{tool}"
    );
    assert_ne!(after.agent_head, before.agent_head, "{tool}");
    assert_ne!(
        after.ledger_root, before.ledger_root,
        "{tool}: the committed retry must move the ledger — otherwise the unchanged \
         root after the refusal proves nothing"
    );
    assert!(
        !after.has_restore_point,
        "{tool}: the commit resolved the restore point"
    );
}

/// act family — `tool_submit_turn`, the `mcp_execute_via_producer` site.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn mcp_submit_turn_append_refusal_rolls_back_and_releases_the_lock() {
    let (state, agent, _tmp) = funded_node().await;
    let params = json!({
        "target_cell": hex_encode(&agent.0),
        "method": "append_refusal_probe",
        "fee": 500_000,
    });
    refused_then_retried(&state, &agent, "dregg_submit_turn", params, |j| {
        j["accepted"] == true
    })
    .await;
}

/// delegate family — `tool_grant_capability`.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn mcp_grant_capability_append_refusal_rolls_back_and_releases_the_lock() {
    let (state, agent, _tmp) = funded_node().await;
    let recipient = insert_cell(&state, [0x77; 32]).await;
    let params = json!({
        "to_agent": hex_encode(&recipient.0),
        "target_cell": hex_encode(&agent.0),
        "permissions": "signature",
    });
    refused_then_retried(&state, &agent, "dregg_grant_capability", params, |j| {
        j["activity_status"] == "committed" && j["granted"] == true
    })
    .await;
}

/// apps family — `run_starbridge_action` via `dregg_register_name`, the site that
/// opens its window early (`mcp_begin_turn`) and writes stub cells before
/// executing: those stubs must roll back with the rest.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn mcp_register_name_append_refusal_rolls_back_and_releases_the_lock() {
    let (state, agent, _tmp) = funded_node().await;
    let params = json!({ "name": "b8c.dregg", "expiry_height": 100_000u64 });
    refused_then_retried(&state, &agent, "dregg_register_name", params, |j| {
        j["committed"] == true
    })
    .await;
}

/// The non-`Turn` settle, `mcp_apply_to_ledger` — `tool_fulfill_intent`'s path,
/// driven directly (no fixture reaches a committed fulfillment through
/// `dispatch_tool`). The closure stands in for the verified settle edge: it
/// writes the ledger and returns the receipt to append.
///
/// ⚠ The privacy family (`tool_private_transfer`) has no test here because it
/// cannot commit at all: its turn carries `fee: 0` (refused `computron budget
/// exceeded: limit=0`), and with a fee its `NoteCreate.value_commitment` — a
/// BLAKE3 digest labelled "Pedersen" — is refused as "not a valid Ristretto
/// point". Its site goes through the same `mcp_execute` settle as the rest.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn mcp_apply_to_ledger_append_refusal_rolls_back_and_releases_the_lock() {
    use super::{McpApplyError, SettleError, mcp_apply_to_ledger};

    let (state, agent, _tmp) = funded_node().await;
    let written = dregg_cell::Cell::new([0x79; 32], [0u8; 32]);
    let written_id = written.id();
    let receipt = dregg_turn::TurnReceipt {
        agent,
        previous_receipt_hash: None,
        ..Default::default()
    };
    let apply = |s: &mut crate::state::NodeStateInner| {
        let (cell, receipt) = (written.clone(), receipt.clone());
        mcp_apply_to_ledger(s, move |ledger| {
            ledger.insert_cell(cell).expect("insert");
            Ok::<_, std::convert::Infallible>(receipt)
        })
    };

    state
        .write()
        .await
        .cclerk
        .set_receipt_persist(std::sync::Arc::new(|_, _| Err(INJECTED.to_string())));
    let before = snapshot(&state, &agent).await;
    let refused = apply(&mut *state.write().await);
    match refused {
        Err(McpApplyError::Settle(SettleError::AppendRefused(reason))) => {
            assert!(reason.contains(INJECTED), "{reason}")
        }
        other => panic!("expected an append refusal, got {other:?}"),
    }
    assert_eq!(snapshot(&state, &agent).await, before);
    assert!(
        state.read().await.ledger.get(&written_id).is_none(),
        "the flow's ledger write must be rolled back"
    );

    state
        .write()
        .await
        .cclerk
        .set_receipt_persist(std::sync::Arc::new(|_, _| Ok(())));
    apply(&mut *state.write().await).expect("the same apply commits once the sink accepts");
    let after = snapshot(&state, &agent).await;
    assert_eq!(after.receipt_chain_len, before.receipt_chain_len + 1);
    assert_ne!(after.ledger_root, before.ledger_root);
    assert!(!after.has_restore_point);
    assert!(state.read().await.ledger.get(&written_id).is_some());
}

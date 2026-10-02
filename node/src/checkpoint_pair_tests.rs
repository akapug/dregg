use super::*;

// No other test mutates this exact key. Hold this lock across each real
// producer callback and restore the previous value BEFORE releasing it.
static ARCHIVAL_CHECKPOINT_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
const ARCHIVAL_CHECKPOINT_ENV: &str = "DREGG_ARCHIVAL_BLOCKLACE_CHECKPOINTS";

struct RestoreArchivalCheckpointEnv(Option<std::ffi::OsString>);

impl RestoreArchivalCheckpointEnv {
    fn set(archival: bool) -> Self {
        let previous = std::env::var_os(ARCHIVAL_CHECKPOINT_ENV);
        // SAFETY: the test-local environment mutation is serialized by
        // ARCHIVAL_CHECKPOINT_ENV_LOCK, held through this guard's Drop.
        unsafe {
            if archival {
                std::env::set_var(ARCHIVAL_CHECKPOINT_ENV, "1");
            } else {
                std::env::remove_var(ARCHIVAL_CHECKPOINT_ENV);
            }
        }
        Self(previous)
    }
}

impl Drop for RestoreArchivalCheckpointEnv {
    fn drop(&mut self) {
        // SAFETY: the same test-local lock remains held until after Drop.
        unsafe {
            if let Some(previous) = self.0.take() {
                std::env::set_var(ARCHIVAL_CHECKPOINT_ENV, previous);
            } else {
                std::env::remove_var(ARCHIVAL_CHECKPOINT_ENV);
            }
        }
    }
}

#[tokio::test]
async fn live_finality_producer_mints_exact_height_proof_and_repeated_callback_returns() {
    let _env_lock = ARCHIVAL_CHECKPOINT_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let _env_restore = RestoreArchivalCheckpointEnv::set(false);
    let dir = tempfile::tempdir().unwrap();
    let state = NodeState::new(dir.path(), Vec::new()).unwrap();
    let self_key = { state.read().await.cclerk.public_key().0 };
    let mut handle = super::tests::test_handle_with_committee(self_key, vec![self_key]).await;
    handle.checkpoint_interval = 1;
    {
        let s = state.read().await;
        assert_eq!(s.store.commit_cursor().unwrap(), 0);
        s.store
            .commit_finalized_turn(0, &empty_checkpoint_test_commit(&s.ledger))
            .unwrap();
    }
    handle
        .cursor
        .write()
        .await
        .mark_executed(BlockId([0x53; 32]));
    maybe_produce_checkpoint(&state, &handle).await;
    let s = state.read().await;
    assert!(existing_checkpoint_is_authorized(&s.store, 1).unwrap());
    assert_eq!(latest_blocklace_checkpoint_height(&s.store), 1);
    let original = load_blocklace_checkpoint(&s.store, 1).unwrap();
    drop(s);
    maybe_produce_checkpoint(&state, &handle).await;
    let s = state.read().await;
    assert_eq!(
        load_blocklace_checkpoint(&s.store, 1).unwrap().blocklace,
        original.blocklace
    );
    assert_eq!(
        load_blocklace_checkpoint(&s.store, 1).unwrap().ledger,
        original.ledger
    );
}

async fn produce_six_live_checkpoints(archival: bool, switch_at_six: bool) {
    let dir = tempfile::tempdir().unwrap();
    let state = NodeState::new(dir.path(), Vec::new()).unwrap();
    let self_key = { state.read().await.cclerk.public_key().0 };
    let mut handle = super::tests::test_handle_with_committee(self_key, vec![self_key]).await;
    handle.checkpoint_interval = 1;
    let mut predecessor = None;
    for height in 1u8..=6 {
        if height == 6 && switch_at_six {
            let s = state.read().await;
            assert_eq!(s.store.commit_cursor().unwrap(), 5);
            assert!(load_blocklace_checkpoint(&s.store, 1).is_some());
            let proofs = checkpoint_proofs().lock().unwrap();
            assert!(
                !proofs
                    .get(&(s.store.checkpoint_store_id(), 1))
                    .unwrap()
                    .archival
            );
            drop(proofs);
            drop(s);
            // SAFETY: the caller holds ARCHIVAL_CHECKPOINT_ENV_LOCK throughout
            // the producer callbacks and restores its original value on Drop.
            unsafe { std::env::set_var(ARCHIVAL_CHECKPOINT_ENV, "1") };
            maybe_produce_checkpoint(&state, &handle).await;
            let s = state.read().await;
            assert_eq!(s.store.commit_cursor().unwrap(), 5);
            assert!(load_blocklace_checkpoint(&s.store, 1).is_some());
            let proofs = checkpoint_proofs().lock().unwrap();
            assert!(
                proofs
                    .get(&(s.store.checkpoint_store_id(), 1))
                    .unwrap()
                    .archival,
                "repeated H5 callback must promote existing H1 before early return"
            );
            drop(proofs);
            drop(s);
        }
        // The callback sees six real, causally linked signed DAG blocks and
        // six durable finalized-root fixture records, never hand-inserted
        // provenance. Turn execution itself is outside this producer control.
        let block = Block::new(
            &handle.signing_key,
            u64::from(height - 1),
            Payload::Turn(vec![height]),
            predecessor.into_iter().collect(),
        );
        let id = block.id();
        handle.lace.write().await.receive_block(block).unwrap();
        predecessor = Some(id);
        {
            let s = state.read().await;
            let mut record = empty_checkpoint_test_commit(&s.ledger);
            record.ordinal = u64::from(height - 1);
            record.height = u64::from(height);
            record.block_id = id.0;
            record.block_executed_up_to = u64::from(height);
            record.turn_hash = [height; 32];
            record.receipt_hash = [height.wrapping_add(10); 32];
            s.store
                .commit_finalized_turn(record.ordinal, &record)
                .unwrap();
        }
        handle.cursor.write().await.mark_executed(id);
        maybe_produce_checkpoint(&state, &handle).await;
        let s = state.read().await;
        assert_eq!(
            latest_blocklace_checkpoint_height(&s.store),
            u64::from(height)
        );
        assert!(load_blocklace_checkpoint(&s.store, u64::from(height)).is_some());
    }
    let s = state.read().await;
    assert_eq!(s.store.commit_cursor().unwrap(), 6);
    let proofs = checkpoint_proofs().lock().unwrap();
    let for_store = proofs
        .keys()
        .filter(|(id, _)| *id == s.store.checkpoint_store_id())
        .count();
    drop(proofs);
    if archival || switch_at_six {
        for height in 1..=6 {
            assert!(
                s.store
                    .published_blocklace_checkpoint_pair(height)
                    .unwrap()
                    .is_some(),
                "archival policy keeps every derived pair's exact bytes"
            );
            assert!(
                load_blocklace_checkpoint(&s.store, height).is_some(),
                "every archival height remains explicitly servable in this process"
            );
        }
        assert!(
            load_blocklace_checkpoint(&s.store, 1).is_some(),
            "archival H1 remains explicitly servable after six real producer callbacks"
        );
        assert!(existing_checkpoint_is_authorized(&s.store, 1).unwrap());
        assert_eq!(for_store, 6);
    } else {
        assert!(
            s.store
                .published_blocklace_checkpoint_pair(1)
                .unwrap()
                .is_none()
        );
        assert!(
            load_blocklace_checkpoint(&s.store, 1).is_none(),
            "default pair H1 is evicted and never explicitly served"
        );
        assert!(!existing_checkpoint_is_authorized(&s.store, 1).unwrap());
        assert_eq!(for_store, MAX_RETAINED_CHECKPOINTS);
    }
    if switch_at_six {
        let target = s.store.checkpoint_store_id();
        let real = checkpoint_proofs().lock().unwrap();
        assert_eq!(for_store, 6);
        assert!(
            real.get(&(target, 1)).unwrap().archival,
            "sixth producer must promote EVERY existing verified receipt"
        );
        // Internal cap-pressure fixture, NOT 257 producer runs or trusted
        // authority. Clone genuine target receipts into an isolated map so
        // parallel tests cannot observe placeholder store IDs. Drive the SAME
        // eviction function used by producer mint and early-return policy.
        let mut cap_fixture: std::collections::BTreeMap<_, _> = real
            .iter()
            .filter(|((id, _), _)| *id == target)
            .map(|(key, proof)| (*key, *proof))
            .collect();
        let example = *cap_fixture.get(&(target, 1)).unwrap();
        drop(real);
        const OTHER_STORE: u64 = u64::MAX - 300;
        for offset in 0..257 {
            cap_fixture.insert(
                (OTHER_STORE + offset, 1),
                LiveCheckpointProof {
                    archival: false,
                    ..example
                },
            );
        }
        assert!(
            cap_fixture.values().filter(|p| !p.archival).count() > 256,
            "fixture MUST exceed the actual global cap, not pass vacuously"
        );
        apply_checkpoint_proof_policy(&mut cap_fixture, u64::MAX, MAX_RETAINED_CHECKPOINTS);
        assert!(
            cap_fixture.contains_key(&(target, 1)),
            "other default-incarnation cap must retain archival H1"
        );
        assert_eq!(cap_fixture.values().filter(|p| !p.archival).count(), 256);
        assert!(
            !cap_fixture.contains_key(&(OTHER_STORE, 1)),
            "the cap actually evicted the oldest default fixture entry"
        );
        assert!(
            load_blocklace_checkpoint(&s.store, 1).is_some(),
            "real H1 remains explicitly servable after the cap-pressure witness"
        );
        drop(s);
        let unproved = dregg_persist::PersistentStore::open_in_memory().unwrap();
        let empty = dregg_cell::Ledger::new();
        unproved
            .commit_finalized_turn(0, &empty_checkpoint_test_commit(&empty))
            .unwrap();
        let wire = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&empty));
        let dag = compress_checkpoint_data(b"generic unproved pair".to_vec());
        unproved
            .publish_blocklace_checkpoint_pair(1, &dag, &wire, usize::MAX)
            .unwrap();
        assert!(
            existing_checkpoint_is_authorized(&unproved, 1).is_err(),
            "an archival policy cannot mint authority for generic publication"
        );
        assert!(load_blocklace_checkpoint(&unproved, 1).is_none());
        // SAFETY: this test still holds ARCHIVAL_CHECKPOINT_ENV_LOCK, and its
        // RestoreArchivalCheckpointEnv guard restores the original value.
        unsafe { std::env::remove_var(ARCHIVAL_CHECKPOINT_ENV) };
        maybe_produce_checkpoint(&state, &handle).await;
        let s = state.read().await;
        assert_eq!(latest_blocklace_checkpoint_height(&s.store), 6);
        assert!(
            s.store
                .published_blocklace_checkpoint_pair(1)
                .unwrap()
                .is_some(),
            "early return changes no immutable derived bytes"
        );
        assert!(
            existing_checkpoint_is_authorized(&s.store, 1).is_err(),
            "default early return must restore bounded proof policy"
        );
        assert!(load_blocklace_checkpoint(&s.store, 1).is_none());
        let proofs = checkpoint_proofs().lock().unwrap();
        assert_eq!(
            proofs.keys().filter(|(id, _)| *id == target).count(),
            MAX_RETAINED_CHECKPOINTS
        );
        assert!(proofs.get(&(target, 6)).is_some_and(|p| !p.archival));
    }
}

#[tokio::test]
async fn archival_six_live_producer_checkpoints_keep_explicit_height_one() {
    let _env_lock = ARCHIVAL_CHECKPOINT_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let _env_restore = RestoreArchivalCheckpointEnv::set(true);
    produce_six_live_checkpoints(true, false).await;
}

#[tokio::test]
async fn default_six_live_producer_checkpoints_evict_height_one() {
    let _env_lock = ARCHIVAL_CHECKPOINT_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let _env_restore = RestoreArchivalCheckpointEnv::set(false);
    produce_six_live_checkpoints(false, false).await;
}

#[tokio::test]
async fn switching_default_to_archival_promotes_only_existing_receipts_then_early_return_restores_cap()
 {
    let _env_lock = ARCHIVAL_CHECKPOINT_ENV_LOCK
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let _env_restore = RestoreArchivalCheckpointEnv::set(false);
    produce_six_live_checkpoints(false, true).await;
}

#[tokio::test]
async fn finalized_checkpoint_ledger_refuses_concurrent_unfinalized_mutation() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = std::sync::Arc::new(tokio::sync::RwLock::new(dregg_cell::Ledger::new()));
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&*ledger.read().await))
        .unwrap();
    let durable_root = store
        .finalized_commit_authority_at(0)
        .unwrap()
        .unwrap()
        .ledger_root();
    let (attempt, started) = tokio::sync::oneshot::channel();
    let (finished, mut completion) = tokio::sync::oneshot::channel();
    let guard = ledger.read().await;
    let writer = ledger.clone();
    let mutation = tokio::spawn(async move {
        attempt.send(()).unwrap();
        let mut ledger = writer.write().await;
        ledger
            .insert_cell(dregg_cell::Cell::with_balance([0x31; 32], [0; 32], 7))
            .unwrap();
        finished.send(()).unwrap();
    });
    started.await.unwrap();
    assert!(
        completion.try_recv().is_err(),
        "mutation cannot pass the snapshot read lock"
    );
    assert!(
        finalized_checkpoint_ledger_wire(&store, &guard, 1).is_ok(),
        "a committed root and unchanged ledger are publishable before the writer enters"
    );
    drop(guard);
    completion.await.unwrap();
    mutation.await.unwrap();
    assert_eq!(
        store.commit_cursor().unwrap(),
        1,
        "local MCP mutation is not a commit"
    );
    assert_eq!(
        store
            .finalized_commit_authority_at(0)
            .unwrap()
            .unwrap()
            .ledger_root(),
        durable_root,
        "local MCP mutation leaves finalized authority unchanged"
    );
    assert!(
        finalized_checkpoint_ledger_wire(&store, &*ledger.read().await, 1)
            .unwrap_err()
            .contains("diverges from finalized authority"),
        "the same height must refuse a local cell inserted after the DAG snapshot"
    );
}

fn empty_checkpoint_test_commit(ledger: &dregg_cell::Ledger) -> dregg_persist::CommitRecord {
    dregg_persist::CommitRecord {
        ordinal: 0,
        height: 1,
        block_id: [0x22; 32],
        block_executed_up_to: 1,
        turn_hash: [0x23; 32],
        creator: [0x24; 32],
        receipt_hash: [0x25; 32],
        ledger_root: canonical_ledger_root(ledger),
        touched_cells: vec![],
        removed: vec![],
    }
}

#[test]
fn finalized_checkpoint_ledger_binds_committed_root_and_refuses_missing_authority() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = dregg_cell::Ledger::new();
    assert!(finalized_checkpoint_ledger_wire(&store, &ledger, 1).is_err());
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    assert!(finalized_checkpoint_ledger_wire(&store, &ledger, 1).is_ok());
    let mut altered = ledger;
    altered
        .insert_cell(dregg_cell::Cell::with_balance([0x32; 32], [0; 32], 9))
        .unwrap();
    assert!(finalized_checkpoint_ledger_wire(&store, &altered, 1).is_err());
}

#[test]
fn fresh_produced_pair_serves_unchanged_wire_but_legacy_pair_refuses() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let dag = compress_checkpoint_data(b"full historical DAG".to_vec());
    let ledger = dregg_cell::Ledger::new();
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    let wire = finalized_checkpoint_ledger_wire(&store, &ledger, 12).unwrap();
    let stored = compress_checkpoint_data(wire.clone());
    store.set_config("blocklace_checkpoint_12", &dag).unwrap();
    store
        .set_config("blocklace_checkpoint_latest_height", &12u64.to_le_bytes())
        .unwrap();
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    assert!(
        load_blocklace_checkpoint(&store, 12).is_none(),
        "orphaned DAG is not published"
    );
    store
        .set_config("blocklace_ledger_snapshot_12", &stored)
        .unwrap();
    assert_eq!(
        latest_blocklace_checkpoint_height(&store),
        0,
        "a complete legacy pair has no H→ordinal proof"
    );
    assert!(load_blocklace_checkpoint(&store, 12).is_none());
    assert!(existing_checkpoint_is_authorized(&store, 12).is_err());
    assert_eq!(
        store.get_config("blocklace_ledger_snapshot_12").unwrap(),
        Some(stored.clone())
    );

    let fresh = dregg_persist::PersistentStore::open_in_memory().unwrap();
    fresh
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    fresh
        .publish_blocklace_checkpoint_pair(12, &dag, &stored, 5)
        .unwrap();
    assert!(
        load_blocklace_checkpoint(&fresh, 12).is_none(),
        "generic publication alone cannot mint proof"
    );
    record_live_finality_checkpoint(&fresh, 12, &dag, &stored, canonical_ledger_root(&ledger), 5)
        .unwrap();
    let served = load_blocklace_checkpoint(&fresh, 12).unwrap();
    assert_eq!(served.height, 12);
    assert_eq!(hex_decode_var(&served.blocklace).unwrap(), dag);
    assert_eq!(hex_decode_var(&served.ledger).unwrap(), stored);
    assert_eq!(
        hex_decode_var(&served.blocklace_hash).unwrap(),
        blake3::hash(b"full historical DAG").as_bytes().to_vec()
    );
    assert_eq!(
        hex_decode_var(&served.ledger_hash).unwrap(),
        blake3::hash(&wire).as_bytes().to_vec()
    );
    assert!(existing_checkpoint_is_authorized(&fresh, 12).unwrap());
    assert_eq!(latest_blocklace_checkpoint_height(&fresh), 12);
}

#[test]
fn legacy_pair_refuses_even_with_matching_root_and_preserves_immutable_bytes() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let dag = compress_checkpoint_data(b"legacy signed DAG".to_vec());
    let ledger = dregg_cell::Ledger::new();
    let good = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    store.set_config("blocklace_checkpoint_12", &dag).unwrap();
    store
        .set_config("blocklace_ledger_snapshot_12", &good)
        .unwrap();
    store
        .set_config("blocklace_checkpoint_latest_height", &12u64.to_le_bytes())
        .unwrap();
    assert!(
        existing_checkpoint_is_authorized(&store, 12).is_err(),
        "producer cannot early-return on legacy root membership"
    );
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    assert!(load_blocklace_checkpoint(&store, 12).is_none());
    assert_eq!(
        store.get_config("blocklace_ledger_snapshot_12").unwrap(),
        Some(good.clone())
    );

    // A locally inserted MCP cell leaves the durable commit root unchanged.
    let mut mutated = ledger;
    mutated
        .insert_cell(dregg_cell::Cell::with_balance([0x45; 32], [0; 32], 100))
        .unwrap();
    let bad = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&mutated));
    store
        .set_config("blocklace_ledger_snapshot_12", &bad)
        .unwrap();
    assert!(
        existing_checkpoint_is_authorized(&store, 12).is_err(),
        "producer cannot bypass verification"
    );
    assert_eq!(
        latest_blocklace_checkpoint_height(&store),
        0,
        "do not advertise unfinalized pair"
    );
    assert!(
        load_blocklace_checkpoint(&store, 12).is_none(),
        "explicit-height API also refuses"
    );
    assert!(
        store
            .publish_blocklace_checkpoint_pair(12, &dag, &good, 5)
            .is_err(),
        "never overwrite complete immutable bad pair"
    );
    assert_eq!(
        store.get_config("blocklace_ledger_snapshot_12").unwrap(),
        Some(bad)
    );
}

#[test]
fn fresh_retained_pair_keeps_its_ordinal_and_wrong_height_legacy_root_refuses() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = dregg_cell::Ledger::new();
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    let original = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    let dag = compress_checkpoint_data(b"old signed DAG".to_vec());
    store
        .publish_blocklace_checkpoint_pair(1, &dag, &original, 5)
        .unwrap();
    record_live_finality_checkpoint(
        &store,
        1,
        &dag,
        &original,
        canonical_ledger_root(&ledger),
        5,
    )
    .unwrap();
    let mut changed = ledger;
    changed
        .insert_cell(dregg_cell::Cell::with_balance([0x47; 32], [0; 32], 50))
        .unwrap();
    let mut next = empty_checkpoint_test_commit(&changed);
    next.ordinal = 1;
    next.height = 2;
    next.block_executed_up_to = 2;
    next.block_id = [0x48; 32];
    next.turn_hash = [0x49; 32];
    store.commit_finalized_turn(1, &next).unwrap();
    assert!(existing_checkpoint_is_authorized(&store, 1).unwrap());
    assert_eq!(load_blocklace_checkpoint(&store, 1).unwrap().height, 1);
    // Adversarial pre-upgrade H2/A matches a historical finalized root,
    // but H2 finalized with B: a root-membership check would serve A.
    store
        .publish_blocklace_checkpoint_pair(2, &dag, &original, 5)
        .unwrap();
    assert!(existing_checkpoint_is_authorized(&store, 2).is_err());
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    assert!(load_blocklace_checkpoint(&store, 2).is_none());
    assert_eq!(
        store.get_config("blocklace_ledger_snapshot_2").unwrap(),
        Some(original)
    );
    assert!(
        load_blocklace_checkpoint(&store, 1).is_some(),
        "exact older live receipt remains valid"
    );
    let later = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&changed));
    assert!(
        store
            .publish_blocklace_checkpoint_pair(2, &dag, &later, 5)
            .is_err(),
        "immutable wrong-height pair cannot be replaced"
    );
}

#[test]
fn tombstoned_duplicate_latest_preserves_unproven_predecessor_but_refuses_it() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = dregg_cell::Ledger::new();
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    let good = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    store
        .set_config(
            "blocklace_checkpoint_1",
            &compress_checkpoint_data(b"historical DAG".to_vec()),
        )
        .unwrap();
    store
        .set_config("blocklace_ledger_snapshot_1", &good)
        .unwrap();
    store.set_config("blocklace_checkpoint_2", b"").unwrap();
    store
        .set_config("blocklace_ledger_snapshot_2", b"")
        .unwrap();
    store
        .set_config(
            "blocklace_checkpoint_heights",
            &postcard::to_stdvec(&vec![1u64, 2, 2]).unwrap(),
        )
        .unwrap();
    store
        .set_config("blocklace_checkpoint_latest_height", &2u64.to_le_bytes())
        .unwrap();
    assert_eq!(
        store.latest_blocklace_checkpoint_candidate().unwrap(),
        Some(1)
    );
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    assert!(load_blocklace_checkpoint(&store, 1).is_none());
    assert!(load_blocklace_checkpoint(&store, 2).is_none());
    assert!(
        !existing_checkpoint_is_authorized(&store, 2).unwrap(),
        "producer must re-publish tombstoned height"
    );
}

#[test]
fn failed_legacy_latest_write_is_structurally_recoverable_but_not_authorized() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = dregg_cell::Ledger::new();
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    let bytes = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    let dag = compress_checkpoint_data(b"signed historical DAG".to_vec());
    store.set_config("blocklace_checkpoint_1", &dag).unwrap();
    store
        .set_config("blocklace_ledger_snapshot_1", &bytes)
        .unwrap();
    store.set_config("blocklace_checkpoint_2", &dag).unwrap();
    store
        .set_config("blocklace_checkpoint_latest_height", &1u64.to_le_bytes())
        .unwrap();
    store
        .set_config(
            "blocklace_checkpoint_heights",
            &postcard::to_stdvec(&vec![1u64, 2]).unwrap(),
        )
        .unwrap();
    assert_eq!(
        latest_blocklace_checkpoint_height(&store),
        0,
        "torn indexed tail is not an announcement"
    );
    assert!(load_blocklace_checkpoint(&store, 2).is_none());
    store
        .set_config("blocklace_ledger_snapshot_2", &bytes)
        .unwrap();
    assert_eq!(
        store.latest_blocklace_checkpoint_candidate().unwrap(),
        Some(2)
    );
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    assert!(load_blocklace_checkpoint(&store, 2).is_none());
    assert!(existing_checkpoint_is_authorized(&store, 2).is_err());
}

#[test]
fn missing_authority_and_generic_published_pair_cannot_mint_producer_proof() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = dregg_cell::Ledger::new();
    let bytes = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    store
        .publish_blocklace_checkpoint_pair(1, b"dag", &bytes, 5)
        .unwrap();
    assert!(existing_checkpoint_is_authorized(&store, 1).is_err());
    assert!(load_blocklace_checkpoint(&store, 1).is_none());
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    assert!(existing_checkpoint_is_authorized(&store, 1).is_err());
    assert!(load_blocklace_checkpoint(&store, 1).is_none());
    assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
    assert!(
        record_live_finality_checkpoint(&store, 1, b"dag", &bytes, [0x77; 32], 5).is_err(),
        "a wrong finalized root cannot mint even via the private producer function"
    );
}

#[test]
fn reopened_pair_and_mutated_bytes_or_ordinal_fail_closed() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("checkpoint.redb");
    let dag = compress_checkpoint_data(b"signed DAG".to_vec());
    let ledger = dregg_cell::Ledger::new();
    let wire = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    {
        let store = dregg_persist::PersistentStore::open(&path).unwrap();
        store
            .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
            .unwrap();
        store
            .publish_blocklace_checkpoint_pair(1, &dag, &wire, 5)
            .unwrap();
        record_live_finality_checkpoint(&store, 1, &dag, &wire, canonical_ledger_root(&ledger), 5)
            .unwrap();
        assert_eq!(latest_blocklace_checkpoint_height(&store), 1);
        store
            .set_config("blocklace_checkpoint_1", b"changed DAG")
            .unwrap();
        assert!(
            existing_checkpoint_is_authorized(&store, 1).is_err(),
            "mutated exact bytes fail early return"
        );
        assert_eq!(latest_blocklace_checkpoint_height(&store), 0);
        assert!(load_blocklace_checkpoint(&store, 1).is_none());
        store.set_config("blocklace_checkpoint_1", &dag).unwrap();
        store
            .set_config("blocklace_ledger_snapshot_1", b"changed ledger")
            .unwrap();
        assert!(
            existing_checkpoint_is_authorized(&store, 1).is_err(),
            "mutated ledger bytes refuse early return"
        );
        assert!(load_blocklace_checkpoint(&store, 1).is_none());
        store
            .set_config("blocklace_ledger_snapshot_1", &wire)
            .unwrap();
        assert!(existing_checkpoint_is_authorized(&store, 1).unwrap());
        let mut second = empty_checkpoint_test_commit(&ledger);
        second.ordinal = 1;
        second.height = 2;
        second.block_id = [0x61; 32];
        second.turn_hash = [0x62; 32];
        second.receipt_hash = [0x63; 32];
        store.commit_finalized_turn(1, &second).unwrap();
        // The receipt is pinned to ordinal 0, not the most recent root.
        assert!(existing_checkpoint_is_authorized(&store, 1).unwrap());
    }
    let reopened = dregg_persist::PersistentStore::open(&path).unwrap();
    assert_eq!(
        reopened.get_config("blocklace_checkpoint_1").unwrap(),
        Some(dag)
    );
    assert_eq!(
        reopened.get_config("blocklace_ledger_snapshot_1").unwrap(),
        Some(wire)
    );
    assert!(
        existing_checkpoint_is_authorized(&reopened, 1).is_err(),
        "reopen has no volatile receipt"
    );
    assert_eq!(latest_blocklace_checkpoint_height(&reopened), 0);
    assert!(load_blocklace_checkpoint(&reopened, 1).is_none());
}

#[test]
fn live_proof_detects_durable_authority_change_and_bounds_retention() {
    let store = dregg_persist::PersistentStore::open_in_memory().unwrap();
    let ledger = dregg_cell::Ledger::new();
    store
        .commit_finalized_turn(0, &empty_checkpoint_test_commit(&ledger))
        .unwrap();
    let wire = compress_checkpoint_data(finalized_checkpoint_ledger_wire_for_test(&ledger));
    for height in 1..=6 {
        let dag = compress_checkpoint_data(vec![height as u8]);
        store
            .publish_blocklace_checkpoint_pair(height, &dag, &wire, MAX_RETAINED_CHECKPOINTS)
            .unwrap();
        record_live_finality_checkpoint(
            &store,
            height,
            &dag,
            &wire,
            canonical_ledger_root(&ledger),
            MAX_RETAINED_CHECKPOINTS,
        )
        .unwrap();
    }
    assert!(
        !existing_checkpoint_is_authorized(&store, 1).unwrap(),
        "default derived-pair and matching proof eviction refuse oldest height"
    );
    assert!(existing_checkpoint_is_authorized(&store, 6).unwrap());
    let old_ordinal = {
        let mut proofs = checkpoint_proofs().lock().unwrap();
        let proof = proofs.get_mut(&(store.checkpoint_store_id(), 6)).unwrap();
        std::mem::replace(&mut proof.ordinal, 7)
    };
    assert!(
        existing_checkpoint_is_authorized(&store, 6).is_err(),
        "a forged ordinal has no durable authority"
    );
    checkpoint_proofs()
        .lock()
        .unwrap()
        .get_mut(&(store.checkpoint_store_id(), 6))
        .unwrap()
        .ordinal = old_ordinal;
    assert!(existing_checkpoint_is_authorized(&store, 6).unwrap());
    // A changed root at the recorded ordinal cannot be manufactured by
    // derived metadata: this is an internal negative proof assertion.
    let old = {
        let mut proofs = checkpoint_proofs().lock().unwrap();
        let proof = proofs.get_mut(&(store.checkpoint_store_id(), 6)).unwrap();
        std::mem::replace(&mut proof.root, [0x63; 32])
    };
    assert!(existing_checkpoint_is_authorized(&store, 6).is_err());
    checkpoint_proofs()
        .lock()
        .unwrap()
        .get_mut(&(store.checkpoint_store_id(), 6))
        .unwrap()
        .root = old;
    assert!(existing_checkpoint_is_authorized(&store, 6).unwrap());
}

fn finalized_checkpoint_ledger_wire_for_test(ledger: &dregg_cell::Ledger) -> Vec<u8> {
    let cells: Vec<(&dregg_cell::CellId, &dregg_cell::Cell)> = ledger.iter().collect();
    postcard::to_stdvec(&cells).unwrap()
}

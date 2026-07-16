//! Driven demonstration of GENESIS-FROM-SNAPSHOT.
//!
//! The hard gate: export a cell-set (cells + content addresses + cross-epoch
//! vouchers) → seed a FRESH genesis → the cells survive and re-address
//! IDENTICALLY; a POST-FREEZE-TAMPERED export (forged cell) is REFUSED; a fresh
//! genesis without the snapshot is empty (the baseline WIPE).
//!
//! (No history-proof assertions: the simulated-IVC "history proof" leg was
//! REMOVED by the mock-proof purge — see lib.rs HONEST SCOPE.)

use super::*;
use dregg_cell::Cell;

/// The OLD chain's federation id (committee epoch N).
fn old_fed() -> FederationId {
    [0xA1; 32]
}

/// The FRESH genesis's federation id (committee epoch N+1) — minted from new
/// committee keys, distinct from the old one.
fn new_fed() -> FederationId {
    [0xB2; 32]
}

/// A "character" cell: a hosted cell whose balance is the character's score and
/// whose state fields carry level / class. Its identity is content-addressed
/// from (public_key, token_id), independent of the chain hosting it.
fn character_cell() -> Cell {
    let public_key = [0x11; 32];
    let token_id = *b"the-descent:character:hero-0001\0"; // 32-byte token domain
    let mut cell = Cell::with_balance(public_key, token_id, 1337 /* score */);
    // level = 7, class = 3 (arbitrary character state).
    cell.state.fields[0] = {
        let mut f = [0u8; 32];
        f[0] = 7;
        f
    };
    cell.state.fields[1] = {
        let mut f = [0u8; 32];
        f[0] = 3;
        f
    };
    cell
}

/// A "universe" cell — a second carried object (a procgen seed + generation count).
fn universe_cell() -> Cell {
    let public_key = [0x22; 32];
    let token_id = *b"the-descent:universe:seed-000042"; // 32 bytes
    let mut cell = Cell::with_balance(public_key, token_id, 0);
    cell.state.fields[0] = {
        let mut f = [0u8; 32];
        f[0..8].copy_from_slice(&42u64.to_le_bytes()); // seed
        f
    };
    cell
}

// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn honest_snapshot_survives_readdresses_and_verifies() {
    let cells = vec![character_cell(), universe_cell()];

    // FREEZE + EXPORT from the old chain, targeting the fresh genesis.
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells)
        .expect("export builds a snapshot with cross-epoch vouchers");
    assert_eq!(snapshot.entries.len(), 2);

    // Remember the exported content-addresses.
    let char_addr = character_cell().id();
    let uni_addr = universe_cell().id();

    // IMPORT / SEED a fresh genesis (new committee keys → new_fed()).
    let seeded = seed_genesis(&snapshot, new_fed()).expect("honest snapshot seeds cleanly");
    assert_eq!(seeded.new_federation_id, new_fed());
    assert_eq!(seeded.cells.len(), 2, "both cells survive the re-genesis");

    // RE-ADDRESS IDENTICALLY: each carried cell recomputes to the SAME content
    // address it had on the old chain, and to what a fresh derive would produce.
    let survived_char = &seeded.cells[0];
    assert_eq!(
        survived_char.id(),
        char_addr,
        "character re-addresses identically"
    );
    assert_eq!(recompute_content_address(survived_char), char_addr);
    assert_eq!(
        Cell::new(*survived_char.public_key(), *survived_char.token_id()).id(),
        char_addr,
        "a fresh derive in the new chain yields the identical address",
    );

    let survived_uni = &seeded.cells[1];
    assert_eq!(
        survived_uni.id(),
        uni_addr,
        "universe re-addresses identically"
    );

    // The carried character state is intact (score + level preserved).
    assert_eq!(survived_char.state.balance(), 1337);
    assert_eq!(survived_char.state.fields[0][0], 7);

    // Each entry's voucher binds the exact frozen state (the consistency check
    // seed_genesis re-runs).
    for entry in &snapshot.entries {
        assert_eq!(
            entry.voucher.state_commitment,
            entry.cell.state_commitment()
        );
        assert_eq!(entry.voucher.cell_id, entry.cell.id());
    }
}

#[test]
fn baseline_empty_snapshot_seeds_an_empty_genesis() {
    // A re-genesis with NOTHING to carry forward → an empty cell-set (today's
    // WIPE behaviour, recovered as the degenerate case).
    let empty = GenesisSnapshot::export(old_fed(), new_fed(), 0, &[]).unwrap();
    let seeded = seed_genesis(&empty, new_fed()).unwrap();
    assert!(seeded.cells.is_empty(), "no snapshot ⇒ empty fresh genesis");
}

#[test]
fn tampered_forged_cell_is_refused_but_honest_imports() {
    // Non-vacuity: the SAME snapshot imports honestly; only the forged copy is refused.
    let cells = vec![character_cell()];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    // Honest import succeeds.
    assert!(seed_genesis(&snapshot, new_fed()).is_ok());

    // Forge the carried cell: bump the character's level AFTER freeze. This
    // changes the cell's state_commitment, breaking the voucher binding.
    let mut forged = snapshot.clone();
    forged.entries[0].cell.state.fields[0][0] = 99; // level 7 → 99

    let err = seed_genesis(&forged, new_fed()).expect_err("a forged cell is refused");
    match err {
        ImportError::Entry {
            index: 0,
            kind: EntryReject::VoucherMismatch,
        } => {}
        other => panic!("expected VoucherMismatch on the forged cell, got {other:?}"),
    }
}

#[test]
fn snapshot_minted_for_a_different_epoch_is_refused() {
    let cells = vec![character_cell()];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    // Seeding a chain whose federation id is NOT the snapshot's target → refused.
    let wrong_fed = [0xCC; 32];
    assert_eq!(
        seed_genesis(&snapshot, wrong_fed),
        Err(ImportError::WrongDestination),
    );
}

#[test]
fn snapshot_round_trips_through_serde() {
    // The snapshot is meant to be written to a file the operator hands to the
    // fresh-genesis boot, so it must serialize and deserialize losslessly.
    let cells = vec![character_cell()];
    let snapshot = GenesisSnapshot::export(old_fed(), new_fed(), 4096, &cells).unwrap();

    let json = serde_json::to_string(&snapshot).expect("serialize snapshot");
    let back: GenesisSnapshot = serde_json::from_str(&json).expect("deserialize snapshot");
    // Compare the canonical re-serialization (GenesisSnapshot derives no PartialEq).
    assert_eq!(
        json,
        serde_json::to_string(&back).expect("re-serialize"),
        "snapshot round-trips through serde losslessly",
    );

    // The deserialized snapshot still seeds and its cells still re-address identically.
    let seeded = seed_genesis(&back, new_fed()).expect("deserialized snapshot seeds");
    assert_eq!(seeded.cells[0].id(), character_cell().id());
}

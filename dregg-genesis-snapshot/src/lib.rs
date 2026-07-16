//! GENESIS-FROM-SNAPSHOT — carry a cell-set across an EPOCH bump.
//!
//! ## The gap this closes
//!
//! A devnet re-genesis today is a **WIPE**: `node/src/genesis.rs` mints fresh
//! committee keys → a fresh `federation_id` → a brand-new chain, and
//! `deploy/genesis/generate.sh --force` deletes the old `genesis.json` and keys.
//! Every character, leaderboard, and universe minted on the old chain is gone.
//!
//! The vat-migration design (`plans/vat-migration-design.md`) already specifies a
//! `CellExportBundle` — a cell carried FROM one federation TO another with a
//! state-commitment binding, so the target can install it without re-executing the
//! source. That primitive is **cross-federation**. This crate **generalizes it to
//! cross-EPOCH**: the "source federation" is the OLD chain (committee epoch N),
//! the "destination federation" is the FRESH GENESIS (epoch N+1). A re-genesis can
//! then SEED the new chain with a frozen EXPORT of the old cell-set instead of
//! wiping it.
//!
//! ```text
//!   OLD chain (epoch N)                         FRESH genesis (epoch N+1)
//!   ───────────────────                         ─────────────────────────
//!   mint new committee keys ── new fed id ─────▶ (destination federation id)
//!   FREEZE + EXPORT cell-set:                    IMPORT / SEED:
//!     per cell:                                    per entry, REFUSE unless
//!       · full Cell                                  · id re-addresses identically
//!       · content-address (CellId)                     (verify_id_integrity)
//!       · cross-epoch MigrationVoucher              · voucher binds this exact state
//!         (from = old fed, to = new fed)               (from/to + state_commitment)
//!                                                 ⇒ carried-forward cells re-address
//!                                                    IDENTICALLY, freeze-state bound.
//! ```
//!
//! ## Why the imported cell re-addresses identically
//!
//! A cell's identity is `CellId = derive_raw(public_key, token_id)` — a pure
//! content-address, independent of which federation or epoch hosts it. So an
//! honestly-carried cell, dropped into the fresh genesis, recomputes to the SAME
//! `CellId`. [`seed_genesis`] re-checks this ([`SnapshotEntry`] integrity) and
//! refuses any entry whose declared address does not match its recomputed one.
//!
//! ## What is refused on import (non-vacuous tamper rejection)
//!
//! * A **forged cell** (e.g. a balance bumped after freeze) changes the cell's
//!   `state_commitment`, which breaks the migration voucher binding
//!   ([`EntryReject::VoucherMismatch`]).
//! * A cell whose **content-address does not recompute** → [`EntryReject::AddressMismatch`]
//!   / [`EntryReject::IdentityBroken`].
//! * A snapshot minted for a **different destination epoch** → [`ImportError::WrongDestination`].
//!
//! The honest cell in every one of these pairs imports cleanly, so the rejection
//! is non-vacuous.
//!
//! ## HONEST SCOPE — what these checks are, and are NOT
//!
//! The import checks are **CONSISTENCY checks over unauthenticated data**: they
//! bind the carried cell to its own freeze-time voucher and its own content
//! address, so post-freeze mutation of an entry is caught. They are **NOT a
//! history proof and NOT source-chain authentication** — a forger who authors an
//! entire entry (cell + voucher, self-consistent) passes them. Authenticity of a
//! snapshot therefore rests on the channel that delivers it (the operator hands
//! the snapshot file to the fresh-genesis boot).
//!
//! **THE HISTORY PROOF WAS REMOVED, NOT FAKED** (mock-proof purge, 2026-07-16;
//! `circuit-prove/tests/mock_proof_purge_gate.rs`). Earlier revisions attached a
//! per-entry "IVC history proof" minted by the simulated IVC in
//! `circuit/src/ivc.rs` — a hash-chain over synthetic fold deltas whose verifier
//! only recomputes a digest of the proof's OWN public data. Anyone who could
//! author a snapshot entry could mint a passing "history proof" for it, so the
//! leg added ZERO soundness over the voucher binding while *reading* as a
//! cryptographic history claim. A REAL history leg needs the per-turn
//! `FinalizedTurn` data (the rotated whole-turn descriptor proofs) folded by
//! `dregg_circuit_prove::ivc_turn_chain::prove_turn_chain_recursive` — data this
//! layer does not hold (the exporter has only the `Cell`); wiring it requires the
//! node to persist `FinalizedTurn`s at finalization (see the purge-gate module
//! docs). Until then, this crate carries NO history claim at all.
//!
//! * **Real**: the export/import carry-forward, the content-address re-addressing
//!   stability, and the freeze-state voucher consistency check on import.
//! * **Deploy wiring** (NOT built here): threading [`GenesisSnapshot::export`] into a
//!   node's freeze path and [`seed_genesis`] into `node/src/genesis.rs` /
//!   `deploy/genesis/generate.sh` so a live re-genesis reads a snapshot file. This
//!   crate is the additive primitive; the operator wiring is a separate deploy step.

use dregg_cell::migration::{FederationId, MigrationError as CellMigrationError, MigrationVoucher};
use dregg_cell::{Cell, CellId};
use serde::{Deserialize, Serialize};

/// One carried cell in a [`GenesisSnapshot`]: the full cell, its content-address,
/// and a cross-epoch migration voucher.
///
/// Deliberately **no history field**: see the module's HONEST SCOPE — this layer
/// holds no provable per-turn data, and a mock "history proof" is worse than none.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SnapshotEntry {
    /// The full cell state carried forward.
    pub cell: Cell,
    /// The content-addressed id declared for this cell. Import recomputes
    /// `cell.id()` and refuses on mismatch, so the address is stable and honest.
    pub content_address: CellId,
    /// The cross-epoch migration voucher — the vat-migration primitive
    /// ([`Cell::migration_voucher`](dregg_cell::Cell::migration_voucher)) reused
    /// with `from = old federation id`, `to = new (fresh-genesis) federation id`.
    /// It binds the exact pre-freeze `state_commitment`, so a state forged after
    /// freeze is caught (a consistency check, not source-chain authentication).
    pub voucher: MigrationVoucher,
}

/// A frozen EXPORT of an old chain's cell-set, minted to seed a fresh genesis.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct GenesisSnapshot {
    /// The OLD chain's federation id (committee epoch N).
    pub source_federation_id: FederationId,
    /// The fresh genesis's federation id (committee epoch N+1). Bound into every
    /// voucher; import refuses a snapshot whose target is not the seeding chain.
    pub target_federation_id: FederationId,
    /// The old-chain height at which the cell-set was frozen and exported.
    pub frozen_at_height: u64,
    /// The carried cells.
    pub entries: Vec<SnapshotEntry>,
}

impl GenesisSnapshot {
    /// FREEZE + EXPORT: build a snapshot of `cells` targeting the fresh-genesis
    /// `target_federation_id`.
    ///
    /// This models the operator flow of a carry-forward re-genesis: mint the new
    /// committee keys first (→ `target_federation_id`), then freeze the old
    /// cell-set and export it toward that new chain.
    pub fn export(
        source_federation_id: FederationId,
        target_federation_id: FederationId,
        frozen_at_height: u64,
        cells: &[Cell],
    ) -> Result<Self, SnapshotError> {
        let mut entries = Vec::with_capacity(cells.len());
        for cell in cells {
            // The vat-migration voucher, generalized cross-epoch: from = old fed,
            // to = fresh-genesis fed, mode preserved, height = freeze height.
            let voucher = cell
                .migration_voucher(
                    source_federation_id,
                    target_federation_id,
                    cell.mode.clone(),
                    frozen_at_height,
                )
                .map_err(SnapshotError::Voucher)?;
            entries.push(SnapshotEntry {
                content_address: cell.id(),
                voucher,
                cell: cell.clone(),
            });
        }
        Ok(Self {
            source_federation_id,
            target_federation_id,
            frozen_at_height,
            entries,
        })
    }
}

/// The result of seeding a fresh genesis from a snapshot: the new federation id
/// plus the carried-forward cells (each having re-addressed identically and had
/// its history validated). An empty snapshot yields an empty cell-set — the
/// baseline WIPE behaviour when there is nothing to carry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeededGenesis {
    /// The fresh chain's federation id.
    pub new_federation_id: FederationId,
    /// The carried-forward, validated cells — ready to be materialized as the
    /// fresh genesis's initial cell-set.
    pub cells: Vec<Cell>,
}

/// IMPORT / SEED: validate every entry of `snapshot` and produce the fresh
/// genesis's carried-forward cell-set.
///
/// Refuses (returns `Err`) if the snapshot targets a different destination epoch,
/// or if ANY entry fails validation (post-freeze forged cell / non-stable
/// address). The honest snapshot seeds cleanly. These are CONSISTENCY checks over
/// unauthenticated data — see the module's HONEST SCOPE for what they do NOT claim.
pub fn seed_genesis(
    snapshot: &GenesisSnapshot,
    new_federation_id: FederationId,
) -> Result<SeededGenesis, ImportError> {
    // Cross-epoch destination binding: the snapshot must have been minted FOR
    // this fresh chain (the vouchers' `to` == this federation id).
    if snapshot.target_federation_id != new_federation_id {
        return Err(ImportError::WrongDestination);
    }

    let mut cells = Vec::with_capacity(snapshot.entries.len());
    for (index, entry) in snapshot.entries.iter().enumerate() {
        validate_entry(snapshot, entry).map_err(|kind| ImportError::Entry { index, kind })?;
        cells.push(entry.cell.clone());
    }

    Ok(SeededGenesis {
        new_federation_id,
        cells,
    })
}

/// Validate a single carried cell. Layered so that a forged cell trips at least
/// one independent check.
fn validate_entry(snapshot: &GenesisSnapshot, entry: &SnapshotEntry) -> Result<(), EntryReject> {
    // 1. Content-address stability: the imported cell must re-address identically.
    //    `verify_id_integrity` recomputes `derive_raw(public_key, token_id)` and
    //    compares to the carried id (federation/epoch-independent), and the
    //    declared `content_address` must match it too.
    if !entry.cell.verify_id_integrity() {
        return Err(EntryReject::IdentityBroken);
    }
    if entry.content_address != entry.cell.id() {
        return Err(EntryReject::AddressMismatch);
    }

    // 2. Cross-epoch migration voucher binding (the vat-migration primitive):
    //    the voucher must bind THIS cell's id + exact state commitment, and the
    //    old→new federation pair. A state forged after freeze changes
    //    `state_commitment` and is caught here.
    //
    //    (No history leg: the layer holds no per-turn provable data, and the
    //    simulated-IVC "history proof" that used to sit here was minterable by
    //    any forger — removed by the mock-proof purge, see the module docs.)
    let state_commitment = entry.cell.state_commitment();
    if entry.voucher.cell_id != entry.cell.id()
        || entry.voucher.state_commitment != state_commitment
        || entry.voucher.from != snapshot.source_federation_id
        || entry.voucher.to != snapshot.target_federation_id
    {
        return Err(EntryReject::VoucherMismatch);
    }

    Ok(())
}

/// Errors from building a snapshot (EXPORT side).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotError {
    /// The underlying vat-migration voucher could not be minted (terminal / broken cell).
    Voucher(CellMigrationError),
}

impl core::fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Voucher(e) => write!(f, "migration voucher mint failed: {e}"),
        }
    }
}

impl std::error::Error for SnapshotError {}

/// Errors from seeding a genesis (IMPORT side).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportError {
    /// The snapshot was minted for a different destination federation (epoch).
    WrongDestination,
    /// A specific entry was refused.
    Entry {
        /// Index of the offending entry in `snapshot.entries`.
        index: usize,
        /// Why it was refused.
        kind: EntryReject,
    },
}

impl core::fmt::Display for ImportError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WrongDestination => {
                f.write_str("snapshot target federation does not match the seeding chain")
            }
            Self::Entry { index, kind } => write!(f, "snapshot entry {index} refused: {kind}"),
        }
    }
}

impl std::error::Error for ImportError {}

/// The specific reason a carried cell was refused on import.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EntryReject {
    /// `id != derive_raw(public_key, token_id)` — the cell does not re-address to its own id.
    IdentityBroken,
    /// The declared `content_address` does not match the recomputed `cell.id()`.
    AddressMismatch,
    /// The migration voucher does not bind this cell's id/state or the old→new federations.
    VoucherMismatch,
}

impl core::fmt::Display for EntryReject {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::IdentityBroken => f.write_str("cell does not re-address to its own id"),
            Self::AddressMismatch => f.write_str("declared content-address does not recompute"),
            Self::VoucherMismatch => f.write_str("cross-epoch migration voucher binding broken"),
        }
    }
}

/// Recompute the content-address a cell would take in ANY chain/epoch. Exposed so
/// callers (and the demo) can demonstrate re-address stability directly.
pub fn recompute_content_address(cell: &Cell) -> CellId {
    CellId::derive_raw(cell.public_key(), cell.token_id())
}

#[cfg(test)]
mod tests;

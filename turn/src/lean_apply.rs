//! lean_apply.rs — THE SWAP state-producer: reconstitute a `cell::Ledger` from the verified
//! Lean executor's produced `WireState`.
//!
//! # The authority inversion this closes
//!
//! Today the node runs the verified Lean executor (`dregg_exec_full_forest_auth` /
//! `execFullForestG`, proven sorry-free) only as a passive veto-only SHADOW: the FFI produces a
//! full post-state, but `decode_shadow_verdict` keeps only `{committed, loglen, status}` and the
//! node commits the post-state the LEGACY Rust `TurnExecutor` produced. The verified executor is
//! never the state PRODUCER.
//!
//! The missing mechanism — which `dregg-lean-ffi/src/marshal.rs` names as "the biggest gap" — is a
//! `WireState → cell::Ledger` extractor. This module is that extractor. `dregg_lean_ffi`'s
//! `decode_shadow_state` now keeps the post-state `WireState`; here we map it back onto real
//! `CellId`s and reconstitute the authoritative ledger, so the verified executor's output can BE
//! the committed state.
//!
//! # The id seam
//!
//! The wire carries cells by a `u64` Nat (`marshal::cell_id_to_nat`'s codomain). The pre-state
//! snapshot assigned each referenced `CellId` a Nat via the SAME deterministic sorted scheme the
//! shadow marshaller uses (`lean_shadow::collect_id_map`). We invert that map (Nat → `CellId`) to
//! put the produced balances/nonces/fields back on the right cells. A produced cell whose Nat is
//! not in the inverse map is a marshaller gap (a created cell with a fresh, above-range Nat) and is
//! reported, never silently dropped.
//!
//! # Root computation (deliberately Rust-side)
//!
//! Lean produces the STATE; the EXISTING Rust hashing (`Ledger::root` / `hash_cell`) computes the
//! commitment. We do NOT ask Lean to compute the root — root-scheme unification is a separate later
//! task. Here: Lean produces the cells, Rust hashes them.

use std::collections::HashMap;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_lean_ffi::marshal::{WireState, WireValue};

use crate::lean_shadow::{self, ShadowHostCtx};
use crate::turn::Turn;

/// Why a `WireState` could not be fully reconstituted into a `Ledger`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtractError {
    /// A produced cell's wire Nat has no inverse in the pre-state id map (e.g. a freshly created
    /// cell whose Nat was assigned above the snapshot range). The verified executor edited a cell
    /// the marshaller cannot name back — a real marshaller gap, surfaced loudly.
    UnknownCellNat(u64),
    /// A produced cell's wire Nat maps to a `CellId` absent from the pre-state ledger (no template
    /// cell to carry the pk/token_id/permissions forward).
    NoTemplateCell { nat: u64, cell: CellId },
    /// A cell record carried a non-Int `balance`/`nonce` (the wire grammar should never emit this;
    /// fail-closed rather than coerce).
    NonIntScalar { nat: u64, field: &'static str },
    /// Driving the FFI / decoding the produced state failed.
    Ffi(String),
    /// The turn's forest was not fully marshallable (some effect has no wire arm), so there is no
    /// verified post-state to install.
    Ineligible,
}

impl std::fmt::Display for ExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtractError::UnknownCellNat(n) => {
                write!(f, "produced cell Nat {n} has no inverse in the pre-state id map (marshaller gap: a created/unmapped cell)")
            }
            ExtractError::NoTemplateCell { nat, cell } => {
                write!(f, "produced cell Nat {nat} -> {cell:?} has no pre-state template cell")
            }
            ExtractError::NonIntScalar { nat, field } => {
                write!(f, "produced cell Nat {nat} carried a non-Int `{field}`")
            }
            ExtractError::Ffi(e) => write!(f, "lean FFI / decode failed: {e}"),
            ExtractError::Ineligible => {
                write!(f, "turn forest not fully marshallable — no verified post-state to install")
            }
        }
    }
}

impl std::error::Error for ExtractError {}

/// Read a named `Int` field out of a cell record (returns `None` if absent or not an Int).
fn record_int(v: &WireValue, name: &str) -> Option<i128> {
    match v {
        WireValue::Record(fs) => fs.iter().find(|(k, _)| k == name).and_then(|(_, x)| match x {
            WireValue::Int(i) => Some(*i),
            _ => None,
        }),
        _ => None,
    }
}

/// Inverse of `lean_shadow::field_index_to_name` — map a wire field NAME back to its `fields[]`
/// slot index, or `None` for the scalar `balance`/`nonce` (handled separately) and any name that
/// is not a state slot.
fn field_name_to_index(name: &str) -> Option<usize> {
    match name {
        "balance" | "nonce" => None,
        "name" => Some(2),
        "owner" => Some(3),
        "expiry" => Some(4),
        "revoked" => Some(5),
        "target" => Some(6),
        other => other
            .strip_prefix("field_")
            .and_then(|n| n.parse::<usize>().ok()),
    }
}

/// Inverse of `lean_shadow::field_to_i128`: write the low 64 bits of an `i128` into the canonical
/// big-endian slot (`bytes[24..32]`).
fn i128_to_field(v: i128) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..32].copy_from_slice(&(v as u64).to_be_bytes());
    out
}

/// Build the inverse id map (wire Nat → `CellId`) from the pre-state snapshot's id map.
fn invert_id_map(id_map: &HashMap<CellId, u64>) -> HashMap<u64, CellId> {
    id_map.iter().map(|(cid, nat)| (*nat, *cid)).collect()
}

/// THE EXTRACTOR. Reconstitute a `cell::Ledger` from a verified-executor-produced `WireState`.
///
/// `inv_id_map` inverts the pre-state Nat labelling; `template` is the pre-state ledger whose cells
/// carry the identity/permission/capability fields the wire does not (pk, token_id, permissions,
/// c-list, program). For each produced cell we clone its template and overwrite the
/// balance/nonce/state-fields the verified executor produced.
///
/// Cells present in the template but ABSENT from the produced state (the verified executor left
/// them out of its output cell list) are carried forward UNCHANGED — the kernel's `cellsOfState`
/// only re-emits the cells it was given, so an unlisted template cell is unedited, not deleted.
pub fn wire_state_to_ledger(
    ws: &WireState,
    inv_id_map: &HashMap<u64, CellId>,
    template: &Ledger,
) -> Result<Ledger, ExtractError> {
    let mut produced_ids = std::collections::HashSet::new();
    let mut out_cells: HashMap<CellId, Cell> = HashMap::new();

    // The CANONICAL asset-0 balance lives in the per-asset `bal` side-table, NOT the cell record's
    // `balance` field — the verified Transfer (`bal` action) mutates `recKExecAsset`'s `bal` map and
    // leaves the record scalar at its seed value (a real wire-model fact, see the module-level note).
    // `cell::CellState::balance` is the asset-0 holding, so we read it from `bal` (asset 0), and only
    // fall back to the record `balance` when a cell has no `bal` entry.
    let asset0_bal: HashMap<u64, i128> = ws
        .bal
        .iter()
        .filter(|(_, asset, _)| *asset == 0)
        .map(|(cell, _, amt)| (*cell, *amt))
        .collect();

    for (nat, value) in &ws.cells {
        let cell_id = *inv_id_map
            .get(nat)
            .ok_or(ExtractError::UnknownCellNat(*nat))?;
        produced_ids.insert(cell_id);

        // Start from the pre-state template so identity/permissions/c-list/program survive.
        let mut cell = template
            .get(&cell_id)
            .cloned()
            .ok_or(ExtractError::NoTemplateCell { nat: *nat, cell: cell_id })?;

        // nonce is carried as a named scalar Int field in the cell record.
        let nonce = record_int(value, "nonce")
            .ok_or(ExtractError::NonIntScalar { nat: *nat, field: "nonce" })?;
        // balance: prefer the authoritative asset-0 `bal` entry; fall back to the record scalar.
        let bal = asset0_bal.get(nat).copied().or_else(|| record_int(value, "balance")).ok_or(
            ExtractError::NonIntScalar { nat: *nat, field: "balance" },
        )?;
        cell.state.set_balance(bal.max(0) as u64);
        cell.state.set_nonce(nonce.max(0) as u64);

        // Any other named Int field maps to a `fields[]` slot.
        if let WireValue::Record(fs) = value {
            for (k, x) in fs {
                if let (Some(idx), WireValue::Int(i)) = (field_name_to_index(k), x) {
                    if idx < dregg_cell::state::STATE_SLOTS {
                        let _ = cell.state.set_field(idx, i128_to_field(*i));
                    }
                }
            }
        }

        out_cells.insert(cell_id, cell);
    }

    // Reconstitute the ledger: produced cells (edited) + template cells the executor did not list
    // (carried unchanged, since the kernel only re-emits the cells it was handed).
    let mut ledger = Ledger::new();
    for (id, cell) in template.iter() {
        if let Some(produced) = out_cells.get(id) {
            let _ = ledger.insert_cell(produced.clone());
        } else {
            let _ = ledger.insert_cell(cell.clone());
        }
    }
    // Any produced cell NOT in the template (should be impossible given UnknownCellNat guards the
    // Nat, but defend against a fresh template-absent id) is inserted directly.
    for (id, cell) in &out_cells {
        if template.get(id).is_none() {
            let _ = ledger.insert_cell(cell.clone());
        }
    }

    Ok(ledger)
}

/// Drive a turn through the VERIFIED Lean executor and reconstitute the authoritative `Ledger` from
/// the post-state it produces — the full state-producer path (install the verified executor's
/// output). Returns the reconstituted ledger AND the commit bit.
///
/// `pre_ledger` is the pre-state; `host` the node-fed admission context (clock/freeze/head/budget).
/// On a rollback the verified executor echoes the (unchanged) pre-state, so the reconstituted
/// ledger equals the pre-state — which is exactly the legacy executor's rollback behaviour.
pub fn execute_via_lean(
    turn: &Turn,
    pre_ledger: &Ledger,
    host: &ShadowHostCtx,
) -> Result<(Ledger, bool), ExtractError> {
    if !lean_shadow::forest_is_marshallable(turn) {
        return Err(ExtractError::Ineligible);
    }
    let pre = lean_shadow::build_pre_ledger(turn, pre_ledger);
    let shadow_state =
        lean_shadow::run_shadow_state(turn, &pre, host).map_err(ExtractError::Ffi)?;
    let inv = invert_id_map(&pre.id_map);
    let ledger = wire_state_to_ledger(&shadow_state.state, &inv, pre_ledger)?;
    Ok((ledger, shadow_state.verdict.committed))
}

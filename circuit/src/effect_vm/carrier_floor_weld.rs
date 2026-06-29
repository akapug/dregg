//! # `carrier_floor_weld` — the GENTIAN floor BINDING discharged (PATH b, STAGED).
//!
//! `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md` §6 item 2 / `IN-AIR-AUTHORITY-DIGEST-GADGET.md`
//! named the last soundness gap before the sealed-escrow weld can flip to a deployed PURE-LIGHT-CLIENT
//! truth: the selector-forcing gadget ([`authority_digest_weld`]) decoded the required-tag floor from a
//! separately-hashed `B_AUTHORITY_DIGEST` limb, and its soundness was conditional on the Lean
//! `hcommitLimb` hypothesis — that the FREE rotated limb carries `hash(the real declared floor)`.
//! Nothing FORCED it: a forger settling a half-open escrow on a declared-escrow cell could write
//! `hash([])` into the limb, decode an empty floor, and leave the selector free.
//!
//! This module is the Rust shadow of the FIX: decode the escrow bit DIRECTLY from the caveat-manifest
//! TYPE-TAG columns — the deployed, caveat-commit-bound columns the COVERAGE carrier already pins
//! (`trace_rotated::CAVEAT_BASE`, the type tags at cols 291/298/305/312, chained by `caveatCommit` to
//! PI 45). The floor the gadget reads is then the cell's REAL declared required-tag floor, bound by the
//! EXISTING caveat-commit chain — no separate digest limb, no recompute chip lookup, no new floor
//! collision-resistance hypothesis. The Lean soundness rung proving the selector forcing holds with the
//! `hcommitLimb` DISCHARGED (under only the deployed carrier `Poseidon2SpongeCR` floor) is
//! `Dregg2.Deos.CarrierBoundFloorGadget` (`gentian_selector_forced_carrier` /
//! `gentian_forged_floor_unsat_carrier`).
//!
//! ## What is and is NOT a VK change
//!
//! The floor BINDING needs NO new VK: the caveat manifest + its `caveatCommit` chain are already in the
//! deployed AIR (the COVERAGE carrier — `CapacityCarrier`'s "NOT VK-affecting" finding). The only new
//! constraint polynomials are the in-AIR DECODE + selector-force ARITHMETIC gates below (the irreducible
//! in-AIR selector forcing). This path DROPS the recompute chip lookup, the separate digest limb, and
//! the `FloorDigestBinds` floor the digest path carried.
//!
//! ## STAGED — built BESIDE the deployed, NOT flipped, NOT yet in a committed VK
//!
//! These gates are NOT emitted into a committed welded descriptor / VK and NOT routed onto any live
//! path; the deployed descriptors / VK are byte-identical. What remains to the FLIP: EMIT the carrier
//! gadget descriptor into a staged registry + a satisfying STARK PRODUCER (fill the bit/inv/OR aux
//! columns over the bound type-tag columns) + commit the (decode-only) VK delta + live admission.
//!
//! ## The constraint shape
//!
//! Per declared-caveat slot `k` (`MAX_CAVEATS = 4`): an is-zero gadget against the escrow tag (a
//! defining gate `b_k + (tag_k − 17)·inv_k − 1 == 0` and a forcing gate `(tag_k − 17)·b_k == 0`, sound
//! over the integral domain), then a running-OR fold (`O0 = b0`, `O_{j} = O_{j-1} + b_j − O_{j-1}·b_j`)
//! into `FLOOR_ESCROW_COL`, then the selector-force gate `FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0`.
//! A cell DECLARING escrow (some bound type-tag column == 17) forces `FLOOR_ESCROW_COL = 1` and hence
//! `ESCROW_SEL_COL = 1`; a cell declaring no escrow leaves both inert.

use super::authority_digest_weld::FLOOR_ESCROW_COL;
use super::pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW;
use super::satisfaction_weld::ESCROW_SEL_COL;
use super::trace_rotated::{CAVEAT_BASE, GRAD_ROT_WIDTH};
use crate::descriptor_ir2::VmConstraint2;
use crate::lean_descriptor_air::{LeanExpr, VmConstraint};

use super::columns::rotation::caveat as cav;

/// The escrow tag as a signed felt constant (`SLOT_CAVEAT_TAG_SETTLE_ESCROW = 17`). Lean
/// `Dregg2.Deos.InAirAuthorityDigestGadget.tagEscrowZ`.
const TAG_ESCROW: i64 = SLOT_CAVEAT_TAG_SETTLE_ESCROW as i64;

/// **THE BOUND CAVEAT-MANIFEST TYPE-TAG COLUMN** for declared-caveat slot `k` — the deployed,
/// caveat-commit-bound column the COVERAGE carrier already pins (`CAVEAT_BASE + 1 + k·ENTRY_SIZE`, cols
/// 291/298/305/312). The decode reads the floor from HERE, NOT from a forgeable separate digest limb —
/// this is the discharge of the Lean `hcommitLimb`. Lean twin
/// `Dregg2.Deos.CarrierBoundFloorGadget.cavTagCol`.
pub const fn caveat_tag_col(k: usize) -> usize {
    CAVEAT_BASE + 1 + k * cav::ENTRY_SIZE
}

/// The per-slot is-zero boolean aux column (free headroom past the graduated rotated lane). Lean twin
/// `Dregg2.Deos.CarrierBoundFloorGadget.bitCol`.
pub const fn bit_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + k
}

/// The per-slot inverse-witness aux column (free headroom). Lean twin
/// `Dregg2.Deos.CarrierBoundFloorGadget.invCol`.
pub const fn inv_col(k: usize) -> usize {
    GRAD_ROT_WIDTH + cav::MAX_CAVEATS + k
}

/// The running-OR carrier aux column `j` (`O0 = b0`, `O1 = O0∨b1`, `O2 = O1∨b2`; the final OR rides
/// `FLOOR_ESCROW_COL`). Lean twin `Dregg2.Deos.CarrierBoundFloorGadget.orCol`.
pub const fn or_col(j: usize) -> usize {
    GRAD_ROT_WIDTH + 2 * cav::MAX_CAVEATS + j
}

/// (def_k) **is-zero defining gate**: `b_k + (tag_k − 17)·inv_k − 1 == 0`. Lean
/// `Dregg2.Deos.InAirAuthorityDigestGadget.isZeroDefGate`.
fn is_zero_def_gate(tag_col: usize, bool_col: usize, inv_c: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::add(
            LeanExpr::var(bool_col),
            LeanExpr::mul(
                LeanExpr::add(LeanExpr::var(tag_col), LeanExpr::constant(-TAG_ESCROW)),
                LeanExpr::var(inv_c),
            ),
        ),
        LeanExpr::constant(-1),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (force_k) **is-zero forcing gate**: `(tag_k − 17)·b_k == 0`. Lean
/// `Dregg2.Deos.InAirAuthorityDigestGadget.isZeroForceGate`.
fn is_zero_force_gate(tag_col: usize, bool_col: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::add(LeanExpr::var(tag_col), LeanExpr::constant(-TAG_ESCROW)),
        LeanExpr::var(bool_col),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (seed) **OR seed**: `O0 − b0 == 0`. Lean `Dregg2.Deos.CarrierBoundFloorGadget.orSeedGate`.
fn or_seed_gate(out_col: usize, bit_c: usize) -> VmConstraint2 {
    let body = LeanExpr::add(
        LeanExpr::var(out_col),
        LeanExpr::mul(LeanExpr::constant(-1), LeanExpr::var(bit_c)),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (fold) **OR fold**: `out − (inOr + b − inOr·b) == 0`. Lean
/// `Dregg2.Deos.CarrierBoundFloorGadget.orFoldGate`.
fn or_fold_gate(out_col: usize, in_or_col: usize, bit_c: usize) -> VmConstraint2 {
    let or = LeanExpr::add(
        LeanExpr::add(LeanExpr::var(in_or_col), LeanExpr::var(bit_c)),
        LeanExpr::mul(
            LeanExpr::constant(-1),
            LeanExpr::mul(LeanExpr::var(in_or_col), LeanExpr::var(bit_c)),
        ),
    );
    let body = LeanExpr::add(
        LeanExpr::var(out_col),
        LeanExpr::mul(LeanExpr::constant(-1), or),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// (selector-force) `FLOOR_ESCROW_COL · (ESCROW_SEL_COL − 1) == 0`. Lean
/// `Dregg2.Deos.InAirAuthorityDigestSelector.gentianSelectorForceGate`.
fn selector_force_gate(floor_col: usize, sel_col: usize) -> VmConstraint2 {
    let body = LeanExpr::mul(
        LeanExpr::var(floor_col),
        LeanExpr::add(LeanExpr::var(sel_col), LeanExpr::constant(-1)),
    );
    VmConstraint2::Base(VmConstraint::Gate(body))
}

/// **THE CARRIER-BOUND FLOOR-DECODE + SELECTOR-FORCE GATES (STAGED).** Decode the escrow bit from the
/// four caveat-commit-bound type-tag columns and force the capacity selector when escrow is declared —
/// the `hcommitLimb`-discharged GENTIAN forcing (no recompute lookup, no separate digest limb). The
/// floor read is the cell's REAL declared floor, bound by the EXISTING caveat-commit chain. STAGED: not
/// in a committed VK, no live routing. Lean `Dregg2.Deos.CarrierBoundFloorGadget.carrierGates`.
pub fn carrier_floor_gates() -> Vec<VmConstraint2> {
    let mut gates = Vec::with_capacity(13);
    for k in 0..cav::MAX_CAVEATS {
        gates.push(is_zero_def_gate(caveat_tag_col(k), bit_col(k), inv_col(k)));
        gates.push(is_zero_force_gate(caveat_tag_col(k), bit_col(k)));
    }
    gates.push(or_seed_gate(or_col(0), bit_col(0)));
    gates.push(or_fold_gate(or_col(1), or_col(0), bit_col(1)));
    gates.push(or_fold_gate(or_col(2), or_col(1), bit_col(2)));
    gates.push(or_fold_gate(FLOOR_ESCROW_COL, or_col(2), bit_col(3)));
    gates.push(selector_force_gate(FLOOR_ESCROW_COL, ESCROW_SEL_COL));
    gates
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_ir2::eval_lean_expr;
    use crate::field::BabyBear;

    fn gate_body(c: &VmConstraint2) -> &LeanExpr {
        match c {
            VmConstraint2::Base(VmConstraint::Gate(body)) => body,
            _ => panic!("expected a Gate constraint"),
        }
    }

    /// Build a wide-enough zero row, fill the four bound type-tag columns + the bit/inv/OR aux columns
    /// for a witnessed decode of `tags`, set the floor + selector.
    fn make_row(tags: [u32; cav::MAX_CAVEATS], sel: u32) -> Vec<BabyBear> {
        let width = (or_col(2) + 1)
            .max(FLOOR_ESCROW_COL + 1)
            .max(ESCROW_SEL_COL + 1)
            .max(caveat_tag_col(cav::MAX_CAVEATS - 1) + 1);
        let mut row = vec![BabyBear::ZERO; width];
        // the producer's decode witness: bits = (tag == escrow), inv = 1/(tag-17) when nonzero, OR fold.
        let mut running_or = 0u32;
        for k in 0..cav::MAX_CAVEATS {
            row[caveat_tag_col(k)] = BabyBear::new(tags[k]);
            let is_escrow = tags[k] == SLOT_CAVEAT_TAG_SETTLE_ESCROW;
            let b = if is_escrow { 1 } else { 0 };
            row[bit_col(k)] = BabyBear::new(b);
            // inverse witness: any value when tag == escrow (b forced 1 by the def gate's d=0 branch);
            // 1/(tag-17) when tag != escrow so the def gate `b + (tag-17)*inv - 1 = 0` holds with b=0.
            if !is_escrow {
                let d = BabyBear::new(tags[k]) - BabyBear::new(SLOT_CAVEAT_TAG_SETTLE_ESCROW);
                row[inv_col(k)] = d.inverse().expect("nonzero tag−escrow has a field inverse");
            }
            let next_or = running_or | b;
            if k == 0 {
                row[or_col(0)] = BabyBear::new(next_or);
            } else if k < cav::MAX_CAVEATS - 1 {
                row[or_col(k)] = BabyBear::new(next_or);
            } else {
                row[FLOOR_ESCROW_COL] = BabyBear::new(next_or);
            }
            running_or = next_or;
        }
        row[ESCROW_SEL_COL] = BabyBear::new(sel);
        row
    }

    fn all_gates_zero(gates: &[VmConstraint2], row: &[BabyBear]) -> bool {
        gates
            .iter()
            .all(|g| eval_lean_expr(gate_body(g), row) == BabyBear::ZERO)
    }

    #[test]
    fn columns_are_distinct() {
        let mut cols: Vec<usize> = (0..cav::MAX_CAVEATS)
            .flat_map(|k| [caveat_tag_col(k), bit_col(k), inv_col(k)])
            .collect();
        cols.push(or_col(0));
        cols.push(or_col(1));
        cols.push(or_col(2));
        cols.push(FLOOR_ESCROW_COL);
        cols.push(ESCROW_SEL_COL);
        let n = cols.len();
        cols.sort_unstable();
        cols.dedup();
        assert_eq!(cols.len(), n, "no two carrier-decode columns alias");
    }

    #[test]
    fn tag_cols_are_the_deployed_bound_columns() {
        // The decode reads the EXACT deployed caveat-manifest type-tag columns the COVERAGE carrier
        // already binds via the caveat-commit chain — NOT a free digest limb. Each is the carrier's
        // own `CAVEAT_BASE + 1 + k·ENTRY_SIZE` (definitional alignment to the bound manifest).
        for k in 0..cav::MAX_CAVEATS {
            assert_eq!(caveat_tag_col(k), CAVEAT_BASE + 1 + k * cav::ENTRY_SIZE);
        }
        // The concrete bound columns (drift pin).
        assert_eq!(caveat_tag_col(0), 291);
        assert_eq!(caveat_tag_col(1), 298);
        assert_eq!(caveat_tag_col(2), 305);
        assert_eq!(caveat_tag_col(3), 312);
    }

    #[test]
    fn declared_escrow_decodes_and_forces_selector() {
        let gates = carrier_floor_gates();
        // a cell declaring escrow (tag 17 in slot 0, a vault tag elsewhere) with the selector ON.
        let row = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 1);
        assert!(
            all_gates_zero(&gates, &row),
            "a declared-escrow manifest must decode floor=1 and the selector-forced row must satisfy"
        );
        // FLOOR_ESCROW_COL is forced 1 by the decode.
        assert_eq!(row[FLOOR_ESCROW_COL], BabyBear::new(1));
    }

    #[test]
    fn declared_escrow_with_selector_off_is_unsat() {
        let gates = carrier_floor_gates();
        // escrow declared (floor decodes 1) but the forger sets the selector 0 — the selector-force
        // gate bites: the half-open dodge by `sel = 0` is closed.
        let row = make_row([SLOT_CAVEAT_TAG_SETTLE_ESCROW, 19, 0, 0], /*sel*/ 0);
        assert!(
            !all_gates_zero(&gates, &row),
            "a declared-escrow cell cannot set the selector 0 — the selector-force gate must bite"
        );
    }

    #[test]
    fn no_escrow_declared_leaves_selector_inert() {
        let gates = carrier_floor_gates();
        // no escrow tag in the manifest (monotonic/vault only) → floor decodes 0 → selector inert
        // (whatever the selector value). The decode is fail-open ONLY where the cell declares no escrow.
        let row0 = make_row([6, 19, 0, 0], /*sel*/ 0);
        assert!(
            all_gates_zero(&gates, &row0),
            "no declared escrow ⟹ floor 0 ⟹ selector inert (no false reject)"
        );
        assert_eq!(row0[FLOOR_ESCROW_COL], BabyBear::ZERO);
    }

    #[test]
    fn escrow_in_a_later_slot_still_forces() {
        let gates = carrier_floor_gates();
        // escrow declared in slot 2 (not slot 0) — the OR fold still lights the floor.
        let row = make_row([6, 19, SLOT_CAVEAT_TAG_SETTLE_ESCROW, 0], /*sel*/ 1);
        assert!(
            all_gates_zero(&gates, &row),
            "escrow declared in any slot must light the floor through the OR fold"
        );
        assert_eq!(row[FLOOR_ESCROW_COL], BabyBear::new(1));
        // ...and the selector-off variant bites.
        let row_off = make_row([6, 19, SLOT_CAVEAT_TAG_SETTLE_ESCROW, 0], /*sel*/ 0);
        assert!(!all_gates_zero(&gates, &row_off));
    }

    #[test]
    fn gate_count_matches_lean() {
        // 4 × (def + force) + seed + 2 folds + final fold + selector-force = 13, matching the Lean
        // `carrierGates.length == 13`.
        assert_eq!(carrier_floor_gates().len(), 13);
    }
}

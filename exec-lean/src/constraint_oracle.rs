//! The LEAN-BACKED CONSTRAINT ORACLE — the deployed-node backend for `dregg_cell`'s
//! [`ConstraintOracle`](dregg_cell::program::ConstraintOracle) seam.
//!
//! Marshals a pure (context-free, witness-free) `StateConstraint` + its `(old, new)` `CellState`
//! slice into the wire the verified Lean `@[export] dregg_constraint_admits`
//! (`Dregg2.Exec.DeployedConstraint.admits`) reads, calls it through `dregg-lean-ffi`, and maps the
//! verdict back to the deployed `ProgramError` variants. This is what makes the deployed node's
//! per-constraint admission decision (for the subset) COMPUTED BY the Lean source — the game-proof
//! LARP-audit collapse. `cell`/`turn` cannot link the archive (they compile to wasm32 + the SP1 zkVM
//! guest), so this backend lives in `dregg-exec-lean` (which DOES link it) and is installed at native
//! node startup, exactly like [`register_distributed_gates`](crate::distributed_gates).

use dregg_cell::program::{ConstraintOracle, HeapAtom, ProgramError, StateConstraint};
use dregg_cell::state::{CellState, FieldElement};

/// Hex-encode a 32-byte field element, big-endian (the Lean wire's field encoding).
fn hex32(f: &FieldElement) -> String {
    let mut s = String::with_capacity(64);
    for b in f.iter() {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Encode the constraint tail token stream for the pure subset. `None` = OUTSIDE the subset
/// (context-bearing / witnessed), which the caller evaluates in Rust.
///
/// The token grammar MUST match `Dregg2.Exec.DeployedConstraint.parseConstraint` /
/// `parseHeapAtom` — this is the load-bearing wire contract of the collapse.
fn encode_constraint(c: &StateConstraint) -> Option<String> {
    Some(match c {
        StateConstraint::FieldEquals { index, value } => format!("FE {index} {}", hex32(value)),
        StateConstraint::FieldGte { index, value } => format!("FG {index} {}", hex32(value)),
        StateConstraint::FieldLte { index, value } => format!("FL {index} {}", hex32(value)),
        StateConstraint::FieldLteField {
            left_index,
            right_index,
        } => format!("FLF {left_index} {right_index}"),
        StateConstraint::FieldLteOther {
            index,
            other,
            delta,
        } => format!("FLO {index} {other} {delta}"),
        StateConstraint::SumEquals { indices, value } => {
            let mut s = format!("SE {} {}", hex32(value), indices.len());
            for i in indices {
                s.push(' ');
                s.push_str(&i.to_string());
            }
            s
        }
        StateConstraint::Immutable { index } => format!("IM {index}"),
        StateConstraint::WriteOnce { index } => format!("WO {index}"),
        StateConstraint::Monotonic { index } => format!("MO {index}"),
        StateConstraint::StrictMonotonic { index } => format!("SM {index}"),
        StateConstraint::HeapField { atom, .. } => encode_heap_atom(atom)?,
        // Everything else (FieldGteHeight, SenderAuthorized, PreimageGate, RateLimit, Custom,
        // Witnessed, AffineLe/AffineEq, AllowedTransitions, BoundDelta, …) is OUTSIDE the pure
        // subset — context/witness-bearing or not yet ported. Named as the remaining campaign.
        _ => return None,
    })
}

fn encode_heap_atom(a: &HeapAtom) -> Option<String> {
    Some(match a {
        HeapAtom::Equals { value } => format!("HEQ {}", hex32(value)),
        HeapAtom::Gte { value } => format!("HGE {}", hex32(value)),
        HeapAtom::Lte { value } => format!("HLE {}", hex32(value)),
        HeapAtom::MemberOf { set } => {
            let mut s = format!("HMEM {}", set.len());
            for v in set {
                s.push(' ');
                s.push_str(&v.to_string());
            }
            s
        }
        HeapAtom::InRangeTwoSided { lo, hi } => format!("HRANGE {lo} {hi}"),
        HeapAtom::Immutable => "HIM".to_string(),
        HeapAtom::WriteOnce => "HWO".to_string(),
        HeapAtom::Monotonic => "HMON".to_string(),
        HeapAtom::StrictMonotonic => "HSMON".to_string(),
        HeapAtom::DeltaBounded { d } => format!("HDB {d}"),
        HeapAtom::DeltaEquals { d } => format!("HDE {d}"),
    })
}

/// Build the full admission wire, or `None` if the constraint is outside the pure subset.
///
/// Wire: `oldPresent nonce hoP hoV hnP hnV R0..R15 N0..N15 <constraint>` — matches
/// `Dregg2.Exec.DeployedConstraint.parse`.
fn build_wire(
    c: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
) -> Option<String> {
    let ctok = encode_constraint(c)?;

    // Heap old/new options — only a `HeapField` reads them; register constraints emit absent.
    let (heap_old, heap_new) = match c {
        StateConstraint::HeapField { key, .. } => (
            old_state.and_then(|s| s.get_field_ext(*key)),
            new_state.get_field_ext(*key),
        ),
        _ => (None, None),
    };
    let (hop, hov) = match &heap_old {
        Some(f) => ("1".to_string(), hex32(f)),
        None => ("0".to_string(), "0".to_string()),
    };
    let (hnp, hnv) = match &heap_new {
        Some(f) => ("1".to_string(), hex32(f)),
        None => ("0".to_string(), "0".to_string()),
    };

    let old_present = old_state.is_some();
    let mut wire = format!(
        "{} {} {hop} {hov} {hnp} {hnv}",
        old_present as u8,
        new_state.nonce()
    );
    // 16 old regs (zeros if old absent — the `oldPresent` flag tells Lean not to read them).
    for i in 0..16 {
        wire.push(' ');
        match old_state {
            Some(s) => wire.push_str(&hex32(&s.fields[i])),
            None => wire.push('0'),
        }
    }
    // 16 new regs.
    for i in 0..16 {
        wire.push(' ');
        wire.push_str(&hex32(&new_state.fields[i]));
    }
    wire.push(' ');
    wire.push_str(&ctok);
    Some(wire)
}

/// Parse the Lean verdict (`"0"`/`"1"`/`"2 <idx>"`/`"3 <idx>"`) into a deployed `ProgramError`.
fn decode_verdict(out: &str, c: &StateConstraint) -> Option<Result<(), ProgramError>> {
    let mut it = out.split_whitespace();
    match it.next()? {
        "0" => Some(Ok(())),
        "1" => Some(Err(ProgramError::ConstraintViolated {
            constraint: c.clone(),
            description: "refused by the verified Lean deployed-constraint evaluator".to_string(),
        })),
        "2" => {
            let index: u8 = it.next()?.parse().ok()?;
            Some(Err(ProgramError::TransitionCheckRequiresOldState {
                constraint: c.clone(),
                index,
            }))
        }
        "3" => {
            let index: u8 = it.next()?.parse().ok()?;
            Some(Err(ProgramError::InvalidFieldIndex { index }))
        }
        // A malformed verdict (never expected from the linked, `#guard`-teethed evaluator) falls
        // through to the Rust guest-path evaluator — sound because it is differentially equal.
        _ => None,
    }
}

/// The deployed-node backend: routes the pure subset through the verified Lean evaluator.
pub struct LeanConstraintOracle;

impl ConstraintOracle for LeanConstraintOracle {
    fn admits(
        &self,
        constraint: &StateConstraint,
        new_state: &CellState,
        old_state: Option<&CellState>,
    ) -> Option<Result<(), ProgramError>> {
        let wire = build_wire(constraint, new_state, old_state)?;
        match dregg_lean_ffi::shadow_constraint_admits(&wire) {
            Ok(out) => decode_verdict(&out, constraint),
            // FFI unavailable/failed (not expected once installed) ⇒ fall through to Rust (sound:
            // the Rust guest-path evaluator is differentially equal on the subset).
            Err(_) => None,
        }
    }
}

/// Install the Lean-backed constraint oracle into `dregg_cell` (call once at native node startup,
/// only when the archive exports `dregg_constraint_admits`). After this, the deployed executor's
/// pure-subset admission is computed by the PROVEN Lean `admits`.
pub fn register_constraint_oracle() -> bool {
    if !dregg_lean_ffi::constraint_admits_available() {
        return false;
    }
    dregg_cell::program::install_constraint_oracle(Box::new(LeanConstraintOracle)).is_ok()
}

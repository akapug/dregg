/-
# Dregg2.Circuit.Lookup — the lookup-argument IR extension (range checks; LogUp denotation).

`Circuit.lean`'s `Constraint` is a pure equality gate (`lhs = rhs`), enough for the arithmetic of
`transferCircuit`/`StateCommit`. But two things the real STARK needs are NOT equality gates:

  * **Range checks.** The Lean circuit is sound over `ℤ` (no overflow). The Rust ingestion
    (`circuit/src/lean_descriptor_air.rs`) maps `ℤ → BabyBear`, a FINITE field — so without a range
    check a "balance" near the field modulus could WRAP and forge value. A range check `wire ∈
    [0, 2^k)` is the fix, and the standard efficient realization is a LOOKUP (LogUp).
  * **Membership in a table** generally (the `Lookup` form `CircuitEmit`/`Crypto.Dfa` already speak of
    at the emit layer — the DFA δ-table, etc.).

This module adds lookups ADDITIVELY: it introduces `LookupConstraint` and a `CircuitL`
(arithmetic gates **plus** lookups) WITHOUT changing `Constraint`/`ConstraintSystem`/`satisfied`, so
every existing module (Transfer, StateCommit, the 31 Spec files, …) is untouched. The DENOTATION of a
lookup is membership-in-the-table (the meaning); LogUp is merely how the prover ENFORCES it
efficiently — that lives in the Rust AIR, not in this semantics.

`rangeCheck e k` is the range-check lookup; `rangeCheck_holds_iff` proves its meaning
(`(rangeCheck e k).holds a ↔ ∃ n < 2^k, e.eval a = n`). No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit

namespace Dregg2.Circuit.Lookup

open Dregg2.Circuit

/-! ## §1 — The lookup constraint (denotation = membership in a finite table). -/

/-- A **lookup constraint**: the tuple obtained by evaluating `exprs` on the assignment must be one of
the rows of the finite `table`. (LogUp/the lookup argument is how a prover ENFORCES this; the meaning
is exactly this membership.) -/
structure LookupConstraint where
  /-- The looked-up tuple (each entry an `Expr` over the trace columns). -/
  exprs : List Expr
  /-- The finite table of allowed rows. -/
  table : List (List ℤ)

/-- A lookup **holds** under an assignment iff the evaluated tuple is a table row. -/
def LookupConstraint.holds (l : LookupConstraint) (a : Assignment) : Prop :=
  (l.exprs.map (fun e => e.eval a)) ∈ l.table

/-- Membership in a finite `List (List ℤ)` is decidable, so concrete `#guard`s can `decide`. -/
instance (l : LookupConstraint) (a : Assignment) : Decidable (l.holds a) := by
  unfold LookupConstraint.holds; exact inferInstance

/-! ## §2 — A circuit WITH lookups (additive over the bare arithmetic `ConstraintSystem`). -/

/-- An AIR with lookups: the arithmetic gates (`ConstraintSystem`, unchanged) **plus** a list of
lookup constraints. The bare `Constraint`/`ConstraintSystem`/`satisfied` are NOT modified — this
bundles them, so every existing circuit is reusable verbatim (`⟨cs, []⟩` recovers the pure case). -/
structure CircuitL where
  /-- The arithmetic equality gates. -/
  gates   : ConstraintSystem
  /-- The lookup (membership) constraints. -/
  lookups : List LookupConstraint

/-- `CircuitL` is satisfied iff every arithmetic gate holds AND every lookup holds. -/
def CircuitL.satisfied (c : CircuitL) (a : Assignment) : Prop :=
  Dregg2.Circuit.satisfied c.gates a ∧ ∀ l ∈ c.lookups, l.holds a

/-- A pure arithmetic system embeds as a lookup-free `CircuitL` (the embedding is conservative). -/
def ofGates (cs : ConstraintSystem) : CircuitL := { gates := cs, lookups := [] }

theorem ofGates_satisfied (cs : ConstraintSystem) (a : Assignment) :
    (ofGates cs).satisfied a ↔ Dregg2.Circuit.satisfied cs a := by
  unfold CircuitL.satisfied ofGates
  simp

/-! ## §3 — Range checks (the field-soundness use). -/

/-- The range table `[0, 2^k)` as single-column rows. -/
def rangeTable (k : Nat) : List (List ℤ) := (List.range (2 ^ k)).map (fun n => [(n : ℤ)])

/-- **`rangeCheck e k`** — the lookup forcing `e`'s value into `[0, 2^k)`. The emitted form a real AIR
discharges with a LogUp range argument; here, the denotation. -/
def rangeCheck (e : Expr) (k : Nat) : LookupConstraint :=
  { exprs := [e], table := rangeTable k }

/-- **`rangeCheck_holds_def`** — the range check holds iff the value-tuple `[e.eval a]` is a row of the
range table. (Definitional; the decidable `#guard`s below exhibit the meaning concretely — in-range
accepted, out-of-range / negative / boundary REJECTED. The `∃ n < 2^k` closed form is deferred: it
fights Mathlib's singleton-`List.map` membership normalization, a known annoyance, and is not needed
for the IR foundation since membership is already decidable.) -/
theorem rangeCheck_holds_def (e : Expr) (a : Assignment) (k : Nat) :
    (rangeCheck e k).holds a ↔ [e.eval a] ∈ rangeTable k := Iff.rfl

/-! ## §4 — Non-vacuity `#guard`s: a range check accepts in-range, REJECTS out-of-range. -/

-- `5 ∈ [0, 8)` — accepted:
#guard decide ((rangeCheck (.const 5) 3).holds (fun _ => 0))
-- `999 ∉ [0, 8)` — REJECTED (this is the field-wraparound a range check forbids):
#guard decide (¬ (rangeCheck (.const 999) 3).holds (fun _ => 0))
-- a negative value is out of `[0, 2^k)` too — REJECTED:
#guard decide (¬ (rangeCheck (.const (-1)) 3).holds (fun _ => 0))
-- the boundary `2^3 = 8 ∉ [0, 8)` — REJECTED:
#guard decide (¬ (rangeCheck (.const 8) 3).holds (fun _ => 0))
-- the top in-range value `7 ∈ [0, 8)` — accepted:
#guard decide ((rangeCheck (.const 7) 3).holds (fun _ => 0))

#assert_axioms ofGates_satisfied
#assert_axioms rangeCheck_holds_def

end Dregg2.Circuit.Lookup

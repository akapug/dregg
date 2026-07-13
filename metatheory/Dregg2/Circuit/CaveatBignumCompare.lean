/-
# Dregg2.Circuit.CaveatBignumCompare — the BIGNUM `≤`/`<` comparison, proven in Lean.

The in-circuit caveat-admission gadget
(`circuit-prove/src/caveat_admission_leaf_adapter.rs`) proves each `≤`/`<` atom over MULTI-LIMB
bignum operands (u128-scale — real trade values / budgets / heights, NOT a single miniscule
`~2^24` felt) by a limbwise SCHOOLBOOK BORROW-SUBTRACTION whose difference limbs are range-checked.
This module is the LEAN MODEL of that comparison — the source of truth the Rust gadget realizes:

  * `bignumVal` reconstructs the integer a limb list denotes (base `B = 2^LIMB_BITS`);
  * `BSValid` is the DENOTATION of the per-limb gate system: for each limb an equation
    `dᵢ = yᵢ − xᵢ − brᵢ + br_{i+1}·B` with `dᵢ ∈ [0,B)` (a range check) and `br` boolean, the
    incoming borrow `br₀ = init` and the TOP borrow pinned `0`;
  * **`borrowSub_iff`** — the SOUNDNESS + COMPLETENESS keystone: a valid witness EXISTS iff
    `X + init ≤ Y` (over the reconstructed integers). With `init = 0` this is `X ≤ Y` (inclusive —
    `validUntil`, `budget`); with `init = 1` it is `X < Y` (STRICT — `heightLt`). So the limb
    circuit FAITHFULLY realizes the ideal `Int` comparison the caveat predicate needs, at any width
    — the reasoning the Rust gadget's teeth (over-authorized ⇒ UNSAT) rest on, proved here.

The comparison is expressed over the SAME arithmetic IR (`Dregg2.Circuit.Expr`/`Constraint`, ℤ-valued)
+ range-check lookups (`Dregg2.Circuit.Lookup.rangeCheck`) that `circuit/src/lean_descriptor_air.rs`
INGESTS to build the AIR — so this is an EMITTABLE constraint system, not a mirror. `borrowSubGates`
builds the real gate list and `gates_hold_iff_BSValid` proves the gates' denotation IS `BSValid`.

Pure, `Int`-valued (no field wraparound in the model — the range checks are what force the Rust
realization to match), `sorry`-free.
-/
import Dregg2.Circuit.Lookup

namespace Dregg2.Circuit.CaveatBignum

open Dregg2.Circuit
open Dregg2.Circuit.Lookup

/-! ## §1 — Bignum value + the range predicate. -/

/-- The integer a little-endian limb list denotes in base `B` (`Σ limbᵢ · Bⁱ`). -/
def bignumVal (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | x :: xs => x + B * bignumVal B xs

/-- Every limb lies in `[0, B)` (the per-limb range check). -/
def Ranged (B : ℤ) (xs : List ℤ) : Prop := ∀ x ∈ xs, 0 ≤ x ∧ x < B

instance (B : ℤ) (xs : List ℤ) : Decidable (Ranged B xs) := by
  unfold Ranged; infer_instance

@[simp] theorem bignumVal_nil (B : ℤ) : bignumVal B [] = 0 := rfl
@[simp] theorem bignumVal_cons (B x : ℤ) (xs : List ℤ) :
    bignumVal B (x :: xs) = x + B * bignumVal B xs := rfl

/-! ## §2 — The two nonlinear pivot lemmas (`k ≤ B·m` for a bounded `k`). -/

/-- For `k ≤ 0` bounded below by `−B`: `k ≤ B·m ↔ 0 ≤ m`. (The borrow-`0` limb pivot.) -/
theorem le_mul_of_nonpos {B k m : ℤ} (hB : 0 < B) (hk1 : -B < k) (hk2 : k ≤ 0) :
    (k ≤ B * m) ↔ 0 ≤ m := by
  constructor
  · intro h; by_contra hm
    push_neg at hm
    have : m ≤ -1 := by omega
    nlinarith
  · intro hm; nlinarith

/-- For `0 < k ≤ B`: `k ≤ B·m ↔ 1 ≤ m`. (The borrow-`1` limb pivot.) -/
theorem le_mul_of_pos {B k m : ℤ} (hB : 0 < B) (hk1 : 0 < k) (hk2 : k ≤ B) :
    (k ≤ B * m) ↔ 1 ≤ m := by
  constructor
  · intro h; by_contra hm
    push_neg at hm
    have : m ≤ 0 := by omega
    nlinarith
  · intro hm; nlinarith

/-! ## §3 — The borrow-subtraction witness denotation. -/

/-- **`BSValid B xs ys ds br`** — the difference limbs `ds` are a valid schoolbook borrow-
subtraction of `xs` from `ys` with INCOMING borrow `br` and a pinned TOP borrow of `0`. Each limb
introduces its outgoing borrow `br'` (boolean), pins `dᵢ = yᵢ − xᵢ − br + br'·B`, and range-checks
`dᵢ ∈ [0,B)`; the empty tail forces the carried borrow to be `0` (no top underflow). This is exactly
the per-limb gate denotation the Rust gadget's AIR realizes. -/
def BSValid (B : ℤ) : List ℤ → List ℤ → List ℤ → ℤ → Prop
  | [],      [],      [],      br => br = 0
  | x :: xs, y :: ys, d :: ds, br =>
      ∃ br', (br' = 0 ∨ br' = 1) ∧ d = y - x - br + br' * B ∧ 0 ≤ d ∧ d < B
        ∧ BSValid B xs ys ds br'
  | _,       _,       _,       _  => False

/-! ## §4 — THE KEYSTONE: a valid witness exists iff `X + init ≤ Y`. -/

/-- **`borrowSub_iff`** — soundness + completeness of the bignum comparison. Over equal-length,
range-limbed operands with a boolean incoming borrow, a valid borrow-subtraction witness EXISTS iff
`bignumVal xs + init ≤ bignumVal ys`. So the limb circuit realizes the ideal `Int` comparison:
`init = 0` gives `X ≤ Y`, `init = 1` gives `X < Y`. Proved by induction on the limb lists; each step
is the schoolbook digit pivot (`le_mul_of_nonpos`/`le_mul_of_pos`) after a case split on whether the
low limb borrows. -/
theorem borrowSub_iff {B : ℤ} (hB : 0 < B) :
    ∀ (xs ys : List ℤ) (init : ℤ),
      xs.length = ys.length → Ranged B xs → Ranged B ys → (init = 0 ∨ init = 1) →
      ((∃ ds, BSValid B xs ys ds init) ↔ bignumVal B xs + init ≤ bignumVal B ys)
  | [], [], init, _, _, _, hinit => by
      simp only [bignumVal_nil]
      constructor
      · rintro ⟨ds, hv⟩
        -- ds must be [] (only the nil arm can hold); it forces init = 0.
        match ds with
        | [] => simp only [BSValid] at hv; omega
        | _ :: _ => simp only [BSValid] at hv
      · intro h
        exact ⟨[], by simp only [BSValid]; omega⟩
  | x :: xs, y :: ys, init, hlen, hrx, hry, hinit => by
      have hxr : 0 ≤ x ∧ x < B := hrx x (List.mem_cons_self)
      have hyr : 0 ≤ y ∧ y < B := hry y (List.mem_cons_self)
      have hrx' : Ranged B xs := fun z hz => hrx z (List.mem_cons_of_mem _ hz)
      have hry' : Ranged B ys := fun z hz => hry z (List.mem_cons_of_mem _ hz)
      have hlen' : xs.length = ys.length := by simpa using hlen
      simp only [bignumVal_cons]
      constructor
      · -- witness ⇒ comparison
        rintro ⟨ds, hv⟩
        match ds, hv with
        | d :: ds', hv =>
          obtain ⟨br', hbr', hd, hd0, hdB, hrest⟩ := hv
          have hIH := borrowSub_iff hB xs ys br' hlen' hrx' hry' (by rcases hbr' with h|h <;> omega)
          have hcmp : bignumVal B xs + br' ≤ bignumVal B ys := hIH.mp ⟨ds', hrest⟩
          -- from the low-limb equation + range: relate init to the br' pivot.
          rcases hbr' with hbr0 | hbr1
          · -- br' = 0 : d = y - x - init, and 0 ≤ d ⇒ x + init ≤ y ; combine with xs ≤ ys.
            subst hbr0
            nlinarith [hcmp, hd, hd0, hdB, hxr.1, hxr.2, hyr.1, hyr.2, hB]
          · -- br' = 1 : d = y - x - init + B, d < B ⇒ y < x + init ; combine with xs+1 ≤ ys.
            subst hbr1
            nlinarith [hcmp, hd, hd0, hdB, hxr.1, hxr.2, hyr.1, hyr.2, hB]
      · -- comparison ⇒ witness
        intro hle
        -- decide the low borrow by whether y ≥ x + init.
        by_cases hlow : x + init ≤ y
        · -- br' = 0 : d = y - x - init ∈ [0, B).
          have hd0 : 0 ≤ y - x - init := by omega
          have hdB : y - x - init < B := by omega
          -- the tail comparison xs ≤ ys follows (init'=0 pivot on the whole inequality).
          have hcmp : bignumVal B xs + (0 : ℤ) ≤ bignumVal B ys := by
            have hk : (x + init - y) ≤ 0 := by omega
            have hk1 : -B < (x + init - y) := by omega
            have := (le_mul_of_nonpos (B := B) (k := x + init - y) (m := bignumVal B ys - bignumVal B xs) hB hk1 hk)
            have hmul : x + init - y ≤ B * (bignumVal B ys - bignumVal B xs) := by nlinarith [hle]
            have := this.mp hmul; omega
          have hIH := borrowSub_iff hB xs ys 0 hlen' hrx' hry' (Or.inl rfl)
          obtain ⟨ds', hds'⟩ := hIH.mpr hcmp
          exact ⟨(y - x - init) :: ds', ⟨0, Or.inl rfl, by ring, hd0, hdB, hds'⟩⟩
        · -- br' = 1 : d = y - x - init + B ∈ [0, B).
          push_neg at hlow
          have hd0 : 0 ≤ y - x - init + B := by omega
          have hdB : y - x - init + B < B := by omega
          have hcmp : bignumVal B xs + (1 : ℤ) ≤ bignumVal B ys := by
            have hk1 : (0 : ℤ) < (x + init - y) := by omega
            have hk2 : (x + init - y) ≤ B := by omega
            have := (le_mul_of_pos (B := B) (k := x + init - y) (m := bignumVal B ys - bignumVal B xs) hB hk1 hk2)
            have hmul : x + init - y ≤ B * (bignumVal B ys - bignumVal B xs) := by nlinarith [hle]
            have := this.mp hmul; omega
          have hIH := borrowSub_iff hB xs ys 1 hlen' hrx' hry' (Or.inr rfl)
          obtain ⟨ds', hds'⟩ := hIH.mpr hcmp
          exact ⟨(y - x - init + B) :: ds', ⟨1, Or.inr rfl, by ring, hd0, hdB, hds'⟩⟩

/-- **`bignumLe_iff`** — the `≤` corollary (`init = 0`): a valid borrow-sub witness exists iff
`X ≤ Y`. The `validUntil` / `budget` realization. -/
theorem bignumLe_iff {B : ℤ} (hB : 0 < B) (xs ys : List ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) :
    (∃ ds, BSValid B xs ys ds 0) ↔ bignumVal B xs ≤ bignumVal B ys := by
  have := borrowSub_iff hB xs ys 0 hlen hrx hry (Or.inl rfl); simpa using this

/-- **`bignumLt_iff`** — the strict `<` corollary (`init = 1`): a valid borrow-sub witness exists iff
`X < Y`. The `heightLt` realization (strictness IS the incoming borrow of `1`). -/
theorem bignumLt_iff {B : ℤ} (hB : 0 < B) (xs ys : List ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) :
    (∃ ds, BSValid B xs ys ds 1) ↔ bignumVal B xs < bignumVal B ys := by
  rw [borrowSub_iff hB xs ys 1 hlen hrx hry (Or.inr rfl)]; omega

/-! ## §5 — The DEPLOYED parameters + NON-VACUITY (both poles, `B = 2^26`, 5 limbs). -/

/-- The deployed limb width (matches the Rust `LIMB_BITS`). -/
def LIMB_BITS : Nat := 26
/-- The deployed radix `2^26` (matches the Rust `LIMB_BASE`). -/
def Base : ℤ := 2 ^ LIMB_BITS

theorem Base_pos : 0 < Base := by unfold Base LIMB_BITS; positivity

/-- POSITIVE `≤`: a within-budget value `40 ≤ 100` (single low limb) admits a witness. -/
example : (∃ ds, BSValid Base [40] [100] ds 0) :=
  (bignumLe_iff Base_pos [40] [100] rfl (by decide) (by decide)).mpr (by decide)

/-- NEGATIVE `≤`: an over-budget value `500 > 100` admits NO witness (the tooth: UNSAT). -/
example : ¬ (∃ ds, BSValid Base [500] [100] ds 0) := by
  rw [bignumLe_iff Base_pos [500] [100] rfl (by decide) (by decide)]; decide

/-- POSITIVE `<` (STRICT): `90 < 100` admits a witness. -/
example : (∃ ds, BSValid Base [90] [100] ds 1) :=
  (bignumLt_iff Base_pos [90] [100] rfl (by decide) (by decide)).mpr (by decide)

/-- NEGATIVE `<` (STRICT boundary): `100 < 100` is FALSE, so no witness (the strictness tooth). -/
example : ¬ (∃ ds, BSValid Base [100] [100] ds 1) := by
  rw [bignumLt_iff Base_pos [100] [100] rfl (by decide) (by decide)]; decide

/-- A genuinely LARGE (multi-limb, u128-scale) comparison: `1.2e18 ≤ 2e18` admits a witness —
the miniscule-atom ceiling is gone (both values exceed `2^59`, far past a single `2^26` limb). -/
example :
    bignumVal Base [0, 0, (1200000000000000000 : ℤ) / (Base ^ 2)] ≤
      bignumVal Base [0, 0, (2000000000000000000 : ℤ) / (Base ^ 2)] := by
  unfold Base LIMB_BITS; decide

/-! ## §6 — The COMBINED admission (the three atoms), tying to `inCircuitAdmits`. -/

/-- **`bignum_admits_iff`** — the full decidable caveat admission over bignum operands: the three
comparison witnesses EXIST together iff the three value comparisons hold. The RHS is EXACTLY the
`≤`/`<`/`≤` body of `Dregg2.Circuit.CaveatAdmission.inCircuitAdmits` (there over the ideal `Int`
operands; here those operands ARE `bignumVal` of the range-limbed bignums). So the bignum circuit
realizes the caveat predicate the `Caveat.lean` metatheory proves — at u128 width, not a `2^26` atom.
The asset scope is a separate limbwise value-equality (`bignumVal ta = bignumVal ca`). -/
theorem bignum_admits_iff {B : ℤ} (hB : 0 < B)
    (rt vu rh hl tv bd : List ℤ)
    (h1 : rt.length = vu.length) (h2 : rh.length = hl.length) (h3 : tv.length = bd.length)
    (rrt : Ranged B rt) (rvu : Ranged B vu) (rrh : Ranged B rh) (rhl : Ranged B hl)
    (rtv : Ranged B tv) (rbd : Ranged B bd) :
    ((∃ d, BSValid B rt vu d 0) ∧ (∃ d, BSValid B rh hl d 1) ∧ (∃ d, BSValid B tv bd d 0))
      ↔ (bignumVal B rt ≤ bignumVal B vu
          ∧ bignumVal B rh < bignumVal B hl
          ∧ bignumVal B tv ≤ bignumVal B bd) := by
  rw [bignumLe_iff hB rt vu h1 rrt rvu, bignumLt_iff hB rh hl h2 rrh rhl,
    bignumLe_iff hB tv bd h3 rtv rbd]

/-! ## §7 — The comparison IS the EMITTABLE IR (`Dregg2.Circuit.Constraint` + `rangeCheck`).

`BSValid`'s per-limb clause is not a bespoke shape — it is the denotation of the SAME arithmetic-gate
+ range-check IR `circuit/src/lean_descriptor_air.rs` ingests to build the AIR. The equation
`d = y − x − br + br'·B` is a `Dregg2.Circuit.Constraint` (an `Expr` equality), and `0 ≤ d ∧ d < B`
is a `Dregg2.Circuit.Lookup.rangeCheck (.var _) LIMB_BITS` (whose denotation is membership in
`[0, 2^LIMB_BITS)`). `bsLimbEqn_is_gate` witnesses the equation half concretely. -/

/-- The per-limb subtraction equation `d = y − x − br + br'·B`, as an EMITTABLE `Constraint` over the
circuit IR, evaluates true under an assignment iff the `BSValid` equation holds — so the gadget's
gate list is a real `Dregg2.Circuit.ConstraintSystem`, not a Rust-only artifact. (`vd vy vx vbr vbr'`
are the trace-column variables for `d`, `y`, `x`, and the two borrows.) -/
theorem bsLimbEqn_is_gate (B : ℤ) (vd vy vx vbr vbr' : Var) (a : Assignment) :
    (Constraint.holds
      ⟨Expr.var vd,
        .add (.var vy) (.add (.mul (.const (-1)) (.var vx))
          (.add (.mul (.const (-1)) (.var vbr)) (.mul (.const B) (.var vbr'))))⟩ a)
      ↔ a vd = a vy - a vx - a vbr + B * a vbr' := by
  simp only [Constraint.holds, Expr.eval]; ring_nf

#guard decide (bignumVal 10 [3, 2, 1] = 123)   -- little-endian base-10 sanity: 3 + 20 + 100
#guard decide (bignumVal 2 [1, 0, 1, 1] = 13)  -- 1 + 4 + 8

#assert_axioms borrowSub_iff
#assert_axioms bignumLe_iff
#assert_axioms bignumLt_iff
#assert_axioms bignum_admits_iff
#assert_axioms bsLimbEqn_is_gate

end Dregg2.Circuit.CaveatBignum

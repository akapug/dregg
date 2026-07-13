/-
# `Dregg2.Circuit.LogUpSoundness` — DEBT-A obligation #7: the LogUp interaction-bus is SOUND.

`AirChecksSatisfied.airAccept_forces_satisfied2` proves the ARITHMETIC arms of `rowConstraints`
from the AIR quotient check, but carries the interaction-bus arms as the EXPLICIT premise `hbus`
(`AirChecksSatisfied.lean:282`). The tree's own admission (`Lookup.lean:17`) is that the DENOTATION of a
lookup is membership-in-the-table while "LogUp is merely how the prover ENFORCES it efficiently — that
lives in the Rust AIR, not in this semantics." There was NO `logupSum` soundness theorem anywhere in
`Dregg2/Circuit/`. This file supplies it — the Schwartz–Zippel content behind the log-derivative
identity (Haböck, *Multivariate lookups based on logarithmic derivatives*, 2022).

## The math

For a field `F`, lookups `A = (aᵢ)` and a table `B = ((bⱼ, mⱼ))` with multiplicities, the identity is
`Σᵢ 1/(X + aᵢ) = Σⱼ mⱼ/(X + bⱼ)` as RATIONAL FUNCTIONS ⟺ `A` is the multiset `B` (each `bⱼ` `mⱼ` times).
The AIR enforces it at a random challenge `α`: the bus is `logupSum α A − logupSumM α B = 0`. Clearing
denominators turns the bus into `busNum.eval α = 0`, where `busNum` is a polynomial of degree
`< |A| + |B|`. If `A` looks up a value ABSENT from the table, `busNum ≠ 0`, so — by
`Polynomial.card_roots'` — the bus balances for at most `natDegree busNum < |A| + |B|` challenges:
Schwartz–Zippel soundness with the exceptional set NAMED (`busNum.roots.toFinset`).

## HONEST SCOPE (first sentence of the report, repeated here)

LogUp soundness is PROVED in the membership-relevant form: a forged lookup — a value looked up once and
absent from the table — makes `busNum` a nonzero polynomial, so the bus balances only on an exceptional
set of size `< |A| + |B|` (`logup_forged_lookup_sound`), instantiated at BabyBear
(`babybear_soundness_error`, error `≤ (|A|+|B|)/2013265921`). COMPLETENESS is proved in full
(`logup_complete`). What is NOT closed here: the connection to `AirChecksSatisfied.hbus` needs the
DEPLOYED bus's actual column layout (which trace columns carry `A`, the table `B`, the challenge column,
the running cumulative-sum column) — that plumbing is UNMODELED and named as the residual, so `hbus` is
NOT discharged, only reduced to it. The general multiplicity case (repeated looked-up values) is the same
residue argument at a higher-order pole — DISCHARGED in `LogUpMultiset.lean`
(`busBalance_forces_membership_multiset`); this file proves the single-occurrence/`Nodup` case.
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Dregg2.Circuit.BabyBearFriField

namespace Dregg2.Circuit.LogUpSoundness

open Polynomial

variable {F : Type*} [Field F]

/-! ## §1 — The bus, as field sums. -/

/-- **`logupSum α A`** — the lookup side of the bus: `Σ_{a ∈ A} 1/(α + a)`. -/
def logupSum (α : F) (A : List F) : F := (A.map (fun a => (α + a)⁻¹)).sum

/-- **`logupSumM α B`** — the table side of the bus, in MULTIPLICITY form: `Σ_{(b,m) ∈ B} m · 1/(α + b)`
(each table row `b` carries the count `m` of how often it is looked up). -/
def logupSumM (α : F) (B : List (F × ℕ)) : F := (B.map (fun p => p.2 • (α + p.1)⁻¹)).sum

/-- The multiplicity-expansion of a table: `(b, m)` becomes `m` copies of `b`. -/
def expand (B : List (F × ℕ)) : List F := B.flatMap (fun p => List.replicate p.2 p.1)

@[simp] theorem logupSum_nil (α : F) : logupSum α [] = 0 := rfl

@[simp] theorem logupSum_cons (α a : F) (A : List F) :
    logupSum α (a :: A) = (α + a)⁻¹ + logupSum α A := rfl

theorem logupSum_append (α : F) (A A' : List F) :
    logupSum α (A ++ A') = logupSum α A + logupSum α A' := by
  simp [logupSum, List.map_append, List.sum_append]

/-- `logupSum` is invariant under permutation (a bus does not care about the trace-row order). -/
theorem logupSum_perm (α : F) {A A' : List F} (h : A.Perm A') : logupSum α A = logupSum α A' := by
  unfold logupSum; exact (h.map _).sum_eq

/-- The two bus forms agree: the multiplicity form equals the lookup form on the expansion. -/
theorem logupSumM_eq_expand (α : F) (B : List (F × ℕ)) :
    logupSumM α B = logupSum α (expand B) := by
  induction B with
  | nil => simp [logupSumM, expand]
  | cons p B ih =>
      obtain ⟨b, m⟩ := p
      have hhead : logupSum α (expand ((b, m) :: B)) = m • (α + b)⁻¹ + logupSum α (expand B) := by
        rw [expand, List.flatMap_cons, ← expand, logupSum_append]
        congr 1
        rw [logupSum, List.map_replicate, List.sum_replicate]
      rw [hhead, ← ih]
      simp [logupSumM]

/-! ## §2 — The bus, as polynomials: clearing denominators. -/

/-- `prodLin A = ∏_{a ∈ A} (X + a)` — the common denominator of the lookup side. -/
noncomputable def prodLin (A : List F) : F[X] := (A.map (fun a => X + C a)).prod

@[simp] theorem prodLin_nil : prodLin ([] : List F) = 1 := rfl

@[simp] theorem prodLin_cons (a : F) (A : List F) :
    prodLin (a :: A) = (X + C a) * prodLin A := by simp [prodLin]

/-- `sumSkip A = Σ_i ∏_{i' ≠ i} (X + a_{i'})` — the numerator of the lookup side (`prodLin A`'s
derivative; the recursive form below is what the eval identities peel). -/
noncomputable def sumSkip : List F → F[X]
  | [] => 0
  | a :: A => prodLin A + (X + C a) * sumSkip A

@[simp] theorem sumSkip_nil : sumSkip ([] : List F) = 0 := rfl

@[simp] theorem sumSkip_cons (a : F) (A : List F) :
    sumSkip (a :: A) = prodLin A + (X + C a) * sumSkip A := rfl

/-- `sumSkip` IS the derivative of `prodLin` (so it is permutation-invariant and degree-dropping). -/
theorem sumSkip_eq_derivative (A : List F) : sumSkip A = derivative (prodLin A) := by
  induction A with
  | nil => simp
  | cons a A ih =>
      rw [sumSkip_cons, prodLin_cons, derivative_mul, derivative_add, derivative_X, derivative_C,
        add_zero, one_mul, ih]

/-- **`busNum A B`** — the difference numerator: `sumSkip A · prodLin B − sumSkip B · prodLin A`.
The bus is zero at `α` (off the poles) iff this polynomial vanishes at `α` (`bus_zero_iff_busNum`). -/
noncomputable def busNum (A B : List F) : F[X] := sumSkip A * prodLin B - sumSkip B * prodLin A

/-! ### Evaluation identities. -/

/-- `prodLin A` evaluated at `α` is the field product `∏ (α + a)`. -/
theorem prodLin_eval (α : F) (A : List F) :
    (prodLin A).eval α = (A.map (fun a => α + a)).prod := by
  unfold prodLin
  rw [eval_list_prod, List.map_map]
  simp [Function.comp_def]

theorem prodLin_ne_zero (A : List F) : prodLin A ≠ 0 := by
  induction A with
  | nil => simp
  | cons a A ih => rw [prodLin_cons]; exact mul_ne_zero (X_add_C_ne_zero a) ih

/-- Off the poles, `prodLin A` does not vanish at `α`. -/
theorem prodLin_eval_ne_zero {α : F} {A : List F} (h : ∀ a ∈ A, α + a ≠ 0) :
    (prodLin A).eval α ≠ 0 := by
  rw [prodLin_eval, Ne, List.prod_eq_zero_iff]
  intro hmem
  obtain ⟨a, ha, hz⟩ := List.mem_map.mp hmem
  exact h a ha hz

/-- **The key relation (partial fractions, cleared).** Off the poles,
`logupSum α A · ∏(α + a) = Σ_i ∏_{i'≠i}(α + a_{i'})` — the lookup bus times its denominator IS the
numerator, evaluated. This is the whole content of "the bus is the log-derivative of `prodLin`." -/
theorem logupSum_mul_prodLin_eval {α : F} :
    ∀ {A : List F}, (∀ a ∈ A, α + a ≠ 0) →
      logupSum α A * (prodLin A).eval α = (sumSkip A).eval α
  | [], _ => by simp
  | a :: A, h => by
      have ha : α + a ≠ 0 := h a (List.mem_cons_self ..)
      have hA : ∀ a' ∈ A, α + a' ≠ 0 := fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
      have ih := logupSum_mul_prodLin_eval hA
      have hev : (prodLin (a :: A)).eval α = (α + a) * (prodLin A).eval α := by
        rw [prodLin_cons, eval_mul, eval_add, eval_X, eval_C]
      have hsk : (sumSkip (a :: A)).eval α
          = (prodLin A).eval α + (α + a) * (sumSkip A).eval α := by
        rw [sumSkip_cons, eval_add, eval_mul, eval_add, eval_X, eval_C]
      rw [logupSum_cons, hev, hsk]
      have hu : (α + a)⁻¹ * (α + a) = 1 := inv_mul_cancel₀ ha
      calc ((α + a)⁻¹ + logupSum α A) * ((α + a) * (prodLin A).eval α)
          = (α + a)⁻¹ * (α + a) * (prodLin A).eval α
            + (α + a) * (logupSum α A * (prodLin A).eval α) := by ring
        _ = (prodLin A).eval α + (α + a) * (sumSkip A).eval α := by rw [hu, ih]; ring

/-- **Bus-zero ⟺ numerator-zero (pole-guarded).** Off the poles of BOTH sides, the bus balances at `α`
exactly when `busNum` vanishes at `α`. -/
theorem bus_zero_iff_busNum {α : F} {A B : List F}
    (hA : ∀ a ∈ A, α + a ≠ 0) (hB : ∀ b ∈ B, α + b ≠ 0) :
    logupSum α A = logupSum α B ↔ (busNum A B).eval α = 0 := by
  have hPA : (prodLin A).eval α ≠ 0 := prodLin_eval_ne_zero hA
  have hPB : (prodLin B).eval α ≠ 0 := prodLin_eval_ne_zero hB
  have kA := logupSum_mul_prodLin_eval hA
  have kB := logupSum_mul_prodLin_eval hB
  unfold busNum
  rw [eval_sub, eval_mul, eval_mul, ← kA, ← kB]
  constructor
  · intro h; rw [h]; ring
  · intro h
    have hfac : (logupSum α A - logupSum α B) * ((prodLin A).eval α * (prodLin B).eval α) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd h2 (mul_ne_zero hPA hPB)

/-! ## §3 — Degrees: `busNum` has degree `< |A| + |B|`. -/

theorem degree_prodLin (A : List F) : (prodLin A).degree = (A.length : ℕ) := by
  induction A with
  | nil => simp
  | cons a A ih =>
      rw [prodLin_cons, degree_mul, degree_X_add_C, ih, List.length_cons]
      push_cast; ring

/-- `sumSkip A` has degree STRICTLY below `|A|` (it is a derivative). -/
theorem degree_sumSkip_lt (A : List F) : (sumSkip A).degree < (A.length : ℕ) := by
  rw [sumSkip_eq_derivative, ← degree_prodLin A]
  exact degree_derivative_lt (prodLin_ne_zero A)

/-- **`busNum A B` has degree `< |A| + |B|`.** The Schwartz–Zippel degree the exceptional set rides. -/
theorem degree_busNum_lt (A B : List F) :
    (busNum A B).degree < ((A.length + B.length : ℕ) : WithBot ℕ) := by
  have h1 : (sumSkip A * prodLin B).degree < ((A.length + B.length : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_prodLin]
    calc (sumSkip A).degree + (B.length : ℕ)
        < (A.length : ℕ) + (B.length : ℕ) :=
          WithBot.add_lt_add_right (by simp) (degree_sumSkip_lt A)
      _ = ((A.length + B.length : ℕ) : WithBot ℕ) := by push_cast; ring
  have h2 : (sumSkip B * prodLin A).degree < ((A.length + B.length : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_prodLin]
    calc (sumSkip B).degree + (A.length : ℕ)
        < (B.length : ℕ) + (A.length : ℕ) :=
          WithBot.add_lt_add_right (by simp) (degree_sumSkip_lt B)
      _ = ((A.length + B.length : ℕ) : WithBot ℕ) := by push_cast; ring
  exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt h1 h2)

/-! ### Permutation-invariance of the numerator (a bus does not care about looked-up-row order).

`prodLin`/`sumSkip`/`busNum` depend only on the MULTISET of `A` — a reordering of the looked-up rows
leaves the polynomial identity untouched. This is what lets us bring ANY single looked-up value to the
head, where `busNum_ne_zero_of_forged` (§5) bites. -/

/-- `prodLin` is permutation-invariant (it is a product over `A`). -/
theorem prodLin_perm {A A' : List F} (h : A.Perm A') : prodLin A = prodLin A' := by
  unfold prodLin; exact List.Perm.prod_eq (h.map _)

/-- `sumSkip` is permutation-invariant (it is the derivative of the perm-invariant `prodLin`). -/
theorem sumSkip_perm {A A' : List F} (h : A.Perm A') : sumSkip A = sumSkip A' := by
  rw [sumSkip_eq_derivative, sumSkip_eq_derivative, prodLin_perm h]

/-- **`busNum` is permutation-invariant in the lookup side.** Reordering the looked-up rows `A` leaves
`busNum A B` unchanged — the polynomial sees only the multiset. -/
theorem busNum_perm_left {A A' : List F} (h : A.Perm A') (B : List F) :
    busNum A B = busNum A' B := by
  unfold busNum; rw [prodLin_perm h, sumSkip_perm h]

/-- `busNum A A = 0` — an HONEST bus (lookups exactly the table) has a vanishing numerator, so its
exceptional set is empty and every challenge balances. The completeness face of the SZ argument. -/
theorem busNum_self (A : List F) : busNum A A = 0 := sub_self _

/-! ## §4 — The exceptional set and the Schwartz–Zippel soundness bound. -/

variable [DecidableEq F]

/-- **The exceptional set** — the challenges `α` at which a MISMATCHED bus can still balance: the roots
of `busNum`. Named, as the honest Schwartz–Zippel form demands. -/
noncomputable def exceptionalSet (A B : List F) : Finset F := (busNum A B).roots.toFinset

/-- **The exceptional set is SMALL.** When `busNum` is a nonzero polynomial (the mismatch case), the bus
balances only on `< |A| + |B|` challenges. This is `Polynomial.card_roots'` + the degree bound. -/
theorem exceptionalSet_card_lt {A B : List F} (hne : busNum A B ≠ 0) :
    (exceptionalSet A B).card < A.length + B.length := by
  have hnd : (busNum A B).natDegree < A.length + B.length :=
    (natDegree_lt_iff_degree_lt hne).mpr (degree_busNum_lt A B)
  calc (exceptionalSet A B).card
      ≤ Multiset.card (busNum A B).roots := Multiset.toFinset_card_le _
    _ ≤ (busNum A B).natDegree := card_roots' _
    _ < A.length + B.length := hnd

/-- The exceptional set is permutation-invariant in the lookup side (it reads only `busNum`). -/
theorem exceptionalSet_perm_left {A A' : List F} (h : A.Perm A') (B : List F) :
    exceptionalSet A B = exceptionalSet A' B := by
  unfold exceptionalSet; rw [busNum_perm_left h B]

/-! ## §5 — The forged-lookup tooth: a non-member makes `busNum` nonzero. -/

omit [DecidableEq F] in
/-- **A forged lookup makes the numerator NONZERO.** If `c` is looked up (once, at the head — any single
occurrence can be brought here by `logupSum_perm`) and `c` is ABSENT from the table `B`, then `busNum`
is a nonzero polynomial: it does not vanish at `X = -c`. At `-c` the lookup denominator `prodLin (c::A)`
vanishes (kills the second term) while the table denominator `prodLin B` does NOT (c not in B), and the
surviving numerator `sumSkip (c::A) = prodLin A + (X+c)·…` reads `prodLin A ≠ 0` off `-c`. -/
theorem busNum_ne_zero_of_forged {A B : List F} {c : F}
    (hcA : c ∉ A) (hcB : c ∉ B) : busNum (c :: A) B ≠ 0 := by
  -- evaluate at -c: prodLin (c::A) vanishes, prodLin B and prodLin A do not.
  have hPcA : (prodLin (c :: A)).eval (-c) = 0 := by
    rw [prodLin_cons, eval_mul, eval_add, eval_X, eval_C, neg_add_cancel, zero_mul]
  have hPA : (prodLin A).eval (-c) ≠ 0 := by
    rw [prodLin_eval, Ne, List.prod_eq_zero_iff]
    intro hmem
    obtain ⟨a, ha, hz⟩ := List.mem_map.mp hmem
    have hac : a = c := by linear_combination hz
    exact hcA (hac ▸ ha)
  have hPB : (prodLin B).eval (-c) ≠ 0 := by
    rw [prodLin_eval, Ne, List.prod_eq_zero_iff]
    intro hmem
    obtain ⟨b, hb, hz⟩ := List.mem_map.mp hmem
    have hbc : b = c := by linear_combination hz
    exact hcB (hbc ▸ hb)
  -- busNum(-c) = sumSkip(c::A)(-c)·prodLin B(-c) − sumSkip B(-c)·0 = prodLin A(-c)·prodLin B(-c) ≠ 0.
  have hval : (busNum (c :: A) B).eval (-c) ≠ 0 := by
    have hsk : (sumSkip (c :: A)).eval (-c) = (prodLin A).eval (-c) := by
      rw [sumSkip_cons, eval_add, eval_mul, eval_add, eval_X, eval_C, neg_add_cancel, zero_mul,
        add_zero]
    unfold busNum
    rw [eval_sub, eval_mul, eval_mul, hsk, hPcA, mul_zero, sub_zero]
    exact mul_ne_zero hPA hPB
  intro h
  rw [h, eval_zero] at hval
  exact hval rfl

/-- **LogUp soundness — the forged-lookup form (bus-zero ⟹ membership, exceptional set named).**
Suppose the prover looks up `c` (once, at the head) which is ABSENT from the table `B`, and yet the bus
BALANCES at the challenge `α` (off the poles). Then `α` lies in the exceptional set, whose size is
`< |c::A| + |B|`. Contrapositive: for all but `< |A|+|B|` challenges, a forged (non-member) lookup makes
the bus NONZERO — the prover cannot look up a value outside the table and pass. -/
theorem logup_forged_lookup_sound {A B : List F} {c α : F}
    (hcA : c ∉ A) (hcB : c ∉ B)
    (hpA : ∀ x ∈ c :: A, α + x ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α (c :: A) = logupSum α B) :
    α ∈ exceptionalSet (c :: A) B ∧
      (exceptionalSet (c :: A) B).card < (c :: A).length + B.length := by
  have hne : busNum (c :: A) B ≠ 0 := busNum_ne_zero_of_forged hcA hcB
  refine ⟨?_, exceptionalSet_card_lt hne⟩
  have hroot : (busNum (c :: A) B).eval α = 0 := (bus_zero_iff_busNum hpA hpB).mp hbal
  rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hne]
  exact hroot

/-! ## §5½ — THE BRIDGE: bus-balance ⟹ membership (`hbus`'s missing arrow, proved by SZ).

`logup_forged_lookup_sound` (§5) is the CONTRAPOSITIVE, stated at the head. Here is the POSITIVE form
`AirLegsDischarged.hbus_is_lookup` calls for: a bus that balances at a NON-exceptional challenge forces
every looked-up value to be a TABLE MEMBER. This is the exact `hmem : tuple ∈ tbl` hypothesis that
`DescriptorIR2.chip_lookup_sound_N` / the range lever consume — DERIVED, no longer assumed. -/

/-- **`busBalance_forces_membership_single` — the single-occurrence membership bridge.** If the LogUp
bus BALANCES at `α` (off the poles) and `α` is NON-exceptional (not a root of `busNum`), then any value
`c` looked up EXACTLY ONCE (`A.count c = 1`) is a member of the table `B`. Pure Schwartz–Zippel: were
`c ∉ B`, `busNum` would be nonzero (`busNum_ne_zero_of_forged`, via the head brought over by
`busNum_perm_left`), so a balancing `α` would have to be one of its `< |A|+|B|` roots — i.e.
exceptional. The `card_roots'` route, run in the accept ⟹ membership direction. -/
theorem busBalance_forces_membership_single {A B : List F} {α c : F}
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B)
    (hc : c ∈ A) (hcount : A.count c = 1) : c ∈ B := by
  by_contra hcB
  -- Bring the single occurrence of `c` to the head: `A ~ c :: A.erase c`, with `c ∉ A.erase c`.
  have hperm : A.Perm (c :: A.erase c) := List.perm_cons_erase hc
  have hcA' : c ∉ A.erase c := by
    rw [← List.count_eq_zero, List.count_erase_self, hcount]
  -- A forged head makes the numerator a NONZERO polynomial.
  have hne : busNum (c :: A.erase c) B ≠ 0 := busNum_ne_zero_of_forged hcA' hcB
  -- Transport the balance / non-exceptionality / poles across the permutation.
  have hbal' : logupSum α (c :: A.erase c) = logupSum α B := by
    rw [← logupSum_perm α hperm]; exact hbal
  have hnonexc' : α ∉ exceptionalSet (c :: A.erase c) B := by
    rwa [exceptionalSet_perm_left hperm B] at hnonexc
  have hpA' : ∀ x ∈ c :: A.erase c, α + x ≠ 0 := fun x hx => hpA x (hperm.mem_iff.mpr hx)
  -- A balancing challenge is a root of the (nonzero) numerator: it lands in the exceptional set.
  have hroot : (busNum (c :: A.erase c) B).eval α = 0 := (bus_zero_iff_busNum hpA' hpB).mp hbal'
  exact hnonexc' (by rw [exceptionalSet, Multiset.mem_toFinset, mem_roots hne]; exact hroot)

/-- **`busBalance_forces_membership` — support containment for DISTINCT looked-up values.** When the
looked-up list `A` has no repeats (`A.Nodup`), a balancing non-exceptional bus forces EVERY looked-up
value into the table: `∀ c ∈ A, c ∈ B`. The multiset support of the trace's lookups is contained in the
table support — the soundness statement a range/chip lookup needs. (Repeated looked-up values are the
higher-order-pole residual named in §8; each DISTINCT value is covered here.) -/
theorem busBalance_forces_membership {A B : List F} {α : F}
    (hpA : ∀ a ∈ A, α + a ≠ 0) (hpB : ∀ b ∈ B, α + b ≠ 0)
    (hbal : logupSum α A = logupSum α B)
    (hnonexc : α ∉ exceptionalSet A B)
    (hnodup : A.Nodup) : ∀ c ∈ A, c ∈ B := fun _ hc =>
  busBalance_forces_membership_single hpA hpB hbal hnonexc hc
    (List.count_eq_one_of_mem hnodup hc)

/-! ## §6 — Completeness (the easy direction, full). -/

omit [DecidableEq F] in
/-- **Completeness.** If the lookups `A` ARE the table `B` with the declared multiplicities (`A` a
permutation of `expand B`), then for every valid challenge the bus balances — a genuine lookup FIRES. -/
theorem logup_complete (α : F) {A : List F} {B : List (F × ℕ)} (h : A.Perm (expand B)) :
    logupSum α A = logupSumM α B := by
  rw [logupSumM_eq_expand, logupSum_perm α h]

#assert_axioms logupSum_mul_prodLin_eval
#assert_axioms bus_zero_iff_busNum
#assert_axioms degree_busNum_lt
#assert_axioms exceptionalSet_card_lt
#assert_axioms busNum_ne_zero_of_forged
#assert_axioms logup_forged_lookup_sound
#assert_axioms busNum_perm_left
#assert_axioms exceptionalSet_perm_left
#assert_axioms busBalance_forces_membership_single
#assert_axioms busBalance_forces_membership
#assert_axioms logup_complete

/-! ## §7 — BabyBear instantiation + the concrete soundness error. -/

section BabyBear

open Dregg2.Circuit.BabyBearFriField

/-- **The soundness error at BabyBear.** A forged lookup passes the bus at at most
`natDegree busNum < |A| + |B|` of the `|F| = 2013265921` challenges, so a UNIFORM `α` catches it with
error `≤ (|A| + |B|)/2013265921`. Stated as: the exceptional set has `< |A|+|B|` elements inside the
`2013265921`-element field — the concrete BabyBear Schwartz–Zippel bound. -/
theorem babybear_soundness_error {A B : List BabyBear} {c : BabyBear}
    (hcA : c ∉ A) (hcB : c ∉ B) :
    (exceptionalSet (c :: A) B).card < (c :: A).length + B.length ∧
      Fintype.card BabyBear = 2013265921 :=
  ⟨exceptionalSet_card_lt (busNum_ne_zero_of_forged hcA hcB), by
    haveI : NeZero babyBearP := ⟨by norm_num⟩
    exact ZMod.card babyBearP⟩

/-! ### Teeth (both instances load-bearing), at concrete BabyBear values.

Table `B = [10, 20, 30]`. A genuine lookup of `20` balances the bus; a FORGED lookup of `7` (not in the
table) makes `busNum` a nonzero polynomial — the forgery bites for all but `< 4` of the 2·10⁹ challenges,
and here we exhibit it as `busNum ≠ 0`. -/

/-- The concrete table. -/
noncomputable def tbl3 : List BabyBear := [10, 20, 30]

/-- RESPECTING TOOTH (fires): a genuine lookup `[20]` — exactly the table row `20` at multiplicity 1 —
balances the bus, because `[20]` is a permutation of `expand [(20,1)]`. -/
theorem honest_lookup_balances (α : BabyBear) :
    logupSum α [20] = logupSumM α [((20 : BabyBear), 1)] := by
  rw [logupSumM_eq_expand]
  rfl

/-- FORGED TOOTH (bites): `7 ∉ tbl3`, looked up once, forces `busNum` NONZERO — so the bus fails for all
but `< |[7]| + |tbl3| = 4` challenges. A prover CANNOT look up `7` (absent from the table) and pass. -/
theorem forged_lookup_bites : busNum ([7] : List BabyBear) tbl3 ≠ 0 :=
  busNum_ne_zero_of_forged (by decide) (by decide)

/-- …and its exceptional set is genuinely small: `< 4` of the `2013265921` field elements. -/
theorem forged_lookup_exceptional_small :
    (exceptionalSet ([7] : List BabyBear) tbl3).card < 1 + tbl3.length :=
  exceptionalSet_card_lt forged_lookup_bites

/-- MEMBERSHIP-BRIDGE TOOTH (fires, not vacuous): the honest lookup `[20]` against the table `[20]`
balances at the non-exceptional `α = 0` (the honest bus has an EMPTY exceptional set, `busNum_self`),
so `busBalance_forces_membership_single` DERIVES `20 ∈ [20]`. Exercises the whole accept ⟹ membership
path on concrete BabyBear values, so the landing lemma is not vacuously stated. -/
theorem membership_bridge_fires : (20 : BabyBear) ∈ ([20] : List BabyBear) := by
  refine busBalance_forces_membership_single (α := (0 : BabyBear)) (c := 20)
    (A := [20]) (B := [20]) ?_ ?_ rfl ?_ (by simp) (by decide)
  · intro a ha; simp at ha; subst ha; decide
  · intro b hb; simp at hb; subst hb; decide
  · -- α = 0 is non-exceptional: the honest bus's numerator is 0, whose root set is empty.
    rw [exceptionalSet, busNum_self, roots_zero]; simp

end BabyBear

/-! ## §8 — The connection to `AirChecksSatisfied.hbus` (REDUCED to a NAMED floor; the SZ arrow proved).

`AirLegsDischarged.hbus_is_lookup` pins every remaining `hbus` obligation to a chip/range LOOKUP
membership: `Lookup.holdsAt` says the evaluated tuple IS a row of the committed table. §5½ now supplies
the missing ARROW as a THEOREM, not an assumption: `busBalance_forces_membership` — a bus that balances
at a non-exceptional challenge FORCES support containment `∀ c ∈ A, c ∈ B` (`busBalance_forces_membership_single`
for any single-occurrence value; the `Nodup` corollary for the distinct support), by the identical
`card_roots'` Schwartz–Zippel route `OodSoundnessGame.rlc_debatch` runs on the batching challenge. This
is exactly the `hmem : tuple ∈ tbl` hypothesis `DescriptorIR2.chip_lookup_sound_N` and the range lever
consume — now DERIVED from the bus, not carried.

So `hbus` is REDUCED to the following NAMED floor (no longer a bare premise):

  1. **LogUp-SZ soundness — PROVED here.** `busBalance_forces_membership` (support containment) +
     `logup_complete` (completeness) + the FS ε-bound `≤ (|A|+|B|)/|F|` (`exceptionalSet_card_lt`,
     `babybear_soundness_error`), the same quantitative game frame as `OodSoundnessGame`.
  2. **Chip/range TABLE FAITHFULNESS — the table `B` IS the honest function's graph.** For the RANGE
     table this is STRUCTURAL, not a floor: `rangeRows BAL_LIMB_BITS = Lookup.rangeTable 30` is
     definitionally `[0, 2^30)`, so its faithfulness is `rfl`-level — and CRUCIALLY it is argued
     symbolically over `List.range (2^30)`, NEVER enumerated (2^30 ≈ 10⁹ rows are not `#eval`-able).
     For the CHIP table it is the real-permutation carrier `ChipTableSoundN permOutDeployed`
     (`deployedChipTbl_sound`) — i.e. the Poseidon2 floor already named elsewhere, not a new obligation.
  3. **FS non-exceptionality ε-bound** — `α ∉ exceptionalSet`, a bounded-advantage event, ε ≤ deg/|F|
     (`OodSoundnessGame.oodNonExc_winProb_le`, transported to the LogUp bus here).

WHAT GENUINELY REMAINS (two honest residuals, precisely named — neither a fresh crypto primitive):
  * **Column-layout plumbing (irreducible HERE).** Exhibiting, from the descriptor's actual AIR
    columns, (i) the list `A` of per-row looked-up tuples and the table `B` with its multiplicity
    column, (ii) the challenge column `α` and the running cumulative-sum column whose boundary-zero IS
    `logupSum α A = logupSumM α B`, (iii) the pole-avoidance side-condition. This plumbing is UNMODELED
    in `Dregg2/Circuit/` — the same unmodeled-layout residual `OodSoundnessGame` names for the OOD Λ-column.
  * **Repeated-value multiplicity — DISCHARGED (`LogUpMultiset.lean`).** Formerly the second residual:
    the support-containment theorem here is proved per DISTINCT looked-up value (single-occurrence head).
    `LogUpMultiset.busBalance_forces_membership_multiset` now proves it for ARBITRARY multiplicities —
    `busNum` factors as `(X+C c)^(k−1) · G` with the NONZERO residue `G(−c) = k·∏(−c+aᵢ)·∏(−c+bⱼ)`
    (root multiplicity EXACTLY `k−1`, `busNum_forged_rootMultiplicity`), needing only the no-wrap fact
    `k <` char `F` (`k ≪ 2·10⁹` always; `…_of_charP` discharges it for any trace shorter than the field).
    That theorem SUBSUMES `busBalance_forces_membership` (multiplicity-1 specialization). No longer open.

This file therefore DISCHARGES the LogUp-SZ arrow of `hbus` for the distinct support (shared across ALL
27 effects — the bus is one argument, not 27), and `LogUpMultiset.lean` extends it to the full MULTISET
support, reducing `hbus` to {chip/range table faithfulness (§2, structural for range / Poseidon2-floor
for chip) + FS ε + the column-layout wire}. -/

#check @busBalance_forces_membership
#check @logup_forged_lookup_sound
#check @exceptionalSet_card_lt

end Dregg2.Circuit.LogUpSoundness

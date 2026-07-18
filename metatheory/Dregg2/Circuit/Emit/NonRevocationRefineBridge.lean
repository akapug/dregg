/-
# Dregg2.Circuit.Emit.NonRevocationRefineBridge — the FOLDED `air_accepts ⟺ spec` bridge for the
`revocation` (sorted-tree non-membership) family: ONE named carrier bundle, ONE literal biconditional.

## Why this file exists (the TEMPLATE)

`NonRevocationRefine` proves the SOUNDNESS direction (`Satisfied2 ⟹ NonMember`, `FieldCanonicalDiffs`
discharged by real lookups) and `NonRevocationRefineComplete` proves COMPLETENESS (from bracketing
data, a satisfying trace with SOUND, CONSTRUCTED carriers EXISTS). They already carry both directions.

This file does the last mile the assurance-perimeter campaign asked for: **fold the residual trust
into ONE named carrier bundle (`NonRevCarriers`) and state the literal `⟺`, composing the two existing
directions.** It is meant to be the clean SCHEMA the rest of the perimeter (garbled-eval, note-spend,
transfer-commit) copies. See `docs/DESIGN-assurance-perimeter-closure.md`.

## THE 5-STEP SCHEMA (where each step lives — copy this for the next value on the surface)

  1. **Semantic relation.** `Crypto.NonMembership.NonMember spine e := Sorted spine ∧ e ∉ spine`
     (trace-independent; the human meaning "e is not revoked"). Combinatorial core:
     `sorted_gap_excludes`.
  2. **SAT ⟹ SEM vs NAMED carriers.** `NonRevocationRefine.nonRevocation_nonmembership`: a satisfying
     trace + the named crypto carriers force `NonMember`. Here folded behind `NonRevCarriers` →
     `nonRevocation_sound` (§2).
  3. **Construct the satisfying trace.** `NonRevocationRefineComplete.semTrace` (parametric over the
     bracketing data `(hash, L, x, R, sib, pos)`), `sem_satisfied` (§5 uses it).
  4. **Construct AND PROVE the carriers (never assume).** `sem_chipSound` (Poseidon2 CR realized),
     `sem_rangeSound` (the range argument realized — the ONE place `L < x < R` is load-bearing).
  5. **Round-trip / compose the `⟺`.** This file: `nonRevocation_accepts_iff` (§3, the literal single
     biconditional accept-set = spec) and `nonRevocation_bridge` (§4, the ∀-soundness ∧ ∃-completeness
     conjunction that concludes the literal `NonMember`, mirroring `NonMembership.nonmembership_bridge`).

## The ONE named carrier bundle (the honest floor, shared across the whole surface)

`NonRevCarriers hash t spine` (§2) folds EVERYTHING between `Satisfied2` and `NonMember`:
  * `chip`  — `ChipTableSound` (Poseidon2 collision-resistance; the emitter's chip argument);
  * `range` — `RangeTableSound` (the 30-bit LogUp range argument's faithfulness);
  * `canon` — `NonRevCanon` (the deployed range-check envelope: digests canonical, ordering wires in
              the field's low half — the ℤ-vs-BabyBear wrap-freeness);
  * `sorted` / `adjacent` — the spine decode (`Sorted spine`, `L`,`R` consecutive in `spine`).
Nothing else is trusted. `chip`/`range` are the honest crypto floor the campaign names once and shares;
`canon` is the deployed-range-check envelope; the decode is pure combinatorics.

## Why the literal `⟺` is `AirAccepts ↔ WindowBracketed`, not `Satisfied2 t ↔ NonMember`

A naive single-trace `Satisfied2 t ↔ NonMember spine (…X)` is NOT the right object, and the reason is a
reusable lesson for the template: `sem_satisfied` proves `Satisfied2` on the completeness witness
**unconditionally** — the strict ordering `L < x < R` is enforced NOT by a gate but by the range
LOOKUP's soundness (the `RangeTableSound` carrier: a negative diff wire is simply an out-of-range table
entry). So on the constructed family `Satisfied2` is constant-true and a single-trace iff would
degenerate; and against the FULL `NonMember` the reverse fails at the set boundary (a below-minimum
non-member is not bracketed by any committed pair — this circuit computes BRACKETED non-membership; a
sentinel-leaf accumulator would close the gap, and is not modelled here). The honest renderings:

  * `nonRevocation_accepts_iff` — the descriptor's accept-set (canonical traces whose RANGE ARGUMENT is
    sound) is EXACTLY the window-bracketed non-members: `AirAccepts hash spine x ↔ WindowBracketed
    spine x`. Both directions real, modulo NO extra carrier (the range argument alone forces the
    ordering); `WindowBracketed ⟹ NonMember` (§3) is the tie to the human spec.
  * `nonRevocation_bridge` — soundness over ALL traces (the hostile-prover guarantee) ∧ completeness
    (∃ a satisfying trace), concluding the literal `NonMember spine (…X)` — the codebase idiom
    (`NonMembership.nonmembership_bridge`).

## Mutation canary (load-bearing, machine-checked, §5)
  * `carrier_load_bearing` — a MEMBER query (`x = L`) still SATISFIES the descriptor (gates are
    identities) yet its range table is UNSOUND: `Satisfied2 ∧ ¬ RangeTableSound`. So the `range`
    carrier is essential to the `→` of the iff — deleting it lets a member through.
  * `gate_load_bearing` — a de-bracketed trace (`RPOS = LPOS + 2`) is REJECTED (`¬ Satisfied2`): the
    adjacency GATE is load-bearing for the `←` completeness (its `sem_satisfied` reds if the gate goes).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`/`axiom`/`native_decide`. The
crypto carriers enter ONLY as the named `NonRevCarriers` fields (never as axioms). NEW file; every
import read-only; the committed `NonRevocationRefine{,Complete}` proofs are untouched.
-/
import Dregg2.Circuit.Emit.NonRevocationRefineComplete

namespace Dregg2.Circuit.Emit.NonRevocationRefineBridge

open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 Satisfied2 VmTrace envAt TableId ChipTableSound)
open Dregg2.Circuit.Emit.NonRevocationEmit
  (nonRevocationDesc HALF_P_MINUS_1 ORDERING_BITS X LEAF_L LEAF_R)
open Dregg2.Circuit.Emit.NonRevocationRefine
  (RangeTableSound NonRevCanon range_lookup_sound nonRevocation_nonmembership)
open Dregg2.Circuit.Emit.NonRevocationRefineComplete
  (semTrace semRange semTraceBad sem_satisfied sem_chipSound sem_rangeSound sem_fail
   sem_needs_bracketing)
open Dregg2.Crypto.NonMembership (Sorted Adjacent NonMember sorted_gap_excludes)

set_option autoImplicit false

/-! ## §1 — the semantic side: window-bracketed non-membership (what the circuit COMPUTES).

`WindowBracketed spine x` — `x` sits strictly between two ADJACENT committed leaves `L`, `R`, both gaps
inside the half-field window. This is the exact fragment the deployed non-revocation AIR witnesses; with
a `Sorted spine` it PROVES the human spec `NonMember spine x` (`windowBracketed_nonMember`). It does NOT
capture below-minimum / above-maximum absence — a sentinel-leaf accumulator would; this circuit does
not model sentinels, and saying so is the honest resolution of the accept-set. -/

/-- **`WindowBracketed spine x`** — an adjacent committed pair `L`,`R` brackets `x` (`L < x < R`) with
both gaps in the half-field window (`x−L−1, R−x−1 ≤ HALF_P_MINUS_1`). The spec the AIR's accept-set
equals; a strict refinement of `NonMember` (it also fixes the bracketing witness + the field window). -/
def WindowBracketed (spine : List ℤ) (x : ℤ) : Prop :=
  ∃ L R : ℤ, Adjacent spine L R ∧ L < x ∧ x < R
    ∧ x - L - 1 ≤ HALF_P_MINUS_1 ∧ R - x - 1 ≤ HALF_P_MINUS_1

/-- **`WindowBracketed ⟹ NonMember`** — the tie to the human spec: bracketing by an adjacent present
pair EXCLUDES `x` from a sorted committed set (`sorted_gap_excludes`, the unconditional core). -/
theorem windowBracketed_nonMember {spine : List ℤ} {x : ℤ}
    (hsorted : Sorted spine) (hw : WindowBracketed spine x) : NonMember spine x := by
  obtain ⟨L, R, hadj, hlt, hgt, _, _⟩ := hw
  exact ⟨hsorted, sorted_gap_excludes spine L R x hsorted hadj hlt hgt⟩

/-! ## §2 — the ONE named carrier bundle + the soundness leg through it (SAT ⟹ SEM). -/

/-- **`NonRevCarriers hash t spine` — THE named carrier bundle.** Everything the soundness bridge trusts
between a satisfying trace and genuine non-membership, folded into one structure: the two crypto
carriers (`chip` = Poseidon2 CR, `range` = the 30-bit range argument), the deployed range-check
envelope (`canon`), and the spine decode (`sorted`, `adjacent`). This is the single honest floor the
whole assurance perimeter shares; nothing else is assumed. -/
structure NonRevCarriers (hash : List ℤ → ℤ) (t : VmTrace) (spine : List ℤ) : Prop where
  /-- Row 0 is an active window (the descriptor's row-0 constraints fire). -/
  hlen     : 0 < t.rows.length
  /-- Poseidon2 collision-resistance — the chip argument's faithfulness (the ONE hash carrier). -/
  chip     : ChipTableSound hash (t.tf .poseidon2)
  /-- The 30-bit LogUp range argument's faithfulness (the ONE range carrier). -/
  range    : RangeTableSound ORDERING_BITS (t.tf .range)
  /-- The deployed range-check envelope: digests canonical, ordering wires in the field's low half. -/
  canon    : NonRevCanon t
  /-- The committed spine is sorted (the structure the root commits to). -/
  sorted   : Sorted spine
  /-- The trace's two bracketing leaves are CONSECUTIVE in the committed spine (the decode). -/
  adjacent : Adjacent spine ((envAt t 0).loc LEAF_L) ((envAt t 0).loc LEAF_R)

/-- **`nonRevocation_sound` — the SOUNDNESS leg, folded (step 2 of the schema).** A satisfying trace
carrying the named bundle reads a GENUINE non-member: `Satisfied2 ⟹ NonMember spine (…X)`. This is the
hostile-prover guarantee (quantified over ALL traces, not the constructed family); it just repackages
`nonRevocation_nonmembership` behind `NonRevCarriers`. -/
theorem nonRevocation_sound {hash : List ℤ → ℤ} {t : VmTrace} {spine : List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (C : NonRevCarriers hash t spine)
    (hsat : Satisfied2 hash nonRevocationDesc minit mfin maddrs t) :
    NonMember spine ((envAt t 0).loc X) :=
  nonRevocation_nonmembership C.hlen hsat C.chip C.range C.canon spine C.sorted C.adjacent

/-! ## §3 — the literal single biconditional: accept-set = spec.

`AirAccepts hash spine x` — the descriptor ACCEPTS a canonical trace for `x` (some adjacent bracket
`L`,`R` in `spine`) whose RANGE ARGUMENT is sound. The literal `⟺` says this accept-set is EXACTLY the
window-bracketed non-members. Both directions are real: `→` extracts the ordering from the sound range
table (the carrier is load-bearing, `carrier_load_bearing`); `←` CONSTRUCTS the satisfying trace and
PROVES its range carrier (`sem_satisfied` + `sem_rangeSound`). No hash/canon carrier is needed for this
biconditional — the range argument alone pins the ordering. -/

/-- **`AirAccepts hash spine x`** — there is a bracket `L`,`R` (adjacent in `spine`) and a canonical
trace `semTrace` for `x` that the deployed descriptor SATISFIES with a SOUND range argument. The
descriptor's non-membership judgment on `x`. -/
def AirAccepts (hash : List ℤ → ℤ) (spine : List ℤ) (x : ℤ) : Prop :=
  ∃ L R sib pos : ℤ,
    Adjacent spine L R
    ∧ Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) []
        (semTrace hash L x R sib pos)
    ∧ RangeTableSound ORDERING_BITS ((semTrace hash L x R sib pos).tf .range)

/-- **`nonRevocation_accepts_iff` — THE LITERAL `⟺` (accept-set = spec).** The descriptor's
non-membership accept-set for `x` against `spine` is EXACTLY the window-bracketed non-members:
`AirAccepts hash spine x ↔ WindowBracketed spine x`. A genuine biconditional, both directions
load-bearing, modulo NO extra carrier beyond the range argument folded into `AirAccepts` itself.

`→` : the sound range table forces every diff/half-diff wire into `[0, 2^30)`, hence `L < x < R` and the
      window bounds — the ordering lives in the range ARGUMENT (see `carrier_load_bearing`).
`←` : the completeness construction (`sem_satisfied` unconditional; `sem_rangeSound` from `L < x < R`)
      builds the accepting trace. -/
theorem nonRevocation_accepts_iff (hash : List ℤ → ℤ) (spine : List ℤ) (x : ℤ) :
    AirAccepts hash spine x ↔ WindowBracketed spine x := by
  constructor
  · rintro ⟨L, R, sib, pos, hadj, _hsat, hrange⟩
    -- the four range-table rows: [x−L−1], [R−x−1], [HALF−(x−L−1)], [HALF−(R−x−1)] all in [0, 2^30).
    have hmemDL : ([x - L - 1] : List ℤ) ∈ (semTrace hash L x R sib pos).tf .range := by
      show ([x - L - 1] : List ℤ) ∈ semRange L x R
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have hmemDR : ([R - x - 1] : List ℤ) ∈ (semTrace hash L x R sib pos).tf .range := by
      show ([R - x - 1] : List ℤ) ∈ semRange L x R
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have hmemRL : ([HALF_P_MINUS_1 - (x - L - 1)] : List ℤ)
        ∈ (semTrace hash L x R sib pos).tf .range := by
      show ([HALF_P_MINUS_1 - (x - L - 1)] : List ℤ) ∈ semRange L x R
      exact List.mem_cons_self
    have hmemRR : ([HALF_P_MINUS_1 - (R - x - 1)] : List ℤ)
        ∈ (semTrace hash L x R sib pos).tf .range := by
      show ([HALF_P_MINUS_1 - (R - x - 1)] : List ℤ) ∈ semRange L x R
      exact List.mem_cons_of_mem _ List.mem_cons_self
    have hDL := (range_lookup_sound hrange _ hmemDL).1   -- 0 ≤ x − L − 1
    have hDR := (range_lookup_sound hrange _ hmemDR).1   -- 0 ≤ R − x − 1
    have hRL := (range_lookup_sound hrange _ hmemRL).1   -- 0 ≤ HALF − (x − L − 1)
    have hRR := (range_lookup_sound hrange _ hmemRR).1   -- 0 ≤ HALF − (R − x − 1)
    exact ⟨L, R, hadj, by omega, by omega, by omega, by omega⟩
  · rintro ⟨L, R, hadj, hlt, hgt, hbL, hbR⟩
    exact ⟨L, R, 0, 0, hadj, sem_satisfied hash L x R 0 0,
      sem_rangeSound hash L x R 0 0 hlt hgt hbL hbR⟩

/-- **`nonRevocation_accepts_sound` — the security corollary.** The descriptor accepting `x` PROVES the
human spec: `AirAccepts hash spine x → NonMember spine x` (compose `nonRevocation_accepts_iff` with
`windowBracketed_nonMember`). "If the circuit says `x` is not revoked, it genuinely is not." -/
theorem nonRevocation_accepts_sound {hash : List ℤ → ℤ} {spine : List ℤ} {x : ℤ}
    (hsorted : Sorted spine) (h : AirAccepts hash spine x) : NonMember spine x :=
  windowBracketed_nonMember hsorted ((nonRevocation_accepts_iff hash spine x).mp h)

/-! ## §4 — the codebase-idiom bridge: ∀-soundness ∧ ∃-completeness (concludes literal `NonMember`).

The `air_accepts ⟺ spec` object in the shape `Crypto.NonMembership.nonmembership_bridge` uses: soundness
is ∀-over-all-traces (the hostile-prover guarantee) and completeness is ∃-a-trace (constructed). We fold
soundness behind `NonRevCarriers` and construct completeness from `sem_*`. -/

/-- **`nonRevocation_bridge` — the two-direction bridge (concludes the literal `NonMember`).**
  * SOUNDNESS (∀-trace): every trace carrying the named bundle and satisfying the descriptor reads a
    genuine non-member (`nonRevocation_sound`).
  * COMPLETENESS (∃-trace): any window-bracketing data `L < x < R` (in the field window) yields a trace
    that genuinely satisfies the descriptor with SOUND, CONSTRUCTED chip + range carriers, reading back
    the bracketing data (`sem_satisfied`, `sem_chipSound`, `sem_rangeSound`).
Together: the descriptor's accept-set (∀→) and the semantic relation (∃←) agree on the whole family. -/
theorem nonRevocation_bridge (hash : List ℤ → ℤ) (spine : List ℤ) :
    (∀ (t : VmTrace) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
        NonRevCarriers hash t spine →
        Satisfied2 hash nonRevocationDesc minit mfin maddrs t →
        NonMember spine ((envAt t 0).loc X))
    ∧
    (∀ L x R : ℤ, L < x → x < R →
        x - L - 1 ≤ HALF_P_MINUS_1 → R - x - 1 ≤ HALF_P_MINUS_1 →
        ∃ t : VmTrace,
          Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] t
          ∧ ChipTableSound hash (t.tf .poseidon2)
          ∧ RangeTableSound ORDERING_BITS (t.tf .range)
          ∧ (envAt t 0).loc X = x
          ∧ (envAt t 0).loc LEAF_L = L
          ∧ (envAt t 0).loc LEAF_R = R) :=
  ⟨fun _t _minit _mfin _maddrs C hsat => nonRevocation_sound C hsat,
   fun L x R hlt hgt hbL hbR =>
     ⟨semTrace hash L x R 0 0, sem_satisfied hash L x R 0 0,
      sem_chipSound hash L x R 0 0, sem_rangeSound hash L x R 0 0 hlt hgt hbL hbR,
      rfl, rfl, rfl⟩⟩

#assert_axioms windowBracketed_nonMember
#assert_axioms nonRevocation_sound
#assert_axioms nonRevocation_accepts_iff
#assert_axioms nonRevocation_accepts_sound
#assert_axioms nonRevocation_bridge

/-! ## §5 — the mutation canary (load-bearing witnesses) + a run-through of the `⟺`. -/

/-- **CANARY — the `range` carrier is load-bearing (the `→` of the iff).** A MEMBER query (`x = L =
100`, so `diff_left = −1`) STILL satisfies the descriptor — the gates are identities on the honest
row (`sem_satisfied` needs no ordering) — yet its range table is UNSOUND (it carries the row `[−1]`).
So `Satisfied2` does NOT entail `RangeTableSound`; deleting the `range` carrier from `AirAccepts` would
admit this member. Breaking the carrier reds the `→` direction. -/
theorem carrier_load_bearing (hash : List ℤ → ℤ) :
    ∃ t : VmTrace,
      Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) [] t
      ∧ ¬ RangeTableSound ORDERING_BITS (t.tf .range) := by
  refine ⟨semTrace hash 100 100 300 7 5, sem_satisfied hash 100 100 300 7 5, ?_⟩
  intro hsound
  have hmem : ([(100 : ℤ) - 100 - 1]) ∈ (semTrace hash 100 100 300 7 5).tf .range := by
    show ([(100 : ℤ) - 100 - 1]) ∈ semRange 100 100 300
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h0 := (range_lookup_sound hsound _ hmem).1   -- 0 ≤ 100 − 100 − 1 = −1
  norm_num at h0

/-- **CANARY — the adjacency GATE is load-bearing (the `←` of the bridge).** A de-bracketed trace
(`RPOS = LPOS + 2`) is REJECTED: the adjacency gate cannot vanish, so NO `Satisfied2` exists. Breaking
that gate reds the completeness construction (`sem_satisfied`). Delegates to the committed `sem_fail`. -/
theorem gate_load_bearing (hash : List ℤ → ℤ) (L x R sib pos : ℤ) :
    ¬ Satisfied2 hash nonRevocationDesc (fun _ => 0) (fun _ => (0, 0)) []
        (semTraceBad hash L x R sib pos) :=
  sem_fail hash L x R sib pos

/-- **TEETH — the spec is TWO-VALUED.** A PRESENT key (`100 ∈ [100,300]`) is NOT a non-member, so the
`⟺`'s conclusion genuinely discriminates (a `True`/`P → P` bridge could not). Reuses the committed
`sem_needs_bracketing`. -/
theorem accepts_sound_teeth : ¬ NonMember ([100, 300] : List ℤ) 100 :=
  sem_needs_bracketing

/-- **THE `⟺` RUN END-TO-END on an inhabited instance.** `AirAccepts … [100,300] 200` holds (via the
`←` completeness leg through `nonRevocation_accepts_iff`), and `nonRevocation_accepts_sound` turns the
descriptor's acceptance into the genuine `200 ∉ [100,300]`. Not a hollow green. -/
theorem accepts_iff_demo : NonMember ([100, 300] : List ℤ) 200 := by
  have hsorted : Sorted ([100, 300] : List ℤ) := by simp [Sorted, List.pairwise_cons]
  have hwin : WindowBracketed ([100, 300] : List ℤ) 200 :=
    ⟨100, 300, ⟨[], [], rfl⟩, by norm_num, by norm_num,
      by rw [show HALF_P_MINUS_1 = 1006632959 from rfl]; norm_num,
      by rw [show HALF_P_MINUS_1 = 1006632959 from rfl]; norm_num⟩
  have haccepts : AirAccepts (fun xs => xs.foldl (fun a v => a * 1000 + v) 0) [100, 300] 200 :=
    (nonRevocation_accepts_iff _ _ _).mpr hwin
  exact nonRevocation_accepts_sound hsorted haccepts

#assert_axioms carrier_load_bearing
#assert_axioms gate_load_bearing
#assert_axioms accepts_iff_demo

end Dregg2.Circuit.Emit.NonRevocationRefineBridge

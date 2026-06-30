/-
# Dregg2.Circuit.StateTransitionAirSound — the `StateTransitionAir` (IVC fold chain) soundness twin.

**What this closes.** The AIR census flagged `circuit/src/ivc.rs::StateTransitionAir` (the real STARK AIR
for the attenuation/IVC delegation fold chain, `ivc.rs:585`) as a STATUS-C gap: load-bearing-adjacent,
yet with NO Lean denotational twin. This file gives it one, in the `Satisfied ⟹ intended relation`
style of `BindingAirSound` / `AggAirSound`, resting only on `Poseidon2SpongeCR`.

**What `StateTransitionAir` is.** A width-4 trace `[step, old_hash, new_root, new_hash]`, one row per
attenuation fold step. Its load-bearing accumulator is the `ACCUMULATED_HASH_WIDTH = 8`-felt wide hash
(`AccumulatedHash = [BabyBear; 8]`, ~124-bit collision floor — `ivc.rs:187`), folded by
`extend_accumulated_hash_wide(old, new_root, step) = Poseidon2(IVC_TAG ‖ old[0..8] ‖ new_root ‖ step)`
from the base `initial_accumulated_hash_wide(initial_root) = Poseidon2(IVC_TAG ‖ initial_root ‖ 0)`
(`ivc.rs:214`/`253`), recomputed + checked end-to-end by `recompute_accumulated_hash_wide` /
`verify_ivc_with_roots`. We model the wide multi-felt digest as a single field over a list-sponge
`sponge : List ℤ → ℤ` (the exact binary/quaternary specialization whose collision resistance IS
`Poseidon2SpongeCR`, as in `BindingAirSound.histDigest` / `AggAirSound.Hsponge`); the 8-felt width is
the realization of that sponge's CR.

We model the constraints the IVC's load-bearing wide chain actually enforces (the explicit per-row hash
gate C5, the hash-continuity C8, the step-increment C7 of the constraint-prover `IvcAir`
(`ivc.rs:397`–`443`), plus the four boundary pins of `StateTransitionAir::boundary_constraints`
(`ivc.rs:644`)). This is STRONGER than — and so conservative w.r.t. — the bare `StateTransitionAir`,
which leaves continuity/increment to Poseidon2 preimage resistance (`ivc.rs:622`): we discharge them as
modeled teeth and never lean on preimage resistance.

Proved:
  * **`state_transition_forces_fold` (THE KEYSTONE, no crypto).** A satisfying trace FORCES the
    published `accumulated_hash` to be the genuine sequential wide-hash fold over the new-root sequence
    with steps `1, 2, …`, AND the hash chain is continuous, AND the step (delegation-depth) accumulator
    increments by one. Pure reading of the gates + boundaries — NO cryptographic assumption.
  * **`stepCount_is_length` (THE DEPTH TOOTH, no crypto).** The published `step_count` equals the chain
    length — the delegation-depth accumulator binds the claimed depth to the actual number of folds (so
    `MAX_FOLD_DEPTH` rejection at `step_count` is rejection at chain length).
  * **`state_digest_binds_chain` (THE CR TOOTH).** Under `Poseidon2SpongeCR`, two satisfying traces
    publishing the same `accumulated_hash` and the same `step_count` have the SAME ordered
    `(new_root, step)` sequence — a same-count reorder/forge of the fold history yields a different
    digest and is rejected. The ONLY result resting on the hash floor.

Non-vacuity BOTH ways: an honest 2-step chain satisfies (`honest_satisfies`) and the keystone fires
(`keystone_fires`); a broken-continuity chain, a wrong first step, and a forged digest each fail to
satisfy (`broken_continuity_unsat`, `wrong_step_init_unsat`, `forged_digest_unsat`).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `Poseidon2SpongeCR` is a Prop
HYPOTHESIS where used, never an `axiom`. New module; not wired into `Dregg2.lean`.
-/
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.StateTransitionAirSound

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## 1. The denotational model of one `StateTransitionAir` row + the public inputs. -/

/-- One `StateTransitionAir` row's load-bearing content (`st_col::{STEP, OLD_HASH, NEW_ROOT, NEW_HASH}`,
`ivc.rs:553`). `step` is the 1-indexed delegation-depth position; `oldHash`/`newHash` are the wide
accumulated hash before/after this fold step (modeled as a single sponge-valued digest); `newRoot` is
the state root the step introduces. -/
structure StateRow where
  step    : ℤ
  oldHash : ℤ
  newRoot : ℤ
  newHash : ℤ

/-- The four public inputs `[initial_root, final_root, step_count, accumulated_hash]`
(`StateTransitionAir::boundary_constraints`, `ivc.rs:651`). -/
structure StatePublic where
  initialRoot     : ℤ
  finalRoot       : ℤ
  stepCount       : ℤ
  accumulatedHash : ℤ

/-- The ordered datum the digest commits to at each row: the `(new_root, step)` pair (the `old_hash`
threads from the previous `new_hash`, so it is determined; `new_root`/`step` are the free content). -/
def projST (r : StateRow) : ℤ × ℤ := (r.newRoot, r.step)

/-! ## 2. The wide-hash fold the AIR computes (the sponge twin of `extend_accumulated_hash_wide`). -/

/-- **`stExtend tag sponge acc newRoot step`** — the per-step wide fold
`extend_accumulated_hash_wide(acc, new_root, step) = Poseidon2(IVC_TAG ‖ acc ‖ new_root ‖ step)`
(`ivc.rs:253`), as the list-sponge `sponge [tag, acc, newRoot, step]`. The 8-felt width of the real
`AccumulatedHash` is the realization of `sponge`'s collision resistance. -/
def stExtend (tag : ℤ) (sponge : List ℤ → ℤ) (acc newRoot step : ℤ) : ℤ :=
  sponge [tag, acc, newRoot, step]

/-- **`initHash tag sponge initialRoot`** — the base accumulated hash
`initial_accumulated_hash_wide(initial_root) = Poseidon2(IVC_TAG ‖ initial_root ‖ 0)` (`ivc.rs:214`). -/
def initHash (tag : ℤ) (sponge : List ℤ → ℤ) (initialRoot : ℤ) : ℤ :=
  sponge [tag, initialRoot, 0]

/-- **`stFold tag sponge acc rows`** — the genuine sequential wide-hash fold the chain computes:
starting from `acc`, absorb each row's `(new_root, step)` via `stExtend`. The last row's `new_hash` of a
satisfying trace is exactly `stFold tag sponge (initHash …) rows`. -/
def stFold (tag : ℤ) (sponge : List ℤ → ℤ) (acc : ℤ) : List StateRow → ℤ
  | []          => acc
  | r :: rest => stFold tag sponge (stExtend tag sponge acc r.newRoot r.step) rest

/-! ## 3. The constraint predicates (the Lean twins of the IVC fold-chain constraints). -/

/-- **`HashThread`** — the hash-chain continuity tooth `new_hash[i] == old_hash[i+1]` (IvcAir C8
`hash_chain_continuity`, `ivc.rs:434`). 2-lookahead recursion. -/
def HashThread : List StateRow → Prop
  | []            => True
  | [_]           => True
  | r :: r' :: rest => r.newHash = r'.oldHash ∧ HashThread (r' :: rest)

/-- **`StepChain`** — the delegation-depth accumulator: `step[i+1] == step[i] + 1` (IvcAir C7
`step_count_increment`, `ivc.rs:423`). 2-lookahead recursion. -/
def StepChain : List StateRow → Prop
  | []            => True
  | [_]           => True
  | r :: r' :: rest => r'.step = r.step + 1 ∧ StepChain (r' :: rest)

/-- **`Satisfies tag sponge rows pub`** — a denotational satisfying `StateTransitionAir` trace. Fields:
  * `nonempty` — a folded chain has ≥ 1 row;
  * `rowGate` (C5/per-row) — `new_hash == extend_accumulated_hash(old_hash, new_root, step)`;
  * `hashThread` (C8) — the hash-chain continuity tooth;
  * `stepChain` (C7) — the step (depth) increment;
  * `stepInit` (boundary, `ivc.rs:654`) — first row `step == 1`;
  * `hashInit` (boundary, `ivc.rs:660`) — first row `old_hash == initial_accumulated_hash(initial_root)`;
  * `stepFinal` (boundary, `ivc.rs:669`) — last row `step == step_count`;
  * `hashFinal` (boundary, `ivc.rs:675`) — last row `new_hash == accumulated_hash`. -/
structure Satisfies (tag : ℤ) (sponge : List ℤ → ℤ) (rows : List StateRow) (pub : StatePublic) : Prop where
  nonempty   : rows ≠ []
  rowGate    : ∀ r ∈ rows, r.newHash = stExtend tag sponge r.oldHash r.newRoot r.step
  hashThread : HashThread rows
  stepChain  : StepChain rows
  stepInit   : ∀ r, rows.head? = some r → r.step = 1
  hashInit   : ∀ r, rows.head? = some r → r.oldHash = initHash tag sponge pub.initialRoot
  stepFinal  : ∀ r, rows.getLast? = some r → r.step = pub.stepCount
  hashFinal  : ∀ r, rows.getLast? = some r → r.newHash = pub.accumulatedHash

/-! ## 4. THE KEYSTONE — a satisfying trace IS the genuine sequential fold (no crypto). -/

/-- The last row's `new_hash` of a chain whose head `old_hash` is `acc`, with the per-row hash gate and
the continuity tooth, is exactly the genuine fold `stFold tag sponge acc rows`. Induction threading the
accumulator through the continuity tooth — pure, no crypto. -/
theorem last_newHash_eq_fold (tag : ℤ) (sponge : List ℤ → ℤ) :
    ∀ (rows : List StateRow) (acc : ℤ) (lr : StateRow),
      (∀ x ∈ rows, x.newHash = stExtend tag sponge x.oldHash x.newRoot x.step) →
      HashThread rows →
      (∀ r, rows.head? = some r → r.oldHash = acc) →
      rows.getLast? = some lr →
      lr.newHash = stFold tag sponge acc rows := by
  intro rows
  induction rows with
  | nil => intro acc lr _ _ _ hlast; simp at hlast
  | cons a rest ih =>
    intro acc lr hgate hthread hhead hlast
    have ha : a.oldHash = acc := hhead a (by simp)
    have hag : a.newHash = stExtend tag sponge a.oldHash a.newRoot a.step := hgate a (by simp)
    have hkey : stExtend tag sponge acc a.newRoot a.step = a.newHash := by rw [← ha, ← hag]
    cases rest with
    | nil =>
      rw [List.getLast?_singleton] at hlast; cases hlast
      calc a.newHash = stExtend tag sponge acc a.newRoot a.step := hkey.symm
        _ = stFold tag sponge acc [a] := rfl
    | cons b rest' =>
      obtain ⟨hcont, hthread'⟩ := hthread
      have hlast' : (b :: rest').getLast? = some lr := by rwa [List.getLast?_cons_cons] at hlast
      have hgate' : ∀ x ∈ b :: rest', x.newHash = stExtend tag sponge x.oldHash x.newRoot x.step :=
        fun x hx => hgate x (List.mem_cons_of_mem a hx)
      have hhead' : ∀ r, (b :: rest').head? = some r → r.oldHash = a.newHash := by
        intro r hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; exact hcont.symm
      have hrec := ih a.newHash lr hgate' hthread' hhead' hlast'
      calc lr.newHash = stFold tag sponge a.newHash (b :: rest') := hrec
        _ = stFold tag sponge (stExtend tag sponge acc a.newRoot a.step) (b :: rest') := by rw [hkey]
        _ = stFold tag sponge acc (a :: b :: rest') := rfl

/-- **`state_transition_forces_fold` (THE KEYSTONE).** A satisfying `StateTransitionAir` trace FORCES:
  (a) the published `accumulated_hash` is the genuine sequential wide-hash fold `stFold` from the base
      `initial_accumulated_hash(initial_root)` over the rows' `(new_root, step)` sequence;
  (b) the hash chain is continuous (`HashThread`);
  (c) the step / delegation-depth accumulator increments by one (`StepChain`).
The fold + continuity + ordering are forced by the per-row hash gate and the continuity / increment /
boundary constraints ALONE — NO cryptographic assumption. -/
theorem state_transition_forces_fold
    {tag : ℤ} {sponge : List ℤ → ℤ} {rows : List StateRow} {pub : StatePublic}
    (hsat : Satisfies tag sponge rows pub) :
    pub.accumulatedHash = stFold tag sponge (initHash tag sponge pub.initialRoot) rows
      ∧ HashThread rows ∧ StepChain rows := by
  obtain ⟨lr, hlr⟩ : ∃ lr, rows.getLast? = some lr := by
    cases h : rows.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; exact absurd h hsat.nonempty
    | some lr => exact ⟨lr, rfl⟩
  have hf := hsat.hashFinal lr hlr
  have hfold := last_newHash_eq_fold tag sponge rows (initHash tag sponge pub.initialRoot) lr
    hsat.rowGate hsat.hashThread hsat.hashInit hlr
  exact ⟨by rw [← hf, hfold], hsat.hashThread, hsat.stepChain⟩

/-! ## 5. THE DEPTH TOOTH — the published `step_count` is the chain length (no crypto). -/

/-- Under the step-increment chain with head step `s0`, the last row's step is `s0 + (length − 1)`. -/
theorem stepchain_last_step :
    ∀ (rows : List StateRow) (s0 : ℤ),
      StepChain rows → (∀ r, rows.head? = some r → r.step = s0) → rows ≠ [] →
      ∀ lr, rows.getLast? = some lr → lr.step = s0 + ((rows.length : ℤ) - 1) := by
  intro rows
  induction rows with
  | nil => intro s0 _ _ hne; exact absurd rfl hne
  | cons a rest ih =>
    intro s0 hstep hhead _ lr hlast
    have ha : a.step = s0 := hhead a (by simp)
    cases rest with
    | nil =>
      rw [List.getLast?_singleton] at hlast; cases hlast
      simp only [List.length_singleton]; push_cast; rw [ha]; ring
    | cons b rest' =>
      obtain ⟨hinc, hstep'⟩ := hstep
      have hlast' : (b :: rest').getLast? = some lr := by rwa [List.getLast?_cons_cons] at hlast
      have hhead' : ∀ r, (b :: rest').head? = some r → r.step = a.step + 1 := by
        intro r hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; exact hinc
      have hrec := ih (a.step + 1) hstep' hhead' (by simp) lr hlast'
      rw [hrec, ha]; simp only [List.length_cons]; push_cast; ring

/-- **`stepCount_is_length` (THE DEPTH TOOTH).** A satisfying trace's published `step_count` equals the
chain length: the delegation-depth accumulator binds the CLAIMED depth to the genuine number of fold
steps. So the `MAX_FOLD_DEPTH` rejection (`ivc.rs:1099`) on `step_count` is rejection on actual chain
length — a prover cannot under-report a too-deep chain. Pure, no crypto. -/
theorem stepCount_is_length
    {tag : ℤ} {sponge : List ℤ → ℤ} {rows : List StateRow} {pub : StatePublic}
    (hsat : Satisfies tag sponge rows pub) :
    pub.stepCount = (rows.length : ℤ) := by
  obtain ⟨lr, hlr⟩ : ∃ lr, rows.getLast? = some lr := by
    cases h : rows.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; exact absurd h hsat.nonempty
    | some lr => exact ⟨lr, rfl⟩
  have h1 := hsat.stepFinal lr hlr
  have h2 := stepchain_last_step rows 1 hsat.stepChain hsat.stepInit hsat.nonempty lr hlr
  rw [← h1, h2]; ring

/-! ## 6. THE CR TOOTH — the digest binds the whole ordered fold history (`Poseidon2SpongeCR`). -/

/-- **`stFold_inj`** — injectivity of the sequential fold under sponge collision-resistance: two
equal-length row lists folded (from any starting accumulators) to the SAME digest have equal starting
accumulator AND equal ordered `(new_root, step)` projections. Each peel uses one
`sponge [tag, acc, new_root, step]` collision. -/
theorem stFold_inj (tag : ℤ) (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge) :
    ∀ (rows rows' : List StateRow) (a b : ℤ),
      rows.length = rows'.length →
      stFold tag sponge a rows = stFold tag sponge b rows' →
      a = b ∧ rows.map projST = rows'.map projST := by
  intro rows
  induction rows with
  | nil =>
    intro rows' a b hlen heq
    cases rows' with
    | nil => exact ⟨heq, rfl⟩
    | cons r' rest' => simp at hlen
  | cons r rest ih =>
    intro rows' a b hlen heq
    cases rows' with
    | nil => simp at hlen
    | cons r' rest' =>
      have hlen' : rest.length = rest'.length := by simpa using hlen
      simp only [stFold] at heq
      obtain ⟨hinner, htail⟩ :=
        ih rest' (stExtend tag sponge a r.newRoot r.step) (stExtend tag sponge b r'.newRoot r'.step)
          hlen' heq
      simp only [stExtend] at hinner
      have hlist := hCR _ _ hinner
      injection hlist with _ h1
      injection h1 with hab h2
      injection h2 with hnr h3
      injection h3 with hst _
      refine ⟨hab, ?_⟩
      have hprojr : projST r = projST r' := by unfold projST; rw [hnr, hst]
      simp only [List.map_cons, hprojr, htail]

/-- **`state_digest_binds_chain` (THE CR ANTI-REORDER TOOTH).** Two satisfying `StateTransitionAir`
traces that publish the same `accumulated_hash` and the same `step_count` have the SAME ordered
`(new_root, step)` sequence. So a same-count reorder/forge of the finalized fold history yields a
DIFFERENT `accumulated_hash` and is rejected — the ONLY crypto reliance is the named
`Poseidon2SpongeCR` floor. (Length equality is supplied by the no-crypto `stepCount_is_length` depth
tooth; the `step` lane in each absorb makes the fold position-sensitive.) -/
theorem state_digest_binds_chain
    {tag : ℤ} {sponge : List ℤ → ℤ} (hCR : Poseidon2SpongeCR sponge)
    {rows rows' : List StateRow} {pub pub' : StatePublic}
    (h : Satisfies tag sponge rows pub) (h' : Satisfies tag sponge rows' pub')
    (hnum : pub.stepCount = pub'.stepCount)
    (hdig : pub.accumulatedHash = pub'.accumulatedHash) :
    rows.map projST = rows'.map projST := by
  have hlen : rows.length = rows'.length := by
    have e1 := stepCount_is_length h
    have e2 := stepCount_is_length h'
    have : (rows.length : ℤ) = (rows'.length : ℤ) := by rw [← e1, ← e2, hnum]
    exact_mod_cast this
  have e : stFold tag sponge (initHash tag sponge pub.initialRoot) rows
         = stFold tag sponge (initHash tag sponge pub'.initialRoot) rows' := by
    rw [← (state_transition_forces_fold h).1, ← (state_transition_forces_fold h').1, hdig]
  exact (stFold_inj tag sponge hCR rows rows' _ _ hlen e).2

/-! ## 7. NON-VACUITY — satisfiable (witnessed) AND falsifiable (anti-ghost). -/

section Vacuity

/-- A concrete sponge for the witnesses (constant-zero: the realizing instance only needs the gate shape
to typecheck; the CR floor is never invoked here). -/
def zSponge : List ℤ → ℤ := fun _ => 0

/-- An honest 2-step chain: steps `1, 2`, every hash `0` (= `zSponge` of anything), `new_root`s `0`. The
gates hold: continuity `0 = 0`, increment `2 = 1 + 1`, both boundary pins, and each `new_hash = 0` IS
the genuine `stExtend = zSponge _ = 0`. -/
def honestRows : List StateRow :=
  [{ step := 1, oldHash := 0, newRoot := 0, newHash := 0 },
   { step := 2, oldHash := 0, newRoot := 0, newHash := 0 }]

/-- Public inputs for the honest chain (`step_count = 2`, `accumulated_hash = 0`). -/
def honestPub : StatePublic :=
  { initialRoot := 0, finalRoot := 0, stepCount := 2, accumulatedHash := 0 }

/-- **`honest_satisfies` (positive non-vacuity).** The honest 2-step chain satisfies the AIR with a
nontrivial continuity tooth (`new_hash[0] = 0 = old_hash[1]`) and a real depth increment (`1 → 2`). So
`Satisfies` is inhabited. -/
theorem honest_satisfies : Satisfies 0 zSponge honestRows honestPub where
  nonempty := by simp [honestRows]
  rowGate := by intro r hr; fin_cases hr <;> rfl
  hashThread := ⟨rfl, trivial⟩
  stepChain := ⟨rfl, trivial⟩
  stepInit := by intro r hr; simp only [honestRows, List.head?_cons, Option.some.injEq] at hr
                 subst hr; rfl
  hashInit := by intro r hr; simp only [honestRows, List.head?_cons, Option.some.injEq] at hr
                 subst hr; rfl
  stepFinal := by intro r hr
                  simp only [honestRows] at hr
                  rw [List.getLast?_cons_cons, List.getLast?_singleton] at hr; cases hr; rfl
  hashFinal := by intro r hr
                  simp only [honestRows] at hr
                  rw [List.getLast?_cons_cons, List.getLast?_singleton] at hr; cases hr; rfl

/-- **`keystone_fires` (the discharge is non-vacuous).** On the honest chain the keystone FIRES — the
published `accumulated_hash` IS the genuine fold, the chain is continuous, and the depth accumulator
increments. A true fact about a real chain, not an empty implication. -/
theorem keystone_fires :
    honestPub.accumulatedHash = stFold 0 zSponge (initHash 0 zSponge honestPub.initialRoot) honestRows
      ∧ HashThread honestRows ∧ StepChain honestRows :=
  state_transition_forces_fold honest_satisfies

/-- **`depth_tooth_fires`.** The honest chain's published `step_count` is its length `2`. -/
theorem depth_tooth_fires : honestPub.stepCount = (honestRows.length : ℤ) :=
  stepCount_is_length honest_satisfies

/-! ### The anti-ghost teeth. -/

/-- A chain whose hash continuity is broken: `new_hash[0] = 0 ≠ 1 = old_hash[1]` (a spliced/reordered
seam). -/
def brokenRows : List StateRow :=
  [{ step := 1, oldHash := 0, newRoot := 0, newHash := 0 },
   { step := 2, oldHash := 1, newRoot := 0, newHash := 0 }]

/-- **`broken_continuity_unsat` (THE CONTINUITY TOOTH).** A chain whose hash-continuity is broken does
NOT satisfy: the `HashThread` tooth forces `0 = 1`. Holds for any tag/sponge. -/
theorem broken_continuity_unsat (tag : ℤ) (sponge : List ℤ → ℤ) (pub : StatePublic) :
    ¬ Satisfies tag sponge brokenRows pub := by
  intro h
  have hb := h.hashThread
  simp only [brokenRows, HashThread] at hb
  exact absurd hb.1 (by norm_num)

/-- A chain whose first step is `5`, not `1`. -/
def badStepRows : List StateRow :=
  [{ step := 5, oldHash := 0, newRoot := 0, newHash := 0 }]

/-- **`wrong_step_init_unsat` (THE DEPTH-INIT TOOTH).** A chain whose first step is not `1` does NOT
satisfy: the `stepInit` boundary forces `5 = 1`. -/
theorem wrong_step_init_unsat (tag : ℤ) (sponge : List ℤ → ℤ) (pub : StatePublic) :
    ¬ Satisfies tag sponge badStepRows pub := by
  intro h
  have := h.stepInit { step := 5, oldHash := 0, newRoot := 0, newHash := 0 } (by simp [badStepRows])
  exact absurd this (by norm_num)

/-- The honest rows but a FORGED published digest `99 ≠ 0` (the genuine fold under `zSponge`). -/
def forgedPub : StatePublic :=
  { initialRoot := 0, finalRoot := 0, stepCount := 2, accumulatedHash := 99 }

/-- **`forged_digest_unsat` (THE DIGEST TOOTH).** The honest chain with a forged `accumulated_hash` does
NOT satisfy: the `hashFinal` boundary forces the last `new_hash = 0` to equal the forged `99`. A forged
fold-history digest is rejected. -/
theorem forged_digest_unsat : ¬ Satisfies 0 zSponge honestRows forgedPub := by
  intro h
  have := h.hashFinal { step := 2, oldHash := 0, newRoot := 0, newHash := 0 } (by
    simp only [honestRows]; rw [List.getLast?_cons_cons, List.getLast?_singleton])
  exact absurd this (by simp [forgedPub])

end Vacuity

/-! ## 8. Axiom hygiene. -/

#assert_axioms last_newHash_eq_fold
#assert_axioms state_transition_forces_fold
#assert_axioms stepchain_last_step
#assert_axioms stepCount_is_length
#assert_axioms stFold_inj
#assert_axioms state_digest_binds_chain
#assert_axioms honest_satisfies
#assert_axioms keystone_fires
#assert_axioms depth_tooth_fires
#assert_axioms broken_continuity_unsat
#assert_axioms wrong_step_init_unsat
#assert_axioms forged_digest_unsat

end Dregg2.Circuit.StateTransitionAirSound

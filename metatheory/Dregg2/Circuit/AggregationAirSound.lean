/-
# Dregg2.Circuit.AggregationAirSound — the `AggregationAir` (Poseidon2 hash-chain aggregation) twin.

**What this closes.** The AIR census flagged `circuit/src/plonky3_recursion.rs::AggregationAir`
(`plonky3_recursion.rs:40`) as a STATUS-C gap: a Poseidon2 hash-chain aggregation AIR with no Lean
denotational twin. This file gives it one, in the `Satisfied ⟹ intended relation` style of
`BindingAirSound` / `AggAirSound`, resting only on `Poseidon2SpongeCR`.

**An honest reading of the real `eval` (the load-bearing finding).** `AggregationAir` is documented as a
width-4 running accumulator `(acc_in, leaf, root, acc_out)` with
`acc_out = hash_4_to_1([acc_in, leaf, root, step_index])` (the layout comment, `plonky3_recursion.rs:32`).
But its actual `Air::eval` (`plonky3_recursion.rs:58`) enforces ONLY three constraints — first-row
`acc_in = pv0`, last-row `acc_out = pv1`, and chain continuity `acc_out[i] = acc_in[i+1]` — and does NOT
constrain `acc_out` to the Poseidon2 hash at all. This matches its role: a "deliberately minimal,
self-contained AIR … borrowed as a generic 'some AIR' smoke wrap" for the recursion-shape /
VK-pin-negative tests (`plonky3_recursion.rs:8`, `circuit-prove/tests/ivc_turn_chain_rotated.rs:490`).
The LIVE whole-chain aggregation rides the real `emberian/plonky3-recursion` fork via
`circuit-prove/src/ivc_turn_chain.rs` + `joint_turn_recursive.rs`, NOT this scaffold AIR.

We therefore model BOTH layers, honestly separated:
  * **Bare layer** (`SatBare`, `agg_bare_endpoints`) — EXACTLY what `eval` enforces: an accumulator
    chain pinned to `init` at the head and `final` at the tail, continuous in between. No hash gate, so
    NO binding of the published accumulator to the genuine history. This is the faithful twin of the
    scaffold as it stands.
  * **Hashed layer** (`SatHashed`, `agg_chain_is_genuine_hash_fold`, `agg_digest_binds_history`) — the
    bare layer PLUS the documented/real per-row Poseidon2 gate `acc_out = sponge[acc_in, leaf, root,
    idx]` (the relation a genuine aggregation AIR — the `eval` `step_index` lane, the live fork, the
    sibling `JointTurnAggregationAir` — enforces). Under it the published final accumulator IS the
    genuine ordered hash fold, and the digest binds the whole ordered `(leaf, root, idx)` history.

Proved:
  * **`agg_bare_endpoints` (no crypto).** A satisfying bare trace pins head `acc_in = init` and tail
    `acc_out = final`, with a continuous accumulator. (All the scaffold's `eval` gives.)
  * **`agg_chain_is_genuine_hash_fold` (THE KEYSTONE, no crypto).** A satisfying HASHED trace FORCES the
    published `final_accumulator` to be the genuine ordered Poseidon2 hash fold over the rows'
    `(leaf, root, idx)` sequence from `init`. Pure reading of the gates — NO crypto.
  * **`agg_digest_binds_history` (THE CR TOOTH).** Under `Poseidon2SpongeCR`, two satisfying hashed
    traces of equal length, same `init` and same published `final_accumulator`, have the SAME ordered
    `(leaf, root, idx)` sequence — a reorder/forge is rejected; the `idx` lane makes it position-bound.
    The ONLY result resting on the hash floor.

Non-vacuity BOTH ways: an honest hashed chain satisfies (`honest_satHashed`) and the keystone fires
(`keystone_fires`); broken continuity and a forged final accumulator each fail to satisfy
(`broken_continuity_unsat`, `forged_final_unsat`).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `Poseidon2SpongeCR` is a Prop
HYPOTHESIS where used, never an `axiom`. Imported into `Dregg2.lean` (in the trusted, axiom-audited closure).
-/
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.AggregationAirSound

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## 1. The denotational model of one `AggregationAir` row + the public inputs. -/

/-- One `AggregationAir` row (width-4 layout, `plonky3_recursion.rs:28`): the accumulator before
(`acc_in`, col 0), the inner-proof `leaf`/`root` public values (cols 1/2), the `step_index` `idx` (the
documented hash input), and the accumulator after (`acc_out`, col 3). -/
structure AggRow where
  accIn  : ℤ
  leaf   : ℤ
  root   : ℤ
  idx    : ℤ
  accOut : ℤ

/-- The two public inputs `[initial_accumulator, final_accumulator]` (`num_public_values = 2`,
`plonky3_recursion.rs:47`). The real `initial_accumulator` is `0`. -/
structure AggPublic where
  initAcc  : ℤ
  finalAcc : ℤ

/-- The ordered datum a genuine aggregation digest commits to per row: `(leaf, root, idx)` (the `acc_in`
threads from the previous `acc_out`, so it is determined; the `idx`/`step_index` lane makes the position
part of the committed datum). -/
def projAgg (r : AggRow) : ℤ × ℤ × ℤ := (r.leaf, r.root, r.idx)

/-! ## 2. The continuity tooth (the `eval` transition constraint). -/

/-- **`AccThread`** — the chain-continuity tooth `acc_out[i] == acc_in[i+1]`
(`AggregationAir::eval` constraint 3, `plonky3_recursion.rs:81`). 2-lookahead recursion. -/
def AccThread : List AggRow → Prop
  | []            => True
  | [_]           => True
  | r :: r' :: rest => r.accOut = r'.accIn ∧ AccThread (r' :: rest)

/-! ## 3. The BARE model — EXACTLY the three constraints `AggregationAir::eval` enforces. -/

/-- **`SatBare rows pub`** — the EXACT `AggregationAir::eval` constraints, nothing more:
  * `nonempty` — a nonempty trace;
  * `firstAcc` (C1) — head `acc_in == initial_accumulator`;
  * `lastAcc` (C2) — tail `acc_out == final_accumulator`;
  * `accThread` (C3) — the continuity tooth.
There is deliberately NO hash gate here, because the real `eval` has none. -/
structure SatBare (rows : List AggRow) (pub : AggPublic) : Prop where
  nonempty  : rows ≠ []
  firstAcc  : ∀ r, rows.head? = some r → r.accIn = pub.initAcc
  lastAcc   : ∀ r, rows.getLast? = some r → r.accOut = pub.finalAcc
  accThread : AccThread rows

/-- **`agg_bare_endpoints` (the bare scaffold's full guarantee, no crypto).** A satisfying bare trace
pins the head `acc_in` to `initial_accumulator` and the tail `acc_out` to `final_accumulator`, with a
continuous accumulator in between. This is ALL `AggregationAir::eval` forces — note it does NOT bind the
published `final_accumulator` to any genuine hash of the inner proofs' `(leaf, root)`, because the bare
AIR has no hash gate. (Modeling the corpse honestly: the binding is supplied by the hashed layer below /
the live recursion fork, not by this scaffold.) -/
theorem agg_bare_endpoints {rows : List AggRow} {pub : AggPublic} (h : SatBare rows pub) :
    (∀ r, rows.head? = some r → r.accIn = pub.initAcc)
      ∧ (∀ r, rows.getLast? = some r → r.accOut = pub.finalAcc)
      ∧ AccThread rows :=
  ⟨h.firstAcc, h.lastAcc, h.accThread⟩

/-! ## 4. The genuine ordered Poseidon2 hash fold (the documented / real-aggregation semantics). -/

/-- **`aggExtend sponge accIn leaf root idx`** — the per-row Poseidon2 gate documented for `AggregationAir`
(`acc_out = hash_4_to_1([acc_in, leaf, root, step_index])`, `plonky3_recursion.rs:32`), as the list-sponge
`sponge [accIn, leaf, root, idx]`. -/
def aggExtend (sponge : List ℤ → ℤ) (accIn leaf root idx : ℤ) : ℤ :=
  sponge [accIn, leaf, root, idx]

/-- **`aggFold sponge acc rows`** — the genuine ordered hash fold: from `acc`, absorb each row's
`(leaf, root, idx)` via `aggExtend`. The last row's `acc_out` of a satisfying hashed trace is exactly
`aggFold sponge init rows`. -/
def aggFold (sponge : List ℤ → ℤ) (acc : ℤ) : List AggRow → ℤ
  | []          => acc
  | r :: rest => aggFold sponge (aggExtend sponge acc r.leaf r.root r.idx) rest

/-- **`SatHashed sponge rows pub`** — the bare AIR PLUS the documented/real per-row Poseidon2 gate
`acc_out == aggExtend sponge acc_in leaf root idx`. This is what a GENUINE Poseidon2 hash-chain
aggregation AIR (the `eval` `step_index` lane wired up, the live fork, `JointTurnAggregationAir`)
enforces. -/
structure SatHashed (sponge : List ℤ → ℤ) (rows : List AggRow) (pub : AggPublic) : Prop where
  bare    : SatBare rows pub
  rowHash : ∀ r ∈ rows, r.accOut = aggExtend sponge r.accIn r.leaf r.root r.idx

/-- The last row's `acc_out` of a chain whose head `acc_in` is `acc`, with the per-row hash gate and the
continuity tooth, is exactly the genuine fold `aggFold sponge acc rows`. Induction threading the
accumulator through the continuity tooth — pure, no crypto. -/
theorem last_accOut_eq_fold (sponge : List ℤ → ℤ) :
    ∀ (rows : List AggRow) (acc : ℤ) (lr : AggRow),
      (∀ x ∈ rows, x.accOut = aggExtend sponge x.accIn x.leaf x.root x.idx) →
      AccThread rows →
      (∀ r, rows.head? = some r → r.accIn = acc) →
      rows.getLast? = some lr →
      lr.accOut = aggFold sponge acc rows := by
  intro rows
  induction rows with
  | nil => intro acc lr _ _ _ hlast; simp at hlast
  | cons a rest ih =>
    intro acc lr hgate hthread hhead hlast
    have ha : a.accIn = acc := hhead a (by simp)
    have hag : a.accOut = aggExtend sponge a.accIn a.leaf a.root a.idx := hgate a (by simp)
    have hkey : aggExtend sponge acc a.leaf a.root a.idx = a.accOut := by rw [← ha, ← hag]
    cases rest with
    | nil =>
      rw [List.getLast?_singleton] at hlast; cases hlast
      calc a.accOut = aggExtend sponge acc a.leaf a.root a.idx := hkey.symm
        _ = aggFold sponge acc [a] := rfl
    | cons b rest' =>
      obtain ⟨hcont, hthread'⟩ := hthread
      have hlast' : (b :: rest').getLast? = some lr := by rwa [List.getLast?_cons_cons] at hlast
      have hgate' : ∀ x ∈ b :: rest', x.accOut = aggExtend sponge x.accIn x.leaf x.root x.idx :=
        fun x hx => hgate x (List.mem_cons_of_mem a hx)
      have hhead' : ∀ r, (b :: rest').head? = some r → r.accIn = a.accOut := by
        intro r hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; exact hcont.symm
      have hrec := ih a.accOut lr hgate' hthread' hhead' hlast'
      calc lr.accOut = aggFold sponge a.accOut (b :: rest') := hrec
        _ = aggFold sponge (aggExtend sponge acc a.leaf a.root a.idx) (b :: rest') := by rw [hkey]
        _ = aggFold sponge acc (a :: b :: rest') := rfl

/-- **`agg_chain_is_genuine_hash_fold` (THE KEYSTONE, no crypto).** A satisfying HASHED trace FORCES the
published `final_accumulator` to be the genuine ordered Poseidon2 hash fold over the rows'
`(leaf, root, idx)` sequence, started from `initial_accumulator`. So the aggregated accumulator is
provably the real ordered fold of the inner proofs' exposed `(leaf, root)`, not a free claim — forced by
the hash gate + continuity + boundary constraints ALONE, NO crypto. -/
theorem agg_chain_is_genuine_hash_fold
    {sponge : List ℤ → ℤ} {rows : List AggRow} {pub : AggPublic}
    (hsat : SatHashed sponge rows pub) :
    pub.finalAcc = aggFold sponge pub.initAcc rows := by
  obtain ⟨lr, hlr⟩ : ∃ lr, rows.getLast? = some lr := by
    cases h : rows.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; exact absurd h hsat.bare.nonempty
    | some lr => exact ⟨lr, rfl⟩
  have hf := hsat.bare.lastAcc lr hlr
  have hfold := last_accOut_eq_fold sponge rows pub.initAcc lr
    hsat.rowHash hsat.bare.accThread hsat.bare.firstAcc hlr
  rw [← hf, hfold]

/-! ## 5. THE CR TOOTH — the digest binds the whole ordered history (`Poseidon2SpongeCR`). -/

/-- **`aggFold_inj`** — injectivity of the ordered hash fold under sponge collision-resistance: two
equal-length row lists folded (from any starting accumulators) to the SAME digest have equal starting
accumulator AND equal ordered `(leaf, root, idx)` projections. Each peel uses one
`sponge [acc, leaf, root, idx]` collision. -/
theorem aggFold_inj (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge) :
    ∀ (rows rows' : List AggRow) (a b : ℤ),
      rows.length = rows'.length →
      aggFold sponge a rows = aggFold sponge b rows' →
      a = b ∧ rows.map projAgg = rows'.map projAgg := by
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
      simp only [aggFold] at heq
      obtain ⟨hinner, htail⟩ :=
        ih rest' (aggExtend sponge a r.leaf r.root r.idx) (aggExtend sponge b r'.leaf r'.root r'.idx)
          hlen' heq
      simp only [aggExtend] at hinner
      have hlist := hCR _ _ hinner
      injection hlist with hab h1
      injection h1 with hleaf h2
      injection h2 with hroot h3
      injection h3 with hidx _
      refine ⟨hab, ?_⟩
      have hprojr : projAgg r = projAgg r' := by unfold projAgg; rw [hleaf, hroot, hidx]
      simp only [List.map_cons, hprojr, htail]

/-- **`agg_digest_binds_history` (THE CR ANTI-REORDER TOOTH).** Two satisfying hashed traces of equal
length, the same `initial_accumulator`, and the same published `final_accumulator`, have the SAME ordered
`(leaf, root, idx)` sequence. So a reorder/forge of the aggregated history yields a DIFFERENT
`final_accumulator` and is rejected — the `idx`/`step_index` lane makes the fold position-sensitive, so
even an equal-endpoint swap is caught. The ONLY crypto reliance is the named `Poseidon2SpongeCR`. -/
theorem agg_digest_binds_history
    {sponge : List ℤ → ℤ} (hCR : Poseidon2SpongeCR sponge)
    {rows rows' : List AggRow} {pub pub' : AggPublic}
    (h : SatHashed sponge rows pub) (h' : SatHashed sponge rows' pub')
    (hlen : rows.length = rows'.length)
    (hinit : pub.initAcc = pub'.initAcc)
    (hfin : pub.finalAcc = pub'.finalAcc) :
    rows.map projAgg = rows'.map projAgg := by
  have e : aggFold sponge pub.initAcc rows = aggFold sponge pub'.initAcc rows' := by
    rw [← agg_chain_is_genuine_hash_fold h, ← agg_chain_is_genuine_hash_fold h', hfin]
  rw [hinit] at e
  exact (aggFold_inj sponge hCR rows rows' _ _ hlen e).2

/-! ## 6. NON-VACUITY — satisfiable (witnessed) AND falsifiable (anti-ghost). -/

section Vacuity

/-- A concrete sponge for the witnesses (constant-zero: only the gate shape need typecheck; the CR floor
is never invoked here). -/
def zSponge : List ℤ → ℤ := fun _ => 0

/-- An honest 2-row aggregation chain: every accumulator `0` (= `zSponge` of anything), `idx`s `0, 1`.
The gates hold: continuity `0 = 0`, both boundary pins (`init = final = 0`), and each `acc_out = 0` IS
the genuine `aggExtend = zSponge _ = 0`. -/
def honestRows : List AggRow :=
  [{ accIn := 0, leaf := 0, root := 0, idx := 0, accOut := 0 },
   { accIn := 0, leaf := 0, root := 0, idx := 1, accOut := 0 }]

/-- Public inputs for the honest chain (`init = final = 0`). -/
def honestPub : AggPublic := { initAcc := 0, finalAcc := 0 }

/-- The honest chain satisfies the BARE AIR (positive non-vacuity for `eval` as it stands). -/
theorem honest_satBare : SatBare honestRows honestPub where
  nonempty := by simp [honestRows]
  firstAcc := by intro r hr; simp only [honestRows, List.head?_cons, Option.some.injEq] at hr
                 subst hr; rfl
  lastAcc := by intro r hr; simp only [honestRows] at hr
                rw [List.getLast?_cons_cons, List.getLast?_singleton] at hr; cases hr; rfl
  accThread := ⟨rfl, trivial⟩

/-- **`honest_satHashed` (positive non-vacuity).** The honest chain also satisfies the HASHED AIR — each
`acc_out = 0` is the genuine ordered fold. So `SatHashed` is inhabited. -/
theorem honest_satHashed : SatHashed zSponge honestRows honestPub where
  bare := honest_satBare
  rowHash := by intro r hr; fin_cases hr <;> rfl

/-- **`keystone_fires` (the discharge is non-vacuous).** On the honest chain the keystone FIRES: the
published `final_accumulator` IS the genuine ordered Poseidon2 hash fold. A true fact about a real chain,
not an empty implication. -/
theorem keystone_fires : honestPub.finalAcc = aggFold zSponge honestPub.initAcc honestRows :=
  agg_chain_is_genuine_hash_fold honest_satHashed

/-! ### The anti-ghost teeth. -/

/-- A chain whose accumulator continuity is broken: `acc_out[0] = 0 ≠ 1 = acc_in[1]` (a spliced/reordered
seam). -/
def brokenRows : List AggRow :=
  [{ accIn := 0, leaf := 0, root := 0, idx := 0, accOut := 0 },
   { accIn := 1, leaf := 0, root := 0, idx := 1, accOut := 0 }]

/-- **`broken_continuity_unsat` (THE CONTINUITY TOOTH).** A chain whose accumulator continuity is broken
does NOT satisfy the bare AIR: the `AccThread` tooth forces `0 = 1`. (A fortiori it fails the hashed
AIR.) -/
theorem broken_continuity_unsat (pub : AggPublic) : ¬ SatBare brokenRows pub := by
  intro h
  have hb := h.accThread
  simp only [brokenRows, AccThread] at hb
  exact absurd hb.1 (by norm_num)

/-- The honest rows but a FORGED published `final_accumulator` `99 ≠ 0` (the genuine fold under
`zSponge`). -/
def forgedPub : AggPublic := { initAcc := 0, finalAcc := 99 }

/-- **`forged_final_unsat` (THE DIGEST TOOTH).** The honest chain with a forged `final_accumulator` does
NOT satisfy: the last-row boundary forces the genuine tail `acc_out = 0` to equal the forged `99`. A
forged aggregated digest is rejected. -/
theorem forged_final_unsat : ¬ SatBare honestRows forgedPub := by
  intro h
  have := h.lastAcc { accIn := 0, leaf := 0, root := 0, idx := 1, accOut := 0 } (by
    simp only [honestRows]; rw [List.getLast?_cons_cons, List.getLast?_singleton])
  exact absurd this (by simp [forgedPub])

end Vacuity

/-! ## 7. Axiom hygiene. -/

#assert_axioms agg_bare_endpoints
#assert_axioms last_accOut_eq_fold
#assert_axioms agg_chain_is_genuine_hash_fold
#assert_axioms aggFold_inj
#assert_axioms agg_digest_binds_history
#assert_axioms honest_satBare
#assert_axioms honest_satHashed
#assert_axioms keystone_fires
#assert_axioms broken_continuity_unsat
#assert_axioms forged_final_unsat

end Dregg2.Circuit.AggregationAirSound

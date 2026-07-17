/-
THE EMBEDDING: the generic-oracle strategy model (`GgmAdaptive.Strat` / `runAux`) connected to
ArkLib's REAL `tSdhAdversary` / `tSdhExperiment`. This is the load-bearing construction that makes
the end-to-end t-SDH GGM theorem escape the vacuity of `∀ A : tSdhAdversary, …` (which is FALSE — a
`Classical.choice`-definable adversary computes discrete logs and wins with probability 1). The
target quantifies over generic **strategies** and applies `embed`; "generic-restricted" = *in the
image of `embed`*.

NOT part of ArkLib. Scratch research file supporting `docs/reference/arklib-kzg-vacuity/`
(END-TO-END-PLAN.md, task D). Built against ArkLib @ `d72f8392` (Lean v4.31.0); imports ArkLib's
REAL `Groups.tSdhAdversary`, `Groups.PowerSrs.generate/tower`, and our `GgmAdaptive` (linear,
pairing-free `Move`) / `GgmArkLibTransport` (`gpow_val_inj_iff`). Nothing is restated.

THE CONSTRUCTION (honest, generic-restricted). `embed strat : tSdhAdversary D` is
`fun srs => pure (runEmbed g₁ D fuel strat srs)`. `runEmbed` receives ONLY the SRS group vectors
(never τ), seeds a `List G₁` handle table from the G₁ tower, interprets `strat`'s linear-combination
moves by REAL group products (`combineG`), answers `strat`'s equality queries by REAL group equality
(`DecidableEq` classically) of the realized handles, and returns the committed `(offset, G₁ elt)`. It
never inverts the encoding — the opacity is discharged by construction (`strat : List Bool → …`
receives only equality booleans). This is exactly why `embed strat` stays within the generic bound:
it can only produce `g₁ ^ (f τ)` with `deg f ≤ D`, so `embed_run_correspondence` — which certifies
`runEmbed` reproduces the SYMBOLIC run's output realized in the group — is the certificate that the
adversary is generic within this deterministic, one-sort, explicit-equality model (a τ-inverting
cheat would break the correspondence). This is an embedded subclass, not a characterization of
all randomized or two-sort generic-group adversaries; in particular `runEmbed` ignores the G₂ leg.

THE CRUX (`embed_run_correspondence`). `runEmbed`'s equality branch compares real group elements
`g₁^(f τ).val =? g₁^(h τ).val`; by INJECTIVITY (`GgmArkLibTransport.gpow_val_inj_iff`) this equals
`f.eval τ =? h.eval τ` = `GgmAdaptive.realAns τ f h`. So the group-table run steps in lockstep with
`runAux (realAns τ)`, threading the table↔polynomial invariant `tableG[i] = g₁^(table[i].eval τ).val`
by induction on fuel (mirroring `runAux`'s recursion). The invariant is seeded because the G₁ tower
`PowerSrs.generate D τ` realizes each seed monomial `X^k` as `g₁^(τ^k)`.

⚑ SCOPE (named honestly). The seed carries `1 ≤ D`: `srsSt D`'s table `[1,X,…,X^D,1,X]` includes the
two "G₂ seed" monomials `1 = X^0`, `X = X^1`, which the *pairing-free* G₁ adversary must realize from
its own G₁ tower `[g₁^(τ^0),…,g₁^(τ^D)]`. `g₁^τ = g₁^(τ^1)` is present exactly when `D ≥ 1`. At
`D = 0` the SRS is `(g₁),(g₂,g₂^τ)` and a G₁-output adversary genuinely CANNOT form `g₁^τ` (no
pairing to move `g₂^τ` into G₁), so the unconditional correspondence is FALSE there — an honest fact
about the interface, not a proof gap. `D ≥ 1` is the meaningful KZG regime.
-/
import GgmArkLibTransport
import GgmRandomEncoding
import ArkLib.Commitments.Functional.KZG.HardnessAssumptions

open Polynomial Groups

namespace GgmEmbed

open GgmCandidate GgmAdaptive GgmRandomEncoding GgmArkLibTransport

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p]
variable {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p]

/-! ## 1. The exponent encoding `E g a = g ^ a.val` as an additive-to-multiplicative morphism.

`E g` sends the field of exponents into the group; the correspondence realizes every handle through
it. Its two morphism laws (over an order-`p` base) are all we need to push `combine`'s field-linear
combination through to `combineG`'s group-linear combination. -/

lemma encode_zero (g : G₁) : g ^ (0 : ZMod p).val = 1 := by simp

omit [PrimeOrderWith G₁ p] in
/-- `E g (a + b) = E g a * E g b`. -/
lemma encode_add {g : G₁} (hord : orderOf g = p) (a b : ZMod p) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [← pow_add]
  exact (Groups.gpow_eq_of_nat_cast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)).symm

omit [PrimeOrderWith G₁ p] in
/-- `E g (c * a) = (E g a) ^ c.val` — scalar multiplication becomes group exponentiation. -/
lemma encode_mul {g : G₁} (hord : orderOf g = p) (c a : ZMod p) :
    g ^ (c * a).val = (g ^ a.val) ^ c.val := by
  rw [← pow_mul]
  exact (Groups.gpow_eq_of_nat_cast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)).symm

/-! ## 2. The group-side linear-combination oracle and the table↔polynomial invariant. -/

/-- The real-group realization of a `Move.lin` move: `∏ᵢ (tableG[idxᵢ]) ^ (cᵢ).val` — the group
product-of-powers that faithfully realizes `GgmAdaptive.combine`'s formal `Σᵢ cᵢ · table[idxᵢ]`. -/
noncomputable def combineG (spec : List (ZMod p × ℕ)) (tableG : List G₁) : G₁ :=
  (spec.map (fun ci => (tableG.getD ci.2 1) ^ ci.1.val)).prod

/-- The table↔polynomial invariant threaded through the run: the group table and the symbolic
polynomial table have equal length and each group handle is the encoding of its polynomial's
evaluation at `τ`. (The pointwise clause holds even off the ends: both default to `1 = g^(0.eval τ)`.) -/
def Inv (g : G₁) (τ : ZMod p) (tableG : List G₁) (table : List ((ZMod p)[X])) : Prop :=
  tableG.length = table.length ∧
    ∀ i, tableG.getD i 1 = g ^ ((table.getD i 0).eval τ).val

/-- **The combine correspondence.** Under the invariant, the group product-of-powers realizes the
encoding of the formal linear combination's evaluation. Induction on the move's index list. -/
lemma combineG_eq {g : G₁} (hord : orderOf g = p) (τ : ZMod p)
    (spec : List (ZMod p × ℕ)) (tableG : List G₁) (table : List ((ZMod p)[X]))
    (hInv : Inv g τ tableG table) :
    combineG spec tableG = g ^ ((combine spec table).eval τ).val := by
  induction spec with
  | nil => simp [combineG, combine]
  | cons ck t ih =>
    have hcomb : combine (ck :: t) table
        = Polynomial.C ck.1 * table.getD ck.2 0 + combine t table := by
      simp [combine, List.map_cons, List.sum_cons]
    rw [combineG, List.map_cons, List.prod_cons, ← combineG, ih, hcomb]
    rw [eval_add, eval_mul, eval_C, encode_add hord, encode_mul hord, hInv.2 ck.2]

/-! ## 3. `runEmbed` — the real-group run, and `embed` — the ArkLib adversary. -/

/-- REAL group equality as a `Bool`, decided classically (an abstract group carries no decision
procedure). This is the query oracle: `strat` learns only this boolean, never a group element. -/
noncomputable def groupEq (x y : G₁) : Bool := @decide (x = y) (Classical.propDecidable _)

/-- **The real-group generic run.** A `List G₁` handle table (no polynomials, no τ), evolved by
`strat`'s moves interpreted as REAL group operations: `Move.lin` appends a `combineG` product,
`Move.query i j` appends the boolean of REAL group equality `tableG[i] = tableG[j]`, the committed
output reads the offset and the output handle out of the table. Mirrors `GgmAdaptive.runAux`'s
recursion exactly. -/
noncomputable def runEmbedAux (g : G₁) (strat : Strat p) :
    ℕ → (List G₁ × List Bool) → Option (ZMod p × G₁)
  | 0, _ => some (0, 1)
  | fuel + 1, (tableG, hist) =>
    match strat hist with
    | Sum.inr (c, k) => some (c, tableG.getD k 1)
    | Sum.inl (Move.lin spec) =>
        runEmbedAux g strat fuel (tableG ++ [combineG spec tableG], hist)
    | Sum.inl (Move.query i j) =>
        runEmbedAux g strat fuel (tableG, hist ++ [groupEq (tableG.getD i 1) (tableG.getD j 1)])

/-- The G₁ seed table: the tower handles `g₁^(τ^k)` (`k ≤ D`) plus the two "G₂ seed" monomials
`1 = X^0` and `X = X^1` realized from the same tower (positions `0` and `1`) — matching `srsSt D`'s
polynomial table `[X^0,…,X^D, 1, X]` entry-for-entry. -/
noncomputable def seedG (srs1 : List G₁) (D : ℕ) : List G₁ :=
  ((List.range (D + 1)).map (fun i => srs1.getD i 1)) ++ [srs1.getD 0 1, srs1.getD 1 1]

/-- **`runEmbed`** — run `strat` against the real-group SRS. A function of the G₁ generator `g₁`
and the SRS alone: it reads only `srs.1` (the G₁ tower), so — being pairing-free — it needs neither
the G₂ generator, nor `srs.2`, nor τ. -/
noncomputable def runEmbed (g₁ : G₁) (D fuel : ℕ) (strat : Strat p)
    (srs : Vector G₁ (D + 1) × Vector G₂ 2) : Option (ZMod p × G₁) :=
  runEmbedAux g₁ strat fuel (seedG srs.1.toList D, [])

/-- **`embed : Strat p → tSdhAdversary D`.** Deterministic, empty-cache; its IMAGE is the
"generic-restricted" adversary class the target theorem quantifies over. Pairing-free: a function of
`g₁` and the SRS only (the G₂ generator is never consulted). -/
noncomputable def embed (g₁ : G₁) (D fuel : ℕ) (strat : Strat p) :
    Groups.tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p) :=
  fun srs => pure (runEmbed g₁ D fuel strat srs)

/-! ## 4. The correspondence: `runEmbedAux` steps in lockstep with `runAux (realAns τ)`. -/

/-- Appending a matching pair of handles preserves the invariant: the new group handle realizes the
new polynomial (`combineG_eq`), and existing handles are untouched. -/
lemma Inv_append {g : G₁} (hord : orderOf g = p) {τ : ZMod p}
    {tableG : List G₁} {table : List ((ZMod p)[X])} (spec : List (ZMod p × ℕ))
    (hInv : Inv g τ tableG table) :
    Inv g τ (tableG ++ [combineG spec tableG]) (table ++ [combine spec table]) := by
  obtain ⟨hlen, hpt⟩ := hInv
  refine ⟨by simp [hlen], fun i => ?_⟩
  rcases lt_trichotomy i tableG.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hpt i
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _),
        List.getD_append_right _ _ _ _ (by rw [hlen]), hlen]
    simp only [Nat.sub_self, List.getD_cons_zero]
    exact combineG_eq hord τ spec tableG table ⟨hlen, hpt⟩
  · rw [List.getD_append_right _ _ _ _ (le_of_lt h),
        List.getD_append_right _ _ _ _ (by rw [← hlen]; exact le_of_lt h)]
    rw [List.getD_eq_default _ _ (by simpa using (by omega : 1 ≤ i - tableG.length)),
        List.getD_eq_default _ _ (by rw [← hlen]; simpa using (by omega : 1 ≤ i - tableG.length))]
    simp

/-- **THE CORRESPONDENCE (induction core).** Under the invariant, `runEmbedAux` on the group table
returns exactly the committed offset of `runAux (realAns τ)` and the real-group encoding of its
committed output polynomial — for the SAME history. The two runs step in lockstep: equality queries
agree because `realAns τ` answers `f.eval τ =? h.eval τ`, which injectivity (`gpow_val_inj_iff`)
aligns with the real group equality `g^(f τ).val =? g^(h τ).val`. -/
lemma runEmbedAux_correspondence {g : G₁} (hord : orderOf g = p) (τ : ZMod p) (strat : Strat p) :
    ∀ (fuel : ℕ) (tableG : List G₁) (table : List ((ZMod p)[X])) (hist : List Bool),
      Inv g τ tableG table →
      runEmbedAux g strat fuel (tableG, hist)
        = some ((runAux (realAns τ) strat fuel ⟨table, hist⟩).1.1,
                g ^ (((runAux (realAns τ) strat fuel ⟨table, hist⟩).1.2).eval τ).val) := by
  intro fuel
  induction fuel with
  | zero =>
    intro tableG table hist hInv
    simp [runEmbedAux, runAux]
  | succ fuel ih =>
    intro tableG table hist hInv
    rcases hdec : strat hist with m | out
    · cases m with
      | lin spec =>
        have e1 : runEmbedAux g strat (fuel + 1) (tableG, hist)
            = runEmbedAux g strat fuel (tableG ++ [combineG spec tableG], hist) := by
          simp only [runEmbedAux, hdec]
        have e2 : runAux (realAns τ) strat (fuel + 1) ⟨table, hist⟩
            = runAux (realAns τ) strat fuel ⟨table ++ [combine spec table], hist⟩ := by
          simp only [runAux, hdec]
        rw [e1, e2]
        exact ih _ _ _ (Inv_append hord spec hInv)
      | query i j =>
        have hans : groupEq (tableG.getD i 1) (tableG.getD j 1)
            = realAns τ (table.getD i 0) (table.getD j 0) := by
          simp only [groupEq, realAns]
          rw [decide_eq_decide, hInv.2 i, hInv.2 j]
          exact gpow_val_inj_iff hord
        have e1 : runEmbedAux g strat (fuel + 1) (tableG, hist)
            = runEmbedAux g strat fuel
                (tableG, hist ++ [groupEq (tableG.getD i 1) (tableG.getD j 1)]) := by
          simp only [runEmbedAux, hdec]
        have e2 : runAux (realAns τ) strat (fuel + 1) ⟨table, hist⟩
            = ((runAux (realAns τ) strat fuel
                  ⟨table, hist ++ [realAns τ (table.getD i 0) (table.getD j 0)]⟩).1,
                (table.getD i 0, table.getD j 0) ::
                  (runAux (realAns τ) strat fuel
                    ⟨table, hist ++ [realAns τ (table.getD i 0) (table.getD j 0)]⟩).2) := by
          simp only [runAux, hdec]
        rw [e1, e2, hans]
        exact ih _ _ _ hInv
    · have e1 : runEmbedAux g strat (fuel + 1) (tableG, hist) = some (out.1, tableG.getD out.2 1) := by
        simp only [runEmbedAux, hdec]
      have e2 : runAux (realAns τ) strat (fuel + 1) ⟨table, hist⟩
          = ((out.1, table.getD out.2 0), []) := by
        simp only [runAux, hdec]
      rw [e1, e2, hInv.2 out.2]

/-! ## 5. The seed invariant and the deliverable correspondence. -/

/-- `getD` of a `List.range`-map at an in-range index. -/
lemma rangeMap_getD_lt {α : Type*} (f : ℕ → α) (n i : ℕ) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  have hlen : i < ((List.range n).map f).length := by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some,
      List.getElem_map, List.getElem_range]

/-- Tower `toList` indexing: the `i`-th tower handle (`i ≤ D`) is `g₁^(τ^i)`. -/
lemma tower_toList_getD {g : G₁} (τ : ZMod p) (D i : ℕ) (h : i < D + 1) :
    (PowerSrs.tower g τ D).toList.getD i 1 = g ^ (τ.val ^ i) := by
  unfold PowerSrs.tower
  rw [Vector.toList_ofFn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dif_pos h]
  rfl

/-- **The seed invariant.** For `srs = generate D τ` with `1 ≤ D`, the G₁ seed table realizes
`srsSt D`'s polynomial table under the encoding: the tower positions cover `X^0,…,X^D`, and the two
"G₂ seed" monomials `1, X` are `g₁^(τ^0), g₁^(τ^1)`. -/
lemma seedG_Inv (g : G₁) (hord : orderOf g = p) (τ : ZMod p) (D : ℕ) (hD : 1 ≤ D) :
    Inv g τ (seedG (PowerSrs.tower g τ D).toList D) (srsSt D).table := by
  have htab : (srsSt (p := p) D).table
      = ((List.range (D + 1)).map (fun i => (X : (ZMod p)[X]) ^ i)) ++ [1, X] := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [seedG, htab]; simp
  · -- realize each seed monomial's evaluation
    have key : ∀ k, k < D + 1 →
        (PowerSrs.tower g τ D).toList.getD k 1 = g ^ ((X ^ k : (ZMod p)[X]).eval τ).val := by
      intro k hk
      rw [tower_toList_getD τ D k hk, eval_pow, eval_X]
      exact Groups.gpow_eq_of_nat_cast_eq hord _ _ (by push_cast [ZMod.natCast_zmod_val]; ring)
    rw [seedG, htab]
    rcases lt_trichotomy i (D + 1) with h | h | h
    · -- first segment: X^i
      rw [List.getD_append _ _ _ _ (by simpa using h),
          List.getD_append _ _ _ _ (by simpa using h),
          rangeMap_getD_lt _ _ _ _ h, rangeMap_getD_lt _ _ _ _ h]
      exact key i h
    · -- position D+1 : the "G₂ seed" 1 = X^0
      subst h
      rw [List.getD_append_right _ _ _ _ (by simp),
          List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero, eval_one]
      have := key 0 (Nat.succ_pos D)
      rw [eval_pow, eval_X, pow_zero] at this
      simpa using this
    · -- positions ≥ D+2 : the "G₂ seed" X (at D+2, needs D ≥ 1) then defaults
      rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map, List.length_range]; omega),
          List.getD_append_right _ _ _ _ (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.length_map, List.length_range]
      rcases Nat.lt_or_ge i (D + 3) with h2 | h2
      · -- i = D + 2 : the "G₂ seed" X = X^1
        have hi : i - (D + 1) = 1 := by omega
        rw [hi]
        simp only [List.getD_cons_succ, List.getD_cons_zero, eval_X]
        have := key 1 (by omega)
        rw [eval_pow, eval_X, pow_one] at this
        exact this
      · -- i ≥ D + 3 : both default
        rw [List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega),
            List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
        simp

omit [PrimeOrderWith G₂ p] in
/-- **THE DELIVERABLE (§2b, verbatim).** `runEmbed` on the real SRS `PowerSrs.generate D τ` returns
the committed offset of the SYMBOLIC run `runOutput (realAns τ) strat fuel (srsSt D)` and the
real-group encoding `g₁ ^ (output.eval τ).val` of its committed output polynomial. This certifies
`embed strat` is genuinely generic (it reproduces the symbolic run realized in the group, never
inverting the encoding), and is the socket the end-to-end composition (task E) consumes. -/
theorem embed_run_correspondence {g₁ : G₁} {g₂ : G₂} (hord : orderOf g₁ = p)
    (D : ℕ) (hD : 1 ≤ D) (τ : ZMod p) (strat : Strat p) (fuel : ℕ) :
    runEmbed g₁ D fuel strat (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)
      = some ((runOutput (realAns τ) strat fuel (srsSt D)).1,
              g₁ ^ ((runOutput (realAns τ) strat fuel (srsSt D)).2.eval τ).val) := by
  have hsrs1 : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).1 = PowerSrs.tower g₁ τ D := rfl
  rw [runEmbed, hsrs1,
    runEmbedAux_correspondence hord τ strat fuel
      (seedG (PowerSrs.tower g₁ τ D).toList D) (srsSt (p := p) D).table []
      (seedG_Inv g₁ hord τ D hD)]
  rfl

/-! ## 6. Non-collapse: the embedded adversary class is a genuine non-singleton.

`tSdh_ggm_sound` (GgmEndToEnd) quantifies over the IMAGE of `embed`, NOT over all
`Groups.tSdhAdversary` (over which the bound is FALSE — a `Classical.choice`-definable adversary
inverts the encoding and wins with probability 1). A reviewer must therefore see that the
replacement class is at least not degenerate: `embed_noncollapsing` certifies that its image is a
genuine non-singleton and really exercises the group. This richness witness does not prove that the
image captures every conventional generic-group adversary.

⚑ WHAT THIS WITNESSES (and what it does NOT). It witnesses only RICHNESS — the image of `embed` is
not a single point. It does NOT claim completeness of the model or injectivity of `embed`: literal
injectivity is FALSE, and honestly so.
Two strategies that differ only on equality-histories the run never actually reaches produce the
SAME committed adversary — `runEmbed` consults a strategy only along the single branch its own
realized queries carve out, so off-branch disagreement is invisible. The theorem therefore records
that the intended restricted class has distinct behaviors, without claiming an injective
parametrization.

⚑ WHERE `g₁ ≠ 1` LIVES. This hypothesis belongs HERE, not on `tSdh_ggm_sound`. Soundness holds for
ANY base `g₁` — the counting bound never needs a nontrivial generator, and `tSdh_ggm_sound`
correctly does not assume one. But the *meaningfulness* of quantifying over `embed`'s image — that
the class carries a genuinely nontrivial GROUP output (conjunct (ii)), not merely distinct offset
labels — is what consumes `g₁ ≠ 1`. That asymmetry (soundness free of it, meaningfulness using it)
is itself the point. The non-singleton conjunct (i) needs even less: only `0 ≠ 1` in `ZMod p`. -/

/-- The constant strategy that immediately commits offset `c` and reads out handle `0`, ignoring the
equality history. The two instances `stratOffset 0` / `stratOffset 1` are the non-collapse witness. -/
private def stratOffset (c : ZMod p) : Strat p := fun _ => Sum.inr (c, 0)

/-- `getD 0` of the seed table is the `0`-th SRS G₁ handle (the seed's first segment starts at the
tower, so position `0` is `srs1[0]`). -/
lemma seedG_getD_zero (srs1 : List G₁) (D : ℕ) :
    (seedG srs1 D).getD 0 1 = srs1.getD 0 1 := by
  rw [seedG, List.getD_append _ _ _ _ (by simp),
      rangeMap_getD_lt (fun i => srs1.getD i 1) (D + 1) 0 1 (Nat.succ_pos D)]

omit [Group G₂] [PrimeOrderWith G₂ p] in
/-- A `stratOffset c` run (with at least one unit of fuel) commits `c` and the `0`-th seed handle —
which is the SRS's `0`-th G₁ element — on ANY SRS, decided with no group machinery. -/
lemma runEmbed_stratOffset {g₁ : G₁} (D f : ℕ) (c : ZMod p)
    (srs : Vector G₁ (D + 1) × Vector G₂ 2) :
    runEmbed g₁ D (f + 1) (stratOffset c) srs = some (c, srs.1.toList.getD 0 1) := by
  simp only [runEmbed, runEmbedAux, stratOffset, seedG_getD_zero]

omit [PrimeOrderWith G₂ p] in
/-- **`embed_noncollapsing` — the non-collapse witness.** There are two generic strategies whose
`embed`-outputs (the deterministic `runEmbed` values, since `embed strat srs = pure (runEmbed …)`)
are distinct, so the IMAGE of `embed` is a genuine non-singleton:

* (i) On EVERY SRS, `stratOffset 0` and `stratOffset 1` commit distinct offsets (`0 ≠ 1` in
  `ZMod p`), hence distinct outputs — no group machinery, no nontrivial generator. This is the
  non-vacuity of `tSdh_ggm_sound`'s quantifier: its range is not one point.
* (ii) On the real KZG SRS `PowerSrs.generate D τ`, `stratOffset 0`'s committed GROUP element is the
  base generator `g₁`, which is `≠ 1` by `hg₁`. So the image really exercises the group — its
  adversaries produce nontrivial group outputs, not only distinct labels. This is the sole consumer
  of `g₁ ≠ 1`.

Honest non-claim: this does not assert `embed` is injective (it is not — see the section note); it
asserts the image is not a singleton, which is what a meaningful quantifier requires. -/
theorem embed_noncollapsing {g₁ : G₁} {g₂ : G₂} (hg₁ : g₁ ≠ 1) (D f : ℕ) :
    ∃ s₀ s₁ : Strat p,
      (∀ srs : Vector G₁ (D + 1) × Vector G₂ 2,
          runEmbed g₁ D (f + 1) s₀ srs ≠ runEmbed g₁ D (f + 1) s₁ srs) ∧
      (∀ τ : ZMod p,
          runEmbed g₁ D (f + 1) s₀ (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)
            ≠ some (0, 1)) := by
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  refine ⟨stratOffset 0, stratOffset 1, ?_, ?_⟩
  · -- (i) distinct offsets on every SRS, by `0 ≠ 1`
    intro srs h
    rw [runEmbed_stratOffset D f 0 srs, runEmbed_stratOffset D f 1 srs,
        Option.some.injEq, Prod.mk.injEq] at h
    exact h01 h.1
  · -- (ii) the group output on the real SRS is the nontrivial generator `g₁`
    intro τ h
    have hval : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).1.toList.getD 0 1 = g₁ := by
      have hsrs1 : (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ).1 = PowerSrs.tower g₁ τ D := rfl
      rw [hsrs1, tower_toList_getD τ D 0 (Nat.succ_pos D), pow_zero, pow_one]
    rw [runEmbed_stratOffset D f 0 (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ), hval,
        Option.some.injEq, Prod.mk.injEq] at h
    exact hg₁ h.2

#print axioms embed_run_correspondence
#print axioms embed
#print axioms runEmbed
#print axioms embed_noncollapsing

end GgmEmbed

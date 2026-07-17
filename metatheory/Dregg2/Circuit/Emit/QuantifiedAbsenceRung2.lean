/-
# Dregg2.Circuit.Emit.QuantifiedAbsenceRung2 — the RUNG-2 discharge of the `quantified_absence`
quotient-accumulator descriptor to GENUINE SET-ABSENCE (no forged non-membership), via the
accumulator-binding + quotient-commitment carriers.

## What Rung 1 gave, and the residual it leaves

`QuantifiedAbsenceRefine.lean` (RUNG 1) proves the whole-descriptor bridge
`Satisfied2 ⟹ QuotientAbsenceRel elem w v accAll alpha`, i.e. the BARE division certificate over
BabyBear⁴:

    w ⊗ (alpha ⊖ elem) ⊕ v  =  Acc_all .

Its own §"Honest scope" is explicit that this is NOT a soundness statement: it does NOT establish that
`Acc_all` is the genuine characteristic value `∏(alpha − hⱼ)` of the committed set, and it does NOT
establish the non-membership content `v ≠ 0`. Compared with the SIBLING family
(`AccumulatorNonRevocationRefine.lean`, whose descriptor DOES carry a `check`/`v_inv` unit gate and so
concludes the full `NonMemberCertified := ∃ w v, acc = w⊗(α⊖h)⊕v ∧ v ≠ 0`), the `quantified_absence`
emit is STRICTLY WEAKER: it drops the remainder-nonzero gate. So the residual is precise and twofold:

  (R1)  the accumulator `Acc_all` is not tied to any committed set — the descriptor treats it as a free
        public input (the off-descriptor accumulator carrier, same one the sibling names);
  (R2)  the remainder `v` is a FREE witness column — the pointwise identity at the single challenge
        `alpha` is solvable for ANY `elem` (member or not), so `Satisfied2` alone certifies nothing.

Unconditional `Satisfied2 ⟹ elem ∉ S` is therefore FALSE and provably so (§5, `cheat_breaks_absence`):
a MEMBER `elem ∈ S` admits a `Satisfied2` trace with a nonzero remainder `v` — the pointwise equation
`w(α−elem)+v = Acc_all` is one linear equation in the free `(w, v)`, always satisfiable. So the
soundness of "elem is absent" pivots on binding `(Acc_all, w, v)` to a GENUINE committed set — which is
exactly the crypto anchor this file supplies.

## The discharge (the accumulator anchor + the quotient-commitment carrier)

We author the genuine reference object `HonestAbsence elem alpha accAll` — the honest committed set `S`
with `Acc_all = charEval S alpha` (the accumulator IS the characteristic evaluation `∏(alpha − hⱼ)` at
the public challenge — carrier R1) together with the honest quotient `qPoly` witnessing the POLYNOMIAL
remainder identity `∀ x, charEval S x = qPoly x ⊗ (x ⊖ elem) ⊕ (charEval S elem)` (the remainder
theorem for dividing the characteristic polynomial by `(x − elem)`; its constant remainder is
`charEval S elem`).

The named carrier is the QUOTIENT-COMMITMENT binding `QuotientBinds : w = qPoly alpha` — the trace's
quotient column IS the honest quotient polynomial evaluated at the challenge (what the deployed
polynomial-commitment / Fiat-Shamir layer enforces, and what the emitted descriptor does NOT check).
Given it, the two division identities at `alpha` share the same `w ⊗ (alpha ⊖ elem)` summand, so
extension-field cancellation forces `v = charEval S elem`: the disclosed remainder IS the genuine
characteristic evaluation. With the acceptance side-condition `v ≠ 0` (see the EMIT-FIX below),
`charEval S elem ≠ 0`, and since a member's characteristic evaluation vanishes
(`mem_charEval_zero`, fully proved over the integral ring `ℤ[X]/(X⁴−11)`), `elem ∉ S` — GENUINE ABSENCE
of the queried element from the committed set. No forged non-membership survives.

## THE EMIT-FIX (named precisely)

The `v ≠ 0` side-condition is discharged here as an explicit hypothesis because the emitted
`quantifiedAbsenceDesc` OMITS the in-circuit remainder-nonzero gate. The precise fix mirrors the sibling
`AccumulatorNonRevocationEmit`: add a `v_inv` column plus a C4 group `check = v ⊗ v_inv` (four
`ExtElem::mul` gates) and a boundary `check = (1,0,0,0)` pin. Then `v` is forced to be a UNIT
(`unit_ne_ezero`), so `v ≠ 0` becomes an in-circuit fact and the Rung-2 side-condition drops. Until that
emit lands, `v ≠ 0` is the disclosed acceptance criterion (the verifier's public check on the exposed
remainder), named here rather than hidden.

## Axiom hygiene / non-vacuity

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The accumulator/quotient carriers ride as
NAMED hypotheses (`HonestAbsence` fields + `QuotientBinds`), never as Lean axioms. §4 exhibits a concrete
genuine absence — the committed set `S = {0}`, query `elem = 1`, over a real `Satisfied2` trace whose
Rung-2 conclusion FIRES (`1 ∉ {0}`) — and §5 the load-bearing cheat: a MEMBER (`elem = 1 ∈ {1}`) whose
trace `Satisfied2`s with a nonzero remainder, so the anchor is a real filter, not `True`. NEW file;
imports read-only.
-/
import Dregg2.Circuit.Emit.QuantifiedAbsenceRefine

namespace Dregg2.Circuit.Emit.QuantifiedAbsenceRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt zeroAsg memLog mapLog)
open Dregg2.Circuit.Argus.InterpCore (decideConstraint decideConstraint_iff)
open Dregg2.Circuit.Emit.QuantifiedAbsenceEmit
open Dregg2.Circuit.Emit.QuantifiedAbsenceRefine

set_option autoImplicit false

/-! ## §1 — The BabyBear⁴ ring facts (over Rung-1's `Ext`, `extAdd`/`extSub`/`extMul`) and the
characteristic evaluation `charEval S x = ∏_{h∈S}(x ⊖ h)`. -/

/-- Left cancellation of the extension addition (componentwise `a + b = a + c → b = c`). -/
theorem extAdd_left_cancel {a b c : Ext} (h : extAdd a b = extAdd a c) : b = c := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  obtain ⟨c0, c1, c2, c3⟩ := c
  simp only [extAdd, Prod.mk.injEq] at h ⊢
  omega

/-- `x ⊖ x = 0`. -/
theorem extSub_self (a : Ext) : extSub a a = ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp only [extSub, Prod.mk.injEq]; omega

/-- `0 ⊗ b = 0`. -/
theorem extMul_zero_left (b : Ext) :
    extMul ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) b = ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) := by
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [extMul, Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `a ⊗ 0 = 0`. -/
theorem extMul_zero_right (a : Ext) :
    extMul a ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) = ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp only [extMul, Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `1 ⊗ b = b` (the `X⁴−11` multiplicative identity `(1,0,0,0)`). -/
theorem extMul_one_left (b : Ext) : extMul ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) b = b := by
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [extMul, Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- `a ⊗ 1 = a`. -/
theorem extMul_one_right (a : Ext) : extMul a ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) = a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp only [extMul, Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

/-- **`charEval S x`** — the characteristic-polynomial evaluation of the committed set `S` at `x`:
`∏_{h∈S}(x ⊖ h)` over BabyBear⁴. This is the value the accumulator commits (`Acc_all = charEval S α`)
and whose evaluation at `elem` is the honest division remainder. -/
def charEval (S : List Ext) (x : Ext) : Ext :=
  S.foldr (fun h acc => extMul (extSub x h) acc) ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))

theorem charEval_cons (a : Ext) (rest : List Ext) (x : Ext) :
    charEval (a :: rest) x = extMul (extSub x a) (charEval rest x) := rfl

/-- `charEval [c] x = x ⊖ c` (the degree-1 characteristic value of a singleton set). -/
theorem charEval_single (c x : Ext) : charEval [c] x = extSub x c := by
  show extMul (extSub x c) ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) = extSub x c
  exact extMul_one_right (extSub x c)

/-- **`mem_charEval_zero` — a MEMBER's characteristic evaluation vanishes (FULLY PROVED, no carrier).**
If `elem ∈ S` then some factor `(elem ⊖ elem) = 0`, and a zero factor annihilates the product. This is
the semantic heart: `charEval S elem ≠ 0 ⟹ elem ∉ S` (its contrapositive), the genuine set-absence
witness — over the integral ring `ℤ[X]/(X⁴−11)`, `∏(elem − hⱼ) = 0` iff some `elem = hⱼ`. -/
theorem mem_charEval_zero {S : List Ext} {elem : Ext} :
    elem ∈ S → charEval S elem = ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) := by
  induction S with
  | nil => intro h; simp only [List.not_mem_nil] at h
  | cons a rest ih =>
    intro h
    rw [charEval_cons]
    rcases List.mem_cons.mp h with rfl | hrest
    · rw [extSub_self, extMul_zero_left]
    · rw [ih hrest, extMul_zero_right]

/-! ## §2 — The genuine reference anchor: the honest committed set + its remainder identity. -/

/-- **`HonestAbsence elem alpha accAll`** — the genuine reference object (the honest committed set with
its accumulator and honest quotient). `S` is the committed set; `accHonest` is the accumulator-binding
carrier (`Acc_all = charEval S α = ∏(α − hⱼ)`); `polyId` is the honest polynomial remainder identity —
dividing the characteristic polynomial by `(x − elem)` gives quotient `qPoly` and CONSTANT remainder
`charEval S elem`. Evaluated at the public challenge `alpha`, `polyId` yields the honest certificate the
trace's certificate is bound against. -/
structure HonestAbsence (elem alpha accAll : Ext) where
  /-- The honest committed set (its characteristic value is the accumulator). -/
  S : List Ext
  /-- The honest quotient polynomial (evaluated), from dividing `charEval S` by `(x − elem)`. -/
  qPoly : Ext → Ext
  /-- The polynomial remainder identity: constant remainder `charEval S elem`. -/
  polyId : ∀ x, charEval S x = extAdd (extMul (qPoly x) (extSub x elem)) (charEval S elem)
  /-- **Accumulator-binding carrier (R1):** the public accumulator IS the characteristic evaluation. -/
  accHonest : accAll = charEval S alpha

/-! ## §2c — field-nonzero of a BabyBear⁴ element (the faithful acceptance side-condition).

Under the field-faithful denotation Rung 1's certificate binds only mod `p`, so the honest remainder
is recovered only in 𝔽_p⁴: the acceptance condition `v ≠ 0` is the FIELD non-zero `¬ EzeroMod v`
(the deployed `verify` checks `v ≠ 0` as a field element — exactly what the emit-fix `v_inv` gate
would force). `EzeroMod` is `v = 0` in 𝔽_p⁴ (every limb `≡ 0 [ZMOD p]`). -/
@[reducible] def EzeroMod (v : Ext) : Prop :=
  v.1 ≡ 0 [ZMOD 2013265921] ∧ v.2.1 ≡ 0 [ZMOD 2013265921]
  ∧ v.2.2.1 ≡ 0 [ZMOD 2013265921] ∧ v.2.2.2 ≡ 0 [ZMOD 2013265921]

/-- Cancel a shared ℤ summand under a mod-`p` congruence. -/
theorem modEq_of_add_cancel {a b c : ℤ} (h : a + b ≡ a + c [ZMOD 2013265921]) :
    b ≡ c [ZMOD 2013265921] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  have he : (a + c) - (a + b) = c - b := by ring
  rwa [he] at h

/-! ## §3 — THE RUNG-2 DISCHARGE. -/

/-- **`quotientRel_absent` — the core discharge (division certificate ⟹ genuine absence).** Given the
Rung-1 division certificate `QuotientAbsenceRel elem w v accAll alpha`, the genuine reference anchor `g`
(accumulator-binding + honest quotient), the QUOTIENT-COMMITMENT carrier `hqb : w = g.qPoly alpha`, and
the remainder-nonzero acceptance side-condition `hv : v ≠ 0`, the queried `elem` is GENUINELY ABSENT from
the committed set `g.S`.

The two division identities at `alpha` — the trace's `w ⊗ (α⊖elem) ⊕ v = accAll` and the anchor's
`accAll = charEval S α = g.qPoly α ⊗ (α⊖elem) ⊕ charEval S elem` — share the summand `g.qPoly α ⊗ (α⊖elem)`
once `hqb` rewrites `w`, so extension-field cancellation forces `v = charEval S elem`. Then `v ≠ 0` gives
`charEval S elem ≠ 0`, and `mem_charEval_zero`'s contrapositive gives `elem ∉ g.S`. -/
theorem quotientRel_absent
    {elem w v accAll alpha : Ext}
    (hrel : QuotientAbsenceRel elem w v accAll alpha)
    (g : HonestAbsence elem alpha accAll)
    (hqb : w = g.qPoly alpha)
    (hv : ¬ EzeroMod v) :
    elem ∉ g.S := by
  intro hmem
  -- a member's characteristic evaluation vanishes (exactly, over `ℤ[X]/(X⁴−11)`).
  have hz : charEval g.S elem = ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) := mem_charEval_zero hmem
  -- the anchor's honest certificate at `alpha`, with `w = qPoly α` and the vanishing remainder folded
  -- in: `accAll = w ⊗ (α ⊖ elem) ⊕ 0` (exact ℤ, from the honest polynomial identity).
  have ha : accAll = extAdd (extMul w (extSub alpha elem)) (charEval g.S elem) := by
    rw [hqb]; exact g.accHonest.trans (g.polyId alpha)
  rw [hz] at ha
  -- Rung 1's certificate binds only mod `p`: `w ⊗ (α⊖elem) ⊕ v ≡ accAll` per limb. Cancelling the
  -- shared `w ⊗ (α⊖elem)` summand (exact, via `ha`) forces `v ≡ 0` per limb — i.e. `EzeroMod v`,
  -- contradicting the field-nonzero acceptance side-condition. So no member can satisfy the certificate.
  apply hv
  obtain ⟨e0, e1, e2, e3⟩ := elem
  obtain ⟨w0, w1, w2, w3⟩ := w
  obtain ⟨al0, al1, al2, al3⟩ := alpha
  obtain ⟨v0, v1, v2, v3⟩ := v
  obtain ⟨ac0, ac1, ac2, ac3⟩ := accAll
  simp only [QuotientAbsenceRel, extAdd, extMul, extSub] at hrel
  simp only [extAdd, extMul, extSub, Prod.mk.injEq] at ha
  obtain ⟨hr0, hr1, hr2, hr3⟩ := hrel
  obtain ⟨ha0, ha1, ha2, ha3⟩ := ha
  rw [ha0] at hr0; rw [ha1] at hr1; rw [ha2] at hr2; rw [ha3] at hr3
  exact ⟨modEq_of_add_cancel hr0, modEq_of_add_cancel hr1,
         modEq_of_add_cancel hr2, modEq_of_add_cancel hr3⟩

/-- **`quantifiedAbsence_rung2` — the RUNG-2 no-forgery theorem (from `Satisfied2`).** Any multi-table
witness that `Satisfied2`s the emitted `quantifiedAbsenceDesc` (on a ≥2-row trace, so row 0 is active),
carrying the accumulator anchor `g`, the quotient-commitment carrier `hqb`, and the disclosed nonzero
remainder `hv`, has its queried element GENUINELY ABSENT from the committed set `g.S`. Composes Rung-1's
`quantifiedAbsence_refines` (the division certificate) with `quotientRel_absent` (the discharge). No
`Acc_all`-is-honest / `v ≠ 0` obligation is laundered — both ride as NAMED carriers. -/
theorem quantifiedAbsence_rung2
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash quantifiedAbsenceDesc minit mfin maddrs t)
    (h2 : 2 ≤ t.rows.length)
    (g : HonestAbsence
          ((envAt t 0).loc E0, (envAt t 0).loc E1, (envAt t 0).loc E2, (envAt t 0).loc E3)
          ((envAt t 0).pub (PI_ALPHA0 + 0), (envAt t 0).pub (PI_ALPHA0 + 1),
           (envAt t 0).pub (PI_ALPHA0 + 2), (envAt t 0).pub (PI_ALPHA0 + 3))
          ((envAt t 0).pub (PI_ACC0 + 0), (envAt t 0).pub (PI_ACC0 + 1),
           (envAt t 0).pub (PI_ACC0 + 2), (envAt t 0).pub (PI_ACC0 + 3)))
    (hqb : ((envAt t 0).loc Q0, (envAt t 0).loc Q1, (envAt t 0).loc Q2, (envAt t 0).loc Q3)
            = g.qPoly ((envAt t 0).pub (PI_ALPHA0 + 0), (envAt t 0).pub (PI_ALPHA0 + 1),
                       (envAt t 0).pub (PI_ALPHA0 + 2), (envAt t 0).pub (PI_ALPHA0 + 3)))
    (hv : ¬ EzeroMod ((envAt t 0).loc V0, (envAt t 0).loc V1,
            (envAt t 0).loc V2, (envAt t 0).loc V3)) :
    (((envAt t 0).loc E0, (envAt t 0).loc E1, (envAt t 0).loc E2, (envAt t 0).loc E3) : Ext) ∉ g.S :=
  quotientRel_absent (quantifiedAbsence_refines hsat h2) g hqb hv

#assert_axioms quotientRel_absent
#assert_axioms quantifiedAbsence_rung2

/-! ## §4 — NON-VACUITY (TRUE half): the discharge FIRES on a genuine absence.

Committed set `S = {0}` (`Acc_all = charEval {0} α = α`), query `elem = 1`. The genuine anchor: quotient
`qPoly ≡ 1` (constant), remainder `charEval {0} 1 = 1`. The concrete 2-row `fireTrace` carries
`elem=1, w=1, v=1, α=7, Acc_all=7` (`w·(α−elem)+v = 1·6+1 = 7 = Acc_all`); every hypothesis is met and the
Rung-2 conclusion FIRES: `1 ∉ {0}`. -/

/-- Row 0 of the firing witness: `elem=1, w=1, v=1, diff=6, prod=6, sum=7, α=7` (limb 0, else 0). -/
def fireRow0 : Assignment := fun n =>
  [1,0,0,0, 1,0,0,0, 1,0,0,0, 6,0,0,0, 6,0,0,0, 7,0,0,0, 7,0,0,0].getD n 0

/-- Public inputs of the firing witness: `Acc_all = 7`, `α = 7` (limb 0). -/
def firePub : Assignment := fun n => [7,0,0,0, 7,0,0,0].getD n 0

/-- The firing 2-row trace (active row 0 + one wrap row). -/
def fireTrace : VmTrace := { rows := [fireRow0, zeroAsg], pub := firePub, tf := fun _ => [] }

/-- The descriptor declares no mem/map ops, so both logs are empty on ANY trace. -/
theorem qad_memLog (tr : VmTrace) : memLog quantifiedAbsenceDesc tr = [] := by
  simp [memLog, Dregg2.Circuit.DescriptorIR2.memOpsOf, quantifiedAbsenceDesc,
    diffGates, prodGates, sumGates, sumPins, alphaPins]

theorem qad_mapLog (tr : VmTrace) : mapLog quantifiedAbsenceDesc tr = [] := by
  simp [mapLog, Dregg2.Circuit.DescriptorIR2.mapOpsOf, quantifiedAbsenceDesc,
    diffGates, prodGates, sumGates, sumPins, alphaPins]

/-- **The firing trace `Satisfied2`s the descriptor** — row 0 discharges every gate (the consistent
quotient trace), the two wrap-row twins are vacuous, the mem/map legs collapse. -/
theorem fire_sat (hash : List ℤ → ℤ) :
    Satisfied2 hash quantifiedAbsenceDesc (fun _ => 0) (fun _ => (0, 0)) [] fireTrace := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · intro i hi c hc
    simp only [quantifiedAbsenceDesc, diffGates, prodGates, sumGates, sumPins, alphaPins,
      List.cons_append, List.nil_append] at hc
    have hlen : fireTrace.rows.length = 2 := rfl
    rw [hlen] at hi
    interval_cases i <;>
      (fin_cases hc <;>
        (simp only [VmConstraint2.holdsAt]; exact (decideConstraint_iff _ _ _ _).mp (by decide)))
  · intro i _; exact True.intro
  · intro i _ r hr; simp [quantifiedAbsenceDesc] at hr
  · exact List.nodup_nil
  · rw [qad_memLog]; simp
  · rw [qad_memLog]; exact True.intro
  · rw [qad_memLog]
    simp [Dregg2.Crypto.MemoryChecking.MemCheck, Dregg2.Crypto.MemoryChecking.initSet,
      Dregg2.Crypto.MemoryChecking.finalSet]
  · rw [qad_memLog]; rfl
  · rw [qad_mapLog]; rfl

/-- **The genuine reference anchor for the firing witness.** Committed set `{0}`, honest constant
quotient `1`, matching the firing trace's public `(Acc_all, α) = (7, 7)`. -/
def gFire : HonestAbsence ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
    ((7 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) ((7 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) where
  S := [((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))]
  qPoly := fun _ => ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
  polyId := by
    intro x
    simp only [charEval_single]
    show extSub x ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
        = extAdd (extMul ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
            (extSub x ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))))
            (extSub ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)))
    rw [extMul_one_left]
    obtain ⟨x0, x1, x2, x3⟩ := x
    simp only [extSub, extAdd, Prod.mk.injEq]; refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  accHonest := by decide

/-- **THE RUNG-2 DISCHARGE FIRES on the genuine witness.** Feeding `fireTrace`, its anchor `gFire`, the
quotient-commitment binding (`w = 1 = qPoly α`), and the nonzero remainder (`v = 1`) to
`quantifiedAbsence_rung2` recovers GENUINE ABSENCE — the queried `elem = 1` is not in the committed set
`{0}` — WITHOUT any laundered obligation. -/
theorem fire_absent : (((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) : Ext) ∉ gFire.S :=
  quantifiedAbsence_rung2 (fire_sat (fun _ => 0)) (by decide) gFire (by decide) (by decide)

/-- The committed-set relation genuinely DISCRIMINATES: a MEMBER of `gFire.S` (the element `0`) has a
VANISHING characteristic evaluation — so the `charEval ≠ 0` filter (hence the `∉` conclusion) is
two-valued, not a tautology. -/
theorem fire_member_charEval_zero :
    charEval gFire.S ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))
      = ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) :=
  mem_charEval_zero (by decide)

/-! ## §5 — NON-VACUITY (FALSE half): `Satisfied2 ∧ v ≠ 0` alone does NOT force absence.

The committed set `S = {1}`; the queried `elem = 1` is a genuine MEMBER (`charEval {1} 1 = 0`). A cheating
prover picks a nonzero remainder `v = 3` and a matching `w = 1` so the pointwise identity still holds at
`α = 5`: `w·(α−elem)+v = 1·4+3 = 7 = Acc_all`. The trace PROVABLY `Satisfied2`s and exposes `v = 3 ≠ 0`,
yet `elem = 1 ∈ {1}`. So NO `Satisfied2`-plus-`v≠0` theorem can conclude absence — the accumulator anchor
(`Acc_all = charEval S α`) + quotient-commitment carrier are LOAD-BEARING. The cheat's forged `Acc_all = 7`
differs from the honest `charEval {1} 5 = 4`, and its disclosed `v = 3` differs from the true remainder
`charEval {1} 1 = 0` — exactly the two bindings the carriers restore. -/

/-- The cheating row: `elem=1, w=1, v=3, diff=4, prod=4, sum=7, α=5` — a MEMBER forging `v ≠ 0`. -/
def cheatRow0 : Assignment := fun n =>
  [1,0,0,0, 1,0,0,0, 3,0,0,0, 4,0,0,0, 4,0,0,0, 7,0,0,0, 5,0,0,0].getD n 0

/-- Cheat public inputs: `Acc_all = 7`, `α = 5` (limb 0). -/
def cheatPub : Assignment := fun n => [7,0,0,0, 5,0,0,0].getD n 0

/-- The cheating 2-row trace. -/
def cheatTrace : VmTrace := { rows := [cheatRow0, zeroAsg], pub := cheatPub, tf := fun _ => [] }

/-- The cheat's committed set — the queried `elem = 1` IS one of its members. -/
def cheatS : List Ext := [((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))]

/-- **The cheat PROVABLY `Satisfied2`s** — every gate holds on the forged row (the pointwise identity is
solvable for the free `(w, v)`), the wrap row is vacuous, the mem/map legs collapse. -/
theorem cheat_sat (hash : List ℤ → ℤ) :
    Satisfied2 hash quantifiedAbsenceDesc (fun _ => 0) (fun _ => (0, 0)) [] cheatTrace := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · intro i hi c hc
    simp only [quantifiedAbsenceDesc, diffGates, prodGates, sumGates, sumPins, alphaPins,
      List.cons_append, List.nil_append] at hc
    have hlen : cheatTrace.rows.length = 2 := rfl
    rw [hlen] at hi
    interval_cases i <;>
      (fin_cases hc <;>
        (simp only [VmConstraint2.holdsAt]; exact (decideConstraint_iff _ _ _ _).mp (by decide)))
  · intro i _; exact True.intro
  · intro i _ r hr; simp [quantifiedAbsenceDesc] at hr
  · exact List.nodup_nil
  · rw [qad_memLog]; simp
  · rw [qad_memLog]; exact True.intro
  · rw [qad_memLog]
    simp [Dregg2.Crypto.MemoryChecking.MemCheck, Dregg2.Crypto.MemoryChecking.initSet,
      Dregg2.Crypto.MemoryChecking.finalSet]
  · rw [qad_memLog]; rfl
  · rw [qad_mapLog]; rfl

/-- **`cheat_breaks_absence` — the anchor is LOAD-BEARING.** The forged trace `Satisfied2`s AND exposes a
nonzero remainder (`v = 3 ≠ 0`), yet the queried element `1` is a GENUINE MEMBER of the committed set
`{1}`. So `Satisfied2 ∧ v ≠ 0` — the naive criterion without the accumulator/quotient carriers — is
satisfiable by a member; absence CANNOT be concluded from it. -/
theorem cheat_breaks_absence :
    (Satisfied2 (fun _ => 0) quantifiedAbsenceDesc (fun _ => 0) (fun _ => (0, 0)) [] cheatTrace)
    ∧ (((envAt cheatTrace 0).loc V0, (envAt cheatTrace 0).loc V1,
        (envAt cheatTrace 0).loc V2, (envAt cheatTrace 0).loc V3)
          ≠ ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)))
    ∧ (((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) : Ext) ∈ cheatS :=
  ⟨cheat_sat (fun _ => 0), by decide, by decide⟩

/-- **The broken binding, pinpointed.** The disclosed remainder `v = 3` differs from the TRUE
characteristic evaluation `charEval cheatS 1 = 0` (a member's remainder vanishes). This is exactly the
`v = charEval S elem` binding that `quotientRel_absent` derives from the carriers — and that the cheat,
lacking them, violates. -/
theorem cheat_binding_violated :
    ((envAt cheatTrace 0).loc V0, (envAt cheatTrace 0).loc V1,
     (envAt cheatTrace 0).loc V2, (envAt cheatTrace 0).loc V3)
      ≠ charEval cheatS ((1 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)) := by decide

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms fire_sat
#assert_axioms fire_absent
#assert_axioms fire_member_charEval_zero
#assert_axioms cheat_sat
#assert_axioms cheat_breaks_absence
#assert_axioms cheat_binding_violated

end Dregg2.Circuit.Emit.QuantifiedAbsenceRung2

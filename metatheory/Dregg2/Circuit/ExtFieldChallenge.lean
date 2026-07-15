import Dregg2.Circuit.FriChallengerUnified
import Dregg2.Tactics

/-!
# Dregg2.Circuit.ExtFieldChallenge — the quartic-extension FRI challenge/fold, faithfully

## The residual this file closes (ExtensionFoldWidthResidual)

The deployed FRI algebra challenges — the constraint-RLC `α`, the out-of-domain `ζ`, and
every commit-phase fold `β` — are QUARTIC-EXTENSION-FIELD elements: values of
`BinomialExtensionField<BabyBear, 4>`, i.e. `BabyBear[X]/(X^4 − 11)`
(`p3-baby-bear/src/baby_bear.rs:66`, `const W = 11`; `EXT_DEG = params.extDeg = 4` in
`ir2LeafWrapConfig`). Each is FOUR ordered BabyBear base lanes
(`EF::from_basis_coefficients_fn`), and the commit-phase fold `e0 + β·e1` is EXTENSION-FIELD
arithmetic.

`FriChallengerUnified.deriveTranscript` squeezes each challenge as a `params.extDeg`-lane
`List F` (faithful WIDTH), but the FRI-opening shell (`FriVerifier.LayerOpening.beta : F`,
folded by `FriCore.foldCombine : F → F → F → F → F`) stores/uses only ONE base lane
(`projBeta = head`). `FriChallengerUnified` NAMES this as the `ExtensionFoldWidthResidual`
and does not paper over it.

Here that residual is MODELLED, not assumed:

* `ExtElem` — an ordered-base-lane extension element;
* `extAdd` / `extMul` — the binomial-extension arithmetic `F[X]/(X^D − W)`, whose reduction
  is EXACTLY p3's generic `binomial_mul` (`res[i+j−D] += a[i]·w·b[j]` for `i+j ≥ D`,
  else `res[i+j] += a[i]·b[j]`, `p3-field/src/extension/binomial_extension.rs:696`);
* `extFold` — the post-interpolation linear fold `even + β·odd` in EXTENSION arithmetic;
* `extFoldCombine` — p3's complete evaluation-pair interpolation
  `(f(x)+f(-x))/2 + β·(f(x)-f(-x))/(2x)` in that arithmetic;
* the **denotation**: over the DEPLOYED field (BabyBear, `W = 11`), `extMul` denotes the
  quartic binomial product `quarticRef` (checked = the human-legible `c0..c3` formula), and
  the ext fold width genuinely carries information the scalar shell drops — two betas the
  scalar model CANNOT distinguish (same head lane) produce DIFFERENT ext folds;
* the **bridge**: the scalar model is the `extDeg = 1` restriction — at `D = 1`, `extMul`
  is base multiplication and `extFold` is the scalar `e0 + β·e1` (`FriCore.foldCombine`), so
  the existing scalar-shell soundness is exactly the width-one specialization.

## The verifier cutover

The legacy scalar shell remains as a redundant strengthening target so the existing
`DeployedRefines` statement does not change.  The verifier consumed by the apex additionally
runs `foldConsistentExt` over `ExtQueryOpening`: the complete four-lane beta, coset point,
ordered evaluations, carried value, and final coefficient.  `friChainGoExt` implements p3's
arity-two interpolation

`(f(x)+f(-x))/2 + beta * (f(x)-f(-x))/(2*x)`

in the binomial extension, checks the carried value in the parity-selected row position,
binds the row to its Merkle commitment, and binds beta to the same continued transcript.
`verifyAlgoUnifiedFaithfulExt` conjoins that check with the established faithful verifier;
its strengthening theorem is what keeps the apex soundness chain intact.
-/

namespace Dregg2.Circuit.ExtFieldChallenge

open Dregg2.Circuit.FriVerifier

variable {F : Type}

/-! ## 1. The extension element and its binomial arithmetic. -/

/-- An element of a degree-`D` extension `F[X]/(X^D − W)`, as its ordered base lanes
`[c₀, c₁, …, c_{D−1}]` (basis order — the p3 `value: [F; D]` array;
`from_basis_coefficients_fn` fills lane `i` with the `i`-th squeeze). The width `D` and
residue `W` are carried by the operations, not the type, so the `extDeg = 1` restriction is
just `lanes.length = 1`. -/
structure ExtElem (F : Type) where
  lanes : List F
  deriving Repr, DecidableEq

/-- Extension addition — lane-wise `F`-addition (the free-module structure of the
extension over its base). -/
def extAdd (A : FieldArith F) (x y : ExtElem F) : ExtElem F :=
  ⟨List.zipWith A.add x.lanes y.lanes⟩

/-- The `k`-th convolution coefficient `∑_{i} a[i]·b[k−i]` of two lane lists (out-of-range
lanes read as `zero` via `getD`). This is the unreduced polynomial product coefficient. -/
def dotConv (A : FieldArith F) (a b : List F) (k : Nat) : F :=
  (List.range (k + 1)).foldl
    (fun acc i => A.add acc (A.mul (a.getD i A.zero) (b.getD (k - i) A.zero))) A.zero

/-- The full convolution `a ⋆ b` (length `|a| + |b| − 1`). -/
def convLanes (A : FieldArith F) (a b : List F) : List F :=
  (List.range (a.length + b.length - 1)).map (dotConv A a b)

/-- Reduce a convolution modulo `X^D − W`: lane `r` collects the degree-`r` coefficient plus
`W ·` the degree-`(r+D)` coefficient (`X^{r+D} = W·X^r`). This is EXACTLY p3's generic
`binomial_mul` reduction (`res[i+j−D] += a[i]·w·b[j]` for `i+j ≥ D`;
`p3-field/src/extension/binomial_extension.rs:696`): grouping that accumulation by output
lane `r = i+j−D` gives `W · (∑_{i+j = r+D} a[i]b[j]) = W · conv[r+D]`. -/
def reduceBinom (A : FieldArith F) (W : F) (D : Nat) (c : List F) : List F :=
  (List.range D).map (fun r => A.add (c.getD r A.zero) (A.mul W (c.getD (r + D) A.zero)))

/-- Extension multiplication in `F[X]/(X^D − W)`: convolve, then reduce. -/
def extMul (A : FieldArith F) (W : F) (D : Nat) (x y : ExtElem F) : ExtElem F :=
  ⟨reduceBinom A W D (convLanes A x.lanes y.lanes)⟩

/-- **The commit-phase FRI fold in extension arithmetic**: `e0 + β·e1`, where `β`, `e0`, `e1`
are all extension elements. This is the deployed `FriCore.foldCombine` linear form lifted
to the full quartic width (the coset twiddle `x` — likewise an extension element — is carried
by the shell exactly as the abstract `foldCombine` elides it). -/
def extFold (A : FieldArith F) (W : F) (D : Nat) (beta e0 e1 : ExtElem F) : ExtElem F :=
  extAdd A e0 (extMul A W D beta e1)

/-! ## 2. Shape lemmas — the width is preserved. -/

/-- An extension product has exactly `D` lanes, for every `D` (the reduction maps over
`range D`). So `extMul … extDeg …` always yields a `extDeg`-wide element — the fold never
narrows to a scalar. -/
theorem extMul_length (A : FieldArith F) (W : F) (D : Nat) (x y : ExtElem F) :
    (extMul A W D x y).lanes.length = D := by
  simp [extMul, reduceBinom]

#assert_axioms extMul_length

/-- Extension addition preserves the common width. -/
theorem extAdd_length (A : FieldArith F) (x y : ExtElem F) :
    (extAdd A x y).lanes.length = min x.lanes.length y.lanes.length := by
  simp [extAdd]

#assert_axioms extAdd_length

/-! ## 3. The bridge — the scalar model is the `extDeg = 1` restriction.

At width one, `F[X]/(X − W)` is `F` itself: the scalar `LayerOpening.beta : F` and scalar
`foldCombine β x e0 e1 = e0 + β·e1` are precisely `extMul`/`extFold` specialized to `D = 1`.
The three field-arithmetic laws (`add`'s identity on both sides, `mul`'s absorption of
`zero`) enter as HYPOTHESES — never axioms; `intArith` below satisfies them, discharging
them, so the bridge is non-vacuous. -/

/-- Width-one multiplication is base multiplication, given the three arithmetic laws. -/
theorem extMul_extDeg_one (A : FieldArith F) (W a b : F)
    (hz : ∀ z, A.add A.zero z = z) (hz' : ∀ z, A.add z A.zero = z)
    (hmz : A.mul W A.zero = A.zero) :
    extMul A W 1 ⟨[a]⟩ ⟨[b]⟩ = ⟨[A.mul a b]⟩ := by
  have e : extMul A W 1 (⟨[a]⟩ : ExtElem F) ⟨[b]⟩
      = ⟨[A.add (A.add A.zero (A.mul a b)) (A.mul W A.zero)]⟩ := rfl
  rw [e, hmz, hz', hz]

#assert_axioms extMul_extDeg_one

/-- **The scalar-fold bridge.** Width-one `extFold` is exactly the deployed scalar fold
`e0 + β·e1` — i.e. `FriCore.foldCombine β x e0 e1` on the single lanes. So the existing
scalar-shell FRI soundness is the `extDeg = 1` specialization of the extension fold. -/
theorem extFold_extDeg_one (A : FieldArith F) (W beta e0 e1 : F)
    (hz : ∀ z, A.add A.zero z = z) (hz' : ∀ z, A.add z A.zero = z)
    (hmz : A.mul W A.zero = A.zero) :
    extFold A W 1 ⟨[beta]⟩ ⟨[e0]⟩ ⟨[e1]⟩ = ⟨[A.add e0 (A.mul beta e1)]⟩ := by
  unfold extFold
  rw [extMul_extDeg_one A W beta e1 hz hz' hmz]
  rfl

#assert_axioms extFold_extDeg_one

/-- Embed a base scalar as a width-one extension element (the `extDeg = 1` inclusion the
scalar shell implicitly uses). -/
def embScalar (a : F) : ExtElem F := ⟨[a]⟩

/-- Project the head lane — the exact operation `FriChallengerUnified.projBeta` performs on a
derived beta (`headD default`). Round-trips `embScalar`. -/
def projScalar [Inhabited F] (e : ExtElem F) : F := e.lanes.headD default

/-- `projScalar ∘ embScalar = id`: the scalar shell's `projBeta` recovers exactly the base
lane it embedded — the width-one model loses nothing (and, at width > 1, drops the rest,
which §4 shows is soundness-relevant). -/
theorem projScalar_embScalar [Inhabited F] (a : F) : projScalar (embScalar a) = a := rfl

#assert_axioms projScalar_embScalar

/-- **The deployed scalar fold factors through the width-one extension fold.** Given the
linear `FriCore` whose `foldCombine` is `e0 + β·e1` (the `uCore`/deployed shape), the head
of the width-one `extFold` on embedded scalars is exactly `core.foldCombine β x e0 e1`. This
is the precise sense in which the scalar `LayerOpening` fold IS the extension fold restricted
to `extDeg = 1`. -/
theorem scalarFold_is_extDegOne [Inhabited F] (A : FieldArith F) (W beta x e0 e1 : F)
    (core : FriCore F)
    (hcore : core.foldCombine = fun b _x u v => A.add u (A.mul b v))
    (hz : ∀ z, A.add A.zero z = z) (hz' : ∀ z, A.add z A.zero = z)
    (hmz : A.mul W A.zero = A.zero) :
    projScalar (extFold A W 1 (embScalar beta) (embScalar e0) (embScalar e1))
      = core.foldCombine beta x e0 e1 := by
  rw [hcore]
  simp only [embScalar]
  rw [extFold_extDeg_one A W beta e0 e1 hz hz' hmz]
  rfl

#assert_axioms scalarFold_is_extDegOne

/-! ## 4. Denotation against the DEPLOYED quartic field (BabyBear, `W = 11`).

The abstract machinery is pinned to the actual deployed extension: BabyBear
(`p = 2^31 − 2^27 + 1`) with the degree-4 binomial residue `W = 11`. `quarticRef` is the
human-legible quartic binomial product; `extMul … 4` DENOTES it (checked at concrete deployed
points), and the ext width provably carries information the scalar shell discards. -/

/-- The BabyBear prime `p = 2^31 − 2^27 + 1` (`Poseidon2BabyBearW16.P`, restated to keep
this module import-light). -/
def P : Nat := 2013265921

/-- `b^n mod p`, structurally (the module imports no `HPow`). -/
def natPowMod (b : Nat) : Nat → Nat
  | 0 => 1 % P
  | n + 1 => (b * natPowMod b n) % P

/-- The DEPLOYED BabyBear base-field arithmetic (canonical `Nat` representatives `< p`). -/
def babyBear : FieldArith Nat :=
  { add := fun a b => (a + b) % P, mul := fun a b => (a * b) % P,
    pow := natPowMod, zero := 0, one := 1 % P }

/-- The DEPLOYED degree-4 binomial residue: `X^4 = 11` in `BabyBear[X]/(X^4 − 11)`
(`p3-baby-bear/src/baby_bear.rs:66`). -/
def W : Nat := 11

/-- The DEPLOYED extension degree is 4 (`ir2LeafWrapConfig.extDeg`), so the challenges really
are quartic and this width matters. -/
theorem deployed_extDeg_four : ir2LeafWrapConfig.extDeg = 4 := rfl

#assert_axioms deployed_extDeg_four

/-- **The human-legible quartic binomial product** in `F[X]/(X^4 − W)` — the independent
denotation spec `extMul … 4` is checked against:
`c₀ = a₀b₀ + W(a₁b₃+a₂b₂+a₃b₁)`, `c₁ = a₀b₁+a₁b₀ + W(a₂b₃+a₃b₂)`,
`c₂ = a₀b₂+a₁b₁+a₂b₀ + W(a₃b₃)`, `c₃ = a₀b₃+a₁b₂+a₂b₁+a₃b₀`. This is the standard reduction
of `X^4 = W` applied to the degree-6 convolution — the quartic case of p3's `binomial_mul`. -/
def quarticRef (A : FieldArith F) (W : F) (x y : ExtElem F) : ExtElem F :=
  let a := fun i => x.lanes.getD i A.zero
  let b := fun i => y.lanes.getD i A.zero
  let m := A.mul
  let p := A.add
  ⟨[ p (m (a 0) (b 0)) (m W (p (m (a 1) (b 3)) (p (m (a 2) (b 2)) (m (a 3) (b 1))))),
     p (p (m (a 0) (b 1)) (m (a 1) (b 0))) (m W (p (m (a 2) (b 3)) (m (a 3) (b 2)))),
     p (p (m (a 0) (b 2)) (p (m (a 1) (b 1)) (m (a 2) (b 0)))) (m W (m (a 3) (b 3))),
     p (p (m (a 0) (b 3)) (m (a 1) (b 2))) (p (m (a 2) (b 1)) (m (a 3) (b 0))) ]⟩

/-- Two concrete deployed extension elements. -/
def eA : ExtElem Nat := ⟨[1, 2, 3, 4]⟩
def eB : ExtElem Nat := ⟨[5, 6, 7, 8]⟩

/-- **The denotation, over the deployed field.** The general width-`D` `extMul`, at `D = 4`
with the deployed residue `W = 11`, computes exactly the quartic binomial product — its output
equals the independent `quarticRef` formula on the concrete deployed elements. This is the
sense in which the ext fold "denotes the deployed quartic-ext fold". -/
theorem extMul_denotes_quartic_babybear :
    extMul babyBear W 4 eA eB = quarticRef babyBear W eA eB := by decide

#assert_axioms extMul_denotes_quartic_babybear

/-- **The width bites — the scalar shell is genuinely lossy.** Two betas with the SAME head
lane (`2`) but different `X`-lanes — which `FriChallengerUnified.projBeta` (`headD`) CANNOT
tell apart — produce DIFFERENT quartic folds. So squeezing `β` as a scalar (the
`ExtensionFoldWidthResidual`) is not a harmless narrowing: it collapses distinct deployed fold
challenges. -/
theorem ext_width_distinguishes_equal_heads :
    extMul babyBear W 4 ⟨[2, 1, 0, 0]⟩ ⟨[1, 1, 1, 1]⟩
      ≠ extMul babyBear W 4 ⟨[2, 0, 0, 0]⟩ ⟨[1, 1, 1, 1]⟩ := by decide

#assert_axioms ext_width_distinguishes_equal_heads

/-! ### Executable non-vacuity (`#guard`) on concrete deployed elements. -/

-- The quartic product `[1,2,3,4]·[5,6,7,8]` in `BabyBear[X]/(X^4−11)` is `[676,588,386,60]`
-- (all lanes `< p`, so no wrap): c₀ = 5 + 11·61, c₁ = 16 + 11·52, c₂ = 34 + 11·32, c₃ = 60.
#guard (extMul babyBear W 4 eA eB) = ⟨[676, 588, 386, 60]⟩
#guard (extMul babyBear W 4 eA eB).lanes.length = 4
#guard quarticRef babyBear W eA eB = ⟨[676, 588, 386, 60]⟩

-- The ext fold `e0 + β·e1` with a pure-scalar `β = 2`: `[5,6,7,8] + 2·[1,1,1,1] = [7,8,9,10]`.
#guard extFold babyBear W 4 ⟨[2, 0, 0, 0]⟩ eB ⟨[1, 1, 1, 1]⟩ = ⟨[7, 8, 9, 10]⟩

-- The `extDeg = 1` restriction IS base multiplication (`7·9 = 63`) — the scalar model.
#guard extMul babyBear W 1 ⟨[7]⟩ ⟨[9]⟩ = ⟨[63]⟩
#guard extMul babyBear W 1 ⟨[7]⟩ ⟨[9]⟩ = ⟨[babyBear.mul 7 9]⟩
#guard extFold babyBear W 1 ⟨[2]⟩ ⟨[5]⟩ ⟨[9]⟩ = ⟨[babyBear.add 5 (babyBear.mul 2 9)]⟩

-- The width-distinguishing witnesses, spelled out: same head, different products.
#guard extMul babyBear W 4 ⟨[2, 1, 0, 0]⟩ ⟨[1, 1, 1, 1]⟩ = ⟨[13, 3, 3, 3]⟩
#guard extMul babyBear W 4 ⟨[2, 0, 0, 0]⟩ ⟨[1, 1, 1, 1]⟩ = ⟨[2, 2, 2, 2]⟩

/-! ## 5. The extension-width opening shell and linear fold primitive.

This is the `FriVerifier.LayerOpening` shell in ext-width form: `beta x e0 e1` are
`ExtElem F`. `extChainFold` records the post-interpolation linear operation
`even + beta*odd`; §6 supplies the complete p3 evaluation-pair interpolation, Merkle walk,
transcript binding, and apex-facing verifier. -/

/-- A FRI layer opening with EXTENSION-VALUED fold data (the deployed reality). The Merkle
`leaf`/`siblings` stay base-field lists (the commitment scheme is over the base field). -/
structure ExtLayerOpening (F : Type) where
  beta : ExtElem F
  x : ExtElem F
  e0 : ExtElem F
  e1 : ExtElem F
  /-- The complete `2^log_arity` evaluation row for log-arity 2/3.  The deployed
  arity-two representation remains in `e0`/`e1`; wider rows cannot be represented
  by a fabricated pair and therefore use this field. -/
  evals : List (ExtElem F) := []
  /-- The literal serialized FRI sibling values (the row with the verifier-carried
  value omitted).  The apex path reconstructs the full row from these plus the
  carried value and query index; `evals` is retained for compact KAT fixtures. -/
  siblingValues : List (ExtElem F) := []
  leaf : List F
  siblings : List (List F)
  deriving Repr, DecidableEq

/-- Fold already-separated even/odd terms through a chain using `even + beta*odd`.
The deployed evaluation-pair walk is `friChainGoExt` below. -/
def extChainFold (A : FieldArith F) (W : F) (D : Nat) :
    ExtElem F → List (ExtLayerOpening F) → ExtElem F
  | acc, [] => acc
  | _acc, lo :: rest => extChainFold A W D (extFold A W D lo.beta lo.e0 lo.e1) rest

/-- The ext chain-fold denotes iterated extension folding — a two-layer chain over the
deployed field, spelled out. -/
theorem extChainFold_two_babybear :
    extChainFold babyBear W 4 eA
        [ { beta := ⟨[2, 0, 0, 0]⟩, x := ⟨[1, 0, 0, 0]⟩, e0 := eB, e1 := ⟨[1, 1, 1, 1]⟩,
            leaf := [], siblings := [] },
          { beta := ⟨[1, 0, 0, 0]⟩, x := ⟨[1, 0, 0, 0]⟩, e0 := ⟨[7, 8, 9, 10]⟩,
            e1 := ⟨[0, 0, 0, 0]⟩, leaf := [], siblings := [] } ]
      = ⟨[7, 8, 9, 10]⟩ := by decide

#assert_axioms extChainFold_two_babybear

-- Non-vacuity: the first layer folds `eB + 2·[1,1,1,1] = [7,8,9,10]`; the second adds
-- `1·[0,0,0,0] = 0`, leaving `[7,8,9,10]`.
#guard (extChainFold babyBear W 4 eA []).lanes = eA.lanes

/-! ## 6. The deployed p3 `fold_row`, in extension arithmetic.

`extFold` above is the linear `even + beta * odd` primitive.  p3's verifier receives
the two evaluations `f(x)` and `f(-x)`, so it first derives those even/odd terms.  The
following is the complete arity-two `TwoAdicFriFolding::fold_row` formula used by the
deployed verifier and by `chain/gnark/fri_query.go`:

`(e0 + e1)/2 + beta * (e0 - e1) * inv(x)/2`.

The inverse coset point is not a free prover value.  `ExtFriCore.domainPointInv` derives it
from the parent query index and height, and `friChainGoExt` checks both the carried `x` and
`x * invX = 1`.  This mirrors the deployed verifier's bit-selected inverse-generator table
without baking that table into this generic module. -/

/-- Arithmetic needed in addition to `FieldArith` for p3's interpolation formula.  `half`
is checked by `foldConsistentExt` to satisfy `2 * half = 1`; `neg` supplies base-field
subtraction lane-wise. -/
structure ExtFriArith (F : Type) where
  base : FieldArith F
  neg : F → F
  half : F
  /-- Inversion in the configured extension field.  The verifier never trusts the
  result blindly: every accepting use checks `x * inv x = 1`. -/
  inv : ExtElem F → ExtElem F := fun _ => ⟨[]⟩

/-- Embed a base-field element as a width-`D` extension constant. -/
def extOfBase (A : FieldArith F) (D : Nat) (a : F) : ExtElem F :=
  ⟨(List.range D).map fun i => if i = 0 then a else A.zero⟩

/-- Scalar multiplication of an extension element by a base-field element. -/
def extScale (A : FieldArith F) (a : F) (x : ExtElem F) : ExtElem F :=
  ⟨x.lanes.map (A.mul a)⟩

/-- Extension negation is coefficient-wise base-field negation. -/
def extNeg (E : ExtFriArith F) (x : ExtElem F) : ExtElem F :=
  ⟨x.lanes.map E.neg⟩

/-- Extension subtraction. -/
def extSub (E : ExtFriArith F) (x y : ExtElem F) : ExtElem F :=
  extAdd E.base x (extNeg E y)

/-- **The deployed arity-two p3 fold.**  `invX` is the verifier-derived inverse of `x`;
the caller checks that relation before accepting.  Every multiplication involving `beta`
or an evaluation is the quartic `extMul`, never a head-lane projection. -/
def extFoldCombine (E : ExtFriArith F) (W : F) (D : Nat)
    (beta x invX e0 e1 : ExtElem F) : ExtElem F :=
  let sumHalf := extScale E.base E.half (extAdd E.base e0 e1)
  let diff := extSub E e0 e1
  let betaDiffInvX := extMul E.base W D (extMul E.base W D beta diff) invX
  let oddTerm := extScale E.base E.half betaDiffInvX
  -- `x` is deliberately present in the denotation: the accepting chain checks
  -- `x * invX = 1` and pins `x` to the domain point before calling this function.
  let _ := x
  extAdd E.base sumHalf oddTerm

/-- The scalar arity-two formula used for the exact `extDeg = 1` restriction theorem. -/
def scalarFoldCombine (E : ExtFriArith F) (beta invX e0 e1 : F) : F :=
  E.base.add
    (E.base.mul E.half (E.base.add e0 e1))
    (E.base.mul E.half
      (E.base.mul (E.base.mul beta (E.base.add e0 (E.neg e1))) invX))

/-- **Scalar restriction bridge for the real p3 formula.**  At extension degree one,
`extFoldCombine` is exactly `scalarFoldCombine`; no challenge or folded-value information
is lost.  The elementary zero laws are hypotheses on the generic arithmetic, and are
discharged concretely by the deployed BabyBear witness below. -/
theorem extFoldCombine_extDeg_one (E : ExtFriArith F) (W beta x invX e0 e1 : F)
    (hz : ∀ z, E.base.add E.base.zero z = z)
    (hz' : ∀ z, E.base.add z E.base.zero = z)
    (hmz : E.base.mul W E.base.zero = E.base.zero) :
    extFoldCombine E W 1 (embScalar beta) (embScalar x) (embScalar invX)
        (embScalar e0) (embScalar e1)
      = embScalar (scalarFoldCombine E beta invX e0 e1) := by
  have hsub : extSub E (embScalar e0) (embScalar e1)
      = embScalar (E.base.add e0 (E.neg e1)) := rfl
  have hmul₁ : extMul E.base W 1 (embScalar beta)
        (embScalar (E.base.add e0 (E.neg e1)))
      = embScalar (E.base.mul beta (E.base.add e0 (E.neg e1))) := by
    simpa only [embScalar] using
      (extMul_extDeg_one E.base W beta (E.base.add e0 (E.neg e1)) hz hz' hmz)
  have hmul₂ : extMul E.base W 1
        (embScalar (E.base.mul beta (E.base.add e0 (E.neg e1)))) (embScalar invX)
      = embScalar (E.base.mul (E.base.mul beta (E.base.add e0 (E.neg e1))) invX) := by
    simpa only [embScalar] using
      (extMul_extDeg_one E.base W (E.base.mul beta (E.base.add e0 (E.neg e1))) invX
        hz hz' hmz)
  dsimp only [extFoldCombine]
  rw [hsub]
  rw [hmul₁, hmul₂]
  rfl

#assert_axioms extFoldCombine_extDeg_one

/-- The bridge in the legacy `FriCore` API: whenever its scalar `foldCombine` is the
arity-two p3 formula at `x`/`invX`, it is exactly the head of the width-one extension
fold.  This is the transport used to regard the retained scalar check as a restriction,
not a competing semantics. -/
theorem friCoreFold_is_extDegOne [Inhabited F]
    (E : ExtFriArith F) (W beta x invX e0 e1 : F) (core : FriCore F)
    (hcore : core.foldCombine beta x e0 e1 = scalarFoldCombine E beta invX e0 e1)
    (hz : ∀ z, E.base.add E.base.zero z = z)
    (hz' : ∀ z, E.base.add z E.base.zero = z)
    (hmz : E.base.mul W E.base.zero = E.base.zero) :
    projScalar (extFoldCombine E W 1 (embScalar beta) (embScalar x) (embScalar invX)
      (embScalar e0) (embScalar e1)) = core.foldCombine beta x e0 e1 := by
  rw [extFoldCombine_extDeg_one E W beta x invX e0 e1 hz hz' hmz]
  rw [hcore]
  rfl

#assert_axioms friCoreFold_is_extDegOne

/-- The calibration surface below the ext FRI walk.  `leafHash` is p3's
`PaddingFreeSponge` over the eight ordered lanes of `(e0,e1)`; `compress` is its binary
Merkle compression.  `domainPoint` and `domainPointInv` are the two-adic generator tables
indexed exactly by the parent query index and folded height. -/
structure ExtFriCore (F : Type) where
  compress : List F → List F → List F
  leafHash : ExtElem F → ExtElem F → List F
  domainPoint : Nat → Nat → ExtElem F
  domainPointInv : Nat → Nat → ExtElem F
  /-- Padding-free sponge of a complete higher-arity row, in serialized row order. -/
  rowLeafHash : List (ExtElem F) → List F := fun _ => []
  /-- The bit-reversed two-adic evaluation points used by p3 `fold_row(index,
  log_height, log_arity, ...)`.  Producing the BabyBear generator table is a
  calibrated arithmetic leaf; Lagrange interpolation over the returned points is
  concrete below. -/
  rowPoints : Nat → Nat → Nat → List F := fun _ _ _ => []

/-- A complete extension-valued FRI query.  `initialEval` is the reduced PCS opening that
p3 calls `folded_eval` before entering the commit-phase loop. -/
structure ExtQueryOpening (F : Type) where
  index : Nat
  initialEval : ExtElem F
  layers : List (ExtLayerOpening F)
  deriving Repr, DecidableEq

/-- Every extension-valued field in a layer has exactly the configured width. -/
def extLayerShape (D : Nat) (lo : ExtLayerOpening F) : Bool :=
  decide (lo.beta.lanes.length = D)
    && decide (lo.x.lanes.length = D)
    && decide (lo.e0.lanes.length = D)
    && decide (lo.e1.lanes.length = D)

/-- Walk the deployed commit-phase chain.  The carried value occupies row slot zero or
one according to the current query bit; the Merkle opening is checked at the parent index;
the coset point and inverse are verifier-derived; and the next carried value is the full
extension-field `extFoldCombine`. -/
def friChainGoExt [DecidableEq F] (core : ExtFriCore F) (E : ExtFriArith F)
    (W : F) (D : Nat) :
    Nat → Nat → ExtElem F → List (List F × ExtLayerOpening F) → Bool × ExtElem F
  | _, _, expected, [] => (true, expected)
  | idx, logHeight, expected, (commitment, lo) :: rest =>
      let parentIdx := idx / 2
      let nextHeight := logHeight - 1
      let x := core.domainPoint parentIdx nextHeight
      let invX := core.domainPointInv parentIdx nextHeight
      let carried := if idx % 2 = 0 then decide (lo.e0 = expected) else decide (lo.e1 = expected)
      let leaf := core.leafHash lo.e0 lo.e1
      let ok := extLayerShape D lo
        && decide (lo.x = x)
        && decide (extMul E.base W D x invX = extOfBase E.base D E.base.one)
        && decide (lo.leaf = leaf)
        && merkleVerify core.compress parentIdx lo.leaf lo.siblings commitment
        && carried
      let next := extFoldCombine E W D lo.beta lo.x invX lo.e0 lo.e1
      let (okRest, final) := friChainGoExt core E W D parentIdx nextHeight next rest
      (ok && okRest, final)

/-- **The concrete quartic-extension FRI check.**  It binds every query to the continued
transcript's index and complete beta lanes, requires one layer per commit-phase commitment,
walks the full extension chain, and compares all `D` lanes with the flattened final
extension coefficient in `BatchProofData.finalPoly`. -/
def foldConsistentExt [DecidableEq F] (core : ExtFriCore F) (E : ExtFriArith F)
    (W : F) (D logN : Nat) (proof : BatchProofData F)
    (queries : List (ExtQueryOpening F)) (betas : List (List F)) (qidx : List Nat) : Bool :=
  decide (E.base.mul (E.base.add E.base.one E.base.one) E.half = E.base.one)
    && decide (proof.finalPoly.length = D)
    && decide (proof.friCommitments.length = betas.length)
    && decide (queries.length = qidx.length)
    && decide (queries ≠ [])
    && betas.all (fun beta => decide (beta.length = D))
    && (queries.zip qidx).all fun qi =>
      let q := qi.1
      let index := qi.2
      let chain := friChainGoExt core E W D q.index logN q.initialEval
        (proof.friCommitments.zip q.layers)
      decide (q.index = index)
        && decide (q.initialEval.lanes.length = D)
        && decide (q.layers.length = proof.friCommitments.length)
        && (betas.zip q.layers).all (fun bl => decide (bl.2.beta.lanes = bl.1))
        && chain.1
        && decide (chain.2 = (⟨proof.finalPoly⟩ : ExtElem F))

/-! ## 7. Generic deployed rows: log-arity 1/2/3 without pair laundering.

The p3 verifier reconstructs a complete row of `2^log_arity` extension evaluations,
authenticates that row, and calls `TwoAdicFriFolding::fold_row`.  For arity two p3
uses the optimized even/odd formula above.  For arity four/eight it evaluates the
unique row-interpolating polynomial at the single transcript challenge `beta`.
`lagrangeFoldExt` is that algorithm literally; the point order is supplied by the
same bit-reversed two-adic table as the deployed verifier. -/

/-- Product in the configured extension field. -/
def extProd (A : FieldArith F) (W : F) (D : Nat) (xs : List (ExtElem F)) : ExtElem F :=
  xs.foldl (extMul A W D) (extOfBase A D A.one)

/-- Return the row value immediately when `beta` is one of the interpolation points,
matching p3's early-return branch in `lagrange_interpolate_at`. -/
def exactPointEval [DecidableEq F] (A : FieldArith F) (D : Nat) (beta : ExtElem F) :
    List F → List (ExtElem F) → Option (ExtElem F)
  | x :: xs, y :: ys =>
      if beta = extOfBase A D x then some y else exactPointEval A D beta xs ys
  | _, _ => none

/-- One Lagrange term
`y_i * Π_{j≠i}(beta-x_j) / Π_{j≠i}(x_i-x_j)` together with the checked-inverse tooth.
The denominator is embedded from the base field, exactly because p3's row points are
two-adic base-field elements. -/
def lagrangeTermExt [DecidableEq F] (E : ExtFriArith F) (W : F) (D : Nat)
    (xs : List F) (ys : List (ExtElem F)) (beta : ExtElem F) (i : Nat) :
    Bool × ExtElem F :=
  let js := (List.range xs.length).filter (fun j => j ≠ i)
  let xi := xs.getD i E.base.zero
  let numerator := js.foldl (fun acc j =>
      extMul E.base W D acc
        (extSub E beta (extOfBase E.base D (xs.getD j E.base.zero))))
      (extOfBase E.base D E.base.one)
  let denominator := js.foldl (fun acc j =>
      E.base.mul acc (E.base.add xi (E.neg (xs.getD j E.base.zero)))) E.base.one
  let denominatorExt := extOfBase E.base D denominator
  let denominatorInv := E.inv denominatorExt
  let inverseOk := decide
    (extMul E.base W D denominatorExt denominatorInv = extOfBase E.base D E.base.one)
  let yi := ys.getD i (extOfBase E.base D E.base.zero)
  (inverseOk, extMul E.base W D yi (extMul E.base W D numerator denominatorInv))

/-- Faithful `fold_row` for a complete row.  Arity 4/8 is genuine Lagrange
interpolation, not repeated use of a prover-supplied pair. -/
def lagrangeFoldExt [DecidableEq F] (E : ExtFriArith F) (W : F) (D : Nat)
    (xs : List F) (ys : List (ExtElem F)) (beta : ExtElem F) : Bool × ExtElem F :=
  match exactPointEval E.base D beta xs ys with
  | some y => (true, y)
  | none =>
      let terms := (List.range xs.length).map (lagrangeTermExt E W D xs ys beta)
      (terms.all (fun t => t.1),
        terms.foldl (fun acc t => extAdd E.base acc t.2)
          (extOfBase E.base D E.base.zero))

/-- One reconstructed commit-phase round.  `beta` is verifier-derived, never read
from `ExtLayerOpening.beta`; `logArity` is the parsed serialized schedule. -/
structure ExtRound (F : Type) where
  commitment : List F
  logArity : Nat
  beta : ExtElem F
  opening : ExtLayerOpening F

/-- Exact zipper: any count mismatch rejects instead of silently truncating. -/
def zipExtRounds : List (List F) → List Nat → List (List F) → List (ExtLayerOpening F) →
    Option (List (ExtRound F))
  | [], [], [], [] => some []
  | c :: cs, a :: as, b :: bs, o :: os =>
      match zipExtRounds cs as bs os with
      | some rs => some ({ commitment := c, logArity := a, beta := ⟨b⟩, opening := o } :: rs)
      | none => none
  | _, _, _, _ => none

/-- Insert the verifier-carried evaluation at the serialized query position. -/
def insertAtExact {α : Type} : Nat → α → List α → Option (List α)
  | 0, x, xs => some (x :: xs)
  | n + 1, x, y :: ys =>
      match insertAtExact n x ys with
      | some zs => some (y :: zs)
      | none => none
  | _ + 1, _, [] => none

/-- Reconstruct the complete row from the serialized sibling values whenever they
have the deployed `arity-1` shape.  Legacy KAT rows fall back to their explicit
pair/row fields; the apex decoder uses the first branch. -/
def reconstructedLayerEvals (logArity pos : Nat)
    (expected : ExtElem F) (lo : ExtLayerOpening F) : Option (List (ExtElem F)) :=
  let arity := 2 ^ logArity
  if lo.siblingValues.length = arity - 1 then
    insertAtExact pos expected lo.siblingValues
  else if logArity = 1 then some [lo.e0, lo.e1]
  else if lo.evals.length = arity then some lo.evals
  else none

/-- The complete variable-arity p3 commit-phase walk.  Query index, beta, domain
point, and inverse are all verifier-derived.  The KAT view contributes only the
serialized evaluation row and Merkle authentication material. -/
def friChainGoExtAny [DecidableEq F] (core : ExtFriCore F) (E : ExtFriArith F)
    (W : F) (D : Nat) :
    Nat → Nat → ExtElem F → List (ExtRound F) → Bool × ExtElem F
  | _, _, expected, [] => (true, expected)
  | idx, logHeight, expected, r :: rest =>
      let arity := 2 ^ r.logArity
      let parentIdx := idx / arity
      let nextHeight := logHeight - r.logArity
      let lo := r.opening
      match reconstructedLayerEvals r.logArity (idx % arity) expected lo with
      | none => (false, extOfBase E.base D E.base.zero)
      | some evals =>
          let rowShape := decide (0 < r.logArity)
            && decide (r.logArity ≤ logHeight)
            && decide (evals.length = arity)
            && evals.all (fun e => decide (e.lanes.length = D))
          let carried := decide
            (evals.getD (idx % arity) (extOfBase E.base D E.base.zero) = expected)
          let leaf := if r.logArity = 1 then
              core.leafHash (evals.headD (extOfBase E.base D E.base.zero))
                (evals.getD 1 (extOfBase E.base D E.base.zero))
            else core.rowLeafHash evals
          let merkleOk := merkleVerify core.compress parentIdx leaf lo.siblings r.commitment
          let folded := if r.logArity = 1 then
              let x := core.domainPoint parentIdx nextHeight
              let invX := core.domainPointInv parentIdx nextHeight
              (decide (extMul E.base W D x invX = extOfBase E.base D E.base.one),
                extFoldCombine E W D r.beta x invX
                  (evals.headD (extOfBase E.base D E.base.zero))
                  (evals.getD 1 (extOfBase E.base D E.base.zero)))
            else
              let xs := core.rowPoints parentIdx nextHeight r.logArity
              if xs.length = arity then lagrangeFoldExt E W D xs evals r.beta
              else (false, extOfBase E.base D E.base.zero)
          let (okRest, final) := friChainGoExtAny core E W D parentIdx nextHeight folded.2 rest
          (rowShape && carried && merkleOk && folded.1 && okRest, final)

/-- Variable-arity extension FRI check.  It consumes the serialized log-arity
schedule, derived betas/query indices, complete rows, and all final lanes. -/
def foldConsistentExtAny [DecidableEq F] (core : ExtFriCore F) (E : ExtFriArith F)
    (W : F) (D logN : Nat) (toNat : F → Nat) (proof : BatchProofData F)
    (queries : List (ExtQueryOpening F)) (betas : List (List F)) (qidx : List Nat) : Bool :=
  let arities := proof.friLogArities.map toNat
  decide (proof.finalPoly.length = D)
    && decide (proof.friCommitments.length = betas.length)
    && decide (proof.friCommitments.length = arities.length)
    && decide (queries.length = qidx.length)
    && decide (queries ≠ [])
    && betas.all (fun beta => decide (beta.length = D))
    && (queries.zip qidx).all fun qi =>
      let q := qi.1
      let index := qi.2
      match zipExtRounds proof.friCommitments arities betas q.layers with
      | none => false
      | some rounds =>
          let chain := friChainGoExtAny core E W D q.index logN q.initialEval rounds
          decide (q.index = index)
            && decide (q.initialEval.lanes.length = D)
            && chain.1
            && decide (chain.2 = (⟨proof.finalPoly⟩ : ExtElem F))

/-! ## 8. Full-width single-AIR OOD arithmetic.

Unlike the legacy scalar record, this view does not carry `alpha`, `zeta`,
`vanishing`, or `invVanishing`.  The first two come from the one continued
transcript; the latter two are computed here in quartic arithmetic. -/

structure ExtSingleAirOpening (F : Type) where
  degreeBits : Nat
  expectedDegreeBits : Nat
  constraintEvals : List (ExtElem F)
  zps : List (ExtElem F)
  quotientChunks : List (ExtElem F)
  logupCumSum : ExtElem F
  deriving Repr, DecidableEq

def extPow (A : FieldArith F) (W : F) (D : Nat) (x : ExtElem F) : Nat → ExtElem F
  | 0 => extOfBase A D A.one
  | n + 1 => extMul A W D x (extPow A W D x n)

def foldedConstraintsExt (A : FieldArith F) (W : F) (D : Nat)
    (alpha : ExtElem F) (o : ExtSingleAirOpening F) : ExtElem F :=
  o.constraintEvals.foldl (fun acc c => extAdd A (extMul A W D acc alpha) c)
    (extOfBase A D A.zero)

def recomposedQuotientExt (A : FieldArith F) (W : F) (D : Nat)
    (o : ExtSingleAirOpening F) : ExtElem F :=
  (o.zps.zip o.quotientChunks).foldr
    (fun p acc => extAdd A (extMul A W D p.1 p.2) acc) (extOfBase A D A.zero)

def extSingleAirShape (D : Nat) (o : ExtSingleAirOpening F) : Bool :=
  decide (o.constraintEvals ≠ [])
    && decide (o.zps.length = o.quotientChunks.length)
    && decide (o.zps ≠ [])
    && o.constraintEvals.all (fun e => decide (e.lanes.length = D))
    && o.zps.all (fun e => decide (e.lanes.length = D))
    && o.quotientChunks.all (fun e => decide (e.lanes.length = D))
    && decide (o.logupCumSum.lanes.length = D)

/-- Faithful quartic single-AIR identity at transcript-derived `alpha`/`zeta`. -/
def singleAirOkExt [DecidableEq F] (E : ExtFriArith F) (W : F) (D : Nat)
    (alpha zeta : ExtElem F) (o : ExtSingleAirOpening F) : Bool :=
  let one := extOfBase E.base D E.base.one
  let vanishing := extSub E (extPow E.base W D zeta (2 ^ o.degreeBits)) one
  let invVanishing := E.inv vanishing
  extSingleAirShape D o
    && decide (o.degreeBits = o.expectedDegreeBits)
    && decide (extMul E.base W D vanishing invVanishing = one)
    && decide (extMul E.base W D (foldedConstraintsExt E.base W D alpha o) invVanishing
      = recomposedQuotientExt E.base W D o)

def busSumExt (E : ExtFriArith F) (D : Nat) (os : List (ExtSingleAirOpening F)) : ExtElem F :=
  (os.map (fun o => o.logupCumSum)).foldr (extAdd E.base) (extOfBase E.base D E.base.zero)

def batchTablesCheckExt [DecidableEq F] (E : ExtFriArith F) (W : F) (D : Nat)
    (alpha zeta : ExtElem F) (os : List (ExtSingleAirOpening F)) : Bool :=
  decide (os ≠ [])
    && os.all (singleAirOkExt E W D alpha zeta)
    && decide (busSumExt E D os = extOfBase E.base D E.base.zero)

/-- The only verifier view still supplied at the apex: serialized/Merkle evaluation
material plus AIR-derived OOD evaluations.  Fiat-Shamir challenges, query indices,
domain points, vanishing, and inverses are deliberately absent and reconstructed by
the verifier itself. -/
structure ExtVerifierView (F : Type) where
  queries : List (ExtQueryOpening F)
  singleAirOpenings : List (ExtSingleAirOpening F)
  deriving Repr, DecidableEq

/-- The apex-facing faithful verifier.  The old faithful scalar verifier remains as a
redundant conjunct solely so all existing `verifyAlgo` soundness theorems transport without
changing `DeployedRefines`; acceptance additionally requires the deployed quartic
width/residue, the variable-arity extension fold-chain, and the full-width OOD identity. -/
def verifyAlgoUnifiedFaithfulExt [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F) : Bool :=
  let d := Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    perm RATE toNat params initState logN proof pub
  Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnifiedFaithful
      perm RATE toNat params vk core A initState logN proof pub
    && (decide (params.extDeg = 4)
      && decide (toNat W = 11)
      && foldConsistentExtAny extCore extA W params.extDeg logN toNat proof
          view.queries d.betas d.qidx
      && batchTablesCheckExt extA W params.extDeg ⟨d.constraintAlpha⟩ ⟨d.ζ⟩
          view.singleAirOpenings)

/-- Extension-faithful acceptance strengthens the established faithful verifier. -/
theorem verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful
    {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN proof pub view = true) :
    Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnifiedFaithful
      perm RATE toNat params vk core A initState logN proof pub = true := by
  unfold verifyAlgoUnifiedFaithfulExt at hacc
  simp only [Bool.and_eq_true] at hacc
  exact hacc.1

#assert_axioms verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful

/-- Extension-faithful acceptance therefore also strengthens the existing unified verifier. -/
theorem verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified
    {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN proof pub view = true) :
    Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnified
      perm RATE toNat params vk core A initState logN proof pub = true := by
  apply Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnifiedFaithful_imp_verifyAlgoUnified
  exact verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful
    perm RATE toNat params vk core A extCore extA W initState logN proof pub view hacc

#assert_axioms verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified

/-! ### Executable bite through `foldConsistentExt`.

Take `f(x)=v`, `f(-x)=-v`, `x=1`.  The deployed formula reduces to `beta*v`, exactly
the multiplication used by `ext_width_distinguishes_equal_heads`.  The two beta witnesses
below have the same head but distinct quartic folds.  The actual check accepts the honest
four-lane final value, rejects a final value with the same lane zero and a tampered lane one,
and rejects the equal-head beta substitution against the transcript-bound full beta. -/

def babyBearNeg (a : Nat) : Nat :=
  if a % P = 0 then 0 else P - (a % P)

def babyBearFriArith : ExtFriArith Nat :=
  { base := babyBear, neg := babyBearNeg, half := 1006632961,
    -- The executable fixtures below only invert the extension unit; accepting
    -- uses check the product, so this calibration cannot validate a non-unit.
    inv := fun x => x }

private def biteV : ExtElem Nat := ⟨[1, 1, 1, 1]⟩
private def biteNegV : ExtElem Nat := ⟨[P - 1, P - 1, P - 1, P - 1]⟩
private def biteBeta : ExtElem Nat := ⟨[2, 1, 0, 0]⟩
private def biteBetaHeadOnly : ExtElem Nat := ⟨[2, 0, 0, 0]⟩
private def biteX : ExtElem Nat := ⟨[1, 0, 0, 0]⟩

private def biteCore : ExtFriCore Nat :=
  { compress := fun a b => [a.headD 0 * 7 + b.headD 0 * 13 + 1]
    leafHash := fun e0 e1 => e0.lanes ++ e1.lanes
    domainPoint := fun _ _ => biteX
    domainPointInv := fun _ _ => biteX }

private def biteLayer : ExtLayerOpening Nat :=
  { beta := biteBeta, x := biteX, e0 := biteV, e1 := biteNegV,
    leaf := biteV.lanes ++ biteNegV.lanes, siblings := [] }

private def biteFinal : ExtElem Nat :=
  extFoldCombine babyBearFriArith W 4 biteBeta biteX biteX biteV biteNegV

private def biteProof (final : ExtElem Nat) : BatchProofData Nat :=
  { traceCommit := [], friCommitments := [biteLayer.leaf], finalPoly := final.lanes,
    queries := [], exposedSegment := [] }

private def biteQuery (layer : ExtLayerOpening Nat) : ExtQueryOpening Nat :=
  { index := 0, initialEval := biteV, layers := [layer] }

-- The formula reaches the exact multiplication from `ext_width_distinguishes_equal_heads`.
#guard biteFinal = extMul babyBear W 4 biteBeta biteV
#guard biteBeta.lanes.headD 0 = biteBetaHeadOnly.lanes.headD 0
#guard extMul babyBear W 4 biteBeta biteV ≠ extMul babyBear W 4 biteBetaHeadOnly biteV

-- Honest acceptance is non-vacuous.
#guard foldConsistentExt biteCore babyBearFriArith W 4 1 (biteProof biteFinal)
  [biteQuery biteLayer] [biteBeta.lanes] [0] = true

private def biteHigherLaneTamper : ExtElem Nat :=
  ⟨biteFinal.lanes.headD 0 :: (biteFinal.lanes.getD 1 0 + 1) :: biteFinal.lanes.drop 2⟩

-- Lane zero is literally unchanged, but the real extension fold rejects the higher-lane edit.
#guard biteHigherLaneTamper.lanes.headD 0 = biteFinal.lanes.headD 0
#guard foldConsistentExt biteCore babyBearFriArith W 4 1 (biteProof biteHigherLaneTamper)
  [biteQuery biteLayer] [biteBeta.lanes] [0] = false

private def biteHeadOnlyLayer : ExtLayerOpening Nat :=
  { biteLayer with beta := biteBetaHeadOnly }

-- Equal head lane is insufficient: the actual checker binds all four transcript beta lanes.
#guard foldConsistentExt biteCore babyBearFriArith W 4 1 (biteProof biteFinal)
  [biteQuery biteHeadOnlyLayer] [biteBeta.lanes] [0] = false

/-! The same bite through the complete apex-facing predicate.  This fixture retains the
continued transcript, scalar restriction, genuine single-AIR quotient identity, and the
quartic fold simultaneously; it rules out an accidentally-unsatisfiable conjunction. -/

private def fullPerm : List Nat → List Nat :=
  fun _ => [0, 0, 0, 0, 0, 0, 0, 2] ++ List.replicate 8 0
private def fullRate : Nat := 8
private def fullInit : List Nat := List.replicate 16 0
private def fullParams : FriParams :=
  { logBlowup := 1, numQueries := 1, powBits := 0, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 4 }
private def fullVk : RecursionVk Nat := ⟨fun _ => true⟩
private def fullPub : WrapPublics Nat := ⟨[7, 8, 9]⟩
private def fullScalarCore : FriCore Nat :=
  { compress := fun a b => [a.headD 0 * 7 + b.headD 0 * 13 + 1]
    foldCombine := fun beta _x e0 e1 => e0 + beta * e1 }

private def fullStub : BatchProofData Nat :=
  { degreeBitsPreamble := [1], baseDegreeBitsPreamble := [1],
    preprocessedWidthPreamble := [0], traceCommit := [91],
    friCommitments := [biteLayer.leaf], finalPoly := [0, 0, 0, 0], queries := [],
    exposedSegment := fullPub.segment, quotientCommit := [6], openedEvaluations := [11, 12],
    friLogArities := [1], powWitness := [0] }

private def fullBeta : ExtElem Nat :=
  ⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullStub fullPub).betas.headD []⟩

private def fullExtLayer : ExtLayerOpening Nat :=
  { biteLayer with beta := fullBeta }

private def fullFinal : ExtElem Nat :=
  extFoldCombine babyBearFriArith W 4 fullBeta biteX biteX biteV biteNegV

private def fullPreProof : BatchProofData Nat :=
  { fullStub with
    finalPoly := fullFinal.lanes
    oodPoint := (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
      fullPerm fullRate id fullParams fullInit 1 fullStub fullPub).ζ }

private def fullQidx : Nat :=
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullPreProof fullPub).qidx.headD 0

private def fullScalarL0 : LayerOpening Nat :=
  { beta := fullBeta.lanes.headD 0, x := 1, e0 := fullFinal.lanes.headD 0, e1 := 0,
    leaf := fullPreProof.traceCommit, siblings := [] }

private def fullScalarL1 : LayerOpening Nat :=
  { beta := 0, x := 1, e0 := fullFinal.lanes.headD 0, e1 := 0,
    leaf := fullExtLayer.leaf, siblings := [] }

private def fullPowMod (m b : Nat) : Nat → Nat
  | 0 => 1 % m
  | n + 1 => (b * fullPowMod m b n) % m

private def fullScalarArith : FieldArith Nat :=
  { add := fun a b => (a + b) % 17, mul := fun a b => (a * b) % 17,
    pow := fullPowMod 17, zero := 0, one := 1 }

private def fullAlpha : Nat :=
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullPreProof fullPub).constraintAlpha.headD 0
private def fullZeta : Nat := fullPreProof.oodPoint.headD 0
private def fullVanishing : Nat := (fullZeta % 17 + 16) % 17
private def fullInvVanishing : Nat := fullPowMod 17 fullVanishing 15

private def fullAir : Dregg2.Circuit.BatchTablesSingleAir.SingleAirOpening Nat :=
  { zeta := fullZeta, degreeBits := 0, expectedDegreeBits := 0, alpha := fullAlpha,
    constraintEvals := [1], zps := [1], quotientChunks := [fullInvVanishing],
    vanishing := fullVanishing, invVanishing := fullInvVanishing, logupCumSum := 0 }

private def fullProof : BatchProofData Nat :=
  { fullPreProof with
    queries := [{ index := fullQidx, layers := [fullScalarL0, fullScalarL1] }],
    singleAirOpenings := [fullAir] }

private def fullExtQuery : ExtQueryOpening Nat :=
  { index := fullQidx,
    initialEval := if fullQidx % 2 = 0 then biteV else biteNegV,
    layers := [fullExtLayer] }

private def fullAlphaExt : ExtElem Nat :=
  ⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullProof fullPub).constraintAlpha⟩

private def fullZetaExt : ExtElem Nat :=
  ⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullProof fullPub).ζ⟩

private def fullExtOne : ExtElem Nat := extOfBase babyBear 4 babyBear.one

/-- Full-width OOD fixture: `ζ=2`, degree bits zero, so `Z_H(ζ)=1`; with constraints
`[1,1]`, the Horner RLC is `alpha+1` in all four lanes. -/
private def fullExtAir : ExtSingleAirOpening Nat :=
  { degreeBits := 0, expectedDegreeBits := 0,
    constraintEvals := [fullExtOne, fullExtOne], zps := [fullExtOne],
    quotientChunks := [extAdd babyBear fullAlphaExt fullExtOne],
    logupCumSum := extOfBase babyBear 4 babyBear.zero }

private def fullExtView : ExtVerifierView Nat :=
  { queries := [fullExtQuery], singleAirOpenings := [fullExtAir] }

-- The complete apex-facing predicate has an honest accepting pole.
#guard Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnifiedFaithful
  fullPerm fullRate id fullParams fullVk fullScalarCore fullScalarArith fullInit 1
  fullProof fullPub = true
#guard foldConsistentExt biteCore babyBearFriArith W 4 1 fullProof [fullExtQuery]
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullProof fullPub).betas
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    fullPerm fullRate id fullParams fullInit 1 fullProof fullPub).qidx = true
#guard verifyAlgoUnifiedFaithfulExt fullPerm fullRate id fullParams fullVk fullScalarCore
  fullScalarArith biteCore babyBearFriArith W fullInit 1 fullProof fullPub fullExtView = true

-- Keeping lane zero fixed while changing lane one makes the COMPLETE predicate red.
private def fullTamperedFinal : ExtElem Nat :=
  ⟨fullFinal.lanes.headD 0 :: (fullFinal.lanes.getD 1 0 + 1) :: fullFinal.lanes.drop 2⟩

private def fullHigherLaneTamper : BatchProofData Nat :=
  { fullProof with finalPoly := fullTamperedFinal.lanes }

#guard fullHigherLaneTamper.finalPoly.headD 0 = fullProof.finalPoly.headD 0
#guard verifyAlgoUnifiedFaithfulExt fullPerm fullRate id fullParams fullVk fullScalarCore
  fullScalarArith biteCore babyBearFriArith W fullInit 1 fullHigherLaneTamper fullPub
  fullExtView = false

private def fullExtOodHigherLaneTamper : ExtSingleAirOpening Nat :=
  { fullExtAir with quotientChunks :=
      [⟨(fullExtAir.quotientChunks.headD fullExtOne).lanes.headD 0 ::
        ((fullExtAir.quotientChunks.headD fullExtOne).lanes.getD 1 0 + 1) ::
        (fullExtAir.quotientChunks.headD fullExtOne).lanes.drop 2⟩] }

private def fullExtOodTamperView : ExtVerifierView Nat :=
  { fullExtView with singleAirOpenings := [fullExtOodHigherLaneTamper] }

-- Extension OOD arithmetic bites above lane zero: the scalar head is unchanged,
-- but the complete apex verifier rejects the tampered quotient evaluation.
#guard (fullExtOodHigherLaneTamper.quotientChunks.headD fullExtOne).lanes.headD 0 =
  (fullExtAir.quotientChunks.headD fullExtOne).lanes.headD 0
#guard verifyAlgoUnifiedFaithfulExt fullPerm fullRate id fullParams fullVk fullScalarCore
  fullScalarArith biteCore babyBearFriArith W fullInit 1 fullProof fullPub
  fullExtOodTamperView = false

/-! ### Honest higher-arity rows (the former fail-closed residual).

These fixtures enter through `foldConsistentExtAny`, authenticate the complete row,
and run the genuine Lagrange branch at log-arities two and three.  `beta` equals the
first two-adic point, exercising p3's specified exact-point branch; the returned value
still has four live extension lanes.  A higher-lane row mutation with the old Merkle
leaf is rejected. -/

private def wideRowHash (es : List (ExtElem Nat)) : List Nat := (es.map (·.lanes)).flatten

private def wideCore : ExtFriCore Nat :=
  { biteCore with
    rowLeafHash := wideRowHash
    rowPoints := fun _ _ logArity =>
      if logArity = 2 then [1, 2, 3, 4]
      else if logArity = 3 then [1, 2, 3, 4, 5, 6, 7, 8]
      else [] }

private def wideBeta : ExtElem Nat := extOfBase babyBear 4 1
private def wideV0 : ExtElem Nat := ⟨[9, 8, 7, 6]⟩
private def wideRow4 : List (ExtElem Nat) :=
  [wideV0, ⟨[2, 1, 0, 0]⟩, ⟨[3, 0, 1, 0]⟩, ⟨[4, 0, 0, 1]⟩]
private def wideRow8 : List (ExtElem Nat) :=
  wideRow4 ++ [⟨[5, 1, 1, 0]⟩, ⟨[6, 1, 0, 1]⟩,
    ⟨[7, 0, 1, 1]⟩, ⟨[8, 1, 1, 1]⟩]

private def wideLayer (row : List (ExtElem Nat)) : ExtLayerOpening Nat :=
  { beta := ⟨[]⟩, x := ⟨[]⟩,
    e0 := row.headD (extOfBase babyBear 4 0),
    e1 := row.getD 1 (extOfBase babyBear 4 0), evals := row,
    leaf := wideRowHash row, siblings := [] }

private def wideProof (a : Nat) (row : List (ExtElem Nat)) : BatchProofData Nat :=
  { traceCommit := [], friCommitments := [wideRowHash row], finalPoly := wideV0.lanes,
    queries := [], exposedSegment := [], friLogArities := [a] }

private def wideQuery (row : List (ExtElem Nat)) : ExtQueryOpening Nat :=
  { index := 0, initialEval := wideV0, layers := [wideLayer row] }

#guard foldConsistentExtAny wideCore babyBearFriArith W 4 2 id
  (wideProof 2 wideRow4) [wideQuery wideRow4] [wideBeta.lanes] [0] = true
#guard foldConsistentExtAny wideCore babyBearFriArith W 4 3 id
  (wideProof 3 wideRow8) [wideQuery wideRow8] [wideBeta.lanes] [0] = true

private def wideRow8HigherLaneTamper : List (ExtElem Nat) :=
  wideRow8.set 7 ⟨[8, 1, 1, 2]⟩

private def wideTamperedQuery : ExtQueryOpening Nat :=
  { index := 0, initialEval := wideV0,
    -- Keep the authenticated leaf fixed while changing a non-carried row lane.
    layers := [{ wideLayer wideRow8 with evals := wideRow8HigherLaneTamper }] }

#guard foldConsistentExtAny wideCore babyBearFriArith W 4 3 id
  (wideProof 3 wideRow8) [wideTamperedQuery] [wideBeta.lanes] [0] = false

theorem higherArity4_honest_accepts :
    foldConsistentExtAny wideCore babyBearFriArith W 4 2 id
      (wideProof 2 wideRow4) [wideQuery wideRow4] [wideBeta.lanes] [0] = true := by decide

theorem higherArity8_honest_accepts :
    foldConsistentExtAny wideCore babyBearFriArith W 4 3 id
      (wideProof 3 wideRow8) [wideQuery wideRow8] [wideBeta.lanes] [0] = true := by decide

#assert_axioms higherArity4_honest_accepts
#assert_axioms higherArity8_honest_accepts

/-! The fixtures above exercise p3's exact-point early return.  The following
rational calibration exercises the full division-bearing Lagrange branch at a
quartic beta that is NOT any row point.  The row is evaluations of the genuine
extension polynomial `f(X)=X+c`, so the expected fold is `beta+c`; every denominator
inverse is checked by multiplication before acceptance. -/

private def ratField : FieldArith ℚ :=
  { add := (· + ·), mul := (· * ·), pow := (· ^ ·), zero := 0, one := 1 }

private def ratExtArith : ExtFriArith ℚ :=
  { base := ratField, neg := (- ·), half := 1 / 2,
    inv := fun x => ⟨[(x.lanes.headD 0)⁻¹, 0, 0, 0]⟩ }

private def ratToNat (x : ℚ) : Nat := if x = 2 then 2 else if x = 3 then 3 else 0
private def ratBeta : ExtElem ℚ := ⟨[9, 1, 0, 0]⟩
private def ratC : ExtElem ℚ := ⟨[0, 1, 2, 3]⟩
private def ratEval (x : ℚ) : ExtElem ℚ := extAdd ratField (extOfBase ratField 4 x) ratC
private def ratRow4 : List (ExtElem ℚ) := [1, 2, 3, 4].map ratEval
private def ratRow8 : List (ExtElem ℚ) := [1, 2, 3, 4, 5, 6, 7, 8].map ratEval
private def ratFinal : ExtElem ℚ := extAdd ratField ratBeta ratC
private def ratRowHash (es : List (ExtElem ℚ)) : List ℚ := (es.map (·.lanes)).flatten

private def ratWideCore : ExtFriCore ℚ :=
  { compress := fun a b => a ++ b
    leafHash := fun e0 e1 => e0.lanes ++ e1.lanes
    domainPoint := fun _ _ => extOfBase ratField 4 1
    domainPointInv := fun _ _ => extOfBase ratField 4 1
    rowLeafHash := ratRowHash
    rowPoints := fun _ _ logArity =>
      if logArity = 2 then [1, 2, 3, 4]
      else if logArity = 3 then [1, 2, 3, 4, 5, 6, 7, 8]
      else [] }

private def ratLayer (row : List (ExtElem ℚ)) : ExtLayerOpening ℚ :=
  { beta := ⟨[]⟩, x := ⟨[]⟩,
    e0 := row.headD (extOfBase ratField 4 0),
    e1 := row.getD 1 (extOfBase ratField 4 0), evals := row,
    leaf := ratRowHash row, siblings := [] }

private def ratProof (a : ℚ) (row : List (ExtElem ℚ)) : BatchProofData ℚ :=
  { traceCommit := [], friCommitments := [ratRowHash row], finalPoly := ratFinal.lanes,
    queries := [], exposedSegment := [], friLogArities := [a] }

private def ratQuery (row : List (ExtElem ℚ)) : ExtQueryOpening ℚ :=
  { index := 0, initialEval := row.headD (extOfBase ratField 4 0), layers := [ratLayer row] }

#guard exactPointEval ratField 4 ratBeta (ratWideCore.rowPoints 0 0 2) ratRow4 = none
#guard exactPointEval ratField 4 ratBeta (ratWideCore.rowPoints 0 0 3) ratRow8 = none
#guard (lagrangeFoldExt ratExtArith 11 4 (ratWideCore.rowPoints 0 0 2)
  ratRow4 ratBeta) = (true, ratFinal)
#guard (lagrangeFoldExt ratExtArith 11 4 (ratWideCore.rowPoints 0 0 3)
  ratRow8 ratBeta) = (true, ratFinal)
#guard foldConsistentExtAny ratWideCore ratExtArith 11 4 2 ratToNat
  (ratProof 2 ratRow4) [ratQuery ratRow4] [ratBeta.lanes] [0] = true
#guard foldConsistentExtAny ratWideCore ratExtArith 11 4 3 ratToNat
  (ratProof 3 ratRow8) [ratQuery ratRow8] [ratBeta.lanes] [0] = true

-- The real p3 scalar-restriction bridge also computes on an executable width-one point.
#guard extFoldCombine babyBearFriArith W 1 (embScalar 2) (embScalar 1) (embScalar 1)
  (embScalar 5) (embScalar 1)
    = embScalar (scalarFoldCombine babyBearFriArith 2 1 5 1)

#assert_axioms extFoldCombine
#assert_axioms friChainGoExt
#assert_axioms foldConsistentExt
#assert_axioms lagrangeFoldExt
#assert_axioms friChainGoExtAny
#assert_axioms foldConsistentExtAny
#assert_axioms singleAirOkExt
#assert_axioms batchTablesCheckExt
#assert_axioms verifyAlgoUnifiedFaithfulExt

end Dregg2.Circuit.ExtFieldChallenge

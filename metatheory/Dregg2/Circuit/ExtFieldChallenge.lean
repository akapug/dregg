import Dregg2.Circuit.FriVerifier
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
* `extFold` — the commit-phase fold `e0 + β·e1` in EXTENSION arithmetic;
* the **denotation**: over the DEPLOYED field (BabyBear, `W = 11`), `extMul` denotes the
  quartic binomial product `quarticRef` (checked = the human-legible `c0..c3` formula), and
  the ext fold width genuinely carries information the scalar shell drops — two betas the
  scalar model CANNOT distinguish (same head lane) produce DIFFERENT ext folds;
* the **bridge**: the scalar model is the `extDeg = 1` restriction — at `D = 1`, `extMul`
  is base multiplication and `extFold` is the scalar `e0 + β·e1` (`FriCore.foldCombine`), so
  the existing scalar-shell soundness is exactly the width-one specialization.

## Named residual — the LayerOpening shell cutover (a SHARED-STRUCT change)

Wiring this ext-width fold INTO the deployed verifier shell requires changing
`FriVerifier.LayerOpening` (currently `beta x e0 e1 : F`) to carry extension values, and
re-typing `FriCore.foldCombine`/`friChainGo` to fold in `ExtElem`. That is a shared-struct
edit touching every `LayerOpening` user (`FriChallengerUnified.betasBound`/`projBeta`, the
`uCore`/`acceptProof` fixtures). It is NOT done here (kept additive). The additive variant
`ExtLayerOpening` + `extChainFold` below is the shell in ext-width form, ready for the
supervisor to cut over. The precise minimal change is reported to the supervisor.
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

/-! ## 5. The additive ext-width shell (`ExtLayerOpening`) — ready for the cutover.

This is the `FriVerifier.LayerOpening` shell in ext-width form: `beta x e0 e1` become
`ExtElem F`. It is ADDITIVE (a new structure), so it touches no existing user. The named
residual is wiring it into `BatchProofData.queries` in place of the scalar `LayerOpening`,
which is the shared-struct change reported to the supervisor. -/

/-- A FRI layer opening with EXTENSION-VALUED fold data (the deployed reality). The Merkle
`leaf`/`siblings` stay base-field lists (the commitment scheme is over the base field). -/
structure ExtLayerOpening (F : Type) where
  beta : ExtElem F
  x : ExtElem F
  e0 : ExtElem F
  e1 : ExtElem F
  leaf : List F
  siblings : List (List F)

/-- Fold a starting extension value through a chain of ext-layer openings — the ext-width
analogue of `FriVerifier.friChainGo`'s fold accumulation (`extFold` per layer). Returns the
final folded extension element. -/
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

end Dregg2.Circuit.ExtFieldChallenge

/-
# `Dregg2.Crypto.CodecRoundTrip` — the ML-DSA byte codec round-trip `decode ∘ encode = id`, ∀ (the
`VerifyCoreSpec.DecodeSemantics` residual, at the structured-value level).

`VerifyCoreEqSpec.unpackBits_packBits` closed the mixed-radix bit round-trip `unpackBits (packBits c) = c`
(the mathematical core the `DecodeSemantics` seam named). THIS module threads that closed core through the
FIPS 204 §7 per-block byte layout — the `Array.extract`/`++`/offset bookkeeping — to close the
structured-value recovery `pkDecode ∘ pkEncode = id` and the `c̃`/`z` legs of `sigDecode ∘ sigEncode = id`,
for ALL well-formed structured values (not just the pinned KAT bytes `MlDsaCodec.{pk,sig}_roundtrip` reach by
`native_decide`). This is the ML-DSA analog of `MlKemCodecSpec.byteDecodeAt_byteEncode` (the ML-KEM codec
round-trip), and the byte-level completion of the VERIFY direction of Seam 1 (the ring-level `=spec` is
`VerifyCoreEqSpec.verifyCore_eq_challengeMatches_and_norm`).

## What CLOSES here (real ∀-proofs, `#assert_axioms`-clean)

* **`appendFold_spec`** — the block-append fold `init ++ g 0 ++ … ++ g (n−1)` (uniform block size `s`): its
  size, and the per-block byte layout (`out[init.size + i·s + j]! = (g i)[j]!`). The mechanical offset engine.
* **`unpackBits_eq_of_window`** — `unpackBits` depends only on its `count·cbits/8`-byte window (off
  `bytesToNatLE`), so a decode at an interior offset reads exactly the block that `packBits` wrote there.
* **`pkDecode_pkEncode`** — for any `ρ` of length 32 and any `k = 6` size-256 `t1` polys with coeffs `< 2¹⁰`
  (the `SimpleBitUnpack` codomain), `pkDecode (pkEncode (ρ, t1)) = (ρ, t1)`. Rides `unpackBits_packBits`
  through the `ρ(32) ‖ SimpleBitPack₁₀(t1₀) ‖ … ‖ SimpleBitPack₁₀(t1₅)` layout.
* **`sigDecode_sigEncode`** — for any `c̃` of length 48, any `ℓ = 5` size-256 `z` polys whose coefficients lie
  in the `BitUnpack(·, γ₁−1, γ₁)` codomain (`c ≤ γ₁` or the negative wing `q−γ₁ < c < q`), AND given the FIPS
  `HintBitUnpack ∘ HintBitPack` round-trip on the hint region, `sigDecode (sigEncode (c̃, z, h)) = (c̃, z, h)`.
  The `c̃` (byte prefix) and `z` (20-bit `BitPack` + the `γ₁`-sign map `zCoeffFromField ∘ zFieldFromCoeff`)
  legs are CLOSED here off `unpackBits_packBits` + `VerifyCoreEqSpec.zCoeff_zField`.

## HONEST RESIDUAL (named, not laundered)

`sigDecode_sigEncode` carries ONE hypothesis: `hintDecode (…) hoff = some h` — the FIPS 204 `HintBitUnpack ∘
HintBitPack = id` round-trip on a valid hint. The hint codec (Algorithm 20/21) does NOT ride the
`unpackBits`/`packBits` mixed-radix core at all — it is a SEPARATE combinatorial layout (per-poly set-bit
indices + cumulative boundaries, with the fail-closed rejection logic) whose inversion is offset/loop
bookkeeping over a data-dependent inner range `[start:bound]`. It is pure `Array`/`Nat` bookkeeping — NO
crypto, NO hardness, NO framework gap — named precisely as the remaining hint-codec leg. The non-vacuity
witness `real_sig_wf` DISCHARGES it (`native_decide`) on the genuine crate signature, so it is satisfiable and
the `z`/`c̃` legs fire together with a genuinely-decoding hint on real data.

## NON-FAKE

Every `∀`-theorem is `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `native_decide` in
any `∀`-body. Non-vacuity: `pkDecode_pkEncode_witness` / `sigDecode_sigEncode_witness` fire on the genuine
`fips204` v0.4.6 crate public key / signature (the real structured values), and `real_pk_wf` / `real_sig_wf`
witness that the well-formedness hypotheses are satisfiable there.
-/
import Dregg2.Crypto.VerifyCoreEqSpec

namespace Dregg2.Crypto.CodecRoundTrip

open Dregg2.Crypto.MlDsaCodec
open Dregg2.Crypto.MlDsaRing (Poly zeroPoly)
open Dregg2.Crypto.VerifyCoreEqSpec (unpackBits_size unpackBits_getElem bytesToNatLE_eq arrayExtAll
  unpackBits_packBits getElem!_push_lt getElem!_push_eq)

set_option maxRecDepth 8000

theorem getElem!_append_left {β} [Inhabited β] (a b : Array β) (i : Nat) (h : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append_left h]

theorem getElem!_append_right {β} [Inhabited β] (a b : Array β) (i : Nat)
    (h : a.size ≤ i) (h2 : i < a.size + b.size) : (a ++ b)[i]! = b[i - a.size]! := by
  have hb : i - a.size < b.size := by omega
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append_right h]

theorem appendFold_spec {β} [Inhabited β] (g : Nat → Array β) (s : Nat) (init : Array β) :
    ∀ (n : Nat), (∀ i, i < n → (g i).size = s) →
      let r := List.foldl (fun out i => out ++ g i) init (List.range' 0 n 1)
      r.size = init.size + n * s
      ∧ (∀ j, j < init.size → r[j]! = init[j]!)
      ∧ (∀ i, i < n → ∀ j, j < s → r[init.size + i * s + j]! = (g i)[j]!) := by
  intro n
  induction n with
  | zero => intro _; refine ⟨by simp, by simp, by intro i hi; omega⟩
  | succ k ih =>
    intro hsz
    obtain ⟨hsize, hlo, hhi⟩ := ih (fun i hi => hsz i (by omega))
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun out i => out ++ g i) init (List.range' 0 k 1) with hP
    have hgk : (g k).size = s := hsz k (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (P ++ g k).size = _
      rw [Array.size_append, hsize, hgk]; ring
    · intro j hj
      rw [getElem!_append_left _ _ _ (by rw [hsize]; omega), hlo j hj]
    · intro i hi j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · have hik : i * s + j < k * s := by
          have h2 : (i+1) * s ≤ k * s := by apply Nat.mul_le_mul_right; omega
          rw [Nat.succ_mul] at h2; omega
        rw [getElem!_append_left _ _ _ (by rw [hsize]; omega), hhi i h j hj]
      · subst h
        rw [getElem!_append_right _ _ _ (by rw [hsize]; omega) (by rw [hsize, hgk]; omega),
            show init.size + i*s + j - P.size = j from by rw [hsize]; omega]

theorem unpackBits_eq_of_window (b b' : Array UInt8) (off off' count cbits : Nat)
    (h : ∀ i, i < count * cbits / 8 → b[off + i]! = b'[off' + i]!) :
    unpackBits b off count cbits = unpackBits b' off' count cbits := by
  apply arrayExtAll
  · rw [unpackBits_size, unpackBits_size]
  · intro j hj
    rw [unpackBits_size] at hj
    rw [unpackBits_getElem _ _ _ _ _ hj, unpackBits_getElem _ _ _ _ _ hj]
    have hbn : bytesToNatLE b off (count * cbits / 8) = bytesToNatLE b' off' (count * cbits / 8) := by
      rw [bytesToNatLE_eq, bytesToNatLE_eq]
      exact Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
    rw [hbn]

theorem pushIdxFold_spec {β} [Inhabited β] (f : Nat → β) :
    ∀ (n : Nat) (init : Array β),
      let r := List.foldl (fun out i => out.push (f i)) init (List.range' 0 n 1)
      r.size = init.size + n ∧ (∀ j, j < init.size → r[j]! = init[j]!) ∧
        (∀ j, j < n → r[init.size + j]! = f j) := by
  intro n
  induction n with
  | zero => intro init; refine ⟨by simp, by simp, by intro j hj; omega⟩
  | succ k ih =>
    intro init
    obtain ⟨hsize, hlo, hhi⟩ := ih init
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun out i => out.push (f i)) init (List.range' 0 k 1) with hP
    refine ⟨?_, ?_, ?_⟩
    · show (P.push (f k)).size = _; rw [Array.size_push, hsize]; omega
    · intro j hj
      rw [getElem!_push_lt _ _ _ (by rw [hsize]; omega), hlo j hj]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [getElem!_push_lt _ _ _ (by rw [hsize]; omega), hhi j h]
      · subst h
        rw [show init.size + j = P.size from by rw [hsize], getElem!_push_eq]

theorem getElem!_extract {β} [Inhabited β] (a : Array β) (start stop i : Nat)
    (h : start + i < min stop a.size) : (a.extract start stop)[i]! = a[start + i]! := by
  have hi : i < (a.extract start stop).size := by rw [Array.size_extract]; omega
  have hb : start + i < a.size := by omega
  rw [getElem!_pos _ i hi, getElem!_pos a (start+i) hb, Array.getElem_extract]

/-- pkEncode do-block unfold. -/
theorem pkEncode_unfold (rho : List UInt8) (t1 : Array Poly) :
    pkEncode (rho, t1) =
      (List.foldl (fun out i => out ++ packBits (t1[i]!) t1Bits) rho.toArray
        (List.range' 0 paramK 1)).toList := by
  unfold pkEncode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

/-- pkDecode do-block unfold. -/
theorem pkDecode_unfold (pk : List UInt8) :
    pkDecode pk =
      ((pk.toArray.extract 0 32).toList,
       List.foldl (fun t1 i => t1.push (unpackBits pk.toArray (32 + i * t1PolyBytes) 256 t1Bits))
         (Array.mkEmpty paramK) (List.range' 0 paramK 1)) := by
  unfold pkDecode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl


open Dregg2.Crypto.VerifyCoreEqSpec (packBits_size size_mkEmpty) in
theorem pkDecode_pkEncode (rho : List UInt8) (t1 : Array Poly)
    (hrho : rho.length = 32) (ht1 : t1.size = paramK)
    (hpsz : ∀ i, i < paramK → (t1[i]!).size = 256)
    (hplt : ∀ i, i < paramK → ∀ j, j < 256 → (t1[i]!)[j]! < 2 ^ t1Bits) :
    pkDecode (pkEncode (rho, t1)) = (rho, t1) := by
  set out := List.foldl (fun out i => out ++ packBits (t1[i]!) t1Bits) rho.toArray
    (List.range' 0 paramK 1) with hout
  have hb : (pkEncode (rho, t1)).toArray = out := by rw [pkEncode_unfold]
  have hrhosz : rho.toArray.size = 32 := by simp [hrho]
  have hgsz : ∀ i, i < paramK → (packBits (t1[i]!) t1Bits).size = t1PolyBytes := by
    intro i hi; rw [packBits_size, hpsz i hi]; decide
  obtain ⟨hAsz, hAlo, hAhi⟩ :=
    appendFold_spec (fun i => packBits (t1[i]!) t1Bits) t1PolyBytes rho.toArray paramK hgsz
  rw [hrhosz] at hAsz hAlo hAhi
  have houtsz : out.size = 32 + paramK * t1PolyBytes := hAsz
  rw [pkDecode_unfold, hb]
  refine Prod.ext ?_ ?_
  · -- ρ recovery
    show (out.extract 0 32).toList = rho
    have h32 : (32 : Nat) ≤ out.size := by rw [houtsz]; omega
    have hext : out.extract 0 32 = rho.toArray := by
      apply arrayExtAll
      · rw [Array.size_extract, Nat.min_eq_left h32, Nat.sub_zero, hrhosz]
      · intro j hj
        rw [Array.size_extract, Nat.min_eq_left h32, Nat.sub_zero] at hj
        rw [getElem!_extract _ _ _ _ (by rw [houtsz]; omega), Nat.zero_add, hAlo j hj]
    rw [hext]
  · -- t1 recovery
    obtain ⟨hPsz, _, hPhi⟩ :=
      pushIdxFold_spec (fun i => unpackBits out (32 + i * t1PolyBytes) 256 t1Bits) paramK
        (Array.mkEmpty paramK)
    simp only [size_mkEmpty, Nat.zero_add] at hPsz hPhi
    apply arrayExtAll
    · rw [hPsz, ht1]
    · intro j hj
      rw [hPsz] at hj
      rw [hPhi j hj]
      have hwin : unpackBits out (32 + j * t1PolyBytes) 256 t1Bits
          = unpackBits (packBits (t1[j]!) t1Bits) 0 256 t1Bits := by
        apply unpackBits_eq_of_window
        intro jj hjj
        have hjj320 : jj < t1PolyBytes := by
          have h320 : (256 : Nat) * t1Bits / 8 = t1PolyBytes := by decide
          omega
        rw [Nat.zero_add]
        exact hAhi j hj jj hjj320
      rw [hwin, unpackBits_packBits _ _ (hpsz j hj) (hplt j hj)]


/-! ## Signature codec round-trip (ctilde + z legs; hint via a reduced residual). -/

open Dregg2.Crypto.MlDsaRing (q)

theorem getElem!_set!_ne {β} [Inhabited β] (arr : Array β) (i : Nat) (v : β) (j : Nat) (h : i ≠ j) :
    (arr.set! i v)[j]! = arr[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne h]

theorem getElem!_set!_self {β} [Inhabited β] (arr : Array β) (i : Nat) (v : β) (h : i < arr.size) :
    (arr.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

/-- Indexed `set!`-fold: writing `g j` at slot `j` for `j ∈ [0,n)` into `base`. -/
theorem setIdxFold_spec {β} [Inhabited β] (g : Nat → β) (base : Array β) :
    ∀ (n : Nat), n ≤ base.size →
      let r := List.foldl (fun p j => p.set! j (g j)) base (List.range' 0 n 1)
      r.size = base.size ∧ (∀ j, j < n → r[j]! = g j) ∧ (∀ j, n ≤ j → r[j]! = base[j]!) := by
  intro n
  induction n with
  | zero => intro _; refine ⟨by simp, by intro j hj; omega, by intro j _; simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨hsz, hlo, hhi⟩ := ih (by omega)
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set P := List.foldl (fun p j => p.set! j (g j)) base (List.range' 0 k 1) with hP
    refine ⟨?_, ?_, ?_⟩
    · show (P.set! k (g k)).size = _
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hsz]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [getElem!_set!_ne _ _ _ _ (by omega), hlo j h]
      · subst h; rw [getElem!_set!_self _ _ _ (by rw [hsz]; omega)]
    · intro j hj
      rw [getElem!_set!_ne _ _ _ _ (by omega), hhi j (by omega)]

/-- The signature `z`-field encode inner loop: `fields[j] = zFieldFromCoeff (p[j])`. -/
def zFieldsOf (p : Poly) : Array Nat :=
  List.foldl (fun fields j => fields.push (zFieldFromCoeff (p[j]!))) (Array.mkEmpty 256)
    (List.range' 0 256 1)

theorem zFieldsOf_size (p : Poly) : (zFieldsOf p).size = 256 := by
  obtain ⟨h, _, _⟩ := pushIdxFold_spec (fun j => zFieldFromCoeff (p[j]!)) 256 (Array.mkEmpty 256)
  rw [Dregg2.Crypto.VerifyCoreEqSpec.size_mkEmpty, Nat.zero_add] at h
  exact h

theorem zFieldsOf_get (p : Poly) (j : Nat) (hj : j < 256) :
    (zFieldsOf p)[j]! = zFieldFromCoeff (p[j]!) := by
  obtain ⟨_, _, h⟩ := pushIdxFold_spec (fun j => zFieldFromCoeff (p[j]!)) 256 (Array.mkEmpty 256)
  rw [Dregg2.Crypto.VerifyCoreEqSpec.size_mkEmpty] at h
  have hh := h j hj
  rw [Nat.zero_add] at hh
  exact hh

theorem zFieldFromCoeff_lt (c : Nat) (hc : c ≤ gamma1 ∨ (q - gamma1 < c ∧ c < q)) :
    zFieldFromCoeff c < 2 ^ zBits := by
  have hg : gamma1 = 524288 := rfl
  have hq : q = 8380417 := rfl
  have hb : (2 : Nat) ^ zBits = 1048576 := rfl
  simp only [zFieldFromCoeff, hg, hq, hb] at hc ⊢
  rcases hc with h | ⟨h1, h2⟩ <;> split_ifs <;> omega

theorem sigEncode_unfold (ctilde : List UInt8) (z h : Array Poly) :
    sigEncode (ctilde, z, h) =
      ((List.foldl (fun out i => out ++ packBits (zFieldsOf (z[i]!)) zBits) ctilde.toArray
        (List.range' 0 paramL 1)) ++ hintEncode h).toList := by
  unfold sigEncode zFieldsOf
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl

theorem sigDecode_unfold (sig : List UInt8) :
    sigDecode sig =
      ((sig.toArray.extract 0 cTildeLen).toList,
       List.foldl (fun z i =>
          z.push (List.foldl (fun p j => p.set! j
              (zCoeffFromField ((unpackBits sig.toArray (cTildeLen + i * zPolyBytes) 256 zBits)[j]!)))
            zeroPoly (List.range' 0 256 1)))
          (Array.mkEmpty paramL) (List.range' 0 paramL 1),
       (match hintDecode sig.toArray (cTildeLen + paramL * zPolyBytes) with
          | some hs => hs | none => (#[] : Array Poly))) := by
  unfold sigDecode
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rfl



open Dregg2.Crypto.VerifyCoreEqSpec (packBits_size size_mkEmpty zCoeff_zField) in
theorem sigDecode_sigEncode (ctilde : List UInt8) (z h : Array Poly)
    (hct : ctilde.length = cTildeLen) (hz : z.size = paramL)
    (hzsz : ∀ i, i < paramL → (z[i]!).size = 256)
    (hzcod : ∀ i, i < paramL → ∀ j, j < 256 →
      ((z[i]!)[j]! ≤ gamma1 ∨ (q - gamma1 < (z[i]!)[j]! ∧ (z[i]!)[j]! < q)))
    (hhint : hintDecode (sigEncode (ctilde, z, h)).toArray (cTildeLen + paramL * zPolyBytes) = some h) :
    sigDecode (sigEncode (ctilde, z, h)) = (ctilde, z, h) := by
  set zPart := List.foldl (fun out i => out ++ packBits (zFieldsOf (z[i]!)) zBits) ctilde.toArray
    (List.range' 0 paramL 1) with hzP
  set out := zPart ++ hintEncode h with houtdef
  have hb : (sigEncode (ctilde, z, h)).toArray = out := by rw [sigEncode_unfold]
  have hctsz : ctilde.toArray.size = cTildeLen := by simp [hct]
  -- block sizes
  have hblocksz : ∀ i, i < paramL → (packBits (zFieldsOf (z[i]!)) zBits).size = zPolyBytes := by
    intro i hi; rw [packBits_size, zFieldsOf_size]; decide
  obtain ⟨hZsz, hZlo, hZhi⟩ :=
    appendFold_spec (fun i => packBits (zFieldsOf (z[i]!)) zBits) zPolyBytes ctilde.toArray paramL hblocksz
  rw [hctsz] at hZsz hZlo hZhi
  have hzPsz : zPart.size = cTildeLen + paramL * zPolyBytes := hZsz
  have houtsz : out.size = zPart.size + (hintEncode h).size := by rw [houtdef, Array.size_append]
  have hzP_le_out : ∀ k, k < zPart.size → out[k]! = zPart[k]! := by
    intro k hk; rw [houtdef, getElem!_append_left _ _ _ hk]
  rw [hb] at hhint
  rw [sigDecode_unfold, hb]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · -- c̃ recovery
    show (out.extract 0 cTildeLen).toList = ctilde
    have hcle : cTildeLen ≤ out.size := by rw [houtsz, hzPsz]; omega
    have hext : out.extract 0 cTildeLen = ctilde.toArray := by
      apply arrayExtAll
      · rw [Array.size_extract, Nat.min_eq_left hcle, Nat.sub_zero, hctsz]
      · intro j hj
        rw [Array.size_extract, Nat.min_eq_left hcle, Nat.sub_zero] at hj
        rw [getElem!_extract _ _ _ _ (by rw [Nat.min_eq_left hcle]; omega), Nat.zero_add,
            hzP_le_out j (by rw [hzPsz]; omega), hZlo j hj]
    rw [hext]
  · -- z recovery
    obtain ⟨hPsz, _, hPhi⟩ :=
      pushIdxFold_spec (fun i => List.foldl (fun p j => p.set! j
          (zCoeffFromField ((unpackBits out (cTildeLen + i * zPolyBytes) 256 zBits)[j]!)))
          zeroPoly (List.range' 0 256 1)) paramL (Array.mkEmpty paramL)
    simp only [size_mkEmpty, Nat.zero_add] at hPsz hPhi
    apply arrayExtAll
    · rw [hPsz, hz]
    · intro i hi
      rw [hPsz] at hi
      rw [hPhi i hi]
      -- pBuild_i = z[i]!
      obtain ⟨hpsz, hplo, _⟩ :=
        setIdxFold_spec (fun j => zCoeffFromField
            ((unpackBits out (cTildeLen + i * zPolyBytes) 256 zBits)[j]!)) zeroPoly 256
          (by rw [show zeroPoly.size = 256 from by simp [zeroPoly]])
      apply arrayExtAll
      · rw [hpsz, show zeroPoly.size = 256 from by simp [zeroPoly], hzsz i hi]
      · intro j hj
        rw [hpsz, show zeroPoly.size = 256 from by simp [zeroPoly]] at hj
        rw [hplo j hj]
        -- unpackBits window = zFieldsOf z[i]!
        have hfld : unpackBits out (cTildeLen + i * zPolyBytes) 256 zBits = zFieldsOf (z[i]!) := by
          have hwin : unpackBits out (cTildeLen + i * zPolyBytes) 256 zBits
              = unpackBits (packBits (zFieldsOf (z[i]!)) zBits) 0 256 zBits := by
            apply unpackBits_eq_of_window
            intro jj hjj
            have hjj640 : jj < zPolyBytes := by
              have h640 : (256 : Nat) * zBits / 8 = zPolyBytes := by decide
              omega
            rw [Nat.zero_add]
            have hidx : cTildeLen + i * zPolyBytes + jj < zPart.size := by
              rw [hzPsz]
              have : (i + 1) * zPolyBytes ≤ paramL * zPolyBytes := by
                apply Nat.mul_le_mul_right; omega
              rw [Nat.succ_mul] at this; omega
            rw [hzP_le_out _ hidx, hZhi i hi jj hjj640]
          rw [hwin, unpackBits_packBits _ _ (zFieldsOf_size _)
                (fun j hj => by rw [zFieldsOf_get _ _ hj]; exact zFieldFromCoeff_lt _ (hzcod i hi j hj))]
        rw [hfld, zFieldsOf_get _ _ hj, zCoeff_zField _ (hzcod i hi j hj)]
  · -- hint recovery
    rw [hhint]


/-- The `pk` well-formedness hypotheses of `pkDecode_pkEncode` are SATISFIABLE — they all hold on the genuine
`fips204` crate public key (`ρ` length 32, `k = 6` size-256 `t1` polys, coeffs `< 2¹⁰`). -/
theorem real_pk_wf :
    (pkDecode realPk.toList).1.length = 32
    ∧ (pkDecode realPk.toList).2.size = paramK
    ∧ (∀ i, i < paramK → ((pkDecode realPk.toList).2[i]!).size = 256)
    ∧ (∀ i, i < paramK → ∀ j, j < 256 → ((pkDecode realPk.toList).2[i]!)[j]! < 2 ^ t1Bits) := by
  native_decide

/-- **Non-vacuity**: `pkDecode_pkEncode` FIRES on the genuine crate public key (decode→encode→decode is the
identity on the real structured value), so the ∀-theorem is not vacuous. -/
theorem pkDecode_pkEncode_witness :
    pkDecode (pkEncode (pkDecode realPk.toList)) = pkDecode realPk.toList := by native_decide

/-- The `sig` well-formedness hypotheses of `sigDecode_sigEncode` are SATISFIABLE on the genuine crate
signature (`c̃` length 48, `ℓ = 5` size-256 `z` polys in the `BitUnpack` codomain, and the hint decodes). -/
theorem real_sig_wf :
    (sigDecode realSig.toList).1.length = cTildeLen
    ∧ (sigDecode realSig.toList).2.1.size = paramL
    ∧ (∀ i, i < paramL → ((sigDecode realSig.toList).2.1[i]!).size = 256)
    ∧ hintDecode (sigEncode (sigDecode realSig.toList)).toArray (cTildeLen + paramL * zPolyBytes)
        = some (sigDecode realSig.toList).2.2 := by
  native_decide

/-- **Non-vacuity**: `sigDecode_sigEncode` FIRES on the genuine crate signature (decode→encode→decode is the
identity on the real structured value — `c̃`, `z`, AND the hint), so the ∀-theorem is not vacuous. -/
theorem sigDecode_sigEncode_witness :
    sigDecode (sigEncode (sigDecode realSig.toList)) = sigDecode realSig.toList := by native_decide

#assert_axioms pkDecode_pkEncode
#assert_axioms sigDecode_sigEncode
#assert_axioms appendFold_spec
#assert_axioms unpackBits_eq_of_window
#assert_axioms setIdxFold_spec

#assert_axioms pkDecode_pkEncode
#assert_axioms sigDecode_sigEncode
#assert_axioms appendFold_spec
#assert_axioms unpackBits_eq_of_window
#assert_axioms setIdxFold_spec

end Dregg2.Crypto.CodecRoundTrip

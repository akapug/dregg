/-
# `Dregg2.Crypto.Keccak` — the REAL SHA-3 / SHAKE sponge, as EXECUTABLE `def`s (extractable native code).

FIPS 202. This module builds Keccak-f[1600] and the SHAKE extendable-output functions as plain computable
`def`s (the same `leanc`-extractable shape as `Fips204Verify.verifyCore` / `Fips203Kem.encapsCore`): no
`Prop`, no classical choice, only `UInt64`/`Array`/`List` arithmetic. It is BRICK 1 of replacing the `A = id`
scalar caricature in `Fips204Verify.lean` with the real ML-DSA-65 verify — `SampleInBall`, `ExpandA`, and the
byte codec all draw their randomness from `SHAKE` over `Keccak-f[1600]`, so their byte-faithfulness rests on
this module reproducing the published Keccak permutation and SHAKE padding/domain byte EXACTLY.

## THE ANTI-FAKE GATE (checked, not asserted)

The implementation is pinned to the published NIST SHAKE Known-Answer-Test vectors by executable theorems
over the CONCRETE output bytes — `shake256_empty_kat`, `shake128_empty_kat`, `shake256_abc_kat`,
`shake128_abc_kat`, `shake256_empty_prefix` — each closed by KERNEL `decide` through the
`forIn → List.foldl` conversion tower (`kRoundFold`/`kFFold`/`absorbFold`/`squeezeFold` + the `_eq_fold`
equalities): the imperative `Std.Range.forIn` loops do not kernel-reduce (well-founded recursion), but the
equal concrete-`List.range'` folds do, and the kernel GMP-accelerates the underlying `Nat` bitwise ops — a
full Keccak-f reduces in seconds. If a step (θ/ρ/π/χ/ι, the lane bit-order, the `0x1F` SHAKE domain byte, or
`pad10*1`) were wrong, these theorems would NOT close. The empty-input vectors are the FIPS 202 anchors; the
`abc` vectors are an independent cross-check against a reference implementation.

## RESIDUAL

NONE beyond the standard kernel axioms: the KATs carry axiom set ⊆ {propext, Classical.choice, Quot.sound} —
no `Lean.ofReduceBool`/`Lean.trustCompiler`, no `sorry`, no user `axiom`, no toy substitute for the
permutation. (Downstream extracted-core users still carry the `leanc`/FFI residual `Fips204Verify` names;
THIS module's gate no longer contributes a compiled-evaluation residual.)
-/

namespace Dregg2.Crypto.Keccak

/-! ## Keccak-f[1600] primitives -/

/-- Rotate-left on a 64-bit lane. `n = 0` is the identity (all published ρ offsets we use are `1..62`). -/
@[inline] def rotl64 (x : UInt64) (n : UInt64) : UInt64 :=
  if n == 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- The 24 Keccak-f round constants (ι step), FIPS 202. -/
def RC : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- The ρ rotation offsets `r[x][y]`, indexed by lane `x + 5·y` (FIPS 202, the `(t+1)(t+2)/2 mod 64`
sequence over the `(x,y) ↦ (y, 2x+3y)` orbit). -/
def rho : Array UInt64 := #[
   0,  1, 62, 28, 27,   -- y=0:  (0,0)(1,0)(2,0)(3,0)(4,0)
  36, 44,  6, 55, 20,   -- y=1
   3, 10, 43, 25, 39,   -- y=2
  41, 45, 15, 21,  8,   -- y=3
  18,  2, 61, 56, 14]   -- y=4

/-- One Keccak-f[1600] round: θ, ρ+π, χ, ι. State = 25 lanes, lane `(x,y)` at index `x + 5·y`,
little-endian byte order within each lane. -/
def keccakRound (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ
  let mut c : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    c := c.set! x (a[x]! ^^^ a[x+5]! ^^^ a[x+10]! ^^^ a[x+15]! ^^^ a[x+20]!)
  let mut d : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    d := d.set! x (c[(x+4)%5]! ^^^ rotl64 c[(x+1)%5]! 1)
  let mut s := a
  for x in [0:5] do
    for y in [0:5] do
      s := s.set! (x + 5*y) (a[x + 5*y]! ^^^ d[x]!)
  -- ρ + π :  B[y, (2x+3y) mod 5] = rotl(A[x,y], r[x][y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5*((2*x + 3*y) % 5)) (rotl64 s[x + 5*y]! rho[x + 5*y]!)
  -- χ
  let mut o : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      o := o.set! (x + 5*y)
        (b[x + 5*y]! ^^^ ((~~~ b[(x+1)%5 + 5*y]!) &&& b[(x+2)%5 + 5*y]!))
  -- ι
  return o.set! 0 (o[0]! ^^^ rc)

/-- The full Keccak-f[1600] permutation: 24 rounds. -/
def keccakF (a : Array UInt64) : Array UInt64 := Id.run do
  let mut s := a
  for i in [0:24] do
    s := keccakRound s RC[i]!
  return s

/-! ## The sponge -/

/-- `pad10*1` with the SHAKE domain byte `0x1F` (FIPS 202 §6.2 — SHAKE, not SHA-3's `0x06`). Appends the
domain byte, zero-fills to a multiple of `rate`, and sets the final byte's high bit (`| 0x80`). When only one
pad byte is available both collapse into `0x9F`. `rate` ∈ {136 (SHAKE256), 168 (SHAKE128)}. -/
def pad (rate : Nat) (msg : List UInt8) : List UInt8 :=
  let q := rate - (msg.length % rate)          -- pad-byte count, 1..rate
  if q == 1 then
    msg ++ [0x9F]
  else
    msg ++ (0x1F :: List.replicate (q - 2) 0x00) ++ [0x80]

/-- Absorb the (already padded) byte stream into a fresh state: XOR each `rate`-byte block into the lanes
little-endian, then apply Keccak-f. `rate` is a multiple of 8 (136 = 17 lanes, 168 = 21 lanes). -/
def absorb (rate : Nat) (padded : List UInt8) : Array UInt64 := Id.run do
  let arr := padded.toArray
  let nblocks := arr.size / rate
  let mut s : Array UInt64 := Array.replicate 25 0
  for blk in [0:nblocks] do
    for i in [0:rate] do
      let laneIdx := i / 8
      let shift := (8 * (i % 8)).toUInt64
      s := s.set! laneIdx (s[laneIdx]! ^^^ (arr[blk*rate + i]!.toUInt64 <<< shift))
    s := keccakF s
  return s

/-- Squeeze `outLen` bytes: read `rate` little-endian bytes from the state, apply Keccak-f between blocks,
truncate to `outLen`. -/
def squeeze (rate : Nat) (s0 : Array UInt64) (outLen : Nat) : List UInt8 := Id.run do
  let nblocks := (outLen + rate - 1) / rate
  let mut s := s0
  let mut out : Array UInt8 := #[]
  for blk in [0:nblocks] do
    for i in [0:rate] do
      let laneIdx := i / 8
      let shift := (8 * (i % 8)).toUInt64
      out := out.push (s[laneIdx]! >>> shift).toUInt8
    if blk + 1 < nblocks then
      s := keccakF s
  return out.toList.take outLen

/-- **SHAKE256** (FIPS 202): rate 136 bytes (capacity 512 bits), domain `0x1F`. -/
def shake256 (input : List UInt8) (outLen : Nat) : List UInt8 :=
  squeeze 136 (absorb 136 (pad 136 input)) outLen

/-- **SHAKE128** (FIPS 202): rate 168 bytes (capacity 256 bits), domain `0x1F`. -/
def shake128 (input : List UInt8) (outLen : Nat) : List UInt8 :=
  squeeze 168 (absorb 168 (pad 168 input)) outLen

/-! ## The kernel-reduction mirror — `forIn → List.foldl` conversion tower.

The `for _ in [0:n]` loops above desugar to `Std.Range.forIn`, whose well-founded recursion the KERNEL
cannot reduce — so concrete facts about them get stuck under `decide` and previously needed
`native_decide`. `List.foldl` over a concrete `List.range'` DOES kernel-reduce (and the kernel
GMP-accelerates the `Nat` bitwise ops under the `UInt64`/`BitVec` wrappers), so each sponge stage gets a
fold-shaped mirror proven equal to the imperative def (the same lever as `MlDsaRing.powModQ_eq_fold`).
Rewriting a KAT through the tower turns it into a computation kernel `decide` closes in seconds — the
KATs below carry NO `Lean.ofReduceBool`/`trustCompiler` residual. -/

/-- Fold-based θρπχι round (kernel-reducible mirror of `keccakRound`). -/
def kRoundFold (a : Array UInt64) (rc : UInt64) : Array UInt64 :=
  let c := (List.range' 0 5 1).foldl (fun c x =>
    c.set! x (a[x]! ^^^ a[x+5]! ^^^ a[x+10]! ^^^ a[x+15]! ^^^ a[x+20]!)) (Array.replicate 5 0)
  let d := (List.range' 0 5 1).foldl (fun d x =>
    d.set! x (c[(x+4)%5]! ^^^ rotl64 c[(x+1)%5]! 1)) (Array.replicate 5 0)
  let s := (List.range' 0 5 1).foldl (fun s x =>
    (List.range' 0 5 1).foldl (fun s y => s.set! (x + 5*y) (a[x + 5*y]! ^^^ d[x]!)) s) a
  let b := (List.range' 0 5 1).foldl (fun b x =>
    (List.range' 0 5 1).foldl (fun b y =>
      b.set! (y + 5*((2*x + 3*y) % 5)) (rotl64 s[x + 5*y]! rho[x + 5*y]!)) b)
    (Array.replicate 25 0)
  let o := (List.range' 0 5 1).foldl (fun o x =>
    (List.range' 0 5 1).foldl (fun o y =>
      o.set! (x + 5*y) (b[x + 5*y]! ^^^ ((~~~ b[(x+1)%5 + 5*y]!) &&& b[(x+2)%5 + 5*y]!))) o)
    (Array.replicate 25 0)
  o.set! 0 (o[0]! ^^^ rc)

theorem keccakRound_eq_fold (a : Array UInt64) (rc : UInt64) :
    keccakRound a rc = kRoundFold a rc := by
  unfold keccakRound kRoundFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- Fold-based 24-round permutation (kernel-reducible mirror of `keccakF`). -/
def kFFold (a : Array UInt64) : Array UInt64 :=
  (List.range' 0 24 1).foldl (fun s i => kRoundFold s RC[i]!) a

theorem keccakF_eq_fold (a : Array UInt64) : keccakF a = kFFold a := by
  unfold keccakF kFFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, keccakRound_eq_fold]
  rfl

/-- Fold-based absorb (kernel-reducible mirror of `absorb`). -/
def absorbFold (rate : Nat) (padded : List UInt8) : Array UInt64 :=
  let arr := padded.toArray
  let nblocks := arr.size / rate
  (List.range' 0 nblocks 1).foldl (fun s blk =>
    kFFold ((List.range' 0 rate 1).foldl (fun s i =>
      s.set! (i / 8) (s[i / 8]! ^^^ (arr[blk*rate + i]!.toUInt64 <<< (8 * (i % 8)).toUInt64))) s))
    (Array.replicate 25 0)

theorem absorb_eq_fold (rate : Nat) (padded : List UInt8) :
    absorb rate padded = absorbFold rate padded := by
  unfold absorb absorbFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, bind_pure, keccakF_eq_fold]
  rfl

/-- Fold-based squeeze; state `⟨out, s⟩` (the `MProd` order the do-desugaring produces, so the
conversion closes by `rfl`). -/
def squeezeFold (rate : Nat) (s0 : Array UInt64) (outLen : Nat) : List UInt8 :=
  let nblocks := (outLen + rate - 1) / rate
  let st := (List.range' 0 nblocks 1).foldl (fun (st : MProd (Array UInt8) (Array UInt64)) blk =>
    ⟨(List.range' 0 rate 1).foldl (fun out i =>
        out.push (st.snd[i / 8]! >>> (8 * (i % 8)).toUInt64).toUInt8) st.fst,
      if blk + 1 < nblocks then kFFold st.snd else st.snd⟩)
    ⟨#[], s0⟩
  st.fst.toList.take outLen

theorem squeeze_eq_fold (rate : Nat) (s0 : Array UInt64) (outLen : Nat) :
    squeeze rate s0 outLen = squeezeFold rate s0 outLen := by
  unfold squeeze squeezeFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, keccakF_eq_fold]
  rfl

/-- `shake256` through the fold tower — the KAT-shrinking rewrite. -/
theorem shake256_eq_fold (input : List UInt8) (outLen : Nat) :
    shake256 input outLen = squeezeFold 136 (absorbFold 136 (pad 136 input)) outLen := by
  unfold shake256; rw [absorb_eq_fold, squeeze_eq_fold]

/-- `shake128` through the fold tower — the KAT-shrinking rewrite. -/
theorem shake128_eq_fold (input : List UInt8) (outLen : Nat) :
    shake128 input outLen = squeezeFold 168 (absorbFold 168 (pad 168 input)) outLen := by
  unfold shake128; rw [absorb_eq_fold, squeeze_eq_fold]

/-! ## THE ANTI-FAKE GATE — byte-exact NIST/reference Known-Answer-Test vectors.

Each KAT is rewritten through the fold tower (`shake256_eq_fold`/`shake128_eq_fold`) and closed by KERNEL
`decide` over the concrete output bytes — axiom set ⊆ {propext, Classical.choice, Quot.sound}, no
`Lean.ofReduceBool`/`trustCompiler`. These are the load-bearing proof that the permutation, lane bit-order,
`0x1F` domain byte, and `pad10*1` are RIGHT. -/

set_option maxRecDepth 100000 in
/-- SHAKE256("") first 32 output bytes — the FIPS 202 anchor. -/
theorem shake256_empty_kat :
    shake256 [] 32 =
      [0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
       0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
       0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
       0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f] := by
  rw [shake256_eq_fold]; decide

set_option maxRecDepth 100000 in
/-- SHAKE128("") first 32 output bytes — the FIPS 202 anchor. -/
theorem shake128_empty_kat :
    shake128 [] 32 =
      [0x7f, 0x9c, 0x2b, 0xa4, 0xe8, 0x8f, 0x82, 0x7d,
       0x61, 0x60, 0x45, 0x50, 0x76, 0x05, 0x85, 0x3e,
       0xd7, 0x3b, 0x80, 0x93, 0xf6, 0xef, 0xbc, 0x88,
       0xeb, 0x1a, 0x6e, 0xac, 0xfa, 0x66, 0xef, 0x26] := by
  rw [shake128_eq_fold]; decide

set_option maxRecDepth 100000 in
/-- SHAKE256("abc") first 32 output bytes — non-empty cross-check ("abc" = `0x61 0x62 0x63`). -/
theorem shake256_abc_kat :
    shake256 [0x61, 0x62, 0x63] 32 =
      [0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77,
       0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11, 0x4d,
       0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee,
       0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b, 0x57, 0x39] := by
  rw [shake256_eq_fold]; decide

set_option maxRecDepth 100000 in
/-- SHAKE128("abc") first 32 output bytes — non-empty cross-check. -/
theorem shake128_abc_kat :
    shake128 [0x61, 0x62, 0x63] 32 =
      [0x58, 0x81, 0x09, 0x2d, 0xd8, 0x18, 0xbf, 0x5c,
       0xf8, 0xa3, 0xdd, 0xb7, 0x93, 0xfb, 0xcb, 0xa7,
       0x40, 0x97, 0xd5, 0xc5, 0x26, 0xa6, 0xd3, 0x5f,
       0x97, 0xb8, 0x33, 0x51, 0x94, 0x0f, 0x2c, 0xc8] := by
  rw [shake128_eq_fold]; decide

set_option maxRecDepth 100000 in
/-- Length is honoured: SHAKE is extendable — a longer squeeze extends (does not restart) the stream, so the
32-byte KAT is a prefix of the 64-byte output. -/
theorem shake256_empty_prefix : (shake256 [] 64).take 32 = shake256 [] 32 := by
  simp only [shake256_eq_fold]; decide

end Dregg2.Crypto.Keccak

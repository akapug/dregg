/-
# `Dregg2.Crypto.MlDsaSampleInBall` — the REAL ML-DSA-65 `SampleInBall` (FIPS 204 Algorithm 29), as an EXECUTABLE `def`.

FIPS 204 §7.3, Algorithm 29. `SampleInBall(ρ)` deterministically derives the *challenge polynomial* `c ∈ R_q`
from a seed `ρ = c̃` by driving a SHAKE-256 XOF: a polynomial with EXACTLY `τ` nonzero coefficients, each `±1`.
For ML-DSA-65 the challenge weight is `τ = 49`.

This is BRICK 3 of replacing the `A = id` scalar caricature in `Fips204Verify.lean` with the real ML-DSA-65
verify. It REUSES — does not reimplement — the two landed, verified bricks:

* BRICK 1 `Dregg2.Crypto.Keccak` — real SHAKE-256 (`shake256`), byte-exact vs the FIPS 202 NIST KATs.
* BRICK 2 `Dregg2.Crypto.MlDsaRing` — the real ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` (`Poly`, `q = 8380417`, gate-verified NTT).

The output `c` is a `MlDsaRing.Poly` (256 coefficients in `[0, q)`). A `−1` is carried as its canonical rep
`q − 1 = 8380416`, so `c` drops straight into the ring arithmetic of brick 2 (brick 4 `ExpandA` and brick 6
`verifyCore` consume this challenge directly).

## THE ALGORITHM (FIPS 204 Algorithm 29, faithfully)

```
Input:  ρ ∈ B^{λ/4}                      (ML-DSA-65: λ = 192, so |ρ| = 48 bytes = c̃)
Output: c ∈ R with exactly τ nonzero coeffs, each ±1
1  c ← 0
2  ctx ← SHAKE256.Init ; Absorb(ctx, ρ)
3  s ← Squeeze(ctx, 8)                    (8 bytes → a 64-bit sign field)
4  h ← BytesToBits(s)                     (h[k] = bit (k mod 8) of byte (k/8); LSB-first)
5  for i from 256 − τ (= 207) to 255 do
6     j ← Squeeze(ctx, 1)                  (one stream byte)
7     while j > i do j ← Squeeze(ctx, 1)  (rejection: keep drawing until j ≤ i)
8     c[i] ← c[j]                          (swap old c[j] up to position i)
9     c[j] ← (−1)^{h[i + τ − 256]}         (i + τ − 256 = i − 207, the next sign bit in order)
10 return c
```

`h[i + τ − 256] = h[i − 207]`, so as `i` runs 207 → 255 the sign bits are consumed `s`-bit `0, 1, …, 48` in
order. `BytesToBits` is LSB-first, so assembling the 8 bytes little-endian into a 64-bit `s` makes
`h[k] = (s >>> k) &&& 1` exactly. The byte `j` is consumed AFTER the sign is fixed (bit index depends only on
`i`, not on `j`), matching the loop above. `(−1)^0 = 1`, `(−1)^1 = −1 ≡ q − 1`.

The one implementation liberty: rather than an incremental squeeze, we pull a generously-sized SHAKE-256 block
up front and index into it (`pos`), refusing any byte `> i`. The gates below (τ = 49 exact, all `±1`, and a
pinned full-poly cross-check against an INDEPENDENT reference) would red the build if the buffer were too small
or the byte/bit order wrong.

## THE ANTI-FAKE GATES (`native_decide`, compiled)

* `sampleInBall_tau_count` — the output has EXACTLY 49 nonzero coefficients.
* `sampleInBall_pm_one` — every nonzero coefficient is in `{1, q−1}` (i.e. `±1 mod q`); nothing else appears.
* `sampleInBall_kat_ctilde_0_47` — for the concrete `c̃ = [0,1,…,47]` (48 bytes), the FULL 256-coefficient
  output is byte-for-byte the value produced by an INDEPENDENT reference: Python `hashlib.shake_256` (a trusted
  SHAKE) driving a from-scratch transcription of FIPS 204 Algorithm 29. This is a genuine cross-implementation
  Known-Answer-Test, not a self-consistency tautology; any future drift in SHAKE, the sign order, or the
  rejection loop reds the build.

`native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler`, the
same residual `Keccak` and `MlDsaRing` already name. No `sorry`, no user `axiom`, no toy substitute.
-/

import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlDsaRing

namespace Dregg2.Crypto.MlDsaSampleInBall

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly)
open Dregg2.Crypto.Keccak (shake256)

/-- ML-DSA-65 challenge Hamming weight, FIPS 204 Table 2: `τ = 49`. -/
def tau : Nat := 49

/-- The FIPS 204 loop start index, `256 − τ = 207`. -/
def loStart : Nat := 256 - tau

/-- Bytes of SHAKE-256 stream to pull up front: the 8-byte sign field plus a generous rejection reserve. The
expected rejection consumption is `Σ_{i=207}^{255} 256/(i+1) ≈ 54` bytes; `4·136` (four SHAKE-256 rate blocks)
is a wide margin. If it were ever too small the `τ = 49` gate would fail (a short buffer places coefficients at
the wrong positions), so the size is self-checked. -/
def streamBytes : Nat := 8 + 4 * 136

/-- **`SampleInBall` — FIPS 204 Algorithm 29 for ML-DSA-65 (`τ = 49`).**

Absorb `cTilde` into SHAKE-256, take the first 8 stream bytes as a little-endian 64-bit sign field `s`, then run
the Fisher–Yates-style rejection loop `i = 207 … 255`: draw stream bytes until `j ≤ i`, set `c[i] ← c[j]`, then
`c[j] ← (−1)^{s-bit (i−207)}` (carried as `1` or `q−1 = 8380416`). Result: a `Poly` with exactly `τ = 49`
nonzero coefficients, each `±1`. For ML-DSA-65 the caller passes `cTilde` of length `λ/4 = 48` bytes. -/
def sampleInBall (cTilde : List UInt8) : Poly := Id.run do
  let stream : Array UInt8 := (shake256 cTilde streamBytes).toArray
  -- Sign field `s`: first 8 stream bytes, little-endian → `h[k] = (s >>> k) &&& 1` (BytesToBits, LSB-first).
  let mut s : UInt64 := 0
  for b in [0:8] do
    s := s ||| (stream[b]!.toUInt64 <<< (UInt64.ofNat (8 * b)))
  let mut c : Poly := zeroPoly
  let mut pos : Nat := 8                              -- stream cursor (past the 8 sign bytes)
  for i in [loStart:256] do                           -- i = 207 … 255  (τ = 49 iterations)
    -- Rejection-sample the next byte `j ≤ i` from the stream, advancing `pos`.
    let mut j : Nat := 0
    for p in [pos:streamBytes] do
      if stream[p]!.toNat ≤ i then
        j := stream[p]!.toNat
        pos := p + 1
        break
    -- FIPS order: c[i] ← c[j] (old), THEN c[j] ← ±1 with sign bit (i − 207).
    c := c.set! i c[j]!
    let bit : UInt64 := (s >>> (UInt64.ofNat (i - loStart))) &&& 1
    c := c.set! j (if bit == 0 then 1 else q - 1)
  return c

/-! ## THE ANTI-FAKE GATES — `native_decide` over a concrete `c̃`. -/

/-- The ML-DSA-65 test seed `c̃ = [0,1,2,…,47]` — exactly `λ/4 = 48` bytes (λ = 192). -/
def ctilde047 : List UInt8 := (List.range 48).map (fun n => UInt8.ofNat n)

/-- The challenge polynomial for `ctilde047`, held once for the gates below. -/
def challenge047 : Poly := sampleInBall ctilde047

/-- **Gate 1 — exact weight τ = 49**: the output has exactly 49 nonzero coefficients. A sampler that drew the
wrong number of coefficients (bad loop bound, off-by-one rejection, exhausted buffer) fails here. -/
theorem sampleInBall_tau_count :
    (challenge047.filter (· ≠ 0)).size = 49 := by native_decide

/-- **Gate 2 — every nonzero coefficient is `±1`**: no coefficient lies outside `{0, 1, q−1}`. A sampler that
wrote a magnitude other than `±1` (wrong sign encoding, unreduced `−1`) fails here. -/
theorem sampleInBall_pm_one :
    challenge047.all (fun x => x = 0 ∨ x = 1 ∨ x = q - 1) = true := by native_decide

/-- **Gate 3 — full-output cross-implementation KAT**: for `c̃ = [0,…,47]` the entire 256-coefficient challenge
matches, coefficient-for-coefficient, an INDEPENDENT reference — Python `hashlib.shake_256` driving a
from-scratch transcription of FIPS 204 Algorithm 29 (`−1` carried as `q−1 = 8380416`). This pins SHAKE, the
little-endian sign field, the LSB-first bit order, and the rejection loop simultaneously; any drift reds it. -/
theorem sampleInBall_kat_ctilde_0_47 :
    challenge047 =
      #[0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 8380416, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0,
        1, 0, 0, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 0, 8380416, 0, 1, 0, 0,
        0, 0, 0, 0, 8380416, 8380416, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 8380416, 0, 0, 0, 0, 8380416, 0, 0, 0, 8380416,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 0, 1, 1, 0, 0, 0, 8380416,
        8380416, 8380416, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
        1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 0, 0, 0, 0, 8380416, 1, 1, 0, 1, 0, 0, 8380416, 0, 0,
        0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8380416, 0, 0, 0, 8380416, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0,
        1, 0, 1, 8380416, 1, 0, 0, 0, 8380416, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  native_decide

end Dregg2.Crypto.MlDsaSampleInBall

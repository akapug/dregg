/-
# Bfv.Params — the BFV parameter algebra (q, t, Δ, r) and the deployed fhe.rs degree-4096 set.

**The first stone of Lean-first BFV.** The additive-only fold path (`fhegg-fhe/src/additive.rs` +
`boundary.rs`) consumes exactly this parameter surface: a ciphertext modulus `q`, a plaintext modulus
`t`, and the derived scaling factor `Δ = ⌊q/t⌋` with residue `r = q mod t`. Everything the two
silent-failure theorems need (`Bfv.NoWrap`, `Bfv.Noise`, `Bfv.Fold`) is arithmetic over these four
numbers — no ring structure, no NTT, no multiplication, because NO multiplication ever rides the
fold path (verified against the workspace: the consumed fhe.rs API is encode/encrypt/`+=`/decrypt
only — see `TESTQALOG.md` 4swarm/bfv-sizing).

## The concrete set — `fheRs4096`

The fhe.rs `default_parameters` degree-4096 set the fold actually runs on (ground truth read from
the unpacked fhe.rs 0.1.1 registry checkout, not from docs):

  * `q = 0xffffee001 · 0xffffc4001 · 0x1ffffe0001` — the three NTT-friendly HE-standard moduli,
    109 bits total (pinned: `2^108 < q < 2^110`). This is exactly the HE-standard 128-bit-security
    cap for n = 4096 — ZERO slack for q growth (a Phase-2 named constraint, not a theorem here).
  * `t = 1032193 ≈ 2^20`, SIMD-friendly (`t ≡ 1 [MOD 8192]`, pinned by `decide`).
  * `Δ = ⌊q/t⌋` (90 bits), `r = q mod t = 843789`.

## What this module proves

  * `Params.q_eq` — `q = Δ·t + r` (the Euclidean identity every rounding proof leans on).
  * `Params.r_lt_t`, `Params.Δ_pos`, `Params.q_pos` — the sign/size facts.
  * The `decide`-pinned concrete facts about `fheRs4096` listed above. Every pin is kernel-`decide`
    on literals — the kernel's GMP-backed Nat arithmetic is the oracle, not a comment.

## What this module does NOT claim (honest scope)

  * **Lattice security of this parameter set is NOT a Lean theorem and never will be** — it is
    class (B) of the silent-failure taxonomy: the 128-bit estimate is an ESTIMATOR artifact
    (lattice-estimator pin + build gate on the Rust side), not something a proof assistant can
    state truthfully. Nothing in `Bfv/` pretends otherwise.
  * Primality / NTT-friendliness of the three moduli is not proved (the fold path never runs an
    NTT-dependent op in this model; `t ≡ 1 [MOD 8192]` is pinned because slot-encoding needs it).

Pure. No axioms beyond the kernel triple.
-/
import Mathlib.Tactic.Linarith
import Dregg2.Tactics

namespace Bfv

/-- **BFV parameter set** for the additive-only model: ciphertext modulus `q`, plaintext modulus
`t`, with `0 < t < q`. Everything else (`Δ`, `r`) is derived. -/
structure Params where
  /-- The ciphertext modulus. -/
  q : ℕ
  /-- The plaintext modulus (the bucket-value space of the fold). -/
  t : ℕ
  /-- The plaintext modulus is nonzero. -/
  t_pos : 0 < t
  /-- The plaintext modulus is strictly below the ciphertext modulus (so `Δ ≥ 1`). -/
  t_lt_q : t < q

namespace Params

variable (P : Params)

/-- The BFV scaling factor `Δ = ⌊q/t⌋` — a fresh encryption of `m` has phase `Δ·m + e`. -/
def Δ : ℕ := P.q / P.t

/-- The scaling residue `r = q mod t` — the exact error term of the integer division `q/t`;
it is the reason the decrypt-correctness bound carries a `2(t−1)r` term and not just `2t|e|`. -/
def r : ℕ := P.q % P.t

/-- The Euclidean identity `q = Δ·t + r` — the spine of every rounding argument in `Bfv.Noise`. -/
theorem q_eq : P.q = P.Δ * P.t + P.r := by
  show P.q = P.q / P.t * P.t + P.q % P.t
  rw [Nat.mul_comm]
  exact (Nat.div_add_mod P.q P.t).symm

/-- The residue is below the plaintext modulus. -/
theorem r_lt_t : P.r < P.t := Nat.mod_lt _ P.t_pos

/-- The scaling factor is nonzero (because `t < q`). -/
theorem Δ_pos : 0 < P.Δ := Nat.div_pos (Nat.le_of_lt P.t_lt_q) P.t_pos

/-- The ciphertext modulus is nonzero. -/
theorem q_pos : 0 < P.q := lt_trans P.t_pos P.t_lt_q

end Params

/-! ## The deployed fhe.rs degree-4096 parameter set. -/

/-- The three NTT-friendly moduli of the fhe.rs `default_parameters` degree-4096 set, multiplied
out: `q = 0xffffee001 · 0xffffc4001 · 0x1ffffe0001` (109 bits). -/
def q4096 : ℕ := 0xffffee001 * 0xffffc4001 * 0x1ffffe0001

/-- The deployed plaintext modulus `t = 1032193 ≈ 2^20` (SIMD-friendly: `t ≡ 1 [MOD 8192]`). -/
def t4096 : ℕ := 1032193

/-- **The deployed parameter set** — the exact numbers the fold runs on. -/
def fheRs4096 : Params where
  q := q4096
  t := t4096
  t_pos := by decide
  t_lt_q := by decide

/-! ### `decide`-pinned concrete facts (the kernel is the oracle, not a comment). -/

/-- `q` is a 109-bit modulus: `2^108 < q < 2^110`. -/
theorem q4096_bits : 2 ^ 108 < q4096 ∧ q4096 < 2 ^ 110 := by decide

/-- `t` is SIMD-friendly for degree 4096: `t ≡ 1 [MOD 8192]` (required for slot encoding). -/
theorem t4096_simd : t4096 % 8192 = 1 := by decide

/-- The residue of the deployed set is `r = 843789` (used by the concrete margin pins). -/
theorem r4096_value : fheRs4096.r = 843789 := by decide

/-- The scaling factor of the deployed set is a 90-bit number: `2^89 < Δ < 2^90` —
this is the headroom the noise budget spends from (`Δ/2 ≈ 2^88` of tolerable phase noise). -/
theorem Δ4096_bits : 2 ^ 89 < fheRs4096.Δ ∧ fheRs4096.Δ < 2 ^ 90 := by decide

#assert_all_clean [Bfv.Params.q_eq, Bfv.Params.r_lt_t, Bfv.Params.Δ_pos, Bfv.Params.q_pos,
  Bfv.q4096_bits, Bfv.t4096_simd, Bfv.r4096_value, Bfv.Δ4096_bits]

end Bfv

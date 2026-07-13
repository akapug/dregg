/-
# Crypto linking-chain gauntlet aggregator

Building THIS module builds the entire from-scratch PQ-spec linking chain as one — the CI-reproducible
form of the whole-tree gauntlet (`lake build Dregg2.Crypto.CryptoVerifyAll`). It imports every top-level
linking result so a single target confirms they all compose (they are otherwise outside the default
`Dregg2.lean` aggregator, deliberately: they pull the heavy KAT `native_decide` chain, which would bloat
every default build).

What this transitively verifies:
- Both NTT-correctness proofs from scratch (Mathlib ships neither): `NttFaithful` (ML-DSA complete NTT),
  `MlKemNttFaithful` (ML-KEM incomplete Kyber NTT).
- All four `=spec` directions: `VerifyCoreEqSpec` (verify, full biconditional), `SignCoreSpec` (sign),
  `DecapsCoreSpec` (decaps byte-level), `EncapsCoreSpec` (encaps byte-level).
- Seam 2 floor unification: `FloorBridge`, and the quantitative reductions `ProbCrypto`, `UcSignatureQuant`,
  `HybridThresholdQuant`, `ProtocolSoundnessQuant`.
- Seam 3 model bridge: `ModelBridge`.
- Seam 4 δ analysis: `MlKemDelta`.
- Seam 1 empirical floor (broadened): `AcvpKats` — a representative NIST-ACVP-style edge-case batch
  (15 verify-accept, 15 verify-reject, 10 deterministic-sign, 15 KEM-encaps, 15 KEM-decaps-recover,
  10 KEM-decaps-implicit-reject), each `native_decide`-pinned byte-exact against the `fips204`/`ml-kem`
  reference — the empirical complement to the `=spec` for-all proofs above.

See `docs/LINKING-SEAMS-PROGRESS.md` for the seam-by-seam status and the named residuals.
-/
import Dregg2.Crypto.VerifyCoreEqSpec
import Dregg2.Crypto.VerifyCoreEqSpecW
import Dregg2.Crypto.CodecRoundTrip
import Dregg2.Crypto.MlDsaHintCodec
import Dregg2.Crypto.MlDsaSigCodecClosed
import Dregg2.Crypto.SignCoreSpec
import Dregg2.Crypto.DecapsCoreSpec
import Dregg2.Crypto.EncapsCoreSpec
import Dregg2.Crypto.MlKemCodecSpec
import Dregg2.Crypto.FloorBridge
import Dregg2.Crypto.MlKemDelta
import Dregg2.Crypto.ModelBridge
import Dregg2.Crypto.UcSignatureQuant
import Dregg2.Crypto.HybridThresholdQuant
import Dregg2.Crypto.ProtocolSoundnessQuant
import Dregg2.Crypto.KemSoundnessQuant
import Dregg2.Crypto.AcvpKats
import Dregg2.Tactics

/-! ## Trust-shrink pins — the loop-leg `forIn → List.foldl` conversions.

The SHAKE KATs and both ζ gates close by KERNEL `decide` through the fold towers
(`Keccak.shake256_eq_fold`/`shake128_eq_fold`, `MlDsaRing.powModQ_eq_fold`,
`MlKemRing.powModQ_eq_fold`): pinned here so a `native_decide` regression
(`Lean.ofReduceBool`/`trustCompiler` re-entering these axiom sets) fails THIS aggregator. -/
#assert_all_clean [Dregg2.Crypto.Keccak.shake256_empty_kat,
  Dregg2.Crypto.Keccak.shake128_empty_kat,
  Dregg2.Crypto.Keccak.shake256_abc_kat,
  Dregg2.Crypto.Keccak.shake128_abc_kat,
  Dregg2.Crypto.Keccak.shake256_empty_prefix,
  Dregg2.Crypto.MlDsaRing.zeta_primitive_512th_root,
  Dregg2.Crypto.MlKemRing.zeta_order]

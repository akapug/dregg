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
- The four `=spec` modules: `VerifyCoreEqSpec` (verify — NOTE its headline biconditional is a
  SYNTACTIC BISECTION of `verifyCore`, not a spec identification; see its header), `SignCoreSpec` (sign),
  `DecapsCoreSpec` (decaps byte-level), `EncapsCoreSpec` (encaps byte-level).
- Seam 2 floor unification: `FloorBridge`, and the quantitative reductions `ProbCrypto`, `UcSignatureQuant`,
  `HybridThresholdQuant`, `ProtocolSoundnessQuant`.
- Seam 3 model bridge: `ModelBridge`.
- Seam 4 δ analysis: `MlKemDelta`.
- Seam 1 empirical floor, NIST-anchored: `MlDsaSigVerAcvp` — the COMPLETE NIST ACVP
  `ML-DSA-sigVer-FIPS204` ML-DSA-65 external/pure group (`tgId = 3`, `tcId` 31–45: 3 accept, 12 reject),
  `verifyCore` reproducing NIST's own `testPassed` on every case. The other NIST anchors ride in with
  their cores: `MlKemDecaps.decaps_matches_acvp` (the complete `ML-KEM-encapDecap-FIPS203` ML-KEM-768
  decapsulation group, `tgId = 5`, `tcId` 86–95, including the exact implicit-reject keys),
  `MlKemEncaps.encaps_matches_acvp`, `MlDsaSignReal.sign_matches_acvp_deterministic`. Each cites its
  ACVP-Server file, group, test-case ids and downloaded-file digests.
- Seam 1 empirical floor, CRATE-anchored (broader, NOT NIST): `CrateGeneratedKats` — a representative
  edge-case batch (15 verify-accept, 15 verify-reject, 10 deterministic-sign, 15 KEM-encaps,
  15 KEM-decaps-recover, 10 KEM-decaps-implicit-reject), `#guard`-pinned byte-exact against the
  `fips204` v0.4.6 / `ml-kem` v0.2.3 Rust reference. This is differential agreement with an independent
  implementation over a wide input space — NOT evidence of matching FIPS 203/204. (Renamed from
  `AcvpKats`, whose name implied a NIST provenance the vectors never had.)

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
import Dregg2.Crypto.MlDsaSigVerAcvp
import Dregg2.Crypto.MlKemEncapsAcvp
import Dregg2.Crypto.MlDsaSigGenAcvp
import Dregg2.Crypto.CrateGeneratedKats
import Dregg2.Crypto.KeccakCavp

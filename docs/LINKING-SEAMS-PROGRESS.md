# Linking-seams goal — progress record

Goal: link the parallel PQ-crypto proofs into ONE integrated formal foundation. Close every
executable↔spec and quantitative↔Boolean seam; prove the bridge, never relabel. Work is on branch
`mldsa-sign-route` (a +N clean superset of `main`; `git merge --ff-only mldsa-sign-route` captures it).
The Crypto real-verify/NTT chain is OUTSIDE the default `lake build` — build modules explicitly
(`lake build Dregg2.Crypto.<M>`), or direct-`lean`/hbox when the shared lock stalls.

## Seam 1 — executable ↔ spec
**VERIFY: DONE.** `VerifyCoreEqSpec.verifyCore_eq_spec` — `verifyCore = the FIPS 204 Alg-8 verify
predicate, for-all`, axiom-clean (no `native_decide` in the ∀). Built on:
- `NttFaithful.lean` — **the entire Cooley-Tukey NTT proven correct from scratch** (Mathlib lacks it):
  `nttEvalsAtRoots_canonical` (ntt = eval-at-negacyclic-roots), `nttMulHom_proven` (ntt is a ring hom),
  `nttLeftInverse_proven`/`ringRepFaithful_proven` (intt inverts; NTT computes the R_q product) — via
  `omega_orthogonality`, the butterfly primitive `bfFold_spec`/`cast_bfSweep`, the stage inductions
  `stage_inv`/`inttStage_inv`. Guards: size=256 + reduced-range (the props are FALSE unguarded — 3 bugs caught).
- `VerifyCoreEqSpec.lean` — `toRq` coeff↔R_q bridge (`toRq_schoolbookMul`, `toRq_nttMul`,
  `toRq_intt_matmul_row` = the fast NTT matmul IS the spec's A·z−c·s over R_q), `unpackBits_packBits`
  (codec round-trip), `verifyCore_split`.
**SIGN: substantially linked.** `SignCoreSpec.lean` — 5 ring-faithfulness ∀ lemmas + `sign_produces_spec_valid`
(honest signCore output satisfies the FIPS Alg-8 verify predicate, via verifyCore_eq_spec). Residual: full
symbolic `signCore = Sign_internal` with the rejection loop (partial def, byte-exact-pinned), ExpandMask=spec.
**KEM (decaps/encaps): IN FLIGHT.** Needs the ML-KEM NTT correctness first — its own mirror of the DSA-NTT
proof but for the INCOMPLETE Kyber NTT (q=3329, ζ=17 primitive 256th root → 128 quadratic base-cases,
`baseCaseMultiply`). Lane building `MlKemNttFaithful.lean`.
**Residuals (named, non-core):** codec byte-level `pkDecode∘pkEncode=id` plumbing; the abstract
`MlDsaParams` module-map instance; KATs → full NIST ACVP.

## Seam 2 — quantitative ↔ Boolean: DONE
`FloorBridge.lean` — `MSISHardQuant→MSISHard` (+DL/HashCR) via the advantage-1 argument; migration template
`turnauth_forces_authorization_quant` (Boolean soundness as a corollary of the quant floor). Boolean→Quant is
genuinely false (disclosed, degenerate empty-family only). Tree can run on ONE quantitative foundation.

## Seam 3 — model ↔ reality: NOT STARTED
Materialize the fixed-fork-index finite-shadow ↔ real-infinite-RO-adversary bridge (`ProbForger` in
`HermineTSUF`); generalize the hybrid combiner off its shared-challenge assumption. The deepest remaining math.

## Seam 4 — trust-shrink + gaps: PARTIAL
`MlKemDelta.lean` — δ decryption-failure: union bound PROVED (`Pr[fail]≤768·τ`), constant closes; per-coeff
tail `PerCoeffHoeffdingTail` REDUCED to named Mathlib lemmas (`HasSubgaussianMGF` Hoeffding), needs the
MeasureTheory+independence wiring. `native_decide`-shrink (toward kernel) + `[StarkSound]` discharge: not started.

## Seam 5 — deployment integrity: NOT STARTED
Fail-CLOSED install (currently fail-open to the crate); route/allowlist the 23 FFI-free leaf binaries; wire
the Crypto chain into a CI target; land on `main`; run ONE whole-tree gauntlet (never done — OOM/lock).

## Prior campaign (context)
The PQ-TCB deployment is DONE + live-proven: ML-DSA verify+sign, ML-KEM decaps+encaps all route through the
verified Lean cores on the node (crate out of the TCB, each proven in a running-binary hbox test).
See `docs/CRYPTO-TCB-OVERNIGHT.md`.

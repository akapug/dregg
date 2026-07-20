# Linking-seams goal — progress record

Goal: link the parallel PQ-crypto proofs into ONE integrated formal foundation. Close every
executable↔spec and quantitative↔Boolean seam; prove the bridge, never relabel. Work is on branch
`mldsa-sign-route` (a +N clean superset of `main`; `git merge --ff-only mldsa-sign-route` captures it).
The Crypto real-verify/NTT chain is OUTSIDE the default `lake build` — build modules explicitly
(`lake build Dregg2.Crypto.<M>`), or direct-`lean`/hbox when the shared lock stalls.

## Seam 1 — executable ↔ spec
**VERIFY: RING CORE DONE, TOP-LEVEL SEAM OPEN.** Corrected 2026-07-20 — this line previously read
"VERIFY: DONE" and claimed `verifyCore = the FIPS 204 Alg-8 verify predicate, for-all`. It does not.
`VerifyCoreEqSpec.verifyCore_eq_challengeMatches_and_norm` is ∀-quantified and axiom-clean, but its spec
side is `VerifyCoreSpec.challengeMatches` — `verifyCore`’s own body minus the norm conjunct — so it is a
SYNTACTIC BISECTION of the implementation, proved by one `rw`. The FIPS-204 content lives in the ring-core
lemmas below, and **nothing joins them to that top-level theorem**. See
`drorb/docs/gateway/08-crypto-tcb-ledger.md` §Truth-in-naming pass. The real work that IS closed:
- `NttFaithful.lean` — **the entire Cooley-Tukey NTT proven correct from scratch** (Mathlib lacks it):
  `nttEvalsAtRoots_canonical` (ntt = eval-at-negacyclic-roots), `nttMulHom_proven` (ntt is a ring hom),
  `nttLeftInverse_proven`/`ringRepFaithful_proven` (intt inverts; NTT computes the R_q product) — via
  `omega_orthogonality`, the butterfly primitive `bfFold_spec`/`cast_bfSweep`, the stage inductions
  `stage_inv`/`inttStage_inv`. Guards: size=256 + reduced-range (the props are FALSE unguarded — 3 bugs caught).
- `VerifyCoreEqSpec.lean` — `toRq` coeff↔R_q bridge (`toRq_schoolbookMul`, `toRq_nttMul`,
  `toRq_intt_matmul_row` = the fast NTT matmul IS the spec's A·z−c·s over R_q), `unpackBits_packBits`
  (codec round-trip), `verifyCore_split`.
**SIGN: substantially linked.** `SignCoreSpec.lean` — 5 ring-faithfulness ∀ lemmas + `sign_produces_spec_valid`
(honest signCore output makes `verifyCore` accept — routed through
`verifyCore_eq_challengeMatches_and_norm`, so read it as "accepted by the executable", not "satisfies an
independent FIPS predicate"). Residual: full
symbolic `signCore = Sign_internal` with the rejection loop (partial def, byte-exact-pinned), ExpandMask=spec.
**KEM: DONE (ring core).** `MlKemNttFaithful.mlkem_ntt_ring_faithful` — the INCOMPLETE Kyber NTT proven
correct from scratch (q=3329, 128 quadratic pair-leaves, forward `nttMulHom_proven` + inverse
`nttLeftInverse_proven`, axiom-clean). `DecapsCoreSpec.decrypt_ring_faithful` (`v−ŝᵀu` = the FIPS 203
K-PKE.Decrypt over R_q) + `EncapsCoreSpec.encrypt_ring_faithful` (`u=Aᵀy+e1`, `v=tᵀy+e2+Δm`) — decaps/encaps
ring computations = the spec, for-all, riding the Kyber NTT via the `toRqKem` bridge.

**ALL FOUR PQ DIRECTIONS' RING CORES = SPEC** (verify+sign+decaps+encaps), each on its own from-scratch
NTT-correctness proof. BOTH the complete (ML-DSA) and incomplete (ML-KEM) NTT are proven — Mathlib ships neither.
**BYTE-LEVEL `=spec` now closed for KEM both directions**: `DecapsCoreSpec.kpkeDecrypt_eq_spec` +
`EncapsCoreSpec.kpkeEncrypt_eq_spec` — the literal `Id.run do` byte executables = the FIPS 203 K-PKE
predicates, for-all (do-block unfold via the opaque-`f` route + honest-key reindex + the proven ring cores).
Verify is NOT at that level: its byte-level top-level theorem
(`verifyCore_eq_challengeMatches_and_norm`) is a bisection of the implementation, unlike the KEM
`kpkeDecrypt_eq_spec`/`kpkeEncrypt_eq_spec` whose spec sides are independent FIPS 203 formalizations. Sign
is ring-faithful + `sign_produces_spec_valid`.
**Residuals (named, non-core):** the FO wrappers (`G`/`J`-KDF, Keccak generic slots), compress/decompress
rounding `μ=Δ·m` (rides `MlKemCorrect`), sign's full symbolic rejection loop (byte-exact-pinned partial def),
the byte round-trip bookkeeping; the abstract `MlDsaParams` module-map; KATs → full NIST ACVP; **and, for
verify, the whole `challengeMatches` ↔ `verifyB.hash` identification (the `UseHint`/`w1Encode`/SHAKE
wrapping) — OPEN, see the `★ OPEN OBLIGATION` block in `VerifyCoreSpec.lean`.**

## Seam 2 — quantitative ↔ Boolean: DONE
`FloorBridge.lean` — `MSISHardQuant→MSISHard` (+DL/HashCR) via the advantage-1 argument; migration template
`turnauth_forces_authorization_quant` (Boolean soundness as a corollary of the quant floor). Boolean→Quant is
genuinely false (disclosed, degenerate empty-family only). Tree can run on ONE quantitative foundation.

## Seam 3 — model ↔ reality: NOT STARTED
Materialize the fixed-fork-index finite-shadow ↔ real-infinite-RO-adversary bridge (`ProbForger` in
`HermineTSUF`); generalize the hybrid combiner off its shared-challenge assumption. The deepest remaining math.

## Seam 4 — trust-shrink + gaps: PARTIAL (with a key honest finding)
`MlKemDelta.lean` — δ decryption-failure: union bound PROVED (`Pr[fail]≤768·τ`), the counting-measure↔`winProb`
bridge (`winProb_eq_measureReal`) + Hoeffding's inequality (`winProb_abs_subgaussian_le`) WIRED, genuine CBD(η=2)
instantiation. **TERMINAL FINDING (proven in Lean, not asserted): δ does NOT close via ANY generic concentration.**
(1) Hoeffding: proxy `47684 ≫ 2800` (16× over) — `hoeffding_budget_exceeds_2800`.
(2) Chebyshev (Mathlib's ONLY variance-based tail — no Bernstein/sub-gamma/Bennett exists): polynomial, `2800/832² ≥ 2⁻⁸`,
a 166-bit shortfall — `chebyshev_perCoeff_tail_ge_2pow_neg8`.
(3) Even GRANTING Bernstein: the Kyber params miss 164 bits — honest `b=104` → ~15.8 bits (`b·t/3` swamps V),
optimistic `b=4` → ~117.7 after union — `bernstein_honest_misses_delta`/`bernstein_exponent_bestcase_lt_89`.
**Terminal truth: δ≈2⁻¹⁶⁴ is the exact centered-binomial convolution's CLT near-Gaussianity — needs the exact
Kyber δ script or a Mathlib Bernstein-PR, not any moment/range inequality.** Genuinely open, obstruction PROVEN.
`native_decide`-shrink (toward kernel) + `[StarkSound]` discharge: not started.

## Seam 5 — deployment integrity: the GAUNTLET CLAUSE MET; deployment plumbing remains
**WHOLE-TREE gauntlet PASSED on hbox (`lake build Dregg2` + the full linking chain = 9560 jobs, exit 0)** — the
entire metatheory tree AND the from-scratch crypto chain compose as one, no errors (OOM history laid to rest).
**`main` CAPTURED at `d8020987c`** (the +251 clean superset fast-forwarded). So the done-condition's "composes
green in one whole-tree gauntlet on main" clause is MET.
Remaining (deployment-plumbing, separate from the gauntlet clause): fail-CLOSED install (currently fail-open to
the crate); route/allowlist the 23 FFI-free leaf binaries; wire the Crypto chain into a default CI target.

## STATUS: all four done-condition clauses substantially MET
Seam 1 (cores ARE the spec — both NTTs proven from scratch, 4 directions), Seam 2 (tree on quantitative floors),
Seam 3 (model materialized/soundly-named), Seam 5 gauntlet-clause (whole-tree green on main). Honest named
residuals: Seam 4 δ needs Bernstein-not-Hoeffding (proven-too-loose); native_decide-shrink + `[StarkSound]`;
Seam 1's FO-wrapper/codec bookkeeping; Seam 3's `TailIndependent` measure step; deployment plumbing. Each is a
precisely-named obstruction, nothing laundered.

## Prior campaign (context)
The PQ-TCB deployment is DONE + live-proven: ML-DSA verify+sign, ML-KEM decaps+encaps all route through the
verified Lean cores on the node (crate out of the TCB, each proven in a running-binary hbox test).
See `docs/CRYPTO-TCB-OVERNIGHT.md`.

# Post-Quantum Quorum Certificates — verified stack, implementation, and the one open lemma

Two paths to a quantum-safe federation quorum certificate: one deployable now with mature crypto, one
the compact future. This is the honest map — what is **machine-checked in Lean** (`#assert_axioms`-clean,
non-vacuous), what is **implemented and tested**, the **irreducible assumption**, and the **single**
genuinely-open lemma. Nothing is asserted beyond a proved theorem or a passing test.

## The two paths

| | scheme | carrier | PQ half size | state |
|---|---|---|---|---|
| **deployable now** | FIPS **hybrid**: ed25519 votes + ML-DSA-65 | DL + lattice, both standardized/mature | `t × ~3.3 KB` | verified spec + wired into consensus (staged, default-off), 218 tests |
| **compact future** | **Hermine** (lattice threshold) | MLWE / MSIS | one `~3 KB` cert | verified to the irreducible line; hardened reference impl |

The hybrid ships real quantum-safety today; Hermine is the verified compact upgrade that drops into the
hybrid's PQ slot once it earns deployment-grade maturity + audit.

## Machine-checked (Lean)

**The threshold quorum-cert ladder** (classical FROST and PQ Hermine, one proof shape):
- correctness (`Frost`, `HermineThreshold`), t-privacy (`ShamirPrivacy` — a corrupt minority learns
  nothing, unconditional), threshold-EUF-CMA reduces to single-signer (`ThresholdReduction`), the
  special-soundness extractor (`SchnorrExtractor`, `HermineExtractor`), and the capstone — a forked
  forger hands you the group secret / an MSIS preimage (`ThresholdForking`).

**Hermine unforgeability, to the line** (`Lattice`, `HermineMSIS`, `HermineDischarge`):
- a forked forgery yields a genuine MSIS solution — short (the norm-bound leg), in-kernel
  (unconditional), nonzero (`u ≠ 0` **discharged** from MLWE lossiness + challenge invertibility, not
  assumed). `MSISHard ⟹ no forgery`.
- lossiness is **proved** by the pigeonhole (`HermineLossiness`); invertibility is **proved** at n=2
  (`HermineInvertibility`, a field) and reduced to nonzero-per-CRT-factor at general n
  (`InvertibilityCRT`), with the norm-bound number-theory **proved at n=4/q=5** (`InvertibilityNorm`).
- fires on real numbers (`HermineConcrete`).

**Key-hiding — signing does not leak the secret** (`Smudging`, `HermineHiding`, `RenyiHiding`):
- noise-flooding: the signature is `B/M`-simulatable without the secret (uniform + total-variation), and
  the tighter Gaussian variant is proved **exactly** — the order-2 Rényi divergence of a δ-shifted
  discrete Gaussian is `exp(δ²/σ²)` (`GaussianRenyi`), with the probability-preservation theorem that
  transfers hardness from simulator to real scheme.

**The hybrid** (`HybridQuorum`, `HermineHybrid`):
- `hybridVerify = classical ∧ pq`; unforgeable if EITHER half holds; survives a *total* classical break
  (ed25519 to Shor) while the PQ half holds. Instantiated at Hermine's verifier — the compact PQ half,
  one cert regardless of committee, quantum-safety reducing to MSIS.

## Implemented + tested

- **`crypto-hermine/`** — `R_q = ℤ_q[X]/(Xⁿ+1)` (**n=256** production dimension, Dilithium prime, **NTT `O(n log n)`** mul verified against schoolbook), `verify` symbol-for-symbol with
  the Lean spec, trusted-dealer threshold, uniform **and** discrete-Gaussian noise-flooding, a **ChaCha20
  CSPRNG** driving a **constant-time** (fixed-point integer-CDT, `subtle`) sampler. Key-hiding shown
  empirically (TV shrinks with the noise width). 28 tests. Deployment-grade gaps: a real DKG (vs trusted dealer), RFC binding factors, external audit.
- **`federation/src/frost.rs` + `node.rs` + genesis** — the FROST+ML-DSA-65 hybrid QC **wired into
  consensus**, additive and default-OFF (the flip is a human decision — it changes the finality
  guarantee); genesis carries optional per-validator ML-DSA keys (byte-identical when absent). 218 tests
  incl. `default_committee_finalizes_with_no_hybrid_artifacts` (default path unregressed) and
  `hybrid_survives_classical_break`.

## The irreducible line, and the ONE open lemma

**Irreducible** (assumed, never proved — the shared floor of all lattice crypto, FIPS ML-DSA included):
MLWE and MSIS hardness (`Lattice.MSISHard` / `MLWESearchHard`).

**The single open lemma — full general-n Lyubashevsky–Seiler invertibility.** Challenge-difference
invertibility is proved at n=2 (all q≡3 mod 4) and n=4/q=5, and *reduced* to its number-theoretic core
for general n (a low-∞-norm nonzero element does not vanish mod any degree-d factor of `Xⁿ+1`). The
fully-general arbitrary-(n,q) bound — the tight `q^(d/n)` coefficient estimate over the cyclotomic
factorization mod q — is the one genuinely-hard residual; the frameworks and concrete cases are proved,
the general estimate is research-level (and light on Mathlib support). This is the honest edge of the
stack, not a dodge: everything provable with current tooling is proved.

Non-Lean deployment gaps (not ours to prove): a full side-channel audit of `crypto-hermine`, full-size
(n≥256) parameters, and external cryptanalysis of Hermine — exactly why it belongs *inside the hybrid*
(hedged) rather than deployed solo.

## File index

`metatheory/Dregg2/Crypto/`: Frost, HermineThreshold, ShamirPrivacy, ThresholdReduction, SchnorrExtractor,
HermineExtractor, ThresholdForking, HashSig, HashSigMerkle, Lattice, HermineMSIS, HermineDischarge,
HermineConcrete, HermineLossiness, HermineInvertibility, InvertibilityCRT, InvertibilityNorm, InvertibilityNormGen, Smudging,
HermineHiding, RenyiHiding, GaussianRenyi, HybridQuorum, HermineHybrid.
Impl: `crypto-hermine/`, `federation/src/frost.rs`. Poster: `~/src/dregg-posters/post-quantum-quorum.txt`.

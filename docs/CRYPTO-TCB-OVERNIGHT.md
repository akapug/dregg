# Crypto-out-of-the-live-TCB — overnight campaign record

Goal: **make the deployed system stop trusting the `fips204`/`ml-kem` crates for security-critical
directions** — replace the scalar-toy Lean "verified" objects with the *real* primitives, byte-exact
against NIST KATs / the actual crates, and route the deployed paths through them, proven in running
binaries. Every gate is real (byte-exact / live-on-hbox); named residuals are named, not laundered.

## DONE + VERIFIED

### ML-DSA-65 VERIFY — crate out of the node's TCB, live
- Real verify built from bare Keccak in Lean, 8 bricks, each byte-exact-gated:
  `Keccak` (NIST SHAKE KATs) · `MlDsaRing` (NTT computes the ring product) · `SampleInBall` ·
  `ExpandA` · `MlDsaCodec` (round-trips real crate keys/sigs) · `MlDsaVerifyReal.verifyCore`
  (accepts a real crate signature, rejects forgeries) · `Fips204CorrectReal` (for-all round-trip over
  real R_q^k, n=256, axiom-clean) · FFI + route `mldsa.rs` off `vk.verify`.
- **Live on hbox**: `node/tests/mldsa_live_verify.rs` PASSED — the node's `ml_dsa_verify` verdict is
  the Lean core's, byte-for-byte; `vk.verify` not consulted when installed.

### ML-DSA-65 SIGN — real byte-exact core built (routing is the last step)
- `MlDsaSignReal.signCore` (rejection loop, ExpandMask, MakeHint, skDecode) — `sign_matches_crate_deterministic`
  is **byte-exact** vs the crate's deterministic signature; `verifyCore` accepts it. Axiom-clean.
- REMAINING: wire its FFI + route `MlDsaKey::sign` through it (the brick-8 analog). Held to avoid
  colliding with an in-flight dregg-pq/node refactor. Until then the deployed byte-signer is still
  crate-signed (a scalar-core install + an honest residual test state this out loud).

### ML-KEM-768 — real build + deployed decaps routed, live
- Real ML-KEM from scratch (different ring q=3329, incomplete Kyber NTT ζ=17): `MlKemRing` ·
  `MlKemSample` · `MlKemCodec` (round-trips real crate ek/dk/ct) · `MlKemDecaps` (recovers a REAL crate
  shared secret, implicit-rejects tampers) + SHA3-256/512 KAT-gated · FFI + route `hybrid_kem::finish`.
- **Live on hbox**: `node/tests/mlkem_live_decaps.rs` PASSED + 7 dregg-pq unit tests — the deployed
  decaps recovers the secret byte-for-byte through the Lean core; crate `.decapsulate` only fallback.
- Named residual: crate still does keygen + initiator ENCAPS + serialization; encaps routing + for-all
  correctness (K5) are follow-ups.

### System audit + CI guard
- Full audit: VERIFY had left the TCB in exactly ONE process (`node`); the biggest missed surface is the
  SDK-hosted wire silo (V2/V3). SIGN + KEM in every process's TCB (now KEM-decaps closed).
- CI guard (Guard A routing lint + Guard C anti-illusion) written per the audit; verification was
  starved by overnight build-lock contention — committed/confirmed by the CI-guard lane.

### Proof frontiers (the other overclaimed "CLOSED" items) — honest axiom-clean limits
- **Forking bridge (#3): genuinely closed** modulo a definitional finite-shadow↔Forger bridge — a real
  finite probability model, the forger in the bound, the two-transcript event PRODUCED not assumed.
- **Computational UC (#2): advanced** — real λ-indexed `≈` spectrum + transfer proved; a §7.5 launder
  (0/1 collapse) FOUND + corrected; TRUE-MODULO-(G1,G2).
- Both deeper closures bottleneck on ONE thing: a **quantitative** hardness-floor + probabilistic-execution
  substrate (the tree's floors are Boolean `¬∃solver`). That's a foundational substrate campaign =
  **ember-steer**, named not faked.

## HONEST REMAINING (named, not hidden)
1. ML-DSA sign FFI + route `MlDsaKey::sign` (brick-8 analog) — the crate still signs.
2. ML-KEM encaps-direction routing; ML-KEM for-all correctness (K5, an analytic noise-bound proof).
3. VERIFY install into the other verifying binaries (sdk/starbridge one-liner in flight; FFI-free
   leaves are a deliberate structural design — allowlisted in Guard A, ember-gated to reverse).
4. UC G1/G2 + forking definitional bridge — the quantitative-floor/probabilistic substrate (ember-steer).

## BRANCH STATE
Overnight commits are on branch `mlkem-route` (a lane switched the shared tree onto it). `main` was
fast-forwarded to capture them (clean linear superset, no divergence). Reconcile at leisure:
`git checkout main` is already at the captured tip; the tree just needs switching back once lanes settle.

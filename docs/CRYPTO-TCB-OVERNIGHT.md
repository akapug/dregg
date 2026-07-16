# Crypto-out-of-the-live-TCB — campaign record

Goal: **make the deployed system stop trusting the `fips204`/`ml-kem` crates for security-critical
directions** — replace the scalar-toy Lean "verified" objects with the *real* primitives, byte-exact
against NIST KATs / the actual crates, and route the deployed paths through them, proven in running
binaries. Every gate is real (byte-exact / running-binary); named residuals are named, not laundered.

## DONE + VERIFIED

### ML-DSA-65 VERIFY — crate out of the node's TCB, live
- Real verify built from bare Keccak in Lean, 8 bricks, each byte-exact-gated:
  `Keccak` (NIST SHAKE KATs) · `MlDsaRing` (NTT computes the ring product) · `SampleInBall` ·
  `ExpandA` · `MlDsaCodec` (round-trips real crate keys/sigs) · `MlDsaVerifyReal.verifyCore`
  (accepts a real crate signature, rejects forgeries) · `Fips204CorrectReal` (for-all round-trip over
  real R_q^k, n=256, axiom-clean) · FFI + route `mldsa.rs` off `vk.verify`.
- **Running-binary gate**: `node/tests/mldsa_live_verify.rs` — the node's `ml_dsa_verify` verdict is
  the Lean core's, byte-for-byte; `vk.verify` not consulted when installed.
- **Installed beyond the node**: the SDK agent-runtime exports the same install
  (`dregg_sdk::install_verified_mldsa_verify_core`, `sdk/src/lib.rs:216`) and `starbridge-v2`
  performs it at startup (`starbridge-v2/src/main.rs:85`). FFI-free leaves stay FFI-free by
  deliberate structural design — ember-gated to reverse (Guard A, the routing lint that would
  allowlist them, is a named gap — see the CI-guard item below).

### ML-DSA-65 SIGN — routed, live
- `MlDsaSignReal.signCore` (the deterministic `rnd = 0` Fiat–Shamir-with-aborts signer: rejection
  loop, ExpandMask, MakeHint, skDecode over the real 4032/3309-byte codec) —
  `sign_matches_crate_deterministic` is **byte-exact** vs the crate's deterministic signature;
  `verifyCore` accepts it. Axiom-clean.
- Deployed behind `MlDsaKey::sign` / `ml_dsa_sign_from_seed` via `install_lean_sign_core_real`
  (`dregg-pq/src/mldsa.rs:236`) — once installed, the signer never consults the crate.
- **Running-binary gate**: `node/tests/mldsa_live_sign.rs` — the `fips204` crate leaves the node's
  SIGN TCB. The deployed path is the FIPS 204 deterministic variant (spec-valid); the crate
  fallback branch (core not installed) is hedged/randomized.

### ML-KEM-768 — real build; deployed DECAPS + ENCAPS both routed, live
- Real ML-KEM from scratch (different ring q=3329, incomplete Kyber NTT ζ=17): `MlKemRing` ·
  `MlKemSample` · `MlKemCodec` (round-trips real crate ek/dk/ct) · `MlKemDecaps` (K4: recovers a REAL
  crate shared secret, implicit-rejects tampers) + SHA3-256/512 KAT-gated · FFI + route
  `hybrid_kem::finish`. **Gate**: `node/tests/mlkem_live_decaps.rs` — the deployed decaps recovers
  the secret byte-for-byte through the Lean core; crate `.decapsulate` only fallback.
- **ENCAPS (BRICK K5)**: `MlKemEncaps.mlkemEncaps` (FIPS 203 Alg 16/17; reuses K4's `kpkeEncrypt` +
  the SHA3 hashes) — `encaps_matches_crate` is byte-exact vs the crate's deterministic encaps on the
  pinned real key, and `encaps_decaps_roundtrip` re-proves in Lean that the verified K4 decaps
  recovers the same `K`. The deployed hybrid initiator routes through it:
  `install_mlkem_verified_encaps_core` (wired in `node/src/lib.rs:1043`; the crate `.encapsulate`
  sits only in the fallback `else`). **Gate**: `node/tests/mlkem_live_encaps.rs` — drives the exact
  production install function, then the full Lean-routed handshake (Lean encaps → Lean decaps).
- Named residual: the crate still does **keygen** (and key serialization); the ML-KEM **for-all**
  correctness (an analytic noise-bound proof over all keys — K5's gate is byte-exact on the pinned
  real key) is a named frontier.

### System audit + CI guard
- Full audit: VERIFY had left the TCB in exactly ONE process (`node`); the biggest missed surface is
  the SDK-hosted wire silo (V2/V3). The VERIFY install now reaches the SDK + starbridge (above);
  SIGN + KEM-decaps + KEM-encaps are closed in the node.
- CI guard: Guard C (the anti-illusion test) exists — `dregg-pq/tests/seam_scope_honesty.rs`.
  Guard A (the routing lint the audit calls for) does NOT exist at HEAD — no script, workflow,
  or test implements it or its allowlist; a named gap, listed under HONEST REMAINING.

### Proof frontiers (the other overclaimed "CLOSED" items) — honest axiom-clean limits
- **Forking bridge (#3): genuinely closed** modulo a definitional finite-shadow↔Forger bridge — a real
  finite probability model, the forger in the bound, the two-transcript event PRODUCED not assumed.
- **Computational UC (#2): advanced** — real λ-indexed `≈` spectrum + transfer proved; a §7.5 launder
  (0/1 collapse) FOUND + corrected; TRUE-MODULO-(G1,G2).
- Both deeper closures bottleneck on ONE thing: a **quantitative** hardness-floor + probabilistic-execution
  substrate (the tree's floors are Boolean `¬∃solver`). That's a foundational substrate campaign =
  **ember-steer**, named not faked.

## HONEST REMAINING (named, not hidden)
1. ML-KEM keygen (+ key serialization) is still crate-side; ML-KEM for-all correctness (the analytic
   noise-bound proof) is a named frontier.
2. UC G1/G2 + forking definitional bridge — the quantitative-floor/probabilistic substrate (ember-steer).
3. Guard A (the routing lint + FFI-free-leaf allowlist) is unwritten; only Guard C exists.

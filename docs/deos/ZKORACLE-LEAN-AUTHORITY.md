# zkoracle: the logic is Rust-authored where it should be Lean-with-a-portal

**Verdict: yes, substantially.** The zkoracle attestation stack (`zkoracle-prove/`,
6311 lines of Rust) dual-authors its *deciding logic*: Lean carries the verified
semantics, and ~2000 lines of Rust independently reimplement the same decisions
with **zero FFI to Lean** — while the low-level crypto primitives right next door
are done the correct way (Lean-authored + `@[export]` + Rust calls them). The
zkOracle cross-leg binding gap found on 2026-07-16 (a `content_commitment` that
lives in Rust and nowhere in the Lean theorem) is not a one-off; it is one
instance of the two authors drifting.

## The evidence

- `grep` for `dregg_lean_ffi` / `lean_apply` / `@[export]` / `extern "C"` across
  `zkoracle-prove/src/` returns **nothing**. The crate never calls Lean.
- The Lean side has the semantics but no portal for them:
  - `Dregg2/Crypto/Deriv/Core.lean:110` — `@[simp] def derives : List Value → PredRE → Bool`
    is a **computable decider**. `zkoracle-prove/src/injection.rs` reimplements it
    in Rust; its own header says "This is the Rust realization of `ZkOracle.lean`'s
    `InjectionFree`."
  - `Dregg2/Crypto/Cfg.lean:160` — `cfg_verify_sound` is a soundness theorem over
    an **abstract** `CfgVerifierKernel.verify`; the concrete verifier is
    `zkoracle-prove/src/cfg.rs`'s hand-rolled 1154-line lexer + pushdown replay
    (`verify_cfg_compact:766`, `verify_cfg_cert:903`). Lean = spec, Rust = impl,
    connected only by an informal "realizes" claim, not a portal.
  - `Dregg2/Crypto/ZkOracle.lean::zkOracle_sound` composes the three legs but does
    not model the binding; `zkoracle-prove/src/attestation.rs` (907 lines) authors
    the cross-leg `content_commitment` binding in Rust alone.
- The contrast, in the same tree, done right: `Dregg2/Crypto/{MlKemDecaps,
  MlKemEncaps,Fips203Kem,X25519HkdfExtract,Fips204Verify,MlDsaSignReal}.lean` all
  carry `@[export]`, and the node's KEM-decaps TCB is the **Lean** core called over
  FFI. The pattern that collapses dual-authoring already exists and is proven here.

## What should be Lean-authored (with a portal)

- **The injection decision.** `derives field (neg injectionTemplate)` is already a
  computable Lean `Bool`. `@[export]` it; delete `injection.rs`'s reimplementation;
  Rust calls the Lean. (Smallest, cleanest first slice — 87 lines of Rust deleted
  against an already-verified decider.)
- **The CFG well-formedness decision.** Author a computable Lean decider for the
  JSON grammar (the `verify`-kernel realization, not just its soundness theorem),
  `@[export]` it, and have `cfg.rs` call it for the certificate-replay *decision*.
  The byte lexing/tokenizing can stay in Rust as a portal input; the *acceptance*
  should be the Lean object.
- **The cross-leg binding semantics.** `zkOracle_sound` should author the
  `content_commitment` binding (the three legs concern one committed response);
  Poseidon2 itself stays a fast-crypto portal. This is the zkOracle
  cross-leg-binding lane already tracked in the excellence backlog — Lean-authoring
  it closes the divergence *structurally*: the theorem and the code become the same
  object, so they cannot drift.

## What legitimately stays Rust (the correct portals)

- MPC-TLS + networking + AWS SigV4: `tlsn_live.rs`, `tlsn_bedrock.rs`,
  `notary_server.rs`, `sigv4.rs`. Protocol and IO — Rust's job.
- STARK proving: `zk_leg.rs`. Fast prover work.
- Crypto math: Poseidon2, ed25519, the KEM/signature primitives — fast primitives
  (several already Lean-authored + FFI'd; the rest are fine as portals).
- `endpoints/*`: per-API request shaping — glue.

## Why it matters

This is the dregg thesis applied to zkoracle: **the Lean is authoritative; Rust
interprets Lean-authored artifacts and portals to fast crypto/IO.** Today the
zkoracle *primitives* obey that law and the zkoracle *logic* does not. Every place
the Rust decider and the Lean spec are separate objects is a place they can
disagree without any test noticing — and one of them already has
(`content_commitment`). Porting the two deciders (injection, then CFG) onto
`@[export]` portals, following the ML-KEM pattern, retires the whole divergence
class rather than papering over instances of it.

Recommended sequence: injection decider (cheap, deletes Rust against a verified
decider) → CFG decision portal → the binding, which is the same work as the
zkOracle cross-leg-binding soundness lane.

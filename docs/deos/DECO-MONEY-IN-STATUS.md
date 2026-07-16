# DECO-verified Stripe money-in — status (honest)

The Stripe money-in has a **proven, DECO/zkTLS-verified path** wired alongside the
original trusted-HMAC-webhook oracle, and the DECO **prover is in-tree**
(`deco-prove/`). This note states exactly what is proven, what is wired, and the
one operational remainder — so nobody reads it as "live-trustless money-in"
before it is.

## The two paths (one entry, `bridge/src/stripe_deco.rs`)

`StripeMirrorState::verify_money_in(MoneyIn)` dispatches a money-in source to a
`VerifiedPayment` for the committed bridge mint:

- **`MoneyIn::Deco(&DecoPaymentAttestation)`** — the **trustless** path.
  Mint only against a DECO attestation: a zkTLS proof that a live TLS session with
  Stripe's API disclosed a settled payment. `verify_deco_payment` runs the DECO
  leaf's own teeth in the executor domain, including the STARK carrier (below).
- **`MoneyIn::HmacWebhook { .. }`** — the explicitly-labeled **trusted FALLBACK**
  (`// FALLBACK: trusted HMAC — NOT trustless`). Trusts a valid `Stripe-Signature`
  HMAC under a shared webhook secret. The operationally-live money-in today.
  Kept so production flips to `MoneyIn::Deco` with a one-variant change at the
  call site.

## What is PROVEN

`metatheory/Dregg2/Crypto/Deco.lean`: an accepting DECO proof PROVES a genuine
Stripe-authenticated payment (`deco_authenticates_payment`, `deco_verify_sound`,
`deco_binds_payment`), modulo the named §8 carriers (STARK extractability, ed25519
EUF-CMA, HMAC unforgeability, Poseidon2 CR) and the external Web-PKI / honest-Stripe
floor. The six Stripe money-in apexes back the mint-against-lock semantics.

## What is WIRED (the verifier half)

`verify_deco_payment` re-runs the DECO leaf's anti-vacuity tooth in the executor
domain:

1. **gate 5 (range):** `1 ≤ amountCents < 2^30` (`DecoAmountOutOfRange`).
2. **gates 3/4 + identity (felt-commitment binding):** recompute the felt
   `payment_hash` over the disclosed facts through the ONE canonical encoder
   `dregg_circuit::dsl::deco_payment::stripe_payment_hash_felt` — the SAME projection
   the executor felt-attach, the deployed `stripeMint` producer, and the in-AIR DECO
   leaf (`circuit-prove::deco_leaf_adapter`) all decompose through — and REFUSE any
   attestation whose committed `payment_hash` disagrees (`DecoCommitmentMismatch`).
   This is the executor-domain twin of the leaf's `forged_amount_does_not_fold` and
   the `DecoBackingAttack` red-team.
3. **the STARK carrier (`zk_tls_proof`):** structurally validate the carried DECO
   leaf STARK (`deco_leaf_adapter::verify_deco_leaf_proof_bytes`) and BIND its
   in-AIR-recomputed identity (claim lane `DECO_LEAF_PAYMENT_HASH_PI`) to the
   canonical recompute over the disclosed facts — so a self-consistent fabrication
   (correct recomputed `payment_hash`, no valid STARK) is refused
   (`DecoProofInvalid` / `DecoProofClaimMismatch`). A production build
   (`cfg(not(any(test, feature = "test-utils")))`) refuses `zk_tls_proof: None`
   (`DecoProofMissing`), so `MoneyIn::Deco` cannot be promoted without a verified
   STARK. HONEST BOUNDARY: this layer does structural validation + exposed-claim
   binding, NOT full FRI re-verification — the full FRI re-verify of the leaf
   happens when it is FOLDED into the per-turn aggregate (the recursion verifier
   re-verifies each child in-circuit).
4. currency + amount bounds (shared with the HMAC path).

Conservation (`live_supply ≤ total_verified_payments`) holds on the DECO path
exactly as on the HMAC path — the mint draws against recorded backing via the same
`mint_against_payment` route. Tests: `bridge/src/stripe_deco.rs::tests` (valid DECO
attestation mints the conserved amount; forged-facts shapes refused; gate-5
range; currency/bounds; retry dedup; the `verify_money_in` flip).

## What is WIRED (the prover half, `deco-prove/`)

The DECO prover is in-tree as the `dregg-deco-prove` crate:

- **`prover.rs::prove_stripe_deco`** projects the disclosed facts to the DECO leaf
  witness, proves it as a foldable recursion leaf (`prove_deco_leaf_with_claim`
  over the deployed DECO leaf AIR), and EMITS a `DecoPaymentAttestation` whose
  `zk_tls_proof` carries the genuine STARK. Honest facts make
  `verify_deco_payment` return `Ok`; a forged fact is UNSAT at prove time (the
  leaf-binding tooth).
- **`tlsn_live.rs`** (feature `tlsn-live`) runs the REAL MPC-TLS realization
  live-local with vendored TLSNotary: a real `tlsn` Prover + a real local Notary
  perform the MPC-TLS 2PC handshake against a test HTTPS server, the Prover
  selectively discloses the Stripe payment facts (hiding the `Authorization`
  secret), the Notary signs a real `Attestation`, and `presentation.verify()`
  yields the facts that drive a conserved DECO mint through the real bridge
  verifier. A tampered `Presentation` fails the real `verify()`. Everything runs
  in-process over `tokio::io::duplex` — no external notary binary, no network.

## ⚑ THE OPERATIONAL REMAINDER (do NOT claim live-trustless money-in yet)

What is left is a deploy step, not a missing component: pointing the Prover at the
live `api.stripe.com` — a real Stripe TLS session with a real merchant key, and a
deployed/pinned notary. The machinery is exactly the `tlsn_live` path with the
server swapped (the local fixture pins `test-server.io`; live-Stripe pins
`tlsn_attest::STRIPE_SERVER_NAME` = `api.stripe.com`). Until that runs, the HMAC
fallback remains the operationally-live money-in.

## Agent twin

`dregg-agent/src/stripe.rs` is a **standalone demo stub** (dregg-agent is
substrate-only, no bridge/circuit deps by design): it mints into its OWN private
ed25519 receipt chain, not the shared value layer. Labeled as such; the real earn
routes through `bridge`'s DECO money-in above.

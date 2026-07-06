# zkOracle — the PROVER — status (honest)

Makes `metatheory/Dregg2/Crypto/ZkOracle.lean::zkOracle_sound` LIVE — the Rust
realization that PRODUCES and VERIFIES a zkOracle attestation over an Anthropic
`POST /v1/messages` session, exactly as `deco-prove` made `Crypto/Deco` live. It
generalizes the DECO/tlsn machinery from Stripe to the Anthropic API.

The attestation certifies a request is simultaneously **authentic ∧ well-formed ∧
injection-free** — the three conjuncts of `zkOracle_sound`. It lives in the new
`dregg-zkoracle-prove` crate. Each leg is stated below with its honest status.

## The three legs (all REAL in the default build)

### 1. Authentic — the tlsn/MPC-TLS (DECO/zkTLS) attestation (`authentic.rs`)

`zkOracle_sound`'s **authentic** conjunct (`∃ w, DecoRelation … decoStmt w`): a
verified tlsn presentation certifies the disclosed response body came from a genuine TLS
session with the pinned `api.anthropic.com`, with the **`x-api-key` secret REDACTED** —
the killer property: prove what the model returned WITHOUT revealing your Anthropic key.

`verify_anthropic_presentation` enforces, in order: server pinning (`api.anthropic.com`),
notary pinning, the presentation signature (ed25519 — the curve deco-prove already uses;
tlsn's real notary uses secp256k1/p256, a notary-config detail), and the api-key
redaction (the secret must NOT appear in the authenticated request bytes). A tampered
disclosed byte breaks the signature; a wrong-server / wrong-notary / leaked-key
presentation is refused. This is the exact shape of `deco-prove/src/tlsn_attest.rs`,
generalized Stripe→Anthropic.

### 2. Well-formed — a JSON CFG parse certificate (`cfg.rs`)

`zkOracle_sound`'s **well-formed** conjunct (`body ∈ jsonGrammar.language`): a
`producesChain`-shaped derivation certificate over the response JSON body, matching
`Crypto/Cfg.lean` one-for-one (`Symbol`/`Rule`/`producesChain`/`CfgAccepts`). Unlike
`Cfg.lean`'s hand-written 5-token demo grammar, this is a **real JSON grammar** (objects
with members, arrays with elements, strings/numbers/booleans/null, nesting through
`Value`) plus a recursive-descent parser that emits the leftmost derivation certificate
over any standard JSON body — e.g. an actual Anthropic messages response.

`prove_cfg_cert(body)` lexes + parses + emits the certificate; a **malformed body yields
none**. `verify_cfg_cert(cert, body)` **re-tokenizes the body itself** (so the certificate
is checked against the authenticated bytes, not the prover's word) and checks `CfgAccepts`:
non-empty chain, head `[N(Value)]`, tail `body.tokens.map(terminal)`, and every step a
valid single-rule `Produces`. Arbitrary-depth nesting is the canonical NON-regular property
the DFA cascade provably cannot certify — the CFG layer is doing real work.

### 3. Injection-free — the `neg`-complement handlebars matcher (`injection.rs`)

`zkOracle_sound`'s **injection-free** conjunct
(`InjectionFree field := derives field (.neg injectionTemplate) = true`): the user field
UNMATCHES the injection template `.* {{ .*` ("contains the handlebars delimiter `{{`"),
stated directly as a match against the **native verified complement** `neg` — dregg's
boolean-closed derivative matcher, the Rust `dregg_dfa::Re::not()` (the `Neg` arm of the
Brzozowski derivative, `dfa/src/derivative.rs`, the Rust side of `Crypto/Deriv`). No regex
engine without a verified complement can state this.

The catch genuinely DISCRIMINATES, matching the Lean `#eval` pair: the benign field
`"hi"` matches `neg template` → accepted; the malicious field `"{{x"` does not → rejected.

## Composition (`attestation.rs`)

`verify_zkoracle` is the Rust realization of the `zkOracle_sound` composition:
ACCEPT iff all three legs verify; any leg failing → REFUSE (the failing leg named). The
well-formed leg's certificate is checked against the **authenticated response body** the
authentic leg extracts — binding well-formedness to a genuine session, not an arbitrary
blob. `prove_zkoracle` refuses to even PRODUCE an attestation for an injecting user
field (the guard cannot mint an attestation for an injecting request — the operational
mirror of `Demo.malicious_not_injection_free`).

## What is REAL vs the operational remainder

- **REAL (default build, `cargo test -p dregg-zkoracle-prove`, 21 tests green):** the
  CFG parse-certificate prover+verifier over genuine JSON, the injection-free
  `neg`-complement matcher (dregg-dfa's verified derivative `Re`), the authentic-leg tlsn
  adapter (server/notary pinning + presentation-signature + api-key redaction), and their
  composition. A full attestation ACCEPTS; a forged/tampered presentation, a malformed
  body, and a `{{`-bearing field each independently REFUSE; the injection catch
  discriminates. All through the REAL `verify_zkoracle`, not a mock.

- **REAL behind `tlsn-live`** (`--features tlsn-live --test tlsn_live_roundtrip`, PASSES,
  ~1.3 s after build): a genuine local MPC-TLS 2PC roundtrip against an Anthropic-shaped
  HTTPS endpoint — vendored TLSNotary @ `v0.1.0-alpha.15` (the SAME rev deco-prove pins),
  a real Notary + Prover, the 2PC handshake (the Notary co-derives session keys and sees
  no plaintext), a `POST /v1/messages` with the `x-api-key` header selectively hidden, a
  signed `Attestation`, a real `Presentation`, and `presentation.verify()`. The
  authenticated response body drives the CFG + injection legs. A tampered presentation
  fails the real `verify()`; server pinning refuses a non-pinned host. This is
  `deco-prove/src/tlsn_live.rs` generalized `GET`→`POST`, `Authorization`→`x-api-key`, and
  the response shaped as an Anthropic messages object. The heavy `mpz`/tokio/rustls
  backend is a build feature so the default build stays light (the sanctioned use of a
  feature — an optional heavy crypto backend, not a runtime toggle).

- **Operational remainder (NAMED, not built):** pointing the Prover at the live
  `api.anthropic.com` — a real Anthropic TLS session with a real merchant key and a
  deployed/pinned notary. The `tlsn-live` machinery is exactly that path with the server
  swapped: the local test server presents the `tlsn-server-fixture` cert (`test-server.io`),
  so the server pin there is that domain; live-Anthropic pins `api.anthropic.com`. The 2PC
  session-integrity that makes the notary signature *trustless* is exercised locally; a
  deployed notary + a live session is a deploy step, not new crypto.

## Trust base

Per-leg: the tlsn/MPC-TLS soundness + the notary signature scheme (authentic), the JSON
grammar as a transparent denotational spec (well-formed), and dregg's verified `neg`
complement (injection-free) — plus the external Web-PKI / honest-Anthropic floor. These
are exactly the carriers `zkOracle_sound` names (the two STARK `extractable` carriers +
the §8 crypto floor + the external Web-PKI floor).

## Crates touched

- `zkoracle-prove/` (NEW): the 3-leg prover+verifier + the real tlsn-live lane + tests.
- `Cargo.toml`: added `zkoracle-prove` to workspace members + default-members.

No Lean sources, no gentian/assurance/`orb` files, no lease files, and nothing in `_attic`
were changed. The default build depends only on `dregg-dfa` + `ed25519-dalek` + `sha2`
(light); the heavy tlsn backend is behind the `tlsn-live` feature.

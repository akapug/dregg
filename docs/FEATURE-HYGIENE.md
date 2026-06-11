# Cargo Feature Hygiene — the census and the principle

**The principle.** A cargo feature flag answers exactly one question: *what platform am
I compiling for?* (wasm32, a zkVM guest, no_std/embedded, a future seL4 component, a
native-only prover or keychain). A feature flag must **never** answer *which guarantees
does this dregg have*. Optional core semantics is a footgun: it must not be possible to
compile a dregg that silently lacks a verification step, an enforcement path, or an
audit trail. Dev/test/bench gates are tolerated when they are loud, additive-only, and
fail-closed (they may ADD test helpers; they may never REMOVE a guarantee from the
default build).

Census date: 2026-06-11. Scope: every `[features]` table in the repo (workspace members
plus the out-of-workspace `chain/`; `site/dist/` build artifacts and the orphaned
`apps/*` manifests censused but not normative).

Classification key:
- **A — PLATFORM-TARGET**: legitimate; keep.
- **B — SEMANTIC-OPTIONALITY**: gates a guarantee; remove (make always-on) or flag.
- **C — DEAD**: gates nothing reachable / enabled nowhere; delete.
- **D — DEV/BENCH/TEST**: keep, noted.

## The census table

| Crate | Feature | What it gates | Class | Disposition |
|---|---|---|---|---|
| app-framework | `dev` | forwards `dregg-sdk/dev` | D | keep |
| app-framework | `lean-producer` | forwards `dregg-sdk/lean-producer` | B | **FLAGGED** (lean-archive constraint, see §Lean) |
| bridge | ~~`turn`~~ | the turn-proof `verifier` module (`DslAwareProofVerifier`, `StarkProofVerifier`) | B | **REMOVED** — always compiled in now |
| bridge | `test-utils` | test helpers in `present.rs` | D | keep |
| captp | `lean-gate` | verified Lean non-amplification verdict in `validate_handoff` / gc / pipeline; off ⇒ silent fallback to the Rust lattice | B | **FLAGGED** (§Lean) |
| cell | `crypto` (default) | dalek/chacha/bulletproofs stack; off only for the zkVM guest | A | keep (platform: SP1 guest) |
| cell | `zkvm` | SP1-guest code paths (`note.rs`, `peer_exchange.rs`) | A | keep |
| cell | `test-stubs` | predicate test stubs | D | keep |
| chain† | `mock` (**default**) | mock proving in `prove.rs`/`withdraw.rs`/`credential.rs` | B | **FLAGGED**: the *default* build of `chain` proves nothing. Recommend `default = []` (force the caller to pick `mock` xor `prove` explicitly) |
| chain† | `prove` | real SP1 proving (`sp1-sdk`, native-only, heavy) | A | keep (platform), but see `mock` flag |
| chain† | `on-chain` | `alloy` chain listener/verifier | A | keep (deployment target) |
| circuit | `plonky3` (default) | the native prover stack (p3-\*); off for wasm32 | A | keep |
| circuit | `recursion` (default) | recursion/IVC prover stack | A | keep |
| circuit | ~~`mock`~~ | **nothing** — zero `cfg` uses anywhere | C | **DELETED** (and the dangling `features = ["mock"]` requests in `wasm/`, `apps/compute-exchange`, `apps/bounty-board` removed) |
| circuit | ~~`dev`~~ | **nothing** — zero `cfg` uses | C | **DELETED** (sdk's forward `dev = ["dregg-circuit/dev"]` → `dev = []`) |
| coord | `lean-gate` | verified Lean gates in `shared_budget`/`causal`/`atomic`; off ⇒ silent Rust fallback | B | **FLAGGED** (§Lean) |
| dfa | `federation-verifier` | the `federation_verifier` module (`dep:dregg-federation`) | B | **FLAGGED — UNWIRED**: enabled by NO crate in the tree; the federation verifier compiles into no build. Decide: wire it on in `node`/`wire` consumers, or make unconditional (changes the wasm dep closure — needs a wasm32 check) |
| dregg-dsl-runtime | `plonky3` (default) | prover-coupled half of the runtime | A | keep |
| dregg-lean-ffi | `lean-lib` | linking `libdregg_lean.a` + the differential bins | A/B | keep as platform/native-link gate, but it is the root of the §Lean footgun |
| federation | `runtime` (default) | tokio + crossbeam transport (non-wasm32) | A | keep |
| federation | `lean-admission` | verified `dregg_strand_admit` in the F-4 admission gate; off ⇒ `admitted_rust` fallback | B | **FLAGGED** (§Lean) |
| hints | `parallel` (default) | rayon/ark parallel | A | keep (perf/platform) |
| hints | `asm` (default) | `ark-ff/asm` | A | keep |
| intent | `verified-settle` | per-leg Lean FFI cross-check in `settle_ring_verified`; off ⇒ Rust mirror only | B | **FLAGGED** (§Lean) |
| lightclient | `recursion` (default) | forwards `dregg-circuit/recursion` | A | keep |
| macaroon | `crypto` (default) | the crypto stack; off only for zkVM guest | A | keep |
| macaroon | `zkvm` | SP1-guest path | A | keep |
| persist | ~~`audit-bridge`~~ | `PersistentStore::persist_audit_events` (the in-memory→durable audit bridge) | B | **REMOVED** — `dregg-audit` is now an unconditional dep; an auditable dregg can no longer be silently compiled into an unauditable one |
| preflight | *(none declared)* | — but `checks/backends.rs` used `#[cfg(feature = "plonky3")]`, a feature preflight never declared ⇒ **always false** ⇒ `check_plonky3_backend` passed **vacuously** | C (dead cfg, live damage) | **FIXED** — the check is now unconditional and real |
| sdk | `federation-client` | reqwest client (non-wasm32) | A | keep |
| sdk | `network` (default) | tokio + quinn + dregg-wire (non-wasm32) | A | keep |
| sdk | `captp` (default) | dregg-captp surface (non-wasm32 today) | A | keep |
| sdk | `lean-producer` | `dregg-turn/lean-shadow` + lean-ffi | B | **FLAGGED** (§Lean) |
| sdk | `dev` | exports `verify_any_tier` (any-tier acceptance) under `any(test, dev)` | D | keep — loud, additive, absent by default (using it without the feature is a compile error, not a silent downgrade) |
| sdk | `unsafe-test-utils` | loud unsafe test helpers in cipherclerk | D | keep |
| secrets | `keychain` (default) | OS keyring backend | A | keep |
| storage | `kzg` | `poly_queue` module + o1-labs `poly-commitment` deps | C-ish | **FLAGGED — enabled by no crate in the tree**, so the KZG queue compiles nowhere. NOT deleted: the kimchi/`stark_in_pickles` heritage is recorded as load-bearing. Human decision: wire a consumer or retire the module |
| tests | `__legacy_tests`, `__wip_tests` | quarantined legacy/WIP test modules | D | keep (loudly named) |
| token | `biscuit` (default) | biscuit-auth token format | A | keep (zkVM guest excludes it) |
| token | `macaroon` (default) | macaroon token format | A | keep |
| token | `rand-deps` (default) | getrandom/rand/ed25519 (no getrandom in zkVM guest) | A | keep |
| token | `zkvm` | SP1-guest macaroon path | A | keep |
| turn | `lean-shadow` | the Lean shadow/gate executor path (`lean_shadow.rs`); off ⇒ Rust-only execution | B | **FLAGGED** (§Lean) |
| wire | ~~`stark-verifier`~~ | the real `StarkVerifier` impl; off ⇒ fail-closed reject-all stub | B | **REMOVED** — always compiled in. The optionality was illusory anyway: the unconditional `dregg-dsl-runtime` dep already pulled `dregg-circuit/plonky3` |
| wire | ~~`bridge`~~ | dregg-bridge/dregg-commit deps + `cross_node_auth` bin | B | **REMOVED** — unconditional |
| wire | ~~`dev`~~ | **nothing** — zero `cfg` uses, enabled nowhere | C | **DELETED** |

† `chain/` is not a member of the root workspace (its own manifest tree, with
`chain/program`); censused for completeness.

Also fixed under the same rule (undeclared-feature `cfg`s — always-false, i.e. dead
code wearing a feature's name):
- `bridge/src/present.rs`: `UnsafeLocalOnlyMarker::new_for_testing` was gated on
  `any(test, feature = "bench")` — bridge declares no `bench` feature. Re-gated on the
  declared `test-utils` (D-class) gate.
- `preflight/src/checks/backends.rs`: see table — the vacuous preflight gate.

## §Lean — the one big remaining footgun (flagged for ember)

Every Lean enforcement gate in Rust is feature-optional and **off by default**:
`captp/lean-gate`, `coord/lean-gate`, `federation/lean-admission`, `turn/lean-shadow`,
`intent/verified-settle`, `sdk`/`app-framework` `lean-producer` — all bottoming out in
`dregg-lean-ffi/lean-lib`, which links the checked-in `libdregg_lean.a`.

What keeps this from being a pure category-B removal today:
1. **It is a genuine native-link constraint.** The archive cannot link on wasm32, and a
   build box without the Lean toolchain/archive can `cargo check` but not link tests/bins.
2. `node/Cargo.toml` enables **all** of them, so the production node runs gated.

Why it is still a footgun: every *other* consumer (default `sdk`, `teasting`, `wire`'s
captp/coord deps, any new binary) silently compiles the `cfg(not(...))` fallbacks —
Rust-lattice handoff verdicts, `admitted_rust`, un-cross-checked settlement — with no
runtime evidence that the verified gate is absent. "Never break the live path" today
means "silently run the unverified path".

Recommended closure lane (needs a human/build-infra decision, hence flagged not done):
invert the polarity — make the Lean gates the **unconditional default** on native, and
introduce ONE platform-named gate (e.g. `platform-no-lean-link`, enabled only by the
wasm/zkvm builds) for the genuinely-can't-link targets, so absence of verification is
visible at the build graph instead of defaulted into. That touches link-time CI on every
machine that builds the workspace, so it is sequenced behind a decision, not snuck in.

## Notes / smaller flags

- `wire` ships `dregg-bridge` with `features = ["test-utils"]` in **production**
  dependencies (pre-existing; preserved verbatim during the feature removal). Worth a
  look: production wire should not need bridge's test helpers.
- `wire::NoopVerifier` (always-accept) is an unconditional pub type — not a cargo
  feature, but the same disease one layer up; out of this lane's scope.
- `dfa::router` re-exports `StubVerifier` unconditionally — same remark.
- `apps/compute-exchange`, `apps/bounty-board`, `apps/gallery`, `apps/privacy-voting`
  are orphaned manifests (they believe they are in the root workspace but are not
  members — `cargo metadata` errors; pre-existing, the apps/ → starbridge-apps/
  migration left them). Their dangling `dregg-circuit/mock` requests were cleaned
  anyway; retiring the directories is a separate decision.
- `tests/` gates `dregg-bridge` behind `__legacy_tests`/`__wip_tests` — correct shape
  for quarantine (loud, underscore-prefixed, off by default).

## Counts

- 46 features censused (24 crates with `[features]`, + `chain`).
- **A — platform/perf, kept: 22.**
- **B — semantic-optionality: 13 found → 4 REMOVED (always-on now): `wire/stark-verifier`,
  `wire/bridge`, `bridge/turn`, `persist/audit-bridge`; 9 FLAGGED** (7 Lean-family +
  `dfa/federation-verifier` unwired + `chain/mock`-as-default).
- **C — dead: 4 → 3 DELETED** (`circuit/mock`, `circuit/dev`, `wire/dev`), 1 flagged-kept
  (`storage/kzg`, heritage); **plus 2 always-false undeclared cfgs fixed** (preflight
  `plonky3` — a vacuously-green preflight gate made real; bridge `bench`).
- **D — dev/test, kept: 7.**

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
| app-framework | ~~`lean-producer`~~ → `no-lean-link` | forwards the platform gate | B→A | **INVERTED** (§Lean) — Lean unconditional on native |
| bridge | ~~`turn`~~ | the turn-proof `verifier` module (`DslAwareProofVerifier`, `StarkProofVerifier`) | B | **REMOVED** — always compiled in now |
| bridge | `test-utils` | test helpers in `present.rs` | D | keep |
| captp | ~~`lean-gate`~~ → `no-lean-link` | the verified non-amplification verdict in `validate_handoff` / gc / pipeline is now UNCONDITIONAL on native; the platform gate compiles the Rust-lattice fallback only on wasm32/zkvm | B→A | **INVERTED** (§Lean) |
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
| coord | ~~`lean-gate`~~ → `no-lean-link` | verified Lean gates in `shared_budget`/`causal`/`atomic` now UNCONDITIONAL on native | B→A | **INVERTED** (§Lean) |
| dfa | `federation-verifier` | the `federation_verifier` module (`dep:dregg-federation`) | B | **FLAGGED — UNWIRED**: enabled by NO crate in the tree; the federation verifier compiles into no build. Decide: wire it on in `node`/`wire` consumers, or make unconditional (changes the wasm dep closure — needs a wasm32 check) |
| dregg-dsl-runtime | `plonky3` (default) | prover-coupled half of the runtime | A | keep |
| dregg-lean-ffi | `no-lean-link` (new) + `lean-lib` | the link is UNCONDITIONAL on native (build.rs also hard-skips wasm32/zkvm targets); `no-lean-link` is the ONE platform opt-out; `lean-lib` now only arms the differential bins (+ proptest) | A | **INVERTED** (§Lean) |
| federation | `runtime` (default) | tokio + crossbeam transport (non-wasm32) | A | keep |
| federation | ~~`lean-admission`~~ → `no-lean-link` | verified `dregg_strand_admit` F-4 gate now UNCONDITIONAL on native | B→A | **INVERTED** (§Lean) |
| hints | `parallel` (default) | rayon/ark parallel | A | keep (perf/platform) |
| hints | `asm` (default) | `ark-ff/asm` | A | keep |
| intent | ~~`verified-settle`~~ → `no-lean-link` | per-leg Lean FFI cross-check in `settle_ring_verified` now UNCONDITIONAL on native | B→A | **INVERTED** (§Lean) |
| lightclient | `recursion` (default) | forwards `dregg-circuit/recursion` | A | keep |
| macaroon | `crypto` (default) | the crypto stack; off only for zkVM guest | A | keep |
| macaroon | `zkvm` | SP1-guest path | A | keep |
| persist | ~~`audit-bridge`~~ | `PersistentStore::persist_audit_events` (the in-memory→durable audit bridge) | B | **REMOVED** — `dregg-audit` is now an unconditional dep; an auditable dregg can no longer be silently compiled into an unauditable one |
| preflight | *(none declared)* | — but `checks/backends.rs` used `#[cfg(feature = "plonky3")]`, a feature preflight never declared ⇒ **always false** ⇒ `check_plonky3_backend` passed **vacuously** | C (dead cfg, live damage) | **FIXED** — the check is now unconditional and real |
| sdk | `federation-client` | reqwest client (non-wasm32) | A | keep |
| sdk | `network` (default) | tokio + quinn + dregg-wire (non-wasm32) | A | keep |
| sdk | `captp` (default) | dregg-captp surface (non-wasm32 today) | A | keep |
| sdk | ~~`lean-producer`~~ → `no-lean-link` | the verified Lean producer now UNCONDITIONAL on native (runtime-gated by `DREGG_LEAN_PRODUCER`) | B→A | **INVERTED** (§Lean) |
| sdk | `dev` | exports `verify_any_tier` (any-tier acceptance) under `any(test, dev)` | D | keep — loud, additive, absent by default (using it without the feature is a compile error, not a silent downgrade) |
| sdk | `unsafe-test-utils` | loud unsafe test helpers in cipherclerk | D | keep |
| secrets | `keychain` (default) | OS keyring backend | A | keep |
| storage | `kzg` | `poly_queue` module + o1-labs `poly-commitment` deps | C-ish | **FLAGGED — enabled by no crate in the tree**, so the KZG queue compiles nowhere. NOT deleted: the kimchi/`stark_in_pickles` heritage is recorded as load-bearing. Human decision: wire a consumer or retire the module |
| tests | `__legacy_tests`, `__wip_tests` | quarantined legacy/WIP test modules | D | keep (loudly named) |
| token | `biscuit` (default) | biscuit-auth token format | A | keep (zkVM guest excludes it) |
| token | `macaroon` (default) | macaroon token format | A | keep |
| token | `rand-deps` (default) | getrandom/rand/ed25519 (no getrandom in zkVM guest) | A | keep |
| token | `zkvm` | SP1-guest macaroon path | A | keep |
| turn | ~~`lean-shadow`~~ → `no-lean-link` | the Lean shadow/gate executor path (`lean_shadow.rs` + `lean_apply`) now UNCONDITIONAL on native | B→A | **INVERTED** (§Lean) |
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

## §Lean — CLOSED: the polarity inversion (2026-06-11)

The footgun this section used to flag is closed. The recommended inversion is DONE:

**The Lean gates are the unconditional default on native.** The seven former opt-in
features (`captp/lean-gate`, `coord/lean-gate`, `federation/lean-admission`,
`turn/lean-shadow`, `intent/verified-settle`, `sdk/lean-producer`,
`app-framework/lean-producer`) are deleted. Their Lean-using paths compile into every
native build; `dregg-lean-ffi` is a regular (non-optional) dependency of captp / coord /
federation / turn / intent / sdk, and its build.rs links `libdregg_lean.a`
unconditionally on native.

**ONE platform gate: `no-lean-link`** (workspace-consistent name, declared by each of the
seven crates + `dregg-lean-ffi`), OFF by default, set ONLY by builds whose target cannot
link the archive (wasm32 today; the SP1 zkvm guest doesn't consume these crates but the
gate covers it). It compiles the Rust fallback paths *in place of* the verified gates —
a statement about the target's linker, never about which guarantees a dregg has.
`dregg-wasm` enables it on its dregg-turn/coord/intent/sdk/captp/federation deps.
Defense-in-depth: `dregg-lean-ffi/build.rs` also hard-skips the archive refresh + all
link directives whenever `CARGO_CFG_TARGET_ARCH=wasm32` or `CARGO_CFG_TARGET_OS=zkvm`,
so a wasm/zkvm build that forgot the feature degrades to the marshal-only stubs instead
of attempting a native-archive link.

`node/Cargo.toml` no longer carries per-crate Lean enables (they are the default).
`dregg-lean-ffi/lean-lib` survives only to arm the differential binaries
(`required-features` + the optional `proptest` dep, which is what keeps the
now-unconditional lib dep wasm32-compilable).

Residual (known, accepted): every native consumer of these crates now links the Lean
runtime into its test/bin link step — a build box needs the checked-in archive + the
project Lean toolchain to LINK (cargo check is unaffected). That is the point: absence
of verification is visible at the build graph, not defaulted into.

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

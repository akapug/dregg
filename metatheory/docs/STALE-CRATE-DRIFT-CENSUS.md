# Stale-But-Live Core Crate Drift Census

A source-grounded census of five core Rust crates that the whole tree has
churned *past* — real dependents, but the crate itself untouched for weeks
while everything else moved. Each is classified by reading the SOURCE, not the
calendar: a stale crate is neither automatically rotten nor automatically fine.

Method: for each crate, enumerate the public surface (`lib.rs`), then grep every
real dependent's `src/` (and `tests/`) tree-wide for which public symbols have
genuine NON-TEST callers vs which are dead corners (zero non-self, non-test
callers tree-wide, or a path the live system moved away from). Crate dirs are
siblings of `metatheory/` under `/Users/ember/dev/breadstuffs/`.

READ-ONLY census. No code edits. No commit.

---

## Headline

Two of the five are genuinely **STABLE — leave them**; three have **drift** worth
a spirit-visit, but only one is a real liability:

| Crate | Last touched | Stakes (deps) | Verdict | Recommendation |
|---|---|---|---|---|
| **dregg-commit** | 2026-05-26 | 22 | **STABLE-DONE** (+3 internal-only re-exports) | CONFIRM-STABLE-AND-LEAVE |
| **dregg-trace** | 2026-06-15 | 9 | **STABLE-DONE** (+3 dead dep-lines) | CONFIRM-STABLE-AND-LEAVE |
| **dregg-hints** | 2026-05-26 | 9 | **STABLE-DONE** | CONFIRM-STABLE-AND-LEAVE |
| **dregg-dfa** | 2026-06-15 | 9 | **PARTIALLY-SUPERSEDED** (~705 dead lines + stale docs + dormant security gate) | CLEAN-DEAD-CORNERS + REFRESH-DOCS |
| **dregg-storage** | 2026-06-15 | 9 | **PARTIALLY-SUPERSEDED** (~3,700 orphan lines: DA + kzg + dataflow/sharding/metering) | CLEAN-DEAD-CORNERS (retire DA + kzg) |

**The single most worth doing: the dregg-storage cleanup** — ~3,700 lines of
built-and-tested-but-zero-caller code (the Reed-Solomon DA half + the
never-enabled kzg half + three fully-orphaned modules), the largest dead mass in
the cohort and the one whose orphaned trust-model prose (`lib.rs:33,60`) actively
*overclaims* a live availability capability.

**The most dangerous (lower line-count, higher risk): dregg-dfa's dormant
`federation-verifier`** — live governance route-table swaps run CAS-only today
because the cryptographic threshold gate (`federation_verifier.rs`) sits behind a
feature enabled by nobody. That's an internalize-the-guarantee gap, not just dead
weight.

**Refuted assumption (the reason this census was commissioned):** the perf-epoch
"incremental commitment ~130,000×" did NOT leave dregg-commit stale or
duplicated. That work lives entirely in `cell/src/commitment.rs` (the cap-root
cache, `.docs-history-noclaude/INCREMENTAL-COMMITMENT.md`) and is orthogonal to dregg-commit —
`cell/src` has ZERO `dregg_commit` references; the dep is `zkvm`-feature-gated and
only pulled by the sp1-guest build. dregg-commit is genuinely the live core that
~28 non-test files across 12 crates depend on.

---

## 1. dregg-commit (`commit/`) — STABLE-DONE — 22 deps — highest stakes

### What it IS

`commit/src/lib.rs:1-46` — the foundational commitment data structures for the
dregg token system: `Fact` (predicate + up to 3 terms over a 253-bit field),
`FactSet` (ordered fact set with Merkle commitment + membership/non-membership
proofs), the 4-ary Poseidon Merkle tree (`merkle.rs` + `poseidon2_tree.rs`),
`TokenState`/`StateCommitment`, `FoldDelta`/`FoldDeltaBuilder`/`verify_fold_chain`
(attenuation steps), `SymbolTable`, the `typed` field-encoding helpers, and the
`PolynomialAccumulator` (constant-size revocation accumulator).

### What the live system uses it for

It is **heavily, genuinely live** — ~28 non-test source files across audit,
bridge, demo, federation, intent, node, persist, preflight, sdk, token, turn,
verifier, wasm. The most-used symbols (by external import count):

| Symbol | external refs | Symbol | external refs |
|---|---|---|---|
| `FieldElement` | 15 | `Fact`/`CommitFact` | ~40 |
| `TokenState` | 13 | `MerkleProof` | 12 |
| `Poseidon2MerkleTree` | 10 | `MerkleTree` | 8 |
| `commitment_to_field` | 8 | `FactSet` | 7 |
| `SymbolTable` | 7 | `FoldDelta`/`Builder` | 5 each |
| `verify_fold_chain` | 5 | `NonMembershipProof` | 4 |
| `typed::canonical_32_to_felts_4` | 9 | `PolynomialAccumulator` | 2 (live) |

Module-level external usage: `merkle` (16), `typed` (10), `poseidon2_tree` (8),
`hash` (4), `accumulator` (2). The `PolynomialAccumulator` is the live
revocation accumulator used at `node/src/state.rs:16,295` (`NodeState.revocation_accumulator`,
"O(1) polynomial accumulator over all revoked token hashes") and documented at
`node/src/turn_proving.rs:53-60`. Not superseded — actively the revocation path.

### Is there a duplicate / superseded commitment path under the 22 deps? NO.

The worry was that `cell/src/commitment.rs` (2,125 lines, touched 2026-06-23,
the perf-epoch hot file) is a duplicate that bypassed dregg-commit. It is NOT:

- `cell/src/commitment.rs:1-50` is the **canonical Cell state-commitment**
  (BLAKE3 `dregg-cell-state-v9`, audit P0-2 unification of three disjoint
  schemes) — a fundamentally different artifact (cell identity/permissions/VK)
  from dregg-commit's fact-Merkle/Poseidon world.
- `cell/src` has **zero `dregg_commit` references** (grep confirms). The
  `dregg-commit` dep in `cell/Cargo.toml:47` is `optional` and gated behind the
  `zkvm` feature (`cell/Cargo.toml:19`), which is enabled only by the sp1-guest
  build (`circuit/sp1-guest/Cargo.toml:25`), never by any native dependent.
- The perf-epoch "incremental commitment" is the cap-root sub-root cache at
  `cell/src/commitment.rs:558-566` (`.docs-history-noclaude/INCREMENTAL-COMMITMENT.md`), with its
  own `cap_root_cache_matches_fresh` differential — orthogonal to dregg-commit.

So dregg-commit and cell-commitment are two orthogonal schemes; neither
supersedes the other. The 22 deps depend on the genuine core.

### Dead corners (small, internal-only re-exports)

Three `pub use` re-exports in `lib.rs` have zero external callers AND are used
only inside `commit/src` itself — they need not be public:

- `StateCommitment` (lib.rs `pub use state::StateCommitment`) — 0 external;
  used internally by `state.rs`, `typed.rs`.
- `hash_bytes_to_field` (lib.rs `pub use poseidon2_tree::hash_bytes_to_field`) —
  0 external; used internally by `poseidon2_tree.rs`.
- `SurvivalWitness` (lib.rs `pub use merkle::SurvivalWitness`) — 0 external;
  used internally by `merkle.rs`, `fold.rs`.
- `typed::absorb_4` — appears externally only in a doc-comment ("same shape as
  `dregg_commit::typed::absorb_4`"), no real caller.

These are visibility-tidy candidates, not drift. The crate is not stale.

### Verdict + recommendation

**STABLE-DONE.** **CONFIRM-STABLE-AND-LEAVE** (tiny optional tidy: demote 3-4
internal-only re-exports from `pub` if a visibility sweep ever happens). The
"22 deps untouched since May while the perf epoch shipped" framing is resolved:
the perf epoch never touched this crate because it operates on a different
commitment (cell state), and dregg-commit remains the live token-commitment core.

---

## 2. dregg-trace (`trace/`) — STABLE-DONE — 9 deps — the reference-evaluator worry

### What it IS

`trace/src/lib.rs:9-19` — the **Datalog authorization layer of the dregg1
token-ZK world** (NOT the metatheory Lean kernel). Its "reference evaluator"
(`eval.rs`, 528 lines) is a bottom-up forward-chaining Datalog evaluator over
policy rules that emits an `AuthorizationTrace` (a sequence of `DerivationStep`s
ending in `Allow{rule_id}` / `Deny`). Public surface: `types::*` (Term, Atom,
Check, Rule, Fact, DerivationStep, AuthorizationTrace, ...), `eval::Evaluator`,
`verify::{verify_trace, verify_trace_with_request}`, `policy::{standard_policy,
secure_policy, legacy_policy, ...}`, `check::eval_check`.

### What the live system uses it for (per-dependent)

| Dependent | Usage | Status |
|---|---|---|
| **token** | `Evaluator.evaluate(...)` as the "SOLE ground-truth verification semantics" (`token/src/datalog_verify.rs:2-15,200-210`) | Core consumer |
| **bridge** | `Evaluator`/`evaluate` (`authorize.rs:95,230,477`); `standard_policy`/`legacy_policy`; the live trace→STARK path `build_derivation_witness` (`present.rs:1466-1525`) | Core consumer |
| **sdk** | `Conclusion`, `AuthorizationTrace`, `Fact`, `Term`, `symbol_from_str` (`runtime.rs:1134`, `cipherclerk.rs`, `verify.rs:226`) | Live |
| **wasm** | `Evaluator`, `standard_policy`, `types::*` (`lib.rs:660,705`) | Live (touched 2026-06-24) |
| **circuit** | dep declared (`Cargo.toml:75`), **zero `src/` use** — consumed only transitively via bridge | Dead dep-line |
| **credentials** | dep declared (`Cargo.toml:21`), **no `src/` use** | Dead dep-line |
| **intent** | dep declared (`Cargo.toml:24`); the `.evaluate(` at `matcher.rs:529` is an unrelated `custom_evaluators` type | Dead dep-line |
| **demo-agent** | used only in `examples/`, not `src/` | examples |

### Is the reference evaluator faithful + genuinely exercised?

**Within its own world, yes** — `trace/src/tests.rs` has 88 tests / 91 evaluate
+ verify_trace call-sites, a real eval↔verify round-trip + tamper battery
(`test_verify_tampered_derived_fact:463`, `..._substitution:483`,
`..._conclusion_allow_to_deny:531`). Solid negative coverage.

**The eval↔circuit agreement differential does NOT exist** — but this is NOT the
byte-identity scar. The circuit re-models the same Datalog in
`circuit/src/dsl/derivation.rs` + `derivation_air.rs`, and bridge feeds the same
`AuthorizationTrace` into both `verify_trace` and `build_derivation_witness`
(`present.rs:1466`) — yet no test asserts "Evaluator output == circuit-derivation
accept". Faithfulness of the Datalog evaluator to the Datalog circuit is asserted
by review, not by a machine-checked differential.

Critically, the `feedback-byte-identity-differential-is-not-faithfulness` SCAR
and its cure (`circuit/tests/ir2_denotational_differential.rs`,
`Satisfied2`↔`Ir2Air::eval`) concern the **metatheory dregg2 IR-v2 kernel** and
contain **zero references to dregg_trace**. The two worlds are disjoint: the scar
does not apply to `trace/eval.rs`, which is a separate dregg1 artifact.

### Drift assessment

No API drift. `Check::Contains` is self-documented DEPRECATED (`types.rs:43-48`,
substring vuln) but intentionally retained for `legacy_policy`/demo-agent — a
governed deprecation, not accidental staleness. Last touch 2026-06-15 was a
fmt/clippy green-drive; live consumers (bridge `present.rs` 2026-06-22, wasm
2026-06-24) use it unchanged.

### Verdict + recommendation

**STABLE-DONE.** **CONFIRM-STABLE-AND-LEAVE** + optional CLEAN-DEAD-CORNERS
(~3 unused `dregg-trace` dep-lines in `credentials/Cargo.toml:21`,
`intent/Cargo.toml:24`, `circuit/Cargo.toml:75` — verify circuit needs no
transitive feature first). Do NOT invest in an eval↔circuit-derivation
differential unless the dregg1 token-ZK path is actively shipped — the
eval-agreement obligation lives in the metatheory IR-v2 work, which already has
its real differential.

---

## 3. dregg-hints (`hints/`) — STABLE-DONE — 9 deps — the "what is it" crate

### What it IS

`hints/README.md:1-5`, `hints/src/lib.rs` — an arkworks BLS12-381 implementation
of the **HInTS** weighted-threshold-signature scheme (eprint 2023/567). "Silent
setup" (no DKG); an aggregator combines BLS partials + per-party hints into a
constant-size aggregate QC carrying a Plonk/KZG SNARK proof that the weighted
threshold was met. Lib name is `hints` (not `dregg_hints`); vendors the upstream
reference SNARK engine under `hints/src/snark/`, heavily modified. ~1,407 LOC.
Public surface: `setup_eth`, `generate_keypair`, `generate_hint`, `setup_universe`,
`sign`/`verify_partial`, `sign_aggregate`/`verify_aggregate`, re-exported curve
types + `Aggregator`/`Verifier`/`Signature`/`HintsError`.

### Is it live or orphaned? LIVE — and it is the federation/turn threshold scheme.

| Dependent | Usage | Status |
|---|---|---|
| **federation** | `federation/src/threshold.rs` IS the wrapper: `setup_eth`/`setup_universe`/`generate_hint` in `FederationCommittee` ctors (`:182-240`), `sign_aggregate` (`:275`), `verify_aggregate` (`:289`). Also beacon.rs, dkg.rs, dkg_ceremony.rs, bls_quorum_diff.rs | LIVE — the wrapper |
| **turn** | `turn/src/executor/membership_verifier.rs` — the live enforcement seam: deserializes a `hints::Signature` QC, pins the threshold floor against k-of-n downgrade (`:1367-1391`), then `hints::verify_aggregate(...)` is the authoritative gate (`:1394`). Wired into the real executor via `registry_with_real_verifiers()` (`executor/mod.rs:793,852,893`). Feature `threshold-sig`. | LIVE — load-bearing |
| **sdk** | `council_seal.rs:302-306`, `hints_onboarding.rs:50,346,406,631` | LIVE |
| **governed-namespace** | dev-dep (`Cargo.toml:58`); `hints::` mentions in `src/lib.rs:1555,1560` are comments; real use is `tests/commit_threshold_sig.rs` (both-polarity proof) | test-only indirect |
| **discord-bot, dregg-doc, sel4/dregg-firmament** | NOT declared deps — only `ark-serialize`/`serde_with` transitive-build comments | not a dep |

The federation does NOT bypass hints with a separate scheme — `threshold.rs` IS
the federation's constant-size QC scheme, built on hints, and `turn` enforces it
at a real authorization seam with both-polarity test coverage.

### Drift assessment

Vendored upstream reference impl + ember's modifications (subgroup checks in
`verify_partial` lib.rs:99-115; `setup_eth` ceremony cap; threshold-downgrade
`Signature.threshold` field). Frozen-by-nature crypto. Consumers were touched a
month LATER (turn `membership_verifier` 2026-06-23) against a stable API; import
surface matches `lib.rs` exports exactly. No API drift, no broken imports.

### Verdict + recommendation

**STABLE-DONE.** **CONFIRM-STABLE-AND-LEAVE.** Small, vendored-frozen,
load-bearing-live. The prompt's dependent list conflated three real direct
callers (federation/turn/sdk) with one dev-only indirect (governed-namespace) and
three non-deps (discord-bot/dregg-doc/firmament, transitive comments only).

---

## 4. dregg-dfa (`dfa/`) — PARTIALLY-SUPERSEDED — 9 deps — live core, dead AIR/filter periphery

### What it IS

`dfa/src/lib.rs:3-6` — the canonical DFA route-table engine: compile
`Pattern → NFA → DFA` (`compiler.rs`), assemble tagged-union route tables with
BLAKE3 commitments (`router.rs` `RouteTableBuilder`/`RouteTable`), classify input
via linear DFA walk (`Router`/`GovernedRouter`), gate table swaps on CAS +
threshold proof (`update_routes`). Deliberately subsumes three legacy routers.

### Live core (genuinely used, NON-TEST)

| Dependent | Usage | Status |
|---|---|---|
| **directory** | `dfa_routed.rs:30-31,64,143,172-177` — `DfaRoutedDirectory` holds a live `Router`, `.classify()` → `RouteTarget` | LIVE |
| **intent** | `gossip_filter.rs:50-51,85,108,152` — `GossipTopicFilter` wraps `Arc<GovernedRouter>`, `.classify_path()` for topic admission, `KindRegistry` | LIVE |
| **governed-namespace** | `lib.rs:171,595,636,1008` — `build_route_table`, `build_governed_router`, `dispatch()` | LIVE |
| **discord-bot** | `dashboard.rs:1401-1477`, `governance.rs:515-594` — `parse_route_table`/`parse_route_target` | LIVE |
| **wasm** | `bindings.rs:856-868` — `route_table_commitment` (RouteTableBuilder + commitment) | LIVE |
| **wire** | `dfa_router.rs:27-32` — blanket pass-through re-export (adapter shim, not a consumer) | shim |
| **teasting** | `router_sim.rs`, `tests/dfa_routing.rs` — test-only | test |

The route-table core (`compiler.rs` routing + `router.rs`) is STABLE and live
across 5 real dependents. `cell/` does NOT depend on dregg-dfa — cell's
effect-dispatch is an orthogonal axis (slot-caveat predicates / effect execution),
so there is no "cell routing bypassed dfa". The two are different layers.

### Dead corners (~705 lines)

- **`air.rs` (390 lines) — ORPHAN SCAFFOLD with a stale, load-bearing false doc.**
  `air.rs:88` and `air.rs:211-219` claim its `compile_to_air`/`verify_acceptance`
  is invoked by `cell::program::WitnessedPredicateKind::Dfa` through a fixed
  dispatch table. **False against HEAD:** `cell/src/predicate.rs:1448-1520` shows
  the `Dfa` predicate kind is served by `NotYetWiredVerifier::dfa()`, whose
  declared upstream is `dregg_circuit::dsl::circuit` (`predicate.rs:1462`), NOT
  dregg-dfa, and which rejects all proofs. The entire air API (`compile_to_air`,
  `verify_acceptance`, `AirTrace`, `DfaError`, ...) has zero real callers
  tree-wide; the only external mention is wire's blanket `pub use dregg_dfa::air`,
  which nothing downstream consumes.
- **`filter.rs` (230 lines) — `TopicFilter`/`FilterTree`/`accept_all_dfa`** —
  zero real consumers; intent's gossip filter uses `GovernedRouter`, not
  `TopicFilter`. Only wire's pass-through re-export references it.
- **`federation_verifier.rs` (85 lines) — dormant security gate.** The
  `federation-verifier` feature is defined only at `dfa/Cargo.toml:13` and enabled
  by NO ONE (grep across all Cargo.toml = single definition hit). The production
  `FederationQcVerifier` never compiles; all live `GovernedRouter` paths use
  `StubVerifier` (CAS-only). **Live governance route-table swaps are CAS-only,
  with no cryptographic threshold gate.**

### Verdict + recommendation

**PARTIALLY-SUPERSEDED.** ~705 of ~2,540 source lines are dead periphery.
**CLEAN-DEAD-CORNERS + REFRESH-DOCS**, one focused pass:
1. **REFRESH (cheap, do first):** fix `air.rs:88` + `:211-219` — they assert a
   `cell/` wiring that doesn't exist (real upstream is `dregg_circuit::dsl::circuit`
   per `NotYetWiredVerifier::dfa`). Either retire air.rs or mark it honestly as
   "trace-shape reference, not wired."
2. **CLEAN:** retire `filter.rs` (no consumer) and `air.rs` (orphan), OR wire them
   in if intended.
3. **DECIDE the security gate:** either enable `federation-verifier` on the real
   governed-namespace/intent deployment (replacing CAS-only `StubVerifier` — an
   internalize-the-guarantee gap) or retire `federation_verifier.rs`. Most
   consequential item.
4. **LEAVE** the route-table core — confirmed stable.

---

## 5. dregg-storage (`storage/`) — PARTIALLY-SUPERSEDED — 9 deps — live spine, large orphan DA half

### What it IS

`storage/src/lib.rs` — the resource-accountable, quota-bounded storage substrate:
content-addressed blobs (BLAKE3), Merkle queues, quota/space accounting,
relay/operator state machines, and a Reed-Solomon **data-availability (DA)** layer.
~13,850 LOC across 23 files. In the root `Cargo.toml` `exclude` list, builds
standalone. `lib.rs:3-25` documents a migration (`STORAGE-AS-CELL-PROGRAMS.md`)
deprecating the operator-side modules in favor of cell-program templates in
`dregg-storage-templates`.

### Per-module live/dead table (external NON-TEST callers)

| Module | LoC | Non-test callers | Status |
|---|---|---|---|
| `queue` | — | 4 (node, sdk-net, preflight) | **LIVE (core)** |
| `operator` | — | 3 (node) | LIVE |
| `relay` | — | 3 (node, preflight) | LIVE (deprecated path) |
| `inbox` | — | 2 (node, preflight) | LIVE (deprecated path) |
| `programmable` | — | 2 (app-framework, preflight) | LIVE (deprecated path) |
| `quota` | — | 2 (node, preflight) | LIVE |
| `content` | 188 | 1 (node) | LIVE |
| `blinded` | 1016 | 1 (app-framework) | LIVE (deprecated path) |
| `pubsub` | — | 1 (preflight) | LIVE (deprecated path) |
| `dedup` | — | 1 (preflight) | LIVE |
| `commitment` | 899 | 0 (internal via blinded) | dead externally |
| `multi_asset` | 404 | 0 (teasting tests only) | TEST-ONLY |
| `namespace_mount` | 466 | 0 (teasting tests only) | TEST-ONLY |
| `atomic` | 463 | 0 (teasting tests only) | TEST-ONLY |
| **`availability`** | **370** | **0 (zero anywhere)** | **ORPHAN (DA)** |
| **`erasure`** | **679** | **0 (zero anywhere)** | **ORPHAN (DA)** |
| **`poly_queue`** | **1456** | **0 (kzg-gated, never enabled)** | **ORPHAN** |
| **`dataflow`** | **673** | **0** | **ORPHAN** |
| **`sharding`** | **347** | **0** | **ORPHAN** |
| **`metering`** | **169** | **0 (folds into templates)** | **ORPHAN** |
| `wal` | 536 | 0 (internal via queue only) | internal-only |

Dependent → modules: **node** → queue/operator/relay/inbox/content/quota (the live
core, `storage_service.rs:60-62`, `relay_service.rs:35-38`); **preflight** →
queue/inbox/programmable/pubsub/dedup/quota/relay; **app-framework** →
programmable/blinded/inbox; **dregg-sdk-net** → queue only; **teasting** →
integration tests; **dregg-storage-templates** → doc-comments only (it is the
*replacement*, not a caller); **discord-bot** → transitive via app-framework,
zero direct refs.

### Confirmed findings

- **CONFIRMED: `erasure.rs` + `availability.rs` orphaned.** Zero non-self,
  non-test callers tree-wide. A closed dead loop: `erasure` → `availability` →
  nobody. Built (and per the prior orphan census, tested) but disconnected.
- **CONFIRMED: the `kzg` feature is dead.** Defined only at `storage/Cargo.toml:9`,
  enabled by no dependent. Its sole `#[cfg(feature="kzg")]` module is `poly_queue`
  (1,456 LOC), dead-in-practice; it drags in arkworks + a git-pinned
  `poly-commitment`. (`commitment.rs` is NOT kzg-gated — Poseidon2/BLAKE3 — but
  has zero external callers; reached only internally by `blinded.rs`.)
- **Additional orphans beyond the known pair:** `dataflow` (673), `sharding`
  (347), `metering` (169) — all zero callers anywhere. `metering` is documented as
  folding into templates (`dregg-storage-templates/src/relay_operator.rs:49`).

### Verdict + recommendation

**PARTIALLY-SUPERSEDED**, sharp boundary:
- **Live core** (production): `queue`, `content`, `quota`, `dedup` + top-level
  `ContentHash`/`QuotaId`.
- **Live-but-deprecated** (still wired, marked for retirement into templates per
  `lib.rs:1-25`): `inbox`, `pubsub`, `blinded`, `programmable`, `operator`,
  `relay` — let these follow the `dregg-storage-templates` migration sweep, not an
  ad-hoc delete.
- **Orphaned** (zero callers): the DA half + kzg half + dataflow/sharding/metering.

**CLEAN-DEAD-CORNERS** — removable without touching any live or test caller:
- **DA half:** `erasure.rs` (679) + `availability.rs` (370) = ~1,049 LOC.
- **kzg-dead:** `poly_queue.rs` (1,456) + the `kzg` feature block + the
  arkworks/poly-commitment optional deps (`Cargo.toml:35-46`).
- **Other fully-orphaned:** `dataflow.rs` (673) + `sharding.rs` (347) +
  `metering.rs` (169) = ~1,189 LOC.

Total cleanly removable: **~3,700 LOC** (rising to ~5,500 if `commitment.rs` +
`wal.rs` are collapsed, which needs internal callsite surgery in
`blinded.rs`/`queue.rs` first — not free deletes). DON'T FINISH the DA layer
unless DAS-at-consensus (`lib.rs:48-51`) is on the actual roadmap.

---

## Ranking (stakes × drift-likelihood) and the highest-leverage spirit-visit

1. **dregg-storage — VISIT (highest leverage).** Largest dead mass (~3,700
   confirmed-orphan lines), and the orphaned trust-model prose at `lib.rs:33,60`
   ("erasure sampling" / "light clients verify availability without full
   download") actively overclaims a capability nothing invokes — a
   rise-to-meet-the-claim liability, not just dead weight. Retire the DA + kzg
   halves; let the deprecated operator modules follow the templates migration.
2. **dregg-dfa — VISIT (highest-risk-per-line).** Smaller dead mass (~705 lines)
   but two sharp issues: a load-bearing FALSE doc (`air.rs:88,211-219` claims a
   cell-wiring that HEAD refutes) and a dormant security gate (governance swaps
   are CAS-only because `federation-verifier` is enabled nowhere). The doc-refresh
   is cheap; the verifier decision is consequential.
3. **dregg-commit — LEAVE.** Genuinely the live 22-dep core; not duplicated by
   cell-commitment; only 3-4 internal-only re-exports are tidy-able.
4. **dregg-trace — LEAVE.** Stable dregg1 Datalog auth layer, faithful within its
   world, strong test battery; the eval-agreement scar belongs to the metatheory
   IR-v2 work, not here. ~3 dead dep-lines tidy-able.
5. **dregg-hints — LEAVE.** Vendored-frozen, load-bearing-live threshold scheme
   under federation + turn, both-polarity-tested. No drift.

---

## MEMORY / DOC corrections

- **Refute the commissioning premise (worth a MEMORY note):** the perf-epoch
  "incremental commitment ~130,000×" did NOT leave dregg-commit stale or
  duplicated. That work is `cell/src/commitment.rs` (cap-root cache,
  `.docs-history-noclaude/INCREMENTAL-COMMITMENT.md`), orthogonal to dregg-commit; `cell/src` has
  zero `dregg_commit` refs (dep is `zkvm`-gated, sp1-guest-only). dregg-commit is
  the live token-commitment core for 12 crates / ~28 non-test files.
- **`dfa/air.rs:88` & `:211-219` are STALE/FALSE** — they claim
  `cell::program::WitnessedPredicateKind::Dfa` calls `verify_acceptance`; HEAD
  shows it is served by `NotYetWiredVerifier` pointing at
  `dregg_circuit::dsl::circuit`, and the air API has zero real callers.
  `intent/src/predicate.rs:19,68,85` similarly references a dfa::air design intent
  doesn't implement.
- **`storage/src/lib.rs:33,60` trust-model prose is aspirational** — "erasure
  sampling" / "light clients verify availability" describe the orphaned
  `erasure`/`availability` modules nothing calls. Any outward doc inheriting this
  overstates a live capability.
- **The byte-identity-differential SCAR does NOT apply to `trace/eval.rs`** — that
  scar + its cure (`ir2_denotational_differential.rs`) concern the metatheory
  dregg2 IR-v2 kernel and contain zero `dregg_trace` references. dregg-trace's
  evaluator is a separate dregg1 artifact, exercised by an 88-test eval↔verify
  battery; its evaluator↔circuit faithfulness was never claimed to be
  machine-checked. Do not conflate the two worlds.
- **The MEMORY threshold/federation lines are accurate for hints** — for the
  record (not currently indexed): hints is the live constant-size-QC primitive
  under federation's `FederationCommittee`/`ThresholdQC` and turn's
  `ThresholdSigVerifier` (`Authorization::Custom`/`GOVERNANCE_VK` seam), wired into
  the real executor via `registry_with_real_verifiers()` — a live, enforced,
  both-polarity-tested path, not a sketch.

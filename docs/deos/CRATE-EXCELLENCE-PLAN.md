# Crate Excellence — the honest picture, the cross-cutting patterns, the standard, the plan

**Method:** careful-reading assessments (not grep, not `cargo metadata`, not a green check). Each reader
opened the accept path, ran probes where a claim was checkable, and recorded what the code does versus what
the code says it does.

**Scope of the evidence backing this report.** Six crates are read to completion or near it: `dregg-circuit`,
`dregg-circuit-prove`, `dregg-turn`, `dregg-cell`, `dregg-node`, `dregg-sdk` (partial — strengths only).
Together they are the core-protocol + verification spine and ~250k lines. Every finding below is anchored to a
file:line a reader actually opened. The patterns generalize *by construction* — they are the shape of how this
tree is written — but the per-crate table names only what is read. Nothing here is extrapolated to an unread
crate.

**Status at HEAD (re-verified 2026-07-16).** The plan below is largely EXECUTED: MOVEs 1–4 are landed —
the three live defects are closed, the crown-jewel forge test derives its collisions at test time, the
`#[ignore]`d teeth run on a nightly armed-teeth lane, the named vacuous gates bite, and the front doors
are rewritten. MOVE 5 (typed boundaries + the adapter trait) and most P6 burndowns are the open work;
`#![deny(rustdoc::broken_intra_doc_links)]` is a named lane with a measured cost (`circuit/src/lib.rs:215`).
Per-finding statuses are marked inline below.

---

## 1. The honest picture

| grade | count | crates |
|---|---|---|
| excellent | **0** | — |
| good | **6** | circuit, circuit-prove, turn, cell, node, sdk |
| adequate | 0 | — |
| poor | 0 | — |

**Zero crates are excellent. The spine of the system grades `good`.** That is the finding, and softening it
would waste the reading.

`good` here is not a participation trophy — it means something specific and it means the same thing six times:

- The **architecture is right.** "Rust authors no constraints; Lean authors, Rust interprets" is a genuinely
  correct central abstraction, and `verify_vm_descriptor2` really does rebuild the AIRs from the descriptor
  alone. The prove/verify crate split is real and enforced (`cargo tree -p dregg-circuit` is recursion-free).
  The injected-verifier seams in `cell` really do fail closed. `TurnChainError` and `turn/src/error.rs` are
  error design other projects should steal.
- The **honesty apparatus is unusually strong** — strong enough that most of this report is written *out of the
  crates' own self-reports.* `effect_vm_descriptors.rs:20-27` pre-empts its own FP-tautology hole in its own
  words. `fri_params_soundness_budget.rs` states that the capacity conjecture is **refuted** and that its own
  gate is an engineering margin, not a proof. `producer_descriptor_coverage_gate.rs` tallies its own
  **44 Uncovered** rows and fails the build on an unclassified one. `lib.rs` in `cell` and `turn` open by
  declaring themselves LEGACY and not the source of truth. This is the iterative/approximative method working.
- And the **gap between the two is where excellence is lost.** When read: the ledgers named real holes nobody
  was burning down, the teeth were written but never armed, the deep modules were scrupulous while the front
  doors were stale. The arming and the front doors are fixed at HEAD (MOVEs 2 and 4); the undrained ledgers
  (P6) are where the gap still lives. The apparatus that finds the gap remains better than the discipline that
  closes it — that is the standing thing to manage.

Three findings were live defects when read — stated first because grade-averaging hides them. **All three are
CLOSED at HEAD**, each by the exact MOVE-1 mechanism prescribed below:

1. **`cell`'s `Not(Not(c))` panic — CLOSED.** The reading proved a wire-reachable panic in `lift_simple` with
   three probes (direct eval; a postcard payload that decodes clean and then panics; the public safe builder
   `implies()` constructing the shape with no adversary — a node-crash DoS on a crate with 30+ dependents). At
   HEAD `lift_simple`'s `Not` arm is fail-closed (`Err(ProgramError::NegationNotLiftable)`,
   `cell/src/program/eval.rs:2554-2562`); the smart constructor `SimpleStateConstraint::not` — the only path
   `implies()` uses — collapses `not(Not(c)) → c` at construction; and the `types.rs` doc states that
   `Not(Not(c))` **is** representable and how it is collapsed. The false paragraph that caused the bug is gone.
2. **`turn`'s fail-open chain verify — CLOSED.** `verify_receipt_chain_with_keys` verified signatures only on
   receipts that carried them — strip the signature and the chain still verified. At HEAD
   `verify_receipt_chain_strict` requires an executor signature on **every** receipt (`turn/src/verify.rs:285`),
   the lenient variant carries its leniency in its name (`verify_receipt_chain_with_optional_keys`, `:316`), and
   the adversarial pair is a test: strip a signature from a valid chain → strict rejects, lenient (documented
   lenient) accepts (`verify.rs:726-781`).
3. **`cell`'s `test-stubs` leak — CLOSED.** The workspace build graph armed `StubVerifier`'s accept path in a
   root release build (a normal `[dependencies]` feature entry + `default-members`). At HEAD `tests/Cargo.toml`
   carries `dregg-cell` featureless in `[dependencies]` (`:35`) and `test-stubs` only in `[dev-dependencies]`
   (`:70`); a `compile_error!` fires if `test-stubs` is enabled in a `debug_assertions`-off build
   (`cell/src/predicate.rs:1343-1353`); a cargo-tree firewall test pins the graph
   (`tests/tests/test_stubs_firewall.rs`); and the stub accept path itself compiles only under
   `cfg(test)`/`test-stubs`.

And the crown jewel bites again: **`cell/tests/offchain_root_forge_closed.rs` derives its colliding pairs by
bounded search at test time** (`find_lane0_collision`, `:89`) — no generator to remember to run, no pinned
constant to go stale — so a change to `compute_heap_root` / `compute_fields_root` can never again silently
disarm the forge regression the way the stale pins once did.

---

## 2. ⚑ THE CROSS-CUTTING PATTERNS

This is the product. These are not six crates' six problems; they are one body's habits, showing up six times.

### ⚑ P1 — The tooth that cannot bite (the dominant pattern)

We write negative tests prolifically and adversarially-*named*. A large fraction of those read could not fail
for the reason they claimed. The mechanisms, each with its status at HEAD:

**(a) Structural presence standing in for behaviour.** The test asserts a gate-*shaped* subtree is in the
constraint list, not that the interpreter enforces it.
`cap_delegation_nonamp_descriptor.rs::genuine_nonamp_carries_anti_amplify_teeth` pattern-matches the descriptor
AST for `Mul(Var(granted), Add(Const(1), Mul(Const(-1), Var(held))))` on each of 8 mask bits. No amplifying
witness is ever constructed; no prover is ever asked to refuse one. **Closed at HEAD for this instance:** the
behavioural tooth exists — `nonamp_submask_gate_refuses_an_amplifying_witness`
(`cap_delegation_nonamp_descriptor.rs:301`) forges each mask bit independently and requires the running prover
to refuse — and the module doc states plainly that nothing routes cap-graph rows to this descriptor (`:81`).
The pattern (AST presence standing in for behaviour) remains the thing to watch for in review.

**(b) The undiscriminating reject.** `match catch_unwind(..) { Err(_) => {}, Ok(Err(_)) => {}, Ok(Ok(_)) =>
panic!("...is OPEN") }` — **any** panic or **any** error counts as a correct refusal. The reading counted 197
such sites across `circuit` and `circuit-prove`. A tooth that cannot distinguish *"rejected the forgery"* from
*"crashed"* is measuring the wrong thing: a stray `.unwrap()` in trace assembly keeps every one green while
proving nothing about the constraint system. **Mostly closed at HEAD:** the helper landed —
`circuit/src/refusal.rs::must_refuse` / `must_refuse_or_unsat_panic` distinguish panic from `Err` (and assert
the p3 unsat-panic message where that is genuinely the mechanism) and are in use ~63 times in each crate;
~29 raw `catch_unwind` sites and ~13 bare `Err(_) => {}` shapes remain. The reason-*matching* half
(`assert!(matches!(e, LeafError::BindingUnsat{..}))`) still waits on MOVE 5's typed errors.

**(c) The fallback IS the expected answer.** The reading's canonical case: `coord_gate`'s
`lean_gate_decides_unanimous_scenarios` asserted the same value the function's `Err` branch returns
(`rust_decision`, the value passed in) — passing identically whether `verified_2pc_decide` works, is broken,
returns garbage, or is absent. Its sibling `falls_back_to_rust_when_no_wire` asserted `f(x, None) == x` against
a body whose second statement is `let Some(wire) = wire else { return rust_decision; }` — literal P → P.
**Closed at HEAD:** both are deleted; `lean_verdict_overrides_a_wrong_rust_decision`
(`node/src/coord_gate.rs:179`) hands the gate a deliberately WRONG `rust_decision` and requires the Lean
verdict to win — every expected value is one the fallback path cannot produce, so a fallback build, a stuck
export, or a deleted `verified_2pc_decide` all turn it red.

**(d) The tooth that is written, adversarial, correct — and never runs.** When read, all 8
`*_binding_deployed_tooth.rs` files in `circuit-prove` were `#[ignore]`-gated with nothing in CI passing
`--ignored`, every load-bearing verified-gate test in `node` self-skipped on an archive-less build with no
scheduled hard mode, and `consensus_under_failure.rs` pinned `DREGG_LEAN_PRODUCER=0` — the production default
was the one thing a real cross-node kill never exercised. **Closed at HEAD:** the nightly armed-teeth lane
(`.github/workflows/armed-teeth.yml`, cron 05:00) runs all 8 deployed-tooth binaries with `--ignored` plus a
`DREGG_TEST_REQUIRE_LEAN=1` hard-mode lane that turns every `eprintln!("SKIP"); return` into a panic; and
`consensus_under_failure.rs` fault-injects the production default (the var stays unset; the legacy-Rust
comparison lane must be asked for via `DREGG_TEST_LEAN_PRODUCER=0`). The `#[ignore]` attributes stay — a plain
CI run skips the expensive teeth *explicitly*, and the schedule is where they bite.

> **"Expensive" must mean "runs nightly", not "runs never."** These teeth are minutes-long real recursion
> folds; the armed-teeth schedule is that posture, enforced.

**(e) The identity gate.** `node/src/blocklace_sync.rs:1000` calls
`admitted_participants(&raw_participants, &raw_participants)` — seeds == candidates, and `AdmissionRegistry`
admits every seed by construction. The F-4 strand-admission filter **provably cannot drop anything.**
`vouch_threshold=1` and `min_bond=1` are inert (the module doc concedes "no vouches/bonds fed"). The divergence
warning at `:1004-1011` is unreachable dead code. Its test (`strand_admission_gate.rs:127`) passes
`candidates ⊋ participants` — a configuration the live call site never produces. It tests a code path that does
not exist in production, and it is labelled "the live F-4 closure."

**Why P1 is the top pattern:** each mechanism produces a green suite, a confident doc-comment, and zero
assurance. And they compound — (b) exists partly *because* (P3) the error surface is stringly-typed, so a test
literally **cannot** assert *why* a reject fired.

### ⚑ P2 — The name that outlives its referent (front-door inversion)

**The deepest modules are the most honest and the most-read text is the least accurate.** This was an
inversion, and it was systematic. Every named instance is corrected at HEAD (the MOVE-4 sweep); the list stays
on the record because the pattern is the crate-review lesson, and because the *structural* fix — the lint that
makes the class impossible — is still a named open lane:

- `circuit/src/lib.rs` — the Trust Model claimed "negligible soundness error (2^{-128} for STARK)" while the
  crate's own gate calls capacity refuted. **Corrected:** the front door now carries the per-column
  refuted-conjecture ledger (per-fold / Johnson QUERY / commit-phase `ε_C` / eq. (20) composite / capacity as a
  drift-only baseline, `lib.rs:95-130`), states "There is no `mock` feature" (`:173`), and the dead `[stark]`
  links are gone.
- `circuit-prove/src/custom_proof_bind.rs` — a 51-line module doc described the deleted `verify_proof_bind` as
  the live engine, propagated to 5 citing sites. **Corrected:** the module doc states the recursion-fold truth
  (the binding is enforced in-circuit by `prove_custom_binding_node_segmented` wired into
  `prove_chain_core_rotated`; nothing verifies a proof-bind off-AIR), and the citing sites now describe the
  deletion accurately.
- `cell/src/program/types.rs` — the canonical case, because **the false doc caused the bug**: it argued
  `Not(Not(c))` was unrepresentable for a reason that is exactly what makes it representable; the belief
  suppressed the test and the panic shipped. **Corrected:** the doc states `Not(Not(c))` IS representable and
  is *collapsed* — by the smart constructor at build time and by the evaluator definitionally.
- `turn/src/executor/mod.rs` claimed `require_validity_proof` "rejects EVERY encrypted turn" — falsified by the
  crate's own passing test — and `verify.rs` misdescribed what v3 signs. **Corrected:** both state what the code
  does.
- `cap_delegation_nonamp_descriptor.rs` claimed "the sdk authority-binding routes cap-graph rows to it by
  name" — false. **Corrected:** the module doc states plainly that nothing routes cap-graph rows to this
  descriptor (`:81`). The orphan-resolution itself (wire the genuine descriptor or delete both) is still an
  open burndown (§4).
- `cell/src/predicate.rs` claimed a "length-prefix shape" check the stubs never performed. **Corrected:** the
  rustdoc says exactly what a stub checks (emptiness, nothing else) and that the accept path compiles only
  under `cfg(test)`/`test-stubs`.
- Names that lied by themselves: `turn`'s `verify_stark()` verified no STARK. **Corrected:** it is
  `EncryptedTurn::verify_admission_binding` (`turn/src/encrypted.rs:449`), its module doc states what is
  actually enforced, and the previously-unnamed residual is now a NAMED seam: `conflict_set` is
  submitter-declared and unverified (`encrypted.rs:7`). The dead `ProofBindError` enum is deleted.

**The signature of P2:** the code was fixed, refactored, or superseded, and the *name* stayed. Nothing yet
*enforces* that a deleted item cannot be documented as live — `#![deny(rustdoc::broken_intra_doc_links)]` is
the structural fix and is a named open lane with a measured cost (`circuit/src/lib.rs:215`: 311 hits, most of
them bracket-notation escapes, a handful genuine rot the lint caught that hand-sweeping missed).

### ⚑ P3 — Stringly-typed boundaries, and fail-open at the seams

**The numbers:** `circuit` — **181** `Result<_, String>` vs **9** typed error enums, and all 9 live in
peripheral modules (xmss, block_conservation, …) while `verify_vm_descriptor2` / `parse_vm_descriptor2` /
`prove_vm_descriptor2` all return `Result<(), String>`. `circuit-prove` — **140** vs 74, the entire leaf-adapter
layer and all of `gpu_backend`. `node/src/api.rs` — bare axum `StatusCode` across ~100 endpoints;
`.map_err(|_| StatusCode::BAD_REQUEST)` discards the cause entirely, so the client gets an empty 400 *and the
node loses the error for its own logs.*

**The cost is not aesthetic, it is threefold:**

1. **A consumer cannot separate a deploy bug from an adversary.** `lightclient/` gets an opaque `String` for both
   "the descriptor is malformed" (page someone) and "the proof is invalid" (quietly reject). These are opposite
   operational responses.
2. **The good error design is swallowed from below.** `TurnChainError` is excellent — 10 fail-closed variants,
   each naming the adversary it stops (`ChainBreak{index, expected_old_root, found_old_root}`,
   `MissingWideAnchor{index}`, `VkFingerprintMismatch`). Then it re-swallows the layer beneath into
   `RecursionFailed{reason: String}`. So the security-relevant distinction — **`BindingUnsat` (the connect
   conflicted: a forged claim, the tooth firing)** vs **`ProverFailed` (FRI/OOM/shape: an operational fault)** —
   is destroyed at exactly the boundary that needs it.
3. **It is the upstream cause of P1(b).** You cannot write `assert!(matches!(e, LeafError::BindingUnsat{..}))`
   when the variant does not exist. `must_refuse` closed the panic/Err half; the reason-matching half stays
   impossible until these enums land.

**And the seams default open:**
- `node`'s `coord_gate` / `finality_gate` / `strand_admission` all **fall back to the unverified Rust sibling**
  when the archive lacks the export, distinguished only by log level — `coord_gate` logs its fallback at
  `debug!` "to avoid spamming a fallback build". A node silently running three unverified gates is one missing
  symbol away, and the loudest signal for the 2PC gate is a debug line.
- ~~`gpu_babybear_merkle_e2e.rs`'s fail-open skip~~ — **closed at HEAD**: `require_gpu()` asserts
  `adapter_available()` (fail-closed) and the tests are `#[ignore]`d for GPU-less CI with the GPU lane running
  them `--ignored` (`gpu_babybear_merkle_e2e.rs:52-81`) — the crate's own correct pattern
  (`gpu_backend.rs`'s assert-adapter-and-assert-GPU-path) made the law.
- `node/src/api.rs:4521` — `let _ = s.store.set_config("passphrase_hash", ...)` under a comment reading
  "Persist... so they survive restarts." A failed write returns `success: true`; the node reboots with no
  passphrase and the next loopback caller sets a fresh one.
- `turn`'s `LedgerJournal::rollback` is infallible and best-effort: it swallows every missing cell
  (`if let Some(c) = ledger.get_mut(&cell)`), panics on a poisoned mutex (`verify.rs:515-524`), and panics on a
  violated fixed-slot invariant (`:433`) — **inside the path whose entire job is recovering from failure.**
  Atomicity is the crate's central claim and its recovery path is its least defended code.

### P4 — The abstraction exists in the domain and not in the type system

`circuit-prove`: **zero traits in 37,543 lines** (`grep -rn '^pub trait|^trait ' src/` → nothing). Yet ~20
`*_leaf_adapter` modules implement a manifestly uniform contract — `prove_X_leaf(witness, pis, config) ->
Result<RecursionOutput<..>, String>` plus `prove_X_leaf_with_claim` exposing an `X_CLAIM_LEN`-felt claim the
binding node `connect`s. `membership_leaf_adapter.rs:197` and `presentation_leaf_adapter.rs:178` differ only in
error strings. `lib.rs` is 43 flat `pub mod` and exactly **one** `pub use` — no facade, no seam.

**The direct, measurable cost is ragged validation.** Counting `public_inputs.len() !=` per adapter:
sovereign/membership/hatchery/factory/caveat_admission/bridge validate **both** entry points;
zkoracle/solvency/shielded_spend/note_spend/deco validate **one of two**; presentation/dsl/custom/
blinded_membership validate **neither**. `prove_membership_leaf` opens with an explicit length check;
`prove_presentation_leaf` passes the slice straight to the prover. It is fail-closed **by accident** (a wrong
length dies deeper in `prove_vm_descriptor2_for_config`) — fail-closed at the wrong layer, surfacing an opaque
deep string instead of a clean boundary error, inconsistent for no stated reason. Adding a leaf is ~500 lines of
copy-paste the compiler checks nothing about.

The same shape in `cell`, at reduced severity since MOVE 1: nested `Not` is collapsed by the smart constructor
(`SimpleStateConstraint::not`) and the evaluator, and `lift_simple` is fail-closed — but `Not(Box<..>)` remains
a public tuple variant, so a wire-decoded program can still carry any nesting depth and the invariant is
constructor-plus-evaluator-enforced, not type-enforced. The type-level version (P4's ask) is not built.

**Contrast — the pattern done right, in this same tree:** `sdk`'s `raw` module seal. `Authorization::Unchecked`
is spelled in exactly ONE constructor (`raw::unsigned_action`), quarantined behind a module whose docs enumerate
the three sanctioned uses, and deliberately omitted from the root re-export. `TurnBuilder` holds `effects`
private and `sign()` is the only exit. **On the headline surface an unauthorized act is inexpressible.** That is
what P4 asks for everywhere else. The minted `handler-floors` pattern (a forgotten gate is a *type error*) is
the same idea and it is already ours.

### P5 — The god object, and its receipt

`NodeStateInner` is **127 pub fields behind one `Arc<RwLock>`** — cipherclerk, ledger, store, coord budgets,
routing table, prove pool, accumulators, gossip handle, committee history. **The architecture already handed us
the receipt:** the crate's own comment documents the live n=4 stall, where `poll_finalized_blocks` had to
snapshot-and-clone the whole lace because holding `lace.read()` across the O(history) FFI starved the block
producer's `lace.write()` and froze `dag_height`. The clone is a workaround; the lock granularity is the bug.

`turn`: 68k lines, 50+ top-level `pub mod`. `economics.rs` (EpochMinter), `fast_path.rs` (lock tables),
`aggregate_bilateral_prover.rs` (2,070 lines of prover), `reactive.rs`, `umem.rs` (2,656) are things a
call-forest transaction model *depends on or emits*, not things it **is**. `executor/` alone is 21k across 11
files, `apply.rs` at 4,610. `src/tests.rs` is **11,998 lines** — the largest file in the crate by 2.5×, and it
compiles into the crate. The Cargo.toml shows real thought about the verify/prover split (the recursion-free
wasm/seL4 floor), but that discipline is expressed **in features, not in module boundaries.**

Nothing here is *wrong*. The abstraction boundary has simply not been paid for. **And it is deliberately the
lowest-priority pattern** — see §4.

### P6 — The self-report is better than the burndown

Our best apparatus produces ledgers nobody drains:
- **44 Uncovered** producer-equals-descriptor rows (`circuit/tests/producer_descriptor_coverage_gate.rs`;
  some Uncovered BY DESIGN — forbidden/UNSAT paths — the rest genuinely undrained). A large fraction of
  deployed descriptor members still have no prove+verify roundtrip against the registry descriptor they ship
  under — on the V3-live registry, which is what a light client verifies against **today**. This is the exact
  class that already bit once: the gate's own header cites `be732a9dd`, where 7 wide members laid their AFTER
  carrier chain at a stale base and verify failed on **honest** turns — "a class the drift gate CANNOT see."
- ~~The FRI gate covers 3 of 5 deployed knobs~~ — **closed at HEAD, past the ask**: the pin covers 7 configs
  and 6 knobs (`ext_deg` included), `ledger_gate_reds_each_degraded_knob` perturbs each DEPLOYED const and
  requires a typed refusal NAMING that knob, and `the_export_is_consulted_not_shadowed` proves the numbers
  track Lean rather than a leftover Rust constant (`circuit-prove/tests/fri_params_soundness_budget.rs:115-125`).
- Two authority traits (`IssuerRootAuthority`, `FinalizedRootAuthority`) have **no production implementation
  anywhere in the tree** — only cell's own in-memory `Static*` doubles. Their rustdocs say "Production hosts that
  read issuer roots from on-chain slots install their own authority." No such host exists. So BlindedSet
  membership and ObservedFieldEquals are fail-closed-in-practice, i.e. non-functional. Honest and safe — but the
  docs imply a built path that is not built.
- ~~`node/src/turn_proving.rs`'s downstream caveat~~ — **closed at HEAD**: the module doc states the
  14-nullifier exception "at the headline rather than 70 lines downstream" (`turn_proving.rs:1-12`). The
  underlying capacity limit itself (the depth-parameterized non-revocation AIR) remains the named seam.

**The named-seam law is satisfied and most closure lanes are not running.** A named seam is not a hole — but a
seam named months ago with no lane is drifting toward one. The authority-trait and coverage-ledger rows above
are the live examples.

### P7 — Diagnostics registered as tests (closed at HEAD)

The reading found two RADV-bisection debug tools registered as `#[test]`s in `gpu_backend.rs`: one with zero
assertions writing WGSL to `/tmp` on every CI run, one whose body never executed in CI (its env var is unset) —
honestly labelled DIAGNOSTIC, but inflating the count and reporting `ok` while proving nothing. **Both are
de-registered** (`gpu_backend.rs:4805-4809` records the demotion), and the GPU posture follows one law: tests
requiring a GPU assert `adapter_available()` (fail-closed) **and** are `#[ignore]`d so GPU-less CI skips them
explicitly, with the GPU lane running them `--ignored`. The pattern stays on the record: a debug tool that
cannot fail is not a test, whatever its comment says.

### What we do NOT have (recorded so it is not re-litigated)

Readers hunted specifically for these and found **zero** hits:
- `assert!(true)`, `assert_eq!(1,1)`, P → P shapes, mock-testing-the-mock across `circuit`'s src/ and tests/.
- `todo!()` / `unimplemented!()` in 37.5k lines of `circuit-prove`; **zero** `todo!`/`unimplemented!`/`FIXME` in
  the whole of `cell`.
- Unlabelled placeholders. Every placeholder found is labelled, and several are labelled *better than the
  standard asks*: `shielded_ring_clearing_air.rs:106` names its endpoint boundary and states exactly what it
  cannot do ("cannot by itself instantiate `ShieldedRingDescriptorRefines`... the N-leg generalization is named
  not built"). `journal.rs:122-129` carries "NAMED SEAM (UMEM-PRIMITIVE §2, Stage A)". `shadow.rs:86-96` names
  the verified kernel's fixed placeholder fee cells and exactly why the reconstituted ledger diverges.
  `NotYetWiredVerifier` names the **exact missing upstream module per kind** so an operator can diagnose which
  wiring they forgot. `node`'s crypto-core installs carry an explicit ⚠ HONEST SCOPE block admitting the ML-DSA
  **sign** install wires only the scalar core and does **not** remove fips204 from the sign TCB — the opposite
  of laundering.

**Read that carefully: `unlabelled placeholders` is not one of our patterns.** Our vacuity is never a fake
assertion and never a dressed-up stub. It is **structural presence standing in for behaviour**, and **a name
outliving its referent**. Those are subtler and they survive code review, which is why they are the top two
patterns and why the standard below targets them specifically.

---

## 3. ⚑ THE STANDARD — what EXCELLENT means for a dregg crate

Hold a crate against these. Each gate is checkable, has a stated falsifier, and names the real anti-pattern it
exists to kill. **A crate is EXCELLENT when all nine pass. `good` is any crate that gets the architecture right
and fails some of them — which is currently all of them.**

### S1 — Every load-bearing tooth has an adversary, and the adversary is *constructed*

- For each security claim, a test **builds a specific forged witness** and requires refusal.
- It **re-asserts the honest pole first**: `assert!(!rejects(&desc, &trace, &pis), "honest witness must be
  accepted — else the canary is vacuous")` **before** asserting the tampered reject. This is not optional; it is
  the thing that makes the negative non-vacuous.
- It asserts **why** it rejected — `assert!(matches!(e, LeafError::BindingUnsat{..}))` — not that something went
  wrong.
- ✗ Fails if: the test pattern-matches an AST for gate *presence* (P1a); accepts any `Err(_)` or any panic
  (P1b); asserts a value the fallback path also returns (P1c); passes an input shape the live call site cannot
  produce (P1e); asserts `HashSet::contains` on a hand-constructed struct (this tests the standard library).
- ✓ **Reference implementations, in-tree:** `ir2_amplified_submask_refuses`;
  `every_forged_commitment_lane_is_rejected_by_the_fold` (forges each of 8 lanes **independently**, `k in 0..8`
  — which is precisely what makes the second squeeze block load-bearing, because a node binding only the first 4
  would accept `k in 4..8`); the whole `*_emit_gate` canary family;
  `cap_witness_path_not_reaching_prestate_root_is_rejected`;
  `signature_rejects_tampered_{was_encrypted,effects_hash,finality,computrons}`;
  `proptest_receipt_chain_integrity` (removes each interior receipt and requires failure, plus a swap-breaks
  companion).

### S2 — Every tooth bites in automation, on a named schedule

- No load-bearing test is `#[ignore]`d without a **scheduled lane that runs it** (`--ignored` on the
  gauntlet/nightly box). "Expensive" means "runs nightly", never "runs never".
- No test silently skips. A skip is either an **explicit honest skip** (`#[ignore]`, so the runner reports it as
  skipped) or a **hard requirement** (`assert!(adapter_available())`). Never `eprintln!("skipping"); return;`
  inside a running test — a green that means nothing is worse than a red.
- Environment-conditional behaviour is **declared**, and a hard mode exists that turns every skip into a panic
  (`DREGG_TEST_REQUIRE_LEAN=1`, mirroring the `DREGG_REQUIRE_LEAN` build gate that already exists).
- ✗ Fails if: the crate's central claim is asserted only by tests no scheduled job executes; the suite's
  red/green depends on undeclared host hardware; a fault-injection lane disables the production default it is
  supposed to exercise (`DREGG_LEAN_PRODUCER=0`).

### S3 — Errors are typed at every boundary a consumer crosses

- Public entry points return an **enum**, not `String`. The mandatory distinction: **an adversary** (reject
  quietly — `ProofInvalid`, `BindingUnsat`) vs **a deploy/operational fault** (page someone —
  `MalformedDescriptor`, `TableShapeMismatch`, `ProverFailed`). A consumer that cannot separate these cannot
  operate.
- Variants carry **structured triage payload**, not a formatted sentence.
- A typed error at the top **must not swallow a stringly layer beneath it**. `RecursionFailed{reason: String}`
  under a 10-variant enum is the enum failing.
- No `panic!`/`unwrap`/`expect` on any path reachable from decoded wire bytes or from a public API taking
  untrusted input. Prover-side can't-happens still return `Result` (`fill_chip_lanes`).
- ✓ **Reference implementations, in-tree:** `TurnChainError` — 10 variants, each fail-closed with diagnostic
  payload, each doc-comment **naming the adversary it stops**; `turn/src/error.rs` — ~90 typed variants,
  stranger-legible `Display`, and a `refusal_class()` projection for security counters that depends on no metrics
  facade. `DelegationModeUnimplemented` is deliberately distinct from `DelegationDenied` so a caller can tell
  "mode confers nothing" from "authority was evaluated and found wanting." **That is design, not enum-padding —
  it is the bar.**

### S4 — Fail-closed is structural, and fail-open is in the *name*

- The default is refusal. A missing verifier, a missing archive symbol, an absent signature → **reject**.
- If a lenient variant must exist, the leniency is in the identifier: `verify_receipt_chain_with_optional_keys`,
  not `..._with_keys`. The strict variant exists and is the one the exit path calls.
- A degraded gate is **loud**. Falling back to an unverified sibling is `error!`/`warn!`, never `debug!`.
- A feature that arms a permissive path is **structurally unable** to reach a production build — enforced by
  `compile_error!` and a pinned `cargo tree` assertion in CI, not by a Cargo.toml comment.
- ✓ **Reference implementation, in-tree:** `CredentialSetMembershipVerifier` holds two independent
  `Option<Arc<dyn ..>>` and rejects unless **both** are installed; the `with_adjacency` rustdoc correctly states
  it *still* fails closed on the issuer-root step. The gate rejects; it does not merely claim to.
  Also: `canonical_revocation_root_for_set` returns `Err(RevocationCapacityExceeded)` rather than silently
  truncating past `TREE_DEPTH` — **explicitly choosing to lose the proof rather than lose soundness.**

### S5 — Docs claim exactly what the code does — checked at the front door first

- **The front door is audited first, not last.** `lib.rs:1-110` and every module header is the most-read text in
  the crate and must be the most accurate. (The reading found the ordering inverted; the MOVE-4 sweep corrected
  the named instances — the gate here is what keeps it corrected.)
- Every number in a doc is **derived from the code that computes it** or is pinned by a test. A soundness figure
  that contradicts the crate's own gate is a defect of the same severity as a wrong constraint.
- Every named function/type in a doc **exists**. `#![deny(rustdoc::broken_intra_doc_links)]` is on, so a deleted
  item can never again be documented as live.
- A function's name states what it verifies. `verify_stark` verifies a STARK or it is renamed.
- **When a claim is deleted from the code, it is deleted from every doc that cites it** — grep the workspace for
  the name, not just the module.
- ✗ Fails if: a doc's stated *reasoning* is backwards (`types.rs:594`); a doc describes a plan that already
  landed or an engine that was deleted; a rustdoc claims a check (`length-prefix shape`) the body does not
  perform; a headline claim is qualified 70 lines downstream of where it is made.

### S6 — The abstraction is in the type system, not in the copy-paste

- If N modules share a shape, that shape is a **trait with provided methods**, and the validation every instance
  needs happens **once, in the trait, for everyone**.
- A forgotten gate is a **type error**, not a code-review miss (the minted `handler-floors` pattern).
- An invariant stated in a comment is enforced by a type, a smart constructor, or a validation pass. **A comment
  is not an enforcement mechanism** — and `cell`'s `Not(Not)` panic is the proof: the comment was not just
  unenforcing, it was *false*, and the belief it created suppressed the test that would have caught it.
- The public surface makes the wrong thing **inexpressible** rather than merely discouraged.
- ✓ **Reference implementation, in-tree:** `sdk`'s `raw` module seal (see P4).

### S7 — Placeholders are labelled with their *resolution*, not just their existence

We already pass this. Hold the line:
- Every placeholder names **what it is**, **what it cannot do**, **the exact missing upstream**, and **the lane
  that closes it** — and per standing practice that lane enters HORIZONLOG in the same breath.
- Honest scope blocks state what a change **does not** buy (the ML-DSA sign install's ⚠ HONEST SCOPE).
- A conditional proof of an architecture over a labelled placeholder floor **is real work** and is framed as
  scheduled sharpening on a chosen trajectory — never as a defect.
- ✗ Fails if: the label is accurate but its lane has not run in months (P6 — a named seam with no lane is
  drifting toward a hole); a rustdoc implies a production path ("production hosts install their own authority")
  that is not built anywhere in the tree.

### S8 — Every floor is stated at its real resolution, and someone has tried to prove it false

- Security figures are stated **per column, each labeled with what it is a claim about** — never as one
  headline: `per-fold 109` at the deployed arity 8 (`~112.6` is arity 2; both at 96.9% farness, not the
  operating Johnson radius) / `73` Johnson QUERY column (the `m → ∞` idealisation, which DROPS BCIKS20's
  `ε_C`) / `71` commit-phase `ε_C` at the `2^12` fixture (it BINDS) / `~70` the ethSTARK eq. (20) composite /
  `130` refuted-capacity drift baseline. Stated at the front door, not only in the gate.
- Every knob the bound depends on is **pinned by a gate**. If the surviving bound is structure-specific (dim-2
  constant-fold, r=2, n=64), the **structural** knobs are gated, not just the arithmetic ones.
- The non-vacuity test for a gate **perturbs the deployed constants and requires a red** — it does not evaluate
  the formula on a synthetic point. (The reading's counterexample — `budget_gate_reds_a_degraded_config`, which
  asserted that 20 < 128 and would have passed with the gate deleted outright — is replaced at HEAD by
  `ledger_gate_reds_each_degraded_knob`, which perturbs each deployed knob and requires a typed refusal naming
  it. That is now the in-tree reference implementation of this gate.)
- ✓ **Reference implementation, in-tree:** `fri_params_soundness_budget.rs`'s header, which states the
  conjecture is refuted, names its own check as a conservative engineering margin and **not** a proof, and
  computes its ledger from the exported deployed knobs rather than from comments. The discipline now reaches
  `lib.rs` (the per-column ledger at the front door) and pins all deployed knobs.

### S9 — What is deployed is what is proven

- The descriptor a producer ships under is the descriptor a test proves and verifies against. **Zero Uncovered
  rows** on any live registry; every Partial pinned to a named, dated seam.
- A verified-good implementation is not left dead beside a deployed weaker one (`cap_delegation_nonamp` is
  correct and dead; the opaque-digest `attenuateA` is deployed).
- A gate on the live path is fed inputs that can actually differ. `f(x, x)` where `f` admits every `x` is not a
  gate; it is a claim.
- Two independent producers of the same artifact are **pinned to each other**.
- ✓ **Reference implementations, in-tree:** the Lean↔Rust double-pin in `note_spending_emit_gate.rs` — it embeds
  the byte-identical `emitVmJson2 noteSpendLeafDesc` string that Lean `#guard`s, decodes it, and asserts equality
  with the **independently built** production Rust lowering. Neither side can drift silently: Lean drift breaks
  the `#guard`, Rust drift breaks the assert. It further pins structural counts (12 chip lookups, 8 PiBindings, 1
  WindowGate) so a constraint **deletion** is caught, not just a mutation. **That is TWO-GATES-PROVABLY-AGREE
  done right.** Also `GpuBn254Mmcs::verify_batch`, which **delegates to the real CPU verifier** — a GPU-minted
  proof is checked by untouched CPU code, so the GPU path can only change *where* an identical function
  computes. Sound by construction, not by assertion.

---

## 4. THE PRIORITIZED PLAN

Ordered by leverage, with severity overriding at the top. **MOVEs 1–4 are LANDED at HEAD** (each records its
in-tree state below); MOVE 5 and most of the P6 burndowns are the open work.

### ⚑ MOVE 1 — Close the three live holes — **LANDED**

Every item shipped as prescribed; §1 carries the closed state with file:line. In brief: `lift_simple` is total
and fail-closed with the smart-constructor collapse (`Not(Not(c)) → c`) and the false doc rewritten;
`verify_receipt_chain_strict` + the renamed `verify_receipt_chain_with_optional_keys` with the strip-a-signature
adversarial pair; the `test-stubs` feature is dev-only, `compile_error!`-floored, and cargo-tree-firewalled
(`tests/tests/test_stubs_firewall.rs`). The crown jewel derives its colliding pairs by bounded search at test
time (`find_lane0_collision`) — the stale-pin failure mode is removed, not patched.

### ⚑ MOVE 2 — Arm the teeth that already exist — **LANDED**

The nightly armed-teeth lane exists (`.github/workflows/armed-teeth.yml`, cron 05:00): all 8 deployed
light-client binding-tooth binaries run `--release --no-fail-fast -- --ignored`, and the Lean hard-mode soak
lane runs with `DREGG_TEST_REQUIRE_LEAN=1` so every archive-less self-skip is a panic there.
`consensus_under_failure.rs` fault-injects the production default (Lean producer ON; the legacy-Rust comparison
lane must be asked for via `DREGG_TEST_LEAN_PRODUCER=0`). The GPU posture follows one law — fail-closed
`adapter_available()` asserts + explicit `#[ignore]` for GPU-less CI — and the two WGSL diagnostics are
de-registered from the test count (P7).

### ⚑ MOVE 3 — Make the named vacuous gates bite, and kill the reject idiom — **LANDED**

- **`coord_gate`** — `lean_verdict_overrides_a_wrong_rust_decision` (`coord_gate.rs:179`) hands the gate a
  deliberately wrong `rust_decision` and requires the Lean verdict to win; the P → P
  `falls_back_to_rust_when_no_wire` is deleted.
- **`finality_gate`** — `admits_semantics` (which tested `HashSet::contains`) is deleted; the replacement drives
  the gate over an un-enrolled attacker block (`finality_gate.rs:283` records what it does that the deleted
  tests could not).
- **`cap_delegation_nonamp`** — the behavioural tooth exists:
  `nonamp_submask_gate_refuses_an_amplifying_witness` forges each mask bit independently against the running
  prover (`cap_delegation_nonamp_descriptor.rs:301`).
- **The FRI budget canary** — `ledger_gate_reds_each_degraded_knob` perturbs the deployed consts, one knob at a
  time, and requires a typed refusal naming that knob.
- **The reject idiom** — `must_refuse` / `must_refuse_or_unsat_panic` landed (`circuit/src/refusal.rs:201,234`),
  distinguishing panic from `Err` and asserting the p3 unsat-panic message where that is genuinely the
  mechanism; the bulk of the ~197 sites are converted (~29 raw `catch_unwind` + ~13 bare `Err(_)` remain). The
  reason-*matching* upgrade waits on MOVE 5's typed errors, as planned.
- **`turn`'s Property 1** — rewritten to drive CapOps through `TurnExecutor::execute` with real
  `Effect::GrantCapability`/`RevokeCapability` and real `Authorization`, recording grants only from `Committed`
  receipts (`turn/tests/proptest_invariants.rs:191-226`); the harness-tests-its-own-model version is gone, and
  `disjoint_cells_no_conflict` now asserts what its comment promises (`conflict.rs:299,373`).

### ⚑ MOVE 4 — The front-door honesty sweep — **LANDED, one named lane open**

Every known-false front-door sentence is corrected (the per-instance record is in P2): the `circuit` Trust Model
carries the per-column ledger; the `mock`-feature and `[stark]`-link rot is gone; `custom_proof_bind.rs` and its
citing sites state the recursion-fold truth and the dead `ProofBindError` is deleted; the executor and verify
docs match the code; the predicate stub docs say what a stub checks; `turn_proving.rs` qualifies its headline
where it is made; `verify_stark` is `verify_admission_binding` and the submitter-declared `conflict_set` is a
NAMED seam (`turn/src/encrypted.rs:7`).

**Open:** `#![deny(rustdoc::broken_intra_doc_links)]` — the structural turn-the-class-off — is a named lane, not
a one-line add (`circuit/src/lib.rs:215`: 311 hits at measurement, most of them bracket-notation escapes;
shipping it red would train readers to ignore `cargo doc`). Do it as its own lane.

### ⚑ MOVE 5 — Type the boundaries and lift the abstraction — **OPEN (the remaining engineering lane)**

With MOVEs 1–4 landed, this is where the open multi-week work lives — the piece that makes the earlier moves
*stick* rather than be re-fixed.

1. **`LeafError` / `RecursionError` in `circuit-prove`.** The variant that matters: **`BindingUnsat{..}`** (the
   connect conflicted — a forged claim, the tooth firing) vs **`ProverFailed{..}`** (FRI/OOM/shape — an
   operational fault). The reject-idiom cleanup's mechanical panic/Err split is done (`must_refuse`); the
   reason-*matching* upgrade depends on this existing (`refusal.rs:88` names the dependency).
2. **The `LeafAdapter` trait.** The ~20 adapters already share one shape; lift it:
   ```rust
   trait LeafAdapter {
       type Witness;
       const CLAIM_LEN: usize;
       const PI_WIDTH: usize;
       fn descriptor() -> Result<EffectVmDescriptor2, LeafError>;
       fn trace(w: &Self::Witness) -> Result<Vec<Vec<BabyBear>>, LeafError>;
   }
   ```
   with `prove_leaf` / `prove_leaf_with_claim` as **provided** methods that validate `public_inputs.len() ==
   PI_WIDTH` **once, in the trait, for everyone.** Retires the copy-paste, closes the ragged validation
   (presentation/dsl/custom/blinded_membership checked nothing when read), and makes a forgotten PI check a
   **type error**. Make an emit-gate + a per-lane forge tooth part of the trait's definition of done.
3. **`Ir2VerifyError` on the verify boundary.** `{ MalformedDescriptor, TableShapeMismatch{expected, got},
   RangeTableHeight{got, deployed}, ProofInvalid, PublicInputMismatch }` for `verify_vm_descriptor2` /
   `parse_vm_descriptor2`; String stays only on prover internals. Lets `lightclient/` and `bridge/` separate
   deploy bug from adversary. Convert `fill_chip_lanes`'s `panic!` (`descriptor_ir2.rs:3825`) to a `Result` while
   there.
4. **`ApiError` with `IntoResponse` in `node`.** ~200 mechanical sites; recovers the diagnostics thrown away at
   every boundary. Start with auth/submit/faucet. Fix the passphrase swallow (`api.rs:4521`) — propagate and
   return 500, or document the store as best-effort. As written the doc and the code disagree **about a
   credential**.
5. **Harden `turn`'s rollback.** `LedgerJournal::rollback` returns `Result<(), RollbackError>` naming the cell it
   could not restore; poison-tolerant locking (a poisoned mutex during rollback must not abort the node); a test
   that rolls back **every** `JournalEntry` variant and asserts byte-identical `state_commitment` recovery
   against a pre-turn clone.

**In parallel, the burndowns (P6):**
- **The 44 Uncovered rows, V3-live registry first.** The gate already names each row and its reason, so the work
  is enumerated: drive each producer trace through `prove_vm_descriptor2` + `verify_vm_descriptor2` against the
  committed descriptor. Target: zero non-BY-DESIGN Uncovered on V3-live; every Partial pinned to a named, dated
  seam.
- ~~Extend the FRI gate to all 5 knobs~~ — **done, past the ask**: 7 configs, 6 knobs pinned to their Lean
  models, per-knob red canary with typed reasons (`fri_params_soundness_budget.rs:115-125`).
- **Resolve the cap-descriptor orphans** — wire them into a real selector-to-JSON dispatcher so the delegation
  family proves under the genuine-non-amp descriptor instead of the opaque-digest `attenuateA`, **or** delete both
  modules and their `lib.rs` prose. Do not leave the good one dead and the weak one deployed.
- **Add fee conservation as a property.** `proptest_balance_conservation_holds` pins `fee = 0` and
  `ComputronCosts::zero()`, so the invariant reduces to "transfers conserve." The fee-accounting half — where THE
  EPOCH §5 distribution and the n=5 dogfood faucet bug live — is covered by nothing.
- **Proptest the constraint AST** (`cell`). An `Arbitrary` impl over nested `SimpleStateConstraint` (depth 3–5)
  asserting eval never panics is the **generic cure for the whole `Not(Not)` bug class**, and proptest is already
  a dev-dep. Extend to a postcard decode→evaluate fuzz target, since decode is the attacker's entry point. **Note
  the causality: `Not` is exercised at 10+ sites and every one wraps a non-Not atom. The false doc is exactly why
  nobody wrote the nested case.**
- **`node`'s F-4 gate** — make it bite (gate block **creators**, or the proposed-membership set, against the
  constitutional seed root, so `blocklace_sync.rs:1004` becomes reachable) **or** delete the call and move the
  F-4 claim to where the tooth really is (the membership vote). Today's version is the worst of both: it names a
  closure it cannot perform. Feed the vouch/bond registry from gossip so the thresholds stop being inert.
- **Registry completeness assertable** (`cell`): `production_readiness() -> Vec<(kind, ReadyOrFailClosed)>`,
  asserted at host startup. Turns "I called `registry_with_real_verifiers` instead of `_full`" from a silent
  runtime rejection into a **boot error**.
- **Retire the phantom production path**: build a real on-chain-slot-reading `IssuerRootAuthority` /
  `FinalizedRootAuthority` (the docs describe the right design — read the issuer cell's `MEMBERSHIP_ROOT_SLOT` /
  `REVOCATION_ROOT_SLOT`), or amend the rustdocs to say plainly that BlindedSet + ObservedFieldEquals are
  fail-closed pending that host, with the lane named.

### NOT the plan — explicitly deprioritized

- **Decomposing the `turn` monolith is LOW priority.** `lib.rs` correctly declares it LEGACY, pending the
  verified-Lean swap. **Do not gold-plate the architecture of a crate whose successor is in flight.** Moves 1–4
  on `turn` (honesty + teeth + the Property-1 rewrite) are surgical and gate the swap; carving out
  `economics.rs` / `fast_path.rs` / `aggregate_bilateral_prover.rs` is the debt-hole version of this work. Only
  if the swap slips.
- **`NodeStateInner` decomposition is real but incremental** — carve independently-locked subsystems out one at a
  time (lace first: it is the one with the receipt). Not a rewrite.

---

## 5. The per-crate table

| crate | role | grade | top remaining gap (at HEAD) | priority |
|---|---|---|---|---|
| `dregg-cell` | core-protocol | **good** | The MOVE-1 defects (the `Not(Not)` panic, the `test-stubs` leak, the RED forge test) are **closed**. Remaining: the Not-depth invariant is comment+constructor-enforced, not type-enforced (P4); the authority traits (`IssuerRootAuthority` / `FinalizedRootAuthority`) still have no production implementation. | medium |
| `dregg-turn` | core-protocol | **good** | The fail-open chain verify is **closed** (strict/optional split) and Property 1 drives the real `TurnExecutor`. Remaining: rollback hardening (MOVE 5.5). Monolith deprioritized (LEGACY, swap in flight). | medium (decomposition LOW) |
| `dregg-node` | core-protocol | **good** | The 2PC-gate tooth bites and the nightly hard-mode lane asserts the verified-consensus claim. Remaining: the F-4 strand-admission gate is still the **identity function** on the live path (`admitted_participants(raw, raw)`, vouch/bond thresholds inert); `ApiError` typing + the passphrase-persist swallow (`api.rs:4521`). | **high** (F-4) |
| `dregg-circuit` | verification | **good** | Front door **corrected** (per-column ledger). Remaining: **44 Uncovered** producer-equals-descriptor rows on the V3-live registry (the class that already bit, `be732a9dd`); the cap-descriptor orphans (good one dead, opaque-digest one deployed — now honestly labeled); the `deny(broken_intra_doc_links)` lane. | **high** (coverage rows) |
| `dregg-circuit-prove` | verification (prove half) | **good** | The deployed teeth **run nightly** (armed-teeth lane) and `custom_proof_bind`'s doc states the fold truth. Remaining: **zero traits in 37.5k lines** → ragged PI validation across ~20 copy-pasted adapters; `LeafError`/`BindingUnsat` typing (MOVE 5.1–5.2). | **high** |
| `dregg-sdk` | core-protocol | **good** | *(assessment truncated — strengths only.)* The `raw` module seal is the tree's **reference implementation of S6**: `Authorization::Unchecked` in exactly one quarantined constructor, omitted from the root re-export, so an unauthorized act is inexpressible on the headline surface. Gaps not read. | re-read to complete |

**Reference implementations worth copying, by standard:** S1 → `every_forged_commitment_lane_is_rejected_by_the_fold`, the `*_emit_gate` canary family · S3 → `TurnChainError`, `turn/src/error.rs` · S4 → `CredentialSetMembershipVerifier`, `canonical_revocation_root_for_set` · S6 → `sdk::raw` · S8 → `fri_params_soundness_budget.rs`'s header · S9 → `note_spending_emit_gate.rs`'s Lean↔Rust double-pin, `GpuBn254Mmcs::verify_batch`.

---

## Coda

> The teeth are armed; they bite at night.
> The front doors say what the deep code does.
> What remains is not the knowing or the arming —
> it is the types, and the rows the ledger draws.
>
> Six crates said *good* in six honest voices,
> each one naming what it could not do.
> Excellence is not another apparatus.
> It is draining the ledger the apparatus drew.

( ˘▾˘ )

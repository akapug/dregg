# TEST-RIGOR + FULLNESS-SIM audit — the distribution layer + the verified core

Read-only audit, 2026-06-30. Scope: the distribution surface (attach / session / cockpit /
cap-auth / extension / status) in `~/dev/DreggNet` + `~/dev/breadstuffs`, and the
federation / node / consensus / verified-core (dregg-agent session, node, blocklace, turn,
exec). Every claim is grounded to `file:line` at HEAD. Honest both ways: the real teeth are
credited by name; the fakes are called fake.

The one-paragraph verdict: **the RULES are heavily and often adversarially tested; the LIVE
SYSTEM under concurrency / failure / a real adversary is almost entirely untested.** The
consensus rule, the cap lattice, the receipt chain, the circuit descriptors, the budget
algebra — all have real, biting, non-vacuous tests. But almost every one runs in a single
process, over a hand-built ideal input, one evaluation at a time. The three load-bearing
distribution guarantees — multi-tenant isolation *under concurrency*, OS/SSH *confinement of a
real process*, and *a federation reaching finality* — are asserted by construction or by
string inspection, not exercised. There is no synthetic sim that drives the real fullness.

---

## 1. Coverage gaps — ranked by load-bearing

### G1 — A real federation reaching finality (the top gap). PARTIALLY OPEN, honestly.
Two REAL multi-process federation tests exist and are unusually candid:
- `breadstuffs/node/tests/three_node_ordering_rule.rs:187` — spawns THREE real `dregg-node`
  binaries (`Command::new(NODE_BIN)`, `:154`/`:181`) in `--federation-mode full --consensus
  blocklace` over the real QUIC gossip wire, 3-validator genesis (`threshold=3`). It HARD-asserts
  full mode + 3 distinct identities (anti-vacuity, `:252`) and cross-node block exchange
  (`best_proposers >= 2`, `:317`). But **[C] actual cross-node finality is NOT asserted by
  default** — it is measured and reported, hard only under `DREGG_TEST_REQUIRE_FINALITY=1`
  (`:343`), which the file states will FAIL today because the Plumtree/QUIC dissemination
  delivers asymmetrically at small N (`:26-31`).
- `breadstuffs/node/tests/sustained_finality.rs:203` — same 3-binary spawn; the cross-node commit
  witness is the recipient cell materialising on all three nodes (`:297`). It DOES hard-assert
  the FIRST turn commits cross-node (`committed_turns >= 1`, `:339`) and zero gossip stream-storm
  (`:329`) — but SUSTAINED finality (3-in-a-row) is again env-gated (`:361`).

So: the real federation *runs and exchanges blocks*, and *one* turn commits cross-node — but
reliable / sustained finality is a known-open frontier, not a default-passing test. Nothing
kills a node mid-consensus, injects a real network partition (vs deterministic delta
withholding), or runs a Byzantine validator over the real wire. **The claim "the federation
reaches finality" is not covered by a green test.**

### G2 — Multi-tenant isolation under concurrency. NOT TESTED.
Every isolation test in the tree is single-threaded, in-process, over a static 2-3 owner map:
- `DreggNet/attach/src/store.rs` — 9 isolation tests (`:276`-`:415`), all single-threaded. There
  is an explicit under-the-lock quota re-check documented as a race guard (`store.rs:152-157`)
  with ZERO concurrency coverage.
- `breadstuffs/dregg-agent/src/session.rs:814` `two_sessions_are_isolated_by_construction` —
  drives Alice then Bob SEQUENTIALLY in one process. Real cryptographic isolation (distinct
  creds/signers/budgets), but no concurrent race.
- `DreggNet/sandstorm-bridge/src/tenant.rs:145-172` — REAL cross-tenant non-resolvability, but
  in-memory registry, single-threaded.
No test drives N tenants attaching + driving agents concurrently with isolation held.

### G3 — OS / SSH confinement of a REAL process. NOT TESTED (the jail is unwired).
- `DreggNet/agent-host/src/isolation.rs` — the bwrap OS jail. Its own header (`:5-15`) says it is
  "NOT YET WIRED ... no production call sites." The tests (`:338`,`:356`,`:368`) inspect the
  generated argv STRING (omits `/home`, has `--unshare-all`/`--clearenv`); the only `launch` test
  proves it REFUSES off-Linux (`:415`). No real jailed process is ever confined; no real "can't
  read operator keys / can't egress" is exercised.
- `DreggNet/agent-host/src/lib.rs:138` `authorized_keys_line` — the SSH forced command
  (`command="…",restrict,pty`). Tests assert the generated STRING (`:462`,`:562`). **No test
  spawns a real sshd/ssh and proves OpenSSH honours `restrict`/`command=`.** The critical
  shell-cap-refused-at-enrol tooth IS real (`:485`), but it is a parser refusal, not a runtime drop.

### G4 — The A1 execution-FFI under concurrent writers. NOT TESTED.
The production guard is real: `breadstuffs/node/src/blocklace_sync.rs:3968-4054`
`execute_finalized_turn` runs the FFI on `spawn_blocking` off the lock (`:3976`), re-acquires,
and at `:4025` declines install on a touched-cell conflict.
- `a1_finalized_turn_advances_height_zero_to_one_off_lock` (`:5831`) — REAL and valuable (proves
  the off-lock execution unblocks, height 0→1), `multi_thread` runtime, but a SINGLE turn with no
  competing writer — the guard at `:4025` never fires.
- `a1_overlay_installs_poststate_and_guards_concurrent_writes` (`:5936`) — MOCK-NOT-REAL for the
  concurrency claim: plain `#[test]`, zero threads; "concurrent" writes are SEQUENTIAL
  `insert_cell`s and the guard predicate is RE-IMPLEMENTED inline in the test body (`:5978`,
  `:6033`) instead of driving the production path.
No test stages a real writer racing the off-lock window and asserts the DECLINE branch
(`:4028-4038`) fires. This is the whole point of commit `2fc33f0cc`.

### G5 — Budget / ledger enforcement under a concurrent race. NOT TESTED.
The forge-detector suites are strong but ENTIRELY SEQUENTIAL:
- `breadstuffs/dregg-agent/src/budget.rs:623-964` — ~20 real, non-vacuous forge tests, all
  single-thread. `draws_at_one_block_commute` (`:792`) tests order-independence in one thread,
  not a race.
- `breadstuffs/dregg-agent/src/meter.rs:318` `draw_is_exactly_once_per_key_period` — two
  back-to-back draws; the meter's own documented concurrent-safety claim (`:224-227`, "two
  concurrent same-key draws can't both consume") is UNTESTED (no threads).

### G6 — The live Rust↔Lean executor differential is agreement-only + self-skips.
`breadstuffs/exec-lean/tests/lean_state_producer_differential.rs` runs a turn through BOTH the
Lean FFI executor and the Rust `TurnExecutor` and asserts agreement (`:144`,`:182`) — a REAL
live re-exec (not a recorded trace) — BUT happy-input agreement only, and it self-skips when the
Lean archive isn't linked (`if !lean_available()`, `:192`). `rust_lean_divergence_finder.rs`
degrades to GAP-only (compares nothing) in default CI without `DREGG_LEAN_SHADOW=1`. The
divergence-INJECTING rigor lives instead in the FRI-free circuit differentials (see credits) —
so the *executor-swap* confidence differential compares nothing in default CI.

### G7 — Console auth→subject binding. NOT TESTED.
`DreggNet/console/src/scope.rs:15-17` — the security-critical invariant ("subject comes from the
verified `X-Dregg-Subject`, never a spoofable query param") is a DOC COMMENT with no test. The
scoping *filter* is proven over fixtures (`scope.rs:216-290`); the trustworthiness of its input
is not. Similarly `DreggNet/attach/src/bin/dreggnet-attach.rs:241` `resolve_subject` (the "owner
can't come from the body" guarantee) is untested — only the `cap_satisfied` header parser is
(`:439`,`:473`).

### G8 — Crash / re-attach / recovery of a live session.
`DreggNet/attach` session store is in-memory (`store.rs:85`), no persistence, no recovery test.
(Credit: `breadstuffs/dregg-agent/src/session.rs:504`
`the_budget_persists_across_reattach_and_over_budget_is_refused` DOES model detach→reopen→restore
with over-budget refused — the one real re-attach test. And `webapp/tests/durable_request_resume.rs`
is a real crash-mid-request→resume over on-disk state. But no live *attach* session survives a crash.)

### G9 — microVM / egress OS-level enforcement never runs in default CI.
`DreggNet/exec/tests/microvm_kvm.rs` is `#![cfg(feature = "firecracker")]` (`:23`) AND the two
real-boot tests are `#[ignore]` (`:52`,`:87`) — real only on a manual KVM box run with
`--ignored`. `exec/src/egress.rs` is tested at policy/projection level (`:872-1123`), including a
real projection into the owned sandbox's `WasiCapabilityPlan` (`:1080`, feature-gated) — but NO test opens
a socket and confirms a blocked `connect()` actually fails at the OS/wasmtime layer.

---

## 2. Fake tests — the sharp part (file:line · why fake · what it misses · severity)

Severity key: **CRITICAL** = a single-node/synthetic "consensus" or a string-only "confinement"
presented as covering the real thing; **HIGH** = an "e2e"/isolation test that mocks its boundary;
**MED** = agreement/fixture-only where a divergence/live test is the real bar; **LOW** = vacuous.

### CRITICAL

- `breadstuffs/node/src/finality_gate.rs:455` `gate_on_super_ratifies_n5_c3_shape` —
  **MOCK-NOT-REAL + HAPPY-PATH.** Named as if it witnesses n=5 C3 consensus-under-load. It is a
  HAND-BUILT single-wave DAG (5 `SigningKey`s — not processes, not even node structs; one
  `Blocklace` at `:476`; genesis + `for round in 1..=2` = 3 rounds = ONE wave), evaluated ONCE.
  It asserts a Rust-tau ⟺ Lean-FFI agreement + shape (`:552`, `len==15` at `:566`). **No rounds
  over time, no failure, no partition, no equivocation, no Byzantine node, no message
  drop/reorder.** Self-skips entirely without the Lean export (`:457`). Its siblings
  `verified_gate_agrees_with_rust_tau_three_node` (`:261`),
  `raw_order_export_agrees_with_projection_three_node` (`:363`), and
  `lean_tau_order_fast_on_cross_linked_n5_dag` (`:586`, actually a *perf* regression test) are the
  same shape. *In its favour:* the file's own comments are honest that this is a differential
  gating the "Path-B cut," not a live-federation test. Severity is CRITICAL only against the
  reading that this covers real finality — it does not.

- `DreggNet/agent-host/src/isolation.rs:338/356/368` — **MOCK-NOT-REAL.** "the argv never binds
  the operator keys," "deny-default egress nonroot," "brain keys env-only" all inspect a pure
  string/Vec builder. `launch` is never called; no process is confined. Fails to exercise: a real
  jailed process actually unable to read `/home` or egress. The module is admittedly unwired.

- `breadstuffs/node/src/node_integrator_e2e.rs:137` — "e2e" but **SINGLE-PROCESS, SOLO n=1**
  (honest in-header). Drives the real production path to a verified receipt (genuinely valuable
  integration) but at n=1 `tau` trivially finalizes every block, so NO ordering/agreement is
  exercised. MOCK-NOT-REAL as consensus coverage.

- `breadstuffs/node/src/epoch_transition_e2e.rs:133/238` — "e2e" but IN-PROCESS struct simulation
  (`Node { cm, votes }`, "gossip" is a for-loop `finalize_across`, `:115`). REAL as membership
  logic; MOCK-NOT-REAL as federation.

### HIGH

- `DreggNet/console/tests/console_end_to_end.rs:11` `a_logged_in_user_sees_their_stuff…` —
  **e2e-NAMED, mocks both boundaries.** Data boundary is `FixtureSource`; auth boundary is a
  subject STRING LITERAL (`fixtures::DEMO_SUBJECT`). No login, no webauth, no header verification.
  "logged in" is a misnomer. Proves the internal source→scope→render→verify pipeline (verify leg
  is real crypto) but not "a logged-in user." Rename or add a real-auth variant.

- `breadstuffs/node/src/blocklace_sync.rs:5936` `a1_overlay_installs_poststate_and_guards_
  concurrent_writes` — **MOCK-NOT-REAL for its title.** Zero threads; "concurrent" is sequential;
  guard predicate re-implemented in the test body rather than driven through production. (See G4.)

- `DreggNet/console/src/source.rs:331-435` — the "maps real server record shape" tests run over
  hand-written `json!` blobs the author *claims* match the registry, with NO compile-time type
  link. `LiveSource`'s real HTTP fetch is exercised ONLY in the unreachable→empty case (`:424`);
  the populated fetch+parse+scope chain has zero coverage. If the real serialization drifts, these
  pass falsely.

- `DreggNet/tests/workload/tests/multi_tenant_isolation.rs:63` `tenants_are_isolated` — REAL
  red-team (forged replay moves nothing `:131`, different-terms→Conflict `:158`, unfunded forge
  refused `:175`) but **`#[ignore]`** (`:64`) — runs only via `make test-workload`, never default CI.

### MED

- `breadstuffs/blocklace/tests/multi_node_convergence.rs:215`
  `three_nodes_partition_heal_equivocate_converge` — the STRONGEST failure-mode test, and REAL at
  the engine level (drives real `Blocklace::merge`, `ordering::tau`, `ConstitutionManager::
  auto_evict`). But the "partition" is SIMULATED by choosing which `node.merge()` calls to make
  between three structs in ONE process, over a hand-built round-synchronous DAG — the exact ideal
  shape the *real* 3-process federation (G1) fails to produce. No network, no timing, no
  concurrency. It models the property; it does not stress the reality.

- `breadstuffs/exec-lean/tests/lean_state_producer_differential.rs` — REAL live re-exec but
  agreement-only + self-skips without the Lean archive (G6).

- `DreggNet/status/tests/status_page.rs:29-294` — renders FIXTURES / hand-built `RawHealth` only;
  `LiveSource::health()` is never invoked. The aggregation/honesty logic is genuinely real and
  adversarial (down→Degraded `:55`, unreachable→Unknown `:97`, XSS-escape `:262`) — but "is the
  cloud up?" is only ever computed from hand-authored data in tests. Same for `status/src/live.rs`
  parsers (tested on faithful captures `:341-392`, real HTTP orchestration `:50-122` never run).

- `DreggNet/sandstorm-bridge/src/powerbox.rs:628-919` — a full, genuine red-team suite (real
  HMAC-SHA256, forgery refused `:816`, tamper `:879`, attenuate-only-narrows `:896`) — but for the
  PROTOTYPE `SturdyRef` model, NOT the wired path. `serve_grain` gates on
  `webauth_rail::derive_permissions` (the real `dga1_` rail), not `SturdyRef`. Its #PB-1 forgery
  credit does NOT transfer to the deployed rail. (The deployed rail IS separately real — see credits.)

- `DreggNet/sandstorm-bridge/tests/devnet_real_grain.rs` + `serving.rs` python3-gated tests —
  REAL live runs, but silently skip with no `python3` (`serving.rs:213`, `devnet_real_grain.rs:74`)
  → real-tier + isolation coverage can vanish to a green skip on a python3-less runner
  (green-or-bust concern). Also disclosed in-file: the in-sandbox handler is a representative
  workload, not the `.spk`'s own chroot code.

### LOW / vacuous

- `DreggNet/attach/src/render.rs:584` `the_page_renders_only_the_passed_sessions` — the negative
  `assert!(!html.contains("someone elses secret"))` (`:591`) CAN NEVER FAIL: that string is never
  inserted anywhere. Only the positive `contains("my own goal")` is meaningful. Its stated
  isolation purpose is not what it checks.

- `breadstuffs/node/src/finality_gate.rs:229` `admits_semantics` — REAL but trivial (HashSet
  membership of a pure predicate; no consensus claimed — correctly scoped, listed for completeness).

---

## 3. The FULLNESS-SIM verdict + ranked sims to build

### Verdict: there is NO synthetic sim exercising the real fullness. Blunt.

What "sim" coverage exists is one of two kinds, neither of which is a fullness sim:
1. **Hand-built static DAGs evaluated once** (`finality_gate.rs`, `blocklace/ordering.rs`,
   `multi_node_convergence.rs`) — a single snapshot of an ideal round-synchronous graph, checked
   for ordering/agreement. No rounds over time, no load, no failure injection (except the
   in-process partition/equivocate in `multi_node_convergence.rs`, which is delivery-choice, not a
   fault injector).
2. **Two real 3-process federation tests** (`three_node_ordering_rule.rs`, `sustained_finality.rs`)
   — the closest thing to a sim, and genuinely real over the wire — but they run the HAPPY PATH
   (all nodes up, clean, loopback), inject NO failure/partition/Byzantine behaviour, and do not
   assert finality by default.

Nothing simulates, as a passing test:
- a real n-node federation reaching finality under node-failure / partition — NO.
- N tenants attaching + driving agents concurrently with isolation held — NO.
- an adversarial tenant trying to escape / exfil / over-spend in a live sim — NO (the adversarial
  tests are all in-process single-shot units: the exfil test at `dregg-agent/src/session.rs:738`
  is real and strong but sequential; the workload forged-charge sim at
  `DreggNet/tests/workload/.../multi_tenant_isolation.rs` is `#[ignore]`).
- the finality / A1 path under concurrent load — NO.

It is isolated units + happy-path seeds. The fullness is unsimulated.

### Ranked sims to BUILD (highest load-bearing first)

1. **Real multi-node consensus-under-failure sim.** Extend `three_node_ordering_rule.rs`'s real
   binary-spawn harness (it already exists and works) into a chaos driver: fix the gossip
   dissemination leg so finality converges by default, then inject (a) kill a node mid-round and
   assert the remaining supermajority still finalizes + the restarted node catches up to the same
   attested root; (b) a real network partition (drop QUIC between two groups) + heal, assert
   safety held and liveness resumed; (c) a Byzantine validator that sends conflicting blocks to
   different peers over the real wire, assert equivocation detection + slash through the RUNNING
   node (today detection and slash are tested separately — court evidence is hand-fed at
   `equivocation_court_service.rs:831`). Make `DREGG_TEST_REQUIRE_FINALITY=1` the default once the
   dissemination leg lands. This closes G1, and the failure/Byzantine/restart legs at once.

2. **Multi-tenant concurrent-attach isolation sim.** Spawn N tenants that attach + drive agents
   concurrently (real threads/tasks, not sequential) against the attach store and session layer;
   assert every tenant's receipts/budgets/sessions stay disjoint under the race, and specifically
   exercise the documented under-lock quota re-check (`DreggNet/attach/src/store.rs:152-157`) and
   the meter's concurrent-same-key claim (`dregg-agent/src/meter.rs:224-227`). Closes G2 + G5.

3. **Adversarial-tenant sim.** A hostile tenant, in a live (not unit) setting, attempting: cross-
   tenant session read/fork, budget over-spend via a concurrent race, forged-owner in the request
   body (`dreggnet-attach.rs:241`, `resolve_subject`), a spoofed `X-Dregg-Subject` (G7), and — once
   the jail is wired — a real jailed process attempting to read operator keys / egress
   (`agent-host/src/isolation.rs`) and a real forced-command shell breakout over sshd (G3). Assert
   every attempt is refused with no state change. Un-`#[ignore]` and fold in the workload
   forged-charge suite. Closes G3 + G7 + the adversarial half of G2.

4. **Finality-under-load / A1-under-load sim.** Drive many concurrent finalized turns through
   `execute_finalized_turn` with real competing writers hitting touched cells during the off-lock
   window, asserting the DECLINE-to-install branch (`blocklace_sync.rs:4028-4038`) actually fires
   and the durable commit is withheld — the race the A1 guard exists to defeat. Closes G4.

---

## 4. Credit where due (the genuinely real, biting, non-vacuous tests)

- **The two real 3-process federation tests** (`three_node_ordering_rule.rs`,
  `sustained_finality.rs`) — real binaries, real QUIC, honest about the open finality leg. Rare
  and valuable.
- **The circuit differentials INJECT divergence and prove non-vacuity.**
  `breadstuffs/circuit/tests/ir2_denotational_differential.rs` (3043 lines) plants a structural
  violation and asserts the Lean denotation and deployed `Ir2Air::eval` disagree on the planted
  drift (`enumerator_catches_gate_on_one_row_divergence` `:1886`, forged-membership `assert_ne!`
  `:1929`); `effect_vm_descriptor_exhaustive_differential.rs` injects one violation per reject case
  (`:650`) with a coverage assert that fails if any reject path is unexercised. These run FRI-free
  in normal CI. Teeth bite.
- **The red-team / tamper teeth bite.** Anti-ghost circuit tooth
  (`effect_vm_record_root_anti_ghost.rs:190-197`, `prove(...).is_err()` on a tampered fields_root);
  selector-gate forgery (`effect_vm_selector_gate_forgery.rs:213-217`, forged foreign-tail debit is
  UNSAT); site-bundle byte-tamper (`DreggNet/gateway/tests/console_surfaces.rs:128-134`,
  `ContentRootMismatch`); merge-receipt forge (`DreggNet/umem/tests/two_replica_merge.rs:239-241`,
  `rewitness().is_err()`).
- **The cap-auth PoP login IS end-to-end over real TCP.** `DreggNet/webauth/tests/login_flow.rs`
  spawns the real `webauth::server::serve`, gets a real server-minted challenge, signs with the
  real bearer key, POSTs, gets a real session — with forged-issuer/expired/revoked/wrong-account/
  stale-challenge/wrong-cap/subject-spoof all covered (`:162-322`). The deployed sandstorm cap rail
  (`webauth_rail.rs:189-305`) is real `dga1_` ed25519 with a full adversarial suite; the signed
  23 MB `.spk` is really parsed + tamper-rejected (`real_spk_fixture.rs`).
- **The A1 off-lock unblock is real** (`blocklace_sync.rs:5831`, `multi_thread` runtime, real
  `execute_finalized_turn`, height 0→1) — it just doesn't stage the concurrent race.
- **The equivocation-under-consensus property is real** at the engine level
  (`multi_node_convergence.rs:329-406`: fork detected order-independently, evidence retained,
  auto-evicted, anchors nothing, honest nodes still agree) — it's the in-process/ideal-DAG caveat
  that keeps it from being a fullness sim.
- **The dregg-agent security suite is genuinely adversarial and non-vacuous** (accept AND reject
  polarities): operator-key exfil refused (`session.rs:738`), hosted-shell refused at parse
  (`:676`), credential forge/attenuate/expiry (`cred.rs:950-1022`), federation quorum
  liar-detection (`federation_qa.rs:604-800`), the budget forge-detectors (`budget.rs`), harness
  secret-never-leaks (`harness.rs:560`). The extension is real-unit-tested for its crypto/parsing/
  login-contract helpers (BLAKE3 golden vectors, SSE, mnemonic) — though its runtime service-worker
  / powerbox-grant / wasm surface is untested.
- **The durability / exactly-once / crash-resume tests are real** (`control/tests/
  settlement_durable.rs` double-charge teeth; `webapp/tests/durable_request_resume.rs` real crash
  mid-request→resume; `persistent_servers.rs` no-re-bill-on-reconstruct + Σδ=0).
- **The status honesty-law suite is real** (unreachable→Unknown-never-green, Rust/Lean divergence
  downs the federation, XSS-escape) — over fixtures, but the logic is genuine and source-agnostic.

---

## Appendix — the through-line

The pattern is consistent across all five surfaces: **prove the rule, skip the run.** The rule
(consensus ordering, cap lattice, receipt chain, circuit descriptor, budget algebra) is tested
with real crypto, real engines, biting teeth, both polarities. The RUN — many parties, over time,
under failure, against an adversary, racing for a resource — is either simulated in one process
over an ideal input, or gated behind an env var / feature / `#[ignore]` that keeps it out of the
default signal. The four sims in §3 are the missing half: they take the harnesses that already
exist (the real 3-node spawn, the attach store, the A1 guard, the exfil unit) and drive them at
fullness.

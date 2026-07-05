# TEST-RIGOR — the agent runtime + the public cloud

An honest, grounded audit of what the DreggNet cloud (`gateway` / hosting / `storage`
/ `billing` / `durable` / `control` / `webapp`) and the agent runtime
(`~/dev/breadstuffs/dregg-agent`, surfaced in-cloud by `agent-host` + `attach`) actually
test — and, sharply, what they *don't*, what they *fake*, and whether a synthetic sim
exercises the real fullness end-to-end.

*Dated 2026-06-30. Read-only audit; every claim is grounded to `file:line` at HEAD.
Verify against HEAD before acting — line numbers drift.*

## TL;DR — the honest verdict, both ways

**The good, and it is genuinely good.** This is *not* a repo of green-but-hollow tests.
The unit / integration / e2e suites are real where it is cheap-enough to be real:
real on-disk SQLite crash-resume across a genuine `process::abort()` and a *second*
process (`webapp/tests/durable_request_real_restart.rs`), real HTTP servers over real
TCP (`webapp/tests/{site_publish_serve,verified_read_http}.rs`,
`gateway/tests/live_wireup.rs` spawns the *shipped binary*), the real dregg
Poseidon2 heap-root crypto (`umem` depends on `dregg-cell` **non-optionally** — the
fork / time-travel tests commit against the real kernel commitment), real KVM microVM
execution with a clean self-skip on macOS (`exec/tests/microvm_kvm.rs`), a real
Postgres verified store with **raw-SQL tamper teeth** (`durable/tests/verified_store_pg.rs`),
and adversarial negatives nearly everywhere (RBAC refusals in `org/tests/teams.rs`,
cross-tenant refusals in `attach/`, forged-receipt teeth in `storage/`). **No vacuous
(`assert!(true)` / no-panic-only) tests were found in scope.** The `tests/workload/`
sim is real enough to have *found and fixed a real double-charge race* under concurrent
settlement (`durable/src/settle.rs:267`, BASELINES §"Bug surfaced").

**The gap, and it is load-bearing.** Everything that would cost real money, a real
model, or a real chain to exercise is mocked at the boundary and the *real* path runs
only in a gated / `#[ignore]`d lane that CI never runs:

1. **The real economy never settles in any default/CI test.** Every test (including the
   whole workload sim) settles on `ConservingLedger` — an in-process `HashMap` twin
   explicitly labeled "the faithful twin of a dregg `Payable`" (`durable/src/settle.rs:212`).
   The *real* on-chain conserving `Transfer` (the `dregg-verify` / `dregg-conserve` /
   `pg-dregg` lanes) is off-by-default and its only real-node/real-pg tests are
   `#[ignore]`d + env-gated (`bridge/tests/verified_read_live.rs`,
   `durable/tests/verified_store_pg.rs`).
2. **The real Stripe earn leg is a self-signed offline oracle.** The test signs the
   webhook with the same secret it verifies against (`dregg-agent/src/stripe.rs` tests);
   the live Stripe CLI leg (`CliStripeSkills::{provision,pay}`) is never exercised — only
   `RecordedStripeSkills`. No test proves a real dollar can arrive.
3. **The real model HTTP runs only under a non-default feature.** The default build is
   100 % `RecordedOpenAICaller`; the live transport is exercised only under
   `--features live-brain` (a hermetic localhost server — real, but not a real provider)
   or the `#[ignore]`d real-Moonshot test.
4. **Many in-scope crates' (real, good) tests are not in the default gauntlet** —
   `storage`, `org`, `status`, `attach`, `billing`, `agent-host`, `umem`, `gateway` are
   *not* in `scripts/test.sh`'s `SERVICE_CRATES`, so `make test` / CI never runs them.
5. **The fullness sim exists but is gated out, twin-settled, stub-computed, and never
   run long.** It is the right shape and a real asset, but it is not wired to the real
   dregg-agent runtime, not run against the real economy, and its 8 h soak (the one that
   would catch the *known* unbounded-map leak it documents) has never been run.

So: **the loop is well-tested on twins; the real edges (money in, model in, chain out)
are named, gated, and unexercised.** That is the classic "green ≠ the real thing works"
surface, and it sits exactly on the funding / settle / verify path.

---

## 1. Coverage gaps — real (non-test) paths with no meaningful test

Ranked by how load-bearing.

### G1 — the real on-chain settlement / conservation path (CRITICAL)
Every settlement in every runnable test goes through `ConservingLedger`, an in-process
`HashMap<(asset,holder), i64>` twin (`durable/src/settle.rs:212–259`). The real dregg
`Payable` / `Effect::Transfer` conserving move (`durable/src/conserve.rs`, the
`dregg-conserve` lane) is `#[cfg(feature = "dregg-conserve")]` and off by default
(`durable/src/conserve.rs:98`); the "byte-identical to the substrate" cross-check the
comment promises only runs under that feature (`conserve.rs:142`). The real light-client
verified read against a live node exists only as `bridge/tests/verified_read_live.rs`
(`#[ignore]`, gated on `DREGGNET_LIVE_NODE`, `scripts/test.sh:59`). **No default/CI test
ever exercises a real conserving transfer or a real on-chain settle.** The economy's
soundness in CI rests entirely on the twin matching the real thing — which is asserted
nowhere that runs.

### G2 — the real earn (Stripe) path (CRITICAL for a business)
The "earn" rail (`dregg-agent/src/stripe.rs`) is a self-signed oracle: `StripeWebhook::sign`
+ `StripeMirror::verify` share the secret. The real Stripe webhook / API is never hit.
The live payout/provision leg (`CliStripeSkills`, `dregg-agent/src/stripe_skills.rs:210+`)
shells real CLIs but is never run by a test — `RecordedStripeSkills` (labeled, honest)
stands in. There is no test — anywhere, gated or not — that a real payment clears into a
mint. The whole "a business earns real money" leg is unexercised.

### G3 — the live agent brain driving the real loop (HIGH)
The default build never makes a real model call. `LiveOpenAICompatCaller` is exercised
only under `--features live-brain` (`dregg-agent/src/brain.rs:1731`, a hermetic localhost
server — genuinely real HTTP + header/redaction/fail-closed assertions, credit due) and
the real-provider call is `#[cfg(feature="live-brain")] #[ignore]` (`brain.rs`, "hits the
live Moonshot API"). CI green tells you nothing about a real model driving the confined
loop.

### G4 — the gateway against a real dregg node (HIGH)
`gateway/tests/live_wireup.rs` spawns the *real shipped binary* over real TCP (excellent),
but points it at a hand-rolled **stub** dregg node (`spawn_stub_node`, line 60). No test
drives the gateway's funding decode against a real chain. Combined with G1, the entire
gateway → chain funding-authority path is twin/stub-only.

### G5 — in-scope crates excluded from the default gauntlet (HIGH, cheap to fix)
`SERVICE_CRATES` (`scripts/test.sh:21`, `Makefile:16`) is
`cli durable exec bridge control webapp ops`. **Not** included: `storage`, `org`,
`status`, `attach`, `billing`, `agent-host`, `umem`, `gateway`. Their tests are real and
good (see §4) but `make test` / the macOS CI job never runs them — they can rot green.
`umem` is especially notable: it holds the *only* real-Poseidon2-crypto tests and does
not run in the gauntlet.

### G6 — the cross-repo business run (HIGH — see §5)
Nothing wires the real `dregg-agent` runtime (breadstuffs) to the DreggNet cloud as one
run: earn (Stripe) → fund a lease → operate (the agent's metered/receipted loop) →
spend (dispatch to compute) → settle → verify. The two repos are tested in isolation.

### G7 — true concurrency in the orchestrator (MEDIUM)
The workload sim's driver ticks the loop synchronously: dispatch + settle complete
*within one tick*, so `max_inflight` is observed as **0** in every scale run (BASELINES
§5.1). The `capacity_bound` / "in-flight bounded" SLOs therefore never bite — they are
vacuous against this in-process driver. Real queue-depth / backpressure under a truly
async fleet is unmeasured. The one place real concurrency *is* exercised is the racing-
settle scenario against the ledger mutex (§5.4) — and that found the double-charge bug.

### G8 — long-run / leak behavior (MEDIUM, with a known latent bug)
The endurance soak defaults to **20 s** (BASELINES §5.6). The 8 h overnight window has
never been run. BASELINES itself documents an **unreaped orchestrator `workloads` map
that grows without bound** and would blow RSS over 8 h — the exact failure the soak is
built to catch, latent and unfixed because the soak is never run long enough to fail.

### G9 — durable resume at real scale / on pg (MEDIUM)
`durable/tests/durable_resume.rs` is a real on-disk SQLite crash-resume with a real
budget-exhaustion negative — solid. But the pg variant (`durable_resume_pg.rs`) and the
verified store (`verified_store_pg.rs`) are `#[ignore]` + `DATABASE_URL`-gated; CI runs
neither. The workload durability scenario (§5.5) parks 12 workflows and hit SQLite
`database is locked` backoff (~1 s/workflow) — a real concurrency limit surfaced but not
resolved.

---

## 2. Fake tests — green that doesn't mean the real thing works

Category legend: **vacuous** / **mock-not-real** / **tautological** / **happy-only**.
A mock-not-real on the verify / budget / funding / settle path is the worst.

| # | test (file:line) | category | why fake / what it fails to exercise | severity |
|---|---|---|---|---|
| F1 | the entire economy under `ConservingLedger` — `durable/src/settle.rs:212,261`; consumed by **all** of `control/tests/*`, `tests/workload/*`, `webapp`/`storage` hosting-billing | **mock-not-real** | Settles on an in-process `HashMap` twin, not the real dregg `Payable`/`Transfer`. Conservation, exactly-once, meter==settle are proven *on the twin*. The twin==substrate equivalence is asserted nowhere that runs (`dregg-conserve` off by default). Green here ≠ the real chain conserves. | **CRITICAL** |
| F2 | Stripe earn — `dregg-agent/src/stripe.rs` tests `a_genuine_signed_webhook_mints_conserved_credit`, `a_webhook_retry_is_refused`, `a_forged_signature_webhook_is_refused` | **mock-not-real** + partly **tautological** | The test signs the webhook with the same secret it verifies against (`StripeWebhook::sign(&body, SECRET,…)` → `verify` under `SECRET`) — the happy case is circular. The forged-body / wrong-secret negatives *are* real teeth (non-vacuous, credit). But the *real* Stripe boundary (a webhook actually from Stripe, a real API call) is never touched. Money-in is untested. | **CRITICAL** |
| F3 | Stripe payout/provision — `RecordedStripeSkills` used in tests; `CliStripeSkills` (`dregg-agent/src/stripe_skills.rs:210`) never run | **mock-not-real** | The live leg shells real `stripe` CLIs; no test runs it. Honestly labeled ("never fakes a live success") — so not deceptive, but the real spend/provision path is uncovered. | HIGH |
| F4 | the agent's default-build brain — `dregg-agent/tests/standalone.rs` (all `RecordedOpenAICaller`), `dregg-agent/tests/session_repl.rs` (real binary, recorded responses) | **mock-not-real** | Real loop / cap-gate / budget / receipt are exercised (good), but the model is canned. No real model reasons in any default test. Mitigated by the `live-brain` hermetic transport test (§4). | HIGH |
| F5 | `gateway/tests/live_wireup.rs::shipped_binary_admits_funded_…` — real binary, **stub** node (`spawn_stub_node`, line 60) | **mock-not-real** | Real HTTP + real binary (credit), but the chain that "funds" the lease is a hand-rolled stub. The funding-authority-from-a-real-chain path is not exercised. | HIGH |
| F6 | `tests/workload/tests/scale_load.rs` `capacity_bound` + the plan's "in-flight bounded" SLO | **vacuous (artifact)** | The in-process driver dispatches+settles in one tick, so `max_inflight` is always 0 (BASELINES §5.1); the SLO `max_inflight <= fleet×cap` can never fail. It asserts a bound that the driver structurally cannot violate. | MEDIUM |
| F7 | `tests/workload/tests/multi_tenant_isolation.rs::check()` returns `SloResult::todo(...)` (lines 43–59) | **decorative** (not vacuous — the real asserts are in the body) | The `check()` SLO table is placeholders; the substantive isolation asserts live in the test body and are real. But note the "isolation" is enforced by the *twin* ledger's per-holder debit + the bridge funded-gate — the plan admits (`multi_tenant_isolation.rs:12–15`) the real cap/holder crypto binding "lives in the dregg lease cell … here it is modelled by these two gates." So cross-tenant isolation is tested against a *model* of the enforcement, not the real cap crypto. | MEDIUM |
| F8 | `tests/workload/tests/durability.rs` pg variant | **skipped-clean** | SKIPS when `DATABASE_URL` unset (the norm); the real-pg durable population is never run in practice. Honest skip, but the pg fullness is uncovered. | MEDIUM |
| F9 | the six workload scenarios are `#[ignore]`d and out of `SERVICE_CRATES` | **out-of-gauntlet** | Real bodies, but `make test` / CI never runs them; only a manual `make test-workload` does. A regression in the sim (or what it guards) won't fail CI. | MEDIUM |

No `assert!(true)` / no-assertion / pure-no-panic tests were found in scope — a real
credit. The "fakeness" here is uniformly *mock-not-real at a boundary*, not vacuity.

---

## 3. Genuinely-real tests — the solid floor (credit where due)

These exercise a real boundary and carry real negatives; they are the parts you can trust.

- **Real process crash-resume.** `webapp/tests/durable_request_real_restart.rs` — spawns
  a child via `process::Command`, the child `process::abort()`s (a genuine ungraceful
  crash), a *second* process resumes from the on-disk SQLite store and the handler/meter
  run **0** times (replayed, not re-executed, not double-charged). This is the real
  exactly-once guarantee, really.
- **Real HTTP over real TCP.** `webapp/tests/site_publish_serve.rs` +
  `verified_read_http.rs` (real `TcpListener`/`TcpStream`, 404 negatives, a **tampered
  served byte → `ContentRootMismatch`** tooth); `gateway/tests/live_wireup.rs` +
  `no_free_compute.rs` (spawns the shipped binary, admits funded / **refuses unfunded**,
  fails closed with no funding source).
- **Real kernel crypto.** `umem` depends on `dregg-cell` non-optionally
  (`umem/Cargo.toml:39`); `umem/tests/two_replica_merge.rs`,
  `storage/tests/umem_buckets_fork_timetravel.rs`,
  `webapp/tests/umem_sites_fork_timetravel.rs`,
  `control/tests/umem_servers_mesh_fork_timetravel.rs` all commit/fork/restore against
  the real Poseidon2 `compute_heap_root`.
- **Real Postgres with tamper teeth.** `durable/tests/verified_store_pg.rs` (gated) —
  raw-SQL inflation of a chain row / balance row / a deleted chain tail each caught by
  `revalidate()`/cross-check (`is_err()`). Real anti-substitution.
- **Real KVM microVM.** `exec/tests/microvm_kvm.rs` — real CPython in Firecracker,
  self-skips cleanly on macOS, and a **refuse-without-KVM** negative.
- **Real durable SQLite crash-resume + budget teeth.** `durable/tests/durable_resume.rs`
  — real duroxide + real WAT execution, exactly-once across a crash, budget-exhaustion
  negative.
- **Real adversarial unit teeth.** `storage/tests/{receipt_chain_verify,roundtrip}.rs`
  (bad-signature / broken-link / cross-bucket-cap / over-budget), `org/tests/teams.rs`
  (a dense RBAC negative battery: viewer-write / cross-org-cap / stranger-invite /
  cannot-remove-owner refused), `attach/tests/*` (cap-gate refusal, tampered receipt,
  cross-tenant session isolation), `agent-host/src/lib.rs` (shell-cap refused at enrol,
  quota exceeded), `control/tests/trusted_root_anchor.rs` (unfinalized / rolled-back /
  wrong-anchor-root all refused).
- **The real live transport, hermetically.** `dregg-agent/src/brain.rs:1731`
  (`--features live-brain`) — real `reqwest` over real TCP to a local OpenAI-compatible
  server; asserts the configured base is honored, the key rides *only* the Authorization
  header (never the body), and a dead endpoint fail-closes.
- **The workload racing-settle scenario** (`economy_under_load.rs` §5.4) — 12 800
  concurrent settles on 200 keys against the real ledger mutex; **found the double-charge
  race** now guarded at `durable/src/settle.rs:267`. A real win from a real concurrency
  test.

---

## 4. The fullness-sim verdict — do we have a real end-to-end business sim?

**Partly. The scaffold is real and valuable; the fullness is not yet real.**

### What exists
`tests/workload/` (`dreggnet-workload`) is a genuine multi-tenant load harness
(`docs/WORKLOAD-TEST-PLAN.md`, `BASELINES.md`). It drives the **real** `Orchestrator`
loop, the **real** durable SQLite layer (§5.5), real `BackendRegistry` health/failover,
and samples conservation every tick. Six scenario classes are filled in (not empty
skeletons — BASELINES shows a real calibrated run happened):
- **5.1 scale** — 1 000 leases, fleet sweep {1,2,4,8}, ~2 800–3 000 settles/s.
- **5.2 multi-tenant isolation** — 50 tenants, 3 adversarial cross-tenant vectors refused.
- **5.3 failure injection** — backend-down / partition / node-down / settler-restart /
  lease-lapse, each with a recovery assertion.
- **5.4 economy under load** — 200 tenants, the racing-settle that found the double-charge.
- **5.5 durability** — 20 workflows, 12 parked + crash-resumed exactly-once on real disk.
- **5.6 endurance soak** — steady churn, RSS/fd/task/store sampling → Prometheus.

This is real, well-built work and covers multi-tenant, scale, and failure-injection *in
shape*.

### The gap (why it is not yet "the real fullness")
1. **Twin-settled, not chain-settled.** Every scenario settles on `ConservingLedger`
   (§F1). The sim proves the *loop + twin* conserves, not the real economy.
2. **Stub-computed.** The compute backend is a loopback `:8021/fulfill` stub
   (`tests/workload/src/backends.rs`) running a 2-step demo meter — **not** the real
   agent brain, not a real exec/microVM run. The "workload" is a fixed arithmetic stub.
3. **Not the real agent runtime.** Nothing in the sim runs the breadstuffs `dregg-agent`
   loop. The sim's "tenant workload" and the actual agent runtime are disjoint.
4. **No earn leg.** No Stripe / funding source in the sim — leases start pre-funded on
   the twin. There is no "earn real money → fund → operate → spend → settle → verify"
   run anywhere.
5. **Isolation is modeled, not crypto-enforced** (§F7) — the cap/holder binding is stood
   in by the twin's per-holder debit + the bridge funded-gate.
6. **Concurrency is single-ticked** (§G7) — `max_inflight` is structurally 0.
7. **Never run long** (§G8) — 20 s default; the 8 h soak that would catch the documented
   unbounded-map leak has not been run.
8. **Gated out of CI** (§F9) — a fullness regression won't fail the gauntlet.

**Verdict:** we have a real *load-simulation scaffold for the control loop over twins*,
which already earned its keep (the double-charge bug). We do **not** have a synthetic sim
that exercises the *real* fullness — real money in, real model, real compute, real
chain-out — as one repeatable business run.

---

## 5. Ranked sims to build (the fullness we're missing)

1. **The one-business run (cross-repo), real edges.** A single repeatable sim: a real
   (test-mode) Stripe payment → mint → fund a lease → the **real** `dregg-agent` loop
   operates (metered, cap-gated, receipted) → dispatches to a **real** exec backend
   (wasm tier, runs everywhere) → settles → a light-client **verifies** the receipt
   chain end-to-end. This is the single highest-value sim: it closes F2, F4, F5, G3, G6
   in one artifact and answers "can a stranger's dollar become verified work?"
2. **The real-economy variant of the whole workload suite.** Run the six scenarios with
   `--features dregg-conserve` (and, gated, `dregg-verify` / `pg-dregg`) so at least one
   nightly settles on the **real** conserving substrate, not the twin — and assert the
   twin's numbers match the substrate's (closes F1, G1). Even one scenario nightly kills
   the "twin ≈ substrate is asserted nowhere" gap.
3. **Wire the workload sim into CI as a smoke lane, and run the 8 h soak weekly.** Add a
   small-N `make test-workload-smoke` to the gauntlet (closes F9) and a scheduled 8 h
   soak that will *fail* on the documented unbounded `workloads` map — forcing the reap
   fix (closes G8). Then add G5: put `storage/org/status/attach/billing/agent-host/umem`
   into `SERVICE_CRATES` so their real tests actually run.
4. **Adversarial multi-tenant with the real cap crypto.** Re-run §5.2 with the real dregg
   lease-cell cap/holder binding (not the modeled gates) so a forged cross-tenant cap is
   refused by the real crypto, not the twin (closes F7). A "malicious tenant" fault:
   forged caps, replayed webhooks, over-claimed budgets, a poisoned backend response.
5. **A truly-async fleet driver.** Replace the single-tick dispatch+settle with a real
   concurrent fleet so `max_inflight`/queue-depth are non-trivial and the capacity /
   backpressure SLOs actually bite (closes G7, F6). Then a scale run at N≫fleet×cap
   that must show bounded, recovering in-flight.
6. **A real Stripe integration test (gated).** Against Stripe test mode + a real webhook
   (or the CLI event forwarder): a real signed event → mint → the ed25519 receipt
   re-witnesses. Gated on a test key like the pg/node lanes (closes F2, F3, G2).
7. **Failure-injection with real processes.** Extend §5.3 to kill/restart real gateway /
   settler *processes* (as `durable_request_real_restart.rs` already does for one
   workflow) under load — not just flip an in-memory down-flag — to test real crash
   recovery of the live services at scale.

---

## Appendix — what runs where

- **`make test` (default gauntlet, `scripts/test.sh`):** `-p` = `cli durable exec bridge
  control webapp ops` only. Real: durable SQLite crash-resume, real-process restart,
  real-HTTP webapp/gateway-adjacent, real umem crypto (via deps), wasm exec. Twin: all
  economy. Excluded: `storage org status attach billing agent-host umem gateway`.
- **Gated lanes (skipped clean, never run in default CI):** `test-pg` (real Postgres,
  `#[ignore]`), `test-verify` (real dregg node via `bridge/tests/verified_read_live.rs`,
  `#[ignore]`), `test-net` (Linux net stack), `test-workload` (the sim, `#[ignore]`).
- **`dregg-agent` (breadstuffs, separate repo):** 150 tests; default build 100 %
  recorded brain + recorded Stripe; real transport only under `--features live-brain`;
  real Moonshot + real Stripe CLI never run.
</content>
</invoke>

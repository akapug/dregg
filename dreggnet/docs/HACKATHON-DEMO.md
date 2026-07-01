# DreggNet — Hermes Accelerated Business Hackathon

**Nous / NVIDIA / Stripe · "agents that earn, spend, run real operations"**

> An agent pays Stripe and gets **verifiable, durable, metered compute** — earn,
> spend, run, on a formally-verified rail. **Boundaries are theorems; every spend
> is a receipt.**

This doc is the demo package: (1) the runnable demo, (2) the video script,
(3) the submission writeup, (4) the honest scope (what's real vs narrated).

---

## 1. The loop (what we built)

```
  earn / hold        pay via Stripe         spend on a dregg          run durable
  value      ──────▶ (signed webhook  ─────▶ execution-lease  ──────▶ metered compute
                      → conserving           (resolve_pay,            on DreggNet
                      USD-credit mint)        Σδ = 0)                  (owned sandbox, crash-resumable)
  ▲                                                                        │
  └────────────────────────── a receipt + a meter you can verify ─────────┘
```

Two repos, one loop:

| half | repo | license | what it is |
|---|---|---|---|
| **dregg** | `~/dev/breadstuffs` | AGPL-3.0, public | the verified ocap **rail**: Stripe→mint, `resolve_pay`, the execution-lease, the meter |
| **DreggNet** | here | AGPL-3.0 | the **reality**: the metered, crash-resumable durable workload that actually runs |

dregg says *what was promised, paid, and owed* — verifiably. DreggNet *delivers it*.

---

## 2. Run it

```sh
# both halves, end to end (dregg payment rail + DreggNet durable exec)
demo/run-demo.sh

# just one half
demo/run-demo.sh --dregg-only       # the Stripe→mint→pay-lease rail (dregg tests)
demo/run-demo.sh --dreggnet-only    # the durable metered workload (dreggnet CLI)
```

The script labels every step `[REAL]` (a genuine code path runs) or `[NARRATED]`
(the autonomous-agent framing). It resolves a `dreggnet` binary (prebuilt → build →
docker), and runs the dregg half as the dregg crates' own tests against
`$BREADSTUFFS_DIR` (default `~/dev/breadstuffs`).

Two focused, visceral beats run on their own:

```sh
# A REAL Stripe event funds the agent. A local endpoint runs breadstuffs' genuine
# stripe_mirror verify+mint; a signed payment_intent.succeeded mints conserved credit.
demo/stripe-trigger.sh           # fixture: fully automated + offline (real verify+mint)
demo/stripe-trigger.sh --live    # prints the exact `stripe listen` / `stripe trigger` cmds

# Crash-resume, on camera: run a durable metered workload, SIGKILL it mid-flight,
# resume → step 1 replayed (not re-run), step 2 once, meter charged exactly twice.
demo/crash-resume.sh
```

A fully containerized DreggNet half (no local Rust toolchain needed):

```sh
docker compose up -d --build
docker compose run --rm dreggnet dreggnet-demo   # lease → run → status, metered
```

See `docs/RUN-LOCALLY.md` for the full Docker runbook.

---

## 3. Video script (target 2:00, hard cap 3:00)

Format: screen recording of `demo/run-demo.sh`, voiceover. Times are cumulative.

### Beat 0 — Hook (0:00–0:18)
**On screen:** the banner from `run-demo.sh`.
**VO:** "Agents are starting to earn and spend money. But when an agent pays for
compute, what does it actually *get*? Today: a promise and an invoice. We built the
other thing — an agent pays Stripe and gets compute it can *verify*: durable,
metered, and bounded by math. We call the rail **dregg**; the service that runs the
work is **DreggNet**."

### Beat 1 — A REAL Stripe event funds the agent (0:18–0:48)
**On screen:** `demo/stripe-trigger.sh` — the receiver starts ("listening on
…/webhook"), then a signed `payment_intent.succeeded` is fired and the endpoint
prints `✓ MINTED 2500 cents`, the real `Effect::Mint`, and the agent's running
credit; then a retry prints `✗ REFUSED … double-mint prevented` and a forged
signature prints `✗ REFUSED … forged or wrong secret`.
**VO:** "The agent pays with Stripe. A real, signed `payment_intent.succeeded` hits a
local endpoint — and that endpoint runs the substrate's *own* verification: it checks
Stripe's HMAC signature and mints exactly the paid amount as conserved USD-credit,
value-in-equals-value-out. Watch the guarantees on real events: Stripe *retries*
webhooks — the retry is deduped, no double-mint. A *forged* signature mints nothing.
This isn't a mock endpoint; it's dregg's real `stripe_mirror` verify-and-mint."
*(Live variant: `demo/stripe-trigger.sh --live` with `stripe listen` /
`stripe trigger` against your own test key — same code path, your key.)*

### Beat 2 — The spend (0:48–1:12)
**On screen:** ACT I/`service_economy` — the lease tests pass; highlight the
`stripe_payment_funds_an_execution_lease` line.
**VO:** "Now the agent *spends* that credit. It opens an **execution-lease** — an
on-substrate record of *who* may run *what*, at what isolation grade, for how much.
Funding it desugars to exactly one conserving transfer through the same `resolve_pay`
rail every dregg payment uses. And the kernel *enforces* the ceiling: a run past the
funded budget is refused by the executor — not by a check we remembered to write, but
by the verified rail itself."

### Beat 3 — The run (1:12–1:40)
**On screen:** ACT II — `dregg-cloud lease open`, then `dregg-cloud run` printing
`add(40,2)=42`, `*2=84`, and the meter; then `dregg-cloud status`.
**VO:** "DreggNet sees the funded lease and runs the workload — for real, in a wasm
sandbox, as a *durable* job. Each step charges the meter against the lease budget. And
if a tick would exceed the budget, the workload *lapses and is reaped* — no compute
runs that wasn't paid for."

### Beat 4 — The crash (1:40–2:15) — *the differentiator*
**On screen:** `demo/crash-resume.sh` — phase 1 prints the step-1 checkpoint and a
PID, then a big `💥 kill -9 <pid>`; phase 2 (a new process) prints
`step1 = 42 REPLAYED, not re-run [this process executed it 0 time(s)]`,
`step2 = 84 ran once`, and `meter charged (total) 2`.
**VO:** "Here's the part that matters for money. The meter is transactional — a charge
commits exactly when the durable checkpoint commits. So watch: we run the workload, it
checkpoints after step one… and we *kill it*. A real `kill -9`, mid-flight. Now a
brand-new process resumes from the on-disk checkpoint. Step one is *replayed* — it
never re-runs; the new process executed it zero times. Step two runs once. And the
meter is charged exactly twice — never three. A crash can't make you pay twice, and
can't lose work you paid for. Exactly-once, across a real crash."

### Beat 5 — The payoff (2:15–2:30)
**On screen:** the THE LOOP summary; `dregg-cloud status` meter.
**VO:** "Earn, spend, run. The agent paid Stripe and got verifiable, durable, metered
compute on a formally-verified rail. Boundaries are theorems; every spend is a
receipt. That's DreggNet."

> **Recording tips:** pre-build everything (`cargo build -p dreggnet-cli` in DreggNet;
> one warm `cargo build -p dregg-bridge` in breadstuffs; pre-build the receiver:
> `CARGO_TARGET_DIR=$BREADSTUFFS_DIR/target cargo build --manifest-path
> demo/stripe-receiver/Cargo.toml`) so every beat runs fast. `demo/stripe-trigger.sh`
> and `demo/crash-resume.sh` each run standalone in ~10s — record them as their own
> clips and cut together. Run with a wide terminal and a dark theme; the
> `[REAL]`/`[NARRATED]` tags and the `💥 kill -9` / `✓ MINTED` lines read well on
> camera. Beat 4 (the crash) is the strongest 30 seconds — give it room.

---

## 4. Submission writeup

### One-liner
**An agent pays Stripe and gets verifiable, durable, metered compute — earn, spend,
run, on a formally-verified rail.**

### Tweet-length
> Agents that *earn, spend, and run real ops*: an agent pays @stripe → we mint
> conserved credit → it opens a capability-bounded **execution-lease** → and gets a
> **durable, metered, crash-resumable** compute job on DreggNet. Boundaries are
> theorems; every spend is a receipt. Built on the formally-verified dregg substrate.

### Form-length (what it is / why novel / scope)

**What it is.** DreggNet is durable execution-as-a-service for agents, settled over
an open, formally-verified capability substrate (dregg). The loop: an agent pays via
Stripe; a signed webhook mints conserved USD-credit to the agent's dregg cell
(idempotent, conserving); the agent spends it opening + funding an **execution-lease**;
DreggNet fulfills the lease as a **durable, metered, sandboxed** workload (the owned
wasmi sandbox, wasm tier genuinely running today; native / firecracker tiers are
fail-closed seams — owned engines are future work). The meter charges per
step transactionally — charge commits with the durable checkpoint — so a crash
resumes within the same budget and an over-budget tick lapses → the workload is
reaped. No compute runs that wasn't paid for.

**Why it's novel.** Agent-payment demos usually stop at "the agent sent money."
Ours closes the loop to *verifiable execution*: the payment, the authorization
(an object-capability lease, not an API key), the metering, and the conservation are
all on a substrate with machine-checked soundness — a light client can't be fooled
about what was paid for or run. The economic guarantees are *enforced by the rail*,
not bolted-on checks: value is conserved (Σδ = 0), the budget ceiling is
executor-enforced, and metering is exactly-once across crashes (a DBOS-style
transactional outbox: charge ⟺ checkpoint). The honest line: **dregg's half is
verifiable; DreggNet's half is the operated, paid reality — neither claim outruns
the other.**

**Usefulness / viability / presentation (judging).**
- *Useful:* a real need — agents need compute that's metered, bounded, and durable,
  paid through rails they already use (Stripe). The lease is a clean primitive for
  "rent compute with a hard budget."
- *Viable:* the substrate is open + verified (the trustless rail); the operated
  infra is the moat that bills for real execution. Clear open-core revenue path.
- *Presentation:* one command runs the loop end-to-end; every step is labelled real
  vs narrated; the guarantees (conservation, idempotency, budget enforcement,
  crash-exact metering) are demonstrated as passing tests, not asserted.

---

## 5. Honest scope — real vs narrated

**Real (genuine code paths, each independently tested):**
- **Stripe → mint:** HMAC-signed webhook verification, replay-window check, currency
  + amount bounds, and a conserving `Effect::Mint` against verified-payment backing.
  Forged/tampered webhooks are refused; retries + sibling `charge.succeeded` events
  are deduped on the payment-intent id (no double-mint).
  (`breadstuffs/bridge/src/stripe_mirror.rs`)
- **Mint → pay-lease:** the minted USD-credit pays an execution-lease through the
  same `resolve_pay` rail, desugaring to exactly one conserving `Transfer` (Σδ = 0).
  (`stripe_payment_funds_an_execution_lease` test)
- **The lease:** open → fund → metered run; the funded ceiling is **executor-enforced**
  (a run past it is refused by the kernel, not by app code).
  (`breadstuffs/sdk/src/service_economy.rs`)
- **The durable workload:** `dregg-cloud run` genuinely executes `add(40,2)=42` then
  `*2=84` in the owned wasmi sandbox, through control → bridge → durable → exec.
  (`cli/`, `bridge/`, `durable/`, `exec/`)
- **The meter:** each durable step charges against the lease budget; an over-budget
  tick lapses the workflow → the machine is reaped (no unpaid work). Crash-resume is
  exactly-once (charge ⟺ checkpoint, idempotent on `(lease_id, period)`), proved over
  a Postgres-backed store in the durable crate's resume test.
  (`durable/`, `docs/DBOS-DURABLE-LAYER.md`)
- **Crash-resume across a real process kill:** `demo/crash-resume.sh` runs the durable
  workload to its step-1 checkpoint, `SIGKILL`s the live process mid-flight, then a
  brand-new process resumes over the on-disk SQLite store. The fresh process executes
  step 1 *zero* times (it is replayed from the checkpoint), runs step 2 once, and the
  meter is charged exactly twice — proven, not asserted, with the binary exiting
  non-zero on any violation. This is a stronger statement than the in-process resume
  test: the in-memory ledger is wiped by the real crash, so a zero step-1 execution
  count in the resumed process is unfakeable evidence of exactly-once.
  (`cli/src/bin/crash-resume.rs`, `demo/crash-resume.sh`)
- **A real Stripe event over HTTP:** `demo/stripe-trigger.sh` runs a local endpoint
  (`demo/stripe-receiver/`) that calls breadstuffs' genuine
  `StripeMirrorState::mint_against_webhook` on each inbound webhook. A signed
  `payment_intent.succeeded` mints conserved USD-credit; a retry is deduped; a forged
  signature is refused — over real HTTP, not just an in-test struct. `--live` drives it
  with `stripe listen` / `stripe trigger` against the operator's own test key.
  (`demo/stripe-receiver/src/main.rs`, `demo/stripe-trigger.sh`)

**Narrated / scoped (honest seams):**
- **The "fully autonomous agent"** is the wrapper. The demo drives the real code
  paths in a scripted narrative; there is no LLM agent in the loop deciding to pay
  and rent. The pieces it would call are real.
- **Two repos, scripted together.** dregg and DreggNet are separate repos (both
  AGPL-3.0); the demo is a script driving both, not one binary. On the
  DreggNet side the lease is a plain struct **mirroring** the dregg `LeaseTerms`
  rather than read from a live dregg node — reading a real funded lease over a light
  client is the named next step (`bridge/src/dregg_verify.rs`). The dregg-side test
  (`stripe_payment_funds_an_execution_lease`) is where the two are stitched on the
  verified side.
- **Live Stripe.** The verify+mint code is the real thing and now runs behind a real
  HTTP endpoint (`demo/stripe-trigger.sh`). The default (fixture) run self-signs the
  exact HMAC + JSON shape Stripe sends and POSTs it locally; the `--live` run forwards
  genuine Stripe test events via `stripe listen` / `stripe trigger`. The only operator-
  supplied piece is the live Stripe test key (the `whsec_…` signing secret); the path
  the event travels is identical either way. (The receiver is a demo integration tool
  that links the AGPL `dregg-bridge` to run its genuine `stripe_mirror`; it is a
  standalone, workspace-excluded crate so the DreggNet product never links
  dregg — the "two repos, scripted together" boundary holds.)
- **Sandbox tiers.** Only the wasmi sandbox tier is wired into exec today; the
  stronger grades (native+seccomp+landlock, firecracker microVM) are mapped in the
  bridge's `map_cap_grade` but not yet linked.
- **The gateway** (fly.io-compatible machines API over httpe) is a tested handler
  library, not yet a socket-bound server (`docs/RUN-LOCALLY.md` "Deferred").

Nothing in the video claims more than the corresponding code runs.

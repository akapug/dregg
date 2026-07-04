# Hermes Agent Accelerated Business Hackathon — the winning demo + integration plan

**NVIDIA × Stripe × Nous Research** — *"agents that can earn, spend, and run real
operations at any scale."*

This is the build plan for the demo we should ship. It is grounded in code that
exists at HEAD (every claim cites the file); the "new glue" section is small and
honest. Companion docs: `docs/HACKATHON-DEMO.md` (the earn→spend→run→crash-resume
loop already written), `docs/VISION-AGENT-WORLD.md`, `docs/PROVABLE-AGENT-LABOR.md`.
Verify any file:line against HEAD before relying on it.

---

## 1. The pitch

> **The autonomous business you can audit.** An agent running Hermes (on Nemotron,
> NemoClaw-guarded) that **earns** — provides a service, gets paid via Stripe, and the
> payment is verified + minted as conserved credit and *receipted*; **spends** — buys
> the SaaS / compute it needs through a Stripe spend that is **cap-bounded** (it can
> only pay vendors it was granted) and **budget-drawn** (the dollar comes out of a
> ceiling it *physically cannot exceed*, by construction, not by a watchdog) and
> *receipted*; and **operates** on the dregg cloud — runs the actual work in a metered,
> crash-resumable sandbox — at **any scale**: fork the agent and the budget + authority
> *attenuate* to each sub-agent, provably narrower, never wider. At the end it hands you
> one **cryptographic proof of everything it did and a hard bound on everything it could
> have done**, re-verifiable by anyone, offline, trusting no host.

**The differentiator, stated sharply.** Every team at this hackathon will build an agent
that *can* earn and spend via Stripe and *can* run Hermes. The capability is table
stakes by Saturday. What no one else will have is the **trust layer that makes it
deployable**: ours is the only agent whose earning, spending, and operating is

- **cap-bounded** — every action is checked against an attenuable `dga1_` credential
  *before* it runs; a vendor / service / cell outside the grant is refused, no receipt
  (`dregg-agent/src/agent.rs::run_inner`, the `Credential::verify` gate ≈ line 1026);
- **budget-rate-limited by construction** — every spend draws from a `ReplenishingBudget`
  cell whose `check_draw` rejects an over-ceiling draw *in-band* before the work commits
  (`dregg-agent/src/budget.rs:348`); the un-drawn headroom is a hard ceiling on
  everything the agent *could still have done* (`AgentRunReport::headroom`,
  `agent.rs:512`). This is a theorem about the cell, not a counter someone remembered to
  check;
- **cryptographically receipted** — every admitted action (and the verdict/amount bound
  into it) seals into a prev-hash-linked, ed25519-signed chain that a non-witness
  re-verifies end to end with `verify_agent_run` (`agent.rs:622`) — a forged "I paid $5"
  or "the tests passed" breaks the signature (`receipt.rs:307`).

NVIDIA wants agents that run business *safely*; Stripe wants agents that *spend*; Nous
wants Hermes *operating* it — and our confinement + proof is the missing piece that lets
a real company hand an autonomous agent a **credit card and a deploy key** and sleep at
night. Autonomy and safety are one primitive: the same budget cell + capability +
receipt chain that let the agent *act* are what *bound and prove* it. **The leash is the
grant.**

---

## 2. The concrete demo — "Acme Test-as-a-Service, run by an agent"

A judge watches one terminal. The agent runs a tiny automated service business: it
takes a job (run a customer's test suite), does the work on Hermes/Nemotron + the dregg
compute tier, charges the customer via Stripe, pays for the compute/SaaS it used via
Stripe, and the **entire P&L is one receipt chain you can re-verify**.

### What the judge sees, beat by beat

**Beat 1 — EARN (a real Stripe event funds the agent).** `demo/stripe-trigger.sh` fires
a signed `payment_intent.succeeded`. The local receiver
(`demo/stripe-receiver/src/main.rs`) runs breadstuffs' **genuine**
`StripeMirrorState::mint_against_webhook` (`bridge/src/stripe_mirror.rs:547`) — HMAC-SHA256
verify, replay window, amount/currency bounds, double-mint dedup — and mints exactly the
paid cents as conserved USD-credit into the agent's dregg cell. On camera:
`✓ MINTED 5000 cents`, the real `Effect::Mint`, the running credit. Then a Stripe
**retry** prints `✗ REFUSED … double-mint prevented` and a **forged signature** prints
`✗ REFUSED`. *This is the agent's revenue, and it is conserved and receipted — not a
number in a database the host can edit.*
→ **earn = receipted Stripe-in** (`stripe_mirror.rs`, the mint path; LIVE, tested).

**Beat 2 — OPERATE (the brain does the work, confined).** The agent is deployed with a
budget cell + a cap bundle (`AgentCloud::deploy`, `agent.rs:906`). Its brain is **Hermes
on Nemotron** (`OpenAICompatBrain::with_base(... "https://integrate.api.nvidia.com/v1",
"nvidia/…-nemotron-…")`, `brain.rs:486`). The model reasons → emits a tool-call →
`run_tests` runs the customer's suite in the real owned wasmi sandbox
(`exec/src/agent_toolkit.rs::SandboxToolkit::with_run_tests_in`). Every tool-call is
cap-gated, budget-drawn, and the verdict is **bound into the receipt** — and the
compute-tier tool binds a `WitnessedRun` `(command · code_root · result)` so a verifier
can later re-execute it and confirm *these tests ran on this code with this result*
(`toolkit.rs::run_tests_verdict`, `agent.rs::verify_witnessed_qa` ≈ line 764). The agent
*cannot claim a green it did not run.*
→ **operate = the cloud cells + the witnessed toolkit** (LIVE on the local owned-sandbox path).

**Beat 3 — SPEND (the agent pays its vendor, bounded).** Having earned the fee and done
the work, the agent pays for the compute/SaaS it consumed via a Stripe spend. This rides
the same `invoke` rail as a **budget-gated spend tool** (`stripe_pay`, the one piece of
new glue, §3): the call is cap-gated (`invoke:stripe_pay` must be in the bundle), the
**dollar amount is drawn from the budget cell** so it is impossible to overspend the
ceiling, and the payout is receipted. On camera the agent tries to spend more than its
ceiling and the meter **refuses it in-band** — the `BudgetRefused` outcome, headroom 0
(`agent.rs::ActionOutcome::BudgetRefused`, the `Meter::draw` gate ≈ line 1049). *The
agent has a credit card it provably cannot max out past what you funded.*
→ **spend = budget-gated, receipted Stripe-out** (new glue over the existing rail).

**Beat 4 — SCALE (fork the agent, attenuate the budget).** The agent spins up a
sub-agent for a spiky sub-job: `deploy_subagent` (`agent.rs:929`) opens a **child budget
attenuated off the parent** (the meter refuses a child asking for a larger ceiling or
faster refill — `budget.rs::attenuate`, `agent.rs::AgentError::Widen`) and a child
credential genuinely attenuated off the parent's real cap chain (the no-amplify lattice).
On camera: the child runs to its narrower ceiling and stops; a child trying to invoke a
vendor the parent never held is refused up front. *Scale out without ever widening the
blast radius.*
→ **scale = fork + attenuate, both axes** (LIVE, tested:
`a_subagent_attenuates_and_cannot_exceed_the_parent`).

**Beat 5 — PROVE (the whole P&L re-verifies, the WOW).** `dregg-agent verify run.json`
re-witnesses the entire run with no trust in the host: the receipt chain is intact and
signed (`verify_chain`), consumption never exceeded the ceiling (the bound holds), the
proof and the bound agree, and the headroom report shows the hard limit on everything the
agent *could have done but didn't*. We tamper one line (flip a "paid $5" or a "tests
passed") and re-run: `BadSignature`, caught. **The judge sees a complete autonomous
business — money in, work done, money out, scaled — and a one-command audit a stranger
can reproduce offline.**
→ **prove = `verify_agent_run` + `verify_witnessed_qa`** (LIVE, tested).

### The one-sentence wow

> The agent earned real money via Stripe, spent real money within a budget it **provably
> could not exceed**, ran the work in a metered sandbox, forked a sub-agent that **could
> not out-reach its parent** — and here is the cryptographic audit of every dollar and
> every operation, which you can re-verify yourself without trusting us.

### Capability → our primitive (the map judges will remember)

| Capability | Our primitive | Status |
|---|---|---|
| **earn** | receipted Stripe-in: `stripe_mirror::mint_against_webhook` → conserved `Effect::Mint`, receipted | LIVE, tested |
| **spend** | budget-gated Stripe-out: `stripe_pay` tool over the `invoke` rail, amount drawn from the budget cell, receipted | new glue (§3.2) |
| **operate** | the cloud cells + witnessed toolkit (`run_tests`/`check_health`/`verify_deploy`), verdict bound in receipt | LIVE on owned-sandbox path |
| **scale** | `deploy_subagent` — budget + cap attenuation, no-amplify on both axes | LIVE, tested |
| **prove** | `verify_agent_run` + `verify_witnessed_qa` — re-witness, host untrusted; headroom = could-have bound | LIVE, tested |
| **safely** | cap-gate + in-band budget refusal + NemoClaw guard composed (§3.4) | LIVE braid; NemoClaw = stretch |

---

## 3. The integration plan — wiring the hackathon stack into `dregg-agent`

The agent runtime is already provider-agnostic and engine-agnostic by design: the brain
takes any OpenAI-compatible base URL + model (`brain.rs`), and the compute tools take an
*injected runner* (`toolkit.rs::RunFn`). So most of "integration" is **configuration +
one new tool**, not new substrate.

### 3.1 Nemotron 3 Ultra — the brain's model

The brain already drives any OpenAI-compatible chat/tool-use endpoint via
`OpenAICompatBrain::with_base(task, services, cells, key, base, model, caller)`
(`brain.rs:486`) and a real HTTP transport behind the `live-brain` feature
(`LiveOpenAICompatCaller`, `brain.rs:340`). NVIDIA serves Nemotron over an
OpenAI-compatible API (NVIDIA NIM / `integrate.api.nvidia.com/v1`), so the wiring is:

```rust
let key   = ProviderKey::from_env("nvidia", "NVIDIA_API_KEY")?;     // BYO, confined
let brain = OpenAICompatBrain::with_base(
    task, services, cells, key,
    "https://integrate.api.nvidia.com/v1",                          // --llm-base
    "nvidia/llama-3.1-nemotron-ultra-253b-v1",                      // --llm-model (per NIM catalog)
    LiveOpenAICompatCaller::new(),                                  // live-brain feature
);
```

No code change to the runtime — a `--llm-base` / `--llm-model` flag and a key in the
brain's pocket (the key reaches *only* the provider seam; it is redacted in `Debug` and
proven never to leak into a request body / receipt / report —
`brain.rs::ProviderKey`, the `the_byo_key_never_leaks` tooth). If the NIM endpoint is
rate-limited during judging, the identical brain points at a local vLLM/NIM container
(`http://localhost:8000/v1`) — the recorded-transport and live-mock-server tests already
prove a configured base is honored end to end.

### 3.2 Stripe Skills — the earn + spend rails through the budget gate

**Earn (LIVE).** `demo/stripe-receiver/src/main.rs` already runs the genuine
`stripe_mirror` verify+mint over real HTTP. For the demo we add one line: on a successful
mint, **fund the agent's budget cell** with the minted cents (denominate the budget in
USD-cents so the budget ceiling *is* the dollar ceiling). The mint is already conserved +
deduped + forged-rejected; we are just routing the credit into the agent's allowance.

**Spend (the one new primitive).** Register a Stripe payout/charge as a **priced tool**
on the existing `invoke` rail:

```rust
let toolkit = Toolkit::new()
    .with_run_tests_in("run_tests", "wat", suite, CapTier::WasmSandbox)   // operate
    .with_priced_tool("stripe_pay", |args, cells| {                       // spend (NEW)
        // args: {vendor, amount_cents}. Returns a ToolOutcome carrying the priced amount.
        stripe_payout(args)   // the Stripe API call (or a recorded stand-in for the demo)
    });
```

The only genuinely new code is a **variable-amount draw**. Today `run_inner` draws the
flat `handle.cost_per_action` per action (`agent.rs` ≈ line 1049). The spend tool needs
the draw to be the tool's *price* (`amount_cents`) so the budget cell is the dollar
ceiling. `BudgetState::check_draw` already accepts an arbitrary `amount`
(`budget.rs:348`) — so this is a small, honest extension to the run loop: a priced
`Invoke` draws its price, an over-ceiling price is refused **before the Stripe call
happens** (no money moves), and the amount is bound into the receipt. This is the cleanest
expression of "an agent with a credit card it cannot max out." (Internal dregg-side
spend — paying a dregg execution-lease — already works via `resolve_pay → Effect::Transfer`,
the `stripe_payment_funds_an_execution_lease` thesis test in `stripe_mirror.rs:980`; the
new tool is the *outbound Stripe* face of the same idea, behind the cap+budget gate.)

### 3.3 Hermes — the model / skills / the confined harness

Two integration depths, both real:

1. **Hermes-as-model (fast path).** Hermes is served as an OpenAI-compatible endpoint
   (Nous / a local serve); point `with_base` at it exactly as Nemotron. The same
   cap+budget+receipt braid wraps it unchanged. This is the path the
   `dregg-agent/tests/standalone.rs` hackathon proof already exercises with a recorded
   Hermes-shaped transport.
2. **Hermes-as-harness (deep path).** `deos-hermes/` already confines the *real*
   Nous Hermes agent over ACP: every Hermes tool-call hits the proven `ToolGateway`
   (`deos-hermes/DESIGN.md` §2) — admitted → a receipted turn, refused → an in-band
   `Reject`. The `HermesAgentPeer<B: LlmBrain>` runs the brain loop over the same ACP
   wire shapes. For the demo, the fast path is enough; the deep path is the "and it works
   with the *actual* Hermes runtime, confined" credibility slide.

### 3.4 NemoClaw — safe-running, composed (defense in depth)

NemoClaw / NeMo Guardrails guard **what the model says** (content safety, jailbreak,
topical rails) — a filter on the I/O of the LLM. dregg bounds **what the model can do**,
provably — cap (reach), budget (spend), receipt (record). They compose as orthogonal
layers, and the composition is the story:

- NemoClaw sits on the brain's request/response (the `OpenAICompatCaller` seam in
  `brain.rs`, or in front of the NIM endpoint) and can refuse/rewrite an unsafe
  generation.
- dregg sits on the *action*: even a generation NemoClaw passed cannot touch a vendor,
  spend a dollar, or reach an endpoint outside the cap bundle, and cannot exceed the
  budget — and whatever it *did* do is receipted. The `deos-hermes` ACP gate is the exact
  point where a NemoClaw verdict and the dregg gate stack into one allow/deny.

Pitch line: *NemoClaw makes the model safe to talk to; dregg makes the agent safe to
deploy — and proves it.*

### What's already done vs the new glue (honest)

- **Done (LIVE, tested):** the runtime (budget·cap·receipt braid, `agent.rs`), the
  provider-agnostic brain incl. live HTTP (`brain.rs`), the witnessed toolkit
  (`toolkit.rs`) + the owned wasmi sandbox injection (`exec/src/agent_toolkit.rs`), sub-agent
  attenuation, `verify_agent_run` / `verify_witnessed_qa`, the Stripe verify+mint earn
  path (`stripe_mirror.rs` + `demo/stripe-receiver`), federation-attested QA
  (`federation_qa.rs`).
- **New glue (small, reachable):** (a) the priced/variable-amount spend tool + draw
  (§3.2); (b) point the brain at the NIM/Nemotron base (config); (c) fund the budget cell
  from the minted credit (one line); (d) a thin `dregg-agent` demo binary that runs the
  scenario and emits `run.json` (§4); (e) NemoClaw compose (stretch).

---

## 4. The build checklist — ranked to a winning demo

The target is **"the wow in one command"**: a judge runs one script and sees earn →
operate → spend (bounded) → scale → verify, with a tamper-caught audit at the end.

1. **The demo binary + the one-command script (do first).** `dregg-agent` is a *library*
   today (no bin; the CLI lives in DreggNet as `dregg-cloud agent deploy/verify`). Add a
   thin `examples/business.rs` (or a `dregg-agent business` bin) that: deploys an agent,
   funds it from a (fixture) Stripe mint, runs the brain over the toolkit, does a bounded
   `stripe_pay`, forks a sub-agent, and writes `run.json`; plus `dregg-agent verify
   run.json`. Wrap it as a new `demo/business.sh` (mirror `demo/run-demo.sh`'s
   `[REAL]`/`[NARRATED]` labelling). This is the spine everything else hangs on; build it
   against the **recorded** brain transport first so it is deterministic and offline.

2. **The budget-gated Stripe-out spend tool (the differentiator primitive).** Implement
   the priced/variable-amount draw (§3.2): a priced `Invoke` draws its `amount_cents` from
   the budget cell, over-ceiling refused in-band before the payout, amount bound into the
   receipt. Add the teeth: an over-budget spend is `BudgetRefused`, a forged amount breaks
   the signature. **This is the single most important new code — it is the "credit card it
   cannot max out" beat.**

3. **Earn → fund the budget cell (close the loop).** On a successful mint in
   `demo/stripe-receiver`, fund the agent's budget cell with the minted cents (budget
   denominated in USD-cents). Now the demo is a closed P&L: revenue in raises the ceiling,
   spend draws it down, headroom is the provable bound.

4. **Point the brain at Nemotron (live, behind a flag).** Wire `--llm-base
   https://integrate.api.nvidia.com/v1 --llm-model nvidia/…-nemotron-…` + `NVIDIA_API_KEY`
   through the `live-brain` transport, with a one-call smoke test (the existing
   `live_transport_honors_a_configurable_base_url_end_to_end` mock-server test is the
   template). Keep the **recorded** transport as the deterministic default for the
   filmed run; `--live` flips to Nemotron. Fail-closed if the endpoint is down (already
   proven: `live_transport_fails_closed_on_a_dead_endpoint`).

5. **Sub-agent fork on camera.** Add the `deploy_subagent` beat to the script: the child
   runs to its narrower ceiling and a widening child is refused. Already LIVE — this is
   wiring it into the demo narrative, not new code.

6. **NemoClaw compose (stretch / slide).** Put NeMo Guardrails in front of the NIM
   endpoint (or on the `OpenAICompatCaller` seam) and show one beat where NemoClaw refuses
   an unsafe generation *and* one beat where dregg refuses an unsafe *action* NemoClaw let
   through — the two-layer defense. If time-boxed out, keep it as the architecture slide
   in the writeup (§3.4).

7. **Polish for the 2-minute video.** Reuse `docs/HACKATHON-DEMO.md`'s recording
   discipline: pre-build everything, wide dark terminal, the `✓ MINTED` / `BudgetRefused`
   / `BadSignature` lines read well on camera. The strongest 30 seconds is **Beat 3
   (the bounded spend) + Beat 5 (the one-command tamper-caught audit)** — give them room.

### Reachability note

Items 1–5 are all reachable from HEAD with no new substrate — they are a demo binary,
one small run-loop extension (the priced draw), and configuration. The runtime, the
Stripe verify+mint, the toolkit, attenuation, and verify are already built and tested.
The honest seams we *do not* hide: the live NIM call needs a key + network (recorded
transport is the deterministic fallback); the Stripe *payout* leg uses a recorded
stand-in unless an operator supplies live Stripe keys (the verify+mint *earn* leg is the
genuine code path either way); full operator-independence of the witnessed work is the
federation/in-circuit residual already named in `PROVABLE-AGENT-LABOR.md`. Nothing in the
demo claims more than the code runs.

# DreggNet — the next killer product

*The product bet, grounded in what shipped. `docs/VISION.md` paints the category
(the Verifiable Agent Cloud + three bold bets); this doc answers the sharper
question underneath it: **what does a user/dev/org actually pay for, and tell their
friends about?** Read this for the WEDGE; verify any LIVE/seam claim against HEAD
before relying on it. Companion grounding: `docs/VISION.md`,
`docs/LIFTOFF-SURPASS-MATRIX.md`, `docs/PERMISSIONLESS-CLOUD-PLAN.md`,
`docs/DEVNET-ROADMAP.md`, `docs/RECEIPT-CONTRACT.md`,
`docs/REPLENISHING-BUDGET.md`, `docs/SANDSTORM-INTEGRATION-PLAN.md`,
`docs/IPFS-INTEGRATION-PLAN.md`.*

---

## 0. What just shipped (the anchor — read this, don't fantasize past it)

The Verifiable Agent Cloud stopped being a slide and became a command. At HEAD,
`dregg-cloud agent deploy` runs end-to-end on the safe-autonomous path:

- **`dregg-cloud agent deploy`** (`cli/src/main.rs:1168`) deploys an agent with (a)
  a **replenishing-budget cell** — a spend ceiling that refills lazily at a rate, so
  a runaway is *rate-bounded by construction*, not by a watchdog (`exec/src/budget.rs`,
  the `Meter` trait `exec/src/meter.rs`); (b) a **cap bundle** — an attenuable
  `dga1_` ed25519 credential, powerbox-style (`webauth/`); and it runs a confined
  plan where **every action is cap-gated, metered, and receipted** (an ed25519,
  prev-hash-linked chain). It prints a *proof* (the receipt chain) and a *bound* (the
  hard ceiling + the headroom it never touched). `--subagent` deploys an attenuated
  child (half the budget, a narrower service list).
- **The agent toolkit** (`exec/src/agent_toolkit.rs`) — the self-verifying ops/coding
  agent's hands: **`run_tests`** (runs a test workload in a sandbox tier, line 178),
  **`verify_deploy`** (re-witnesses a deployed result via
  `webapp::verify_site_bundle`, line 156), **`check_health`** (probes a
  `HealthSnapshot` — consensus divergence, conservation breach, liveness — line 108),
  plus `verify_receipts` / `run_workload`. **Each tool's verdict is bound into the
  signed receipt** — the agent cannot *claim* a green test it did not run.
- **`dregg-cloud agent verify`** (`cli/src/main.rs:1310`) — runnable verify-don't-
  trust: re-witnesses the stored run's receipt chain (`receipt::verify_chain`),
  confirms consumption stayed under the hard ceiling, prints the signer key. No trust
  in the operator.
- **The brain is a seam.** `PlannedBrain` (a fixed action list, safe-autonomous) is
  wired today behind the `AgentBrain` trait (`exec/src/agent.rs:222`). A **real LLM
  brain** (the `deos-hermes` BYO-key loop) is the named **reviewed-go** substitution
  behind the same seam — *not yet wired at HEAD*. (No Kimi/Moonshot at HEAD; the
  brain port is real and the model that drops into it is an integration + a go-live,
  not new substrate.)

Around it: **`dregg-cloud verify`** trustless reads, **IPFS** (`dregg-ipfs/`) — blake3
content commitment *is* a CIDv1, so a published object is fetchable + re-witnessable
from any node, plus the merge-runtime delta transport; **Sandstorm**
(`sandstorm-bridge/`) — a real `.spk` parser (Ed25519+xz), grain=cell, powerbox=cap;
and a **live n=4 federation** (`edge`, `node-a`, `node-b-lean`, `node-b-rust` —
two share a fault domain today, `docs/MORNING-REVIEW.md`).

**The one-sentence what-is:** *you can hand an autonomous agent a budget and a
capability, and get back a cryptographic proof of everything it did and a hard bound
on everything it could do.* That sentence is now a CLI, not a pitch. The product
question is which slice of it a stranger pays for first.

---

## 1. The question this doc answers

Not "what's the category" (that's `docs/VISION.md`). The question is: **what is the
single thing a developer tries on a Tuesday, pays for by Friday, and posts about?**
A category does not get bought; a wedge does. The wedge has to be (a) a pain someone
has *today*, (b) reachable from HEAD in weeks not quarters, and (c) something **only
dregg can do** — otherwise it is a feature, not a moat.

---

## 2. The candidates — buyer × wedge × moat × distance-from-HEAD

A flat read of the six candidates (the prompt's five + the swarm-as-a-product), each
graded for how short the path is from what shipped in §0.

| Candidate | Buyer | The wedge (the Tuesday try) | Why ONLY dregg | Distance from HEAD |
|---|---|---|---|---|
| **Proof-of-QA / verifiable CI-CD agent** | Eng teams + platform/security leads adopting AI coding/ops agents who *can't trust the agent's word* | "Drop in our agent; it tests + deploys + verifies + monitors, and emits a proof anyone can re-run that the QA actually happened — inside a hard spend cap." | The QA verdict is **bound into a tamper-proof receipt** (`agent_toolkit.rs` → signed chain), re-witnessable trustless (`agent verify`); spend is **rate-bounded by construction** (`budget.rs`); blast radius is **cap-bounded** (`webauth`). No log scraper can fake the proof. | **Shortest.** The toolkit (`run_tests`/`verify_deploy`/`check_health`), the budget, the cap, and `agent verify` *exist*. Remaining: a real brain (reviewed-go), real tool wiring, a shareable proof artifact. |
| **Verifiable agent marketplace** | Orgs hiring autonomous agents/services; builders monetizing an agent | "List your agent; others hire it escrow-bonded; it's paid only on a proof-of-work-done." | Escrow + proof + cap + budget are **one substrate**; the powerbox makes the hire a *provable* delegation; federation means cross-operator hiring **without a shared chain**. | **Medium.** Needs the escrow-release-on-receipt loop (`SealedEscrow` × the receipt), a catalog (Sandstorm path), and the merge-runtime for offchain coordination. The category Proof-of-QA grows into. |
| **Verifiable agent swarms** (productize *this* swarm) | Teams running fleets of cap-bounded agents on a big task (the dregg-build swarm, as a product) | "Run a swarm where each agent is budgeted, capped, and receipted, composing under one parent budget." | The `--subagent` attenuation + the Stingray budget split (`REPLENISHING-BUDGET.md` §3) make N children settle without contending the parent — *provably* bounded composition. | **Medium-far.** Seed exists (`--subagent`); the orchestration surface + the composition proof story are the build. Beautiful, but a harder first sale than one agent in one CI. |
| **Trustless multi-tenant SaaS** | SaaS operators wanting "we literally cannot see/tamper with tenant data" as a sellable property | "Run your app; each tenant is a cell; you prove isolation + honest billing." | Per-tenant cap partition + verifiable billing + trustless reads — isolation is a *theorem*, not a policy. | **Far / platform.** A horizontal platform, not a wedge — rides *on top of* a won wedge. |
| **deos desktop-as-a-cloud** | Prosumers / power users wanting a live, malleable, cap-secured workspace | "Inhabit a reflective cockpit hosted + metered like any grain." | The reflective cockpit (breadstuffs) as a served, cap-secured surface. | **Horizon.** Inspiring, large, not a first paying user. |
| **Compute markets on the escrow-bond** | B2B compute buyers/sellers wanting slashable-stake trust-minimized capacity | "Provider bonds slashable stake; consumer's posting rate is cap-bounded." | `SealedEscrow` + `StandingObligation` + cap-bounded posting (`REPLENISHING-BUDGET.md` §4). | **Medium-far.** The B2B face of the marketplace; same primitives, later. |

Read the table top-down: the distance column collapses to one answer. **Proof-of-QA
is the only candidate where the differentiating machinery already runs at HEAD** —
the others need a new loop, a catalog, or a platform. So that is the bet, and the
marketplace is the category it earns its way into.

---

## 3. The bet — "Proof-of-QA": the agent whose work you don't have to take on faith

### The product, in one line

> **A coding/ops agent that tests, deploys, verifies, and monitors — and hands you a
> cryptographic proof that the QA actually happened, inside a hard budget you set.
> Anyone can re-run the proof offline. The agent cannot lie, and it cannot overspend.**

### Who pays, and why now

The buyer is the engineering team — and specifically the platform/security lead — at
any shop now putting an AI coding or ops agent into a real pipeline. The pain is
acute and *brand new in 2026*: an autonomous agent says *"I ran the tests, they
passed, I deployed, it's healthy."* You have its word and a log it wrote itself. You
cannot tell a genuine green run from a confident hallucination, you cannot bound what
it spent, and you cannot bound what it touched. Every team adopting agents hits this
wall the first time an agent confidently reports success on work it skipped.

They pay because the alternative is *don't ship the agent* (lose the speedup) or
*ship it on trust* (carry the risk). Proof-of-QA removes the dilemma: the agent's
claims become **receipts a third party re-verifies**, its spend becomes a **ceiling
that refills at a rate**, and its reach becomes a **capability you attenuated**. That
is a budget line a security lead can sign — it converts "trust the agent" into "audit
the agent," which is the difference between a pilot and production.

### The wedge — the Tuesday try

A dev points the agent at a repo and a deploy target with a budget and a cap:

```
  dregg-cloud agent deploy --repo . --budget 5.00/day --cap deploy-only,one-site
    │
    ▼ the agent (brain behind the AgentBrain seam) plans + acts, each step:
    │    run_tests      → real suite runs in a sandbox tier; verdict → signed receipt
    │    verify_deploy  → re-witnesses the deployed bytes against the published cell
    │    check_health   → probes the live HealthSnapshot; anomaly → flagged + receipted
    ▼ every action cap-gated · metered (drawn from the budget) · receipted
    ▼ output: the live URL + a RECEIPT CHAIN + the budget headroom it never touched

  dregg-cloud agent verify <run>          # anyone, offline, no trust in the operator
    │
    ▼ ✓ receipt chain intact · actions re-witnessed (tamper-evident, budget/cap-bounded)
    ▼ ✓ the declared tests ran against the deployed code with the declared result
    │     (run_tests' verdict is bound to a re-witnessed TIER EXECUTION — command +
    │      code_root[==deployed root] + result — not the agent's say-so;
    │      verify_witnessed_qa re-executes the bound and a mismatch is ✗)
    ▼ ✓ consumed 2.10 / 5.00 — stayed under the ceiling · signer <pubkey>
```

The "post about it" moment is the second command: a reviewer who *was not there* runs
`agent verify` and gets a precise, bounded proof — **a tamper-evident,
budget/cap-bounded, tier-witnessed proof that the declared tests ran against the
deployed code with the declared result** — plus a number proving it stayed in budget.
It is *not* a claim that the tests are good (whether a suite is meaningful is never
provable — Layer 4); it is a proof the QA *happened, on the deployed code, as
recorded*. That is a screenshot. It is also a CI gate, a compliance artifact, and a
reason to trust the next, bigger autonomy.

### Why ONLY dregg can do this (the moat — four primitives, one substrate)

Every "AI agent in CI" product can run tests and print a log. None can make the log
**unfakeable, bounded, and re-witnessable by a stranger**, because that needs all
four of these at once, and they are the *same substrate*:

1. **The verdict is bound to a witnessed execution, not a claim.** Three layers,
   each stronger:
   - *tamper-evidence* — `run_tests`/`verify_deploy`/`check_health` bind their
     result into an ed25519, prev-hash-linked chain (`exec/src/agent_toolkit.rs`);
     `agent verify` re-witnesses it with no operator trust (`receipt::verify_chain`).
     A forged verdict breaks the signature.
   - *boundedness* — every action is metered + cap-gated (points 2–3).
   - *execution-witnessing* — `run_tests`'s verdict carries a `WitnessedRun`
     binding `(command · code_root · result)`: the test command, a commitment to
     the code it ran (the `code_root`, **tied to the deploy's `content_root`** so
     the tests provably ran on the *deployed* code), and the result (exit +
     output digest). `verify_witnessed_qa` (`exec/src/agent.rs`) **re-executes the
     bound `(command, code_root)` in the compute tier and a mismatch is ✗** — so a
     lying runtime that records a verdict its execution does not produce is caught.
   A self-written log is trust-me; this is verify-me down to *the substrate ran
   these tests on this code with this result*. *This is the moat — the others are
   the fence around it.*

   **The honest residual (Layer 3, not yet closed).** The re-execution still runs
   in the *same compute substrate*, so today this proves "the substrate ran these
   tests" — it does not yet make the tier run independent of the operator who owns
   the substrate. Full operator-independence needs the tier run *itself* attested
   by the federation / light client — the in-circuit execution witness (breadstuffs
   `circuit/` + `metatheory/`, the VK-epoch). That is the named seam, owned by the
   circuit-soundness lane (point 4); the DreggNet side binds `(command, code_root,
   result)` and re-witnesses it up to that boundary. And **Layer 4 — whether the
   tests are *meaningful* — is never claimed and never provable.**
2. **The spend is bounded by construction.** The budget is a replenishing-budget cell
   (`exec/src/budget.rs`): consumption is metered against a ceiling that refills at a
   rate, so a stuck or adversarial agent is *rate-bounded* — the cap on damage is a
   property of the cell, not a monitor that has to fire in time.
3. **The reach is a capability, not a key.** The agent holds a `dga1_` attenuable
   credential (`webauth/`), not your root token: deploy-only, one-site, time-boxed.
   A confused or compromised agent cannot exceed the authority you handed it, and a
   third party can *witness exactly* what authority that was.
4. **It is all anchored to a light-client-unfoolable rail.** `verifyBatch accept ⟹ ∃
   genuine kernel transition` (breadstuffs `CircuitSoundness.lean`) — the proof is
   not "the operator says so," it is anchored to a finalized committee checkpoint on
   the n=4 federation.

A trusted CI host *cannot* offer (1) by construction — it would have to prove its own
honesty to itself. That is the category gap, applied to the one workflow every team
is anxious about right now.

### The nearest-reachable MVP (the honest path from HEAD)

Four steps, in order, each named with its seam. The first three are weeks of braid,
not new engines; the fourth is the reviewed-go go-live.

1. **A real brain behind the `AgentBrain` seam** (`exec/src/agent.rs:222`). Swap
   `PlannedBrain` for the `deos-hermes` BYO-key loop so the agent genuinely plans
   against a repo. *Seam: reviewed-go* (BYO-key, an outbound-LLM call) — the port is
   real; the model dropping in is an integration + a go-live, not substrate.
2. **Wire the toolkit to a real pipeline.** `run_tests` runs the *actual* suite in a
   `Caged`/`MicroVm` tier; `verify_deploy` hits the *real* deployed URL; `check_health`
   probes *real* control-plane metrics (rides the C2 observability work,
   `docs/DEVNET-ROADMAP.md`). The tool *shapes* exist; this points them at production.
3. **Ship the proof artifact + the badge.** Finish receipt adoption (C3,
   `docs/DEVNET-ROADMAP.md`: `verify_chain` is producer-only today) so a run emits a
   sealed, shareable manifest, and **print the `agent verify` command after every
   deploy** (CRITIQUE-PRODUCT: the most compelling property is currently invisible at
   the surface). A green badge + a one-command re-verify is the share moment.
4. **First wowed user.** A team running an AI coding agent in CI who wants a
   tamper-proof record that the agent's claimed tests + deploys really happened, under
   a hard spend cap. Give them: the agent, a budget, a cap, and `agent verify` in
   their PR check. The first time their reviewer re-runs the proof and it goes green
   without trusting anyone, they tell a friend.

**Named seams to carry honestly** (caveat lifetime = the burn-down, not a parking
lot): the brain is mock today (real LLM = reviewed-go); `content_root` is an FNV
stand-in until the Poseidon2 `Effect::Write` flip (`docs/STAND-INS-CENSUS.md`,
D-VERIFY-FLIP); the receipt crate is ~40% adopted (C3); and the n=4 federation has
two nodes in one fault domain until lassie lands true f=1.

---

## 4. The category it grows into — the Verifiable Agent Marketplace

Proof-of-QA is the wedge; it earns the right to the category. Once an agent's work is
a re-witnessable proof and its spend is a bounded cell, the same primitives make the
agent **hireable**:

> Deploy an agent as a service others hire — **escrow-bonded, paid on
> proof-of-work-done.** A buyer funds a `SealedEscrow`; the agent does the job under a
> cap; the escrow releases *only* against a receipt that proves the work; a dispute
> re-witnesses the same chain. The powerbox makes the hire a provable delegation, and
> the n=4 federation means two parties on *different operators* settle without a
> shared chain.

This is the network play, and it is the same four primitives as §3 plus two pieces
already in the tree: `SealedEscrow`/`StandingObligation` (`docs/REPLENISHING-BUDGET.md`
§4) for the bond, and the Sandstorm catalog (`sandstorm-bridge/`) as the listing
surface — *a catalog app is itself a cap an agent can be granted through the same
provable powerbox.* The merge runtime (`dregg-ipfs/` delta transport +
`SettlementSoundness.lean`) is what lets buyer and seller coordinate offchain and
settle only at the boundary. The B2B face of the same thing — providers bonding
slashable stake into a compute market — is the `Hellas`-shaped extension
(`docs/REPLENISHING-BUDGET.md` §4).

The marketplace is the destination; **do not build it first.** It needs a catalog, an
escrow-release loop, and the merge-runtime's first production path — all named, none a
wedge. Proof-of-QA ships the trust primitive (a proof of work done, under a bound) on
a workflow a single team buys alone; the marketplace is what that primitive becomes
when two parties who don't trust each other both hold it.

---

## 5. The through-line

`docs/VISION.md` says the unit of compute, account, and authority are one verified
object — a cell. This doc says: **the first dollar comes from the one workflow where
"I can't trust what the agent told me" is a wall a team hits this quarter.** Proof-of-
QA turns that wall into a one-command proof: the agent's QA is a receipt anyone
re-witnesses, its spend a ceiling that refills, its reach a capability you attenuated.
That is the shortest path from `dregg-cloud agent deploy` (shipped) to a developer who
pays — and it is the trust primitive the verifiable agent marketplace is built out of.

Build the proof artifact and the real brain; ship Proof-of-QA to one anxious team;
let the marketplace be the category it grows into. The wedge is a file in this tree;
the moat is the substrate underneath it.

---

*Dated 2026-06-30. Bold by intent, grounded by discipline: every reach names the
primitive (file:line) it stands on, and every seam names its burn-down. Verify any
LIVE/seam/file:line claim against HEAD before relying on it — the brain is mock at
HEAD, the real LLM and the live edge are reviewed-go.*

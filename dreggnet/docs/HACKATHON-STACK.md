# Hermes Agent Accelerated Business Hackathon — Integration Stack

> Research date: **2026-06-30**. Sources cited inline. These are **brand-new
> products** (announced 2026-06-16); some docs are thin and some surfaces are
> still maturing. Confidence is flagged per item. Verify against the live docs
> before depending on an exact command string.

We build on **`dregg-agent`** (`~/dev/breadstuffs/dregg-agent/`): an open-source,
cap-bounded / budget-bounded / receipted autonomous-agent runtime in Rust that
drives **any OpenAI-compatible model**. The brain seam is
`brain::OpenAICompatBrain` + the live HTTP transport `LiveOpenAICompatCaller`
(behind the off-by-default `live-brain` cargo feature); capabilities are reached
through `toolkit::Toolkit` (cap-gated + metered + receipted `invoke` tools).

---

## 0. The hackathon — requirements, judging, deadline (LEAD)

**Presented by:** NVIDIA AI × Stripe × Nous Research. Announced 2026-06-16.

- **⏰ Deadline: EOD Tuesday, 2026-06-30** (TODAY). Two-week window (Jun 16 → Jun 30).
- **Theme:** "builders making agents that can **earn, spend, and run real
  operations at any scale**." Winning shapes named in the announcement: a
  **fully automated company**, a **business framework**, or an **enterprise-
  function acceleration tool**.
- **Submission (all three steps):**
  1. Tweet a **1–3 minute demo video** tagging **@NousResearch** with a short writeup.
  2. Drop the link in the Nous **Discord** submissions channel (`discord.gg/nousresearch`).
  3. Complete the submission form: `typeform.com/to/hpEifIK4`.
- **Judging criteria:** **Usefulness · Viability · Presentation** — judged by
  Nous Research, NVIDIA, and Stripe.
- **Prizes (total ~$17,500 + 3× DGX Spark):**
  - 1st: $10,000 cash + NVIDIA DGX Spark + $5,000 Stripe credits
  - 2nd: $5,000 cash + NVIDIA DGX Spark + $3,000 Stripe credits
  - 3rd: $2,500 cash + NVIDIA DGX Spark + $1,000 Stripe credits
- **Required integrations:** NONE are mandatory — "participation in NVIDIA or
  Stripe services is **optional**." But the prize stack (Stripe credits, DGX
  Sparks) and the judging panel signal that using the **Stripe spend** + **NVIDIA
  stack** is what's rewarded.

> ⚠️ **Do not confuse** this with the **DEV Community "Hermes Agent Challenge"**
> (a separate, earlier, $1,000 *blog-post* contest started 2026-05-15, judged on a
> published DEV post). That is a different event. The hackathon we are entering is
> the NVIDIA × Stripe × Nous **business** hackathon with the tweet+Discord+typeform
> submission and the $17.5k/DGX prizes.

**Confidence: HIGH** on theme/prizes/submission/deadline (consistent across the
announcement, digg writeup, and multiple secondary reports). MEDIUM on the exact
Discord channel slug — verify the live invite.

---

## 1. Stripe Skills for Hermes — THE SPEND INTEGRATION (most important)

**What it is.** Not one product — it's a *suite* of Hermes **skills** (installable
SKILL.md bundles, see §5) that wrap **Stripe's agentic-payments CLIs**. Announced
2026-06-16 ("Hermes Agent now supports a full suite of Stripe skills. Your agent
can buy things, pay per-call APIs, and provision its own SaaS, with configurable
safety limits on every action."). Two concrete skills exist:

### 1a. `official/payments/stripe-projects` — provision + pay for SaaS

Wraps the **Stripe Projects CLI** (a Stripe CLI plugin). The agent provisions
real SaaS (Neon, Twilio, Vercel, …) in the *user's own* provider accounts,
generates credentials, syncs them, and records the resource.

- **Install:**
  ```
  hermes skills install official/payments/stripe-projects
  brew install stripe/stripe-cli/stripe      # macOS; Linux uses platform install
  stripe plugin install projects
  ```
- **Core CLI:**
  | Action | Command |
  |---|---|
  | Init | `stripe projects init` |
  | Browse | `stripe projects catalog` |
  | Provision | `stripe projects add <provider>/<service>` |
  | List | `stripe projects list` |
  | Upgrade tier | `stripe projects upgrade <provider>` |
  | Remove | `stripe projects remove <provider>` |
  | Rotate creds | `stripe projects rotate <provider>` |
- **Credentials:** auto-sync to `.env` (plaintext) + encrypted `.projects/vault/vault.json`.
- **Auth/billing:** tier prompts during `add`/`upgrade` are **real charges** and
  require user confirmation. The docs do **not** spell out an API-key/spending-
  limit model for this skill (gap). Gated to **Linux/macOS** during maturation.

### 1b. `official/payments/stripe-link-cli` — buy things / pay per-call APIs

Wraps **`@stripe/link-cli`** (Stripe **Link wallet for agents** + **Issuing**).
This is the "buy what it needs / pay for services it uses" surface.

- **Install:** `npm install -g @stripe/link-cli` (Node 20+), or `npx @stripe/link-cli`.
- **Payment methods:**
  - **One-time-use virtual cards** for web checkout forms.
  - **Shared Payment Tokens (SPT)** for merchants that return **HTTP 402**.
- **Auth flow:**
  ```
  link-cli auth status
  link-cli auth login --client-name "Hermes" --interval 5 --timeout 300
  ```
  Account created at `app.link.com`, payment methods at `app.link.com/wallet`.
- **Spend flow:** `link-cli payment-methods list` → create a spend request
  (amount in cents + merchant + line items) → **user approves in the Link
  app** (the agent **cannot self-approve**) → CLI polls → retrieve creds:
  `link-cli spend-request retrieve <lsrq_id> --output-file /tmp/link-card.json`.
- **Constraints:** **US-only**, Linux/macOS only, Node 20+. Approval gates every
  transaction; per-purchase spending limits are not documented for this skill
  (the *human-set budget/ruleset* model is described at the announcement level —
  "operates within a budget rather than asking permission per purchase" — but the
  Link-CLI skill itself enforces an explicit approval gate per spend).

> **Safety model (announcement-level):** real card never enters the agent's chat;
> a one-time payment code is used and deleted after purchase; the human supervises
> via **limits/rulesets set once**, not per-purchase approvals (this is the Stripe
> Issuing-for-agents / SPT delegated-authority story). The shipped `link-cli`
> skill currently enforces a stricter **per-spend approval** gate.

### How `dregg-agent` wires the spend

The Stripe spend is a **CLI/tool**, not an LLM endpoint — so it wires through our
**`toolkit`**, *not* the brain seam. Register a `stripe_buy` / `provision_saas`
tool via `Toolkit::with_tool(name, |cells| …)` that shells out to
`stripe projects add …` / `link-cli spend-request …`. It then inherits all three
guarantees for free (`toolkit.rs:1`):

- **cap-gated** — `invoke:stripe_buy` is refused unless the agent's bundle grants
  it (the model can't widen reach by asking);
- **metered** — each spend draws from the `ReplenishingBudget` cell → **our budget
  cell IS a cryptographic mirror of Stripe's spending limit**, but receipted;
- **receipted** — the spend's verdict (`lsrq_id`, amount, merchant, the
  `provision`'d resource) is bound into an ed25519 receipt; a forged "I paid $5
  not $500" breaks the signature (`verify_agent_run`).

**This is our headline differentiator:** the hackathon gives agents a *budget +
ruleset*; dregg makes every spend a **tamper-evident, re-witnessable receipt**
and gates the spend tool behind an **attenuable capability** — supervision by
*proof*, not just by limit. Frame the demo as "the agent earns/spends/provisions,
and every dollar leaves a verifiable receipt."

**Confidence: HIGH** that the two skills exist and the CLIs/commands are as quoted
(from the live Hermes docs). MEDIUM on the precise auth/spending-limit semantics
(docs are thin; the announcement and the shipped skill differ on per-purchase
approval). Verify the exact `link-cli` flags against the live skill before the demo.

---

## 2. Nemotron 3 Ultra (NVIDIA) — the inference model

**What it is.** NVIDIA's top reasoning model for long-running agentic tasks:
`nvidia/nemotron-3-ultra-550b-a55b` — 550B total / ~55B active params, hybrid
Mamba-Transformer (Nemotron-H) MoE, text-only, reasoning-capable.

- **Base URL (hosted, OpenAI-compatible):** `https://integrate.api.nvidia.com/v1`
  — this is NVIDIA's standard hosted endpoint. ⚠️ The Hermes *provider* doc lists
  `https://build.nvidia.com/v1` for the `nvidia` provider; treat these as the
  same hosted service reached two ways and **test both** — `integrate.api.nvidia.com/v1`
  is the canonical NIM/OpenAI-compat host. Self-hosted NIM is `http://localhost:8000/v1`.
- **Model id:** `nvidia/nemotron-3-ultra-550b-a55b`.
- **Auth:** `Authorization: Bearer $NVIDIA_API_KEY`. Free key from
  **build.nvidia.com** (free NVIDIA Developer Program account, no credit card).
- **OpenAI-compatible?** **Yes** — `/v1/chat/completions` + `/v1/embeddings`,
  plus an Anthropic-compatible Messages API; **tool calling supported**. (Also on
  OpenRouter as `nvidia/nemotron-3-ultra-550b-a55b:free`.)

### How `dregg-agent` wires it

Drops straight into the brain seam — no code change, just config:

```rust
let key = ProviderKey::from_env("nvidia", "NVIDIA_API_KEY").unwrap();
let brain = OpenAICompatBrain::with_base(
    task, services, cells, key,
    "https://integrate.api.nvidia.com/v1",     // --llm-base
    "nvidia/nemotron-3-ultra-550b-a55b",       // --llm-model
    LiveOpenAICompatCaller::new(),             // live-brain feature
);
```

`chat_completions_url` appends `/chat/completions`; the key rides only in the
`Authorization: Bearer` header (confinement tooth: it never enters a request
body, receipt, or log — `brain.rs` `the_byo_key_never_leaks`). Our tool-use shape
(`{messages, tools}` → `choices[].message.tool_calls`) matches NVIDIA's.

**Confidence: HIGH** on model id, OpenAI-compat, tool calling, free key.
MEDIUM on which base host the Hermes `--provider nvidia` path uses vs. the raw
`integrate.api.nvidia.com` host — both are reported; verify with a live curl.

---

## 3. NemoClaw (NVIDIA) — "run agents safely"

**What it is.** Not a single tool — a **blueprint/reference architecture** for
open agents in a secure runtime, three layers:

1. **Model** — Nemotron (the blog example uses Nemotron 3 **Super** 120B; Ultra is
   the upgrade path);
2. **Harness** — **Hermes Agent** (skills, memory, sessions, tool bridging);
3. **Runtime** — **NVIDIA OpenShell**: a sandbox that enforces **code-based**
   (not prompt-based) network policy — every allowed destination/port/HTTP-verb/
   binary is declared; **credentials are brokered at the proxy** (hidden from the
   agent); unauthorized access returns **403**, which the agent sees as a tool
   failure.

### Relation to our confinement — COMPLEMENTARY, different layer

| | NemoClaw / OpenShell | dregg-agent |
|---|---|---|
| Confines | **OS/network** reach (filesystem, egress, ports, binaries) | **capability** reach (which tools/cells), **spend**, and **integrity** |
| Mechanism | sandbox + proxy + 403 | attenuable cap bundle + budget cell + ed25519 receipt chain |
| Proof | runtime enforcement (trust the sandbox) | **re-witnessable receipt** — a non-witness re-checks the whole run |
| Credentials | brokered at proxy, hidden from agent | BYO key confined to the transport seam, redacted everywhere else |

They stack cleanly: run `dregg-agent` **inside** an OpenShell sandbox — OpenShell
bounds *where bytes can go*, dregg bounds *what the agent may do, how much it may
spend, and proves it after the fact*. The story: "NemoClaw keeps the agent in its
box; dregg makes the agent's every action a verifiable receipt." No overlap to
resolve — different planes (network/OS vs. capability/economic/cryptographic).

**Confidence: MEDIUM-HIGH.** NemoClaw is genuinely new and the blog is the main
source; "OpenShell" naming and the 3-layer framing are from that single blog.
The blueprint shape is clear; exact OpenShell APIs are not documented yet.

---

## 4. Hermes (Nous Research) — the agent model + harness

**Two things named "Hermes":** (a) the **Hermes-4 model family**, (b) the
**Hermes Agent** harness (the CLI/runtime where skills install).

- **Models:** Hermes-4-70B, Hermes-4-405B, Hermes-4.3-36B (served via Nous Portal
  subscription). The hackathon harness *is* Hermes Agent.
- **Inference API:** **OpenAI-compatible** — "if a server implements
  `/v1/chat/completions`, you can point Hermes at it." Served through the **Nous
  Portal proxy** (`http://127.0.0.1:8645/v1`, forwards per-subscription; test
  endpoint `http://localhost:8642/v1/chat/completions`, model name `hermes-agent`).
  Nous Portal also fronts 300+ models (Claude/GPT/Gemini/DeepSeek/Qwen/Kimi/…).
- **Auth:** `Authorization: Bearer <portal key>`; Portal OAuth via
  `hermes setup --portal`.
- **"Extensive agent skills":** the Hermes skills system (§5) — `/learn`,
  bundled + official skills, slash commands.

### How `dregg-agent` wires it

Identical to §2 — point `OpenAICompatBrain::with_base` at the Portal/Hermes base
(`http://127.0.0.1:8645/v1`) with the Hermes model id and the Portal bearer key.
Because Hermes Agent itself speaks OpenAI-compat, dregg can either (a) consume a
Hermes model directly as its brain, or (b) sit *beside* Hermes Agent, wrapping its
tool calls in the cap/budget/receipt rail.

**Confidence: HIGH** on OpenAI-compat + Portal proxy ports/model name (from the
Hermes docs). MEDIUM on which exact Hermes-4 variant is the hackathon default.

---

## 5. Agent skills — the skill framework/format

**What it is.** Hermes skills = **on-demand knowledge documents** (a folder with a
`SKILL.md`: YAML frontmatter + fixed-order markdown body, progressive disclosure
to keep tokens low). **Compatible with the `agentskills.io` open standard.**

- Live in `~/.hermes/skills/` (single source of truth); each installed skill
  becomes a **slash command** automatically.
- **Install:** `hermes skills install official/<cat>/<name>` (CLI) or
  `/skills install …` (in-session). `/learn` captures a workflow as a new skill
  without hand-writing SKILL.md.
- The **Stripe Skills (§1) are exactly these** — `official/payments/stripe-projects`
  and `official/payments/stripe-link-cli`.

### Should our toolkit speak it?

Yes, optionally, for adoption: a thin adapter that reads an `agentskills.io`
SKILL.md and registers it as a `Toolkit` entry (behind the cap/budget/receipt
rail) lets a dregg agent consume the **same skill ecosystem** Hermes uses — and
adds the receipt guarantee on top. Low effort, high "fits the ecosystem" signal.
Not required to compete, but it's the clean interop play.

**Confidence: HIGH** on format/install/agentskills.io compat (from the Hermes
skills docs). The agentskills.io spec details themselves were not fetched — verify
the exact frontmatter schema if we build the adapter.

---

## Summary — wiring map

| Surface | Type | dregg-agent seam | Confidence |
|---|---|---|---|
| **Stripe Skills** (projects / link-cli) | CLI/tool | `Toolkit::with_tool` → cap-gated/metered/receipted spend | HIGH exist / MED semantics |
| **Nemotron 3 Ultra** | OpenAI-compat LLM | `OpenAICompatBrain::with_base` (`integrate.api.nvidia.com/v1`) | HIGH |
| **NemoClaw / OpenShell** | OS/net sandbox | run dregg *inside* it; complementary | MED-HIGH |
| **Hermes-4 / Nous Portal** | OpenAI-compat LLM | `OpenAICompatBrain::with_base` (`127.0.0.1:8645/v1`) | HIGH |
| **Agent skills** | SKILL.md / agentskills.io | optional `Toolkit` adapter | HIGH |

**The pitch.** dregg-agent is the *only* runtime in this stack where the agent's
**spend, capability reach, and every action** are **cryptographically receipted
and re-witnessable** — supervision by **proof**, not just by a limit or a sandbox.
Nemotron is the brain, NemoClaw boxes the OS, Stripe Skills move the money; dregg
makes the whole loop **verifiable**.

---

## Sources

- [Nous Research announcement (X)](https://x.com/NousResearch/status/2066921443548348436) · [Stripe skills announcement (X)](https://x.com/NousResearch/status/2066647737613832624)
- [NVIDIA/Stripe/Nous launch — digg](https://digg.com/tech/hz8d871s) · [AlphaSignal: Hermes can spend real money](https://alphasignal.ai/news/nous-research-s-hermes-agent-can-now-spend-real-money-autonomously)
- [Stripe Projects skill (Hermes docs)](https://hermes-agent.nousresearch.com/docs/user-guide/skills/optional/payments/payments-stripe-projects) · [Stripe Link CLI skill (Hermes docs)](https://hermes-agent.nousresearch.com/docs/user-guide/skills/optional/payments/payments-stripe-link-cli)
- [Stripe Projects for AI agents (Stripe blog)](https://stripe.com/blog/stripe-projects-adds-new-agents-providers-developer-controls)
- [Nemotron 3 Ultra on build.nvidia.com](https://build.nvidia.com/nvidia/nemotron-3-ultra-550b-a55b) · [Nemotron 3 Ultra NIM docs](https://docs.nvidia.com/nim/large-language-models/2.0.6/day-0/get-started-nemotron-3-ultra.html) · [NVIDIA Nemotron developer page](https://developer.nvidia.com/nemotron)
- [NemoClaw + Hermes (NVIDIA blog)](https://developer.nvidia.com/blog/deploy-self-evolving-agents-for-faster-more-secure-research-with-a-hermes-agent-and-nvidia-nemoclaw/)
- [Hermes Agent — AI providers](https://hermes-agent.nousresearch.com/docs/integrations/providers) · [API server](https://hermes-agent.nousresearch.com/docs/user-guide/features/api-server) · [Skills system](https://hermes-agent.nousresearch.com/docs/user-guide/features/skills) · [Working with skills](https://hermes-agent.nousresearch.com/docs/guides/work-with-skills)

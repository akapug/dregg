# Hermes Agent Accelerated Business Hackathon — SUBMISSION assets

**NVIDIA × Stripe × Nous Research** · Deadline EOD 2026-06-30 · Judging: **Usefulness · Viability · Presentation**

Submission path (all three): (1) Tweet a 1–3 min demo video tagging **@NousResearch** + writeup → (2) drop the link in the Nous Discord submissions channel → (3) complete `typeform.com/to/hpEifIK4`.

Grounded in `docs/HACKATHON-DEMO-PLAN.md` + `docs/HACKATHON-STACK.md`. The one-line pitch:

> **The autonomous business you can audit.** An agent on Hermes/Nemotron that earns, spends, operates, and scales — whose every dollar is **bounded by construction and proven to the cent**.

---

## 0. Project name

**Primary: `Provenant`** — an autonomous business with provenance: every action it takes carries a verifiable record of what it did, and a hard bound on what it could have done. Tagline-friendly ("Provenant — the autonomous business you can audit"), one word, pronounceable, evokes *prove* + *covenant* (the leash is the grant).

Alternates (in case of clash / preference):
- **`Comptroller`** — the financial-control officer for your agent; dry but exactly on-theme (bounded spend + audit).
- **`Ledgerling`** — a small autonomous business that keeps its own provable ledger; playful, memorable.
- **`Receiptd`** — every action leaves a receipt; very short, the differentiator as the name.
- Runtime stays **`dregg-agent`** (the open-source AGPL crate); `Provenant` is the demo/product face built on it.

The in-demo customer business is **"Acme Test-as-a-Service"** (Provenant runs Acme). Keep that name for the scenario; use `Provenant` for the project/tweet/typeform.

---

## 1. The video — shot-list + narration (≤ 3:00, target 2:30)

Recording discipline (from `HACKATHON-DEMO.md`): pre-build everything, one wide dark terminal, large font. The strong lines (`✓ MINTED`, `✗ REFUSED`, `BudgetRefused`, `verified ✓`, `BadSignature`) must read on camera. One command drives the whole loop: `./demo/business.sh`. Narration is voiceover or captions; keep it punchy. Timestamps are cumulative.

**[0:00–0:12] COLD OPEN — the problem.**
- *On screen:* Black slate, one line types out: `$ # Would you give an AI agent your credit card?` then `Provenant — the autonomous business you can audit.`
- *Narration:* "Everyone's building agents that can spend money. Nobody's solved the part a real business needs first: a leash, and an audit."

**[0:12–0:30] BEAT 1 — EARN (real Stripe money in, receipted).**
- *On screen:* `./demo/business.sh` starts. A signed Stripe `payment_intent.succeeded` fires; receiver prints `✓ verified HMAC-SHA256  ✓ MINTED 5000 cents → agent cell`. Then a retry: `✗ REFUSED — double-mint prevented`, and a forged sig: `✗ REFUSED — bad signature`.
- *Narration:* "A customer pays Acme through Stripe. We verify the webhook and mint exactly the paid cents as conserved, receipted credit — and a replay or a forged event is refused. This is revenue you can't fake."

**[0:30–0:50] BEAT 2 — OPERATE (Hermes/Nemotron does the work, confined).**
- *On screen:* `brain: Hermes on nvidia/nemotron-3-ultra-550b-a55b` · model emits a tool-call · `run_tests` runs in the wasm sandbox · `✓ 42/42 passed  · witnessed(cmd·code_root·result) bound into receipt`.
- *Narration:* "The brain is Hermes running on NVIDIA Nemotron. It runs the customer's test suite in a sandbox — and binds a witness of the command, the code, and the result into the receipt. It cannot claim a green it didn't run."

**[0:50–1:25] BEAT 3 — SPEND + THE REFUSAL (the climax).**
- *On screen:* Agent pays its compute/SaaS vendor: `stripe_pay vendor=neon amount=1200c → drawn from budget (headroom 5000→3800) · ✓ receipted`. Then the over-ceiling attempt, slow and clear: `stripe_pay vendor=bigco amount=9000c` → **`✗ BudgetRefused — ceiling 3800c, requested 9000c — NO MONEY MOVED`** (headroom unchanged).
- *Narration:* "Now it spends. Every payment draws from a budget cell it physically cannot exceed — not a watchdog, a property of the cell. Watch: it tries to overspend, and the meter refuses it *before the Stripe call happens*. No dollar moves. A credit card it cannot max out past what you funded."

**[1:25–1:45] BEAT 4 — SCALE (fork the agent, attenuate the budget).**
- *On screen:* `deploy_subagent → child budget = 1000c (attenuated off parent)`. Child runs to its ceiling and stops. A widening child: `✗ Widen — child ceiling 6000c > parent grant`. A child reaching for a vendor the parent never held: `✗ cap refused`.
- *Narration:* "Spiky job? Fork a sub-agent. Its budget and authority attenuate off the parent — provably narrower, never wider. Scale out without ever widening the blast radius."

**[1:45–2:25] BEAT 5 — PROVE + TAMPER-FAILS (the WOW).**
- *On screen:* `dregg-agent verify run.json` → `✓ chain intact (ed25519)  ✓ spend ≤ ceiling  ✓ proof = bound  · headroom: 2800c could-have-spent, didn't`. Then edit one line of `run.json` (flip `paid 1200` → `paid 12`), re-run: **`✗ BadSignature at receipt #7 — TAMPER DETECTED`**.
- *Narration:* "At the end, one command re-verifies the entire P&L with zero trust in us: money in, work done, money out, scaled — chain intact, spend within ceiling, proof and bound agree. Change one dollar in the record, and the signature breaks. A stranger can reproduce this audit offline."

**[2:25–2:40] CLOSE — the tagline.**
- *On screen:* `Provenant` · `earn · spend · operate · scale — bounded by construction, proven to the cent.` · `open source (AGPL): dregg-agent` · `@NousResearch @NVIDIAAI @stripe`.
- *Narration:* "NemoClaw keeps the agent in its box. Stripe moves the money. Hermes on Nemotron does the thinking. **Provenant makes it safe to deploy — and proves it.** The autonomous business you can audit."

> Filming note: if the live NIM/Stripe-payout legs are flaky during the cut, run on the deterministic recorded transport and the recorded Stripe-payout stand-in (the Stripe *earn*/verify+mint leg is the genuine code path either way). Caption the few recorded legs honestly (`[recorded]`); never imply more than ran.

---

## 2. The tweet

**Single-tweet version (≤ 280):**

> You wouldn't hand an AI agent your credit card without a leash *and* an audit.
>
> Meet Provenant: an agent on @NousResearch Hermes + @NVIDIAAI Nemotron that earns, spends (@stripe), operates & scales — every dollar **bounded by construction & proven to the cent**.
>
> Demo ↓

**Thread version (preferred — more room for the differentiator):**

1/ You wouldn't hand an AI agent a credit card without a leash *and* an audit. Meet **Provenant** — the autonomous business you can audit. An agent that earns, spends, operates & scales, and proves every dollar. Built on @NousResearch Hermes + @NVIDIAAI Nemotron + @stripe. 🧵 [video]

2/ Every team here built an agent that *can* spend. Ours's spending is **bounded by construction**: every payment draws from a budget cell it physically cannot exceed, and is refused *before the Stripe call happens*. Watch it try to overspend — no dollar moves. (•‿•)

3/ At the end: one command re-verifies the whole P&L — money in, work done, money out, scaled — with zero trust in the host. Tamper with one dollar in the record and the signature breaks. The runtime is open source (AGPL): `dregg-agent`. Supervision by **proof**, not just a limit.

---

## 3. The writeup

**The problem.** Agents can now spend real money — Stripe Skills give Hermes a wallet, a card, and the ability to provision its own SaaS. But "can spend" is the easy half. No business hands an autonomous process a credit card and a deploy key on the strength of a prompt that says *please stay under budget*. It needs two things first: a **leash** it cannot slip, and an **audit** it cannot forge. That trust layer — not the spending capability — is the real blocker to deploying autonomous business.

**Our solution.** Provenant is built on `dregg-agent`, an open-source (AGPL) cap-bounded, budget-bounded, receipted agent runtime in Rust that drives any OpenAI-compatible model. Three guarantees ride on every action, by construction:
- **Cap-bounded** — every action is checked against an attenuable capability *before* it runs; a vendor, tool, or cell outside the grant is refused, with no receipt. The model cannot widen its own reach by asking.
- **Budget-rate-limited by construction** — every spend draws from a budget cell whose draw is rejected in-band if it would exceed the ceiling. This is a property of the cell, not a counter someone remembered to check. The un-drawn headroom is a hard bound on everything the agent *could still have done*.
- **Cryptographically receipted** — every admitted action and the amount/verdict bound into it seals into a prev-hash-linked, ed25519-signed chain. A non-witness re-verifies the whole run offline; a forged "I paid $5" or "the tests passed" breaks the signature.

**The demo.** A judge watches one terminal run "Acme Test-as-a-Service," operated end to end by the agent: a customer pays via Stripe (verified webhook → conserved, receipted mint); Hermes-on-Nemotron runs the customer's suite in a sandbox and binds a witness of `(command · code · result)` into the receipt; the agent pays its own compute/SaaS vendor via Stripe — drawn from its budget; it **tries to overspend and is refused before any money moves**; it forks a sub-agent whose budget and authority attenuate off the parent, provably narrower; and finally `verify run.json` re-witnesses the entire P&L with zero host trust — then we tamper one line and the signature breaks.

**Why it wins.**
- **Usefulness** — a deployable autonomous business loop (earn → operate → spend → scale), not a toy. The agent runs a real metered service, takes real Stripe revenue, and pays real vendors, all from one runtime.
- **Viability** — the trust/audit layer is the actual blocker to letting agents spend, and we solve it *provably*: supervision by proof, not by a limit you hope holds. That is what a real company needs before it funds an agent, and it composes with the rest of the stack rather than competing with it.
- **Presentation** — one command, a live tamper-fails moment, and a refusal you can *see* happen before money moves. The wow is legible in 30 seconds.

**The stack (and how it composes).** **Hermes** is the harness/model — we drive it (and Nemotron) through the OpenAI-compatible brain seam; the same cap/budget/receipt braid wraps it unchanged, and `deos-hermes/` confines the *real* Hermes runtime over ACP as the deep-path credibility. **Nemotron 3 Ultra** (`nvidia/nemotron-3-ultra-550b-a55b`, hosted OpenAI-compatible at `integrate.api.nvidia.com/v1`) is the brain — drops in by config, the BYO key confined to the transport seam and proven never to leak into a request/receipt/log. **Stripe Skills** (`stripe-link-cli` / `stripe-projects`) move the money — wired as cap-gated, metered, receipted `Toolkit` tools, so our budget cell becomes a *tamper-evident mirror* of Stripe's spending limit. **NemoClaw / OpenShell** is complementary, not overlapping: it bounds *where bytes can go* (OS/network), dregg bounds *what the agent may do and how much it may spend, and proves it after the fact* — run dregg inside an OpenShell sandbox and the two planes stack. NemoClaw makes the model safe to talk to; Provenant makes the agent safe to deploy — and proves it.

**Honest about live vs recorded.** The Stripe *earn* (verify + conserved mint), the cap/budget/receipt runtime, the witnessed toolkit, sub-agent attenuation, and `verify`/tamper-detection are the genuine, tested code paths. The live Nemotron call needs a key + network; the deterministic recorded transport is the filmed default and `--live` flips to NIM. The outbound Stripe *payout* leg uses a recorded stand-in unless an operator supplies live Stripe keys (the verify+mint earn leg is genuine either way). Full operator-independence of the witnessed work is the federation/in-circuit residual we name openly. Nothing in the demo claims more than the code runs.

---

## 4. Typeform answers (`typeform.com/to/hpEifIK4`)

Field names are anticipated; map to the actual form at submission.

- **Project name:** Provenant — the autonomous business you can audit.

- **One-liner / tagline:** An agent that earns, spends, operates, and scales a real business — with every dollar bounded by construction and proven to the cent.

- **What it does (short):** Provenant runs an automated service business ("Acme Test-as-a-Service") end to end on an autonomous agent: it takes Stripe revenue, runs the work on Hermes/Nemotron in a sandbox, pays its vendors via Stripe, and forks sub-agents to scale — and its spending is *cap-bounded* (only granted vendors), *budget-bounded by construction* (a ceiling it physically cannot exceed, refused before money moves), and *cryptographically receipted* (every dollar re-verifiable offline, tamper-evident). One command re-audits the whole P&L; change one dollar and the signature breaks.

- **Problem it solves:** No business will hand an autonomous agent a credit card and a deploy key without a leash it can't slip and an audit it can't forge. Spending capability is now table stakes (Stripe Skills); the trust/audit layer is the real blocker. We provide it provably.

- **Tech / integrations used:** Nous **Hermes** (agent harness + model, OpenAI-compatible; real runtime confined over ACP in `deos-hermes`); NVIDIA **Nemotron 3 Ultra** (`nvidia/nemotron-3-ultra-550b-a55b`, hosted NIM at `integrate.api.nvidia.com/v1`) as the brain; **Stripe Skills** (`stripe-link-cli`, `stripe-projects`) for earn + spend, wired as cap-gated/metered/receipted tools; **NemoClaw / OpenShell** as the complementary OS/network sandbox (dregg runs inside it). Runtime: `dregg-agent` — Rust, cap-bounded + budget-bounded + ed25519-receipted, drives any OpenAI-compatible model.

- **Open source?** Yes — the `dregg-agent` runtime is open source under AGPL.

- **What's live vs in progress:** Live + tested — Stripe verify+conserved-mint (earn), the cap/budget/receipt runtime, the witnessed toolkit, sub-agent attenuation, `verify` + tamper-detection. Config/recorded — live Nemotron call (recorded transport is the deterministic default, `--live` flips to NIM); outbound Stripe payout uses a recorded stand-in absent live operator keys. Named residual — full operator-independent witnessing (federation/in-circuit).

- **Team:** ember arlynx (ember.software) + Claude (Opus 4.8).

- **Links:**
  - Demo video: `<TWEET / VIDEO URL — fill at submission>`
  - Open-source runtime: `<repo URL — dregg-agent>`
  - Writeup: this submission (`docs/HACKATHON-SUBMISSION.md`)

- **Demo video URL:** `<paste the tweet permalink here>`

- **Anything else judges should know:** The differentiator is one sentence — every team's agent *can* spend; ours's spending is **bounded by construction and proven to the cent**. Watch the over-ceiling spend get refused *before money moves*, and watch one tampered dollar break the signature. Supervision by proof, not by a limit you hope holds.

---

*The leash is the grant. (⌐■_■)*

# DROPPED BALLS — the DreggNet-push open-loop sweep

A `cv` mining of the context-rolled main-loop session chain since the DreggNet
push began (2026-06-29 → 2026-06-30): `d70e4744 → 59e8e250 → 7432ede0 →
53f647dd → d9cdf9b3 → b5afe2ba → 5de610a6 → 1822c1e7 → 86f445c3 → 50b7b4f5 →
a96e268c → 99f316b8 → a77a9549` (live). ~10–13 sessions, ~720 candidate ember
messages after filtering subagent-output turns.

**Method.** The chain is one continuous conversation re-exported across context
rolls, so almost every idea ember raised appears verbatim in many sessions. The
dropped-ball signal is **an idea ember had to re-raise across rolls that is still
unresolved at HEAD**. Each item below was verified against the DreggNet `dev`
git log, `docs/`, and the breadstuffs HEAD — not taken from the transcript alone.

**Honesty bar.** A thing the re-dregg / scholar-visionary / VK-epoch waves
*absorbed* is NOT a dropped ball — it is listed under "Superseded / Picked-up"
so we don't re-chase it. A real idea that died in a context-roll IS a dropped
ball.

---

## Count

- **Genuinely-dropped, still-worth-doing (ember-raised): 4** (A1–A4 below).
- **Soft / parked, lower urgency (ember-raised): 5** (A5–A9).
- **My queued REVIEWED-GO awaiting ember's go: a battery of ~10** (section B) —
  not dropped *by me*, but sitting while ember repeatedly asked "why not a
  go-real flip?". The mismatch is the finding.
- **Named seams genuinely dropped (not terminal-floor, not in-flight): ~4**
  (section C; the other ~28 in `NAMED-RUNGS.md` are either in-flight VK-epoch or
  terminal crypto floor).
- **Decisions pending ember: 5** (section D).
- **Superseded / already picked-up (do NOT re-chase): ~9** (section E).

**Highest-value to resurrect:** **A1 (provable QA — "how does dregg-cloud prove
the QA was real?")**, then **A2 (model/subscription flexibility — harness-tied
access routes)** and **A3 (a researched "what DreggNet IS" message to builders)**.

---

## (A) Ember-raised ideas that petered out — highest value

### A1. "How does dregg-cloud prove the QA *was real*?" — GENUINELY DROPPED ★
- **Raised by:** ember, late chain (`99f316b8 #681`, `a77a9549 #674`); and the
  parked `#7` of the 7-point answer in `#641` ("let's talk about this more, this
  is nuanced").
- **What:** when a dregg-cloud agent runs testing/QA/prod-monitoring for a
  customer, how does the protocol *witness/prove the QA actually happened and was
  real* — not just "the agent said so". This is the dregg thesis applied to the
  agent-services product itself (federation-attested QA).
- **Last state:** ember explicitly wanted to continue the design ("nuanced,
  let's talk more"). **No `docs/` artifact, no design thread, no follow-up
  exists** at HEAD. Died in the roll between `99f316b8` and `a77a9549`.
- **Worth doing?** YES — high. It is the single most on-thesis product question
  raised in the whole push (provable agent labor), and it is unanswered.

### A2. Model / subscription **flexibility** — harness-tied & "alternative" access routes — DROPPED-PARTIAL ★
- **Raised by:** ember (`#662`, `#669`, `a77a9549 #716`).
- **What:** the Kimi BYO-key adapter landed (`28b4282dc` + `KIMI-LIVE-DEMO.md`,
  `BRING-YOUR-OWN-LLM.md`, provider-agnostic OpenAI-compatible brain — DONE). But
  ember's *broader* point is unresolved: the key was for `kimi-code` (a
  harness-tied subscription), and "we do need to figure out a way to allow ppl to
  use their subscriptions that might be harness-tied or have 'alternative' access
  routes." ember's unease: "maybe we aren't thinking about these things flexibly
  enough."
- **Last state:** the OpenAI-compatible *API-key* path is done; the
  **harness-/subscription-tied** access path (let a user bring their Claude/Kimi
  *subscription*, not a raw API key) is named but unbuilt. `BRING-YOUR-OWN-
  HARNESS.md` exists but does not solve subscription-auth bridging.
- **Worth doing?** YES — medium-high. It is the difference between "BYO API key"
  and "BYO whatever-you-already-pay-for," which is the actual adoption surface.

### A3. A **researched** "what DreggNet IS" message to builders.dev — DROPPED (quality) ★
- **Raised by:** ember, repeatedly (`a96e268c #704`, `99f316b8 #460/#466`,
  `a77a9549 #453/#459`, and the many "check/update builders" pokes).
- **What:** "did you ever send a message to builders about what dreggnet IS?
  david (pug) has no fucking clue, he's just 'wow ember is doing dregg!'" — then,
  on the attempt: "i'm pretty sure that message wasn't very good. like it wasn't
  researched on dreggnet."
- **Last state:** builders updates were posted, but ember twice judged the
  *explainer* inadequate (unresearched). No durable, vetted "this is what
  DreggNet is and what it offers" artifact was confirmed-good. Recurs into the
  live session unresolved.
- **Worth doing?** YES — medium. Cheap, and it is the external-comprehension gap
  ember keeps hitting (it rhymes with the recurring "it's still not clear how
  anyone can *use* the dreggnet cloud / what it offers").

### A4. Migrate the chain **"fluidly" across operator sets** — MOSTLY-ADDRESSED, verify
- **Raised by:** ember (`#352/#605/etc` — "wait do we not have a way to
  migrate/the chain 'fluidly'..? across operator sets?").
- **What:** moving the live chain across operator/committee sets without a
  genesis re-roll.
- **Last state:** **largely answered** by the live epoch-transition wiring
  (validator add/remove/rotate, chain-continuing) — exercised live in the n=4 →
  genesis-C2 run (`97e22d4`, `858e34e` committee-change runbooks). The residual
  is true cross-operator *fluidity* under quorum-stall (named in the runbook
  gaps) and `lassie`/n=5 independent fault domains (NAMED-RUNGS #4/#9).
- **Worth doing?** Verify the runbook gaps; not a clean dropped ball.

### A5. GPU provers / **Apple private compute cloud + private inference** — PARKED
- **Raised by:** ember (`#125/#126`, then `#152`).
- **State:** answered "not worth Apple-Metal **unless** it lets us deploy dregg
  to Apple's private compute cloud (and access Apple private inference)." That
  *unless*-clause was never investigated. Genuinely parked, low urgency.

### A6. The "are we actually **computing in-circuit**, not just attesting over
combinatorial circuits of unverifiable input wires?" doubt — SOFT
- **Raised by:** ember 3× (`#214/#361/#457`).
- **State:** a soundness-integrity reassurance question, raised across three
  rolls. Likely answered conversationally each time, but never pinned to a
  durable doc. Worth a one-paragraph grounded answer so it stops recurring.

### A7. **Ethereum bridging + settle to Mina** ("for old time's sake") — PARKED/DROPPED
- **Raised by:** ember once-ish (`#612/#665`).
- **State:** Solana is the live bridge focus; ETH/Mina never acted on. Genuinely
  parked. Low priority unless ember revives.

### A8. "**front office** — please swarm over that" (`a77a9549 #757`) — LIKELY-ADDRESSED
- **State:** the customer-facing surface was worked via `WEB-PORTALS-CENSUS.md`,
  `CLOUD-PROVIDER-READINESS.md`, `MYOPIA-AUDIT.md`. Probably absorbed; verify the
  "front office" framing landed as ember meant it.

### A9. "**DEC** — Dregg Electric Coin? lol" (`#481/#488`) — NOT A BALL
- An aside/joke about a doc abbreviation. No action intended.

---

## (B) My queued / REVIEWED-GO that never returned

`MORNING-REVIEW.md` is the explicit reviewed-go queue. These are **staged,
green, reversible, and waiting on ember's one-word go** — they are not dropped
*by me*, but the standing tension is real: ember asked "why not a go-real flip
please? :)" in nearly every session while this battery sat. Surfacing them
together is the point.

1. **n=4 epoch-transition** — READY (David standing by for "proposed"); the
   `persvati-rust` keep-vs-remove topology is an ember decision (see D1). *(Note:
   an n=4 → genesis-C2 transition WAS exercised live since — confirm which shape
   is now deployed.)*
2. **Owned compute engine** — RESOLVED by ownership: the external compute submodule
   was fully removed; the `Sandboxed` wasm tier now runs on an owned, in-crate,
   pure-Rust `wasmi` interpreter (zero unsafe). Wiring owned engines for the stronger
   tiers (JIT/Caged/MicroVm/Gpu — currently fail-closed seams) is the remaining work.
3. **Auto-deploy public webhook** (`dregg-deploy` is built+green; the public
   push-triggered ingress + Caged/MicroVm fleet build + public go-live are
   reviewed-go).
4. **Custom domains** — live DNS resolver landed; **live cert** is reviewed-go.
5. **Persistent servers** — built; **live fleet boot** reviewed-go.
6. **Real ToolGateway `invoke` rail** — code-proven; two go-lives reviewed-go.
7. **Real EC2 provider + overlay mesh fleet default** — code-proven; live
   spin-up reviewed-go.
8. **Solana bridge LIVE MAINNET relayer** — mock/devnet landed; real-mint /
   real-$ relayer is reviewed-go (fires real money).
9. **Hosting-billing meter — real `$DREGG` on the live edge** — built+staged,
   S3-gated (the billing flip is the §3.5 ember-decision; see D2).
10. **pg-dregg verified store as settlement backing** — landed; verified-proof /
    on-chain Payable is S3-gated.

---

## (C) Named seams / residuals genuinely dropped

`NAMED-RUNGS.md` (32 rows + an older-epoch tail) already accountably catalogs
these — that catalog IS the cure ("named = a burn-down, not a parking lot").
Filtering out (i) the VK-epoch circuit rungs that are **actively** handed to the
recursion-verifier session (`RECURSION-VERIFIER-HANDOFF.md`, parallel sessions
`5f565ac4`/`cb68e2f5`/`12518a7b`; ember at `a77a9549 #696`: "circuit bro has
mostly finished his work") and (ii) the terminal FRI/STARK/Poseidon2-CR crypto
floor, the genuinely-dropped small ops seams are:

- **persvati hardware config does not persist a reboot** (NAMED-RUNGS #20) —
  **CLOSED 2026-06-30.** The persistence was already implemented on the box (a
  `modprobe.d` conf + the enabled `persvati-thermal-config.service` oneshot) and
  ran cleanly on the last real boot; the only gap was that it was not
  version-controlled. Now committed to `deploy/persvati-tuning/` + the runbook
  (`runbooks/HARDWARE-PERSVATI.md`) rewritten with install/verify steps. Verified
  durable (enabled boot-firing oneshot, idempotent re-apply).
- **metrics scrape wiring** (#19) — **DIAGNOSED 2026-06-30: the wiring is already
  correct.** Prometheus scrapes `dregg-node:8420/metrics` (target UP), 17 `dregg_*`
  families land when the node is healthy, and the dashboards reference the right
  names. The Grafana "No data" confusion is really (a) the deployed `n4` binary
  lacking the newer eager-registration of `block_height`/`turns_submitted`/
  `proofs_verified` (HEAD `eade56d0c` has it → rides the redeploy) and (b) NO
  dashboard surfaces gossip — the storm had zero visibility. The honest standalone
  open is a node gossip-rejection counter + a gossip dashboard panel (node-code,
  redeploy/orchestration lane).
- **genesis-baseline recovery fix rollout** (#21) — **CONFIRMED STALE LIVE
  2026-06-30.** The deployed edge `dregg-node:n4` (built `2026-06-29T08:43Z`) is
  missing the recovery fix `6aa2ddc2e` (supersedes `1a61dc16d`), the gossip-storm
  fix `923becc66`, AND the metrics eager-seed `eade56d0c` — all committed AFTER
  the image build. The gossip-storm fix's absence is observable live: the edge
  node is wedged in a per-peer stream storm (ops PAGE `node_down`). Redeploy lane
  owns the rebake; do NOT restart the stale binary (its recovery path is buggy).
- **DreggNet private GitHub remote** (#10) — *resolved since* (the `dev` branch
  now has `origin git@github.com:emberian/DreggNet.git`); leave noted.

---

## (D) Decisions still pending ember

1. **n=4 committee topology** — `MORNING-REVIEW.md §1`: keep `persvati-rust`
   (5-node, snoopy carries 2/5) vs remove it (clean 4-node David topology).
   Explicitly "a decision ember should make."
2. **Billing go-live** — flip real `$DREGG` charging for build / `invoke` /
   hosting (the §3.5 ember-decision; S3-gated). Recurs as ember's "why not a
   go-real flip."
3. **LIVE MAINNET Solana relayer** — authorizing real mints against real
   on-chain locks (real money). Reviewed-go, ember's word.
4. **Minimum legal/policy posture** — the `docs/legal/` pack (LEGAL-POSTURE,
   TERMS, AUP, DMCA, PRIVACY; `78b56ef`) is *drafted*; the operating decision
   (operator entity, KYC-free posture acceptance) is ember's. ember at
   `a77a9549 #755`: "we definitely need to work out our minimum posture towards
   this regarding legal/policy."
5. **Provable-QA design direction** (= A1) — ember asked to "talk about this
   more"; it needs a design decision before it can be built.

---

## (E) Superseded / already-picked-up — do NOT re-chase

These looked like open loops in the transcript but were absorbed by later waves;
listed so we don't waste a cycle re-opening them.

- **"What went wrong with mostly-offchain coordination / kill calling them
  receipts / real-regrounding"** (`#632/#647/#681`) → became the **re-dregg**
  (`ARCHITECTURE-CRITIQUE.md`, `RECEIPT-CONTRACT.md`, and commits `4aeecf5` /
  `f72d8e4` / `cdef48d` / `f7a2e61` / `3521914` / `0a225a4` — registries/buckets/
  servers/durable dissolved onto the proven umem substrate Σδ=0).
- **"Is dregg pulling its weight / why isn't dregg more involved in generic
  hosting / issue scholar-visionaries to propose something bigger"** (`#841/#844/
  #490`) → `THE-BIGGER-DREGGNET.md` + `MYOPIA-AUDIT.md` + `DREGG-PRIMITIVE-
  VOCABULARY.md` + the resource-cloud/agent-in-the-world vision docs (`797c016`,
  `f0a10d2`, `bf2e2ba`, `7c2b37e`, `b535bf3`).
- **Gallery "garbled circuits" regression / "garbled auction took forever"**
  (`#647` etc) → real Chou-Orlandi OT wired into the Yao garbled circuit, a
  genuine 2PC sealed-bid auction (breadstuffs `715648d84`).
- **Kimi live brain** (`#641/#648/#696/#716`) → `28b4282dc` + `KIMI-LIVE-DEMO.md`
  (the *subscription* sub-point survives as A2).
- **KERI** (`a77a9549 #790`) → `KEY-RECOVERY-AND-KERI.md` + `3862b58` (cap-account
  rotation/recovery vs KERI gap mapped) + `0372685` account-identity weld.
- **Posters in the public repo** (`#569/#574`) → relocated out of the tree
  (`8d6ec09ab`, `f89a85585`) into `~/src/dregg-posters` (10 posters present).
- **Guardrail hook for forward-looking/secret leakage into the public repo**
  (`#536/#543`) → `~/.claude/hooks/dregg-boundary-guard.sh` exists; plus
  `f63e4afde` scrubbed product leakage, `LEAK-EXPOSURE-AUDIT.md`.
- **AGPL / "are we restricted / sole ownership" firewall** (`#710/#819/#835/
  #893`) → ember decided: own copyright, destined for AGPL, keep DreggNet private
  **until the httpe/Elide-net is segregated** — SINCE DONE: the Elide net stack was
  ejected and DreggNet flipped to AGPL-3.0 (`ELIDE-NET-EJECTION.md`); `FIREWALL-DISSOLUTION.md` +
  the httpe-decouple (`57e81f7` — own the ~6 HTTP value types) is underway. The
  open *work* (finish the httpe/Elide segregation so DreggNet can open-source,
  esp. for the open-source Nous-hackathon Hermes split, `#893`) is a real lane,
  not a dropped ball — tracked in `HTTPE-TIDY-PLAN.md` / `NET-CRATES-STALENESS.md`.
- **Sandstorm.io native integration** (`#650/#682/#594` etc) → design landed
  (`SANDSTORM-INTEGRATION-PLAN.md`, `SANDSTORM-DEFENSE-IN-DEPTH.md`,
  `SANDSTORM-DEVNET-READY.md`); the live grain is part of the devnet-ready lane,
  not dropped.
- **Liftoff surpass / permissionless cloud** (`#610/#698`) → `LIFTOFF-SURPASS-
  MATRIX.md` + `PERMISSIONLESS-CLOUD-PLAN.md`; ember later said "let's not call
  out liftoff" — handled.

---

*Generated 2026-06-30 by a read-only `cv` sweep at ember's request
(`a77a9549 #948`). Verify each row's STATE against HEAD before acting — memories
and transcripts are point-in-time; `docs/` + git log at HEAD are the truth.*

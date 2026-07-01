# FAKEOUTS — the agent runtime + its integrations (`breadstuffs/dregg-agent`)

Read-only audit of the hackathon-critical agent surface: the brains, the tools, the
Stripe Skills, the budget/cap gates, verify/receipts/tamper, federation-QA, and the
demo. Every finding is grounded to `breadstuffs/dregg-agent/src/…` at HEAD.

**Bottom line (sober): the "bounded + proven + live" story is REAL end-to-end.** The
four pitch-load-bearing paths — `verify`, the budget gate, the cap gate, the
`--tamper` catch — are each genuine, non-vacuous, and fail-closed, verified against
the code below. The "live" brain is a real HTTP request; the `run` subcommand refuses
loudly (does not silently replay) when the live feature is absent. The recorded /
stub transports are honestly labelled everywhere I looked ("recorded", "(needs a
key)", "REPLAY … tools execute for real"). **No CRITICAL fakeout found** — no vacuous
verify, no always-admitting budget, no always-passing cap gate, no faked tamper-catch,
no "live" brain that is secretly canned.

The residuals are two honest **not-wired / provenance** seams (MEDIUM/LOW), not
laundered fakes. They are listed below the "verified-real" ledger.

---

## Ranked findings

### MEDIUM — `federation_qa` is a real crypto primitive that is NOT WIRED into the bin or demo (named-not-wired)

- **file:line** — `src/federation_qa.rs` (whole module); `src/lib.rs:53` (`pub mod federation_qa;` — the only non-test reference in the crate).
- **pretends** — the module header (`src/federation_qa.rs:1-60`) describes "the QA verdict is submitted to **the live federation (the n=4 nodes — edge · node-a · node-b-lean · node-b-rust)**", each operator re-executing "on its OWN substrate", and says "In production the oracle is the operator's local tier run … on its own node" (`:121-122`).
- **does** — `Operator` (`:127-131`) holds an **injected in-process closure** `rerun: Box<dyn Fn(&WitnessedRun) -> Option<ReWitness>>`. There is **no code path anywhere in the crate that constructs a `Federation`, contacts a remote node, or wires a per-operator remote substrate** — the only callers are the module's own `#[cfg(test)]` tests, which build 4 keypairs + 4 closures in one process. The demo (`demo/business.sh`) never invokes it. The quorum-verify LOGIC itself is genuinely real (see ledger below): `verify_quorum_cert` (`:400-482`) does real ed25519 per-vote verification, rejects unknown/duplicate/off-topic/forged votes, enforces the threshold, and names dissenters — non-vacuous.
- **severity** — MEDIUM. Not a demo fakeout (it is never on the demo path, so it fakes nothing a judge runs), and the verify logic is real. But the "the live federation (n=4 nodes)" / "In production the oracle is the operator's local tier run on its own node" framing over-states integration: the production remote-node oracle is unimplemented; only the in-process closure exists. A reader of the header could believe 4 independent machines are contacted.
- **fakeout-or-honest-label** — MIXED. The body honestly says "in the std/test path it is a supplied closure" (`:123`) and the boundary section (`:50-60`) is candid that light-client-witnessed re-exec is the deeper unclosed seam. The *over-claim* is only the "live federation" / "in production … on its own node" phrasing versus zero wiring.
- **fix** — either (a) wire a real `Operator::remote(node_url, key)` that POSTs the `WitnessedRun` to each node's re-exec endpoint and collects the signed `(exit, output_digest)`, then exercise it in a demo beat; or (b) soften the header from "the live federation (n=4 nodes)" to "a quorum-QA *primitive*; the per-node remote oracle is the named wiring step (`crate::federation_qa`), today exercised in-process." Keep the honest boundary note.

### LOW — `run.json` stamps a live model id + endpoint onto a `--replay` (recorded-brain) artifact

- **file:line** — `src/bin/dregg-agent.rs:453-455` (replay branch passes the live default `base`/`model` into `make_brain`) → recorded into `LiveRun.model` / `LiveRun.endpoint` (`src/live.rs:41-44`); observable in `demo/run.json` (`"model": "nvidia/llama-3.3-nemotron-super-49b-v1"`, `"endpoint": "https://integrate.api.nvidia.com/v1"`) even though that file was produced via `--replay`.
- **pretends** — the committed `run.json` carries a live NVIDIA model + endpoint, with **no field marking the run as a replay**. A judge reading `run.json` alone (not the ephemeral stdout `[mode] REPLAY of a recorded brain` banner at `:442-445`) would read it as a live model run.
- **does** — the model *decisions* are canned (`RecordedOpenAICaller`, `:446`) — but the tools genuinely ran (real shell/http/git/stripe) and the receipts are genuinely signed, so `verify` holds regardless of provenance. The `funding` field IS honest here ("Stripe Skills: RECORDED — set ~/.stripekey …").
- **severity** — LOW. Not load-bearing: `verify_live` does not depend on the model field, and the pitch is "bounded + proven", not "this exact model ran live". The mislabel is confined to the informational `model`/`endpoint` provenance fields.
- **fakeout-or-honest-label** — soft mislabel (the live banner is honest; the persisted artifact drops the "replayed" fact).
- **fix** — record provenance into the artifact: add a `LiveRun.brain_mode: "live" | "replay"` field (or prefix the recorded model with `replayed:`), set it in the `--replay` branch, and print it in `cmd_verify`.

### INFO — `HealthSnapshot { conservation_ok: true, … }` default; `check_health`/`run_tests`/`verify_deploy` not wired in the bin

- **file:line** — `src/toolkit.rs:528-538` (`Default` → all-healthy); `src/toolkit.rs:506-510` (doc: "or, in the safe-autonomous path, from a local snapshot"). The bin toolkit (`src/bin/dregg-agent.rs:417-420`, `:1071-1073`) wires only `with_shell` + `with_http` + `with_stripe_skills_boxed(detect())`.
- **pretends / does** — the flat verdict tools (`run_tests`, `check_health`, `verify_deploy`) are **not registered** on the bin's toolkit, so if a model calls one it hits `ToolOutcome::fail("no tool `…` registered on this toolkit")` (`src/toolkit.rs:501`) — an honest receipted fail, not a faked green. `HealthSnapshot::anomalies()` (`:550-568`) is real, non-vacuous logic (flags divergence>0, `!conservation_ok`, errors>0, lapse); the all-true default only appears in test wiring and `healthy()` helpers.
- **severity** — INFO (not on the demo path; no fake presented as real).
- **fix** — none needed; if these tools are later advertised in the demo, wire a real probe (node `/health` + `/metrics` + receipt-log read) behind `with_check_health`, do not ship the all-healthy default.

---

## Verified REAL / non-vacuous (the pitch, ground-truthed) — NOT fakeouts

| Path | file:line | Why it is real (not vacuous/stub) |
|---|---|---|
| **`verify` (re-witness)** | `agent.rs:925-943` `verify_agent_run` | Re-runs `verify_chain` (real ed25519 + blake3 link check), then enforces `consumed ≤ budget` AND `chain tip consumed_after == report.consumed`. Fail-closed. |
| **receipt chain** | `receipt.rs:307-359` `verify_chain_from` | Real ed25519 verify per receipt + prev-hash link + strict-monotone seq + single-signer. Tests prove tamper/splice/foreign-signer all rejected (`:432-474`). Empty slice is the only vacuous case, documented. |
| **tamper binds the signed body** | `agent.rs:727-765` `AgentReceipt::body_hash` | `cost`, `consumed_after`, `headroom_after`, `tool_ok`, and the `WitnessedRun` `(command, code_root, exit, output_digest)` are all folded into the signed body hash — so a forged verdict/cost moves the hash and breaks the signature. |
| **`--tamper` catch** | `bin/dregg-agent.rs:165-177` | Actually mutates a receipt's `cost` to a guaranteed-different value, then `verify_live` recomputes body_hash → ed25519 `BadSignature`. A genuine catch, not a scripted "caught". |
| **budget gate (meter)** | `meter.rs:224-274` `draw` | Real fail-closed draw over a `ReplenishingBudget` cell; over-ceiling → `MeterError::OverBudget` *before* commit; exactly-once per `(subject, period)`. Test `over_budget_is_refused_in_band_before_commit` (`:332-348`) proves both polarities (10 admits, +1 refused, 0 charged). |
| **budget ceiling** | `budget.rs:383-394` | Real `outstanding + amount > terms.budget ⇒ ExceedsCeiling`; refill blocks derived from `at_block` (early refill inexpressible). `lease_budget_free_period_always_admits` is honest free-tier (ppu=0), not vacuity. |
| **cap gate (macaroon)** | `cred.rs:466-513` `Credential::verify` | Real ed25519 signature chain from root + the meet of every first-party `Pred` and third-party discharge; run loop refuses on `Err` (`agent.rs:1405-1422`). `tools.rs:921-922` proves granted host admits / ungranted host refuses. |
| **no-amplify (sub-agent)** | `grant.rs:62-71` `covers` | Exact covers only identical; prefix covers equal/longer prefix. A child widening past the parent is refused (`agent.rs` `AgentError::Widen`). |
| **live brain (HTTP)** | `brain.rs:350-395` `LiveOpenAICompatCaller::complete` | Real `reqwest::blocking` POST with 60s timeout, BYO key in `Authorization: Bearer` only, fail-closed on http error / non-2xx. Behind the `live-brain` feature. |
| **`run` refuses when not live** | `bin/dregg-agent.rs:219-224` | Without `live-brain` the `run` subcommand errors ("needs the `live-brain` feature … Rebuild:") — it does NOT silently fall back to recorded. |
| **recorded brain honesty** | `brain.rs:224-322` `RecordedOpenAICaller` | Replays canned responses; returns `Err("no more recorded responses")` when exhausted (never fabricates); `--replay` prints "REPLAY … tools execute for real". |
| **real shell** | `tools.rs:67-134` `real_shell` | Real `bash -c` spawn, captured stdout/stderr/exit, SIGKILL timeout→124, cd-persistence, secret-env stripping + HOME re-root. Honest about NOT confining absolute-path reads / raw egress (needs OS isolation). |
| **real http / git** | `tools.rs:514-587` | `op_http_get` calls the injected reqwest runner; `op_git_clone` shells real `git clone --depth 1` confined under workdir. Both fail-closed ("runner not wired") — no canned constant. |
| **Stripe Skills (live)** | `stripe_skills.rs:261-355` `CliStripeSkills` | Shells the real `stripe projects add` / `link-cli spend-request create`; key rides in child env only + redacted from all captured bytes; returns `Err` on non-zero exit — **never fakes a "✓ paid"**. `live: true` only on a real exit-0. |
| **Stripe Skills (recorded)** | `stripe_skills.rs:108-176` `RecordedStripeSkills` | Deterministic, `live: false`, every outcome labelled `"recorded: …"` / `mode()=="recorded"`; test asserts it is never labelled live (`:553`). |
| **federation quorum verify** | `federation_qa.rs:400-482` `verify_quorum_cert` | Real ed25519 per-vote verify + known-operator + one-vote + off-topic + forged rejection + threshold tally + dissenter naming. Non-vacuous (`Federation::new` panics on threshold 0). Only caveat: not wired to remote nodes (MEDIUM above). |
| **hermes-cli harness** | `bin/dregg-agent.rs:768-815`, `hermes.rs:104-186` | Spawns the REAL hermes CLI only when `DREGG_HERMES_CMD` points to a reviewed ndjson bridge; else falls back to the recorded demo with an explicit `[mode] could not spawn … falling back to the recorded demo` banner. Deliberately never auto-spawns a bare `hermes`. Honest reviewed-wiring seam. |
| **witnessed-QA re-exec** | `agent.rs:1067-1108` `verify_witnessed_qa` | Real: rejects `code_root != deployed_root`, rejects un-re-executable (fail-closed), rejects a recorded result the re-run does not reproduce. Honest residual noted: rerun still runs in the same substrate (federation-QA is the named next layer). |

## Honestly-labelled recorded/stub seams (NOT fakeouts)

- `brain.rs:224` `RecordedOpenAICaller` — "replays canned responses"; exhaustion errors, never fabricates.
- `stripe_skills.rs:110-176` `RecordedStripeSkills` — labelled `"recorded"`, `live:false`, "(needs a key)"-style funding notes.
- `harness.rs:161` `MockHarness` — named "the fake harness driver"; the real path is `SubprocessHarness`.
- `hermes.rs:186` `recorded_hermes_demo_calls` — "honestly labelled, never a faked live success" (`hermes.rs:47`).
- `toolkit.rs:592` `runner` — a test-only "mock compute runner"; the cloud wires polyana behind the same seam.
- `demo/business.sh:63-69` — prints "(no model key — replaying a bundled transcript; tools run for real)" before a `--replay`.
- `demo/run.json` / `skills-run.json` `funding` — "Stripe Skills: RECORDED — set ~/.stripekey … for the live leg".

---

*Method: read-only; every claim ground-checked against `breadstuffs/dregg-agent/src` at HEAD. Critical paths (verify/budget/cap/tamper/brain-live) were read in full, not sampled.*

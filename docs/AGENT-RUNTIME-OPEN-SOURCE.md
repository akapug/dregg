# The open-source agent runtime (`dregg-agent`)

The dregg substrate carries a **complete, self-contained agent runtime**: an
autonomous agent loop that is *bounded* (a replenishing budget meter), *gated*
(a capability bundle / powerbox over the dregg-auth credential lattice),
*receipted* (a prev-hash-chained, ed25519-signed receipt log re-witnessable by a
non-witness), and *driven by any OpenAI-compatible model* (the Hermes / BYO-key
brain). It depends on **nothing but the substrate** — no cloud, no hosting, no
private control plane.

This document is the dependency boundary and the extraction record: what is
open, what stays cloud-coupled, and how the cloud *wraps* the open core instead
of owning it.

## The one-sentence shape

> A confined agent is a brain proposing actions, each one cap-gated against an
> attenuable bundle, metered against a replenishing budget, and sealed into a
> signed receipt chain — so an agent run is a *verifiable artifact* (`verify_agent_run`)
> that a non-witness can re-check end to end.

## Where it lives

`dregg-agent/` — a workspace member next to `deos-hermes/` (the confined Hermes
agent surface). AGPL, substrate-only, public on `github.com/emberian/dregg`. It
was lifted out of the private cloud (`exec/`), where it had grown up coupled to
the cloud only at *one* seam (the owned wasmi compute engine). Post-AGPL-firewall
dissolution, everything else it needs is the substrate.

## The dependency boundary

```
                       dregg-agent  (AGPL, OPEN, substrate-only)
   ┌──────────────────────────────────────────────────────────────────┐
   │  agent.rs      — the loop: budget · cap · receipt braid            │
   │                  (AgentCloud::run_with_toolkit, verify_agent_run)  │
   │  budget.rs     — ReplenishingBudget cell (the spend bound)         │
   │  meter.rs      — the Meter trait + ReplenishingMeter               │
   │  cred.rs       — the dregg-auth credential core (ed25519 caveat    │
   │                  chain, attenuate-only-narrows) — substrate port   │
   │  grant.rs      — mint_caps / attenuate_caps / cap_context          │
   │  receipt.rs    — the TurnReceipt discipline: prev-hash chain +     │
   │                  ed25519 attest + verify_chain (no host trust)     │
   │  brain.rs      — the OpenAI-compatible / Hermes brain (BYO key,    │
   │                  recorded transport, live transport behind a flag) │
   │  harness.rs    — the BYO-harness confinement (stdin/stdout child)  │
   │  toolkit.rs    — the Toolkit registry + the ToolKit trait;         │
   │                  compute tools are CLOSURE-INJECTED (no engine)    │
   │  federation_qa.rs — the quorum-QA core (re-witness attestation)    │
   └──────────────────────────────────────────────────────────────────┘
        depends only on: serde · blake3 · ed25519-dalek · postcard ·
                         base64 · getrandom · hex   (+ reqwest behind the
                         off-by-default `live-brain` feature)

                       the private cloud exec  (separate repo, AGPL)  — WRAPS it
   ┌──────────────────────────────────────────────────────────────────┐
   │  pub use dregg_agent::{agent, budget, meter, harness,             │
   │                        federation_qa, brain, toolkit}             │
   │  + SandboxToolkit ext — injects the owned wasmi compute engine   │
   │    (run_workload) as the toolkit's run_tests / run_workload runner │
   │  + rewitness_run_tests — the Layer-3 re-witness riding the owned sandbox    │
   │  + model.rs (cloud workload taxonomy), egress, host_api, capture  │
   └──────────────────────────────────────────────────────────────────┘
```

There is **one** agent runtime. The cloud does not fork it; it depends on it and
supplies the cloud-only implementations behind traits/closures.

## What is open vs. what stays cloud-coupled

| Concern | Home | Why |
|---|---|---|
| The agent loop (budget·cap·receipt braid) | **open** (`dregg-agent`) | pure substrate primitives |
| The replenishing budget + meter (the bound) | **open** | std + the budget cell |
| Cap bundle / powerbox / attenuation | **open** | the dregg-auth credential lattice |
| The receipt chain + non-witness verifier | **open** | the substrate TurnReceipt discipline |
| The OpenAI-compatible / Hermes brain | **open** | std + serde; live HTTP behind `live-brain` |
| The BYO-harness (confined child process) | **open** | std process I/O |
| The toolkit registry + `ToolKit` trait | **open** | closures all the way down |
| `check_health` / `verify_deploy` tools | **open seam** | already closure-injected — the *cloud* supplies the probe / verifier closure |
| The **compute engine** (`run_tests` / `run_workload`) | **seam → cloud** | the toolkit takes an injected `Fn(&str,&str) -> Result<RunReport,String>` runner; the cloud wires the owned **wasmi** sandbox behind it (`SandboxToolkit`) |
| The federation-QA **live node** read | **seam → cloud** | the quorum-QA *core* (the re-witness attestation) is open; the live-node fetch is the injected surface |
| Cloud workload taxonomy (`model.rs`), egress accounting, host-API spine, log capture | **cloud** (`exec`) | genuinely cloud/hosting concerns |

The single substantive change made during extraction: the toolkit's compute
tools (`run_tests`, `run_workload`) no longer call a crate-private `run_workload`
engine. They take an **injected runner closure**, so the open core has no
compute-engine dependency at all. The witness binding (`WitnessedRun` over
`(command, code_root, exit, output_digest)`) — the security-critical part — stays
in the open core; only the *execution* is injected. The cloud's `SandboxToolkit`
extension trait wires the owned wasmi sandbox as that runner.

## The hackathon proof

`cargo test -p dregg-agent` (substrate-only, no private cloud on the path) runs a
bounded + receipted agent against a recorded OpenAI-compatible transport: the
cap-gate refuses an ungranted action, the meter refuses over-budget steps, the
receipt chain re-witnesses with `verify_agent_run`, the BYO-harness confines a
child brain, and the toolkit dispatches injected (mock) compute tools — all with
**zero** private dependency. That is the hackathon-critical path: *a Hermes /
OpenAI-compatible agent, bounded and receipted, fully open.*

## Naming

The extracted code is **substrate / hermes-flavored**, never cloud-flavored:
`dregg-agent`, `hermes`-style brains, substrate domain-separation tags
(`dregg-agent-…-v1`). No cloud product names leak into the AGPL substrate.

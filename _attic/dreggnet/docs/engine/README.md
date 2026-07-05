# DreggNet engine — the plan set

This directory is the **autonomous-execution bible** for the DreggNet verified
network engine: a clean-room, formal-first rebuild of "The Network Orchestrator"
as the verified, line-rate **net PD** of the dregg/deos seL4 capability OS —
AGPL-3.0, un-rug-pullable, provably safer than the original.

It is written so a fleet of agents can drive the project to completion **without
the originating human or the originating session in the room.** The agents run
under a *spirit* (a `decision-spirit`-derived skill, developed and owned by ember
+ an operator's buildr fleet, NOT in this repo) that supplies judgment/escalation; these
docs supply the **plan, the architecture, the decisions, and the definition of
done** that the spirit executes against.

## Read in this order

| Doc | What it is | When to read |
|---|---|---|
| `00-CHARTER.md` | The mission + the non-negotiable invariants + definition of done. | First, always. The keel — everything inherits it. |
| `10-DECISIONS.md` | The ADR log: every locked call + rationale; open calls + **default + revisit-trigger**. | Before any load-bearing choice. Don't relitigate a locked ADR. |
| `20-ARCHITECTURE.md` | The layered system: DSL → verified compiler → seL4 net PD → raw NIC; the three tiers; the cap-fabric unification; the cold/hot split. | Before building anything. |
| `21-FORMAL-MODEL.md` | The difficulty-ranked formal-model build order (the representations to formalize+generate). | Before writing any model or proof. The technical spine. |
| `22-PERFORMANCE.md` | The line-rate budget as an acceptance criterion + the design rules that meet it by verified means. | Before any dataplane perf work. |
| `30-ROADMAP.md` | The phased rung ladder — the actual sequenced work, each rung with done-criteria, deps, verification obligation. | To pick what to do next. |
| `60-COORDINATION.md` | How the buildr fleet runs this under the spirit + the builders.dev MCP; roles, decomposition, escalation, source-of-truth precedence. | When operating the fleet. |

*(Not yet written, scheduled: `23-COMPILER.md` — the verified-compiler pass pipeline in detail (currently covered across 20/21/30); `50-ORACLE.md` — the compiled session charts (Roadmap rung R0.3); `51-GLOSSARY.md` — the ontology.)*

## Companion material (not in this dir)

- **The spirit** — the judgment/escalation skill (ember + an operator, in buildr). Governs *how* the fleet decides; these docs govern *what* it builds.
- **The memories** — a local session memory store holds the session-derived reference (the engine charts, the dregg seL4/deos architecture, the formal-model skeleton, the liberation manifest). The plans here are the distilled, durable version; the memories are the deeper raw notes.
- **The oracles** (read, never port — see Charter CR-3 + `oracle/PROVENANCE.md`):
  - Engine semantics — **inlined for the fleet** (the bots can't read the internal Elide source tree):
    - the protocol/IO/TLS libraries: `DreggNet/net/` (already in-tree).
    - the orchestrator + config schema + gate + migration: `docs/engine/oracle/`
      (`elide-cli/`, `elide-pkl/`, `elide-licensing/`, `elide-sidecar/`).
    - **READ-ONLY. Elide-proprietary. Never copy into the clean-room tree.** See
      `oracle/PROVENANCE.md`.
  - dregg semantics: the breadstuffs workspace (Lean kernel `metatheory/`, seL4 `sel4/`,
    CapTP `captp/`, `wire/`, `uc-crypthol/`) — referenced in place, not copied.

## The one-sentence project

Describe the engine **once** in a high-level data-oriented DSL; a **verified
compiler we own** (front-end + domain passes on CakeML/Pancake's verified backend)
emits line-rate machine code, the formal model, and ~90% of the proofs; the ~10%
residual (a handful of concurrent objects + the confinement theorem) is closed by
hand — so the fastest shape and the most-provable shape are the same shape, and
there is no unverified link from the spec to the NIC.

## Status

Bootstrap. No engine code or proofs written yet (by design — see Roadmap Phase 0).
The first stone is the `region`/`view` verified compiler pass (Roadmap R1.1).

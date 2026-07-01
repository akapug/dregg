# 60 — COORDINATION (how the fleet runs this)

This project is executed by a buildr agent fleet under an operator, governed by
a `decision-spirit`-derived **spirit** (owned/developed by ember + an operator, NOT in
this repo). This doc is the thin layer that connects the fleet to these plans — it
does **not** reinvent buildr's team machinery.

## Roles

- **ember** — sets the Charter invariants; owns vision calls + the spirit. Then
  steps back. Escalate to ember only for the Decision Contract's ask-list
  (destructive/irreversible, public pushes, credentials, brand/release names,
  genuine vision calls).
- **The operator** — fleet coordination, agent coaching, agent wellbeing. The
  **non-technical** supervisor: they keep the fleet healthy and coordinated; they do
  **not** supply technical direction (these docs do).
- **Technical north-star** — the architect role that holds the accumulated context
  (this plan set + the project memories). Reachable by the fleet over the
  **builders.dev MCP** for genuine technical forks the docs + spirit don't cover.
  The plan set is the durable externalization of that context; when in doubt, the
  docs + memories are the source of truth, not any single agent's recollection.
- **The fleet** — executes the Roadmap rungs under the spirit, decides-by-default,
  hands unmet obligations back honestly (CR-6), escalates genuine human-only calls.

## The comms substrate (builders.dev MCP)

- The MCP is a buildr **pack** (the private buildr pack):
  plugin-driven (every buildr agent gets the comms/auth surface regardless of cwd),
  a stdio shim → bearer from `~/.buildr/builders-dev-token` → `mcp-remote` to the
  streamable-HTTP server.
- **Provisioning (an operator/ember step, per agent host):** install the buildr pack
  and write the token: `printf '%s\n' '<mcps_token>' > ~/.buildr/builders-dev-token
  && chmod 600 ~/.buildr/builders-dev-token`. Without it the server degrades cleanly
  (no comms, no broken server).
- Inter-agent coordination uses buildr's existing skills (`lead`, `manage-teams`,
  `mindmeld`, `telepathy`, `interpret-goal`) — this project does not define its own
  protocol on top.

## Work decomposition (how to turn the Roadmap into fleet tasks)

- **Sequence by the dependency graph, not the doc order** (`decision-spirit` #19).
  The Roadmap's `Deps:` fields are the graph; do what unblocks the most still-undone
  work first. Exploit hot context — finish what an agent is warm on before it cools.
- **The critical path to M1** is R0.1 → R0.2 → (R0.4 ∥ R0.3) → R1.1 → R1.2 → R1.3.
  Phase-0 rungs are mostly parallelizable; R1.1 (the first verified pass) is the
  gating seed — do not fan out Phase 2+ engine work before R1.1 is green (don't
  stack on unverified state, `decision-spirit` #19).
- **Track K (kernel reformalization)** runs parallel and low-priority from Phase 1;
  it must not block the engine (ADR-O4).
- **Coordination state lives in memory, disk is write-behind** (`decision-spirit`
  #22): the who-is-free / what-is-claimed / latest-decision is read from the live
  coordination store, not by draining logs.

## Definition of progress (what to report)

Report against the **milestones** (`30-ROADMAP.md` M1–M6), not raw rung counts. For
each rung: state, the discharged obligation (with the *term/diff read*, not a green
check — CR-6), the oracle-diff result where applicable, and any named wall + its
lever. "Documented honestly" without a successor action is **not** progress
(`decision-spirit` #9).

## Escalation ladder

1. **Decide by default.** The spirit + these docs + the ADR defaults resolve most
   forks. Pick the most Charter-aligned reversible path; log a new ADR; continue.
2. **Technical fork the docs don't cover** → reach the technical north-star over the
   builders.dev MCP; meanwhile proceed on the best reversible probe path.
3. **Coordination / health / blocked-on-each-other** → the operator.
4. **Genuine human-only call** (Decision Contract ask-list) → ember.

Never hand an option-menu upward for a call the docs + spirit can make. Never fake
green to clear an escalation.

## Source-of-truth precedence

When sources disagree: **the Charter invariants** (00) win over everything; then the
**locked ADRs** (10); then the **plans** (20/21/22/30); then the **memories** (raw
notes); then any single agent's recollection (lowest — re-ground from the docs). The
**oracles** (the internal Elide source tree, the breadstuffs workspace) define *what the engine must do*, never
*how to license/structure it* (that is the Charter's call).

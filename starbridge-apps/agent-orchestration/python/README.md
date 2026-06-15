# dregg-orchestration — a verified mandate gate for any Python agent loop

**Embed dregg's verified-orchestration substrate natively into an agent loop** (hermes-agent, or any
tool-calling loop): gate EVERY tool call through an attenuable mandate, so a worker can never invoke a
tool outside its granted scope or over its budget — and a stranger can audit the whole swarm without
trusting the loop.

This is the Python face of the canonical Rust development
[`starbridge-apps/agent-orchestration`](../). The Rust crate is the source of truth; this package is a
faithful mirror (pinned by `tests/test_differential.py`) plus the live weld onto hermes-agent.

> The four ADOS integrators (`buildr`/`builders`/`sig`/`simbi`) each hand-rolled the same six primitives
> around their agent loop and **every one punted on enforcement** ("no budget enforcement, a runaway could
> drain $1000s"). dregg closes exactly that gap at ONE seam — the tool-call / verdict record. This package
> is that seam, in Python.

## The idea in 10 lines

```python
from dregg_orchestration import Mandate, Orchestration, Tool

# A coordinator delegates ATTENUATED mandates (granted ⊑ held — the proven non-amplification):
coordinator  = Mandate.coordinator([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE, Tool.WRITE], budget=1000)
researcher   = coordinator.attenuate([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE], 700, "research")
fact_checker = coordinator.attenuate([Tool.READ], 300, "fact-check")  # `write` STRICTLY dropped

orch = Orchestration(coordinator, {"researcher": researcher, "fact-checker": fact_checker})

orch.authorize_call("researcher", "web_search", {"q": "x"})   # ALLOW (metered, content-addressed)
orch.authorize_call("fact-checker", "write_file", {"p": "x"}) # raises MandateError — out of scope!

orch.audit()  # proves no agent exceeded its mandate (re-derived from the log), or raises
```

## Native hermes-agent embedding (zero hermes core edits)

Hermes already serializes "an agent did X" at its tool-call guardrail
(`agent/tool_guardrails.py::ToolCallGuardrailController.before_call`). Wrap it so the dregg mandate runs
first — both teeth bite:

```python
from dregg_orchestration import Mandate, Tool
from dregg_orchestration.hermes_guardrail import DreggToolGuardrail, wrap_controller
from agent.tool_guardrails import ToolCallGuardrailController

mandate = Mandate.coordinator([Tool.READ, Tool.SEARCH], budget=500)
guard   = DreggToolGuardrail.for_single_worker(mandate, worker="hermes")

# In run_agent.py, where `self._tool_guardrails = ToolCallGuardrailController(...)`:
self._tool_guardrails = wrap_controller(self._tool_guardrails, guard, worker="hermes")
#   → before_call now: (1) dregg mandate gate (block out-of-mandate, never runs the tool);
#                      (2) hermes's own heuristic guardrail. A drop-in — every other method forwarded.
```

`wrap_controller` returns a proxy that is duck-compatible with hermes's controller (`before_call`,
`after_call`, `reset_for_turn`, `halt_decision`, …), plus `dregg_audit()`.

## Run the proofs

```bash
cd python
python3 tests/test_differential.py          # 14 vectors pinned against the Rust #[test]s
python3 tests/test_hermes_integration.py     # welds onto the REAL hermes controller (skips if absent)
python3 examples/hermes_native_demo.py       # the full arc: delegate → gated run → refuse → audit
```

## What mirrors what

| Python (`dregg_orchestration`)        | canonical Rust                                   |
|---------------------------------------|--------------------------------------------------|
| `Tool` / `Mandate` / `Mandate.le`     | `src/lib.rs` `Tool` / `Mandate` / `worker_authority_subset_orchestrator` |
| `Mandate.attenuate`                   | `Mandate::attenuate` (`derive_no_amplify`)       |
| `tool_for_mcp_name`                   | `src/mcp.rs` `mcp::tool_for_mcp_name`            |
| `content_address`                     | `McpToolCall::digest` (`blake3(name ‖ args)`)    |
| `Orchestration.authorize_call`        | `mcp::step_from_mcp_call` (the verified-step gate)|
| `Orchestration.audit`                 | `audit_run` (re-derive, prove no over-mandate)   |

The Rust executor remains where a verified TURN is committed (via the `dregg` sdk-py binding's
`AuthorizedTurn.submit`); this package is the in-loop GATE + the off-loop AUDIT — the decision and the
proof, in the loop's own language.

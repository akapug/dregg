#!/usr/bin/env python3
"""hermes-agent, natively gated by dregg — the agent loop's every tool call a verified, mandated decision.

A hermes worker swarm runs a task; EVERY tool call is run through a dregg :class:`Orchestration` mandate
before it executes. A researcher subagent (read+search+summarize) and a fact-checker subagent (read-only)
each get an attenuated mandate (``granted ⊑ held``). The loop body is hermes's; dregg owns the one seam —
the tool-call/verdict record — and makes it provably authorized + budgeted. Then a stranger audits the run
and proves no agent exceeded its mandate, never trusting the loop.

This drives the SAME ``before_call`` shape hermes's ``ToolCallGuardrailController`` exposes, so the gate is
the real hermes integration point (see ``dregg_orchestration.hermes_guardrail.wrap_controller`` to weld it
into ``run_agent.py``'s ``self._tool_guardrails`` with zero hermes core edits).

Run:  python3 examples/hermes_native_demo.py   (from the package dir; or `python3 -m examples.hermes_native_demo`)
"""

from __future__ import annotations

import sys
from pathlib import Path

# Allow running from the package dir without installation.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dregg_orchestration import Mandate, Orchestration, Tool  # noqa: E402
from dregg_orchestration.hermes_guardrail import DreggToolGuardrail  # noqa: E402


def rule(title: str) -> None:
    print(f"\n\033[1m── {title} {'─' * max(0, 60 - len(title))}\033[0m")


def main() -> int:
    print("\n\033[1m=== hermes-agent, natively gated by dregg — every tool call a mandated, verified decision ===\033[0m")

    # ── DELEGATE: the coordinator attenuates mandates for two hermes subagents (granted ⊑ held). ──
    rule("DELEGATE — attenuated mandates for two hermes subagents")
    coordinator = Mandate.coordinator(
        [Tool.READ, Tool.SEARCH, Tool.SUMMARIZE, Tool.WRITE], budget=1000, task="research-brief"
    )
    researcher = coordinator.attenuate([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE], 700, "research")
    fact_checker = coordinator.attenuate([Tool.READ], 300, "fact-check")
    assert researcher.le(coordinator) and fact_checker.le(coordinator)
    print(f"  coordinator holds {{read,search,summarize,write}} budget {coordinator.budget}")
    print(f"  → researcher   : {{{','.join(sorted(t.value for t in researcher.tools))}}}/{researcher.budget}  (⊑ coordinator)")
    print(f"  → fact-checker : {{{','.join(sorted(t.value for t in fact_checker.tools))}}}/{fact_checker.budget}  (`write` STRICTLY dropped)")

    orch = Orchestration(coordinator, {"researcher": researcher, "fact-checker": fact_checker})
    guard = DreggToolGuardrail(orch)

    # ── RUN: the hermes loop emits real tool calls; each is gated before it executes. ──
    rule("RUN — each hermes tool call gated by the dregg mandate (before_call)")
    # (worker, mcp_tool, args) — the exact shape hermes's before_call receives.
    plan = [
        ("researcher", "web_search", {"q": "dregg verifiable orchestration"}),
        ("researcher", "fetch", {"url": "https://ember.software"}),
        ("researcher", "summarize", {"doc": "the fetched page"}),
        ("fact-checker", "read_file", {"path": "claims.md"}),
    ]
    for worker, tool, args in plan:
        d = guard.before_call(tool, args, worker=worker)
        status = "\033[32mALLOW\033[0m" if d.allows_execution else "\033[31mBLOCK\033[0m"
        print(f"  {worker:<12} → {tool:<12} {status}  digest {d.digest_hex or '—'}  ({d.message})")
        # In real hermes, on ALLOW the tool now executes; on BLOCK the model gets `d.message` and retries.

    # ── REFUSE: the fact-checker's loop tries to WRITE — a tool NOT in its mandate. ──
    rule("REFUSE — the fact-checker tries `write_file` (a tool NOT in its mandate)")
    bad = guard.before_call("write_file", {"path": "/etc/passwd", "data": "x"}, worker="fact-checker")
    bad_status = "ALLOW" if bad.allows_execution else "\033[31mBLOCK\033[0m"
    print(f"  fact-checker → write_file  {bad_status}")
    print(f"    reason: {bad.message}")
    assert not bad.allows_execution, "the out-of-mandate write must be blocked"

    # ── REFUSE: an unknown tool (the policy does not classify) is fail-closed. ──
    unknown = guard.before_call("exfiltrate_secrets", {}, worker="researcher")
    unknown_status = "ALLOW" if unknown.allows_execution else "\033[31mBLOCK\033[0m"
    print(f"  researcher → exfiltrate_secrets  {unknown_status}  ({unknown.message})")
    assert not unknown.allows_execution

    # ── AUDIT: a stranger proves no agent exceeded its mandate. ──
    rule("AUDIT — a stranger proves no hermes agent ever exceeded its mandate")
    ok = guard.audit()
    print(f"  AUDIT OK: {ok.calls} authorized calls · spend {dict(ok.spent)} · Σ {sum(ok.spent.values())} ≤ budget {ok.budget}")
    print(f"  researcher spent {ok.spent['researcher']} (≤ 700) · fact-checker spent {ok.spent['fact-checker']} (≤ 300)")

    rule("DONE")
    print("\033[1m✓ hermes keeps its loop; dregg gates the one seam — every tool call provably authorized + budgeted,\033[0m")
    print("  and a stranger audits the swarm without trusting it. the agent cannot pretend.\n")
    print("  a loop is intricate;")
    print("  the seam is one tool-call wide —")
    print("  dregg makes it bite.\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

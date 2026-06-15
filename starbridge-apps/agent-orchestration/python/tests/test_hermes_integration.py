"""Live integration: the dregg mandate gate welded onto the REAL hermes ``ToolCallGuardrailController``.

This is the proof the embedding is NATIVE, not a parallel model: it imports the actual
``agent.tool_guardrails.ToolCallGuardrailController`` from ``~/pug/hermes-agent`` and wraps it with
``dregg_orchestration.hermes_guardrail.wrap_controller`` — so a single ``before_call`` runs the dregg
mandate FIRST (a refusal short-circuits to block, the tool never runs) and then hermes's own heuristic
guardrail. Both teeth bite, on hermes's real decision shape, with zero hermes core edits.

Skipped (not failed) if the hermes checkout is not importable in this environment — the dregg-only
differential test (``test_differential.py``) is the always-runnable proof; this is the extra "it really
welds onto hermes" check when the loop is present.

Run:  python3 tests/test_hermes_integration.py   (or via pytest)
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dregg_orchestration import Mandate, Tool  # noqa: E402
from dregg_orchestration.hermes_guardrail import DreggToolGuardrail, wrap_controller  # noqa: E402

_HERMES = os.path.expanduser("~/pug/hermes-agent")


def _load_hermes_controller():
    """Import the real hermes ToolCallGuardrailController, or return None if unavailable."""
    if _HERMES not in sys.path:
        sys.path.insert(0, _HERMES)
    try:
        from agent.tool_guardrails import ToolCallGuardrailController  # type: ignore

        return ToolCallGuardrailController
    except Exception:
        return None


def test_dregg_gate_welds_onto_the_real_hermes_controller():
    Controller = _load_hermes_controller()
    if Controller is None:
        print("  SKIP: hermes-agent not importable in this environment")
        return

    # A read-only fact-checker worker, gated by dregg, wrapping hermes's real controller.
    coord = Mandate.coordinator([Tool.READ, Tool.SEARCH, Tool.WRITE], 1000, "task")
    fact_checker = coord.attenuate([Tool.READ], 300, "fact-check")
    dregg_guard = DreggToolGuardrail.for_single_worker(fact_checker, worker="fact-checker")

    hermes_controller = Controller()
    guarded = wrap_controller(hermes_controller, dregg_guard, worker="fact-checker")

    # (1) An in-mandate read: dregg ADMITS, then hermes's guardrail runs — overall ALLOW.
    d_read = guarded.before_call("read_file", {"path": "claims.md"})
    assert d_read.allows_execution, f"an in-mandate read should be allowed, got {d_read.action}"

    # (2) An out-of-mandate write: dregg BLOCKS first — the tool never reaches hermes's guardrail.
    d_write = guarded.before_call("write_file", {"path": "/etc/passwd", "data": "x"})
    assert not d_write.allows_execution, "an out-of-mandate write must be blocked by the dregg gate"
    assert "out-of-mandate" in d_write.message.lower()

    # (3) The wrapper forwards hermes's OWN attributes (e.g. reset_for_turn) unchanged — it is a drop-in.
    assert hasattr(guarded, "reset_for_turn"), "the wrapper forwards hermes's controller methods"
    guarded.reset_for_turn()  # must not raise — hermes's real method, forwarded.

    # (4) The dregg audit is reachable through the wrapper.
    ok = guarded.dregg_audit()
    assert ok.calls == 1, "exactly the one in-mandate read was authorized + logged"
    assert ok.spent["fact-checker"] == 50

    print("  ok   the dregg mandate gate welds onto the real hermes ToolCallGuardrailController")


if __name__ == "__main__":
    import traceback

    try:
        test_dregg_gate_welds_onto_the_real_hermes_controller()
        print("\n1/1 passed (or skipped)")
    except Exception:
        traceback.print_exc()
        raise SystemExit(1)

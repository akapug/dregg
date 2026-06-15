"""Differential: the Python mirror must agree with the canonical Rust development.

The Rust crate ``starbridge-apps/agent-orchestration`` is the SOURCE OF TRUTH. These tests pin the Python
``dregg_orchestration`` mirror against the SAME vectors the Rust ``#[test]``s assert (``src/lib.rs`` tests
for the mandate lattice; ``src/mcp.rs`` tests for the MCP map + content-address + the audit). Drift on
either side fails — exactly the discipline the dregg house uses for every Rust↔X mirror.

Run:  python3 -m pytest tests/   (or `python3 tests/test_differential.py` for a no-pytest run)
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from dregg_orchestration import (  # noqa: E402
    Mandate,
    MandateError,
    Orchestration,
    Tool,
    content_address,
    tool_for_mcp_name,
)


# ── §1 the mandate lattice (mirrors src/lib.rs tests) ────────────────────────


def test_attenuate_narrows_tools_and_clamps_budget():
    # Rust: attenuate_narrows_tools_and_clamps_budget
    coord = Mandate.coordinator([Tool.READ, Tool.SEARCH, Tool.WRITE], 1000, "task")
    w = coord.attenuate([Tool.READ, Tool.SEARCH, Tool.SPEND], 600, "sub")
    assert w.tools == frozenset({Tool.READ, Tool.SEARCH}), "SPEND (not held) is dropped by intersection"
    assert w.budget == 600
    assert w.le(coord)


def test_attenuate_clamps_overbudget_request_down():
    # Rust: attenuate_clamps_overbudget_request_down
    coord = Mandate.coordinator([Tool.READ], 500, "task")
    w = coord.attenuate([Tool.READ], 9999, "sub")
    assert w.budget == 500, "an over-budget request is clamped to held (no amplification)"
    assert w.le(coord)


def test_le_is_the_subset_and_budget_order():
    # Rust: le_is_the_subset_and_budget_order
    held = Mandate.coordinator([Tool.READ, Tool.WRITE], 1000, "t")
    assert Mandate.coordinator([Tool.READ], 400, "s").le(held)
    assert not Mandate.coordinator([Tool.READ, Tool.WRITE, Tool.SPEND], 400, "s").le(held), "wider tool breaks ⊑"
    assert not Mandate.coordinator([Tool.READ], 1001, "s").le(held), "larger budget breaks ⊑"


def test_strict_attenuation_drops_a_held_tool():
    # Rust: strict_attenuation_drops_a_held_tool (worker_attenuation_is_strict)
    coord = Mandate.coordinator([Tool.READ, Tool.WRITE], 1000, "t")
    worker = coord.attenuate([Tool.READ], 400, "s")
    assert worker.le(coord)
    assert Tool.WRITE in coord.tools
    assert Tool.WRITE not in worker.tools, "the subset is STRICT — WRITE dropped"


def test_authorizes_is_scope_and_budget_fail_closed():
    # Rust: authorizes_is_scope_and_budget_fail_closed
    m = Mandate.coordinator([Tool.READ, Tool.SEARCH], 1000, "t")
    assert m.authorizes(Tool.READ, 0, 600)
    assert m.authorizes(Tool.SEARCH, 600, 400)  # 600+400=1000 <= 1000
    assert not m.authorizes(Tool.SEARCH, 600, 401)  # over budget — BUDGET tooth
    assert not m.authorizes(Tool.WRITE, 0, 1)  # out of scope — SCOPE tooth


# ── §2 the MCP map (mirrors src/mcp.rs::known_mcp_tools_map_to_capabilities) ──


def test_known_mcp_tools_map_to_capabilities():
    assert tool_for_mcp_name("search").tool == Tool.SEARCH
    assert tool_for_mcp_name("read_file").tool == Tool.READ
    assert tool_for_mcp_name("write_file").tool == Tool.WRITE
    assert tool_for_mcp_name("pay").tool == Tool.SPEND
    assert tool_for_mcp_name("rm_minus_rf_the_universe") is None, "an unknown tool is unclassified (fail-closed)"


def test_mcp_default_costs_match_rust():
    # The Rust default costs: read 50, search 100, summarize 150, write 200, spend 300.
    assert tool_for_mcp_name("fetch").cost == 50
    assert tool_for_mcp_name("web_search").cost == 100
    assert tool_for_mcp_name("summarize").cost == 150
    assert tool_for_mcp_name("write_file").cost == 200
    assert tool_for_mcp_name("transfer").cost == 300


# ── §3 the content-address (mirrors src/mcp.rs::the_digest_binds_name_and_arguments) ──


def test_content_address_binds_name_and_arguments():
    a = content_address("search", {"q": "dregg"})
    b = content_address("search", {"q": "dregg"})
    c = content_address("search", {"q": "other"})
    d = content_address("grep", {"q": "dregg"})
    assert a == b, "same call ⇒ same digest"
    assert a != c, "different args ⇒ different digest"
    assert a != d, "different tool ⇒ different digest"
    assert len(a) == 32, "a 32-byte content-address"


# ── §4 the orchestration gate + audit (mirrors the run/refuse/audit teeth) ───


def test_in_mandate_call_is_authorized_and_metered():
    coord = Mandate.coordinator([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE, Tool.WRITE], 1000, "task")
    a = coord.attenuate([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE], 700, "research")
    b = coord.attenuate([Tool.READ], 300, "fact-check")
    orch = Orchestration(coord, {"a": a, "b": b})
    entry = orch.authorize_call("a", "search", {"q": "x"})
    assert entry.tool == Tool.SEARCH
    assert entry.spent_after == 100
    assert orch.spent("a") == 100


def test_out_of_mandate_tool_is_refused():
    coord = Mandate.coordinator([Tool.READ, Tool.WRITE], 1000, "task")
    b = coord.attenuate([Tool.READ], 300, "fact-check")
    orch = Orchestration(coord, {"b": b})
    try:
        orch.authorize_call("b", "write_file", {"path": "x"})
        raise AssertionError("an out-of-scope tool must be refused")
    except MandateError:
        pass
    assert orch.spent("b") == 0, "a refused call meters nothing (fail-closed)"


def test_unknown_tool_is_fail_closed():
    coord = Mandate.coordinator([Tool.READ], 1000, "task")
    orch = Orchestration(coord, {"a": coord.attenuate([Tool.READ], 500, "s")})
    try:
        orch.authorize_call("a", "exfiltrate", {})
        raise AssertionError("an unknown tool must be refused")
    except MandateError:
        pass


def test_amplified_worker_mandate_is_caught_at_construction():
    coord = Mandate.coordinator([Tool.READ], 500, "task")
    amplified = Mandate.coordinator([Tool.READ, Tool.SPEND], 9999, "amp")  # NOT ⊑ coord
    try:
        Orchestration(coord, {"a": amplified})
        raise AssertionError("an amplified worker mandate must be caught")
    except MandateError:
        pass


def test_a_clean_run_audits():
    coord = Mandate.coordinator([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE, Tool.WRITE], 1000, "task")
    a = coord.attenuate([Tool.READ, Tool.SEARCH, Tool.SUMMARIZE], 700, "research")
    b = coord.attenuate([Tool.READ], 300, "fact-check")
    orch = Orchestration(coord, {"a": a, "b": b})
    orch.authorize_call("a", "web_search", {"q": "x"})  # 100
    orch.authorize_call("a", "summarize", {"doc": "y"})  # 150
    orch.authorize_call("b", "fetch", {"url": "z"})  # 50
    ok = orch.audit()
    assert ok.calls == 3
    assert ok.spent["a"] == 250
    assert ok.spent["b"] == 50
    assert sum(ok.spent.values()) <= ok.budget


def test_over_subbudget_is_refused():
    coord = Mandate.coordinator([Tool.READ], 1000, "task")
    b = coord.attenuate([Tool.READ], 120, "fact-check")  # budget only fits ONE read (50) ... two = 100 ok, three = 150 > 120
    orch = Orchestration(coord, {"b": b})
    orch.authorize_call("b", "read_file", {})  # 50
    orch.authorize_call("b", "read_file", {})  # 100
    try:
        orch.authorize_call("b", "read_file", {})  # 150 > 120
        raise AssertionError("the third read breaches the sub-budget")
    except MandateError:
        pass
    assert orch.spent("b") == 100, "the refused call meters nothing"


# ── no-pytest runner (so the proof runs even without pytest installed) ───────

if __name__ == "__main__":
    import traceback

    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    failed = 0
    for fn in fns:
        try:
            fn()
            print(f"  ok   {fn.__name__}")
        except Exception:
            failed += 1
            print(f"  FAIL {fn.__name__}")
            traceback.print_exc()
    print(f"\n{len(fns) - failed}/{len(fns)} passed")
    raise SystemExit(1 if failed else 0)

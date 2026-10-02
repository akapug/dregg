#!/usr/bin/env python3
r"""check-lean-hard-mode.py — run the verified-gate tests that DECIDE against the linked Lean, in
hard mode, filtered, and refuse unless every one of them actually ran and passed.

ANSWERS:         with DREGG_REQUIRE_LEAN=1 DREGG_TEST_REQUIRE_LEAN=1 (and the missing-Lean opt-out
                 scrubbed), do dregg-node's `finality_gate`, `poa_signal_genesis` and
                 `poa_galley_genesis` tests and dregg-lean-ffi's `linked_archive_freshness` and
                 `poa_network_genesis_probe` pass — and did at least the floor number of each, and
                 every named anchor, run?
DOES NOT ANSWER: anything about the rest of either crate. This is deliberately NOT a `-p` suite:
                 it is the set that sat red for eight weeks (2026-08-08..10-01) because nothing ran
                 it with the Lean armed. Widen it by adding a module below, never by dropping the
                 filter.

⚑ WHY (2026-10-01). `finality_gate`'s verified-gate tests went red at `d182d10fc` (08-08: tau
moved to Cordial Miners Def. 6, a three-round lace finalizes one block) and the attacker-refusal
tooth went VACUOUS in the same commit; `poa_signal_genesis` went red when the signed bundle moved
from counter 2 to 12 (08-04..08-10) under a frozen tuple; `poa_galley_genesis` was red from its
birth commit (a dead federation id typed beside the artifact). No scheduled or local gate ran any
of them with the archive armed, so none of it was seen.

Floors and anchors: a filter that matches nothing, a renamed module, or a test that skips instead
of running all read as "0 failed" to nextest. So each module has a FLOOR (its test count at
landing) and a few ANCHORS (the tests whose silence cost the most) that must appear as PASS.
Lowering a floor needs the same review as deleting the tests it counts.

USAGE
  scripts/check-lean-hard-mode.py              # build + run (uses `swarm-build` when on PATH)
  scripts/check-lean-hard-mode.py --self-test  # the verdict reader can go red (no cargo)
  scripts/check-lean-hard-mode.py --verify LOG # re-read a saved nextest log

Exit 0 only when both invocations exit 0 AND every floor and anchor is met.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

HARD_ENV = {"DREGG_REQUIRE_LEAN": "1", "DREGG_TEST_REQUIRE_LEAN": "1"}
SCRUB_ENV = ("DREGG_TEST_ALLOW_MISSING_LEAN",)

# `--profile full`: its default-filter is all() (the -E below does the narrowing) and its
# slow-timeout is 60 s x 60. `default`'s 45 s x 4 kills a Lean-armed test process on a busy box
# before it finishes initializing the archive (measured ~175-360 s on hbox before node-init-86).
NODE_FILTER = ("test(/^finality_gate::/) or test(/^poa_signal_genesis::/) "
               "or test(/^poa_galley_genesis::/)")
INVOCATIONS = [
    ["cargo", "nextest", "run", "-p", "dregg-node", "--lib", "--profile", "full",
     "--no-fail-fast", "-E", NODE_FILTER],
    ["cargo", "nextest", "run", "-p", "dregg-lean-ffi", "--features", "lean-lib",
     "--profile", "full", "--no-fail-fast",
     "--test", "linked_archive_freshness", "--test", "poa_network_genesis_probe"],
]

# (crate, test-path prefix) -> minimum PASS count. Counts at landing (2026-10-01).
FLOORS = {
    ("dregg-node", "finality_gate::"): 6,
    ("dregg-node", "poa_signal_genesis::"): 13,
    ("dregg-node", "poa_galley_genesis::"): 6,
    ("dregg-lean-ffi", "linked_archive_freshness"): 2,
    ("dregg-lean-ffi", "poa_network_genesis_probe"): 3,
}
ANCHORS = [
    "finality_gate::tests::attacker_block_from_unenrolled_creator_is_refused_by_the_verified_rule",
    "finality_gate::tests::verified_gate_agrees_with_rust_tau_three_node",
    "finality_gate::tests::raw_order_export_agrees_with_projection_three_node",
    "finality_gate::tests::gate_on_super_ratifies_n5_c3_shape",
    "poa_signal_genesis::tests::exact_tuple_installs_and_crash_reopens_the_same_head",
    "poa_signal_genesis::tests::nonempty_generic_store_refuses_without_losing_the_commit",
    "poa_signal_genesis::tests::template_target_linked_lean_export_drives_the_real_store_ceremony",
    "poa_galley_genesis::tests::authored_content_opens_the_galley_organ",
    "the_linked_archive_is_not_older_than_its_lean_sources",
    "live_genesis_export_returns_exact_lean_bytes_hashes_and_embedded_images",
]

# `PASS [ 362.412s] ( 1/49) dregg-node finality_gate::tests::x` (counter optional across versions);
# integration-test binaries print `dregg-lean-ffi::linked_archive_freshness the_linked_…`.
RESULT = re.compile(
    r"^\s*(PASS|FAIL|SIGABRT|SIGSEGV|SIGKILL|TIMEOUT|LEAK-FAIL|ABORT)\s+\[[^\]]*\]\s+"
    r"(?:\(\s*\d+/\d+\)\s+)?(\S+)\s+(\S+)\s*$")


def verify(log: str) -> list[str]:
    """Every reason the run is NOT a pass, from nextest's own result lines. Empty = pass."""
    problems: list[str] = []
    passed: list[tuple[str, str]] = []
    for line in log.splitlines():
        m = RESULT.match(line)
        if not m:
            continue
        status, binary, test = m.groups()
        crate = binary.split("::", 1)[0]
        target = binary.split("::", 1)[1] if "::" in binary else ""
        if status == "PASS":
            passed.append((crate, f"{target}::{test}" if target else test))
        else:
            # nextest repeats each failure in its closing summary; report it once.
            if f"{status} {binary} {test}" not in problems:
                problems.append(f"{status} {binary} {test}")
    for (crate, prefix), floor in FLOORS.items():
        n = sum(1 for c, t in passed if c == crate and t.startswith(prefix))
        if n < floor:
            problems.append(f"FLOOR {crate} {prefix}: {n} passed < {floor}")
    for anchor in ANCHORS:
        if not any(t == anchor or t.endswith("::" + anchor) for _, t in passed):
            problems.append(f"ANCHOR not passed: {anchor}")
    return problems


def run() -> int:
    env = {k: v for k, v in os.environ.items() if k not in SCRUB_ENV}
    env.update(HARD_ENV)
    wrap = ["swarm-build"] if shutil.which("swarm-build") else []
    log_parts: list[str] = []
    rcs: list[int] = []
    for argv in INVOCATIONS:
        print("+ " + " ".join(f"{k}={v}" for k, v in HARD_ENV.items()) + " "
              + " ".join(wrap + argv), flush=True)
        proc = subprocess.run(wrap + argv, cwd=REPO, env=env, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True)
        sys.stdout.write(proc.stdout)
        log_parts.append(proc.stdout)
        rcs.append(proc.returncode)
    problems = verify("\n".join(log_parts))
    problems += [f"invocation {i + 1} exited {rc}" for i, rc in enumerate(rcs) if rc != 0]
    if problems:
        print("\nLEAN HARD-MODE GATE: RED")
        for p in problems:
            print("  " + p)
        return 1
    total = sum(1 for line in "\n".join(log_parts).splitlines()
                if (m := RESULT.match(line)) and m.group(1) == "PASS")
    print(f"\nLEAN HARD-MODE GATE: green — {total} tests passed in hard mode, "
          f"{len(FLOORS)} floors and {len(ANCHORS)} anchors met")
    return 0


def self_test() -> int:
    def line(status: str, binary: str, test: str) -> str:
        return f"        {status} [ 1.000s] ( 1/9) {binary} {test}"

    good = []
    for (crate, prefix), floor in FLOORS.items():
        binary = crate if prefix.endswith("::") else f"{crate}::{prefix}"
        for i in range(floor):
            test = f"{prefix}tests::filler_{i}" if prefix.endswith("::") else f"filler_{i}"
            good.append(line("PASS", binary, test))
    for anchor in ANCHORS:
        if "::" in anchor:
            good.append(line("PASS", "dregg-node", anchor))
        elif anchor.startswith("the_linked"):
            good.append(line("PASS", "dregg-lean-ffi::linked_archive_freshness", anchor))
        else:
            good.append(line("PASS", "dregg-lean-ffi::poa_network_genesis_probe", anchor))
    good_log = "\n".join(good)
    cases = {
        "control (every floor and anchor met)": (good_log, True),
        "a FAIL line": (good_log + "\n" + line("FAIL", "dregg-node",
                                               "finality_gate::tests::x"), False),
        "a SIGABRT (Lean archive missing)": (good_log + "\n" + line(
            "SIGABRT", "dregg-node", "poa_signal_genesis::tests::x"), False),
        "a TIMEOUT": (good_log + "\n" + line("TIMEOUT", "dregg-node",
                                             "poa_galley_genesis::tests::x"), False),
        "an anchor that did not run": ("\n".join(
            l for l in good if "authored_content_opens_the_galley_organ" not in l), False),
        "a filter that matched nothing": ("Starting 0 tests across 1 binary", False),
        "a renamed module (floor unmet)": (good_log.replace(" finality_gate::", " finality::"),
                                           False),
        "the old 1/9 red, verbatim": (good_log + "\n" + "        FAIL [ 379.424s] (11/19) "
                                      "dregg-node finality_gate::tests::"
                                      "raw_order_export_agrees_with_projection_three_node",
                                      False),
    }
    bad = 0
    for name, (log, want_pass) in cases.items():
        got = verify(log)
        ok = (not got) == want_pass
        print(f"{'ok ' if ok else 'BAD'} {name}: {'pass' if not got else 'red: ' + got[0]}")
        bad += 0 if ok else 1
    if bad:
        print(f"SELF-TEST FAIL: {bad} case(s) misjudged")
        return 1
    print(f"self-test: {len(cases)} cases judged correctly (1 control passes, "
          f"{len(cases) - 1} plants red)")
    return 0


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "--self-test":
        return self_test()
    if len(sys.argv) > 2 and sys.argv[1] == "--verify":
        with open(sys.argv[2], encoding="utf-8", errors="replace") as handle:
            problems = verify(handle.read())
        for p in problems:
            print("  " + p)
        print("RED" if problems else "green")
        return 1 if problems else 0
    if len(sys.argv) > 1:
        print(__doc__)
        return 2
    return run()


if __name__ == "__main__":
    raise SystemExit(main())

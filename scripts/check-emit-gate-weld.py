#!/usr/bin/env python3
"""check-emit-gate-weld.py — THE CROSS-LANGUAGE WELD GATE for the emit-gate pairs.

Each `circuit-prove/tests/*_emit_gate.rs` embeds a GOLDEN_JSON string literal that is
DOCUMENTED as byte-identical to a `#guard emitVmJson2 <desc> == "..."` (or v1
`emitJson`/`emitVmJson`) string in a `metatheory/Dregg2/Circuit/Emit/*.lean` file.
The Lean `#guard` pins the Lean side (checked at `lake build` time); the Rust test
pins the Rust side (checked at `cargo test` time). But NOTHING EXECUTABLE compared
the two literals to each other: each side is welded only to itself, so the pair can
drift while both stay green — a gate comparing two checked-in copies of the same
claim validates nothing about their agreement.

This script closes that seam STATICALLY (no lake, no cargo, <1s):
  1. For every emit-gate Rust file, extract each raw-string descriptor literal
     (r#"{"name":...}"#) and parse its "name".
  2. Collect the AUTHORITATIVE pins: every #guard-pinned JSON string in the Lean
     tree (Lean escaped string literals whose payload parses as a descriptor with
     a "name"), plus every `circuit/descriptors/**.json` artifact (those are
     generate-fresh-gated by scripts/check-descriptor-drift.sh, so byte-equality
     to one of them inherits that gate).
  3. For each Rust golden, find a pin with the same descriptor name and require
     BYTE EQUALITY.

Exit 0 = every Rust golden is byte-identical to an authoritative pin.
Exit 1 = a drifted pair (named on both sides, bytes differ) or a Rust golden with
         no pin anywhere (an unwelded golden — its gate certifies only itself).

A drifted pair means one side moved and the other kept certifying the old bytes —
exactly the silent divergence the emit gates claim ("neither can silently diverge")
but could not themselves enforce.

Also prints (informational, non-gating) the reverse gap: Lean #guard-pinned
descriptor names with NO Rust-side counterpart at all (neither a test golden nor
a checked-in artifact) — Lean-emitted descriptors nothing on the Rust side
validates against.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
GATES_DIR = ROOT / "circuit-prove" / "tests"
LEAN_DIRS = [ROOT / "metatheory" / "Dregg2" / "Circuit" / "Emit", ROOT / "metatheory"]

# Rust raw-string literals that look like a descriptor JSON object.
RUST_RAW = re.compile(r'r#"(\{.*?\})"#', re.DOTALL)

# A Lean string literal (double-quoted, backslash escapes), possibly spanning lines.
LEAN_STR = re.compile(r'"((?:[^"\\]|\\.)*)"', re.DOTALL)


def lean_unescape(s: str) -> str:
    # Lean string escapes relevant here: \" \\ \n \t (descriptor JSON uses only \" and \\).
    out = []
    i = 0
    while i < len(s):
        c = s[i]
        if c == "\\" and i + 1 < len(s):
            n = s[i + 1]
            out.append({"n": "\n", "t": "\t", '"': '"', "\\": "\\"}.get(n, n))
            i += 2
        else:
            out.append(c)
            i += 1
    return "".join(out)


def descriptor_name(payload: str) -> str | None:
    if not payload.lstrip().startswith("{"):
        return None
    try:
        v = json.loads(payload)
    except json.JSONDecodeError:
        return None
    if isinstance(v, dict) and isinstance(v.get("name"), str) and "constraints" in v:
        return v["name"]
    return None


def collect_lean_pins() -> dict[str, list[tuple[Path, str]]]:
    pins: dict[str, list[tuple[Path, str]]] = {}
    seen: set[Path] = set()
    for d in LEAN_DIRS:
        for f in sorted(d.glob("*.lean")):
            if f in seen:
                continue
            seen.add(f)
            text = f.read_text(encoding="utf-8", errors="replace")
            if "#guard" not in text:
                continue
            for m in LEAN_STR.finditer(text):
                payload = lean_unescape(m.group(1))
                name = descriptor_name(payload)
                if name:
                    pins.setdefault(name, []).append((f, payload))
    return pins


def collect_artifact_pins() -> dict[str, list[tuple[Path, str]]]:
    """Every circuit/descriptors/**.json artifact, keyed by descriptor name.

    These are drift-gated by scripts/check-descriptor-drift.sh (generate-fresh
    from Lean), so a golden byte-equal to one of them inherits that gate. A
    trailing newline on the artifact is tolerated (the directory's convention is
    mixed and FP-pinned; a Rust golden never carries it).
    """
    pins: dict[str, list[tuple[Path, str]]] = {}
    desc_dir = ROOT / "circuit" / "descriptors"
    for f in sorted(desc_dir.rglob("*.json")):
        text = f.read_text(encoding="utf-8", errors="replace")
        name = descriptor_name(text)
        if name:
            pins.setdefault(name, []).append((f, text.rstrip("\n")))
    # The staged registries are TSVs of `key<TAB>name<TAB>json` rows — same authority
    # (emitted + drift-gated), just packed.
    for f in sorted(desc_dir.rglob("*.tsv")):
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            parts = line.split("\t")
            for cell in parts:
                name = descriptor_name(cell)
                if name:
                    pins.setdefault(name, []).append((f, cell))
    return pins


def main() -> int:
    lean_pins = collect_lean_pins()
    artifact_pins = collect_artifact_pins()
    failures: list[str] = []
    checked = 0
    unpinned: list[str] = []
    rust_names: set[str] = set()

    # EVERY test in the directory, not just `*_emit_gate.rs` — the `*_audit_extra` /
    # `*_audit_*` teeth embed the same goldens and rot identically (found: the fold
    # audit-extra still carried the pre-fix 17-constraint descriptor after the gate
    # itself was re-welded).
    for rf in sorted(GATES_DIR.glob("*.rs")):
        text = rf.read_text(encoding="utf-8", errors="replace")
        for m in RUST_RAW.finditer(text):
            payload = m.group(1)
            name = descriptor_name(payload)
            if not name:
                continue
            checked += 1
            rust_names.add(name)
            rel = rf.relative_to(ROOT)
            pins = lean_pins.get(name, []) + artifact_pins.get(name, [])
            if not pins:
                unpinned.append(
                    f"  {rel}: `{name}` has NO pin anywhere (no Lean #guard, no "
                    f"circuit/descriptors artifact) — the gate certifies only itself"
                )
                continue
            if any(payload == p for _, p in pins):
                continue
            # Named on both sides but the bytes differ: the drifted pair.
            lf = pins[0][0].relative_to(ROOT)
            pin_payload = pins[0][1]
            try:
                rj, lj = json.loads(payload), json.loads(pin_payload)
                detail = (
                    f" (Rust: {len(rj.get('constraints', []))} constraints"
                    f" / pin: {len(lj.get('constraints', []))} constraints)"
                )
            except json.JSONDecodeError:
                detail = ""
            failures.append(
                f"  DRIFTED: `{name}`{detail}\n"
                f"    Rust golden: {rel}\n"
                f"    Pin:         {lf}\n"
                f"    The Rust gate is green against STALE bytes — it certifies a descriptor\n"
                f"    the Lean emission no longer produces."
            )

    print(f"check-emit-gate-weld: {checked} Rust goldens checked against "
          f"{sum(len(v) for v in lean_pins.values())} Lean #guard pins + "
          f"{sum(len(v) for v in artifact_pins.values())} descriptor artifacts.")

    # ARM THE GATE. If the extraction found ZERO Rust goldens there is nothing to weld,
    # and every check below vacuously "passes" — the gate would print PASS having verified
    # NOTHING. That happens on a silent drift of the harness itself: GATES_DIR renamed, or
    # the raw-string convention changing from `r#"…"#` to `r##"…"##` (needed when a golden
    # contains `"#`) so RUST_RAW stops matching. A weld gate that welds nothing is exactly
    # the "mechanism that cannot tell you it did nothing" — fail LOUD instead of green.
    if checked == 0:
        print(
            "\ncheck-emit-gate-weld: FATAL — found ZERO Rust emit-gate goldens to weld.\n"
            f"  Scanned {GATES_DIR.relative_to(ROOT)}/*.rs with the r#\"…\"# extractor and\n"
            "  extracted no descriptor literals. The harness has drifted out from under this\n"
            "  gate (tests moved, or the raw-string delimiter changed) — it is NOT a clean\n"
            "  tree with nothing to check. Re-point GATES_DIR / RUST_RAW.",
            file=sys.stderr,
        )
        return 2

    # The reverse gap (informational): Lean #guard-pinned descriptors nothing Rust-side touches.
    artifact_names = set(artifact_pins)
    orphans = sorted(n for n in lean_pins if n not in rust_names and n not in artifact_names)
    if orphans:
        print(f"\nINFO — {len(orphans)} Lean #guard-pinned descriptor(s) with NO Rust-side "
              f"counterpart (no test golden, no checked-in artifact):")
        for n in orphans:
            src = lean_pins[n][0][0].relative_to(ROOT)
            print(f"  {n}  ({src})")

    if unpinned:
        print("\nUNPINNED goldens:")
        print("\n".join(unpinned))
    if failures:
        print("\nWELD FAILURES:")
        print("\n\n".join(failures))
        return 1
    if unpinned:
        return 1
    print("check-emit-gate-weld: PASS — every Rust golden is byte-identical to an authoritative pin.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

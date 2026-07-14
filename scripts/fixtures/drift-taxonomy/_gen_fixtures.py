#!/usr/bin/env python3
"""Generate the drift-taxonomy fixtures (synthetic descriptor sets).

Four sibling descriptor-set directories exercise every class of the classifier:

  old/            the base cohort  (2-member registry + 1 standalone descriptor)
  unchanged/      a byte-identical copy of old/                 -> UNCHANGED
  tail-append/    old/ + a new registry row appended at the tail
                  + a withMintHashPin-style tail PI (pi_index 46, trace_width
                  UNCHANGED) added to an existing member         -> TAIL-APPEND
  geometry-widen/ old/ but an existing member's trace_width moved -> GEOMETRY-WIDEN

Run:  python3 scripts/fixtures/drift-taxonomy/_gen_fixtures.py
(re-emits the fixtures byte-identically; the checked-in fixtures are the output).
"""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent

PI_PREFIX = 46  # matches the classifier default; tail bindings live at pi_index >= 46.


def pi_binding(col, pi_index, row="first"):
    return {"t": "pi_binding", "row": row, "col": col, "pi_index": pi_index}


def member(name, trace_width, pic, binds):
    # A minimal-but-realistic descriptor: a couple of ordinary gates + the pi_bindings.
    return {
        "name": name,
        "ir": 2,
        "trace_width": trace_width,
        "public_input_count": pic,
        "constraints": [
            {"t": "gate", "body": {"t": "var", "v": 3}},
            *binds,
        ],
        "hash_sites": [],
        "ranges": [],
    }


def compact(obj):
    # TSV rows carry compact single-line JSON (matching the real registry).
    return json.dumps(obj, separators=(",", ":"))


def write_set(name, registry_rows, standalones):
    d = HERE / name
    d.mkdir(parents=True, exist_ok=True)
    # registry.tsv : key<TAB>name<TAB>json  (one row per member, trailing newline)
    lines = [f"{k}\t{obj['name']}\t{compact(obj)}" for (k, obj) in registry_rows]
    (d / "registry.tsv").write_text("\n".join(lines) + "\n")
    for obj in standalones:
        (d / f"{obj['name']}.json").write_text(json.dumps(obj, indent=1) + "\n")


# ---- the base cohort (old/) -------------------------------------------------

def base_registry():
    return [
        ("memberA", member(
            "dregg-fix-a", trace_width=188, pic=42,
            binds=[pi_binding(30, 20), pi_binding(56, 41)])),
        ("memberB", member(
            "dregg-fix-b", trace_width=188, pic=42,
            binds=[pi_binding(30, 20)])),
    ]


def base_standalone():
    return member("dregg-fix-standalone", trace_width=96, pic=2, binds=[pi_binding(10, 0)])


def main():
    # old/
    write_set("old", base_registry(), [base_standalone()])

    # unchanged/  — byte-identical copy
    write_set("unchanged", base_registry(), [base_standalone()])

    # tail-append/  — memberA gains a TAIL pin (pi_index 46, trace_width UNCHANGED, pic
    # 42->43), a brand-new memberC is appended at the tail; standalone untouched.
    ta_reg = [
        ("memberA", member(
            "dregg-fix-a", trace_width=188, pic=43,
            binds=[pi_binding(30, 20), pi_binding(56, 41), pi_binding(70, 46)])),
        ("memberB", member(
            "dregg-fix-b", trace_width=188, pic=42,
            binds=[pi_binding(30, 20)])),
        ("memberC", member(
            "dregg-fix-c", trace_width=188, pic=42,
            binds=[pi_binding(30, 20)])),
    ]
    write_set("tail-append", ta_reg, [base_standalone()])

    # geometry-widen/  — memberA's trace_width moves 188 -> 200 (carrier geometry
    # widened); everything else identical to old/.
    gw_reg = [
        ("memberA", member(
            "dregg-fix-a", trace_width=200, pic=42,
            binds=[pi_binding(30, 20), pi_binding(56, 41)])),
        ("memberB", member(
            "dregg-fix-b", trace_width=188, pic=42,
            binds=[pi_binding(30, 20)])),
    ]
    write_set("geometry-widen", gw_reg, [base_standalone()])

    print("wrote fixtures under", HERE)


if __name__ == "__main__":
    main()

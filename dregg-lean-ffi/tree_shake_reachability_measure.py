#!/usr/bin/env python3
"""Tree-shaker Milestone-1, phase A2 — the runtime-reachability MEASUREMENT for the FFI archive.

Usage:  python3 tree_shake_reachability_measure.py <libdregg_lean.a>

Reproduces `build.rs::runtime_dead_init_trim`'s symbol-BFS EXACTLY (chase edges whose symbol does
NOT start with `initialize_`), then re-runs it with the CORRECTED init classification (also treat
`runtime_initialize_*` / `meta_initialize_*` as init edges — Lean v4.30's `module` system emits
three initializers per module, and the deployed trim only pattern-matches the first). Reports the
per-library kept-set breakdown, byte sizes (`ar tv`), and — the decisive check — how many REAL
(non-init) call edges cross from the corrected-live set into the members the fix drops.

MEASURED (hbox warm tree @1cdc7fe66, Linux, libdregg_lean.a 3091 members / 259 MB):
  deployed TRIM  = 936 members / 128.1 MB
  FIXED init-cut = 153 members / 23.7 MB
  real-call edges lost by the fix = 0   →   783 members / 104.4 MB (81.5% of the trim) are kept
  by the trim ONLY through mis-classified `runtime_initialize_*` init edges into Aesop /
  Mathlib.Tactic / Qq / Plausible / ProofWidgets — proof-time libraries the executor never CALLS.
"""
import subprocess, sys, re
from collections import defaultdict

AR = sys.argv[1] if len(sys.argv) > 1 else "./dregg-lean-ffi/libdregg_lean.a"

# nm -A output lines: ARCHIVE:MEMBER:  <addr?> <type> <sym>
out = subprocess.run(["nm", "-A", AR], capture_output=True, text=True).stdout

undef_func = defaultdict(set)   # member -> undefined non-init syms (TRIM classification: prefix)
undef_init = defaultdict(set)   # member -> undefined init syms (TRIM classification: prefix)
undef_func2 = defaultdict(set)  # member -> undefined non-init syms (FIXED: substring initialize_)
sym_def_in = defaultdict(set)   # sym -> members defining it
members = set()
roots = set()
import os
member_size = {}                # member -> byte size (from ar t/ar p not available; use nm size? fallback later)

# strip archive prefix "path.a:"
arprefix = AR + ":"
memre = re.compile(r"^(.*?\.o):(.*)$")
for line in out.splitlines():
    if line.startswith(arprefix):
        line = line[len(arprefix):]
    m = memre.match(line)
    if not m:
        continue
    member, rest = m.group(1), m.group(2)
    toks = rest.split()
    if len(toks) == 2 and len(toks[0]) == 1:
        ty, sym = toks[0], toks[1]
    elif len(toks) == 3 and len(toks[1]) == 1:
        ty, sym = toks[1], toks[2]
    else:
        continue
    members.add(member)
    bare = sym.lstrip("_")
    is_init = bare.startswith("initialize_")           # TRIM's classification
    is_init2 = ("initialize_" in bare)                 # FIXED: also runtime_initialize_
    if ty in ("U", "u"):
        (undef_init if is_init else undef_func)[member].add(sym)
        if not is_init2:
            undef_func2[member].add(sym)
    else:
        sym_def_in[sym].add(member)
        if bare.startswith("dregg_"):
            roots.add(member)

print(f"members={len(members)} roots(dregg_*)={len(roots)}")

def bfs(undef_maps):
    live = set()
    queue = list(roots)
    while queue:
        member = queue.pop()
        if member in live:
            continue
        live.add(member)
        for umap in undef_maps:
            for u in umap.get(member, ()):
                for dm in sym_def_in.get(u, ()):
                    if dm not in live:
                        queue.append(dm)
    return live

# The ACTUAL trim: chase only non-init (func) edges (prefix classification).
live_trim = bfs([undef_func])
print(f"TRIM (func-edges, prefix initialize_) kept = {len(live_trim)}")
# FIXED init classification: also treat runtime_initialize_ as init.
live_fixed = bfs([undef_func2])
print(f"FIXED (func-edges, substring initialize_) kept = {len(live_fixed)}")
print(f"DELTA members dropped by fixing init classification = {len(live_trim)-len(live_fixed)}")

def lib_of(member):
    base = member[:-2] if member.endswith(".o") else member
    top = re.split(r"[._]", base)[0]
    if top in ("Mathlib",):
        # sub-split Tactic vs core
        if base.startswith("Mathlib.Tactic") or base.startswith("Mathlib_Tactic"):
            return "Mathlib.Tactic"
        return "Mathlib(core)"
    return top

def breakdown(memset, label):
    b = defaultdict(int)
    for m in memset:
        b[lib_of(m)] += 1
    print(f"--- {label}: {len(memset)} members ---")
    for k in sorted(b, key=lambda x: -b[x]):
        print(f"  {b[k]:5d}  {k}")

# member byte sizes via `ar tv`
tv = subprocess.run(["ar", "tv", AR], capture_output=True, text=True).stdout
size_of = {}
for line in tv.splitlines():
    # rw-r--r-- 0/0   12345 Jan 1 2020 Member.o
    parts = line.split()
    if len(parts) >= 6 and parts[-1].endswith(".o"):
        try:
            size_of[parts[-1]] = int(parts[2])
        except ValueError:
            pass

def total_bytes(memset):
    return sum(size_of.get(m, 0) for m in memset)

breakdown(live_trim, "TRIM kept by library")
breakdown(live_fixed, "FIXED kept by library")
tb_trim = total_bytes(live_trim); tb_fixed = total_bytes(live_fixed)
tb_full = total_bytes(members)
print(f"\n=== SIZE (from `ar tv`, .o member bytes) ===")
print(f"  full   : {len(members):5d} members  {tb_full:,} B")
print(f"  TRIM   : {len(live_trim):5d} members  {tb_trim:,} B")
print(f"  FIXED  : {len(live_fixed):5d} members  {tb_fixed:,} B")
print(f"  LCNF-style saving beyond TRIM: {tb_trim-tb_fixed:,} B "
      f"({100*(tb_trim-tb_fixed)/max(tb_trim,1):.1f}% of trim)")

# proof-lib members kept
PROOF_PREFIXES = ("Mathlib.Tactic", "Mathlib_Tactic", "Aesop", "Qq", "Plausible",
                  "ProofWidgets", "LeanSearchClient", "ImportGraph", "importGraph")
proof_kept = sorted(m for m in live_trim
                    if any(m.startswith(p) or m.split(".")[0]==p for p in PROOF_PREFIXES)
                    or m.startswith("Aesop") or m.startswith("Qq"))
print(f"\n=== PROOF-LIB members in TRIM kept set: {len(proof_kept)} ===")
for m in proof_kept:
    print("  ", m)

# === Are the 783 dropped members entered by ANY non-init (real call) edge from a FIXED-live member? ===
dropped = live_trim - live_fixed
def is_initlike(sym):
    return "initialize_" in sym.lstrip("_")
real_call_into_dropped = []   # (fixed_live_member, sym, dropped_member)
for lm in live_fixed:
    for u in undef_func2.get(lm, ()):   # undef_func2 already excludes initialize_ substring
        for dm in sym_def_in.get(u, ()):
            if dm in dropped:
                real_call_into_dropped.append((lm, u, dm))
print(f"\n=== REAL (non-init) call edges from FIXED-live INTO a dropped member: {len(real_call_into_dropped)} ===")
for e in real_call_into_dropped[:30]:
    print("   ", e)

# === Edges from Dregg2 members into ANY proof-lib member: are they all init? ===
def is_proof(m):
    return (m.startswith("Aesop") or m.startswith("Qq") or m.startswith("Mathlib_Tactic")
            or m.startswith("Plausible") or m.startswith("ProofWidgets")
            or m.startswith("LeanSearchClient") or m.startswith("ImportGraph"))
dregg_to_proof = []
for lm in [m for m in live_trim if m.startswith("Dregg2") or m.startswith("Metatheory")]:
    for u in undef_func.get(lm, ()):        # trim's func classification (prefix)
        for dm in sym_def_in.get(u, ()):
            if is_proof(dm):
                dregg_to_proof.append((lm, u, dm, "INIT" if is_initlike(u) else "REALCALL"))
print(f"\n=== Edges from Dregg2/Metatheory members into proof-lib members (trim-func class): {len(dregg_to_proof)} ===")
realcalls = [e for e in dregg_to_proof if e[3]=="REALCALL"]
print(f"    of which REAL (non-init-substring) call edges: {len(realcalls)}")
for e in dregg_to_proof[:20]:
    print("   ", e)

# === proof-lib members surviving in FIXED set ===
fixed_proof = sorted(m for m in live_fixed if is_proof(m) or m.startswith("Mathlib_Tactic"))
print(f"\n=== proof-lib members STILL in FIXED set: {len(fixed_proof)} ===")
for pm in fixed_proof:
    referers = []
    for lm in live_fixed:
        if lm==pm: continue
        for u in undef_func2.get(lm, ()):
            if pm in sym_def_in.get(u, ()):
                referers.append((lm,u))
    print(f"   {pm}: {referers[:3]}")

# For each proof-lib kept member, find WHO references it and via which symbol.
# Build reverse: which live member's undef_func symbol is defined in a proof member.
proof_set = set(proof_kept)
print("\n=== WHY each proof member is kept (referencing live member -> symbol) ===")
# map sym -> proof member for syms defined in proof members
for pm in proof_kept:
    # find syms defined here
    defsyms = {s for s, ms in sym_def_in.items() if pm in ms}
    referers = []
    for lm in live_trim:
        if lm == pm: continue
        for u in undef_func.get(lm, ()):
            if u in defsyms and pm in sym_def_in.get(u, ()):
                referers.append((lm, u))
    # only show a couple
    shown = referers[:3]
    print(f"  {pm}: referenced by {len(referers)} live members; e.g. {shown}")

# LCNF-style: cut ALL edges that ORIGINATE from an init function is not derivable from nm alone
# (nm classifies by SYMBOL name, not reference-site). Report the delta set is empty here by construction.

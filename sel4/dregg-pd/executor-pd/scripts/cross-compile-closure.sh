#!/usr/bin/env bash
#
# cross-compile-closure.sh — ELF-recompile the verified-executor Lean closure
# for the bare-metal seL4 aarch64 target.
#
# THE HEART, step (1) of the executor-PD excision plan (.docs-history-noclaude/SEL4-EMBEDDING.md §2,
# .docs-history-noclaude/FIRMAMENT.md §6): the compiled Lean closure (`libdregg_lean.a`) is Mach-O
# arm64 (the macOS host build); the seL4 target is ELF aarch64. The whole closure
# must be RECOMPILED with the Lean toolchain's clang targeting an ELF triple — a
# recompile, not a relink.
#
# PROVEN (2026-06-13): this works. The Dregg2 `:c` facets emitted by `lake build`
# compile cleanly to ELF aarch64 with ZERO source changes, and the executor FFI
# entry `dregg_exec_full_forest_auth` survives into the ELF closure. The
# object-format wall — the part the roadmap called "weeks-to-a-quarter fog" — is
# PASSABLE on the native macOS host with the in-toolchain clang.
#
# THE CLOSURE IS PRINCIPLED (EMBEDDABLE-LEAN-RUNTIME.md §4 #2): rather than
# globbing every facet `lake build` emitted (~820, the whole proof/circuit tree),
# this compiles exactly the transitive IMPORT closure rooted at `Dregg2.Exec.FFI`
# (the module that `@[export]`s the executor entry) — 77 local modules — MINUS the
# one runtime-dead leaf `Dregg2.Tactics` (pure metaprogramming; see the closure
# block below). Excluding `Tactics.c` SEVERS the elaborator at the shape of the
# archive: it is the only facet in the closure that calls `initialize_Lean`, so
# the Lean elaborator/kernel init-chain is never pulled — replacing the prior
# link-order no-op shadow with a true closure boundary.
#
# What this script does NOT yet do (the precise remaining wall, see WALL.md):
#   * It compiles the Dregg2 IR facets (pure Lean → C → ELF). It does NOT
#     recompile the Lean RUNTIME (leanrt/leancpp/Init/Std/Lean), because the
#     toolchain ships those only as Mach-O `.a` — the C++ runtime SOURCES
#     (`init_module.cpp`, `object.cpp`, …) are NOT in $LEAN_SYSROOT/src. Getting
#     an ELF leanrt requires the upstream lean4 repo at the toolchain commit.
#   * It therefore produces `libdregg_lean_elf.a` (the application closure), the
#     INPUT to the final link — not the linked PD. The link needs the ELF runtime.
#
# Usage:
#   ./cross-compile-closure.sh [OUT_DIR]
# Env:
#   LEAN_SYSROOT   (default: `lean --print-prefix`)
#   METATHEORY     (default: repo-root/metatheory) — must have `.lake/build/ir`
#   TARGET         (default: aarch64-unknown-none) — the ELF triple
set -euo pipefail

LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
METATHEORY="${METATHEORY:-$(cd "$HERE/../../../../metatheory" && pwd)}"
TARGET="${TARGET:-aarch64-unknown-none}"
OUT_DIR="${1:-$HERE/../out}"

CLANG="$LEAN_SYSROOT/bin/clang"
# Use the toolchain's llvm-ar: the host BSD `ar` mangles cross-arch (ELF on a
# Mach-O host) archives, collapsing members and running a Mach-O-only ranlib.
AR="$LEAN_SYSROOT/bin/llvm-ar"
# The Lean toolchain's clang ships its freestanding headers (stddef.h, stdint.h,
# stdarg.h) under include/clang, NOT the usual resource-dir/include. The Lean C
# runtime header lives under include/lean.
FREESTANDING_INC="$LEAN_SYSROOT/include/clang"
LEAN_INC="$LEAN_SYSROOT/include"

IR_DIR="$METATHEORY/.lake/build/ir"
if [ ! -d "$IR_DIR" ]; then
    echo "ERROR: $IR_DIR not found. Run 'lake build' in $METATHEORY first" >&2
    echo "(the C facets are emitted by the lake :c facet; see dregg-lean-ffi/build.rs)" >&2
    exit 1
fi

# Start the object dir CLEAN: the archive globs obj/*.o, so a stale object from a
# prior (untrimmed) run would silently re-enter the closure — including the very
# Tactics.o this trim excludes. Rebuild the closure from exactly the facet list.
rm -rf "$OUT_DIR/obj"
mkdir -p "$OUT_DIR/obj"
echo "[xcompile] LEAN_SYSROOT=$LEAN_SYSROOT"
echo "[xcompile] TARGET=$TARGET   IR_DIR=$IR_DIR"

# ─── The PRINCIPLED closure: the executor's import-reachable facets, MINUS the
#     runtime-dead tactic module (EMBEDDABLE-LEAN-RUNTIME.md §4 #2) ───
#
# The compiled closure is NOT "every Dregg2 + Metatheory facet `lake build`
# emitted" (~820 facets — the whole proof/circuit/distributed tree). It is the
# transitive IMPORT closure rooted at `Dregg2.Exec.FFI` (the module that
# `@[export]`s `dregg_exec_full_forest_auth`) — the only facets the executor can
# reach. That root closure is 77 local modules.
#
# Within it, exactly one module is RUNTIME-DEAD: `Dregg2.Tactics`. It is a pure
# metaprogramming module (`#assert_axioms`/`#assert_clean` command `elab`s + the
# `dregg_auto`/`option_inj`/… proof-automation `macro`s) — its compiled facet
# `Tactics.c` `LEAN_EXPORT`s ZERO `l_Dregg2_*` runtime functions, only its module
# initializer `initialize_Dregg2_Dregg2_Tactics`. The 22 executor facets that
# `import Dregg2.Tactics` use only its compile-time macros (expanded during the
# proof build); none CALL a runtime symbol from it. But `initialize_Dregg2_Dregg2_
# Tactics` (which the toolchain emits to chain into `initialize_Lean` + the
# mathlib `Tactic.Tauto`/`Ring` inits) drags the WHOLE Lean elaborator/kernel into
# the init-chain at module load.
#
# So we PRINCIPALLY TRIM it: `Tactics.c` is excluded from the closure archive
# entirely — the elaborator is never PULLED, because the only facet that ever
# calls `initialize_Lean` is `Tactics.c` itself (verified: 1 caller in the whole
# closure). `initialize_Dregg2_Dregg2_Tactics` is then a genuine import-boundary
# symbol, resolved by the no-op in `init-stubs.c` (now a true closure-boundary
# stub, not a link-order shadow of a linked-but-dead facet). After the trim the
# closure has ZERO undefined `l_*` runtime symbols (verified) — it is
# runtime-self-contained.
#
# This excises the Lean elaborator at the SHAPE of the closure (the production
# form §4 #2 asks for), not at link time. The trim flows to BOTH the host-musl
# link-probe and the on-device seL4 ELF (both reuse this `libdregg_lean_elf.a`).
#
# RUNTIME_DEAD_TRIM: modules import-reachable from the executor but whose facet is
# runtime-dead (only metaprogramming). Excluded from the closure; their module
# init resolves to the `init-stubs.c` boundary no-op. (Today: just Tactics. If a
# future executor import adds another pure-tactic leaf, list its module here — the
# closure walk will otherwise pull its facet.)
RUNTIME_DEAD_TRIM="Dregg2.Tactics"

# Compute the import closure (rooted at the FFI entry module) → the exact facet
# set. Robust .lean import parse: skip block/line comments, stop at the first
# declaration/command (imports always precede the body). Emit one relative facet
# path per line, EXCLUDING the runtime-dead trim set.
CLOSURE_LIST="$OUT_DIR/closure-facets.txt"
python3 - "$METATHEORY" "$IR_DIR" "$RUNTIME_DEAD_TRIM" > "$CLOSURE_LIST" <<'PY'
import os, sys
SRC, IR, TRIM = sys.argv[1], sys.argv[2], set(sys.argv[3].split())
def mod_file(m): return os.path.join(SRC, m.replace('.', '/') + ".lean")
def imports(path):
    out=[]
    try: f=open(path, encoding="utf-8", errors="replace")
    except FileNotFoundError: return None   # external (Mathlib/Lean/Std/…): no local src
    in_block=False
    DECL=("namespace","open","def","theorem","lemma","instance","structure",
          "inductive","@[","section","universe","variable","set_option","abbrev",
          "class","mutual","macro","syntax","elab","notation","#","attribute",
          "deriving","example","partial","unsafe","noncomputable","prelude")
    for raw in f:
        s=raw.strip()
        if s.startswith("/-"):
            in_block = not s.endswith("-/"); continue
        if in_block:
            if s.endswith("-/"): in_block=False
            continue
        if s.startswith("--") or s=="": continue
        if s.startswith("import "): out.append(s.split()[1]); continue
        if s.startswith(DECL): break
    f.close(); return out
seen=set(); stack=["Dregg2.Exec.FFI"]
while stack:
    m=stack.pop()
    if m in seen: continue
    seen.add(m)
    imps=imports(mod_file(m))
    if imps is None: continue
    for i in imps:
        if i not in seen: stack.append(i)
# local modules with a compiled facet, minus the runtime-dead trim
facets=[]
for m in sorted(seen):
    if m in TRIM: continue
    if not (m.startswith("Dregg2.") or m.startswith("Metatheory.") or m in ("Dregg2","Metatheory")):
        continue
    c=os.path.join(IR, m.replace('.', '/')+".c")
    if os.path.exists(c): facets.append(os.path.relpath(c, IR))
for r in facets: print(r)
PY
n_closure="$(wc -l < "$CLOSURE_LIST" | tr -d ' ')"
if [ "$n_closure" -lt 50 ]; then
    echo "[xcompile] ERROR: closure walk produced only $n_closure facets (<50) — the" >&2
    echo "[xcompile]   import parse or IR_DIR is wrong; refusing to build a hollow closure." >&2
    exit 1
fi
echo "[xcompile] executor import-closure (rooted at Dregg2.Exec.FFI): $n_closure facets"
echo "[xcompile]   (runtime-dead trim, elaborator-severing: $RUNTIME_DEAD_TRIM — EXCLUDED)"

ok=0; fail=0; failed=""
# Compile each closure facet. -ffreestanding: no hosted libc assumptions.
# The facet C is pure (decode→step→encode over Lean objects); it calls leanrt
# entry points (lean_nat_add, lean_alloc_ctor, …) that the final link resolves.
while IFS= read -r rel; do
    [ -z "$rel" ] && continue
    c="$IR_DIR/$rel"
    name="${rel%.c}"; name="${name//\//_}"
    if "$CLANG" --target="$TARGET" -ffreestanding -O1 -fno-exceptions \
            -isystem "$FREESTANDING_INC" -I "$LEAN_INC" \
            -c "$c" -o "$OUT_DIR/obj/$name.o" 2>"$OUT_DIR/obj/$name.err"; then
        ok=$((ok+1)); rm -f "$OUT_DIR/obj/$name.err"
    else
        fail=$((fail+1)); failed="$failed $name"
    fi
done < "$CLOSURE_LIST"

echo "[xcompile] closure facets: OK=$ok  FAIL=$fail"
if [ "$fail" -ne 0 ]; then
    echo "[xcompile] FAILED:$failed" >&2
    f="$(echo "$failed" | awk '{print $1}')"
    echo "[xcompile] first error ($f):" >&2
    head -12 "$OUT_DIR/obj/$f.err" >&2
    exit 1
fi

# Archive the ELF closure. This is `libdregg_lean_elf.a` — the application half
# of the link. (The runtime half — an ELF leanrt — is built by build-leanrt-elf.sh
# et al.) obj/ holds exactly the trimmed closure (cleaned above), so the glob is
# the closure.
rm -f "$OUT_DIR/libdregg_lean_elf.a"
"$AR" rcs "$OUT_DIR/libdregg_lean_elf.a" "$OUT_DIR"/obj/*.o
echo "[xcompile] wrote $OUT_DIR/libdregg_lean_elf.a"
file "$OUT_DIR/libdregg_lean_elf.a"
echo "[xcompile] members: $("$AR" t "$OUT_DIR/libdregg_lean_elf.a" | wc -l | tr -d ' ')"

# The principled-trim invariant: the elaborator-dragging tactic facet must NOT be
# in the archive (that is the whole cut). Fail loudly if it crept back in.
# (Capture first, then match — same SIGPIPE-under-pipefail avoidance as above.)
ar_members="$("$AR" t "$OUT_DIR/libdregg_lean_elf.a" 2>/dev/null || true)"
if [[ $'\n'"$ar_members"$'\n' == *$'\nDregg2_Tactics.o\n'* ]]; then
    echo "[xcompile] ⚠ TRIM VIOLATED: Dregg2_Tactics.o is in the closure archive —" >&2
    echo "[xcompile]   the elaborator init-chain would be pulled. Check RUNTIME_DEAD_TRIM." >&2
    exit 1
fi
echo "[xcompile] ✓ trim invariant: Dregg2_Tactics.o absent (elaborator init-chain severed)"

# Prove the executor entry survived into the ELF closure. (Use the host `nm`,
# which reads these host-emitted ELF objects correctly; the toolchain's
# `llvm-nm` mis-parses them on this macOS host.) Materialize the nm output first —
# piping straight into `grep -q` lets grep close the pipe on first match, which
# under `set -o pipefail` reports the SIGPIPE'd nm as a pipeline failure (a race
# that spuriously trips the check).
nm_out="$(nm "$OUT_DIR/libdregg_lean_elf.a" 2>/dev/null || true)"
if [[ "$nm_out" == *" T dregg_exec_full_forest_auth"* ]]; then
    echo "[xcompile] ✅ executor entry dregg_exec_full_forest_auth present in ELF closure (global text symbol)"
else
    echo "[xcompile] ⚠ executor entry NOT found — check Dregg2/Exec/FFI.c emitted" >&2
    exit 1
fi

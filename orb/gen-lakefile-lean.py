#!/usr/bin/env python3
# Deterministically convert lakefile.toml -> lakefile.lean, adding a per-OS
# `osLink` transform for the FFI/crypto exe link args:
#   macOS  -> prepend -Wl,-no_data_const (unchanged from today)
#   Linux  -> drop -no_data_const; insert ffi/glibc_isoc23_compat.o before
#             target/release/libaes_fallback.a (glibc C23 __isoc23_* aliases)
# and drop the hard-coded -L/opt/hacl-star path (HACL resolved via LIBRARY_PATH=$HACL_DIST).
#
# Run from the repo root:  python3 gen-lakefile-lean.py && rm lakefile.toml
# Faithful: on Linux `lake build orb` replays cached oleans (0 recompiles) then links.
import tomllib, json, re
d = tomllib.load(open("lakefile.toml", "rb"))
def s(x): return json.dumps(x)
def tgt(name): return name if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name) else "«%s»" % name
L = []
L += ["import Lake", "open Lake DSL", ""]
L += ["/-- Per-OS link args for the FFI/crypto-linking executables.",
      "    macOS: keep the data segment writable with `-Wl,-no_data_const` (ld64/__DATA_CONST",
      "    workaround; rejected by GNU/lld on Linux, so dropped there).",
      "    Linux: supply the glibc>=2.38 C23 symbols (__isoc23_sscanf/__isoc23_strtol) that",
      "    aws-lc in libaes_fallback.a references but the Lean toolchain glibc lacks, via the",
      "    ABI-identical aliases in ffi/glibc_isoc23_compat.o, inserted before that archive.",
      "    HACL/EverCrypt (-levercrypt) is resolved via LIBRARY_PATH (=$HACL_DIST, the project",
      "    convention) rather than a hard-coded -L path, so it is machine-independent. -/",
      "def osLink (core : Array String) : Array String :=",
      "  if System.Platform.isOSX then",
      "    #[\"-Wl,-no_data_const\"] ++ core",
      "  else",
      "    core.foldl (init := #[]) fun acc a =>",
      "      if a == \"target/release/libaes_fallback.a\" then",
      "        (acc.push \"ffi/glibc_isoc23_compat.o\").push a",
      "      else acc.push a", ""]
L += ["package drorb where", "  version := v!%s" % s(d["version"]), ""]
dtset = set(d["defaultTargets"])
for l in d["lean_lib"]:
    name = l["name"]; attr = "@[default_target] " if name in dtset else ""
    head = "%slean_lib %s" % (attr, tgt(name)); body = []
    if "srcDir" in l: body.append("  srcDir := %s" % s(l["srcDir"]))
    if "roots" in l: body.append("  roots := #[%s]" % ", ".join("`" + r for r in l["roots"]))
    if "globs" in l: body.append("  globs := #[%s]" % ", ".join("Glob.one `" + g for g in l["globs"]))
    L.append(head + " where\n" + "\n".join(body) if body else head)
for e in d["lean_exe"]:
    core = [a for a in e["moreLinkArgs"] if a not in ("-Wl,-no_data_const", "-L/opt/hacl-star/dist/gcc-compatible")]
    L += ["lean_exe %s where" % tgt(e["name"]),
          "  root := `%s" % e["root"],
          "  moreLinkArgs := osLink #[%s]" % ", ".join(s(a) for a in core)]
open("lakefile.lean", "w").write("\n".join(L) + "\n")
print("wrote lakefile.lean (%d libs, %d exes)" % (len(d["lean_lib"]), len(d["lean_exe"])))

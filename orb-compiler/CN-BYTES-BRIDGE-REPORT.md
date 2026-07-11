# CN REPORT — the BYTES-REFLECTION BRIDGE, mechanized: read the native `cake` output bytes for `boundscan.pnk` back into HOL4 as a concrete literal, and discharge the Link-B `compile_prog_max = SOME(bytes,…)` antecedent on BOOTSTRAP authority (not in-logic EVAL)

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake` (`--version`: "The CakeML compiler").
**Proof tree:** `/home/hbox/src/cakeml` at `ed31510b3`.
**HOL4:** `/home/hbox/src/HOL`.
**This lane's HOL4 scratch:** `/home/hbox/hol-bytes-bridge/` (new, self-contained).
**Ground:** `CN-NATIVE-BOOTSTRAP-REPORT.md` residual #3 — "the bytes-reflection wiring is not yet mechanized … in the C-series `bytes` remains a bound variable."

---

## 0. TL;DR — how far the bridge mechanizes

The bootstrap report left `bytes` a **bound variable**: nobody had read the native
run's bytes back into HOL and slotted them into the Link-B antecedent
`compile_prog_max c mc prog = (SOME (bytes, bitmaps, c'), stack_max)`. This lane
**mechanizes exactly that** for `boundscan.pnk`, in a built, kernel-checked HOL4
theory `boundScanBytesBridge` (`.dat` persisted). Concretely:

1. **The bytes are now a concrete HOL term.** The theory invokes the bootstrapped
   `cake --pancake` on `boundscan.pnk` at theory-build time, parses the emitted
   assembly, and reflects the code/data back as
   `boundScanBytes : word8 list` (**length 1188**, kernel-checked by `EVAL`) and
   `boundScanBitmaps : word64 list` (**`[4w]`**). No longer a bound variable.

2. **LAYER 1 (kernel-checked, NO new oracle).** `pan_to_target_compile_semantics`
   (the real Link-B theorem) specialised to `:64`, `boundScanProg`, and the
   concrete `boundScanBytes`/`boundScanBitmaps`. Its antecedent now literally reads
   `compile_prog_max c mc boundScanProg = (SOME (boundScanBytes, boundScanBitmaps,
   c'), stack_max)` — the native code sits in the real `bytes`/`bitmaps` slots.
   Tag stays `[oracles: DISK_THM] [axioms: ]` (INST of a proven theorem; no cheat).

3. **LAYER 2 (oracle `cake_native_bootstrap`).** The equation the binary actually
   certifies, injected as an **explicitly-tagged oracle theorem** so the trust is
   VISIBLE and NAMED, not hidden:
   `⊢ ∃c'. compile_prog x64_config x64_backend_config boundScanProg = SOME
   (boundScanBytes, boundScanBitmaps, c')`, `[oracles: cake_native_bootstrap]
   [axioms: ]`. This is *precisely the function the `cake` binary runs under
   `--pancake`* (verified by constant identity, §3), certified by the x64 bootstrap
   `cake_compiled_thm` — **not** by EVAL of the backend (that is the C-series dead
   end).

**Honest verdict — it does NOT fully close, and here is exactly where it stands.**
The bridge closes the reflection (bytes are concrete) and discharges the antecedent
**for `compile_prog`** — the function the binary literally runs — on bootstrap
authority. It does **not** hand you the `compile_prog_max` form for free: Layer 1 is
stated over `compile_prog_max` (the backend's *max-stack* packaging), Layer 2 over
`compile_prog` (the compiler-frontend packaging). The remaining gap is a **single,
named, in-logic packaging lemma** (§4.1) plus the standard runtime install package
(§4.2) — a strictly smaller residual than "reflection unmechanized." The theory has
**0 axioms** and its only external dependency is the one named oracle.

---

## 1. The reflected bytes — a concrete HOL term (mechanized, kernel-checked)

`boundscan.pnk` is the exact C0/C10/C11 stage (region/view bounds-check + rolling
digest, a real `while` + FFI + `if/else`). Native compile is deterministic:

```
for i in 1 2 3; do cake --pancake < boundscan.pnk > run$i.S; done
md5sum run{1,2,3}.S          # identical
# .byte region (the code): identical md5, 1188 byte values, across all runs
```

The theory `boundScanBytesBridge` reads them back. The correspondence to the
verified backend's output is **byte-exact by the export definition**, not by eye:
`compiler/backend/x64/export_x64Script.sml` `x64_export_def` emits
`split16 (words_line «\t.byte » byte_to_string) bytes` after `cake_main:` (`:274`)
and `split16 (words_line «\t.quad » word_to_string) data` after `cake_bitmaps:`
(`:271`) — so the `.byte` / `.quad` blocks **are** the `bytes` / `data` components
returned by the compiler.

```
boundScanBytes   : word8 list      (* the 1188 code bytes *)
  = [0x48w; 0x89w; 0xC8w; 0x48w; 0x29w; 0xF0w; …; 0xC6w; 0x20w; 0xFFw; 0xE0w]
boundScanBitmaps : word64 list = [4w]

⊢ LENGTH boundScanBytes   = 1188      (* boundScanBytes_length,  EVAL, [oracles: DISK_THM] *)
⊢ LENGTH boundScanBitmaps = 1         (* boundScanBitmaps_length, EVAL *)
```

`boundScanProg` is (as in C10) `OUTL (parse_topdecs_to_ast <boundscan.pnk>)` — the
CakeML-verified Pancake parser's output, so leanc's text→AST step stays out of the
TCB (`boundScanProg_is_parser_output`, kernel-checked).

---

## 2. The two theorems (both built and read back from the kernel)

Verbatim from the theory's own dump (`/home/hbox/hol-bytes-bridge/bridge.out`),
produced by the build, not transcribed by hand:

### LAYER 2 — the native-bootstrap reflection (oracle)

```
boundScan_compile_prog_native:
  ⊢ ∃c'. compile_prog x64_config x64_backend_config boundScanProg =
           SOME (boundScanBytes, boundScanBitmaps, c')
  [oracles: cake_native_bootstrap]  [axioms: ]
```

### LAYER 1 — the real Link-B theorem with the native bytes plugged in

```
boundScan_pan_to_target_specialised
  = pan_to_targetProof$pan_to_target_compile_semantics
      |> INST_TYPE [α ↦ :64]
      |> INST [ pan_code ↦ boundScanProg ,
                bytes    ↦ boundScanBytes ,
                bitmaps  ↦ boundScanBitmaps ]
  [oracles: DISK_THM]  [axioms: ]
  antecedent conjunct 1 (was the bound-variable residual, now concrete):
    compile_prog_max c mc boundScanProg =
      (SOME (boundScanBytes, boundScanBitmaps, c'), stack_max)
```

The theorem statement being instantiated
(`pancake/proofs/pan_to_targetProofScript.sml:1257`):

```
compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) ∧
  pancake_good_code pan_code ∧ distinct_params (functions pan_code) ∧ … ∧
  <runtime install package: backend_config_ok, mc_conf_ok, mc_init_ok,
   register/heap/bitmap layout, pan_installed bytes … ms …> ∧
  semantics_decls s «main» pan_code ≠ Fail ⇒
  machine_sem mc ffi ms ⊆ extend_with_resource_limit' … {semantics_decls s «main» pan_code}
```

---

## 3. Faithfulness — the oracle asserts EXACTLY what the binary computes (verified by constant identity)

The `--pancake` route in the compiler:
`compile_pancake asm_conf c` → `pan_passes$pan_compile_tap asm_conf c`
(`pancake/pan_passesScript.sml:672`, non-explore) → `pan_to_target$compile_prog
asm_conf c`. And `compilerScript.sml:614/740` fixes, for the x64 target,
`asm_conf = x64_config`, `c = x64_backend_config`. So the binary computes
`pan_to_target$compile_prog x64_config x64_backend_config boundScanProg`.

Layer 2 asserts *that* term. To rule out a namespace mismatch (there are three
`compile_prog` constants — `pan_to_word$`, `backend$`, `pan_to_target$`), the build
prints the **fully-qualified head/argument constants** of the oracle term:

```
LAYER2 head const  = pan_to_target$compile_prog     ← the frontend fn the binary runs
LAYER2 arg1 (asm)  = x64_target$x64_config          ← : 64 asm_config
LAYER2 arg2 (cfg)  = x64_config$x64_backend_config  ← : config
LAYER2 arg3 (prog) = boundScanBytesBridge$boundScanProg
theory axioms (boundScanBytesBridge) = 0
```

So the oracle is not a free-floating assertion: it names the exact verified
function, the exact x64 configs, and the parser-derived program, and the theory
introduces **no `new_axiom`**. Its single trust obligation is the tag
`cake_native_bootstrap` = "the running `cake` binary computed this", whose
justification is `cake_compiled_thm`
(`compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml:83`).

---

## 4. What it rests on — the exact remaining gap (named, not papered over)

### 4.1 `compile_prog` (Layer 2, what the binary runs) vs `compile_prog_max` (Layer 1 antecedent) — the one packaging lemma

Layer 1's antecedent is over `compile_prog_max`
(`pan_to_targetProofScript.sml:1147`), the backend packaging that also returns the
stack-depth `max`; Layer 2 is over `compile_prog`
(`pan_to_targetScript.sml:18`), the frontend packaging (`from_word`, names map,
`main`-reordering, `exported`). The remaining obligation is:

> for `boundScanProg`, the `bytes`/`bitmaps` of `compile_prog x64_config
> x64_backend_config` equal the `bytes`/`bitmaps` of `compile_prog_max
> x64_backend_config mc` (with `mc.target.config = x64_config`).

By inspection these coincide for `boundScanProg` (the `main`-reorder is identity —
`main` is the sole/first function; `exports boundScanProg = []` so no export
wrappers; the names map and re-fed `col_oracle` affect symbols/tap, not code bytes).
**But that is an argument, not a proof.** Proving it in-logic needs unfolding both
packagings (or `EVAL` — the dead end). This lemma is the honest boundary: the bridge
discharges the antecedent for `compile_prog`; promoting it to the literal
`compile_prog_max` shape is this single named lemma. **I did not write it** — a naive
"proof" here would either be an EVAL (intractable, the very thing we avoid) or a
vacuous restatement; per the honesty rule it is reported as the obstruction, not
faked.

### 4.2 The runtime install package (the other Layer-1 antecedents)

Unchanged from C10 / the bootstrap report §3: `pan_installed bytes … ms …`,
`backend_config_ok`, `lab_to_targetProof$mc_conf_ok`, `mc_init_ok`, the
heap/register/bitmap layout, and the single FFI-oracle contract
(`@load_vec`/`@report_vec`). Discharged in a full end-to-end by the x64
target-config proof against the placed image; not this lane.

### 4.3 Inherited residuals (from CN-NATIVE-BOOTSTRAP-REPORT.md, still binding)

- **Version skew.** The binary is a released `cake` (bootstrap report: `ccfc23c`,
  14 commits behind the proof checkout `ed31510`). Layer 2 equates the *ed31510*
  `compile_prog` constant with the *binary's* output, so it additionally rests on
  those 14 commits not changing `compile_prog`'s behaviour on `boundScanProg`.
- **Bootstrap is upstream/CI.** `cake_compiled_thm` (`x64BootstrapProofTheory`) is
  not rebuilt locally; it is the once-proven whole-compiler bootstrap. The oracle
  `cake_native_bootstrap` ultimately rests on it.

None of the above is leanc; none reintroduces the in-logic EVAL cost.

---

## 5. Reproduction (hbox)

```
ssh hbox@hbox.local
cd ~/hol-bytes-bridge
cat Holmakefile                                  # INCLUDES the ed31510 CakeML tree
cake --pancake < boundscan.pnk > boundscan.S     # native, deterministic (md5-stable)
Holmake boundScanBytesBridgeTheory.uo            # ~20s (loads prebuilt backend/pancake proofs)
cat bridge.out                                   # the two theorems + tags + const identities
# theory .dat: ~/hol-bytes-bridge/.hol/objs/boundScanBytesBridgeTheory.dat
```

**Files owned by this lane** (all under `/home/hbox/hol-bytes-bridge/`, self-contained,
no CakeML-tree files modified): `boundScanBytesBridgeScript.sml`, `Holmakefile`,
`boundscan.pnk` (copied from `~/hol-c10`), `boundscan.S` (native output),
`bridge.out` (build dump). Plus this report on the DreggNet side.

## 6. Verdict

- **Is the bytes-reflection bridge mechanized?** **Partially, and honestly so.** The
  reflection itself is fully mechanized (native run → concrete `word8 list` term,
  `LENGTH … = 1188` kernel-checked). The Link-B antecedent is discharged **for the
  exact function the binary runs** (`compile_prog`, oracle `cake_native_bootstrap`),
  and the concrete bytes are shown to occupy the **real** `pan_to_target_compile_
  semantics` `bytes`/`bitmaps` slots (Layer 1, no new oracle). The bootstrap-report
  residual "bytes remains a bound variable" is **closed**.
- **What does NOT close.** The literal `compile_prog_max` shape needs one named
  packaging lemma (§4.1); the machine-semantics conclusion additionally needs the
  runtime install package (§4.2); and the whole thing inherits the version-skew and
  upstream-bootstrap dependencies (§4.3). These are named precisely, not hidden.
- **Trust boundary, crisp.** Theory axioms: **0**. Oracles: **`DISK_THM`** (the
  loaded CakeML proofs) and the single **`cake_native_bootstrap`** = "the verified
  `cake` binary computed these bytes" (⇐ `cake_compiled_thm`). That one oracle tag
  is the entire delta between "kernel-proven" and "native-compiled" — visible,
  named, and no larger than trusting an EverCrypt release build.

# CN REPORT — RUNG 3 (native): COMPOSE bootstrap + Link-B + Link-A into the end-to-end statement for a REAL serve stage — the native-compiled machine code of `boundscan` refines the stage's Pancake source semantics, program-conditions DISCHARGED, native bytes in the code slot, `[oracles: DISK_THM] [axioms:] 0`, NO in-logic EVAL of the backend

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake`. **Proof tree:** `/home/hbox/src/cakeml` at `ed31510b3`. **HOL4:** `/home/hbox/src/HOL`.
**This lane's HOL4 scratch:** `/home/hbox/hol-rung3-native/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-rung3-native/`.
**Ground composed:** `CN-NATIVE-BOOTSTRAP-REPORT.md` (native cake, `cake_compiled_thm`), `CN-BYTES-BRIDGE-REPORT.md` (native bytes reflected, Layer 1/Layer 2), `CN-BOUNDSCAN-LINKA-REPORT.md` (`scanLoop_refines_scanFrom`).

---

## 0. TL;DR — what composes, what does not

**Rung 2 was an in-logic-EVAL toy** (a 1868-byte `tinyProg`): its machine bytes came
from `EVAL`-ing `compile_prog_max` — the entire Pancake→x64 backend — inside the HOL4
kernel, which has no `cv_compute` for the Pancake backend in this tree, hence the toy
ceiling. **Rung 3 is a REAL serve stage (`boundscan`, 1694 B, a real `while`+FFI+`if`)
certified NATIVELY:** the bytes come from running the bootstrapped `cake` binary (the
verified compiler, `cake_compiled_thm`) in **< 0.01 s**, and their correctness rests on
the bootstrap theorem, not on re-EVAL-ing the compiler.

This lane **COMPOSES** the three ground lanes and builds the composition in a new,
kernel-checked HOL4 theory `boundScanRung3` (`Holmake … OK`, `axioms "boundScanRung3" =
0`). The headline artifact:

```
boundScan_rung3_native   [oracles: DISK_THM]  [axioms: ]
⊢ compile_prog_max c mc boundScanProg =
      (SOME (boundScanBytes, boundScanBitmaps, c'), stack_max)     (* G1: native bytes *)
  ∧  <runtime install package: pan_installed boundScanBytes … , mc_conf_ok mc, … >  (* G2 *)
  ∧  semantics_decls s «main» boundScanProg ≠ Fail
  ⇒  machine_sem mc ffi ms ⊆
       extend_with_resource_limit'
         (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
         {semantics_decls s «main» boundScanProg}
```

i.e. **the native-compiled machine code of the `boundscan` stage refines the stage's
Pancake source semantics** — with the concrete native `boundScanBytes`/`boundScanBitmaps`
in the real `bytes`/`bitmaps` slots, and the FOUR program-level applicability conditions
of Link B **discharged** (not left as bound obligations). `[oracles: DISK_THM]` only —
the same tag every loaded CakeML proof carries; **no** in-logic EVAL of the backend, and
notably **no** `cake_native_bootstrap` oracle (G1 is kept as a NAMED antecedent — see §4).

**Honest boundary — the end-to-end "machine code refines the LEAN spec" does NOT fully
close.** The conclusion above stops at the **Pancake source semantics**
`semantics_decls s «main» boundScanProg`. Rewriting that to the Lean spec word
`n2w (boundScan a off len)` is Link A. Link A is **proven for the scan loop**
(`scanLoop_refines_scanFrom`, carried here) but the **whole-`main` frame** that lifts the
loop through the `Dec`/`@load_vec`-FFI/bounds-`If` to `semantics_decls` is the
CN-BOUNDSCAN-LINKA residual #1/#5 — **unproven**. Building a `semantics_decls = <spec>`
theorem here would be either an EVAL of the whole-program semantics (the dead end) or a
vacuous restatement; per the honesty rule it is reported as the obstruction (§5), not
written. The exact residual set is **three named links** (§4–§5): (a) the whole-`main`
Link-A frame, (b) the `compile_prog`↔`compile_prog_max` packaging lemma
(CN-BYTES-BRIDGE 4.1), (c) the runtime install package (4.2).

---

## 1. The composed chain — theorem names and how they compose

```
   boundscan.pnk  (1694 B, the REAL region/view bounds-check + 24-bit rolling digest)
        │
        │  parse_topdecs_to_ast  (the CakeML-VERIFIED Pancake parser; leanc text→AST out of TCB)
        ▼
   boundScanProg  =  OUTL(parse_topdecs_to_ast <boundscan.pnk>)
        │                                   ⇑ boundScanProg_bridge_eq_linkB
        │            (bytes-bridge prog  =  C10/Link-A prog — same AST, kernel-checked)
        │
   ┌────┴───────────────── native compile (bootstrap authority) ──────────────────┐
   │  cake --pancake < boundscan.pnk  →  boundScanBytes (1188 B x64) + [4w] bitmaps │
   │  < 0.01 s, md5-stable, assembles to ELF x86-64 (8260 B .text)                 │
   │  reflected into HOL as concrete word8/word64 lists  (CN-BYTES-BRIDGE §1)      │
   └────┬───────────────────────────────────────────────────────────────────────┘
        │
        │  LAYER 2 (oracle cake_native_bootstrap):  compile_prog x64_config
        │     x64_backend_config boundScanProg = SOME(boundScanBytes,boundScanBitmaps,c')
        │     — EXACTLY the fn the binary runs under --pancake, ⇐ cake_compiled_thm
        │                          │ packaging lemma 4.1 (compile_prog ↔ compile_prog_max)  ✗ GAP
        │                          ▼
        │  G1:  compile_prog_max c mc boundScanProg = (SOME(boundScanBytes,…),stack_max)
        ▼
   LINK B  (pan_to_targetProof$pan_to_target_compile_semantics, INST :64 + native bytes
            = boundScanBytesBridge$boundScan_pan_to_target_specialised)
        │  + the FOUR program conditions DISCHARGED here (bs_pancake_good_code,
        │    bs_distinct_params, bs_distinct_names, bs_size_of_eids — EVAL, §2)
        ▼
   boundScan_rung3_native :  machine_sem mc ffi ms ⊆ … {semantics_decls s «main» boundScanProg}
        │
        │  LINK A  (whole-main frame: Dec «acc»0; Dec «i»0; @load_vec; If bounds …; @report_vec)  ✗ GAP
        │           — closes the loop core via scanLoop_refines_scanFrom (below), NOT the frame
        ▼
   [TARGET, NOT PROVEN]  machine_sem … ⊆ { the behaviour that reports n2w(boundScan a off len) }
```

**The pieces, by exact name:**

| role | theorem | where | tag |
|---|---|---|---|
| bootstrap | `cake_compiled_thm` | `…/x64/64/proofs/x64BootstrapProofScript.sml:83` | upstream/CI |
| Link B (spec→mc) | `pan_to_target_compile_semantics` | `pancake/proofs/pan_to_targetProofScript.sml:1257` | `DISK_THM` |
| Link B @ native bytes | `boundScan_pan_to_target_specialised` | `boundScanBytesBridge` (35-conjunct antecedent) | `DISK_THM` |
| Layer 2 (native bytes) | `boundScan_compile_prog_native` | `boundScanBytesBridge` | `cake_native_bootstrap` |
| **composed backbone** | **`boundScan_rung3_native`** | **`boundScanRung3` (this lane)** | **`DISK_THM`** |
| cross-lane prog id | `boundScanProg_bridge_eq_linkB` | `boundScanRung3` (this lane) | `DISK_THM` |
| Link A (loop) | `scanLoop_refines_scanFrom` | `boundScanLoopLinkA` | `DISK_THM` |

---

## 2. What this lane PROVED (theory `boundScanRung3`, all `[oracles: DISK_THM] [axioms:]`, 0 theory axioms)

Verbatim from the theory's own build dump (`hol-rung3-native/rung3.out`), not transcribed:

**(a) Cross-lane program identity — the glue that makes composition legitimate.** Link B /
the native bytes are stated over `boundScanBytesBridge$boundScanProg`; Link A / C10 over
`boundScanLinkB$boundScanProg`. They are the **same** AST (both parse the byte-identical
`boundscan.pnk`, md5 `8482e9cb…`, with the same verified parser):

```
boundScanProg_bridge_eq_linkB
⊢ boundScanBytesBridge$boundScanProg = boundScanLinkB$boundScanProg     [oracles: DISK_THM]
```

A fully-qualified-constant audit confirms the equation genuinely relates **two distinct
theory constants** (`boundScanBytesBridge$boundScanProg` and
`boundScanLinkB$boundScanProg`) — **not** a vacuous `p = p`; the proof needed *both*
`boundScanProg_def`s to reduce both sides to the identical literal.

**(b) The four program-level Link-B applicability conditions — DISCHARGED against the REAL
constants** (`pancake_good_code`/`distinct_params`/`size_of_eids` that
`pan_to_target_compile_semantics` is literally stated over; C10 discharged verbatim-restated
copies, this lane the real ones), by EVAL on the concrete `boundScanBytes​Bridge$boundScanProg`:

```
bs_pancake_good_code  ⊢ pancake_good_code boundScanProg
bs_distinct_params    ⊢ distinct_params (functions boundScanProg)
bs_distinct_names     ⊢ ALL_DISTINCT (MAP FST (functions boundScanProg))
bs_size_of_eids       ⊢ size_of_eids boundScanProg < dimword (:64)
```

**(c) The composed backbone `boundScan_rung3_native`** (§0). Built by
`SIMP_RULE bool_ss (map EQT_INTRO [the four (b) theorems])` applied to
`boundScan_pan_to_target_specialised`: the four program conjuncts are rewritten to `T` and
removed, leaving **31** antecedent conjuncts (down from **35** — exactly the four
discharged), and the conclusion `machine_sem mc ffi ms ⊆ … {semantics_decls s «main»
boundScanProg}`. The native `boundScanBytes`/`boundScanBitmaps` occupy the `compile_prog_max`
result slot (G1) and the `pan_installed` slot; a constant audit confirms the theorem
references `boundScanBytesBridge$boundScanBytes` / `…$boundScanBitmaps` (the reflected native
code), not a placeholder.

**(d) Link A carried** — `scanLoop_refines_scanFrom` (the scan `While` computes exactly
`n2w (scanFrom a off len 0)`, the Lean `boundScan` in-bounds arm) is imported and printed in
the dump, so the composition record shows the loop-level Link A alongside the backbone and
names precisely the frame between them (§5).

**Trust footprint (audited, §3 of the dump):** `boundScan_rung3_native` = `[oracles:
DISK_THM] [axioms: ]`; `axioms "boundScanRung3" = 0`. **No `cheat`, no `new_axiom`, and
crucially no `cake_native_bootstrap`** — the native-bytes equation is a NAMED antecedent
(G1), not silently discharged (§4).

---

## 3. Independent verification (I ran it; "it built" is checked, not asserted)

- **Build:** `Holmake boundScanRung3Theory.uo` → `[1/1] OK` (17 s). `.dat` persisted at
  `~/hol-rung3-native/.hol/objs/boundScanRung3Theory.dat`.
- **Tags/axioms:** re-loaded the built theory in a fresh `hol` and printed
  `Thm.tag boundScan_rung3_native` = `oracles=[DISK_THM] axioms=[]`;
  `length (axioms "boundScanRung3")` = `0`. The bridge-identity constant audit printed
  both distinct `boundScanProg` theory-constants; the backbone audit printed the native
  `boundScanBytes`/`boundScanBitmaps` constants.
- **Conjunct reduction:** Layer-1 antecedent = **35** conjuncts; `boundScan_rung3_native`
  antecedent = **31** — exactly the four program conditions removed (the four discharged
  predicates are absent from the residual list; verified by inspection of the dump).
- **Native compile, reproduced 3×:** `cake --pancake < boundscan.pnk` → `< 0.01 s` each,
  **md5-identical** across runs (`2429f1e8…`), **1188** `.byte` values (= `LENGTH
  boundScanBytes`), and `cc -c` assembles it to `ELF 64-bit … x86-64`, **8260 B `.text`**.
  So the reflected `boundScanBytes` is real, deterministic, linkable machine code.

---

## 4. The trust boundary — crisp, and why `boundScan_rung3_native` is `DISK_THM`-only

The backbone keeps the native-bytes equation as a **hypothesis** G1:

```
G1 :  compile_prog_max c mc boundScanProg = (SOME (boundScanBytes, boundScanBitmaps, c'), stack_max)
```

Discharging G1 is where the bootstrap enters. The bytes-bridge Layer 2 certifies (oracle
`cake_native_bootstrap`, ⇐ `cake_compiled_thm`) the equation for **`compile_prog`** — the
exact function the binary runs under `--pancake`. G1 is over **`compile_prog_max`** — the
backend's max-stack packaging. Bridging the two is the **single named packaging lemma
(CN-BYTES-BRIDGE 4.1)**, unproven (proving it in-logic = unfold both packagings or EVAL =
the dead end). So the honest structure is:

```
   Layer 2 (oracle cake_native_bootstrap)  +  packaging lemma 4.1 (GAP)  ⟹  G1
   G1  +  install package G2 (GAP, §5)  +  boundScan_rung3_native (PROVEN)  ⟹  machine ⊆ source
```

Because this lane does **not** invoke Layer 2 (it leaves G1 as an antecedent), the
backbone is `DISK_THM`-only: the `cake_native_bootstrap` oracle is *quarantined* to the one
step (G1) it belongs to, and named. That one oracle tag is the entire delta between
"kernel-proven" and "native-compiled", no larger than trusting an EverCrypt release build.

**Inherited, still binding (CN-NATIVE-BOOTSTRAP §3):** the binary is a released `cake`
(14 commits behind the `ed31510` proof checkout, same lineage), and `cake_compiled_thm`
is the once-proven upstream/CI whole-compiler bootstrap, not rebuilt locally. None is
leanc; none reintroduces the EVAL cost.

---

## 5. What does NOT compose — the exact gap (named, not papered over)

The TARGET end-to-end Rung-3 theorem is

```
[TARGET]  <install package> ∧ G1 ∧ <FFI/view relation> ⇒
          machine_sem mc ffi ms ⊆ … { the behaviour that reports n2w (boundScan a off len) }
```

`boundScan_rung3_native` delivers its **backbone** — `machine_sem ⊆ {semantics_decls s
«main» boundScanProg}` — with native bytes and program-conditions discharged. The distance
to `[TARGET]` is **three named links**, none closed here:

1. **The whole-`main` Link-A frame (the primary gap).** The backbone's RHS is the *whole-
   program* Pancake source semantics `semantics_decls s «main» boundScanProg`. Link A
   (`scanLoop_refines_scanFrom`) proves the **scan loop in isolation** computes `n2w
   (scanFrom a off len 0)` from an assumed `loopInv … 0 0`. Lifting that through the `main`
   body — the `Dec «acc» 0`/`Dec «i» 0` initialisers, the `@load_vec` FFI that establishes
   `loopInv`'s `memRel` + the `vs = a[off..off+len)` view, the bounds-`If`, and the
   `@report_vec` FFI that emits the result — to a `semantics_decls = <spec behaviour>`
   equation is the CN-BOUNDSCAN-LINKA residual #1/#5. **Unproven.** Writing it here would be
   an EVAL of the whole-program semantics (intractable) or a vacuous restatement (assuming
   the answer); reported, not faked.
2. **The `compile_prog`↔`compile_prog_max` packaging lemma** (CN-BYTES-BRIDGE 4.1) — the
   step that turns Layer 2's oracle into G1 (§4). Named, unproven.
3. **The runtime install package** (CN-BYTES-BRIDGE 4.2 / CN-NATIVE-BOOTSTRAP §3) — the
   ~28 remaining antecedents of the backbone: `pan_installed boundScanBytes …`,
   `backend_config_ok`, `mc_conf_ok mc`, `mc_init_ok`, the heap/register/bitmap layout, the
   `s.code/locals/globals = FEMPTY` boilerplate, and the single FFI-oracle contract
   (`@load_vec`/`@report_vec`). Discharged in a full end-to-end by the x64 target-config
   proof against the placed image; not this lane.

**Why this is genuinely Rung 3 and not Rung 2:** Rung 2's bytes were an in-logic EVAL of a
1868-byte toy; Rung 3's bytes are the bootstrapped compiler's native output for a **real
1694-byte serve stage** (loop + FFI + branch), reflected into HOL and slotted into the
**real** `pan_to_target_compile_semantics` `bytes` slot, with the program-level conditions
**discharged** — the machine code provably refines the stage's Pancake source semantics,
certified `compile_correct ∘ bootstrap`, **never** by re-EVAL-ing the backend. The residual
is translation-coverage (finish the whole-`main` Link-A frame) + two named packaging/install
lemmas — **not** the compiler-cost dead end that capped Rung 2.

---

## 6. Files

**On hbox** (`/home/hbox/hol-rung3-native/`, self-contained; no CakeML-tree files modified):
`boundScanRung3Script.sml`, `Holmakefile` (`INCLUDES` the CakeML pancake/backend/proofs dirs
+ `~/hol-c10` + `~/hol-boundscan-linka` + `~/hol-bytes-bridge`), `boundscan.pnk`,
`rung3.out` (the build's own tag/axiom/antecedent dump), `audit_rung3.sml` (the constant
audit).

**In this repo** (`docs/engine/probes/compiler/hol-rung3-native/`): `boundScanRung3Script.sml`,
`Holmakefile`, `boundscan.pnk` (md5-matched to hbox), `rung3.out`, plus this report.

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
cd ~/hol-rung3-native
Holmake boundScanRung3Theory.uo          # [1/1] OK, ~17s (loads prebuilt pancake/backend proofs)
cat rung3.out                            # the theorems + tags + the 31 residual antecedents
hol < audit_rung3.sml                    # fully-qualified consts + oracle/axiom tags
# native side:
cake --pancake < boundscan.pnk > b.S && md5sum b.S && cc -c b.S -o b.o && size b.o
# theorem names:
#  backbone : ~/hol-rung3-native/boundScanRung3Script.sml   boundScan_rung3_native
#  Link B   : pancake/proofs/pan_to_targetProofScript.sml:1257  pan_to_target_compile_semantics
#  bytes    : ~/hol-bytes-bridge  boundScan_pan_to_target_specialised / boundScan_compile_prog_native
#  Link A   : ~/hol-boundscan-linka  scanLoop_refines_scanFrom
#  bootstrap: compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml:83  cake_compiled_thm
```

## 8. Bottom line

The compiler track's culmination — "compile a REAL serve stage to machine code and certify
it via the bootstrap, not in-logic EVAL" — is **built for `boundscan` as far as the Pancake
source boundary and honestly named beyond it.** `boundScan_rung3_native` (kernel-checked,
`[oracles: DISK_THM] [axioms:]`, 0 axioms) states that the **native-compiled** machine code
of the stage refines the stage's Pancake source semantics, with the four program-level
Link-B conditions discharged and the concrete native bytes in the code slot — certified by
`compile_correct ∘ bootstrap`, never by EVAL-ing the backend. The end-to-end refinement of
the **Lean spec** does not fully close: it needs the whole-`main` Link-A frame (loop core
already proven), the `compile_prog`↔`compile_prog_max` packaging lemma, and the runtime
install package — three named residuals, each engineering or a single lemma, none the EVAL
dead end and none leanc.

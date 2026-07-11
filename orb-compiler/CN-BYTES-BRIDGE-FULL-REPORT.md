# CN REPORT — BYTES-BRIDGE FULL: the `compile_prog` ↔ `compile_prog_max` PACKAGING LEMMA is CLOSED in-logic (CN-BYTES-BRIDGE §4.1 residual / CN-RUNG3-NATIVE gap-2) — INDEPENDENTLY RE-VERIFIED clean-from-scratch on hbox, real tags read from the kernel, non-vacuity + faithfulness audited against the real backend defs

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb Lean work.
**Proof tree:** `/home/hbox/src/cakeml` @ `ed31510b3`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2). **Lane scratch:** `/home/hbox/hol-rung3-finish/` (mirrored to `docs/engine/probes/compiler/hol-rung3-finish/`, md5-matched).
**Ground:** `CN-BYTES-BRIDGE-REPORT.md` §4.1 (the packaging gap — "an argument, not a proof"), `CN-RUNG3-NATIVE-REPORT.md` gap-2, `CN-RUNG3-FINISH-REPORT.md` (the lane that first wrote `boundScanPkg`).

---

## 0. TL;DR — the packaging lemma is real, and I checked it (not the agent's word)

The RUNG-3-FINISH lane claimed gap-2 closed as `boundScan_pkg_bridge`. Per the honesty
mandate (lanes shipped broken-elaboration / inflated-measure / false-pure-kernel tonight),
this lane **independently re-verified** that claim end-to-end rather than trusting the prior
dump:

1. **Clean from-scratch build GREEN.** Deleted all `*Theory.{dat,uo,ui,sig}` for
   `boundScanPkg`/`boundScanMainFrame`, ran `Holmake` — `boundScanPkgTheory (17s) [2/2] OK`
   (20 s total, loads the prebuilt pancake/backend/bytes-bridge proofs). Not a stale `.dat`.
2. **Real tags read from the kernel** via `Tag.dest_tag (Thm.tag …)` (NOT a grep-count):
   `boundScan_pkg_bridge` = `oracles=[DISK_THM] axioms=[]`; `boundScan_G1_native` =
   `oracles=[DISK_THM,cake_native_bootstrap] axioms=[]`; `axioms "boundScanPkg" = 0`.
3. **Faithfulness audited against the REAL defs.** Fully-qualified `dest_thy_const` confirms
   the lemma relates the two **distinct real backend functions** —
   `pan_to_target$compile_prog` (what the `cake` binary runs under `--pancake`) and
   `pan_to_targetProof$compile_prog_max` (the Link-B antecedent) — not a local re-declaration.
   `boundScan_G1_native`'s `compile_prog_max` is `pan_to_targetProof$` too.
4. **Non-vacuity + soundness traced by hand** through `compile_prog_def`,
   `compile_prog_max_def`, `from_word_def`, `from_stack_def`, `from_lab_def`,
   `attach_bitmaps_def` (§2): the passes genuinely cancel; the statement carries the
   load-bearing content (native bytes in the `compile_prog_max` SOME-slot).

**Verdict: gap-2 (the `compile_prog`↔`compile_prog_max` packaging lemma) is CLOSED, in-logic,
no EVAL of the backend, one cheap side-condition. It is genuine.** What it does **not** close:
the runtime install package (~28 antecedents, CN-BYTES-BRIDGE §4.2) and the whole-`main`
Link-A frame (semantics → Lean spec), plus the inherited version-skew / upstream-bootstrap
dependencies — the same three residuals named by the ground reports, none the EVAL dead end,
none leanc.

---

## 1. The packaging lemma — statement (verbatim from the kernel)

```
boundScan_pkg_bridge                                        [oracles: DISK_THM] [axioms: ]
⊢ mc.target.config = x64_config ∧
  compile_prog x64_config x64_backend_config boundScanProg = SOME (bytes, bitmaps, c'c) ⇒
  ∃c'm sm.
    compile_prog_max x64_backend_config mc boundScanProg = (SOME (bytes, bitmaps, c'm), sm) ∧
    c'm.lab_conf = c'c.lab_conf
```

with the general (abstract prog/config) form it instantiates:

```
compile_prog_max_bytes_bridge                              [oracles: DISK_THM] [axioms: ]
⊢ mc.target.config = asm_conf ∧
  c.stack_conf.perf_calls = F ∧
  SPLITP (λx. case x of Function fi => fi.name = «main» | _ => F) prog = ([], prog) ∧
  compile_prog asm_conf c prog = SOME (bytes, bitmaps, c'c) ⇒
  ∃c'm sm.
    compile_prog_max c mc prog = (SOME (bytes, bitmaps, c'm), sm) ∧ c'm.lab_conf = c'c.lab_conf
```

The two O(1) side facts specialising it to boundscan (both cheap, NOT a backend run):
`bs_perf_calls_F ⊢ x64_backend_config.stack_conf.perf_calls = F` (config-field `EVAL`) and
`bs_splitp ⊢ SPLITP … boundScanProg = ([], boundScanProg)` (`SPLITP` over the AST decl list —
`main` is boundScanProg's sole/first function, so the reorder is the identity).

**`compile_prog` here is `pan_to_target$compile_prog`** — the exact function the bootstrapped
`cake` binary computes under `--pancake` (CN-NATIVE-BOOTSTRAP §2c) and that Layer 2 certifies.
**`compile_prog_max` is `pan_to_targetProof$compile_prog_max`** — the max-stack backend
packaging that `pan_to_target_compile_semantics` (Link B) is literally stated over.

## 2. Why it is TRUE without EVAL-ing the backend (traced against the real defs)

`compile_prog_max c mc prog` (with `asm_conf = mc.target.config`, §`pan_to_targetProofScript.sml:1147`):

```
prog2 = pan_to_word$compile_prog asm_conf.ISA prog
(col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog2
(bm,c',fs,p) = word_to_stack$compile asm_conf F wprog                 ← literal F
from_stack asm_conf c LN p bm                                          ← names = LN, config = c
```

`compile_prog asm_conf c prog` (`pan_to_targetScript.sml:18`), with `bs_splitp` firing the
`([],ys)⇒ys` arm so `prog1 = prog`:

```
prog2 = pan_to_word$compile_prog asm_conf.ISA prog                    ← SAME prog2
(col,prog3) = word_to_word$compile c.word_to_word_conf asm_conf prog2 ← SAME (col,wprog)
c_a = c with word_to_word_conf updated_by (col_oracle := col)
c_b = c_a with exported := exports prog
from_word asm_conf c_b names prog3
   ⇒ (bm,c',fs,p) = word_to_stack$compile asm_conf c_b.stack_conf.perf_calls prog3
```

The passes cancel as byte-identical opaque subterms:

- **word_to_stack:** `c_b.stack_conf = c.stack_conf` (the `word_to_word_conf`/`exported`
  updates don't touch `stack_conf`), and `bs_perf_calls_F` gives
  `c.stack_conf.perf_calls = F`. So compile_prog's call is `word_to_stack$compile asm_conf F
  wprog` — **identical** to compile_prog_max's ⇒ same `(bm, c', fs, p)`.
- **stack_to_lab** (in `from_stack`) reads only `c.stack_conf`/`c.data_conf`; **lab_to_target**
  (in `from_lab`) reads only `c.lab_conf`. compile_prog's `c_c = c_b with word_conf := c'`
  leaves all three equal to `c`'s ⇒ **identical** `plab` and **identical** `lab_to_target$compile
  asm_conf c.lab_conf plab` result (call it `labres`).
- **attach_bitmaps** (`backendScript.sml:34`): `attach_bitmaps names cfg bm (SOME (bytes,c')) =
  SOME (bytes, bm, cfg with <|lab_conf := c'; symbols := …names…|>)`. The **bytes** (1st) and
  **bitmaps** (2nd = `bm`) components are independent of `names` and `cfg`, and the returned
  config's `.lab_conf` is `c'` on both sides. So compile_prog's `attach_bitmaps N c_c bm labres`
  and compile_prog_max's `attach_bitmaps LN c bm labres` return the **same bytes, same bitmaps,
  same `.lab_conf`** — differing only in `.symbols`, `.exported`, `.word_conf`,
  `.word_to_word_conf.col_oracle`, none of which any downstream consumer of G1 reads
  (`pan_installed` uses only `c'.lab_conf.{ffi_names,shmem_extra}`).

The whole content is `attach_bitmaps_bytes_agree` (a 3-line lemma:
`attach_bitmaps n1 c1 bm x = SOME (b,bm',cc1) ⇒ ∃cc2. attach_bitmaps n2 c2 bm x = SOME (b,bm',cc2)
∧ cc2.lab_conf = cc1.lab_conf`) + the two O(1) config/AST facts. **The Pancake→x64 backend is
never evaluated on `boundScanProg`.** This is exactly the "unfold both packagings" that
CN-BYTES-BRIDGE §4.1 called the dead end — made tractable by the passes **cancelling** as
subterms rather than needing evaluation.

## 3. How it closes the Link-B antecedent for boundscan (native bytes + bootstrap)

Composed with the Layer-2 native oracle (`boundScan_compile_prog_native`, the reflected native
`cake` output, oracle `cake_native_bootstrap` ⇐ `cake_compiled_thm`):

```
boundScan_G1_native                       [oracles: DISK_THM, cake_native_bootstrap] [axioms: ]
⊢ mc.target.config = x64_config ⇒
  ∃c'm sm c'c.
    compile_prog_max x64_backend_config mc boundScanProg =
      (SOME (boundScanBytes, boundScanBitmaps, c'm), sm) ∧ c'm.lab_conf = c'c.lab_conf
```

This is **G1** — the Link-B / Rung-3-backbone antecedent
`compile_prog_max c mc boundScanProg = (SOME (bytes, bitmaps, c'), stack_max)` — **discharged
with the concrete native `boundScanBytes` (1188 B) / `boundScanBitmaps` (`[4w]`) in the
`SOME`-slot**, under one cheap side-condition (`mc.target.config = x64_config`), carrying
exactly the one named `cake_native_bootstrap` oracle and nothing else. Chained with
`boundScan_rung3_native` (CN-RUNG3-NATIVE, `machine_sem ⊆ … {semantics_decls s «main»
boundScanProg}`, four program-conditions discharged), the native machine code of the boundscan
stage refines the stage's Pancake source semantics with G1 now flowing through the real
`compile_prog_max` packaging — not an unproven §4.1 argument.

**Honest note on `boundScan_G1_native`'s `c'm.lab_conf = c'c.lab_conf`:** `c'c` is
existentially bound and otherwise unconstrained there, so *that conjunct alone* is
decorative. The **load-bearing** claim — `boundScanBytes`/`boundScanBitmaps` in the
`compile_prog_max` `SOME`-slot — is genuine content, derived from the oracle via the bridge
(the theorem carries `cake_native_bootstrap`, so the oracle was really used). In
`boundScan_pkg_bridge` / `compile_prog_max_bytes_bridge` themselves, `c'c` is bound by the
antecedent (a free var), so there the `.lab_conf` equality is real, quantified content.

## 4. Verification evidence (I ran it; "it built" is checked, not asserted)

- **Clean from-scratch:** `rm -f *Theory.{dat,uo,ui,sig}` then `Holmake` →
  `boundScanMainFrameTheory (8s) [1/2] OK`, `boundScanPkgTheory (17s) [2/2] OK`. No CakeML-tree
  file modified.
- **Real tags (kernel, `Tag.dest_tag`):** `boundScan_pkg_bridge` /
  `compile_prog_max_bytes_bridge` / `attach_bitmaps_bytes_agree` = `oracles=[DISK_THM]
  axioms=[]`; `boundScan_G1_native` = `oracles=[DISK_THM,cake_native_bootstrap] axioms=[]`;
  `axioms "boundScanPkg" = 0`. **No `cheat`, no `new_axiom`, no `native_decide`** (HOL4 has no
  `ofReduceBool`; the only `EVAL`s are the two O(1) config/AST facts, never the backend).
- **Fully-qualified constant audit:** `pkg_bridge compile_prog -> pan_to_target$compile_prog`;
  `pkg_bridge compile_prog_max -> pan_to_targetProof$compile_prog_max`; `G1_native
  compile_prog_max thy: pan_to_targetProof`. The lemma relates the two real, distinct backend
  functions — not a mirror.
- **Artifact identity:** repo `boundScanPkgScript.sml` md5 `f2dba1b5…` == hbox; `boundscan.pnk`
  md5 `8482e9cb…` == hbox == bytes-bridge/linka lanes.

## 5. What remains (named, not papered over)

`boundScan_pkg_bridge` closes gap-2 **fully**. The distance from `boundScan_rung3_native` +
`boundScan_G1_native` to the Lean-spec end-to-end is the two OTHER residuals the ground reports
already named — this lane does **not** touch them:

1. **The runtime install package** (CN-BYTES-BRIDGE §4.2): the ~28 remaining Link-B
   antecedents — `pan_installed boundScanBytes …`, `backend_config_ok`, `mc_conf_ok`,
   `mc_init_ok`, heap/register/bitmap layout, the `s.code/locals/globals = FEMPTY` boilerplate,
   and the single FFI-oracle contract (`@load_vec`/`@report_vec`). Discharged in a full
   end-to-end by the x64 target-config proof against the placed image; not this lane.
2. **The whole-`main` Link-A frame** (CN-RUNG3-FINISH §2.3): rewriting `semantics_decls s
   «main» boundScanProg` to the Lean spec word `n2w (boundScan a off len)`. Loop core
   (`scanLoop_refines_scanFrom`), else-arm identity (`elseBranch_faithful`), and loop-body
   frame (`scanBody_frame/res/clock/fixclock`) are proven; the `scanLoop` locals-frame
   (engineering, hit tactic friction), the `Dec`/`If`/`Seq` threading (mechanical), and the
   `@load_vec`/`@report_vec` FFI-oracle contract (the irreducible research boundary) are open.
3. **Inherited (CN-NATIVE-BOOTSTRAP §3):** version skew (binary `ccfc23c`, 14 commits behind
   the `ed31510` proof checkout, same lineage) and the upstream/CI whole-compiler bootstrap
   `cake_compiled_thm` not rebuilt locally. None is leanc; none reintroduces the EVAL cost.

## 6. Files (this lane owns none of the CakeML tree)

- **Report:** this file, `docs/engine/probes/compiler/CN-BYTES-BRIDGE-FULL-REPORT.md`.
- **HOL4 (already in repo + hbox, md5-matched, unchanged by this verification lane):**
  `docs/engine/probes/compiler/hol-rung3-finish/{boundScanPkgScript.sml, Holmakefile,
  boundscan.pnk, rung3finish.out}` == `/home/hbox/hol-rung3-finish/`.
- **Fresh audit script (hbox):** `/home/hbox/hol-rung3-finish/audit_pkg.sml` (the
  `Tag.dest_tag` + `dest_thy_const` audit run for §4).

**Scope note:** HOL4/CakeML COMPILER-track lane. Touches no Lean spec, no `Datapath.lean`, no
`libdrorb`, no Rust dataplane — there is no `cargo` / `build-dataplane-lib.sh` / `curl` delta.
The mergeable artifact is this report (the HOL4 theory already landed with the FINISH lane).

## 7. Bottom line

The `compile_prog` ↔ `compile_prog_max` packaging lemma (CN-BYTES-BRIDGE §4.1 / CN-RUNG3 gap-2)
is a **single in-logic theorem** — `boundScan_pkg_bridge`, `[oracles: DISK_THM]`, 0 axioms —
proven by symbolic cancellation of the shared passes + two O(1) config/AST facts, **no EVAL of
the backend**, and composed with the Layer-2 native oracle into `boundScan_G1_native`,
discharging the Link-B `compile_prog_max = SOME(boundScanBytes,…)` antecedent for boundscan on
the concrete native bytes under the single named `cake_native_bootstrap` oracle and one cheap
`mc.target.config = x64_config` side-condition. **Independently re-verified clean-from-scratch,
tags read from the kernel, faithfulness and non-vacuity audited.** It closes gap-2 fully; the
end-to-end to the Lean spec still needs the runtime install package and the whole-`main`
Link-A frame — named, not the EVAL dead end, not leanc.

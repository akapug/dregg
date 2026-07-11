# CN REPORT — RUNG-3 FINISH: close the two named gaps of the boundscan Rung-3 chain — (2) the `compile_prog`↔`compile_prog_max` PACKAGING LEMMA discharged IN-LOGIC (no EVAL), and (1) the whole-`main` Link-A frame ATTEMPTED (loop-body frame + faithful else-arm extraction; the FFI-oracle boundary named)

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake`. **Proof tree:** `/home/hbox/src/cakeml` @ `ed31510b3`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2).
**This lane's HOL4 scratch:** `/home/hbox/hol-rung3-finish/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-rung3-finish/`.
**Ground composed:** `CN-RUNG3-NATIVE-REPORT.md` (`boundScan_rung3_native`, the backbone with G1 as a named antecedent), `CN-BYTES-BRIDGE-REPORT.md` (Layer 2 native oracle, §4.1 the packaging gap), `CN-BOUNDSCAN-LINKA-REPORT.md` (`scanLoop_refines_scanFrom`, §5 the whole-`main` frame residual).

---

## 0. TL;DR — what closed, what advanced, what remains

The RUNG-3-NATIVE report named **three** residuals between `boundScan_rung3_native` (machine code ⊑ Pancake source, native bytes in the slot, program-conditions discharged, `[oracles: DISK_THM]`) and the Lean-spec end-to-end. This lane targets the two the task called out:

- **Gap (2) — the `compile_prog`↔`compile_prog_max` packaging lemma (CN-BYTES-BRIDGE §4.1): CLOSED, kernel-proven, no EVAL of the backend.** `boundScan_pkg_bridge` (`[oracles: DISK_THM] [axioms:]`, 0 theory axioms) proves that for `boundScanProg` the `bytes`/`bitmaps` of `pan_to_target$compile_prog x64_config x64_backend_config` (the function the `cake` binary runs, what Layer 2 certifies) equal those of `pan_to_targetProof$compile_prog_max` (what Link B / the backbone antecedent G1 is stated over), with the returned config's `lab_conf` (the only part the downstream `pan_installed` reads) identical. Composed with the Layer-2 native oracle it gives `boundScan_G1_native` — **G1 with the concrete native `boundScanBytes`/`boundScanBitmaps` in the `compile_prog_max` slot**, carrying exactly the one named `cake_native_bootstrap` oracle and nothing else. The §4.1 "argument, not a proof" is now a proof.

- **Gap (1) — the whole-`main` Link-A frame: ADVANCED, honestly bounded, NOT fully closed.** The `main` body was structurally extracted from the C10 verified-parser program and the If's else-arm — `Dec «acc» 0; Dec «i» 0; scanLoop; «result»:=«acc»` — is shown, kernel-checked, to **be** the else-arm of the real `boundScanProg` (`elseBranch_faithful`, over `boundScanLinkB$boundScanProg`, not a mirror). The loop-**body** frame lemmas the composition rests on are proven (`scanBody_frame` / `scanBody_res` / `scanBody_clock` / `scanBody_fixclock`). The remaining distance is named precisely in §4: (a) the `scanLoop` locals-frame (a clocked-`While` induction — body ingredients proven, the induction assembly hit HOL tactic friction and is **not** closed in-session), (b) the mechanical `Dec`/`If`/`Seq` threading, and (c) the **irreducible** `@load_vec`/`@report_vec` FFI-oracle contract, where the arena bytes enter through the abstract `s.ffi` oracle — an assumption, not a derivation.

**No `native_decide`, no `cheat`, no `new_axiom`.** Both new theories: `axioms = 0`. The only oracle beyond the universal `DISK_THM` is the single, named `cake_native_bootstrap` on `boundScan_G1_native` (inherited from Layer 2, quarantined to the one step it belongs to).

---

## 1. Gap (2) — the packaging lemma, discharged in-logic (theory `boundScanPkg`)

### The theorem (verbatim from the build's own dump `hol-rung3-finish/rung3finish.out`)

```
boundScan_pkg_bridge                                        [oracles: DISK_THM] [axioms: ]
⊢ mc.target.config = x64_config ∧
  compile_prog x64_config x64_backend_config boundScanProg = SOME (bytes, bitmaps, c'c) ⇒
  ∃c'm sm.
    compile_prog_max x64_backend_config mc boundScanProg = (SOME (bytes, bitmaps, c'm), sm) ∧
    c'm.lab_conf = c'c.lab_conf
```

A fully-qualified-constant audit confirms this relates the **two distinct real backend functions** — `pan_to_target$compile_prog` (Layer 2 / the binary) and `pan_to_targetProof$compile_prog_max` (Link B / G1) — not a local re-declaration.

### Why it is provable WITHOUT EVAL-ing the compiler (the content §4.1 missed)

`compile_prog` and `compile_prog_max` share the **entire** pass pipeline. Unfolding both definitions symbolically (`compile_prog_def`, `compile_prog_max_def`, `from_word_def`, `from_stack_def`, `from_lab_def`, `attach_bitmaps_def`) makes the pass applications appear as **byte-identical opaque subterms** on both sides:

- `pan_to_word$compile_prog asm_conf.ISA boundScanProg` — identical (`compile_prog_max` applies it to `boundScanProg` directly; `compile_prog` applies it to the `main`-reordered `prog1`, which **equals** `boundScanProg` because `main` is `boundScanProg`'s sole/first function — `bs_splitp`, a cheap `SPLITP` over the AST decl list, NOT a compiler run);
- `word_to_word$compile x64_backend_config.word_to_word_conf x64_config …` — identical inputs → identical `(col, wprog)`;
- `word_to_stack$compile x64_config F …` — `compile_prog_max` uses the literal `F`; `compile_prog` (via `from_word`) uses `x64_backend_config.stack_conf.perf_calls`, and `bs_perf_calls_F` (a cheap config-field EVAL) shows that field **is** `F` — so the calls coincide, giving the same `(bm, c', fs, p)`;
- `stack_to_lab$compile` and `lab_to_target$compile` — depend only on `stack_conf`/`data_conf`/`lab_conf`, which the `col_oracle`/`exported`/`word_conf` record-updates on `compile_prog`'s config **do not touch**, so both reduce (via the record accessors, no compute) to the same `SOME (code_bytes, ltc)`.

`attach_bitmaps` then returns `SOME (code_bytes, bm, cfg with <|lab_conf := ltc; symbols := …|>)`: the 1st (bytes) and 2nd (bitmaps) components are **independent of the names-map and the base config**, and the 3rd's `.lab_conf` is `ltc` on both sides. The Pancake→x64 backend is **never evaluated on `boundScanProg`** — the passes cancel as syntactic subterms; only two O(1) config/AST facts are computed. That is exactly the "unfold both packagings" §4.1 called the dead end, made tractable by observing the passes **cancel** rather than needing evaluation. The whole content is `attach_bitmaps_bytes_agree` (an abstract 3-line lemma) + the two config facts.

### Composition with Layer 2 → G1 discharged on the native bytes

```
boundScan_G1_native                       [oracles: DISK_THM, cake_native_bootstrap] [axioms: ]
⊢ mc.target.config = x64_config ⇒
  ∃c'm sm c'c.
    compile_prog_max x64_backend_config mc boundScanProg =
      (SOME (boundScanBytes, boundScanBitmaps, c'm), sm) ∧
    c'm.lab_conf = c'c.lab_conf
```

This is the backbone antecedent **G1** (`compile_prog_max … = (SOME(boundScanBytes,boundScanBitmaps,c'),stack_max)`) **discharged**, on the single named bootstrap oracle, under one cheap side-condition (`mc.target.config = x64_config`). The distance between "kernel-proven" and "native-compiled" remains exactly that one tag — no larger than trusting an EverCrypt release build — and is now the ONLY thing standing between Layer 2 and the literal G1 in the backbone.

### Honest boundary of gap (2)

`boundScan_pkg_bridge` proves the `bytes`/`bitmaps` equal **and** `c'm.lab_conf = c'c.lab_conf`. It does **not** prove `c'm = c'c` in full: the two returned configs genuinely differ in `.symbols` (names-map `LN` vs the real user-name map), `.word_to_word_conf.col_oracle`, `.exported`, and `.word_conf`. None of those is read downstream — `pan_installed` uses only `c'.lab_conf.ffi_names` and `c'.lab_conf.shmem_extra`, both determined by `c'.lab_conf`, which the lemma pins. So the equality delivered is exactly the part G1's consumers depend on; the residual config-field difference is named, not hidden.

---

## 2. Gap (1) — the whole-`main` frame, attempted (theory `boundScanMainFrame`)

### 2.1 The `main` body, and the faithful else-arm extraction (CLOSED)

The C10 verified-parser AST of `boundScanProg` `main` is a nested `Dec`/`Seq`/`ExtCall`/`If`/`Store`/`ExtCall`/`Return`:

```
Dec «base» BaseAddr; Dec «buf» (base+32);
@load_vec(base,24,buf,4096);                         (* FFI: fills control block + arena bytes *)
Dec «alen» [base]; Dec «off» [base+8]; Dec «len» [base+16]; Dec «result» 0;
If (alen < off+len) { «result» := 0xFFFFFFFF }       (* out-of-bounds sentinel *)
                    { Dec «acc» 0; Dec «i» 0; scanLoop; «result» := «acc» };   (* the else-arm *)
st (base+24) «result»;
@report_vec(base+24,8,base,8); return 0
```

`elseBranch_faithful` (`[oracles: DISK_THM]`) is a kernel-checked equation that the else-arm `Seq (Annot …) (Dec «acc» 0 (… Dec «i» 0 (Seq (Seq (Annot …) scanLoop) (Seq (Annot …) («result»:=«acc»)))))` **is** the else-arm of the real `boundScanLinkB$boundScanProg` (structurally extracted by `extract_else_decl`, then `EVAL`-checked — NOT hand-transcribed), with the loop being exactly `boundScanLoopLinkA$scanLoop`. This pins precisely the statements the whole-`main` frame must thread and closes the "which term" question the way `scanLoop_faithful` did for the loop.

### 2.2 The loop-BODY frame lemmas (CLOSED)

The whole-`main` frame needs to know the loop touches only its own locals and preserves the clock/`«result»`. Those body-level facts are proven (`[oracles: DISK_THM] [axioms:]`):

```
scanBody_frame    ⊢ evaluate (scanBody,s) = (NONE,s2) ⇒
                      ∀v. v ≠ «acc» ∧ v ≠ «i» ⇒ FLOOKUP s2.locals v = FLOOKUP s.locals v
scanBody_res      ⊢ evaluate (scanBody,s) = (r,s') ⇒ r = NONE ∨ r = SOME Error
scanBody_clock    ⊢ evaluate (scanBody,s) = (r,s') ⇒ s'.clock = s.clock
scanBody_fixclock ⊢ fix_clock t (evaluate (scanBody,t)) = evaluate (scanBody,t)
```

These are the exact ingredients of the `scanLoop` locals-frame (lift `scanBody_frame` across the clocked `While` by induction on a clock bound, using `scanBody_res` to rule out `Break`/`Continue` and `scanBody_fixclock` to collapse `panSem`'s `fix_clock` bookkeeping).

### 2.3 What is NOT closed, and exactly why (the honest boundary)

A full `evaluate`-level frame for `elseBranch` (from a post-`@load_vec` state, run `Dec «acc» 0; Dec «i» 0; scanLoop; «result»:=«acc»` and land `«result» = n2w (scanFrom a off len 0)`, the Lean in-bounds digest) reduces to three residuals — the first two engineering, the third genuine:

1. **The `scanLoop` locals-frame** (`evaluate(scanLoop,s)=(NONE,s') ⇒ ∀v∉{«acc»,«i»}. FLOOKUP s'.locals v = FLOOKUP s.locals v`) — needed so the trailing `«result»:=«acc»` passes `is_valid_value` (the loop must not clobber `«result»`). Its ingredients (§2.2) are all proven; the assembly is a standard clock-bounded induction over `panSem`'s clocked `While`. In-session it hit HOL4 tactic friction (the `fix_clock`/nested-`If`/`case res` unfolding of the `While` clause repeatedly mis-split under `gvs`/`IF_CASES_TAC`, and a spurious `s.clock = 0` branch leaked into the recursive arm). It is **engineering, not research**, and is **not closed** here — reported, not faked.
2. **The `Dec`/`If`/`Seq` threading** — peeling `Dec «acc» 0`/`Dec «i» 0` to establish `loopInv … 0 0` (all fields discharge from the post-`@load_vec` locals + `memRel`, which are frame-invariant to the `Dec`s), applying `scanLoop_refines_scanFrom`, then the `«result»` store and the `Dec` pops. Mechanical `panSem$evaluate` threading over the proven pieces; not closed here.
3. **The `@load_vec`/`@report_vec` FFI-oracle contract — the IRREDUCIBLE boundary.** `panSem`'s `ExtCall` semantics (`panSemScript.sml:714`) resolves `@load_vec`'s memory effect **entirely through the abstract oracle** `call_FFI s.ffi (ExtCall «load_vec») …`: `loopInv`'s `memRel` (the arena bytes sit at `buf+off+j`) and the view relation `vs = a[off..off+len)` hold **iff the oracle returns the arena bytes**. That is an assumption about `s.ffi`, not derivable — it is the front-end↔C-driver contract, the true research edge of the whole-`main` frame (CN-BOUNDSCAN-LINKA §5.1–§5.2). Establishing `semantics_decls s «main» boundScanProg` in full additionally passes through the top-level `semantics`/`evaluate_decls` wrapper; writing it as an EVAL is the dead end, and writing it without the FFI contract is vacuous — so per the honesty rule it is named as the obstruction, not produced.

---

## 3. The end-to-end boundscan Rung-3 chain, after this lane

```
boundscan.pnk  (1694 B, region/view bounds-check + 24-bit rolling digest)
   │  parse_topdecs_to_ast  (CakeML-VERIFIED Pancake parser; leanc text→AST out of TCB)
   ▼
boundScanProg  = OUTL(parse_topdecs_to_ast <boundscan.pnk>)
   │
   │  cake --pancake < boundscan.pnk  →  boundScanBytes (1188 B x64) + [4w] bitmaps   (< 0.01 s, md5-stable)
   │  reflected into HOL  (CN-BYTES-BRIDGE §1)
   ▼
Layer 2 (oracle cake_native_bootstrap):  compile_prog x64_config x64_backend_config boundScanProg
                                            = SOME(boundScanBytes, boundScanBitmaps, c')     ⇐ cake_compiled_thm
   │  boundScan_pkg_bridge  (THIS LANE, [oracles: DISK_THM], NO EVAL)   ← GAP (2) CLOSED
   ▼
G1 (native):  compile_prog_max x64_backend_config mc boundScanProg
                = (SOME(boundScanBytes, boundScanBitmaps, c'm), sm),  c'm.lab_conf = c'.lab_conf
   │  boundScan_G1_native  (THIS LANE, [oracles: DISK_THM, cake_native_bootstrap])
   ▼
Link B  (pan_to_target_compile_semantics @ native bytes = boundScan_pan_to_target_specialised)
   │  + FOUR program-conditions DISCHARGED (CN-RUNG3-NATIVE §2)
   ▼
boundScan_rung3_native :  machine_sem mc ffi ms ⊆ … {semantics_decls s «main» boundScanProg}
   │  Link A: whole-`main` frame
   │    · scanLoop core  : scanLoop_refines_scanFrom  (CN-BOUNDSCAN-LINKA, PROVEN)
   │    · else-arm ident : elseBranch_faithful         (THIS LANE, PROVEN)
   │    · loop-body frame: scanBody_frame/res/clock/fixclock (THIS LANE, PROVEN)
   │    · scanLoop locals-frame  (engineering, NOT closed — §2.3.1)
   │    · Dec/If/Seq threading    (mechanical,  NOT closed — §2.3.2)
   │    · @load_vec/@report_vec FFI-oracle contract  (IRREDUCIBLE boundary — §2.3.3)
   ▼
[TARGET]  machine_sem … ⊆ { behaviour that reports n2w (boundScan a off len) }   (Lean spec)
```

**The native machine code of the `boundscan` serve stage refines the stage's Pancake source semantics, certified by `compile_correct ∘ bootstrap` (NO in-logic EVAL of the backend), with the native bytes now flowing through the `compile_prog_max` packaging into G1 (gap (2) closed) rather than sitting behind an unproven §4.1 argument.** The residual to the Lean-spec end-to-end is the whole-`main` Link-A frame, whose loop core, else-arm identity, and loop-body frame are proven, and whose remainder is two mechanical threading steps + the one irreducible FFI-oracle contract — none the EVAL dead end, none leanc.

---

## 4. Independent verification (ran it; "it built" is checked, not asserted)

- **Clean from-scratch build** of both new theories (`rm -f *Theory.dat *Theory.uo` then `Holmake`): `boundScanMainFrameTheory [1/2] OK` (10 s), `boundScanPkgTheory [2/2] OK` (20 s). Loads the prebuilt pancake/backend/bytes-bridge/linka proofs; no CakeML-tree file modified.
- **Tags/axioms** (re-loaded in a fresh `hol`, printed): `boundScan_pkg_bridge`, `elseBranch_faithful`, `scanBody_frame` = `[oracles: DISK_THM] [axioms:]`; `boundScan_G1_native` = `[oracles: DISK_THM, cake_native_bootstrap] [axioms:]`. `axioms "boundScanPkg" = 0`, `axioms "boundScanMainFrame" = 0`. **No `native_decide`/`Lean.ofReduceBool`, no `cheat`, no `new_axiom`.**
- **Non-vacuity audit:** `boundScan_pkg_bridge`'s constant audit prints `pan_to_target$compile_prog` and `pan_to_targetProof$compile_prog_max` — the two REAL, distinct backend functions. `elseBranch_faithful`'s audit prints `boundScanLinkB$boundScanProg` (the C10 verified-parser program) and `boundScanLoopLinkA$scanLoop` — the extraction reasons about the real program, not a local mirror.
- **Native compile, reproduced:** `cake --pancake < boundscan.pnk` → `< 0.01 s`, `boundscan.pnk` md5 `8482e9cb…` (matches hbox and the bytes-bridge lane).

---

## 5. Files

**On hbox** (`/home/hbox/hol-rung3-finish/`, self-contained; no CakeML-tree files modified):
`boundScanPkgScript.sml`, `boundScanMainFrameScript.sml`, `Holmakefile` (INCLUDES the CakeML pancake/backend/proofs dirs + `~/hol-c10` + `~/hol-boundscan-linka` + `~/hol-bytes-bridge`), `boundscan.pnk`, `rung3finish.out` (the build's tag/axiom/const dump).

**In this repo** (`docs/engine/probes/compiler/hol-rung3-finish/`): the same five files (`boundscan.pnk` md5-matched to hbox), plus this report.

**Scope note (like CN-BOUNDSCAN-LINKA §6):** this is a HOL4/CakeML COMPILER-track lane. It touches no Lean spec, no Rust dataplane, no `Datapath.lean`, no `lakefile`, no `libdrorb` — there is **no `cargo`/`build-dataplane-lib.sh`/`curl` delta**; the mergeable artifact is the two new HOL4 theories + Holmakefile + this report.

## 6. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
cd ~/hol-rung3-finish
Holmake                                  # [1/2] boundScanMainFrame, [2/2] boundScanPkg — OK
cat rung3finish.out                      # the theorems + tags + fully-qualified const audit
# theorem names:
#  packaging   : boundScanPkgScript.sml         boundScan_pkg_bridge / boundScan_G1_native
#  else-arm    : boundScanMainFrameScript.sml   elseBranch_faithful
#  loop-body   : boundScanMainFrameScript.sml   scanBody_frame / scanBody_res / scanBody_clock
```

## 7. Bottom line

**Gap (2) is closed:** the `compile_prog`↔`compile_prog_max` packaging lemma is a single in-logic theorem (`boundScan_pkg_bridge`, `[oracles: DISK_THM]`, 0 axioms), proven by symbolic cancellation of the shared passes + two O(1) config/AST facts — **no EVAL of the backend** — and composed with Layer 2 into `boundScan_G1_native`, discharging the backbone's G1 antecedent on the concrete native bytes under the single named `cake_native_bootstrap` oracle. **Gap (1) is advanced and honestly bounded:** the `main` else-arm is kernel-checked to be the real program's else-arm, the loop-body frame lemmas are proven, and the remainder is named exactly — the `scanLoop` locals-frame (engineering, hit tactic friction, not closed), the `Dec`/`If` threading (mechanical, not closed), and the `@load_vec`/`@report_vec` FFI-oracle contract (the irreducible research boundary where the arena bytes enter through the abstract oracle). None of the residual is the EVAL dead end; none is leanc.

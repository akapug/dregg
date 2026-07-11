# PNK-MANIFEST — every real serve `.pnk`, native-compiled by bootstrapped `cake`, toward a full-serve image

**Date:** 2026-07-10 · **Machine:** hbox (24-core, io_uring) · **Compiler:**
`/home/hbox/r05/cake-x64-64/cake` (CakeML `ccfc23c…`, x64 bootstrap).
**Working dir (hbox):** `/home/hbox/pnk-manifest/` (28 `.pnk`, one `.S` + one `.o` each).
**Basis:** `CN-NATIVE-BOOTSTRAP-REPORT.md` — the bootstrap authority (`cake_compiled_thm`)
that makes the native bytes the verified backend's output, not an in-logic EVAL.
**Ground truth for "full serve":** `~/dev/drorb/Reactor/Deploy.lean:1511`
`deployStagesFull2 : List Stage` — the deployed **14-stage** middleware fold `main` runs.

This manifest is the **breadth sweep** the CN report's 7-stage table pointed at: it
native-compiles **all 28** real serve `.pnk` (the 7 runtime-substrate stages + the
serve-decision/transform stages the C-series lowered + the two EmitPancake-generated
stages), records each stage's **source size, native compile time, emitted x64
machine-code size, and ELF-object validity**, and maps them onto the 14-stage
`deployStagesFull2` to name the exact gap to a single fused full-serve image.

---

## 0. TL;DR — measured, verified by running it

- **28/28 `.pnk` native-compile** with `cake --pancake` — **0 parse failures**,
  compile times **3.6–20.2 ms** each (best of 20 runs).
- **28/28 assemble to a valid ELF relocatable object** via `cc -c` — checked with
  `file … | grep ELF`; **27 objects are byte-distinct** (md5), the one collision is
  `region.o ≡ boundscan.o` **by construction** (EmitPancake's `emitRegion` *reproduces*
  boundscan — a wanted equality, not a bug).
- **Total emitted x64 machine code across the 28 stages: 34 012 bytes** (992 B for the
  smallest probe `tiny`, 1 942 B for the largest real stage `parseline`).
- **Coverage of the deployed serve:** **13 of the 14** `deployStagesFull2` stages have a
  native-compiling `.pnk` representative; **1 (`HtmlRewrite`)** has none — a genuine
  streaming-tokenizer body-rewrite **loop** residual (§4).
- **EmitPancake path is live and axiom-free:** `lean --run Dsl/EmitPancake.lean`
  regenerates `emit/region.pnk` + `emit/machine.pnk` byte-identically to the committed
  files; both compile natively; `#print axioms Dsl.EmitPancake.emitRegion` /
  `emitMachine` → **"does not depend on any axioms"** (verified on hbox, §5).

**Honest boundary (unchanged from CN §3):** native-compiled ≠ in-logic-proven bytes;
certification is `compile_correct ∘ bootstrap`. And the 28 are **28 standalone
programs**, each carrying its own `cake_main`/basis image — **not one fused serve
`.pnk`**. The gap to a full-serve image is composition + the loop residuals, §4.

---

## 1. The full sweep — every stage, measured on hbox

Columns: **SRC** = `.pnk` source bytes; **ASM** = emitted `.S` bytes; **CODE** = sum of
the `.byte` machine-code operands = the **real per-program compiled x64 size** (see the
`.text` note below); **TIME** = native `cake --pancake` best-of-20; **ELF** = `cc -c`
produced a valid ELF relocatable object.

| # | stage `.pnk` | SRC B | ASM B | **CODE B** | TIME | ELF | serve role · provenance |
|---|---|---:|---:|---:|---:|:--:|---|
| **Runtime substrate (7)** ||||||||
| 1 | `boundscan`   | 1694 | 10 340 | 1188 | 6.3 ms | ✅ | region bounds-check + rolling digest · C0/C10/C11 |
| 2 | `arenascan`   | 1538 | 10 277 | 1176 | 5.8 ms | ✅ | arena live-object scan · C5 |
| 3 | `arenawrite`  | 2478 | 12 527 | 1588 | 13.6 ms | ✅ | arena bump-write / alloc · C7 |
| 4 | `collect`     | 2048 | 10 089 | 1138 | 5.7 ms | ✅ | GC sweep/compact · C8 |
| 5 | `freelist`    | 1969 |  9 527 | 1078 | 5.9 ms | ✅ | free-list reclaim · C9 |
| 6 | `machinestep` | 1729 | 10 089 | 1142 | 5.8 ms | ✅ | parse/FSM machine step · C2/C4 |
| 7 | `parseline`   | 3200 | 14 448 | 1942 | 20.2 ms | ✅ | request-line parse loop · C6 |
| **Serve decision / transform stages (deployStagesFull2)** ||||||||
| 8 | `jwt`         | 1853 | 10 748 | 1264 | 7.6 ms | ✅ | **[S1] jwtAdminStage** · C31 |
| 9 | `basic`       | 1800 | 10 651 | 1246 | 7.1 ms | ✅ | **[S2] BasicAuth** (decision proj.) · C27 |
| 10 | `ipf`        | 3401 | 12 525 | 1590 | 12.1 ms | ✅ | **[S3] IpFilter** deny 10/8 · C29 |
| 11 | `rateadmit`  | 1472 |  9 674 | 1066 | 4.5 ms | ✅ | **[S4] Rate** admit (decision proj.) · C18 |
| 12 | `cachekey`   | 1594 | 10 912 | 1294 | 7.8 ms | ✅ | **[S5] cache** key · C22/C31 |
| 13 | `hashbytes`  | 1003 | 10 002 | 1126 | 5.3 ms | ✅ | **[S5] cache** `Cache.hashBytes` fold · C20 |
| 14 | `cachefresh` | 1481 |  9 674 | 1066 | 4.6 ms | ✅ | **[S5] cache** freshness · C18 |
| 15 | `redirectstatus` | 1742 | 9 955 | 1118 | 4.8 ms | ✅ | **[S6] Redirect** status pick · C17 |
| 16 | `traversal`  | 2219 | 10 979 | 1306 | 7.5 ms | ✅ | **[S7] traversal** guard · C24 |
| 17 | `admit`      | 1532 | 10 785 | 1270 | 7.8 ms | ✅ | **[S8] policy** admission · C23/C25 |
| 18 | `copy`       | 1140 |  9 878 | 1104 | 4.8 ms | ✅ | **[S9] headerRewrite / [S14] Header** · C30 |
| 19 | `cors`       | 1841 | 10 775 | 1268 | 7.5 ms | ✅ | **[S10] deployCors** · C25 |
| 20 | `gzipupper`  | 1463 |  9 791 | 1088 | 4.9 ms | ✅ | **[S11] Gzip** len upper-bound (decision proj.) · C18 |
| 21 | `secheaders` | 1765 |  9 674 | 1066 | 4.6 ms | ✅ | **[S13] SecurityHeaders** · C26 |
| **Supporting decision probes** ||||||||
| 22 | `clen`       | 1163 |  9 982 | 1122 | 5.1 ms | ✅ | content-length digit count (BodyLimit) · C21 |
| 23 | `statusclass`| 1463 | 10 119 | 1148 | 5.1 ms | ✅ | RFC-9110 status classification · C15/C16 |
| 24 | `machinestep_gate` | 1311 | 9 818 | 1092 | 5.0 ms | ✅ | machine-step admission gate · C14/C16 |
| 25 | `reflect`    | 1365 | 10 226 | 1168 | 5.9 ms | ✅ | bytes-reflection bridge probe · C32 |
| 26 | `tiny`       |  303 |  9 034 |  992 | 3.6 ms | ✅ | minimal non-toy probe · C33 |
| **EmitPancake-generated (Lean → `.pnk`)** ||||||||
| 27 | `region`     |  704 | 10 340 | 1188 | 6.5 ms | ✅ | `emitRegion regionC0` — **≡ boundscan** (md5-identical `.S`) |
| 28 | `machine`    |  588 | 10 283 | 1178 | 5.6 ms | ✅ | `emitMachine machineC0` — guarded threshold scan |
| | **TOTAL** | | | **34 012** | | **28/28** | |

**`.text`-size note (honesty).** `size *.o` reports **`.text` ≈ 8260 B for every stage**
(freelist/tiny 8243). That figure is **NOT** a per-program discriminator — it is
dominated by the fixed CakeML runtime/basis trampoline (`cml_main`, `cake_main`,
FFI stubs) that is byte-for-byte identical in every standalone image. The genuine
per-program signal is the **CODE** column (the `.byte` machine-code literals the
compiler emits for the stage body); `boundscan.o` and `parseline.o` have identical
`.text=8260` yet **different object md5** and different CODE (1188 vs 1942). I report
CODE, not `.text`, as the per-stage size.

---

## 2. My-hand-runnable commands (verbatim, hbox)

```bash
ssh hbox@hbox.local
CAKE=/home/hbox/r05/cake-x64-64/cake
cd /home/hbox/pnk-manifest                       # 28 real serve .pnk live here

# one stage, end to end (native compile → assemble → prove ELF + size):
$CAKE --pancake < boundscan.pnk > boundscan.S    # ~7 ms
cc -c boundscan.S -o boundscan.o                 # assemble
file boundscan.o                                 # ELF 64-bit … x86-64
size boundscan.o                                 # .text/.data (see .text note §1)
grep -oE '0x[0-9A-Fa-f]{2}' boundscan.S | wc -l  # = CODE bytes (real program size)

# the whole sweep (compile + best-of-20 timing + cc -c ELF check, all 28):
bash /home/hbox/pnk-manifest/sweep.sh            # reproduces the §1 table

# the EmitPancake generator (Lean → .pnk), from the DreggNet checkout:
cd ~/dev/DreggNet && lean --run Dsl/EmitPancake.lean   # writes emit/region.pnk + emit/machine.pnk
```

The `.pnk` sources are in the DreggNet tree under `docs/engine/probes/compiler/`
(`pnk/` for the 7 substrate stages, `hol-c*/` for the C-series stages, `emit/` for the
two generated ones); the exact canonical version chosen for each stage is the one
copied into `/home/hbox/pnk-manifest/` (latest C-series dir per stage).

---

## 3. Coverage against the deployed serve (`deployStagesFull2`, 14 stages)

`deployStagesFull2` (`Reactor/Deploy.lean:1511`) is the ordered chain `main` folds. Its
14 stages map onto the sweep as:

| # | `deployStagesFull2` stage | `.pnk` | status |
|---|---|---|---|
| S1 | `jwtAdminStage` | `jwt` | ✅ compiles |
| S2 | `BasicAuth.basicStage` | `basic` | ⚠️ decision projection only — base64-decode + byte-compare **loop** is a residual |
| S3 | `IpFilter.ipfilterStage` | `ipf` | ✅ compiles (deny 10.0.0.0/8, C29) |
| S4 | `Rate.rateStage` | `rateadmit` | ⚠️ token-bucket **decision** only — windowed-counter loop is a residual |
| S5 | `cacheEmptyStage` | `cachekey`,`hashbytes`,`cachefresh` | ✅ compiles (key + `hashBytes` fold + freshness) |
| S6 | `Redirect.redirectStage` | `redirectstatus` | ✅ compiles (RFC-9110 status pick) |
| S7 | `traversalStage` | `traversal` | ✅ compiles |
| S8 | `policyStage` | `admit` | ✅ compiles |
| S9 | `headerRewriteStage` | `copy` | ✅ compiles |
| S10 | `deployCorsStage` | `cors` | ✅ compiles |
| S11 | `Gzip.gzipStage` | `gzipupper` | ⚠️ length upper-bound **decision** only — body-rewrite loop is a residual |
| S12 | `HtmlRewrite.htmlrewriteStage` | **—** | ❌ **NO `.pnk`** — streaming-tokenizer body rewrite (real loop/parser, §4) |
| S13 | `SecurityHeaders.securityheadersStage` | `secheaders` | ✅ compiles (unconditional header set, C26) |
| S14 | `Header.headerStage` | `copy` | ✅ compiles (shares the C30 copy/rewrite emitter) |

**Coverage: 13 / 14 stages have a native-compiling `.pnk`; 1 (S12 HtmlRewrite) has
none.** Of the 13, **S2/S4/S11** compile only their **loop-free decision projection**
(the exact honest caveat `Pancake/ServeFragment.lean` names for BasicAuth/Rate/Gzip):
the standalone `.pnk` is the branch/threshold the stage decides on, **not** the full
base64-parse / windowed-counter / body-rewrite loop body. That is the named Link-A
loop residual (CN §4.1), not a compiler limitation — `parseline`/`boundscan`/`arenascan`
prove the compiler emits real `while`+`ld8`+`st8` loops today; the residual is the
*refinement proof* for each loop, not the compile.

---

## 4. The gap to a **full-serve `.pnk`** — precise, named

The sweep produces **28 standalone programs**, not a serve. Four concrete items stand
between here and a single bootstrap-certified full-serve x64 image; **none is leanc,
none is the backend metatheory, none is compiler cost**:

1. **One missing stage — `HtmlRewrite` (S12).** No `.pnk` exists. It is a genuine
   streaming-tokenizer **body rewrite** (`~/dev/drorb/Reactor/Stage/HtmlRewrite.lean`:
   "the real streaming tokenizer … over the response body and emits the rewritten
   bytes"), content-type-gated. Emitting a `.pnk` *shell* for it via EmitPancake is
   mechanically possible (the surface has `while`/`ld8`/`st`), but **without its
   Link-A refinement that artifact would be a mirror** — it would compile green and
   prove nothing about `htmlrewriteStage`. **I did not write it.** The obstruction is
   the loop refinement, and it is named here rather than faked.

2. **Three loop-body residuals — BasicAuth / Gzip / Rate (S2/S4/S11).** Each compiles
   its decision projection today; the full parse/window/rewrite loop body + its
   `While`-invariant + FFI-trace Link-A refinement is the outstanding front-end work
   (the C11 §4 named residual, `mk_wrapper`-generatable per C20 §5).

3. **Composition — 28 images → 1 fused serve.** Every stage is compiled as its own
   `main` with a private `cake_main`/basis. A full serve is the **14-stage fold as one
   Pancake program**: a single entry, the stages sequenced/threaded through one `Ctx`,
   sharing **one** FFI-oracle contract (`@load_vec`/`@report_vec`). The in-logic compose
   machinery exists (C22 compose-stage, C23 compose-generator) but **no fused
   `serve.pnk` has been emitted or native-compiled**. This is the single biggest item.

4. **The bytes-reflection bridge + runtime-install antecedents** (CN §3.3, §4.3) —
   unchanged: mechanize "the native run's bytes discharge Link B on bootstrap
   authority" per stage, and discharge the standard x64 install package
   (`pan_installed`, register/heap layout) + the per-stage FFI contract via the x64
   target-config proof and the `basis_ffi.c` + `*_ffi.c` shims present alongside each
   `.pnk`.

**What is closed:** the *compile-cost* problem (CN's thesis) is closed for the whole
breadth — 28 real stages, loops + FFI included, compile to assemblable x64 in
single-digit-to-20 ms each. The full-serve gap is now a **coverage + composition**
problem (items 1–3) sitting on the bootstrap-certification residual (item 4), exactly
as CN §4 predicted.

---

## 5. EmitPancake — the Lean→`.pnk` generator is live and axiom-free (verified)

Two stages in the sweep (`region`, `machine`) are **generated**, not hand-authored:

```
$ cd ~/dev/DreggNet && lean --run Dsl/EmitPancake.lean
wrote emit/region.pnk and emit/machine.pnk
$ diff <(git show HEAD:…/emit/region.pnk) …/emit/region.pnk     # identical
```

- `emitRegion regionC0` → `region.pnk` → native-compiles to a program whose `.S` is
  **md5-identical to `boundscan.S`** (row 27 ≡ row 1): the generator *reproduces* the
  hand-written C0 stage on the nose, post-compile.
- `emitMachine machineC0` → `machine.pnk` → a **distinct** guarded threshold-scan
  program (1178 CODE B, its own `.S`).
- **Axiom-free, verified on hbox** (not asserted):
  ```
  'Dsl.EmitPancake.emitRegion' does not depend on any axioms
  'Dsl.EmitPancake.emitMachine' does not depend on any axioms
  ```
  (`#print axioms` on the fully-qualified `Dsl.EmitPancake.{emitRegion,emitMachine}`.)

The emission surface is the honest C0/C1-proven subset (`Var/Const/@base`, `+ * < &`,
`lds/ld8`, `var/assign/if/while/st/@ffi/return`). It currently exposes **two** emitters
(region, machine); emitting the missing S12/loop-body stages needs a **new** faithful
emitter **plus** its Link-A refinement — the §4 item-1/2 residual, not a today-tractable
drop.

---

## 6. Residuals, named precisely

- **R1 (composition).** No fused `serve.pnk` (the 14-stage fold as one Pancake program /
  one FFI contract). 28 standalone images exist. *Biggest gap.*
- **R2 (missing stage).** `HtmlRewrite` (S12) has no `.pnk`; body-rewrite loop —
  refinement obstruction reported, mirror **not** written.
- **R3 (loop bodies).** BasicAuth/Rate/Gzip (S2/S4/S11) compiled as decision
  projections; full loop bodies + Link-A refinements outstanding.
- **R4 (bootstrap certification).** Unchanged from CN §3: version skew
  (`ccfc23c` binary vs `ed31510` proof, 14 commits, same lineage), bootstrap proof is
  upstream/CI not rebuilt locally, and the bytes-reflection bridge is unmechanized.
- **R5 (install antecedents).** Standard x64 install package + per-stage FFI-oracle
  contract discharged by the x64 target-config proof — not yet wired per stage.

None of R1–R5 is leanc; none reintroduces the in-logic EVAL cost.

# CN REPORT — RUNG-3 END-TO-END: COMPOSE the native-bytes backbone with the whole-`main` FFI-trace frame — the NATIVE-compiled `boundscan` machine code PROVEN to refine the Lean/Pancake spec, its observable `@report_vec` trace reporting EXACTLY `n2w (c0_encode (boundScan a off len))`, via bootstrap. `boundScan_rung3_e2e` (`[oracles: DISK_THM] [axioms:]`, hyps=0) and `boundScan_rung3_e2e_native` (`[oracles: DISK_THM, cake_native_bootstrap] [axioms:]`, hyps=0), 0 theory axioms.

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Proof tree:** `/home/hbox/src/cakeml` @ `ed31510b3`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2, stdknl), Poly/ML. **Native compiler:** `/home/hbox/r05/cake-x64-64/cake`.
**This lane's HOL4 scratch:** `/home/hbox/hol-rung3-e2e/` (new, self-contained; **no CakeML-tree file modified**) — mirrored to `docs/engine/probes/compiler/hol-rung3-e2e/` (`boundScanRung3E2EScript.sml` md5 `e5b44cc6…`, `boundScanE2EFrameScript.sml` md5 `4d0a1682…`, == hbox).
**Ground COMPOSED (all pre-proven, unmodified):** `CN-RUNG3-INSTALL-REPORT.md` (`boundScan_rung3_installed`, the native-bytes backbone @ x64 config), `CN-RUNG3-WHOLEMAIN/FINISH/NATIVE/BYTES-BRIDGE-FULL` reports, and the **C13 whole-`main` FFI-trace frame** (`~/hol-c13`: `mainBody_refines` → `main_semantics` → the c13 `boundScanProg_semantics_decls`, `[oracles: DISK_THM]`) + `boundScan_G1_native` (`~/hol-rung3-finish/boundScanPkg`, oracle `cake_native_bootstrap`).

---

## 0. TL;DR — what closed, and the two named gaps, honestly

The task named two last gaps to close end-to-end: (1) the whole-`main` FFI-trace frame lifting the loop refinement to `semantics_decls s «main» boundScanProg`, and (2) the concrete x64 install machine-state discharging the install antecedent. Then COMPOSE to the end-to-end theorem.

**What this lane delivers — the COMPOSITION, kernel-checked, non-vacuous, no `cheat`/`new_axiom`/`native_decide`:**

- **`boundScan_rung3_e2e`** (`[oracles: DISK_THM] [axioms:]`, `Thm.hyp = 0`, `axioms "boundScanRung3E2E" = 0`) — the native-bytes backbone `boundScan_rung3_installed` (the concrete reflected native `boundScanBytes`/`boundScanBitmaps` in the `compile_prog_max` **and** `pan_installed` slots, x64 config-well-formedness discharged) with its opaque `{semantics_decls s «main» boundScanProg}` set-element **rewritten** to the digest trace by the whole-`main` FFI-trace frame:
  ```
  machine_sem mc ffi ms ⊆
    extend_with_resource_limit' (option_lt stack_max (SOME (FST (read_limits x64_config x64_backend_config mc ms))))
      { Terminate Success (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]) }
  ```
  i.e. **every observable behaviour of the installed machine code is the single terminating trace whose `@report_vec`-emitted result word is EXACTLY the Lean spec `n2w (c0_encode (boundScan a off len))`** (`model/BoundScan.lean` `C0.encode (C0.boundScan a off len)`).

- **`boundScan_rung3_e2e_native`** (`[oracles: DISK_THM, cake_native_bootstrap] [axioms:]`, `Thm.hyp = 0`) — the same, with the **G1 native-bytes antecedent DISCHARGED via the bootstrap** (`boundScan_G1_native` ⇐ `cake_compiled_thm`): the install package need only hold for *whatever config the compiler emits alongside `boundScanBytes`* (`∀c' stack_max. compile_prog_max … = (SOME (boundScanBytes,…),stack_max) ⇒ pkg c'`), and the bootstrap supplies that the compiler's output **is** the native `boundScanBytes`. The single named `cake_native_bootstrap` oracle is quarantined to G1 — no larger than trusting an EverCrypt release build.

**Gap (1) — the whole-`main` FFI-trace frame: CLOSED (composed).** `semantics_decls s «main» boundScanProg` is reduced to the digest trace by `boundScanProg_semantics_decls_bridge` (this lane, `[oracles: DISK_THM]`), which rests on the **C13** whole-`main` frame (`mainBody_refines`: the full `main` body — outer `Dec`s, `@load_vec`, control-block `Load`s, the bounds-`If`, the digest loop, `Store`, `@report_vec`, `Return` — run to a `Return 0w` emitting the digest event; `main_semantics`: lifted through `Call NONE «main» []` + the all-clocks `panSem$semantics`). The C13 frame was proven Jul-6 but stated over the **C11** `boundScanProg` (symbolic-bytes Link-B) and its own `boundScanInstall` theory; this lane re-proves the `semantics_decls` reduction over `boundScanBytesBridge$boundScanProg` — the **exact** program the native backbone carries (aconv-identical to C10/C11, §3) — and COMPOSES it with the native-bytes backbone. The frame is **tied to the real verified-parser program**, not a mirror: `boundScanProg_semantics_decls_bridge` EVAL-proves `FLOOKUP s'.code «main» = SOME ([], mainBody)` from `boundScanBytesBridge$boundScanProg_def`, so `mainBody` **is** the actual `main` body.

**Gap (2) — the concrete x64 install machine-state: NOT discharged; kept as a NAMED antecedent (honest boundary, not faked).** `pan_installed boundScanBytes … ms …` + the placed-image geometry (heap/register/globals/bitmap layout, alignment) is the **loader / target-config contract** — exactly the `installed` fact CakeML's own end-to-end examples leave as a hypothesis (`helloProof` `DISCH_ALL`s it against a concrete placed image). Constructing a concrete `ms` with `boundScanBytes` placed and discharging `pan_installed` against it is genuine target-config engineering with **no worked Pancake `pan_installed`-against-concrete-`ms` example in this tree to reuse** (CN-RUNG3-INSTALL §5). It is **not** produced as a vacuous/EVAL'd restatement. Likewise the **`@load_vec`/`@report_vec` FFI-oracle contract `boundScanFFI`** (the arena bytes enter, and the digest leaves, through the abstract `call_FFI s.ffi`) remains a named antecedent — the observable behaviour **is** an FFI I/O trace; it is irreducible (CN-RUNG3-WHOLEMAIN residual (3)).

**So the end-to-end is NOT antecedent-free — nor can it honestly be.** `Thm.hyp = 0` (no floating assumptions; everything is in the implication), but the two physical contracts — `pan_installed boundScanBytes … ms …` (loader) and `boundScanFFI a off len s` (FFI-oracle) — remain as **explicit named antecedents**, exactly as the CakeML-standard `installed` + FFI hypotheses must. A truly hypothesis-free `hyps=0` end-to-end would require fabricating a concrete `ms` and asserting the FFI oracle — the vacuous/faked end-to-end the task forbids. **The honest milestone is the composition under these two named CakeML-standard contracts, which is what closed.**

---

## 1. The theorems (verbatim from the kernel; §4 fresh-session audit)

### `boundScan_rung3_e2e` — the composition (DISK_THM only)

```
boundScan_rung3_e2e                                        [oracles: DISK_THM] [axioms: ]
⊢ is_x64_machine_config mc ⇒
  ( compile_prog_max x64_backend_config mc boundScanProg =
        (SOME (boundScanBytes,boundScanBitmaps,c'),stack_max)   (* G1: native bytes in the slot *)
    ∧ s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧ … (* placed-image geometry, ¬s.be *)
    ∧ pan_installed boundScanBytes cbspace boundScanBitmaps data_sp
        c'.lab_conf.ffi_names (heap_regs x64_backend_config.stack_conf.reg_names)
        mc c'.lab_conf.shmem_extra ms (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs )
  ∧ boundScanFFI a off len s                                   (* the FFI-oracle contract *)
  ∧ (∃K. 0 < K ∧ len < K)                                     (* a witness clock *)
  ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
      extend_with_resource_limit'
        (option_lt stack_max (SOME (FST (read_limits x64_config x64_backend_config mc ms))))
        { Terminate Success
            (s.ffi.io_events ++ loadEv ++
             [IO_event (ExtCall «report_vec»)
                (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]) }
```

The `semantics_decls s «main» boundScanProg ≠ Fail` side-condition of the backbone is **proved here** (from the frame's `Terminate Success … ≠ Fail`), not assumed — it is absent from the antecedent above.

### `boundScan_rung3_e2e_native` — G1 discharged by the bootstrap

```
boundScan_rung3_e2e_native                    [oracles: DISK_THM, cake_native_bootstrap] [axioms: ]
⊢ is_x64_machine_config mc ⇒
  ( ∀c' stack_max.
      compile_prog_max x64_backend_config mc boundScanProg =
          (SOME (boundScanBytes,boundScanBitmaps,c'),stack_max) ⇒
      ( <placed-image geometry> ∧
        pan_installed boundScanBytes … c'.lab_conf … ms … ∧
        boundScanFFI a off len s ∧ (∃K. 0 < K ∧ len < K) ) )
  ⇒
  ∃stack_max loadEv rb.
    machine_sem mc ffi ms ⊆
      extend_with_resource_limit'
        (option_lt stack_max (SOME (FST (read_limits x64_config x64_backend_config mc ms))))
        { Terminate Success
            (s.ffi.io_events ++ loadEv ++
             [IO_event (ExtCall «report_vec»)
                (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]) }
```

The universally-quantified `compile_prog_max … = (SOME (boundScanBytes,…),…) ⇒ pkg c'` is the honest way to state "the install package holds for the **actual** (bootstrap-certified) native output"; `boundScan_G1_native` (`cake_native_bootstrap` ⇐ `cake_compiled_thm`, under `mc.target.config = x64_config` supplied by `is_x64_machine_config mc`) instantiates it to the concrete native bytes.

### `boundScanProg_semantics_decls_bridge` — the frame reduction (this lane, isolated theory)

```
boundScanProg_semantics_decls_bridge                       [oracles: DISK_THM] [axioms: ]
⊢ s.code = FEMPTY ∧ boundScanFFI a off len s ∧ (∃K. 0 < K ∧ len < K) ⇒
  ∃loadEv rb.
    semantics_decls s «main» boundScanProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb])
```

over `boundScanBytesBridge$boundScanProg`. Proof: `decs_stcnames [] boundScanProg = SOME []` and `evaluate_decls (s with structs := []) boundScanProg` install `«main» ↦ ([], mainBody)` (both by `EVAL` on `boundScanProg_def` — kernel-checks `mainBody` **is** the real `main` body), then the C13 `main_semantics` (⇐ `mainBody_refines`). Kept in the sibling theory `boundScanE2EFrame` with **minimal opens** so the fragile `simp [semantics_decls_def, …EVAL…]` step is not perturbed by the x64/backend stateful simpset the composition theory pulls in (paid for in debugging — see §6).

---

## 2. How the composition works (theory `boundScanRung3E2E`, `axioms = 0`)

```
   NATIVE bytes track (rung3)                     WHOLE-MAIN FFI-trace frame track (c13)
   ─────────────────────────                      ────────────────────────────────────────
   cake --pancake < boundscan.pnk                  mainBody_refines  (the full main body run,
     → boundScanBytes (1188 B x64)                   @load_vec/If/loop/@report_vec → Return 0w,
   boundScan_G1_native  (cake_native_bootstrap)      digest event)          [c13, DISK_THM]
   boundScan_rung3_native  (Link B, 4 conds)        main_semantics  (Call + all-clocks semantics)
   boundScan_rung3_installed  (x64 cfg,  DISK_THM)                          [c13, DISK_THM]
     machine_sem ⊆ {semantics_decls s «main» P}    boundScanProg_semantics_decls_bridge  (THIS LANE)
             │                                        semantics_decls s «main» P = Terminate Success
             │   (A) re-derived here (config              (trace carrying n2w(c0_encode(boundScan …)))
             │        discharge, verbatim recipe)                     │  [DISK_THM]
             └───────────────┬────────────────────────────────────────┘
                             ▼   (C) rewrite the opaque {semantics_decls …} with the digest trace
                   boundScan_rung3_e2e         [DISK_THM]           (§1)
                             │   (D) discharge G1 via boundScan_G1_native
                             ▼
                   boundScan_rung3_e2e_native  [DISK_THM, cake_native_bootstrap]
```

- **(A)** the config-well-formedness discharge of the install antecedent (`boundScan_rung3_native` @ `x64_backend_config` under `is_x64_machine_config mc`, 31→25 antecedents, the five `x64_configProof` well-formedness lemmas + the `INST_TYPE` β-fix) is **re-derived verbatim** from `~/hol-rung3-install` (avoiding the `boundScanInstall` theory-name clash between the rung3 and c13 tracks — both define a theory of that name).
- **(B)** the frame reduction `boundScanProg_semantics_decls_bridge` (§1), in the sibling `boundScanE2EFrame`.
- **(C)** the goal is built in ML from the backbone's own antecedent/conclusion (no transcription): drop the `≠ Fail` conjunct (proved from (B)), add `boundScanFFI` + witness, substitute `Terminate Success <trace>` for the opaque `semantics_decls` in the singleton set.
- **(D)** `boundScan_G1_native` instantiates the `compile_prog_max … = (SOME (boundScanBytes,…),…)` conjunct with the bootstrap-certified native bytes.

---

## 3. The `boundScanProg` unification (why the composition is legitimate, not a mirror)

The native backbone states `semantics_decls s «main» boundScanBytesBridge$boundScanProg`; the C13 frame was proven over `boundScanLinkBInst$boundScanProg` (C11). Both are `OUTL (parse_topdecs_to_ast <boundscan.pnk>)` for the **byte-identical** `boundscan.pnk` (md5 `8482e9cb…`) under the same CakeML-verified Pancake parser. An `aconv` audit in a fresh `hol` confirmed:
`boundScanLinkBInst$boundScanProg` **≡** `boundScanLinkB$boundScanProg` (C10) **≡** `boundScanBytesBridge$boundScanProg` (all `aconv = true`), and `boundScan_rung3_installed`'s conclusion carries `boundScanBytesBridge$boundScanProg`. So re-proving `boundScanProg_semantics_decls_bridge` over the bytes-bridge program (its `boundScanProg_def` for the `EVAL`) is faithful, and the rewrite in (C) is a direct set-element substitution. The `EVAL`-checked `FLOOKUP s'.code «main» = SOME ([], mainBody)` ties `mainBody` to the **real** program's `main` body — this is not a hand-transcribed mirror.

**Spec provenance (a named cross-prover boundary, not a HOL theorem):** the digest is `boundScanCoreLinkA$c0_encode (boundScanCoreLinkA$boundScan a off len)` (C12), which its own header declares **"byte-identical to `model/BoundScan.lean` `C0.encode`/`C0.boundScan`"** — a re-declaration of the Lean spec in HOL, checked by inspection, the standard Lean↔HOL spec-identity boundary (the leanc text→AST is out of TCB via the verified parser; the Lean↔HOL *digest* identity is by-inspection re-declaration).

---

## 4. Independent verification (ran it; "it built" is checked, not asserted)

- **Clean from-scratch build GREEN.** Deleted `boundScan{Rung3E2E,E2EFrame}Theory.*` + `.hol` artifacts, `Holmake` → `boundScanE2EFrameTheory (21s) [1/2] OK`, `boundScanRung3E2ETheory (18s) [2/2] OK` (loads the prebuilt pancake/backend/x64/c10–c13/rung3 proofs; **no CakeML-tree file modified**). Not a stale `.dat`.
- **Real kernel tags, fresh load** (`Tag.dest_tag (Thm.tag …)`, not a grep): `boundScan_rung3_e2e` = `oracles=[DISK_THM] axioms=[]`, `Thm.hyp = 0`; `boundScan_rung3_e2e_native` = `oracles=[DISK_THM, cake_native_bootstrap] axioms=[]`, `Thm.hyp = 0`; `boundScanProg_semantics_decls_bridge` = `oracles=[DISK_THM] axioms=[]`. `axioms "boundScanRung3E2E" = 0`, `axioms "boundScanE2EFrame" = 0`. **No `cheat`, no `new_axiom`, no `native_decide`** (HOL4 has no `ofReduceBool`); the only oracle beyond `DISK_THM` is the single named `cake_native_bootstrap`, quarantined to G1 in `_native`.
- **Non-vacuity — fully-qualified `dest_thy_const` audit** of `boundScan_rung3_e2e`'s conclusion: `boundScanBytesBridge$boundScanBytes` / `$boundScanBitmaps` (the reflected **native** code, in the `compile_prog_max` and `pan_installed` slots), `pan_to_targetProof$pan_installed`, `boundScanBytesBridge$boundScanProg`, `boundScanCoreLinkA$boundScan` / `$c0_encode` (the Lean digest), `boundScanWrapperLinkA$boundScanFFI`, `targetSem$machine_sem`, `x64_configProof$is_x64_machine_config`, `ffi$Terminate`. The theorem carries the load-bearing native code + real spec digest, not a placeholder.
- **`boundScanProg` `aconv` identity** C10 ≡ C11 ≡ bytes-bridge verified in a fresh `hol` (§3).
- **Native compile reproduced** (inherited): `cake --pancake < boundscan.pnk` md5-stable, 1188 `boundScanBytes`, assembles to x86-64 (CN-RUNG3-NATIVE §3).

**Scope note:** HOL4/CakeML COMPILER-track lane. Touches no Lean spec, no `Datapath.lean`, no `libdrorb`, no Rust dataplane — **no `cargo` / `build-dataplane-lib.sh` / `curl` delta**. The mergeable artifact is the two new HOL4 theories (`boundScanRung3E2E`, `boundScanE2EFrame`) + `Holmakefile` + audit + this report.

---

## 5. What remains (named, not papered over)

The composition closes the distance the rung3 track named open — the whole-`main` frame that lifts the loop refinement to the whole-program observable and the rewrite into the native-bytes backbone. What **remains as named antecedents** (the CakeML-standard contracts, deliberately not faked):

1. **`pan_installed boundScanBytes … ms …` + the placed-image geometry** — the loader / target-config contract. Requires a **concrete initial machine state `ms`** with the 1188-byte `boundScanBytes` + bitmaps placed at the entry PC and the registers set to the heap/stack/bitmap bounds, discharged against `good_init_state`/`pan_installed`. CakeML leaves the same fact as a `DISCH_ALL` hypothesis (`helloProof`); there is no worked Pancake `pan_installed`-against-concrete-`ms` example in this tree. **Kept as antecedent — genuine target-config engineering, not a one-lemma gap.**
2. **`boundScanFFI a off len s`** — the `@load_vec`/`@report_vec` FFI-oracle contract. The observable behaviour **is** an FFI I/O trace: the arena bytes arrive, and the digest word leaves, through the abstract `call_FFI s.ffi`. **Irreducible** (CN-RUNG3-WHOLEMAIN residual (3)); it is the front-end↔C-driver contract, scoped as a named hypothesis.
3. **`is_x64_machine_config mc` + a witness clock `∃K. 0 < K ∧ len < K`** — standard.
4. **Inherited (CN-NATIVE-BOOTSTRAP §3):** the `cake` binary is 14 commits behind the `ed31510` proof checkout (same lineage), and `cake_compiled_thm` is the upstream/CI whole-compiler bootstrap, not rebuilt locally. The Lean↔HOL *digest* identity (§3) is by-inspection re-declaration.

None of the residual is the in-logic-EVAL dead end; none is leanc.

---

## 6. Files & reproduce

**On hbox** (`/home/hbox/hol-rung3-e2e/`, self-contained): `boundScanRung3E2EScript.sml` (md5 `e5b44cc6…`), `boundScanE2EFrameScript.sml` (md5 `4d0a1682…`), `Holmakefile` (INCLUDES the CakeML pancake/backend/x64/x64-proofs dirs + `~/c6work` + `~/hol-c10..c13` + `~/hol-boundscan-linka` + `~/hol-bytes-bridge` + `~/hol-rung3-native` + `~/hol-rung3-finish`), `audit_final.sml` / `final_audit.out` (the fresh-session tag + non-vacuity dump), `build.log` / `cleanbuild.log`.
**In this repo** (`docs/engine/probes/compiler/hol-rung3-e2e/`): the same, md5-matched, plus this report.

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
cd ~/hol-rung3-e2e
rm -f boundScan{Rung3E2E,E2EFrame}Theory.* ; find .hol -name "*boundScan*E2E*" -delete
Holmake                          # boundScanE2EFrame [1/2] OK, boundScanRung3E2E [2/2] OK
hol < audit_final.sml            # tags + hyps=0 + axioms=0 + native oracle set + non-vacuity
# theorem names (boundScanRung3E2EScript.sml):
#   composition (DISK_THM)          : boundScan_rung3_e2e
#   bootstrap-certified             : boundScan_rung3_e2e_native   ([…, cake_native_bootstrap])
#   frame reduction (boundScanE2EFrameScript.sml) : boundScanProg_semantics_decls_bridge
```

## 7. Bottom line

The boundscan Rung-3 end-to-end **composes**: the native-bytes backbone (`boundScan_rung3_installed`, the reflected `cake`-compiled `boundScanBytes` in the `compile_prog_max`/`pan_installed` slots, x64 config discharged) meets the whole-`main` FFI-trace frame (`boundScanProg_semantics_decls_bridge` ⇐ the C13 `mainBody_refines`/`main_semantics`, reducing `semantics_decls s «main» boundScanProg` to the digest trace) in `boundScan_rung3_e2e` (`[oracles: DISK_THM] [axioms:]`, hyps=0, 0 theory axioms) — **every observable behaviour of the installed NATIVE machine code is the terminating trace reporting `n2w (c0_encode (boundScan a off len))`, the Lean `model/BoundScan.lean` digest** — and, with the G1 native-bytes antecedent discharged by the bootstrap, in `boundScan_rung3_e2e_native` (`[oracles: DISK_THM, cake_native_bootstrap] [axioms:]`, hyps=0). **HONEST boundary:** this is NOT antecedent-free — the loader contract (`pan_installed boundScanBytes … ms …` + placed-image geometry) and the FFI-oracle contract (`boundScanFFI`) remain as the two named CakeML-standard hypotheses, deliberately **not** faked with a fabricated `ms` or an asserted oracle. None of the residual is the in-logic-EVAL dead end; none is leanc.

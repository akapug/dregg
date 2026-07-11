# CN REPORT — RUNG-3 INSTALL: the runtime-install antecedent of the boundscan Rung-3 backbone, its config-well-formedness CORE discharged IN-LOGIC against the REAL x64_configProof lemmas — `boundScan_rung3_installed` (`[oracles: DISK_THM] [axioms:]`, 0 theory axioms), and the placed-image geometry + `pan_installed` scoped precisely to the irreducible loader/target-config contract (= CakeML's own `installed` boundary)

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Proof tree:** `/home/hbox/src/cakeml` @ `ed31510b3`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2).
**This lane's HOL4 scratch:** `/home/hbox/hol-rung3-install/` (new, self-contained; no CakeML-tree file modified) — mirrored to `docs/engine/probes/compiler/hol-rung3-install/` (`boundScanInstallScript.sml` md5 `b376884c…` == hbox).
**Ground:** `CN-RUNG3-NATIVE-REPORT.md` (`boundScan_rung3_native`, the backbone, 31 antecedent conjuncts, `[oracles: DISK_THM]`), `CN-RUNG3-FINISH-REPORT.md` + `CN-BYTES-BRIDGE-FULL-REPORT.md` (the runtime-install antecedent = the `<install package>` hypothesis / residual (3); `boundScan_G1_native` closed G1 separately). The install antecedent is the machine-state setup: code+data installed in memory, the initial machine config.

---

## 0. TL;DR — what closed, what is scoped

The RUNG-3-NATIVE/FINISH reports named the **runtime install package** (their residual (3)) as the last unattacked block of `boundScan_rung3_native`'s antecedent: `pan_installed …`, `backend_config_ok`, `mc_conf_ok`, `mc_init_ok`, the heap/register/globals/bitmap layout, the `s.code/locals/globals = FEMPTY` boilerplate, endianness, and the FFI-oracle contract. This lane **splits that block** and discharges the part that is genuinely a well-formedness fact, in-logic, against the concrete x64 machine config:

- **The config-well-formedness CORE of the install package is DISCHARGED, kernel-proven, no EVAL of the backend.** `boundScan_rung3_installed` (`[oracles: DISK_THM] [axioms:]`, `axioms "boundScanInstall" = 0`) instantiates the backbone at the concrete x64 backend config (`c := x64_backend_config`) under the single well-formedness hypothesis `is_x64_machine_config mc`, and removes **six** antecedent conjuncts (31 → 25) using the REAL CakeML x64 lemmas (`x64_configProofTheory`):
  - `backend_config_ok mc.target.config c`  — `x64_backend_config_ok`
  - `mc_conf_ok mc`                          — `x64_machine_config_ok`
  - `mc_init_ok mc.target.config c mc`       — `x64_init_ok`
  - `mc.target.config.ISA ≠ Ag32`           — EVAL on `x64_config`
  - `OPTION_ALL (EVERY (λx. ∃s. x = ExtCall s)) c.lab_conf.ffi_names` — EVAL on `x64_backend_config`
  - `start = «main»`                         — folded (`start := «main»`, cleans the conclusion)

  and **simplifies** the endianness conjunct `mc.target.config.big_endian ⇔ s.be` to the little-endian constraint `¬s.be` (x64 is little-endian). The conclusion's `read_limits mc.target.config …` becomes `read_limits x64_config …`.

- **The placed-image geometry + `pan_installed` + the initial-state relation is SCOPED, not faked.** The remaining 25 conjuncts are: G1 (the native-bytes `compile_prog_max` equation — separately discharged by `boundScanPkgTheory.boundScan_G1_native`, oracle `cake_native_bootstrap`), the `s.code/locals/globals = FEMPTY` / `eshapes` / `s.ffi = ffi` / `¬s.be` initial-state boilerplate, the register/heap/globals/bitmap **geometry** (base_addr/top_addr/memaddrs/globals_size/heap_len/adj_ptr2/4 + the `≤₊`/`aligned` ordering), `pan_installed boundScanBytes … ms …` itself, and non-failure. This block relates a **concrete initial machine state `ms` and Pancake state `s`** (registers + placed code+bitmaps+arena) to the source state — it is the **loader / target-config contract**, exactly what CakeML's own end-to-end examples leave as the `installed` hypothesis (`helloProof` `DISCH_ALL`s it against a concrete placed image). It cannot be discharged in-logic while `ms`/`s` stay symbolic, and is NOT written as a vacuous or EVAL'd restatement.

**No `native_decide`/`ofReduceBool` (HOL4 has none), no `cheat`, no `new_axiom`.** The one carried assumption is `is_x64_machine_config mc` — the CakeML predicate pinning `mc.target = x64_target`, `len_reg=6`, `ptr_reg=7`, etc. — the same well-formedness hypothesis every x64 CakeML end-to-end carries. `boundScan_rung3_installed` = `[oracles: DISK_THM] [axioms:]`.

---

## 1. The theorem (verbatim from the kernel; §4 fresh-session audit)

```
boundScan_rung3_installed                                  [oracles: DISK_THM] [axioms: ]
⊢ is_x64_machine_config mc ⇒
  compile_prog_max x64_backend_config mc boundScanProg =
      (SOME (boundScanBytes,boundScanBitmaps,c'),stack_max) ∧          (* G1: native bytes *)
  s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧            (* initial-state boilerplate *)
  FDOM s.eshapes = FDOM (get_eids (functions boundScanProg)) ∧
  0w <₊ mc.target.get_reg ms mc.len_reg ∧                              (* ── placed-image geometry ── *)
  globals_size = (let dec_shs = dec_shapes boundScanProg;
                      struct_ctxt = decs_stcnames [] boundScanProg
                  in SUM (MAP (size_of_sh_with_ctxt (THE struct_ctxt)) dec_shs)) ∧
  mc.target.get_reg ms mc.len_reg <₊ mc.target.get_reg ms mc.ptr2_reg ∧
  mc.target.get_reg ms mc.len_reg = s.base_addr ∧
  globals_allocatable s boundScanProg ∧
  heap_len = w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * s.base_addr) DIV (dimindex (:64) DIV 8) ∧
  s.top_addr = s.base_addr + bytes_in_word * n2w heap_len − n2w (globals_size * dimindex (:64) DIV 8) ∧
  globals_size ≤ heap_len ∧
  s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg) (heap_len − globals_size) ∧
  aligned (shift (:64) + 1) (mc.target.get_reg ms mc.ptr2_reg + -1w * mc.target.get_reg ms mc.len_reg) ∧
  adj_ptr2 = mc.target.get_reg ms mc.len_reg + bytes_in_word * n2w max_stack_alloc ∧
  adj_ptr4 = mc.target.get_reg ms mc.len2_reg − bytes_in_word * n2w max_stack_alloc ∧
  adj_ptr2 ≤₊ mc.target.get_reg ms mc.ptr2_reg ∧
  mc.target.get_reg ms mc.ptr2_reg ≤₊ adj_ptr4 ∧
  w2n (mc.target.get_reg ms mc.ptr2_reg + -1w * mc.target.get_reg ms mc.len_reg) ≤
      w2n bytes_in_word * (2 * max_heap_limit (:64) x64_backend_config.data_conf − 1) ∧
  w2n bytes_in_word * (2 * max_heap_limit (:64) x64_backend_config.data_conf − 1) < dimword (:64) ∧
  s.ffi = ffi ∧
  ¬s.be ∧                                                              (* was big_endian ⇔ s.be *)
  pan_installed boundScanBytes cbspace boundScanBitmaps data_sp
      c'.lab_conf.ffi_names (heap_regs x64_backend_config.stack_conf.reg_names)
      mc c'.lab_conf.shmem_extra ms (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs ∧
  semantics_decls s «main» boundScanProg ≠ Fail
  ⇒
  machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits x64_config x64_backend_config mc ms))))
      {semantics_decls s «main» boundScanProg}
```

Compared with the ground backbone `boundScan_rung3_native` (31 antecedent conjuncts): the five well-formedness predicates (`backend_config_ok`, `mc_conf_ok`, `mc_init_ok`, `ISA≠Ag32`, the FFI-names shape) and `start = «main»` are **gone**; the endianness conjunct is the little-endian constraint `¬s.be`. The concrete native `boundScanBytes`/`boundScanBitmaps` remain in the `compile_prog_max` and `pan_installed` slots (non-vacuity, §4).

---

## 2. How the install antecedent discharges (theory `boundScanInstall`)

The one load-bearing bridge is that `is_x64_machine_config mc` fixes `mc.target.config`:

```
mc_target_config_x64  [oracles: DISK_THM]
⊢ is_x64_machine_config mc ⇒ mc.target.config = x64_config
```

(`is_x64_machine_config_def` gives `mc.target = x64_target`; `x64_target_def` gives `.config = x64_config`.) The three CakeML x64 well-formedness lemmas then apply **verbatim** — they are the exact predicates `pan_to_target_compile_semantics` is stated over, shared with every CakeML `compile_correct` instantiation:

- `x64_configProofTheory.x64_backend_config_ok  ⊢ backend_config_ok x64_config x64_backend_config`
- `x64_configProofTheory.x64_machine_config_ok  ⊢ is_x64_machine_config mc ⇒ mc_conf_ok mc`
- `x64_configProofTheory.x64_init_ok            ⊢ is_x64_machine_config mc ⇒ mc_init_ok x64_config x64_backend_config mc`

plus two O(1) EVAL facts on the concrete config (`x64_config.ISA ≠ Ag32`; `OPTION_ALL … x64_backend_config.lab_conf.ffi_names`) and `x64_config.big_endian = F`.

The reduction is `INST [c ↦ x64_backend_config, start ↦ «main»]` then `REWRITE_RULE [mc_target_config_x64]` then `SIMP_RULE bool_ss` with the six facts as `EQT_INTRO` rewrites — pure kernel rule application on the backbone, no new tactic proof of the conclusion, no EVAL of the backend.

**One real subtlety (paid for in debugging).** The backbone's `mc` is `(64,β,γ) machine_config` with a **polymorphic** target-state `β`, but `is_x64_machine_config mc` forces `mc` to x64's concrete target-state type. Rewriting `mc.target.config → x64_config` therefore silently no-ops on a type mismatch (`REWRITE_CONV` returns `REFL`) until the backbone is first `INST_TYPE`-specialised to fix `β` to the x64 target-state type — computed by `match_type` against `is_x64_machine_config mc`'s own `mc`. After that the rewrite and all five well-formedness discharges fire. This is faithful, not a workaround: `is_x64_machine_config mc` is only well-typed at that `β`, so the specialisation is forced by the hypothesis, and `ms` (the machine state in `machine_sem mc ffi ms`) is correctly pinned to the x64 state type by the same instantiation.

---

## 3. Where the boundary is, and why the residual is the loader contract (not faked)

The 25 residual conjuncts fall into four named groups:

1. **G1 — the native-bytes equation** `compile_prog_max x64_backend_config mc boundScanProg = (SOME (boundScanBytes,boundScanBitmaps,c'),stack_max)`. **Separately discharged** by `boundScanPkgTheory.boundScan_G1_native` (`[oracles: DISK_THM, cake_native_bootstrap]`, CN-BYTES-BRIDGE-FULL), under `mc.target.config = x64_config` — which `is_x64_machine_config mc` supplies. Not folded in here to keep this lane's install-core theorem `DISK_THM`-only (the `cake_native_bootstrap` oracle stays quarantined to G1).
2. **Initial-state boilerplate** — `s.code/locals/globals = FEMPTY`, `FDOM s.eshapes = FDOM (get_eids (functions boundScanProg))`, `s.ffi = ffi`, `¬s.be`. Trivially satisfied by the initial Pancake state constructor, but genuine **constraints on `s`**; they cannot be rewritten away while `s` is symbolic without asserting a specific `s`.
3. **Placed-image geometry** (~16 conjuncts) — `0w <₊ len_reg`, the `globals_size`/`heap_len`/`adj_ptr2`/`adj_ptr4` layout definitions, `len_reg = s.base_addr`, `globals_allocatable`, `s.top_addr = …`, `s.memaddrs = addresses …`, `globals_size ≤ heap_len`, the `≤₊` register orderings, the `aligned` fact, and the two `max_heap_limit` size bounds. These relate the **concrete initial machine registers** (`mc.target.get_reg ms …`) and the Pancake heap/globals/arena to `s`.
4. **`pan_installed boundScanBytes … ms …`** and **`semantics_decls s «main» boundScanProg ≠ Fail`**.

Groups 2–4 are the **runtime install package proper**: they hold **iff** a concrete initial machine state `ms` has the 1188-byte `boundScanBytes` + bitmaps placed in memory at the entry PC, the control-block/arena words laid out, and the registers (`len_reg`/`ptr2_reg`/`len2_reg`) set to the heap/stack/bitmap bounds — i.e. the output of the x64 startup + loader against the placed image. `pan_installed_imp_installed` (`pan_to_targetProofScript.sml:328`) shows `pan_installed` is exactly the Pancake wrapper over CakeML's `installed` plus the arena/bitmap layout. **CakeML's own end-to-end examples do not discharge `installed` in-logic either** — `helloProof` leaves it (and `is_x64_machine_config mc`) as a `DISCH_ALL` hypothesis about the concrete machine. So this lane reaches the *same* boundary CakeML reaches: the well-formedness of the config is proven; the placed-image `installed`/`pan_installed` fact is the operational loader contract, discharged only against a concrete `ms` (the target-config discharge the ground reports scheduled as engineering), and is honestly named here, not produced as a vacuous or whole-program-EVAL restatement.

One conjunct in group 3 — `w2n bytes_in_word * (2 * max_heap_limit (:64) x64_backend_config.data_conf − 1) < dimword (:64)` — is **config-only** (no `ms`/`s`) and in principle EVAL-closable; in-session `EVAL_TAC` reduced `max_heap_limit`/`shift` but stalled on `shift_length x64_backend_config.data_conf` inside the tight `≈ 2^64 − 8 < 2^64` big-number inequality. Left in the residual rather than shipped half-proven; it is a decidable side-condition, not the loader contract.

---

## 4. Independent verification (ran it; "it built" is checked, not asserted)

- **Clean from-scratch build GREEN.** `rm -f boundScanInstallTheory.* install.out` then `Holmake boundScanInstallTheory.uo` → `boundScanInstallTheory (16s) [1/1] OK` (loads the prebuilt pancake/backend/x64/rung3-native proofs; no CakeML-tree file modified). Not a stale `.dat`.
- **Real tags read from the kernel in a FRESH `hol`** (`Tag.dest_tag (Thm.tag …)`, not a grep-count): `boundScan_rung3_installed` = `oracles=[DISK_THM] axioms=[]`; `mc_target_config_x64` = `oracles=[DISK_THM] axioms=[]`; `axioms "boundScanInstall" = 0`. **No `cheat`, no `new_axiom`, no `native_decide`.**
- **Structural non-vacuity audit** (`audit_install.sml`, fresh session): the reduced antecedent has **25** conjuncts; `backend_config_ok`/`mc_conf_ok`/`mc_init_ok`/`Ag32` are **absent** (genuinely discharged, not renamed); `pan_installed` is **present** and its head constant is the REAL `pan_to_targetProof$pan_installed` (fully-qualified `dest_thy_const`); `boundScanBytes` is **present** (the concrete native code is still in the slot — the theorem carries load-bearing content, not a placeholder).
- **Ground backbone unchanged:** `boundScan_rung3_native` still `[oracles: DISK_THM]`, 31 antecedent conjuncts (the dump reads it live).

---

## 5. The end-to-end boundscan Rung-3 chain, after this lane

```
boundscan.pnk (1694 B) ─cake --pancake─▶ boundScanBytes (1188 B x64, md5-stable) ─reflect─▶ HOL
   │  Layer 2 (oracle cake_native_bootstrap)  +  boundScan_pkg_bridge (DISK_THM)   [BYTES-BRIDGE / FINISH]
   ▼
G1 : compile_prog_max x64_backend_config mc boundScanProg = (SOME(boundScanBytes,boundScanBitmaps,c'm),sm)
   │  boundScan_G1_native  [oracles: DISK_THM, cake_native_bootstrap]              [FINISH]
   ▼
Link B (pan_to_target_compile_semantics @ native bytes) + 4 program-conditions DISCHARGED   [RUNG3-NATIVE]
   ▼
boundScan_rung3_native : machine_sem mc ffi ms ⊆ … {semantics_decls s «main» boundScanProg}   (31 antecedents)
   │  runtime-install antecedent:
   │    · config-well-formedness core  : backend_config_ok / mc_conf_ok / mc_init_ok /
   │                                      ISA≠Ag32 / ffi_names shape         (THIS LANE, DISCHARGED, DISK_THM)
   │    · endianness ⇔ s.be → ¬s.be, start := «main»                        (THIS LANE, simplified/folded)
   │    · placed-image geometry + pan_installed + s-boilerplate + ¬Fail     (loader/target-config contract,
   │                                                                          needs concrete ms/s — SCOPED, §3)
   ▼
boundScan_rung3_installed : is_x64_machine_config mc ⇒ (25 antecedents) ⇒ machine_sem ⊆ … {semantics_decls}
   │  Link A: whole-`main` frame  (loop core + else-arm + loop-body frame PROVEN; scanLoop locals-frame /
   │           Dec/If threading / @load_vec-@report_vec FFI-oracle contract  OPEN)   [FINISH / LINK-A]
   ▼
[TARGET]  machine_sem … ⊆ { behaviour that reports n2w (boundScan a off len) }   (Lean spec)
```

**Distance to a fully-closed boundscan Rung-3 end-to-end (native bytes → refines the Lean/Pancake spec, via bootstrap, no in-logic EVAL):**

- **G1 (native bytes):** CLOSED as `boundScan_G1_native` (one named `cake_native_bootstrap` oracle ⇐ `cake_compiled_thm`).
- **Link B (mc ⊑ Pancake source) + 4 program-conditions:** CLOSED (`boundScan_rung3_native`, DISK_THM).
- **Install antecedent — config-well-formedness core:** CLOSED here in-logic (`boundScan_rung3_installed`, DISK_THM).
- **Install antecedent — placed-image geometry + `pan_installed` + initial-state relation:** OPEN, **scoped** to the loader/target-config contract; requires constructing a concrete x64 initial machine state `ms` with the placed image (the x64 startup machinery + the Pancake arena/globals layout) and discharging `good_init_state`/`pan_installed` against it. This is the same `installed` fact CakeML leaves as a hypothesis; there is **no worked Pancake `pan_installed`-against-concrete-`ms` example in this tree** to reuse, so it is genuine target-config engineering, not a one-lemma gap.
- **Link A (Pancake source → Lean spec word):** OPEN, per CN-RUNG3-FINISH §2.3 — loop core / else-arm identity / loop-body frame PROVEN; the `scanLoop` locals-frame (tactic friction), the `Dec`/`If` threading (mechanical), and the `@load_vec`/`@report_vec` FFI-oracle contract (irreducible research boundary) remain.

None of the residual is the in-logic-EVAL dead end; none is leanc.

---

## 6. Files

**On hbox** (`/home/hbox/hol-rung3-install/`, self-contained; no CakeML-tree file modified):
`boundScanInstallScript.sml`, `Holmakefile` (INCLUDES the CakeML pancake/backend/x64/x64-proofs dirs + `~/hol-c10` + `~/hol-boundscan-linka` + `~/hol-bytes-bridge` + `~/hol-rung3-native`), `install.out` (the build's own tag/axiom/residual-antecedent dump), `audit_install.sml` (the fresh-session tag + non-vacuity + fully-qualified-const audit), `build.log`.

**In this repo** (`docs/engine/probes/compiler/hol-rung3-install/`): the same files (`boundScanInstallScript.sml` md5 `b376884c…` == hbox), plus this report.

**Scope note:** HOL4/CakeML COMPILER-track lane. Touches no Lean spec, no `Datapath.lean`, no `libdrorb`, no Rust dataplane — there is **no** `cargo` / `build-dataplane-lib.sh` / `curl` delta. The mergeable artifact is the new HOL4 theory (`boundScanInstall`) + Holmakefile + audit + this report.

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
cd ~/hol-rung3-install
rm -f boundScanInstallTheory.* install.out
Holmake boundScanInstallTheory.uo        # [1/1] OK, ~16s
cat install.out                          # tags + 31→25 antecedent reduction + the 25 residual conjuncts
hol < audit_install.sml                  # fresh-session kernel tags + non-vacuity + fully-qualified consts
# theorem names:
#  install core : ~/hol-rung3-install/boundScanInstallScript.sml   boundScan_rung3_installed
#  backbone     : ~/hol-rung3-native   boundScan_rung3_native
#  G1 (native)  : ~/hol-rung3-finish   boundScan_G1_native
#  x64 lemmas   : compiler/backend/x64/proofs/x64_configProofScript.sml
#                 x64_backend_config_ok / x64_machine_config_ok / x64_init_ok
```

## 8. Bottom line

The runtime-install antecedent of `boundScan_rung3_native` — the last named block of its 31-conjunct antecedent — is **split and its config-well-formedness core discharged in-logic**: `boundScan_rung3_installed` (`[oracles: DISK_THM] [axioms:]`, 0 theory axioms) instantiates the backbone at the concrete x64 machine config under `is_x64_machine_config mc` and removes the five well-formedness predicates (`backend_config_ok`/`mc_conf_ok`/`mc_init_ok`/`ISA≠Ag32`/FFI-names) using the REAL `x64_configProof` lemmas — the exact predicates every CakeML x64 `compile_correct` instantiation carries — plus folds `start` and simplifies endianness to `¬s.be`, taking 31 antecedents to 25. **What remains is honestly scoped, not faked:** G1 (separately closed by `boundScan_G1_native`), the initial-state boilerplate, and the placed-image geometry + `pan_installed` — the loader/target-config contract that requires a concrete initial machine state `ms`, exactly the `installed` fact CakeML itself leaves as a hypothesis (`helloProof` `DISCH_ALL`). The end-to-end to the Lean spec still needs that placed-image discharge and the whole-`main` Link-A frame — named residuals, neither the in-logic-EVAL dead end nor leanc.

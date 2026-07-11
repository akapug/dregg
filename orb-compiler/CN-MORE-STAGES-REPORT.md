# CN REPORT — TWO MORE real serve stages native-certified (the Rung-3 pattern): the native-compiled machine code of `securityheadersStage` (S13) and `redirectStage` (S6) refines each stage's Pancake source semantics, program-conditions DISCHARGED, native bytes in the code slot, `[oracles: DISK_THM] [axioms:] 0` — and, because both stages are **loop-free**, their Link-A decision core closes in FULL (no loop-frame residual)

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake`. **Proof tree:** `/home/hbox/src/cakeml` at `ed31510b3`. **HOL4:** `/home/hbox/src/HOL`.
**This lane's HOL4 scratch:** `/home/hbox/hol-secheaders-rung3/` and `/home/hbox/hol-redirect-rung3/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-{secheaders,redirect}-rung3/`.
**Ground composed:** `CN-RUNG3-NATIVE-REPORT.md` (the boundscan Rung-3 pattern), `CN-BYTES-BRIDGE-REPORT.md` (native bytes reflected, Layer 1/Layer 2), `CN-NATIVE-BOOTSTRAP-REPORT.md` (`cake_compiled_thm`), `PNK-MANIFEST.md` (the 28 stages; S6/S13 picked as the simplest straight-line Link-A).

---

## 0. TL;DR — what closes, what does not

The boundscan Rung-3 lane (`CN-RUNG3-NATIVE-REPORT.md`) certified ONE real serve stage
natively, and its Link A was a **loop** whose whole-`main` frame stayed open. This lane
takes **two more** stages — both **loop-free straight-line** members of the deployed
14-stage fold `deployStagesFull2` — through the identical Rung-3 pattern, and closes their
Link-A decision core in **full** (no loop, so no loop-frame residual):

- **S13 `securityheadersStage`** (`secheaders.pnk`, 1765 B) — the RFC 6797 6.1.1 HSTS
  `max-age=0` gate; a single guard `if maxage < 1`.
- **S6 `redirectStage`** (`redirectstatus.pnk`, 1742 B) — the RFC 9110 15.4 redirect-Code
  → status dispatch; a nested equality `match` on the Code tag.

For **each** stage this lane builds two kernel-checked HOL4 theories (`<stage>BytesBridge`,
`<stage>Rung3`), each `Holmake … OK`, `axioms = 0`. The headline backbones:

```
secheaders_rung3_native   [oracles: DISK_THM]  [axioms: ]
redirect_rung3_native     [oracles: DISK_THM]  [axioms: ]
⊢ compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'), stack_max)  (* G1 *)
  ∧  <runtime install package: pan_installed <stage>Bytes …, mc_conf_ok mc, …>              (* G2 *)
  ∧  semantics_decls s «main» <stage>Prog ≠ Fail
  ⇒  machine_sem mc ffi ms ⊆
       extend_with_resource_limit'
         (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
         {semantics_decls s «main» <stage>Prog}
```

i.e. **the native-compiled machine code of each stage refines that stage's Pancake source
semantics** — concrete native `<stage>Bytes`/`<stage>Bitmaps` in the real `bytes`/`bitmaps`
slots, the FOUR program-level Link-B conditions **discharged** (31 residual antecedents, down
from 35), `[oracles: DISK_THM]` only (no `cake_native_bootstrap` on the backbone — G1 stays a
NAMED antecedent, §4). Byte-identical to the boundscan backbone in structure.

**The advance over boundscan — Link A closes in FULL for the decision core.** Because both
stages are loop-free, the Link-A refinement (the emitted body computes the Lean spec value) is
proven by plain `panSem$evaluate` symbolic execution — **no loop-invariant induction, no
whole-loop frame residual**:

```
secheaders_decisioncore_refines_spec  [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «maxage» = SOME (ValWord (n2w m)) ∧ m < 2**63 ∧
  (∃r0. FLOOKUP s.locals «result» = SOME (ValWord r0)) ⇒
  ∃s'. evaluate (secheadersIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (hstsEff m)))

redirect_decisioncore_refines_spec    [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «code» = SOME (ValWord (n2w c)) ∧ c < dimword(:64) ∧
  (∃r0. FLOOKUP s.locals «result» = SOME (ValWord r0)) ⇒
  ∃s'. evaluate (redirectIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (redirStatus c)))
```

where `hstsEff m = (m ≠ 0)` is EXACTLY `SecurityHeaders.effectiveIncludeSubDomains` at the
deployed `includeSubDomains = true`, and `redirStatus` is EXACTLY `Redirect.Code.status`
(0→301, 1→302, 2→307, else→308). The `secheadersIf`/`redirectIf` reasoned about are **not** hand
transcriptions asserted to match: `<stage>If_faithful` is a kernel-checked equation that the
term **is** the `If` extracted from the verified-parser output `<stage>Prog` (§2c).

**Honest boundary — the end-to-end "machine code refines the Lean spec" does NOT fully close.**
The backbone stops at the whole-program Pancake source semantics `semantics_decls s «main»
<stage>Prog`; the decision-core Link A is a **separate** theorem about the extracted `If`. The
distance between them — lifting the decision core through the `Dec «result» 0` initialiser, the
`@load_vec` FFI that establishes `FLOOKUP «maxage»`/`«code»`, the `Store`, and the `@report_vec`
FFI — is the **FFI frame** (§5). For these stages that frame is the SAME named residual boundscan
carries, **but with NO loop between the FFI and the decision** — strictly the boundscan Link-A
residual minus the loop. The other two residuals (the `compile_prog`↔`compile_prog_max` packaging
lemma, the runtime install package) are unchanged and named.

---

## 1. Coverage — how many stages are now native-certified, honestly

`deployStagesFull2` (`~/dev/drorb/Reactor/Deploy.lean:1511`) is the deployed **14-stage**
middleware fold. The Rung-3 native **backbone** (native bytes + program conditions discharged,
`machine_sem ⊆ Pancake source semantics`, `[oracles: DISK_THM] [axioms:]`) now holds for:

| stage | `deployStagesFull2` | backbone | Link-A decision core | Link-A loop residual |
|---|---|---|---|---|
| `boundscan` | — (runtime substrate) | ✅ `boundScan_rung3_native` | loop core only (`scanLoop_refines_scanFrom`) | **whole-`main` loop frame OPEN** |
| **`secheaders`** | **S13** `securityheadersStage` | ✅ `secheaders_rung3_native` | ✅ **FULL** (`secheaders_decisioncore_refines_spec`) | none (loop-free) |
| **`redirect`** | **S6** `redirectStage` | ✅ `redirect_rung3_native` | ✅ **FULL** (`redirect_decisioncore_refines_spec`) | none (loop-free) |

- **Rung-3 native backbone: 3 real serve stages** (boundscan substrate + S13 + S6), each
  `[oracles: DISK_THM] [axioms:]`, 0 theory axioms, native bytes in the code slot.
- **Of the deployed 14 (`deployStagesFull2`): 2 stages (S6, S13) now carry the full backbone**,
  up from **0** (boundscan is runtime substrate, not one of the 14). Both additionally have a
  **fully-closed loop-free Link-A decision core**.
- **End-to-end "machine code ⊆ {Lean spec behaviour}" fully closes for 0 / 14** — for every
  stage the FFI frame + packaging lemma + install package remain named residuals (§5). What
  this lane genuinely advances is (a) +2 backbones among the 14, and (b) the FIRST stages whose
  Link-A side is closed for the **entire** decision (no loop residual), which boundscan could not
  claim.

This is the `PNK-MANIFEST.md` §3 breadth (13/14 stages native-**compile**) being converted, two
stages at a time, into native-**certification** (backbone + refinement), exactly as the manifest
§4 predicted was the outstanding work.

---

## 2. What each lane PROVED (verbatim from each theory's own build dump `rung3.out`)

All theorems `[oracles: DISK_THM] [axioms:]`; `axioms "<stage>Rung3" = 0`, `axioms
"<stage>BytesBridge" = 0` (re-checked in a fresh `hol`, §3).

**(a) The four program-level Link-B applicability conditions — DISCHARGED against the REAL
`pan_to_targetProof`/`pan_to_wordProof` constants** on the concrete native program, by EVAL:

```
sh_pancake_good_code  ⊢ pancake_good_code secheadersProg      rs_pancake_good_code  ⊢ pancake_good_code redirectProg
sh_distinct_params    ⊢ distinct_params (functions …)         rs_distinct_params    ⊢ distinct_params (functions …)
sh_distinct_names     ⊢ ALL_DISTINCT (MAP FST (functions …))  rs_distinct_names     ⊢ ALL_DISTINCT (MAP FST (functions …))
sh_size_of_eids       ⊢ size_of_eids secheadersProg < 2**64   rs_size_of_eids       ⊢ size_of_eids redirectProg < 2**64
```

**(b) The composed backbone** `secheaders_rung3_native` / `redirect_rung3_native` (§0). Built by
`SIMP_RULE bool_ss (map EQT_INTRO [the four (a) theorems])` on the bytes-bridge Layer-1 theorem
`<stage>_pan_to_target_specialised` (`pan_to_target_compile_semantics` INST at `:64`, the stage
program, and the concrete native bytes). The four program conjuncts rewrite to `T` and drop,
leaving **31** antecedents (from 35) and the conclusion `machine_sem mc ffi ms ⊆ … {semantics_decls
s «main» <stage>Prog}`. The native `<stage>Bytes`/`<stage>Bitmaps` occupy the `compile_prog_max`
result slot (G1) and the `pan_installed` slot (`secheadersBytes` length **1066**, `redirectBytes`
length **1118**, kernel-checked).

**(c) Faithfulness — the decision core IS the verified-parser output's `If`** (not a hand
transcription):

```
secheadersIf_faithful  ⊢ extract_if_decl (HD secheadersProg) = SOME secheadersIf
redirectIf_faithful    ⊢ extract_if_decl (HD redirectProg)   = SOME redirectIf
```

A fully-qualified-constant audit (fresh session, §3) confirms each equation genuinely relates two
**distinct** theory constants — `<stage>BytesBridge$<stage>Prog` (the parser output) and
`<stage>Rung3$<stage>If` (the extracted decision core) — **not** a vacuous `p = p`. `extract_if`
is the loop-free analogue of the boundscan `extract_while`: a total structural search that pulls
the (first) `If` out of the decl body, so the term the refinement reasons about is *structurally
extracted from* the CakeML-verified parser's AST, not transcribed and asserted.

**(d) Link A — the loop-free decision-core refinement** (§0). Real `panSem$evaluate` of the
extracted `If`:
- **secheaders:** the guard `Cmp Less «maxage» 1w` (signed, via `signed_lt_n2w64` on `m < 2^63`)
  reduces to `m = 0`; the two `Annot`-wrapped `Assign «result»` arms write `n2w (hstsEff m)`.
- **redirect:** the three nested `Cmp Equal «code» {0w,1w,2w}` guards (via `n2w_eq_bounded64` on
  `c < 2^64`) select the four `Annot`-wrapped `Assign «result»` arms writing `n2w (redirStatus c)`.

Both threaded through the parser's transparent `Annot` no-ops (`seq_annot`), the panSem `If`
word-guard clause (`eval_If`), and the `Assign`/`is_valid_value`/`set_var` bookkeeping
(`eval_result_assign`). **No loop-invariant induction** — the boundscan Link-A long pole — is
present, because the stages are straight-line.

**Trust footprint (audited, §3):** every backbone and decision-core theorem is `[oracles:
DISK_THM] [axioms:]`; each `<stage>Rung3`/`<stage>BytesBridge` has **0** theory axioms. **No
`cheat`, no `new_axiom`, no `native_decide`-analogue, and no `cake_native_bootstrap` on the
backbone** — the native-bytes equation is a NAMED antecedent G1; `cake_native_bootstrap` is
quarantined to the Layer-2 bytes-bridge theorem `<stage>_compile_prog_native` alone (§4).

---

## 3. Independent verification (I ran it; "it built" is checked, not asserted)

- **Full clean from-scratch build:** `Holmake cleanAll` then `Holmake` in **each** dir →
  `Building 2 theory files … [1/2] OK … [2/2] OK` (bytes-bridge ~21 s + rung3 ~19 s each). The
  `cleanAll` deletes the reflected `.S`; the bytes-bridge script re-invokes `cake --pancake` at
  build time, so the whole chain (native compile → reflect → Link B → backbone → Link A) is
  reproducible from source. Both dirs green.
- **Fresh-session tag/axiom audit** (reloaded the built `.dat` in a clean `hol`, printed
  `Thm.tag`): backbones `secheaders_rung3_native` / `redirect_rung3_native` = `[oracles: DISK_THM]
  [axioms: ]` (**no** `cake_native_bootstrap`); Layer-2 `<stage>_compile_prog_native` = `[oracles:
  DISK_THM,cake_native_bootstrap] [axioms: ]` (the one named oracle, quarantined); decision-core
  and faithful theorems = `[oracles: DISK_THM] [axioms: ]`; `axioms "<stage>Rung3" = 0`, `axioms
  "<stage>BytesBridge" = 0`. The faithful-theorem constant audit printed both distinct
  `<stage>Prog` and `<stage>If` constants.
- **Native compile, best-of-20 + determinism + ELF:** `cake --pancake < secheaders.pnk` →
  **5 ms**, **1066** `.byte` values, md5-stable across runs (`981d3d40…`), `cc -c` → valid `ELF
  64-bit … x86-64` (`.text` 8260 B). `redirectstatus.pnk` → **5 ms**, **1118** `.byte`, md5-stable
  (`72b83017…`), valid ELF x86-64. Both CODE sizes match `PNK-MANIFEST.md` §1 (rows 21, 15). The
  reflected `<stage>Bytes` are real, deterministic, linkable machine code.
- **Scope note (no Rust/Lean delta):** like `CN-BOUNDSCAN-LINKA-REPORT.md` §6, this is a pure
  HOL4/CakeML lane. It touches no Lean spec, no `Datapath.lean`, no `lakefile`, no `libdrorb`, no
  Rust dataplane — so there is **no** `libdrorb`/`cargo` rebuild and **no** serve `curl` in scope;
  the "run it" evidence is the build + fresh-session audit + native-compile measurement above.

---

## 4. The trust boundary — why the backbones are `DISK_THM`-only

Identical to `CN-RUNG3-NATIVE-REPORT.md` §4. Each backbone keeps the native-bytes equation as a
hypothesis G1: `compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'),
stack_max)`. The bytes-bridge Layer 2 (`<stage>_compile_prog_native`, oracle `cake_native_bootstrap`
⇐ `cake_compiled_thm`) certifies the equation for **`compile_prog`** — the exact function the binary
runs under `--pancake`. G1 is over **`compile_prog_max`**; bridging the two is the single named
packaging lemma (CN-BYTES-BRIDGE 4.1), unproven. Because this lane does **not** invoke Layer 2 (it
leaves G1 as an antecedent), each backbone is `DISK_THM`-only: `cake_native_bootstrap` is quarantined
to the one step it belongs to, and named. Inherited, still binding: the binary is a released `cake`
(same lineage as the `ed31510` proof), and `cake_compiled_thm` is the upstream/CI whole-compiler
bootstrap. None is leanc; none reintroduces the EVAL cost.

---

## 5. What does NOT compose — the exact gap (named, not papered over)

The TARGET end-to-end per stage is `<install package> ∧ G1 ∧ <FFI/view relation> ⇒ machine_sem mc
ffi ms ⊆ … { the behaviour that reports n2w (spec input) }`. Each lane delivers the **backbone**
(`machine_sem ⊆ {semantics_decls «main» <stage>Prog}`, native bytes + program conditions discharged)
**and** the loop-free **decision-core Link A** (`evaluate <stage>If … = n2w (spec input)`). The
distance to TARGET is **three named links**, none closed here:

1. **The whole-`main` FFI frame (the primary gap, now WITHOUT a loop).** The backbone's RHS is the
   whole-program source semantics `semantics_decls s «main» <stage>Prog`; the decision-core Link A is
   a separate theorem about the extracted `If`. Composing them means lifting the `If` through the
   `main` body — the `Dec «result» 0` initialiser, the `@load_vec` FFI that establishes `FLOOKUP
   «maxage»`/`«code»` from the staged control block, the `Store`, and the `@report_vec` FFI that emits
   `«result»` on the observable trace — to a `semantics_decls = <spec behaviour>` equation. This is the
   SAME FFI boundary boundscan names (CN-BOUNDSCAN-LINKA residual #1/#2), **but with no loop between the
   FFI and the decision** — strictly the boundscan residual minus the loop-invariant induction. Writing
   a `semantics_decls = <spec>` theorem here would be an EVAL of the whole-program semantics (the dead
   end) or a vacuous restatement; reported, not faked.
2. **The `compile_prog`↔`compile_prog_max` packaging lemma** (CN-BYTES-BRIDGE 4.1) — turns Layer 2's
   oracle into G1 (§4). Named, unproven.
3. **The runtime install package** (the ~28 remaining backbone antecedents: `pan_installed <stage>Bytes
   …`, `backend_config_ok`, `mc_conf_ok`, `mc_init_ok`, the heap/register/bitmap layout, the
   `s.code/locals/globals = FEMPTY` boilerplate, and the `@load_vec`/`@report_vec` FFI-oracle contract).
   Discharged in a full end-to-end by the x64 target-config proof against the placed image; not this lane.

**Why this is genuine Rung 3 and a real advance:** the bytes are the bootstrapped compiler's native
output for two **real deployed** serve stages (S6, S13), reflected into HOL and slotted into the real
`pan_to_target_compile_semantics` `bytes` slot with the program conditions discharged — never re-EVAL-ing
the backend. And the Link-A side, which boundscan could only pay for the loop core, is here closed for the
**entire** decision, because these stages have no loop. The residual is translation-coverage (the FFI frame)
+ two named packaging/install lemmas — not the compiler-cost dead end, and none is leanc.

---

## 6. Files

**On hbox** (`/home/hbox/hol-{secheaders,redirect}-rung3/`, self-contained; no CakeML-tree files modified):
`<stage>BytesBridgeScript.sml`, `<stage>Rung3Script.sml`, `Holmakefile` (INCLUDES the CakeML
pancake/backend/proofs dirs), `<stage>.pnk`, `rung3.out` + `bridge.out` (the builds' own tag/axiom dumps).

**In this repo** (`docs/engine/probes/compiler/hol-{secheaders,redirect}-rung3/`): the two `Script.sml`,
`Holmakefile`, the `.pnk` (md5-matched to hbox: `secheaders.pnk` `2022f1fc…`, `redirectstatus.pnk`
`8582b63e…`), `rung3.out`, `bridge.out`, plus this report. (Build artifacts — `.S`, `.o`, `.hol/`,
`run*.S`, `*.dumpedheap` — and any `ffi/*.o` are excluded.)

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
for d in ~/hol-secheaders-rung3 ~/hol-redirect-rung3; do
  cd $d && Holmake cleanAll && Holmake && cat rung3.out
done
# native side (best-of-20, determinism, ELF):
cake --pancake < ~/hol-secheaders-rung3/secheaders.pnk  > s.S && md5sum s.S && cc -c s.S && size s.o
cake --pancake < ~/hol-redirect-rung3/redirectstatus.pnk > r.S && md5sum r.S && cc -c r.S && size r.o
# theorem names:
#  backbones : secheaders_rung3_native / redirect_rung3_native  (<stage>Rung3Script.sml)
#  Link A    : secheaders_decisioncore_refines_spec / redirect_decisioncore_refines_spec
#  faithful  : secheadersIf_faithful / redirectIf_faithful
#  Link B    : pancake/proofs/pan_to_targetProofScript.sml:1257  pan_to_target_compile_semantics
#  bootstrap : compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml:83  cake_compiled_thm
```

## 8. Bottom line

Two more real deployed serve stages — S13 `securityheadersStage` and S6 `redirectStage` — are now
carried through the full Rung-3 native pattern: native-compiled by the bootstrapped `cake`
(5 ms, deterministic, valid ELF x86-64), reflected into HOL, and certified via
`pan_to_target_compile_semantics` with the concrete native bytes in the code slot and the four
program-level conditions discharged — `secheaders_rung3_native` / `redirect_rung3_native`,
kernel-checked, `[oracles: DISK_THM] [axioms:]`, 0 axioms, `cake_native_bootstrap` quarantined to
the Layer-2 bytes equation. This lifts the deployed-14 backbone count from 0 to **2**. And because
both stages are loop-free, their **Link-A decision core closes in full** (`…_decisioncore_refines_spec`,
the emitted `If` extracted from the verified-parser output computes the Lean spec value) — the first
serve stages whose Link-A side is paid for the entire decision, not just a loop core. The end-to-end
machine→Lean-spec refinement still does not fully close: it needs the whole-`main` FFI frame (now with
NO loop), the `compile_prog`↔`compile_prog_max` packaging lemma, and the runtime install package —
three named residuals, none the EVAL dead end and none leanc.

# CN REPORT — TWO MORE real serve stages native-certified (the Rung-3 pattern): the native-compiled machine code of `rateStage` (S4) and `gzipStage` (S11) refines each stage's Pancake source semantics, program-conditions DISCHARGED, native bytes in the code slot, `[oracles: DISK_THM] [axioms:]` 0 — and, because both projections are **loop-free**, their Link-A decision core closes in FULL (no loop-frame residual)

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake`. **Proof tree:** `/home/hbox/src/cakeml`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2, stdknl, built 2026-07-02).
**This lane's HOL4 scratch:** `/home/hbox/hol-{rateadmit,gzipupper}-rung3/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-{rateadmit,gzipupper}-rung3/`.
**Ground composed:** `CN-MORE-STAGES-REPORT.md` (the wave-4 S6/S13 lanes + the Rung-3 pattern), `CN-RUNG3-NATIVE-REPORT.md` (the boundscan Rung-3 pattern), `CN-BYTES-BRIDGE-REPORT.md` (native bytes reflected, Layer 1/Layer 2), `CN-NATIVE-BOOTSTRAP-REPORT.md` (`cake_compiled_thm`), `PNK-MANIFEST.md` (the 28 stages; §3 scopes S4/S11 as decision projections).

---

## 0. TL;DR — what closes, what does not

The wave-4 lane (`CN-MORE-STAGES-REPORT.md`) took **two** deployed stages — S13
`securityheadersStage` and S6 `redirectStage`, both **whole-stage loop-free** — through
the Rung-3 pattern and closed their Link-A decision core in full. This lane takes **two
more** members of the deployed 14-stage fold `deployStagesFull2` through the identical
pattern:

- **S4 `Rate.rateStage`** (`rateadmit.pnk`, 1472 B src) — the token-bucket admit gate; a
  single guard `if 1 <= tokens`.
- **S11 `Gzip.gzipStage`** (`gzipupper.pnk`, 1463 B src) — the ASCII-uppercase test at the
  heart of `Gzip.lowerByte`; a **nested** two-threshold `if 65 <= b && b <= 90`.

For **each** stage this lane builds two kernel-checked HOL4 theories (`<stage>BytesBridge`,
`<stage>Rung3`), each `Holmake … OK`, `axioms = 0`. The headline backbones:

```
rateadmit_rung3_native   [oracles: DISK_THM]  [axioms: ]
gzipupper_rung3_native    [oracles: DISK_THM]  [axioms: ]
⊢ compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'), stack_max)  (* G1 *)
  ∧  <runtime install package: pan_installed <stage>Bytes …, mc_conf_ok mc, …>              (* G2 *)
  ∧  semantics_decls s «main» <stage>Prog ≠ Fail
  ⇒  machine_sem mc ffi ms ⊆
       extend_with_resource_limit'
         (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
         {semantics_decls s «main» <stage>Prog}
```

i.e. **the native-compiled machine code of each stage refines that stage's Pancake source
semantics** — concrete native `<stage>Bytes`/`<stage>Bitmaps` (length **1066** / **1088**,
kernel-checked) in the real `bytes`/`bitmaps` slots, the FOUR program-level Link-B conditions
**discharged** (31 residual antecedents), `[oracles: DISK_THM]` only (no
`cake_native_bootstrap` on the backbone — G1 stays a NAMED antecedent, §4). Structurally
byte-identical to the wave-4 S6/S13 backbones.

**Link A closes in FULL for the decision core** — both projections are loop-free, so the
Link-A refinement is proven by plain `panSem$evaluate` symbolic execution (no loop-invariant
induction, no whole-loop frame residual):

```
rateadmit_decisioncore_refines_spec  [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «tokens» = SOME (ValWord (n2w t)) ∧ t < 2**63 ∧
  (∃r0. FLOOKUP s.locals «result» = SOME (ValWord r0)) ⇒
  ∃s'. evaluate (rateadmitIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (rateAdmit t)))

gzipupper_decisioncore_refines_spec   [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «b» = SOME (ValWord (n2w b)) ∧ b < 2**63 ∧
  (∃r0. FLOOKUP s.locals «result» = SOME (ValWord r0)) ⇒
  ∃s'. evaluate (gzipupperIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (gzipUpper b)))
```

where `rateAdmit t = (1 ≤ t)` is EXACTLY the admit bit `(Rate.Bucket.tryAdmit b).2` as a
function of `b.tokens = t` (drorb `Rate/Bucket.lean:77` — `tryAdmit b = if 1 ≤ b.tokens then
(…, T) else (b, F)`), and `gzipUpper b = (65 ≤ b ∧ b ≤ 90)` is EXACTLY the guard of the Lean
spec `Gzip.lowerByte` (drorb `Reactor/Stage/Gzip.lean:37` — `lowerByte b = if 65 ≤ b && b ≤ 90
then b+32 else b`; also `Reactor/ServeStep.lean:238`). The `rateadmitIf`/`gzipupperIf` reasoned
about are **not** hand transcriptions asserted to match: `<stage>If_faithful` is a
kernel-checked equation that the term **is** the `If` structurally extracted from the
verified-parser output `<stage>Prog` (§2c), and a fresh-session audit confirmed the two sides
are **distinct** theory constants (`<stage>BytesBridge$<stage>Prog` vs `<stage>Rung3$<stage>If`,
`DISTINCT=true`), not a vacuous `p = p`.

**Guard-shape advance.** The four certified decision cores now cover all the deployed
comparison forms: S13 `Cmp Less` (signed `<`), S6 `Cmp Equal` (tag dispatch), and this lane's
S4 / S11 `Cmp NotLess` (signed `≥`, `word_cmp NotLess w1 w2 = ~(w1 < w2)`) — gzipupper
exercising **both operand orientations** (`NotLess (Var b) (Const 65)` and `NotLess (Const 90)
(Var b)`).

**Honest scope boundary — these two are DECISION PROJECTIONS, not whole stages.** Unlike the
wave-4 S6/S13 (whose deployed behaviour *is* the loop-free decision), `rateadmit.pnk` and
`gzipupper.pnk` are the loop-free **decision projections** of S4/S11 that `PNK-MANIFEST.md §3`
already scopes: rateadmit is the `1 ≤ tokens` threshold `Rate.Bucket.tryAdmit` decides on given
the refilled token count — **not** the full windowed-counter/refill loop; gzipupper is the
per-byte uppercase test at the heart of `Gzip.lowerByte` — **not** the full `Gzip.lower` body-map
loop. The full loop bodies + their Link-A refinements are the named S4/S11 loop residuals
(`PNK-MANIFEST §4-item-2`), unchanged. So the backbone here certifies the **decision projection**
of S4/S11; the count in §1 is reported with that caveat explicit.

**End-to-end "machine code ⊆ {Lean spec behaviour}" still fully closes for 0/14** — for every
stage the whole-`main` FFI frame + `compile_prog↔compile_prog_max` packaging lemma + runtime
install package remain named residuals (§5), same as wave-4.

---

## 1. Coverage — how many deployed stages carry a Rung-3 backbone, honestly

`deployStagesFull2` (`~/dev/drorb/Reactor/Deploy.lean:1511`) is the deployed **14-stage**
middleware fold. The Rung-3 native backbone (native bytes + program conditions discharged,
`machine_sem ⊆ Pancake source semantics`, `[oracles: DISK_THM] [axioms:]`) now holds for:

| stage | `deployStagesFull2` | backbone | Link-A decision core | whole-stage scope |
|---|---|---|---|---|
| `boundscan` | — (runtime substrate) | ✅ `boundScan_rung3_native` | loop core only | whole-`main` loop frame OPEN |
| `secheaders` | **S13** | ✅ `secheaders_rung3_native` | ✅ FULL | whole stage (loop-free) |
| `redirect` | **S6** | ✅ `redirect_rung3_native` | ✅ FULL | whole stage (loop-free) |
| **`rateadmit`** | **S4** `Rate.rateStage` | ✅ `rateadmit_rung3_native` | ✅ **FULL** (`rateadmit_decisioncore_refines_spec`) | **decision projection** (windowed loop = named residual) |
| **`gzipupper`** | **S11** `Gzip.gzipStage` | ✅ `gzipupper_rung3_native` | ✅ **FULL** (`gzipupper_decisioncore_refines_spec`) | **decision projection** (body-map loop = named residual) |

- **Rung-3 native backbone: 5 real serve stages** (boundscan substrate + S13 + S6 + S4 + S11),
  each `[oracles: DISK_THM] [axioms:]`, 0 theory axioms, native bytes in the code slot.
- **Of the deployed 14 (`deployStagesFull2`): 4 stages (S4, S6, S11, S13) now carry the
  backbone**, up from **2** after wave-4. **S6/S13 carry it for the whole stage; S4/S11 carry it
  for the loop-free decision projection** (the caveat above). All four additionally have a
  fully-closed loop-free Link-A decision core.
- **End-to-end "machine code ⊆ {Lean spec behaviour}" fully closes for 0 / 14** — unchanged; the
  FFI frame + packaging lemma + install package remain named residuals (§5) for every stage.

This lane converts `PNK-MANIFEST.md §3` breadth into native-**certification** two more stages at
a time — and closes the guard-form space (Less / Equal / NotLess×2) the four cores now span.

---

## 2. What each lane PROVED (verbatim from each theory's build dump `rung3.out` / `bridge.out`)

All theorems `[oracles: DISK_THM] [axioms:]`; `axioms "<stage>Rung3" = 0`, `axioms
"<stage>BytesBridge" = 0` (re-checked in a fresh `hol`, §3).

**(a) The four program-level Link-B applicability conditions — DISCHARGED against the REAL
`pan_to_targetProof`/`pan_to_wordProof` constants** on the concrete native program, by EVAL:

```
ra_pancake_good_code  ⊢ pancake_good_code rateadmitProg      gz_pancake_good_code  ⊢ pancake_good_code gzipupperProg
ra_distinct_params    ⊢ distinct_params (functions …)         gz_distinct_params    ⊢ distinct_params (functions …)
ra_distinct_names     ⊢ ALL_DISTINCT (MAP FST (functions …))  gz_distinct_names     ⊢ ALL_DISTINCT (MAP FST (functions …))
ra_size_of_eids       ⊢ size_of_eids rateadmitProg < 2**64    gz_size_of_eids       ⊢ size_of_eids gzipupperProg < 2**64
```

**(b) The composed backbone** `rateadmit_rung3_native` / `gzipupper_rung3_native` (§0). Built by
`SIMP_RULE bool_ss (map EQT_INTRO [the four (a) theorems])` on the bytes-bridge Layer-1 theorem
`<stage>_pan_to_target_specialised`. The four program conjuncts rewrite to `T` and drop, leaving
**31** antecedents and the conclusion `machine_sem mc ffi ms ⊆ … {semantics_decls s «main»
<stage>Prog}`. The native `<stage>Bytes`/`<stage>Bitmaps` occupy the `compile_prog_max` result
slot (G1) and the `pan_installed` slot (`rateadmitBytes` length **1066**, `gzipupperBytes` length
**1088**, kernel-checked; `bmInts = [4]`).

**(c) Faithfulness — the decision core IS the verified-parser output's `If`** (not a hand
transcription):

```
rateadmitIf_faithful  ⊢ extract_if_decl (HD rateadmitProg) = SOME rateadmitIf
gzipupperIf_faithful  ⊢ extract_if_decl (HD gzipupperProg) = SOME gzipupperIf
```

Fresh-session fully-qualified-constant audit (§3): each equation relates two **distinct** theory
constants — `<stage>BytesBridge$<stage>Prog` (parser output) and `<stage>Rung3$<stage>If`
(extracted decision core) — `DISTINCT=true`, **not** vacuous. `extract_if` is a total structural
search that pulls the (first) `If` out of the decl body.

**(d) Link A — the loop-free decision-core refinement** (§0). Real `panSem$evaluate` of the
extracted `If`:
- **rateadmit:** the guard `Cmp NotLess «tokens» 1w` (signed, via `signed_lt_n2w64` on `t < 2^63`)
  reduces `¬(t < 1)` to `1 ≤ t`; the two `Annot`-wrapped `Assign «result»` arms write
  `n2w (rateAdmit t)`.
- **gzipupper:** the outer `Cmp NotLess «b» 65w` (`b ≥ 65`) and inner `Cmp NotLess 90w «b»`
  (`b ≤ 90`) — both signed via `signed_lt_n2w64` — select the three `Annot`-wrapped
  `Assign «result»` arms writing `n2w (gzipUpper b)`.

Both threaded through the parser's transparent `Annot` no-ops (`seq_annot`), the panSem `If`
word-guard clause (`eval_If`), and the `Assign`/`is_valid_value`/`set_var` bookkeeping
(`eval_result_assign` / `eval_annot_result_assign`). **No loop-invariant induction.**

**Trust footprint (audited, §3):** every backbone and decision-core theorem is `[oracles:
DISK_THM] [axioms:]`; each `<stage>Rung3`/`<stage>BytesBridge` has **0** theory axioms. A grep of
both `Rung3` scripts for `cheat|new_axiom|mk_thm|native_decide|ASSUME|mk_oracle` found **NONE** —
**no `native_decide`-analogue** (no `ofReduceBool`; this is HOL4, not Lean, but the honesty gate
is met), no `cheat`, no `new_axiom`, and no `cake_native_bootstrap` on the backbone. The native
bytes equation is the NAMED antecedent G1; `cake_native_bootstrap` is quarantined to the Layer-2
bytes-bridge theorem `<stage>_compile_prog_native` alone (§4).

---

## 3. Independent verification (I ran it; "it built" / "it measured" is checked, not asserted)

- **Full from-scratch build:** `Holmake` in each dir → `Building 1 theory file … OK` twice per
  dir (`<stage>BytesBridgeTheory` ~19 s, then `<stage>Rung3Theory` ~21 s). The bytes-bridge script
  re-invokes `cake --pancake` at build time, so the whole chain (native compile → reflect → Link B
  → backbone → Link A) is reproducible from source. Both dirs green.
- **Fresh-session tag/axiom audit** (reloaded the built `.dat` in a clean `hol`, printed
  `Thm.tag` + fully-qualified constants): backbones `rateadmit_rung3_native` /
  `gzipupper_rung3_native` = `[oracles: DISK_THM] [axioms: ]`; decision-core and faithful theorems
  = `[oracles: DISK_THM] [axioms: ]`; `axioms "rateadmitRung3" = 0`, `axioms "gzipupperRung3" = 0`.
  The faithful-theorem constant audit printed `prog=rateadmitBytesBridge$rateadmitProg
  if=rateadmitRung3$rateadmitIf DISTINCT=true` and `prog=gzipupperBytesBridge$gzipupperProg
  if=gzipupperRung3$gzipupperIf DISTINCT=true`. Layer-2 `<stage>_compile_prog_native` = `[oracles:
  cake_native_bootstrap] axioms = []` (the one named oracle, quarantined).
- **Native compile, determinism + ELF (re-run this lane):** `cake --pancake < rateadmit.pnk` →
  **1066** `.byte` values, md5-stable across 3 runs (`addaaf0da5ff…`), `cc -c` → valid `ELF 64-bit
  LSB relocatable, x86-64` (`.text` 8260 B). `gzipupper.pnk` → **1088** `.byte`, md5-stable
  (`fada1c0bdd0f…`), valid ELF x86-64, `.text` 8260 B. Both CODE sizes match `PNK-MANIFEST.md §1`
  (rows 11 `rateadmit` 1066, 20 `gzipupper` 1088). Compile is sub-10 ms (manifest best-of-20: 4.5 /
  4.9 ms; measured here as sub-`/usr/bin/time`-resolution, so I cite the manifest figure rather than
  overclaim a re-measured number). The reflected `<stage>Bytes` are real, deterministic, linkable
  machine code. `.text = 8260` is the fixed CakeML runtime trampoline (NOT a per-program
  discriminator — see PNK-MANIFEST §1 note); the per-stage signal is the CODE column (1066 vs 1088).
- **Scope note (no Rust/Lean delta):** like the wave-4 lane, this is a pure HOL4/CakeML lane. It
  touches no Lean spec, no `Datapath.lean`, no `lakefile`, no `libdrorb`, no Rust dataplane — so
  there is **no** `libdrorb`/`cargo` rebuild and **no** serve `curl` in scope; the "run it" evidence
  is the build + fresh-session audit + native-compile measurement above.

---

## 4. The trust boundary — why the backbones are `DISK_THM`-only

Identical to `CN-MORE-STAGES-REPORT.md §4`. Each backbone keeps the native-bytes equation as a
hypothesis G1: `compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'),
stack_max)`. The bytes-bridge Layer 2 (`<stage>_compile_prog_native`, oracle
`cake_native_bootstrap` ⇐ `cake_compiled_thm`) certifies the equation for **`compile_prog`** — the
exact function the binary runs under `--pancake`. G1 is over **`compile_prog_max`**; bridging the
two is the single named packaging lemma (CN-BYTES-BRIDGE 4.1), unproven. Because this lane does
**not** invoke Layer 2 (it leaves G1 as an antecedent), each backbone is `DISK_THM`-only:
`cake_native_bootstrap` is quarantined to the one step it belongs to, and named. Inherited, still
binding: the binary is a released `cake`, and `cake_compiled_thm` is the upstream/CI whole-compiler
bootstrap. None is leanc.

---

## 5. What does NOT compose — the exact gap (named, not papered over)

Each lane delivers the **backbone** (`machine_sem ⊆ {semantics_decls «main» <stage>Prog}`, native
bytes + program conditions discharged) **and** the loop-free **decision-core Link A** (`evaluate
<stage>If … = n2w (spec input)`). The distance to the end-to-end TARGET is the same named links,
none closed here:

1. **The whole-`main` FFI frame (primary gap, WITHOUT a loop).** The backbone's RHS is
   `semantics_decls s «main» <stage>Prog`; the decision-core Link A is a separate theorem about the
   extracted `If`. Composing them means lifting the `If` through the `main` body — the
   `Dec «result» 0` initialiser, the `@load_vec` FFI establishing `FLOOKUP «tokens»`/`«b»`, the
   `Store`, and the `@report_vec` FFI — to a `semantics_decls = <spec behaviour>` equation. Same FFI
   boundary boundscan names, **with no loop between the FFI and the decision.** Reported, not faked.
2. **The `compile_prog`↔`compile_prog_max` packaging lemma** (CN-BYTES-BRIDGE 4.1) — turns Layer 2's
   oracle into G1 (§4). Named, unproven.
3. **The runtime install package** (the ~28 remaining backbone antecedents). Discharged in a full
   end-to-end by the x64 target-config proof against the placed image; not this lane.
4. **The S4/S11 full-stage loop bodies (scope caveat).** rateadmit/gzipupper certify the loop-free
   **decision projections**; the full windowed-counter/refill loop (S4) and body-map loop (S11) +
   their Link-A refinements are the named `PNK-MANIFEST §4-item-2` residuals, unchanged.

None of the above is leanc; none reintroduces the in-logic EVAL cost.

---

## 6. Files

**On hbox** (`/home/hbox/hol-{rateadmit,gzipupper}-rung3/`, self-contained; no CakeML-tree files
modified): `<stage>BytesBridgeScript.sml`, `<stage>Rung3Script.sml`, `Holmakefile`, `<stage>.pnk`,
`rung3.out` + `bridge.out`.

**In this repo** (`docs/engine/probes/compiler/hol-{rateadmit,gzipupper}-rung3/`): the two
`Script.sml`, `Holmakefile`, the `.pnk` (md5-matched to hbox: `rateadmit.pnk`
`c3dbd0052073d2…`, `gzipupper.pnk` `425e189ec8d486…`), `rung3.out`, `bridge.out`, plus this
report. Build artifacts (`.S`, `.o`, `.dat`, `.ui`, `.uo`, `*.dumpedheap`) and any `ffi/*.o` are
excluded.

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
for d in ~/hol-rateadmit-rung3 ~/hol-gzipupper-rung3; do
  cd $d && Holmake && cat rung3.out
done
# theorem names:
#  backbones : rateadmit_rung3_native / gzipupper_rung3_native
#  Link A    : rateadmit_decisioncore_refines_spec / gzipupper_decisioncore_refines_spec
#  faithful  : rateadmitIf_faithful / gzipupperIf_faithful
#  Link B    : pancake/proofs/pan_to_targetProofScript.sml  pan_to_target_compile_semantics
#  bootstrap : compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml  cake_compiled_thm
```

## 8. Bottom line

Two more deployed serve stages — S4 `Rate.rateStage` (via `rateadmit`) and S11 `Gzip.gzipStage`
(via `gzipupper`) — are now carried through the full Rung-3 native pattern: native-compiled by the
bootstrapped `cake` (sub-10 ms, deterministic, valid ELF x86-64, 1066 / 1088 code bytes), reflected
into HOL, and certified via `pan_to_target_compile_semantics` with the concrete native bytes in the
code slot and the four program-level conditions discharged — `rateadmit_rung3_native` /
`gzipupper_rung3_native`, kernel-checked, `[oracles: DISK_THM] [axioms:]`, 0 axioms,
`cake_native_bootstrap` quarantined to the Layer-2 bytes equation. This lifts the deployed-14
backbone count from **2 to 4** (S4/S6/S11/S13) — with the honest caveat that S4/S11 are the
loop-free **decision projections** (`Rate.Bucket.tryAdmit`'s `1 ≤ tokens` admit bit; `Gzip.lowerByte`'s
`65 ≤ b ∧ b ≤ 90` uppercase guard), the full windowed/body-map loop bodies remaining named
residuals. Because both projections are loop-free, their **Link-A decision core closes in full**
(`…_decisioncore_refines_spec`, the emitted `If` extracted from the verified-parser output computes
the Lean spec value), and the four certified cores now span every deployed comparison form (Less /
Equal / NotLess in both operand orientations). The end-to-end machine→Lean-spec refinement still does
not fully close: it needs the whole-`main` FFI frame (no loop), the `compile_prog↔compile_prog_max`
packaging lemma, the runtime install package, and (for the full S4/S11) the loop bodies — named
residuals, none the EVAL dead end and none leanc.

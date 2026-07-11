# CN REPORT — TWO MORE real serve stages native-certified (the Rung-3 pattern): the native-compiled machine code of `IpFilter.ipfilterStage`'s admit/deny gate (S3, `ipf`) and `traversalStage`'s `..`-escape gate (S7, `traversal`) refines each stage's Pancake source semantics, program-conditions DISCHARGED, native bytes in the code slot, `[oracles: DISK_THM] [axioms:]` 0 — and each stage's loop-free Link-A decision core closes in FULL. This lifts the deployed-14 backbone count from **6 to 8**.

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake` (CakeML `ccfc23c`, x64 bootstrap). **Proof tree:** `/home/hbox/src/cakeml`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2, stdknl, built 2026-07-02).
**This lane's HOL4 scratch:** `/home/hbox/hol-{ipf,traversal}-rung3/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-{ipf,traversal}-rung3/`.
**Ground composed:** `CN-MORE-STAGES-{,2,3}-REPORT.md` (the wave-4 → S5/S10 lanes + the Rung-3 pattern), `CN-RUNG3-NATIVE-REPORT.md` (boundscan Rung-3), `CN-BYTES-BRIDGE-REPORT.md` (Layer 1 / Layer 2), `CN-NATIVE-BOOTSTRAP-REPORT.md` (`cake_compiled_thm`), `PNK-MANIFEST.md` (28 stages; S3/S7 picked as the next two deployed decision projections not yet certified).

---

## 0. TL;DR — what closes, what does not

The three predecessor lanes took **six** deployed stages — S13 `securityheadersStage`, S6
`redirectStage`, S4 `Rate.rateStage`, S11 `Gzip.gzipStage`, S5 `cacheEmptyStage`'s freshness gate,
S10 `deployCorsStage` — through the Rung-3 pattern and closed each one's loop-free Link-A decision
core in full. This lane takes **two more** members of the deployed 14-stage fold `deployStagesFull2`
through the identical pattern:

- **S3 `IpFilter.ipfilterStage` admit/deny gate** (`ipf.pnk`, 3401 B src) — the CIDR admission
  decision `deployAdmits a = IpFilter.permits deployRuleset a` for the deployed single-deny-rule
  ruleset (`{ rules := [(denyCidr, Action.deny)], defaultDeny := false }`, `denyCidr = 10.0.0.0/8`);
  a single ordered guard `if acc = 9` over the prefix-matcher fold output (`acc = 9` ≡ the deny
  prefix fully matched).
- **S7 `traversalStage` `..`-escape gate** (`traversal.pnk`, 2219 B src) — the path-traversal
  decision `targetEscapes req = escapesSegs (rawSegsOf req)` (`escapesSegs = (decodeSegs segs).contains
  ".."`); a **nested** gate `if acc = 4 { … } else { if acc = 2 { … } }` over the escape-detector
  fold output.

For **each** stage this lane builds two kernel-checked HOL4 theories (`<stage>BytesBridge`,
`<stage>Rung3`), each `Holmake … OK`, `axioms = 0`. The headline backbones (verbatim from each
theory's own build dump `rung3.out`):

```
ipf_rung3_native        [oracles: DISK_THM]  [axioms: ]
traversal_rung3_native  [oracles: DISK_THM]  [axioms: ]
⊢ compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'), stack_max)  (* G1 *)
  ∧  <runtime install package: pan_installed <stage>Bytes …, mc_conf_ok mc, …>              (* G2 *)
  ∧  semantics_decls s «main» <stage>Prog ≠ Fail
  ⇒  machine_sem mc ffi ms ⊆
       extend_with_resource_limit'
         (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
         {semantics_decls s «main» <stage>Prog}
```

i.e. **the native-compiled machine code of each stage refines that stage's Pancake source
semantics** — concrete native `<stage>Bytes`/`<stage>Bitmaps` (code length **1590** / **1306**
bytes, `bmInts = [4]`, kernel-checked) in the real `bytes`/`bitmaps` slots, the FOUR program-level
Link-B conditions **discharged** (31 residual antecedents), `[oracles: DISK_THM]` only (no
`cake_native_bootstrap` on the backbone — G1 stays a NAMED antecedent, §4). Structurally
byte-identical to the S5/S10 (cachefresh/cors) backbones.

**Link A closes in FULL for each decision core** — both projections are loop-free, so the Link-A
refinement is proven by plain `panSem$evaluate` symbolic execution (no loop-invariant induction, no
whole-loop frame residual):

```
ipf_decisioncore_refines_spec        [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «acc» = SOME (ValWord (n2w acc)) ∧ acc < dimword(:64) ∧
  (∃d0. FLOOKUP s.locals «dec» = SOME (ValWord d0)) ⇒
  ∃s'. evaluate (ipfIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (ipfAdmit acc)))

traversal_decisioncore_refines_spec  [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «acc» = SOME (ValWord (n2w acc)) ∧ acc < dimword(:64) ∧
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ⇒
  ∃s'. evaluate (traversalIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (travBlock acc)))
```

where `ipfAdmit acc = (if acc = 9 then 0 else 1)` is EXACTLY `WireIpFilter.deployAdmits`
(= `IpFilter.permits deployRuleset`) as a function of the prefix-matcher fold output — the
deny-precedence access decision for the single-deny-rule deploy: admit (`1`) unless the
`10.0.0.0/8` deny prefix fully matched (`acc = 9`, blocked `0`) — and `travBlock acc = (if acc = 4
then 1 else if acc = 2 then 1 else 0)` is EXACTLY `escapesSegs`' `".."`-contains as a function of the
escape-detector fold output — blocked (`1`) iff an internal `..` segment was closed (`acc = 4`) or a
trailing bare `..` segment remains (`acc = 2`), else allowed (`0`) (drorb `Reactor/Stage/IpFilter.lean`
lines 78–83, `Reactor/Deploy.lean` lines 743–764; positions S3 and S7 of `deployStagesFull2`,
`Reactor/Deploy.lean:1511`). The `ipfIf`/`traversalIf` reasoned about are **not** hand transcriptions
asserted to match: `<stage>If_faithful` is a kernel-checked equation that the term **is** the `If`
structurally extracted from the verified-parser output `<stage>Prog` (§2c), and a fresh-session audit
confirmed the two sides are **distinct** theory constants (`ipfBytesBridge$ipfProg` vs `ipfRung3$ipfIf`;
`traversalBytesBridge$traversalProg` vs `traversalRung3$traversalIf`; `DISTINCT=true`), not a vacuous
`p = p`.

**Guard-shape coverage.** ipf adds a second `Cmp Equal`-against-constant single gate (like S6
redirect, both arms assign), on real deployed CIDR-admission serve code. traversal adds a **nested
`Cmp Equal`/`Cmp Equal`** gate with a **`Skip` fall-through** (the `acc ≠ 4 ∧ acc ≠ 2` arm leaves
`«dec»` at its `0` initialiser) — the same `Skip`-fall-through structure S10 cors introduced, here
over two equality-against-constant guards.

**Honest scope boundary — both are DECISION PROJECTIONS** (like S4/S10/S11). Each `.pnk` runs one
bounded fold loop (ipf: the 9-byte prefix matcher over the encoded address; traversal: the 5-state
escape detector over the decoded path bytes) and then the loop-free gate; this lane certifies the
**loop-free gate `If`** over the fold output `{acc}`. The fold body + its Link-A refinement is the
named S3 / S7 loop residual (the same residual class as C22/C23/rateadmit/cors). So the backbone here
certifies each stage's whole-`main` Pancake source refinement + the loop-free decision gate; the fold
loops are out of scope and named (§5).

**End-to-end "machine code ⊆ {Lean spec behaviour}" still fully closes for 0/14** — for every stage
the whole-`main` FFI frame + `compile_prog↔compile_prog_max` packaging lemma + runtime install
package remain named residuals (§5), same as the prior lanes.

---

## 1. Coverage — how many deployed stages carry a Rung-3 backbone, honestly

`deployStagesFull2` (`~/dev/drorb/Reactor/Deploy.lean:1511`) is the deployed **14-stage** middleware
fold (verified ordering re-read this lane, §3). The Rung-3 native backbone (native bytes + program
conditions discharged, `machine_sem ⊆ Pancake source semantics`, `[oracles: DISK_THM] [axioms:]`)
now holds for:

| stage | `deployStagesFull2` | backbone | Link-A decision core | whole-stage scope |
|---|---|---|---|---|
| `boundscan` | — (runtime substrate) | ✅ `boundScan_rung3_native` | loop core only | whole-`main` loop frame OPEN |
| `secheaders` | **S13** | ✅ `secheaders_rung3_native` | ✅ FULL (`Cmp Less`) | whole stage (loop-free) |
| `redirect` | **S6** | ✅ `redirect_rung3_native` | ✅ FULL (`Cmp Equal`) | whole stage (loop-free) |
| `rateadmit` | **S4** | ✅ `rateadmit_rung3_native` | ✅ FULL (`Cmp NotLess`) | decision projection (windowed loop = residual) |
| `gzipupper` | **S11** | ✅ `gzipupper_rung3_native` | ✅ FULL (`Cmp NotLess` ×2 orient.) | decision projection (body-map loop = residual) |
| `cachefresh` | **S5** `cacheEmptyStage` | ✅ `cachefresh_rung3_native` | ✅ FULL (`Cmp Less`, `isFresh`) | freshness decision (loop-free); S5 key/digest folds = residual |
| `cors` | **S10** `deployCorsStage` | ✅ `cors_rung3_native` | ✅ FULL (`Cmp NotEqual` + `Cmp Equal`) | decision projection (2 hashBytes folds = residual) |
| **`ipf`** | **S3** `IpFilter.ipfilterStage` | ✅ `ipf_rung3_native` | ✅ **FULL** (`Cmp Equal`, `deployAdmits`) | **decision projection** (prefix-matcher fold = residual) |
| **`traversal`** | **S7** `traversalStage` | ✅ `traversal_rung3_native` | ✅ **FULL** (nested `Cmp Equal`×2 + `Skip`, `escapesSegs`) | **decision projection** (escape-detector fold = residual) |

- **Rung-3 native backbone: 9 real serve stages** (boundscan substrate + S13 + S6 + S4 + S11 + S5 +
  S10 + **S3** + **S7**), each `[oracles: DISK_THM] [axioms:]`, 0 theory axioms, native bytes in the
  code slot.
- **Of the deployed 14 (`deployStagesFull2`): 8 stages (S3, S4, S5, S6, S7, S10, S11, S13) now carry
  the backbone**, up from **6** after the previous lane. S5/S6/S13 carry it for a whole loop-free
  decision; S3/S4/S7/S10/S11 carry it for a loop-free decision projection (the caveats in §0). All
  eight additionally have a fully-closed loop-free Link-A decision core.
- **End-to-end "machine code ⊆ {Lean spec behaviour}" fully closes for 0 / 14** — unchanged; the FFI
  frame + packaging lemma + install package remain named residuals (§5) for every stage.

**Cumulative vs 14:** **8 / 14** deployed stages carry a Rung-3 native backbone (was 6/14). The
certified guard forms span `Less` / `Equal` (const & var / single & nested) / `NotLess` (both
orientations) / `NotEqual`, plus the `Skip` fall-through — the full set of comparison forms the
deployed decisions use.

---

## 2. What each lane PROVED (verbatim from each theory's build dump `rung3.out` / `bridge.out`)

All theorems `[oracles: DISK_THM] [axioms:]`; `axioms "<stage>Rung3" = 0`, `axioms
"<stage>BytesBridge" = 0` (re-checked in a fresh `hol`, §3).

**(a) The four program-level Link-B applicability conditions — DISCHARGED against the REAL
`pan_to_targetProof`/`pan_to_wordProof` constants** on the concrete native program, by EVAL:

```
ip_pancake_good_code ⊢ pancake_good_code ipfProg        tr_pancake_good_code ⊢ pancake_good_code traversalProg
ip_distinct_params   ⊢ distinct_params (functions …)     tr_distinct_params   ⊢ distinct_params (functions …)
ip_distinct_names    ⊢ ALL_DISTINCT (MAP FST (functions …))  tr_distinct_names ⊢ ALL_DISTINCT (MAP FST (functions …))
ip_size_of_eids      ⊢ size_of_eids ipfProg < 2**64      tr_size_of_eids      ⊢ size_of_eids traversalProg < 2**64
```

**(b) The composed backbone** `ipf_rung3_native` / `traversal_rung3_native` (§0). Built by
`SIMP_RULE bool_ss (map EQT_INTRO [the four (a) theorems])` on the bytes-bridge Layer-1 theorem
`<stage>_pan_to_target_specialised`. The four program conjuncts rewrite to `T` and drop, leaving
**31** antecedents and the conclusion `machine_sem mc ffi ms ⊆ … {semantics_decls s «main»
<stage>Prog}`. The native `<stage>Bytes`/`<stage>Bitmaps` occupy the `compile_prog_max` result slot
(G1) and the `pan_installed` slot (`ipfBytes` length **1590**, `traversalBytes` length **1306**,
kernel-checked; `bmInts = [4]`). Fresh-session audit: `backbone concl-mentions-<stage>Prog = true`,
`backbone ante-mentions-<stage>Bytes = true`, `antecedent-conjuncts = 31`.

**(c) Faithfulness — the decision core IS the verified-parser output's `If`** (not a hand
transcription):

```
ipfIf_faithful        ⊢ extract_if_decl (HD ipfProg)       = SOME ipfIf
traversalIf_faithful  ⊢ extract_if_decl (HD traversalProg) = SOME traversalIf
```

Fresh-session fully-qualified-constant audit (§3): each equation relates two **distinct** theory
constants — `prog=ipfBytesBridge$ipfProg if=ipfRung3$ipfIf DISTINCT=true` and
`prog=traversalBytesBridge$traversalProg if=traversalRung3$traversalIf DISTINCT=true` — **not**
vacuous. `extract_if` is a total structural search that pulls the (first) `If` out of the decl body;
it walks past the `While` fold body (the `_ ⇒ NONE` clause) and returns the gate `If`.

**(d) Link A — the loop-free decision-core refinement** (§0). Real `panSem$evaluate` of the extracted
`If`:
- **ipf:** the guard `Cmp Equal «acc» 9w` — via `n2w_eq_bounded64` (n2w injective on the machine
  range) reduces `(n2w acc = 9w)` to `(acc = 9)` — selects the two `Annot`-wrapped `Assign «dec»`
  arms (`dec := 0` on the deny match, `dec := 1` on admit), so the emitted gate writes
  `n2w (ipfAdmit acc)`.
- **traversal:** the outer `Cmp Equal «acc» 4w` and inner `Cmp Equal «acc» 2w` (both via
  `n2w_eq_bounded64`) select the two `Annot`-wrapped `Assign «dec» 1w` arms, with the `acc ≠ 4 ∧
  acc ≠ 2` fall-through `Annot`-wrapped `Skip` leaving `«dec»` at its `0` initialiser, so the emitted
  gate writes `n2w (travBlock acc)`.

Both threaded through the parser's transparent `Annot` no-ops (`seq_annot`), the panSem `If`
word-guard clause (`eval_If`), and the `Assign`/`is_valid_value`/`set_var` bookkeeping. **No
loop-invariant induction.**

**Trust footprint (audited, §3):** every backbone and decision-core theorem is `[oracles: DISK_THM]
[axioms:]`; each `<stage>Rung3`/`<stage>BytesBridge` has **0** theory axioms. A grep of both `Rung3`
scripts for `cheat|new_axiom|mk_thm|native_decide|ofReduceBool|ASSUME|mk_oracle` found **NONE** — no
`native_decide`-analogue (no `ofReduceBool`; this is HOL4, but the honesty gate is met), no `cheat`,
no `new_axiom`, and no `cake_native_bootstrap` on the backbone. The native bytes equation is the
NAMED antecedent G1; `cake_native_bootstrap` is quarantined to the Layer-2 bytes-bridge theorem
`<stage>_compile_prog_native` alone (one `mk_oracle_thm` per BytesBridge, grep-confirmed, §4). (The
traversal `Skip` fall-through rewrite is pulled directly from `panSem$evaluate_def` clause 1, not
re-stated — a standalone `Skip` is overloaded across wordLang/stackLang/panLang, all in scope via the
`pan_to_target` opens; the def clause fixes it to `panLang$Skip` under `panSem$evaluate`
unambiguously.)

---

## 3. Independent verification (I ran it; "it built" / "it measured" is checked, not asserted)

- **Full from-scratch build:** `Holmake` in each dir (fresh dir, no prebuilt lane oleans present) →
  `Building 1 theory file … OK` for the bytes-bridge (24 s each) then the Rung3 (ipf 19 s, traversal
  18 s). The bytes-bridge script re-invokes `cake --pancake` at build time, so the whole chain (native
  compile → reflect → Link B → backbone → Link A) is reproducible from source. The prebuilt CakeML
  `.dat` are reused; no CakeML-tree file modified. Both dirs green. **NB — the new oleans
  (`ipf*Theory.dat`, `traversal*Theory.dat`) were absent on hbox until this lane built them; I
  verified GREEN myself before claiming (build dumps above).**
- **Fresh-session tag/axiom audit** (reloaded the built `.dat` in a clean `hol`, printed `Thm.tag` +
  fully-qualified constants, `audit.sml`): backbones `ipf_rung3_native` / `traversal_rung3_native` =
  `[oracles: DISK_THM] [axioms: ]`; decision-core and faithful theorems = `[oracles: DISK_THM]
  [axioms: ]`; `axioms "ipfRung3" = 0`, `axioms "traversalRung3" = 0`, both BytesBridge = 0. The
  faithful-theorem constant audit printed `prog=ipfBytesBridge$ipfProg if=ipfRung3$ipfIf
  DISTINCT=true` and `prog=traversalBytesBridge$traversalProg if=traversalRung3$traversalIf
  DISTINCT=true`. Backbone antecedent-conjuncts = 31, conclusion mentions `<stage>Prog`, antecedent
  mentions the native `<stage>Bytes`. Layer-2 `<stage>_compile_prog_native` = `[oracles:
  DISK_THM,cake_native_bootstrap] [axioms: ]` (the one named oracle, quarantined).
- **Native compile, determinism + ELF (re-run this lane):** `cake --pancake < ipf.pnk` → **1590**
  `.byte` values, md5-stable across 3 runs (`d11d3ffa…`), `cc -c` → valid `ELF 64-bit LSB
  relocatable, x86-64`. `traversal.pnk` → **1306** `.byte`, md5-stable (`d2962cb6…`), valid ELF
  x86-64. Both CODE sizes match `PNK-MANIFEST.md §1` (row 10 `ipf` 1590, row 16 `traversal` 1306).
  `.pnk` md5s: `ipf.pnk` `e37696e5…`, `traversal.pnk` `fa88d77e…` (repo copies md5-identical to hbox).
- **Lean-spec correspondence grounded (read, not invented):** the spec functions are drorb constants,
  read this lane — `deployRuleset := { rules := [(denyCidr, Action.deny)], defaultDeny := false }`,
  `deployAdmits a := IpFilter.permits deployRuleset a` (`Reactor/Stage/IpFilter.lean:78–83`);
  `escapesSegs`, `targetEscapes req := escapesSegs (rawSegsOf req)` (`Reactor/Deploy.lean:743–764`);
  `deployStagesFull2` orders `IpFilter.ipfilterStage` at position 3 and `traversalStage` at position 7
  (`Reactor/Deploy.lean:1511`). `ipfAdmit`/`travBlock` re-declare these as functions of the fold
  output.
- **Scope note (no Rust/Lean delta):** like the prior lanes, this is a pure HOL4/CakeML lane. It
  touches no Lean spec, no `Datapath.lean`, no `lakefile`, no `libdrorb`, no Rust dataplane — so there
  is **no** `libdrorb`/`cargo` rebuild and **no** serve `curl` in scope; the "run it" evidence is the
  build + fresh-session audit + native-compile measurement above (identical scope posture to
  `CN-MORE-STAGES-3-REPORT.md §3`).

---

## 4. The trust boundary — why the backbones are `DISK_THM`-only

Identical to `CN-MORE-STAGES-3-REPORT.md §4`. Each backbone keeps the native-bytes equation as a
hypothesis G1: `compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'),
stack_max)`. The bytes-bridge Layer 2 (`<stage>_compile_prog_native`, oracle `cake_native_bootstrap`
⇐ `cake_compiled_thm`) certifies the equation for **`compile_prog`** — the exact function the binary
runs under `--pancake` (fresh-session audit: `LAYER2 head const = pan_to_target$compile_prog`, `arg1 =
x64_target$x64_config`, `arg2 = x64_config$x64_backend_config`, `arg3 = <stage>BytesBridge$<stage>Prog`).
G1 is over **`compile_prog_max`**; bridging the two is the single named packaging lemma
(CN-BYTES-BRIDGE 4.1, discharged in-logic for boundscan in `CN-RUNG3-FINISH-REPORT.md`, not re-run
here). Because this lane does **not** invoke Layer 2 (it leaves G1 as an antecedent), each backbone is
`DISK_THM`-only: `cake_native_bootstrap` is quarantined to the one step it belongs to, and named.
Inherited, still binding: the binary is a released `cake`, and `cake_compiled_thm` is the upstream/CI
whole-compiler bootstrap. None is leanc.

---

## 5. What does NOT compose — the exact gap (named, not papered over)

Each lane delivers the **backbone** (`machine_sem ⊆ {semantics_decls «main» <stage>Prog}`, native
bytes + program conditions discharged) **and** the loop-free **decision-core Link A** (`evaluate
<stage>If … = n2w (spec (fold output))`). The distance to the end-to-end TARGET is the same named
links, none closed here:

1. **The whole-`main` FFI frame (primary gap).** The backbone's RHS is `semantics_decls s «main»
   <stage>Prog`; the decision-core Link A is a separate theorem about the extracted `If`. Composing
   them means lifting the `If` through the `main` body — the `Dec …` initialisers, the `@load_vec` FFI
   establishing the arena, the fold `While`, the `Store`, and the `@report_vec` FFI — to a
   `semantics_decls = <spec behaviour>` equation. Same FFI boundary boundscan names.
2. **The `compile_prog`↔`compile_prog_max` packaging lemma** (CN-BYTES-BRIDGE 4.1) — turns Layer 2's
   oracle into G1 (§4). Named; discharged in-logic for boundscan (`CN-RUNG3-FINISH`), not re-run per
   stage here.
3. **The runtime install package** (the ~28 remaining backbone antecedents). Discharged in a full
   end-to-end by the x64 target-config proof against the placed image; not this lane.
4. **The S3 prefix-matcher fold + the S7 escape-detector fold (scope caveat).** ipf certifies the
   loop-free **gate** over `acc`; the 9-byte prefix-matcher `While` body (state 0..10) + its Link-A
   refinement is the named S3 loop residual. traversal certifies the loop-free **gate** over `acc`;
   the 5-state escape-detector `While` body + its Link-A refinement is the named S7 loop residual.
   Both are the same residual class as C22/C23/rateadmit/cors.

None of the above is leanc; none reintroduces the in-logic EVAL cost.

---

## 6. Files

**On hbox** (`/home/hbox/hol-{ipf,traversal}-rung3/`, self-contained; no CakeML-tree files modified):
`<stage>BytesBridgeScript.sml`, `<stage>Rung3Script.sml`, `Holmakefile`, `<stage>.pnk`, `audit.sml`,
`rung3.out` + `bridge.out`.

**In this repo** (`docs/engine/probes/compiler/hol-{ipf,traversal}-rung3/`): the two `Script.sml`,
`Holmakefile`, the `.pnk` (md5-matched to hbox: `ipf.pnk` `e37696e5…`, `traversal.pnk` `fa88d77e…`),
`audit.sml`, `rung3.out`, `bridge.out`, plus this report. Build artifacts (`.S`, `.o`, `.dat`, `.ui`,
`.uo`, `*.dumpedheap`) and any `ffi/*.o` are excluded.

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
for d in ~/hol-ipf-rung3 ~/hol-traversal-rung3; do
  cd $d && Holmake && cat rung3.out && hol < audit.sml | grep '^AAA '
done
# theorem names:
#  backbones : ipf_rung3_native / traversal_rung3_native
#  Link A    : ipf_decisioncore_refines_spec / traversal_decisioncore_refines_spec
#  faithful  : ipfIf_faithful / traversalIf_faithful
#  Link B    : pancake/proofs/pan_to_targetProofScript.sml  pan_to_target_compile_semantics
#  bootstrap : compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml  cake_compiled_thm
```

## 8. Bottom line

Two more deployed serve stages — S3 `IpFilter.ipfilterStage`'s admit/deny gate (via `ipf`, the
`deployAdmits = permits deployRuleset` decision for the single `10.0.0.0/8` deny rule) and S7
`traversalStage`'s `..`-escape gate (via `traversal`, the `escapesSegs` `".."`-contains decision) —
are now carried through the full Rung-3 native pattern: native-compiled by the bootstrapped `cake`
(deterministic, valid ELF x86-64, 1590 / 1306 code bytes), reflected into HOL, and certified via
`pan_to_target_compile_semantics` with the concrete native bytes in the code slot and the four
program-level conditions discharged — `ipf_rung3_native` / `traversal_rung3_native`, kernel-checked,
`[oracles: DISK_THM] [axioms:]`, 0 axioms, `cake_native_bootstrap` quarantined to the Layer-2 bytes
equation. This lifts the deployed-14 backbone count from **6 to 8** (S3/S4/S5/S6/S7/S10/S11/S13) —
with the honest caveat that both are loop-free **decision projections** over their fold outputs (the
prefix-matcher / escape-detector fold bodies are separate named residuals). Because both projections
are loop-free, their **Link-A decision core closes in full** (`…_decisioncore_refines_spec`), and the
certified cores now cover the nested-equality + `Skip`-fall-through gate on real deployed
path-traversal code. The end-to-end machine→Lean-spec refinement still does not fully close: it needs
the whole-`main` FFI frame, the `compile_prog↔compile_prog_max` packaging lemma, the runtime install
package, and (for the full S3/S7) the fold loops — named residuals, none the EVAL dead end and none
leanc.

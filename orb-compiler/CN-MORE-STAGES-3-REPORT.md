# CN REPORT — TWO MORE real serve stages native-certified (the Rung-3 pattern): the native-compiled machine code of `cacheEmptyStage`'s freshness gate (S5, `cachefresh`) and `deployCorsStage` (S10, `cors`) refines each stage's Pancake source semantics, program-conditions DISCHARGED, native bytes in the code slot, `[oracles: DISK_THM] [axioms:]` 0 — and, because both projections are **loop-free**, their Link-A decision core closes in FULL (no loop-frame residual). NotEqual is a NEW certified guard form.

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake` (CakeML `ccfc23c`, x64 bootstrap). **Proof tree:** `/home/hbox/src/cakeml` @ `ed31510b3`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2, stdknl, built 2026-07-02).
**This lane's HOL4 scratch:** `/home/hbox/hol-{cachefresh,cors}-rung3/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-{cachefresh,cors}-rung3/`.
**Ground composed:** `CN-MORE-STAGES-REPORT.md` (wave-4 S13/S6 + the Rung-3 pattern), `CN-MORE-STAGES-2-REPORT.md` (S4/S11 + the decision-projection caveat), `CN-RUNG3-NATIVE-REPORT.md` (boundscan Rung-3), `CN-BYTES-BRIDGE-REPORT.md` (Layer 1 / Layer 2), `CN-NATIVE-BOOTSTRAP-REPORT.md` (`cake_compiled_thm`), `PNK-MANIFEST.md` (28 stages; S5/S10 picked as the simplest remaining Link-A).

---

## 0. TL;DR — what closes, what does not

The wave-4 lane and its successor took **four** deployed stages — S13 `securityheadersStage`,
S6 `redirectStage`, S4 `Rate.rateStage`, S11 `Gzip.gzipStage` — through the Rung-3 pattern and
closed each one's Link-A decision core in full. This lane takes **two more** members of the
deployed 14-stage fold `deployStagesFull2` through the identical pattern:

- **S5 `cacheEmptyStage` freshness gate** (`cachefresh.pnk`, 1481 B src) — the
  `Cache.Meta.isFresh` freshness test at the deployed `freshnessLifetime = 100`; a single
  ordered guard `if age < 100`. **Whole loop-free freshness decision** (like S6/S13, not a
  loop projection): the emitted `If` IS this gate's behaviour.
- **S10 `deployCorsStage`** (`cors.pnk`, 1841 B src) — the CORS `Access-Control-Allow-Origin`
  origin-allowed gate `originAllowed p o = allowAnyOrigin ∨ allowedOrigins.contains o`; a
  **nested** gate `if wild ≠ 0 { … } else { if km = ku { … } }` over the two hashBytes fold
  outputs.

For **each** stage this lane builds two kernel-checked HOL4 theories (`<stage>BytesBridge`,
`<stage>Rung3`), each `Holmake … OK`, `axioms = 0`. The headline backbones (verbatim from each
theory's own build dump `rung3.out`):

```
cachefresh_rung3_native   [oracles: DISK_THM]  [axioms: ]
cors_rung3_native         [oracles: DISK_THM]  [axioms: ]
⊢ compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'), stack_max)  (* G1 *)
  ∧  <runtime install package: pan_installed <stage>Bytes …, mc_conf_ok mc, …>              (* G2 *)
  ∧  semantics_decls s «main» <stage>Prog ≠ Fail
  ⇒  machine_sem mc ffi ms ⊆
       extend_with_resource_limit'
         (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
         {semantics_decls s «main» <stage>Prog}
```

i.e. **the native-compiled machine code of each stage refines that stage's Pancake source
semantics** — concrete native `<stage>Bytes`/`<stage>Bitmaps` (length **1066** / **1268**,
kernel-checked) in the real `bytes`/`bitmaps` slots, the FOUR program-level Link-B conditions
**discharged** (31 residual antecedents), `[oracles: DISK_THM]` only (no `cake_native_bootstrap`
on the backbone — G1 stays a NAMED antecedent, §4). Structurally byte-identical to the wave-4
S6/S13 and S4/S11 backbones.

**Link A closes in FULL for each decision core** — both projections are loop-free, so the Link-A
refinement is proven by plain `panSem$evaluate` symbolic execution (no loop-invariant induction,
no whole-loop frame residual):

```
cachefresh_decisioncore_refines_spec  [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «age» = SOME (ValWord (n2w a)) ∧ a < 2**63 ∧
  (∃r0. FLOOKUP s.locals «result» = SOME (ValWord r0)) ⇒
  ∃s'. evaluate (cachefreshIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (cacheFresh a)))

cors_decisioncore_refines_spec        [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «wild» = SOME (ValWord (n2w wild)) ∧
  FLOOKUP s.locals «km» = SOME (ValWord (n2w km)) ∧
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w ku)) ∧
  wild < dimword(:64) ∧ km < dimword(:64) ∧ ku < dimword(:64) ∧
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ⇒
  ∃s'. evaluate (corsIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (corsAllow wild km ku)))
```

where `cacheFresh a = (a < 100)` is EXACTLY `Cache.Meta.isFresh m now = decide (currentAge <
freshnessLifetime)` at the deployed `freshnessLifetime = 100` (drorb `Cache.lean`; the gate
consulted by `Reactor.Stage.Cache.Config.onReq`, position S5 of `deployStagesFull2`), and
`corsAllow wild km ku = (wild ≠ 0 ∨ km = ku)` is EXACTLY `Cors.originAllowed p o = p.allowAnyOrigin
∨ p.allowedOrigins.contains o` (drorb `Reactor.Stage.Cors` / `deployCorsStage`) as a function of the
loaded gate words — `wild` = the `allowAnyOrigin` flag, `km = ku` = the request-origin-hash equals
allowed-origin-hash test that models `allowedOrigins.contains o` for the single-allowed-origin
deploy (the C25 hashBytes-equality modelling caveat). The `cachefreshIf`/`corsIf` reasoned about
are **not** hand transcriptions asserted to match: `<stage>If_faithful` is a kernel-checked equation
that the term **is** the `If` structurally extracted from the verified-parser output `<stage>Prog`
(§2c), and a fresh-session audit confirmed the two sides are **distinct** theory constants
(`cachefreshBytesBridge$cachefreshProg` vs `cachefreshRung3$cachefreshIf`; `corsBytesBridge$corsProg`
vs `corsRung3$corsIf`; `DISTINCT=true`), not a vacuous `p = p`.

**Guard-shape advance — NotEqual is NEW.** The certified decision cores previously spanned `Cmp
Less` (S13, signed `<`), `Cmp Equal` (S6 tag dispatch), and `Cmp NotLess` (S4/S11, signed `≥`, both
operand orientations). This lane adds **`Cmp NotEqual`** (cors outer guard `wild ≠ 0`) and **`Cmp
Equal` between two variables** (cors inner guard `km = ku`, vs S6's Equal-against-constants), plus a
second `Cmp Less` on real deployed serve code (cachefresh). The cors gate also exercises the
**Skip fall-through** (the `km ≠ ku` arm leaves `«dec»` at its `0` initialiser — no assignment),
which the earlier all-arms-assign cores did not.

**Honest scope boundary.**
- **cachefresh (S5) is loop-free and closed IN FULL for the freshness decision** — like S6/S13. It
  is the `isFresh` sub-decision of `cacheEmptyStage`; the *other* S5 representatives (`cachekey`,
  `hashbytes`, the key/digest folds) are separate loop-carrying parts of S5 whose Link-A refinements
  remain named residuals (`PNK-MANIFEST §3`, unchanged). So the backbone here certifies S5's
  freshness gate; the S5 key/digest folds are out of scope and named.
- **cors (S10) is a DECISION PROJECTION** — like S4/S11. `cors.pnk` runs two hashBytes fold loops
  (hash(origin) = km, hash(allowed) = ku) and then the loop-free gate; this lane certifies the
  **loop-free gate `If`** over the fold outputs {wild, km, ku}. The two fold bodies + their Link-A
  refinements are the named S10 loop residual (the same residual class as C22/C23/rateadmit).

**End-to-end "machine code ⊆ {Lean spec behaviour}" still fully closes for 0/14** — for every stage
the whole-`main` FFI frame + `compile_prog↔compile_prog_max` packaging lemma + runtime install
package remain named residuals (§5), same as the prior lanes.

---

## 1. Coverage — how many deployed stages carry a Rung-3 backbone, honestly

`deployStagesFull2` (`~/dev/drorb/Reactor/Deploy.lean:1511`) is the deployed **14-stage**
middleware fold. The Rung-3 native backbone (native bytes + program conditions discharged,
`machine_sem ⊆ Pancake source semantics`, `[oracles: DISK_THM] [axioms:]`) now holds for:

| stage | `deployStagesFull2` | backbone | Link-A decision core | whole-stage scope |
|---|---|---|---|---|
| `boundscan` | — (runtime substrate) | ✅ `boundScan_rung3_native` | loop core only | whole-`main` loop frame OPEN |
| `secheaders` | **S13** | ✅ `secheaders_rung3_native` | ✅ FULL (`Cmp Less`) | whole stage (loop-free) |
| `redirect` | **S6** | ✅ `redirect_rung3_native` | ✅ FULL (`Cmp Equal`) | whole stage (loop-free) |
| `rateadmit` | **S4** | ✅ `rateadmit_rung3_native` | ✅ FULL (`Cmp NotLess`) | decision projection (windowed loop = residual) |
| `gzipupper` | **S11** | ✅ `gzipupper_rung3_native` | ✅ FULL (`Cmp NotLess` ×2 orient.) | decision projection (body-map loop = residual) |
| **`cachefresh`** | **S5** `cacheEmptyStage` | ✅ `cachefresh_rung3_native` | ✅ **FULL** (`Cmp Less`, `isFresh`) | **freshness decision (loop-free)**; S5 key/digest folds = residual |
| **`cors`** | **S10** `deployCorsStage` | ✅ `cors_rung3_native` | ✅ **FULL** (`Cmp NotEqual` + `Cmp Equal`, `originAllowed`) | **decision projection** (2 hashBytes folds = residual) |

- **Rung-3 native backbone: 7 real serve stages** (boundscan substrate + S13 + S6 + S4 + S11 + S5 + S10),
  each `[oracles: DISK_THM] [axioms:]`, 0 theory axioms, native bytes in the code slot.
- **Of the deployed 14 (`deployStagesFull2`): 6 stages (S4, S5, S6, S10, S11, S13) now carry the
  backbone**, up from **4** after the previous lane. **S5/S6/S13 carry it for a whole loop-free
  decision; S4/S10/S11 carry it for a loop-free decision projection** (the caveats in §0). All six
  additionally have a fully-closed loop-free Link-A decision core.
- **End-to-end "machine code ⊆ {Lean spec behaviour}" fully closes for 0 / 14** — unchanged; the FFI
  frame + packaging lemma + install package remain named residuals (§5) for every stage.

**Cumulative vs 14:** **6 / 14** deployed stages carry a Rung-3 native backbone (was 4/14). The four
certified guard forms now span `Less` / `Equal` / `NotLess` (both orientations) / **`NotEqual`** — the
full set of comparison forms the deployed decisions use.

---

## 2. What each lane PROVED (verbatim from each theory's build dump `rung3.out` / `bridge.out`)

All theorems `[oracles: DISK_THM] [axioms:]`; `axioms "<stage>Rung3" = 0`, `axioms
"<stage>BytesBridge" = 0` (re-checked in a fresh `hol`, §3).

**(a) The four program-level Link-B applicability conditions — DISCHARGED against the REAL
`pan_to_targetProof`/`pan_to_wordProof` constants** on the concrete native program, by EVAL:

```
cf_pancake_good_code ⊢ pancake_good_code cachefreshProg      co_pancake_good_code ⊢ pancake_good_code corsProg
cf_distinct_params   ⊢ distinct_params (functions …)          co_distinct_params   ⊢ distinct_params (functions …)
cf_distinct_names    ⊢ ALL_DISTINCT (MAP FST (functions …))   co_distinct_names    ⊢ ALL_DISTINCT (MAP FST (functions …))
cf_size_of_eids      ⊢ size_of_eids cachefreshProg < 2**64    co_size_of_eids      ⊢ size_of_eids corsProg < 2**64
```

**(b) The composed backbone** `cachefresh_rung3_native` / `cors_rung3_native` (§0). Built by
`SIMP_RULE bool_ss (map EQT_INTRO [the four (a) theorems])` on the bytes-bridge Layer-1 theorem
`<stage>_pan_to_target_specialised`. The four program conjuncts rewrite to `T` and drop, leaving
**31** antecedents and the conclusion `machine_sem mc ffi ms ⊆ … {semantics_decls s «main»
<stage>Prog}`. The native `<stage>Bytes`/`<stage>Bitmaps` occupy the `compile_prog_max` result slot
(G1) and the `pan_installed` slot (`cachefreshBytes` length **1066**, `corsBytes` length **1268**,
kernel-checked; `bmInts = [4]`).

**(c) Faithfulness — the decision core IS the verified-parser output's `If`** (not a hand
transcription):

```
cachefreshIf_faithful  ⊢ extract_if_decl (HD cachefreshProg) = SOME cachefreshIf
corsIf_faithful        ⊢ extract_if_decl (HD corsProg)       = SOME corsIf
```

Fresh-session fully-qualified-constant audit (§3): each equation relates two **distinct** theory
constants — `DISTINCT=true` — **not** vacuous. `extract_if` is a total structural search that pulls
the (first) `If` out of the decl body; for cors it walks past the two `While` fold bodies (the
`_ ⇒ NONE` clause) and returns the gate `If`.

**(d) Link A — the loop-free decision-core refinement** (§0). Real `panSem$evaluate` of the
extracted `If`:
- **cachefresh:** the guard `Cmp Less «age» 100w` (signed, via `signed_lt_n2w64` on `a < 2^63`)
  reduces to `a < 100`; the two `Annot`-wrapped `Assign «result»` arms write `n2w (cacheFresh a)`
  (fresh = 1 on the then-arm, stale = 0 on the else-arm).
- **cors:** the outer `Cmp NotEqual «wild» 0w` (`wild ≠ 0`) and inner `Cmp Equal «km» «ku»`
  (`km = ku`) — equalities via `n2w_eq_bounded64` (n2w injective on the machine range) — select the
  two `Annot`-wrapped `Assign «dec» 1w` arms, with the `km ≠ ku` fall-through `Annot`-wrapped `Skip`
  leaving `«dec»` at its `0` initialiser, so the emitted gate writes `n2w (corsAllow wild km ku)`.

Both threaded through the parser's transparent `Annot` no-ops (`seq_annot`), the panSem `If`
word-guard clause (`eval_If`), and the `Assign`/`is_valid_value`/`set_var` bookkeeping. **No
loop-invariant induction.**

**Trust footprint (audited, §3):** every backbone and decision-core theorem is `[oracles: DISK_THM]
[axioms:]`; each `<stage>Rung3`/`<stage>BytesBridge` has **0** theory axioms. A grep of both `Rung3`
scripts for `cheat|new_axiom|mk_thm|native_decide|ofReduceBool|ASSUME|mk_oracle` found **NONE** — no
`native_decide`-analogue (no `ofReduceBool`; this is HOL4, but the honesty gate is met), no `cheat`,
no `new_axiom`, and no `cake_native_bootstrap` on the backbone. The native bytes equation is the
NAMED antecedent G1; `cake_native_bootstrap` is quarantined to the Layer-2 bytes-bridge theorem
`<stage>_compile_prog_native` alone (§4). (The cors `Skip` fall-through rewrite is pulled directly
from `panSem$evaluate_def` clause 1, not re-stated — a standalone `Skip` is overloaded across
wordLang/stackLang/panLang, all in scope via the `pan_to_target` opens; the def clause fixes it to
`panLang$Skip` under `panSem$evaluate` unambiguously.)

---

## 3. Independent verification (I ran it; "it built" / "it measured" is checked, not asserted)

- **Full from-scratch build:** `Holmake` in each dir → `Building 1 theory file … OK` for the
  bytes-bridge (~18–20 s) then the Rung3 (~18–23 s). The bytes-bridge script re-invokes `cake
  --pancake` at build time, so the whole chain (native compile → reflect → Link B → backbone → Link A)
  is reproducible from source. The 259 prebuilt CakeML `.hol/objs/*Theory.dat` are reused; no
  CakeML-tree file modified. Both dirs green. **NB — the new oleans (`*Theory.dat`) were absent on
  hbox until this lane built them; I verified GREEN myself before claiming (build dumps above).**
- **Fresh-session tag/axiom audit** (reloaded the built `.dat` in a clean `hol`, printed `Thm.tag`
  + fully-qualified constants): backbones `cachefresh_rung3_native` / `cors_rung3_native` =
  `[oracles: DISK_THM] [axioms: ]`; decision-core and faithful theorems = `[oracles: DISK_THM]
  [axioms: ]`; `axioms "cachefreshRung3" = 0`, `axioms "corsRung3" = 0`, both BytesBridge = 0. The
  faithful-theorem constant audit printed `prog=cachefreshBytesBridge$cachefreshProg
  if=cachefreshRung3$cachefreshIf DISTINCT=true` and `prog=corsBytesBridge$corsProg
  if=corsRung3$corsIf DISTINCT=true`. Backbone antecedent-conjuncts = 31, conclusion mentions
  `<stage>Prog`, antecedent mentions the native `<stage>Bytes`. Layer-2 `<stage>_compile_prog_native`
  = `[oracles: DISK_THM,cake_native_bootstrap] [axioms: ]` (the one named oracle, quarantined).
- **Native compile, determinism + ELF (re-run this lane):** `cake --pancake < cachefresh.pnk` →
  **1066** `.byte` values, md5-stable across 3 runs (`cd4ac6c6…`), `cc -c` → valid `ELF 64-bit LSB
  relocatable, x86-64`. `cors.pnk` → **1268** `.byte`, md5-stable (`f0558cba…`), valid ELF x86-64.
  Both CODE sizes match `PNK-MANIFEST.md §1` (rows 14 `cachefresh` 1066, 19 `cors` 1268). `.pnk`
  md5s: `cachefresh.pnk` `0c53c703…`, `cors.pnk` `17db255d…` (repo copies md5-identical to hbox).
- **Scope note (no Rust/Lean delta):** like the prior lanes, this is a pure HOL4/CakeML lane. It
  touches no Lean spec, no `Datapath.lean`, no `lakefile`, no `libdrorb`, no Rust dataplane — so there
  is **no** `libdrorb`/`cargo` rebuild and **no** serve `curl` in scope; the "run it" evidence is the
  build + fresh-session audit + native-compile measurement above.

---

## 4. The trust boundary — why the backbones are `DISK_THM`-only

Identical to `CN-MORE-STAGES-2-REPORT.md §4`. Each backbone keeps the native-bytes equation as a
hypothesis G1: `compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'),
stack_max)`. The bytes-bridge Layer 2 (`<stage>_compile_prog_native`, oracle `cake_native_bootstrap`
⇐ `cake_compiled_thm`) certifies the equation for **`compile_prog`** — the exact function the binary
runs under `--pancake`. G1 is over **`compile_prog_max`**; bridging the two is the single named
packaging lemma (CN-BYTES-BRIDGE 4.1, discharged in-logic for boundscan in `CN-RUNG3-FINISH-REPORT.md`,
not re-run here). Because this lane does **not** invoke Layer 2 (it leaves G1 as an antecedent), each
backbone is `DISK_THM`-only: `cake_native_bootstrap` is quarantined to the one step it belongs to, and
named. Inherited, still binding: the binary is a released `cake`, and `cake_compiled_thm` is the
upstream/CI whole-compiler bootstrap. None is leanc.

---

## 5. What does NOT compose — the exact gap (named, not papered over)

Each lane delivers the **backbone** (`machine_sem ⊆ {semantics_decls «main» <stage>Prog}`, native
bytes + program conditions discharged) **and** the loop-free **decision-core Link A** (`evaluate
<stage>If … = n2w (spec input)`). The distance to the end-to-end TARGET is the same named links, none
closed here:

1. **The whole-`main` FFI frame (primary gap).** The backbone's RHS is `semantics_decls s «main»
   <stage>Prog`; the decision-core Link A is a separate theorem about the extracted `If`. Composing
   them means lifting the `If` through the `main` body — the `Dec …` initialisers, the `@load_vec`
   FFI establishing `FLOOKUP «age»`/`«wild»`/`«km»`/`«ku»`, the `Store`, and the `@report_vec` FFI —
   to a `semantics_decls = <spec behaviour>` equation. Same FFI boundary boundscan names; for
   cachefresh **with no loop between the FFI and the decision**. Reported, not faked.
2. **The `compile_prog`↔`compile_prog_max` packaging lemma** (CN-BYTES-BRIDGE 4.1) — turns Layer 2's
   oracle into G1 (§4). Named; discharged in-logic for boundscan (`CN-RUNG3-FINISH`), not re-run per
   stage here.
3. **The runtime install package** (the ~28 remaining backbone antecedents). Discharged in a full
   end-to-end by the x64 target-config proof against the placed image; not this lane.
4. **The S10 hashBytes fold loops + the S5 key/digest folds (scope caveat).** cors certifies the
   loop-free **gate**; the two hashBytes folds (km/ku) + their Link-A refinements are the named S10
   loop residual. cachefresh certifies S5's loop-free **freshness gate**; the S5 key/digest folds
   (`cachekey`/`hashbytes`) are separate loop-carrying representatives, their refinements the named S5
   residual. Both unchanged from `PNK-MANIFEST §3`.

None of the above is leanc; none reintroduces the in-logic EVAL cost.

---

## 6. Files

**On hbox** (`/home/hbox/hol-{cachefresh,cors}-rung3/`, self-contained; no CakeML-tree files
modified): `<stage>BytesBridgeScript.sml`, `<stage>Rung3Script.sml`, `Holmakefile`, `<stage>.pnk`,
`audit.sml`, `rung3.out` + `bridge.out`.

**In this repo** (`docs/engine/probes/compiler/hol-{cachefresh,cors}-rung3/`): the two
`Script.sml`, `Holmakefile`, the `.pnk` (md5-matched to hbox: `cachefresh.pnk` `0c53c703…`,
`cors.pnk` `17db255d…`), `audit.sml`, `rung3.out`, `bridge.out`, plus this report. Build artifacts
(`.S`, `.o`, `.dat`, `.ui`, `.uo`, `*.dumpedheap`) and any `ffi/*.o` are excluded.

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
for d in ~/hol-cachefresh-rung3 ~/hol-cors-rung3; do
  cd $d && Holmake && cat rung3.out && hol < audit.sml | grep '^AAA '
done
# theorem names:
#  backbones : cachefresh_rung3_native / cors_rung3_native
#  Link A    : cachefresh_decisioncore_refines_spec / cors_decisioncore_refines_spec
#  faithful  : cachefreshIf_faithful / corsIf_faithful
#  Link B    : pancake/proofs/pan_to_targetProofScript.sml  pan_to_target_compile_semantics
#  bootstrap : compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml  cake_compiled_thm
```

## 8. Bottom line

Two more deployed serve stages — S5 `cacheEmptyStage`'s freshness gate (via `cachefresh`, the
`Cache.Meta.isFresh` `age < 100` test) and S10 `deployCorsStage` (via `cors`, the `originAllowed`
gate) — are now carried through the full Rung-3 native pattern: native-compiled by the bootstrapped
`cake` (deterministic, valid ELF x86-64, 1066 / 1268 code bytes), reflected into HOL, and certified
via `pan_to_target_compile_semantics` with the concrete native bytes in the code slot and the four
program-level conditions discharged — `cachefresh_rung3_native` / `cors_rung3_native`, kernel-checked,
`[oracles: DISK_THM] [axioms:]`, 0 axioms, `cake_native_bootstrap` quarantined to the Layer-2 bytes
equation. This lifts the deployed-14 backbone count from **4 to 6** (S4/S5/S6/S10/S11/S13) — with the
honest caveats that cachefresh certifies S5's loop-free freshness decision (the S5 key/digest folds
are separate residuals) and cors is the loop-free **decision projection** over the two hashBytes fold
outputs. Because both projections are loop-free, their **Link-A decision core closes in full**
(`…_decisioncore_refines_spec`), and the certified cores now span every deployed comparison form
(`Less` / `Equal` / `NotLess` both orientations / **`NotEqual`** — new this lane), plus the first
`Skip`-fall-through gate. The end-to-end machine→Lean-spec refinement still does not fully close: it
needs the whole-`main` FFI frame, the `compile_prog↔compile_prog_max` packaging lemma, the runtime
install package, and (for the full S5/S10) the fold loops — named residuals, none the EVAL dead end
and none leanc.

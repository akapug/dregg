# CN REPORT — TWO MORE real serve stages native-certified (the Rung-3 pattern): the native-compiled machine code of `jwtAdminStage`'s HS256 verify/alg-confusion gate (S1, `jwt`) and `policyStage`'s declared-surface admit gate (S8, `admit`) refines each stage's Pancake source semantics, program-conditions DISCHARGED, native bytes in the code slot, `[oracles: DISK_THM] [axioms:]` 0 — and each stage's loop-free Link-A decision core closes in FULL. This lifts the deployed-14 backbone count from **8 to 10**.

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake` (CakeML `ccfc23c`, x64 bootstrap). **Proof tree:** `/home/hbox/src/cakeml`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2, stdknl, built 2026-07-02).
**This lane's HOL4 scratch:** `/home/hbox/hol-{jwt,admit}-rung3/` (new, self-contained; no CakeML-tree files modified) — mirrored to `docs/engine/probes/compiler/hol-{jwt,admit}-rung3/`.
**Ground composed:** `CN-MORE-STAGES-{,2,3,4}-REPORT.md` (the 8-stage cumulative + the Rung-3 pattern), `CN-RUNG3-NATIVE-REPORT.md` (boundscan Rung-3), `CN-BYTES-BRIDGE-REPORT.md` (Layer 1 / Layer 2), `CN-NATIVE-BOOTSTRAP-REPORT.md` (`cake_compiled_thm`), `PNK-MANIFEST.md` (28 stages; S1/S8 picked as the next two deployed decision projections not yet certified).

---

## 0. TL;DR — what closes, what does not

The four predecessor lanes took **eight** deployed stages — S13 `securityheadersStage`, S6
`redirectStage`, S4 `Rate.rateStage`, S11 `Gzip.gzipStage`, S5 `cacheEmptyStage`'s freshness gate,
S10 `deployCorsStage`, S3 `IpFilter.ipfilterStage`, S7 `traversalStage` — through the Rung-3 pattern
and closed each one's loop-free Link-A decision core in full. This lane takes **two more** members of
the deployed 14-stage fold `deployStagesFull2` through the identical pattern:

- **S1 `jwtAdminStage` HS256 verify + alg-confusion gate** (`jwt.pnk`, 1853 B src) — the deployed
  `Reactor.Stage.Jwt.jwtStage` / `Jwt.authenticate` admit decision `dec = 1 iff km = ku ∧ alg = 1`
  where `km`/`ku` are the hashBytes fold outputs of the HMAC-SHA256 **digest** and the **signature**
  arenas (`km = ku` IS `verifyHmac`'s signature-equality), and `alg` is the token's declared
  algorithm tag (`1` = HS256; the alg-confusion gate). A **nested** gate over a
  **variable-vs-variable** outer guard `if km == ku { if alg == 1 { … } }`.
- **S8 `policyStage` declared-surface admit gate** (`admit.pnk`, 1532 B src) — the deployed
  `deployDecisionOf` / `Policy.serveDecision` declared-surface admission
  `dec = 1 iff km = KM ∧ ku = KU` for the single declared `(method, route)` surface, where
  `km`/`ku` are the hashBytes fold outputs of the request method / route and
  `KM = hashBytes "GET" = 4773603` (`0x48D6E3`), `KU = hashBytes "/api" = 821282413` (`0x30F3C66D`).
  A **nested** AND gate `if km == KM { if ku == KU { … } }` over two equality-against-constant guards.

For **each** stage this lane builds two kernel-checked HOL4 theories (`<stage>BytesBridge`,
`<stage>Rung3`), each `Holmake … OK` from a genuine `cleanAll`, `axioms = 0`. The headline backbones
(verbatim from each theory's own build dump `rung3.out`):

```
jwt_rung3_native    [oracles: DISK_THM]  [axioms: ]
admit_rung3_native  [oracles: DISK_THM]  [axioms: ]
⊢ compile_prog_max c mc <stage>Prog = (SOME (<stage>Bytes, <stage>Bitmaps, c'), stack_max)  (* G1 *)
  ∧  <runtime install package: pan_installed <stage>Bytes …, mc_conf_ok mc, …>              (* G2 *)
  ∧  semantics_decls s «main» <stage>Prog ≠ Fail
  ⇒  machine_sem mc ffi ms ⊆
       extend_with_resource_limit'
         (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
         {semantics_decls s «main» <stage>Prog}
```

i.e. **the native-compiled machine code of each stage refines that stage's Pancake source
semantics** — concrete native `<stage>Bytes`/`<stage>Bitmaps` (code length **1264** / **1270** bytes,
`bmInts = [4]`, kernel-checked) in the real `bytes`/`bitmaps` slots, the FOUR program-level Link-B
conditions **discharged** (31 residual antecedents), `[oracles: DISK_THM]` only (no
`cake_native_bootstrap` on the backbone — G1 stays a NAMED antecedent, §4). Structurally
byte-identical to the S3/S7 (ipf/traversal) backbones.

**Link A closes in FULL for each decision core** — both projections are loop-free, so the Link-A
refinement is proven by plain `panSem$evaluate` symbolic execution (no loop-invariant induction, no
whole-loop frame residual):

```
jwt_decisioncore_refines_spec    [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «km» = SOME (ValWord (n2w km)) ∧ km < dimword(:64) ∧
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w ku)) ∧ ku < dimword(:64) ∧
  FLOOKUP s.locals «alg» = SOME (ValWord (n2w alg)) ∧ alg < dimword(:64) ∧
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ⇒
  ∃s'. evaluate (jwtIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (jwtDec km ku alg)))

admit_decisioncore_refines_spec  [oracles: DISK_THM] [axioms: ]
⊢ FLOOKUP s.locals «km» = SOME (ValWord (n2w km)) ∧ km < dimword(:64) ∧
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w ku)) ∧ ku < dimword(:64) ∧
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ⇒
  ∃s'. evaluate (admitIf, s) = (NONE, s') ∧
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (admitDec km ku)))
```

where `jwtDec km ku alg = (if km = ku ∧ alg = 1 then 1 else 0)` is EXACTLY `jwtAdminStage`'s
sig-equality + HS256 admit as a function of the fold outputs + alg tag (drorb
`Reactor/Deploy.lean:1388`, `Reactor/Stage/Jwt.lean` `authenticate`; position S1 of `deployStagesFull2`,
`Reactor/Deploy.lean:1517`), and `admitDec km ku = (if km = 4773603 ∧ ku = 821282413 then 1 else 0)`
is EXACTLY `policyStage`'s declared-surface admit (`policyReserved` = the REAL `deployDecisionOf` /
`Policy.serveDecision`; `Reactor/Deploy.lean:1036`) for the single declared `(GET, /api)` surface, as
a function of the two hashBytes fold outputs (position S8 of `deployStagesFull2`). The
`jwtIf`/`admitIf` reasoned about are **not** hand transcriptions asserted to match: `<stage>If_faithful`
is a kernel-checked equation that the term **is** the `If` structurally extracted from the
verified-parser output `<stage>Prog` (§2c), and a fresh-session audit confirmed the two sides are
**distinct** theory constants (`jwtBytesBridge$jwtProg` vs `jwtRung3$jwtIf`;
`admitBytesBridge$admitProg` vs `admitRung3$admitIf`; `DISTINCT=true`), not a vacuous `p = p`.

**Guard-shape coverage — a genuinely new form.** jwt introduces the first **variable-vs-variable**
equality guard: the outer `Cmp Equal (Var «km») (Var «ku»)` compares two loaded fold outputs (every
prior lane compared a variable against a `Const`). It is discharged via `n2w_eq_bounded64` on **both**
sides (`(n2w km = n2w ku) ⇔ (km = ku)`, both `< dimword(:64)`). admit adds a **nested `Cmp Equal`/`Cmp
Equal` AND gate against two constants** with a `Skip` fall-through on **both** else-arms (dec stays at
its `0` initialiser unless both equalities hold) — the deny-by-default admission shape. Both gates
carry the `Skip`-fall-through structure S10 cors / S7 traversal introduced.

**Honest scope boundary — both are DECISION PROJECTIONS** (like S3/S4/S7/S10/S11). Each `.pnk` runs
its bounded fold loops (jwt: two hashBytes folds over the digest / signature arenas; admit: two
hashBytes folds over the method / route arenas) and then the loop-free gate; this lane certifies the
**loop-free gate `If`** over the fold outputs `{km, ku(, alg)}`. The fold bodies + their Link-A
refinements are the named S1 / S8 loop residuals (the same residual class as C22/C23/ipf/cors). For
jwt additionally: the **HMAC-SHA256 digest itself is the crypto FFI trust boundary** (an input to the
gate, not compiled here — like the TLS crypto), and the upstream base64url-decode / JSON claim parse
are the C27 base64 residual class. So the backbone here certifies each stage's whole-`main` Pancake
source refinement + the loop-free decision gate; the fold loops (and jwt's crypto FFI) are out of
scope and named (§5).

**End-to-end "machine code ⊆ {Lean spec behaviour}" still fully closes for 0/14** — for every stage
the whole-`main` FFI frame + `compile_prog↔compile_prog_max` packaging lemma + runtime install
package remain named residuals (§5), same as the prior lanes.

---

## 1. Coverage — how many deployed stages carry a Rung-3 backbone, honestly

`deployStagesFull2` (`~/dev/drorb/Reactor/Deploy.lean:1517`) is the deployed **14-stage** middleware
fold (ordering re-read this lane, §3). The Rung-3 native backbone (native bytes + program conditions
discharged, `machine_sem ⊆ Pancake source semantics`, `[oracles: DISK_THM] [axioms:]`) now holds for:

| stage | `deployStagesFull2` | backbone | Link-A decision core | whole-stage scope |
|---|---|---|---|---|
| `boundscan` | — (runtime substrate) | ✅ `boundScan_rung3_native` | loop core only | whole-`main` loop frame OPEN |
| **`jwt`** | **S1** `jwtAdminStage` | ✅ **`jwt_rung3_native`** | ✅ **FULL** (var-vs-var `Cmp Equal` + `Cmp Equal` + `Skip`, `jwtDec`) | **decision projection** (2 hashBytes folds + base64/JSON + HMAC FFI = residuals) |
| `ipf` | S3 `IpFilter.ipfilterStage` | ✅ `ipf_rung3_native` | ✅ FULL (`Cmp Equal`, `deployAdmits`) | decision projection (prefix-matcher fold = residual) |
| `rateadmit` | S4 `Rate.rateStage` | ✅ `rateadmit_rung3_native` | ✅ FULL (`Cmp NotLess`) | decision projection (windowed loop = residual) |
| `cachefresh` | S5 `cacheEmptyStage` | ✅ `cachefresh_rung3_native` | ✅ FULL (`Cmp Less`, `isFresh`) | freshness decision (loop-free); S5 folds = residual |
| `redirect` | S6 `redirectStage` | ✅ `redirect_rung3_native` | ✅ FULL (`Cmp Equal`) | whole stage (loop-free) |
| `traversal` | S7 `traversalStage` | ✅ `traversal_rung3_native` | ✅ FULL (nested `Cmp Equal`×2 + `Skip`, `escapesSegs`) | decision projection (escape-detector fold = residual) |
| **`admit`** | **S8** `policyStage` | ✅ **`admit_rung3_native`** | ✅ **FULL** (nested `Cmp Equal`×2 const + `Skip`, `admitDec`) | **decision projection** (2 hashBytes folds = residuals) |
| `cors` | S10 `deployCorsStage` | ✅ `cors_rung3_native` | ✅ FULL (`Cmp NotEqual` + `Cmp Equal`) | decision projection (2 hashBytes folds = residual) |
| `gzipupper` | S11 `Gzip.gzipStage` | ✅ `gzipupper_rung3_native` | ✅ FULL (`Cmp NotLess` ×2 orient.) | decision projection (body-map loop = residual) |
| `secheaders` | S13 `securityheadersStage` | ✅ `secheaders_rung3_native` | ✅ FULL (`Cmp Less`) | whole stage (loop-free) |

- **Rung-3 native backbone: 11 real serve stages** (boundscan substrate + S1 + S3 + S4 + S5 + S6 + S7
  + S8 + S10 + S11 + S13), each `[oracles: DISK_THM] [axioms:]`, 0 theory axioms, native bytes in the
  code slot.
- **Of the deployed 14 (`deployStagesFull2`): 10 stages (S1, S3, S4, S5, S6, S7, S8, S10, S11, S13)
  now carry the backbone**, up from **8** after the previous lane. S5/S6/S13 carry it for a whole
  loop-free decision; S1/S3/S4/S7/S8/S10/S11 carry it for a loop-free decision projection (the caveats
  in §0). All ten additionally have a fully-closed loop-free Link-A decision core.
- **End-to-end "machine code ⊆ {Lean spec behaviour}" fully closes for 0 / 14** — unchanged; the FFI
  frame + packaging lemma + install package remain named residuals (§5) for every stage.

**Cumulative vs 14:** **10 / 14** deployed stages carry a Rung-3 native backbone (was 8/14).
**Remaining 4:** S2 `BasicAuth.basicStage` (base64-decode loop residual), S9 `headerRewriteStage` /
S14 `Header.headerStage` (the `copy` rewrite emitter — no branch gate to project), and S12
`HtmlRewrite.htmlrewriteStage` (no `.pnk`; streaming-tokenizer body-rewrite loop). The certified guard
forms now span `Less` / `Equal` (const & **var-vs-var** / single & nested) / `NotLess` (both
orientations) / `NotEqual`, plus the `Skip` fall-through — the full set of comparison forms the
deployed decisions use.

---

## 2. What each lane PROVED (verbatim from each theory's build dump `rung3.out` / `bridge.out`)

All theorems `[oracles: DISK_THM] [axioms:]`; `axioms "<stage>Rung3" = 0`, `axioms "<stage>BytesBridge"
= 0` (re-checked in a fresh `hol` after a `cleanAll` rebuild, §3).

**(a) The four program-level Link-B applicability conditions — DISCHARGED against the REAL
`pan_to_targetProof`/`pan_to_wordProof` constants** on the concrete native program, by EVAL:

```
jw_pancake_good_code ⊢ pancake_good_code jwtProg          ad_pancake_good_code ⊢ pancake_good_code admitProg
jw_distinct_params   ⊢ distinct_params (functions …)       ad_distinct_params   ⊢ distinct_params (functions …)
jw_distinct_names    ⊢ ALL_DISTINCT (MAP FST (functions …))  ad_distinct_names ⊢ ALL_DISTINCT (MAP FST (functions …))
jw_size_of_eids      ⊢ size_of_eids jwtProg < 2**64        ad_size_of_eids      ⊢ size_of_eids admitProg < 2**64
```

**(b) The composed backbone** `jwt_rung3_native` / `admit_rung3_native` (§0). Built by
`SIMP_RULE bool_ss (map EQT_INTRO [the four (a) theorems])` on the bytes-bridge Layer-1 theorem
`<stage>_pan_to_target_specialised`. The four program conjuncts rewrite to `T` and drop, leaving
**31** antecedents and the conclusion `machine_sem mc ffi ms ⊆ … {semantics_decls s «main»
<stage>Prog}`. The native `<stage>Bytes`/`<stage>Bitmaps` occupy the `compile_prog_max` result slot
(G1) and the `pan_installed` slot (`jwtBytes` length **1264**, `admitBytes` length **1270**,
kernel-checked; `bmInts = [4]`). Fresh-session audit: `backbone concl-mentions-<stage>Prog = true`,
`backbone ante-mentions-<stage>Bytes = true`, `antecedent-conjuncts = 31`.

**(c) Faithfulness — the decision core IS the verified-parser output's `If`** (not a hand
transcription):

```
jwtIf_faithful    ⊢ extract_if_decl (HD jwtProg)    = SOME jwtIf
admitIf_faithful  ⊢ extract_if_decl (HD admitProg)  = SOME admitIf
```

Fresh-session fully-qualified-constant audit (§3): each equation relates two **distinct** theory
constants — `prog=jwtBytesBridge$jwtProg if=jwtRung3$jwtIf DISTINCT=true` and
`prog=admitBytesBridge$admitProg if=admitRung3$admitIf DISTINCT=true` — **not** vacuous. `extract_if`
is a total structural search that pulls the (first) `If` out of the decl body; it walks past the two
`While` fold bodies (the `_ ⇒ NONE` clause) and returns the gate `If` (transcribed exactly from the
build-time parser dump: outer guard, both `Annot` location strings, and the `Skip` fall-throughs —
`(44:7 UNKNOWN)`, `(45:6 45:12)`, `(UNKNOWN UNKNOWN)`).

**(d) Link A — the loop-free decision-core refinement** (§0). Real `panSem$evaluate` of the extracted
nested `If`:
- **jwt:** the outer guard `Cmp Equal «km» «ku»` — via `n2w_eq_bounded64` on **both** operands
  reduces `(n2w km = n2w ku)` to `(km = ku)` — and the inner `Cmp Equal «alg» 1w` (via
  `n2w_eq_bounded64`) — selects the deep `Annot`-wrapped `Assign «dec» 1w`, with the `km ≠ ku` and
  `alg ≠ 1` fall-throughs `Annot`-wrapped `Skip` leaving `«dec»` at its `0` initialiser, so the
  emitted gate writes `n2w (jwtDec km ku alg)`.
- **admit:** the outer `Cmp Equal «km» 4773603w` and inner `Cmp Equal «ku» 821282413w` (both via
  `n2w_eq_bounded64`) select the deep `Assign «dec» 1w`, with both `Skip` fall-throughs leaving
  `«dec»` at `0`, so the emitted gate writes `n2w (admitDec km ku)`.

Both threaded through the parser's transparent `Annot` no-ops (`seq_annot`), the panSem `If`
word-guard clause (`eval_If`), the `Assign`/`is_valid_value`/`set_var` bookkeeping (`eval_dec_assign`),
and the `Skip` fall-through clause pulled directly from `panSem$evaluate_def` (`eval_skip`). **No
loop-invariant induction.**

**Trust footprint (audited, §3):** every backbone and decision-core theorem is `[oracles: DISK_THM]
[axioms:]`; each `<stage>Rung3`/`<stage>BytesBridge` has **0** theory axioms. A grep of both `Rung3`
scripts for `cheat|new_axiom|mk_thm|native_decide|ofReduceBool|ASSUME|mk_oracle` found **NONE** — no
`native_decide`-analogue (no `ofReduceBool`; this is HOL4, the honesty gate is met), no `cheat`, no
`new_axiom`, and no `cake_native_bootstrap` on the backbone. The native bytes equation is the NAMED
antecedent G1; `cake_native_bootstrap` is quarantined to the Layer-2 bytes-bridge theorem
`<stage>_compile_prog_native` alone (**exactly one** `mk_oracle_thm` per BytesBridge, grep-confirmed,
§4). (The `Skip` fall-through rewrite is pulled directly from `panSem$evaluate_def` clause 1, not
re-stated — a standalone `Skip` is overloaded across wordLang/stackLang/panLang, all in scope via the
`pan_to_target` opens; the def clause fixes it to `panLang$Skip` under `panSem$evaluate`.)

---

## 3. Independent verification (I ran it; "it built" / "it measured" is checked, not asserted)

- **Full from-scratch build:** `Holmake cleanAll` in each dir (emptied `.hol/`, removed `<stage>.S`),
  then `Holmake` → `Building 2 theory files … OK` for both — the bytes-bridge (jwt 22 s / admit 20 s)
  then the Rung3 (jwt 19 s / admit 18 s). The bytes-bridge script re-invokes `cake --pancake` at build
  time, so the whole chain (native compile → reflect → Link B → backbone → Link A) is reproducible
  from source. The prebuilt CakeML `.dat` are reused; no CakeML-tree file modified. Both dirs green.
  **NB — the new oleans (`jwt*Theory`, `admit*Theory`) were absent on hbox until this lane built them;
  I verified GREEN myself, including after a genuine `cleanAll`, before claiming (build dumps above).**
- **Fresh-session tag/axiom audit** (reloaded the freshly-rebuilt oleans in a clean `hol`, printed
  `Thm.tag` + fully-qualified constants, `audit.sml`): backbones `jwt_rung3_native` /
  `admit_rung3_native` = `[oracles: DISK_THM] [axioms: ]`; decision-core and faithful theorems =
  `[oracles: DISK_THM] [axioms: ]`; `axioms "jwtRung3" = 0`, `axioms "admitRung3" = 0`, both
  BytesBridge = 0. The faithful-theorem constant audit printed `prog=jwtBytesBridge$jwtProg
  if=jwtRung3$jwtIf DISTINCT=true` and `prog=admitBytesBridge$admitProg if=admitRung3$admitIf
  DISTINCT=true`. Backbone antecedent-conjuncts = 31, conclusion mentions `<stage>Prog`, antecedent
  mentions the native `<stage>Bytes`. Layer-2 `<stage>_compile_prog_native` = `[oracles:
  DISK_THM,cake_native_bootstrap] [axioms: ]` (the one named oracle, quarantined).
- **Native compile, determinism + ELF (re-run this lane):** `cake --pancake < jwt.pnk` → **1264**
  `.byte` values, md5-stable across 3 runs (`f4e67ed4…`), `cc -c` → valid `ELF 64-bit LSB relocatable,
  x86-64`. `admit.pnk` → **1270** `.byte`, md5-stable (`654eeeaa…`), valid ELF x86-64. Both CODE sizes
  match `PNK-MANIFEST.md §1` (row 8 `jwt` 1264, row 17 `admit` 1270). `.pnk` md5s: `jwt.pnk`
  `d1deca6c…`, `admit.pnk` `31166dc1…` (repo copies md5-identical to hbox, verified).
- **Lean-spec correspondence grounded (read, not invented):** the spec functions are drorb constants,
  read this lane — `jwtAdminStage` (`Reactor/Deploy.lean:1388`, runs the REAL `Jwt.jwtStage` /
  `Jwt.authenticate` on `/admin*`), `policyStage` (`:1036`, `onRequest = cond (policyReserved req)
  (.respond forbidden403) (.continue c)`; `policyReserved`/`deployDecisionOf` = the REAL
  `Policy.serveDecision`, `:759`); `deployStagesFull2` orders `jwtAdminStage` at position **1** and
  `policyStage` at position **8** (`Reactor/Deploy.lean:1517`). `jwtDec`/`admitDec` re-declare these as
  functions of the fold outputs; `KM = hashBytes "GET" = 4773603`, `KU = hashBytes "/api" = 821282413`
  are the declared-surface keys the C23 fold reproduces (`0x48D6E3`/`0x30F3C66D` in the parser dump).
- **Scope note (no Rust/Lean delta → no cargo/curl in scope):** like the prior lanes, this is a pure
  HOL4/CakeML lane. It touches no Lean spec, no `Datapath.lean`, no `lakefile`, no `libdrorb`, no Rust
  dataplane — so there is **no** `libdrorb`/`cargo` rebuild and **no** serve `curl` in scope; the "run
  it" evidence is the `cleanAll` build + fresh-session audit + native-compile measurement above
  (identical scope posture to `CN-MORE-STAGES-3/4-REPORT.md §3`). The deployed serve is unchanged.

---

## 4. The trust boundary — why the backbones are `DISK_THM`-only

Identical to `CN-MORE-STAGES-4-REPORT.md §4`. Each backbone keeps the native-bytes equation as a
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
<stage>If … = n2w (spec (fold outputs))`). The distance to the end-to-end TARGET is the same named
links, none closed here:

1. **The whole-`main` FFI frame (primary gap).** The backbone's RHS is `semantics_decls s «main»
   <stage>Prog`; the decision-core Link A is a separate theorem about the extracted `If`. Composing
   them means lifting the `If` through the `main` body — the `Dec …` initialisers, the `@load_vec` FFI
   establishing the arena, the two fold `While`s, the `Store`, and the `@report_vec` FFI — to a
   `semantics_decls = <spec behaviour>` equation. Same FFI boundary boundscan names.
2. **The `compile_prog`↔`compile_prog_max` packaging lemma** (CN-BYTES-BRIDGE 4.1) — turns Layer 2's
   oracle into G1 (§4). Named; discharged in-logic for boundscan (`CN-RUNG3-FINISH`), not re-run per
   stage here.
3. **The runtime install package** (the ~28 remaining backbone antecedents). Discharged in a full
   end-to-end by the x64 target-config proof against the placed image; not this lane.
4. **The S1 / S8 fold loops (scope caveat).** jwt certifies the loop-free **gate** over `{km,ku,alg}`;
   the two hashBytes `While` bodies + their Link-A refinements + the upstream base64url-decode / JSON
   claim parse loops + the **HMAC-SHA256 digest crypto FFI** are the named S1 residuals. admit
   certifies the loop-free **gate** over `{km,ku}`; the two hashBytes `While` bodies + their Link-A
   refinements are the named S8 residual. Both fold classes are the same residual class as
   C22/C23/ipf/cors.

None of the above is leanc; none reintroduces the in-logic EVAL cost.

---

## 6. Files

**On hbox** (`/home/hbox/hol-{jwt,admit}-rung3/`, self-contained; no CakeML-tree files modified):
`<stage>BytesBridgeScript.sml`, `<stage>Rung3Script.sml`, `Holmakefile`, `<stage>.pnk`, `audit.sml`,
`rung3.out` + `bridge.out`.

**In this repo** (`docs/engine/probes/compiler/hol-{jwt,admit}-rung3/`): the two `Script.sml`,
`Holmakefile`, the `.pnk` (md5-matched to hbox: `jwt.pnk` `d1deca6c…`, `admit.pnk` `31166dc1…`),
`audit.sml`, `rung3.out`, `bridge.out`, plus this report. Build artifacts (`.hol/`, `.S`, `.o`,
`.dat`, `.ui`, `.uo`, `*.dumpedheap`) and any `ffi/*.o` are excluded.

## 7. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
for d in ~/hol-jwt-rung3 ~/hol-admit-rung3; do
  cd $d && Holmake cleanAll >/dev/null && Holmake && cat rung3.out && hol < audit.sml | grep '^AAA '
done
# theorem names:
#  backbones : jwt_rung3_native / admit_rung3_native
#  Link A    : jwt_decisioncore_refines_spec / admit_decisioncore_refines_spec
#  faithful  : jwtIf_faithful / admitIf_faithful
#  Link B    : pancake/proofs/pan_to_targetProofScript.sml  pan_to_target_compile_semantics
#  bootstrap : compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml  cake_compiled_thm
```

## 8. Bottom line

Two more deployed serve stages — S1 `jwtAdminStage`'s HS256 verify + alg-confusion gate (via `jwt`,
the `km = ku ∧ alg = 1` sig-equality/HS256 decision) and S8 `policyStage`'s declared-surface admit
gate (via `admit`, the `km = KM ∧ ku = KU` `deployDecisionOf`/`declared` decision for the single
declared `(GET,/api)` surface) — are now carried through the full Rung-3 native pattern:
native-compiled by the bootstrapped `cake` (deterministic, valid ELF x86-64, 1264 / 1270 code bytes),
reflected into HOL, and certified via `pan_to_target_compile_semantics` with the concrete native bytes
in the code slot and the four program-level conditions discharged — `jwt_rung3_native` /
`admit_rung3_native`, kernel-checked, `[oracles: DISK_THM] [axioms:]`, 0 axioms,
`cake_native_bootstrap` quarantined to the Layer-2 bytes equation. This lifts the deployed-14 backbone
count from **8 to 10** (S1/S3/S4/S5/S6/S7/S8/S10/S11/S13) — with the honest caveat that both are
loop-free **decision projections** over their fold outputs (the hashBytes fold bodies, jwt's crypto
FFI, and the base64/JSON parse loops are separate named residuals). Because both projections are
loop-free, their **Link-A decision core closes in full** (`…_decisioncore_refines_spec`), and the
certified cores now cover the first **variable-vs-variable** equality gate (`km = ku`) plus the nested
AND-with-`Skip` admission gate on real deployed JWT and policy code. The end-to-end machine→Lean-spec
refinement still does not fully close: it needs the whole-`main` FFI frame, the
`compile_prog↔compile_prog_max` packaging lemma, the runtime install package, and (for the full
S1/S8) the fold loops — named residuals, none the EVAL dead end and none leanc.

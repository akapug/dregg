# C22 REPORT — the FIRST full serve STAGE is composed end-to-end: `cacheEmptyStage`'s cache-key path (two `hashBytes` folds + the `isFresh` gate, sequenced) closes `spec → machine code` in ONE program

Gate A asked whether the mechanical folds of C21 (`mk_foldWrapper`: each fold =
one generator call + a ~16-line core) **compose** into a whole serve stage. C22
answers it on the real target: the deployed `cacheEmptyStage`
(`Reactor.Deploy.deployStagesFull2` stage 4). One Pancake program **sequences**
fold #1 (`hashBytes` over the method arena) → fold #2 (`hashBytes` over the target
arena, preserving fold #1's result) → the composed key → the C18-closed `isFresh`
scalar gate, and the composed end-to-end theorem `cacheKey_machine_code` is
**kernel-checked, `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats**, leanc out
of the TCB.

**Verdict up front.**
- **Is `cacheEmptyStage` closed END-TO-END?** **Yes.** `cacheKey_machine_code`
  (theory `cacheKeyGen`) states `machine_sem mc ffi ms ⊆ extend_with_resource_limit'
  … {Terminate Success (… report_vec (word_to_bytes (n2w (cacheServe method tgt
  age)) F) …)}` — every behaviour of the installed x64 code CakeML emits for the
  composed program is the single terminating trace reporting the composed Lean
  decision `cacheServe method tgt age`. **NON-vacuous**: `cacheServe` = keyOf's two
  `hashBytes` folds compared to the stored `(GET,/)` key AND `Meta.isFresh`
  (`age < 100`); the `verifyC22` audit machine-checks `4773603 = hashBytes "GET"`,
  `48 = hashBytes "/"`, and `cacheServe GET / 50 = 1` (fresh hit) / `… 200 = 0`
  (stale) / `POST / 50 = 0` (key miss). `cacheKeyProg` is the VERIFIED parser's
  output (`mk_linkB`), so leanc is out of the TCB; the two-fold + gate surgery
  fires against genuine parser subterms (`cacheKeyData` raises `Fail` otherwise).
- **New hand-lines for the composition?** The two fold **cores** cost ~16 lines
  each (C21's prediction held; and since `keyOf` uses `hashBytes` for BOTH arenas,
  the two cores are near-identical). But the **sequencing** is NOT cheap: the
  single-fold generator `mk_foldWrapper` **cannot** wrap a two-fold + gate spine
  (its peeler is hardwired to `Dec len; Dec acc; Dec i; Dec b; While; Store`), so
  the whole-program wrapper is a **bespoke ~347-line `MainRefine`** plus **~250
  lines of two-fold frame/clock machinery** (below). Only the Sem/Install/EndToEnd
  tail (~110 lines) reused verbatim in shape from the C21 template.
- **Bounded repeatable pattern toward the whole `deployStagesFull2` fold?** **Not
  yet — and the residual is named precisely.** The metatheory is all reused (C16
  fold schema, C21 `While_frame`, C18 `isFresh` gate); the forward-chain + backward
  wrap are **mechanical** (Dec/Annot/Seq trace threading + the fold-core/gate
  lemmas, no new metatheory). But they are hand-written per composed spine. The
  residual is exactly the move C21 made for the single fold: turn the bespoke
  `MainRefine` into a `mk_composedWrapper` generator that peels an N-fold + gate
  spine. Until it exists, each multi-fold stage pays the ~350-line wrapper.

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2 stdknl,
CakeML `ed31510b3`** — the exact tree C1–C21 used. **Dir:**
`docs/engine/probes/compiler/hol-c22/` (built on hbox `~/hol-c22`, full `Holmake`
exit 0, incl. the `verifyC22` audit theory). Sibling agents own `hol-c16..c21`
(done); C22 stayed out.

---

## 1. The composed target (grounded in drorb)

`cacheEmptyStage = Reactor.Stage.Cache.mkStage emptyCacheCfg`
(`Reactor/Deploy.lean:1442`). Its request-phase decision (`Config.onReq`,
`Reactor/Stage/Cache.lean:56`) on the branch `Reactor.Stage.Cache` proves fires:
serve the stored entry iff `Store.get?` finds it (exact-key match) **and**
`Meta.isFresh` holds. The key is `keyOf c = { method := hashBytes c.req.method,
uri := hashBytes c.req.target }` (`Cache.lean:118`), `hashBytes b = b.foldl (a x =>
a*257 + x + 1) 0` (`Cache.lean:115`). So the warm decision the stage computes is

```
cacheServe method tgt age =
  if  n2w (hashBytesN method) = 4773603w   (* = hashBytes "GET" *)
  ∧ n2w (hashBytesN tgt)    = 48w        (* = hashBytes "/"   *)
  ∧ age < 100                            (* §4.2 freshness lifetime *)
  then 1 (serve stored) else 0 (miss/stale continue)
```

Two `hashBytes` folds over distinct arenas + the RFC 9111 §4.2 freshness `<` gate —
the exact composition the deployed stage runs per request. Non-vacuous in method,
target, and age.

## 2. The composed Pancake program (`cachekey.pnk`, parser output)

```
fun main() {
  var ctrl = @base;  var base = ctrl + 64;
  @load_vec(ctrl, 32, base, 4096);
  var len = lds 1 ctrl;  var acc = 0; var i = 0; var b = 0;   // fold 1: method arena
  while i < len { b = ld8 (base+i); acc = acc*257 + b + 1; i = i+1; }
  var km = acc;                                                 // save fold-1 result
  base = ctrl + 2112;  len = lds 1 (ctrl+8);  acc = 0; i = 0; b = 0;  // retarget + fold 2
  while i < len { b = ld8 (base+i); acc = acc*257 + b + 1; i = i+1; }  // target arena
  var ku = acc;  var age = lds 1 (ctrl+16);  var dec = 0;
  if km == 4773603 { if ku == 48 { if age < 100 { dec = 1; } } }  // key-match ∧ isFresh
  st ctrl + 24, dec;  @report_vec(ctrl + 24, 8, ctrl, 8);  return 0;
}
```

Both `While` bodies are `hashBytes`, so **one fold-core theorem instantiates
twice** (`evaluate_cacheGate`'s two `While foldGuard cacheBodyA{1,2}` differ only in
their emitted location Annots). The two folds are threaded so fold #2 preserves
`km` (`While_frame`, C21); the gate reads both fold results + `age`.

## 3. The composed end-to-end theorem (verbatim `show_tags`, from `verifyC22`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ (compile_prog_max c mc cacheKeyProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   … the standard pan_to_target install package over cacheKeyProg … ∧
   pan_installed … ms (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
   cacheFFI method tgt age s ∧ (∃K. 0 < K ∧ LENGTH method + LENGTH tgt < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (cacheServe method tgt age)) F) rb])}
```

Reading it: under the install package and the **single** trusted FFI contract
`cacheFFI` (the `@load_vec` that stages both arenas + lengths + age, and the
`@report_vec` that emits the result word), every observable behaviour of the
installed machine code is the one terminating trace reporting `n2w (cacheServe
method tgt age)` — the composed keyOf/isFresh decision, faithful to leanc's
fixed-width codegen. `verifyC22` asserts DISK_THM-only, hyps = 0, non-vacuous
(mentions `machine_sem` / `Terminate Success` / `cacheServe`), and grounds the
constants.

## 4. What the composition cost — the honest quantification

With the folds mechanical (C21) and the gate reused (C18), sequencing them into one
stage cost:

| piece | lines | kind |
|---|---:|---|
| **the two fold cores** `cacheBodyA1_step`, `cacheBodyA2_step` | 2 × ~16 | per-fold input (C21-predicted; near-identical, both `hashBytes`) |
| **the gate** `cacheGate` + `evaluate_cacheGate` | ~50 | the C18 `isFresh` `<` gate, extended to the key-match `=` guards |
| **two-fold FRAME machinery** (`cacheKeyFrame`) | ~250 | **NEW for sequencing** (see below) |
| **bespoke whole-program `MainRefine`** (`cacheKeyGen` 49–396) | ~347 | **NEW — `mk_foldWrapper` cannot take the spine** |
| Sem + Install + EndToEnd tail | ~110 | reused verbatim in shape from C21 |
| `cacheFFI` / `cacheStaged` / surgery (`cacheKeyData`) | ~89 | the single trusted contract + parser-subterm surgery |

**Why the ~250-line two-fold frame is genuinely new** (`cacheKeyFrame`): a single
fold never needed it, but sequencing two does —
- **memory frame** (`cacheLoop1_mem`): `evaluate_invariants` gives memaddrs/be but
  NOT memory; fold #2's target-arena `memRel` must survive fold #1 (which stores
  nothing). Inlined clocked `While` induction.
- **clock lower bound** (`cacheLoop1_clock_bounded`): fold #1 **consumes** clock, so
  fold #2 must know enough remains — `s'.clock ≥ s.clock − LENGTH input`. A single
  fold's fuel was trivial; the two-fold budget is not.
- **fold-1 exit invariant** (`cacheLoop1_exit`): the loop-exit `foldInv` at
  `i = LENGTH input` hands `«i»/«b»/«len»/«base»` shapes, which the fold-2 reassigns'
  `is_valid_value` obligations need.

**Why the ~347-line `MainRefine` is bespoke.** `mk_foldWrapper`'s ML spine-peel is
hardwired to the single-fold spine (`Dec len; Dec acc; Dec i; Dec b; While; Store;
report; Return`). The composed spine is `… fold₁; Dec km; retarget base/len/acc/i/b;
fold₂; Dec ku; Dec age; Dec dec; GATE; Store; report; Return` — a different peel.
So the whole-program refinement (forward state-threading through ~25 spine nodes +
the backward Dec/Annot/Seq-trace wrap) is hand-written. It uses **no new
metatheory**: the two fold cores (`cacheLoop{1,2}_framed`), `While_frame`, the gate
lemma, and the c14Generic trace lemmas — exactly the C21/C18/C16 kit.

## 5. Is stage-composition a bounded, repeatable pattern? — the residual, named

**The metatheory IS bounded and reused.** Every ingredient the composition rests on
was proven once and reused: the C16 fold schema, the C21 `While_frame`, the C18
`isFresh` gate, and the two-fold frame/clock/exit lemmas added here (reusable by any
multi-fold stage). The forward-chain + backward wrap add **zero** lemmas — they only
thread the existing ones.

**But the WRAPPER is not yet a generator.** The bespoke `MainRefine` is the same
kind of hand stack C20 wrote for the single fold before C21 turned it into
`mk_foldWrapper`. The clean next step is a **`mk_composedWrapper`**: given a list of
fold cores + a scalar gate + the arena offsets, peel the `Dec…;fold;retarget;…;gate;
Store;report;Return` spine mechanically (the peel and the trace-wrap are fully
regular — this report's `MainRefine` is the template). With that generator, each of
the `deployStagesFull2` stages that composes multiple folds would cost only its
folds' ~16-line cores + its gate + one generator call — the C21 economics, extended
to composition. **That generator is the single residual between here and the whole
`deployStagesFull2` fold.**

Concretely, the honest scaling picture for the ~14 deployed stages:
- **scalar-branch stages** (redirect, rate, gzip-case) — C18, one-line each. Done.
- **single-fold value reports** (the cache-key hash alone, Content-Length) — C21,
  one `mk_foldWrapper` call + ~16-line core. Done.
- **composed stages** (this one: keyOf's two folds + the freshness gate; and by the
  same shape the header/CORS/traversal folds-of-folds) — proven closable end-to-end
  (this probe), but currently ~350 bespoke wrapper lines each until
  `mk_composedWrapper` lands.
- **general loops** (parse `While` [C13], DEFLATE, JWT FSM, CIDR walk) — still open,
  unchanged from C18's map.

## 6. Trust ledger (unchanged from C13–C21; none of it is leanc)

`cacheKey_machine_code` is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats
(`verifyC22` asserts this adversarially + non-vacuity + the grounded constants).
`DISK_THM` is the benign CakeML disk-export tag. The theorem rests only on: CakeML
backend correctness (Link B via `mk_linkB`), the C16 fold schema (reused verbatim
for both folds), the `hashBytes` Nat→word homomorphism (C19), the C18 `isFresh`
gate machinery, and the **single named FFI contract** `cacheFFI` (the `@load_vec` /
`@report_vec`). leanc is out: `cacheKeyProg` is the verified-parser output and every
fold/gate surgery fires against a real parser subterm.

## 7. Files (`docs/engine/probes/compiler/hol-c22/`, built on hbox `~/hol-c22`)

**New (the composed stage):**
- `cachekey.pnk` — the emitted two-fold + gate program.
- `cacheKeyCoreScript.sml` — the composed spec `cacheServe`; the two verbatim fold
  bodies `cacheBodyA{1,2}` + their ~16-line steps; the loop refinements (C16
  schema); the gate `cacheGate` + `evaluate_cacheGate` (C18 `<` + the key-match `=`
  guards).
- `cacheKeyFrameScript.sml` — the **two-fold frame/clock machinery**: memory frame,
  fold-1 exit `foldInv`, clock lower bound, the framed cores, and the reassign/store
  helpers.
- `cacheKeyDataScript.sml` — `cacheStaged` (both arenas + lengths + age), the single
  trusted `cacheFFI` contract, and the `cacheMainBody` ML surgery (three fold/gate
  fold-ins; raises if not a genuine parser subterm).
- `cacheKeyLinkBInstScript.sml` — Link B via `mk_linkB` (leanc out of the TCB).
- `cacheKeyGenScript.sml` — the **bespoke composed `MainRefine`** (forward chain +
  backward wrap for the two-fold + gate spine) + the C21-template Sem/Install/
  EndToEnd tail → `cacheKey_machine_code`.
- `verifyC22Script.sml` — the machine-checked audit (DISK_THM-only, hyps = 0,
  non-vacuous, grounds `4773603 = hashBytes "GET"`, `48 = hashBytes "/"`, and the
  `cacheServe` truth table).

**Carried verbatim from C21:** `hashCoreScript.sml` (fold body/loop),
`hashBytesLoopScript.sml` (`hashBytesN` + homomorphism), `foldLoopSchemaScript.sml`
(C16), `foldWrapCommonScript.sml` (`While_frame`), `c14GenericScript.sml`,
`panAutoScript.sml`, `panAutoLib.sml` (`mk_linkB`), `Holmakefile`.
Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0 (14 theories).

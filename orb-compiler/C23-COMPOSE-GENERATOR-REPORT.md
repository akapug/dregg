# C23 REPORT — the C22 bespoke composed-stage stack is now a REUSABLE GENERATOR: `mk_composedWrapper` reproduces C22 byte-identically AND closes a SECOND real composed stage from ~one generator call

Gate A asked whether C22's first full serve **stage** — `cacheEmptyStage`'s
cache-key path (two `hashBytes` folds threaded through one `main` + the C18
`isFresh` gate, `cacheKey_machine_code`) — could stop being a **bespoke** ~347-line
`MainRefine` + ~250-line two-fold frame machinery, and become a **generator** the
way C20→C21 turned the single-fold wrapper into `mk_foldWrapper`. **C23 lands it.**
`panComposedLib` now exports **`mk_composedWrapper`**: an ML generator (no new
metatheory — mechanical term/theorem construction) that peels a **two-fold +
scalar-gate** composed spine and emits the whole-program `MainRefine` + Sem +
Install + EndToEnd → `<prefix>_machine_code`. The inter-fold memory frame, clock
lower bounds, and fold-exit `foldInv` threading are handled by a **body-generic
frame engine** (`composedCommon`) — C22's per-body `cacheKeyFrame` (378 lines)
generalized to lemmas quantified over an arbitrary fold body.

**Verdict up front.**
- **Is `mk_composedWrapper` a real generator?** **Yes.** It reproduces C22's
  `cacheKey_machine_code` **byte-identically** — `cacheKeyRegen_machine_code`
  (theory `cacheKeyGen2`, a single generator call over the SAME parser-output
  `cacheMainBody`/`cacheKeyProg`) is **α-equal** to the bespoke theorem (machine
  checked in `verifyC23`), `[oracles: DISK_THM] [axioms: ]`, hyps = 0. The
  512-line bespoke `cacheKeyGenScript` collapses to a **34-line** spine record +
  `mk_composedWrapper` call.
- **Does it GENERALIZE — close a SECOND, different composed stage?** **Yes.**
  `admit_machine_code` (theory `admitGen`) closes a genuinely different deployed
  gate — the `(method, route)` **declared-surface admission** decision (drorb
  `Reactor/Deploy.lean` `policyStage` / `deployDecisionOf`): a **2-way AND** gate
  (no freshness `<` — structurally different from the C22 cache gate) over the two
  `hashBytes` folds `keyOf` uses. `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0
  cheats, **non-vacuous** (`verifyC23` grounds `admitDecide GET /api = 1`,
  `POST /api = 0`, `GET / = 0`, and `hashBytes "GET" = 4773603`,
  `hashBytes "/api" = 821282413`). leanc out of the TCB (`admitProg` is the verified
  parser's output on `admit.pnk`; the loop/gate surgery raises unless it fires on a
  genuine parser subterm).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C22 used. **Dir:**
`docs/engine/probes/compiler/hol-c23/` (built on hbox `~/hol-c23`, full `Holmake`
exit 0). Sibling agents own `hol-c16..c22` (done); C23 stayed out.

---

## 1. The two residuals C22 named, both landed

C22 §5 named the single residual between it and the whole `deployStagesFull2`
fold: **a `mk_composedWrapper` generator that peels an N-fold + gate spine.** That
residual had two independent parts; C23 lands both.

### 1a. The frame machinery → body-generic (`composedCommon`, 232 lines, once)

C22's `cacheKeyFrame` (378 lines) proved the two-fold frame/clock/exit lemmas
**per body** (`cacheBodyA1`/`cacheBodyA2`). `composedCommon` re-states each over an
**arbitrary** fold body `bdy` + accumulator `accf`, with the three body facts
(single-step / memory-preserving / ctrl-preserving) as antecedents:

| generic lemma | what C22 wrote per body | replaces |
|---|---|---|
| `loop_mem` | `cacheLoop1_mem` / `cacheLoop2_mem` | 2× inlined clocked inductions |
| `foldLoop_exit` | `cacheLoop1_exit(_bounded)` | 2× bounded inductions |
| `foldLoop_clock(_bounded)` | `cacheLoop{1,2}_clock(_bounded)` | 4× lemmas |
| **`loop_frame`** | `cacheLoop{1,2}_framed` | THE per-fold framed core |

`loop_frame` is the headline: any fold body whose single step advances `foldInv`
+ preserves memory + preserves `«ctrl»` gets its **whole** framed core (acc =
`FOLDL accf 0w …`, all exit shapes `base/len/i/b`, the memory/memaddrs/be frame,
the clock lower bound) from one instantiation. `frameGenDemo` proves this
**reproduces** C22's `cacheLoop1_framed` in **~15 lines** (the ~250-line per-body
`cacheKeyFrame` block collapses to the generic engine + a ~10-line homomorphism
rewrite).

### 1b. The whole-program wrapper → generator (`panComposedLib`, 548 lines, once)

`mk_composedWrapper` is the C22 bespoke stack turned into a function. Given the
spine tokens — two fold framed-cores + arena offsets + save vars, a scalar read,
the gate theorem, the result word, the parser-output `mainBody` + Link B — it
emits the four theories mechanically:

```
mk_composedWrapper
  { prefix, ffiName, ffiDef, ffiArgs, stagedDef, clockBound, arena0,
    fold0, fold1, scalars, decVar, gateName, gateThm, storeOff, resultWord,
    mainBodyName, mainBodyDef, progName, progDef, linkB, unfoldCore }
: { mainRefine, callMainRun, mainSemantics, semanticsDecls, machineCode }
```

The ML peel walks the composed spine (`Dec…; fold₁; Dec save₁; retarget
base/len/acc/i/b; fold₂; Dec save₂; Dec scalar; Dec dec; GATE; store; report;
Return`); the forward chain runs each fold's framed core + the retarget reassigns
+ the gate + the store/report oracle; the backward wrap threads the trace bottom-up
through ~40 spine nodes (`Dec_trace`/`Annot_trace`/`Seq_trace`). **No new
metatheory** — exactly the C22 hand tactics, parameterized. The `∃K` fuel
side-condition is discharged from a clean-context `exists_big` (the C21 pattern),
so there is no per-stage tactic hygiene.

## 2. REGRESSION — the generator reproduces C22 byte-identically

`cacheKeyGen2` is a **single `mk_composedWrapper` call** with the C22 cache spine
(fold₀ = `hashBytes` @ ctrl+64, fold₁ = `hashBytes` @ ctrl+2112, scalar `age` @
ctrl+16, `cacheGate`, result `n2w (cacheServe method tgt age)`), over the SAME
parser-output `cacheMainBody`/`cacheKeyProg`. `verifyC23` machine-checks:

```
aconv (concl cacheKey_machine_code) (concl cacheKeyRegen_machine_code) = true
```

— α-equal to the bespoke C22 theorem, `[oracles: DISK_THM] [axioms: ]`, hyps = 0.
The 512-line bespoke `cacheKeyGenScript` → the 34-line `cacheKeyGen2Script`.

## 3. SECOND STAGE — a genuinely different composed gate, generator-closed

The second stage is the `(method, route)` **declared-surface admission** gate
(`admit_machine_code`, theory `admitGen`), grounded in `Reactor/Deploy.lean`'s
`policyStage`/`deployDecisionOf`:

```
admitDecide method route =
  if  n2w (hashBytesN method) = 4773603w       (* hashBytes "GET"  *)
  ∧  n2w (hashBytesN route)  = 821282413w      (* hashBytes "/api" *)
  then 1 (admit) else 0 (refuse)
```

Verbatim `show_tags` (from `verifyC23`):

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … the standard pan_to_target install package over admitProg … ∧
    pan_installed … ) ∧ cacheFFI method tgt age s ∧
    (∃K. 0 < K ∧ LENGTH method + LENGTH tgt < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆ extend_with_resource_limit' …
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (admitDecide method tgt)) F) rb])}
```

**Genuinely different, not a re-run** (`verifyC23` asserts it): a **distinct
parser-output program** (`admitProg` on `admit.pnk`, distinct from `cacheKeyProg`);
a **structurally different gate** (2-way AND — one fewer branch, no scalar `<`); a
**different spec** (`admitDecide`, 2 arguments, no freshness); different constants
(`/api`). The two `hashBytes` folds are **reused verbatim** (drorb hashes keys and
routes with the same `hashBytes`) — `admit.pnk` keeps the fold code byte-identical
to `cachekey.pnk`, so `cacheBodyA1`/`cacheBodyA2` and their `cacheLoop{1,2}_framed`
cores are shared; the `cacheFFI`/`cacheStaged` contract is reused (identical
control-block layout).

## 4. What the second stage cost — the honest quantification

| piece | lines | kind |
|---|---:|---|
| the two fold cores + framed cores | **0** | REUSED (`cacheBodyA{1,2}` / `cacheLoop{1,2}_framed`) |
| `admitDecide` spec | 5 | the stage decision |
| `admitGate` def | 12 | the emitted 2-way `If` (extracted parser subterm) |
| **`evaluate_admitGate`** | **~30** | the ONE bespoke gate lemma (2 `Cases_on`, no `<`) |
| `admitData` mainBody surgery | ~30 | mechanical (reuses `cacheStaged`/`cacheFFI`) |
| Link B | **1** | one `mk_linkB` call |
| **whole-program wrapper (MainRefine+Sem+Install+EndToEnd)** | **0** | one `mk_composedWrapper` call |

Against C22's bespoke budget for the same wrapper — the ~347-line `MainRefine` +
~250-line frame machinery ≈ **~600 hand lines** — the second stage's wrapper is
**0**, and its only genuinely new *proof* is the **~30-line** gate lemma. The
answer to the charge ("does the 2nd multi-fold stage now cost ~cores-only + a
spine record, vs C22's ~600?") is **yes**: the ~600-line composed wrapper collapses
to a generator call; the per-stage cost is its (new) fold cores + its gate lemma +
one `mk_composedWrapper` call.

## 5. Is fan-out to the whole `deployStagesFull2` now bounded? — the residual, named

**Bounded, with a precisely-named residual.** Every composed stage now = its folds'
cores (each ~16-line step + a ~15-line `loop_frame` framed core) + its gate lemma +
**one** `mk_composedWrapper` call. Concretely for the ~14 deployed stages:

- **scalar-branch stages** (redirect, rate, gzip-case) — C18, one line each. Done.
- **single-fold value reports** (cache-key hash alone, Content-Length) — C21, one
  `mk_foldWrapper` call + a ~16-line core. Done.
- **composed fold-fold-gate stages** (this class: `cacheEmptyStage`'s key path
  [C22, now generated] and this `(method,route)` admission [C23]; by the same
  shape the header/CORS/traversal-of-folds gates) — **now one generator call +
  cores + gate**, no bespoke wrapper.
- **general loops** (parse `While` [C13], DEFLATE, JWT FSM, CIDR walk) — **still
  open**, unchanged from C18's map. This is the standing residual.

**Two honest caveats on `mk_composedWrapper`'s current reach:**
1. It peels the **two-fold + one-scalar + gate** spine (the shape both real stages
   here share; **N = 2 exercised**). A stage with a different fold count needs the
   ML peel loop extended over the fold list — mechanical (the forward per-fold work
   and backward node-walk are already regular), but not yet written for N ≠ 2.
2. The second stage **reuses** the `hashBytes` fold body. A stage over a *different*
   fold (e.g. the C21 Content-Length base-10 Horner, or the schema's byte-`sumBody`)
   pays its own ~16-line core step + a ~15-line `loop_frame` framed core — proven
   feasible by `frameGenDemo`, but each new fold body still needs those ~30 lines.

## 6. Trust ledger (unchanged from C13–C22; none of it is leanc)

Both `cacheKeyRegen_machine_code` and `admit_machine_code` are
`[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats (`verifyC23` asserts this
adversarially + non-vacuity + the grounded truth table + that the two stages are
genuinely distinct decisions over distinct programs). `DISK_THM` is the benign
CakeML disk-export tag. The theorems rest only on: CakeML backend correctness (Link
B via `mk_linkB`), the C16 fold schema + `hashBytes` homomorphism (reused), the
body-generic `composedCommon` frame engine (proven once), and the single named FFI
contract `cacheFFI` (`@load_vec` / `@report_vec`). `mk_composedWrapper` and
`mk_linkB` carry **no trust** — they only assemble kernel-checked proofs; the
generator writes zero axioms (`verifyC23`: `axioms = 0`).

## 7. Files (`docs/engine/probes/compiler/hol-c23/`, built on hbox `~/hol-c23`)

**The generator + generic engine (one-time infrastructure):**
- `composedCommonScript.sml` — the body-generic frame engine (`loop_mem`,
  `foldLoop_exit`, `foldLoop_clock`, **`loop_frame`**); generalizes C22's
  `cacheKeyFrame`.
- `panComposedLib.sml` — **`mk_composedMainRefine` + `mk_composedWrapper`** (the
  C22 bespoke composed stack turned into a generator).
- `frameGenDemoScript.sml` — proof that `loop_frame` reproduces `cacheLoop1_framed`
  in ~15 lines.

**Regression (the bespoke C22 stack becomes a generator call):**
- `cacheKeyGen2Script.sml` — the `mk_composedWrapper` call → `cacheKeyRegen_machine_code`
  (α-equal to C22's `cacheKey_machine_code`).

**Second composed stage (the generalization test):**
- `admit.pnk` — the emitted `(method,route)` admission program (2-way gate; folds
  byte-identical to `cachekey.pnk`).
- `admitCoreScript.sml` — `admitDecide` spec + `admitGate` + `evaluate_admitGate`.
- `admitDataScript.sml` — `admitMainBody` surgery (folds `cacheLoop{1,2}` + `admitGate`;
  reuses `cacheStaged`/`cacheFFI`).
- `admitLinkBInstScript.sml` — Link B (`mk_linkB` on `admit.pnk`).
- `admitGenScript.sml` — the `mk_composedWrapper` call → `admit_machine_code`.

**Audit + carried deps:**
- `verifyC23Script.sml` — the adversarial audit (α-equal regression; DISK_THM-only,
  hyps = 0, non-vacuous; distinct decisions/programs; the `admitDecide` truth table
  + stored constants; `loop_frame` non-vacuous).
- carried verbatim from C22: `cacheKeyCore/Frame/Data/LinkBInst`, `cacheKeyGen`
  (the bespoke, kept for the α-equality regression), `hashCore`, `hashBytesLoop`,
  `foldLoopSchema`, `foldWrapCommon`, `c14Generic`, `panAuto(Lib)`, `Holmakefile`.
- Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0.

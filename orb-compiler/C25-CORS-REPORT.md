# C25 REPORT — a THIRD deployed serve stage closed spec→machine-code by the C23 generator with NO spine adaptation: `deployCorsStage`'s `Cors.acaoValue` (Access-Control-Allow-Origin) decision, one `mk_composedWrapper` call + one new gate lemma

Gate A fan-out. C22 hand-wrote the first composed serve stage (`cacheEmptyStage`,
~600 bespoke wrapper lines); C23 turned that into the `mk_composedWrapper`
generator and closed a second stage (`policyStage` admission) from ~one generator
call + a ~30-line gate lemma. **C25 closes a THIRD, structurally different deployed
stage — `deployCorsStage` (stage 10 of `Reactor.Deploy.deployStagesFull2`, the
CORS `Access-Control-Allow-Origin` decision) — and answers the sharpest scaling
question: does `mk_composedWrapper` apply to a stage it was NOT tuned for?**
**Yes, DIRECTLY** — no ML peel extension, no new metatheory, no bespoke wrapper.
The CORS decision maps onto the generator's fixed **2-fold + scalar-gate** spine,
and the only genuinely new proof is a **~30-line gate lemma**.

**Verdict up front.**
- **Is `deployCorsStage` closed END-TO-END?** **Yes.** `cors_machine_code` (theory
  `corsGen`) states `machine_sem mc ffi ms ⊆ extend_with_resource_limit' …
  {Terminate Success (… report_vec (word_to_bytes (n2w (corsAllow wild origin
  allowed)) F) …)}` — every behaviour of the installed x64 code CakeML emits for
  the composed CORS program is the single terminating trace reporting the CORS
  allow/deny decision. **`[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats**
  (`verifyC25` asserts this adversarially). leanc out of the TCB: `corsProg` is the
  verified parser's output on `cors.pnk`; the fold/gate surgery raises unless it
  fires on a genuine parser subterm.
- **NON-vacuous, grounded on real origins?** **Yes.** `corsAllow` is the REAL
  `Cors.originAllowed corsPolicy` decision (`allowAnyOrigin ∨ allowedOrigins.contains
  o`) transported to the fold model, and the reported 1/0 bit is exactly
  `acaoValue`'s `some/none` (deployed `corsPolicy` has no credentials, no wildcard,
  so `acaoValue = if originAllowed then some o else none`). `verifyC25`
  machine-checks the decision over **three real origins** from drorb `Cors.lean`:
  - `corsAllow 0 app app = 1` — the allowlisted origin `https://app.example.com`,
    wildcard off → **ACAO echoed** (matches `Cors.origin_allowed_witness`).
  - `corsAllow 0 evil app = 0` — off-allowlist `https://evil.example.com`, wildcard
    off → **NO ACAO, the no-leak boundary** (matches `Cors.origin_denied_witness` /
    `cors_no_leak`).
  - `corsAllow 1 evil app = 1` — `allowAnyOrigin` set → allow regardless.
  and that the two origins' hashes **genuinely differ as word64**
  (`app-hash = evil-hash? F`) — the deny is a real mismatch, not a hash collision.
- **Did the generator apply cleanly, or need a spine adaptation?** **Applied
  DIRECTLY — no adaptation.** `mk_composedWrapper` ran with the CORS spine record
  and produced `MainRefine + Sem + Install + EndToEnd → cors_machine_code` with
  **zero** wrapper hand-lines. The ML peel was NOT extended and NO fold/gate schema
  lemma was added — the CORS decision fits the existing 2-fold + one-scalar + gate
  shape exactly (see §2).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2 stdknl,
CakeML `ed31510b3`** — the exact tree C1–C24 used. **Dir:**
`docs/engine/probes/compiler/hol-c25/` (built on hbox `~/hol-c25`, full `Holmake`
exit 0, all 20 theories incl. the `verifyC25` audit). Sibling agents own
`hol-c16..c24`; C25 owns a NEW `hol-c25/` and stayed out of theirs.

---

## 1. The target (grounded in drorb)

`deployCorsStage` (`Reactor/Deploy.lean:1463`) is stage 10 of
`deployStagesFull2`. Its response-phase transform runs the REAL `Cors.acaoValue`
over `Reactor.Stage.Cors.corsPolicy` on the request's canonical-lowercase `origin`
header and, iff the origin is permitted, stamps `Access-Control-Allow-Origin`:

```lean
onResponse := fun c b =>
  match Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
  | some v => b.addHeader (acaoName, strBytes v)
  | none   => b
```

The decision (`Cors.lean:76,83`) is a **single-token allowlist membership**:

```lean
originAllowed p o = p.allowAnyOrigin || p.allowedOrigins.contains o
acaoValue p o     = if originAllowed p o then (… no creds/wildcard …) some o else none
```

and the deployed `corsPolicy` (`Stage/Cors.lean:62`) is
`allowedOrigins = ["https://app.example.com"]`, `allowAnyOrigin = false`,
`allowCredentials = false`. So the deployed decision is:

> ACAO granted **iff** `allowAnyOrigin` **or** the request origin equals the single
> allowed origin. A disallowed origin gets **no** ACAO (the CORS security
> boundary — `cors_no_leak`).

**Spine shape.** This is **not** a general loop — it is exactly a **membership
gate over byte tokens**, the same shape C22/C23 close: hash the request origin,
hash the allowed origin, compare. Concretely it maps onto the generator's fixed
`(2-fold + one-scalar + gate)` spine:

| generator slot | CORS meaning |
|---|---|
| fold #0 (arena @ctrl+64) | `hashBytes` of the **request** origin |
| fold #1 (arena @ctrl+2112) | `hashBytes` of the **policy** allowed origin |
| scalar (@ctrl+16) | the `allowAnyOrigin` **wildcard** flag |
| gate | `dec = 1 iff (wild ≠ 0) ∨ (hash(origin) = hash(allowed))` = `originAllowed` |
| report | the ACAO grant bit (`acaoValue`'s some/none) |

Modeling the allowlist entry as a **second runtime arena** (fold #1) rather than a
hardcoded constant is what makes CORS a genuine 2-fold decision (as opposed to a
1-fold "hash = literal" test), and it fits the generator's minimum arity with
room to spare. Using the scalar as the `allowAnyOrigin` flag makes the gate the
**full** `originAllowed` (wildcard OR exact-match), not a stripped deployed
special case — the wildcard branch is exercised in the audit (`corsAllow 1 … = 1`).

## 2. Did the generator apply directly? — YES, no spine adaptation

C23 §5 named two honest caveats on `mk_composedWrapper`'s reach: (1) it peels the
**2-fold** spine, a different fold count needs the ML peel extended; (2) a
different fold *body* costs its own core. **CORS hits neither.** It is a 2-fold
decision, and both folds are `hashBytes` (drorb hashes origin tokens with the same
`hashBytes` it hashes keys/routes), so `cacheBodyA1/A2` and `cacheLoop1/2_framed`
are **reused verbatim**. The generator call is a plain spine record:

```
mk_composedWrapper
  { prefix="cors", ffiName="cacheFFI", …, clockBound="LENGTH origin + LENGTH allowed",
    fold0={ arenaOff="64w",  …, loopName="cacheLoop1", framed=cacheLoop1_framed, saveVar="km" },
    fold1={ arenaOff="2112w",…, loopName="cacheLoop2", framed=cacheLoop2_framed, saveVar="ku" },
    scalars=[ { off="16w", var="wild", valWord="n2w wild" } ],
    gateName="corsGate", gateThm=evaluate_corsGate,
    resultWord="n2w (corsAllow wild origin allowed)",
    mainBodyName="corsMainBody", progName="corsProg", linkB=corsProg_linkB, … }
```

The generator's backward wrap already peels the leading statement-`Annot` before
the gate via `Annot_Seq` (the gate slot is `Seq (Annot …) corsGate`), so the
two-branch If/else gate slots in with **no** peel change. The ML peel loop was
**not** touched; **no** new fold/gate schema lemma was added.

**One authoring constraint worth naming** (not a proof cost): the fold cores are
reused by `Term.subst`, and `cacheBodyA1/A2` carry the emitted **source-location
Annots** from `cachekey.pnk`. So `cors.pnk` lines 16–40 (through `var ku = acc`)
are kept **byte-identical** to `admit.pnk`, landing the two `while` bodies on the
exact lines (25–27, 36–38) whose Annots `cacheBodyA1/A2` bake in — otherwise the
fold surgery raises `"cacheLoop1 surgery did not fire"`. The gate's own Annots
(lines 44/46/47) were read off the parser output and pinned into `corsGate_def`.

## 3. What the third stage cost — the honest quantification

| piece | lines | kind |
|---|---:|---|
| the two `hashBytes` fold cores + framed cores | **0** | REUSED (`cacheBodyA{1,2}` / `cacheLoop{1,2}_framed`) |
| `cacheStaged` / `cacheFFI` contract | **0** | REUSED verbatim (identical control-block layout) |
| `corsAllow` spec | 6 | the CORS ACAO decision (= `originAllowed`) |
| `corsGate` def | 10 | the emitted If/else gate (extracted parser subterm) |
| **`evaluate_corsGate`** | **~30** | the ONE genuinely-new proof (wildcard-`≠`/match-`=` gate) |
| `corsData` mainBody surgery | ~30 | mechanical (reuses `cacheStaged`/`cacheFFI`) |
| Link B (`corsLinkBInst`) | **1** | one `mk_linkB` call |
| **whole-program wrapper** (MainRefine+Sem+Install+EndToEnd) | **0** | one `mk_composedWrapper` call |
| `verifyC25` audit | ~70 | assertions, not a hand proof |

**Total genuinely-new PROOF hand-lines: ~30** (the gate lemma). Everything else is
one spec, one extracted gate def, mechanical surgery, and two one-line generator
calls. Against C22's ~600-line bespoke composed wrapper for the *same shape*, the
CORS stage's wrapper is **0** and its new proof is **~30 lines** — the C23
economics hold for a third, structurally distinct stage.

## 4. The theorem (verbatim `show_tags`, from `verifyC25`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … the standard pan_to_target install package over corsProg … ∧
    pan_installed … ) ∧
  cacheFFI origin allowed wild s ∧
  (∃K. 0 < K ∧ LENGTH origin + LENGTH allowed < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (corsAllow wild origin allowed)) F) rb])}
```

Under the install package and the single trusted FFI contract `cacheFFI` (the
`@load_vec` that stages both origin arenas + the wildcard flag, and the
`@report_vec` that emits the result word), every observable behaviour of the
installed machine code is the one terminating trace reporting `n2w (corsAllow wild
origin allowed)` — the deployed CORS allow/deny decision, faithful to leanc's
fixed-width codegen.

**Audit output (machine-checked, `verifyC25`):**
```
hashBytes "https://app.example.com"  = 11005360001704010755817887174657733517770475365932330666
hashBytes "https://evil.example.com" = 2828377520437930764250866875410321771895016713035353904922
app-hash = evil-hash (word64)? F
corsAllow  app  vs app  (wild=0, allowed)    = 1
corsAllow  evil vs app  (wild=0, disallowed) = 0
corsAllow  evil vs app  (wild=1, wildcard)   = 1
@@ verifyC25 axioms = 0
@@@ C25 AUDIT PASSED @@@
```

## 5. Trust ledger (unchanged from C13–C24; none of it is leanc)

`cors_machine_code` is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats
(`verifyC25` asserts this adversarially + non-vacuity + the grounded truth table +
the no-collision check + distinctness from `cacheServe`/`admitDecide`). `DISK_THM`
is the benign CakeML disk-export tag. The theorem rests only on: CakeML backend
correctness (Link B via `mk_linkB`), the C16 fold schema + `hashBytes` homomorphism
(reused), the body-generic `composedCommon` frame engine (reused), and the single
named FFI contract `cacheFFI`. `mk_composedWrapper`/`mk_linkB` carry no trust —
they assemble kernel-checked proofs; the generator writes zero axioms
(`verifyC25`: `axioms = 0`). leanc is out: `corsProg` is the verified-parser output
on `cors.pnk`, and the fold/gate surgery raises unless it fires on a real parser
subterm.

## 6. Where this leaves the `deployStagesFull2` fan-out

CORS is the **third** composed fold-fold-gate stage closed (after `cacheEmptyStage`
[C22, regenerated C23] and `policyStage` [C23]) and the **first** closed with the
generator applied with **zero** adaptation to a stage it was not tuned for. The
composed-stage class is now bounded: each such stage = its (reused-or-new) fold
cores + one gate lemma + one `mk_composedWrapper` call. The standing residual is
unchanged and named as in C18/C23: **general loops** (parse `While` [C13], DEFLATE,
JWT FSM, CIDR walk) still need per-loop metatheory. `mk_composedWrapper`'s N=2 fold
peel is now exercised on three distinct stages; a stage with N≠2 folds still needs
the mechanical peel extension C23 named (not triggered by CORS).

## 7. Files (`docs/engine/probes/compiler/hol-c25/`, built on hbox `~/hol-c25`)

**New (the CORS stage):**
- `cors.pnk` — the emitted 2-fold + wildcard/match-gate program (lines 16–40
  byte-identical to `admit.pnk` so the two `hashBytes` folds are reused verbatim).
- `corsCoreScript.sml` — `corsAllow` spec (= `originAllowed`), `corsGate` (the
  extracted If/else gate) + `corsGate_noFFI` + the ONE new gate lemma
  `evaluate_corsGate`.
- `corsDataScript.sml` — `corsMainBody` surgery (folds `cacheLoop1/2` + `corsGate`;
  reuses `cacheStaged`/`cacheFFI`; raises if a core is not a genuine parser subterm).
- `corsLinkBInstScript.sml` — Link B (`mk_linkB` on `cors.pnk`); leanc out of TCB.
- `corsGenScript.sml` — the single `mk_composedWrapper` call → `cors_machine_code`.
- `verifyC25Script.sml` — the adversarial audit (DISK_THM-only, hyps = 0,
  non-vacuous; distinct decision/program; `corsAllow` truth table over real
  origins; the no-collision word64 check).

**Carried verbatim as deps** (from C22/C23): `cacheKeyCore/Frame/Data/LinkBInst`,
`admit*`, `composedCommon`, `panComposedLib`, `hashCore`, `hashBytesLoop`,
`foldLoopSchema`, `foldWrapCommon`, `c14Generic`, `panAuto(Lib)`, `Holmakefile`,
and the C22/C23 regression + audit theories. Build:
`CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0 (all theories).

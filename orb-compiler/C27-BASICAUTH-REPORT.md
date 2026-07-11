# C27 REPORT — the Basic-auth gate's `verify` compare closed spec→machine-code by the C23 generator with NO spine adaptation: `basicStage`'s credential-equality decision, one `mk_composedWrapper` call + one new (single-equality) gate lemma

Gate A fan-out — decision seam. C22 hand-wrote the first composed serve stage
(~600 bespoke wrapper lines); C23 turned it into the `mk_composedWrapper`
generator (admit gate) and C25 showed it applies **directly** to a stage it was
not tuned for (CORS). **C27 closes stage 2 of `Reactor.Deploy.deployStagesFull2`,
the HTTP Basic-auth gate — `Reactor.Stage.BasicAuth.basicStage` — at its one trust
boundary, `verify`.** Like admit/cors it is a fold-fold + gate decision; the gate
is the **plainest in the family** (a single hash-equality), and the generator
applied with **zero** adaptation.

**Verdict up front.**
- **Is `basicStage` closed END-TO-END (at the compare gate)?** **Yes.**
  `basic_machine_code` (theory `basicGen`) states `machine_sem mc ffi ms ⊆
  extend_with_resource_limit' … {Terminate Success (… report_vec (word_to_bytes
  (n2w (basicAdmit cred configured)) F) …)}` — every behaviour of the installed
  x64 code CakeML emits for the composed Basic-auth program is the single
  terminating trace reporting the credential-compare decision.
  **`[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats** (`verifyC27` asserts
  this adversarially). leanc out of the TCB: `basicProg` is the verified parser's
  output on `basic.pnk`; the fold/gate surgery raises unless it fires on a genuine
  parser subterm.
- **NON-vacuous, grounded on real credentials?** **Yes.** `basicAdmit cred
  configured = 1 iff hash(cred) = hash(configured)` is the deployed
  `verify user pass = (user == "admin" && pass == "secret")` transported to the
  fold model (hash-equality of the presented vs configured credential arenas, as
  C22/C23/C25 model key/route/origin match). `verifyC27` machine-checks the
  decision over **three real credential inputs** against the deployed
  `stageConfig` credential `"admin:secret"` (drorb `Reactor/Stage/BasicAuth.lean`):
  - `basicAdmit "admin:secret" "admin:secret" = 1` — the **correct** credential →
    `verify` T → `.ok` → **admit** (the request reaches the handler).
  - `basicAdmit "admin:wrong" "admin:secret" = 0` — a **wrong** credential →
    `verify` F → `challenge` → **401** (`basic_rejects_bad_cred`).
  - `basicAdmit [] "admin:secret" = 0` — an **absent** credential (no
    `Authorization` header) → `challenge` → **401** (`basic_no_creds_challenges`).
  and that the wrong / empty credential hashes **genuinely differ** from the
  configured hash as word64 — the reject is a real mismatch, not a hash collision.
- **Did the generator apply cleanly, or need a spine adaptation?** **Applied
  DIRECTLY — no adaptation.** `mk_composedWrapper` ran with the Basic-auth spine
  record and produced `MainRefine + Sem + Install + EndToEnd → basic_machine_code`
  with **zero** wrapper hand-lines. The ML peel was NOT extended and NO fold/gate
  schema lemma was added — the `verify` decision fits the existing 2-fold +
  one-scalar + gate shape exactly (see §2). base64 is a general loop and is
  **out of scope** (named residual, §3).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C26 used. **Dir:**
`docs/engine/probes/compiler/hol-c27/` (built on hbox `~/hol-c27`, full `Holmake`
exit 0, all 15 theories incl. the `verifyC27` audit). Sibling agents own
`hol-c16..c26`; C27 owns a NEW `hol-c27/` and stayed out of theirs.

---

## 1. The target (grounded in drorb)

`basicStage` (`Reactor/Stage/BasicAuth.lean`) is stage 2 of `deployStagesFull2`
(`Reactor/Deploy.lean:1498`). Its request-phase transform, on a `/private*`
target, runs the REAL `BasicAuth.authenticate stageConfig` over the request's
`Authorization` header; an `.ok` passes (`.continue`), a `.challenge`
short-circuits with a `401` carrying the RFC 7617 realm challenge (`.respond`):

```lean
onRequest := fun c =>
  if isProtectedPath c.req then
    match decision c with            -- decision = BasicAuth.authenticate stageConfig (toBasicReq c)
    | .ok _          => .continue c
    | .challenge www => .respond (basicUnauthorized www)
  else .continue c
```

`authenticate` (`BasicAuth.lean:115`) is a decode-then-compare chain:

```lean
authenticate cfg req =
  match req.authorization with
  | none      => challenge
  | some v    => match cfg.parseBasic v with          -- Basic scheme match (RFC 7617 §2)
    | none    => challenge
    | some tok => match cfg.decodeUserPass tok with    -- base64 decode + colon split (RFC 4648 §4)
      | none  => challenge
      | some (user, pass) => if cfg.verify user pass then .ok user else challenge
```

and the deployed `stageConfig` supplies `verify user pass = (user == "admin" &&
pass == "secret")` — the file's own docstring names this **"the one trust
boundary"** (`decodeUserPass`/`parseBasic` are the two *decode* boundaries). So
the security-relevant decision — the one the gate's admit/reject theorems
(`basic_rejects_bad_cred`, `basic_no_creds_challenges`) hinge on — is:

> **admit iff the decoded credential equals the configured `"admin:secret"`.**

**Spine shape.** This is the same **membership/equality gate over byte tokens**
that C22/C23/C25 close, mapped onto the generator's fixed `(2-fold + one-scalar +
gate)` spine:

| generator slot | Basic-auth meaning |
|---|---|
| fold #0 (arena @ctrl+64)   | `hashBytes` of the **presented** (decoded) credential |
| fold #1 (arena @ctrl+2112) | `hashBytes` of the **configured** credential `"admin:secret"` |
| scalar (@ctrl+16)          | **staged but unused** by this gate (as C23 admit's `age`) |
| gate                       | `dec = 1 iff hash(presented) = hash(configured)` = `verify` |
| report                     | the admit bit (`.ok`/`challenge`) |

Modeling the configured credential as a **second runtime arena** (fold #1, not a
hardcoded literal) is faithful — the credential is runtime config — and gives a
genuine 2-fold decision. `verify`'s gate is a **single** hash-equality: the
plainest gate in the family (C22 had a freshness `<`, C23 a 2-way AND, C25 a
wildcard OR-match).

## 2. Did the generator apply directly? — YES, no spine adaptation

C23 §5 named two honest caveats on `mk_composedWrapper`'s reach: (1) it peels the
**2-fold** spine — a different fold count needs the ML peel extended; (2) a
different fold *body* costs its own core. **Basic-auth hits neither.** It is a
2-fold decision, and both folds are `hashBytes` (the presented and configured
credentials are hashed with the same `hashBytes` C22–C25 hash keys/routes/origins
with), so `cacheBodyA1/A2` and `cacheLoop1/2_framed` are **reused verbatim**. The
generator call is a plain spine record (`basicGenScript.sml`):

```
mk_composedWrapper
  { prefix="basic", ffiName="cacheFFI", …,
    clockBound="LENGTH cred + LENGTH configured",
    fold0={ arenaOff="64w",  …, accWord="n2w (hashBytesN cred)",       saveVar="km" },
    fold1={ arenaOff="2112w",…, accWord="n2w (hashBytesN configured)", saveVar="ku" },
    scalars=[ { off="16w", var="pad", valWord="n2w pad" } ],   (* staged, unused — like admit's age *)
    gateName="basicGate", gateThm=evaluate_basicGate,
    resultWord="n2w (basicAdmit cred configured)",
    mainBodyName="basicMainBody", progName="basicProg", linkB=basicProg_linkB, … }
```

The ML peel loop was **not** touched; **no** new fold/gate schema lemma was added.
Because the gate is a single `If`, `basicGate_def` is the shortest gate def in the
family, and `evaluate_basicGate` is the shortest gate lemma (one `Cases_on` on the
hash-equality). The arena layout is kept byte-identical to `admit.pnk` (lines
16–40, the two `while` bodies at 25–27/36–38 whose Annots `cacheBodyA1/A2` bake
in), so the two folds are reused by `Term.subst` with no re-proof; the gate's own
Annot (`dec = 1` at line 44) was read off the parser output and pinned into
`basicGate_def`.

## 3. The residual named honestly — base64 decode is a general loop, out of scope

The task flagged the sharp question: is base64 decode a `hashBytes` fold, or a
different shape? **It is a genuinely different — and harder — loop, and it is NOT
closed here.** `BasicAuth.b64Decode` folds `emitStep` over the sextets:

```lean
emitStep (acc, nbits, out) v =
  let acc := acc*64 + v; let nbits := nbits + 6 in
  if nbits ≥ 8 then (acc % 2^(nbits-8), nbits-8, out ++ [byte]) else (acc, nbits, out)
```

This is a **stateful bit-buffer transducer**: it carries `(acc, nbits)` and emits
a **variable-length** byte list (0 or 1 byte per sextet), preceded by `mapM
b64Char` (a 5-way alphabet branch that short-circuits on a non-alphabet char).
That is **not** the `hashBytes` scalar fold (`acc = acc*257 + b + 1`) the
generator peels — closing it to machine code would need its own emit-buffer loop
invariant, in the **general-loop** residual class C13/C18/C23 named (parse
`While`, DEFLATE, JWT FSM, CIDR walk). So C27 closes the **compare gate** — the
one trust boundary — taking the **decoded credential bytes** as the machine input
arena. This is the same faithful decomposition C25 used (CORS takes the
canonical-lowercase origin as input; the header canonicalization is upstream): the
base64 decode + `Basic` scheme match are the **upstream decode boundaries**
(`parseBasic`/`decodeUserPass`), which `BasicAuth.lean` itself separates from
`verify`. **Residual: base64-decode + scheme-parse (a general emit-buffer loop) —
reachable only with per-loop metatheory, not `mk_composedWrapper`.**

## 4. What the stage cost — the honest quantification

| piece | lines | kind |
|---|---:|---|
| the two `hashBytes` fold cores + framed cores | **0** | REUSED (`cacheBodyA{1,2}` / `cacheLoop{1,2}_framed`) |
| `cacheStaged` / `cacheFFI` contract | **0** | REUSED verbatim (identical control-block layout) |
| `basicAdmit` spec (= `verify`) | 4 | the credential-equality decision |
| `basicGate` def | 7 | the emitted single-`If` gate (extracted parser subterm) |
| **`evaluate_basicGate`** | **22** | the ONE genuinely-new proof (single hash-equality gate) |
| `basicData` mainBody surgery | ~30 | mechanical (reuses `cacheStaged`/`cacheFFI`) |
| Link B (`basicLinkBInst`) | **1** | one `mk_linkB` call |
| **whole-program wrapper** (MainRefine+Sem+Install+EndToEnd) | **0** | one `mk_composedWrapper` call |
| `verifyC27` audit | ~80 | assertions, not a hand proof |

**Total genuinely-new PROOF hand-lines: ~22** (the gate lemma — the smallest in
the C22–C27 family, because `verify` is a single equality). Everything else is one
spec, one extracted gate def, mechanical surgery, and two one-line generator
calls. The C23 economics hold for a fourth, distinct stage.

## 5. The theorem (from `verifyC27`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … the standard pan_to_target install package over basicProg … ∧
    pan_installed … ) ∧
  cacheFFI cred configured pad s ∧
  (∃K. 0 < K ∧ LENGTH cred + LENGTH configured < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (basicAdmit cred configured)) F) rb])}
```

Under the install package and the single trusted FFI contract `cacheFFI` (the
`@load_vec` that stages both credential arenas + the scalar, and the `@report_vec`
that emits the result word), every observable behaviour of the installed machine
code is the one terminating trace reporting `n2w (basicAdmit cred configured)` —
the deployed Basic-auth `verify` decision, faithful to leanc's fixed-width codegen.

**Audit output (machine-checked, `verifyC27`, green at [15/15]):**
```
basic_machine_code TAGS: [oracles: DISK_THM] [axioms: ]   (hyps = 0, axioms = 0)

hashBytes "admin:secret" = 31786003032176536072907659733   (0x66B4C3F51B17C75E6E1419D5)
hashBytes "admin:wrong"  = 123680945650492375931683963     (0x664E757F9B7C4F30A6047B)
wrong-hash = configured-hash (word64)? F      (0x664E75… ≠ 0x66B4C3… — real mismatch)
empty-hash = configured-hash (word64)? F      (0w        ≠ 0x66B4C3… — real mismatch)

basicAdmit  admin:secret (correct)   = 1      (verify T -> .ok -> admit)
basicAdmit  admin:wrong  (wrong)     = 0      (verify F -> challenge -> 401)
basicAdmit  (empty)      (absent)    = 0      (no creds -> challenge -> 401)

@@ verifyC27 axioms = 0
@@@ C27 AUDIT PASSED @@@
```
(Holmake captures theory stdout on success; every `assert` above is machine-checked
— had any failed, `verifyC27` would have raised `C27 AUDIT FAILED` and reddened the
build. All 15 theories built, `Holmake` exit 0.)

## 6. Trust ledger (unchanged from C13–C26; none of it is leanc)

`basic_machine_code` is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats
(`verifyC27` asserts this adversarially + non-vacuity + the grounded truth table +
the no-collision check + distinctness from `cacheServe`/`admitDecide`/`corsAllow`).
`DISK_THM` is the benign CakeML disk-export tag. The theorem rests only on: CakeML
backend correctness (Link B via `mk_linkB`), the C16 fold schema + `hashBytes`
homomorphism (reused), the body-generic `composedCommon` frame engine (reused),
and the single named FFI contract `cacheFFI`. `mk_composedWrapper`/`mk_linkB` carry
no trust — they assemble kernel-checked proofs; the generator writes zero axioms
(`verifyC27`: `axioms = 0`). leanc is out: `basicProg` is the verified-parser
output on `basic.pnk`, and the fold/gate surgery raises unless it fires on a real
parser subterm.

## 7. Where this leaves the `deployStagesFull2` fan-out

Basic-auth is the **fourth** composed fold-fold-gate stage closed (after
`cacheEmptyStage` [C22/C23], `policyStage` [C23], `deployCorsStage` [C25]) and the
**second** closed with the generator applied with **zero** adaptation. The
composed-stage class remains bounded: each such stage = its (reused-or-new) fold
cores + one gate lemma + one `mk_composedWrapper` call, ~20–30 new proof lines.
The standing residual is unchanged and now **sharpened by a concrete instance**:
**general loops** — and Basic-auth's own **base64 decode** (`emitStep`, an
emit-buffer transducer) is a fresh, named member of that class, requiring per-loop
metatheory the generator does not supply. C27 closes the stage's **trust boundary**
(`verify`); the decode boundary is the named frontier.

## 8. Files (`docs/engine/probes/compiler/hol-c27/`, built on hbox `~/hol-c27`)

**New (the Basic-auth stage):**
- `basic.pnk` — the emitted 2-fold + single-equality-gate program (lines 16–40
  byte-identical to `admit.pnk` so the two `hashBytes` folds are reused verbatim).
- `basicCoreScript.sml` — `basicAdmit` spec (= `verify`), `basicGate` (the
  extracted single-`If` gate) + `basicGate_noFFI` + the ONE new gate lemma
  `evaluate_basicGate`.
- `basicDataScript.sml` — `basicMainBody` surgery (folds `cacheLoop1/2` +
  `basicGate`; reuses `cacheStaged`/`cacheFFI`; raises if a core is not a genuine
  parser subterm).
- `basicLinkBInstScript.sml` — Link B (`mk_linkB` on `basic.pnk`); leanc out of TCB.
- `basicGenScript.sml` — the single `mk_composedWrapper` call → `basic_machine_code`.
- `verifyC27Script.sml` — the adversarial audit (DISK_THM-only, hyps = 0,
  non-vacuous; distinct decision/program; `basicAdmit` truth table over real
  correct/wrong/absent credentials; the no-collision word64 checks).

**Carried verbatim as deps** (from C22/C23/C25): `cacheKeyCore/Frame/LinkBInst/Data`,
`composedCommon`, `panComposedLib`, `hashBytesLoop`, `foldLoopSchema`,
`foldWrapCommon`, `c14Generic`, `panAuto(Lib)`, `cachekey.pnk`, `Holmakefile`.
Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0 (all 15 theories).

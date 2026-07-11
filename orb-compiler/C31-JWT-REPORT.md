# C31 REPORT — the deployed HS256 JWT admin gate's sig-verify + alg-confusion decision closed spec→machine-code by the C23 generator with NO spine adaptation: `jwtAdminStage`'s `afterKey` HS256 decision, one `mk_composedWrapper` call + one new (sig-equality ∧ alg) gate lemma

Gate A fan-out — the LAST deployed DECISION stage. C22 hand-wrote the first
composed serve stage (~600 bespoke wrapper lines); C23 turned it into the
`mk_composedWrapper` generator (admit gate); C25/C27 showed it applies **directly**
to stages it was not tuned for (CORS, Basic-auth). **C31 closes stage 1 of
`Reactor.Deploy.deployStagesFull2`, the HS256 JWT admin gate — `jwtAdminStage` →
`Reactor.Stage.Jwt.jwtStage` → `Jwt.authenticate`/`afterKey` — at its signature
trust boundary (the HMAC compare) conjoined with its alg-confusion gate.** With
this stage every deployed DECISION stage in `deployStagesFull2` is closed.

**Verdict up front.**
- **Is the `jwtAdmin` decision gate closed END-TO-END?** **Yes.**
  `jwt_machine_code` (theory `jwtGen`) states `machine_sem mc ffi ms ⊆
  extend_with_resource_limit' … {Terminate Success (… report_vec (word_to_bytes
  (n2w (jwtAdmit digest sig alg)) F) …)}` — every behaviour of the installed x64
  code CakeML emits for the composed JWT program is the single terminating trace
  reporting the sig-verify+alg admit decision. **`[oracles: DISK_THM] [axioms: ]`,
  hyps = 0, 0 cheats** (`verifyC31` asserts this adversarially). leanc out of the
  TCB: `jwtProg` is the verified parser's output on `jwt.pnk`; the fold/gate surgery
  raises unless it fires on a genuine parser subterm.
- **NON-vacuous, grounded on real inputs incl. the alg-confusion-rejected case?**
  **Yes.** `jwtAdmit digest sig alg = 1 iff hash(digest) = hash(sig) ∧ alg = HS256`
  is the deployed `afterKey` HS256 decision — `cfg.sigValid` (`verifyHmac`) T
  **and** `alg = key.alg ∧ alg ≠ none` — transported to the fold model.
  `verifyC31` machine-checks the decision over **four real byte inputs** (a 32-byte
  HMAC-SHA256 digest, the presented signature, the declared alg tag):
  - `jwtAdmit digest validSig 1 = 1` — a **valid** signed HS256 token
    (`validSig == digest`, alg = HS256) → `verifyHmac` T ∧ alg gate → **admit**
    (the request reaches the `/admin` handler).
  - `jwtAdmit digest badSig 1 = 0` — a **forged** signature
    (`badSig ≠ digest`) → `verifyHmac` F → `reject .badSignature` → **401**.
  - `jwtAdmit digest validSig 0 = 0` — **`alg = none`** (a genuinely-valid sig, but
    the unsecured algorithm) → `reject .algNone` → **401**.
  - `jwtAdmit digest validSig 2 = 0` — **algorithm confusion** (`alg = RS256 ≠
    key.alg = HS256`, with a **genuinely-valid** signature) → `reject .algMismatch`
    → **401**. This is `Jwt.jwt_alg_confusion_safe` grounded: an RS256-declared token
    is refused on the HS256 key path **even with a colliding signature**.
  and that `validSig`'s hash **genuinely equals** `digest`'s as word64 (so the
  `alg=none`/confusion rejects are caused by the **alg gate alone**, not a sig
  miss — a non-vacuous alg-confusion witness), while `badSig`'s hash genuinely
  **differs** (the bad-signature reject is a real miss, not a collision).
- **Did the generator apply cleanly, or need a spine adaptation?** **Applied
  DIRECTLY — no adaptation.** `mk_composedWrapper` ran with the JWT spine record and
  produced `MainRefine + Sem + Install + EndToEnd → jwt_machine_code` with **zero**
  wrapper hand-lines. The ML peel was NOT extended and NO fold/gate schema was added.
  The one difference from C27 is honest and small: the **staged scalar @+16, unused
  in C27, is READ by the gate here** — it carries the token's declared `alg` tag, so
  the gate is a two-condition cascade (sig-equality **and** alg-tag) rather than
  C27's single equality. The generator stages/threads exactly one scalar (`hd
  scalars`) and hands it to the gate lemma; the gate consuming it needed no generator
  change.

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C30 used. **Dir:**
`docs/engine/probes/compiler/hol-c31/` (built on hbox `~/hol-c31`, full `Holmake`
exit 0, all theories incl. the `verifyC31` audit). Sibling agents own
`hol-c16..c30`; C31 owns a NEW `hol-c31/` and stayed out of theirs.

---

## 1. The target (grounded in drorb)

`jwtAdminStage` (`Reactor/Deploy.lean:1368`) is stage 1 of `deployStagesFull2`
(`Reactor/Deploy.lean:1497`). Its request-phase transform, on an `/admin*` target,
runs the REAL `Jwt.authenticate stageConfig` (via `Reactor.Stage.Jwt.jwtStage`); an
`.admit` passes (`.continue`), anything else short-circuits with a `401`:

```lean
onRequest := fun c =>
  if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c else .continue c
```

The decision, once a token is parsed and a key selected, is `afterKey`
(`Jwt.lean:441`):

```lean
afterKey cfg ctx jws key =
  if jws.header.alg = Alg.none then .reject .algNone
  else if jws.header.alg ≠ key.alg then .reject .algMismatch
  else if critOk cfg jws.header = false then .reject .critUnknown
  else if cfg.sigValid jws.header.alg key.material jws.signingInput jws.signature then
    (if temporalOk … then (if claimsOk … then .admit … else …) else …)
  else .reject .badSignature
```

For the deployed HS256 configuration `cfg.sigValid … = verifyFor … = verifyHmac`
(`Jwt.lean:420`, `familyVerify` HS256 → `verifyHmac`). `verifyHmac` (a `Config`
boundary, `Jwt.lean:241`) computes the HMAC-SHA256 digest over `signingInput` under
the key and compares it, constant-time, to the token's `signature`. So the
security-relevant admit decision — the one `jwt_rejects_bad_sig` and
`jwt_alg_confusion_safe` hinge on — is:

> **admit iff the presented signature equals HMAC-SHA256(signingInput, key)
> (`verifyHmac` T) AND `alg = key.alg` (= HS256) AND `alg ≠ none`.**

### The decomposition (stated precisely — what is compiled vs FFI vs upstream)

| piece | role | compiled here? |
|---|---|---|
| **the signature-equality compare** — presented `signature` vs the digest | the **DECISION** (verifyHmac's own compare) | **YES** — fold #1 hashes the digest, fold #2 hashes the sig, the gate reports `hash(digest)=hash(sig)` |
| **the alg-confusion-absent check** — `alg = key.alg = HS256`, `alg ≠ none` | the **DECISION** (afterKey alg gate) | **YES** — the staged scalar carries the alg tag; the gate reports `alg = 1` (HS256) |
| **HMAC-SHA256 itself** — `digest = HMAC(signingInput, key)` | **CRYPTO TRUST BOUNDARY** — a verified crypto primitive behind an FFI, exactly like the TLS crypto | **NO** — its OUTPUT (the digest bytes) is taken as the machine input arena; the gate compares, it does not recompute HMAC |
| **base64url-decode** of the header/payload/sig segments + **JSON claim parse** | **UPSTREAM general loop** (C27's base64 residual class) | **NO** — the decoded sig bytes are taken as input, exactly as C27 took the decoded credential |
| **`/admin*` path guard** — `isAdminPath`/`isPrefixB` prefix scan | **upstream routing** (C29's cidr-matcher class) — selects WHETHER the gate runs | **NO** — the same role C27's `isProtectedPath` played; not part of the admit decision |

**Spine shape.** The compiled decision maps onto the generator's fixed `(2-fold +
one-scalar + gate)` spine exactly:

| generator slot | JWT meaning |
|---|---|
| fold #0 (arena @ctrl+64)   | `hashBytes` of the **HMAC-SHA256 digest** (the crypto trust boundary's output, taken as input) |
| fold #1 (arena @ctrl+2112) | `hashBytes` of the **presented (decoded) signature** |
| scalar (@ctrl+16)          | the token's **declared alg tag** (1 = HS256, 0 = none, 2 = RS256/other) — **READ** by the gate (unlike C27's staged-but-unused `pad`) |
| gate                       | `dec = 1 iff hash(digest) = hash(sig) ∧ alg = 1` = `verifyHmac` ∧ alg gate |
| report                     | the admit bit (`.admit`/`.reject`) |

Hash-equality of the digest/sig arenas models `verifyHmac`'s constant-time compare
(as C22/C25/C27 model the key/origin/credential match). Modeling the digest as a
runtime arena (fold #0, not a literal) is faithful — the digest IS runtime crypto
output.

## 2. Did the generator apply directly? — YES, no spine adaptation

C23 §5 named two caveats on `mk_composedWrapper`'s reach: (1) it peels the **2-fold**
spine — a different fold count needs the ML peel extended; (2) a different fold
*body* costs its own core. **JWT hits neither.** It is a 2-fold decision, and both
folds are `hashBytes` (the digest and signature are hashed with the same `hashBytes`
C22–C27 hash keys/routes/origins/credentials with), so `cacheBodyA1/A2` and
`cacheLoop1/2_framed` are **reused verbatim** (the fold Annots land on jwt.pnk lines
24–27 / 35–38, byte-identical to C27's basic.pnk / C23's admit.pnk, so the two
`While` nodes refold by `Term.subst` with no re-proof). The generator call is a plain
spine record (`jwtGenScript.sml`); the ML peel loop was **not** touched, **no** new
fold/gate schema was added.

**The one honest difference from C27.** C27's gate was a single hash-equality (the
scalar `pad` staged-but-unused). C31's gate reads that scalar: it is
`If (km=ku) (If (alg=1) (dec:=1) skip) skip` — a two-condition cascade. That is a
**larger gate**, but it fits the SAME generator slot: `mk_composedWrapper` stages and
threads exactly one scalar (`hd scalars`) and provides it to the gate lemma's
context, so a gate that reads it needs **no** generator change. The gate def is the
verbatim emitted parser subterm; the gate lemma (`evaluate_jwtGate`) is the ONE
genuinely-new proof — a nested-`If` cascade closed by the same `evaluate_If_reduce +
cond1w_ne0` idiom C27/C29 used, with **two** `Cases_on` (the sig-equality and the
alg-tag) instead of one.

## 3. The residuals named honestly — NOT compiled

- **CRYPTO TRUST BOUNDARY: HMAC-SHA256.** The digest `HMAC(signingInput, key)` is a
  verified crypto primitive reached through an FFI (like the TLS crypto / like
  `Crypto.ed25519Verify` in the EdDSA arm). C31 does **not** compile it: it takes the
  digest bytes as the machine input arena and compiles the **compare** (the equality
  that IS `verifyHmac`'s decision). We do **not** claim the HMAC is compiled.
- **UPSTREAM general loop: base64url-decode + JSON claim parse.** RFC 7515 §7.1
  splits the compact token into three dot-separated segments, each base64url-decoded
  (RFC 4648 §5), and the payload JSON-parsed for claims. base64url decode is the same
  stateful emit-buffer transducer C27 named for Basic-auth (a variable-length
  bit-buffer fold, **not** a `hashBytes` scalar fold); JSON parse is a general parse
  `While`. Both are in the general-loop residual class (C13/C18/C23/C27) — reachable
  only with per-loop metatheory, not `mk_composedWrapper`. C31 takes the **decoded
  signature bytes** as input, exactly as C27 took the decoded credential and C25 took
  the canonical origin.
- **UPSTREAM routing: the `/admin*` path guard.** `Deploy.isAdminPath` /
  `isPrefixB` is a byte-prefix scan (C29's cidr-matcher class) that selects WHETHER
  the gate runs — the same role C27's `isProtectedPath` played. It is not part of the
  compiled admit decision; a token on `/admin*` runs this gate, other paths pass.

## 4. What the stage cost — the honest quantification

| piece | lines | kind |
|---|---:|---|
| the two `hashBytes` fold cores + framed cores | **0** | REUSED (`cacheBodyA{1,2}` / `cacheLoop{1,2}_framed`) |
| `cacheStaged` / `cacheFFI` contract | **0** | REUSED verbatim (identical control-block layout) |
| `jwtAdmit` spec (= `verifyHmac` ∧ alg gate) | 5 | the sig-equality ∧ alg-tag decision |
| `jwtGate` def | 10 | the emitted nested-`If` gate (extracted parser subterm) |
| **`evaluate_jwtGate`** | **15** | the ONE genuinely-new proof (two-condition gate cascade) |
| `jwtData` mainBody surgery | ~30 | mechanical (reuses `cacheStaged`/`cacheFFI`) |
| Link B (`jwtLinkBInst`) | **1** | one `mk_linkB` call |
| **whole-program wrapper** (MainRefine+Sem+Install+EndToEnd) | **0** | one `mk_composedWrapper` call |
| `verifyC31` audit | ~90 | assertions, not a hand proof |

**Total genuinely-new PROOF hand-lines: 15** (the gate lemma). It does strictly
more than C27's (two conditions, not one) yet stays in the same family and reuses the
same cascade idiom. Everything else is one spec, one extracted gate def, mechanical
surgery, and two one-line generator calls. The C23 economics hold for a fifth,
distinct stage — the deployed JWT gate.

## 5. The theorem (from `verifyC31`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … the standard pan_to_target install package over jwtProg … ∧
    pan_installed … ) ∧
  cacheFFI digest sig alg s ∧
  (∃K. 0 < K ∧ LENGTH digest + LENGTH sig < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit'
      (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (jwtAdmit digest sig alg) : word64) F) rb])}
```

`verifyC31` (the machine-checked audit theory) asserts: DISK_THM-only oracle, no
axioms, hyps = 0; non-vacuous (`machine_sem` / `Terminate Success` / `jwtAdmit`
present); a distinct decision over a distinct program (`jwtProg`, not
`cacheKeyProg`/`basicProg`; `jwtAdmit`, not `basicAdmit`/`corsAllow`/`admitDecide`/
`cacheServe`); and grounds the four-row admit truth-table on real bytes — incl. the
alg-confusion-rejected row, over a genuinely-valid (hash-equal) signature.

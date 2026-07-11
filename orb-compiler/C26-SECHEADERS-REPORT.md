# C26 REPORT — `securityheadersStage` (stage 13 of `deployStagesFull2`) reaches machine code via the C15 LOOP-FREE path: its RFC-6797 §6.1.1 HSTS decision core auto-closes with renames + ONE tactic call, 0 bespoke proof lines

**Gate A fan-out, stage 13.** `Reactor.Stage.SecurityHeaders.securityheadersStage`
— the security/HSTS response-header stamp, stage 13 of the real
`Reactor.Deploy.deployStagesFull2` orb serve — now has its reportable decision
core compiled spec → machine code, `leanc` out of the TCB, kernel-checked.

**Verdict up front.**
- **Is `securityheadersStage` closed end-to-end?** Its reportable **decision core**
  is. `secheaders_machine_code` (theory `secheadersEndToEnd`):
  `machine_sem mc ffi ms ⊆ extend_with_resource_limit' … { Terminate Success
  (… ++ [IO_event (ExtCall «report_vec») (word_to_bytes (n2w (hstsEffective code)) F) rb]) }`,
  **`[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats, NON-VACUOUS**, `leanc`
  out of the TCB (`secHeadersProg` is the verified CakeML parser's output on
  `secheaders.pnk`).
- **Which compile path fit?** The **C15 / C17 LOOP-FREE path** (`panLinkA_branch`
  + the C15 whole-`main` wrapper), NOT `mk_composedWrapper`. `securityheadersStage`
  is a straight-line transform — the header set is a **compile-time constant** of
  the deployed `policy` (no request dependence, no fold over input, no gate) — so
  the reportable decision is a scalar branch, not a 2-fold+gate spine.
- **Hand-lines?** **Zero bespoke proof lines.** The core equation is ONE
  `panLinkA_branch` call; the whole-program wrapper (MainRefine + Sem + Install +
  EndToEnd + Link B) is the C15 template reused under **mechanical renames** (sed).
  The only stage-authored content is definitions/data: the spec `hstsEffective`
  (3 lines), the verbatim parser-output core `secheadersCore` (5 lines), the
  relation (5 lines), the singleton guard list `[“code < 1n”]` (1 line), and the
  ~12-line `.pnk`.

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2 stdknl,
CakeML `ed31510b3`** — the exact tree C1–C25 used. **Dir:**
`docs/engine/probes/compiler/hol-c26/` (built on hbox `~/hol-c26`, full `Holmake`
exit 0, 11/11 theories OK). Sibling agents own `hol-c16..c25`; C26 stayed out.

---

## 1. The stage and its reportable core — grounded, not invented

`securityheadersStage` (drorb `Reactor/Stage/SecurityHeaders.lean:70`):

```lean
def securityheadersStage : Stage where
  name := "securityheaders"
  onRequest  := fun c => .continue c
  onResponse := fun _ b => (wireHeaders policy).foldl ResponseBuilder.addHeader b
```

The `onResponse` folds `wireHeaders policy = (SecurityHeaders.render policy).map
toWireHeader` onto the affine builder. For the **deployed `policy`** (hsts = some
one-year+subdomains+preload, xfo = DENY, noSniff = true, referrer = no-referrer)
`render policy` is a **fixed 4-element list** — independent of the request. So the
whole-list fold is a straight-line, data-independent transform: there is **no
single reported scalar** for the whole header list.

Per the Gate-A instruction ("if the response-effect is a whole-header-list
transform that is not cleanly a single reported value, close the decision core
that IS reportable + name the residual"), C26 closes the **RFC 6797 §6.1.1 HSTS
`includeSubDomains` gate** — the headline security decision of the stage. The
Lean anchor is `SecurityHeaders.effectiveIncludeSubDomains` + theorem
`hsts_zero_disables`:

```lean
def effectiveIncludeSubDomains (h : Hsts) : Bool :=
  h.includeSubDomains && (h.maxAge != 0)          -- RFC 6797 §6.1.1 NOTE
theorem hsts_zero_disables (h) (h0 : h.maxAge = 0) :
  effectiveIncludeSubDomains h = false
```

Specialized to the deployed policy's `includeSubDomains = true` (drorb
`hstsPolicy`), this is exactly `(maxAge != 0)`. The compiled spec (byte-identical,
re-declared in HOL as `hstsEffective`):

```
hstsEffective (code:num) = if code < 1 then 0n else 1n    (* code = HSTS max-age *)
```

`max-age = 0` ⟺ `code < 1` (nats), so `hstsEffective` = the deployed-policy
`effectiveIncludeSubDomains`. **RFC 6797 §6.1.1 NOTE**: `max-age = 0` disables the
HSTS policy and its `includeSubDomains` directive is then ignored → reports 0;
any positive `max-age` → HSTS active, `includeSubDomains` effective → reports 1.

## 2. The theorem (verbatim `show_tags`, from `verifyC26`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … the standard pan_to_target install package over secHeadersProg … ∧
    pan_installed … ) ∧ secheadersFFI code s ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
      extend_with_resource_limit'
        (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
        {Terminate Success
           (s.ffi.io_events ++ loadEv ++
            [IO_event (ExtCall «report_vec»)
               (word_to_bytes (n2w (hstsEffective code)) F) rb])}
```

Every observable behaviour of the installed x64 machine code emitted for
`secheaders.pnk` is the single terminating trace whose reported word is EXACTLY
the Lean spec value `n2w (hstsEffective code)`.

**Non-vacuity / grounding** (`verifyC26` asserts, build fails otherwise):
`hstsEffective 31536000 = 1` (the **deployed** one-year max-age → HSTS
`includeSubDomains` effective) and `hstsEffective 0 = 0` (RFC 6797 §6.1.1 NOTE:
disabled). The two outputs **differ**, so the guard is a genuine branch on a real
input, not a constant. `leanc` out of the TCB: `secHeadersProg` is proved equal to
`parse_topdecs_to_ast <secheaders.pnk source>` = `INL secHeadersProg` by the
verified parser.

**Axiom ledger (all 0):** `secheadersEndToEnd/Install/LinkBInst/MainRefine/Sem/
Wrapper/Core`, `c14Generic`, `panAuto` each declare **0 axioms**. `DISK_THM` is the
benign CakeML disk-export tag.

## 3. Which path fit + the adaptation (honest quantification)

**Path: C15 loop-free (`panLinkA_branch`), NOT `mk_composedWrapper`.** The stage's
decision is a single-guard `If` over one scalar — strictly *simpler* than C15's
4-guard `statusClass` cascade. Crucially the **control block is byte-identical to
C15's**: one input word `maxage` at `[base+0)`, result at `[base+8)`, `buf =
base+16`, `@load_vec` 8 bytes. So the entire whole-`main` wrapper reused the C15
template with mechanical renames.

| piece | lines | kind |
|---|---:|---|
| `hstsEffective` spec + `secheadersCore` (verbatim parser If) + `secheadersRel` | 13 | **definitions** (data, not proof) |
| core equation `evaluate_secheadersCore` | **0** | one `panLinkA_branch (…defs…) [“code < 1n”]` call |
| `secheaders.pnk` | ~12 | the real Pancake source |
| Wrapper / MainRefine / Sem / Install / EndToEnd | **0** | C15 template, sed renames |
| Link B (`secHeadersProg`) | **1** | one `mk_linkB` call |
| **bespoke proof lines** | **0** | — |

**Adaptation from C15:** essentially none structural. Renames (`status*→secheaders*`,
`code`-local `«code»→«maxage»`, spec `statusClass→hstsEffective`) applied by sed;
the guard list dropped from four `<` predicates to one; the signed-range bound
widened from `code < 1000` to `code < 2^63` (the deployed max-age 31536000 is well
inside signed-positive range). The exact leaf location-`Annot`s were read from the
verified parser's AST dump on `secheaders.pnk` (`ast_dump.txt`) — its main-body
spine is structurally identical to `statusclass.pnk`, so the C15 MainRefine ML
peel discharged verbatim. This is a 4th loop-free primitive (after C15
`statusClass`, C17 `redirectStatus`, and the C18 scalar-branch class) closed by
the same generator path — confirming the loop-free lane is **rename-only** for any
single-scalar branch decision with the canonical `@load_vec/@report_vec` block.

## 4. What is closed vs. the named residual

**Closed:** the RFC 6797 §6.1.1 HSTS effective-`includeSubDomains` decision, spec →
x64 machine code, reported on the observable FFI trace, grounded on the deployed
policy's `max-age = 31536000`.

**Residual (named honestly):** the stage's *full* response-effect is a fold of
**four** constant headers onto the affine `ResponseBuilder`, not one scalar. Not
reduced here:
1. **The three companion headers** — `X-Frame-Options: DENY`,
   `X-Content-Type-Options: nosniff`, `Referrer-Policy: no-referrer`. Each is a
   constant emit governed by the same shape (a `match`/`if` on a policy field);
   each is another loop-free primitive closable by the same rename-only path.
2. **The `includeSubDomains` operand.** `hstsEffective` fixes it to the deployed
   `true`, reporting `effectiveIncludeSubDomains` as a function of `max-age` alone.
   The *complete* two-operand `effectiveIncludeSubDomains h = includeSubDomains &&
   (maxAge ≠ 0)` needs a 2-scalar read spine (a mechanical extension of the C15
   one-word MainRefine: one added `lds`/`Dec` node + staged word).
3. **The exact RFC-6797 value-string bytes** (`"max-age=31536000; includeSubDomains;
   preload"`) and the **whole-list byte fold** into the `ResponseBuilder` — the
   same `foldl ResponseBuilder.addHeader` transform machinery shared with the
   other deployed transform stages (gzip/htmlrewrite/cors/headerRewrite). This is
   a byte-level list transform, not a reportable scalar decision, and is left as
   the standing residual for the transform-stage lane.

## 5. Files (`docs/engine/probes/compiler/hol-c26/`, built on hbox `~/hol-c26`)

- `secheaders.pnk` — the emitted decision program (verified-parser input).
- `secheadersCoreScript.sml` — `hstsEffective` spec + `secheadersCore` (verbatim
  parser `If`) + `secheadersRel`; core equation by one `panLinkA_branch` call.
- `secheadersWrapperScript.sml` — `secheadersCtrlStaged`/`secheadersFFI` contract +
  `secheadersMainBody` (ML surgery on the parser output). C15 template, renamed.
- `secheadersMainRefineScript.sml` — whole-`main` FFI-trace refinement. C15 forward-
  wrap reused verbatim (identical control block).
- `secheadersSemScript.sml` / `secheadersInstallScript.sml` /
  `secheadersEndToEndScript.sml` — clock-lift → `semantics_decls` → compose with
  Link B → `secheaders_machine_code`.
- `secheadersLinkBInstScript.sml` — Link B (`mk_linkB` on `secheaders.pnk`).
- `verifyC26Script.sml` — adversarial audit (tags = `DISK_THM`-only, hyps = 0,
  all axioms = 0, non-vacuous grounded truth table, leanc-out parser output).
- carried verbatim from C15: `panAutoScript.sml`, `panAutoLib.sml`,
  `c14GenericScript.sml`, `Holmakefile`, `astDumpScript.sml`.
- Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0 (11/11 OK).
```
c14Generic (1) astDump (2) panAuto (3) secheadersCore (4) secheadersLinkBInst (5)
secheadersWrapper (6) secheadersMainRefine (7) secheadersSem (8)
secheadersInstall (9) secheadersEndToEnd (10) verifyC26 (11)   — all OK
```

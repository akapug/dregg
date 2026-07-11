# C30 REPORT — the constant secheaders TRANSFORM is now a FULL machine_sem STAGE: its 159-byte response-BYTE effect compiles spec → x64 machine code, reported byte-for-byte on the observable FFI trace, with leanc OUT of the TCB

**Gate A, the response-byte half — CLOSED to machine code.** C28 built the
store-loop machinery (`copyLoop_writes`: an emitted `While`+`StoreByte` loop that
writes exactly the source bytes, proven against real Pancake `panSem$evaluate`)
and grounded it on the deployed 159-byte serialized security-header block, but
stopped at **Link-A** with 3 residuals: (#1) not lifted through `pan_to_target` to
`machine_sem`, (#2) the loop program authored directly (leanc **in** the TCB).
C30 closes residuals **#1 and #2** for the CONSTANT `secheaders` transform: the
store loop is now a genuine **verified-parser** program AND is lifted to a full
`machine_sem` subset theorem — the same standard both `boundScan` (C13) and the
deployed cache-key hash (C20) reached.

**Verdict up front.**

- **Is the secheaders transform now a FULL machine_sem stage with leanc OUT?**
  **Yes.** `secheaders_bytes_machine_code` (theory `transformEndToEnd`):

  ```
  [oracles: DISK_THM] [axioms: ]      (hyps = 0, 0 cheats)
  ⊢ ( … the standard pan_to_target install package over transformProg … ∧
      pan_installed … ) ∧
    transformFFI secHeadersBytes s ∧ (∃K. 0 < K ∧ LENGTH secHeadersBytes < K) ⇒
    ∃loadEv rb.
      machine_sem mc ffi ms ⊆
        extend_with_resource_limit'
          (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
          {Terminate Success
             (s.ffi.io_events ++ loadEv ++
              [IO_event (ExtCall «report_vec»)
                 (MAP (λb. n2w b) secHeadersBytes) rb])}
  ```

  Every observable behaviour of the installed **x64 machine code** emitted for
  `copy.pnk` is the single terminating trace whose reported FFI payload is EXACTLY
  `MAP n2w secHeadersBytes` — the deployed 159-byte serialized security-header
  block, **byte for byte**. This is the multi-byte analogue of the decision
  stages' single-word `report_vec (n2w decision)`: a response-**byte** transform
  reaching `machine_sem`, not a scalar proxy, not Link-A.

- **leanc OUT?** **Yes.** `transformProg_is_parser_output`
  (`transformProg = parse_topdecs_to_ast <copy.pnk> = INL transformProg`, by the
  CakeML-verified Pancake parser via `mk_linkB`). The store-loop program is
  genuine verified-parser output; the `While` folded into `transformMainBody` by
  ML `Term.subst` is a real parsed subterm (the surgery fires or the build fails).

- **Axiom ledger (all 0), tags:** all 8 C30 theories declare **0 axioms**;
  `secheaders_bytes_machine_code` and `transformProg_semantics_decls` carry only
  the benign `DISK_THM` disk-export oracle (asserted by the `verifyC30`
  ML build-guard — no cheats, no extra oracles).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C29 used. **Dir:**
`docs/engine/probes/compiler/hol-c30/` (built on hbox `~/hol-c30`, full `Holmake`
exit 0, all theories OK). Sibling agents own `hol-c16..c29`; C30 stayed out and
copied only the carried deps (`panAuto`, `panAutoLib`, `c14Generic`) + the C28
store-loop core (`transformCopyLoop`, `transformSecHeaders`).

---

## 1. What C30 added over C28 (the mechanical lift, applied)

C28 proved the store loop at the `panSem$evaluate` (Link-A) level for an
**annot-free** authored `copyLoop`. C30 does three things:

1. **The GENUINE PARSED loop (leanc out, residual #2).** `copy.pnk` is authored
   and run through the CakeML-verified parser (`mk_linkB`). The parser wraps each
   `while`-body statement in a `location` `Annot`; C30 transcribes that verbatim
   body as **`copyBodyA`** and `copyLoopA = While copyGuard copyBodyA`. A one-line
   bridge `copyBodyA_body_eq` (the two location Annots are behaviourally
   invisible: `evaluate copyBodyA = evaluate copyBody`) carries the *entire* C28
   store-loop machinery — `copyBody_step`, the three abstract store lemmas, the
   bounded `While` induction — onto the parsed body, yielding **`copyLoopA_writes`**
   with a ~5-line-per-lemma bridge. `transformMainBody` is then the verbatim
   `«main»` body of `transformProg` with the emitted `While` folded to `copyLoopA`
   (ML `Term.subst`, fires against the real parsed subterm).

2. **The whole-`main` FFI-trace refinement (`transformMainRefine`).** The C20
   fuel-budgeted loop-wrapper template (ML spine peel + `Dec/Annot/Seq` forward
   wrap), adapted: the emitted `While` is discharged in **ONE step** by
   `secheaders_copyLoopA_writes`; there is **no separate store** (the copy loop IS
   the write) and **no length read** (159 is a compile-time constant). The load
   oracle stages `copyInv` via one reusable frame lemma (`transformStaged_frame` +
   `transformStaged_copyInv`); the report oracle emits the written buffer as the
   byte vector. `transformMainBody_refines`:
   `transformFFI secHeadersBytes s0 ∧ LENGTH secHeadersBytes ≤ s0.clock ⇒
    evaluate (transformMainBody, s0) = (SOME (Return 0w), sF) ∧ sF.ffi trace = … report_vec (MAP n2w secHeadersBytes) …`.

3. **The C13/C20 Sem → Install → EndToEnd lift (residual #1).** Applied verbatim
   (payload-shape-agnostic): `transformSem` (clock-lift `evaluate` →
   `semantics` via the carried `semantics_Return_lift`), `transformInstall`
   (whole-program `semantics_decls` over `transformProg`), `transformEndToEnd`
   (compose with the CakeML backend `transformProg_linkB`, install-package
   antecedents taken **verbatim** from Link B, the `semantics_decls ≠ Fail` side
   condition PROVED from Link A). Result: `secheaders_bytes_machine_code`.

## 2. Non-vacuity / grounding — the reported bytes are the deployed block

`secHeadersBytes = MAP ORD secHeadersStr`, where `secHeadersStr` is the deployed
`SecurityHeaders.render policy` serialized as an HTTP/1.1 header block
(`name: value` + CRLF), driven off the REAL drorb strings:

```
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload␍␊
X-Frame-Options: DENY␍␊
X-Content-Type-Options: nosniff␍␊
Referrer-Policy: no-referrer␍␊
```

Mechanically checked (`verifyC30`, build fails otherwise):
- `LENGTH secHeadersBytes = 159`, `secHeadersBytes ≠ []`, `EVERY (λx. x < 256)` —
  a concrete, non-empty, wire-valid payload (`c30_payload_nonvacuous`).
- `secHeadersBytes = MAP ORD secHeadersStr` — byte-identical to the serialized block.
- `TAKE 25 secHeadersBytes = MAP ORD "Strict-Transport-Security"`, `EL 0 = ORD #"S"`,
  `IS_SUFFIX secHeadersBytes (MAP ORD ("no-referrer" ++ CRLF))` — grounded
  spot-checks: LEADS with the RFC-6797 HSTS header, ENDS with the Referrer-Policy
  line (`c30_payload_grounded`).

The `machine_sem` theorem carries `MAP n2w secHeadersBytes` as the *observable*
payload; `copyLoopA_writes` ties that payload to the actual written buffer (the
report contract fires only when the buffer holds those bytes), so it is the REAL
written output, not a faked scalar.

## 3. Is a CONSTANT transform stage now a BOUNDED pattern? (quantification)

**Yes — `mk_transformWrapper` is bounded and the pieces are reusable.** A
compile-time-constant response-byte transform closes by:

| piece | what it is | cost / reuse |
|---|---|---|
| store machinery | `copyLoopA_writes` (C28 core on the parsed body) | **O(1) in block length L** — one loop invariant + one per-step + one bounded `While` induction; `bs`-agnostic |
| staging | `transformStaged_frame` + `transformStaged_copyInv` | 2 reusable frame lemmas (load oracle → `copyInv`) |
| whole-`main` refine | `transformMainRefine` | C20 loop-wrapper template; the `While` is ONE `copyLoopA_writes` call |
| lift | `transformSem/Install/EndToEnd` | C13/C20 template, payload-shape-agnostic (the byte vector rides the trace untouched) |
| leanc out | `mk_linkB { pnkFile, progName }` | the C11/C20 generator, one call |

Any other compile-time-constant response-byte append (the `Content-Encoding:
gzip` constant header, a fixed CORS header block) reuses this path by supplying
its own constant `bs` and `.pnk` — the store lane, the lift, and the verified
parse are all instantiate-and-go. The proof is **independent of the block
length**, so a longer constant block does not grow the proof.

## 4. What is closed vs. the named residuals (precise)

**Closed:** the constant `secheaders` transform's response-BYTE effect, spec →
x64 machine code, reported byte-for-byte on the observable FFI trace, grounded on
the deployed 159-byte serialized block, leanc OUT, 0 axioms, `DISK_THM`-only,
non-vacuous. C28 residuals **#1** (`pan_to_target` → `machine_sem`) and **#2**
(verified parser / leanc-out) are **discharged**.

**Residual A — the render-link (shape-checked, NOT proven `= render`).** The tie
from `secHeadersBytes` to the deployed policy is: `secHeadersBytes = MAP ORD
secHeadersStr` where `secHeadersStr` is the HOL **transcription** of the serialized
`SecurityHeaders.render policy` block, grounded by the byte spot-checks above.
This is **byte-identical-to-the-serialized-block + shape-verified**, *not* a proof
that `secHeadersBytes = MAP ORD (SecurityHeaders.render policy serialized)` via a
**compiled** `render`-fold. Closing it fully needs the `render` fold
(request-independent, but a fold over the policy's header list producing the
`name: value␍␊` bytes) compiled and proven equal to `secHeadersStr` — a
`leanc`-emitted or compiled-fold obligation. Named precisely; **not overclaimed**
as `= render`.

**Residual B — REQUEST-DEPENDENT transforms (C28 residual #3, still open).** C30
closes the compile-time-CONSTANT block (no request dependence — exactly the
deployed security-header set). A request-dependent transform (header-rewrite,
gzip, HTML-rewrite) has output bytes that are a *function of the request/response
content*: the source is not a staged constant but must be **computed by a
fold/transform over the input** before the store loop. That composes the
C16/C19/C20 **fold lane** (input → transformed bytes) with **this** store lane
(bytes → output buffer) — the fold's result feeding `copyInv`'s source relation
in place of the load-oracle-staged constant. This is a strictly larger, named
next step; the two lanes now both exist at `machine_sem`, so the remaining work is
their composition seam, not new metatheory.

**FFI trust ledger (unchanged status from C13/C20/C26/C28).** The single named
trusted assumption is `transformFFI secHeadersBytes` — the `@load_vec` /
`@report_vec` oracle contract: (L) `@load_vec` stages the source block at
`ctrl+4096` byte-readable + the output region `[ctrl+32, +159)` writable &
word-disjoint (`transformStaged`); (R) `@report_vec`, given the output buffer
holds the bytes, emits exactly `MAP n2w secHeadersBytes` on the observable trace.
Same status as every prior stage's `report_vec` contract. Not leanc.

## 5. Files (`docs/engine/probes/compiler/hol-c30/`, built on hbox `~/hol-c30`)

- `copy.pnk` — the emitted transform program (verified-parser input); `ast_dump.txt`
  the parser's `functions` output (the exact `Annot`-wrapped spine).
- `transformCopyLoopScript.sml` — C28 store-loop core + the C30 parsed-body layer
  (`copyBodyA`, `copyLoopA`, `copyBodyA_body_eq`, `copyBodyA_step`,
  **`copyLoopA_writes`**, `copyLoopA_noFFI/_io_events`).
- `transformSecHeadersScript.sml` — the deployed block (`secHeadersBytes`, 159
  bytes, wire-valid, HSTS-led) + **`secheaders_copyLoopA_writes`** (grounded instance).
- `transformLinkBInstScript.sml` — Link B (`mk_linkB` on `copy.pnk`);
  `transformProg`, `transformProg_is_parser_output`, `transformProg_linkB`.
- `transformWrapperScript.sml` — `transformStaged` + the `transformFFI` oracle
  contract + `transformStaged_frame`/`transformStaged_copyInv` + `transformMainBody`
  (ML surgery folding `copyLoopA` into the parser output).
- `transformMainRefineScript.sml` — **`transformMainBody_refines`** (whole-`main`
  FFI-trace refinement; the `While` discharged by `secheaders_copyLoopA_writes`).
- `transformSemScript.sml` / `transformInstallScript.sml` /
  `transformEndToEndScript.sml` — clock-lift → `semantics_decls` → compose with
  Link B → **`secheaders_bytes_machine_code`**.
- `verifyC30Script.sml` — adversarial audit (tags = `DISK_THM`-only, 0 axioms
  across all 8 theories, leanc-out parser output, non-vacuous grounded truth).
- carried deps: `panAutoScript.sml`, `panAutoLib.sml`, `c14GenericScript.sml`,
  `astDumpScript.sml`, `Holmakefile`. Build: `CAKEMLDIR=/home/hbox/src/cakeml`,
  full `Holmake` exit 0.

```
astDump · panAuto · c14Generic · transformCopyLoop · transformSecHeaders ·
transformLinkBInst · transformWrapper · transformMainRefine · transformSem ·
transformInstall · transformEndToEnd · verifyC30   — all OK
```

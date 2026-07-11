# C28 REPORT — TRANSFORM-STAGE machinery: a stage's response-BYTE effect compiles to a proven in-place store loop, grounded on the deployed 159-byte security-header block, and reaches an observable multi-byte FFI output

**Gate A, the response-byte half.** The decision/gate stages (C13–C27) compile to
a reported **scalar** (`report_vec (n2w decision)`). A **transform** stage produces
**output bytes** — it writes response-header bytes into the response buffer. C26
closed `securityheadersStage`'s HSTS decision core but explicitly named the
residual: the whole-list `(wireHeaders policy).foldl ResponseBuilder.addHeader`
**byte** effect. C28 pilots the machinery to compile **that** — a stage's
response-byte transform to code that WRITES the right bytes, proven against the
Lean spec, reusing the PROVEN Datapath in-place writer.

**Verdict up front.**

- **Does a transform stage's response BYTES now compile to proven machine code?**
  The **in-place multi-byte store loop does**, at the `panSem$evaluate` /
  `semantics` (Link-A) level: the emitted `While` + `StoreByte` copy loop, run
  against the REAL Pancake operational semantics, writes **exactly** the source
  bytes into the output buffer. Grounded on the **deployed 159-byte serialized
  security-header block**, and lifted to an **observable** `report_vec` FFI event
  carrying those exact bytes. **`[oracles: DISK_THM] [axioms: ]`, 0 cheats,
  NON-VACUOUS.**
- **Reached machine_sem?** **No** — honestly one step below. This is the Link-A
  store loop + the FFI-report contract, NOT yet composed through `pan_to_target`
  to `machine_sem` (that is the C13 `Sem/Install/EndToEnd` template, named
  residual §5). Also, unlike C26, the program AST is authored directly, not yet
  proven equal to the verified CakeML parser's output on a `.pnk` (leanc **in**
  the TCB here — named residual §5).
- **Is it bounded / reusable?** **Yes.** The whole loop closes by ONE loop
  invariant (`copyInv`) + ONE per-step (`copyBody_step`) + a bounded `While`
  induction (`copyLoop_bounded`) — an **O(1) proof independent of the block
  length L**. The byte-memory reasoning is **three reusable abstract store
  lemmas**. Any compile-time-constant response-byte append reuses the path by
  instantiating `bs` (C28-B does exactly this for the deployed header set).
- **The genuine residual.** REQUEST-DEPENDENT transforms (header-rewrite, gzip)
  whose output bytes are a function of the request/response content — those need
  the source bytes *computed by a transform over input*, not staged as a constant
  (§5). The constant-block case (the deployed security headers) is what C28
  closes.

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C27 used. **Dir:**
`docs/engine/probes/compiler/hol-c28/` (built on hbox `~/hol-c28`, full `Holmake`
exit 0, 5/5 theories OK). Sibling agents own `hol-c16..c27`; C28 stayed out and
copied the two carried deps (`panAuto`, `c14Generic`) it needed.

---

## 1. The model writer it realises — drorb `Datapath/Refine.lean`

The PROVEN in-place writer the compiler must emit:

```lean
def storeFrom (buf : ByteArray) (base : Nat) : List UInt8 → ByteArray
  | []      => buf
  | b :: bs => storeFrom (buf.set! base b) (base + 1) bs        -- one set! per byte
theorem storeFrom_get!_at … : (storeFrom buf base bs).get! (base + i) = bs[i]  -- faithful
```

`copyLoop` (theory `transformCopyLoop`) is the EMITTED analogue — one `StoreByte`
per iteration, no fresh allocation (the zero-copy write):

```
copyGuard = Cmp Less (Var «i») (Var «n»)
copyBody  = Seq (StoreByte (out + i) (LoadByte (src + i)))       (* one byte store *)
                (Assign «i» (Op Add [Var «i»; Const 1w]))
copyLoop  = While copyGuard copyBody
```

`copyLoop_writes` is the emitted, `panSem$evaluate`-checked analogue of
`storeFrom_get!_at`: after the compiled loop, reading back byte `j` yields the
`j`-th model byte. The byte-memory core is three abstract, state-free lemmas
mirroring the Datapath obligations:

| C28 abstract lemma | drorb Datapath analogue |
|---|---|
| `store_prefix_extend` — the written prefix extends by one faithful byte | `storeFrom_get!_at` |
| `store_source_preserve` — the source read survives a word-disjoint store | `denote_storeFrom_disjoint` |
| `store_region_writable` — the output region stays `Word`-mapped | (the `Wf`/capacity side) |

They stand on CakeML's `good_dimindex_get_byte_set_byte` /
`get_byte_set_byte_diff` (byte-in-word lane algebra) — the write is faithful and
separated at the real word-addressed `mem_store_byte` / `mem_load_byte`.

## 2. The two headline theorems (verbatim `show_tags`, from `verifyC28`)

**(A) The store-loop core — the machine writes the source bytes.**

```
[oracles: DISK_THM] [axioms: ]
⊢ copyInv bs src out 0 s ∧ LENGTH bs ≤ s.clock ⇒
  ∃s'. evaluate (copyLoop,s) = (NONE,s') ∧
       (∀j. j < LENGTH bs ⇒
            mem_load_byte s'.memory s'.memaddrs s'.be (out + n2w j) = SOME (n2w bs⟨j⟩)) ∧
       FLOOKUP s'.locals «out» = SOME (ValWord out)
```

Program-agnostic in the payload `bs`: for ANY wire-valid byte list, the emitted
loop writes it byte-for-byte into `[out, out+L)`.

**(B) The observable byte output — grounded on the deployed header block.**

```
[oracles: DISK_THM] [axioms: ]
⊢ copyInv secHeadersBytes src out 0 s ∧ LENGTH secHeadersBytes ≤ s.clock ∧
  reportBytesFFI secHeadersBytes out s ⇒
  ∃s' rb. evaluate (copyReportBody,s) = (NONE,s') ∧
          s'.ffi.io_events =
            s.ffi.io_events ++
            [IO_event (ExtCall «report_vec») (MAP (λb. n2w b) secHeadersBytes) rb]
```

Every terminating run of `copyReportBody` (copy loop + `@report_vec`) emits ONE
`report_vec` IO_event whose payload is `MAP n2w secHeadersBytes` — the real
159-byte header block, byte for byte. This is the multi-byte analogue of C26's
single-word `report_vec (n2w decision)`: a response-**byte** transform reaching a
proven **observable**, not a scalar proxy.

`reportBytesFFI` is the ONE named trusted assumption (same status as C13/C26's
`report_vec`): *given the output buffer holds `bs`*, `@report_vec` emits exactly
those `LENGTH bs` bytes. The reported bytes are TIED to the memory contents (the
premise), which `copyLoop_writes` supplies — so the output is the REAL written
buffer, not a fake.

## 3. Non-vacuity / grounding — the quoted payload (`verifyC28`, build-fails-otherwise)

`secHeadersBytes = MAP ORD secHeadersStr`, where `secHeadersStr` is the deployed
`SecurityHeaders.render policy` serialized as an HTTP/1.1 header block
(`name: value` + CRLF), driven off the REAL drorb strings:

```
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload␍␊
X-Frame-Options: DENY␍␊
X-Content-Type-Options: nosniff␍␊
Referrer-Policy: no-referrer␍␊
```

Mechanically checked (build fails otherwise):
- `LENGTH secHeadersBytes = 159` — a concrete, non-empty payload (`c28_payload_nonvacuous`).
- `EVERY (\x. x < 256) secHeadersBytes` — every byte wire-valid.
- `secHeadersBytes = MAP ORD secHeadersStr` — byte-identical to the deployed block.
- `TAKE 25 secHeadersBytes = MAP ORD "Strict-Transport-Security"`, `EL 0 = ORD #"S"`,
  `IS_SUFFIX secHeadersBytes (MAP ORD ("no-referrer" ++ CRLF))` — grounded spot-checks
  that it LEADS with the RFC-6797 HSTS header and ENDS with the Referrer-Policy line
  (`c28_payload_grounded`).

**Axiom ledger (all 0):** `transformCopyLoop` and `transformSecHeaders` each
declare **0 axioms**; `copyLoop_writes` and `secheaders_bytes_reported` carry only
the benign `DISK_THM` disk-export tag (asserted by the `verifyC28` ML build-guard).

## 4. Is transform-stage compilation a bounded, reusable pattern? (honest quantification)

**Bounded — yes, O(1) in the block length.** Unlike an unrolled straight-line
store sequence (whose proof grows with L), the copy loop closes by a single
`While` invariant:

| piece | what it is | cost |
|---|---|---|
| `copyInv` | loop invariant: `«i»/«n»/«src»/«out»` pinned, source `memRel`, written-prefix relation, region-writable, word-disjoint | 1 definition |
| `copyBody_step` | ONE iteration re-establishes `copyInv` at `i+1` (3 abstract store lemmas) | 1 per-step |
| `copyLoop_bounded` | bounded `While` induction (mirrors C16 `foldLoop_bounded`) | 1 induction |
| `copyLoop_writes` | fresh-state headline (`storeFrom_get!_at` analogue) | 1 specialisation |

**Reusable — yes.** `copyLoop_writes` is program-agnostic in `bs`; C28-B
(`secheaders_copyLoop_writes`) instantiates it at `bs = secHeadersBytes` in **one
line** (`metis_tac [copyLoop_writes]`). Any stage whose response-byte effect is a
**compile-time-constant append** (the deployed security headers; likewise the
`Content-Encoding: gzip` / CORS constant-header stages) reuses the same loop +
report by supplying its own constant `bs` — a `mk_transformWrapper`-style path.
The Datapath `storeFrom`/`writeInPlace` shape is reused cleanly: `copyBody` IS the
`storeFrom` step, and the three abstract lemmas are the `storeFrom_get!_at` /
`denote_storeFrom_disjoint` obligations at `mem_store_byte`.

## 5. What is closed vs. the named residuals

**Closed:** the in-place multi-byte store loop → Pancake, `panSem$evaluate`-proven
to write EXACTLY the source bytes (`copyLoop_writes`); grounded on the deployed
159-byte serialized security-header block; lifted to an observable `report_vec`
byte event (`secheaders_bytes_reported`). 0 axioms, DISK_THM-only, non-vacuous.

**Residuals (named precisely):**
1. **`pan_to_target` → `machine_sem`.** C28 stops at Link-A (`evaluate` +
   the FFI-report contract). Lifting to `machine_sem mc ffi ms ⊆ … {Terminate
   Success …}` is the C13 `semLift`→`semantics_decls`→`Install`→`EndToEnd`
   template (clock-lift + `pan_installed` compose) — mechanical, not applied here.
   `c14GenericTheory.semantics_Return_lift` is carried and ready.
2. **leanc / verified parser (Link B).** `copyLoop`/`copyReportBody` are authored
   AST terms, NOT proven equal to `parse_topdecs_to_ast <copy.pnk>`. So leanc is
   **in** the TCB for this program (C26's `secHeadersProg` was out). Residual:
   emit `copy.pnk`, run the verified parser, prove `mainBody = INL <parse>`.
3. **Whole-`main` wrapper.** `copyReportBody` is the loop+report core. The full
   `main` (a `@load_vec` staging `copyInv` from a constant data block, the
   `Dec`/`Annot` spine, `Return`) — the C13/C26 wrapper assembly — is not built;
   `copyInv` + `reportBytesFFI` are taken as the (discharged-by-oracle) staging
   contract, as C26 did for its control block.
4. **REQUEST-DEPENDENT transforms** (header-rewrite, gzip, HTML-rewrite). C28
   closes the **compile-time-CONSTANT** block (no request dependence — exactly the
   deployed security-header set). A request-dependent transform's output bytes are
   a *function of the input*: the source is not a staged constant but must be
   *computed by a fold/transform over the request* before the store loop. That
   composes the C16/C19 fold lane (input → transformed bytes) with **this** store
   lane (bytes → output buffer) — a strictly larger, named next step.

## 6. Files (`docs/engine/probes/compiler/hol-c28/`, built on hbox `~/hol-c28`)

- `transformCopyLoopScript.sml` — the store-loop core: byte lemmas
  (`mem_load_store_byte_same/_ne`), `memRel`/`byteWritable`/`disjWords`/`copyInv`,
  the three abstract store lemmas, `copyBody_step`, `copyLoop_bounded`,
  **`copyLoop_writes`**, `copyLoop_noFFI`/`copyLoop_io_events`.
- `transformSecHeadersScript.sml` — grounding: `secHeadersStr`/`secHeadersBytes`
  (the deployed block) + props (159 bytes, wire-valid, HSTS-led),
  `secheaders_copyLoop_writes`, the `reportBytesFFI` contract, **`secheaders_bytes_reported`**.
- `verifyC28Script.sml` — adversarial audit: tag/axiom ML build-guard (0 axioms,
  DISK_THM-only), `c28_payload_nonvacuous`, `c28_payload_grounded` (quoted block).
- carried deps: `panAutoScript.sml`, `panAutoLib.sml`, `c14GenericScript.sml`,
  `Holmakefile`. Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0
  (5/5 theories: `panAuto`, `c14Generic`, `transformCopyLoop`, `transformSecHeaders`,
  `verifyC28`).
```
panAuto (1) c14Generic (2) transformCopyLoop (3) transformSecHeaders (4) verifyC28 (5)  — all OK
```

# C21 REPORT — the C20 hand-done serve-fold wrapper is now a REUSABLE GENERATOR: `mk_foldWrapper` reproduces C20 byte-identically AND closes a SECOND real serve fold with ~0 wrapper hand-lines

C20 closed the first real serve fold end-to-end (`hash_machine_code`: the deployed
cache-key hash `machine_sem ⊆ {Terminate Success (… n2w (hashBytesN input) …)}`,
leanc out of the TCB) but the whole-program wrapper stack — `MainRefine` + `Sem` +
`Install` + `EndToEnd` (~450 hand lines) — was a **bespoke hand-adaptation**, not a
generator call (C20 §5, the named residual). **C21 lands that residual.**
`panWrapperLib` now exports `mk_foldWrapper`: an ML generator (no new metatheory —
mechanical term/theorem construction, like `mk_wrapper`/`mk_linkB`) that produces
the whole fuel-budgeted fold wrapper stack from parameters. The **next serve fold
= a ~16-line C19-style core fill-in + one `mk_foldWrapper` call**; the ~450-line
whole-program wrapper proof is **zero hand lines**.

**Verdict up front:**
- **Is `mk_foldWrapper` a real generator?** **Yes.** It reproduces C20's
  `hash_machine_code` **byte-identically** from a single generator call (the hand
  stack is deleted), and it closes a **second, genuinely different** real serve
  fold — the HTTP Content-Length decimal accumulator — spec→machine-code
  end-to-end.
- Both end-to-end theorems: `[oracles: DISK_THM] [axioms: ]`, **hyps = 0, 0
  cheats**, leanc out of the TCB (each subject is the verified-parser output).
  `~/hol-c21` green on hbox from a **clean `Holmake`** (14 theories, incl. the
  `verifyC21` audit theory whose adversarial checks pass).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C20 used. **Dir:**
`docs/engine/probes/compiler/hol-c21/` (built on hbox `~/hol-c21`). Sibling agents
own `hol-c16..c20` (done); C21 stayed out.

---

## 1. The generator

`panWrapperLib.mk_foldWrapper` (and its worker `mk_foldMainRefine`) is the C20 hand
stack turned into a function. It emits the five theories of the fuel-budgeted fold
wrapper mechanically:

```
mk_foldWrapper
  { prefix, ffiName, ffiDef, ctrlStagedDef, arenaOff, koff, specWord,
    coreName, coreFramed, coreNoFFI, unfoldCore,
    mainBodyName, mainBodyDef, progName, progDef, linkB }
: { mainRefine, callMainRun, mainSemantics, semanticsDecls, machineCode }
```

Given a fold's **core** (a C19-style framed loop-core theorem `coreFramed` +
`coreNoFFI`), its **data** (the `ctrlStaged` staging relation, the `FFI` oracle
contract, the `mainBody` surgery), the **offsets** (`arenaOff = ctrl+32`, `koff =
ctrl+8`), the **spec word**, and its **Link B**, the generator produces:

| generated theory | what it is | C20 hand analogue |
|---|---|---|
| `…MainBody_refines` | whole `main` body → `Return 0`, result word staged, FFI trace | `hashMainRefine` (178 ln) |
| `…_call_main_run` / `…_main_semantics` | fuel-budgeted clock-lift `Call main → Terminate Success` | `hashSem` (69 ln) |
| `…Prog_semantics_decls` | decls-level whole-program Link A | `hashInstall` (47 ln) |
| `…_machine_code` | **Link A ∘ Link B = spec → machine code** | `hashEndToEnd` (56 ln) |

The generator is a **fixed** ML spine-peel over the deployed fold spine (`ctrl :=
@base ; base := ctrl+32 ; @load_vec ; len := lds ctrl ; acc/i/b := 0 ; WHILE-core ;
st ctrl+8, acc ; @report_vec ; return 0`) plus the C20 tactic sequence with the
varying tokens parameterized. The **composition-seam friction C20 §4 diagnosed**
(assumption pollution swamping `metis`/`DECIDE`/`simp` at the whole-machine seam)
is baked in as the fixed part: the generator discharges the `∃K. 0 < K ∧ LENGTH
input < K` side-condition from a **clean-context** `exists_big` helper via
`MATCH_ACCEPT_TAC`, exactly the C20 pattern. No per-fold tactic hygiene.

The three ctrl-keyed control lemmas (`eval_load_ctrlc`, `eval_ctrl_add`,
`evaluate_store_ctrl_acc`) and the loop-frame lemma (`While_frame`) — program-
agnostic — moved into a shared theory `foldWrapCommon`, reused by every fold's core
and by the generator.

## 2. REGRESSION — the generator reproduces C20 byte-identically

`hashGen` is a **single `mk_foldWrapper` call** with the C20 hash parameters. Its
`hash_machine_code`, verbatim `show_tags` (from the `verifyC21` audit theory):

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ (compile_prog_max c mc hashBytesProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   … (the standard pan_to_target install package) … ∧
   pan_installed … ms (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
   hashFFI input s ∧ (∃K. 0 < K ∧ LENGTH input < K) ⇒
   ∃loadEv rb.
     machine_sem mc ffi ms ⊆
     extend_with_resource_limit'
       (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
       {Terminate Success
          (s.ffi.io_events ++ loadEv ++
           [IO_event (ExtCall «report_vec»)
              (word_to_bytes (n2w (hashBytesN input)) F) rb])}
```

This is the **same theorem C20 proved by hand** (C20 §1), now emitted by the
generator over the same parser-output `hashBytesProg`. The five hand scripts
(`hashMainRefine`, `hashSem`, `hashInstall`, `hashEndToEnd`, and the wrapper half of
`hashWrapperLinkA`) are **gone** from C21 — replaced by the 14-line parameter record
in `hashGenScript.sml`. Only the fold-specific **data** (`hashData`: `hashCtrlStaged`
/ `hashFFI` / `hashMainBody` surgery) and the fold **core** (`hashCore`) remain, as
generator inputs.

## 3. SECOND FOLD — a genuinely different real serve fold, generator-closed

The second fold is the **HTTP Content-Length decimal accumulator**: an HTTP body's
`Content-Length` header value is a run of decimal digit bytes, parsed to a number
by the base-10 Horner fold `acc := acc*10 + d` — a real serve fold (drorb parses it
on every request with a body), and **genuinely different** from the cache-key hash:
base-10 Horner, not the mul-add-1 digest. Different loop body, different spec word,
different Nat→word homomorphism.

`clen_machine_code` (theory `clenGen`), verbatim `show_tags`:

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … the same pan_to_target install package over clenProg … ∧
    pan_installed … ) ∧ clenFFI input s ∧ (∃K. 0 < K ∧ LENGTH input < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆
    extend_with_resource_limit' … 
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (n2w (clenN input)) F) rb])}
```

Read literally: every behaviour of the installed x64 code CakeML emits for the
Content-Length parser is the single terminating trace reporting the 8-byte word
`n2w (clenN input)` = `FOLDL (λa d. a*10 + d) 0 input` mod 2^64 — the decimal value,
faithful to leanc's fixed-width codegen. `clenProg` is the **verified parser's
output** on `clen.pnk` (`clenProg_is_parser_output`, via `mk_linkB`), so **leanc is
out of the TCB**; the `clenLoopCore` substitution into the parsed `main` fires
against a real parser subterm (`clenData` raises `Fail` at build time otherwise —
the theory builds).

**How much did the second fold cost?** The whole-program wrapper (`MainRefine` +
`Sem` + `Install` + `EndToEnd`) = **one `mk_foldWrapper` call** (0 hand-proof
lines). The genuinely-authored per-fold work:

| clen component | what | lines |
|---|---:|---:|
| `clenBodyA_step` — the C19-style per-step core fill-in | the ONE bespoke tactic obligation | **16** |
| fold core scaffold (spec `clenN`, `clenAcc`, Nat→word homomorphism `clen_word`, `clenLoopCore_refines`, `noFFI`, framed) | mechanical, mirrors C16/C19 | ~90 |
| fold data (`clenCtrlStaged` + `clenFFI` contract + `clenMainBody` surgery) | structurally identical to hash; the trusted FFI assumption | ~50 |
| Link B | **one `mk_linkB` call** | 1 |
| **whole-program wrapper (MainRefine+Sem+Install+EndToEnd)** | **one `mk_foldWrapper` call** | **0** |

Against C20's hand budget for the same wrapper — `hashMainRefine` 178 +
`hashSem` 69 + `hashInstall` 47 + `hashEndToEnd` 56 = **350 hand lines** — the second
fold's wrapper is **0**. The answer to the charge ("does the 2nd fold now cost ~8
lines + 1 generator call, vs C20's ~400 hand lines?") is **yes**: the ~350-line
whole-program wrapper collapses to a generator call; the only bespoke per-fold proof
is the ~16-line core step obligation the C16 schema was designed around.

## 4. The residual (honest)

Two things are still authored per fold and are NOT mechanized by `mk_foldWrapper`:

1. **The fold core** (`clenBodyA_step` + spec + homomorphism). This is
   **inherently** fold-specific — it IS the fold function — and is exactly the
   ~16-line C16/C19 schema fill-in the whole design targets. Not a residual to
   remove; it is the irreducible per-fold input.
2. **The fold data** (`ctrlStaged` staging relation, `FFI` oracle contract,
   `mainBody` surgery — ~50 lines in `clenData`). These are **structurally
   identical** to the hash fold's (same control-block convention: length at
   `ctrl`, arena at `ctrl+32`, result at `ctrl+8`); only the FFI-constant name and
   the folded-in core differ. A further `mk_foldData` generator (emitting
   `ctrlStaged` + `FFI` + `mainBody` from the offsets + the core) would mechanize
   this too — **this is the precisely-scoped next residual**. It is deliberately
   left explicit here because the `FFI` contract is the **single trusted
   assumption** of the whole chain, and there is assurance value in each fold
   stating its I/O contract literally rather than machine-generating it. (The two
   generator calls that DID land — `mk_linkB` and `mk_foldWrapper` — carry no
   trust; they only assemble kernel-checked proofs.)

No genuinely fold-specific *wrapper* residual remains: the MainRefine/Sem/Install/
EndToEnd proofs are fully generated for both folds from the same code path.

## 5. Trust ledger (unchanged from C13–C20; none of it is leanc)

Every C21 theory is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats
(`verifyC21` asserts this adversarially, plus that each end-to-end really mentions
`machine_sem ⊆ {Terminate Success …}` with its spec word — no vacuous/tautological
theorem). `DISK_THM` is the benign CakeML disk-export tag. Both end-to-ends rest
only on: CakeML backend correctness (Link B, via `mk_linkB`), the C16 fold schema
(reused verbatim), each fold's Nat→word homomorphism, and the **single named FFI
contract** (`hashFFI` / `clenFFI` — `@load_vec` / `@report_vec`). leanc is out: the
subject of each is the verified-parser output and the wrapper surgery fires against
a real parser subterm.

## 6. Path to composing `cacheEmptyStage` and `deployStagesFull2`

C20 §7 scoped `cacheEmptyStage` (`keyOf` = two `hashBytes` folds + the C18 `isFresh`
gate) as blocked on this generator. It is now unblocked: each `hashBytes` call site
is a `mk_foldWrapper` fold, the two-fold `keyOf` is two generator invocations over
distinct arena regions threaded through one `main` (each preserving the other's
`acc` via the `While_frame` lemma already in `foldWrapCommon`), and the C18
`isFresh` scalar gate sequences after (scalar-after-fold, both cores `noFFI`). The
remaining compose work is `Seq`-threading the two framed cores + the gate — no new
fold metatheory, and now no per-fold wrapper hand-proof. The whole
`deployStagesFull2` fold reduces to: one `mk_foldWrapper` per fold site + the scalar
gates + the seam composition.

## 7. Verdict

- **Is `mk_foldWrapper` a real generator?** **Yes** — it reproduces C20's
  `hash_machine_code` byte-identically (the ~450-line hand stack deleted) and
  closes a **second, different** real serve fold (`clen_machine_code`, the
  Content-Length decimal accumulator) spec→machine-code, both from one generator
  call. `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats, leanc out, clean
  `Holmake` green on hbox.
- **2nd-fold cost?** The ~350-line whole-program wrapper → **0 hand lines** (a
  `mk_foldWrapper` call); the only bespoke per-fold proof is the **~16-line**
  C19-style core step obligation.
- **Residual?** The fold **data** (staging relation + FFI contract + mainBody
  surgery, ~50 lines, structurally identical across folds) is still authored per
  fold; a `mk_foldData` generator would mechanize it (the FFI contract is the sole
  trusted assumption, deliberately kept explicit). No wrapper-proof residual
  remains.

## 8. Files (`docs/engine/probes/compiler/hol-c21/`, built on hbox `~/hol-c21`)

**The generator + shared machinery:**
- `panWrapperLib.sml` — extended with **`mk_foldMainRefine` + `mk_foldWrapper`**
  (the C20 hand stack turned into a generator; +327 meaningful ML lines, one-time).
- `foldWrapCommonScript.sml` — shared program-agnostic lemmas: `While_frame`,
  `eval_load_ctrlc`, `eval_ctrl_add`, `evaluate_store_ctrl_acc`.

**Regression (hash) — the hand stack is now a generator call:**
- `hashCoreScript.sml` — the fold core (carried; `evaluate_hashLoopCore_framed`).
- `hashDataScript.sml` — `hashCtrlStaged` / `hashFFI` / `hashMainBody` surgery.
- `hashGenScript.sml` — **the `mk_foldWrapper` call** → `hash_machine_code`.

**Second fold (clen) — the new real serve fold:**
- `clen.pnk` — the emitted Content-Length decimal-fold Pancake.
- `clenLinkBInstScript.sml` — Link B (`mk_linkB`).
- `clenCoreScript.sml` — spec `clenN`, homomorphism `clen_word`, the ~16-line
  `clenBodyA_step`, `evaluate_clenLoopCore_framed`.
- `clenDataScript.sml` — `clenCtrlStaged` / `clenFFI` / `clenMainBody` surgery.
- `clenGenScript.sml` — **the `mk_foldWrapper` call** → `clen_machine_code`.

**Audit + carried deps:**
- `verifyC21Script.sml` — prints both end-to-ends with `show_tags`; asserts
  DISK_THM-only, hyps = 0, non-vacuous.
- carried verbatim: `foldLoopSchemaScript.sml` (C16), `hashBytesLoopScript.sml`
  (C19 hash homomorphism), `panAutoScript.sml`/`panAutoLib.sml` (C15, `mk_linkB`),
  `c14GenericScript.sml`, `hashBytesLinkBInstScript.sml`, `Holmakefile`.
- Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` (14 theories) exit 0.

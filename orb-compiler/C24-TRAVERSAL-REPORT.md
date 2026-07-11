# C24 REPORT — the deployed `traversalStage` path-traversal gate is closed spec→machine-code by an N=1 peel of the C23 composed generator (0 axioms, leanc out)

Gate A asked whether a **7th stage of `Reactor.Deploy.deployStagesFull2`** —
`traversalStage`, the `..`-escape block — could be closed end-to-end with the C23
`mk_composedWrapper` machinery, and what spine-shape adaptation it needed. **C24
lands it.** `traversal_machine_code` (theory `travGen`) is the first full
spec→machine-code theorem for a **traversal gate**, produced by **one
`mk_composedWrapper1` call** — the **N = 1 peel** of the C23 composed generator,
the exact residual C23 §5 caveat-1 named ("a stage with a different fold count
needs the ML peel loop extended over the fold list — mechanical, not yet written
for N ≠ 2").

**Verdict up front.**
- **Is `traversalStage` closed end-to-end?** **Yes.** `traversal_machine_code` is
  `[oracles: DISK_THM] [axioms: ]`, **hyps = 0, 0 cheats**, non-vacuous — a real
  `machine_sem mc ffi ms ⊆ … {Terminate Success (… report_vec … (word_to_bytes
  (travDecide input) F) …)}` that reports the **actual** traversal decision word
  over the path-byte input. leanc is out of the TCB: `travProg` is the CakeML
  **verified parser's** output on `traversal.pnk`, and the fold body / gate the
  proof reasons about are **genuine parser subterms** (the `travData` surgery
  raises if they are not).
- **Did `mk_composedWrapper` apply directly?** **No — and that is the finding.**
  `traversalStage`'s decision is a **single fold + scalar gate** (one scan of the
  path bytes running a 5-state escape automaton, then a state→`blocked`/`allowed`
  gate), not the 2-fold+gate shape the C23 generator peels. So the ML peel loop
  was **extended to N = 1** (`mk_composedMainRefine1` / `mk_composedWrapper1`):
  the composed spine loses fold₁ + its retarget + the save/scalar, and the gate
  reads the fold accumulator in `«acc»` directly. **Same fixed tactics as
  `mk_composedMainRefine`, minus the deleted nodes** — no new metatheory.
- **Is it non-vacuous / grounded?** **Yes.** `verifyC24` machine-checks the decision
  truth table on **real path bytes** (`travDecide = 1w` BLOCKED, `0w` ALLOWED):

  | path input (bytes) | `travEsc` state | `travDecide` |
  |---|:---:|:---:|
  | `/../etc/passwd` | `4w` (escape found) | **`1w` BLOCKED** |
  | `/a/../b` | `4w` | **`1w` BLOCKED** |
  | `/foo/..` (trailing `..`) | `2w` | **`1w` BLOCKED** |
  | `/health` | `3w` (dirty) | `0w` ALLOWED |
  | `/etc/passwd` | `3w` | `0w` ALLOWED |

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C23 used. **Dir:**
`docs/engine/probes/compiler/hol-c24/` (built on hbox `~/hol-c24`, full `Holmake`
exit 0). Sibling agents own `hol-c16..c23` (done); C24 stayed out of them and
copied `panComposedLib`/`composedCommon`/`panWrapperLib`/`panAutoLib` +
fold/gate deps from `hol-c23`.

---

## 1. Ground truth — the REAL `traversalStage` (drorb `Reactor/Deploy.lean`)

`traversalStage` (`Deploy.lean:985`) is a GATE: on a request whose target
`..`-escapes it short-circuits to the serializer-built `traversalBlocked404`;
otherwise it passes through. Its decision is `targetEscapes` (`:745`) =
`escapesSegs (rawSegsOf req)` (`:725`):

```
escapesSegs segs = (Route.Path.decodeSegs segs).contains ".."
```

i.e. percent-decode each raw path segment **once** (`decodeSegs = segs.map
decodeSeg`, `Route/Path.lean:61` — the single %-boundary), then check whether any
decoded segment equals `".."`. This is a **fold/scan over the path** producing a
boolean, then a gate — **one** input (the path), so **one** fold. The drorb
grounded facts the C24 model reproduces are `escapesSegs ["..","etc","passwd"] =
true`, `escapesSegs ["health"] = false` (`Deploy.lean:906,913`).

**Spine shape: 1 fold + 1 scalar gate.** Not the 2-fold+gate of C22/C23 (which had
two inputs — method and route). This is the key spine-shape difference.

## 2. The stage, modelled and emitted (`traversal.pnk` → verified parser → `travProg`)

`travEsc : num list → word64` is a `FOLDL` over a **5-state escape automaton**
`escAcc` on the path bytes (`travCore`):

- state `0` = at a segment boundary (prev byte was `/` or start)
- state `1`/`2` = one / exactly two leading `.` in the current segment (`..`)
- state `3` = current segment is *dirty* (a non-dot byte, or > 2 dots)
- state `4` = **ESCAPE FOUND** (absorbing) — a `..` segment was closed by `/`

`escAcc` branches only on the bytes `47w` (`/`) and `46w` (`.`) — a **genuinely
different fold core** from the C21/C22 `hashBytes` Horner (the audit asserts
`escAcc`/`travEsc` mention neither `hashBytes` nor `hashAcc`). `travDecide`
reports `1w` iff the final state is `4` (an internal `..` closed by `/`) or `2`
(a trailing bare `..`) — reproducing the `.contains ".."` half of `escapesSegs`.
Decode is named as the drorb boundary (`Route.Path.decodeSegs`); the fold is the
post-decode check.

`traversal.pnk` is emitted on the C0–C23 path (one arena, control block `[len |
result | … | path bytes @+32]`), parsed by the **CakeML-verified**
`parse_topdecs_to_ast` → `travProg` (`travLinkBInst`, `mk_linkB`). `travCore`
**extracts** `escBody` / the while-loop / `travGate` as genuine subterms of
`travProg` (no hand transcription); `travData`'s surgery refolds the deployed
`travMainBody` to `escLoop`/`travGate` and **raises if they are not parser
subterms** — leanc stays out of the TCB.

## 3. The theorem (`travGen`, verbatim `show_tags`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … pan_to_target install package over travProg … ∧ pan_installed … ) ∧
    travFFI input s ∧ (∃K. 0 < K ∧ LENGTH input < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆ extend_with_resource_limit' …
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (travDecide input) F) rb])}
```

`travFFI` is the single named FFI-oracle contract (`@load_vec` stages the path
arena + length; `@report_vec` emits the decision word) — the single-arena
analogue of C22's `cacheFFI`. It is the only trusted assumption; the theorem
carries **no axioms** (`verifyC24`: `axioms = 0`).

## 4. What the stage cost — the honest quantification

| piece | lines | kind |
|---|---:|---|
| `escAcc` / `travEsc` / `travDecide` spec | 11 | the stage decision |
| `escBody` / `escLoop` / `travGate` | **0** | EXTRACTED from `travProg` (genuine subterms) |
| **`escBody_step`** (the new fold-core step) | **~75** | the escape automaton is branchy (5 states) → bigger than the ~16-line `hashBytes`/`clen` step |
| `escBody_mem` / `escBody_ctrl` / `escLoop_noFFI` | ~20 | mem/ctrl frame facts (branchy body ⇒ `COND_RAND` case-split) |
| **`escLoop_framed`** (via body-generic `loop_frame`) | **~29** | one `loop_frame` instantiation (the C23 engine, reused unchanged) |
| `evaluate_travGate` (the one gate lemma) | **~23** | 2-arm `Cmp Equal` gate (state = `4w`/`2w`) |
| `travStaged`/`travFFI` + `travMainBody` surgery | ~55 | single-arena analogue of `cacheStaged`/`cacheFFI` |
| **whole-program wrapper (MainRefine+Sem+Install+EndToEnd)** | **0** | one `mk_composedWrapper1` call (13-line spine record) |

**One-time infrastructure (amortized across all single-fold+gate stages):** the
N = 1 peeler `mk_composedMainRefine1` + `mk_composedWrapper1` (**~355 ML lines**
in `panComposedLib`) — the C23 `mk_composedWrapper` (2-fold) with fold₁'s peel /
retarget / save and the scalar **deleted**, and the gate retargeted to read
`«acc»`. This is the exact mechanical extension C23 §5 named; it writes **zero
axioms** and carries no trust (it only assembles kernel-checked proofs). The
proof of `traversal_machine_code` reused it via a single generator call.

**Per-stage cost, then:** its new fold core (`escBody` + `~75`-line branchy step +
`~29`-line framed core) + its `~23`-line gate lemma + a `13`-line record + one
generator call. The branchy automaton makes the *step* lemma larger than a
Horner fold's, but the whole-program wrapper is again **0 hand lines**.

## 5. Did `mk_composedWrapper` apply cleanly? — the spine-shape answer, and "each stage bounded"

**No, and this is the point of the probe.** `traversalStage` is **N = 1** (one
fold + gate), a different spine count than the C22/C23 stages (N = 2). The 2-fold
generator does not peel it: there is no second arena to retarget to, and the gate
reads the single fold's accumulator, not two saved words. Rather than hand-write a
bespoke ~350-line `MainRefine`, the ML **peel loop was extended to N = 1** — a
**deletion** from the C23 template (fold₁ block + retarget + save + scalar
removed), which is strictly simpler than the N = 2 peeler and is the mechanical
generalization C23 promised.

**Consistent with "each stage bounded"? Yes.** After C24 the deployed stage
classes are:
- **scalar-branch** stages (redirect, rate) — C18, one line each. Done.
- **single-fold value reports** (Content-Length) — C21 `mk_foldWrapper`. Done.
- **single-fold + gate** gates (**this class**: `traversalStage`) — **now one
  `mk_composedWrapper1` call + a fold core + a gate lemma.** Done (N = 1 exercised).
- **two-fold + gate** gates (cache-key freshness [C22/C23], `(method,route)`
  admission [C23]) — one `mk_composedWrapper` call + cores + gate. Done (N = 2).
- **general loops** (parse `While` [C13], DEFLATE, JWT FSM, CIDR walk) — still
  open, unchanged from C18's map. This remains the standing residual.

The fold-count residual C23 named (N ≠ 2) is now **closed for N = 1**; a stage
with N ≥ 3 folds would extend the same peel loop the same mechanical way (walk the
fold list forward, node-walk the extra retargets backward).

## 6. Trust ledger (unchanged from C13–C23; none of it is leanc)

`traversal_machine_code` is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats
(`verifyC24` asserts this adversarially + non-vacuity + the grounded truth table
+ that the fold is genuinely distinct from the hash cores). `DISK_THM` is the
benign CakeML disk-export tag. The theorem rests only on: CakeML backend
correctness (Link B via `mk_linkB`), the C16 fold schema, the body-generic
`composedCommon.loop_frame` frame engine (reused unchanged), and the single named
FFI contract `travFFI`. `mk_composedWrapper1` and `mk_linkB` carry **no trust** —
they only assemble kernel-checked proofs; the generator writes zero axioms
(`verifyC24`: `axioms = 0`). The full `Holmake` (whole `hol-c24` tree, including
C22/C23 rebuilt against the extended `panComposedLib` — so the N = 1 addition did
**not** break the N = 2 generator) is **exit 0**.

## 7. Files (`docs/engine/probes/compiler/hol-c24/`, built on hbox `~/hol-c24`)

**The stage (new):**
- `traversal.pnk` — the emitted single-fold + gate program.
- `travLinkBInstScript.sml` — Link B (`mk_linkB` on `traversal.pnk`).
- `travCoreScript.sml` — `escAcc`/`travEsc`/`travDecide` spec; `escBody`/`escLoop`/
  `travGate` extracted from `travProg`; `escBody_step`/`_mem`/`_ctrl`,
  `escLoop_framed` (via `loop_frame`), `evaluate_travGate`.
- `travDataScript.sml` — `travStaged`/`travFFI` + `travMainBody` surgery (raises
  if `escLoop`/`travGate` are not parser subterms).
- `travGenScript.sml` — the **one** `mk_composedWrapper1` call → `traversal_machine_code`.
- `verifyC24Script.sml` — the adversarial audit (DISK_THM-only, hyps = 0,
  non-vacuous; the `travDecide` truth table + automaton states; the fold is
  distinct from the hash core; `loop_frame` non-vacuous).

**The peel-loop extension (one-time infra, in the carried `panComposedLib.sml`):**
- `mk_composedMainRefine1` + `mk_composedWrapper1` — the N = 1 peel of the C23
  `mk_composedWrapper` (~355 ML lines; fold₁/retarget/scalar deleted, gate reads
  `«acc»`).

**Carried verbatim from C23:** `composedCommonScript` (the `loop_frame` engine),
`foldLoopSchema`, `foldWrapCommon`, `c14Generic`, `hashBytesLoop`, `hashCore`,
`panAuto(Lib)`, `cacheKey*`, `admit*`, `verifyC22/23`, `Holmakefile`.
Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0.

# CN REPORT — LINK A for the boundscan SCAN `While` LOOP, discharged: a general-clock loop-invariant induction over real `panSem$evaluate` that computes EXACTLY the Lean digest fold `scanFrom` over the arena view — the multi-report residual (C0 §4-A-2 / C1 §5 / C3 §5) now proven, 0 axioms

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Proof tree:** `/home/hbox/src/cakeml` at `ed31510b3` (the exact tree C1–C10 used).
**HOL4:** `/home/hbox/src/HOL` at `a9846ebe2` (Trindemossen 2), Poly/ML 5.9.2.
**This lane's HOL4 scratch:** `/home/hbox/hol-boundscan-linka/` (self-contained; no CakeML-tree files modified).
**Theory:** `boundScanLoopLinkA` — built green, `[1/1] OK` in 8s, `axioms "boundScanLoopLinkA" = 0`.
**Ground:** C0-REPORT §4-A-2, C1-REPORT §5, C3-REPORT §5 — each named the boundscan digest scan `While` UNCLOSED. This lane closes it.

---

## 0. TL;DR — what this lane discharges, and the exact boundary

The boundscan stage (C0/C10/CN-BYTES-BRIDGE — the region/view bounds-check + 24-bit
rolling digest) factors its front-end refinement (Link A) into **the bounds `If`
decision** (closed in C1, `evaluate_boundsChk`) and **the digest scan `While`**. Every
prior report named the scan `While` as the recurring long pole and did not close it:

- **C0 §4-A-2:** "The scan `While`. The loop invariant … maintained across the `While`
  clause of `evaluate` … P2 §5 condition #1 … where the front-end person-hours go."
- **C1 §5 / C10 §7:** the scan-`While` loop invariant "the deferred multi-day item."
- **C3 §5.5:** C3 built the loop-induction *skeleton* for a **different** body (the C2
  saturating-counter `mstep`, a separate `«b»` slot, a `base+i` address) and explicitly
  left the boundscan digest owing "its digest step (`*31 + b`) proved as a body lemma
  analogous to `evaluate_stepBody`."

This lane proves Link A for the **actual** boundscan scan loop — the `While` transcribed
**verbatim from the C10 verified-parser output** `boundScanLinkB$boundScanProg`, with the
parser's transparent `Annot` no-ops in place, the `Panop Mul` / `Op And` / 3-summand
`Op Add [«buf»;«off»;«i»]` the parser produced — against the **real** `panSem$evaluate`.
The headline (`scanLoop_refines_scanFrom`) states that running the emitted `While` from
`(acc=0, i=0)` with enough clock leaves `«acc»` holding **exactly** `n2w (scanFrom a off
len 0)` — the in-bounds arm of the Lean `C0.boundScan a off len` digest. Every one of the
eight theorems carries `[oracles: DISK_THM] [axioms: ]`; the theory introduces **no
`new_axiom`, no `cheat`, no extra oracle**.

**Honest boundary (unchanged from C3 §5, named not hidden):** the theorem is the scan
`While` from an invariant precondition. Establishing that precondition (`loopInv … 0 0`)
from the whole `main` — the `Dec` initialisers, the `@load_vec` FFI that fills the buffer,
and the view relation `vs = a[off .. off+len)` — is the whole-program frame that sits
outside this theorem (§5). This lane pays the loop; the frame is the named next step.

---

## 1. What was proven (theory `boundScanLoopLinkA`, all `[oracles: DISK_THM] [axioms: ]`)

Verbatim from the theory's own dump (`hol-boundscan-linka/verify_out.txt`, produced by the
build with `Globals.show_tags := true`, not transcribed by hand):

### The digest step — the NEW body lemma C3 §5 named as owed

```
eval_digest_expr:
⊢ loopInv vs bufw offw acc i s ∧ i < LENGTH vs ⇒
  eval s
    (Op And
       [Op Add
          [Panop Mul [Var Local «acc»; Const 31w];
           LoadByte (Op Add [Var Local «buf»; Var Local «off»; Var Local «i»])];
        Const 0xFFFFFFw]) = SOME (ValWord (n2w (dstep acc vs❲i❳)))
```

Real `panSem$eval` of the digest expression = `n2w (dstep acc byte)`, where
`dstep acc b = (acc*31 + b) MOD 16777216` (byte-identical to the Lean/C1 `step`). This is
the piece C2's `evaluate_stepBody` is to the counter FSM: it threads the word multiply
(`Panop Mul` → `pan_op Mul` → `word_mul_n2w`), the `Op Add` (`FOLDR word_add 0w`), and the
24-bit mask (`Op And` with `0xFFFFFF` → `WORD_AND_EXP_SUB1`, i.e. `MOD 2^24`). It is the
analogue C3 §5.5 said "still needs" — now proven.

### One loop iteration preserves the invariant + threads the memory relation

```
evaluate_scanBody:
⊢ loopInv vs bufw offw acc i s ∧ i < LENGTH vs ⇒
  ∃s2. evaluate (scanBody,s) = (NONE,s2) ∧ s2.clock = s.clock ∧
       loopInv vs bufw offw (dstep acc vs❲i❳) (i + 1) s2
```

Runs the two `Annot`-wrapped assigns (`acc := digest`, `i := i+1`) against real
`panSem$evaluate`, re-establishing `loopInv` at `(dstep acc byte, i+1)`. `memRel` survives
because the body writes only locals (`«acc»`, `«i»`).

### The general-clock loop-invariant induction over the clocked `While`

```
scanLoop_unfold:
⊢ loopInv vs bufw offw acc i s ∧ i < LENGTH vs ∧ s.clock ≠ 0 ⇒
  ∃s2. evaluate (scanLoop,s) = evaluate (scanLoop,s2) ∧
       loopInv vs bufw offw (dstep acc vs❲i❳) (i + 1) s2 ∧ s2.clock = s.clock − 1

scanLoop_fold_bounded:
⊢ ∀k vs bufw offw acc i s.
    loopInv vs bufw offw acc i s ∧ LENGTH vs − i ≤ k ∧ LENGTH vs − i ≤ s.clock ⇒
    ∃s'. evaluate (scanLoop,s) = (NONE,s') ∧
         FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (FOLDL dstep acc (DROP i vs))))
```

`scanLoop_fold_bounded` is the loop proper: induction on a bound `k` for the remaining
iteration count, quantified over **all** view lengths, **all** `(acc,i)`, and **all**
sufficient clocks — not a fixed unroll. Each step unfolds one clocked `While` iteration
(`scanLoop_unfold`, threading `panSem`'s `dec_clock`/`fix_clock` bookkeeping) and applies
the hypothesis at the next `(digest, index)`. The clock decreases by exactly one per
iteration (the body has no `Tick`/`While`/`Call`), so `LENGTH vs − i ≤ s.clock` rules out
`TimeOut`.

### The whole scan = the Lean SPEC's `scanFrom` over the arena view

```
scanLoop_refines_digest:
⊢ loopInv vs bufw offw 0 0 s ∧ LENGTH vs ≤ s.clock ⇒
  ∃s'. evaluate (scanLoop,s) = (NONE,s') ∧
       FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (FOLDL dstep 0 vs)))

foldl_dstep_scanFrom:                    (* pure list bridge, kernel-checked *)
⊢ ∀len off a acc. off + len ≤ LENGTH a ⇒
    FOLDL dstep acc (TAKE len (DROP off a)) = scanFrom a off len acc

scanLoop_refines_scanFrom:               (* THE HEADLINE — loop = Lean spec fold *)
⊢ loopInv (TAKE len (DROP off a)) bufw offw 0 0 s ∧
  LENGTH (TAKE len (DROP off a)) ≤ s.clock ∧ off + len ≤ LENGTH a ⇒
  ∃s'. evaluate (scanLoop,s) = (NONE,s') ∧
       FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (scanFrom a off len 0)))
```

`scanFrom` here is byte-identical to `boundScanLinkA$scanFrom` (C1), the LEFT-recursive
digest the Lean `C0.boundScan` in-bounds arm returns. `foldl_dstep_scanFrom` proves the
`FOLDL dstep` the loop computes over the viewed slice `TAKE len (DROP off a)` **is**
`scanFrom a off len` — so the loop result is the Lean spec's scan, not a coincidentally
shaped fold. `scanLoop_refines_scanFrom` is the composed headline: the emitted `While`
computes exactly the Lean `scanFrom` over the arena view.

### Faithfulness to the emitted program — CLOSED (not transcribed-and-asserted)

```
scanLoop_faithful:
⊢ extract_while_decl (HD boundScanProg) = SOME scanLoop
```

Kernel-checked equation that `scanLoop` **is** the (unique) `While` inside
`boundScanLinkB$boundScanProg` — the CakeML-verified Pancake parser's output on leanc's
emitted `boundscan.pnk` text (C10). A fully-qualified-constant check on the theorem
confirms it references the **real** `boundScanLinkB$boundScanProg`, not a local mirror:

```
consts in scanLoop_faithful =
  boundScanLinkB$boundScanProg    ← the C10 verified-parser program (NOT re-declared here)
  boundScanLoopLinkA$scanLoop
  boundScanLoopLinkA$extract_while_decl
```

So the loop this lane reasons about is not a hand transcription of the `.pnk` (C1/C3's
open residual) — it is *structurally extracted from* the verified parser's AST, with the
transparent `Annot` nodes the parser inserts left in place. Parser-faithfulness **for the
loop** is closed.

---

## 2. How genuinely a LOOP, and how it differs from C3

C3's `machineLoop` and this `scanLoop` share the loop **skeleton** (`loopInv`, `Seq_NONE`,
the `unfold`/`fold_bounded` induction shape) — that is the reusable machinery C3 paid for.
But `scanLoop` is a materially **different** loop, and reusing the skeleton required three
real new pieces:

1. **A new body.** C3's body was `mstep` (a saturating counter with a separate `«b»` byte
   slot and `stepBody`). Boundscan's body is the **inline digest** `acc := ((acc*31) +
   ld8(buf+off+i)) & 16777215` — `Panop Mul`, a 3-summand `Op Add` address `[«buf»;«off»;
   «i»]`, and an `Op And` mask, with **no** `«b»` slot. The body lemma `eval_digest_expr`
   is entirely new (§1) — the word-arithmetic of the mask/multiply is where the work is.
2. **A double-offset memory read.** C3 read `base+i`; boundscan reads `buf+off+i`. `memRel`
   is stated over the viewed slice at base `bufw+offw`, and `eval_loadbyte` folds the
   3-summand address `Op Add [«buf»;«off»;«i»]` to `(bufw+offw) + n2w i` before the
   `mem_load_byte` read.
3. **The fold connects to the Lean spec.** C3 landed at `FOLDL mstep`. This lane adds
   `foldl_dstep_scanFrom` so the result lands at the Lean `C0.boundScan` presentation
   `scanFrom a off len 0` — the actual spec fold, not just a fold.

The invariant `acc < 2^24` is re-established *unconditionally* every step (the `MOD 2^24`
mask), simpler than C3's conditional saturation (`mstep_le`).

## 3. Proof-engineering notes (the crux costs, each paid and verified by building)

The prior in-progress attempt (`boundScanLoopLinkA.eval_digest_expr.dumpedheap`, 452 MB)
failed at the digest lemma. Three concrete obstacles, each diagnosed by driving the goal
and closed:

- **`simp [MULT_COMM]` loops in the srw_ss simpset.** The digest reduces to
  `n2w ((31*acc+b) MOD 2^24) = n2w ((acc*31+b) MOD 2^24)`; adding `MULT_COMM` to `srw_ss`
  fights its built-in numeral-first multiplication ordering and does not terminate. The
  fix is the *bare* `simp []` — `srw_ss`'s own arithmetic normaliser closes it. (Verified:
  the closer was tested in isolation on the exact residual before editing the script.)
- **`simp` cannot discharge `is_valid_value`.** The `Assign «acc»` leaves
  `is_valid_value s Local «acc» (ValWord …)`, which unfolds (via `lookup_kvar` →
  `FLOOKUP s.locals «acc»`) to a shape check that needs the `FLOOKUP s.locals «acc»`
  *assumption*. Plain `simp` ignores assumptions; folding the `is_valid_value`/`lookup_kvar`
  /`shape_of` defs into the assumption-using `asm_simp_tac (srw_ss())` closes it.
- **An `Annot`-led `Seq` breaks `first_assum ACCEPT_TAC`.** The parser wraps each assign in
  `Seq (Annot …) (Assign …)`; the `Seq_NONE` assembly then `qexists`es the *unchanged*
  pre-`Annot` state, so the middle conjunct is `s.clock = s.clock` — a reflexivity, not an
  assumption. `first_assum ACCEPT_TAC` (which C3 used, its `Seq` had no leading `Annot`)
  fails; `(first_assum ACCEPT_TAC ORELSE REFL_TAC)` handles both.

None uses `cheat`/`new_axiom`/an oracle; the footprint audit (§4) is clean.

## 4. Trust footprint — crisp

- **Theory axioms: 0** (`axioms "boundScanLoopLinkA" = 0`, printed by the build).
- **Oracles: `DISK_THM` only** — the tag every loaded CakeML/HOL proof carries; there is
  **no** `cake_native_bootstrap` or any lane-specific oracle here (this is the *front-end*
  refinement; the native-compile oracle is CN-BYTES-BRIDGE's Layer 2, a different seam).
- Every one of the eight theorems: `[oracles: DISK_THM] [axioms: ]`.

## 5. What it rests on — the exact remaining residuals (named, not papered over)

1. **The whole-program frame that establishes `loopInv … 0 0`.** `scanLoop` is the `While`
   in isolation (the `else` arm of the bounds `If`). The full `main` wraps it in
   `Dec «acc» 0`, `Dec «i» 0`, and — crucially — the `@load_vec` FFI that fills the buffer.
   `loopInv`'s `memRel` (the view bytes sit at `bufw+offw+j`) and the initial locals must be
   **discharged from that FFI postcondition + the `Dec` frame**. This lane *assumes*
   `loopInv … 0 0`; connecting it to `main` is the named next step — **identical** to C3
   §5.1's boundary, not new research.
2. **The `vs = TAKE len (DROP off a)` view relation** (a hypothesis of
   `scanLoop_refines_scanFrom`) is exactly what `@load_vec` establishes (the loaded buffer
   at `buf` holds arena `a`, so its `off..off+len` bytes are the view). Named as the FFI
   boundary; not discharged here.
3. **`memRel` altitude.** Stated at `mem_load_byte` (the byte-read result), not unfolded to
   `get_byte`/`byte_align`/endianness — the packing that *populates* memory is the FFI's
   job (C3 §5.2, unchanged).
4. **The clock precondition** `LENGTH vs ≤ s.clock` is the standard CakeML clocked-semantics
   "enough fuel"; the top-level `semantics` wrapper existentially quantifies the clock. Not
   a limitation — the standard shape (C3 §4).
5. **Composing the bounds `If` with the loop into one `main`-level Link A.** C1
   (`evaluate_boundsChk`) proved the bounds decision; this lane proved the scan loop. The
   full `main` body `If(bounds){result:=sentinel} else {Dec; Dec; scanLoop; result:=acc}` as
   a single Link-A theorem for `boundScanProg` is the mechanical `Seq`/`If`/`Dec` threading
   of the two proven pieces — an assembly step, no longer an open loop-induction item.
6. **Link B / spec→machine-code.** Unchanged and out of this lane: the backend refinement is
   C10 + CN-BYTES-BRIDGE (the `compile_prog`↔`compile_prog_max` packaging lemma, the
   machine-state install package, the single FFI-oracle spec). This lane is Link A only.

None of the above is leanc; none reintroduces the in-logic EVAL cost.

## 6. Scope note

This is a **HOL4/CakeML** lane (the COMPILER track). It touches no Lean spec, no Rust
dataplane, no `Datapath.lean`, no `lakefile`, and no `libdrorb` — so there is no
`cargo`/`build-dataplane-lib.sh` delta to merge; the mergeable artifact is the new HOL4
theory + Holmakefile + this report.

## 7. Files

**On hbox** (`/home/hbox/hol-boundscan-linka/`, self-contained): `boundScanLoopLinkAScript.sml`,
`Holmakefile` (`INCLUDES` the CakeML pancake/parser/backend dirs + `~/hol-c10` for the
verified-parser program), `boundscan.pnk`, `ast.out` (the parser output the loop is
extracted from), `verify_out.txt` (the build's own tags/axioms dump).

**In this repo** (`docs/engine/probes/compiler/hol-boundscan-linka/`): the same five files,
byte-identical (`md5` matched hbox), plus this report.

## 8. Reproduce (hbox)

```
ssh hbox@hbox.local
cd ~/hol-boundscan-linka
export CAKEMLDIR=$HOME/src/cakeml
export PATH=$HOME/src/HOL/bin:$PATH
Holmake boundScanLoopLinkATheory.uo        # ~8s (loads prebuilt panSem/parser + hol-c10)
# tags + axiom footprint:
hol < /tmp/verify_bsl.sml                   # prints the 8 theorems, all [oracles: DISK_THM]
                                            #   [axioms: ], and axioms = 0
```

## 9. Bottom line

The compiler lane's recurring long pole for the boundscan primitive — "the digest scan
`While` … a loop-invariant induction over `panSem`'s clocked `While`," named UNCLOSED in
C0, C1, C10, and left for the digest body by C3 — is now **preservation-proven in full**:
a general-clock loop-invariant induction over the real clocked `While`, with the new digest
body lemma, the double-offset byte-memory relation threaded, the loop result shown equal to
the Lean spec's `scanFrom` over the arena view, and the loop shown to be the exact `While`
inside the verified-parser program — kernel-checked, 0 axioms, `DISK_THM` only. What remains
for a whole-`main` Link-A claim is the `Dec`/FFI frame that establishes the loop's
precondition (the C3-named boundary) and the mechanical `If`+loop composition — engineering
and checking, no longer an open loop-induction research item.

# CN REPORT — RUNG-3 WHOLE-MAIN Link-A frame: the two mechanical residuals of the whole-`main` frame DISCHARGED in-logic — the `scanLoop` locals-frame (CN-RUNG3-FINISH §2.3.1, "engineering, hit tactic friction, NOT closed") and the else-arm `Dec`/`Seq` threading (§2.3.2) — lifting `scanLoop_refines_scanFrom` to the whole `elseBranch`, with the `@load_vec` FFI-oracle contract (§2.3.3) scoped as the single explicit `elsePre` hypothesis. `[oracles: DISK_THM] [axioms:]`, 0 theory axioms.

**Date:** 2026-07-10 · **Machine:** hbox (`ssh hbox@hbox.local`, 24-core, io_uring) · **Track:** COMPILER (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.
**Proof tree:** `/home/hbox/src/cakeml` @ `ed31510b3`. **HOL4:** `/home/hbox/src/HOL` (Trindemossen 2, stdknl), Poly/ML.
**This lane's HOL4 scratch:** `/home/hbox/hol-rung3-wholemain/` (new, self-contained; no CakeML-tree file modified) — mirrored to `docs/engine/probes/compiler/hol-rung3-wholemain/` (`boundScanWholeMainScript.sml` md5 `dfe16981…` == hbox).
**Ground:** `CN-RUNG3-FINISH-REPORT.md` §2.3 (the whole-`main` frame residual: three named items) + `CN-RUNG3-INSTALL-REPORT.md` (the runtime-install antecedent) + `CN-BOUNDSCAN-LINKA-REPORT.md` (`scanLoop_refines_scanFrom`, the loop core the frame lifts). Loads `boundScanMainFrameTheory` (else-arm identity + loop-body frame lemmas), `boundScanLoopLinkATheory` (`scanLoop`, `loopInv`, `memRel`, `scanFrom`), `boundScanLinkBTheory` (the C10 verified-parser `boundScanProg`).

---

## 0. TL;DR — what closed, what is scoped

CN-RUNG3-FINISH §2.3 factored the whole-`main` Link-A frame into **three** residuals under `boundScan_rung3_native`/`_installed`. This lane discharges the two the report named as *not research* and left open, and scopes the third precisely:

- **Residual (1) — the `scanLoop` locals-frame: CLOSED, kernel-proven.** `scanLoop_locals_frame` (`[oracles: DISK_THM] [axioms:]`) proves that running the whole clocked `While` writes **only** `«acc»`/`«i»` — every other local survives. This is the item CN-RUNG3-FINISH §2.3.1 named as "**engineering, not research**, and is **not closed** here — reported, not faked" (the clock-bounded `While` induction that "hit HOL4 tactic friction … `fix_clock`/nested-`If`/`case res` mis-split under `gvs`/`IF_CASES_TAC`"). It is now closed by a complete induction on the clock over the **real** `panSem$evaluate` `While` clause, threading the proven body lemmas `scanBody_frame`/`_res`/`_clock` (boundScanMainFrame). The friction is resolved: `BasicProvers.TOP_CASE_TAC` for the value/`word_lab` case-splits + `pairarg_tac` for the `fix_clock`-collapsed body pair + `first_x_assum drule` on the strong IH.

- **Residual (2) — the `Dec`/`Seq` threading for the else-arm: CLOSED, kernel-proven.** `elseBranch_frame` (`[oracles: DISK_THM] [axioms:]`) threads the whole else-arm `Dec «acc» 0; Dec «i» 0; scanLoop; «result» := «acc»` — over the **real** `boundScanMainFrame$elseBranch` (which `elseBranch_faithful` kernel-proves **is** the else-arm of the C10 verified-parser `boundScanLinkB$boundScanProg`) — and lands `FLOOKUP s'.locals «result» = SOME (ValWord (n2w (scanFrom a off len 0)))`, the in-bounds arm of the Lean `C0.boundScan` digest. It peels the two `Dec`s to establish `loopInv … 0 0`, applies `scanLoop_refines_scanFrom`, uses the residual-(1) locals-frame to carry `«result»` past the loop (so the trailing store passes `is_valid_value`), and pops the `Dec`s (`res_var`).

- **Residual (3) — the `@load_vec`/`@report_vec` FFI-oracle contract: SCOPED as an explicit hypothesis, never faked.** `elsePre` is the post-`@load_vec` precondition the FFI oracle establishes: the control-block locals `«len»`/`«buf»`/`«off»`/`«result»` are in place, the arena **view** `TAKE len (DROP off a)` sits at `bufw+offw` (`memRel`), the region is in-bounds (`off+len ≤ LENGTH a`), and the clock suffices. `elseBranch_frame` runs **from** `elsePre`. Establishing `elsePre` from the abstract `s.ffi` oracle is the irreducible front-end↔C-driver contract (CN-RUNG3-FINISH §2.3.3) — named as the hypothesis, not produced.

**No `native_decide`/`ofReduceBool` (HOL4 has none), no `cheat`, no `new_axiom`, no extra oracle.** All four new theorems carry `[oracles: DISK_THM] [axioms:]`; `axioms "boundScanWholeMain" = 0`. There is **no** `cake_native_bootstrap` here — this is the front-end refinement, the same seam as CN-BOUNDSCAN-LINKA.

---

## 1. The theorems (verbatim from the kernel; §4 fresh-session audit)

### Residual (1) — the `scanLoop` locals-frame

```
scanLoop_locals_frame                                      [oracles: DISK_THM] [axioms: ]
⊢ ∀s s' v.
    evaluate (scanLoop,s) = (NONE,s') ∧ v ≠ «acc» ∧ v ≠ «i» ⇒
    FLOOKUP s'.locals v = FLOOKUP s.locals v
```

`scanLoop` is `boundScanLoopLinkA$scanLoop` — the exact `While` inside the C10 verified-parser program (`scanLoop_faithful`). The proof is a complete induction on `s.clock`: one clocked-`While` iteration `dec_clock`s (so the recursive arm has strictly smaller clock, discharging the IH), `scanBody_res` rules out `Break`/`Continue`/`TimeOut`, `scanBody_frame` carries the frame across the body, and the trailing `«result»`-preservation chains through. `fix_clock` collapses automatically (the body has no `Tick`/`While`/`Call`), which is what defeated the earlier `gvs` attempt.

### Residual (2) — the else-arm `Dec`/`Seq` frame

```
elseBranch_frame                                          [oracles: DISK_THM] [axioms: ]
⊢ elsePre a off len bufw offw s ⇒
  ∃s'. evaluate (elseBranch,s) = (NONE,s') ∧
       FLOOKUP s'.locals «result» = SOME (ValWord (n2w (scanFrom a off len 0)))
```

with the **explicit FFI-postcondition hypothesis** (residual (3), scoped):

```
elsePre a off len bufw offw s ⇔
  FLOOKUP s.locals «len»    = SOME (ValWord (n2w len)) ∧
  FLOOKUP s.locals «buf»    = SOME (ValWord bufw) ∧
  FLOOKUP s.locals «off»    = SOME (ValWord offw) ∧
  (∃rv. FLOOKUP s.locals «result» = SOME (ValWord rv)) ∧
  memRel (TAKE len (DROP off a)) (bufw + offw) s ∧          (* the vs = a[off..off+len) view *)
  off + len ≤ LENGTH a ∧ len < 2⁶³ ∧
  EVERY (λx. x < 256) (TAKE len (DROP off a)) ∧ len ≤ s.clock
```

`elseBranch` is `boundScanMainFrame$elseBranch`; `elseBranch_faithful` (CN-RUNG3-FINISH) kernel-proves it **is** the If's else-arm of `boundScanLinkB$boundScanProg`. `scanFrom` is `boundScanLoopLinkA$scanFrom` (C1's `step` = `(acc*31+b) mod 2²⁴`). So this lifts to the **real** program's else-arm and the **real** Lean spec fold. The supporting `elseCore` (whole loop+store at the post-`Dec` state) and the clock-monotone `Seq_NONE_le` (needed because the loop consumes clock, so the plain `Seq_NONE` clock-preservation does not apply to the `Seq` wrapping `scanLoop`) are the two internal steps; both `[oracles: DISK_THM] [axioms:]`.

**How residual (2) uses residual (1):** after the loop leaves `«acc» = n2w (scanFrom …)`, the trailing `«result» := «acc»` must find `«result»` still bound to a `ValWord` (for `is_valid_value`) — `scanLoop_locals_frame` (with `«result» ≠ «acc»,«i»`) delivers exactly that. The two closed residuals compose here.

---

## 2. How far it lifts `scanLoop_refines` toward `semantics_decls s «main» boundScanProg`

The whole `main` body (from the C10 parser AST) is:

```
Dec «base» BaseAddr; Dec «buf» (base+32);
@load_vec(base,24,buf,4096);                          (* FFI: fills control block + arena bytes → establishes elsePre *)
Dec «alen» [base]; Dec «off» [base+8]; Dec «len» [base+16]; Dec «result» 0;
If (alen < off+len) { «result» := 0xFFFFFFFF }        (* bounds-If: C1 evaluate_boundsChk proved the DECISION *)
                    { elseBranch }                    (* ← elseBranch_frame: CLOSED, lands «result» = n2w(scanFrom a off len 0) *)
st (base+24) «result»;
@report_vec(base+24,8,base,8); return 0
```

- **Loop core → whole else-arm: CLOSED (this lane).** `scanLoop_refines_scanFrom` (CN-BOUNDSCAN-LINKA) is lifted, via `elseBranch_frame`, through `Dec «acc» 0; Dec «i» 0; scanLoop; «result»:=«acc»` — the exact `Dec`/`Seq` threading + `loopInv … 0 0` establishment + `vs = a[off..off+len)` view that CN-BOUNDSCAN-LINKA §5 and CN-RUNG3-FINISH §2.3 named as the residual. `«result»` now holds the Lean digest at the end of the in-bounds arm, from `elsePre`.

- **What remains to a fully-closed `semantics_decls s «main» boundScanProg`** (none the EVAL dead end, none leanc):
  1. **The bounds-`If` join** — compose `elseBranch_frame` (else-arm) with C1's `evaluate_boundsChk` (the `If` decision) and the then-arm sentinel `«result» := 0xFFFFFFFF`. A `Seq`/`If` join; needs the guard's word arithmetic (`alen < off+len` signed, cf. `signed_lt_n2w64`) and refines `elsePre`'s `offw` to `n2w off` so the control-block offset and the loop address base coincide. **Mechanical + a small word-arith refinement; OPEN.**
  2. **The outer `Dec` threading** — `Dec «base» BaseAddr; Dec «buf» (base+32); Dec «alen»/«off»/«len» (Load); Dec «result» 0` around the `If`, exactly the `Dec`/`Seq` shape `elseBranch_frame` already threads for `«acc»`/`«i»`, plus the three `Load`s reading the control block from memory (a `memRel`-altitude fact). **Mechanical; OPEN.**
  3. **The `@load_vec`/`@report_vec` `ExtCall` FFI-oracle contract** — `@load_vec` establishes `elsePre` (the arena bytes + control-block words arrive through the abstract `call_FFI s.ffi`); `@report_vec` + `st (base+24) «result»` + `return 0` emit the digest. **IRREDUCIBLE (residual (3)); the front-end↔C-driver contract, scoped as `elsePre`, not derivable in-logic.**
  4. **The top-level `semantics_decls`/`evaluate_decls` wrapper** — the clock existential + install-and-run around the `main` body. Standard CakeML clocked-semantics plumbing; **OPEN, mechanical.**

So the frame lifts `scanLoop_refines_scanFrom` **all the way through the in-bounds else-arm** (the digest-computing half of `main`) to a `«result»`-level statement, under the single named `elsePre` hypothesis. The remaining distance to `semantics_decls` is the bounds-`If` join, the outer `Dec`/`Load` threading, and the `semantics_decls` wrapper (all mechanical), plus the one irreducible `ExtCall` FFI-oracle contract.

---

## 3. The end-to-end boundscan Rung-3 chain, after this lane

```
boundscan.pnk (1694 B) ─cake --pancake─▶ boundScanBytes (1188 B x64) ─reflect─▶ HOL
   │  Layer 2 (oracle cake_native_bootstrap) + boundScan_pkg_bridge (DISK_THM)     [BYTES-BRIDGE/FINISH]
   ▼
G1 native  →  Link B (pan_to_target @ native bytes) + 4 prog-conditions           [RUNG3-NATIVE]
   ▼
boundScan_rung3_native  →  install core discharged (31→25 antecedents)            [RUNG3-INSTALL]
   ▼
boundScan_rung3_installed : machine_sem mc ffi ms ⊆ … {semantics_decls s «main» boundScanProg}
   │  Link A: whole-`main` frame
   │    · scanLoop core         : scanLoop_refines_scanFrom      (LINK-A,   PROVEN)
   │    · else-arm identity     : elseBranch_faithful            (FINISH,   PROVEN)
   │    · loop-body frame       : scanBody_frame/res/clock       (FINISH,   PROVEN)
   │    · scanLoop LOCALS-frame : scanLoop_locals_frame          (THIS LANE, PROVEN)  ← §2.3.1 CLOSED
   │    · else-arm Dec/Seq      : elseBranch_frame               (THIS LANE, PROVEN)  ← §2.3.2 CLOSED
   │        lifts scanLoop_refines → «result» = n2w (scanFrom a off len 0), from elsePre
   │    · bounds-If join + outer Dec/Load + semantics_decls wrapper  (mechanical, OPEN)
   │    · @load_vec/@report_vec FFI-oracle contract  = elsePre   (IRREDUCIBLE, scoped — §2.3.3)
   ▼
[TARGET]  machine_sem … ⊆ { behaviour that reports n2w (boundScan a off len) }   (Lean spec)
```

---

## 4. Independent verification (ran it; "it built" is checked, not asserted)

- **Genuine from-scratch build GREEN.** Removed the cached theory (`.hol/objs/boundScanWholeMainTheory.*`, `.hol/make-deps/…`) then `Holmake` → `boundScanWholeMainTheory (6s) [1/1] OK` (loads the prebuilt pancake/parser/linka/finish proofs; no CakeML-tree file modified). Not a stale artifact.
- **Real kernel tags, fresh load** (`Tag.dest_tag (Thm.tag …)`, not a grep): `scanLoop_locals_frame`, `Seq_NONE_le`, `elseCore`, `elseBranch_frame` each `oracles = [DISK_THM]`, `axiomdeps = []`. `axioms "boundScanWholeMain" = 0`. **No `cheat`/`new_axiom`; no `cake_native_bootstrap` or any lane oracle; no `native_decide` (HOL4 has none).**
- **Non-vacuity — fully-qualified `dest_thy_const` audit** (`wholemain.out`): `scanLoop_locals_frame` references `boundScanLoopLinkA$scanLoop` + `panSem$evaluate` (the REAL verified-parser loop + REAL semantics). `elseBranch_frame` references `boundScanMainFrame$elseBranch` (the REAL C10 else-arm), `boundScanLoopLinkA$scanFrom` (the REAL Lean digest fold), `boundScanWholeMain$elsePre`, and `panSem$evaluate` — it reasons about the actual program's else-arm and the actual spec fold, **not a local mirror**.
- **Statements read from the kernel** (`wholemain.out`): the two headline theorems are the non-vacuous statements in §1 (the loop-frame quantified over all `v ∉ {«acc»,«i»}`; the else-arm landing `«result» = n2w (scanFrom a off len 0)`).

**Scope note:** this is a HOL4/CakeML COMPILER-track lane. It touches no Lean spec, no `Datapath.lean`, no `lakefile`, no `libdrorb`, no Rust dataplane — there is **no** `cargo` / `build-dataplane-lib.sh` / `curl` delta. The mergeable artifact is the new HOL4 theory (`boundScanWholeMain`) + Holmakefile + audit dump + this report.

---

## 5. Files

**On hbox** (`/home/hbox/hol-rung3-wholemain/`, self-contained; no CakeML-tree file modified):
`boundScanWholeMainScript.sml` (md5 `dfe16981…`), `Holmakefile` (INCLUDES the CakeML pancake/parser/backend/x64 dirs + `~/hol-c10` + `~/hol-boundscan-linka` + `~/hol-rung3-finish`), `boundscan.pnk`, `audit_wm.sml` (the fresh-session kernel-tag + theory-axiom + fully-qualified-const audit), `wholemain.out` (its output).

**In this repo** (`docs/engine/probes/compiler/hol-rung3-wholemain/`): the same files (`boundScanWholeMainScript.sml` md5-matched to hbox), plus this report.

## 6. Reproduce (hbox)

```
ssh hbox@hbox.local
export CAKEMLDIR=$HOME/src/cakeml; export PATH=$HOME/src/HOL/bin:$PATH
cd ~/hol-rung3-wholemain
find .hol -name "*oundScanWholeMain*" -delete        # genuine clean (artifacts live in .hol/)
Holmake                                              # boundScanWholeMainTheory (6s) [1/1] OK
hol < audit_wm.sml                                   # kernel tags + axioms=0 + fully-qualified const audit
# theorem names (boundScanWholeMainScript.sml):
#   locals-frame : scanLoop_locals_frame     (residual (1) CLOSED)
#   else-arm     : elseBranch_frame          (residual (2) CLOSED; over elsePre = residual (3), scoped)
#   helpers      : Seq_NONE_le, elseCore, elsePre_def
```

## 7. Bottom line

The two mechanical residuals of the whole-`main` Link-A frame that CN-RUNG3-FINISH §2.3 named as open — the **`scanLoop` locals-frame** (§2.3.1, explicitly "engineering … hit tactic friction … not closed") and the **else-arm `Dec`/`Seq` threading** (§2.3.2) — are now **discharged in-logic** (`scanLoop_locals_frame`, `elseBranch_frame`, both `[oracles: DISK_THM] [axioms:]`, 0 theory axioms). Together they lift `scanLoop_refines_scanFrom` through the **whole in-bounds else-arm** of the real verified-parser `boundScanProg` to `«result» = n2w (scanFrom a off len 0)` (the Lean `C0.boundScan` in-bounds digest), under the single explicit `elsePre` hypothesis — which is precisely the `@load_vec` FFI-oracle postcondition (residual (3), §2.3.3), **scoped, not faked**. What remains to a fully-closed `semantics_decls s «main» boundScanProg` is the bounds-`If` join (compose with C1's `evaluate_boundsChk`), the outer `Dec`/`Load` threading, and the top-level `semantics_decls` wrapper — all mechanical — plus the one irreducible `@load_vec`/`@report_vec` `ExtCall` FFI-oracle contract that establishes `elsePre`. None of the residual is the in-logic-EVAL dead end; none is leanc.

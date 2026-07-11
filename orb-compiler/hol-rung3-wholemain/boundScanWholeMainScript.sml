(* ===========================================================================
   CN RUNG-3 WHOLE-MAIN — Link-A frame: lift scanLoop_refines_scanFrom through
   the `main` Dec/If/Seq/@load_vec-FFI/@report_vec threading toward
   `semantics_decls s «main» boundScanProg`.

   Ground: CN-RUNG3-FINISH-REPORT §2.3 named three residuals under the whole-main
   frame — (1) the `scanLoop` locals-frame (engineering, hit tactic friction, NOT
   closed there), (2) the mechanical Dec/If/Seq threading, (3) the
   @load_vec/@report_vec FFI-oracle contract (the irreducible boundary where the
   arena bytes enter through the abstract `s.ffi`).

   This theory:
     · CLOSES residual (1) — `scanLoop_locals_frame`: a clock-bounded induction
       over the real clocked `While` showing the loop writes ONLY «acc»/«i».
     · CLOSES residual (2) for the else-arm — `elseBranch_frame`: threads
       Dec «acc» 0; Dec «i» 0; scanLoop; «result»:=«acc», lifting
       scanLoop_refines_scanFrom to `«result» = n2w (scanFrom a off len 0)`.
     · SCOPES residual (3) as an EXPLICIT named hypothesis (the @load_vec
       postcondition = loopInv-establishing predicate), never faked.

   All theorems: [oracles: DISK_THM] [axioms:], 0 theory axioms.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory pairTheory finite_mapTheory wordsTheory;
open panLangTheory panSemTheory;
open boundScanLinkBTheory boundScanLoopLinkATheory boundScanMainFrameTheory;

val _ = new_theory "boundScanWholeMain";

val TOP_CASE_TAC = BasicProvers.TOP_CASE_TAC;

(* ===========================================================================
   §1  RESIDUAL (1) CLOSED — the scanLoop LOCALS-FRAME.

   `scanBody_frame`/`_res`/`_clock`/`_fixclock` (boundScanMainFrame) are the body
   ingredients.  This lifts them across the clocked `While` by a complete
   induction on the clock: running the whole `scanLoop` writes only «acc»/«i».
   =========================================================================== *)

Theorem scanLoop_locals_frame:
  !s s' v. evaluate (scanLoop, s) = (NONE, s') /\
           v <> strlit "acc" /\ v <> strlit "i" ==>
           FLOOKUP s'.locals v = FLOOKUP s.locals v
Proof
  qsuff_tac
    `!n s s' v. s.clock = n /\ evaluate (scanLoop, s) = (NONE, s') /\
                v <> strlit "acc" /\ v <> strlit "i" ==>
                FLOOKUP s'.locals v = FLOOKUP s.locals v`
  >- metis_tac [] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `evaluate (scanLoop, s) = (NONE, s')` mp_tac >>
  rewrite_tac [Once scanLoop_def] >>
  once_rewrite_tac [evaluate_def] >>
  rewrite_tac [GSYM scanLoop_def] >>
  TOP_CASE_TAC >> simp [] >>          (* eval option : NONE => (SOME Error,s) *)
  TOP_CASE_TAC >> simp [] >>          (* v : Val / Struct *)
  TOP_CASE_TAC >> simp [] >>          (* word_lab : Word / Label *)
  IF_CASES_TAC >> simp [] >>          (* w <> 0w ; else (NONE,s) closes *)
  IF_CASES_TAC >> simp [] >>          (* clock = 0 : (SOME TimeOut,_), contra *)
  (* fix_clock on scanBody collapses (auto, no Tick/While/Call); name the body pair *)
  pairarg_tac >> simp [] >>
  `res = NONE \/ res = SOME Error` by metis_tac [scanBody_res] >> simp [] >>
  strip_tac >>
  `s1.clock < n` by (imp_res_tac scanBody_clock >> fs [dec_clock_def]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`s1`,`s'`,`v`] mp_tac) >>
  simp [] >> strip_tac >>
  `FLOOKUP s1.locals v = FLOOKUP (dec_clock s).locals v` by metis_tac [scanBody_frame] >>
  fs [dec_clock_def]
QED

(* ===========================================================================
   §2  RESIDUAL (2) CLOSED (else-arm) — the Dec/Seq threading that lifts
   scanLoop_refines_scanFrom to the WHOLE else-arm `elseBranch`.

   `elsePre` is the post-@load_vec precondition the FFI-oracle contract
   establishes (residual (3), SCOPED as this explicit hypothesis, never faked):
   the control-block locals «len»/«buf»/«off»/«result» are in place, the arena
   view sits at `bufw+offw` (memRel), the region is in-bounds, and there is
   enough clock.  From it, running the else-arm
     Dec «acc» 0; Dec «i» 0; scanLoop; «result» := «acc»
   lands «result» = n2w (scanFrom a off len 0) — the in-bounds arm of the Lean
   C0.boundScan digest.
   =========================================================================== *)

(* clock-MONOTONE Seq (sa.clock <= s.clock suffices: fix_clock is then identity).
   Needed because the loop consumes clock, so the Seq wrapping it cannot use the
   clock-preserving Seq_NONE. *)
Theorem Seq_NONE_le:
  !p1 p2 s sa sb.
    evaluate (p1,s) = (NONE,sa) /\ sa.clock <= s.clock /\
    evaluate (p2,sa) = (NONE,sb) ==>
    evaluate (Seq p1 p2, s) = (NONE, sb)
Proof
  rpt strip_tac >> simp [evaluate_def] >>
  `fix_clock s (evaluate (p1,s)) = (NONE, sa)`
     by (`~(s.clock < sa.clock)` by fs [] >>
         simp [fix_clock_def, state_component_equality]) >>
  simp []
QED

(* The @load_vec FFI postcondition, as an EXPLICIT hypothesis (residual (3)).  It
   is the front-end<->C-driver contract: the loaded arena bytes are the view
   `TAKE len (DROP off a)` at `bufw+offw`, and the parsed control-block words are
   in the locals.  Not derivable in-logic (they enter through the abstract
   s.ffi oracle); named, not produced. *)
Definition elsePre_def:
  elsePre a off len bufw offw (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w len)) /\
    FLOOKUP s.locals (strlit "buf") = SOME (ValWord bufw) /\
    FLOOKUP s.locals (strlit "off") = SOME (ValWord offw) /\
    (?rv. FLOOKUP s.locals (strlit "result") = SOME (ValWord rv)) /\
    memRel (TAKE len (DROP off a)) (bufw + offw) s /\
    off + len <= LENGTH a /\ len < 2n ** 63 /\
    EVERY (\x. x < 256) (TAKE len (DROP off a)) /\ len <= s.clock
End

(* the loop-and-store core, at the state after the two Decs set «acc»/«i» to 0 *)
Theorem elseCore:
  elsePre a off len bufw offw s ==>
  ?s_res. evaluate
      (Seq (Seq (Annot (strlit "location") (strlit "(36:10 38:13)")) scanLoop)
           (Seq (Annot (strlit "location") (strlit "(40:4 40:15)"))
                (Assign Local (strlit "result") (Var Local (strlit "acc")))),
       s with locals := s.locals |+ (strlit "acc", ValWord 0w)
                                 |+ (strlit "i", ValWord 0w)) = (NONE, s_res) /\
     s_res.clock <= s.clock /\
     FLOOKUP s_res.locals (strlit "result") = SOME (ValWord (n2w (scanFrom a off len 0)))
Proof
  strip_tac >> fs [elsePre_def] >> qmatch_goalsub_abbrev_tac `evaluate (_, s_i)` >>
  `strlit "acc" <> strlit "i" /\ strlit "acc" <> strlit "result" /\
   strlit "len" <> strlit "acc" /\ strlit "len" <> strlit "i" /\
   strlit "buf" <> strlit "acc" /\ strlit "buf" <> strlit "i" /\
   strlit "off" <> strlit "acc" /\ strlit "off" <> strlit "i" /\
   strlit "result" <> strlit "acc" /\ strlit "result" <> strlit "i"` by EVAL_TAC >>
  `loopInv (TAKE len (DROP off a)) bufw offw 0 0 s_i`
     by (`LENGTH (TAKE len (DROP off a)) = len` by simp [LENGTH_TAKE_EQ, LENGTH_DROP] >>
         simp [loopInv_def, Abbr `s_i`, FLOOKUP_UPDATE, memRel_def] >> fs [memRel_def]) >>
  `LENGTH (TAKE len (DROP off a)) <= s_i.clock`
     by (`LENGTH (TAKE len (DROP off a)) = len` by simp [LENGTH_TAKE_EQ, LENGTH_DROP] >>
         simp [Abbr `s_i`] >> fs []) >>
  `off + len <= LENGTH a` by fs [] >>
  `?s_loop. evaluate (scanLoop, s_i) = (NONE, s_loop) /\
            FLOOKUP s_loop.locals (strlit "acc")
              = SOME (ValWord (n2w (scanFrom a off len 0)))`
     by (qpat_x_assum `loopInv _ _ _ _ _ _` mp_tac >>
         qpat_x_assum `LENGTH _ <= s_i.clock` mp_tac >>
         qpat_x_assum `off + len <= LENGTH a` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac [scanLoop_refines_scanFrom]) >>
  `FLOOKUP s_loop.locals (strlit "result") = SOME (ValWord rv)`
     by (`FLOOKUP s_loop.locals (strlit "result") = FLOOKUP s_i.locals (strlit "result")`
            by (irule scanLoop_locals_frame >> fs []) >>
         fs [Abbr `s_i`, FLOOKUP_UPDATE]) >>
  `s_loop.clock <= s_i.clock` by metis_tac [evaluate_clock] >>
  `evaluate (Seq (Annot (strlit "location") (strlit "(36:10 38:13)")) scanLoop, s_i)
     = (NONE, s_loop)`
     by (irule Seq_NONE >> qexists_tac `s_i` >> simp [evaluate_def]) >>
  qabbrev_tac `s_res = set_var (strlit "result") (ValWord (n2w (scanFrom a off len 0))) s_loop` >>
  `evaluate (Assign Local (strlit "result") (Var Local (strlit "acc")), s_loop) = (NONE, s_res)`
     by simp [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def, shape_of_def,
              Abbr `s_res`] >>
  `evaluate (Seq (Annot (strlit "location") (strlit "(40:4 40:15)"))
                 (Assign Local (strlit "result") (Var Local (strlit "acc"))), s_loop)
     = (NONE, s_res)`
     by (irule Seq_NONE >> qexists_tac `s_loop` >> simp [evaluate_def]) >>
  qexists_tac `s_res` >>
  conj_tac >- (irule Seq_NONE_le >> qexists_tac `s_loop` >> fs []) >>
  conj_tac >- (simp [Abbr `s_res`, set_var_def] >> fs [Abbr `s_i`]) >>
  simp [Abbr `s_res`, set_var_def, FLOOKUP_UPDATE]
QED

(* wrap the two Decs + annots around the core: THE WHOLE ELSE-ARM *)
Theorem elseBranch_frame:
  elsePre a off len bufw offw s ==>
  ?s'. evaluate (elseBranch, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "result") = SOME (ValWord (n2w (scanFrom a off len 0)))
Proof
  strip_tac >> drule elseCore >> strip_tac >>
  `strlit "result" <> strlit "acc" /\ strlit "result" <> strlit "i"` by EVAL_TAC >>
  qmatch_asmsub_abbrev_tac `evaluate (CORE_BODY, s_i) = (NONE, s_res)` >>
  qabbrev_tac `s_acc = s with locals := s.locals |+ (strlit "acc", ValWord 0w)` >>
  `s_acc with locals := s_acc.locals |+ (strlit "i", ValWord 0w) = s_i`
     by simp [Abbr `s_acc`, Abbr `s_i`] >>
  `FLOOKUP s_acc.locals (strlit "i") = FLOOKUP s.locals (strlit "i")`
     by simp [Abbr `s_acc`, FLOOKUP_UPDATE] >>
  qabbrev_tac `s_dec_i = s_res with locals :=
                 res_var s_res.locals (strlit "i", FLOOKUP s.locals (strlit "i"))` >>
  `evaluate (Dec (strlit "i") One (Const 0w) CORE_BODY, s_acc) = (NONE, s_dec_i)`
     by (simp [Once evaluate_def, eval_def, shape_of_def] >>
         asm_simp_tac (srw_ss()) [Abbr `s_dec_i`]) >>
  `evaluate (Seq (Annot (strlit "location") (strlit "(UNKNOWN 40:15)"))
                 (Dec (strlit "i") One (Const 0w) CORE_BODY), s_acc) = (NONE, s_dec_i)`
     by (irule Seq_NONE >> qexists_tac `s_acc` >> simp [evaluate_def]) >>
  qabbrev_tac `s_dec_acc = s_dec_i with locals :=
                 res_var s_dec_i.locals (strlit "acc", FLOOKUP s.locals (strlit "acc"))` >>
  `evaluate (Dec (strlit "acc") One (Const 0w)
              (Seq (Annot (strlit "location") (strlit "(UNKNOWN 40:15)"))
                   (Dec (strlit "i") One (Const 0w) CORE_BODY)), s) = (NONE, s_dec_acc)`
     by (simp [Once evaluate_def, eval_def, shape_of_def] >>
         asm_simp_tac (srw_ss()) [Abbr `s_acc`, Abbr `s_dec_acc`]) >>
  qexists_tac `s_dec_acc` >>
  conj_tac
  >- (simp [elseBranch_def] >> irule Seq_NONE >> qexists_tac `s` >>
      simp [evaluate_def, Abbr `CORE_BODY`]) >>
  simp [Abbr `s_dec_acc`, Abbr `s_dec_i`] >>
  Cases_on `FLOOKUP s.locals (strlit "acc")` >>
  Cases_on `FLOOKUP s.locals (strlit "i")` >>
  simp [res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM]
QED

val _ = export_theory ();

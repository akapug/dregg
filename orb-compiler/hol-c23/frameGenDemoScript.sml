(* ===========================================================================
   C23 — DEMONSTRATION that the body-generic `loop_frame` (composedCommon)
   REPRODUCES C22's per-body framed cores.  C22 hand-wrote cacheLoop1_framed /
   cacheLoop2_framed over ~250 lines of per-body frame/clock/exit machinery
   (cacheKeyFrame).  Here each framed core is ONE `loop_frame` instantiation +
   the fold's Nat->word homomorphism rewrite — the ~250 lines collapse to the
   generic engine (proven once) + a ~10-line per-fold derivation.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory
     composedCommonTheory cacheKeyCoreTheory;

val _ = new_theory "frameGenDemo";

(* fold body facts (mechanical, mirror cacheKeyFrame's 3-line lemmas) *)
Theorem cacheBodyA1_mem':
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA1, s0) = (r,s1) ==> s1.memory = s0.memory
Proof
  rpt gen_tac >> simp [cacheBodyA1_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, empty_locals_def] >> rw [] >> gvs []
QED

Theorem cacheBodyA1_ctrl':
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA1, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [cacheBodyA1_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

(* THE per-body framed core, from loop_frame — the generalized cacheLoop1_framed *)
Theorem cacheLoop1_framed_GEN:
  foldInv method bs 0 0w s /\ LENGTH method <= s.clock ==>
  ?s'. evaluate (cacheLoop1, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (hashBytesN method))) /\
       FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
       FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
       FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH method))) /\
       (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
       (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
       s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
       s.clock - LENGTH method <= s'.clock /\ s'.clock <= s.clock
Proof
  strip_tac >>
  `?s'. evaluate (While foldGuard cacheBodyA1, s) = (NONE, s') /\
        FLOOKUP s'.locals «acc» = SOME (ValWord (FOLDL hashAcc 0w (MAP (\c. (n2w c):word64) method))) /\
        FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
        FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
        FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH method))) /\
        (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
        (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
        s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
        s.clock - LENGTH method <= s'.clock /\ s'.clock <= s.clock`
    by (irule loop_frame >> rpt conj_tac >>
        TRY (rpt strip_tac >> irule cacheBodyA1_step >> fs [] >> NO_TAC) >>
        TRY (rpt strip_tac >> irule cacheBodyA1_mem' >> metis_tac [] >> NO_TAC) >>
        TRY (rpt strip_tac >> irule cacheBodyA1_ctrl' >> metis_tac [] >> NO_TAC) >>
        fs []) >>
  qexists_tac `s'` >> fs [cacheLoop1_def, hashBytes_word]
QED

val _ = export_theory ();

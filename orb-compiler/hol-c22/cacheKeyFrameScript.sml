(* ===========================================================================
   C22 — the FRAME + CLOCK machinery the two-fold composition needs beyond a
   single fold:
     * memory frame — evaluate_invariants gives memaddrs/be but NOT memory; the
       target arena memRel must survive fold #1 (which stores nothing).  Inlined
       clocked While induction.
     * fold-1 EXIT invariant — the loop-exit `foldInv` at i = LENGTH input hands
       «i»/«b»/«len»/«base»/«acc» shapes for free (needed for the fold-2
       reassigns' is_valid_value).  Bounded induction, then applied via metis.
     * clock lower bound — fold #1 consumes clock, so fold #2 needs enough
       remains: s'.clock >= s.clock - LENGTH input.
     * eval_load_ctrl_off / evaluate_Assign_val / evaluate_store_ctrl_var.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     pairTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory cacheKeyCoreTheory;

val _ = new_theory "cacheKeyFrame";

(* ---------- ctrl-relative word load ---------- *)
Theorem eval_load_ctrl_off:
  !s ba k w.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\ (ba + k) IN s.memaddrs /\
    s.memory (ba + k) = Word w ==>
    eval s (Load One (Op Add [Var Local «ctrl»; Const k])) = SOME (ValWord w)
Proof
  rpt strip_tac >>
  simp [eval_def, is_wf_shape_def, mem_load_def, OPT_MMAP_def,
        wordLangTheory.word_op_def]
QED

(* ---------- assign a computed word to an existing local ---------- *)
Theorem evaluate_Assign_val:
  FLOOKUP s.locals v = SOME (ValWord old) /\ eval s e = SOME (ValWord w) ==>
  evaluate (Assign Local v e, s) = (NONE, set_var v (ValWord w) s)
Proof
  strip_tac >>
  simp [Once evaluate_def, is_valid_value_def, lookup_kvar_def, shape_of_def,
        set_kvar_def, set_var_def]
QED

(* ---------- ctrl-keyed store of an arbitrary local (the decision word) ------ *)
Theorem evaluate_store_ctrl_var:
  !s ba w k v.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s.locals v = SOME (ValWord w) /\
    (ba + k) IN s.memaddrs ==>
    evaluate (Store (Op Add [Var Local «ctrl»; Const k]) (Var Local v), s) =
      (NONE, s with memory := ((ba + k) =+ Word w) s.memory)
Proof
  rpt strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        flatten_def, mem_stores_def, mem_store_def]
QED

(* ---------- fold-body single-step memory / ctrl / km frames ---------- *)
Theorem cacheBodyA1_mem:
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA1, s0) = (r,s1) ==> s1.memory = s0.memory
Proof
  rpt gen_tac >> simp [cacheBodyA1_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, empty_locals_def] >> rw [] >> gvs []
QED

Theorem cacheBodyA2_mem:
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA2, s0) = (r,s1) ==> s1.memory = s0.memory
Proof
  rpt gen_tac >> simp [cacheBodyA2_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, empty_locals_def] >> rw [] >> gvs []
QED

Theorem cacheBodyA1_keeps_ctrl:
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA1, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [cacheBodyA1_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

Theorem cacheBodyA2_keeps_ctrl:
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA2, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [cacheBodyA2_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

Theorem cacheBodyA2_keeps_km:
  !(s0:(64,'ffi) state) r s1. evaluate (cacheBodyA2, s0) = (r,s1) ==>
     FLOOKUP s1.locals «km» = FLOOKUP s0.locals «km»
Proof
  rpt gen_tac >> simp [cacheBodyA2_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

(* ---------- loop-level memory frame (inlined clocked induction) ---------- *)
Theorem cacheLoop1_mem:
  !(s:(64,'ffi) state) s1. evaluate (cacheLoop1, s) = (NONE, s1) ==> s1.memory = s.memory
Proof
  simp [cacheLoop1_def] >>
  `!n (s:(64,'ffi) state) s1. s.clock = n /\ evaluate (While foldGuard cacheBodyA1, s) = (NONE, s1) ==> s1.memory = s.memory`
    suffices_by metis_tac [] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `evaluate (While _ _,_) = _` mp_tac >> simp [Once evaluate_def] >>
  Cases_on `eval s foldGuard` >> simp [] >> rename1 `eval s foldGuard = SOME vv` >> Cases_on `vv` >> simp [] >>
  Cases_on `w` >> simp [] >> qmatch_goalsub_rename_tac `if ww <> 0w then _ else _` >>
  reverse (Cases_on `ww <> 0w`) >> simp [] >> Cases_on `n = 0` >> simp [] >>
  Cases_on `evaluate (cacheBodyA1, dec_clock s)` >> rename1 `evaluate (cacheBodyA1,dec_clock s) = (rb, sb)` >>
  `sb.clock <= (dec_clock s).clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `fix_clock (dec_clock s) (rb, sb) = (rb, sb)` by (irule fix_clock_id >> fs []) >> simp [] >>
  `sb.memory = s.memory` by (imp_res_tac cacheBodyA1_mem >> fs [dec_clock_def]) >>
  `sb.clock < n` by fs [dec_clock_def] >>
  Cases_on `rb` >> TRY (rename1 `SOME rr` >> Cases_on `rr`) >> simp [] >> strip_tac >>
  FIRST [ (gvs [] >> NO_TAC),
          (`s1.memory = sb.memory` by (first_x_assum (qspec_then `sb.clock` mp_tac) >> impl_tac >- fs [] >>
             disch_then (qspecl_then [`sb`,`s1`] mp_tac) >> fs []) >> fs []) ]
QED

Theorem cacheLoop2_mem:
  !(s:(64,'ffi) state) s1. evaluate (cacheLoop2, s) = (NONE, s1) ==> s1.memory = s.memory
Proof
  simp [cacheLoop2_def] >>
  `!n (s:(64,'ffi) state) s1. s.clock = n /\ evaluate (While foldGuard cacheBodyA2, s) = (NONE, s1) ==> s1.memory = s.memory`
    suffices_by metis_tac [] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `evaluate (While _ _,_) = _` mp_tac >> simp [Once evaluate_def] >>
  Cases_on `eval s foldGuard` >> simp [] >> rename1 `eval s foldGuard = SOME vv` >> Cases_on `vv` >> simp [] >>
  Cases_on `w` >> simp [] >> qmatch_goalsub_rename_tac `if ww <> 0w then _ else _` >>
  reverse (Cases_on `ww <> 0w`) >> simp [] >> Cases_on `n = 0` >> simp [] >>
  Cases_on `evaluate (cacheBodyA2, dec_clock s)` >> rename1 `evaluate (cacheBodyA2,dec_clock s) = (rb, sb)` >>
  `sb.clock <= (dec_clock s).clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `fix_clock (dec_clock s) (rb, sb) = (rb, sb)` by (irule fix_clock_id >> fs []) >> simp [] >>
  `sb.memory = s.memory` by (imp_res_tac cacheBodyA2_mem >> fs [dec_clock_def]) >>
  `sb.clock < n` by fs [dec_clock_def] >>
  Cases_on `rb` >> TRY (rename1 `SOME rr` >> Cases_on `rr`) >> simp [] >> strip_tac >>
  FIRST [ (gvs [] >> NO_TAC),
          (`s1.memory = sb.memory` by (first_x_assum (qspec_then `sb.clock` mp_tac) >> impl_tac >- fs [] >>
             disch_then (qspecl_then [`sb`,`s1`] mp_tac) >> fs []) >> fs []) ]
QED

(* ---------- fold-1 EXIT foldInv (bounded induction + application) ---------- *)
Theorem cacheLoop1_exit_bounded:
  !method bs.
   !k i acc (s:(64,'ffi) state).
     foldInv method bs i acc s /\ LENGTH method - i <= k /\ LENGTH method - i <= s.clock ==>
     ?s'. evaluate (While foldGuard cacheBodyA1, s) = (NONE, s') /\
          foldInv method bs (LENGTH method)
            (FOLDL hashAcc acc (MAP (\c. (n2w c):word64) (DROP i method))) s'
Proof
  ntac 2 gen_tac >>
  `!i acc (s:(64,'ffi) state). foldInv method bs i acc s /\ i < LENGTH method ==>
     ?s2. evaluate (cacheBodyA1, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv method bs (i+1) (hashAcc acc (n2w (EL i method):word64)) s2`
     by (rpt strip_tac >> irule cacheBodyA1_step >> fs []) >>
  pop_assum (fn bstep => Induct_on `k` >| [
    (rpt strip_tac >> `i = LENGTH method` by fs [foldInv_def] >>
     `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >> qexists_tac `s` >>
     `evaluate (While foldGuard cacheBodyA1, s) = (NONE, s)` by (simp [Once evaluate_def]) >>
     `DROP i method = []` by (`LENGTH method <= i` by fs [] >> simp [DROP_LENGTH_TOO_LONG]) >> fs []),
    (rpt strip_tac >> Cases_on `i < LENGTH method` >| [
       (`s.clock <> 0` by fs [] >> mp_tac (MATCH_MP foldLoop_iter bstep) >>
        disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >> impl_tac >- fs [] >> strip_tac >>
        `LENGTH method - (i + 1) <= k` by fs [] >> `LENGTH method - (i + 1) <= s2.clock` by fs [] >>
        last_x_assum (qspecl_then [`i+1`,`hashAcc acc (n2w (EL i method):word64)`,`s2`] mp_tac) >>
        impl_tac >- fs [] >> strip_tac >> qexists_tac `s'` >>
        `DROP i method = EL i method :: DROP (SUC i) method` by (irule DROP_EL_CONS_local >> fs []) >> gvs [ADD1]),
       (`i = LENGTH method` by fs [foldInv_def] >> `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
        qexists_tac `s` >> `evaluate (While foldGuard cacheBodyA1, s) = (NONE, s)` by (simp [Once evaluate_def]) >>
        `DROP i method = []` by (`LENGTH method <= i` by fs [] >> simp [DROP_LENGTH_TOO_LONG]) >> fs [])])])
QED

Theorem cacheLoop1_exit:
  foldInv method bs 0 0w s /\ LENGTH method <= s.clock ==>
  ?s'. evaluate (cacheLoop1, s) = (NONE, s') /\
       foldInv method bs (LENGTH method) (n2w (hashBytesN method)) s'
Proof
  rpt strip_tac >>
  `foldInv method bs 0 0w s /\ LENGTH method - 0 <= LENGTH method /\ LENGTH method - 0 <= s.clock` by fs [] >>
  `?s'. evaluate (While foldGuard cacheBodyA1, s) = (NONE, s') /\
        foldInv method bs (LENGTH method) (FOLDL hashAcc 0w (MAP (\c. (n2w c):word64) (DROP 0 method))) s'`
    by metis_tac [cacheLoop1_exit_bounded] >>
  qexists_tac `s'` >> gvs [cacheLoop1_def, hashBytes_word]
QED

(* ---------- clock lower bound (the two-fold need) ---------- *)
Theorem foldLoop_clock_bounded:
  !accf body input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (body, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !k i acc (s:(64,'ffi) state) s'.
      foldInv input bs i acc s /\ LENGTH input - i <= k /\ LENGTH input - i <= s.clock /\
      evaluate (While foldGuard body, s) = (NONE, s') ==>
      s.clock - (LENGTH input - i) <= s'.clock
Proof
  ntac 4 gen_tac >>
  disch_then (fn bstep =>
    Induct_on `k` >| [
      (rpt strip_tac >>
       `i <= LENGTH input` by fs [foldInv_def] >>
       `i = LENGTH input` by DECIDE_TAC >>
       `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
       `s' = s` by (qpat_x_assum `evaluate (While foldGuard body, s) = (NONE, s')` mp_tac >>
                    asm_simp_tac (srw_ss()) [Once evaluate_def]) >>
       gvs []),
      (rpt strip_tac >> Cases_on `i < LENGTH input` >| [
         (`s.clock <> 0` by fs [] >>
          mp_tac (MATCH_MP foldLoop_iter bstep) >>
          disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >> impl_tac >- fs [] >> strip_tac >>
          `evaluate (While foldGuard body, s2) = (NONE, s')` by fs [] >>
          `LENGTH input - (i+1) <= k` by fs [] >>
          `LENGTH input - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`accf acc (n2w (EL i input):word64)`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >>
          `s2.clock = s.clock - 1` by fs [] >>
          `s.clock - (LENGTH input - i) = s2.clock - (LENGTH input - (i+1))`
             by (`0 < s.clock` by fs [] >> DECIDE_TAC) >>
          fs []),
         (`i <= LENGTH input` by fs [foldInv_def] >>
          `i = LENGTH input` by DECIDE_TAC >>
          `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
          `s' = s` by (qpat_x_assum `evaluate (While foldGuard body, s) = (NONE, s')` mp_tac >>
                       asm_simp_tac (srw_ss()) [Once evaluate_def]) >>
          gvs [])
      ])
    ])
QED

Theorem cacheLoop1_clock_bounded:
  !input bs.
   !k i acc (s:(64,'ffi) state) s'.
     foldInv input bs i acc s /\ LENGTH input - i <= k /\ LENGTH input - i <= s.clock /\
     evaluate (While foldGuard cacheBodyA1, s) = (NONE, s') ==>
     s.clock - (LENGTH input - i) <= s'.clock
Proof
  ntac 2 gen_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (cacheBodyA1, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule cacheBodyA1_step >> fs []) >>
  pop_assum (fn bstep => Induct_on `k` >| [
      (rpt strip_tac >>
       `i <= LENGTH input` by fs [foldInv_def] >> `i = LENGTH input` by DECIDE_TAC >>
       `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
       `s' = s` by (qpat_x_assum `evaluate (While foldGuard cacheBodyA1, s) = (NONE, s')` mp_tac >>
                    asm_simp_tac (srw_ss()) [Once evaluate_def]) >> gvs []),
      (rpt strip_tac >> Cases_on `i < LENGTH input` >| [
         (`s.clock <> 0` by fs [] >> mp_tac (MATCH_MP foldLoop_iter bstep) >>
          disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >> impl_tac >- fs [] >> strip_tac >>
          `evaluate (While foldGuard cacheBodyA1, s2) = (NONE, s')` by fs [] >>
          `LENGTH input - (i+1) <= k` by fs [] >> `LENGTH input - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`hashAcc acc (n2w (EL i input):word64)`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >>
          `s2.clock = s.clock - 1` by fs [] >>
          `s.clock - (LENGTH input - i) = s2.clock - (LENGTH input - (i+1))`
             by (`0 < s.clock` by fs [] >> DECIDE_TAC) >> fs []),
         (`i <= LENGTH input` by fs [foldInv_def] >> `i = LENGTH input` by DECIDE_TAC >>
          `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
          `s' = s` by (qpat_x_assum `evaluate (While foldGuard cacheBodyA1, s) = (NONE, s')` mp_tac >>
                       asm_simp_tac (srw_ss()) [Once evaluate_def]) >> gvs [])])])
QED

Theorem cacheLoop2_clock_bounded:
  !input bs.
   !k i acc (s:(64,'ffi) state) s'.
     foldInv input bs i acc s /\ LENGTH input - i <= k /\ LENGTH input - i <= s.clock /\
     evaluate (While foldGuard cacheBodyA2, s) = (NONE, s') ==>
     s.clock - (LENGTH input - i) <= s'.clock
Proof
  ntac 2 gen_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (cacheBodyA2, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule cacheBodyA2_step >> fs []) >>
  pop_assum (fn bstep => Induct_on `k` >| [
      (rpt strip_tac >>
       `i <= LENGTH input` by fs [foldInv_def] >> `i = LENGTH input` by DECIDE_TAC >>
       `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
       `s' = s` by (qpat_x_assum `evaluate (While foldGuard cacheBodyA2, s) = (NONE, s')` mp_tac >>
                    asm_simp_tac (srw_ss()) [Once evaluate_def]) >> gvs []),
      (rpt strip_tac >> Cases_on `i < LENGTH input` >| [
         (`s.clock <> 0` by fs [] >> mp_tac (MATCH_MP foldLoop_iter bstep) >>
          disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >> impl_tac >- fs [] >> strip_tac >>
          `evaluate (While foldGuard cacheBodyA2, s2) = (NONE, s')` by fs [] >>
          `LENGTH input - (i+1) <= k` by fs [] >> `LENGTH input - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`hashAcc acc (n2w (EL i input):word64)`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >>
          `s2.clock = s.clock - 1` by fs [] >>
          `s.clock - (LENGTH input - i) = s2.clock - (LENGTH input - (i+1))`
             by (`0 < s.clock` by fs [] >> DECIDE_TAC) >> fs []),
         (`i <= LENGTH input` by fs [foldInv_def] >> `i = LENGTH input` by DECIDE_TAC >>
          `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
          `s' = s` by (qpat_x_assum `evaluate (While foldGuard cacheBodyA2, s) = (NONE, s')` mp_tac >>
                       asm_simp_tac (srw_ss()) [Once evaluate_def]) >> gvs [])])])
QED

Theorem cacheLoop1_clock:
  foldInv input bs 0 0w s /\ LENGTH input <= s.clock /\
  evaluate (cacheLoop1, s) = (NONE, s') ==> s.clock - LENGTH input <= s'.clock
Proof
  strip_tac >>
  `foldInv input bs 0 0w s /\ LENGTH input - 0 <= LENGTH input /\ LENGTH input - 0 <= s.clock /\
   evaluate (While foldGuard cacheBodyA1, s) = (NONE, s')` by fs [cacheLoop1_def] >>
  `s.clock - (LENGTH input - 0) <= s'.clock` by metis_tac [cacheLoop1_clock_bounded] >> fs []
QED

Theorem cacheLoop2_clock:
  foldInv input bs 0 0w s /\ LENGTH input <= s.clock /\
  evaluate (cacheLoop2, s) = (NONE, s') ==> s.clock - LENGTH input <= s'.clock
Proof
  strip_tac >>
  `foldInv input bs 0 0w s /\ LENGTH input - 0 <= LENGTH input /\ LENGTH input - 0 <= s.clock /\
   evaluate (While foldGuard cacheBodyA2, s) = (NONE, s')` by fs [cacheLoop2_def] >>
  `s.clock - (LENGTH input - 0) <= s'.clock` by metis_tac [cacheLoop2_clock_bounded] >> fs []
QED

(* ---------- framed cores ---------- *)
Theorem cacheLoop1_framed:
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
  strip_tac >> drule cacheLoop1_exit >> disch_then drule >> strip_tac >>
  `evaluate (While foldGuard cacheBodyA1, s) = (NONE, s')` by fs [cacheLoop1_def] >>
  qexists_tac `s'` >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- fs [foldInv_def]
  >- (irule (Q.SPECL [`«ctrl»`,`foldGuard`,`cacheBodyA1`] foldWrapCommonTheory.While_frame) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> imp_res_tac cacheBodyA1_keeps_ctrl >> fs [])
  >- fs [foldInv_def]
  >- fs [foldInv_def]
  >- (fs [foldInv_def])
  >- (fs [foldInv_def])
  >- (imp_res_tac cacheLoop1_mem >> fs [])
  >- (imp_res_tac evaluate_invariants >> fs [])
  >- (imp_res_tac evaluate_invariants >> fs [])
  >- (irule cacheLoop1_clock >> metis_tac [])
  >- (imp_res_tac evaluate_clock >> fs [])
QED

Theorem cacheLoop2_framed:
  foldInv target bs 0 0w s /\ LENGTH target <= s.clock ==>
  ?s'. evaluate (cacheLoop2, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (hashBytesN target))) /\
       FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
       FLOOKUP s'.locals «km» = FLOOKUP s.locals «km» /\
       s'.memory = s.memory
Proof
  strip_tac >> drule cacheLoop2_refines >> disch_then drule >> strip_tac >>
  `evaluate (While foldGuard cacheBodyA2, s) = (NONE, s')` by fs [cacheLoop2_def] >>
  qexists_tac `s'` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule (Q.SPECL [`«ctrl»`,`foldGuard`,`cacheBodyA2`] foldWrapCommonTheory.While_frame) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> imp_res_tac cacheBodyA2_keeps_ctrl >> fs [])
  >- (irule (Q.SPECL [`«km»`,`foldGuard`,`cacheBodyA2`] foldWrapCommonTheory.While_frame) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt strip_tac >> imp_res_tac cacheBodyA2_keeps_km >> fs [])
  >- (imp_res_tac cacheLoop2_mem >> fs [])
QED

val _ = export_theory ();

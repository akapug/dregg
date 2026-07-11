open HolKernel boolLib bossLib Parse;
open arithmeticTheory pairTheory finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory;
val _ = new_theory "frameProbe";
Theorem While_frame_gen:
  !v e c.
    (!(s0:(64,'ffi) state) r s1. evaluate (c,s0) = (r,s1) ==> FLOOKUP s1.locals v = FLOOKUP s0.locals v) ==>
    !n (s:(64,'ffi) state) s1. s.clock = n /\ evaluate (While e c, s) = (NONE, s1) ==>
             FLOOKUP s1.locals v = FLOOKUP s.locals v
Proof
  ntac 3 gen_tac >> strip_tac >> completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `evaluate (While _ _,_) = _` mp_tac >> simp [Once evaluate_def] >>
  Cases_on `eval s e` >> simp [] >>
  rename1 `eval s e = SOME vv` >> Cases_on `vv` >> simp [] >>
  Cases_on `w` >> simp [] >>
  qmatch_goalsub_rename_tac `if ww <> 0w then _ else _` >>
  reverse (Cases_on `ww <> 0w`) >> simp [] >>
  Cases_on `n = 0` >> simp [] >>
  Cases_on `evaluate (c, dec_clock s)` >>
  rename1 `evaluate (c,dec_clock s) = (rb, sb)` >>
  `sb.clock <= (dec_clock s).clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `fix_clock (dec_clock s) (rb, sb) = (rb, sb)` by (irule fix_clock_id >> fs []) >> simp [] >>
  `FLOOKUP sb.locals v = FLOOKUP s.locals v`
     by (qpat_assum `!s0 r s1. evaluate (c,s0) = (r,s1) ==> _` drule >> fs [dec_clock_def]) >>
  `sb.clock < n` by fs [dec_clock_def] >>
  Cases_on `rb` >> TRY (rename1 `SOME rr` >> Cases_on `rr`) >> simp [] >> strip_tac >>
  FIRST [ (gvs [] >> NO_TAC),
          (`FLOOKUP s1.locals v = FLOOKUP sb.locals v`
             by (first_x_assum (qspec_then `sb.clock` mp_tac) >> impl_tac >- fs [] >>
                 disch_then (qspecl_then [`sb`,`s1`] mp_tac) >> fs []) >> fs []) ]
QED
Theorem While_frame:
  !v e c.
    (!(s0:(64,'ffi) state) r s1. evaluate (c,s0) = (r,s1) ==> FLOOKUP s1.locals v = FLOOKUP s0.locals v) ==>
    !(s:(64,'ffi) state) s1. evaluate (While e c, s) = (NONE, s1) ==>
             FLOOKUP s1.locals v = FLOOKUP s.locals v
Proof
  metis_tac [While_frame_gen]
QED
val _ = export_theory ();

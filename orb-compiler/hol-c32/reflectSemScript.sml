(* ===========================================================================
   C32 — semantics CLOCK-LIFT for the two-loop reflect `main` (C20/C30 template,
   payload-agnostic).  Observable = the BYTE VECTOR `MAP n2w req` (reflected
   request).  Fuel budget 2 * LENGTH req (two loops).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory reflectWrapperTheory reflectMainRefineTheory;

val _ = new_theory "reflectSem";

Theorem call_main_run:
  FLOOKUP (s'':(64,'ffi)panSem$state).code «main» = SOME ([], reflectMainBody) /\
  s''.clock <> 0 /\ LENGTH req = 8 /\
  reflectFFI req ((dec_clock s'') with locals := FEMPTY) /\
  2 * LENGTH req <= (dec_clock s'').clock ==>
  ?t loadEv rb.
    evaluate (Call NONE «main» [], s'') = (SOME (Return (ValWord 0w)), t) /\
    t.ffi.io_events = s''.ffi.io_events ++ loadEv ++
      [IO_event (ffi$ExtCall «report_vec»)
         (MAP (\b. (n2w b):word8) req) rb]
Proof
  strip_tac >>
  qabbrev_tac `s0 = (dec_clock s'') with locals := FEMPTY` >>
  `s0.locals = FEMPTY /\ 2 * LENGTH req <= s0.clock /\
   reflectFFI req s0 /\ s0.ffi = s''.ffi`
     by (fs [Abbr `s0`, dec_clock_def]) >>
  `?sF loadEv rb.
     evaluate (reflectMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events = s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec») (MAP (\b. (n2w b):word8) req) rb]`
     by (irule reflectMainBody_refines >> fs []) >>
  qmatch_asmsub_rename_tac
     `evaluate (reflectMainBody, s0) = (SOME (Return (ValWord 0w)), sF)` >>
  `sF.clock <= s0.clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `evaluate (reflectMainBody, dec_clock s'' with locals := FEMPTY)
     = (SOME (Return (ValWord 0w)), sF)` by fs [Abbr `s0`] >>
  map_every qexists_tac [`empty_locals sF`, `loadEv`, `rb`] >>
  conj_tac
  >- (simp [Once evaluate_def, OPT_MMAP_def] >>
      gvs [lookup_code_def, FUPDATE_LIST_THM]) >>
  fs [empty_locals_def]
QED

Theorem main_semantics:
  FLOOKUP (s':(64,'ffi)panSem$state).code «main» = SOME ([], reflectMainBody) /\
  LENGTH req = 8 /\
  (!K. reflectFFI req ((dec_clock (s' with clock := K)) with locals := FEMPTY)) /\
  (?K. 0 < K /\ 2 * LENGTH req < K) ==>
  ?loadEv rb.
    semantics s' «main» = Terminate Success
      (s'.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (MAP (\b. (n2w b):word8) req) rb])
Proof
  strip_tac >>
  rename1 `2 * LENGTH req < K0` >>
  qabbrev_tac `sc = s' with clock := K0` >>
  `sc.code = s'.code /\ sc.ffi = s'.ffi /\ sc.clock = K0`
     by simp [Abbr `sc`] >>
  `FLOOKUP sc.code «main» = SOME ([], reflectMainBody)` by fs [] >>
  `sc.clock <> 0` by fs [] >>
  `reflectFFI req ((dec_clock sc) with locals := FEMPTY)`
     by (first_x_assum (qspec_then `K0` mp_tac) >> simp [Abbr `sc`]) >>
  `2 * LENGTH req <= (dec_clock sc).clock` by (simp [dec_clock_def] >> fs []) >>
  drule_all call_main_run >> strip_tac >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  `evaluate (Call NONE «main» [], s' with clock := K0)
     = (SOME (Return (ValWord 0w)), t)` by fs [Abbr `sc`] >>
  drule semantics_Return_lift >> strip_tac >>
  `t.ffi.io_events = s'.ffi.io_events ++ loadEv ++
      [IO_event (ffi$ExtCall «report_vec»)
         (MAP (\b. (n2w b):word8) req) rb]`
     by (qpat_x_assum `t.ffi.io_events = _` mp_tac >> simp [Abbr `sc`]) >>
  simp []
QED

val _ = export_theory ();

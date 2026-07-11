(* ===========================================================================
   C32 — whole-program Link A at the DECLS level for the reflect program
   (C30 template).  Installing reflectProg and running `semantics_decls` yields
   exactly the byte-vector FFI trace `MAP n2w req`.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open reflectLinkBInstTheory reflectWrapperTheory reflectSemTheory;

val _ = new_theory "reflectInstall";

val decs_ev = (REWRITE_CONV [reflectProg_def] THENC EVAL)
                “decs_stcnames [] reflectProg”;
val evd_ev  = (REWRITE_CONV [reflectProg_def] THENC EVAL)
                “evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    reflectProg”;

Theorem reflectProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ LENGTH req = 8 /\
  reflectFFI req s /\ (?K. 0 < K /\ 2 * LENGTH req < K) ==>
  ?loadEv rb.
    semantics_decls s «main» reflectProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ffi$ExtCall «report_vec»)
            (MAP (\b. (n2w b):word8) req) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) reflectProg)` >>
  `semantics_decls s «main» reflectProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], reflectMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [reflectProg_def] >> EVAL_TAC >>
         REWRITE_TAC [reflectMainBody_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [reflectProg_def] >> EVAL_TAC) >>
  `!Kc. reflectFFI req
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `reflectFFI req s` mp_tac >>
         asm_simp_tac (srw_ss()) [reflectFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ffi$ExtCall «report_vec»)
           (MAP (\b. (n2w b):word8) req) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();

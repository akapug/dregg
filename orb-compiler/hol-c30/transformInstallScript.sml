(* ===========================================================================
   C30 — whole-program Link A at the DECLS level for the transform program.
   Installing transformProg (single Function «main») and running
   `semantics_decls` yields exactly the byte-vector FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open transformLinkBInstTheory transformCopyLoopTheory transformSecHeadersTheory
     transformWrapperTheory transformSemTheory;

val _ = new_theory "transformInstall";

val decs_ev = (REWRITE_CONV [transformProg_def] THENC EVAL)
                “decs_stcnames [] transformProg”;
val evd_ev  = (REWRITE_CONV [transformProg_def] THENC EVAL)
                “evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    transformProg”;

Theorem transformProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\
  transformFFI secHeadersBytes s /\ (?K. 0 < K /\ LENGTH secHeadersBytes < K) ==>
  ?loadEv rb.
    semantics_decls s «main» transformProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ffi$ExtCall «report_vec»)
            (MAP (\b. (n2w b):word8) secHeadersBytes) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) transformProg)` >>
  `semantics_decls s «main» transformProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], transformMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [transformProg_def] >> EVAL_TAC >>
         REWRITE_TAC [transformMainBody_def, copyLoopA_def, copyGuard_def, copyBodyA_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [transformProg_def] >> EVAL_TAC) >>
  `!Kc. transformFFI secHeadersBytes
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `transformFFI secHeadersBytes s` mp_tac >>
         asm_simp_tac (srw_ss()) [transformFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ffi$ExtCall «report_vec»)
           (MAP (\b. (n2w b):word8) secHeadersBytes) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();

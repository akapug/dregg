(* ===========================================================================
   C15 probe, PART E1 — whole-program Link A at the DECLS level.
   Installing secHeadersProg (single Function «main», empty struct context) and
   running `semantics_decls` yields exactly the spec-word FFI trace.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open secheadersLinkBInstTheory;    (* secHeadersProg, secHeadersProg_def *)
open secheadersCoreTheory;         (* secheadersCore_def, hstsEffective *)
open secheadersWrapperTheory;      (* secheadersMainBody, secheadersMainBody_def, secheadersFFI, secheadersFFI_def *)
open secheadersSemTheory;          (* main_semantics *)

val _ = new_theory "secheadersInstall";

val decs_ev = (REWRITE_CONV [secHeadersProg_def] THENC EVAL)
                ``decs_stcnames [] secHeadersProg``;
val evd_ev  = (REWRITE_CONV [secHeadersProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    secHeadersProg``;

Theorem secHeadersProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\ secheadersFFI code s ==>
  ?loadEv rb.
    semantics_decls s «main» secHeadersProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (hstsEffective code) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) secHeadersProg)` >>
  `semantics_decls s «main» secHeadersProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], secheadersMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [secHeadersProg_def] >> EVAL_TAC >>
         REWRITE_TAC [secheadersMainBody_def, secheadersCore_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [secHeadersProg_def] >> EVAL_TAC) >>
  `!Kc. secheadersFFI code
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `secheadersFFI code s` mp_tac >>
         asm_simp_tac (srw_ss()) [secheadersFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (hstsEffective code) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();

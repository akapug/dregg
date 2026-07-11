(* ===========================================================================
   C20 — whole-program Link A at the DECLS level for the hash program.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open hashBytesLinkBInstTheory hashCoreTheory foldLoopSchemaTheory hashBytesLoopTheory
     hashWrapperLinkATheory hashSemTheory;

val _ = new_theory "hashInstall";

val decs_ev = (REWRITE_CONV [hashBytesProg_def] THENC EVAL)
                “decs_stcnames [] hashBytesProg”;
val evd_ev  = (REWRITE_CONV [hashBytesProg_def] THENC EVAL)
                “evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    hashBytesProg”;

Theorem hashBytesProg_semantics_decls:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\
  hashFFI input s /\ (?K. 0 < K /\ LENGTH input < K) ==>
  ?loadEv rb.
    semantics_decls s «main» hashBytesProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall «report_vec»)
            (word_to_bytes (n2w (hashBytesN input) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s' = THE (evaluate_decls (s with structs := []) hashBytesProg)` >>
  `semantics_decls s «main» hashBytesProg = semantics s' «main»`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s'`] >>
  `FLOOKUP s'.code «main» = SOME ([], hashMainBody)`
     by (simp [Abbr `s'`] >> REWRITE_TAC [hashBytesProg_def] >> EVAL_TAC >>
         REWRITE_TAC [hashMainBody_def, hashLoopCore_def, foldGuard_def, hashBodyA_def]) >>
  `s'.base_addr = s.base_addr /\ s'.ffi = s.ffi`
     by (simp [Abbr `s'`] >> REWRITE_TAC [hashBytesProg_def] >> EVAL_TAC) >>
  `!Kc. hashFFI input
          ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `hashFFI input s` mp_tac >>
         asm_simp_tac (srw_ss()) [hashFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s' «main» = Terminate Success
       (s'.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall «report_vec»)
           (word_to_bytes (n2w (hashBytesN input) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();

(* ===========================================================================
   CN RUNG-3 E2E — the whole-`main` FFI-trace frame reduction, ISOLATED.

   `boundScanProg_semantics_decls_bridge`: under s.code = FEMPTY + the single
   FFI-oracle contract boundScanFFI + a witness clock, the observational
   `semantics_decls s «main» boundScanProg` (the REAL verified-parser program,
   boundScanBytesBridge$boundScanProg — aconv-identical to C10/C11's) is EXACTLY
   the terminating trace whose reported result word is n2w (c0_encode
   (boundScan a off len)) (the Lean model/BoundScan.lean digest).

   Re-proves the c13 boundScanInstall content over boundScanBytesBridge's
   boundScanProg (the exact constant the rung3 native-bytes backbone carries),
   resting on the already-proven c13 whole-`main` frame (main_semantics <=
   mainBody_refines).  Kept in its OWN theory with MINIMAL opens so the fragile
   `simp [semantics_decls_def, decs_ev, evd_ev]` step is not perturbed by the
   x64/backend stateful simpset that the composition theory pulls in.

   [oracles: DISK_THM] [axioms:], 0 theory axioms.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open boundScanBytesBridgeTheory;           (* boundScanProg, boundScanProg_def *)
open boundScanCoreLinkATheory;             (* innerCore_def, boundScan, c0_encode *)
open boundScanDigestLinkATheory;           (* digLoop_def, digBody_def *)
open boundScanWrapperLinkATheory;          (* mainBody, mainBody_def, boundScanFFI, boundScanFFI_def *)
open boundScanSemTheory;                   (* main_semantics *)

val _ = new_theory "boundScanE2EFrame";

val decs_ev = (REWRITE_CONV [boundScanProg_def] THENC EVAL)
                ``decs_stcnames [] boundScanProg``;
val evd_ev  = (REWRITE_CONV [boundScanProg_def] THENC EVAL)
                ``evaluate_decls ((s:(64,'ffi) panSem$state) with structs := [])
                    boundScanProg``;

Theorem boundScanProg_semantics_decls_bridge:
  (s:(64,'ffi) panSem$state).code = FEMPTY /\
  boundScanFFI a off len s /\ (?K. 0 < K /\ len < K) ==>
  ?loadEv rb.
    semantics_decls s (strlit "main") boundScanProg =
      Terminate Success
        (s.ffi.io_events ++ loadEv ++
         [IO_event (ExtCall (strlit "report_vec"))
            (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb])
Proof
  strip_tac >>
  qabbrev_tac `s2 = THE (evaluate_decls (s with structs := []) boundScanProg)` >>
  `semantics_decls s (strlit "main") boundScanProg = semantics s2 (strlit "main")`
     by simp [semantics_decls_def, decs_ev, evd_ev, Abbr `s2`] >>
  `FLOOKUP s2.code (strlit "main") = SOME ([], mainBody)`
     by (simp [Abbr `s2`] >> REWRITE_TAC [boundScanProg_def] >> EVAL_TAC >>
         REWRITE_TAC [mainBody_def, innerCore_def, digLoop_def, digBody_def]) >>
  `s2.base_addr = s.base_addr /\ s2.ffi = s.ffi`
     by (simp [Abbr `s2`] >> REWRITE_TAC [boundScanProg_def] >> EVAL_TAC) >>
  `!Kc. boundScanFFI a off len
          ((dec_clock (s2 with clock := Kc)) with locals := FEMPTY)`
     by (gen_tac >>
         qpat_x_assum `boundScanFFI a off len s` mp_tac >>
         asm_simp_tac (srw_ss()) [boundScanFFI_def, dec_clock_def]) >>
  `?loadEv rb.
     semantics s2 (strlit "main") = Terminate Success
       (s2.ffi.io_events ++ loadEv ++
        [IO_event (ExtCall (strlit "report_vec"))
           (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb])`
     by (irule main_semantics >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >> gvs []
QED

val _ = export_theory ();

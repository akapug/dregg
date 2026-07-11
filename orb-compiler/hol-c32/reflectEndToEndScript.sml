(* ===========================================================================
   C32 — THE FINAL COMPOSITION: spec -> machine code for the two-loop
   REQUEST-DEPENDENT transform (fold-then-store).  Composes the whole-program
   Link-A wrapper (reflectInstall) with the CakeML backend Link-B
   (reflectProg_linkB): every observable behaviour of the installed x64 machine
   code emitted for reflect.pnk is the single terminating trace whose reported
   FFI payload is EXACTLY `MAP n2w req` — the reflected REQUEST bytes, computed
   in-machine by the fold lane and written by the store lane.  leanc is OUT.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open reflectLinkBInstTheory reflectWrapperTheory reflectInstallTheory;

val _ = new_theory "reflectEndToEnd";

val linkB_ant    = reflectProg_linkB |> concl |> dest_imp |> #1;
val linkB_concl  = reflectProg_linkB |> concl |> dest_imp |> #2;
val sd_tm        = find_term (fn t => same_const (fst (strip_comb t)) “semantics_decls”
                              handle _ => false) linkB_concl;
val notFail_tm   = valOf (List.find (fn c => is_neg c andalso
     (let val e = dest_neg c in is_eq e andalso
        (same_const (fst (strip_comb (lhs e))) “semantics_decls” handle _ => false) end))
     (boolSyntax.strip_conj linkB_ant));
val pkg_tm       = list_mk_conj (filter (fn c => not (aconv c notFail_tm))
                                   (boolSyntax.strip_conj linkB_ant));

val trace_tm =
  “(s:(64,'ffi) panSem$state).ffi.io_events ++ loadEv ++
    [IO_event (ffi$ExtCall «report_vec»)
       (MAP (\b. (n2w b):word8) req) rb]”;

val subset_spec  = subst [sd_tm |-> “Terminate Success ^trace_tm”] linkB_concl;
(* the linkB conclusion with `semantics_decls ...` INTACT — match_mp_tac
   reflectProg_linkB matches this cleanly; the final gvs rewrites sd_tm -> the
   concrete Terminate Success trace to close the goal (subset_spec). *)
val subset_sd    = linkB_concl;

val e2e_goal =
  mk_imp (list_mk_conj [pkg_tm,
                        “LENGTH (req:num list) = 8”,
                        “reflectFFI req (s:(64,'ffi) panSem$state)”,
                        “?K. 0 < K /\ 2 * LENGTH req < K”],
          mk_exists (“loadEv:io_event list”,
            mk_exists (“rb:(word8 # word8) list”, subset_spec)));

Theorem exists_big[local]:
  !n:num. ?K. 0 < K /\ n < K
Proof
  gen_tac >> qexists_tac `SUC n` >> DECIDE_TAC
QED

Theorem reflect_bytes_machine_code = prove (e2e_goal,
  strip_tac >>
  mp_tac (SPEC_ALL reflectProg_semantics_decls) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
               MATCH_ACCEPT_TAC exists_big) >>
  strip_tac >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  `^notFail_tm`
     by (qpat_x_assum `^sd_tm = _` (fn th => simp [th])) >>
  `^subset_sd`
     by (match_mp_tac reflectProg_linkB >> rpt conj_tac >>
         first_assum ACCEPT_TAC) >>
  qpat_x_assum `^sd_tm = _` (fn th => gvs [th]));

val _ = export_theory ();

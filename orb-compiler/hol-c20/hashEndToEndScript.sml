(* ===========================================================================
   C20 — THE FINAL COMPOSITION: spec -> machine code for the deployed cache-key
   hash.  Composes the whole-program Link-A wrapper (hashInstall) with the CakeML
   backend Link-B (hashBytesProg_linkB): every observable behaviour of the
   installed x64 machine code emitted for the hash is the single terminating trace
   whose reported result word is EXACTLY n2w (hashBytesN input) = the deployed
   Lean `Cache.hashBytes input` mod 2^64.  leanc is OUT of the TCB.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open hashBytesLinkBInstTheory hashBytesLoopTheory hashWrapperLinkATheory
     hashInstallTheory;

val _ = new_theory "hashEndToEnd";

val linkB_ant    = hashBytesProg_linkB |> concl |> dest_imp |> #1;
val linkB_concl  = hashBytesProg_linkB |> concl |> dest_imp |> #2;
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
       (word_to_bytes (n2w (hashBytesN input) : word64) F) rb]”;

val subset_sd    = linkB_concl;
val subset_spec  = subst [sd_tm |-> “Terminate Success ^trace_tm”] linkB_concl;

val e2e_goal =
  mk_imp (list_mk_conj [pkg_tm,
                        “hashFFI input (s:(64,'ffi) panSem$state)”,
                        “?K. 0 < K /\ LENGTH input < K”],
          mk_exists (“loadEv:io_event list”,
            mk_exists (“rb:(word8 # word8) list”, subset_spec)));

(* trivial upper-bound witness, proved in a clean context so the numeric
   decision procedure is not polluted by the whole-machine Link-B assumptions
   (pan_installed / word-arith) that swamp DECIDE_TAC at the use site. *)
Theorem exists_big[local]:
  !n:num. ?K. 0 < K /\ n < K
Proof
  gen_tac >> qexists_tac `SUC n` >> DECIDE_TAC
QED

Theorem hash_machine_code = prove (e2e_goal,
  strip_tac >>
  mp_tac (SPEC_ALL hashBytesProg_semantics_decls) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
               MATCH_ACCEPT_TAC exists_big) >>
  strip_tac >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  `^notFail_tm`
     by (qpat_x_assum `^sd_tm = _` (fn th => simp [th])) >>
  `^subset_sd`
     by (match_mp_tac hashBytesProg_linkB >> rpt conj_tac >>
         first_assum ACCEPT_TAC) >>
  qpat_x_assum `^sd_tm = _` (fn th => gvs [th]));

val _ = export_theory ();

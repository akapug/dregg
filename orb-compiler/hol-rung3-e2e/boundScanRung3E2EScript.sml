(* ===========================================================================
   CN RUNG-3 END-TO-END — COMPOSE the native-bytes backbone (rung3) with the
   whole-`main` FFI-trace frame (c13) into ONE kernel-checked theorem:

       the NATIVE-compiled x64 machine code emitted for the boundscan serve
       stage refines the Lean/Pancake spec — every observable behaviour of the
       installed machine code is the single terminating trace whose reported
       result word is EXACTLY n2w (c0_encode (boundScan a off len)) (the Lean
       model/BoundScan.lean C0.encode (C0.boundScan a off len)).

   This lane owns NO CakeML-tree file and re-derives (does not modify) the two
   ground pieces it composes:

     (A) the config-well-formedness discharge of the runtime-install antecedent
         (verbatim recipe from ~/hol-rung3-install/boundScanInstallScript.sml:
         boundScan_rung3_native @ x64 config, 31 -> 25 antecedents, DISK_THM),
         re-derived HERE to avoid the boundScanInstall theory-name clash with
         the c13 track;

     (B) the whole-`main` FFI-trace frame reduction of `semantics_decls s «main»
         boundScanProg` to the digest trace (the c13 boundScanInstall proof,
         re-proved HERE over boundScanBytesBridge$boundScanProg — the exact
         boundScanProg that appears in the rung3 backbone; aconv-checked
         identical to C11's), which rests on the already-proven c13 chain
         (mainBody_refines -> main_semantics), the whole-`main` frame that lifts
         the loop through the Dec/Load/@load_vec/bounds-If/@report_vec threading.

   Then (C) COMPOSES: rewrites the opaque `semantics_decls` set-element of the
   installed backbone with the digest trace from (B), discharging the backbone's
   `semantics_decls <> Fail` side-condition from the reduction (Terminate <> Fail).

   HONEST BOUNDARY (the two irreducible contracts, kept as NAMED antecedents —
   exactly the CakeML-standard `installed` + FFI hypotheses):
     * pan_installed boundScanBytes ... ms ...  + the placed-image geometry — the
       loader / target-config contract (helloProof DISCH_ALLs the same fact);
     * boundScanFFI a off len s — the @load_vec/@report_vec FFI-oracle contract
       (the observable behaviour IS an FFI I/O trace; the arena bytes enter, and
       the digest leaves, through the abstract oracle).
   Neither is faked; neither is the in-logic-EVAL dead end; neither is leanc.

   Tags target: [oracles: DISK_THM] [axioms:], 0 theory axioms (the native-bytes
   backbone keeps G1 as a NAMED antecedent, so the composed theorem is DISK_THM;
   a separate boundScan_rung3_e2e_native discharges G1 via the bootstrap oracle).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory;
open pan_to_targetProofTheory;
open x64_configProofTheory x64_configTheory x64_targetTheory;
open boundScanRung3Theory;                 (* boundScan_rung3_native *)
open boundScanBytesBridgeTheory;           (* boundScanProg, boundScanProg_def *)
open boundScanCoreLinkATheory;             (* boundScan, c0_encode *)
open boundScanWrapperLinkATheory;          (* boundScanFFI *)
open boundScanE2EFrameTheory;              (* boundScanProg_semantics_decls_bridge *)
open boundScanPkgTheory;                    (* boundScan_G1_native  (cake_native_bootstrap) *)

val _ = new_theory "boundScanRung3E2E";

(* ===========================================================================
   (A)  Re-derive boundScan_rung3_installed (config-well-formedness core), the
   verbatim recipe from ~/hol-rung3-install (avoids the theory-name clash).
   =========================================================================== *)

Theorem mc_target_config_x64:
  is_x64_machine_config mc ==> mc.target.config = x64_config
Proof
  rw [x64_configProofTheory.is_x64_machine_config_def]
  \\ rw [x64_targetTheory.x64_target_def]
QED

Theorem bs_isa_not_ag32:
  x64_config.ISA <> Ag32
Proof
  EVAL_TAC
QED

Theorem bs_ffi_names_extcall:
  OPTION_ALL (EVERY (\x. ?s. x = ExtCall s)) x64_backend_config.lab_conf.ffi_names
Proof
  EVAL_TAC
QED

Theorem bs_big_endian_F:
  x64_config.big_endian = F
Proof
  EVAL_TAC
QED

val mc_conf_ok_uh  = UNDISCH x64_configProofTheory.x64_machine_config_ok;
val mc_init_ok_uh  = UNDISCH x64_configProofTheory.x64_init_ok;
val backend_ok_th  = x64_configProofTheory.x64_backend_config_ok;

val mctc_uh   = UNDISCH mc_target_config_x64;
val x64_mc_ty = type_of (rand (hd (hyp mctc_uh)));
val bb_inst   = boundScanRung3Theory.boundScan_rung3_native
                |> Q.INST [`c` |-> `x64_backend_config`, `start` |-> `«main»`];
val bb_mc =
  let val (ante,_) = dest_imp (concl bb_inst)
      val conjs = strip_conj ante
      val t = valOf (List.find
        (fn t => (fst (dest_const (fst (strip_comb t))) = "mc_conf_ok")
                 handle _ => false) conjs)
  in rand t end;
val tyinst = match_type (type_of bb_mc) x64_mc_ty;

val reduced =
  bb_inst
  |> INST_TYPE tyinst
  |> REWRITE_RULE [mctc_uh]
  |> SIMP_RULE bool_ss
       (bs_big_endian_F ::
        map EQT_INTRO
          [backend_ok_th, mc_conf_ok_uh, mc_init_ok_uh,
           bs_isa_not_ag32, bs_ffi_names_extcall]);

val boundScan_rung3_installed =
  save_thm ("boundScan_rung3_installed", reduced |> DISCH_ALL);

(* ===========================================================================
   (B)  The whole-`main` FFI-trace frame reduction is proved in the sibling
   theory boundScanE2EFrame (isolated opens): boundScanProg_semantics_decls_bridge
   over boundScanBytesBridge$boundScanProg — the exact program the backbone uses.
   =========================================================================== *)

(* ===========================================================================
   (C)  COMPOSE — the end-to-end native-bytes theorem.  Build the goal in ML
   from the installed backbone's own antecedent/conclusion (no transcription):
   drop only its `semantics_decls <> Fail` conjunct (PROVED here from (B)), add
   the boundScanFFI contract + witness clock, and substitute the digest trace
   for the opaque semantics_decls in the singleton set.
   =========================================================================== *)

val inst_thm    = boundScan_rung3_installed;  (* is_x64.. ==> ANTE ==> subset_sd *)
val (x64_tm, rest) = dest_imp (concl inst_thm);
val (ante_tm, subset_sd) = dest_imp rest;

val sd_tm = find_term
  (fn t => same_const (fst (strip_comb t)) ``semantics_decls`` handle _ => false)
  subset_sd;

val notFail_tm = valOf (List.find (fn c => is_neg c andalso
     (let val e = dest_neg c in is_eq e andalso
        (same_const (fst (strip_comb (lhs e))) ``semantics_decls`` handle _ => false)
      end)) (boolSyntax.strip_conj ante_tm));

val pkg_tm = list_mk_conj
  (filter (fn c => not (aconv c notFail_tm)) (boolSyntax.strip_conj ante_tm));

val trace_tm =
  ``(s:(64,'ffi) panSem$state).ffi.io_events ++ loadEv ++
    [IO_event (ffi$ExtCall «report_vec»)
       (word_to_bytes (n2w (c0_encode (boundScan a off len)) : word64) F) rb]``;

val subset_spec = subst [sd_tm |-> ``Terminate Success ^trace_tm``] subset_sd;

val e2e_goal =
  mk_imp (x64_tm,
    mk_imp (list_mk_conj
              [pkg_tm,
               ``boundScanFFI a off len (s:(64,'ffi) panSem$state)``,
               ``?K. 0 < K /\ len < K``],
      mk_exists (``loadEv:io_event list``,
        mk_exists (``rb:(word8 # word8) list``, subset_spec))));

Theorem boundScan_rung3_e2e = prove (e2e_goal,
  strip_tac >> strip_tac >>
  (* (B): the whole-main frame value of semantics_decls *)
  `?loadEv rb. ^sd_tm = Terminate Success ^trace_tm`
     by (irule boundScanProg_semantics_decls_bridge >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac `loadEv` >> qexists_tac `rb` >>
  (* the backbone non-Fail side-condition, PROVED from the (B) value *)
  `^notFail_tm`
     by (qpat_x_assum `^sd_tm = _` (fn th => simp [th])) >>
  (* (A): specialise the installed backbone by its is_x64 antecedent *)
  `^ante_tm ==> ^subset_sd`
     by (match_mp_tac boundScan_rung3_installed >> first_assum ACCEPT_TAC) >>
  (* discharge the install package + non-Fail from the assumptions *)
  `^subset_sd`
     by (pop_assum match_mp_tac >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qpat_x_assum `^sd_tm = _` (fn th => gvs [th]));

(* ===========================================================================
   (D)  BOOTSTRAP-CERTIFIED end-to-end: discharge the G1 native-bytes antecedent
   (the `compile_prog_max ... = SOME(boundScanBytes,...)` conjunct) via the
   bootstrap theorem boundScan_G1_native (oracle cake_native_bootstrap, <=
   cake_compiled_thm) — the ONE named oracle, quarantined to G1.  The install
   package minus G1 is required to hold for THE compiler-output config (the
   universal `!c' stack_max. G1 c' stack_max ==> pkg c'`), which the bootstrap
   then instantiates to the concrete native boundScanBytes.

     [oracles: DISK_THM, cake_native_bootstrap] [axioms:]
   =========================================================================== *)

val e2e_x64_tm  = #1 (dest_imp (concl boundScan_rung3_e2e));
val e2e_bigante = #1 (dest_imp (#2 (dest_imp (concl boundScan_rung3_e2e))));
val e2e_conjs   = boolSyntax.strip_conj e2e_bigante;
val g1_conj     = hd e2e_conjs;                       (* compile_prog_max ... = SOME(...) *)
val rest_conj   = list_mk_conj (tl e2e_conjs);        (* pkg-minus-G1 /\ boundScanFFI /\ witness *)
val e2e_exconcl = #2 (dest_imp (#2 (dest_imp (concl boundScan_rung3_e2e))));
val cprime      = find_term (fn t => is_var t andalso fst (dest_var t) = "c'") g1_conj;
val smax        = find_term (fn t => is_var t andalso fst (dest_var t) = "stack_max") g1_conj;

val native_goal =
  mk_imp (e2e_x64_tm,
    mk_imp (list_mk_forall ([cprime, smax], mk_imp (g1_conj, rest_conj)),
            mk_exists (smax, e2e_exconcl)));

Theorem boundScan_rung3_e2e_native = prove (native_goal,
  rpt strip_tac >>
  `mc.target.config = x64_config` by metis_tac [mc_target_config_x64] >>
  drule boundScan_G1_native >> strip_tac >>
  qpat_x_assum `!c' stack_max. _` (qspecl_then [`c'm`, `sm`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexists_tac `sm` >>
  match_mp_tac (boundScan_rung3_e2e
                  |> Q.INST [`c'` |-> `c'm`, `stack_max` |-> `sm`]
                  |> REWRITE_RULE [AND_IMP_INTRO]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac []));

val _ = export_theory ();

(* ===========================================================================
   CN Rung-3-native for the SECURITY-HEADERS serve stage (S13, secheaders):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core.

     secheaders.pnk --native cake--> secheadersBytes (concrete x64, ~5ms, NO
       in-logic EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native
       bytes in the real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)-->
       machine_sem refines the Pancake SOURCE semantics of the exact stage program,
       with the program-level applicability conditions DISCHARGED here.

   Ground (identical to CN-RUNG3-NATIVE-REPORT.md, boundscan):
     - CN-NATIVE-BOOTSTRAP-REPORT.md  : native cake, cake_compiled_thm bootstrap.
     - CN-BYTES-BRIDGE-REPORT.md      : secheadersBytes/Bitmaps concrete; Layer 1
                                        (pan_to_target_compile_semantics INST at
                                        native bytes), Layer 2 (compile_prog =
                                        SOME(native bytes), oracle bootstrap).

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, discharged by EVAL
        against the REAL pan_to_targetProof / pan_to_wordProof constants on the
        bridge program.
     2. secheaders_rung3_native : Link B with the native bytes in the code slot and
        the four program conditions DISCHARGED — reducing to machine_sem refines
        {semantics_decls s <main> secheadersProg}.  DISK_THM only (native-bytes
        equation kept as a NAMED antecedent G1; the compile_prog<->compile_prog_max
        packaging lemma is CN-BYTES-BRIDGE 4.1).
     3. Link A, LOOP-FREE decision core: the emitted `If (maxage < 1)` extracted
        from the verified parser output computes n2w(hstsEff maxage) into <result>,
        where hstsEff m = (m != 0) is EXACTLY the Lean spec
        SecurityHeaders.effectiveIncludeSubDomains at the deployed includeSubDomains
        = true (drorb SecurityHeaders.lean; RFC 6797 6.1.1 max-age=0 gate).
        NO loop-invariant induction (the boundscan Link-A long pole) is needed:
        this stage is straight-line, so the whole decision core closes here.

   What is NOT closed (named, per the honesty rule, NOT faked):
     - The whole-main FFI frame: @load_vec establishes FLOOKUP <maxage> from the
       staged control block; @report_vec emits <result>.  The decision-core Link A
       assumes FLOOKUP s.locals <maxage> = SOME (ValWord (n2w m)); connecting it to
       main through the @load_vec FFI postcondition is the same FFI boundary
       boundscan names (CN-BOUNDSCAN-LINKA residual #1/#2) — the SAME residual, but
       here with NO loop between the FFI and the decision.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open secheadersBytesBridgeTheory;

val _ = new_theory "secheadersRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions of
      pan_to_target_compile_semantics, discharged by EVAL on the bridge program.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem sh_pancake_good_code:
  pancake_good_code secheadersProg
Proof
  REWRITE_TAC [secheadersBytesBridgeTheory.secheadersProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem sh_distinct_params:
  distinct_params (functions secheadersProg)
Proof
  REWRITE_TAC [secheadersBytesBridgeTheory.secheadersProg_def] \\ EVAL_TAC
QED

Theorem sh_distinct_names:
  ALL_DISTINCT (MAP FST (functions secheadersProg))
Proof
  REWRITE_TAC [secheadersBytesBridgeTheory.secheadersProg_def] \\ EVAL_TAC
QED

Theorem sh_size_of_eids:
  size_of_eids secheadersProg < dimword (:64)
Proof
  REWRITE_TAC [secheadersBytesBridgeTheory.secheadersProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val secheaders_rung3_native =
  save_thm ("secheaders_rung3_native",
    secheadersBytesBridgeTheory.secheaders_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [sh_pancake_good_code, sh_distinct_params,
             sh_distinct_names, sh_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A — the LOOP-FREE decision core.
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: effectiveIncludeSubDomains at the deployed
   includeSubDomains = true is (maxAge != 0).  Byte-identical to
   SecurityHeaders.effectiveIncludeSubDomains h = h.includeSubDomains && h.maxAge != 0
   specialised to h.includeSubDomains = true (drorb SecurityHeaders.lean). *)
Definition hstsEff_def:
  hstsEff (m:num) = if m = 0 then 0n else 1n
End

(* On the non-negative signed range the SIGNED word order agrees with nat order
   (the `Cmp Less` guard is signed).  Copied from CN-BOUNDSCAN-LINKA. *)
Theorem signed_lt_n2w64:
  !x y. x < 2n ** 63 /\ y < 2n ** 63 ==>
        (((n2w x):word64) < n2w y <=> x < y)
Proof
  rw [] >>
  `(2:num) ** 63 < 2 ** 64` by EVAL_TAC >>
  `x < dimword(:64) /\ y < dimword(:64)` by
    (`dimword(:64) = 2 ** 64` by EVAL_TAC >> fs [] >>
     conj_tac >> metis_tac [LESS_TRANS]) >>
  `~word_msb ((n2w x):word64) /\ ~word_msb ((n2w y):word64)` by
    (rw [word_msb_n2w] >> irule NOT_BIT_GT_TWOEXP >> fs []) >>
  rw [WORD_LT, w2n_n2w] >> fs []
QED

(* Structural extraction of the (first) `If` from a decl body — the loop-free
   analogue of CN-BOUNDSCAN-LINKA's extract_while.  The whole outer If (including
   its nested branches) is returned; the extraction pins the term to the verified
   parser output, so it is not a hand transcription asserted to match. *)
Definition extract_if_def:
  (extract_if (Seq c1 c2) =
     (case extract_if c1 of SOME w => SOME w | NONE => extract_if c2)) /\
  (extract_if (Dec _ _ _ p) = extract_if p) /\
  (extract_if (If g c1 c2) = SOME (If g c1 c2)) /\
  (extract_if _ = NONE)
End

Definition extract_if_decl_def:
  (extract_if_decl (Function fd) = extract_if fd.body) /\
  (extract_if_decl _ = NONE)
End

(* The decision core, transcribed from the parser output (dump_ast.out). *)
Definition secheadersIf_def:
  secheadersIf =
    If (Cmp Less (Var Local (strlit "maxage")) (Const (1w:word64)))
       (Seq (Annot (strlit "location") (strlit "(33:4 33:13)"))
            (Assign Local (strlit "result") (Const (0w:word64))))
       (Seq (Annot (strlit "location") (strlit "(35:4 35:13)"))
            (Assign Local (strlit "result") (Const (1w:word64))))
End

(* Faithfulness: secheadersIf IS the (first) If inside the verified parser output
   secheadersProg — kernel-checked by EVAL, so the decision core cannot silently
   diverge from what leanc emitted + the CakeML parser produced. *)
Theorem secheadersIf_faithful:
  extract_if_decl (HD secheadersProg) = SOME secheadersIf
Proof
  rw [secheadersBytesBridgeTheory.secheadersProg_def, extract_if_decl_def,
      extract_if_def, secheadersIf_def]
QED

(* One Annot-wrapped result-assign, for any location strings and any target word:
   preserves everything but <result>, which becomes ValWord w.  Requires <result>
   already present (established by the `var result = 0` Dec in main). *)
Theorem eval_annot_result_assign:
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  evaluate (Seq (Annot a b)
              (Assign Local (strlit "result") (Const (w:word64))), s)
    = (NONE, s with locals := s.locals |+ (strlit "result", ValWord w))
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
        shape_of_def, set_kvar_def, set_var_def]
QED

(* THE decision-core Link A: the emitted If computes n2w(hstsEff m) into <result>,
   for a maxage m in the non-negative signed range.  Straight-line — no loop
   induction. *)
Theorem secheaders_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "maxage") = SOME (ValWord (n2w m)) /\
  m < 2n ** 63 /\
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  ?s'. evaluate (secheadersIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "result") =
         SOME (ValWord (n2w (hstsEff m)))
Proof
  strip_tac >>
  `(1w:word64) = n2w 1` by EVAL_TAC >>
  `((n2w m):word64 < n2w 1) = (m < 1)`
     by (irule signed_lt_n2w64 >> fs []) >>
  `((n2w m):word64 < 1w) = (m = 0)` by fs [] >>
  simp [secheadersIf_def, Once evaluate_def, eval_def,
        asmTheory.word_cmp_def] >>
  Cases_on `m = 0` >>
  fs [eval_annot_result_assign, hstsEff_def, FLOOKUP_UPDATE]
QED

(* ---------------------------------------------------------------------------
   Verification dump.
   --------------------------------------------------------------------------- *)
val _ =
  let val os = TextIO.openOut "rung3.out"
      fun p s = TextIO.output (os, s)
      fun tagstr th =
        let val (orc, ax) = Tag.dest_tag (Thm.tag th)
        in "[oracles: " ^ String.concatWith "," orc ^ "] [axioms: "
           ^ String.concatWith "," ax ^ "]" end
  in
    p ("=== sh_pancake_good_code ===\n" ^ tagstr sh_pancake_good_code ^ "\n");
    p ("=== sh_distinct_params ===\n" ^ tagstr sh_distinct_params ^ "\n");
    p ("=== sh_distinct_names ===\n" ^ tagstr sh_distinct_names ^ "\n");
    p ("=== sh_size_of_eids ===\n"
       ^ thm_to_string sh_size_of_eids ^ "\n" ^ tagstr sh_size_of_eids ^ "\n\n");
    p ("=== secheaders_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr secheaders_rung3_native ^ "\n");
    let val c = concl secheaders_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== secheadersIf_faithful ===\n"
       ^ thm_to_string secheadersIf_faithful ^ "\n"
       ^ tagstr secheadersIf_faithful ^ "\n\n");
    p ("=== secheaders_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string secheaders_decisioncore_refines_spec ^ "\n"
       ^ tagstr secheaders_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (secheadersRung3) = "
       ^ Int.toString (length (axioms "secheadersRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

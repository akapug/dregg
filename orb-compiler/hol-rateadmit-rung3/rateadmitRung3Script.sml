(* ===========================================================================
   CN Rung-3-native for the RATE-LIMIT serve stage (S4, rateadmit):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the token-admit threshold).

     rateadmit.pnk --native cake--> rateadmitBytes (concrete x64, ~5ms, NO
       in-logic EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native
       bytes in the real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)-->
       machine_sem refines the Pancake SOURCE semantics of the exact stage program,
       with the program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-RUNG3-NATIVE-REPORT.md (boundscan) and the wave-4
   secheaders/redirect lanes (CN-MORE-STAGES-REPORT.md).

   Honest scope note.  `rateadmit.pnk` is the LOOP-FREE DECISION PROJECTION of the
   deployed S4 `Rate.rateStage` — the token-admit threshold `Rate.Bucket.tryAdmit`
   decides on, given the refilled bucket's token count.  The full windowed-counter /
   refill loop body is the named S4 loop residual (PNK-MANIFEST §3, §4-item-2); this
   lane certifies the decision projection, exactly as the manifest scopes S4.

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. rateadmit_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted `If (NotLess tokens 1)`
        extracted from the verified parser output computes n2w(rateAdmit tokens)
        into <result>, where rateAdmit t = (if 1 <= t then 1 else 0) is EXACTLY
        the admit bit `(Rate.Bucket.tryAdmit b).2` as a function of b.tokens = t
        (drorb Rate/Bucket.lean: tryAdmit b = if 1 <= b.tokens then (.., T) else (b, F)).
        Straight-line — NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The whole-main FFI frame (@load_vec establishes FLOOKUP <tokens>; @report_vec
       emits <result>) — the SAME FFI boundary boundscan names, here with NO loop.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open rateadmitBytesBridgeTheory;

val _ = new_theory "rateadmitRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem ra_pancake_good_code:
  pancake_good_code rateadmitProg
Proof
  REWRITE_TAC [rateadmitBytesBridgeTheory.rateadmitProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem ra_distinct_params:
  distinct_params (functions rateadmitProg)
Proof
  REWRITE_TAC [rateadmitBytesBridgeTheory.rateadmitProg_def] \\ EVAL_TAC
QED

Theorem ra_distinct_names:
  ALL_DISTINCT (MAP FST (functions rateadmitProg))
Proof
  REWRITE_TAC [rateadmitBytesBridgeTheory.rateadmitProg_def] \\ EVAL_TAC
QED

Theorem ra_size_of_eids:
  size_of_eids rateadmitProg < dimword (:64)
Proof
  REWRITE_TAC [rateadmitBytesBridgeTheory.rateadmitProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val rateadmit_rung3_native =
  save_thm ("rateadmit_rung3_native",
    rateadmitBytesBridgeTheory.rateadmit_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [ra_pancake_good_code, ra_distinct_params,
             ra_distinct_names, ra_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A — the LOOP-FREE decision core (the token-admit threshold).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: the admit bit of Rate.Bucket.tryAdmit as a
   function of the refilled bucket's token count t.
   Rate.Bucket.tryAdmit b = if 1 <= b.tokens then ({b with tokens := b.tokens-1}, T)
                            else (b, F)  (drorb Rate/Bucket.lean:77).
   The admit bit .2 = (1 <= t); reported as 1/0. *)
Definition rateAdmit_def:
  rateAdmit (t:num) = if 1 <= t then 1n else 0n
End

(* On the non-negative signed range the SIGNED word order agrees with nat order
   (the `Cmp NotLess` guard is signed: word_cmp NotLess w1 w2 = ~(w1 < w2)).
   Copied from CN-BOUNDSCAN-LINKA / secheaders. *)
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
   analogue of CN-BOUNDSCAN-LINKA's extract_while.  Pins the reasoned-about term to
   the verified parser output, so it is not a hand transcription asserted to match. *)
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

(* The decision core, transcribed from the parser output (extract dump). *)
Definition rateadmitIf_def:
  rateadmitIf =
    If (Cmp NotLess (Var Local (strlit "tokens")) (Const (1w:word64)))
       (Seq (Annot (strlit "location") (strlit "(30:4 30:13)"))
            (Assign Local (strlit "result") (Const (1w:word64))))
       (Seq (Annot (strlit "location") (strlit "(32:4 32:13)"))
            (Assign Local (strlit "result") (Const (0w:word64))))
End

(* Faithfulness: rateadmitIf IS the (first) If inside the verified parser output
   rateadmitProg — kernel-checked by EVAL. *)
Theorem rateadmitIf_faithful:
  extract_if_decl (HD rateadmitProg) = SOME rateadmitIf
Proof
  rw [rateadmitBytesBridgeTheory.rateadmitProg_def, extract_if_decl_def,
      extract_if_def, rateadmitIf_def]
QED

(* One Annot-wrapped result-assign, for any location strings and any target word. *)
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

(* THE decision-core Link A: the emitted If computes n2w(rateAdmit t) into <result>,
   for a token count t in the non-negative signed range.  Straight-line. *)
Theorem rateadmit_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "tokens") = SOME (ValWord (n2w t)) /\
  t < 2n ** 63 /\
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  ?s'. evaluate (rateadmitIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "result") =
         SOME (ValWord (n2w (rateAdmit t)))
Proof
  strip_tac >>
  `(1w:word64) = n2w 1` by EVAL_TAC >>
  `((n2w t):word64 < n2w 1) = (t < 1)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [rateadmitIf_def, Once evaluate_def, eval_def,
        asmTheory.word_cmp_def] >>
  Cases_on `t < 1` >>
  fs [eval_annot_result_assign, rateAdmit_def, FLOOKUP_UPDATE]
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
    p ("=== ra_pancake_good_code ===\n" ^ tagstr ra_pancake_good_code ^ "\n");
    p ("=== ra_distinct_params ===\n" ^ tagstr ra_distinct_params ^ "\n");
    p ("=== ra_distinct_names ===\n" ^ tagstr ra_distinct_names ^ "\n");
    p ("=== ra_size_of_eids ===\n"
       ^ thm_to_string ra_size_of_eids ^ "\n" ^ tagstr ra_size_of_eids ^ "\n\n");
    p ("=== rateadmit_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr rateadmit_rung3_native ^ "\n");
    let val c = concl rateadmit_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== rateadmitIf_faithful ===\n"
       ^ thm_to_string rateadmitIf_faithful ^ "\n"
       ^ tagstr rateadmitIf_faithful ^ "\n\n");
    p ("=== rateadmit_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string rateadmit_decisioncore_refines_spec ^ "\n"
       ^ tagstr rateadmit_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (rateadmitRung3) = "
       ^ Int.toString (length (axioms "rateadmitRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

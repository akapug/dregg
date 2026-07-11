(* ===========================================================================
   CN Rung-3-native for the CACHE-FRESHNESS serve stage (S5, cachefresh):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the freshness `<` gate).

     cachefresh.pnk --native cake--> cachefreshBytes (concrete x64, ~5ms, NO
       in-logic EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native
       bytes in the real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)-->
       machine_sem refines the Pancake SOURCE semantics of the exact stage program,
       with the program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-MORE-STAGES-REPORT.md (secheaders/redirect) and
   CN-MORE-STAGES-2-REPORT.md (rateadmit/gzipupper).

   Scope.  `cachefresh.pnk` is WHOLE-STAGE loop-free: the deployed S5 cache stage's
   freshness test `Cache.Meta.isFresh m now = decide (currentAge < freshnessLifetime)`
   at the deployed `freshnessLifetime = 100` (drorb Cache.lean; consulted by
   Reactor.Stage.Cache.Config.onReq / cacheEmptyStage, position S5 of
   Reactor.Deploy.deployStagesFull2).  Like secheaders/redirect this is a loop-free
   whole-stage decision (NOT a decision projection): the emitted `If (age < 100)` IS
   the stage's freshness behaviour.  (The other S5 representatives cachekey/hashbytes
   are the key/digest folds; their Link-A loop refinements are the named S5 residual.)

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. cachefresh_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted `If (Less age 100)` extracted
        from the verified parser output computes n2w(cacheFresh age) into <result>,
        where cacheFresh a = (if a < 100 then 1 else 0) is EXACTLY Cache.Meta.isFresh
        specialised to freshnessLifetime = 100 (fresh=1, stale=0).  Straight-line —
        NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The whole-main FFI frame (@load_vec establishes FLOOKUP <age>; @report_vec
       emits <result>) — the SAME FFI boundary boundscan names, here with NO loop.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open cachefreshBytesBridgeTheory;

val _ = new_theory "cachefreshRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem cf_pancake_good_code:
  pancake_good_code cachefreshProg
Proof
  REWRITE_TAC [cachefreshBytesBridgeTheory.cachefreshProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem cf_distinct_params:
  distinct_params (functions cachefreshProg)
Proof
  REWRITE_TAC [cachefreshBytesBridgeTheory.cachefreshProg_def] \\ EVAL_TAC
QED

Theorem cf_distinct_names:
  ALL_DISTINCT (MAP FST (functions cachefreshProg))
Proof
  REWRITE_TAC [cachefreshBytesBridgeTheory.cachefreshProg_def] \\ EVAL_TAC
QED

Theorem cf_size_of_eids:
  size_of_eids cachefreshProg < dimword (:64)
Proof
  REWRITE_TAC [cachefreshBytesBridgeTheory.cachefreshProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val cachefresh_rung3_native =
  save_thm ("cachefresh_rung3_native",
    cachefreshBytesBridgeTheory.cachefresh_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [cf_pancake_good_code, cf_distinct_params,
             cf_distinct_names, cf_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A — the LOOP-FREE decision core (the freshness `<` gate).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: Cache.Meta.isFresh at freshnessLifetime = 100.
   isFresh m now = decide (currentAge < freshnessLifetime) (drorb Cache.lean);
   fresh = 1, stale = 0. *)
Definition cacheFresh_def:
  cacheFresh (a:num) = if a < 100 then 1n else 0n
End

(* On the non-negative signed range the SIGNED word order agrees with nat order
   (the `Cmp Less` guard is signed).  Copied from CN-BOUNDSCAN-LINKA / secheaders. *)
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

(* The decision core, transcribed from the parser output (extract dump).
   then-arm (age < 100): result := 1 (fresh) ; else-arm: result := 0 (stale). *)
Definition cachefreshIf_def:
  cachefreshIf =
    If (Cmp Less (Var Local (strlit "age")) (Const (100w:word64)))
       (Seq (Annot (strlit "location") (strlit "(30:4 30:13)"))
            (Assign Local (strlit "result") (Const (1w:word64))))
       (Seq (Annot (strlit "location") (strlit "(32:4 32:13)"))
            (Assign Local (strlit "result") (Const (0w:word64))))
End

(* Faithfulness: cachefreshIf IS the (first) If inside the verified parser output
   cachefreshProg — kernel-checked by EVAL. *)
Theorem cachefreshIf_faithful:
  extract_if_decl (HD cachefreshProg) = SOME cachefreshIf
Proof
  rw [cachefreshBytesBridgeTheory.cachefreshProg_def, extract_if_decl_def,
      extract_if_def, cachefreshIf_def]
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

(* THE decision-core Link A: the emitted If computes n2w(cacheFresh a) into <result>,
   for an age a in the non-negative signed range.  Straight-line. *)
Theorem cachefresh_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "age") = SOME (ValWord (n2w a)) /\
  a < 2n ** 63 /\
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  ?s'. evaluate (cachefreshIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "result") =
         SOME (ValWord (n2w (cacheFresh a)))
Proof
  strip_tac >>
  `(100w:word64) = n2w 100` by EVAL_TAC >>
  `((n2w a):word64 < n2w 100) = (a < 100)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [cachefreshIf_def, Once evaluate_def, eval_def,
        asmTheory.word_cmp_def] >>
  Cases_on `a < 100` >>
  fs [eval_annot_result_assign, cacheFresh_def, FLOOKUP_UPDATE]
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
    p ("=== cf_pancake_good_code ===\n" ^ tagstr cf_pancake_good_code ^ "\n");
    p ("=== cf_distinct_params ===\n" ^ tagstr cf_distinct_params ^ "\n");
    p ("=== cf_distinct_names ===\n" ^ tagstr cf_distinct_names ^ "\n");
    p ("=== cf_size_of_eids ===\n"
       ^ thm_to_string cf_size_of_eids ^ "\n" ^ tagstr cf_size_of_eids ^ "\n\n");
    p ("=== cachefresh_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr cachefresh_rung3_native ^ "\n");
    let val c = concl cachefresh_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== cachefreshIf_faithful ===\n"
       ^ thm_to_string cachefreshIf_faithful ^ "\n"
       ^ tagstr cachefreshIf_faithful ^ "\n\n");
    p ("=== cachefresh_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string cachefresh_decisioncore_refines_spec ^ "\n"
       ^ tagstr cachefresh_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (cachefreshRung3) = "
       ^ Int.toString (length (axioms "cachefreshRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

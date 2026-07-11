(* ===========================================================================
   CN Rung-3-native for the GZIP case-fold serve stage (S11, gzipupper):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (a NESTED two-threshold ASCII-uppercase
   test).

     gzipupper.pnk --native cake--> gzipupperBytes (concrete x64, ~5ms, NO
       in-logic EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native
       bytes in the real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)-->
       machine_sem refines the Pancake SOURCE semantics of the exact stage program,
       with the program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-RUNG3-NATIVE-REPORT.md (boundscan) and the wave-4
   secheaders/redirect lanes (CN-MORE-STAGES-REPORT.md).

   Honest scope note.  `gzipupper.pnk` is the LOOP-FREE DECISION PROJECTION of the
   deployed S11 `Gzip.gzipStage` — the per-byte ASCII-uppercase test at the heart of
   `Gzip.lowerByte` (whether byte b is an uppercase letter, i.e. whether lowerByte
   subtracts 32).  The full body-rewrite / `Gzip.lower` map loop is the named S11
   loop residual (PNK-MANIFEST §3, §4-item-2); this lane certifies the decision
   projection, exactly as the manifest scopes S11.

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. gzipupper_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted NESTED `If` (two `NotLess`
        thresholds, both operand orientations) extracted from the verified parser
        output computes n2w(gzipUpper b) into <result>, where
          gzipUpper b = if 65 <= b /\ b <= 90 then 1 else 0
        is EXACTLY the guard of the Lean spec Gzip.lowerByte
          lowerByte b = if 65 <= b && b <= 90 then b + 32 else b
        (drorb Reactor/Stage/Gzip.lean:37 / Reactor/ServeStep.lean:238).
        Straight-line — NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The whole-main FFI frame (@load_vec establishes FLOOKUP <b>; @report_vec
       emits <result>) — the SAME FFI boundary boundscan names, here with NO loop.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open gzipupperBytesBridgeTheory;

val _ = new_theory "gzipupperRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem gz_pancake_good_code:
  pancake_good_code gzipupperProg
Proof
  REWRITE_TAC [gzipupperBytesBridgeTheory.gzipupperProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem gz_distinct_params:
  distinct_params (functions gzipupperProg)
Proof
  REWRITE_TAC [gzipupperBytesBridgeTheory.gzipupperProg_def] \\ EVAL_TAC
QED

Theorem gz_distinct_names:
  ALL_DISTINCT (MAP FST (functions gzipupperProg))
Proof
  REWRITE_TAC [gzipupperBytesBridgeTheory.gzipupperProg_def] \\ EVAL_TAC
QED

Theorem gz_size_of_eids:
  size_of_eids gzipupperProg < dimword (:64)
Proof
  REWRITE_TAC [gzipupperBytesBridgeTheory.gzipupperProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val gzipupper_rung3_native =
  save_thm ("gzipupper_rung3_native",
    gzipupperBytesBridgeTheory.gzipupper_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [gz_pancake_good_code, gz_distinct_params,
             gz_distinct_names, gz_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A — the LOOP-FREE decision core (nested ASCII-uppercase test).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: the ASCII-uppercase guard of Gzip.lowerByte.
   lowerByte b = if 65 <= b && b <= 90 then b + 32 else b (drorb Gzip.lean:37);
   the loop-free decision core is whether b is an uppercase letter. *)
Definition gzipUpper_def:
  gzipUpper (b:num) = if 65 <= b /\ b <= 90 then 1n else 0n
End

(* On the non-negative signed range the SIGNED word order agrees with nat order
   (the two `Cmp NotLess` guards are signed: word_cmp NotLess w1 w2 = ~(w1 < w2)). *)
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

(* Structural extraction of the (first) `If` from a decl body. *)
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
   Outer guard: 65 <= b  ->  NotLess (Var b) (Const 65)  (variable on LEFT).
   Inner guard: b <= 90   ->  NotLess (Const 90) (Var b)  (variable on RIGHT).
   Both operand orientations of the signed NotLess exercised. *)
Definition gzipupperIf_def:
  gzipupperIf =
    If (Cmp NotLess (Var Local (strlit "b")) (Const (65w:word64)))
       (Seq (Annot (strlit "location") (strlit "(28:7 31:15)"))
          (If (Cmp NotLess (Const (90w:word64)) (Var Local (strlit "b")))
             (Seq (Annot (strlit "location") (strlit "(29:6 29:15)"))
                  (Assign Local (strlit "result") (Const (1w:word64))))
             (Seq (Annot (strlit "location") (strlit "(31:6 31:15)"))
                  (Assign Local (strlit "result") (Const (0w:word64))))))
       (Seq (Annot (strlit "location") (strlit "(34:4 34:13)"))
            (Assign Local (strlit "result") (Const (0w:word64))))
End

(* Faithfulness: gzipupperIf IS the (first) If inside the verified parser output
   gzipupperProg — kernel-checked by EVAL. *)
Theorem gzipupperIf_faithful:
  extract_if_decl (HD gzipupperProg) = SOME gzipupperIf
Proof
  rw [gzipupperBytesBridgeTheory.gzipupperProg_def, extract_if_decl_def,
      extract_if_def, gzipupperIf_def]
QED

(* Strip a leading parser Annot no-op inside a Seq (any location strings). *)
Theorem seq_annot:
  evaluate (Seq (Annot a b) c, s) = evaluate (c, s)
Proof
  simp [evaluate_def, fix_clock_def, state_component_equality]
QED

(* Unfold one `If` on a word guard — controlled, so the nested dispatch unfolds
   without dragging in the evaluate_def Seq clause (which fights seq_annot). *)
Theorem eval_If:
  evaluate (If g t e, s) =
    case eval s g of
      SOME (ValWord w) => evaluate (if w <> 0w then t else e, s)
    | _ => (SOME Error, s)
Proof
  simp [evaluate_def]
QED

(* One result-assign (requires <result> already present). *)
Theorem eval_result_assign:
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  evaluate (Assign Local (strlit "result") (Const (w:word64)), s)
    = (NONE, s with locals := s.locals |+ (strlit "result", ValWord w))
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
        shape_of_def, set_kvar_def, set_var_def]
QED

(* THE decision-core Link A: the emitted nested If computes n2w(gzipUpper b) into
   <result>, for a byte value b in the non-negative signed range.  Straight-line. *)
Theorem gzipupper_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "b") = SOME (ValWord (n2w b)) /\
  b < 2n ** 63 /\
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  ?s'. evaluate (gzipupperIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "result") =
         SOME (ValWord (n2w (gzipUpper b)))
Proof
  strip_tac >>
  `(65w:word64) = n2w 65 /\ (90w:word64) = n2w 90` by EVAL_TAC >>
  `((n2w b):word64 < n2w 65) = (b < 65)`
     by (irule signed_lt_n2w64 >> fs []) >>
  `((n2w 90):word64 < n2w b) = (90 < b)`
     by (irule signed_lt_n2w64 >> fs []) >>
  Cases_on `b < 65` >> Cases_on `90 < b` >>
  fs [gzipupperIf_def, eval_If, seq_annot, eval_result_assign, eval_def,
      asmTheory.word_cmp_def, gzipUpper_def, FLOOKUP_UPDATE]
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
    p ("=== gz_pancake_good_code ===\n" ^ tagstr gz_pancake_good_code ^ "\n");
    p ("=== gz_distinct_params ===\n" ^ tagstr gz_distinct_params ^ "\n");
    p ("=== gz_distinct_names ===\n" ^ tagstr gz_distinct_names ^ "\n");
    p ("=== gz_size_of_eids ===\n"
       ^ thm_to_string gz_size_of_eids ^ "\n" ^ tagstr gz_size_of_eids ^ "\n\n");
    p ("=== gzipupper_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr gzipupper_rung3_native ^ "\n");
    let val c = concl gzipupper_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== gzipupperIf_faithful ===\n"
       ^ thm_to_string gzipupperIf_faithful ^ "\n"
       ^ tagstr gzipupperIf_faithful ^ "\n\n");
    p ("=== gzipupper_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string gzipupper_decisioncore_refines_spec ^ "\n"
       ^ tagstr gzipupper_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (gzipupperRung3) = "
       ^ Int.toString (length (axioms "gzipupperRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

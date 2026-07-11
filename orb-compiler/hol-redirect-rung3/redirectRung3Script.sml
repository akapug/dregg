(* ===========================================================================
   CN Rung-3-native for the REDIRECT-STATUS serve stage (S6, redirectstatus):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (an equality dispatch on the Code tag).

     redirectstatus.pnk --native cake--> redirectBytes (concrete x64, ~5ms, NO
       in-logic EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native
       bytes in the real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)-->
       machine_sem refines the Pancake SOURCE semantics of the exact stage program,
       with the program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-RUNG3-NATIVE-REPORT.md (boundscan).

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. redirect_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted nested `If` equality-dispatch
        extracted from the verified parser output computes n2w(redirStatus code)
        into <result>, where redirStatus is EXACTLY the Lean spec
        Redirect.Code.status (drorb Redirect.lean; RFC 9110 15.4):
          0->301, 1->302, 2->307, else->308.
        Straight-line — NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The whole-main FFI frame (@load_vec establishes FLOOKUP <code>; @report_vec
       emits <result>) — the SAME FFI boundary boundscan names, here with NO loop.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open redirectBytesBridgeTheory;

val _ = new_theory "redirectRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem rs_pancake_good_code:
  pancake_good_code redirectProg
Proof
  REWRITE_TAC [redirectBytesBridgeTheory.redirectProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem rs_distinct_params:
  distinct_params (functions redirectProg)
Proof
  REWRITE_TAC [redirectBytesBridgeTheory.redirectProg_def] \\ EVAL_TAC
QED

Theorem rs_distinct_names:
  ALL_DISTINCT (MAP FST (functions redirectProg))
Proof
  REWRITE_TAC [redirectBytesBridgeTheory.redirectProg_def] \\ EVAL_TAC
QED

Theorem rs_size_of_eids:
  size_of_eids redirectProg < dimword (:64)
Proof
  REWRITE_TAC [redirectBytesBridgeTheory.redirectProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val redirect_rung3_native =
  save_thm ("redirect_rung3_native",
    redirectBytesBridgeTheory.redirect_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [rs_pancake_good_code, rs_distinct_params,
             rs_distinct_names, rs_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A — the LOOP-FREE decision core (equality dispatch on the Code tag).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: Redirect.Code.status (RFC 9110 15.4).
   Byte-identical to drorb Redirect.Code.status on the tag encoding
   moved301=0, found302=1, temp307=2, perm308=3(else). *)
Definition redirStatus_def:
  redirStatus (c:num) =
    if c = 0 then 301n else if c = 1 then 302n else if c = 2 then 307n else 308n
End

(* n2w equality on the bounded range. *)
Theorem n2w_eq_bounded64:
  !c k. c < dimword (:64) /\ k < dimword (:64) ==>
        (((n2w c):word64 = n2w k) = (c = k))
Proof
  rw [] >>
  `((n2w c):word64 = n2w k) = (c MOD dimword (:64) = k MOD dimword (:64))`
     by rw [n2w_11] >>
  fs [LESS_MOD]
QED

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
Definition redirectIf_def:
  redirectIf =
    If (Cmp Equal (Var Local (strlit "code")) (Const (0w:word64)))
       (Seq (Annot (strlit "location") (strlit "(31:4 31:15)"))
            (Assign Local (strlit "result") (Const (301w:word64))))
       (Seq (Annot (strlit "location") (strlit "(33:7 39:19)"))
          (If (Cmp Equal (Var Local (strlit "code")) (Const (1w:word64)))
             (Seq (Annot (strlit "location") (strlit "(34:6 34:17)"))
                  (Assign Local (strlit "result") (Const (302w:word64))))
             (Seq (Annot (strlit "location") (strlit "(36:9 39:19)"))
                (If (Cmp Equal (Var Local (strlit "code")) (Const (2w:word64)))
                   (Seq (Annot (strlit "location") (strlit "(37:8 37:19)"))
                        (Assign Local (strlit "result") (Const (307w:word64))))
                   (Seq (Annot (strlit "location") (strlit "(39:8 39:19)"))
                        (Assign Local (strlit "result")
                           (Const (308w:word64))))))))
End

Theorem redirectIf_faithful:
  extract_if_decl (HD redirectProg) = SOME redirectIf
Proof
  rw [redirectBytesBridgeTheory.redirectProg_def, extract_if_decl_def,
      extract_if_def, redirectIf_def]
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

(* THE decision-core Link A: the emitted nested If computes n2w(redirStatus c)
   into <result>, for a code tag c in the word range.  Straight-line. *)
Theorem redirect_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "code") = SOME (ValWord (n2w c)) /\
  c < dimword (:64) /\
  (?r0. FLOOKUP s.locals (strlit "result") = SOME (ValWord r0)) ==>
  ?s'. evaluate (redirectIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "result") =
         SOME (ValWord (n2w (redirStatus c)))
Proof
  strip_tac >>
  `(0w:word64) = n2w 0 /\ (1w:word64) = n2w 1 /\ (2w:word64) = n2w 2` by EVAL_TAC >>
  `(0:num) < dimword (:64) /\ (1:num) < dimword (:64) /\ (2:num) < dimword (:64)`
     by EVAL_TAC >>
  `(((n2w c):word64 = n2w 0) = (c = 0)) /\
   (((n2w c):word64 = n2w 1) = (c = 1)) /\
   (((n2w c):word64 = n2w 2) = (c = 2))`
     by (rpt conj_tac >> irule n2w_eq_bounded64 >> fs []) >>
  Cases_on `c = 0` >> Cases_on `c = 1` >> Cases_on `c = 2` >>
  fs [redirectIf_def, eval_If, seq_annot, eval_result_assign, eval_def,
      asmTheory.word_cmp_def, redirStatus_def, FLOOKUP_UPDATE]
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
    p ("=== rs_pancake_good_code ===\n" ^ tagstr rs_pancake_good_code ^ "\n");
    p ("=== rs_distinct_params ===\n" ^ tagstr rs_distinct_params ^ "\n");
    p ("=== rs_distinct_names ===\n" ^ tagstr rs_distinct_names ^ "\n");
    p ("=== rs_size_of_eids ===\n"
       ^ thm_to_string rs_size_of_eids ^ "\n" ^ tagstr rs_size_of_eids ^ "\n\n");
    p ("=== redirect_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr redirect_rung3_native ^ "\n");
    let val c = concl redirect_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== redirectIf_faithful ===\n"
       ^ thm_to_string redirectIf_faithful ^ "\n"
       ^ tagstr redirectIf_faithful ^ "\n\n");
    p ("=== redirect_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string redirect_decisioncore_refines_spec ^ "\n"
       ^ tagstr redirect_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (redirectRung3) = "
       ^ Int.toString (length (axioms "redirectRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

(* ===========================================================================
   CN Rung-3-native for the PATH-TRAVERSAL serve stage (S7, traversal):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the ".."-escape gate).

     traversal.pnk --native cake--> traversalBytes (concrete x64, ~7ms, NO in-logic
       EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native bytes in the
       real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)--> machine_sem
       refines the Pancake SOURCE semantics of the exact stage program, with the
       program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-MORE-STAGES-REPORT.md (secheaders/redirect),
   CN-MORE-STAGES-2-REPORT.md (rateadmit/gzipupper) and CN-MORE-STAGES-3-REPORT.md
   (cachefresh/cors).

   Honest scope note.  `traversal.pnk` is the DECISION PROJECTION of the deployed S7
   `traversalStage` (drorb Reactor.Deploy.traversalStage / targetEscapes / escapesSegs
   = (decodeSegs segs).contains ".."):
     blocked  iff  the decoded path contains a ".." segment.
   The stage first runs ONE 5-state escape-detector fold over the decoded path bytes
   (state 4 = an internal ".." segment was closed by '/'; state 2 = a trailing bare
   ".." segment), then the gate decides
     dec = 1  iff  acc = 4 \/ acc = 2   (BLOCKED),
     dec = 0  otherwise                 (ALLOWED).
   This lane certifies the loop-free GATE `If` over the fold output {acc}; the
   escape-detector fold body + its Link-A refinement is the named S7 loop residual
   (the same residual class as C22/C23/rateadmit/cors).

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. traversal_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted nested gate `If` (an outer
        `Cmp Equal acc 4` and an inner `Cmp Equal acc 2`, with the acc<>4/\acc<>2
        fall-through leaving <dec> at its initial 0) extracted from the verified
        parser output computes n2w(travBlock acc) into <dec>, where
          travBlock acc = if acc = 4 then 1 else if acc = 2 then 1 else 0
        is EXACTLY escapesSegs' ".."-contains as a function of the fold output.
        Straight-line -- NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The escape-detector fold loop + its Link-A refinement -- the named S7 loop
       residual, unchanged.
     - The whole-main FFI frame (@load_vec establishes the arena; @report_vec emits
       <dec>) -- the SAME FFI boundary boundscan names.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) -- kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open traversalBytesBridgeTheory;

val _ = new_theory "traversalRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem tr_pancake_good_code:
  pancake_good_code traversalProg
Proof
  REWRITE_TAC [traversalBytesBridgeTheory.traversalProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem tr_distinct_params:
  distinct_params (functions traversalProg)
Proof
  REWRITE_TAC [traversalBytesBridgeTheory.traversalProg_def] \\ EVAL_TAC
QED

Theorem tr_distinct_names:
  ALL_DISTINCT (MAP FST (functions traversalProg))
Proof
  REWRITE_TAC [traversalBytesBridgeTheory.traversalProg_def] \\ EVAL_TAC
QED

Theorem tr_size_of_eids:
  size_of_eids traversalProg < dimword (:64)
Proof
  REWRITE_TAC [traversalBytesBridgeTheory.traversalProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val traversal_rung3_native =
  save_thm ("traversal_rung3_native",
    traversalBytesBridgeTheory.traversal_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [tr_pancake_good_code, tr_distinct_params,
             tr_distinct_names, tr_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A -- the LOOP-FREE decision core (the ".."-escape gate).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: escapesSegs' ".."-contains as a function of
   the fold output.  acc = 4 = an internal ".." segment was closed; acc = 2 = a
   trailing bare ".." segment; either -> BLOCKED (1); else ALLOWED (0). *)
Definition travBlock_def:
  travBlock (acc:num) = if acc = 4 then 1n else if acc = 2 then 1n else 0n
End

(* n2w injective on the machine word range -- for the two Equal guards
   (Equal acc 4 ; Equal acc 2).  Copied from the cors/redirect lane. *)
Theorem n2w_eq_bounded64:
  !x y. x < dimword (:64) /\ y < dimword (:64) ==>
        (((n2w x):word64 = n2w y) <=> (x = y))
Proof
  rw [n2w_11] >>
  `x MOD dimword (:64) = x /\ y MOD dimword (:64) = y` by simp [LESS_MOD] >>
  fs []
QED

(* Structural extraction of the (first) `If` from a decl body -- walks Seq/Dec,
   skips the `While` fold body (the `_ => NONE` clause), returns the gate If.
   Pins the reasoned-about term to the verified parser output. *)
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
   Outer: Cmp Equal acc 4 -> dec := 1 ; else the inner gate.
   Inner: Cmp Equal acc 2 -> dec := 1 ; else Skip (dec stays at its 0 init). *)
Definition traversalIf_def:
  traversalIf =
    If (Cmp Equal (Var Local (strlit "acc")) (Const (4w:word64)))
       (Seq (Annot (strlit "location") (strlit "(61:4 61:10)"))
            (Assign Local (strlit "dec") (Const (1w:word64))))
       (Seq (Annot (strlit "location") (strlit "(63:7 UNKNOWN)"))
          (If (Cmp Equal (Var Local (strlit "acc")) (Const (2w:word64)))
             (Seq (Annot (strlit "location") (strlit "(64:6 64:12)"))
                  (Assign Local (strlit "dec") (Const (1w:word64))))
             (Seq (Annot (strlit "location") (strlit "(UNKNOWN UNKNOWN)")) Skip)))
End

(* Faithfulness: traversalIf IS the (first) If inside the verified parser output
   traversalProg -- kernel-checked by EVAL. *)
Theorem traversalIf_faithful:
  extract_if_decl (HD traversalProg) = SOME traversalIf
Proof
  rw [traversalBytesBridgeTheory.traversalProg_def, extract_if_decl_def,
      extract_if_def, traversalIf_def]
QED

(* Strip a leading parser Annot no-op inside a Seq (any location strings). *)
Theorem seq_annot:
  evaluate (Seq (Annot a b) c, s) = evaluate (c, s)
Proof
  simp [evaluate_def, fix_clock_def, state_component_equality]
QED

(* Unfold one `If` on a word guard, controlled (as in the cors/gzipupper lane). *)
Theorem eval_If:
  evaluate (If g t e, s) =
    case eval s g of
      SOME (ValWord w) => evaluate (if w <> 0w then t else e, s)
    | _ => (SOME Error, s)
Proof
  simp [evaluate_def]
QED

(* One bare <dec>-assign (after seq_annot strips the leading Annot). *)
Theorem eval_dec_assign:
  (?d0. FLOOKUP s.locals (strlit "dec") = SOME (ValWord d0)) ==>
  evaluate (Assign Local (strlit "dec") (Const (w:word64)), s)
    = (NONE, s with locals := s.locals |+ (strlit "dec", ValWord w))
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
        shape_of_def, set_kvar_def, set_var_def]
QED

(* The acc<>4/\acc<>2 fall-through: bare Skip does nothing.  Pulled DIRECTLY from
   panSem's evaluate_def (clause 1) rather than re-stated: a standalone `Skip` is
   overloaded across wordLang/stackLang/panLang (all in scope via the pan_to_target
   opens), and the def clause fixes it to panLang$Skip under panSem$evaluate. *)
val eval_skip = save_thm ("eval_skip", hd (CONJUNCTS panSemTheory.evaluate_def));

(* THE decision-core Link A: the emitted nested gate If computes n2w(travBlock acc)
   into <dec>, given the loaded fold output acc (in the machine word range) and
   <dec> initialised to 0 (the `var dec = 0` in main).  Straight-line -- no loop. *)
Theorem traversal_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "acc") = SOME (ValWord (n2w acc)) /\
  acc < dimword (:64) /\
  FLOOKUP s.locals (strlit "dec") = SOME (ValWord 0w) ==>
  ?s'. evaluate (traversalIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "dec") =
         SOME (ValWord (n2w (travBlock acc)))
Proof
  strip_tac >>
  `((n2w acc):word64 = 4w) = (acc = 4)`
     by (`(4w:word64) = n2w 4` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  `((n2w acc):word64 = 2w) = (acc = 2)`
     by (`(2w:word64) = n2w 2` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  Cases_on `acc = 4` >> Cases_on `acc = 2` >>
  fs [traversalIf_def, eval_If, seq_annot, eval_def, asmTheory.word_cmp_def,
      eval_dec_assign, eval_skip, travBlock_def, FLOOKUP_UPDATE]
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
    p ("=== tr_pancake_good_code ===\n" ^ tagstr tr_pancake_good_code ^ "\n");
    p ("=== tr_distinct_params ===\n" ^ tagstr tr_distinct_params ^ "\n");
    p ("=== tr_distinct_names ===\n" ^ tagstr tr_distinct_names ^ "\n");
    p ("=== tr_size_of_eids ===\n"
       ^ thm_to_string tr_size_of_eids ^ "\n" ^ tagstr tr_size_of_eids ^ "\n\n");
    p ("=== traversal_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr traversal_rung3_native ^ "\n");
    let val c = concl traversal_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== traversalIf_faithful ===\n"
       ^ thm_to_string traversalIf_faithful ^ "\n"
       ^ tagstr traversalIf_faithful ^ "\n\n");
    p ("=== traversal_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string traversal_decisioncore_refines_spec ^ "\n"
       ^ tagstr traversal_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (traversalRung3) = "
       ^ Int.toString (length (axioms "traversalRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

(* ===========================================================================
   CN Rung-3-native for the POLICY-ADMISSION serve stage (S8, admit):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the declared-surface admit gate).

     admit.pnk --native cake--> admitBytes (concrete x64, ~8ms, NO in-logic EVAL
       of the backend)  --bytes-bridge--> Link-B antecedent (native bytes in the
       real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)--> machine_sem
       refines the Pancake SOURCE semantics of the exact stage program, with the
       program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-MORE-STAGES-{,2,3,4}-REPORT.md (secheaders/redirect,
   rateadmit/gzipupper, cachefresh/cors, ipf/traversal).

   Honest scope note.  `admit.pnk` (C23) is the DECISION PROJECTION of the deployed
   S8 `policyStage` (drorb Reactor/Deploy.lean:1036; gate `policyReserved` = the REAL
   `deployDecisionOf` / `Policy.serveDecision` declared-surface admission).  The stage
   runs TWO hashBytes folds over the request method / route byte-strings (the SAME
   keyOf folds C22 cachekey uses) producing km = hashBytes method, ku = hashBytes
   route, then the gate decides the declared-surface admit for the single declared
   (method,route) surface:
     dec = 1  iff  km = KM  AND  ku = KU        (declared -> ADMIT),
     dec = 0  otherwise                          (undeclared -> 403 forbidden),
   with KM = hashBytes "GET" = 4773603 (0x48D6E3), KU = hashBytes "/api" =
   821282413 (0x30F3C66D).  This reproduces `declared (hashBytes method, hashBytes
   route)` = the positive admission of `deployDecisionOf` for the deployed declared
   surface (decision-equivalent).  This lane certifies the loop-free GATE `If` over
   the two fold outputs {km,ku}; the two hashBytes fold bodies + their Link-A
   refinements are the named S8 loop residual (the same residual class as
   C22/C23/cors/ipf).

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. admit_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted NESTED gate `If` (an outer
        `Cmp Equal km KM` whose true-arm is an inner `Cmp Equal ku KU`, with a
        `Skip` fall-through on BOTH else-arms leaving <dec> at its 0 init)
        extracted from the verified parser output computes n2w(admitDec km ku)
        into <dec>, where
          admitDec km ku = if km = 4773603 /\ ku = 821282413 then 1 else 0
        is EXACTLY policyStage's declared-surface admit as a function of the two
        fold outputs.  Straight-line -- NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The two hashBytes fold loops + their Link-A refinements -- the named S8 loop
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
open admitBytesBridgeTheory;

val _ = new_theory "admitRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem ad_pancake_good_code:
  pancake_good_code admitProg
Proof
  REWRITE_TAC [admitBytesBridgeTheory.admitProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem ad_distinct_params:
  distinct_params (functions admitProg)
Proof
  REWRITE_TAC [admitBytesBridgeTheory.admitProg_def] \\ EVAL_TAC
QED

Theorem ad_distinct_names:
  ALL_DISTINCT (MAP FST (functions admitProg))
Proof
  REWRITE_TAC [admitBytesBridgeTheory.admitProg_def] \\ EVAL_TAC
QED

Theorem ad_size_of_eids:
  size_of_eids admitProg < dimword (:64)
Proof
  REWRITE_TAC [admitBytesBridgeTheory.admitProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val admit_rung3_native =
  save_thm ("admit_rung3_native",
    admitBytesBridgeTheory.admit_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [ad_pancake_good_code, ad_distinct_params,
             ad_distinct_names, ad_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A -- the LOOP-FREE decision core (the declared-surface admit gate).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: policyStage's declared-surface admit as a
   function of the two fold outputs.  km = KM AND ku = KU = the declared
   (GET,/api) surface -> ADMIT (1); else undeclared -> 403 (0). *)
Definition admitDec_def:
  admitDec (km:num) (ku:num) =
    if km = 4773603 /\ ku = 821282413 then 1n else 0n
End

(* n2w injective on the machine word range -- for the Equal guards. *)
Theorem n2w_eq_bounded64:
  !x y. x < dimword (:64) /\ y < dimword (:64) ==>
        (((n2w x):word64 = n2w y) <=> (x = y))
Proof
  rw [n2w_11] >>
  `x MOD dimword (:64) = x /\ y MOD dimword (:64) = y` by simp [LESS_MOD] >>
  fs []
QED

(* Structural extraction of the (first) `If` from a decl body -- walks Seq/Dec,
   skips the `While` fold bodies (the `_ => NONE` clause), returns the gate If.
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
   Outer: Cmp Equal km 4773603 -> inner gate ; else Skip (dec stays at 0 init).
   Inner: Cmp Equal ku 821282413 -> dec := 1 ; else Skip (dec stays at 0 init). *)
Definition admitIf_def:
  admitIf =
    If (Cmp Equal (Var Local (strlit "km")) (Const (4773603w:word64)))
       (Seq (Annot (strlit "location") (strlit "(44:7 UNKNOWN)"))
          (If (Cmp Equal (Var Local (strlit "ku")) (Const (821282413w:word64)))
             (Seq (Annot (strlit "location") (strlit "(45:6 45:12)"))
                  (Assign Local (strlit "dec") (Const (1w:word64))))
             (Seq (Annot (strlit "location") (strlit "(UNKNOWN UNKNOWN)")) Skip)))
       (Seq (Annot (strlit "location") (strlit "(UNKNOWN UNKNOWN)")) Skip)
End

(* Faithfulness: admitIf IS the (first) If inside the verified parser output
   admitProg -- kernel-checked by EVAL. *)
Theorem admitIf_faithful:
  extract_if_decl (HD admitProg) = SOME admitIf
Proof
  rw [admitBytesBridgeTheory.admitProg_def, extract_if_decl_def,
      extract_if_def, admitIf_def]
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

(* The fall-through: bare Skip does nothing.  Pulled DIRECTLY from panSem's
   evaluate_def (clause 1) rather than re-stated: a standalone `Skip` is overloaded
   across wordLang/stackLang/panLang (all in scope via the pan_to_target opens),
   and the def clause fixes it to panLang$Skip under panSem$evaluate. *)
val eval_skip = save_thm ("eval_skip", hd (CONJUNCTS panSemTheory.evaluate_def));

(* THE decision-core Link A: the emitted NESTED gate If computes n2w(admitDec km ku)
   into <dec>, given the two loaded fold outputs km/ku (in the machine word range)
   and <dec> initialised to 0 (the `var dec = 0` in main).  Straight-line -- no loop. *)
Theorem admit_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "km") = SOME (ValWord (n2w km)) /\
  km < dimword (:64) /\
  FLOOKUP s.locals (strlit "ku") = SOME (ValWord (n2w ku)) /\
  ku < dimword (:64) /\
  FLOOKUP s.locals (strlit "dec") = SOME (ValWord 0w) ==>
  ?s'. evaluate (admitIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "dec") =
         SOME (ValWord (n2w (admitDec km ku)))
Proof
  strip_tac >>
  `((n2w km):word64 = 4773603w) = (km = 4773603)`
     by (`(4773603w:word64) = n2w 4773603` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  `((n2w ku):word64 = 821282413w) = (ku = 821282413)`
     by (`(821282413w:word64) = n2w 821282413` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  Cases_on `km = 4773603` >> Cases_on `ku = 821282413` >>
  fs [admitIf_def, eval_If, seq_annot, eval_def, asmTheory.word_cmp_def,
      eval_dec_assign, eval_skip, admitDec_def, FLOOKUP_UPDATE]
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
    p ("=== ad_pancake_good_code ===\n" ^ tagstr ad_pancake_good_code ^ "\n");
    p ("=== ad_distinct_params ===\n" ^ tagstr ad_distinct_params ^ "\n");
    p ("=== ad_distinct_names ===\n" ^ tagstr ad_distinct_names ^ "\n");
    p ("=== ad_size_of_eids ===\n"
       ^ thm_to_string ad_size_of_eids ^ "\n" ^ tagstr ad_size_of_eids ^ "\n\n");
    p ("=== admit_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr admit_rung3_native ^ "\n");
    let val c = concl admit_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== admitIf_faithful ===\n"
       ^ thm_to_string admitIf_faithful ^ "\n"
       ^ tagstr admitIf_faithful ^ "\n\n");
    p ("=== admit_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string admit_decisioncore_refines_spec ^ "\n"
       ^ tagstr admit_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (admitRung3) = "
       ^ Int.toString (length (axioms "admitRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

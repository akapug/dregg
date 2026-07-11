(* ===========================================================================
   CN Rung-3-native for the IP-FILTER serve stage (S3, ipf):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the admit/deny gate).

     ipf.pnk --native cake--> ipfBytes (concrete x64, ~12ms, NO in-logic EVAL of
       the backend)  --bytes-bridge--> Link-B antecedent (native bytes in the real
       `bytes` slot)  --Link-B (pan_to_target_compile_semantics)--> machine_sem
       refines the Pancake SOURCE semantics of the exact stage program, with the
       program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-MORE-STAGES-REPORT.md (secheaders/redirect),
   CN-MORE-STAGES-2-REPORT.md (rateadmit/gzipupper) and CN-MORE-STAGES-3-REPORT.md
   (cachefresh/cors).

   Honest scope note.  `ipf.pnk` is the DECISION PROJECTION of the deployed S3
   `IpFilter.ipfilterStage` (drorb Reactor.Stage.IpFilter / WireIpFilter.deployAdmits
   = IpFilter.permits deployRuleset, the single deny rule 10.0.0.0/8 + default-admit):
     permits ruleset addr = NOT (family = v4 /\ addr in 10.0.0.0/8)
   The stage first runs ONE prefix-matcher fold over the encoded address byte-string
   (state 0..8 = k prefix bytes matched, 9 = full match/deny-block, 10 = mismatch),
   then the gate decides
     dec = 0  iff  acc = 9   (the 10.0.0.0/8 deny prefix fully matched -> BLOCKED),
     dec = 1  otherwise      (ADMIT).
   This lane certifies the loop-free GATE `If` over the fold output {acc}; the
   prefix-matcher fold body + its Link-A refinement is the named S3 loop residual
   (the same residual class as C22/C23/rateadmit/cors).

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. ipf_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted gate `If` (a `Cmp Equal acc 9`,
        both arms assigning) extracted from the verified parser output computes
        n2w(ipfAdmit acc) into <dec>, where
          ipfAdmit acc = if acc = 9 then 0 else 1
        is EXACTLY WireIpFilter.deployAdmits as a function of the fold output (the
        deny-precedence single-rule access decision: admit unless the deny prefix
        matched).  Straight-line -- NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The prefix-matcher fold loop + its Link-A refinement -- the named S3 loop
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
open ipfBytesBridgeTheory;

val _ = new_theory "ipfRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem ip_pancake_good_code:
  pancake_good_code ipfProg
Proof
  REWRITE_TAC [ipfBytesBridgeTheory.ipfProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem ip_distinct_params:
  distinct_params (functions ipfProg)
Proof
  REWRITE_TAC [ipfBytesBridgeTheory.ipfProg_def] \\ EVAL_TAC
QED

Theorem ip_distinct_names:
  ALL_DISTINCT (MAP FST (functions ipfProg))
Proof
  REWRITE_TAC [ipfBytesBridgeTheory.ipfProg_def] \\ EVAL_TAC
QED

Theorem ip_size_of_eids:
  size_of_eids ipfProg < dimword (:64)
Proof
  REWRITE_TAC [ipfBytesBridgeTheory.ipfProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val ipf_rung3_native =
  save_thm ("ipf_rung3_native",
    ipfBytesBridgeTheory.ipf_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [ip_pancake_good_code, ip_distinct_params,
             ip_distinct_names, ip_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A -- the LOOP-FREE decision core (the admit/deny gate).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: WireIpFilter.deployAdmits as a function of
   the fold output.  acc = 9 = the 10.0.0.0/8 deny prefix fully matched -> BLOCKED
   (admit bit 0); else ADMIT (1). *)
Definition ipfAdmit_def:
  ipfAdmit (acc:num) = if acc = 9 then 0n else 1n
End

(* n2w injective on the machine word range -- for the Equal guard (Equal acc 9).
   Copied from the cors/redirect lane. *)
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
   guard: Cmp Equal acc 9 -> then dec := 0 (blocked) ; else dec := 1 (admit). *)
Definition ipfIf_def:
  ipfIf =
    If (Cmp Equal (Var Local (strlit "acc")) (Const (9w:word64)))
       (Seq (Annot (strlit "location") (strlit "(81:4 81:10)"))
            (Assign Local (strlit "dec") (Const (0w:word64))))
       (Seq (Annot (strlit "location") (strlit "(83:4 83:10)"))
            (Assign Local (strlit "dec") (Const (1w:word64))))
End

(* Faithfulness: ipfIf IS the (first) If inside the verified parser output
   ipfProg -- kernel-checked by EVAL. *)
Theorem ipfIf_faithful:
  extract_if_decl (HD ipfProg) = SOME ipfIf
Proof
  rw [ipfBytesBridgeTheory.ipfProg_def, extract_if_decl_def,
      extract_if_def, ipfIf_def]
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

(* THE decision-core Link A: the emitted gate If computes n2w(ipfAdmit acc) into
   <dec>, given the loaded fold output acc (in the machine word range) and <dec>
   already word-typed (the `var dec = 0` in main).  Straight-line -- no loop. *)
Theorem ipf_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "acc") = SOME (ValWord (n2w acc)) /\
  acc < dimword (:64) /\
  (?d0. FLOOKUP s.locals (strlit "dec") = SOME (ValWord d0)) ==>
  ?s'. evaluate (ipfIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "dec") =
         SOME (ValWord (n2w (ipfAdmit acc)))
Proof
  strip_tac >>
  `((n2w acc):word64 = 9w) = (acc = 9)`
     by (`(9w:word64) = n2w 9` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  Cases_on `acc = 9` >>
  fs [ipfIf_def, eval_If, seq_annot, eval_def, asmTheory.word_cmp_def,
      eval_dec_assign, ipfAdmit_def, FLOOKUP_UPDATE]
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
    p ("=== ip_pancake_good_code ===\n" ^ tagstr ip_pancake_good_code ^ "\n");
    p ("=== ip_distinct_params ===\n" ^ tagstr ip_distinct_params ^ "\n");
    p ("=== ip_distinct_names ===\n" ^ tagstr ip_distinct_names ^ "\n");
    p ("=== ip_size_of_eids ===\n"
       ^ thm_to_string ip_size_of_eids ^ "\n" ^ tagstr ip_size_of_eids ^ "\n\n");
    p ("=== ipf_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr ipf_rung3_native ^ "\n");
    let val c = concl ipf_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== ipfIf_faithful ===\n"
       ^ thm_to_string ipfIf_faithful ^ "\n"
       ^ tagstr ipfIf_faithful ^ "\n\n");
    p ("=== ipf_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string ipf_decisioncore_refines_spec ^ "\n"
       ^ tagstr ipf_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (ipfRung3) = "
       ^ Int.toString (length (axioms "ipfRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

(* ===========================================================================
   CN Rung-3-native for the CORS ACAO serve stage (S10, cors):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the origin-allowed gate).

     cors.pnk --native cake--> corsBytes (concrete x64, ~7ms, NO in-logic EVAL of
       the backend)  --bytes-bridge--> Link-B antecedent (native bytes in the real
       `bytes` slot)  --Link-B (pan_to_target_compile_semantics)--> machine_sem
       refines the Pancake SOURCE semantics of the exact stage program, with the
       program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-MORE-STAGES-REPORT.md (secheaders/redirect) and
   CN-MORE-STAGES-2-REPORT.md (rateadmit/gzipupper).

   Honest scope note.  `cors.pnk` is the DECISION PROJECTION of the deployed S10
   `deployCorsStage` (drorb Reactor.Stage.Cors / Cors.acaoValue over corsPolicy):
     originAllowed p o = p.allowAnyOrigin || p.allowedOrigins.contains o
     acaoValue     p o = if originAllowed p o then some o else none.
   The stage first runs TWO hashBytes folds — hash(request origin) = km,
   hash(policy allowed origin) = ku — then the gate decides
     dec = 1  iff  (wild != 0) || (km == ku)   = originAllowed
   (wild = the allowAnyOrigin flag; km == ku models allowedOrigins.contains o via
   hashBytes equality for the single-allowed-origin deploy — the C25 hash-equality
   modelling caveat).  This lane certifies the loop-free GATE `If` over the fold
   outputs {wild, km, ku}; the two hashBytes fold bodies + their Link-A refinements
   are the named S10 loop residual (the same residual class as C22/C23/rateadmit).

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. cors_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted nested gate `If` (an outer
        `Cmp NotEqual wild 0` and an inner `Cmp Equal km ku`, with the km!=ku
        fall-through leaving <dec> at its initial 0) extracted from the verified
        parser output computes n2w(corsAllow wild km ku) into <dec>, where
          corsAllow wild km ku = if wild <> 0 \/ km = ku then 1 else 0
        is EXACTLY originAllowed as a function of the loaded gate words.
        Straight-line — NO loop induction.  NotEqual is a NEW guard form beyond the
        earlier cores' Less / Equal / NotLess.

   What is NOT closed (named, per the honesty rule):
     - The two hashBytes fold loops (km/ku) + their Link-A refinements — the named
       S10 loop residual, unchanged.
     - The whole-main FFI frame (@load_vec establishes the arenas; @report_vec emits
       <dec>) — the SAME FFI boundary boundscan names.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open corsBytesBridgeTheory;

val _ = new_theory "corsRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem co_pancake_good_code:
  pancake_good_code corsProg
Proof
  REWRITE_TAC [corsBytesBridgeTheory.corsProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem co_distinct_params:
  distinct_params (functions corsProg)
Proof
  REWRITE_TAC [corsBytesBridgeTheory.corsProg_def] \\ EVAL_TAC
QED

Theorem co_distinct_names:
  ALL_DISTINCT (MAP FST (functions corsProg))
Proof
  REWRITE_TAC [corsBytesBridgeTheory.corsProg_def] \\ EVAL_TAC
QED

Theorem co_size_of_eids:
  size_of_eids corsProg < dimword (:64)
Proof
  REWRITE_TAC [corsBytesBridgeTheory.corsProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val cors_rung3_native =
  save_thm ("cors_rung3_native",
    corsBytesBridgeTheory.cors_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [co_pancake_good_code, co_distinct_params,
             co_distinct_names, co_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A — the LOOP-FREE decision core (the origin-allowed gate).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: originAllowed as a function of the gate
   words.  wild <> 0 = allowAnyOrigin ; km = ku = allowedOrigins.contains o (via
   hashBytes equality); allowed = 1, denied = 0. *)
Definition corsAllow_def:
  corsAllow (wild:num) (km:num) (ku:num) =
    if wild <> 0 \/ km = ku then 1n else 0n
End

(* n2w injective on the machine word range — for the two equality guards
   (NotEqual wild 0 ; Equal km ku).  Copied from the redirect lane. *)
Theorem n2w_eq_bounded64:
  !x y. x < dimword (:64) /\ y < dimword (:64) ==>
        (((n2w x):word64 = n2w y) <=> (x = y))
Proof
  rw [n2w_11] >>
  `x MOD dimword (:64) = x /\ y MOD dimword (:64) = y` by simp [LESS_MOD] >>
  fs []
QED

(* Structural extraction of the (first) `If` from a decl body — walks Seq/Dec,
   skips the two `While` fold bodies (the `_ => NONE` clause), returns the gate
   If.  Pins the reasoned-about term to the verified parser output. *)
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
   Outer: Cmp NotEqual wild 0  -> dec := 1 ; else the inner gate.
   Inner: Cmp Equal km ku      -> dec := 1 ; else Skip (dec stays at its 0 init). *)
Definition corsIf_def:
  corsIf =
    If (Cmp NotEqual (Var Local (strlit "wild")) (Const (0w:word64)))
       (Seq (Annot (strlit "location") (strlit "(44:4 44:10)"))
            (Assign Local (strlit "dec") (Const (1w:word64))))
       (Seq (Annot (strlit "location") (strlit "(46:7 UNKNOWN)"))
          (If (Cmp Equal (Var Local (strlit "km")) (Var Local (strlit "ku")))
             (Seq (Annot (strlit "location") (strlit "(47:6 47:12)"))
                  (Assign Local (strlit "dec") (Const (1w:word64))))
             (Seq (Annot (strlit "location") (strlit "(UNKNOWN UNKNOWN)")) Skip)))
End

(* Faithfulness: corsIf IS the (first) If inside the verified parser output
   corsProg — kernel-checked by EVAL. *)
Theorem corsIf_faithful:
  extract_if_decl (HD corsProg) = SOME corsIf
Proof
  rw [corsBytesBridgeTheory.corsProg_def, extract_if_decl_def,
      extract_if_def, corsIf_def]
QED

(* Strip a leading parser Annot no-op inside a Seq (any location strings). *)
Theorem seq_annot:
  evaluate (Seq (Annot a b) c, s) = evaluate (c, s)
Proof
  simp [evaluate_def, fix_clock_def, state_component_equality]
QED

(* Unfold one `If` on a word guard, controlled (as in the gzipupper lane). *)
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
  (?r0. FLOOKUP s.locals (strlit "dec") = SOME (ValWord r0)) ==>
  evaluate (Assign Local (strlit "dec") (Const (w:word64)), s)
    = (NONE, s with locals := s.locals |+ (strlit "dec", ValWord w))
Proof
  strip_tac >>
  simp [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
        shape_of_def, set_kvar_def, set_var_def]
QED

(* The km!=ku fall-through: bare Skip does nothing.  Pulled DIRECTLY from panSem's
   evaluate_def (clause 1) rather than re-stated: a standalone `Skip` is overloaded
   across wordLang/stackLang/panLang (all in scope via the pan_to_target opens), and
   the def clause fixes it to panLang$Skip under panSem$evaluate unambiguously. *)
val eval_skip = save_thm ("eval_skip", hd (CONJUNCTS panSemTheory.evaluate_def));

(* THE decision-core Link A: the emitted nested gate If computes
   n2w(corsAllow wild km ku) into <dec>, given the loaded gate words and <dec>
   initialised to 0 (the `var dec = 0` in main).  Straight-line — no loop. *)
Theorem cors_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "wild") = SOME (ValWord (n2w wild)) /\
  FLOOKUP s.locals (strlit "km")   = SOME (ValWord (n2w km)) /\
  FLOOKUP s.locals (strlit "ku")   = SOME (ValWord (n2w ku)) /\
  wild < dimword (:64) /\ km < dimword (:64) /\ ku < dimword (:64) /\
  FLOOKUP s.locals (strlit "dec")  = SOME (ValWord 0w) ==>
  ?s'. evaluate (corsIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "dec") =
         SOME (ValWord (n2w (corsAllow wild km ku)))
Proof
  strip_tac >>
  `((n2w wild):word64 = 0w) = (wild = 0)`
     by (`(0w:word64) = n2w 0` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  `((n2w km):word64 = n2w ku) = (km = ku)`
     by (irule n2w_eq_bounded64 >> fs []) >>
  Cases_on `wild = 0` >> Cases_on `km = ku` >>
  fs [corsIf_def, eval_If, seq_annot, eval_def, asmTheory.word_cmp_def,
      eval_dec_assign, eval_skip, corsAllow_def, FLOOKUP_UPDATE]
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
    p ("=== co_pancake_good_code ===\n" ^ tagstr co_pancake_good_code ^ "\n");
    p ("=== co_distinct_params ===\n" ^ tagstr co_distinct_params ^ "\n");
    p ("=== co_distinct_names ===\n" ^ tagstr co_distinct_names ^ "\n");
    p ("=== co_size_of_eids ===\n"
       ^ thm_to_string co_size_of_eids ^ "\n" ^ tagstr co_size_of_eids ^ "\n\n");
    p ("=== cors_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr cors_rung3_native ^ "\n");
    let val c = concl cors_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== corsIf_faithful ===\n"
       ^ thm_to_string corsIf_faithful ^ "\n"
       ^ tagstr corsIf_faithful ^ "\n\n");
    p ("=== cors_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string cors_decisioncore_refines_spec ^ "\n"
       ^ tagstr cors_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (corsRung3) = "
       ^ Int.toString (length (axioms "corsRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

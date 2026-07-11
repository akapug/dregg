(* ===========================================================================
   CN Rung-3-native for the JWT-ADMIN serve stage (S1, jwt):
   COMPOSE native-compile + bytes-bridge + Link B into the backbone, and close
   Link A for the LOOP-FREE decision core (the HS256 sig-verify + alg-confusion gate).

     jwt.pnk --native cake--> jwtBytes (concrete x64, ~8ms, NO in-logic EVAL of
       the backend)  --bytes-bridge--> Link-B antecedent (native bytes in the real
       `bytes` slot)  --Link-B (pan_to_target_compile_semantics)--> machine_sem
       refines the Pancake SOURCE semantics of the exact stage program, with the
       program-level applicability conditions DISCHARGED here.

   Ground: identical to CN-MORE-STAGES-{,2,3,4}-REPORT.md (secheaders/redirect,
   rateadmit/gzipupper, cachefresh/cors, ipf/traversal).

   Honest scope note.  `jwt.pnk` (C31) is the DECISION PROJECTION of the deployed
   S1 `jwtAdminStage` (drorb Reactor/Deploy.lean:1388; runs the REAL
   `Reactor.Stage.Jwt.jwtStage` / `Jwt.authenticate` HS256 verify on /admin* targets).
   The compiled gate takes the HMAC-SHA256 DIGEST as INPUT (the digest is the CRYPTO
   TRUST BOUNDARY, an FFI like the TLS crypto -- NOT compiled here) and reproduces
   `authenticate`'s admit decision:
     admit  iff  verifyHmac(key, header.payload) = signature   (sig-equality)
              AND  alg = HS256                                   (alg-confusion gate).
   Two hashBytes folds hash the digest arena (km) and the signature arena (ku); the
   scalar @+16 carries the token's declared alg tag (1 = HS256).  The gate decides:
     dec = 1  iff  km = ku  AND  alg = 1        (verified HS256 -> ADMIT),
     dec = 0  otherwise                          (401 unauthorized).
   This lane certifies the loop-free GATE `If` over {km,ku,alg}; the two hashBytes
   fold bodies (+ their Link-A refinements) and the upstream base64url-decode / JSON
   claim parse are the named S1 loop residuals (the same residual class as
   C22/C23/C27/cors/ipf).  The HMAC digest itself is the named crypto FFI boundary.

   THIS theory's kernel-checked additions:
     1. The FOUR program-level Link-B applicability conditions, EVAL-discharged.
     2. jwt_rung3_native : Link B with the native bytes + the four program
        conditions discharged; DISK_THM only (native-bytes eq kept as antecedent).
     3. Link A, LOOP-FREE decision core: the emitted NESTED gate `If` (an outer
        VARIABLE-vs-VARIABLE `Cmp Equal km ku` whose true-arm is an inner
        `Cmp Equal alg 1`, with a `Skip` fall-through on BOTH else-arms leaving
        <dec> at its 0 init) extracted from the verified parser output computes
        n2w(jwtDec km ku alg) into <dec>, where
          jwtDec km ku alg = if km = ku /\ alg = 1 then 1 else 0
        is EXACTLY jwtAdminStage's sig-equality + HS256 admit as a function of the
        fold outputs + alg tag.  Straight-line -- NO loop induction.

   What is NOT closed (named, per the honesty rule):
     - The two hashBytes fold loops + the base64url/JSON parse loops + their Link-A
       refinements -- the named S1 loop residuals, unchanged.
     - The HMAC-SHA256 digest -- the crypto FFI trust boundary (input to the gate).
     - The whole-main FFI frame (@load_vec establishes the arena; @report_vec emits
       <dec>) -- the SAME FFI boundary boundscan names.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) -- kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open jwtBytesBridgeTheory;

val _ = new_theory "jwtRung3";

(* ---------------------------------------------------------------------------
   1. The FOUR program-level applicability conditions, EVAL-discharged.
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem jw_pancake_good_code:
  pancake_good_code jwtProg
Proof
  REWRITE_TAC [jwtBytesBridgeTheory.jwtProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem jw_distinct_params:
  distinct_params (functions jwtProg)
Proof
  REWRITE_TAC [jwtBytesBridgeTheory.jwtProg_def] \\ EVAL_TAC
QED

Theorem jw_distinct_names:
  ALL_DISTINCT (MAP FST (functions jwtProg))
Proof
  REWRITE_TAC [jwtBytesBridgeTheory.jwtProg_def] \\ EVAL_TAC
QED

Theorem jw_size_of_eids:
  size_of_eids jwtProg < dimword (:64)
Proof
  REWRITE_TAC [jwtBytesBridgeTheory.jwtProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   2. Rung-3 native backbone.
   --------------------------------------------------------------------------- *)
val jwt_rung3_native =
  save_thm ("jwt_rung3_native",
    jwtBytesBridgeTheory.jwt_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [jw_pancake_good_code, jw_distinct_params,
             jw_distinct_names, jw_size_of_eids]));

(* ---------------------------------------------------------------------------
   3. Link A -- the LOOP-FREE decision core (the HS256 verify + alg-confusion gate).
   --------------------------------------------------------------------------- *)

(* The Lean SPEC, re-declared in HOL: jwtAdminStage's admit as a function of the
   fold outputs + alg tag.  km = ku (verifyHmac's sig-equality) AND alg = 1 (HS256)
   -> ADMIT (1); else 401 (0). *)
Definition jwtDec_def:
  jwtDec (km:num) (ku:num) (alg:num) =
    if km = ku /\ alg = 1 then 1n else 0n
End

(* n2w injective on the machine word range -- for the Equal guards (both the
   variable-vs-variable km = ku and the variable-vs-constant alg = 1). *)
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
   Outer: Cmp Equal km ku (VARIABLE-vs-VARIABLE) -> inner gate ; else Skip (0 init).
   Inner: Cmp Equal alg 1 -> dec := 1 ; else Skip (dec stays at its 0 init). *)
Definition jwtIf_def:
  jwtIf =
    If (Cmp Equal (Var Local (strlit "km")) (Var Local (strlit "ku")))
       (Seq (Annot (strlit "location") (strlit "(44:7 UNKNOWN)"))
          (If (Cmp Equal (Var Local (strlit "alg")) (Const (1w:word64)))
             (Seq (Annot (strlit "location") (strlit "(45:6 45:12)"))
                  (Assign Local (strlit "dec") (Const (1w:word64))))
             (Seq (Annot (strlit "location") (strlit "(UNKNOWN UNKNOWN)")) Skip)))
       (Seq (Annot (strlit "location") (strlit "(UNKNOWN UNKNOWN)")) Skip)
End

(* Faithfulness: jwtIf IS the (first) If inside the verified parser output
   jwtProg -- kernel-checked by EVAL. *)
Theorem jwtIf_faithful:
  extract_if_decl (HD jwtProg) = SOME jwtIf
Proof
  rw [jwtBytesBridgeTheory.jwtProg_def, extract_if_decl_def,
      extract_if_def, jwtIf_def]
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

(* THE decision-core Link A: the emitted NESTED gate If computes n2w(jwtDec km ku alg)
   into <dec>, given the two loaded fold outputs km/ku + the alg tag (in the machine
   word range) and <dec> initialised to 0 (the `var dec = 0` in main).  Straight-line
   -- no loop. *)
Theorem jwt_decisioncore_refines_spec:
  FLOOKUP s.locals (strlit "km") = SOME (ValWord (n2w km)) /\
  km < dimword (:64) /\
  FLOOKUP s.locals (strlit "ku") = SOME (ValWord (n2w ku)) /\
  ku < dimword (:64) /\
  FLOOKUP s.locals (strlit "alg") = SOME (ValWord (n2w alg)) /\
  alg < dimword (:64) /\
  FLOOKUP s.locals (strlit "dec") = SOME (ValWord 0w) ==>
  ?s'. evaluate (jwtIf, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "dec") =
         SOME (ValWord (n2w (jwtDec km ku alg)))
Proof
  strip_tac >>
  `((n2w km):word64 = n2w ku) = (km = ku)`
     by (irule n2w_eq_bounded64 >> fs []) >>
  `((n2w alg):word64 = 1w) = (alg = 1)`
     by (`(1w:word64) = n2w 1` by EVAL_TAC >> pop_assum SUBST1_TAC >>
         irule n2w_eq_bounded64 >> fs [] >> EVAL_TAC) >>
  Cases_on `km = ku` >> Cases_on `alg = 1` >>
  fs [jwtIf_def, eval_If, seq_annot, eval_def, asmTheory.word_cmp_def,
      eval_dec_assign, eval_skip, jwtDec_def, FLOOKUP_UPDATE]
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
    p ("=== jw_pancake_good_code ===\n" ^ tagstr jw_pancake_good_code ^ "\n");
    p ("=== jw_distinct_params ===\n" ^ tagstr jw_distinct_params ^ "\n");
    p ("=== jw_distinct_names ===\n" ^ tagstr jw_distinct_names ^ "\n");
    p ("=== jw_size_of_eids ===\n"
       ^ thm_to_string jw_size_of_eids ^ "\n" ^ tagstr jw_size_of_eids ^ "\n\n");
    p ("=== jwt_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr jwt_rung3_native ^ "\n");
    let val c = concl jwt_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n")
    end;
    p ("=== jwtIf_faithful ===\n"
       ^ thm_to_string jwtIf_faithful ^ "\n"
       ^ tagstr jwtIf_faithful ^ "\n\n");
    p ("=== jwt_decisioncore_refines_spec (Link A, loop-free) ===\n"
       ^ thm_to_string jwt_decisioncore_refines_spec ^ "\n"
       ^ tagstr jwt_decisioncore_refines_spec ^ "\n\n");
    p ("theory axioms (jwtRung3) = "
       ^ Int.toString (length (axioms "jwtRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

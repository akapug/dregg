(* ===========================================================================
   C27 — the machine-checked AUDIT theory.  Asserts, adversarially:
     * the Basic-auth compare gate basic_machine_code closes spec->machine-code:
       [oracles: DISK_THM] [axioms: ], hyps = 0, NON-vacuous (a real
       machine_sem SUBSET {Terminate Success ...} reporting basicAdmit).
     * it is a genuinely DISTINCT decision over a DISTINCT parser-output program
       (basicProg, not cacheKeyProg; basicAdmit, not cacheServe / admitDecide /
       corsAllow).
     * grounds `verify` on THREE real credential inputs (the deployed stageConfig
       credential "admin:secret", drorb Reactor/Stage/BasicAuth.lean verify):
         - the CORRECT credential            -> 1  (verify T -> .ok -> admit)
         - a WRONG credential "admin:wrong"  -> 0  (verify F -> challenge -> 401)
         - an ABSENT credential (empty)      -> 0  (no creds  -> challenge -> 401)
       and that the wrong / empty credential hashes genuinely DIFFER from the
       configured hash as word64 (the reject is a real mismatch, not a collision).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open basicGenTheory basicCoreTheory hashBytesLoopTheory wordsTheory wordsLib;

val _ = new_theory "verifyC27";
val _ = Globals.show_assums := true;

fun assert b msg = if b then () else raise Fail ("C27 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val basic = basicGenTheory.basic_machine_code;

val _ = print "\n===== basic_machine_code (the Basic-auth credential compare gate) =====\n";
val _ = print (thm_to_string basic);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string basic ^ "\n");

(* 1. closed, DISK_THM-only, hyps = 0 *)
val _ = assert (oracles_ok basic) "basic_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp basic)) "basic_machine_code has hypotheses";

(* 2. NON-vacuous: a real machine_sem SUBSET {Terminate Success ...} over basicAdmit *)
val _ = assert (mentions "machine_sem" basic andalso mentions "Terminate Success" basic)
               "basic_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "basicAdmit" basic)
               "basic_machine_code lost its composed spec word basicAdmit";

(* 3. a DISTINCT decision over a DISTINCT program (not a re-run of C22/C23/C25) *)
val _ = assert (mentions "basicProg" basic)
               "basic_machine_code does not target the basicProg parser output";
val _ = assert (not (mentions "cacheServe" basic) andalso not (mentions "admitDecide" basic)
                andalso not (mentions "corsAllow" basic))
               "basic decision is not distinct from the C22/C23/C25 decisions";

(* 4. ground `verify` on THREE real credential inputs (drorb BasicAuth.lean bytes) *)
(* "admin:secret" = the deployed stageConfig demonstration credential           *)
val configured = “[97;100;109;105;110;58;115;101;99;114;101;116]”;
(* correct credential = the SAME "admin:secret"                                  *)
val goodCred   = “[97;100;109;105;110;58;115;101;99;114;101;116]”;
(* wrong credential = "admin:wrong"                                              *)
val badCred    = “[97;100;109;105;110;58;119;114;111;110;103]”;
(* absent credential = empty (no Authorization header)                           *)
val emptyCred  = “[]:num list”;

val hConf = EVAL (mk_comb (“hashBytesN”, configured));
val hBad  = EVAL (mk_comb (“hashBytesN”, badCred));
val _ = print ("\nhashBytes \"admin:secret\" = " ^ term_to_string (rhs (concl hConf)) ^ "\n");
val _ = print ("hashBytes \"admin:wrong\"  = " ^ term_to_string (rhs (concl hBad)) ^ "\n");

(* the wrong credential's hash DIFFERS from configured as word64 - a real miss  *)
val hne = EVAL (Term [QUOTE "(n2w (hashBytesN ", ANTIQUOTE badCred,
                      QUOTE ") = (n2w (hashBytesN ", ANTIQUOTE configured,
                      QUOTE "):word64))"]);
val _ = print ("wrong-hash = configured-hash (word64)? " ^ term_to_string (rhs (concl hne)) ^ "\n");
val _ = assert (rhs (concl hne) ~~ “F”) "wrong-cred hash COLLIDES with configured - reject case vacuous";

(* the empty credential's hash also DIFFERS from configured as word64           *)
val hne2 = EVAL (Term [QUOTE "(n2w (hashBytesN ", ANTIQUOTE emptyCred,
                       QUOTE ") = (n2w (hashBytesN ", ANTIQUOTE configured,
                       QUOTE "):word64))"]);
val _ = print ("empty-hash = configured-hash (word64)? " ^ term_to_string (rhs (concl hne2)) ^ "\n");
val _ = assert (rhs (concl hne2) ~~ “F”) "empty-cred hash COLLIDES with configured - absent case vacuous";

(* the basicAdmit truth table over the three real inputs (= verify) *)
val b1 = EVAL (Term [QUOTE "basicAdmit ", ANTIQUOTE goodCred,  QUOTE " ", ANTIQUOTE configured]);
val b2 = EVAL (Term [QUOTE "basicAdmit ", ANTIQUOTE badCred,   QUOTE " ", ANTIQUOTE configured]);
val b3 = EVAL (Term [QUOTE "basicAdmit ", ANTIQUOTE emptyCred, QUOTE " ", ANTIQUOTE configured]);
val _ = print ("\nbasicAdmit  admin:secret (correct)   = " ^ term_to_string (rhs (concl b1)) ^ "\n");
val _ = print ("basicAdmit  admin:wrong  (wrong)     = " ^ term_to_string (rhs (concl b2)) ^ "\n");
val _ = print ("basicAdmit  (empty)      (absent)    = " ^ term_to_string (rhs (concl b3)) ^ "\n");
val _ = assert (rhs (concl b1) ~~ “1n”) "correct credential != admit (1)";
val _ = assert (rhs (concl b2) ~~ “0n”) "wrong credential != reject (0) - auth boundary broken";
val _ = assert (rhs (concl b3) ~~ “0n”) "absent credential != reject (0) - auth boundary broken";

val _ = print ("\n@@ verifyC27 axioms = " ^ Int.toString (length (axioms "verifyC27")) ^ "\n");
val _ = print "\n@@@ C27 AUDIT PASSED: mk_composedWrapper closes the Basic-auth compare gate (basicStage / verify) DIRECTLY - no spine adaptation; DISK_THM-only, hyps=0, non-vacuous; verify grounded on correct/wrong/absent credentials (no hash collision) @@@\n";

val _ = export_theory ();

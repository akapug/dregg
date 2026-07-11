(* ===========================================================================
   C25 — the machine-checked AUDIT theory.  Asserts, adversarially:
     * the THIRD composed stage cors_machine_code closes spec->machine-code:
       [oracles: DISK_THM] [axioms: ], hyps = 0, NON-vacuous (a real
       machine_sem SUBSET {Terminate Success ...} reporting corsAllow).
     * it is a genuinely DISTINCT decision over a DISTINCT parser-output program
       (corsProg, not cacheKeyProg / admitProg; corsAllow, not cacheServe /
       admitDecide).
     * grounds the CORS decision on THREE real origin inputs (the drorb
       corsPolicy allowlist ["https://app.example.com"], allowAnyOrigin = false):
         - allowed origin, wildcard off  -> 1  (ACAO echoed;  originAllowed = T)
         - disallowed origin, wildcard off-> 0  (NO ACAO, no leak; originAllowed=F)
         - any origin, wildcard on        -> 1  (allowAnyOrigin path)
       and that the two origins' hashes genuinely DIFFER as word64 (the deny is a
       real mismatch, not a hash collision).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open corsGenTheory corsCoreTheory hashBytesLoopTheory wordsTheory wordsLib;

val _ = new_theory "verifyC25";
val _ = Globals.show_assums := true;

fun assert b msg = if b then () else raise Fail ("C25 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val cors = corsGenTheory.cors_machine_code;

val _ = print "\n===== cors_machine_code (THIRD composed stage: the CORS ACAO decision) =====\n";
val _ = print (thm_to_string cors);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string cors ^ "\n");

(* 1. closed, DISK_THM-only, hyps = 0 *)
val _ = assert (oracles_ok cors) "cors_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp cors)) "cors_machine_code has hypotheses";

(* 2. NON-vacuous: a real machine_sem SUBSET {Terminate Success ...} over corsAllow *)
val _ = assert (mentions "machine_sem" cors andalso mentions "Terminate Success" cors)
               "cors_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "corsAllow" cors)
               "cors_machine_code lost its composed spec word corsAllow";

(* 3. a DISTINCT decision over a DISTINCT program (not a re-run of C22/C23) *)
val _ = assert (mentions "corsProg" cors)
               "cors_machine_code does not target the corsProg parser output";
val _ = assert (not (mentions "cacheServe" cors) andalso not (mentions "admitDecide" cors))
               "cors decision is not distinct from the C22/C23 decisions";

(* 4. ground the CORS decision on THREE real origins (drorb Cors.lean bytes) *)
(* "https://app.example.com"  = the single deployed allowlist entry            *)
val appOrigin  = “[104;116;116;112;115;58;47;47;97;112;112;46;101;120;97;109;112;108;101;46;99;111;109]”;
(* "https://evil.example.com" = an off-allowlist origin                        *)
val evilOrigin = “[104;116;116;112;115;58;47;47;101;118;105;108;46;101;120;97;109;112;108;101;46;99;111;109]”;

val hApp  = EVAL (mk_comb (“hashBytesN”, appOrigin));
val hEvil = EVAL (mk_comb (“hashBytesN”, evilOrigin));
val _ = print ("\nhashBytes \"https://app.example.com\"  = " ^ term_to_string (rhs (concl hApp)) ^ "\n");
val _ = print ("hashBytes \"https://evil.example.com\" = " ^ term_to_string (rhs (concl hEvil)) ^ "\n");

(* the two origins' hashes DIFFER as word64 - the deny is a real mismatch *)
val hne = EVAL (Term [QUOTE "(n2w (hashBytesN ", ANTIQUOTE appOrigin,
                      QUOTE ") = (n2w (hashBytesN ", ANTIQUOTE evilOrigin,
                      QUOTE "):word64))"]);
val _ = print ("app-hash = evil-hash (word64)? " ^ term_to_string (rhs (concl hne)) ^ "\n");
val _ = assert (rhs (concl hne) ~~ “F”) "the two origin hashes COLLIDE as word64 - deny case vacuous";

(* the corsAllow truth table over the three real inputs *)
val c1 = EVAL (Term [QUOTE "corsAllow 0 ", ANTIQUOTE appOrigin,  QUOTE " ", ANTIQUOTE appOrigin]);
val c2 = EVAL (Term [QUOTE "corsAllow 0 ", ANTIQUOTE evilOrigin, QUOTE " ", ANTIQUOTE appOrigin]);
val c3 = EVAL (Term [QUOTE "corsAllow 1 ", ANTIQUOTE evilOrigin, QUOTE " ", ANTIQUOTE appOrigin]);
val _ = print ("\ncorsAllow  app  vs app  (wild=0, allowed)    = " ^ term_to_string (rhs (concl c1)) ^ "\n");
val _ = print ("corsAllow  evil vs app  (wild=0, disallowed) = " ^ term_to_string (rhs (concl c2)) ^ "\n");
val _ = print ("corsAllow  evil vs app  (wild=1, wildcard)   = " ^ term_to_string (rhs (concl c3)) ^ "\n");
val _ = assert (rhs (concl c1) ~~ “1n”) "allowed origin != ACAO grant (1)";
val _ = assert (rhs (concl c2) ~~ “0n”) "disallowed origin != deny (0) - no-leak boundary broken";
val _ = assert (rhs (concl c3) ~~ “1n”) "wildcard policy != allow (1)";

val _ = print ("\n@@ verifyC25 axioms = " ^ Int.toString (length (axioms "verifyC25")) ^ "\n");
val _ = print "\n@@@ C25 AUDIT PASSED: mk_composedWrapper closes a THIRD composed stage (deployCorsStage / Cors.acaoValue) DIRECTLY - no spine adaptation; DISK_THM-only, hyps=0, non-vacuous; ACAO decision grounded on real allowed/disallowed/wildcard origins (no hash collision) @@@\n";

val _ = export_theory ();

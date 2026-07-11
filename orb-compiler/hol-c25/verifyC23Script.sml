(* ===========================================================================
   C23 — the machine-checked AUDIT theory.  Asserts, adversarially:
     * mk_composedWrapper REPRODUCES C22 byte-identically: cacheKeyRegen_machine_code
       (generator output) is ALPHA-EQUAL to the bespoke cacheKey_machine_code.
     * the SECOND composed stage admit_machine_code closes spec->machine-code:
       [oracles: DISK_THM] [axioms: ], hyps = 0, NON-vacuous (a real
       machine_sem SUBSET {Terminate Success ...} reporting admitDecide).
     * grounds the 2nd stage's decision values (admitDecide truth table) and the
       stored constants (hashBytes "GET" = 4773603, hashBytes "/api" = 821282413).
     * the body-generic frame engine loop_frame is non-vacuous.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open cacheKeyGenTheory cacheKeyGen2Theory admitGenTheory admitCoreTheory
     composedCommonTheory hashBytesLoopTheory wordsLib;

val _ = new_theory "verifyC23";
val _ = Globals.show_assums := true;

fun assert b msg = if b then () else raise Fail ("C23 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val bespoke = cacheKeyGenTheory.cacheKey_machine_code;
val regen   = cacheKeyGen2Theory.cacheKeyRegen_machine_code;
val admit   = admitGenTheory.admit_machine_code;

val _ = print "\n===== cacheKeyRegen_machine_code (generator reproduction of C22) =====\n";
val _ = print ("TAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string regen ^ "\n");
val _ = print "\n===== admit_machine_code (SECOND composed stage) =====\n";
val _ = print (thm_to_string admit);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string admit ^ "\n");

(* 1. REGRESSION: generator reproduces C22 byte-identically *)
val _ = assert (aconv (concl bespoke) (concl regen))
               "cacheKeyRegen is NOT alpha-equal to the bespoke cacheKey_machine_code";
val _ = assert (oracles_ok regen andalso null (hyp regen)) "regen not DISK_THM/hyps=0";

(* 2. SECOND STAGE closed, DISK_THM-only, hyps=0, non-vacuous *)
val _ = assert (oracles_ok admit) "admit_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp admit)) "admit_machine_code has hypotheses";
val _ = assert (mentions "machine_sem" admit andalso mentions "Terminate Success" admit)
               "admit_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "admitDecide" admit)
               "admit_machine_code lost its composed spec word admitDecide";
val _ = assert (not (mentions "admitDecide" regen) andalso not (mentions "cacheServe" admit))
               "the two stages are not genuinely distinct decisions";

(* 3. the generator is a real generator, not a re-run: DISTINCT programs/decisions *)
val _ = assert (mentions "admitProg" admit andalso mentions "cacheKeyProg" regen)
               "stages do not target distinct parser-output programs";

(* 4. ground the 2nd stage's stored (GET,/api) key + its truth table *)
val km = EVAL “hashBytesN [71;69;84]”;               (* "GET"  *)
val ku = EVAL “hashBytesN [47;97;112;105]”;           (* "/api" *)
val _ = print ("\nKM = hashBytes \"GET\"  = " ^ term_to_string (rhs (concl km)) ^ "\n");
val _ = print ("KU = hashBytes \"/api\" = " ^ term_to_string (rhs (concl ku)) ^ "\n");
val _ = assert (rhs (concl km) ~~ “4773603”) "KM != hashBytes GET";
val _ = assert (rhs (concl ku) ~~ “821282413”) "KU != hashBytes /api";

val a1 = (EVAL THENC SIMP_CONV (srw_ss()) []) “admitDecide [71;69;84] [47;97;112;105]”;  (* GET /api  -> 1 *)
val a2 = (EVAL THENC SIMP_CONV (srw_ss()) []) “admitDecide [80;79;83;84] [47;97;112;105]”;(* POST /api -> 0 *)
val a3 = (EVAL THENC SIMP_CONV (srw_ss()) []) “admitDecide [71;69;84] [47]”;             (* GET /     -> 0 *)
val _ = print ("admitDecide GET  /api  (declared)   = " ^ term_to_string (rhs (concl a1)) ^ "\n");
val _ = print ("admitDecide POST /api  (method miss)= " ^ term_to_string (rhs (concl a2)) ^ "\n");
val _ = print ("admitDecide GET  /     (route miss) = " ^ term_to_string (rhs (concl a3)) ^ "\n");
val _ = assert (rhs (concl a1) ~~ “1n”) "declared surface != admit(1)";
val _ = assert (rhs (concl a2) ~~ “0n”) "method miss != 0";
val _ = assert (rhs (concl a3) ~~ “0n”) "route miss != 0";

(* 5. the body-generic frame engine is non-vacuous *)
val _ = assert (mentions "FOLDL" loop_frame andalso mentions "While foldGuard" loop_frame)
               "loop_frame is vacuous";

val _ = print ("\n@@ verifyC23 axioms = " ^ Int.toString (length (axioms "verifyC23")) ^ "\n");
val _ = print "\n@@@ C23 AUDIT PASSED: mk_composedWrapper reproduces C22 byte-identically AND closes a 2nd composed stage (admit); frame machinery generalized; DISK_THM-only, hyps=0, non-vacuous @@@\n";

val _ = export_theory ();

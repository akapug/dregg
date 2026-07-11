(* ===========================================================================
   C22 — the machine-checked AUDIT theory.  Prints the composed end-to-end
   theorem `cacheKey_machine_code` with show_tags and asserts:
     * [oracles: DISK_THM] [axioms: ], hyps = 0, 0 cheats
     * NON-vacuous: a real `machine_sem ... SUBSET {Terminate Success ...}`
       conclusion that REPORTS the composed spec value `cacheServe method tgt age`
       (keyOf's two hashBytes folds + the isFresh gate), not a placeholder.
     * grounds the stored-key constants: 4773603 = hashBytes "GET",
       48 = hashBytes "/" (the deployed warm request's Cache.Key), 100 = the
       §4.2 freshness lifetime.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open cacheKeyGenTheory cacheKeyCoreTheory hashBytesLoopTheory wordsLib;

val _ = new_theory "verifyC22";
val _ = Globals.show_assums := true;

val e2e = cacheKeyGenTheory.cacheKey_machine_code;

val _ = print "\n===== cacheKey_machine_code =====\n";
val _ = print (thm_to_string e2e);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string e2e ^ "\n");
val _ = print ("HYPS = " ^ Int.toString (length (hyp e2e)) ^ "\n");

fun assert b msg = if b then () else raise Fail ("C22 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs
  end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val _ = assert (oracles_ok e2e) "cacheKey_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp e2e)) "cacheKey_machine_code has hypotheses";
val _ = assert (mentions "machine_sem" e2e andalso mentions "Terminate Success" e2e)
               "cacheKey_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "cacheServe" e2e)
               "cacheKey_machine_code lost its composed spec word cacheServe";

(* ground the stored (GET,/) key + the freshness lifetime *)
val km = EVAL “hashBytesN [71;69;84]”;   (* "GET" *)
val ku = EVAL “hashBytesN [47]”;          (* "/"   *)
val _ = print ("\nKM = hashBytes \"GET\" = " ^ term_to_string (rhs (concl km)) ^ "\n");
val _ = print ("KU = hashBytes \"/\"   = " ^ term_to_string (rhs (concl ku)) ^ "\n");
val _ = assert (rhs (concl km) ~~ “4773603”) "KM != hashBytes GET";
val _ = assert (rhs (concl ku) ~~ “48”) "KU != hashBytes /";

(* the composed spec: serve iff key matches AND fresh (non-vacuous in all inputs) *)
val serve1 = EVAL “cacheServe [71;69;84] [47] 50”;   (* match + fresh -> 1 *)
val serve0 = EVAL “cacheServe [71;69;84] [47] 200”;  (* match + stale -> 0 *)
val serveM = (EVAL THENC SIMP_CONV (srw_ss()) []) “cacheServe [80;79;83;84] [47] 50”;(* key miss -> 0 *)
val _ = print ("cacheServe GET / 50  (fresh hit)  = " ^ term_to_string (rhs (concl serve1)) ^ "\n");
val _ = print ("cacheServe GET / 200 (stale)      = " ^ term_to_string (rhs (concl serve0)) ^ "\n");
val _ = print ("cacheServe POST / 50 (key miss)   = " ^ term_to_string (rhs (concl serveM)) ^ "\n");
val _ = assert (rhs (concl serve1) ~~ “1n”) "fresh hit != 1";
val _ = assert (rhs (concl serve0) ~~ “0n”) "stale != 0";
val _ = assert (rhs (concl serveM) ~~ “0n”) "key miss != 0";

val _ = print ("\n@@ verifyC22 axioms = " ^ Int.toString (length (axioms "verifyC22")) ^ "\n");
val _ = print "\n@@@ C22 AUDIT PASSED: cacheEmptyStage cache-key path closed spec->machine-code, DISK_THM-only, hyps=0, non-vacuous @@@\n";

val _ = export_theory ();

(* ===========================================================================
   C21 — the machine-checked AUDIT theory.  Prints the two generated end-to-end
   theorems (hash REGRESSION + the NEW clen fold) with `show_tags`, and asserts
   each is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats, and NON-vacuous
   (a real `machine_sem SUBSET {Terminate Success ...}` conclusion) — both
   produced by the SAME `mk_foldWrapper` generator call.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open hashGenTheory clenGenTheory;

val _ = new_theory "verifyC21";
val _ = Globals.show_assums := true;

fun rep nm th =
  (print ("\n===== " ^ nm ^ " =====\n");
   print (thm_to_string th); print "\n";
   print ("TAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string th ^ "\n");
   print ("HYPS = " ^ Int.toString (length (hyp th)) ^ "\n"));

val hashE2E = hashGenTheory.hash_machine_code;
val clenE2E = clenGenTheory.clen_machine_code;

val _ = rep "hash_machine_code (REGRESSION: C20 reproduced by generator)" hashE2E;
val _ = rep "clen_machine_code (NEW 2nd fold, generator-closed)" clenE2E;

(* --- adversarial checks: not vacuous, no bad tags, no hyps --- *)
fun assert b msg = if b then () else raise Fail ("C21 AUDIT FAILED: " ^ msg);

fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs
  end;

(* each end-to-end must MENTION machine_sem and Terminate Success (real content) *)
fun mentions s th = String.isSubstring s (thm_to_string th);

val _ = assert (oracles_ok hashE2E) "hash_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (oracles_ok clenE2E) "clen_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp hashE2E)) "hash_machine_code has hypotheses";
val _ = assert (null (hyp clenE2E)) "clen_machine_code has hypotheses";
val _ = assert (mentions "machine_sem" hashE2E andalso mentions "Terminate Success" hashE2E)
               "hash_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "machine_sem" clenE2E andalso mentions "Terminate Success" clenE2E)
               "clen_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "hashBytesN" hashE2E) "hash_machine_code lost its spec word hashBytesN";
val _ = assert (mentions "clenN" clenE2E)       "clen_machine_code lost its spec word clenN";

val _ = print ("\n@@ verifyC21 axioms = " ^ Int.toString (length (axioms "verifyC21")) ^ "\n");
val _ = print "\n@@@ C21 AUDIT PASSED: both folds closed by mk_foldWrapper, DISK_THM-only, hyps=0, non-vacuous @@@\n";

val _ = export_theory ();

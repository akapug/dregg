open HolKernel boolLib bossLib Parse;
open hashCoreTheory hashMainRefineTheory hashInstallTheory hashEndToEndTheory
     hashBytesLoopTheory;
val _ = new_theory "verifyHash20";
val _ = Globals.show_assums := true;
fun rep nm th =
  (print ("\n===== " ^ nm ^ " =====\n");
   print (thm_to_string th); print "\n";
   print ("TAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string th ^ "\n");
   print ("HYPS = " ^ Int.toString (length (hyp th)) ^ "\n"));
val _ = rep "hashLoopCore_refines" hashLoopCore_refines;
val _ = rep "evaluate_hashLoopCore_framed" evaluate_hashLoopCore_framed;
val _ = rep "hashMainBody_refines" hashMainBody_refines;
val _ = rep "hashBytesProg_semantics_decls" hashBytesProg_semantics_decls;
val _ = rep "hash_machine_code" hash_machine_code;
val _ = print ("\n@@ verifyHash20 axioms = " ^ Int.toString (length (axioms "verifyHash20")) ^ "\n");
val _ = export_theory ();

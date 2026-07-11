val _ = List.app load ["boundScanWholeMainTheory"];
open HolKernel boolLib bossLib Parse;
open boundScanWholeMainTheory;
val _ = set_trace "Unicode" 0;
val _ = Globals.max_print_depth := 90;

fun tags nm th =
  let val t = Thm.tag th
  in print ("=== " ^ nm ^ "\n  oracles = [" ^ String.concatWith "," (Tag.dest_tag t |> fst) ^
            "]\n  axiomdeps = [" ^ String.concatWith "," (Tag.dest_tag t |> snd) ^ "]\n") end;

val _ = print "\n@@@ KERNEL TAGS (fresh load) @@@\n";
val _ = tags "scanLoop_locals_frame" scanLoop_locals_frame;
val _ = tags "Seq_NONE_le" Seq_NONE_le;
val _ = tags "elseCore" elseCore;
val _ = tags "elseBranch_frame" elseBranch_frame;

val _ = print ("\n@@@ THEORY AXIOMS: boundScanWholeMain = " ^
               Int.toString (length (axioms "boundScanWholeMain")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: boundScanLoopLinkA = " ^
               Int.toString (length (axioms "boundScanLoopLinkA")) ^ "\n");
val _ = print ("@@@ THEORY AXIOMS: boundScanMainFrame = " ^
               Int.toString (length (axioms "boundScanMainFrame")) ^ "\n");

(* non-vacuity: fully-qualified constants referenced by the headline theorems *)
fun qconsts nm th =
  let val cs = HOLset.listItems (Term.all_atoms (concl th))
      val cns = List.mapPartial (fn t => (SOME (let val {Thy,Name,...} = dest_thy_const t in Thy^"$"^Name end)) handle _ => NONE) cs
      val uniq = Lib.mk_set cns
  in print ("=== consts in " ^ nm ^ ":\n  " ^ String.concatWith "\n  " uniq ^ "\n") end;
val _ = print "\n@@@ FULLY-QUALIFIED CONST AUDIT (non-vacuity) @@@\n";
val _ = qconsts "scanLoop_locals_frame" scanLoop_locals_frame;
val _ = qconsts "elseBranch_frame" elseBranch_frame;

val _ = print "\n@@@ elseBranch_frame STATEMENT @@@\n";
val _ = print (thm_to_string elseBranch_frame ^ "\n");
val _ = print "\n@@@ scanLoop_locals_frame STATEMENT @@@\n";
val _ = print (thm_to_string scanLoop_locals_frame ^ "\n");

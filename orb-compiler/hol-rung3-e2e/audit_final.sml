val _ = app load ["boundScanRung3E2ETheory","boundScanE2EFrameTheory"];
open boundScanRung3E2ETheory boundScanE2EFrameTheory;
fun tg th = let val (orc,ax) = Tag.dest_tag (Thm.tag th)
            in "[oracles: "^String.concatWith "," orc^"] [axioms: "^String.concatWith "," ax^"]" end;
val _ = print "\n@@FINAL TAGS\n";
val _ = print ("boundScan_rung3_e2e         : "^tg boundScan_rung3_e2e
               ^"  hyps="^Int.toString(length(Thm.hyp boundScan_rung3_e2e))^"\n");
val _ = print ("boundScan_rung3_e2e_native  : "^tg boundScan_rung3_e2e_native
               ^"  hyps="^Int.toString(length(Thm.hyp boundScan_rung3_e2e_native))^"\n");
val _ = print ("boundScanProg_sd_bridge     : "^tg boundScanProg_semantics_decls_bridge^"\n");
val _ = print ("axioms E2E   = "^Int.toString(length(axioms "boundScanRung3E2E"))^"\n");
val _ = print ("axioms Frame = "^Int.toString(length(axioms "boundScanE2EFrame"))^"\n");
(* forbid cheat / native_decide surrogates *)
val orc_n = #1 (Tag.dest_tag (Thm.tag boundScan_rung3_e2e_native));
val _ = print ("\n@@ native oracle set = ["^String.concatWith "," orc_n^"]\n");
val _ = print ("@@ has cake_native_bootstrap = "^Bool.toString(List.exists (fn s=>s="cake_native_bootstrap") orc_n)^"\n");
val _ = print ("@@ e2e (DISK_THM-only) oracle set = ["
  ^String.concatWith "," (#1 (Tag.dest_tag (Thm.tag boundScan_rung3_e2e)))^"]\n");
val _ = print "\n@@NATIVE STATEMENT\n";
val _ = Globals.show_tags := true;
val _ = print (thm_to_string boundScan_rung3_e2e_native);
val _ = print "\n@@END\n";

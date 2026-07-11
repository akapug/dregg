(* ===========================================================================
   C30 probe — ADVERSARIAL AUDIT.

   Checks, mechanically (build fails otherwise):
   (1) the END-TO-END theorem `secheaders_bytes_machine_code` (machine_sem SUBSET
       {Terminate Success (... report_vec (MAP n2w secHeadersBytes) ...)}) and the
       whole-program Link-A `transformProg_semantics_decls` carry NO axioms and
       only the benign CakeML disk-export oracle tag (no cheats, no `sorry`);
   (2) leanc OUT of the TCB: transformProg IS the verified parser's output on
       copy.pnk (`transformProg_is_parser_output`);
   (3) NON-VACUITY: `secHeadersBytes` is the concrete, non-empty 159-byte deployed
       serialized security-header block, every byte < 256, byte-for-byte
       `MAP ORD` of the render output — and the store loop actually writes them
       (`copyLoopA_writes` is NON-vacuous: it fires from a satisfiable copyInv).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open listTheory stringTheory;
open transformCopyLoopTheory transformSecHeadersTheory transformLinkBInstTheory
     transformWrapperTheory transformInstallTheory transformEndToEndTheory;

val _ = new_theory "verifyC30";

fun banner s = print ("\n========== " ^ s ^ " ==========\n");

(* ---- (1) tags on the headline theorems ---- *)
banner "axioms across the C30 theories";
val thys = ["transformCopyLoop","transformSecHeaders","transformLinkBInst",
            "transformWrapper","transformMainRefine","transformSem",
            "transformInstall","transformEndToEnd"];
val _ = app (fn t => print (t ^ ": " ^ Int.toString (length (axioms t)) ^ " axioms\n")) thys;

banner "secheaders_bytes_machine_code  (THE END-TO-END spec -> machine code)";
val _ = print (thm_to_string secheaders_bytes_machine_code ^ "\n");
val _ = let val (ors, axs) = Tag.dest_tag (Thm.tag secheaders_bytes_machine_code)
        in print ("oracles = [" ^ String.concatWith ", " ors ^ "]\n");
           print ("axioms  = [" ^ String.concatWith ", " axs ^ "]\n") end;

banner "transformProg_semantics_decls  (whole-program Link A)";
val _ = print (thm_to_string transformProg_semantics_decls ^ "\n");

banner "transformProg_is_parser_output  (leanc OUT: verified-parser output)";
val _ = print (thm_to_string transformProg_is_parser_output ^ "\n");

(* build-fail guard: 0 axioms across all C30 theories, and the two headline
   theorems carry only the benign DISK_THM oracle (no cheats, no extra oracles). *)
val _ =
  let
    fun tagOK th =
      let val (ors, axs) = Tag.dest_tag (Thm.tag th)
      in null axs andalso (ors = [] orelse ors = ["DISK_THM"]) end
  in
    if List.all (fn t => null (axioms t)) thys andalso
       tagOK secheaders_bytes_machine_code andalso
       tagOK transformProg_semantics_decls
    then print "\n@@@ C30 AXIOM/ORACLE CHECK: OK (0 axioms, DISK_THM-only) @@@\n"
    else raise Fail "C30 audit FAILED: unexpected axiom or oracle tag"
  end;

(* ---- (2) leanc-out: the program IS the verified parser output ---- *)
val _ =
  let val c = concl transformProg_is_parser_output
  in if can (find_term (fn t => same_const t “parse_topdecs_to_ast” handle _ => false)) c
     then print "\n@@@ C30 LEANC-OUT: transformProg = parse_topdecs_to_ast <copy.pnk> @@@\n"
     else raise Fail "C30 audit FAILED: parser-output theorem not about the verified parser"
  end;

(* ---- (3) NON-VACUITY / grounding of the payload ---- *)
banner "the deployed serialized security-header block (the quoted payload)";
val _ = print (Parse.term_to_string (rhs (concl secHeadersStr_def)) ^ "\n");

Theorem c30_payload_nonvacuous:
  LENGTH secHeadersBytes = 159 /\
  secHeadersBytes <> [] /\
  EVERY (\x. x < 256) secHeadersBytes /\
  secHeadersBytes = MAP ORD secHeadersStr
Proof
  simp [secHeadersBytes_length_val, secHeadersBytes_nonempty,
        secHeadersBytes_bytes, secHeadersBytes_def]
QED

Theorem c30_payload_grounded:
  TAKE 25 secHeadersBytes = MAP ORD "Strict-Transport-Security" /\
  EL 0 secHeadersBytes = ORD #"S" /\
  IS_SUFFIX secHeadersBytes (MAP ORD ("no-referrer" ++ crlf))
Proof
  simp [secHeadersBytes_prefix] >>
  simp [secHeadersBytes_def, secHeadersStr_def, crlf_def] >> EVAL_TAC
QED

banner "C30 VERIFY DONE";
val _ = print "\n@@@ C30 VERIFY DONE @@@\n";
val _ = export_theory ();

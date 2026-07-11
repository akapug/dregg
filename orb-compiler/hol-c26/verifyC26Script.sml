(* ===========================================================================
   C26 probe — the ADVERSARIAL AUDIT of the security-headers decision core.
   Checks: (1) the final spec->machine-code theorem's tags are [oracles:DISK_THM]
   [axioms:] with hyps = 0; (2) every C26 theory declares ZERO axioms; (3) the
   decision is NON-VACUOUS and GROUNDED — the reported word tracks the real Lean
   spec `hstsEffective` (= SecurityHeaders.effectiveIncludeSubDomains at the
   deployed includeSubDomains = true) on real inputs: the DEPLOYED policy's
   max-age = 31536000 reports 1 (HSTS includeSubDomains effective), and
   max-age = 0 reports 0 (RFC 6797 6.1.1 NOTE: policy disabled) — the two differ,
   so the guard is a genuine branch, not a constant; (4) leanc stays OUT of the
   TCB (secHeadersProg is the verified parser's output).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory wordsTheory;
open secheadersEndToEndTheory secheadersInstallTheory secheadersLinkBInstTheory
     secheadersCoreTheory secheadersMainRefineTheory secheadersSemTheory
     secheadersWrapperTheory;
val _ = new_theory "verifyC26";
val _ = Globals.show_tags := true;
val auditOS = TextIO.openOut "verifyC26_out.txt";
fun emit s = (print s; TextIO.output (auditOS, s));
fun banner s = emit ("\n@@@ "^s^"\n");

banner "secheaders_machine_code (tags shown)";
val _ = emit (thm_to_string secheaders_machine_code);

banner "HYP COUNT of secheaders_machine_code (must be 0)";
val _ = emit ("hyps = " ^ Int.toString (length (hyp secheaders_machine_code)) ^ "\n");

banner "AXIOM COUNTS (must all be 0)";
val thys = ["secheadersEndToEnd","secheadersInstall","secheadersLinkBInst",
            "secheadersMainRefine","secheadersSem","secheadersWrapper",
            "secheadersCore","c14Generic","panAuto"];
val _ = List.app (fn t =>
  emit ("axioms " ^ t ^ " = " ^ Int.toString (length (axioms t)) ^ "\n")) thys;

banner "NON-VACUITY / GROUNDING — the reported word tracks the Lean spec";
(* deployed HSTS policy max-age = 31536000 (one year) -> effective = 1 *)
val ev_deployed = EVAL “hstsEffective 31536000”;
val _ = emit ("hstsEffective 31536000 = " ^ term_to_string (rhs (concl ev_deployed)) ^ "\n");
(* max-age = 0 -> disabled -> effective = 0 (RFC 6797 6.1.1 NOTE) *)
val ev_zero = EVAL “hstsEffective 0”;
val _ = emit ("hstsEffective 0 = " ^ term_to_string (rhs (concl ev_zero)) ^ "\n");
(* assert the concrete truth table + that the branch is REAL (outputs differ) *)
val _ = if aconv (rhs (concl ev_deployed)) “1n” then ()
        else raise Fail "GROUNDING FAILED: deployed max-age did not report 1";
val _ = if aconv (rhs (concl ev_zero)) “0n” then ()
        else raise Fail "GROUNDING FAILED: max-age=0 did not report 0";
val _ = if aconv (rhs (concl ev_deployed)) (rhs (concl ev_zero))
        then raise Fail "VACUOUS: the decision is constant across inputs"
        else emit "OK: decision is a genuine branch (0 vs 1), grounded on real inputs\n";

banner "secHeadersProg_linkB (backend half, tags shown)";
val _ = emit (thm_to_string secHeadersProg_linkB);

banner "evaluate_secheadersCore (AUTO-derived branch core, tags shown)";
val _ = emit (thm_to_string evaluate_secheadersCore);

banner "secHeadersProg_is_parser_output (leanc-out-of-TCB, tags shown)";
val _ = emit (thm_to_string secHeadersProg_is_parser_output);

banner "DONE";
val _ = export_theory ();

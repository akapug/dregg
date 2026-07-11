(* C23 — LINK B for the second composed stage (admit). leanc OUT of the TCB:
   admitProg is the VERIFIED parser's output on admit.pnk. *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "admitLinkBInst";

val linkB_result = mk_linkB { pnkFile = "admit.pnk", progName = "admitProg" };

Theorem admitProg_is_parser_output = #parser_output linkB_result;
Theorem admitProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

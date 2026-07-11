(* C25 — LINK B for the third composed stage (CORS). leanc OUT of the TCB:
   corsProg is the VERIFIED parser's output on cors.pnk. *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "corsLinkBInst";

val linkB_result = mk_linkB { pnkFile = "cors.pnk", progName = "corsProg" };

Theorem corsProg_is_parser_output = #parser_output linkB_result;
Theorem corsProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

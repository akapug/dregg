(* C29 - LINK B for the ipfilter CIDR admission gate stage.  leanc OUT of the TCB:
   ipfProg is the VERIFIED parser's output on ipf.pnk. *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "ipfLinkBInst";

val linkB_result = mk_linkB { pnkFile = "ipf.pnk", progName = "ipfProg" };

Theorem ipfProg_is_parser_output = #parser_output linkB_result;
Theorem ipfProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

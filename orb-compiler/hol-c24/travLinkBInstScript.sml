(* C24 - LINK B for the traversal gate stage.  leanc OUT of the TCB:
   travProg is the VERIFIED parser's output on traversal.pnk. *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "travLinkBInst";

val linkB_result = mk_linkB { pnkFile = "traversal.pnk", progName = "travProg" };

Theorem travProg_is_parser_output = #parser_output linkB_result;
Theorem travProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

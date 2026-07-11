(* ===========================================================================
   C22 — LINK B for the composed cache-key program, via panAutoLib.mk_linkB
   against the real CakeML backend-correctness theorem.  leanc OUT of the TCB:
   cacheKeyProg is the VERIFIED parser's output on cachekey.pnk.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "cacheKeyLinkBInst";

val linkB_result =
  mk_linkB { pnkFile = "cachekey.pnk", progName = "cacheKeyProg" };

Theorem cacheKeyProg_is_parser_output = #parser_output linkB_result;
Theorem cacheKeyProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

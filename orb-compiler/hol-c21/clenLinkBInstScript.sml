(* ===========================================================================
   C21 — LINK B for the Content-Length decimal-fold program, instantiated at the
   emitted clen program against the REAL CakeML backend correctness theorem, via
   the GENERATOR panAutoLib.mk_linkB.  leanc stays OUT of the TCB: clenProg is the
   VERIFIED parser output on clen.pnk.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "clenLinkBInst";

val linkB_result =
  mk_linkB { pnkFile = "clen.pnk", progName = "clenProg" };

Theorem clenProg_is_parser_output = #parser_output linkB_result;
Theorem clenProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

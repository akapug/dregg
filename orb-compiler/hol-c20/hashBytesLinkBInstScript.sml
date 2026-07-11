(* ===========================================================================
   C20 — LINK B for the deployed cache-key hash program, instantiated at the
   emitted hashbytes program against the REAL, built CakeML backend correctness
   theorem, via the GENERATOR panAutoLib.mk_linkB (C11/C14/C18 procedure).
   leanc stays OUT of the TCB: hashBytesProg is the VERIFIED parser output.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "hashBytesLinkBInst";

val linkB_result =
  mk_linkB { pnkFile = "hashbytes.pnk", progName = "hashBytesProg" };

Theorem hashBytesProg_is_parser_output = #parser_output linkB_result;
Theorem hashBytesProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

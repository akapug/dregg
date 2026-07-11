(* ===========================================================================
   C30 — LINK B for the TRANSFORM (constant secheaders) program, instantiated at
   the emitted copy.pnk program against the REAL, built CakeML backend
   correctness theorem, via the GENERATOR panAutoLib.mk_linkB (C11/C14/C20
   procedure).  leanc stays OUT of the TCB: transformProg is the VERIFIED
   parser's output on copy.pnk (`parse_topdecs_to_ast <copy.pnk> = INL
   transformProg`).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "transformLinkBInst";

val linkB_result =
  mk_linkB { pnkFile = "copy.pnk", progName = "transformProg" };

Theorem transformProg_is_parser_output = #parser_output linkB_result;
Theorem transformProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

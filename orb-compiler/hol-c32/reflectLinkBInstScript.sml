(* ===========================================================================
   C32 — LINK B for the two-loop REFLECT (request-dependent fold-then-store)
   program, via the generator panAutoLib.mk_linkB (C11/C20/C30 procedure).
   leanc stays OUT of the TCB: reflectProg is the VERIFIED parser's output on
   reflect.pnk (parse_topdecs_to_ast <reflect.pnk> = INL reflectProg).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "reflectLinkBInst";

val linkB_result =
  mk_linkB { pnkFile = "reflect.pnk", progName = "reflectProg" };

Theorem reflectProg_is_parser_output = #parser_output linkB_result;
Theorem reflectProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

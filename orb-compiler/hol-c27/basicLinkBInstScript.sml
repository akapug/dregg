(* C27 — LINK B for the Basic-auth compare gate. leanc OUT of the TCB:
   basicProg is the VERIFIED parser's output on basic.pnk. *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "basicLinkBInst";

val linkB_result = mk_linkB { pnkFile = "basic.pnk", progName = "basicProg" };

Theorem basicProg_is_parser_output = #parser_output linkB_result;
Theorem basicProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

(* C31 — LINK B for the HS256 JWT admin gate's sig-verify + alg-confusion decision.
   leanc OUT of the TCB: jwtProg is the VERIFIED parser's output on jwt.pnk. *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "jwtLinkBInst";

val linkB_result = mk_linkB { pnkFile = "jwt.pnk", progName = "jwtProg" };

Theorem jwtProg_is_parser_output = #parser_output linkB_result;
Theorem jwtProg_linkB            = #linkB linkB_result;

val _ = export_theory ();

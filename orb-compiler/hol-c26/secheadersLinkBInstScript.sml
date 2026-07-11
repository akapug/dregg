(* ===========================================================================
   C15 probe — LINK B for the THIRD primitive, instantiated at the emitted
   statusclass program against the REAL, built CakeML backend correctness
   theorem.  This is the NEAR-AUTOMATIC backend half: byte-for-byte the C11/C14
   procedure with the program swapped.  Produced by the GENERATOR
   `panAutoLib.mk_linkB` — the ONLY per-primitive inputs are the .pnk filename
   and the program-constant name; the four EVAL side conditions and the
   instantiation of `pan_to_target_compile_semantics` are program-agnostic.
   leanc stays OUT of the TCB: secHeadersProg is the VERIFIED parser's output.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetProofTheory pan_to_wordProofTheory;
open panAutoLib;

val _ = new_theory "secheadersLinkBInst";

(* The generator: parse the .pnk with the verified parser, bind the program
   constant, discharge the four EVAL side conditions, instantiate Link B.  We
   bind the whole record (a flexible `...` record pattern needs the record type
   fully resolved at the binding site, which it is not here) and project the
   fields we re-export with the record accessors. *)
val linkB_result =
  mk_linkB { pnkFile = "secheaders.pnk", progName = "secHeadersProg" };

(* #prog_def was already saved by `new_definition` inside mk_linkB
   (as secHeadersProg_def); re-export the two derived theorems. *)
val secHeadersProg_is_parser_output = #parser_output linkB_result;
val secHeadersProg_linkB            = #linkB linkB_result;

val _ = save_thm ("secHeadersProg_is_parser_output", secHeadersProg_is_parser_output);
val _ = save_thm ("secHeadersProg_linkB", secHeadersProg_linkB);

val _ = export_theory ();

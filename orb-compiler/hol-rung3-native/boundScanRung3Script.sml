(* ===========================================================================
   CN Rung-3-native — COMPOSE the three ground lanes into the end-to-end
   Rung-3 statement for the boundscan serve stage:

     boundscan.pnk --native cake--> boundScanBytes (concrete x64, 7ms, NO in-logic
       EVAL of the backend)  --bytes-bridge--> Link-B antecedent (native bytes in
       the real `bytes` slot)  --Link-B (pan_to_target_compile_semantics)-->
       machine_sem refines the Pancake SOURCE semantics of the exact stage
       program, with the program-level applicability conditions DISCHARGED here.

   Ground:
     - CN-NATIVE-BOOTSTRAP-REPORT.md  : native cake, cake_compiled_thm bootstrap.
     - CN-BYTES-BRIDGE-REPORT.md      : boundScanBytes/Bitmaps concrete; Layer 1
                                        (pan_to_target_compile_semantics INST at
                                        native bytes), Layer 2 (compile_prog =
                                        SOME(native bytes), oracle bootstrap).
     - CN-BOUNDSCAN-LINKA-REPORT.md   : scanLoop_refines_scanFrom (Link A, loop).

   THIS theory's kernel-checked additions:
     1. boundScanProg_bridge_eq_linkB : the bytes-bridge program constant and the
        C10/Link-A program constant are the SAME AST (both = the verified parser's
        output on the byte-identical boundscan.pnk).  Cross-lane glue.
     2. The FOUR program-level Link-B applicability conditions, discharged by EVAL
        against the REAL pan_to_targetProof / pan_to_wordProof constants on the
        bridge program (C10 discharged them against verbatim-restated predicates;
        here against the real constants that pan_to_target_compile_semantics uses).
     3. boundScan_rung3_native : Link B with (a) the native bytes in the code slot
        and (b) the four program conditions DISCHARGED — reducing the theorem to
        machine_sem refines {semantics_decls s <main> boundScanProg}, conditional
        only on [the native-bytes backend equation | the runtime install package |
        semantics_decls != Fail].  DISK_THM only (no cake_native_bootstrap oracle:
        the native-bytes equation is kept as a NAMED antecedent, discharged by the
        bootstrap only via the compile_prog<->compile_prog_max packaging lemma,
        CN-BYTES-BRIDGE 4.1).

   What is NOT closed (named, per the honesty rule, NOT faked):
     - The whole-main Link-A frame connecting semantics_decls s <main>
       boundScanProg to the Lean spec n2w(boundScan a off len).  Link A
       (scanLoop_refines_scanFrom, carried here) closes the SCAN LOOP; lifting it
       through the Dec/@load_vec-FFI/bounds-If frame to the whole-program source
       semantics is the CN-BOUNDSCAN-LINKA residual #1/#5 — unproven.  Hence the
       conclusion of boundScan_rung3_native stays at the Pancake SOURCE semantics,
       NOT the Lean spec word.  Building a semantics_decls = <spec> theorem here
       would be either an EVAL of the whole-program semantics (the dead end) or a
       vacuous restatement; reported as the obstruction, not written.
     - The compile_prog<->compile_prog_max packaging lemma (CN-BYTES-BRIDGE 4.1)
       and the runtime install package (4.2) — the two named Link-B residuals,
       kept as antecedents G1/G2.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open listTheory rich_listTheory wordsTheory wordsLib arithmeticTheory;
open panLangTheory panSemTheory panPropsTheory panPtreeConversionTheory;
open pan_to_targetTheory pan_to_targetProofTheory pan_to_wordProofTheory;
open boundScanBytesBridgeTheory boundScanLoopLinkATheory;

val _ = new_theory "boundScanRung3";

(* the two program constants (three-deep thy$name, no ambiguity) *)
val bridgeProg =
  prim_mk_const {Name = "boundScanProg", Thy = "boundScanBytesBridge"};
val linkbProg =
  prim_mk_const {Name = "boundScanProg", Thy = "boundScanLinkB"};

(* ---------------------------------------------------------------------------
   1. Cross-lane program identity.  Both defs unfold to the SAME AST literal
      (byte-identical boundscan.pnk, same verified parser) => the bytes-bridge
      program (Link B / native bytes) and the C10 / Link-A program are equal.
   --------------------------------------------------------------------------- *)
Theorem boundScanProg_bridge_eq_linkB:
  ^bridgeProg = ^linkbProg
Proof
  REWRITE_TAC [boundScanBytesBridgeTheory.boundScanProg_def,
               boundScanLinkBTheory.boundScanProg_def]
QED

(* ---------------------------------------------------------------------------
   2. The FOUR program-level applicability conditions of
      pan_to_target_compile_semantics, discharged by EVAL on the bridge program,
      against the REAL constants (pancake_good_code / distinct_params /
      size_of_eids the specialised Link-B theorem is stated over).
   --------------------------------------------------------------------------- *)
val _ = computeLib.add_funs
          [pan_to_targetProofTheory.pancake_good_code_def,
           pan_to_wordProofTheory.good_panops_def,
           pan_to_wordProofTheory.distinct_params_def,
           panPropsTheory.exps_of_def,
           panPropsTheory.every_exp_def];

Theorem bs_pancake_good_code:
  pancake_good_code ^bridgeProg
Proof
  REWRITE_TAC [boundScanBytesBridgeTheory.boundScanProg_def]
  \\ EVAL_TAC \\ rw []
QED

Theorem bs_distinct_params:
  distinct_params (functions ^bridgeProg)
Proof
  REWRITE_TAC [boundScanBytesBridgeTheory.boundScanProg_def] \\ EVAL_TAC
QED

Theorem bs_distinct_names:
  ALL_DISTINCT (MAP FST (functions ^bridgeProg))
Proof
  REWRITE_TAC [boundScanBytesBridgeTheory.boundScanProg_def] \\ EVAL_TAC
QED

Theorem bs_size_of_eids:
  size_of_eids ^bridgeProg < dimword (:64)
Proof
  REWRITE_TAC [boundScanBytesBridgeTheory.boundScanProg_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   3. Rung-3 native backbone.  Take the bytes-bridge Layer-1 theorem
      (pan_to_target_compile_semantics INST at :64, boundScanProg, and the
      concrete native boundScanBytes/boundScanBitmaps) and DISCHARGE its four
      program-level conditions (step 2).  The result: the native-compiled
      machine code refines the Pancake SOURCE semantics of the exact stage,
      conditional only on the native-bytes backend equation + the runtime
      install package + non-failure.
   --------------------------------------------------------------------------- *)
val boundScan_rung3_native =
  save_thm ("boundScan_rung3_native",
    boundScanBytesBridgeTheory.boundScan_pan_to_target_specialised
    |> SIMP_RULE bool_ss
         (map EQT_INTRO
            [bs_pancake_good_code, bs_distinct_params,
             bs_distinct_names, bs_size_of_eids]));

(* ---------------------------------------------------------------------------
   Verification dump: tags + axioms + the reduced antecedent shape.
   --------------------------------------------------------------------------- *)
val _ =
  let val os = TextIO.openOut "rung3.out"
      fun p s = TextIO.output (os, s)
      fun tagstr th =
        let val (orc, ax) = Tag.dest_tag (Thm.tag th)
        in "[oracles: " ^ String.concatWith "," orc ^ "] [axioms: "
           ^ String.concatWith "," ax ^ "]" end
  in
    p ("=== boundScanProg_bridge_eq_linkB ===\n"
       ^ thm_to_string boundScanProg_bridge_eq_linkB ^ "\n"
       ^ tagstr boundScanProg_bridge_eq_linkB ^ "\n\n");
    p ("=== bs_pancake_good_code ===\n" ^ tagstr bs_pancake_good_code ^ "\n");
    p ("=== bs_distinct_params ===\n" ^ tagstr bs_distinct_params ^ "\n");
    p ("=== bs_distinct_names ===\n" ^ tagstr bs_distinct_names ^ "\n");
    p ("=== bs_size_of_eids ===\n"
       ^ thm_to_string bs_size_of_eids ^ "\n" ^ tagstr bs_size_of_eids ^ "\n\n");
    p ("=== boundScan_rung3_native (Rung-3 native backbone) ===\n"
       ^ tagstr boundScan_rung3_native ^ "\n");
    let val c = concl boundScan_rung3_native
        val (ante, conc) = dest_imp c
        val conjs = strip_conj ante
    in
      p ("remaining antecedent conjuncts = "
         ^ Int.toString (length conjs) ^ "\n");
      p ("conclusion:\n" ^ term_to_string conc ^ "\n\n");
      p ("--- remaining antecedents (the named residual G1/G2) ---\n");
      List.app (fn t => p ("  * " ^ term_to_string t ^ "\n")) conjs
    end;
    p ("\n=== Link A (carried) scanLoop_refines_scanFrom ===\n"
       ^ thm_to_string boundScanLoopLinkATheory.scanLoop_refines_scanFrom ^ "\n"
       ^ tagstr boundScanLoopLinkATheory.scanLoop_refines_scanFrom ^ "\n");
    p ("\ntheory axioms (boundScanRung3) = "
       ^ Int.toString (length (axioms "boundScanRung3")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

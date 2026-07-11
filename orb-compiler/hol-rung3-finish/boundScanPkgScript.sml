(* ===========================================================================
   CN RUNG-3 FINISH — gap (2): the compile_prog <-> compile_prog_max PACKAGING
   LEMMA (CN-BYTES-BRIDGE 4.1), discharged IN-LOGIC, WITHOUT EVAL of the backend.

   Layer 2 (bytes-bridge, oracle cake_native_bootstrap) certifies the native
   output equation for pan_to_target$compile_prog — the fn the `cake` binary
   runs under --pancake.  Link B / the Rung-3 backbone antecedent G1 is stated
   over compile_prog_max (the backend max-stack packaging).  This theory bridges
   the two for boundScanProg by SYMBOLIC unfolding: the shared compiler passes
   (pan_to_word / word_to_word / word_to_stack / stack_to_lab / lab_to_target)
   occur as byte-identical opaque subterms on both sides and cancel; the only
   program/config content is two CHEAP facts (perf_calls = F; the main-reorder
   is the identity on boundScanProg, `main` being its sole/first function).  The
   Pancake backend is NEVER evaluated on boundScanProg (no EVAL dead end).
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open listTheory rich_listTheory pairTheory;
open pan_to_targetTheory pan_to_targetProofTheory backendTheory;
open x64_configTheory x64_targetTheory;
open boundScanBytesBridgeTheory;

val _ = new_theory "boundScanPkg";

(* ---- cheap, program/config facts (NO backend run) ---- *)

Theorem bs_perf_calls_F:
  x64_backend_config.stack_conf.perf_calls = F
Proof
  EVAL_TAC
QED

Theorem bs_splitp:
  SPLITP (\x. case x of Function fi => fi.name = «main»
                      | Decl _ _ _ => F | Name _ _ => F) boundScanProg
    = ([], boundScanProg)
Proof
  rewrite_tac[boundScanProg_def] \\ EVAL_TAC
QED

(* ---- attach_bitmaps: bytes/bitmaps/lab_conf are invariant under the
        names-map and the base config (only .symbols and the other config
        fields differ).  This is the whole content of the packaging bridge. ---- *)

Theorem attach_bitmaps_bytes_agree:
  attach_bitmaps n1 c1 bm x = SOME (b, bm', cc1) ==>
  ?cc2. attach_bitmaps n2 c2 bm x = SOME (b, bm', cc2) /\
        cc2.lab_conf = cc1.lab_conf
Proof
  Cases_on `x` >> simp[attach_bitmaps_def] >>
  rename1 `SOME y` >> Cases_on `y` >>
  simp[attach_bitmaps_def] >> strip_tac >> gvs[]
QED

(* ---- the GENERAL packaging lemma (abstract prog/config; fast symbolic simp) ---- *)

Theorem compile_prog_max_bytes_bridge:
  mc.target.config = asm_conf /\
  c.stack_conf.perf_calls = F /\
  SPLITP (\x. case x of Function fi => fi.name = «main»
                      | Decl _ _ _ => F | Name _ _ => F) prog = ([], prog) /\
  compile_prog asm_conf c prog = SOME (bytes, bitmaps, c'c) ==>
  ?c'm sm.
    compile_prog_max c mc prog = (SOME (bytes, bitmaps, c'm), sm) /\
    c'm.lab_conf = c'c.lab_conf
Proof
  strip_tac >>
  qpat_x_assum `compile_prog _ _ _ = _` mp_tac >>
  simp[compile_prog_def, compile_prog_max_def, from_word_def,
       from_stack_def, from_lab_def] >>
  rpt (pairarg_tac >> fs[]) >>
  simp[attach_bitmaps_def] >>
  strip_tac >>
  drule attach_bitmaps_bytes_agree >>
  disch_then (qspecl_then [`LN`, `c`] mp_tac) >>
  strip_tac >> metis_tac[]
QED

(* ---- the boundScan instance ---- *)

Theorem boundScan_pkg_bridge:
  mc.target.config = x64_config /\
  compile_prog x64_config x64_backend_config boundScanProg =
    SOME (bytes, bitmaps, c'c) ==>
  ?c'm sm.
    compile_prog_max x64_backend_config mc boundScanProg =
      (SOME (bytes, bitmaps, c'm), sm) /\
    c'm.lab_conf = c'c.lab_conf
Proof
  strip_tac >>
  irule compile_prog_max_bytes_bridge >>
  metis_tac[bs_perf_calls_F, bs_splitp]
QED

(* ---- compose with Layer 2 (oracle cake_native_bootstrap): the NATIVE bytes
        satisfy G1 (compile_prog_max shape) with lab_conf pinned. ---- *)

Theorem boundScan_G1_native:
  mc.target.config = x64_config ==>
  ?c'm sm c'c.
    compile_prog_max x64_backend_config mc boundScanProg =
      (SOME (boundScanBytes, boundScanBitmaps, c'm), sm) /\
    c'm.lab_conf = c'c.lab_conf
Proof
  strip_tac >>
  strip_assume_tac boundScan_compile_prog_native >>
  metis_tac[boundScan_pkg_bridge]
QED

val _ = export_theory ();

(* ===========================================================================
   C32 — the whole-`main` FFI-trace refinement for the two-loop REQUEST-DEPENDENT
   transform (reflect.pnk).  The store lane's SOURCE is produced by the FOLD lane
   (loop1), not staged by the load oracle — the composition seam (reflectSeam).
   Both parsed While loops are bridged to the C30 store core `copyLoopA` via
   `While_body_ext` (Annots behaviourally invisible), so leanc is OUT.
   The observable is the BYTE VECTOR `MAP n2w req` — the reflected request.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory transformCopyLoopTheory reflectSeamTheory reflectWrapperTheory;
open proofManagerLib;
val _ = new_theory "reflectMainRefine";
fun ck s = (print ("\n@@@ "^s^" nGoals="^Int.toString(length(top_goals()))^" @@@\n"));

(* ---- ML peel of the emitted spine ---- *)
val mbT   = Term.inst [Type.alpha |-> “:64”] (rhs (concl reflectMainBody_def));
val Dctrl = rand mbT;        val body_c = rand Dctrl;
val Dout  = rand body_c;     val body_o = rand Dout;
val Dsrc  = rand body_o;     val X3     = rand Dsrc;
val loadSeq = rand (rator X3);  val AfterLoad = rand X3;
val Di = rand AfterLoad;     val body_i = rand Di;
val Dn = rand body_i;        val body_n = rand Dn;
val Dmid = rand body_n;      val body_m = rand Dmid;
val aOutMid = rand (rator body_m); val X6 = rand body_m;
val while1Seq = rand (rator X6);   val X7 = rand X6;
val aSrcMid = rand (rator X7);     val X8 = rand X7;
val aOut2 = rand (rator X8);       val X9 = rand X8;
val aI0 = rand (rator X9);         val X10 = rand X9;
val while2Seq = rand (rator X10);  val X11 = rand X10;
val reportSeq = rand (rator X11);  val retSeq = rand X11;
val whileP1 = rand while1Seq;      val whileP2 = rand while2Seq;

(* ---- bridge each parsed While to copyLoopA (Annots invisible) ---- *)
val while1_eq = prove(
  “!(s:(64,'ffi) panSem$state). evaluate (^whileP1, s) = evaluate (copyLoopA, s)”,
  `!(t:(64,'ffi) panSem$state). evaluate (^(rand whileP1), t) = evaluate (copyBodyA, t)`
     by (gen_tac >> simp [copyBodyA_def] >>
         CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, Annot_Seq_eq])) >>
         CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, Annot_Seq_eq])) >>
         REFL_TAC) >>
  drule While_body_ext >> strip_tac >> gen_tac >>
  simp [copyLoopA_def, copyGuard_def]);

val while2_eq = prove(
  “!(s:(64,'ffi) panSem$state). evaluate (^whileP2, s) = evaluate (copyLoopA, s)”,
  `!(t:(64,'ffi) panSem$state). evaluate (^(rand whileP2), t) = evaluate (copyBodyA, t)`
     by (gen_tac >> simp [copyBodyA_def] >>
         CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, Annot_Seq_eq])) >>
         CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, Annot_Seq_eq])) >>
         REFL_TAC) >>
  drule While_body_ext >> strip_tac >> gen_tac >>
  simp [copyLoopA_def, copyGuard_def]);

(* =========================== the refinement =========================== *)
g `reflectFFI req s0 /\ s0.locals = FEMPTY /\ LENGTH req = 8 /\
   2 * LENGTH req <= s0.clock ==>
   ?sF loadEv rb.
     evaluate (reflectMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events =
       s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (MAP (\b. (n2w b):word8) req) rb]`;
e (strip_tac);
e (qpat_x_assum `reflectFFI _ _` (strip_assume_tac o SIMP_RULE std_ss [reflectFFI_def]));
e (qabbrev_tac `ba = s0.base_addr`);
e (`«ctrl»<>«out» /\ «ctrl»<>«src» /\ «ctrl»<>«i» /\ «ctrl»<>«n» /\ «ctrl»<>«mid» /\
    «out»<>«src» /\ «out»<>«i» /\ «out»<>«n» /\ «out»<>«mid» /\ «src»<>«i» /\
    «src»<>«n» /\ «src»<>«mid» /\ «i»<>«n» /\ «i»<>«mid» /\ «n»<>«mid»` by EVAL_TAC);
(* build states down to the load call *)
e (qabbrev_tac `sCtrl = s0 with locals := s0.locals |+ («ctrl», ValWord ba)`);
e (qabbrev_tac `sOut = sCtrl with locals := sCtrl.locals |+ («out», ValWord (ba + 32w))`);
e (qabbrev_tac `sSrc = sOut with locals := sOut.locals |+ («src», ValWord (ba + 4096w))`);
e (`sSrc.base_addr = ba /\ sSrc.clock = s0.clock /\ sSrc.memory = s0.memory /\
    sSrc.memaddrs = s0.memaddrs /\ sSrc.be = s0.be /\ sSrc.ffi = s0.ffi /\ sSrc.structs = s0.structs`
     by simp [Abbr `sSrc`, Abbr `sOut`, Abbr `sCtrl`, Abbr `ba`]);
e (`FLOOKUP sSrc.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP sSrc.locals «out» = SOME (ValWord (ba + 32w)) /\
    FLOOKUP sSrc.locals «src» = SOME (ValWord (ba + 4096w))`
     by (simp [Abbr `sSrc`, Abbr `sOut`, Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (qpat_x_assum `!s. s.base_addr = _ /\ _ ==> _` (qspec_then `sSrc` mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (ExtCall «load_vec» _ _ _ _, sSrc) = (NONE, s1)`);
e (`s1.locals = sSrc.locals /\ s1.base_addr = ba /\ s1.clock = s0.clock`  by fs []);
e (`reflectStaged req ba s1` by fs []);
(* s1's pre-loop locals (= sSrc's): needed by the backward-wrap is_valid_value
   checks for the aOutMid `out := mid` reassignment (source sM chains to s1). *)
e (`FLOOKUP s1.locals «out» = SOME (ValWord (ba + 32w)) /\
    FLOOKUP s1.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s1.locals «src» = SOME (ValWord (ba + 4096w))` by fs []);
ck "load done";
(* Dec i, Dec n, Dec mid ; Assign out := mid  -> loop1 entry state sOM *)
e (qabbrev_tac `sI = s1 with locals := s1.locals |+ («i», ValWord 0w)`);
e (qabbrev_tac `sN = sI with locals := sI.locals |+ («n», ValWord 8w)`);
e (qabbrev_tac `sM = sN with locals := sN.locals |+ («mid», ValWord (ba + 2048w))`);
e (qabbrev_tac `sOM = sM with locals := sM.locals |+ («out», ValWord (ba + 2048w))`);
e (`sOM.memory = s1.memory /\ sOM.memaddrs = s1.memaddrs /\ sOM.be = s1.be /\
    sOM.structs = s1.structs /\ sOM.clock = s1.clock /\ sOM.ffi = s1.ffi /\ sOM.base_addr = ba`
     by (simp [Abbr `sOM`, Abbr `sM`, Abbr `sN`, Abbr `sI`] >> fs []));
e (`FLOOKUP sOM.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP sOM.locals «src» = SOME (ValWord (ba + 4096w)) /\
    FLOOKUP sOM.locals «mid» = SOME (ValWord (ba + 2048w)) /\
    FLOOKUP sOM.locals «out» = SOME (ValWord (ba + 2048w)) /\
    FLOOKUP sOM.locals «i» = SOME (ValWord 0w) /\
    FLOOKUP sOM.locals «n» = SOME (ValWord 8w)`
     by (simp [Abbr `sOM`, Abbr `sM`, Abbr `sN`, Abbr `sI`, FLOOKUP_UPDATE] >> fs []));
e (`reflectStaged req ba sOM`
     by (irule reflectStaged_frame >> qexists_tac `s1` >> fs []));
e (`copyInv req (ba + 4096w) (ba + 2048w) 0 sOM`
     by (irule reflectStaged_copyInv1 >> fs []));
ck "loop1 entry";
(* run loop1 (parsed while1 = copyLoopA): input(src) -> scratch(mid) *)
e (`LENGTH req <= sOM.clock` by (`sOM.clock = s0.clock` by fs [] >> fs []));
e (drule_all copyLoopA_writes >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (copyLoopA, sOM) = (NONE, sMid)`);
e (`evaluate (^whileP1, sOM) = (NONE, sMid)` by (simp [while1_eq]));
e (`FLOOKUP sMid.locals «out» = SOME (ValWord (ba + 2048w))` by fs []);
e (`sMid.base_addr = ba` by (imp_res_tac evaluate_invariants >> gvs []));
e (`sMid.clock <= sOM.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sMid.ffi.io_events = sOM.ffi.io_events`
     by (`evaluate (copyLoopA, sOM) = (NONE, sMid)` by fs [] >> drule copyLoopA_io_events >> simp []));
e (`sMid.clock = sOM.clock - LENGTH req`
     by (drule_all copyLoopA_clock >> fs []));
(* loop1's exit «i» = n2w(LENGTH req): the loop ran to completion, so the exit
   copyInv (from copyLoopA_bounded) pins «i».  copyLoopA_locals covers every var
   EXCEPT «i», so this is the one local it cannot give — and the backward-wrap
   is_valid_value check for the two-loop-only aI0 reassignment `i := 0` needs it. *)
e (`FLOOKUP sMid.locals «i» = SOME (ValWord (n2w (LENGTH req)))`
     by (drule_all copyLoopA_i_final >> strip_tac >>
         `evaluate (copyLoopA, sOM) = (NONE, sMid)` by fs [] >> gvs []));
(* loop1 preserves every local except «i» — recover «mid»/«ctrl»/«n» *)
e (`!v. v <> «i» ==> FLOOKUP sMid.locals v = FLOOKUP sOM.locals v`
     by (metis_tac [copyLoopA_locals]));
e (`FLOOKUP sMid.locals «mid» = SOME (ValWord (ba + 2048w)) /\
    FLOOKUP sMid.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP sMid.locals «n» = SOME (ValWord 8w) /\
    FLOOKUP sMid.locals «src» = SOME (ValWord (ba + 4096w))`
     by (rpt conj_tac >>
         first_assum (qspec_then `«mid»` mp_tac) >>
         first_assum (qspec_then `«ctrl»` mp_tac) >>
         first_assum (qspec_then `«n»` mp_tac) >>
         first_x_assum (qspec_then `«src»` mp_tac) >> simp [] >> fs []));
ck "loop1 done";
(* Assign src:=mid ; out:=ctrl+32 ; i:=0  -> loop2 entry state sRe *)
e (qabbrev_tac `sA1 = sMid with locals := sMid.locals |+ («src», ValWord (ba + 2048w))`);
e (qabbrev_tac `sA2 = sA1 with locals := sA1.locals |+ («out», ValWord (ba + 32w))`);
e (qabbrev_tac `sRe = sA2 with locals := sA2.locals |+ («i», ValWord 0w)`);
e (`sRe.memory = sMid.memory /\ sRe.memaddrs = sMid.memaddrs /\ sRe.be = sMid.be /\
    sRe.clock = sMid.clock /\ sRe.ffi = sMid.ffi /\ sRe.base_addr = ba /\ sRe.structs = sMid.structs`
     by (simp [Abbr `sRe`, Abbr `sA2`, Abbr `sA1`] >> fs []));
e (`FLOOKUP sRe.locals «i» = SOME (ValWord 0w) /\
    FLOOKUP sRe.locals «n» = SOME (ValWord 8w) /\
    FLOOKUP sRe.locals «src» = SOME (ValWord (ba + 2048w)) /\
    FLOOKUP sRe.locals «out» = SOME (ValWord (ba + 32w))`
     by (simp [Abbr `sRe`, Abbr `sA2`, Abbr `sA1`, FLOOKUP_UPDATE] >> fs []));
(* the seam: loop1 output feeds loop2 copyInv source *)
e (qpat_x_assum `reflectStaged req ba sOM`
     (strip_assume_tac o REWRITE_RULE [reflectStaged_def]));
e (`(!j. j < LENGTH req ==> byteWritable sOM ((ba + 32w) + n2w j)) /\
    disjWords (ba + 2048w) (ba + 32w) (LENGTH req)` by fs []);
e (`n2w (LENGTH req) = (8w:word64)` by fs []);
e (`FLOOKUP sRe.locals «n» = SOME (ValWord (n2w (LENGTH req)))`
     by (qpat_x_assum `n2w (LENGTH req) = 8w` (fn th => simp [th])));
e (`copyInv req (ba + 2048w) (ba + 32w) 0 sRe`
     by (match_mp_tac (Q.INST [`src` |-> `ba + 4096w`, `mid` |-> `ba + 2048w`,
                         `s` |-> `sOM`, `out2` |-> `ba + 32w`] seam_loop2_copyInv) >>
         rpt conj_tac >> fs []));
ck "loop2 entry (SEAM)";
(* run loop2 (parsed while2 = copyLoopA): scratch(mid) -> out(ba+32) *)
e (`LENGTH req <= sRe.clock`
     by (`sRe.clock = sMid.clock` by fs [] >>
         `sMid.clock = s0.clock - LENGTH req` by (`sOM.clock = s0.clock` by fs [] >> fs []) >>
         fs []));
e (drule_all copyLoopA_writes >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (copyLoopA, sRe) = (NONE, sOut2)`);
e (`evaluate (^whileP2, sRe) = (NONE, sOut2)` by (simp [while2_eq]));
e (`FLOOKUP sOut2.locals «out» = SOME (ValWord (ba + 32w))` by fs []);
e (`!j. j < LENGTH req ==>
       mem_load_byte sOut2.memory sOut2.memaddrs sOut2.be ((ba + 32w) + n2w j)
         = SOME ((n2w (EL j req)):word8)` by fs []);
e (`sOut2.base_addr = ba` by (imp_res_tac evaluate_invariants >> gvs []));
(* loop2 clock decrease — needed by the backward-wrap Seq_thread for X10
   (loop1 establishes the analogous sMid.clock <= sOM.clock). *)
e (`sOut2.clock <= sRe.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sOut2.ffi.io_events = sRe.ffi.io_events`
     by (`evaluate (copyLoopA, sRe) = (NONE, sOut2)` by fs [] >> drule copyLoopA_io_events >> simp []));
(* io_events chain to s0 ++ loadEv.  Bare `fs []` here EXPLODES (24GB+) on the
   DOUBLED two-loop context (list-append normalisation against every memory
   predicate); every link is already an equational assumption
   (sOut2.ffi=sRe.ffi [loop2 frame], sRe.ffi=sMid.ffi, sMid.ffi.io=sOM.ffi.io
   [loop1], sOM.ffi=s1.ffi, s1.ffi.io=sSrc.ffi.io++loadEv [load], sSrc.ffi=s0.ffi),
   so a purely SYNTACTIC ASM_REWRITE chains them in bounded time. *)
e (`sOut2.ffi.io_events = s0.ffi.io_events ++ loadEv` by ASM_REWRITE_TAC []);
ck "loop2 done";
(* fire report at sOut2 (out region holds req) *)
e (qpat_x_assum `!s. FLOOKUP s.locals «out» = SOME (ValWord (s.base_addr + 32w)) /\ _ ==> _`
     (qspec_then `sOut2` mp_tac));
e (impl_tac >- (conj_tac >- fs [] >> fs []));
e (strip_tac);
(* fold n2w(LENGTH req) -> 8w in the report ORACLE call: the oracle's length arg
   is `Const (n2w (LENGTH req))` (req abstract) but the PARSED `@report_vec(out,8,
   out,8)` emits the literal `Const 8w`; without this fold the backward-wrap
   `first_assum ACCEPT_TAC` at reportSeq cannot match the parsed code (C30 folded
   the analogous constant via secHeadersBytes_length_val). *)
e (qpat_x_assum `n2w (LENGTH req) = 8w` (fn lenTh =>
     qpat_x_assum `evaluate (ExtCall «report_vec» _ _ _ _, sOut2) = _`
       (assume_tac o REWRITE_RULE [lenTh] o SIMP_RULE std_ss []) >>
     assume_tac lenTh));
e (qmatch_asmsub_rename_tac `evaluate (ExtCall «report_vec» _ _ _ _, sOut2) = (NONE, sRep)`);
(* SLIM the DOUBLED two-loop context now the report has FIRED: the byte-memory
   `!j` facts + staged/copyInv/memRel/disjWords predicates for BOTH loops are
   spent (both copyLoopA ran, report emitted).  Dropping them keeps every
   remaining trace-threading `fs []`/simp (tr, sRep.ffi, the backward wrap) fast
   on a small assumption set — the bare `fs []` list-append normalisation
   otherwise EXPLODES (24GB+) against the doubled memory context. *)
e (rpt (qpat_x_assum `!j. j < LENGTH req ==> _` kall_tac));
e (rpt (qpat_x_assum `disjWords _ _ _` kall_tac));
e (TRY (qpat_x_assum `reflectStaged req ba s1` kall_tac));
e (TRY (qpat_x_assum `reflectStaged req ba sOM` kall_tac));
e (TRY (qpat_x_assum `reflectStaged req ba sRe` kall_tac));
e (TRY (qpat_x_assum `copyInv req _ _ _ sOM` kall_tac));
e (TRY (qpat_x_assum `copyInv req _ _ _ sRe` kall_tac));
e (TRY (qpat_x_assum `memRel req _ s1` kall_tac));
e (qabbrev_tac `tr = s0.ffi.io_events ++ loadEv ++
                    [IO_event (ffi$ExtCall «report_vec»)
                       (MAP (\b. (n2w b):word8) req) rb]`);
e (`sRep.ffi.io_events = tr`
     by (simp [Abbr `tr`] >> `sOut2.ffi.io_events = s0.ffi.io_events ++ loadEv` by fs [] >> fs []));
e (`evaluate (Return (Const 0w), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def]);
e (`(empty_locals sRep).ffi.io_events = tr` by simp [empty_locals_def]);
ck "report done";
(* clock facts for the Seq_trace side-conditions *)
e (`sRep.clock <= sOut2.clock` by (qpat_x_assum `sRep.clock = _` (fn th => simp [th])));
(* ==================== backward wrap: reassemble from the leaves ==================== *)
(* retSeq / reportSeq base *)
e (`evaluate (^retSeq, sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`evaluate (^reportSeq, sOut2) = (NONE, sRep)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`evaluate (^X11, sOut2) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRep` >> rpt conj_tac >> first_assum ACCEPT_TAC));
(* while2Seq *)
e (`evaluate (^while2Seq, sRe) = (NONE, sOut2)`
     by (irule Annot_Seq >> simp [while2_eq] >> first_assum ACCEPT_TAC));
e (`evaluate (^X10, sRe) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sOut2` >> rpt conj_tac >> first_assum ACCEPT_TAC));
(* aI0 : Assign i := 0, sA2 -> sRe *)
e (`evaluate (^aI0, sA2) = (NONE, sRe)`
     by (irule Annot_Seq >>
         asm_simp_tac (srw_ss())
           [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
            shape_of_def, set_kvar_def, set_var_def, Abbr `sRe`, Abbr `sA2`,
            Abbr `sA1`, FLOOKUP_UPDATE]));
(* asm-simp rewrites sRe.clock via the `sRe.clock = sMid.clock` assumption but
   leaves sA2.clock opaque; unfold the whole abbrev chain so BOTH sides reduce to
   the same base clock (reflexive).  Same fix on the sOM/sM step below. *)
e (`sRe.clock <= sA2.clock` by (simp [Abbr `sRe`, Abbr `sA2`, Abbr `sA1`]));
e (`evaluate (^X9, sA2) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRe` >> rpt conj_tac >> first_assum ACCEPT_TAC));
(* aOut2 : Assign out := ctrl+32, sA1 -> sA2 *)
e (`FLOOKUP sA1.locals «ctrl» = SOME (ValWord ba)`
     by (simp [Abbr `sA1`, FLOOKUP_UPDATE] >> fs []));
e (`evaluate (^aOut2, sA1) = (NONE, sA2)`
     by (irule Annot_Seq >>
         asm_simp_tac (srw_ss())
           [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
            is_valid_value_def, lookup_kvar_def, shape_of_def, set_kvar_def,
            set_var_def, Abbr `sA2`, Abbr `sA1`, FLOOKUP_UPDATE]));
e (`sA2.clock <= sA1.clock` by (simp [Abbr `sA2`, Abbr `sA1`]));
e (`evaluate (^X8, sA1) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sA2` >> rpt conj_tac >> first_assum ACCEPT_TAC));
(* aSrcMid : Assign src := mid, sMid -> sA1 *)
e (`FLOOKUP sMid.locals «mid» = SOME (ValWord (ba + 2048w))` by fs []);
e (`evaluate (^aSrcMid, sMid) = (NONE, sA1)`
     by (irule Annot_Seq >>
         asm_simp_tac (srw_ss())
           [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
            shape_of_def, set_kvar_def, set_var_def, Abbr `sA1`, FLOOKUP_UPDATE]));
e (`sA1.clock <= sMid.clock` by (simp [Abbr `sA1`]));
e (`evaluate (^X7, sMid) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sA1` >> rpt conj_tac >> first_assum ACCEPT_TAC));
(* while1Seq *)
e (`evaluate (^while1Seq, sOM) = (NONE, sMid)`
     by (irule Annot_Seq >> simp [while1_eq] >> first_assum ACCEPT_TAC));
e (`evaluate (^X6, sOM) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sMid` >> rpt conj_tac >> first_assum ACCEPT_TAC));
(* aOutMid : Assign out := mid, sM -> sOM *)
e (`FLOOKUP sM.locals «mid» = SOME (ValWord (ba + 2048w))`
     by (simp [Abbr `sM`, FLOOKUP_UPDATE] >> fs []));
e (`evaluate (^aOutMid, sM) = (NONE, sOM)`
     by (irule Annot_Seq >>
         asm_simp_tac (srw_ss())
           [evaluate_def, eval_def, is_valid_value_def, lookup_kvar_def,
            shape_of_def, set_kvar_def, set_var_def, Abbr `sOM`, Abbr `sM`,
            Abbr `sN`, Abbr `sI`, FLOOKUP_UPDATE]));
e (`sOM.clock <= sM.clock` by (simp [Abbr `sOM`, Abbr `sM`, Abbr `sN`, Abbr `sI`]));
e (`evaluate (^body_m, sM) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sOM` >> rpt conj_tac >> first_assum ACCEPT_TAC));
e (`?st. evaluate (^body_m, sM) = (SOME (Return (ValWord 0w)), st) /\ st.ffi.io_events = tr`
     by (qexists_tac `empty_locals sRep` >> conj_tac >> first_assum ACCEPT_TAC));
ck "RB done";
(* ==================== wrap Decs/Annots up to reflectMainBody ==================== *)
e (`s0 with locals := s0.locals |+ («ctrl», ValWord ba) = sCtrl` by simp [Abbr `sCtrl`]);
e (`sCtrl with locals := sCtrl.locals |+ («out», ValWord (ba + 32w)) = sOut` by simp [Abbr `sOut`]);
e (`sOut with locals := sOut.locals |+ («src», ValWord (ba + 4096w)) = sSrc` by simp [Abbr `sSrc`]);
e (`s1 with locals := s1.locals |+ («i», ValWord 0w) = sI` by simp [Abbr `sI`]);
e (`sI with locals := sI.locals |+ («n», ValWord 8w) = sN` by simp [Abbr `sN`]);
e (`sN with locals := sN.locals |+ («mid», ValWord (ba + 2048w)) = sM` by simp [Abbr `sM`]);
e (`eval s0 BaseAddr = SOME (ValWord ba)` by (simp [eval_def, Abbr `ba`]));
e (`FLOOKUP sCtrl.locals «ctrl» = SOME (ValWord ba)`
     by (simp [Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (`FLOOKUP sOut.locals «ctrl» = SOME (ValWord ba)`
     by (simp [Abbr `sOut`, Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (`eval sCtrl (Op Add [Var Local «ctrl»; Const 32w]) = SOME (ValWord (ba + 32w))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]));
e (`eval sOut (Op Add [Var Local «ctrl»; Const 4096w]) = SOME (ValWord (ba + 4096w))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]));
e (`FLOOKUP sN.locals «ctrl» = SOME (ValWord ba)`
     by (simp [Abbr `sN`, Abbr `sI`, FLOOKUP_UPDATE] >> fs []));
e (`eval sN (Op Add [Var Local «ctrl»; Const 2048w]) = SOME (ValWord (ba + 2048w))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]));
e (`evaluate (^loadSeq, sSrc) = (NONE, s1)` by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`s1.clock <= sSrc.clock` by fs []);
ck "prewrap done";
(* `q by tac` STRIP_ASSUME_TAC's the proved `?st'. ...` (skolemising the witness),
   so each Dec_trace/Annot_trace/Seq_trace leaves an EXISTENTIAL `?st. ...` goal that
   first_assum ACCEPT_TAC cannot match against the skolemised assumptions — the
   `metis_tac []` fallback closes it by existential-intro from the skolem witness.
   The metis is FAST here because the context was SLIMMED right after the report
   fired (the doubled two-loop memory context — which made metis hang — is gone). *)
fun decw vq steq =
  irule Dec_trace >> qexists_tac vq >> rpt conj_tac >>
  TRY (qpat_x_assum steq (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC,
          (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, shape_of_def] >> NO_TAC),
          metis_tac [] ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
val seqldw = irule Seq_trace >> qexists_tac `s1` >> rpt conj_tac >>
             FIRST [ first_assum ACCEPT_TAC, (asm_simp_tac (srw_ss()) [] >> NO_TAC), metis_tac [] ];
e (`?st'. evaluate (^Dmid, sN) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (ba + 2048w)` `sN with locals := _ = sM`);
e (`?st'. evaluate (^body_n, sN) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dn, sI) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 8w` `sI with locals := _ = sN`);
e (`?st'. evaluate (^body_i, sI) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Di, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `s1 with locals := _ = sI`);
e (`?st'. evaluate (^AfterLoad, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^X3, sSrc) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by seqldw);
e (`?st'. evaluate (^Dsrc, sOut) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (ba + 4096w)` `sOut with locals := _ = sSrc`);
e (`?st'. evaluate (^body_o, sOut) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dout, sCtrl) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (ba + 32w)` `sCtrl with locals := _ = sOut`);
e (`?st'. evaluate (^body_c, sCtrl) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by annotw);
e (`?st'. evaluate (^Dctrl, s0) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord ba` `s0 with locals := _ = sCtrl`);
e (`?sF. evaluate (reflectMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\ sF.ffi.io_events = tr`
     by (simp [Once reflectMainBody_def] >> annotw));
ck "wrap done";
e (qexists_tac `sF` >> qexists_tac `loadEv` >> qexists_tac `rb`);
e (conj_tac >- first_assum ACCEPT_TAC);
e (qpat_x_assum `sF.ffi.io_events = tr` mp_tac >> simp [Abbr `tr`]);
val reflectMainBody_refines = top_thm ();
val _ = save_thm ("reflectMainBody_refines", reflectMainBody_refines);
val _ = print "\n@@@ reflectMainBody_refines SAVED\n";
val _ = print (thm_to_string reflectMainBody_refines);
val _ = export_theory ();

(* ===========================================================================
   C30 — the whole-`main` FFI-trace refinement for the TRANSFORM (constant
   secheaders) program.  The FUEL-BUDGETED store-loop wrapper (clock antecedent
   `LENGTH secHeadersBytes <= s0.clock`), adapting the C20 loop-wrapper template
   (ML spine peel + uniform decw/annotw/seqldw forward wrap) with the C28 store-
   loop core `copyLoopA`.  The emitted `While` is discharged in ONE step by
   `secheaders_copyLoopA_writes`; there is NO separate store (the copy loop IS
   the write) and NO memory read for the length (it is the compile-time constant
   159).  The observable is the BYTE VECTOR `MAP n2w secHeadersBytes`.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory transformCopyLoopTheory transformSecHeadersTheory
     transformWrapperTheory;
open proofManagerLib;
val _ = new_theory "transformMainRefine";
fun ck s = (print ("\n@@@ "^s^" nGoals="^Int.toString(length(top_goals()))^" @@@\n"));

(* ---- ML peel of the emitted spine (structurally guaranteed correct) ---- *)
val ty64  = fcpSyntax.mk_numeric_type (Arbnum.fromInt 64);
val mbT   = Term.inst [Type.alpha |-> ty64] (rhs (concl transformMainBody_def));
val Dctrl = rand mbT;         val body_c = rand Dctrl;     (* Seq(Annot)(Dec out ..) *)
val Dout  = rand body_c;      val body_o = rand Dout;      (* Seq(Annot)(Dec src ..) *)
val Dsrc  = rand body_o;      val X3     = rand Dsrc;      (* Seq loadSeq AfterLoad *)
val loadSeq   = rand (rator X3);   val AfterLoad = rand X3;   (* AfterLoad=Seq(Annot)(Dec i) *)
val Di    = rand AfterLoad;   val body_i = rand Di;        (* Seq(Annot)(Dec n ..) *)
val Dn    = rand body_i;      val X5     = rand Dn;        (* Seq whileSeq RestR *)
val whileSeq  = rand (rator X5);   val RestR = rand X5;
val REPORTSEQ = rand (rator RestR); val RETSEQ = rand RestR;

g `transformFFI secHeadersBytes s0 /\ s0.locals = FEMPTY /\
   LENGTH secHeadersBytes <= s0.clock ==>
   ?sF loadEv rb.
     evaluate (transformMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events =
       s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (MAP (\b. (n2w b):word8) secHeadersBytes) rb]`;
e (strip_tac);
e (qpat_x_assum `transformFFI _ _` (strip_assume_tac o SIMP_RULE std_ss [transformFFI_def]));
e (qabbrev_tac `ba = s0.base_addr`);
e (`«ctrl»<>«out» /\ «ctrl»<>«src» /\ «ctrl»<>«i» /\ «ctrl»<>«n» /\
    «out»<>«src» /\ «out»<>«i» /\ «out»<>«n» /\ «src»<>«i» /\ «src»<>«n» /\ «i»<>«n»` by EVAL_TAC);
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
(* fire the load_vec oracle at sSrc *)
e (qpat_x_assum `!s. s.base_addr = _ /\ _ ==> _` (qspec_then `sSrc` mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
ck "after L-strip";
e (qmatch_asmsub_rename_tac `evaluate (ExtCall «load_vec» _ _ _ _, sSrc) = (NONE, s1)`);
(* facts about s1 (post-load) *)
e (`s1.locals = sSrc.locals /\ s1.base_addr = ba /\ s1.clock = s0.clock`
     by fs []);
e (`transformStaged secHeadersBytes ba s1` by fs []);
e (`FLOOKUP s1.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s1.locals «out» = SOME (ValWord (ba + 32w)) /\
    FLOOKUP s1.locals «src» = SOME (ValWord (ba + 4096w))` by fs []);
ck "after s1-facts";
(* declare i, n *)
e (qabbrev_tac `sI = s1 with locals := s1.locals |+ («i», ValWord 0w)`);
e (qabbrev_tac `sN = sI with locals := sI.locals |+ («n», ValWord 159w)`);
e (`sN.memory = s1.memory /\ sN.memaddrs = s1.memaddrs /\ sN.be = s1.be /\
    sN.structs = s1.structs /\ sN.clock = s1.clock /\ sN.ffi = s1.ffi /\ sN.base_addr = ba`
     by (simp [Abbr `sN`, Abbr `sI`] >> fs []));
e (`FLOOKUP sN.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP sN.locals «out» = SOME (ValWord (ba + 32w)) /\
    FLOOKUP sN.locals «src» = SOME (ValWord (ba + 4096w)) /\
    FLOOKUP sN.locals «i» = SOME (ValWord 0w) /\
    FLOOKUP sN.locals «n» = SOME (ValWord 159w)`
     by (simp [Abbr `sN`, Abbr `sI`, FLOOKUP_UPDATE] >> fs []));
ck "states-built";
(* copyInv at sN (loop entry) — via the reusable staging frame + builder *)
e (`transformStaged secHeadersBytes ba sN`
     by (irule transformStaged_frame >> qexists_tac `s1` >> fs []));
e (`copyInv secHeadersBytes (ba + 4096w) (ba + 32w) 0 sN`
     by (irule transformStaged_copyInv >> fs [secHeadersBytes_length_val]));
e (`LENGTH secHeadersBytes <= sN.clock`
     by (`sN.clock = s0.clock` by fs [] >> fs []));
ck "copyInv-done";
(* run the store loop (ONE step: the emitted While) *)
e (drule_all secheaders_copyLoopA_writes >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (copyLoopA, sN) = (NONE, sCore)`);
e (`FLOOKUP sCore.locals «out» = SOME (ValWord (ba + 32w))` by fs []);
e (`!j. j < LENGTH secHeadersBytes ==>
       mem_load_byte sCore.memory sCore.memaddrs sCore.be ((ba+32w) + n2w j)
         = SOME ((n2w (EL j secHeadersBytes)):word8)` by fs []);
e (`sCore.clock <= sN.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sCore.base_addr = ba` by (imp_res_tac evaluate_invariants >> gvs []));
e (`sCore.ffi.io_events = s0.ffi.io_events ++ loadEv`
     by (`sCore.ffi.io_events = sN.ffi.io_events`
            by (`evaluate (copyLoopA, sN) = (NONE, sCore)` by fs [] >>
                drule copyLoopA_io_events >> simp []) >>
         `sN.ffi.io_events = s1.ffi.io_events` by (simp [Abbr `sN`, Abbr `sI`]) >>
         `s1.ffi.io_events = s0.ffi.io_events ++ loadEv` by fs [] >> fs []));
ck "core-done";
(* fire the report_vec oracle at sCore (buffer holds the bytes, «out» pinned) *)
e (qpat_x_assum `!s. FLOOKUP s.locals «out» = SOME (ValWord (s.base_addr + 32w)) /\ _ ==> _`
     (qspec_then `sCore` mp_tac));
e (impl_tac >- (conj_tac >- fs [] >> fs []));
e (strip_tac);
e (qpat_x_assum `evaluate (ExtCall «report_vec» _ _ _ _, sCore) = _`
     (assume_tac o SIMP_RULE std_ss [secHeadersBytes_length_val]));
e (qmatch_asmsub_rename_tac `evaluate (ExtCall «report_vec» _ _ _ _, sCore) = (NONE, sRep)`);
e (qabbrev_tac `tr = s0.ffi.io_events ++ loadEv ++
                    [IO_event (ffi$ExtCall «report_vec»)
                       (MAP (\b. (n2w b):word8) secHeadersBytes) rb]`);
e (`sRep.ffi.io_events = tr`
     by (simp [Abbr `tr`] >> `sCore.ffi.io_events = s0.ffi.io_events ++ loadEv` by fs [] >> fs []));
e (`evaluate (Return (Const 0w), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def]);
e (`(empty_locals sRep).ffi.io_events = tr` by simp [empty_locals_def]);
ck "report-done";
(* slim the context: the `!j` byte-memory facts + staged predicates have done
   their job (fired copyLoopA + report); dropping them keeps the remaining
   trace-threading `fs []`/`metis` calls fast on a small assumption set. *)
e (`sRep.clock <= sCore.clock`
     by (qpat_x_assum `sRep.clock = _` (fn th => simp [th])));
e (rpt (qpat_x_assum `!j. j < LENGTH secHeadersBytes ==> _` kall_tac));
e (TRY (qpat_x_assum `transformStaged secHeadersBytes ba s1` kall_tac));
e (TRY (qpat_x_assum `transformStaged secHeadersBytes ba sN` kall_tac));
e (TRY (qpat_x_assum `copyInv secHeadersBytes _ _ _ sN` kall_tac));
(* ==================== RBODY base case (terms from ML peel) ==================== *)
e (`evaluate (^RETSEQ, sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`evaluate (^REPORTSEQ, sCore) = (NONE, sRep)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`evaluate (^RestR, sCore) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRep` >> rpt conj_tac >> first_assum ACCEPT_TAC));
e (`evaluate (^whileSeq, sN) = (NONE, sCore)`
     by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`evaluate (^X5, sN) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sCore` >> rpt conj_tac >> first_assum ACCEPT_TAC));
e (`?st. evaluate (^X5, sN) = (SOME (Return (ValWord 0w)), st) /\ st.ffi.io_events = tr`
     by (qexists_tac `empty_locals sRep` >> conj_tac >> first_assum ACCEPT_TAC));
ck "RB-done";
(* ==================== wrap Decs/Annots up to transformMainBody ==================== *)
e (`s0 with locals := s0.locals |+ («ctrl», ValWord ba) = sCtrl` by simp [Abbr `sCtrl`]);
e (`sCtrl with locals := sCtrl.locals |+ («out», ValWord (ba + 32w)) = sOut` by simp [Abbr `sOut`]);
e (`sOut with locals := sOut.locals |+ («src», ValWord (ba + 4096w)) = sSrc` by simp [Abbr `sSrc`]);
e (`s1 with locals := s1.locals |+ («i», ValWord 0w) = sI` by simp [Abbr `sI`]);
e (`sI with locals := sI.locals |+ («n», ValWord 159w) = sN` by simp [Abbr `sN`]);
e (`eval s0 BaseAddr = SOME (ValWord ba)` by (simp [eval_def, Abbr `ba`]));
e (`FLOOKUP sCtrl.locals «ctrl» = SOME (ValWord ba)`
     by (simp [Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (`FLOOKUP sOut.locals «ctrl» = SOME (ValWord ba)`
     by (simp [Abbr `sOut`, Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (`eval sCtrl (Op Add [Var Local «ctrl»; Const 32w]) = SOME (ValWord (ba + 32w))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]));
e (`eval sOut (Op Add [Var Local «ctrl»; Const 4096w]) = SOME (ValWord (ba + 4096w))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]));
e (`evaluate (^loadSeq, sSrc) = (NONE, s1)` by (irule Annot_Seq >> first_assum ACCEPT_TAC));
e (`s1.clock <= sSrc.clock` by fs []);
ck "prewrap-done";
(* DETERMINISTIC wrap (no metis/fs fallbacks — keeps each step fast regardless of
   the accumulated assumption context): every Dec_trace / Annot_trace / Seq_trace
   subgoal is discharged by a specific pre-proven assumption or a tiny simp. *)
(* `q by tac` strips the intermediate `?st'` facts (STRIP_ASSUME_TAC skolemises),
   so the existential goal each trace-lemma leaves is reassembled by `metis_tac []`
   (fast on the already-slimmed context) — the eval/shape/pre-proven subgoals are
   caught first by ACCEPT / simp, so metis only handles the trivial `?st` witness. *)
fun decw vq steq =
  irule Dec_trace >> qexists_tac vq >> rpt conj_tac >>
  TRY (qpat_x_assum steq (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC,
          (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, shape_of_def]
             >> NO_TAC),
          metis_tac [] ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
val seqldw = irule Seq_trace >> qexists_tac `s1` >> rpt conj_tac >>
             FIRST [ first_assum ACCEPT_TAC,
                     (asm_simp_tac (srw_ss()) [] >> NO_TAC),
                     metis_tac [] ];
e (`?st'. evaluate (^Dn, sI) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 159w` `sI with locals := _ = sN`);
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
e (`?sF. evaluate (transformMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\ sF.ffi.io_events = tr`
     by (simp [Once transformMainBody_def] >> annotw));
ck "wrap-done";
(* the `by` above STRIP_ASSUME_TAC'd the `?sF` fact, skolemising the witness as
   `sF` and adding `evaluate .. = (.., sF)` + `sF.ffi.io_events = tr`. *)
e (qexists_tac `sF` >> qexists_tac `loadEv` >> qexists_tac `rb`);
e (conj_tac >- first_assum ACCEPT_TAC);
e (qpat_x_assum `sF.ffi.io_events = tr` mp_tac >> simp [Abbr `tr`]);
val transformMainBody_refines = top_thm ();
val _ = save_thm ("transformMainBody_refines", transformMainBody_refines);
val _ = print "\n@@@ transformMainBody_refines SAVED\n";
val _ = print (thm_to_string transformMainBody_refines);
val _ = print "\n@@@ TAILDONE\n";
val _ = export_theory ();

(* ===========================================================================
   C20 — the whole-`main` FFI-trace refinement for the deployed cache-key hash.
   The FUEL-BUDGETED loop wrapper (clock antecedent `LENGTH input <= s0.clock`),
   adapting the C18 loop-free template (ML spine peel + uniform decw/annotw/seqldw
   forward wrap) with the C13 clock budget and the C20 loop core.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory hashBytesLoopTheory hashCoreTheory c14GenericTheory
     hashWrapperLinkATheory;
open proofManagerLib;
val _ = new_theory "hashMainRefine";
fun ck s = (print ("\n@@@ "^s^" nGoals="^Int.toString(length(top_goals()))^" @@@\n"));

(* ---- ML peel of the emitted spine ---- *)
val ty64  = fcpSyntax.mk_numeric_type (Arbnum.fromInt 64);
val mbT   = Term.inst [Type.alpha |-> ty64] (rhs (concl hashMainBody_def));
val Dctrl = rand mbT;      val body_c = rand Dctrl;
val Dbase = rand body_c;   val SEQld  = rand Dbase;
val loadSeq = rand (rator SEQld);   val AL = rand SEQld;
val Dlen  = rand AL;       val Alen  = rand Dlen;
val Dacc  = rand Alen;     val Aacc  = rand Dacc;
val Di    = rand Aacc;     val Ai    = rand Di;
val Db    = rand Ai;       val RBODY = rand Db;
val CORE  = rand (rator RBODY);  val REST1 = rand RBODY;
val STORE = rand (rator REST1);  val REST2 = rand REST1;
val REPORT= rand (rator REST2);  val RETURN= rand REST2;

g `hashFFI input s0 /\ s0.locals = FEMPTY /\ LENGTH input <= s0.clock ==>
   ?sF loadEv rb.
     evaluate (hashMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\
     sF.ffi.io_events =
       s0.ffi.io_events ++ loadEv ++
       [IO_event (ffi$ExtCall «report_vec»)
          (word_to_bytes (n2w (hashBytesN input) : word64) F) rb]`;
e (strip_tac);
e (qpat_x_assum `hashFFI _ _` (strip_assume_tac o SIMP_RULE std_ss [hashFFI_def]));
e (qabbrev_tac `ba = s0.base_addr`);
e (`«ctrl»<>«base» /\ «ctrl»<>«len» /\ «ctrl»<>«acc» /\ «ctrl»<>«i» /\ «ctrl»<>«b» /\
    «base»<>«len» /\ «base»<>«acc» /\ «base»<>«i» /\ «base»<>«b» /\
    «len»<>«acc» /\ «len»<>«i» /\ «len»<>«b» /\ «acc»<>«i» /\ «acc»<>«b» /\ «i»<>«b»` by EVAL_TAC);
e (qabbrev_tac `sCtrl = s0 with locals := s0.locals |+ («ctrl», ValWord ba)`);
e (qabbrev_tac `sBase = sCtrl with locals := sCtrl.locals |+ («base», ValWord (ba + 32w))`);
e (`sBase.base_addr = ba /\ sBase.clock = s0.clock /\ sBase.memory = s0.memory /\
    sBase.memaddrs = s0.memaddrs /\ sBase.be = s0.be /\ sBase.ffi = s0.ffi /\ sBase.structs = s0.structs`
     by simp [Abbr `sBase`, Abbr `sCtrl`, Abbr `ba`]);
e (`FLOOKUP sBase.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP sBase.locals «base» = SOME (ValWord (ba + 32w))`
     by (simp [Abbr `sBase`, Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (qpat_x_assum `!s. _ ==> _` (qspec_then `sBase` mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
ck "after L-strip";
(* facts about s1 (post-load) *)
e (`ba IN s1.memaddrs /\ s1.memory ba = Word (n2w (LENGTH input)) /\
    (ba+8w) IN s1.memaddrs /\ memRel input (ba+32w) s1 /\
    LENGTH input < 2n**63 /\ EVERY (\x. x<256) input`
     by (fs [hashCtrlStaged_def]));
e (`FLOOKUP s1.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s1.locals «base» = SOME (ValWord (ba+32w))`
     by (`s1.locals = sBase.locals` by fs [] >> fs []));
ck "after s1-facts";
(* read len; declare acc, i, b *)
e (`eval s1 (Load One (Var Local «ctrl»)) = SOME (ValWord (n2w (LENGTH input)))`
     by (irule eval_load_ctrlc >> qexists_tac `ba` >> fs []));
e (qabbrev_tac `sLen = s1 with locals := s1.locals |+ («len», ValWord (n2w (LENGTH input)))`);
e (qabbrev_tac `sAcc = sLen with locals := sLen.locals |+ («acc», ValWord 0w)`);
e (qabbrev_tac `sI = sAcc with locals := sAcc.locals |+ («i», ValWord 0w)`);
e (qabbrev_tac `sB0 = sI with locals := sI.locals |+ («b», ValWord 0w)`);
e (`sB0.memory = s1.memory /\ sB0.memaddrs = s1.memaddrs /\ sB0.be = s1.be /\
    sB0.structs = s1.structs /\ sB0.clock = s1.clock /\ sB0.ffi = s1.ffi /\ sB0.base_addr = ba`
     by (simp [Abbr `sB0`, Abbr `sI`, Abbr `sAcc`, Abbr `sLen`] >> fs []));
e (`FLOOKUP sB0.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP sB0.locals «base» = SOME (ValWord (ba+32w)) /\
    FLOOKUP sB0.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
    FLOOKUP sB0.locals «acc» = SOME (ValWord 0w) /\
    FLOOKUP sB0.locals «i» = SOME (ValWord 0w) /\
    FLOOKUP sB0.locals «b» = SOME (ValWord 0w)`
     by (simp [Abbr `sB0`, Abbr `sI`, Abbr `sAcc`, Abbr `sLen`, FLOOKUP_UPDATE] >> fs []));
ck "states-built";
(* foldInv at sB0 *)
e (`memRel input (ba+32w) sB0` by (gvs [memRel_def, Abbr `sB0`, Abbr `sI`, Abbr `sAcc`, Abbr `sLen`] >> fs [memRel_def]));
e (`foldInv input (ba+32w) 0 0w sB0`
     by (simp [foldInv_def] >> fs [] >> metis_tac []));
e (`LENGTH input <= sB0.clock`
     by (`sB0.clock = s0.clock` by (fs [] >> `s1.clock = sBase.clock` by fs [] >> fs []) >> fs []));
ck "foldInv-done";
(* run the loop core *)
e (drule evaluate_hashLoopCore_framed >> disch_then drule >> strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (hashLoopCore, sB0) = (NONE, sCore)`);
e (qabbrev_tac `wstar = n2w (hashBytesN input) : word64`);
e (`FLOOKUP sCore.locals «acc» = SOME (ValWord wstar)` by fs [Abbr `wstar`]);
e (`FLOOKUP sCore.locals «ctrl» = SOME (ValWord ba)` by fs []);
e (`sCore.clock <= sB0.clock` by (imp_res_tac evaluate_clock >> fs []));
e (`sCore.memaddrs = s1.memaddrs /\ sCore.base_addr = ba`
     by (imp_res_tac evaluate_invariants >> gvs []));
e (`sCore.ffi.io_events = s0.ffi.io_events ++ loadEv`
     by (`sCore.ffi.io_events = sB0.ffi.io_events`
            by (`evaluate (hashLoopCore, sB0) = (NONE, sCore)` by fs [] >>
                drule noFFI_io_events >> simp [hashLoopCore_noFFI]) >>
         `sB0.ffi.io_events = s0.ffi.io_events ++ loadEv` by fs [] >> fs []));
ck "core-done";
(* Store / report / Return *)
e (`(ba + 8w) IN sCore.memaddrs` by gvs []);
e (qabbrev_tac `sS = sCore with memory := ((ba + 8w) =+ Word wstar) sCore.memory`);
e (`evaluate (Store (Op Add [Var Local «ctrl»; Const 8w]) (Var Local «acc»), sCore) = (NONE, sS)`
     by (simp [Abbr `sS`] >> irule evaluate_store_ctrl_acc >> fs []));
e (`sS.base_addr = ba /\ sS.memaddrs = sCore.memaddrs /\ sS.locals = sCore.locals /\
    sS.clock = sCore.clock /\ sS.ffi = sCore.ffi` by simp [Abbr `sS`]);
e (`FLOOKUP sS.locals «ctrl» = SOME (ValWord sS.base_addr)` by gvs []);
e (`(sS.base_addr + 8w) IN sS.memaddrs` by gvs []);
e (`sS.memory (sS.base_addr + 8w) = Word wstar` by gvs [Abbr `sS`, combinTheory.APPLY_UPDATE_THM]);
ck "store-done";
e (qpat_x_assum `!s w. _` (qspecl_then [`sS`, `wstar`] mp_tac));
e (impl_tac >- fs []);
e (strip_tac);
e (qmatch_asmsub_rename_tac `evaluate (ExtCall «report_vec» _ _ _ _, sS) = (NONE, sRep)`);
e (`sS.ffi.io_events = s0.ffi.io_events ++ loadEv` by fs []);
e (qabbrev_tac `tr = s0.ffi.io_events ++ loadEv ++
                    [IO_event (ffi$ExtCall «report_vec») (word_to_bytes wstar F) rb]`);
e (`sRep.ffi.io_events = tr` by (simp [Abbr `tr`] >> fs []));
e (`evaluate (Return (Const 0w), sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def]);
e (`(empty_locals sRep).ffi.io_events = tr` by simp [empty_locals_def]);
ck "report-done";
(* RBODY base case *)
e (`evaluate (^RETURN, sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Annot_Seq >> fs []));
e (`evaluate (^REPORT, sS) = (NONE, sRep)` by (irule Annot_Seq >> fs []));
e (`evaluate (^REST2, sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sRep` >> fs []));
e (`evaluate (^STORE, sCore) = (NONE, sS)` by (irule Annot_Seq >> fs []));
e (`evaluate (^REST1, sCore) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sS` >> fs []));
e (`evaluate (^CORE, sB0) = (NONE, sCore)` by (irule Annot_Seq >> fs []));
e (`evaluate (^RBODY, sB0) = (SOME (Return (ValWord 0w)), empty_locals sRep)`
     by (irule Seq_thread >> qexists_tac `sCore` >> fs []));
e (`?st. evaluate (^RBODY, sB0) = (SOME (Return (ValWord 0w)), st) /\ st.ffi.io_events = tr`
     by (qexists_tac `empty_locals sRep` >> fs []));
ck "RB-done";
(* wrap Decs/Annots up to hashMainBody *)
e (`s0 with locals := s0.locals |+ («ctrl», ValWord ba) = sCtrl` by simp [Abbr `sCtrl`]);
e (`sCtrl with locals := sCtrl.locals |+ («base», ValWord (ba + 32w)) = sBase` by simp [Abbr `sBase`]);
e (`s1 with locals := s1.locals |+ («len», ValWord (n2w (LENGTH input))) = sLen` by simp [Abbr `sLen`]);
e (`sLen with locals := sLen.locals |+ («acc», ValWord 0w) = sAcc` by simp [Abbr `sAcc`]);
e (`sAcc with locals := sAcc.locals |+ («i», ValWord 0w) = sI` by simp [Abbr `sI`]);
e (`sI with locals := sI.locals |+ («b», ValWord 0w) = sB0` by simp [Abbr `sB0`]);
e (`eval s0 BaseAddr = SOME (ValWord ba)` by (simp [eval_def, Abbr `ba`]));
e (`FLOOKUP sCtrl.locals «ctrl» = SOME (ValWord ba)` by (simp [Abbr `sCtrl`, FLOOKUP_UPDATE] >> fs []));
e (`eval sCtrl (Op Add [Var Local «ctrl»; Const 32w]) = SOME (ValWord (ba + 32w))`
     by (irule eval_ctrl_add >> fs []));
e (`evaluate (^loadSeq, sBase) = (NONE, s1)` by (irule Annot_Seq >> first_assum ACCEPT_TAC));
ck "prewrap-done";
fun decw vq steq =
  irule Dec_trace >> qexists_tac vq >> rpt conj_tac >>
  TRY (qpat_x_assum steq (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC, (simp [eval_def, shape_of_def] >> NO_TAC), (metis_tac []) ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
val seqldw = irule Seq_trace >> qexists_tac `s1` >> rpt conj_tac >>
             FIRST [ first_assum ACCEPT_TAC, (fs [] >> NO_TAC), (metis_tac []) ];
e (`?st'. evaluate (^Db, sI) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `sI with locals := _ = sB0`);
e (`?st'. evaluate (^Ai, sI) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr` by annotw);
e (`?st'. evaluate (^Di, sAcc) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `sAcc with locals := _ = sI`);
e (`?st'. evaluate (^Aacc, sAcc) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr` by annotw);
e (`?st'. evaluate (^Dacc, sLen) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord 0w` `sLen with locals := _ = sAcc`);
e (`?st'. evaluate (^Alen, sLen) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr` by annotw);
e (`?st'. evaluate (^Dlen, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (n2w (LENGTH input))` `s1 with locals := _ = sLen`);
e (`?st'. evaluate (^AL, s1) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr` by annotw);
e (`?st'. evaluate (^SEQld, sBase) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr` by seqldw);
e (`?st'. evaluate (^Dbase, sCtrl) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord (ba + 32w)` `sCtrl with locals := _ = sBase`);
e (`?st'. evaluate (^body_c, sCtrl) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr` by annotw);
e (`?st'. evaluate (^Dctrl, s0) = (SOME (Return (ValWord 0w)), st') /\ st'.ffi.io_events = tr`
     by decw `ValWord ba` `s0 with locals := _ = sCtrl`);
e (`?sF. evaluate (hashMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\ sF.ffi.io_events = tr`
     by (simp [Once hashMainBody_def] >> annotw));
ck "wrap-done";
e (pop_assum strip_assume_tac);
e (qexists_tac `sF` >> qexists_tac `loadEv` >> qexists_tac `rb`);
e (conj_tac >- first_assum ACCEPT_TAC);
e (fs [Abbr `tr`, Abbr `wstar`]);
val hashMainBody_refines = top_thm ();
val _ = save_thm ("hashMainBody_refines", hashMainBody_refines);
val _ = export_theory ();

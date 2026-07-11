(* ===========================================================================
   C22 — the COMPOSED whole-program wrapper for the deployed cacheEmptyStage
   cache-key path.  MainRefine is BESPOKE (the two-fold + gate spine that
   mk_foldWrapper's single-fold peeler cannot take); Sem + Install + EndToEnd
   are the uniform C21-generator template tail, reused verbatim in shape.
   Closes `cacheKey_machine_code`: spec -> machine code, leanc out of the TCB.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse proofManagerLib markerLib;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory pairTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory c14GenericTheory foldWrapCommonTheory
     panAutoTheory cacheKeyCoreTheory cacheKeyFrameTheory cacheKeyDataTheory
     cacheKeyLinkBInstTheory;

val _ = new_theory "cacheKeyGen";

fun QS s = [QUOTE s] : term frag list;
fun EB q tac = ignore (e (q by tac));
val ABB = fn nm => Abbr (QS nm);
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;

(* ---- ML peel of the composed spine ---- *)
val mbT   = inst64 (rhs (concl cacheMainBody_def));
val Dctrl = rand mbT;      val body_c = rand Dctrl;
val Dbase = rand body_c;   val SEQld  = rand Dbase;
val loadSeq = rand (rator SEQld);   val AL = rand SEQld;
val Dlen  = rand AL;       val Alen  = rand Dlen;
val Dacc  = rand Alen;     val Aacc  = rand Dacc;
val Di    = rand Aacc;     val Ai    = rand Di;
val Db    = rand Ai;       val RB1   = rand Db;
val CORE1 = rand (rator RB1);   val Akm = rand RB1;
val Dkm   = rand Akm;      val KmBody = rand Dkm;
val AsgB  = rand (rator KmBody); val KmR1 = rand KmBody;
val AsgL  = rand (rator KmR1);   val KmR2 = rand KmR1;
val AsgA  = rand (rator KmR2);   val KmR3 = rand KmR2;
val AsgI  = rand (rator KmR3);   val KmR4 = rand KmR3;
val AsgBz = rand (rator KmR4);   val KmR5 = rand KmR4;
val CORE2 = rand (rator KmR5);   val Aku = rand KmR5;
val Dku   = rand Aku;      val KuBody = rand Dku;
val Dage  = rand KuBody;   val AgeBody = rand Dage;
val Ddec  = rand AgeBody;  val DecBody = rand Ddec;
val GATEN = rand (rator DecBody); val AfterGate = rand DecBody;
val STOREN= rand (rator AfterGate); val AfterStore = rand AfterGate;
val REPORTN=rand (rator AfterStore);val RETURNN = rand AfterStore;
fun AQ t = [ANTIQUOTE t];
fun AQg pre t post = [QUOTE pre, ANTIQUOTE t, QUOTE post];

(* ================= MainRefine (bespoke) ================= *)
val _ = g (QS (
  "cacheFFI method tgt age s0 /\\ s0.locals = FEMPTY /\\\n" ^
  " LENGTH method + LENGTH tgt <= s0.clock ==>\n" ^
  " ?sF loadEv rb.\n" ^
  "   evaluate (cacheMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\\\n" ^
  "   sF.ffi.io_events = s0.ffi.io_events ++ loadEv ++\n" ^
  "     [IO_event (ffi$ExtCall «report_vec»)\n" ^
  "        (word_to_bytes (n2w (cacheServe method tgt age) : word64) F) rb]"));
val _ = e strip_tac;
val _ = e (qpat_x_assum (QS "cacheFFI _ _ _ _") (strip_assume_tac o SIMP_RULE std_ss [cacheFFI_def]));
val _ = e (qabbrev_tac (QS "ba = s0.base_addr"));
val _ = EB (QS (
  "«ctrl»<>«base» /\\ «ctrl»<>«len» /\\ «ctrl»<>«acc» /\\ «ctrl»<>«i» /\\ «ctrl»<>«b» /\\ " ^
  "«ctrl»<>«km» /\\ «ctrl»<>«ku» /\\ «ctrl»<>«age» /\\ «ctrl»<>«dec» /\\ " ^
  "«base»<>«len» /\\ «base»<>«acc» /\\ «base»<>«i» /\\ «base»<>«b» /\\ «base»<>«km» /\\ " ^
  "«base»<>«ku» /\\ «base»<>«age» /\\ «base»<>«dec» /\\ " ^
  "«len»<>«acc» /\\ «len»<>«i» /\\ «len»<>«b» /\\ «len»<>«km» /\\ «len»<>«ku» /\\ «len»<>«age» /\\ «len»<>«dec» /\\ " ^
  "«acc»<>«i» /\\ «acc»<>«b» /\\ «acc»<>«km» /\\ «acc»<>«ku» /\\ «acc»<>«age» /\\ «acc»<>«dec» /\\ " ^
  "«i»<>«b» /\\ «i»<>«km» /\\ «i»<>«ku» /\\ «i»<>«age» /\\ «i»<>«dec» /\\ " ^
  "«b»<>«km» /\\ «b»<>«ku» /\\ «b»<>«age» /\\ «b»<>«dec» /\\ " ^
  "«km»<>«ku» /\\ «km»<>«age» /\\ «km»<>«dec» /\\ «ku»<>«age» /\\ «ku»<>«dec» /\\ «age»<>«dec»")) EVAL_TAC;

(* -- prelude: ctrl, base, load -- *)
val _ = e (qabbrev_tac (QS "sCtrl = s0 with locals := s0.locals |+ («ctrl», ValWord ba)"));
val _ = e (qabbrev_tac (QS "sBase = sCtrl with locals := sCtrl.locals |+ («base», ValWord (ba + 64w))"));
val _ = EB (QS (
  "sBase.base_addr = ba /\\ sBase.clock = s0.clock /\\ sBase.memory = s0.memory /\\ " ^
  "sBase.memaddrs = s0.memaddrs /\\ sBase.be = s0.be /\\ sBase.ffi = s0.ffi /\\ sBase.structs = s0.structs"))
  (simp [ABB "sBase", ABB "sCtrl", ABB "ba"]);
val _ = EB (QS (
  "FLOOKUP sBase.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP sBase.locals «base» = SOME (ValWord (ba + 64w))"))
  (simp [ABB "sBase", ABB "sCtrl", FLOOKUP_UPDATE] >> fs []);
val _ = e (qpat_x_assum (QS "!s. _ ==> _") (qspec_then (QS "sBase") mp_tac));
val _ = e (impl_tac >- fs []);
val _ = e strip_tac;
val _ = EB (QS (
  "ba IN s1.memaddrs /\\ s1.memory ba = Word (n2w (LENGTH method)) /\\ " ^
  "(ba+8w) IN s1.memaddrs /\\ s1.memory (ba+8w) = Word (n2w (LENGTH tgt)) /\\ " ^
  "(ba+16w) IN s1.memaddrs /\\ s1.memory (ba+16w) = Word (n2w age) /\\ " ^
  "(ba+24w) IN s1.memaddrs /\\ memRel method (ba+64w) s1 /\\ memRel tgt (ba+2112w) s1 /\\ " ^
  "LENGTH method < 2n**63 /\\ LENGTH tgt < 2n**63 /\\ age < 4294967296 /\\ " ^
  "EVERY (\\x. x<256) method /\\ EVERY (\\x. x<256) tgt"))
  (fs [cacheStaged_def]);
val _ = EB (QS (
  "FLOOKUP s1.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP s1.locals «base» = SOME (ValWord (ba+64w))"))
  ((QS "s1.locals = sBase.locals") by (fs []) >> fs []);

(* -- fold 1 setup: read method len, Dec len/acc/i/b -- *)
val _ = EB (QS "eval s1 (Load One (Var Local «ctrl»)) = SOME (ValWord (n2w (LENGTH method)))")
  (irule eval_load_ctrlc >> qexists_tac (QS "ba") >> fs []);
val _ = e (qabbrev_tac (QS "sLen = s1 with locals := s1.locals |+ («len», ValWord (n2w (LENGTH method)))"));
val _ = e (qabbrev_tac (QS "sAcc = sLen with locals := sLen.locals |+ («acc», ValWord 0w)"));
val _ = e (qabbrev_tac (QS "sI = sAcc with locals := sAcc.locals |+ («i», ValWord 0w)"));
val _ = e (qabbrev_tac (QS "sB0 = sI with locals := sI.locals |+ («b», ValWord 0w)"));
val _ = EB (QS (
  "sB0.memory = s1.memory /\\ sB0.memaddrs = s1.memaddrs /\\ sB0.be = s1.be /\\ sB0.structs = s1.structs /\\ " ^
  "sB0.clock = s1.clock /\\ sB0.ffi = s1.ffi /\\ sB0.base_addr = ba"))
  (simp [ABB "sB0", ABB "sI", ABB "sAcc", ABB "sLen"] >> fs []);
val _ = EB (QS (
  "FLOOKUP sB0.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP sB0.locals «base» = SOME (ValWord (ba+64w)) /\\ " ^
  "FLOOKUP sB0.locals «len» = SOME (ValWord (n2w (LENGTH method))) /\\ FLOOKUP sB0.locals «acc» = SOME (ValWord 0w) /\\ " ^
  "FLOOKUP sB0.locals «i» = SOME (ValWord 0w) /\\ FLOOKUP sB0.locals «b» = SOME (ValWord 0w)"))
  (simp [ABB "sB0", ABB "sI", ABB "sAcc", ABB "sLen", FLOOKUP_UPDATE] >> fs []);
val _ = EB (QS "memRel method (ba+64w) sB0")
  (gvs [memRel_def, ABB "sB0", ABB "sI", ABB "sAcc", ABB "sLen"] >> fs [memRel_def]);
val _ = EB (QS "foldInv method (ba+64w) 0 0w sB0") (simp [foldInv_def] >> fs [] >> metis_tac []);
val _ = EB (QS "LENGTH method <= sB0.clock")
  ((QS "sB0.clock = s0.clock") by (fs [] >> (QS "s1.clock = sBase.clock") by fs [] >> fs []) >> fs []);
(* run fold 1 *)
val _ = e (drule cacheLoop1_framed >> disch_then drule >> strip_tac);
val _ = e (qmatch_asmsub_rename_tac (QS "evaluate (cacheLoop1, sB0) = (NONE, sCore1)"));
val _ = EB (QS "FLOOKUP sCore1.locals «acc» = SOME (ValWord (n2w (hashBytesN method)))") (fs []);
val _ = EB (QS "FLOOKUP sCore1.locals «ctrl» = SOME (ValWord ba)") (fs []);
val _ = EB (QS "sCore1.memory = s1.memory /\\ sCore1.memaddrs = s1.memaddrs /\\ sCore1.be = s1.be") (fs []);
val _ = EB (QS "sCore1.base_addr = ba") (imp_res_tac evaluate_invariants >> gvs []);
val _ = EB (QS "sB0.clock - LENGTH method <= sCore1.clock") (fs []);
val _ = EB (QS "sCore1.ffi.io_events = s0.ffi.io_events ++ loadEv")
  ((QS "sCore1.ffi.io_events = sB0.ffi.io_events")
      by ((QS "evaluate (cacheLoop1, sB0) = (NONE, sCore1)") by (fs []) >> drule noFFI_io_events >> simp [cacheLoop1_noFFI]) >>
   (QS "sB0.ffi.io_events = s0.ffi.io_events ++ loadEv") by (fs []) >> fs []);

(* -- expose fold-1 exit shapes (base/len/i/b) for the fold-2 reassigns -- *)
val _ = EB (QS "FLOOKUP sCore1.locals «base» = SOME (ValWord (ba + 64w))") (fs []);
val _ = EB (QS "FLOOKUP sCore1.locals «len» = SOME (ValWord (n2w (LENGTH method)))") (fs []);
val _ = EB (QS "?iw. FLOOKUP sCore1.locals «i» = SOME (ValWord iw)") (metis_tac []);
val _ = EB (QS "?bw. FLOOKUP sCore1.locals «b» = SOME (ValWord bw)") (metis_tac []);
(* -- Dec km -- *)
val _ = EB (QS "eval sCore1 (Var Local «acc») = SOME (ValWord (n2w (hashBytesN method)))") (simp [eval_def] >> fs []);
val _ = e (qabbrev_tac (QS "sKm = sCore1 with locals := sCore1.locals |+ («km», ValWord (n2w (hashBytesN method)))"));
val _ = EB (QS (
  "sKm.memory = s1.memory /\\ sKm.memaddrs = s1.memaddrs /\\ sKm.be = s1.be /\\ sKm.base_addr = ba /\\ " ^
  "sKm.clock = sCore1.clock /\\ sKm.ffi = sCore1.ffi /\\ FLOOKUP sKm.locals «ctrl» = SOME (ValWord ba) /\\ " ^
  "FLOOKUP sKm.locals «base» = SOME (ValWord (ba + 64w)) /\\ " ^
  "FLOOKUP sKm.locals «len» = SOME (ValWord (n2w (LENGTH method))) /\\ " ^
  "FLOOKUP sKm.locals «acc» = SOME (ValWord (n2w (hashBytesN method))) /\\ " ^
  "(?iw. FLOOKUP sKm.locals «i» = SOME (ValWord iw)) /\\ (?bw. FLOOKUP sKm.locals «b» = SOME (ValWord bw)) /\\ " ^
  "FLOOKUP sKm.locals «km» = SOME (ValWord (n2w (hashBytesN method)))"))
  (simp [ABB "sKm", FLOOKUP_UPDATE] >> fs [] >> metis_tac []);
(* -- reassign base := ctrl+2112 -- *)
val _ = EB (QS "eval sKm (Op Add [Var Local «ctrl»; Const 2112w]) = SOME (ValWord (ba + 2112w))")
  (irule eval_ctrl_add >> fs []);
val _ = e (qabbrev_tac (QS "sRB = sKm with locals := sKm.locals |+ («base», ValWord (ba + 2112w))"));
val _ = EB (QS "evaluate (Assign Local «base» (Op Add [Var Local «ctrl»; Const 2112w]), sKm) = (NONE, sRB)")
  ((QS "FLOOKUP sKm.locals «base» = SOME (ValWord (ba + 64w))") by fs [] >>
   (QS "eval sKm (Op Add [Var Local «ctrl»; Const 2112w]) = SOME (ValWord (ba + 2112w))") by (irule eval_ctrl_add >> fs []) >>
   (QS "evaluate (Assign Local «base» (Op Add [Var Local «ctrl»; Const 2112w]), sKm) = (NONE, set_var «base» (ValWord (ba + 2112w)) sKm)") by (irule evaluate_Assign_val >> fs []) >>
   (QS "set_var «base» (ValWord (ba + 2112w)) sKm = sRB") by simp [ABB "sRB", set_var_def] >> metis_tac []);
val _ = EB (QS (
  "sRB.memory = s1.memory /\\ sRB.memaddrs = s1.memaddrs /\\ sRB.be = s1.be /\\ sRB.base_addr = ba /\\ " ^
  "sRB.clock = sCore1.clock /\\ sRB.ffi = sCore1.ffi /\\ FLOOKUP sRB.locals «ctrl» = SOME (ValWord ba) /\\ " ^
  "FLOOKUP sRB.locals «len» = SOME (ValWord (n2w (LENGTH method))) /\\ " ^
  "FLOOKUP sRB.locals «acc» = SOME (ValWord (n2w (hashBytesN method))) /\\ " ^
  "(?iw. FLOOKUP sRB.locals «i» = SOME (ValWord iw)) /\\ (?bw. FLOOKUP sRB.locals «b» = SOME (ValWord bw)) /\\ " ^
  "FLOOKUP sRB.locals «km» = SOME (ValWord (n2w (hashBytesN method)))"))
  (simp [ABB "sRB", FLOOKUP_UPDATE] >> fs [] >> metis_tac []);
(* -- reassign len := lds (ctrl+8) -- *)
val _ = EB (QS "(ba + 8w) IN sRB.memaddrs") (metis_tac []);
val _ = EB (QS "sRB.memory (ba + 8w) = Word (n2w (LENGTH tgt))") (metis_tac []);
val _ = EB (QS "eval sRB (Load One (Op Add [Var Local «ctrl»; Const 8w])) = SOME (ValWord (n2w (LENGTH tgt)))")
  (irule eval_load_ctrl_off >> qexists_tac (QS "ba") >> fs []);
val _ = e (qabbrev_tac (QS "sRL = sRB with locals := sRB.locals |+ («len», ValWord (n2w (LENGTH tgt)))"));
val _ = EB (QS "evaluate (Assign Local «len» (Load One (Op Add [Var Local «ctrl»; Const 8w])), sRB) = (NONE, set_var «len» (ValWord (n2w (LENGTH tgt))) sRB)")
  (irule evaluate_Assign_val >> fs []);
val _ = EB (QS "set_var «len» (ValWord (n2w (LENGTH tgt))) sRB = sRL") (simp [ABB "sRL", set_var_def]);
val _ = EB (QS "evaluate (Assign Local «len» (Load One (Op Add [Var Local «ctrl»; Const 8w])), sRB) = (NONE, sRL)") (fs []);
(* -- reassign acc := 0 -- *)
val _ = e (qabbrev_tac (QS "sRA = sRL with locals := sRL.locals |+ («acc», ValWord 0w)"));
val _ = EB (QS "evaluate (Assign Local «acc» (Const 0w), sRL) = (NONE, sRA)")
  ((QS "FLOOKUP sRL.locals «acc» = SOME (ValWord (n2w (hashBytesN method)))") by (simp [ABB "sRL", FLOOKUP_UPDATE] >> fs []) >>
   (QS "eval sRL (Const 0w) = SOME (ValWord 0w)") by simp [eval_def] >>
   (QS "evaluate (Assign Local «acc» (Const 0w), sRL) = (NONE, set_var «acc» (ValWord 0w) sRL)") by (irule evaluate_Assign_val >> fs []) >>
   (QS "set_var «acc» (ValWord 0w) sRL = sRA") by simp [ABB "sRA", set_var_def] >> metis_tac []);
(* -- reassign i := 0 -- *)
val _ = e (qabbrev_tac (QS "sRI = sRA with locals := sRA.locals |+ («i», ValWord 0w)"));
val _ = EB (QS "?iwv. FLOOKUP sRA.locals «i» = SOME (ValWord iwv)")
  (simp [ABB "sRA", ABB "sRL", FLOOKUP_UPDATE] >> metis_tac []);
val _ = EB (QS "eval sRA (Const 0w) = SOME (ValWord 0w)") (simp [eval_def]);
val _ = EB (QS "evaluate (Assign Local «i» (Const 0w), sRA) = (NONE, set_var «i» (ValWord 0w) sRA)")
  (irule evaluate_Assign_val >> metis_tac []);
val _ = EB (QS "set_var «i» (ValWord 0w) sRA = sRI") (simp [ABB "sRI", set_var_def]);
val _ = EB (QS "evaluate (Assign Local «i» (Const 0w), sRA) = (NONE, sRI)") (fs []);
(* -- reassign b := 0 -- *)
val _ = e (qabbrev_tac (QS "sRBb = sRI with locals := sRI.locals |+ («b», ValWord 0w)"));
val _ = EB (QS "?bwv. FLOOKUP sRI.locals «b» = SOME (ValWord bwv)")
  (simp [ABB "sRI", ABB "sRA", ABB "sRL", FLOOKUP_UPDATE] >> metis_tac []);
val _ = EB (QS "eval sRI (Const 0w) = SOME (ValWord 0w)") (simp [eval_def]);
val _ = EB (QS "evaluate (Assign Local «b» (Const 0w), sRI) = (NONE, set_var «b» (ValWord 0w) sRI)")
  (irule evaluate_Assign_val >> metis_tac []);
val _ = EB (QS "set_var «b» (ValWord 0w) sRI = sRBb") (simp [ABB "sRBb", set_var_def]);
val _ = EB (QS "evaluate (Assign Local «b» (Const 0w), sRI) = (NONE, sRBb)") (fs []);
val _ = EB (QS (
  "sRBb.memory = s1.memory /\\ sRBb.memaddrs = s1.memaddrs /\\ sRBb.be = s1.be /\\ " ^
  "sRBb.base_addr = ba /\\ sRBb.clock = sCore1.clock /\\ sRBb.ffi = sCore1.ffi"))
  (simp [ABB "sRBb", ABB "sRI", ABB "sRA", ABB "sRL"] >> fs []);
val _ = EB (QS (
  "FLOOKUP sRBb.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP sRBb.locals «base» = SOME (ValWord (ba+2112w)) /\\ " ^
  "FLOOKUP sRBb.locals «len» = SOME (ValWord (n2w (LENGTH tgt))) /\\ FLOOKUP sRBb.locals «acc» = SOME (ValWord 0w) /\\ " ^
  "FLOOKUP sRBb.locals «i» = SOME (ValWord 0w) /\\ FLOOKUP sRBb.locals «b» = SOME (ValWord 0w) /\\ " ^
  "FLOOKUP sRBb.locals «km» = SOME (ValWord (n2w (hashBytesN method)))"))
  (simp [ABB "sRBb", ABB "sRI", ABB "sRA", ABB "sRL", ABB "sRB", FLOOKUP_UPDATE] >> fs []);
val _ = EB (QS "memRel tgt (ba+2112w) sRBb")
  (gvs [memRel_def, ABB "sRBb", ABB "sRI", ABB "sRA", ABB "sRL", ABB "sRB"] >> fs [memRel_def]);
val _ = EB (QS "foldInv tgt (ba+2112w) 0 0w sRBb") (simp [foldInv_def] >> fs [] >> metis_tac []);
val _ = EB (QS "LENGTH tgt <= sRBb.clock")
  ((QS "sRBb.clock = sCore1.clock") by fs [] >>
   (QS "sB0.clock = s0.clock") by (fs [] >> (QS "s1.clock = sBase.clock") by fs [] >> fs []) >> fs []);
(* run fold 2 *)
val _ = e (drule cacheLoop2_framed >> disch_then drule >> strip_tac);
val _ = e (qmatch_asmsub_rename_tac (QS "evaluate (cacheLoop2, sRBb) = (NONE, sCore2)"));
val _ = EB (QS "FLOOKUP sCore2.locals «acc» = SOME (ValWord (n2w (hashBytesN tgt)))") (fs []);
val _ = EB (QS "FLOOKUP sCore2.locals «ctrl» = SOME (ValWord ba)") (fs []);
val _ = EB (QS "FLOOKUP sCore2.locals «km» = SOME (ValWord (n2w (hashBytesN method)))") (fs []);
val _ = EB (QS "sCore2.memory = s1.memory") ((QS "sCore2.memory = sRBb.memory") by fs [] >> fs []);
val _ = EB (QS "sCore2.memaddrs = s1.memaddrs /\\ sCore2.base_addr = ba") (imp_res_tac evaluate_invariants >> gvs []);
val _ = EB (QS "sCore2.ffi.io_events = s0.ffi.io_events ++ loadEv")
  ((QS "sCore2.ffi.io_events = sRBb.ffi.io_events")
      by ((QS "evaluate (cacheLoop2, sRBb) = (NONE, sCore2)") by (fs []) >> drule noFFI_io_events >> simp [cacheLoop2_noFFI]) >>
   (QS "sRBb.ffi = sCore1.ffi") by fs [] >> (QS "sCore1.ffi.io_events = s0.ffi.io_events ++ loadEv") by fs [] >> fs []);

(* -- Dec ku, age, dec -- *)
val _ = EB (QS "eval sCore2 (Var Local «acc») = SOME (ValWord (n2w (hashBytesN tgt)))") (simp [eval_def] >> fs []);
val _ = e (qabbrev_tac (QS "sKu = sCore2 with locals := sCore2.locals |+ («ku», ValWord (n2w (hashBytesN tgt)))"));
val _ = EB (QS (
  "sKu.memory = s1.memory /\\ sKu.memaddrs = s1.memaddrs /\\ sKu.base_addr = ba /\\ sKu.clock = sCore2.clock /\\ " ^
  "sKu.ffi = sCore2.ffi /\\ FLOOKUP sKu.locals «ctrl» = SOME (ValWord ba) /\\ " ^
  "FLOOKUP sKu.locals «km» = SOME (ValWord (n2w (hashBytesN method))) /\\ " ^
  "FLOOKUP sKu.locals «ku» = SOME (ValWord (n2w (hashBytesN tgt)))"))
  (simp [ABB "sKu", FLOOKUP_UPDATE] >> fs []);
val _ = EB (QS "(ba + 16w) IN sKu.memaddrs") (metis_tac []);
val _ = EB (QS "sKu.memory (ba + 16w) = Word (n2w age)") (metis_tac []);
val _ = EB (QS "eval sKu (Load One (Op Add [Var Local «ctrl»; Const 16w])) = SOME (ValWord (n2w age))")
  (irule eval_load_ctrl_off >> qexists_tac (QS "ba") >> fs []);
val _ = e (qabbrev_tac (QS "sAge = sKu with locals := sKu.locals |+ («age», ValWord (n2w age))"));
val _ = e (qabbrev_tac (QS "sDec = sAge with locals := sAge.locals |+ («dec», ValWord 0w)"));
val _ = EB (QS (
  "sDec.memory = s1.memory /\\ sDec.memaddrs = s1.memaddrs /\\ sDec.base_addr = ba /\\ sDec.clock = sCore2.clock /\\ " ^
  "sDec.ffi = sCore2.ffi /\\ FLOOKUP sDec.locals «ctrl» = SOME (ValWord ba) /\\ " ^
  "FLOOKUP sDec.locals «km» = SOME (ValWord (n2w (hashBytesN method))) /\\ " ^
  "FLOOKUP sDec.locals «ku» = SOME (ValWord (n2w (hashBytesN tgt))) /\\ " ^
  "FLOOKUP sDec.locals «age» = SOME (ValWord (n2w age)) /\\ FLOOKUP sDec.locals «dec» = SOME (ValWord 0w)"))
  (simp [ABB "sDec", ABB "sAge", ABB "sKu", FLOOKUP_UPDATE] >> fs []);
(* run the gate *)
val _ = EB (QS (
  "?sG. evaluate (cacheGate, sDec) = (NONE, sG) /\\ " ^
  "FLOOKUP sG.locals «dec» = SOME (ValWord (n2w (cacheServe method tgt age))) /\\ " ^
  "(!v. v <> «dec» ==> FLOOKUP sG.locals v = FLOOKUP sDec.locals v) /\\ " ^
  "sG.ffi = sDec.ffi /\\ sG.memory = sDec.memory /\\ sG.memaddrs = sDec.memaddrs /\\ " ^
  "sG.clock = sDec.clock /\\ sG.base_addr = sDec.base_addr"))
  (irule evaluate_cacheGate >> fs []);
val _ = e (pop_assum strip_assume_tac);
val _ = EB (QS "FLOOKUP sG.locals «ctrl» = SOME (ValWord ba)")
  (first_x_assum (qspec_then (QS "«ctrl»") mp_tac) >> impl_tac >- EVAL_TAC >> fs []);
val _ = EB (QS "sG.base_addr = ba /\\ sG.memory = s1.memory /\\ sG.memaddrs = s1.memaddrs /\\ sG.ffi = sCore2.ffi") (fs []);
(* store the decision at ctrl+24 *)
val _ = EB (QS "(ba+24w) IN sG.memaddrs") (metis_tac []);
val _ = e (qabbrev_tac (QS "sS = sG with memory := ((ba + 24w) =+ Word (n2w (cacheServe method tgt age))) sG.memory"));
val _ = EB (QS "FLOOKUP sG.locals «dec» = SOME (ValWord (n2w (cacheServe method tgt age)))") (fs []);
val _ = EB (QS "FLOOKUP sG.locals «ctrl» = SOME (ValWord ba)") (fs []);
val _ = EB (QS (
  "evaluate (Store (Op Add [Var Local «ctrl»; Const 24w]) (Var Local «dec»), sG) = (NONE, sS)"))
  (`evaluate (Store (Op Add [Var Local «ctrl»; Const 24w]) (Var Local «dec»), sG) = (NONE, sG with memory := ((ba + 24w) =+ Word (n2w (cacheServe method tgt age))) sG.memory)`
      by (irule evaluate_store_ctrl_var >> metis_tac []) >>
   simp [ABB "sS"] >> metis_tac []);
val _ = EB (QS (
  "sS.base_addr = ba /\\ sS.memaddrs = sG.memaddrs /\\ sS.locals = sG.locals /\\ sS.clock = sG.clock /\\ sS.ffi = sG.ffi"))
  (simp [ABB "sS"]);
val _ = EB (QS "FLOOKUP sS.locals «ctrl» = SOME (ValWord sS.base_addr)") (gvs []);
val _ = EB (QS "(sS.base_addr + 24w) IN sS.memaddrs") (gvs []);
val _ = EB (QS "sS.memory (sS.base_addr + 24w) = Word (n2w (cacheServe method tgt age))")
  (gvs [ABB "sS", combinTheory.APPLY_UPDATE_THM]);
(* apply the report oracle *)
val _ = e (qpat_x_assum (QS "!s w. _") (qspecl_then [QS "sS", QS "n2w (cacheServe method tgt age)"] mp_tac));
val _ = e (impl_tac >- fs []);
val _ = e strip_tac;
val _ = e (qmatch_asmsub_rename_tac (QS "evaluate (ExtCall «report_vec» _ _ _ _, sS) = (NONE, sRep)"));
val _ = EB (QS "sS.ffi.io_events = s0.ffi.io_events ++ loadEv") (fs []);
val _ = e (qabbrev_tac (QS (
  "tr = s0.ffi.io_events ++ loadEv ++ " ^
  "[IO_event (ffi$ExtCall «report_vec») (word_to_bytes (n2w (cacheServe method tgt age):word64) F) rb]")));
val _ = EB (QS "sRep.ffi.io_events = tr") (simp [ABB "tr"] >> fs []);

(* ================= backward wrap ================= *)
val _ = EB (AQg "evaluate (" RETURNN ", sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
  (irule Annot_Seq >> simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def]);
val _ = EB (QS "(empty_locals sRep).ffi.io_events = tr") (simp [empty_locals_def] >> fs []);
val _ = EB (AQg "evaluate (" REPORTN ", sS) = (NONE, sRep)") (irule Annot_Seq >> fs []);
val _ = EB (AQg "evaluate (" AfterStore ", sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
  (irule Seq_thread >> qexists_tac (QS "sRep") >> fs []);
val _ = EB (AQg "evaluate (" STOREN ", sG) = (NONE, sS)") (irule Annot_Seq >> fs []);
val _ = EB (AQg "evaluate (" AfterGate ", sG) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
  (irule Seq_thread >> qexists_tac (QS "sS") >> fs []);
val _ = EB (AQg "evaluate (" GATEN ", sDec) = (NONE, sG)") (irule Annot_Seq >> fs []);
val _ = EB (AQg "evaluate (" DecBody ", sDec) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
  (irule Seq_thread >> qexists_tac (QS "sG") >> fs []);
val _ = EB (AQg "?st. evaluate (" DecBody ", sDec) = (SOME (Return (ValWord 0w)), st) /\\ st.ffi.io_events = tr")
  (qexists_tac (QS "empty_locals sRep") >> fs []);
(* wrap Dec dec / age / ku (Dec_trace) with the Annot_trace between *)
val decw = fn (vq, steq) =>
  irule Dec_trace >> qexists_tac (QS vq) >> rpt conj_tac >>
  TRY (qpat_x_assum (QS steq) (fn th => REWRITE_TAC [th])) >>
  FIRST [ first_assum ACCEPT_TAC, (simp [eval_def, shape_of_def] >> NO_TAC), (metis_tac []) ];
val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac []);
(* state equalities the decw REWRITEs need *)
val _ = EB (QS "sAge with locals := sAge.locals |+ («dec», ValWord 0w) = sDec") (simp [ABB "sDec"]);
val _ = EB (QS "sKu with locals := sKu.locals |+ («age», ValWord (n2w age)) = sAge") (simp [ABB "sAge"]);
val _ = EB (QS "sCore2 with locals := sCore2.locals |+ («ku», ValWord (n2w (hashBytesN tgt))) = sKu") (simp [ABB "sKu"]);
val _ = EB (QS "sCore1 with locals := sCore1.locals |+ («km», ValWord (n2w (hashBytesN method))) = sKm") (simp [ABB "sKm"]);
val _ = EB (QS "s1 with locals := s1.locals |+ («len», ValWord (n2w (LENGTH method))) = sLen") (simp [ABB "sLen"]);
val _ = EB (QS "sLen with locals := sLen.locals |+ («acc», ValWord 0w) = sAcc") (simp [ABB "sAcc"]);
val _ = EB (QS "sAcc with locals := sAcc.locals |+ («i», ValWord 0w) = sI") (simp [ABB "sI"]);
val _ = EB (QS "sI with locals := sI.locals |+ («b», ValWord 0w) = sB0") (simp [ABB "sB0"]);
val _ = EB (QS "s0 with locals := s0.locals |+ («ctrl», ValWord ba) = sCtrl") (simp [ABB "sCtrl"]);
val _ = EB (QS "sCtrl with locals := sCtrl.locals |+ («base», ValWord (ba + 64w)) = sBase") (simp [ABB "sBase"]);
(* Dec dec *)
val _ = EB (AQg "?st'. evaluate (" Ddec ", sAge) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord 0w", "sAge with locals := _ = sDec"));
val _ = EB (AQg "?st'. evaluate (" AgeBody ", sAge) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
(* Dec age *)
val _ = EB (AQg "?st'. evaluate (" Dage ", sKu) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord (n2w age)", "sKu with locals := _ = sAge"));
val _ = EB (AQg "?st'. evaluate (" KuBody ", sKu) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
(* Dec ku *)
val _ = EB (AQg "?st'. evaluate (" Dku ", sCore2) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord (n2w (hashBytesN tgt))", "sCore2 with locals := _ = sKu"));
val _ = EB (AQg "?st'. evaluate (" Aku ", sCore2) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
(* CORE2 = Seq(Annot)cacheLoop2 at sRBb -> sCore2 ; KmR5 = Seq CORE2 Aku *)
val _ = EB (AQg "evaluate (" CORE2 ", sRBb) = (NONE, sCore2)") (irule Annot_Seq >> fs []);
val _ = EB (AQg "?st'. evaluate (" KmR5 ", sRBb) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sCore2") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
(* Assign b/i/acc/len/base (each Seq(Annot)(Assign) threaded) *)
val _ = EB (AQg "evaluate (" AsgBz ", sRI) = (NONE, sRBb)") (irule Annot_Seq >> first_assum ACCEPT_TAC);
val _ = EB (AQg "?st'. evaluate (" KmR4 ", sRI) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sRBb") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
val _ = EB (AQg "evaluate (" AsgI ", sRA) = (NONE, sRI)") (irule Annot_Seq >> first_assum ACCEPT_TAC);
val _ = EB (AQg "?st'. evaluate (" KmR3 ", sRA) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sRI") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
val _ = EB (AQg "evaluate (" AsgA ", sRL) = (NONE, sRA)") (irule Annot_Seq >> first_assum ACCEPT_TAC);
val _ = EB (AQg "?st'. evaluate (" KmR2 ", sRL) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sRA") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
val _ = EB (AQg "evaluate (" AsgL ", sRB) = (NONE, sRL)") (irule Annot_Seq >> first_assum ACCEPT_TAC);
val _ = EB (AQg "?st'. evaluate (" KmR1 ", sRB) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sRL") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
val _ = EB (AQg "evaluate (" AsgB ", sKm) = (NONE, sRB)") (irule Annot_Seq >> first_assum ACCEPT_TAC);
val _ = EB (AQg "?st'. evaluate (" KmBody ", sKm) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sRB") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
(* Dec km *)
val _ = EB (AQg "?st'. evaluate (" Dkm ", sCore1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord (n2w (hashBytesN method))", "sCore1 with locals := _ = sKm"));
val _ = EB (AQg "?st'. evaluate (" Akm ", sCore1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
(* CORE1 = Seq(Annot)cacheLoop1 at sB0 -> sCore1 ; RB1 = Seq CORE1 Akm *)
val _ = EB (AQg "evaluate (" CORE1 ", sB0) = (NONE, sCore1)") (irule Annot_Seq >> fs []);
val _ = EB (AQg "?st'. evaluate (" RB1 ", sB0) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "sCore1") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
(* Dec b/i/acc/len (Dec_trace) *)
val _ = EB (AQg "?st'. evaluate (" Db ", sI) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord 0w", "sI with locals := _ = sB0"));
val _ = EB (AQg "?st'. evaluate (" Ai ", sI) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
val _ = EB (AQg "?st'. evaluate (" Di ", sAcc) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord 0w", "sAcc with locals := _ = sI"));
val _ = EB (AQg "?st'. evaluate (" Aacc ", sAcc) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
val _ = EB (AQg "?st'. evaluate (" Dacc ", sLen) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord 0w", "sLen with locals := _ = sAcc"));
val _ = EB (AQg "?st'. evaluate (" Alen ", sLen) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
val _ = EB (AQg "?st'. evaluate (" Dlen ", s1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord (n2w (LENGTH method))", "s1 with locals := _ = sLen"));
val _ = EB (AQg "?st'. evaluate (" AL ", s1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
(* loadSeq = Seq(Annot)(load) at sBase -> s1 ; SEQld = Seq loadSeq AL *)
val _ = EB (AQg "evaluate (" loadSeq ", sBase) = (NONE, s1)") (irule Annot_Seq >> first_assum ACCEPT_TAC);
val _ = EB (AQg "?st'. evaluate (" SEQld ", sBase) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (irule Seq_trace >> qexists_tac (QS "s1") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []]);
(* Dec base, Dec ctrl, mainBody *)
val _ = EB (QS "eval s0 BaseAddr = SOME (ValWord ba)") (simp [eval_def, ABB "ba"]);
val _ = EB (QS "FLOOKUP sCtrl.locals «ctrl» = SOME (ValWord ba)") (simp [ABB "sCtrl", FLOOKUP_UPDATE] >> fs []);
val _ = EB (QS "eval sCtrl (Op Add [Var Local «ctrl»; Const 64w]) = SOME (ValWord (ba + 64w))")
  (irule eval_ctrl_add >> fs []);
val _ = EB (AQg "?st'. evaluate (" Dbase ", sCtrl) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord (ba + 64w)", "sCtrl with locals := _ = sBase"));
val _ = EB (AQg "?st'. evaluate (" body_c ", sCtrl) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw;
val _ = EB (AQg "?st'. evaluate (" Dctrl ", s0) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
  (decw ("ValWord ba", "s0 with locals := _ = sCtrl"));
val _ = EB (QS "?sF. evaluate (cacheMainBody, s0) = (SOME (Return (ValWord 0w)), sF) /\\ sF.ffi.io_events = tr")
  (simp [Once cacheMainBody_def] >> annotw);
val _ = e (pop_assum strip_assume_tac);
val _ = e (qexists_tac (QS "sF") >> qexists_tac (QS "loadEv") >> qexists_tac (QS "rb"));
val _ = e (conj_tac >- first_assum ACCEPT_TAC);
val _ = e (fs [ABB "tr"]);
val cacheKeyMainBody_refines = top_thm ();
val _ = proofManagerLib.drop ();
val _ = save_thm ("cacheKeyMainBody_refines", cacheKeyMainBody_refines);

(* ================= Sem + Install + EndToEnd (C21-template tail) ============ *)
fun TM s = Term (QS s);
val traceOf = fn sv =>
  sv ^ ".ffi.io_events ++ loadEv ++\n" ^
  "  [IO_event (ffi$ExtCall «report_vec»)\n" ^
  "     (word_to_bytes (n2w (cacheServe method tgt age) : word64) F) rb]";
val ffiApp = "cacheFFI method tgt age";

val callMainRun = prove (
  TM (
    "FLOOKUP (s'':(64,'ffi)panSem$state).code «main» = SOME ([], cacheMainBody) /\\ " ^
    "s''.clock <> 0 /\\ " ^ ffiApp ^ " ((dec_clock s'') with locals := FEMPTY) /\\ " ^
    "LENGTH method + LENGTH tgt <= (dec_clock s'').clock ==> " ^
    "?t loadEv rb. evaluate (Call NONE «main» [], s'') = (SOME (Return (ValWord 0w)), t) /\\ " ^
    "t.ffi.io_events = " ^ traceOf "s''"),
  strip_tac >>
  qabbrev_tac (QS "s0 = (dec_clock s'') with locals := FEMPTY") >>
  (QS ("s0.locals = FEMPTY /\\ LENGTH method + LENGTH tgt <= s0.clock /\\ " ^ ffiApp ^ " s0 /\\ s0.ffi = s''.ffi")) by
     (fs [ABB "s0", dec_clock_def]) >>
  drule_all cacheKeyMainBody_refines >> strip_tac >>
  qmatch_asmsub_rename_tac (QS "evaluate (cacheMainBody, s0) = (SOME (Return (ValWord 0w)), sF)") >>
  (QS "sF.clock <= s0.clock") by (imp_res_tac evaluate_clock >> fs []) >>
  (QS "evaluate (cacheMainBody, dec_clock s'' with locals := FEMPTY) = (SOME (Return (ValWord 0w)), sF)")
     by (fs [ABB "s0"]) >>
  map_every (fn q => qexists_tac (QS q)) ["empty_locals sF", "loadEv", "rb"] >>
  conj_tac
  >- (simp [Once evaluate_def, OPT_MMAP_def] >> gvs [lookup_code_def, FUPDATE_LIST_THM]) >>
  fs [empty_locals_def]);
val _ = save_thm ("cacheKey_call_main_run", callMainRun);

val mainSemantics = prove (
  TM (
    "FLOOKUP (s':(64,'ffi)panSem$state).code «main» = SOME ([], cacheMainBody) /\\ " ^
    "(!K. " ^ ffiApp ^ " ((dec_clock (s' with clock := K)) with locals := FEMPTY)) /\\ " ^
    "(?K. 0 < K /\\ LENGTH method + LENGTH tgt < K) ==> " ^
    "?loadEv rb. semantics s' «main» = Terminate Success (" ^ traceOf "s'" ^ ")"),
  strip_tac >>
  rename1 (QS "LENGTH method + LENGTH tgt < K0") >>
  qabbrev_tac (QS "sc = s' with clock := K0") >>
  (QS "sc.code = s'.code /\\ sc.ffi = s'.ffi /\\ sc.clock = K0") by (simp [ABB "sc"]) >>
  (QS "FLOOKUP sc.code «main» = SOME ([], cacheMainBody)") by (fs []) >>
  (QS "sc.clock <> 0") by (fs []) >>
  (QS (ffiApp ^ " ((dec_clock sc) with locals := FEMPTY)")) by
     (first_x_assum (qspec_then (QS "K0") mp_tac) >> simp [ABB "sc"]) >>
  (QS "LENGTH method + LENGTH tgt <= (dec_clock sc).clock") by (simp [dec_clock_def] >> fs []) >>
  drule_all callMainRun >> strip_tac >>
  qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >>
  (QS "evaluate (Call NONE «main» [], s' with clock := K0) = (SOME (Return (ValWord 0w)), t)")
     by (fs [ABB "sc"]) >>
  drule semantics_Return_lift >> strip_tac >>
  (QS ("t.ffi.io_events = " ^ traceOf "s'")) by
     (qpat_x_assum (QS "t.ffi.io_events = _") mp_tac >> simp [ABB "sc"]) >>
  simp []);
val _ = save_thm ("cacheKey_main_semantics", mainSemantics);

val decs_ev = (REWRITE_CONV [cacheKeyProg_def] THENC EVAL) (TM "decs_stcnames [] cacheKeyProg");
val evd_ev  = (REWRITE_CONV [cacheKeyProg_def] THENC EVAL)
                (TM "evaluate_decls ((s:(64,'ffi) panSem$state) with structs := []) cacheKeyProg");
val unfoldCore = [cacheMainBody_def, cacheLoop1_def, cacheLoop2_def, foldGuard_def,
                  cacheBodyA1_def, cacheBodyA2_def, cacheGate_def];
val semanticsDecls = prove (
  TM (
    "(s:(64,'ffi) panSem$state).code = FEMPTY /\\ " ^ ffiApp ^ " s /\\ " ^
    "(?K. 0 < K /\\ LENGTH method + LENGTH tgt < K) ==> " ^
    "?loadEv rb. semantics_decls s «main» cacheKeyProg = Terminate Success (" ^ traceOf "s" ^ ")"),
  strip_tac >>
  qabbrev_tac (QS "s' = THE (evaluate_decls (s with structs := []) cacheKeyProg)") >>
  (QS "semantics_decls s «main» cacheKeyProg = semantics s' «main»")
     by (simp [semantics_decls_def, decs_ev, evd_ev, ABB "s'"]) >>
  (QS "FLOOKUP s'.code «main» = SOME ([], cacheMainBody)")
     by (simp [ABB "s'"] >> REWRITE_TAC [cacheKeyProg_def] >> EVAL_TAC >> REWRITE_TAC unfoldCore) >>
  (QS "s'.base_addr = s.base_addr /\\ s'.ffi = s.ffi")
     by (simp [ABB "s'"] >> REWRITE_TAC [cacheKeyProg_def] >> EVAL_TAC) >>
  (QS ("!Kc. " ^ ffiApp ^ " ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)"))
     by (gen_tac >> qpat_x_assum (QS (ffiApp ^ " s")) mp_tac >>
         asm_simp_tac (srw_ss()) [cacheFFI_def, dec_clock_def]) >>
  (QS ("?loadEv rb. semantics s' «main» = Terminate Success (" ^ traceOf "s'" ^ ")"))
     by (irule mainSemantics >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
  qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >> gvs []);
val _ = save_thm ("cacheKeyProg_semantics_decls", semanticsDecls);

val linkB = cacheKeyProg_linkB;
val linkB_ant   = linkB |> concl |> dest_imp |> #1;
val linkB_concl = linkB |> concl |> dest_imp |> #2;
val sd_tm = find_term (fn t => same_const (fst (strip_comb t)) “semantics_decls” handle _ => false) linkB_concl;
val notFail_tm = valOf (List.find (fn c => is_neg c andalso
    (let val e = dest_neg c in is_eq e andalso
       (same_const (fst (strip_comb (lhs e))) “semantics_decls” handle _ => false) end))
    (boolSyntax.strip_conj linkB_ant));
val pkg_tm = list_mk_conj (filter (fn c => not (aconv c notFail_tm)) (boolSyntax.strip_conj linkB_ant));
val trace_tm = TM (traceOf "(s:(64,'ffi) panSem$state)");
val subset_sd = linkB_concl;
val subset_spec = subst [sd_tm |-> Term [QUOTE "Terminate Success ", ANTIQUOTE trace_tm]] linkB_concl;
val e2e_goal =
  mk_imp (list_mk_conj [pkg_tm, TM (ffiApp ^ " (s:(64,'ffi) panSem$state)"),
                        TM "?K. 0 < K /\\ LENGTH method + LENGTH tgt < K"],
          mk_exists (TM "loadEv:io_event list",
            mk_exists (TM "rb:(word8 # word8) list", subset_spec)));
val exists_big = prove (TM "!n:num. ?K. 0 < K /\\ n < K", gen_tac >> qexists_tac (QS "SUC n") >> DECIDE_TAC);
val machineCode = prove (e2e_goal,
  strip_tac >>
  mp_tac (SPEC_ALL semanticsDecls) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> MATCH_ACCEPT_TAC exists_big) >>
  strip_tac >>
  qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >>
  (([ANTIQUOTE notFail_tm]) by
     (qpat_x_assum ([QUOTE "", ANTIQUOTE sd_tm, QUOTE " = _"]) (fn th => simp [th]))) >>
  (([ANTIQUOTE subset_sd]) by
     (match_mp_tac linkB >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac []))) >>
  qpat_x_assum ([QUOTE "", ANTIQUOTE sd_tm, QUOTE " = _"]) (fn th => gvs [th]));
val _ = save_thm ("cacheKey_machine_code", machineCode);

val _ = export_theory ();

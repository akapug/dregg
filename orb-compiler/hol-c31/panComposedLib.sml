(* ===========================================================================
   C23 — mk_composedWrapper : the whole-program wrapper GENERATOR for a composed
   TWO-fold + scalar-gate serve stage.  C22 hand-wrote this stack bespoke (~347
   line MainRefine + the C21-template Sem/Install/EndToEnd tail) because
   mk_foldWrapper's single-fold peeler cannot take the composed spine
   (Dec…;fold1;save;retarget;fold2;save;scalar;Dec dec;GATE;store;report;Return).
   Here it is a GENERATOR: given the spine tokens (two fold framed-cores + arena
   offsets + save vars, a scalar read, the gate theorem, the result word, the
   parser-output mainBody + Link B) it emits MainRefine + Sem + Install + EndToEnd
   -> `<prefix>_machine_code`.  NO new metatheory: the same fixed tactics C22's
   hand proof used, parameterized.  The fold-exit frame/clock/save threading is
   handled internally via the supplied per-fold framed cores (composedCommon's
   body-generic `loop_frame`).
   =========================================================================== *)
structure panComposedLib =
struct

open HolKernel boolLib bossLib Parse proofManagerLib markerLib;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory pairTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory c14GenericTheory foldWrapCommonTheory
     composedCommonTheory panAutoTheory;

fun QS s = [QUOTE s] : term frag list;
fun EBk q tac = ignore (e (q by tac));
val ABB = fn nm => Abbr (QS nm);
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
fun AQ t = [ANTIQUOTE t];
fun AQg pre t post = [QUOTE pre, ANTIQUOTE t, QUOTE post];

type foldSpec =
  { arenaOff : string, lenOff : string option, lenExpr : string, memArg : string,
    loopName : string, framed : thm, noFFI : thm, accWord : string, saveVar : string };

type scalarSpec = { off : string, var : string, valWord : string };

fun mk_composedMainRefine
      { prefix : string, ffiName : string, ffiDef : thm, ffiArgs : string,
        stagedDef : thm, clockBound : string, arena0 : string,
        fold0 : foldSpec, fold1 : foldSpec, scalars : scalarSpec list,
        decVar : string, gateName : string, gateThm : thm,
        storeOff : string, resultWord : string,
        mainBodyName : string, mainBodyDef : thm } : thm =
  let
    fun kv v = "«" ^ v ^ "»"
    val allVars = ["ctrl","base","len","acc","i","b", #saveVar fold0, #saveVar fold1]
                  @ map #var scalars @ [decVar]
    (* ---- ML peel of the composed spine (2-fold + gate) ---- *)
    val mbT   = inst64 (rhs (concl mainBodyDef))
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

    val f0acc = #accWord fold0 and f1acc = #accWord fold1
    val f0mem = #memArg fold0 and f1mem = #memArg fold1
    val f0len = #lenExpr fold0 and f1len = #lenExpr fold1
    val km = #saveVar fold0 and ku = #saveVar fold1
    val sc = hd scalars
    val scoff = #off sc and scvar = #var sc and scval = #valWord sc

    (* ================= MainRefine (forward) ================= *)
    val _ = g (QS (
      ffiName ^ " " ^ ffiArgs ^ " s0 /\\ s0.locals = FEMPTY /\\\n" ^
      " " ^ clockBound ^ " <= s0.clock ==>\n" ^
      " ?sF loadEv rb.\n" ^
      "   evaluate (" ^ mainBodyName ^ ", s0) = (SOME (Return (ValWord 0w)), sF) /\\\n" ^
      "   sF.ffi.io_events = s0.ffi.io_events ++ loadEv ++\n" ^
      "     [IO_event (ffi$ExtCall «report_vec»)\n" ^
      "        (word_to_bytes (" ^ resultWord ^ " : word64) F) rb]"))
    val _ = e strip_tac
    val _ = e (qpat_x_assum (QS (ffiName ^ " _ _ _ _")) (strip_assume_tac o SIMP_RULE std_ss [ffiDef]))
    val _ = e (qabbrev_tac (QS "ba = s0.base_addr"))
    (* distinctness of all local keys *)
    val pairs = let fun go [] = [] | go (x::xs) = map (fn y => (x,y)) xs @ go xs
                in go allVars end
    val distinctConj = String.concatWith " /\\ " (map (fn (a,b) => kv a ^ "<>" ^ kv b) pairs)
    val _ = EBk (QS distinctConj) EVAL_TAC

    (* prelude: ctrl, base, load *)
    val _ = e (qabbrev_tac (QS "sCtrl = s0 with locals := s0.locals |+ («ctrl», ValWord ba)"))
    val _ = e (qabbrev_tac (QS ("sBase = sCtrl with locals := sCtrl.locals |+ («base», ValWord (ba + " ^ arena0 ^ "))")))
    val _ = EBk (QS (
      "sBase.base_addr = ba /\\ sBase.clock = s0.clock /\\ sBase.memory = s0.memory /\\ " ^
      "sBase.memaddrs = s0.memaddrs /\\ sBase.be = s0.be /\\ sBase.ffi = s0.ffi /\\ sBase.structs = s0.structs"))
      (simp [ABB "sBase", ABB "sCtrl", ABB "ba"])
    val _ = EBk (QS (
      "FLOOKUP sBase.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP sBase.locals «base» = SOME (ValWord (ba + " ^ arena0 ^ "))"))
      (simp [ABB "sBase", ABB "sCtrl", FLOOKUP_UPDATE] >> fs [])
    val _ = e (qpat_x_assum (QS "!s. _ ==> _") (qspec_then (QS "sBase") mp_tac))
    val _ = e (impl_tac >- fs [])
    val _ = e strip_tac
    val _ = EBk (QS (
      "ba IN s1.memaddrs /\\ s1.memory ba = Word (n2w (" ^ f0len ^ ")) /\\ " ^
      "(ba+" ^ (#lenOff fold1 |> valOf) ^ ") IN s1.memaddrs /\\ s1.memory (ba+" ^ (#lenOff fold1 |> valOf) ^ ") = Word (n2w (" ^ f1len ^ ")) /\\ " ^
      "(ba+" ^ scoff ^ ") IN s1.memaddrs /\\ s1.memory (ba+" ^ scoff ^ ") = Word (" ^ scval ^ ") /\\ " ^
      "(ba+" ^ storeOff ^ ") IN s1.memaddrs /\\ memRel " ^ f0mem ^ " (ba+" ^ arena0 ^ ") s1 /\\ memRel " ^ f1mem ^ " (ba+" ^ #arenaOff fold1 ^ ") s1 /\\ " ^
      "" ^ f0len ^ " < 2n**63 /\\ " ^ f1len ^ " < 2n**63 /\\ " ^ scvar ^ " < 4294967296 /\\ " ^
      "EVERY (\\x. x<256) " ^ f0mem ^ " /\\ EVERY (\\x. x<256) " ^ f1mem ^ ""))
      (fs [stagedDef])
    val _ = EBk (QS (
      "FLOOKUP s1.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP s1.locals «base» = SOME (ValWord (ba+" ^ arena0 ^ "))"))
      ((QS "s1.locals = sBase.locals") by (fs []) >> fs [])

    (* -- fold 0 setup: read len, Dec len/acc/i/b -- *)
    val _ = EBk (QS ("eval s1 (Load One (Var Local «ctrl»)) = SOME (ValWord (n2w (" ^ f0len ^ ")))"))
      (irule eval_load_ctrlc >> qexists_tac (QS "ba") >> fs [])
    val _ = e (qabbrev_tac (QS ("sLen = s1 with locals := s1.locals |+ («len», ValWord (n2w (" ^ f0len ^ ")))")))
    val _ = e (qabbrev_tac (QS "sAcc = sLen with locals := sLen.locals |+ («acc», ValWord 0w)"))
    val _ = e (qabbrev_tac (QS "sI = sAcc with locals := sAcc.locals |+ («i», ValWord 0w)"))
    val _ = e (qabbrev_tac (QS "sB0 = sI with locals := sI.locals |+ («b», ValWord 0w)"))
    val _ = EBk (QS (
      "sB0.memory = s1.memory /\\ sB0.memaddrs = s1.memaddrs /\\ sB0.be = s1.be /\\ sB0.structs = s1.structs /\\ " ^
      "sB0.clock = s1.clock /\\ sB0.ffi = s1.ffi /\\ sB0.base_addr = ba"))
      (simp [ABB "sB0", ABB "sI", ABB "sAcc", ABB "sLen"] >> fs [])
    val _ = EBk (QS (
      "FLOOKUP sB0.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP sB0.locals «base» = SOME (ValWord (ba+" ^ arena0 ^ ")) /\\ " ^
      "FLOOKUP sB0.locals «len» = SOME (ValWord (n2w (" ^ f0len ^ "))) /\\ FLOOKUP sB0.locals «acc» = SOME (ValWord 0w) /\\ " ^
      "FLOOKUP sB0.locals «i» = SOME (ValWord 0w) /\\ FLOOKUP sB0.locals «b» = SOME (ValWord 0w)"))
      (simp [ABB "sB0", ABB "sI", ABB "sAcc", ABB "sLen", FLOOKUP_UPDATE] >> fs [])
    val _ = EBk (QS ("memRel " ^ f0mem ^ " (ba+" ^ arena0 ^ ") sB0"))
      (gvs [memRel_def, ABB "sB0", ABB "sI", ABB "sAcc", ABB "sLen"] >> fs [memRel_def])
    val _ = EBk (QS ("foldInv " ^ f0mem ^ " (ba+" ^ arena0 ^ ") 0 0w sB0")) (simp [foldInv_def] >> fs [] >> metis_tac [])
    val _ = EBk (QS (f0len ^ " <= sB0.clock"))
      ((QS "sB0.clock = s0.clock") by (fs [] >> (QS "s1.clock = sBase.clock") by fs [] >> fs []) >> fs [])
    (* run fold 0 *)
    val _ = e (drule (#framed fold0) >> disch_then drule >> strip_tac)
    val _ = e (qmatch_asmsub_rename_tac (QS ("evaluate (" ^ #loopName fold0 ^ ", sB0) = (NONE, sCore1)")))
    val _ = EBk (QS ("FLOOKUP sCore1.locals «acc» = SOME (ValWord (" ^ f0acc ^ "))")) (fs [])
    val _ = EBk (QS "FLOOKUP sCore1.locals «ctrl» = SOME (ValWord ba)") (fs [])
    val _ = EBk (QS "sCore1.memory = s1.memory /\\ sCore1.memaddrs = s1.memaddrs /\\ sCore1.be = s1.be") (fs [])
    val _ = EBk (QS "sCore1.base_addr = ba") (imp_res_tac evaluate_invariants >> gvs [])
    val _ = EBk (QS ("sB0.clock - " ^ f0len ^ " <= sCore1.clock")) (fs [])
    val _ = EBk (QS "sCore1.ffi.io_events = s0.ffi.io_events ++ loadEv")
      ((QS ("sCore1.ffi.io_events = sB0.ffi.io_events"))
          by ((QS ("evaluate (" ^ #loopName fold0 ^ ", sB0) = (NONE, sCore1)")) by (fs []) >> drule noFFI_io_events >> simp [#noFFI fold0]) >>
       (QS "sB0.ffi.io_events = s0.ffi.io_events ++ loadEv") by (fs []) >> fs [])
    val _ = EBk (QS ("FLOOKUP sCore1.locals «base» = SOME (ValWord (ba + " ^ arena0 ^ "))")) (fs [])
    val _ = EBk (QS ("FLOOKUP sCore1.locals «len» = SOME (ValWord (n2w (" ^ f0len ^ ")))")) (fs [])
    val _ = EBk (QS "?iw. FLOOKUP sCore1.locals «i» = SOME (ValWord iw)") (metis_tac [])
    val _ = EBk (QS "?bw. FLOOKUP sCore1.locals «b» = SOME (ValWord bw)") (metis_tac [])
    (* -- Dec save0 (km) -- *)
    val _ = EBk (QS ("eval sCore1 (Var Local «acc») = SOME (ValWord (" ^ f0acc ^ "))")) (simp [eval_def] >> fs [])
    val _ = e (qabbrev_tac (QS ("sKm = sCore1 with locals := sCore1.locals |+ (" ^ kv km ^ ", ValWord (" ^ f0acc ^ "))")))
    val _ = EBk (QS (
      "sKm.memory = s1.memory /\\ sKm.memaddrs = s1.memaddrs /\\ sKm.be = s1.be /\\ sKm.base_addr = ba /\\ " ^
      "sKm.clock = sCore1.clock /\\ sKm.ffi = sCore1.ffi /\\ FLOOKUP sKm.locals «ctrl» = SOME (ValWord ba) /\\ " ^
      "FLOOKUP sKm.locals «base» = SOME (ValWord (ba + " ^ arena0 ^ ")) /\\ " ^
      "FLOOKUP sKm.locals «len» = SOME (ValWord (n2w (" ^ f0len ^ "))) /\\ " ^
      "FLOOKUP sKm.locals «acc» = SOME (ValWord (" ^ f0acc ^ ")) /\\ " ^
      "(?iw. FLOOKUP sKm.locals «i» = SOME (ValWord iw)) /\\ (?bw. FLOOKUP sKm.locals «b» = SOME (ValWord bw)) /\\ " ^
      "FLOOKUP sKm.locals " ^ kv km ^ " = SOME (ValWord (" ^ f0acc ^ "))"))
      (simp [ABB "sKm", FLOOKUP_UPDATE] >> fs [] >> metis_tac [])
    (* -- retarget for fold1: base:=ctrl+arenaOff1 -- *)
    val f1arena = #arenaOff fold1
    val f1lenoff = valOf (#lenOff fold1)
    val _ = EBk (QS ("eval sKm (Op Add [Var Local «ctrl»; Const " ^ f1arena ^ "]) = SOME (ValWord (ba + " ^ f1arena ^ "))"))
      (irule eval_ctrl_add >> fs [])
    val _ = e (qabbrev_tac (QS ("sRB = sKm with locals := sKm.locals |+ («base», ValWord (ba + " ^ f1arena ^ "))")))
    val _ = EBk (QS ("evaluate (Assign Local «base» (Op Add [Var Local «ctrl»; Const " ^ f1arena ^ "]), sKm) = (NONE, sRB)"))
      ((QS ("FLOOKUP sKm.locals «base» = SOME (ValWord (ba + " ^ arena0 ^ "))")) by fs [] >>
       (QS ("eval sKm (Op Add [Var Local «ctrl»; Const " ^ f1arena ^ "]) = SOME (ValWord (ba + " ^ f1arena ^ "))")) by (irule eval_ctrl_add >> fs []) >>
       (QS ("evaluate (Assign Local «base» (Op Add [Var Local «ctrl»; Const " ^ f1arena ^ "]), sKm) = (NONE, set_var «base» (ValWord (ba + " ^ f1arena ^ ")) sKm)")) by (irule evaluate_Assign_val >> fs []) >>
       (QS ("set_var «base» (ValWord (ba + " ^ f1arena ^ ")) sKm = sRB")) by simp [ABB "sRB", set_var_def] >> metis_tac [])
    val _ = EBk (QS (
      "sRB.memory = s1.memory /\\ sRB.memaddrs = s1.memaddrs /\\ sRB.be = s1.be /\\ sRB.base_addr = ba /\\ " ^
      "sRB.clock = sCore1.clock /\\ sRB.ffi = sCore1.ffi /\\ FLOOKUP sRB.locals «ctrl» = SOME (ValWord ba) /\\ " ^
      "FLOOKUP sRB.locals «len» = SOME (ValWord (n2w (" ^ f0len ^ "))) /\\ " ^
      "FLOOKUP sRB.locals «acc» = SOME (ValWord (" ^ f0acc ^ ")) /\\ " ^
      "(?iw. FLOOKUP sRB.locals «i» = SOME (ValWord iw)) /\\ (?bw. FLOOKUP sRB.locals «b» = SOME (ValWord bw)) /\\ " ^
      "FLOOKUP sRB.locals " ^ kv km ^ " = SOME (ValWord (" ^ f0acc ^ "))"))
      (simp [ABB "sRB", FLOOKUP_UPDATE] >> fs [] >> metis_tac [])
    (* -- len:=lds(ctrl+lenoff1) -- *)
    val _ = EBk (QS ("(ba + " ^ f1lenoff ^ ") IN sRB.memaddrs")) (metis_tac [])
    val _ = EBk (QS ("sRB.memory (ba + " ^ f1lenoff ^ ") = Word (n2w (" ^ f1len ^ "))")) (metis_tac [])
    val _ = EBk (QS ("eval sRB (Load One (Op Add [Var Local «ctrl»; Const " ^ f1lenoff ^ "])) = SOME (ValWord (n2w (" ^ f1len ^ ")))"))
      (irule eval_load_ctrl_off >> qexists_tac (QS "ba") >> fs [])
    val _ = e (qabbrev_tac (QS ("sRL = sRB with locals := sRB.locals |+ («len», ValWord (n2w (" ^ f1len ^ ")))")))
    val _ = EBk (QS ("evaluate (Assign Local «len» (Load One (Op Add [Var Local «ctrl»; Const " ^ f1lenoff ^ "])), sRB) = (NONE, set_var «len» (ValWord (n2w (" ^ f1len ^ "))) sRB)"))
      (irule evaluate_Assign_val >> fs [])
    val _ = EBk (QS ("set_var «len» (ValWord (n2w (" ^ f1len ^ "))) sRB = sRL")) (simp [ABB "sRL", set_var_def])
    val _ = EBk (QS ("evaluate (Assign Local «len» (Load One (Op Add [Var Local «ctrl»; Const " ^ f1lenoff ^ "])), sRB) = (NONE, sRL)")) (fs [])
    (* -- acc:=0 -- *)
    val _ = e (qabbrev_tac (QS "sRA = sRL with locals := sRL.locals |+ («acc», ValWord 0w)"))
    val _ = EBk (QS "evaluate (Assign Local «acc» (Const 0w), sRL) = (NONE, sRA)")
      ((QS ("FLOOKUP sRL.locals «acc» = SOME (ValWord (" ^ f0acc ^ "))")) by (simp [ABB "sRL", FLOOKUP_UPDATE] >> fs []) >>
       (QS "eval sRL (Const 0w) = SOME (ValWord 0w)") by simp [eval_def] >>
       (QS "evaluate (Assign Local «acc» (Const 0w), sRL) = (NONE, set_var «acc» (ValWord 0w) sRL)") by (irule evaluate_Assign_val >> fs []) >>
       (QS "set_var «acc» (ValWord 0w) sRL = sRA") by simp [ABB "sRA", set_var_def] >> metis_tac [])
    (* -- i:=0 -- *)
    val _ = e (qabbrev_tac (QS "sRI = sRA with locals := sRA.locals |+ («i», ValWord 0w)"))
    val _ = EBk (QS "?iwv. FLOOKUP sRA.locals «i» = SOME (ValWord iwv)")
      (simp [ABB "sRA", ABB "sRL", FLOOKUP_UPDATE] >> metis_tac [])
    val _ = EBk (QS "eval sRA (Const 0w) = SOME (ValWord 0w)") (simp [eval_def])
    val _ = EBk (QS "evaluate (Assign Local «i» (Const 0w), sRA) = (NONE, set_var «i» (ValWord 0w) sRA)")
      (irule evaluate_Assign_val >> metis_tac [])
    val _ = EBk (QS "set_var «i» (ValWord 0w) sRA = sRI") (simp [ABB "sRI", set_var_def])
    val _ = EBk (QS "evaluate (Assign Local «i» (Const 0w), sRA) = (NONE, sRI)") (fs [])
    (* -- b:=0 -- *)
    val _ = e (qabbrev_tac (QS "sRBb = sRI with locals := sRI.locals |+ («b», ValWord 0w)"))
    val _ = EBk (QS "?bwv. FLOOKUP sRI.locals «b» = SOME (ValWord bwv)")
      (simp [ABB "sRI", ABB "sRA", ABB "sRL", FLOOKUP_UPDATE] >> metis_tac [])
    val _ = EBk (QS "eval sRI (Const 0w) = SOME (ValWord 0w)") (simp [eval_def])
    val _ = EBk (QS "evaluate (Assign Local «b» (Const 0w), sRI) = (NONE, set_var «b» (ValWord 0w) sRI)")
      (irule evaluate_Assign_val >> metis_tac [])
    val _ = EBk (QS "set_var «b» (ValWord 0w) sRI = sRBb") (simp [ABB "sRBb", set_var_def])
    val _ = EBk (QS "evaluate (Assign Local «b» (Const 0w), sRI) = (NONE, sRBb)") (fs [])
    val _ = EBk (QS (
      "sRBb.memory = s1.memory /\\ sRBb.memaddrs = s1.memaddrs /\\ sRBb.be = s1.be /\\ " ^
      "sRBb.base_addr = ba /\\ sRBb.clock = sCore1.clock /\\ sRBb.ffi = sCore1.ffi"))
      (simp [ABB "sRBb", ABB "sRI", ABB "sRA", ABB "sRL"] >> fs [])
    val _ = EBk (QS (
      "FLOOKUP sRBb.locals «ctrl» = SOME (ValWord ba) /\\ FLOOKUP sRBb.locals «base» = SOME (ValWord (ba+" ^ f1arena ^ ")) /\\ " ^
      "FLOOKUP sRBb.locals «len» = SOME (ValWord (n2w (" ^ f1len ^ "))) /\\ FLOOKUP sRBb.locals «acc» = SOME (ValWord 0w) /\\ " ^
      "FLOOKUP sRBb.locals «i» = SOME (ValWord 0w) /\\ FLOOKUP sRBb.locals «b» = SOME (ValWord 0w) /\\ " ^
      "FLOOKUP sRBb.locals " ^ kv km ^ " = SOME (ValWord (" ^ f0acc ^ "))"))
      (simp [ABB "sRBb", ABB "sRI", ABB "sRA", ABB "sRL", ABB "sRB", FLOOKUP_UPDATE] >> fs [])
    val _ = EBk (QS ("memRel " ^ f1mem ^ " (ba+" ^ f1arena ^ ") sRBb"))
      (gvs [memRel_def, ABB "sRBb", ABB "sRI", ABB "sRA", ABB "sRL", ABB "sRB"] >> fs [memRel_def])
    val _ = EBk (QS ("foldInv " ^ f1mem ^ " (ba+" ^ f1arena ^ ") 0 0w sRBb")) (simp [foldInv_def] >> fs [] >> metis_tac [])
    val _ = EBk (QS (f1len ^ " <= sRBb.clock"))
      ((QS "sRBb.clock = sCore1.clock") by fs [] >>
       (QS "sB0.clock = s0.clock") by (fs [] >> (QS "s1.clock = sBase.clock") by fs [] >> fs []) >> fs [])
    (* run fold 1 *)
    val _ = e (drule (#framed fold1) >> disch_then drule >> strip_tac)
    val _ = e (qmatch_asmsub_rename_tac (QS ("evaluate (" ^ #loopName fold1 ^ ", sRBb) = (NONE, sCore2)")))
    val _ = EBk (QS ("FLOOKUP sCore2.locals «acc» = SOME (ValWord (" ^ f1acc ^ "))")) (fs [])
    val _ = EBk (QS "FLOOKUP sCore2.locals «ctrl» = SOME (ValWord ba)") (fs [])
    val _ = EBk (QS ("FLOOKUP sCore2.locals " ^ kv km ^ " = SOME (ValWord (" ^ f0acc ^ "))")) (fs [])
    val _ = EBk (QS "sCore2.memory = s1.memory") ((QS "sCore2.memory = sRBb.memory") by fs [] >> fs [])
    val _ = EBk (QS "sCore2.memaddrs = s1.memaddrs /\\ sCore2.base_addr = ba") (imp_res_tac evaluate_invariants >> gvs [])
    val _ = EBk (QS "sCore2.ffi.io_events = s0.ffi.io_events ++ loadEv")
      ((QS ("sCore2.ffi.io_events = sRBb.ffi.io_events"))
          by ((QS ("evaluate (" ^ #loopName fold1 ^ ", sRBb) = (NONE, sCore2)")) by (fs []) >> drule noFFI_io_events >> simp [#noFFI fold1]) >>
       (QS "sRBb.ffi = sCore1.ffi") by fs [] >> (QS "sCore1.ffi.io_events = s0.ffi.io_events ++ loadEv") by fs [] >> fs [])
    (* -- Dec save1 (ku), scalar (age), Dec dec -- *)
    val _ = EBk (QS ("eval sCore2 (Var Local «acc») = SOME (ValWord (" ^ f1acc ^ "))")) (simp [eval_def] >> fs [])
    val _ = e (qabbrev_tac (QS ("sKu = sCore2 with locals := sCore2.locals |+ (" ^ kv ku ^ ", ValWord (" ^ f1acc ^ "))")))
    val _ = EBk (QS (
      "sKu.memory = s1.memory /\\ sKu.memaddrs = s1.memaddrs /\\ sKu.base_addr = ba /\\ sKu.clock = sCore2.clock /\\ " ^
      "sKu.ffi = sCore2.ffi /\\ FLOOKUP sKu.locals «ctrl» = SOME (ValWord ba) /\\ " ^
      "FLOOKUP sKu.locals " ^ kv km ^ " = SOME (ValWord (" ^ f0acc ^ ")) /\\ " ^
      "FLOOKUP sKu.locals " ^ kv ku ^ " = SOME (ValWord (" ^ f1acc ^ "))"))
      (simp [ABB "sKu", FLOOKUP_UPDATE] >> fs [])
    val _ = EBk (QS ("(ba + " ^ scoff ^ ") IN sKu.memaddrs")) (metis_tac [])
    val _ = EBk (QS ("sKu.memory (ba + " ^ scoff ^ ") = Word (" ^ scval ^ ")")) (metis_tac [])
    val _ = EBk (QS ("eval sKu (Load One (Op Add [Var Local «ctrl»; Const " ^ scoff ^ "])) = SOME (ValWord (" ^ scval ^ "))"))
      (irule eval_load_ctrl_off >> qexists_tac (QS "ba") >> fs [])
    val _ = e (qabbrev_tac (QS ("sAge = sKu with locals := sKu.locals |+ (" ^ kv scvar ^ ", ValWord (" ^ scval ^ "))")))
    val _ = e (qabbrev_tac (QS ("sDec = sAge with locals := sAge.locals |+ (" ^ kv decVar ^ ", ValWord 0w)")))
    val _ = EBk (QS (
      "sDec.memory = s1.memory /\\ sDec.memaddrs = s1.memaddrs /\\ sDec.base_addr = ba /\\ sDec.clock = sCore2.clock /\\ " ^
      "sDec.ffi = sCore2.ffi /\\ FLOOKUP sDec.locals «ctrl» = SOME (ValWord ba) /\\ " ^
      "FLOOKUP sDec.locals " ^ kv km ^ " = SOME (ValWord (" ^ f0acc ^ ")) /\\ " ^
      "FLOOKUP sDec.locals " ^ kv ku ^ " = SOME (ValWord (" ^ f1acc ^ ")) /\\ " ^
      "FLOOKUP sDec.locals " ^ kv scvar ^ " = SOME (ValWord (" ^ scval ^ ")) /\\ FLOOKUP sDec.locals " ^ kv decVar ^ " = SOME (ValWord 0w)"))
      (simp [ABB "sDec", ABB "sAge", ABB "sKu", FLOOKUP_UPDATE] >> fs [])
    (* run the gate *)
    val _ = EBk (QS (
      "?sG. evaluate (" ^ gateName ^ ", sDec) = (NONE, sG) /\\ " ^
      "FLOOKUP sG.locals " ^ kv decVar ^ " = SOME (ValWord (" ^ resultWord ^ ")) /\\ " ^
      "(!v. v <> " ^ kv decVar ^ " ==> FLOOKUP sG.locals v = FLOOKUP sDec.locals v) /\\ " ^
      "sG.ffi = sDec.ffi /\\ sG.memory = sDec.memory /\\ sG.memaddrs = sDec.memaddrs /\\ " ^
      "sG.clock = sDec.clock /\\ sG.base_addr = sDec.base_addr"))
      (irule gateThm >> fs [])
    val _ = e (pop_assum strip_assume_tac)
    val _ = EBk (QS "FLOOKUP sG.locals «ctrl» = SOME (ValWord ba)")
      (first_x_assum (qspec_then (QS "«ctrl»") mp_tac) >> impl_tac >- EVAL_TAC >> fs [])
    val _ = EBk (QS "sG.base_addr = ba /\\ sG.memory = s1.memory /\\ sG.memaddrs = s1.memaddrs /\\ sG.ffi = sCore2.ffi") (fs [])
    (* store the decision at ctrl+storeOff *)
    val _ = EBk (QS ("(ba+" ^ storeOff ^ ") IN sG.memaddrs")) (metis_tac [])
    val _ = e (qabbrev_tac (QS ("sS = sG with memory := ((ba + " ^ storeOff ^ ") =+ Word (" ^ resultWord ^ ")) sG.memory")))
    val _ = EBk (QS ("FLOOKUP sG.locals " ^ kv decVar ^ " = SOME (ValWord (" ^ resultWord ^ "))")) (fs [])
    val _ = EBk (QS "FLOOKUP sG.locals «ctrl» = SOME (ValWord ba)") (fs [])
    val _ = EBk (QS (
      "evaluate (Store (Op Add [Var Local «ctrl»; Const " ^ storeOff ^ "]) (Var Local " ^ kv decVar ^ "), sG) = (NONE, sS)"))
      ((QS ("evaluate (Store (Op Add [Var Local «ctrl»; Const " ^ storeOff ^ "]) (Var Local " ^ kv decVar ^ "), sG) = (NONE, sG with memory := ((ba + " ^ storeOff ^ ") =+ Word (" ^ resultWord ^ ")) sG.memory)"))
          by (irule evaluate_store_ctrl_var >> metis_tac []) >>
       simp [ABB "sS"] >> metis_tac [])
    val _ = EBk (QS (
      "sS.base_addr = ba /\\ sS.memaddrs = sG.memaddrs /\\ sS.locals = sG.locals /\\ sS.clock = sG.clock /\\ sS.ffi = sG.ffi"))
      (simp [ABB "sS"])
    val _ = EBk (QS "FLOOKUP sS.locals «ctrl» = SOME (ValWord sS.base_addr)") (gvs [])
    val _ = EBk (QS ("(sS.base_addr + " ^ storeOff ^ ") IN sS.memaddrs")) (gvs [])
    val _ = EBk (QS ("sS.memory (sS.base_addr + " ^ storeOff ^ ") = Word (" ^ resultWord ^ ")"))
      (gvs [ABB "sS", combinTheory.APPLY_UPDATE_THM])
    (* apply the report oracle *)
    val _ = e (qpat_x_assum (QS "!s w. _") (qspecl_then [QS "sS", QS resultWord] mp_tac))
    val _ = e (impl_tac >- fs [])
    val _ = e strip_tac
    val _ = e (qmatch_asmsub_rename_tac (QS "evaluate (ExtCall «report_vec» _ _ _ _, sS) = (NONE, sRep)"))
    val _ = EBk (QS "sS.ffi.io_events = s0.ffi.io_events ++ loadEv") (fs [])
    val _ = e (qabbrev_tac (QS (
      "tr = s0.ffi.io_events ++ loadEv ++ " ^
      "[IO_event (ffi$ExtCall «report_vec») (word_to_bytes (" ^ resultWord ^ ":word64) F) rb]")))
    val _ = EBk (QS "sRep.ffi.io_events = tr") (simp [ABB "tr"] >> fs [])

    (* ================= backward wrap ================= *)
    val _ = EBk (AQg "evaluate (" RETURNN ", sRep) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
      (irule Annot_Seq >> simp [evaluate_def, eval_def, size_of_sh_with_ctxt_def, shape_of_def])
    val _ = EBk (QS "(empty_locals sRep).ffi.io_events = tr") (simp [empty_locals_def] >> fs [])
    val _ = EBk (AQg "evaluate (" REPORTN ", sS) = (NONE, sRep)") (irule Annot_Seq >> fs [])
    val _ = EBk (AQg "evaluate (" AfterStore ", sS) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
      (irule Seq_thread >> qexists_tac (QS "sRep") >> fs [])
    val _ = EBk (AQg "evaluate (" STOREN ", sG) = (NONE, sS)") (irule Annot_Seq >> fs [])
    val _ = EBk (AQg "evaluate (" AfterGate ", sG) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
      (irule Seq_thread >> qexists_tac (QS "sS") >> fs [])
    val _ = EBk (AQg "evaluate (" GATEN ", sDec) = (NONE, sG)") (irule Annot_Seq >> fs [])
    val _ = EBk (AQg "evaluate (" DecBody ", sDec) = (SOME (Return (ValWord 0w)), empty_locals sRep)")
      (irule Seq_thread >> qexists_tac (QS "sG") >> fs [])
    val _ = EBk (AQg "?st. evaluate (" DecBody ", sDec) = (SOME (Return (ValWord 0w)), st) /\\ st.ffi.io_events = tr")
      (qexists_tac (QS "empty_locals sRep") >> fs [])
    val decw = fn (vq, steq) =>
      irule Dec_trace >> qexists_tac (QS vq) >> rpt conj_tac >>
      TRY (qpat_x_assum (QS steq) (fn th => REWRITE_TAC [th])) >>
      FIRST [ first_assum ACCEPT_TAC, (simp [eval_def, shape_of_def] >> NO_TAC), (metis_tac []) ]
    val annotw = irule Annot_trace >> (first_assum ACCEPT_TAC ORELSE metis_tac [])
    (* state equalities the decw REWRITEs need *)
    val _ = EBk (QS ("sAge with locals := sAge.locals |+ (" ^ kv decVar ^ ", ValWord 0w) = sDec")) (simp [ABB "sDec"])
    val _ = EBk (QS ("sKu with locals := sKu.locals |+ (" ^ kv scvar ^ ", ValWord (" ^ scval ^ ")) = sAge")) (simp [ABB "sAge"])
    val _ = EBk (QS ("sCore2 with locals := sCore2.locals |+ (" ^ kv ku ^ ", ValWord (" ^ f1acc ^ ")) = sKu")) (simp [ABB "sKu"])
    val _ = EBk (QS ("sCore1 with locals := sCore1.locals |+ (" ^ kv km ^ ", ValWord (" ^ f0acc ^ ")) = sKm")) (simp [ABB "sKm"])
    val _ = EBk (QS ("s1 with locals := s1.locals |+ («len», ValWord (n2w (" ^ f0len ^ "))) = sLen")) (simp [ABB "sLen"])
    val _ = EBk (QS "sLen with locals := sLen.locals |+ («acc», ValWord 0w) = sAcc") (simp [ABB "sAcc"])
    val _ = EBk (QS "sAcc with locals := sAcc.locals |+ («i», ValWord 0w) = sI") (simp [ABB "sI"])
    val _ = EBk (QS "sI with locals := sI.locals |+ («b», ValWord 0w) = sB0") (simp [ABB "sB0"])
    val _ = EBk (QS "s0 with locals := s0.locals |+ («ctrl», ValWord ba) = sCtrl") (simp [ABB "sCtrl"])
    val _ = EBk (QS ("sCtrl with locals := sCtrl.locals |+ («base», ValWord (ba + " ^ arena0 ^ ")) = sBase")) (simp [ABB "sBase"])
    (* Dec dec *)
    val _ = EBk (AQg "?st'. evaluate (" Ddec ", sAge) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord 0w", "sAge with locals := _ = sDec"))
    val _ = EBk (AQg "?st'. evaluate (" AgeBody ", sAge) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    (* Dec age *)
    val _ = EBk (AQg "?st'. evaluate (" Dage ", sKu) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord (" ^ scval ^ ")", "sKu with locals := _ = sAge"))
    val _ = EBk (AQg "?st'. evaluate (" KuBody ", sKu) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    (* Dec ku *)
    val _ = EBk (AQg "?st'. evaluate (" Dku ", sCore2) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord (" ^ f1acc ^ ")", "sCore2 with locals := _ = sKu"))
    val _ = EBk (AQg "?st'. evaluate (" Aku ", sCore2) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    (* CORE2 ; KmR5 *)
    val _ = EBk (AQg "evaluate (" CORE2 ", sRBb) = (NONE, sCore2)") (irule Annot_Seq >> fs [])
    val _ = EBk (AQg "?st'. evaluate (" KmR5 ", sRBb) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sCore2") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    (* Assign b/i/acc/len/base *)
    val _ = EBk (AQg "evaluate (" AsgBz ", sRI) = (NONE, sRBb)") (irule Annot_Seq >> first_assum ACCEPT_TAC)
    val _ = EBk (AQg "?st'. evaluate (" KmR4 ", sRI) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sRBb") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    val _ = EBk (AQg "evaluate (" AsgI ", sRA) = (NONE, sRI)") (irule Annot_Seq >> first_assum ACCEPT_TAC)
    val _ = EBk (AQg "?st'. evaluate (" KmR3 ", sRA) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sRI") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    val _ = EBk (AQg "evaluate (" AsgA ", sRL) = (NONE, sRA)") (irule Annot_Seq >> first_assum ACCEPT_TAC)
    val _ = EBk (AQg "?st'. evaluate (" KmR2 ", sRL) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sRA") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    val _ = EBk (AQg "evaluate (" AsgL ", sRB) = (NONE, sRL)") (irule Annot_Seq >> first_assum ACCEPT_TAC)
    val _ = EBk (AQg "?st'. evaluate (" KmR1 ", sRB) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sRL") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    val _ = EBk (AQg "evaluate (" AsgB ", sKm) = (NONE, sRB)") (irule Annot_Seq >> first_assum ACCEPT_TAC)
    val _ = EBk (AQg "?st'. evaluate (" KmBody ", sKm) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sRB") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    (* Dec km *)
    val _ = EBk (AQg "?st'. evaluate (" Dkm ", sCore1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord (" ^ f0acc ^ ")", "sCore1 with locals := _ = sKm"))
    val _ = EBk (AQg "?st'. evaluate (" Akm ", sCore1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    (* CORE1 ; RB1 *)
    val _ = EBk (AQg "evaluate (" CORE1 ", sB0) = (NONE, sCore1)") (irule Annot_Seq >> fs [])
    val _ = EBk (AQg "?st'. evaluate (" RB1 ", sB0) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "sCore1") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    (* Dec b/i/acc/len *)
    val _ = EBk (AQg "?st'. evaluate (" Db ", sI) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord 0w", "sI with locals := _ = sB0"))
    val _ = EBk (AQg "?st'. evaluate (" Ai ", sI) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    val _ = EBk (AQg "?st'. evaluate (" Di ", sAcc) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord 0w", "sAcc with locals := _ = sI"))
    val _ = EBk (AQg "?st'. evaluate (" Aacc ", sAcc) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    val _ = EBk (AQg "?st'. evaluate (" Dacc ", sLen) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord 0w", "sLen with locals := _ = sAcc"))
    val _ = EBk (AQg "?st'. evaluate (" Alen ", sLen) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    val _ = EBk (AQg "?st'. evaluate (" Dlen ", s1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord (n2w (" ^ f0len ^ "))", "s1 with locals := _ = sLen"))
    val _ = EBk (AQg "?st'. evaluate (" AL ", s1) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    (* loadSeq ; SEQld *)
    val _ = EBk (AQg "evaluate (" loadSeq ", sBase) = (NONE, s1)") (irule Annot_Seq >> first_assum ACCEPT_TAC)
    val _ = EBk (AQg "?st'. evaluate (" SEQld ", sBase) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (irule Seq_trace >> qexists_tac (QS "s1") >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, (imp_res_tac evaluate_clock >> fs [] >> NO_TAC), (fs [] >> NO_TAC), metis_tac []])
    (* Dec base, Dec ctrl, mainBody *)
    val _ = EBk (QS "eval s0 BaseAddr = SOME (ValWord ba)") (simp [eval_def, ABB "ba"])
    val _ = EBk (QS "FLOOKUP sCtrl.locals «ctrl» = SOME (ValWord ba)") (simp [ABB "sCtrl", FLOOKUP_UPDATE] >> fs [])
    val _ = EBk (QS ("eval sCtrl (Op Add [Var Local «ctrl»; Const " ^ arena0 ^ "]) = SOME (ValWord (ba + " ^ arena0 ^ "))"))
      (irule eval_ctrl_add >> fs [])
    val _ = EBk (AQg "?st'. evaluate (" Dbase ", sCtrl) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord (ba + " ^ arena0 ^ ")", "sCtrl with locals := _ = sBase"))
    val _ = EBk (AQg "?st'. evaluate (" body_c ", sCtrl) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr") annotw
    val _ = EBk (AQg "?st'. evaluate (" Dctrl ", s0) = (SOME (Return (ValWord 0w)), st') /\\ st'.ffi.io_events = tr")
      (decw ("ValWord ba", "s0 with locals := _ = sCtrl"))
    val _ = EBk (QS ("?sF. evaluate (" ^ mainBodyName ^ ", s0) = (SOME (Return (ValWord 0w)), sF) /\\ sF.ffi.io_events = tr"))
      (simp [Once mainBodyDef] >> annotw)
    val _ = e (pop_assum strip_assume_tac)
    val _ = e (qexists_tac (QS "sF") >> qexists_tac (QS "loadEv") >> qexists_tac (QS "rb"))
    val _ = e (conj_tac >- first_assum ACCEPT_TAC)
    val _ = e (fs [ABB "tr"])
    val thm = top_thm ()
    val _ = proofManagerLib.drop ()
    val _ = save_thm (prefix ^ "MainBody_refines", thm)
  in thm end;

(* -- the whole wrapper: MainRefine + Sem + Install + EndToEnd (C21-template tail) -- *)
fun mk_composedWrapper
      (spec as { prefix, ffiName, ffiDef, ffiArgs, stagedDef, clockBound, arena0,
        fold0, fold1, scalars, decVar, gateName, gateThm, storeOff, resultWord,
        mainBodyName, mainBodyDef, progName, progDef, linkB, unfoldCore }) =
  let
    fun TM s = Term (QS s)
    val traceOf = fn sv =>
      sv ^ ".ffi.io_events ++ loadEv ++\n" ^
      "  [IO_event (ffi$ExtCall «report_vec»)\n" ^
      "     (word_to_bytes (" ^ resultWord ^ " : word64) F) rb]"
    val ffiApp = ffiName ^ " " ^ ffiArgs
    val mainRefine = mk_composedMainRefine
      { prefix=prefix, ffiName=ffiName, ffiDef=ffiDef, ffiArgs=ffiArgs, stagedDef=stagedDef,
        clockBound=clockBound, arena0=arena0, fold0=fold0, fold1=fold1, scalars=scalars,
        decVar=decVar, gateName=gateName, gateThm=gateThm, storeOff=storeOff,
        resultWord=resultWord, mainBodyName=mainBodyName, mainBodyDef=mainBodyDef }

    val callMainRun = prove (
      TM (
        "FLOOKUP (s'':(64,'ffi)panSem$state).code «main» = SOME ([], " ^ mainBodyName ^ ") /\\ " ^
        "s''.clock <> 0 /\\ " ^ ffiApp ^ " ((dec_clock s'') with locals := FEMPTY) /\\ " ^
        clockBound ^ " <= (dec_clock s'').clock ==> " ^
        "?t loadEv rb. evaluate (Call NONE «main» [], s'') = (SOME (Return (ValWord 0w)), t) /\\ " ^
        "t.ffi.io_events = " ^ traceOf "s''"),
      strip_tac >>
      qabbrev_tac (QS "s0 = (dec_clock s'') with locals := FEMPTY") >>
      (QS ("s0.locals = FEMPTY /\\ " ^ clockBound ^ " <= s0.clock /\\ " ^ ffiApp ^ " s0 /\\ s0.ffi = s''.ffi")) by
         (fs [ABB "s0", dec_clock_def]) >>
      drule_all mainRefine >> strip_tac >>
      qmatch_asmsub_rename_tac (QS ("evaluate (" ^ mainBodyName ^ ", s0) = (SOME (Return (ValWord 0w)), sF)")) >>
      (QS "sF.clock <= s0.clock") by (imp_res_tac evaluate_clock >> fs []) >>
      (QS ("evaluate (" ^ mainBodyName ^ ", dec_clock s'' with locals := FEMPTY) = (SOME (Return (ValWord 0w)), sF)"))
         by (fs [ABB "s0"]) >>
      map_every (fn q => qexists_tac (QS q)) ["empty_locals sF", "loadEv", "rb"] >>
      conj_tac
      >- (simp [Once evaluate_def, OPT_MMAP_def] >> gvs [lookup_code_def, FUPDATE_LIST_THM]) >>
      fs [empty_locals_def])
    val _ = save_thm (prefix ^ "_call_main_run", callMainRun)

    val mainSemantics = prove (
      TM (
        "FLOOKUP (s':(64,'ffi)panSem$state).code «main» = SOME ([], " ^ mainBodyName ^ ") /\\ " ^
        "(!K. " ^ ffiApp ^ " ((dec_clock (s' with clock := K)) with locals := FEMPTY)) /\\ " ^
        "(?K. 0 < K /\\ " ^ clockBound ^ " < K) ==> " ^
        "?loadEv rb. semantics s' «main» = Terminate Success (" ^ traceOf "s'" ^ ")"),
      strip_tac >>
      rename1 (QS (clockBound ^ " < K0")) >>
      qabbrev_tac (QS "sc = s' with clock := K0") >>
      (QS "sc.code = s'.code /\\ sc.ffi = s'.ffi /\\ sc.clock = K0") by (simp [ABB "sc"]) >>
      (QS ("FLOOKUP sc.code «main» = SOME ([], " ^ mainBodyName ^ ")")) by (fs []) >>
      (QS "sc.clock <> 0") by (fs []) >>
      (QS (ffiApp ^ " ((dec_clock sc) with locals := FEMPTY)")) by
         (first_x_assum (qspec_then (QS "K0") mp_tac) >> simp [ABB "sc"]) >>
      (QS (clockBound ^ " <= (dec_clock sc).clock")) by (simp [dec_clock_def] >> fs []) >>
      drule_all callMainRun >> strip_tac >>
      qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >>
      (QS "evaluate (Call NONE «main» [], s' with clock := K0) = (SOME (Return (ValWord 0w)), t)")
         by (fs [ABB "sc"]) >>
      drule semantics_Return_lift >> strip_tac >>
      (QS ("t.ffi.io_events = " ^ traceOf "s'")) by
         (qpat_x_assum (QS "t.ffi.io_events = _") mp_tac >> simp [ABB "sc"]) >>
      simp [])
    val _ = save_thm (prefix ^ "_main_semantics", mainSemantics)

    val decs_ev = (REWRITE_CONV [progDef] THENC EVAL) (TM ("decs_stcnames [] " ^ progName))
    val evd_ev  = (REWRITE_CONV [progDef] THENC EVAL)
                    (TM ("evaluate_decls ((s:(64,'ffi) panSem$state) with structs := []) " ^ progName))
    val semanticsDecls = prove (
      TM (
        "(s:(64,'ffi) panSem$state).code = FEMPTY /\\ " ^ ffiApp ^ " s /\\ " ^
        "(?K. 0 < K /\\ " ^ clockBound ^ " < K) ==> " ^
        "?loadEv rb. semantics_decls s «main» " ^ progName ^ " = Terminate Success (" ^ traceOf "s" ^ ")"),
      strip_tac >>
      qabbrev_tac (QS ("s' = THE (evaluate_decls (s with structs := []) " ^ progName ^ ")")) >>
      (QS ("semantics_decls s «main» " ^ progName ^ " = semantics s' «main»"))
         by (simp [semantics_decls_def, decs_ev, evd_ev, ABB "s'"]) >>
      (QS ("FLOOKUP s'.code «main» = SOME ([], " ^ mainBodyName ^ ")"))
         by (simp [ABB "s'"] >> REWRITE_TAC [progDef] >> EVAL_TAC >> REWRITE_TAC unfoldCore) >>
      (QS "s'.base_addr = s.base_addr /\\ s'.ffi = s.ffi")
         by (simp [ABB "s'"] >> REWRITE_TAC [progDef] >> EVAL_TAC) >>
      (QS ("!Kc. " ^ ffiApp ^ " ((dec_clock (s' with clock := Kc)) with locals := FEMPTY)"))
         by (gen_tac >> qpat_x_assum (QS (ffiApp ^ " s")) mp_tac >>
             asm_simp_tac (srw_ss()) [ffiDef, dec_clock_def]) >>
      (QS ("?loadEv rb. semantics s' «main» = Terminate Success (" ^ traceOf "s'" ^ ")"))
         by (irule mainSemantics >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac [])) >>
      qexists_tac (QS "loadEv") >> qexists_tac (QS "rb") >> gvs [])
    val _ = save_thm (prefix ^ "Prog_semantics_decls", semanticsDecls)

    val linkB_ant   = linkB |> concl |> dest_imp |> #1
    val linkB_concl = linkB |> concl |> dest_imp |> #2
    val sd_tm = find_term (fn t => same_const (fst (strip_comb t)) “semantics_decls” handle _ => false) linkB_concl
    val notFail_tm = valOf (List.find (fn c => is_neg c andalso
        (let val ee = dest_neg c in is_eq ee andalso
           (same_const (fst (strip_comb (lhs ee))) “semantics_decls” handle _ => false) end))
        (boolSyntax.strip_conj linkB_ant))
    val pkg_tm = list_mk_conj (filter (fn c => not (aconv c notFail_tm)) (boolSyntax.strip_conj linkB_ant))
    val trace_tm = TM (traceOf "(s:(64,'ffi) panSem$state)")
    val subset_sd = linkB_concl
    val subset_spec = subst [sd_tm |-> Term [QUOTE "Terminate Success ", ANTIQUOTE trace_tm]] linkB_concl
    val e2e_goal =
      mk_imp (list_mk_conj [pkg_tm, TM (ffiApp ^ " (s:(64,'ffi) panSem$state)"),
                            TM ("?K. 0 < K /\\ " ^ clockBound ^ " < K")],
              mk_exists (TM "loadEv:io_event list",
                mk_exists (TM "rb:(word8 # word8) list", subset_spec)))
    val exists_big = prove (TM "!n:num. ?K. 0 < K /\\ n < K", gen_tac >> qexists_tac (QS "SUC n") >> DECIDE_TAC)
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
      qpat_x_assum ([QUOTE "", ANTIQUOTE sd_tm, QUOTE " = _"]) (fn th => gvs [th]))
    val _ = save_thm (prefix ^ "_machine_code", machineCode)
  in
    { mainRefine = mainRefine, callMainRun = callMainRun, mainSemantics = mainSemantics,
      semanticsDecls = semanticsDecls, machineCode = machineCode }
  end;

end

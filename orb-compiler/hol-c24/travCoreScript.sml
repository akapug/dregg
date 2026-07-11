(* ===========================================================================
   C24 — the traversal gate stage CORE: a single path-scan fold (a 5-state
   escape automaton) + the scalar gate that maps the final automaton state to
   the traversal decision (1 = BLOCKED, 0 = ALLOWED).  drorb Reactor/Deploy.lean
   traversalStage / targetEscapes / escapesSegs = (decodeSegs segs).contains "..".

   A GENUINELY DIFFERENT fold from the C21 hash / clen Horner: a finite-state
   escape automaton (branchy body), not an arithmetic accumulator.  The fold body
   escBody and the gate travGate are EXTRACTED from the VERIFIED parser's output
   on traversal.pnk (genuine parser subterms by construction — leanc OUT of the
   TCB); the surgery in travData confirms they refold the deployed main body.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory foldWrapCommonTheory c14GenericTheory composedCommonTheory
     panAutoTheory travLinkBInstTheory;

val _ = new_theory "travCore";

(* ---- the machine-word accumulator step: the 5-state escape automaton ----
   state 0 = at a segment boundary (previous byte was '/' or start)
   state 1 = one leading '.' in the current segment
   state 2 = exactly two leading '.' ("..") in the current segment
   state 3 = current segment is "dirty" (a non-dot byte, or > 2 dots)
   state 4 = ESCAPE FOUND (absorbing) — a ".." segment was closed by '/'      *)
Definition escAcc_def:
  escAcc (a:word64) (b:word64) : word64 =
    if a = 4w then 4w
    else if b = 47w then (if a = 2w then 4w else 0w)
    else if b = 46w then (if a = 0w then 1w else if a = 1w then 2w else 3w)
    else 3w
End

(* ---- the Lean SPEC over the path bytes: the escape automaton's final state ---- *)
Definition travEsc_def:
  travEsc (input:num list) : word64 =
    FOLDL escAcc 0w (MAP (\c. (n2w c):word64) input)
End

(* ---- the traversal DECISION: blocked iff the final state is 4 (an internal
   ".." segment closed by '/') or 2 (a trailing bare ".." segment) ---- *)
Definition travDecide_def:
  travDecide (input:num list) : word64 =
    if travEsc input = 4w then 1w else if travEsc input = 2w then 1w else 0w
End

(* ===========================================================================
   EXTRACT the fold body / while-loop / gate as genuine subterms of travProg.
   =========================================================================== *)
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val rd = rand;
val funcs_body = (REWRITE_CONV [travProg_def] THENC EVAL) “functions travProg”
                   |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair
                    |> (fn xs => List.nth (xs, 2)) |> inst64;

(* navigate the deployed main body down to the fold-loop and the gate *)
val Dctrl = rd body_tm;   val ic = rd Dctrl;
val Dbase = rd ic;        val ib = rd Dbase;
val AL    = rd ib;        val Dlen = rd AL;
val il    = rd Dlen;      val Dacc = rd il;
val ia    = rd Dacc;      val Di   = rd ia;
val ii    = rd Di;        val Db   = rd ii;
val innerB = rd Db;
val coreSeq   = rd (rator innerB);   (* Seq (Annot..) (While foldGuard escBody) *)
val whileNode = rd coreSeq;          (* While <guard> <body>                    *)
val guard_tm  = rd (rator whileNode);
val escBody_tm = rd whileNode;
val rightB    = rd innerB;           (* Seq (Annot..) (Dec «dec» 0w GATEETC)    *)
val Ddec      = rd rightB;
val gateetc   = rd Ddec;             (* Seq gateSeq (Seq store (Seq report ret)) *)
val gateSeq   = rd (rator gateetc);  (* Seq (Annot..) (If <gate>)               *)
val travGate_tm = rd gateSeq;

(* the extracted fold-body split for the step proof (no hand transcription) *)
val bAssignSeq = rd (rator escBody_tm);         (* Seq (Annot..) (Assign «b» ..)  *)
val restSeq    = rd escBody_tm;                 (* Seq ifnestSeq iAssignSeq        *)
val ifnestSeq  = rd (rator restSeq);            (* Seq (Annot..) (If «acc»=4 ..)   *)
val iAssignSeq = rd restSeq;                     (* Seq (Annot..) (Assign «i» ..)   *)

(* sanity: the parsed while-guard is exactly foldGuard *)
val foldGuard_rhs = foldGuard_def |> concl |> rhs |> inst64;
val _ = if aconv guard_tm foldGuard_rhs then ()
        else raise Fail "traversal while-guard is not foldGuard";

val escBody_def  = new_definition ("escBody_def",
                     mk_eq (mk_var ("escBody",  type_of escBody_tm),  escBody_tm));
val travGate_def = new_definition ("travGate_def",
                     mk_eq (mk_var ("travGate", type_of travGate_tm), travGate_tm));

Definition escLoop_def:
  escLoop = While foldGuard escBody
End

(* escLoop refolds to the genuine parser while-node *)
Theorem escLoop_eq_parser:
  escLoop = ^whileNode
Proof
  simp [escLoop_def, escBody_def, foldGuard_def]
QED

(* ---- the per-step fill-in: one iteration of the parsed body advances the fold
   by escAcc.  The branchy body reduces by case analysis on the automaton
   guards; each leaf is a single constant assign. ---- *)
Theorem escBody_step:
  !i acc (s:(64,'ffi) panSem$state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (escBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (escAcc acc (n2w (EL i input):word64)) s2
Proof
  rpt strip_tac >>
  `FLOOKUP s.locals «base» = SOME (ValWord bs) /\
   FLOOKUP s.locals «i»    = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «acc»  = SOME (ValWord acc) /\
   FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input)))` by fs [foldInv_def] >>
  `?bb. FLOOKUP s.locals «b» = SOME (ValWord bb)` by fs [foldInv_def] >>
  `eval s (LoadByte (Op Add [Var Local «base»; Var Local «i»])) =
     SOME (ValWord (n2w (EL i input):word64))` by (drule_all eval_foldByte >> simp []) >>
  qabbrev_tac `byte = (n2w (EL i input)):word64` >>
  (* step 1: b := byte *)
  qabbrev_tac `sb = set_var «b» (ValWord byte) s` >>
  `evaluate (^bAssignSeq, s) = (NONE, sb)`
     by (simp [Abbr `sb`] >> irule Annot_Seq >> irule evaluate_Assign_val >>
         fs [] >> metis_tac []) >>
  `FLOOKUP sb.locals «acc» = SOME (ValWord acc) /\
   FLOOKUP sb.locals «b»   = SOME (ValWord byte) /\
   FLOOKUP sb.locals «i»   = SOME (ValWord (n2w i)) /\
   FLOOKUP sb.locals «base»= SOME (ValWord bs) /\
   FLOOKUP sb.locals «len» = SOME (ValWord (n2w (LENGTH input)))`
     by (simp [Abbr `sb`, set_var_def, FLOOKUP_UPDATE]) >>
  `sb.memory = s.memory /\ sb.memaddrs = s.memaddrs /\ sb.be = s.be /\ sb.clock = s.clock`
     by simp [Abbr `sb`, set_var_def] >>
  (* the automaton guard evals in sb *)
  `eval sb (Cmp Equal (Var Local «acc») (Const 4w)) = SOME (ValWord (if acc = 4w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «b») (Const 47w)) = SOME (ValWord (if byte = 47w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «b») (Const 46w)) = SOME (ValWord (if byte = 46w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 2w)) = SOME (ValWord (if acc = 2w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 0w)) = SOME (ValWord (if acc = 0w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 1w)) = SOME (ValWord (if acc = 1w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  (* step 2: the IF-nest reduces to acc := escAcc acc byte *)
  qabbrev_tac `sacc = set_var «acc» (ValWord (escAcc acc byte)) sb` >>
  `evaluate (^ifnestSeq, sb) = (NONE, sacc)`
     by (Cases_on `acc = 4w` >> Cases_on `byte = 47w` >> Cases_on `byte = 46w` >>
         Cases_on `acc = 2w` >> Cases_on `acc = 0w` >> Cases_on `acc = 1w` >>
         full_simp_tac (srw_ss()) [Abbr `sacc`, escAcc_def] >>
         asm_simp_tac (srw_ss())
           [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const, evaluate_def,
            cond1w_ne0, set_var_def, FLOOKUP_UPDATE] >>
         gvs [set_var_def, FLOOKUP_UPDATE]) >>
  `FLOOKUP sacc.locals «i» = SOME (ValWord (n2w i)) /\
   FLOOKUP sacc.locals «acc» = SOME (ValWord (escAcc acc byte)) /\
   FLOOKUP sacc.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
   FLOOKUP sacc.locals «base» = SOME (ValWord bs) /\
   (?bw. FLOOKUP sacc.locals «b» = SOME (ValWord bw)) /\
   sacc.memory = s.memory /\ sacc.memaddrs = s.memaddrs /\ sacc.be = s.be /\ sacc.clock = s.clock`
     by (simp [Abbr `sacc`, set_var_def, FLOOKUP_UPDATE] >> metis_tac []) >>
  (* step 3: i := i + 1 *)
  qabbrev_tac `sfin = set_var «i» (ValWord (n2w i + 1w)) sacc` >>
  `eval sacc (Op Add [Var Local «i»; Const 1w]) = SOME (ValWord (n2w i + 1w))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]) >>
  `evaluate (^iAssignSeq, sacc) = (NONE, sfin)`
     by (simp [Abbr `sfin`] >> irule Annot_Seq >> irule evaluate_Assign_val >>
         fs [] >> metis_tac []) >>
  (* compose the body from the three step evaluates *)
  `evaluate (Seq ^ifnestSeq ^iAssignSeq, sb) = (NONE, sfin)`
     by (irule Seq_thread >> qexists_tac `sacc` >> fs [Abbr `sfin`]) >>
  `evaluate (escBody, s) = (NONE, sfin)`
     by (simp [escBody_def] >> irule Seq_thread >> qexists_tac `sb` >>
         fs [Abbr `sb`, set_var_def]) >>
  qexists_tac `sfin` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (simp [Abbr `sfin`, set_var_def] >> fs []) >>
  simp [foldInv_def, Abbr `sfin`, set_var_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def] >> rw [] >> fs []
QED

(* ---- mem/ctrl preservation (mechanical: blast through the branchy body) ---- *)
Theorem escBody_mem:
  !(s0:(64,'ffi) panSem$state) r s1. evaluate (escBody, s0) = (r,s1) ==> s1.memory = s0.memory
Proof
  rpt gen_tac >> simp [escBody_def, evaluate_def, COND_RAND, COND_RATOR] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs(), COND_RAND, COND_RATOR, evaluate_def,
        set_var_def, set_kvar_def, kvar_defs, empty_locals_def]) >>
  rw [] >> gvs [set_var_def]
QED

Theorem escBody_ctrl:
  !(s0:(64,'ffi) panSem$state) r s1. evaluate (escBody, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [escBody_def, evaluate_def, COND_RAND, COND_RATOR] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs(), COND_RAND, COND_RATOR, evaluate_def,
        set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def]) >>
  rw [] >> gvs [set_var_def, FLOOKUP_UPDATE]
QED

Theorem escLoop_noFFI:
  noFFI escLoop
Proof
  simp [escLoop_def, escBody_def, foldGuard_def, noFFI_def]
QED

(* ---- THE framed fold core, from the body-generic loop_frame ---- *)
Theorem escLoop_framed:
  foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
  ?s'. evaluate (escLoop, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc» = SOME (ValWord (travEsc input)) /\
       FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
       FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
       FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
       (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
       (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
       s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
       s.clock - LENGTH input <= s'.clock /\ s'.clock <= s.clock
Proof
  strip_tac >>
  `?s'. evaluate (While foldGuard escBody, s) = (NONE, s') /\
        FLOOKUP s'.locals «acc» = SOME (ValWord (FOLDL escAcc 0w (MAP (\c. (n2w c):word64) input))) /\
        FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
        FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
        FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
        (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
        (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
        s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
        s.clock - LENGTH input <= s'.clock /\ s'.clock <= s.clock`
    by (irule loop_frame >> rpt conj_tac >>
        TRY (rpt strip_tac >> irule escBody_step >> fs [] >> NO_TAC) >>
        TRY (rpt strip_tac >> irule escBody_mem >> metis_tac [] >> NO_TAC) >>
        TRY (rpt strip_tac >> irule escBody_ctrl >> metis_tac [] >> NO_TAC) >>
        fs []) >>
  qexists_tac `s'` >> fs [escLoop_def, travEsc_def]
QED

Theorem travGate_noFFI:
  noFFI travGate
Proof
  REWRITE_TAC [travGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = travDecide input, reading the fold result in «acc» *)
Theorem evaluate_travGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «acc» = SOME (ValWord (travEsc input)) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ==>
  ?s'. evaluate (travGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (travDecide input)) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `eval s (Cmp Equal (Var Local «acc») (Const 4w)) =
     SOME (ValWord (if travEsc input = 4w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval s (Cmp Equal (Var Local «acc») (Const 2w)) =
     SOME (ValWord (if travEsc input = 2w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  Cases_on `travEsc input = 4w` >> Cases_on `travEsc input = 2w` >>
  full_simp_tac (srw_ss()) [] >>
  simp [travGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, travDecide_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();

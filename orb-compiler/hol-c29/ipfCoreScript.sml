(* ===========================================================================
   C29 — the ipfilter CIDR admission gate stage CORE: a single address-scan fold
   (a prefix matcher against the deployed deny CIDR 10.0.0.0/8) + the scalar gate
   that maps the final matcher state to the admit decision (1 = ADMIT, 0 = BLOCKED).
   drorb Reactor/Stage/IpFilter.lean ipfilterStage / WireIpFilter.deployAdmits =
   IpFilter.permits deployRuleset, deployRuleset = one deny rule 10.0.0.0/8 with
   default-admit.  The ordered deny-precedence access decision over the deployed
   single-deny-rule ruleset collapses to: admit iff NOT (v4 AND first-8-bits match).

   A GENUINELY DIFFERENT fold from the C21 hash / C24 escape automaton: a
   position-carrying prefix matcher over the deny prefix T = [4,0,0,0,0,1,0,1,0]
   (family tag byte + the 8 network bits of 10 = 00001010).  The fold body cidrBody
   and the gate ipfGate are EXTRACTED from the VERIFIED parser's output on ipf.pnk
   (genuine parser subterms by construction — leanc OUT of the TCB); the surgery in
   ipfData confirms they refold the deployed main body.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory foldWrapCommonTheory c14GenericTheory composedCommonTheory
     panAutoTheory ipfLinkBInstTheory;

val _ = new_theory "ipfCore";

(* ---- the machine-word accumulator step: the CIDR-prefix matcher automaton ----
   state k in 0..8 = the first k bytes of the deny prefix T matched in sequence
                     (on track); the next expected byte is T[k]:
                       T[0]=4 (family tag v4), T[1..4]=0, T[5]=1, T[6]=0, T[7]=1, T[8]=0
                     (the tag byte then the 8 network bits of 10 = 00001010).
   state 9  = ALL 9 prefix bytes matched -> the client IS in 10.0.0.0/8 (ABSORBING;
              the remaining address bits are ignored — the ruleset walk's early-exit
              rendered as an accumulate-and-absorb bounded fold, no true break).
   state 10 = a prefix byte MISMATCHED -> never in the deny block (ABSORBING sink). *)
Definition cidrAcc_def:
  cidrAcc (a:word64) (b:word64) : word64 =
    if a = 9w then 9w
    else if a = 0w then (if b = 4w then 1w else 10w)
    else if a = 1w then (if b = 0w then 2w else 10w)
    else if a = 2w then (if b = 0w then 3w else 10w)
    else if a = 3w then (if b = 0w then 4w else 10w)
    else if a = 4w then (if b = 0w then 5w else 10w)
    else if a = 5w then (if b = 1w then 6w else 10w)
    else if a = 6w then (if b = 0w then 7w else 10w)
    else if a = 7w then (if b = 1w then 8w else 10w)
    else if a = 8w then (if b = 0w then 9w else 10w)
    else 10w
End

(* ---- the Lean SPEC over the encoded address bytes: the prefix matcher's final
   state.  input = Reactor.Stage.IpFilter.encodeAddr a = family tag :: 0/1 bytes ---- *)
Definition ipfMatch_def:
  ipfMatch (input:num list) : word64 =
    FOLDL cidrAcc 0w (MAP (\c. (n2w c):word64) input)
End

(* ---- the ADMIT DECISION: admit (1) iff the deny prefix did NOT fully match
   (final state <> 9); blocked (0) iff the client is inside 10.0.0.0/8 (state 9).
   Decision-equivalent to WireIpFilter.deployAdmits for the deployed ruleset:
   deny-precedence with one deny rule + default-admit = negate the CIDR match. ---- *)
Definition ipfDecide_def:
  ipfDecide (input:num list) : word64 =
    if ipfMatch input = 9w then 0w else 1w
End

(* ===========================================================================
   EXTRACT the fold body / while-loop / gate as genuine subterms of ipfProg.
   =========================================================================== *)
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val rd = rand;
val funcs_body = (REWRITE_CONV [ipfProg_def] THENC EVAL) “functions ipfProg”
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
val coreSeq   = rd (rator innerB);   (* Seq (Annot..) (While foldGuard cidrBody) *)
val whileNode = rd coreSeq;          (* While <guard> <body>                     *)
val guard_tm  = rd (rator whileNode);
val cidrBody_tm = rd whileNode;
val rightB    = rd innerB;           (* Seq (Annot..) (Dec «dec» 0w GATEETC)     *)
val Ddec      = rd rightB;
val gateetc   = rd Ddec;             (* Seq gateSeq (Seq store (Seq report ret))  *)
val gateSeq   = rd (rator gateetc);  (* Seq (Annot..) (If <gate>)                *)
val ipfGate_tm = rd gateSeq;

(* the extracted fold-body split for the step proof (no hand transcription) *)
val bAssignSeq = rd (rator cidrBody_tm);        (* Seq (Annot..) (Assign «b» ..)  *)
val restSeq    = rd cidrBody_tm;                (* Seq ifnestSeq iAssignSeq        *)
val ifnestSeq  = rd (rator restSeq);            (* Seq (Annot..) (If «acc»=9 ..)   *)
val iAssignSeq = rd restSeq;                     (* Seq (Annot..) (Assign «i» ..)   *)

(* sanity: the parsed while-guard is exactly foldGuard *)
val foldGuard_rhs = foldGuard_def |> concl |> rhs |> inst64;
val _ = if aconv guard_tm foldGuard_rhs then ()
        else raise Fail "ipfilter while-guard is not foldGuard";

val cidrBody_def = new_definition ("cidrBody_def",
                     mk_eq (mk_var ("cidrBody", type_of cidrBody_tm), cidrBody_tm));
val ipfGate_def  = new_definition ("ipfGate_def",
                     mk_eq (mk_var ("ipfGate", type_of ipfGate_tm), ipfGate_tm));

Definition cidrLoop_def:
  cidrLoop = While foldGuard cidrBody
End

(* cidrLoop refolds to the genuine parser while-node *)
Theorem cidrLoop_eq_parser:
  cidrLoop = ^whileNode
Proof
  simp [cidrLoop_def, cidrBody_def, foldGuard_def]
QED

(* ---- the per-step fill-in: one iteration of the parsed body advances the fold
   by cidrAcc.  The 10-way prefix cascade collapses via evaluate_If_reduce +
   cond1w_ne0 (the panAutoLib decision-cascade idiom); each leaf is a single
   constant assign, so NO case explosion is needed. ---- *)
Theorem cidrBody_step:
  !i acc (s:(64,'ffi) panSem$state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (cidrBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (cidrAcc acc (n2w (EL i input):word64)) s2
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
  (* the automaton guards eval in sb *)
  `eval sb (Cmp Equal (Var Local «acc») (Const 9w)) = SOME (ValWord (if acc = 9w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 0w)) = SOME (ValWord (if acc = 0w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 1w)) = SOME (ValWord (if acc = 1w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 2w)) = SOME (ValWord (if acc = 2w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 3w)) = SOME (ValWord (if acc = 3w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 4w)) = SOME (ValWord (if acc = 4w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 5w)) = SOME (ValWord (if acc = 5w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 6w)) = SOME (ValWord (if acc = 6w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 7w)) = SOME (ValWord (if acc = 7w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «acc») (Const 8w)) = SOME (ValWord (if acc = 8w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «b») (Const 4w)) = SOME (ValWord (if byte = 4w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «b») (Const 1w)) = SOME (ValWord (if byte = 1w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval sb (Cmp Equal (Var Local «b») (Const 0w)) = SOME (ValWord (if byte = 0w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  (* step 2: the IF-nest cascade reduces to acc := cidrAcc acc byte *)
  qabbrev_tac `sacc = set_var «acc» (ValWord (cidrAcc acc byte)) sb` >>
  `evaluate (^ifnestSeq, sb) = (NONE, sacc)`
     by (imp_res_tac evaluate_If_reduce >>
         asm_simp_tac (srw_ss())
           [Abbr `sacc`, cidrAcc_def, Annot_Seq_eval, evaluate_Assign_const,
            cond1w_ne0, set_var_def, FLOOKUP_UPDATE] >>
         rw [] >> gvs [set_var_def, FLOOKUP_UPDATE]) >>
  `FLOOKUP sacc.locals «i» = SOME (ValWord (n2w i)) /\
   FLOOKUP sacc.locals «acc» = SOME (ValWord (cidrAcc acc byte)) /\
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
  `evaluate (cidrBody, s) = (NONE, sfin)`
     by (simp [cidrBody_def] >> irule Seq_thread >> qexists_tac `sb` >>
         fs [Abbr `sb`, set_var_def]) >>
  qexists_tac `sfin` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (simp [Abbr `sfin`, set_var_def] >> fs []) >>
  simp [foldInv_def, Abbr `sfin`, set_var_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def] >> rw [] >> fs []
QED

(* ---- mem/ctrl preservation (mechanical: blast through the branchy body) ---- *)
Theorem cidrBody_mem:
  !(s0:(64,'ffi) panSem$state) r s1. evaluate (cidrBody, s0) = (r,s1) ==> s1.memory = s0.memory
Proof
  rpt gen_tac >> simp [cidrBody_def, evaluate_def, COND_RAND, COND_RATOR] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs(), COND_RAND, COND_RATOR, evaluate_def,
        set_var_def, set_kvar_def, kvar_defs, empty_locals_def]) >>
  rw [] >> gvs [set_var_def]
QED

Theorem cidrBody_ctrl:
  !(s0:(64,'ffi) panSem$state) r s1. evaluate (cidrBody, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [cidrBody_def, evaluate_def, COND_RAND, COND_RATOR] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs(), COND_RAND, COND_RATOR, evaluate_def,
        set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def]) >>
  rw [] >> gvs [set_var_def, FLOOKUP_UPDATE]
QED

Theorem cidrLoop_noFFI:
  noFFI cidrLoop
Proof
  simp [cidrLoop_def, cidrBody_def, foldGuard_def, noFFI_def]
QED

(* ---- THE framed fold core, from the body-generic loop_frame ---- *)
Theorem cidrLoop_framed:
  foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
  ?s'. evaluate (cidrLoop, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc» = SOME (ValWord (ipfMatch input)) /\
       FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
       FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
       FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
       (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
       (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
       s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
       s.clock - LENGTH input <= s'.clock /\ s'.clock <= s.clock
Proof
  strip_tac >>
  `?s'. evaluate (While foldGuard cidrBody, s) = (NONE, s') /\
        FLOOKUP s'.locals «acc» = SOME (ValWord (FOLDL cidrAcc 0w (MAP (\c. (n2w c):word64) input))) /\
        FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
        FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
        FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
        (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
        (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
        s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
        s.clock - LENGTH input <= s'.clock /\ s'.clock <= s.clock`
    by (irule loop_frame >> rpt conj_tac >>
        TRY (rpt strip_tac >> irule cidrBody_step >> fs [] >> NO_TAC) >>
        TRY (rpt strip_tac >> irule cidrBody_mem >> metis_tac [] >> NO_TAC) >>
        TRY (rpt strip_tac >> irule cidrBody_ctrl >> metis_tac [] >> NO_TAC) >>
        fs []) >>
  qexists_tac `s'` >> fs [cidrLoop_def, ipfMatch_def]
QED

Theorem ipfGate_noFFI:
  noFFI ipfGate
Proof
  REWRITE_TAC [ipfGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = ipfDecide input, reading the fold result in «acc» *)
Theorem evaluate_ipfGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «acc» = SOME (ValWord (ipfMatch input)) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ==>
  ?s'. evaluate (ipfGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (ipfDecide input)) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `eval s (Cmp Equal (Var Local «acc») (Const 9w)) =
     SOME (ValWord (if ipfMatch input = 9w then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  Cases_on `ipfMatch input = 9w` >>
  full_simp_tac (srw_ss()) [] >>
  simp [ipfGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, ipfDecide_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();

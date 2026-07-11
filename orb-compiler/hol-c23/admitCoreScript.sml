(* ===========================================================================
   C23 — the SECOND composed stage's core: a (method,route) declared-surface
   admission decision (drorb policyStage / deployDecisionOf).  The two hashBytes
   folds are REUSED verbatim from C22 (cacheBodyA1/A2, cacheLoop1/2 + their
   generic framed cores); ONLY the gate + spec are new — a 2-way AND (no
   freshness `<`, structurally different from the C22 cache gate).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory c14GenericTheory
     panAutoTheory;

val _ = new_theory "admitCore";

(* ---------- the composed Lean SPEC: admit iff (method,route) is declared ------ *)
Definition admitDecide_def:
  admitDecide (method:num list) (route:num list) : num =
    if (n2w (hashBytesN method) = (4773603w:word64)) then
      (if (n2w (hashBytesN route) = (821282413w:word64)) then 1n else 0n) else 0n
End

(* ---------- the scalar GATE (verbatim emitted nested If; 2-way AND) ----------- *)
Definition admitGate_def:
  admitGate =
    If (Cmp Equal (Var Local «km») (Const 4773603w))
      (Seq (Annot «location» «(44:7 UNKNOWN)»)
         (If (Cmp Equal (Var Local «ku») (Const 821282413w))
            (Seq (Annot «location» «(45:6 45:12)»)
               (Assign Local «dec» (Const 1w)))
            (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)))
      (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)
End

Theorem admitGate_noFFI:
  noFFI admitGate
Proof
  REWRITE_TAC [admitGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = n2w (admitDecide ...) and touches only «dec» *)
Theorem evaluate_admitGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «km» = SOME (ValWord (n2w (hashBytesN method))) /\
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w (hashBytesN route))) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) ==>
  ?s'. evaluate (admitGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (admitDecide method route))) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `eval s (Cmp Equal (Var Local «km») (Const 4773603w)) =
     SOME (ValWord (if (n2w (hashBytesN method) = (4773603w:word64)) then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval s (Cmp Equal (Var Local «ku») (Const 821282413w)) =
     SOME (ValWord (if (n2w (hashBytesN route) = (821282413w:word64)) then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  Cases_on `n2w (hashBytesN method) = (4773603w:word64)` >>
  Cases_on `n2w (hashBytesN route) = (821282413w:word64)` >>
  full_simp_tac (srw_ss()) [] >>
  simp [admitGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, admitDecide_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();

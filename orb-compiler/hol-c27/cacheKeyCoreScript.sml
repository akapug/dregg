(* ===========================================================================
   C22 — the COMPOSITE CORE for the deployed cacheEmptyStage cache-key path.

   Two hashBytes folds (method arena, target arena) + the C18 isFresh scalar
   gate, sequenced.  Both folds are the SAME deployed fold (drorb keyOf uses
   `hashBytes` for BOTH method and target), so ONE core schema instantiates
   twice — the only per-fold input is the ~16-line step (the emitted While body
   carries distinct location Annots per site, so two body constants).  The two
   folds are threaded so fold #2 preserves fold #1's result (While_frame), and
   the gate combines both fold results with the freshness test.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory foldWrapCommonTheory c14GenericTheory
     panAutoTheory;

val _ = new_theory "cacheKeyCore";

(* ---------- the composed Lean SPEC (drorb keyOf + Store.get? + isFresh) ------
   keyOf c = { method := hashBytes method, uri := hashBytes target } ; the warm
   Config.onReq serves the stored entry iff its key matches (Store.get? exact
   key) AND it is fresh (Meta.isFresh: age < lifetime).  The stored (GET,/) key:
   hashBytes "GET" = 4773603, hashBytes "/" = 48 ; deployed lifetime 100. --------- *)
Definition cacheServe_def:
  cacheServe (method:num list) (target:num list) (age:num) : num =
    if (n2w (hashBytesN method) = (4773603w:word64)) then
      (if (n2w (hashBytesN target) = (48w:word64)) then
        (if age < 100 then 1n else 0n) else 0n) else 0n
End

(* ---------- the two VERBATIM emitted While bodies (parser output) ------------ *)
Definition cacheBodyA1_def:
  cacheBodyA1 =
    Seq
      (Seq (Annot «location» «(25:4 25:18)»)
           (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»]))))
      (Seq
         (Seq (Annot «location» «(26:4 26:23)»)
              (Assign Local «acc»
                 (Op Add [Panop Mul [Var Local «acc»; Const 257w];
                          Var Local «b»; Const 1w])))
         (Seq (Annot «location» «(27:4 27:11)»)
              (Assign Local «i» (Op Add [Var Local «i»; Const 1w]))))
End

Definition cacheBodyA2_def:
  cacheBodyA2 =
    Seq
      (Seq (Annot «location» «(36:4 36:18)»)
           (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»]))))
      (Seq
         (Seq (Annot «location» «(37:4 37:23)»)
              (Assign Local «acc»
                 (Op Add [Panop Mul [Var Local «acc»; Const 257w];
                          Var Local «b»; Const 1w])))
         (Seq (Annot «location» «(38:4 38:11)»)
              (Assign Local «i» (Op Add [Var Local «i»; Const 1w]))))
End

Definition cacheLoop1_def:
  cacheLoop1 = While foldGuard cacheBodyA1
End

Definition cacheLoop2_def:
  cacheLoop2 = While foldGuard cacheBodyA2
End

(* ---------- per-fold step (the ONLY bespoke per-fold proof; ~16 lines) -------- *)
Theorem cacheBodyA1_step:
  !i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (cacheBodyA1, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2
Proof
  rpt strip_tac >>
  `FLOOKUP s.locals «base» = SOME (ValWord bs) /\
   FLOOKUP s.locals «i»    = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «acc»  = SOME (ValWord acc) /\
   FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input)))` by fs [foldInv_def] >>
  `?bb. FLOOKUP s.locals «b» = SOME (ValWord bb)` by fs [foldInv_def] >>
  `eval s (LoadByte (Op Add [Var Local «base»; Var Local «i»])) =
     SOME (ValWord (n2w (EL i input):word64))` by (drule_all eval_foldByte >> simp []) >>
  qexists_tac `set_var «i» (ValWord (n2w i + 1w))
    (set_var «acc» (ValWord (acc * 257w + n2w (EL i input) + 1w))
    (set_var «b»   (ValWord (n2w (EL i input))) s))` >>
  simp [cacheBodyA1_def, evaluate_def, eval_def, is_valid_value_simps, shape_of_def,
        set_var_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def, pan_op_def,
        word_mul_n2w, OPT_MMAP_def] >>
  simp [foldInv_def, hashAcc_def, memRel_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def]
QED

Theorem cacheBodyA2_step:
  !i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (cacheBodyA2, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2
Proof
  rpt strip_tac >>
  `FLOOKUP s.locals «base» = SOME (ValWord bs) /\
   FLOOKUP s.locals «i»    = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «acc»  = SOME (ValWord acc) /\
   FLOOKUP s.locals «len»  = SOME (ValWord (n2w (LENGTH input)))` by fs [foldInv_def] >>
  `?bb. FLOOKUP s.locals «b» = SOME (ValWord bb)` by fs [foldInv_def] >>
  `eval s (LoadByte (Op Add [Var Local «base»; Var Local «i»])) =
     SOME (ValWord (n2w (EL i input):word64))` by (drule_all eval_foldByte >> simp []) >>
  qexists_tac `set_var «i» (ValWord (n2w i + 1w))
    (set_var «acc» (ValWord (acc * 257w + n2w (EL i input) + 1w))
    (set_var «b»   (ValWord (n2w (EL i input))) s))` >>
  simp [cacheBodyA2_def, evaluate_def, eval_def, is_valid_value_simps, shape_of_def,
        set_var_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def, pan_op_def,
        word_mul_n2w, OPT_MMAP_def] >>
  simp [foldInv_def, hashAcc_def, memRel_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def]
QED

(* ---------- each fold closes to n2w (hashBytesN input) via the schema -------- *)
Theorem cacheLoop1_refines:
  !input bs (s:(64,'ffi) state).
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (cacheLoop1, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» = SOME (ValWord ((n2w (hashBytesN input)):word64))
Proof
  rpt strip_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (cacheBodyA1, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule cacheBodyA1_step >> fs []) >>
  drule foldLoop_refines >> disch_then (qspecl_then [`0w`,`s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> simp [cacheLoop1_def, hashBytes_word]
QED

Theorem cacheLoop2_refines:
  !input bs (s:(64,'ffi) state).
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (cacheLoop2, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» = SOME (ValWord ((n2w (hashBytesN input)):word64))
Proof
  rpt strip_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (cacheBodyA2, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule cacheBodyA2_step >> fs []) >>
  drule foldLoop_refines >> disch_then (qspecl_then [`0w`,`s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> simp [cacheLoop2_def, hashBytes_word]
QED

(* ---------- each fold body preserves any local other than b/acc/i ------------ *)
Theorem cacheBodyA1_keeps:
  !(s0:(64,'ffi) state) r s1 v.
    v <> «b» /\ v <> «acc» /\ v <> «i» /\ evaluate (cacheBodyA1, s0) = (r,s1) ==>
    FLOOKUP s1.locals v = FLOOKUP s0.locals v
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `evaluate _ = _` mp_tac >>
  simp [cacheBodyA1_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

Theorem cacheBodyA2_keeps:
  !(s0:(64,'ffi) state) r s1 v.
    v <> «b» /\ v <> «acc» /\ v <> «i» /\ evaluate (cacheBodyA2, s0) = (r,s1) ==>
    FLOOKUP s1.locals v = FLOOKUP s0.locals v
Proof
  rpt gen_tac >> strip_tac >> qpat_x_assum `evaluate _ = _` mp_tac >>
  simp [cacheBodyA2_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

Theorem cacheLoop1_noFFI:
  noFFI cacheLoop1
Proof
  simp [cacheLoop1_def, cacheBodyA1_def, foldGuard_def, noFFI_def]
QED

Theorem cacheLoop2_noFFI:
  noFFI cacheLoop2
Proof
  simp [cacheLoop2_def, cacheBodyA2_def, foldGuard_def, noFFI_def]
QED

(* ---------- the scalar GATE (verbatim emitted nested If) --------------------- *)
Definition cacheGate_def:
  cacheGate =
    If (Cmp Equal (Var Local «km») (Const 4773603w))
       (Seq (Annot «location» «(44:7 UNKNOWN)»)
          (If (Cmp Equal (Var Local «ku») (Const 48w))
             (Seq (Annot «location» «(45:9 UNKNOWN)»)
                (If (Cmp Less (Var Local «age») (Const 100w))
                   (Seq (Annot «location» «(46:8 46:14)»)
                        (Assign Local «dec» (Const 1w)))
                   (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)))
             (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)))
       (Seq (Annot «location» «(UNKNOWN UNKNOWN)») Skip)
End

Theorem cacheGate_noFFI:
  noFFI cacheGate
Proof
  REWRITE_TAC [cacheGate_def] >> EVAL_TAC
QED

(* the gate leaves «dec» = n2w (cacheServe ...) and touches only «dec» *)
Theorem evaluate_cacheGate:
  FLOOKUP (s:(64,'ffi) panSem$state).locals «km» = SOME (ValWord (n2w (hashBytesN method))) /\
  FLOOKUP s.locals «ku» = SOME (ValWord (n2w (hashBytesN target))) /\
  FLOOKUP s.locals «age» = SOME (ValWord (n2w age)) /\
  FLOOKUP s.locals «dec» = SOME (ValWord 0w) /\ age < 4294967296 ==>
  ?s'. evaluate (cacheGate, s) = (NONE, s') /\
       FLOOKUP s'.locals «dec» = SOME (ValWord (n2w (cacheServe method target age))) /\
       (!v. v <> «dec» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v) /\
       s'.ffi = s.ffi /\ s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\
       s'.clock = s.clock /\ s'.base_addr = s.base_addr
Proof
  strip_tac >>
  `age < 9223372036854775808` by fs [] >>
  `eval s (Cmp Equal (Var Local «km») (Const 4773603w)) =
     SOME (ValWord (if (n2w (hashBytesN method) = (4773603w:word64)) then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval s (Cmp Equal (Var Local «ku») (Const 48w)) =
     SOME (ValWord (if (n2w (hashBytesN target) = (48w:word64)) then 1w else 0w))`
     by (asm_simp_tac (srw_ss()) [eval_def, asmTheory.word_cmp_def, OPT_MMAP_def]) >>
  `eval s (Cmp Less (Var Local «age») (Const 100w)) =
     SOME (ValWord (if age < 100 then 1w else 0w))`
     by (irule eval_lt_pinned >> fs []) >>
  Cases_on `n2w (hashBytesN method) = (4773603w:word64)` >>
  Cases_on `n2w (hashBytesN target) = (48w:word64)` >>
  Cases_on `age < 100` >>
  full_simp_tac (srw_ss()) [] >>
  simp [cacheGate_def] >>
  asm_simp_tac (srw_ss()) [evaluate_If_reduce, Annot_Seq_eval, evaluate_Assign_const,
     evaluate_def, cond1w_ne0, set_var_def, cacheServe_def] >>
  gvs [FLOOKUP_UPDATE, set_var_def] >> rw [] >> gvs [FLOOKUP_UPDATE]
QED

val _ = export_theory ();

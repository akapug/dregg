(* ===========================================================================
   C23 — the BODY-GENERIC composed-fold frame machinery.

   C22's `cacheKeyFrame` proved the two-fold frame/clock/exit lemmas per BODY
   (cacheBodyA1/cacheBodyA2).  Here every lemma is quantified over an ARBITRARY
   fold body `bdy` + accumulator step `accf`, with the three body facts
   (single-step / memory-preserving / ctrl-preserving) as antecedents.  Proven
   ONCE, they give any fold in a composed spine its whole framed core from its
   ~16-line step (`mk_composedWrapper` machinery, generalized to N folds).

     * loop_mem            — a body-mem-preserving `While` preserves memory.
     * foldLoop_exit       — the loop-exit `foldInv` at i = LENGTH input.
     * foldLoop_clock      — the clock lower bound s.clock - LENGTH input.
     * loop_frame          — THE generic framed core (acc = FOLDL accf 0w …,
                             all exit shapes, memory/memaddrs/be preserved,
                             clock bounds) — the generic `cacheLoop1_framed`.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     pairTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory foldWrapCommonTheory;

val _ = new_theory "composedCommon";

(* ---------- ctrl-relative word load / assign / ctrl-keyed store ---------- *)
Theorem eval_load_ctrl_off:
  !s ba k w.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\ (ba + k) IN s.memaddrs /\
    s.memory (ba + k) = Word w ==>
    eval s (Load One (Op Add [Var Local «ctrl»; Const k])) = SOME (ValWord w)
Proof
  rpt strip_tac >>
  simp [eval_def, is_wf_shape_def, mem_load_def, OPT_MMAP_def,
        wordLangTheory.word_op_def]
QED

Theorem evaluate_Assign_val:
  FLOOKUP s.locals v = SOME (ValWord old) /\ eval s e = SOME (ValWord w) ==>
  evaluate (Assign Local v e, s) = (NONE, set_var v (ValWord w) s)
Proof
  strip_tac >>
  simp [Once evaluate_def, is_valid_value_def, lookup_kvar_def, shape_of_def,
        set_kvar_def, set_var_def]
QED

Theorem evaluate_store_ctrl_var:
  !s ba w k v.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s.locals v = SOME (ValWord w) /\
    (ba + k) IN s.memaddrs ==>
    evaluate (Store (Op Add [Var Local «ctrl»; Const k]) (Var Local v), s) =
      (NONE, s with memory := ((ba + k) =+ Word w) s.memory)
Proof
  rpt strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        flatten_def, mem_stores_def, mem_store_def]
QED

(* ---------- generic loop-level memory frame (inlined clocked induction) ----- *)
Theorem loop_mem:
  !bdy.
    (!(s0:(64,'ffi) state) r s1. evaluate (bdy, s0) = (r,s1) ==> s1.memory = s0.memory) ==>
    !(s:(64,'ffi) state) s1. evaluate (While foldGuard bdy, s) = (NONE, s1) ==> s1.memory = s.memory
Proof
  gen_tac >>
  disch_then (fn bmem =>
    `!n (s:(64,'ffi) state) s1. s.clock = n /\ evaluate (While foldGuard bdy, s) = (NONE, s1) ==> s1.memory = s.memory`
      suffices_by metis_tac [] >>
    completeInduct_on `n` >> rpt strip_tac >>
    qpat_x_assum `evaluate (While _ _,_) = _` mp_tac >> simp [Once evaluate_def] >>
    Cases_on `eval s foldGuard` >> simp [] >> rename1 `eval s foldGuard = SOME vv` >> Cases_on `vv` >> simp [] >>
    Cases_on `w` >> simp [] >> qmatch_goalsub_rename_tac `if ww <> 0w then _ else _` >>
    reverse (Cases_on `ww <> 0w`) >> simp [] >> Cases_on `n = 0` >> simp [] >>
    Cases_on `evaluate (bdy, dec_clock s)` >> rename1 `evaluate (bdy,dec_clock s) = (rb, sb)` >>
    `sb.clock <= (dec_clock s).clock` by (imp_res_tac evaluate_clock >> fs []) >>
    `fix_clock (dec_clock s) (rb, sb) = (rb, sb)` by (irule fix_clock_id >> fs []) >> simp [] >>
    `sb.memory = s.memory` by (imp_res_tac bmem >> fs [dec_clock_def]) >>
    `sb.clock < n` by fs [dec_clock_def] >>
    Cases_on `rb` >> TRY (rename1 `SOME rr` >> Cases_on `rr`) >> simp [] >> strip_tac >>
    FIRST [ (gvs [] >> NO_TAC),
            (`s1.memory = sb.memory` by (first_x_assum (qspec_then `sb.clock` mp_tac) >> impl_tac >- fs [] >>
               disch_then (qspecl_then [`sb`,`s1`] mp_tac) >> fs []) >> fs []) ])
QED

(* ---------- generic fold-exit foldInv (bounded induction + application) ------ *)
Theorem foldLoop_exit_bounded:
  !accf bdy input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (bdy, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !k i acc (s:(64,'ffi) state).
     foldInv input bs i acc s /\ LENGTH input - i <= k /\ LENGTH input - i <= s.clock ==>
     ?s'. evaluate (While foldGuard bdy, s) = (NONE, s') /\
          foldInv input bs (LENGTH input)
            (FOLDL accf acc (MAP (\c. (n2w c):word64) (DROP i input))) s'
Proof
  ntac 4 gen_tac >>
  disch_then (fn bstep => Induct_on `k` >| [
    (rpt strip_tac >> `i = LENGTH input` by fs [foldInv_def] >>
     `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >> qexists_tac `s` >>
     `evaluate (While foldGuard bdy, s) = (NONE, s)` by (simp [Once evaluate_def]) >>
     `DROP i input = []` by (`LENGTH input <= i` by fs [] >> simp [DROP_LENGTH_TOO_LONG]) >> fs []),
    (rpt strip_tac >> Cases_on `i < LENGTH input` >| [
       (`s.clock <> 0` by fs [] >> mp_tac (MATCH_MP foldLoop_iter bstep) >>
        disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >> impl_tac >- fs [] >> strip_tac >>
        `LENGTH input - (i + 1) <= k` by fs [] >> `LENGTH input - (i + 1) <= s2.clock` by fs [] >>
        last_x_assum (qspecl_then [`i+1`,`accf acc (n2w (EL i input):word64)`,`s2`] mp_tac) >>
        impl_tac >- fs [] >> strip_tac >> qexists_tac `s'` >>
        `DROP i input = EL i input :: DROP (SUC i) input` by (irule DROP_EL_CONS_local >> fs []) >> gvs [ADD1]),
       (`i = LENGTH input` by fs [foldInv_def] >> `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
        qexists_tac `s` >> `evaluate (While foldGuard bdy, s) = (NONE, s)` by (simp [Once evaluate_def]) >>
        `DROP i input = []` by (`LENGTH input <= i` by fs [] >> simp [DROP_LENGTH_TOO_LONG]) >> fs [])])])
QED

Theorem foldLoop_exit:
  !accf bdy input bs (s:(64,'ffi) state).
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (bdy, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) /\
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (While foldGuard bdy, s) = (NONE, s') /\
         foldInv input bs (LENGTH input) (FOLDL accf 0w (MAP (\c. (n2w c):word64) input)) s'
Proof
  rpt strip_tac >>
  drule foldLoop_exit_bounded >>
  disch_then (qspecl_then [`LENGTH input`,`0`,`0w`,`s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >> qexists_tac `s'` >> gvs []
QED

(* ---------- generic clock lower bound ---------- *)
Theorem foldLoop_clock_bounded:
  !accf bdy input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (bdy, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !k i acc (s:(64,'ffi) state) s'.
      foldInv input bs i acc s /\ LENGTH input - i <= k /\ LENGTH input - i <= s.clock /\
      evaluate (While foldGuard bdy, s) = (NONE, s') ==>
      s.clock - (LENGTH input - i) <= s'.clock
Proof
  ntac 4 gen_tac >>
  disch_then (fn bstep => Induct_on `k` >| [
      (rpt strip_tac >> `i <= LENGTH input` by fs [foldInv_def] >> `i = LENGTH input` by DECIDE_TAC >>
       `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
       `s' = s` by (qpat_x_assum `evaluate (While foldGuard bdy, s) = (NONE, s')` mp_tac >>
                    asm_simp_tac (srw_ss()) [Once evaluate_def]) >> gvs []),
      (rpt strip_tac >> Cases_on `i < LENGTH input` >| [
         (`s.clock <> 0` by fs [] >> mp_tac (MATCH_MP foldLoop_iter bstep) >>
          disch_then (qspecl_then [`i`,`acc`,`s`] mp_tac) >> impl_tac >- fs [] >> strip_tac >>
          `evaluate (While foldGuard bdy, s2) = (NONE, s')` by fs [] >>
          `LENGTH input - (i+1) <= k` by fs [] >> `LENGTH input - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`accf acc (n2w (EL i input):word64)`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >> `s2.clock = s.clock - 1` by fs [] >>
          `s.clock - (LENGTH input - i) = s2.clock - (LENGTH input - (i+1))`
             by (`0 < s.clock` by fs [] >> DECIDE_TAC) >> fs []),
         (`i <= LENGTH input` by fs [foldInv_def] >> `i = LENGTH input` by DECIDE_TAC >>
          `eval s foldGuard = SOME (ValWord 0w)` by (drule eval_foldGuard >> fs []) >>
          `s' = s` by (qpat_x_assum `evaluate (While foldGuard bdy, s) = (NONE, s')` mp_tac >>
                       asm_simp_tac (srw_ss()) [Once evaluate_def]) >> gvs [])])])
QED

Theorem foldLoop_clock:
  !accf bdy input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (bdy, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) ==>
    !(s:(64,'ffi) state) s'.
      foldInv input bs 0 0w s /\ LENGTH input <= s.clock /\
      evaluate (While foldGuard bdy, s) = (NONE, s') ==> s.clock - LENGTH input <= s'.clock
Proof
  rpt gen_tac >>
  disch_then (fn stp => rpt gen_tac >> strip_tac >>
    mp_tac (MATCH_MP foldLoop_clock_bounded stp) >>
    disch_then (qspecl_then [`LENGTH input`,`0`,`0w`,`s`,`s'`] mp_tac) >>
    impl_tac >- fs [] >> fs [])
QED

(* ===========================================================================
   loop_frame — THE generic framed fold core.  Any fold body whose single step
   advances the invariant + preserves memory + preserves «ctrl» refines its
   `While` to the exact `FOLDL accf 0w …`, handing the wrapper every exit shape
   (base/len/i/b), the memory/memaddrs/be frame, and the clock lower bound.
   =========================================================================== *)
Theorem loop_frame:
  !accf bdy input bs.
    (!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
       ?s2. evaluate (bdy, s) = (NONE, s2) /\ s2.clock = s.clock /\
            foldInv input bs (i+1) (accf acc (n2w (EL i input):word64)) s2) /\
    (!(s0:(64,'ffi) state) r s1. evaluate (bdy, s0) = (r,s1) ==> s1.memory = s0.memory) /\
    (!(s0:(64,'ffi) state) r s1. evaluate (bdy, s0) = (r,s1) ==>
       FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl») ==>
    !(s:(64,'ffi) state).
      foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
      ?s'. evaluate (While foldGuard bdy, s) = (NONE, s') /\
           FLOOKUP s'.locals «acc» = SOME (ValWord (FOLDL accf 0w (MAP (\c. (n2w c):word64) input))) /\
           FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl» /\
           FLOOKUP s'.locals «base» = SOME (ValWord bs) /\
           FLOOKUP s'.locals «len» = SOME (ValWord (n2w (LENGTH input))) /\
           (?iw. FLOOKUP s'.locals «i» = SOME (ValWord iw)) /\
           (?bw. FLOOKUP s'.locals «b» = SOME (ValWord bw)) /\
           s'.memory = s.memory /\ s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
           s.clock - LENGTH input <= s'.clock /\ s'.clock <= s.clock
Proof
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  `?s'. evaluate (While foldGuard bdy, s) = (NONE, s') /\
        foldInv input bs (LENGTH input) (FOLDL accf 0w (MAP (\c. (n2w c):word64) input)) s'`
    by (irule foldLoop_exit >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `s'` >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- fs [foldInv_def]
  >- (`!(t:(64,'ffi) state) t1. evaluate (While foldGuard bdy, t) = (NONE, t1) ==>
         FLOOKUP t1.locals «ctrl» = FLOOKUP t.locals «ctrl»`
        by (ho_match_mp_tac While_frame >> first_assum ACCEPT_TAC) >>
      first_x_assum (qspecl_then [`s`,`s'`] mp_tac) >> simp [])
  >- fs [foldInv_def]
  >- fs [foldInv_def]
  >- fs [foldInv_def]
  >- fs [foldInv_def]
  >- (`!(t:(64,'ffi) state) t1. evaluate (While foldGuard bdy, t) = (NONE, t1) ==> t1.memory = t.memory`
        by (ho_match_mp_tac loop_mem >> first_assum ACCEPT_TAC) >>
      first_x_assum (qspecl_then [`s`,`s'`] mp_tac) >> simp [])
  >- (imp_res_tac evaluate_invariants >> fs [])
  >- (imp_res_tac evaluate_invariants >> fs [])
  >- (`!(t:(64,'ffi) state) t'. foldInv input bs 0 0w t /\ LENGTH input <= t.clock /\
         evaluate (While foldGuard bdy, t) = (NONE, t') ==> t.clock - LENGTH input <= t'.clock`
        by (ho_match_mp_tac (Q.SPEC `accf` foldLoop_clock) >> first_assum ACCEPT_TAC) >>
      first_x_assum (qspecl_then [`s`,`s'`] mp_tac) >> simp [])
  >- (imp_res_tac evaluate_clock >> fs [])
QED

val _ = export_theory ();

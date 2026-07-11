(* ===========================================================================
   C21 — the SHARED, PROGRAM-AGNOSTIC fold-wrapper machinery.

   These are the generic lemmas the `mk_foldWrapper` generator (panWrapperLib)
   rests on for the WHOLE-PROGRAM fold wrapper.  None mentions any particular
   fold: every one is stated over an arbitrary Pancake body/loop with the
   canonical ctrl/base control-block shape (ctrl = @base, arena = ctrl+arenaOff,
   result slot = ctrl+koff).  Built ONCE, reused for EVERY byte-fold primitive.

     * While_frame        — a `While` whose body preserves a local `v` preserves
                            `v` across the whole (clocked) loop — gives the wrapper
                            the `ctrl` locals-frame the post-loop store needs.
     * eval_load_ctrlc    — ctrl-keyed control read  (`Load One (Var ctrl)`).
     * eval_ctrl_add      — ctrl-relative address     (`ctrl + k`).
     * evaluate_store_ctrl_acc — store the fold result `acc` at `ctrl + k`.

   (Extracted verbatim from the C20 hand stack `frameProbeScript.sml` and the
   ctrl-keyed lemmas of `hashWrapperLinkAScript.sml`, which are program-agnostic
   and shared by every fold's core + wrapper.)
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     pairTheory finite_mapTheory optionTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory;   (* fix_clock_id *)

val _ = new_theory "foldWrapCommon";

(* --- the While frame: a body-preserved local survives the whole loop --- *)
Theorem While_frame_gen:
  !v e c.
    (!(s0:(64,'ffi) state) r s1. evaluate (c,s0) = (r,s1) ==> FLOOKUP s1.locals v = FLOOKUP s0.locals v) ==>
    !n (s:(64,'ffi) state) s1. s.clock = n /\ evaluate (While e c, s) = (NONE, s1) ==>
             FLOOKUP s1.locals v = FLOOKUP s.locals v
Proof
  ntac 3 gen_tac >> strip_tac >> completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `evaluate (While _ _,_) = _` mp_tac >> simp [Once evaluate_def] >>
  Cases_on `eval s e` >> simp [] >>
  rename1 `eval s e = SOME vv` >> Cases_on `vv` >> simp [] >>
  Cases_on `w` >> simp [] >>
  qmatch_goalsub_rename_tac `if ww <> 0w then _ else _` >>
  reverse (Cases_on `ww <> 0w`) >> simp [] >>
  Cases_on `n = 0` >> simp [] >>
  Cases_on `evaluate (c, dec_clock s)` >>
  rename1 `evaluate (c,dec_clock s) = (rb, sb)` >>
  `sb.clock <= (dec_clock s).clock` by (imp_res_tac evaluate_clock >> fs []) >>
  `fix_clock (dec_clock s) (rb, sb) = (rb, sb)` by (irule fix_clock_id >> fs []) >> simp [] >>
  `FLOOKUP sb.locals v = FLOOKUP s.locals v`
     by (qpat_assum `!s0 r s1. evaluate (c,s0) = (r,s1) ==> _` drule >> fs [dec_clock_def]) >>
  `sb.clock < n` by fs [dec_clock_def] >>
  Cases_on `rb` >> TRY (rename1 `SOME rr` >> Cases_on `rr`) >> simp [] >> strip_tac >>
  FIRST [ (gvs [] >> NO_TAC),
          (`FLOOKUP s1.locals v = FLOOKUP sb.locals v`
             by (first_x_assum (qspec_then `sb.clock` mp_tac) >> impl_tac >- fs [] >>
                 disch_then (qspecl_then [`sb`,`s1`] mp_tac) >> fs []) >> fs []) ]
QED

Theorem While_frame:
  !v e c.
    (!(s0:(64,'ffi) state) r s1. evaluate (c,s0) = (r,s1) ==> FLOOKUP s1.locals v = FLOOKUP s0.locals v) ==>
    !(s:(64,'ffi) state) s1. evaluate (While e c, s) = (NONE, s1) ==>
             FLOOKUP s1.locals v = FLOOKUP s.locals v
Proof
  metis_tac [While_frame_gen]
QED

(* --- ctrl-keyed control read (Load One (Var «ctrl»)) --- *)
Theorem eval_load_ctrlc:
  !s ba w.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\ ba IN s.memaddrs /\
    s.memory ba = Word w ==>
    eval s (Load One (Var Local «ctrl»)) = SOME (ValWord w)
Proof
  rpt strip_tac >> simp [eval_def, is_wf_shape_def, mem_load_def]
QED

(* --- eval (ctrl + k) --- *)
Theorem eval_ctrl_add:
  !s ba k.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) ==>
    eval s (Op Add [Var Local «ctrl»; Const k]) = SOME (ValWord (ba + k))
Proof
  rpt strip_tac >> simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]
QED

(* --- store the fold result `acc` at ctrl+k --- *)
Theorem evaluate_store_ctrl_acc:
  !s ba w k.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s.locals «acc» = SOME (ValWord w) /\
    (ba + k) IN s.memaddrs ==>
    evaluate (Store (Op Add [Var Local «ctrl»; Const k]) (Var Local «acc»), s) =
      (NONE, s with memory := ((ba + k) =+ Word w) s.memory)
Proof
  rpt strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        flatten_def, mem_stores_def, mem_store_def]
QED

val _ = export_theory ();

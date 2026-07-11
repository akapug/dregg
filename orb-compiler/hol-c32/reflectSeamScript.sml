(* ===========================================================================
   C32 — THE FOLD-THEN-STORE COMPOSITION SEAM (panSem level).

   C30 closed the STORE lane for a compile-time-CONSTANT source block (the load
   oracle STAGES the source bytes).  C32 replaces that staged constant with the
   output of a FIRST loop (the "fold" lane: read the request, produce bytes into
   a scratch region), and proves the SECOND loop (the "store" lane, copyLoopA
   verbatim) copies THOSE request-derived bytes to the response buffer.

   The seam = loop1's output byte-facts (`copyLoopA_writes`) ESTABLISH loop2's
   `copyInv` SOURCE relation (`memRel`), in place of the load-oracle constant;
   loop1 PRESERVES loop2's output-region writability (a frame lemma), so the
   store can still write.  This is exactly C30 residual B: "the fold's result
   feeding copyInv's source relation in place of the load-oracle-staged
   constant".  No new metatheory beyond a frame lemma + a While body-congruence
   (Annots are behaviourally invisible), so the SAME copyLoopA carries BOTH
   phases.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory combinTheory;
open c14GenericTheory transformCopyLoopTheory;

val _ = new_theory "reflectSeam";

(* ---------------------------------------------------------------------------
   (0) While body-congruence: two bodies that evaluate-equal on every state give
   While-loops that evaluate-equal on every state.  This lets the SAME copyLoopA
   carry BOTH parsed loops regardless of their (behaviourally-invisible) Annot
   location strings — no fragile annot-matching surgery.
   --------------------------------------------------------------------------- *)
Theorem While_body_ext:
  !g b1 b2.
    (!(s:(64,'ffi) panSem$state). evaluate (b1,s) = evaluate (b2,s)) ==>
    !(s:(64,'ffi) panSem$state). evaluate (While g b1, s) = evaluate (While g b2, s)
Proof
  rpt gen_tac >> strip_tac >>
  `!n s:(64,'ffi) panSem$state. n = s.clock ==>
     evaluate (While g b1, s) = evaluate (While g b2, s)`
    suffices_by metis_tac [] >>
  completeInduct_on `n` >> rpt strip_tac >> gvs [] >>
  ONCE_REWRITE_TAC [evaluate_def] >>
  Cases_on `eval s g` >> simp [] >>
  rename1 `eval s g = SOME v` >> Cases_on `v` >> simp [] >>
  Cases_on `w` >> simp [] >>
  IF_CASES_TAC >> simp [] >>
  IF_CASES_TAC >> simp [] >>
  qpat_x_assum `!s. evaluate (b1,s) = evaluate (b2,s)`
     (fn th => REWRITE_TAC [th]) >>
  Cases_on `evaluate (b2, dec_clock s)` >>
  rename1 `evaluate (b2, dec_clock s) = (res, s1)` >>
  `s1.clock <= (dec_clock s).clock` by (imp_res_tac evaluate_clock >> fs []) >>
  simp [fix_clock_def] >>
  `s1.clock < s.clock` by fs [dec_clock_def] >>
  Cases_on `res` >> simp [] >>
  first_x_assum (qspecl_then [`s1.clock`,`s1`] mp_tac) >> simp []
QED

(* ---------------------------------------------------------------------------
   (1) The per-step MEMORY FRAME.  One `copyBody` iteration stores exactly one
   byte at `out + n2w i` (`mem_store_byte`, a single `byte_align` update), so any
   aligned cell disjoint from `byte_align (out + n2w i)` is untouched, and
   memaddrs / be are preserved.  (Re-derives the store from `copyInv`, tracking
   only the memory delta — the byte-content correctness is `copyBody_step`.)
   --------------------------------------------------------------------------- *)
Theorem copyBody_frame_step:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    ?s2. evaluate (copyBody, s) = (NONE, s2) /\
         s2.memaddrs = s.memaddrs /\ s2.be = s.be /\ s2.clock = s.clock /\
         (!a. a <> byte_align (out + n2w i) ==> s2.memory a = s.memory a)
Proof
  strip_tac >>
  `EL i bs < 256` by (fs [copyInv_def, EVERY_EL]) >>
  drule_all eval_copySrc >> strip_tac >>
  `byteWritable s (out + n2w i)` by (fs [copyInv_def]) >>
  `?v. s.memory (byte_align (out + n2w i)) = Word v /\
       byte_align (out + n2w i) IN s.memaddrs`
     by (fs [byteWritable_def] >> metis_tac []) >>
  `FLOOKUP s.locals «out» = SOME (ValWord out) /\
   FLOOKUP s.locals «i» = SOME (ValWord (n2w i))` by fs [copyInv_def] >>
  `(w2w ((n2w (EL i bs)):word64)):word8 = (n2w (EL i bs)):word8`
     by (simp [w2w_def, w2n_n2w] >> `dimword (:64) = 2n**64` by EVAL_TAC >>
         `dimword (:8) = 256` by EVAL_TAC >> fs [] >>
         `EL i bs MOD 256 = EL i bs` by (irule LESS_MOD >> fs []) >> fs []) >>
  qabbrev_tac
    `m2 = (byte_align (out + n2w i) =+
             Word (set_byte (out + n2w i) ((n2w (EL i bs)):word8) v s.be)) s.memory` >>
  `mem_store_byte s.memory s.memaddrs s.be (out + n2w i) ((n2w (EL i bs)):word8) = SOME m2`
     by (simp [mem_store_byte_def, Abbr `m2`] >> fs []) >>
  `eval s (Op Add [Var Local «out»; Var Local «i»]) = SOME (ValWord (out + n2w i))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]) >>
  qabbrev_tac `sS = s with memory := m2` >>
  `evaluate (StoreByte (Op Add [Var Local «out»; Var Local «i»])
              (LoadByte (Op Add [Var Local «src»; Var Local «i»])), s) = (NONE, sS)`
     by (simp [evaluate_def] >> fs [] >> simp [Abbr `sS`]) >>
  qabbrev_tac `sI = sS with locals := sS.locals |+ («i», ValWord (n2w (i+1)))` >>
  `FLOOKUP sS.locals «i» = SOME (ValWord (n2w i))` by (simp [Abbr `sS`] >> fs []) >>
  `evaluate (Assign Local «i» (Op Add [Var Local «i»; Const 1w]), sS) = (NONE, sI)`
     by (simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
         `(n2w i + 1w):word64 = n2w (i+1)` by simp [GSYM ADD1, n2w_SUC] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def, set_kvar_def,
               set_var_def, Abbr `sI`, Abbr `sS`]) >>
  `evaluate (copyBody, s) = (NONE, sI)`
     by (simp [copyBody_def] >> irule Seq_thread >> qexists_tac `sS` >>
         simp [Abbr `sS`]) >>
  qexists_tac `sI` >> simp [] >>
  `sI.memaddrs = s.memaddrs /\ sI.be = s.be /\ sI.clock = s.clock /\ sI.memory = m2`
     by simp [Abbr `sI`, Abbr `sS`] >>
  simp [] >> rpt strip_tac >>
  simp [Abbr `m2`, APPLY_UPDATE_THM] >> rw [] >> fs []
QED

(* the same frame on the Annot-wrapped parsed body (Annots don't touch state). *)
Theorem copyBodyA_frame_step:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    ?s2. evaluate (copyBodyA, s) = (NONE, s2) /\
         s2.memaddrs = s.memaddrs /\ s2.be = s.be /\ s2.clock = s.clock /\
         (!a. a <> byte_align (out + n2w i) ==> s2.memory a = s.memory a)
Proof
  strip_tac >> drule_all copyBody_frame_step >> strip_tac >>
  qexists_tac `s2` >> simp [copyBodyA_body_eq]
QED

(* ---------------------------------------------------------------------------
   (2) The WHOLE-LOOP FRAME.  copyLoopA writes only `[out, out+LENGTH bs)`, so
   any aligned cell disjoint from that whole region is preserved (and memaddrs /
   be are preserved).  Bounded clocked induction, mirroring copyLoopA_bounded but
   carrying the memory frame from the per-step.
   --------------------------------------------------------------------------- *)
Theorem copyLoopA_frame_bounded:
  !k i (s:(64,'ffi) panSem$state) s'.
    copyInv bs src out i s /\ LENGTH bs - i <= k /\ LENGTH bs - i <= s.clock /\
    evaluate (copyLoopA, s) = (NONE, s') ==>
    s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
    (!a. (!j. i <= j /\ j < LENGTH bs ==> a <> byte_align (out + n2w j)) ==>
         s'.memory a = s.memory a)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> `i = LENGTH bs` by fs [copyInv_def] >>
      `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
      qpat_x_assum `evaluate (copyLoopA, s) = (NONE, s')` mp_tac >>
      simp [copyLoopA_def, Once evaluate_def] >> strip_tac >> gvs [])
  >- (rpt gen_tac >> strip_tac >> Cases_on `i < LENGTH bs`
      >- (`s.clock <> 0` by fs [] >>
          `i < LENGTH bs` by fs [] >>
          `copyInv bs src out i (dec_clock s)`
             by (simp [dec_clock_def] >> irule copyInv_clock >> fs []) >>
          (* one iteration: copyInv advance (copyBodyA_step) + step memory frame *)
          drule_all copyBodyA_step >> strip_tac >>
          drule_all copyBodyA_frame_step >> strip_tac >>
          gvs [] >>
          `eval s copyGuard = SOME (ValWord 1w)`
             by (qpat_assum `copyInv bs src out i s`
                   (fn th => mp_tac (MATCH_MP eval_copyGuard th)) >> fs []) >>
          `evaluate (copyLoopA, s) = evaluate (copyLoopA, s2)`
             by (REWRITE_TAC [copyLoopA_def] >>
                 CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
                 asm_simp_tac (srw_ss()) [fix_clock_def, dec_clock_def] >> simp []) >>
          `evaluate (copyLoopA, s2) = (NONE, s')` by fs [] >>
          `s2.clock = s.clock - 1` by fs [dec_clock_def] >>
          `LENGTH bs - (i+1) <= k` by fs [] >>
          `LENGTH bs - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >>
          `s'.memaddrs = s.memaddrs /\ s'.be = s.be` by (fs [dec_clock_def]) >>
          simp [] >> rpt strip_tac >> fs [dec_clock_def])
      >- (`i = LENGTH bs` by fs [copyInv_def] >>
          `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
          qpat_x_assum `evaluate (copyLoopA, s) = (NONE, s')` mp_tac >>
          simp [copyLoopA_def, Once evaluate_def] >> strip_tac >> gvs []))
QED

Theorem copyLoopA_frame:
  copyInv bs src out 0 s /\ LENGTH bs <= s.clock /\
  evaluate (copyLoopA, s) = (NONE, s') ==>
    s'.memaddrs = s.memaddrs /\ s'.be = s.be /\
    (!a. (!j. j < LENGTH bs ==> a <> byte_align (out + n2w j)) ==>
         s'.memory a = s.memory a)
Proof
  strip_tac >>
  qspecl_then [`LENGTH bs`,`0`,`s`,`s'`] mp_tac copyLoopA_frame_bounded >>
  impl_tac >- fs [] >> strip_tac >> simp [] >> rpt strip_tac >>
  first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> fs []
QED

(* ---------------------------------------------------------------------------
   (2b) EXIT CLOCK.  copyLoopA runs exactly LENGTH bs iterations from i, each a
   single dec_clock, so the exit clock is start - (LENGTH bs - i).  Needed to
   budget the SECOND loop (loop2 must still have >= LENGTH req clock after loop1).
   --------------------------------------------------------------------------- *)
Theorem copyLoopA_clock_bounded:
  !k i (s:(64,'ffi) panSem$state) s'.
    copyInv bs src out i s /\ LENGTH bs - i <= k /\ LENGTH bs - i <= s.clock /\
    evaluate (copyLoopA, s) = (NONE, s') ==>
    s'.clock = s.clock - (LENGTH bs - i)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> `i = LENGTH bs` by fs [copyInv_def] >>
      `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
      qpat_x_assum `evaluate (copyLoopA, s) = (NONE, s')` mp_tac >>
      simp [copyLoopA_def, Once evaluate_def] >> strip_tac >> gvs [])
  >- (rpt gen_tac >> strip_tac >> Cases_on `i < LENGTH bs`
      >- (`s.clock <> 0` by fs [] >>
          `copyInv bs src out i (dec_clock s)`
             by (simp [dec_clock_def] >> irule copyInv_clock >> fs []) >>
          drule_all copyBodyA_step >> strip_tac >>
          `s.clock <> 0` by fs [] >>
          `eval s copyGuard = SOME (ValWord 1w)`
             by (qpat_assum `copyInv bs src out i s`
                   (fn th => mp_tac (MATCH_MP eval_copyGuard th)) >> fs []) >>
          `evaluate (copyLoopA, s) = evaluate (copyLoopA, s2)`
             by (REWRITE_TAC [copyLoopA_def] >>
                 CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
                 asm_simp_tac (srw_ss()) [fix_clock_def, dec_clock_def] >> simp []) >>
          `evaluate (copyLoopA, s2) = (NONE, s')` by fs [] >>
          `s2.clock = s.clock - 1` by fs [dec_clock_def] >>
          `LENGTH bs - (i+1) <= k` by fs [] >>
          `LENGTH bs - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >> fs [])
      >- (`i = LENGTH bs` by fs [copyInv_def] >>
          `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
          qpat_x_assum `evaluate (copyLoopA, s) = (NONE, s')` mp_tac >>
          simp [copyLoopA_def, Once evaluate_def] >> strip_tac >> gvs []))
QED

Theorem copyLoopA_clock:
  copyInv bs src out 0 s /\ LENGTH bs <= s.clock /\
  evaluate (copyLoopA, s) = (NONE, s') ==>
    s'.clock = s.clock - LENGTH bs
Proof
  strip_tac >>
  qspecl_then [`LENGTH bs`,`0`,`s`,`s'`] mp_tac copyLoopA_clock_bounded >>
  impl_tac >- fs [] >> strip_tac >> fs []
QED

(* ---------------------------------------------------------------------------
   (2c) LOCALS FRAME.  copyLoopA's body assigns only «i», so every OTHER local
   is preserved across the whole loop — needed to recover «mid»/«ctrl»/«n» after
   loop1 for the reassigns feeding loop2.
   --------------------------------------------------------------------------- *)
Theorem copyBody_locals_step:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    ?s2. evaluate (copyBody, s) = (NONE, s2) /\
         (!v. v <> «i» ==> FLOOKUP s2.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >>
  `EL i bs < 256` by (fs [copyInv_def, EVERY_EL]) >>
  drule_all eval_copySrc >> strip_tac >>
  `byteWritable s (out + n2w i)` by (fs [copyInv_def]) >>
  `?v. s.memory (byte_align (out + n2w i)) = Word v /\
       byte_align (out + n2w i) IN s.memaddrs`
     by (fs [byteWritable_def] >> metis_tac []) >>
  `FLOOKUP s.locals «out» = SOME (ValWord out) /\
   FLOOKUP s.locals «i» = SOME (ValWord (n2w i))` by fs [copyInv_def] >>
  `(w2w ((n2w (EL i bs)):word64)):word8 = (n2w (EL i bs)):word8`
     by (simp [w2w_def, w2n_n2w] >> `dimword (:64) = 2n**64` by EVAL_TAC >>
         `dimword (:8) = 256` by EVAL_TAC >> fs [] >>
         `EL i bs MOD 256 = EL i bs` by (irule LESS_MOD >> fs []) >> fs []) >>
  qabbrev_tac
    `m2 = (byte_align (out + n2w i) =+
             Word (set_byte (out + n2w i) ((n2w (EL i bs)):word8) v s.be)) s.memory` >>
  `mem_store_byte s.memory s.memaddrs s.be (out + n2w i) ((n2w (EL i bs)):word8) = SOME m2`
     by (simp [mem_store_byte_def, Abbr `m2`] >> fs []) >>
  `eval s (Op Add [Var Local «out»; Var Local «i»]) = SOME (ValWord (out + n2w i))`
     by (simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def]) >>
  qabbrev_tac `sS = s with memory := m2` >>
  `evaluate (StoreByte (Op Add [Var Local «out»; Var Local «i»])
              (LoadByte (Op Add [Var Local «src»; Var Local «i»])), s) = (NONE, sS)`
     by (simp [evaluate_def] >> fs [] >> simp [Abbr `sS`]) >>
  qabbrev_tac `sI = sS with locals := sS.locals |+ («i», ValWord (n2w (i+1)))` >>
  `FLOOKUP sS.locals «i» = SOME (ValWord (n2w i))` by (simp [Abbr `sS`] >> fs []) >>
  `evaluate (Assign Local «i» (Op Add [Var Local «i»; Const 1w]), sS) = (NONE, sI)`
     by (simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def] >>
         `(n2w i + 1w):word64 = n2w (i+1)` by simp [GSYM ADD1, n2w_SUC] >>
         simp [is_valid_value_def, lookup_kvar_def, shape_of_def, set_kvar_def,
               set_var_def, Abbr `sI`, Abbr `sS`]) >>
  `evaluate (copyBody, s) = (NONE, sI)`
     by (simp [copyBody_def] >> irule Seq_thread >> qexists_tac `sS` >>
         simp [Abbr `sS`]) >>
  qexists_tac `sI` >> simp [] >> rpt strip_tac >>
  simp [Abbr `sI`, Abbr `sS`, FLOOKUP_UPDATE]
QED

Theorem copyBodyA_locals_step:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    ?s2. evaluate (copyBodyA, s) = (NONE, s2) /\
         (!v. v <> «i» ==> FLOOKUP s2.locals v = FLOOKUP s.locals v)
Proof
  strip_tac >> drule_all copyBody_locals_step >> strip_tac >>
  qexists_tac `s2` >> simp [copyBodyA_body_eq]
QED

Theorem copyLoopA_locals_bounded:
  !k i (s:(64,'ffi) panSem$state) s'.
    copyInv bs src out i s /\ LENGTH bs - i <= k /\ LENGTH bs - i <= s.clock /\
    evaluate (copyLoopA, s) = (NONE, s') ==>
    !v. v <> «i» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> `i = LENGTH bs` by fs [copyInv_def] >>
      `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
      qpat_x_assum `evaluate (copyLoopA, s) = (NONE, s')` mp_tac >>
      simp [copyLoopA_def, Once evaluate_def] >> strip_tac >> gvs [])
  >- (rpt gen_tac >> strip_tac >> Cases_on `i < LENGTH bs`
      >- (`s.clock <> 0` by fs [] >>
          `copyInv bs src out i (dec_clock s)`
             by (simp [dec_clock_def] >> irule copyInv_clock >> fs []) >>
          drule_all copyBodyA_step >> strip_tac >>
          drule_all copyBodyA_locals_step >> strip_tac >>
          gvs [] >>
          `s.clock <> 0` by fs [] >>
          `eval s copyGuard = SOME (ValWord 1w)`
             by (qpat_assum `copyInv bs src out i s`
                   (fn th => mp_tac (MATCH_MP eval_copyGuard th)) >> fs []) >>
          `evaluate (copyLoopA, s) = evaluate (copyLoopA, s2)`
             by (REWRITE_TAC [copyLoopA_def] >>
                 CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
                 asm_simp_tac (srw_ss()) [fix_clock_def, dec_clock_def] >> simp []) >>
          `evaluate (copyLoopA, s2) = (NONE, s')` by fs [] >>
          `s2.clock = s.clock - 1` by fs [dec_clock_def] >>
          `LENGTH bs - (i+1) <= k` by fs [] >>
          `LENGTH bs - (i+1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`s2`,`s'`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >> rpt strip_tac >>
          `FLOOKUP s'.locals v = FLOOKUP s2.locals v` by fs [] >>
          `FLOOKUP s2.locals v = FLOOKUP (dec_clock s).locals v` by fs [] >>
          fs [dec_clock_def])
      >- (`i = LENGTH bs` by fs [copyInv_def] >>
          `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
          qpat_x_assum `evaluate (copyLoopA, s) = (NONE, s')` mp_tac >>
          simp [copyLoopA_def, Once evaluate_def] >> strip_tac >> gvs []))
QED

Theorem copyLoopA_locals:
  copyInv bs src out 0 s /\ LENGTH bs <= s.clock /\
  evaluate (copyLoopA, s) = (NONE, s') ==>
    !v. v <> «i» ==> FLOOKUP s'.locals v = FLOOKUP s.locals v
Proof
  strip_tac >>
  qspecl_then [`LENGTH bs`,`0`,`s`,`s'`] mp_tac copyLoopA_locals_bounded >>
  impl_tac >- fs [] >> strip_tac >> fs []
QED

(* ---------------------------------------------------------------------------
   (3) THE SEAM.  After loop1 (copyLoopA: src -> mid) writes the request-derived
   bytes into the scratch region `mid`, the reassigned state `sRe` (src:=mid,
   out:=out2, i:=0) satisfies loop2's `copyInv req mid out2 0` — the store lane's
   SOURCE `memRel` comes from loop1's OUTPUT (`copyLoopA_writes`), and loop2's
   OUTPUT-region writability survives loop1 (`copyLoopA_frame`, mid # out2).  This
   is the fold-result feeding copyInv's source in place of the staged constant.
   --------------------------------------------------------------------------- *)
Theorem seam_loop2_copyInv:
  copyInv req src mid 0 s /\ LENGTH req <= s.clock /\
  evaluate (copyLoopA, s) = (NONE, sMid) /\
  (!j. j < LENGTH req ==> byteWritable s (out2 + n2w j)) /\
  disjWords mid out2 (LENGTH req) /\
  sRe.memory = sMid.memory /\ sRe.memaddrs = sMid.memaddrs /\ sRe.be = sMid.be /\
  FLOOKUP sRe.locals «i»   = SOME (ValWord 0w) /\
  FLOOKUP sRe.locals «n»   = SOME (ValWord (n2w (LENGTH req))) /\
  FLOOKUP sRe.locals «src» = SOME (ValWord mid) /\
  FLOOKUP sRe.locals «out» = SOME (ValWord out2) ==>
  copyInv req mid out2 0 sRe
Proof
  strip_tac >>
  (* loop1 OUTPUT (the seam): mid holds req; assert about sMid via the hyp *)
  `(!j. j < LENGTH req ==>
        mem_load_byte sMid.memory sMid.memaddrs sMid.be (mid + n2w j)
          = SOME ((n2w (EL j req)):word8))`
     by (drule_all copyLoopA_writes >> strip_tac >> gvs []) >>
  (* loop1 FRAME: memaddrs / be preserved, mid-disjoint cells preserved *)
  `sMid.memaddrs = s.memaddrs /\ sMid.be = s.be /\
   (!a. (!j. j < LENGTH req ==> a <> byte_align (mid + n2w j)) ==>
        sMid.memory a = s.memory a)`
     by (drule_all copyLoopA_frame >> strip_tac >> gvs []) >>
  simp [copyInv_def] >> rpt conj_tac
  >- (* memRel req mid sRe : straight from loop1's written bytes *)
     (simp [memRel_def] >> rpt strip_tac >>
      `mem_load_byte sMid.memory sMid.memaddrs sMid.be (mid + n2w j)
         = SOME ((n2w (EL j req)):word8)` by fs [] >>
      fs [])
  >- (* out2 region writable in sRe : survives loop1 (mid # out2) *)
     (rpt strip_tac >>
      `byteWritable s (out2 + n2w j)` by fs [] >>
      `byte_align (out2 + n2w j) IN s.memaddrs /\
       ?w. s.memory (byte_align (out2 + n2w j)) = Word w`
         by (fs [byteWritable_def] >> metis_tac []) >>
      `sMid.memory (byte_align (out2 + n2w j)) = s.memory (byte_align (out2 + n2w j))`
         by (first_x_assum irule >> rpt strip_tac >>
             fs [disjWords_def] >>
             first_x_assum (qspecl_then [`j`,`j'`] mp_tac) >> fs []) >>
      simp [byteWritable_def] >> fs [] >> metis_tac [])
  >- (* LENGTH req < 2^63 *) fs [copyInv_def]
  >- (* EVERY (<256) req *) fs [copyInv_def]
QED

(* The full two-phase result: after loop1 (src->mid) and loop2 (mid->out2), the
   response buffer out2 holds the request-derived bytes `req`.  Composes
   `seam_loop2_copyInv` (the seam) with `copyLoopA_writes` (loop2 = the store). *)
Theorem two_copy_out_writes:
  copyInv req src mid 0 s /\ LENGTH req <= s.clock /\
  evaluate (copyLoopA, s) = (NONE, sMid) /\
  (!j. j < LENGTH req ==> byteWritable s (out2 + n2w j)) /\
  disjWords mid out2 (LENGTH req) /\
  sRe.memory = sMid.memory /\ sRe.memaddrs = sMid.memaddrs /\ sRe.be = sMid.be /\
  LENGTH req <= sRe.clock /\
  FLOOKUP sRe.locals «i»   = SOME (ValWord 0w) /\
  FLOOKUP sRe.locals «n»   = SOME (ValWord (n2w (LENGTH req))) /\
  FLOOKUP sRe.locals «src» = SOME (ValWord mid) /\
  FLOOKUP sRe.locals «out» = SOME (ValWord out2) ==>
  ?sOut. evaluate (copyLoopA, sRe) = (NONE, sOut) /\
         (!j. j < LENGTH req ==>
              mem_load_byte sOut.memory sOut.memaddrs sOut.be (out2 + n2w j)
                = SOME ((n2w (EL j req)):word8)) /\
         FLOOKUP sOut.locals «out» = SOME (ValWord out2)
Proof
  strip_tac >>
  `copyInv req mid out2 0 sRe` by (irule seam_loop2_copyInv >> metis_tac []) >>
  drule_all copyLoopA_writes >> strip_tac >>
  qexists_tac `s'` >> simp []
QED

val _ = export_theory ();

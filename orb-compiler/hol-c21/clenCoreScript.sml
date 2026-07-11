(* ===========================================================================
   C21 — the SECOND real serve FOLD: the Content-Length decimal accumulator.
   The HTTP Content-Length header value (a run of decimal digit bytes) is parsed
   into a number by the base-10 Horner fold  acc := acc*10 + d.  This is the
   C19-style loop CORE for the fold, on the GENUINE parsed while body `clenBodyA`
   (the verified parser's output on clen.pnk; leanc out of TCB), closed to
   `n2w (clenN input)` (the Lean spec mod 2^64) with an ~8-line per-step fill-in
   via the C16 schema + the Nat->word homomorphism, and framed against `ctrl`.

   A GENUINELY DIFFERENT fold from the cache-key hash: base-10 Horner (a*10 + d),
   not the mul-add-1 digest — different loop body, spec word, and homomorphism.
   The whole-program wrapper is then produced by the SAME `mk_foldWrapper` call.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory foldWrapCommonTheory c14GenericTheory;

val _ = new_theory "clenCore";

(* ---- the Lean SPEC over nats: the base-10 Horner value of the digit run ---- *)
Definition clenAccN_def:
  clenAccN (a:num) (b:num) = a * 10 + b
End

Definition clenN_def:
  clenN (input:num list) = FOLDL clenAccN 0 input
End

(* ---- the machine-word accumulator step (word64, wraps at 2^64) ---- *)
Definition clenAcc_def:
  clenAcc (a:word64) (b:word64) = a * 10w + b
End

(* ---- the Nat -> word homomorphism (n2w is a semiring hom) ---- *)
Theorem clenAccN_word:
  !a b. (n2w (clenAccN a b) : word64) = clenAcc (n2w a) (n2w b)
Proof
  rw [clenAccN_def, clenAcc_def] >>
  `(10w:word64) = n2w 10` by EVAL_TAC >>
  simp [word_add_n2w, word_mul_n2w] >> simp [GSYM word_add_n2w, GSYM word_mul_n2w]
QED

Theorem clen_word_gen:
  !input a.
    (n2w (FOLDL clenAccN a input) : word64) =
    FOLDL clenAcc (n2w a) (MAP (\c. (n2w c):word64) input)
Proof
  Induct >> rw [] >> simp [clenAccN_word]
QED

Theorem clen_word:
  !input.
    (n2w (clenN input) : word64) =
    FOLDL clenAcc 0w (MAP (\c. (n2w c):word64) input)
Proof
  rw [clenN_def] >>
  `(0w:word64) = n2w 0` by simp [] >>
  metis_tac [clen_word_gen]
QED

(* ---- the VERBATIM emitted while body (Annot-wrapped) from the parser ---- *)
Definition clenBodyA_def:
  clenBodyA =
    Seq
      (Seq (Annot «location» «(22:4 22:18)»)
           (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»]))))
      (Seq
         (Seq (Annot «location» «(23:4 23:19)»)
              (Assign Local «acc»
                 (Op Add [Panop Mul [Var Local «acc»; Const 10w]; Var Local «b»])))
         (Seq (Annot «location» «(24:4 24:11)»)
              (Assign Local «i» (Op Add [Var Local «i»; Const 1w]))))
End

Definition clenLoopCore_def:
  clenLoopCore = While foldGuard clenBodyA
End

(* ---- the per-step fill-in: one iteration of the parsed body advances the fold
   by `clenAcc`.  Same shape as the hash core, minus the +1. ---- *)
Theorem clenBodyA_step:
  !i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (clenBodyA, s) = (NONE, s2) /\ s2.clock = s.clock /\
         foldInv input bs (i+1) (clenAcc acc (n2w (EL i input):word64)) s2
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
    (set_var «acc» (ValWord (acc * 10w + n2w (EL i input)))
    (set_var «b»   (ValWord (n2w (EL i input))) s))` >>
  simp [clenBodyA_def, evaluate_def, eval_def, is_valid_value_simps, shape_of_def,
        set_var_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def, pan_op_def,
        word_mul_n2w, OPT_MMAP_def] >>
  simp [foldInv_def, clenAcc_def, memRel_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def]
QED

(* ---- the closed loop core (via the C16 schema + the homomorphism) ---- *)
Theorem clenLoopCore_refines:
  !input bs (s:(64,'ffi) state).
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (clenLoopCore, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» =
           SOME (ValWord ((n2w (clenN input)):word64))
Proof
  rpt strip_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (clenBodyA, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (clenAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule clenBodyA_step >> fs []) >>
  drule foldLoop_refines >>
  disch_then (qspecl_then [`0w`,`s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> simp [clenLoopCore_def, clen_word]
QED

Theorem clenLoopCore_noFFI:
  noFFI clenLoopCore
Proof
  simp [clenLoopCore_def, clenBodyA_def, foldGuard_def, noFFI_def]
QED

Theorem clenBodyA_keeps_ctrl:
  !(s0:(64,'ffi) state) r s1. evaluate (clenBodyA, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [clenBodyA_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

Theorem evaluate_clenLoopCore_framed:
  foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
  ?s'. evaluate (clenLoopCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (clenN input))) /\
       FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl»
Proof
  strip_tac >>
  drule clenLoopCore_refines >> disch_then drule >> strip_tac >>
  `evaluate (While foldGuard clenBodyA, s) = (NONE, s')` by fs [clenLoopCore_def] >>
  qexists_tac `s'` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule (Q.SPECL [`«ctrl»`,`foldGuard`,`clenBodyA`] While_frame) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> imp_res_tac clenBodyA_keeps_ctrl >> fs []
QED

val _ = export_theory ();

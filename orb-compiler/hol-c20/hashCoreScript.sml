(* ===========================================================================
   C20 — the DEPLOYED cache-key-hash LOOP CORE, on the GENUINE parsed while body.
   `hashBodyA` is the verbatim Annot-wrapped `while` body the CakeML-verified
   parser emits for hashbytes.pnk (leanc out of TCB); `hashLoopCore` is the
   emitted `While foldGuard hashBodyA`.  The C16 fold-loop schema + the C19 Nat->
   word homomorphism close it to `n2w (hashBytesN input)` (the deployed hash mod
   2^64) with an ~8-line per-step fill-in, and `While_frame` gives the `ctrl`
   locals-frame the whole-program wrapper needs after the loop.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory hashBytesLoopTheory frameProbeTheory c14GenericTheory;

val _ = new_theory "hashCore";

(* ---- the VERBATIM emitted while body (Annot-wrapped) from the parser ---- *)
Definition hashBodyA_def:
  hashBodyA =
    Seq
      (Seq (Annot «location» «(21:4 21:18)»)
           (Assign Local «b» (LoadByte (Op Add [Var Local «base»; Var Local «i»]))))
      (Seq
         (Seq (Annot «location» «(22:4 22:23)»)
              (Assign Local «acc»
                 (Op Add [Panop Mul [Var Local «acc»; Const 257w];
                          Var Local «b»; Const 1w])))
         (Seq (Annot «location» «(23:4 23:11)»)
              (Assign Local «i» (Op Add [Var Local «i»; Const 1w]))))
End

Definition hashLoopCore_def:
  hashLoopCore = While foldGuard hashBodyA
End

(* ---- the per-step fill-in: one iteration of the parsed body advances the fold
   by `hashAcc`.  Same shape as C19 hashBody_step, threaded through the three
   transparent Annots. ---- *)
Theorem hashBodyA_step:
  !i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
    ?s2. evaluate (hashBodyA, s) = (NONE, s2) /\ s2.clock = s.clock /\
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
  simp [hashBodyA_def, evaluate_def, eval_def, is_valid_value_simps, shape_of_def,
        set_var_def, FLOOKUP_UPDATE, wordLangTheory.word_op_def, pan_op_def,
        word_mul_n2w, OPT_MMAP_def] >>
  simp [foldInv_def, hashAcc_def, memRel_def, FLOOKUP_UPDATE, GSYM word_add_n2w] >>
  fs [foldInv_def, memRel_def]
QED

(* ---- the closed loop core (via the C16 schema + C19 homomorphism) ---- *)
Theorem hashLoopCore_refines:
  !input bs (s:(64,'ffi) state).
    foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
    ?s'. evaluate (hashLoopCore, s) = (NONE, s') /\
         FLOOKUP s'.locals «acc» =
           SOME (ValWord ((n2w (hashBytesN input)):word64))
Proof
  rpt strip_tac >>
  `!i acc (s:(64,'ffi) state). foldInv input bs i acc s /\ i < LENGTH input ==>
     ?s2. evaluate (hashBodyA, s) = (NONE, s2) /\ s2.clock = s.clock /\
          foldInv input bs (i+1) (hashAcc acc (n2w (EL i input):word64)) s2`
     by (rpt strip_tac >> irule hashBodyA_step >> fs []) >>
  drule foldLoop_refines >>
  disch_then (qspecl_then [`0w`,`s`] mp_tac) >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> simp [hashLoopCore_def, hashBytes_word]
QED

Theorem hashLoopCore_noFFI:
  noFFI hashLoopCore
Proof
  simp [hashLoopCore_def, hashBodyA_def, foldGuard_def, noFFI_def]
QED

(* ---- hashBodyA never assigns `ctrl` (only b/acc/i) ---- *)
Theorem hashBodyA_keeps_ctrl:
  !(s0:(64,'ffi) state) r s1. evaluate (hashBodyA, s0) = (r,s1) ==>
     FLOOKUP s1.locals «ctrl» = FLOOKUP s0.locals «ctrl»
Proof
  rpt gen_tac >> simp [hashBodyA_def, evaluate_def] >>
  rpt (pairarg_tac >> gvs [AllCaseEqs()]) >>
  gvs [set_var_def, set_kvar_def, kvar_defs, FLOOKUP_UPDATE, empty_locals_def] >>
  rw [] >> gvs [FLOOKUP_UPDATE]
QED

(* ---- FRAMED core: result in `acc`, `ctrl` preserved across the whole loop ---- *)
Theorem evaluate_hashLoopCore_framed:
  foldInv input bs 0 0w s /\ LENGTH input <= s.clock ==>
  ?s'. evaluate (hashLoopCore, s) = (NONE, s') /\
       FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (hashBytesN input))) /\
       FLOOKUP s'.locals «ctrl» = FLOOKUP s.locals «ctrl»
Proof
  strip_tac >>
  drule hashLoopCore_refines >> disch_then drule >> strip_tac >>
  `evaluate (While foldGuard hashBodyA, s) = (NONE, s')` by fs [hashLoopCore_def] >>
  qexists_tac `s'` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule (Q.SPECL [`«ctrl»`,`foldGuard`,`hashBodyA`] While_frame) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> imp_res_tac hashBodyA_keeps_ctrl >> fs []
QED

val _ = export_theory ();

(* ===========================================================================
   CN probe — LINK A for the boundscan SCAN `While` LOOP (the C-series residual).

   C0 (§4-A-2), C1 (§5) and C10 (§7) each closed Link A for the boundscan
   region-check `If` against real `panSem$evaluate`, and each named the SAME
   residual UNCLOSED: the digest scan `While` — a loop-invariant induction over
   panSem's CLOCKED `While` clause, refining the Lean digest fold
   `acc := (acc*31 + b) mod 2^24`.

   C3 (`machineLoopLinkA`) discharged the loop-induction SKELETON for a DIFFERENT
   body (the C2 saturating-counter `mstep`, with a separate `«b»` slot and a
   `base+i` address). C3 §5 named the boundscan digest step as still owing its
   own body lemma ("*31 + b … analogous to evaluate_stepBody").

   This file discharges Link A for the ACTUAL boundscan scan loop, taken verbatim
   from the CakeML-verified parser output `boundScanLinkB$boundScanProg` (C10):
     - the guard `Cmp Less «i» «len»`,
     - the body `acc := (Op And [Op Add [Panop Mul [«acc»;31]; LoadByte (buf+off+i)]; 0xFFFFFF]); i := i+1`,
       with the parser's transparent `Annot` no-op nodes IN PLACE,
     - the LoadByte at the 3-summand address `Op Add [«buf»;«off»;«i»]`.
   We prove, against real `panSem$evaluate`, that running this `While` from an
   invariant state computes EXACTLY the Lean digest fold `FOLDL dstep 0` over the
   viewed byte slice, by a general-clock loop-invariant induction.

   Faithfulness to the emitted program is CLOSED (not transcribed-and-asserted):
   `scanLoop_faithful` is a kernel-checked equation that this exact `scanLoop`
   term is the (unique) `While` inside `boundScanProg`.

   Comparison-faithfulness note carries over: Pancake `<` is the SIGNED `Cmp
   Less`; the guard `i < len` needs the non-negative signed-range side condition
   `LENGTH vs < 2^63`, discharged by `signed_lt_n2w64`.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory bitTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory;
open boundScanLinkBTheory;   (* boundScanProg = the verified parser output (C10) *)

val _ = new_theory "boundScanLoopLinkA";

(* AND with the all-ones word is the identity (the `word_op And` FOLDR seed).
   Bit-blasted at the concrete word64 width. *)
Theorem word_and_T_local:
  !a:word64. word_and a (¬0w) = a
Proof
  blastLib.BBLAST_TAC
QED

(* The 24-bit mask: AND-ing with 0xFFFFFF is `MOD 2^24`.  This is the word side
   of the digest's `& 16777215`.  (WORD_AND_EXP_SUB1: n2w n && n2w (2^m-1) =
   n2w (n MOD 2^m).) *)
Theorem mask24:
  !n. ((0xFFFFFFw:word64) && n2w n = n2w (n MOD 16777216)) /\
      (n2w n && (0xFFFFFFw:word64) = n2w (n MOD 16777216))
Proof
  gen_tac >>
  `(0xFFFFFFw:word64) = n2w (2 ** 24 - 1)` by EVAL_TAC >>
  `(16777216:num) = 2 ** 24` by EVAL_TAC >>
  ASM_REWRITE_TAC [] >>
  conj_tac >| [
    once_rewrite_tac [WORD_AND_COMM] >> rewrite_tac [WORD_AND_EXP_SUB1],
    rewrite_tac [WORD_AND_EXP_SUB1]
  ]
QED

(* ---------------------------------------------------------------------------
   §0  Small arithmetic/word helpers (self-contained; the C3 analogues).
   --------------------------------------------------------------------------- *)

(* On the non-negative signed range the SIGNED word order agrees with nat order.
   Discharges the `Cmp Less` guard. *)
Theorem signed_lt_n2w64:
  !x y. x < 2n ** 63 /\ y < 2n ** 63 ==>
        (((n2w x):word64) < n2w y <=> x < y)
Proof
  rw [] >>
  `(2:num) ** 63 < 2 ** 64` by EVAL_TAC >>
  `x < dimword(:64) /\ y < dimword(:64)` by
    (`dimword(:64) = 2 ** 64` by EVAL_TAC >> fs [] >>
     conj_tac >> metis_tac [LESS_TRANS]) >>
  `~word_msb ((n2w x):word64) /\ ~word_msb ((n2w y):word64)` by
    (rw [word_msb_n2w] >> irule NOT_BIT_GT_TWOEXP >> fs []) >>
  rw [WORD_LT, w2n_n2w] >> fs []
QED

(* A memory byte (word8, < 256) widened to word64 is the same nat. *)
Theorem w2w_byte:
  !x. x < 256 ==> (w2w ((n2w x):word8) : word64) = n2w x
Proof
  rw [w2w_def, w2n_n2w] >>
  `dimword (:8) = 256` by EVAL_TAC >>
  fs [] >>
  `x MOD 256 = x` by (irule LESS_MOD >> fs []) >>
  fs []
QED

Theorem DROP_EL_CONS_local:
  !n l. n < LENGTH l ==> DROP n l = EL n l :: DROP (SUC n) l
Proof
  Induct >> Cases_on `l` >> fs []
QED

(* Sequencing two clock-preserving NONE-returning statements: the panSem `Seq`
   `fix_clock` collapses to the identity. *)
Theorem Seq_NONE:
  !p1 p2 s sa sb.
    evaluate (p1,s) = (NONE,sa) /\ sa.clock = s.clock /\
    evaluate (p2,sa) = (NONE,sb) ==>
    evaluate (Seq p1 p2, s) = (NONE, sb)
Proof
  rpt strip_tac >>
  simp [evaluate_def] >>
  `fix_clock s (evaluate (p1,s)) = (NONE, sa)`
     by (`~(s.clock < sa.clock)` by fs [] >>
         simp [fix_clock_def, state_component_equality]) >>
  simp []
QED

(* ---------------------------------------------------------------------------
   §1  The Lean SPEC digest step, re-declared in HOL (byte-identical to
   `C0.boundScan`'s fold `acc := (acc*31 + b) mod 2^24`).
   --------------------------------------------------------------------------- *)
Definition dstep_def:
  dstep (acc:num) (b:num) = (acc * 31 + b) MOD 16777216
End

(* The digest is UNCONDITIONALLY in 24-bit range (the MOD): so the invariant
   `acc < 2^24` is trivially re-established by every step — simpler than mstep's
   conditional saturation. *)
Theorem dstep_lt:
  !acc b. dstep acc b < 16777216
Proof
  rw [dstep_def]
QED

(* ---------------------------------------------------------------------------
   §2  The IMPLEMENTATION: the scan loop, transcribed VERBATIM from the parser
   output `boundScanProg` (C10) — including the transparent `Annot` no-ops and
   the exact `Panop Mul` / `Op And` / 3-summand `Op Add` the parser produced.
   --------------------------------------------------------------------------- *)
Definition scanBody_def:
  scanBody =
    Seq
      (Seq (Annot (strlit "location") (strlit "(37:6 37:45)"))
           (Assign Local (strlit "acc")
              (Op And
                 [Op Add
                    [Panop Mul [Var Local (strlit "acc"); Const (31w:word64)];
                     LoadByte (Op Add [Var Local (strlit "buf");
                                       Var Local (strlit "off");
                                       Var Local (strlit "i")])];
                  Const (0xFFFFFFw:word64)])))
      (Seq (Annot (strlit "location") (strlit "(38:6 38:13)"))
           (Assign Local (strlit "i")
              (Op Add [Var Local (strlit "i"); Const (1w:word64)])))
End

Definition scanLoop_def:
  scanLoop =
    While (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
          scanBody
End

(* ---------------------------------------------------------------------------
   §3  Faithfulness: `scanLoop` is the (unique) `While` inside the verified
   parser output `boundScanProg`.  A total structural search extracts it; the
   equation is kernel-checked by EVAL, so the transcription cannot silently
   diverge from what leanc emitted + the parser produced (C10).
   --------------------------------------------------------------------------- *)
Definition extract_while_def:
  extract_while (Seq c1 c2) =
    (case extract_while c1 of SOME w => SOME w | NONE => extract_while c2) /\
  extract_while (Dec _ _ _ p) = extract_while p /\
  extract_while (If _ c1 c2) =
    (case extract_while c1 of SOME w => SOME w | NONE => extract_while c2) /\
  extract_while (While g b) = SOME (While g b) /\
  extract_while _ = NONE
End

Definition extract_while_decl_def:
  extract_while_decl (Function fd) = extract_while fd.body /\
  extract_while_decl _ = NONE
End

Theorem scanLoop_faithful:
  extract_while_decl (HD boundScanProg) = SOME scanLoop
Proof
  rw [boundScanProg_def, extract_while_decl_def, extract_while_def,
      scanLoop_def, scanBody_def]
QED

(* ---------------------------------------------------------------------------
   §4  The byte-memory relation over the VIEWED slice: real `panSem`
   word-addressed byte memory at `bs + j` yields `n2w (EL j vs)`, for the viewed
   bytes `vs` and view base `bs = buf + off`.  (The endianness/packing that
   POPULATES memory is the FFI's job; stays outside the theorem — C3 §5.2.)
   --------------------------------------------------------------------------- *)
Definition memRel_def:
  memRel (vs:num list) (bs:word64) (s:(64,'ffi) panSem$state) <=>
    !j. j < LENGTH vs ==>
        mem_load_byte s.memory s.memaddrs s.be (bs + n2w j)
          = SOME ((n2w (EL j vs)):word8)
End

(* ---------------------------------------------------------------------------
   §5  The loop invariant.  `«acc»` holds the running digest, `«i»` the index,
   `«len»` the view length (= |vs|), `«buf»`/`«off»` the base words with
   `bs = bufw + offw`, `memRel` threaded, plus the byte-range / signed-range side
   conditions.  NB there is NO `«b»` slot: the boundscan byte read is INLINE.
   --------------------------------------------------------------------------- *)
Definition loopInv_def:
  loopInv (vs:num list) (bufw:word64) (offw:word64) (acc:num) (i:num)
          (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals (strlit "acc") = SOME (ValWord (n2w acc)) /\
    FLOOKUP s.locals (strlit "i")   = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH vs))) /\
    FLOOKUP s.locals (strlit "buf") = SOME (ValWord bufw) /\
    FLOOKUP s.locals (strlit "off") = SOME (ValWord offw) /\
    memRel vs (bufw + offw) s /\
    acc < 16777216 /\ i <= LENGTH vs /\ LENGTH vs < 2n ** 63 /\
    EVERY (\x. x < 256) vs
End

Theorem loopInv_clock:
  loopInv vs bufw offw acc i s ==> loopInv vs bufw offw acc i (s with clock := ck)
Proof
  rw [loopInv_def, memRel_def]
QED

(* ---------------------------------------------------------------------------
   §6  The loop guard: real `panSem$eval` of `i < len` = 1w exactly when in range.
   --------------------------------------------------------------------------- *)
Theorem eval_loop_guard:
  loopInv vs bufw offw acc i s ==>
    eval s (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
      = SOME (ValWord (if i < LENGTH vs then 1w else 0w))
Proof
  strip_tac >>
  fs [loopInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `LENGTH vs` >> fs []) >>
  `(n2w i:word64 < n2w (LENGTH vs)) = (i < LENGTH vs)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [eval_def, asmTheory.word_cmp_def]
QED

(* ---------------------------------------------------------------------------
   §7  The per-iteration byte read: real `panSem$eval` of the inline
   `LoadByte (Op Add [buf;off;i])` returns `n2w (EL i vs)`, via `memRel` +
   `w2w_byte`.  The 3-summand address folds to `(bufw+offw) + n2w i`.
   --------------------------------------------------------------------------- *)
Theorem eval_loadbyte:
  loopInv vs bufw offw acc i s /\ i < LENGTH vs ==>
    eval s (LoadByte (Op Add [Var Local (strlit "buf");
                              Var Local (strlit "off");
                              Var Local (strlit "i")]))
      = SOME (ValWord ((n2w (EL i vs)):word64))
Proof
  strip_tac >>
  `EL i vs < 256` by (fs [loopInv_def, EVERY_EL]) >>
  `mem_load_byte s.memory s.memaddrs s.be ((bufw + offw) + n2w i)
      = SOME ((n2w (EL i vs)):word8)`
     by (fs [loopInv_def, memRel_def]) >>
  fs [loopInv_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0] >>
  `bufw + (offw + n2w i) = bufw + offw + n2w i` by simp [WORD_ADD_ASSOC] >>
  simp [w2w_byte]
QED

(* ---------------------------------------------------------------------------
   §8  THE DIGEST STEP (the new C-series body lemma). Real `panSem$eval` of the
   digest expression = `n2w (dstep acc (EL i vs))`.  This threads:
     Panop Mul (word multiply) -> word_mul_n2w
     Op Add    (FOLDR word_add) -> word_add_n2w
     Op And w. 0xFFFFFF (mask)  -> WORD_AND_EXP_SUB1 (n2w n && n2w (2^m-1) = n2w (n MOD 2^m))
   with acc<2^24, byte<256 so acc*31+byte < 2^63 (no wrap before the mask).
   --------------------------------------------------------------------------- *)
Theorem eval_digest_expr:
  loopInv vs bufw offw acc i s /\ i < LENGTH vs ==>
    eval s
      (Op And
         [Op Add
            [Panop Mul [Var Local (strlit "acc"); Const (31w:word64)];
             LoadByte (Op Add [Var Local (strlit "buf");
                               Var Local (strlit "off");
                               Var Local (strlit "i")])];
          Const (0xFFFFFFw:word64)])
      = SOME (ValWord (n2w (dstep acc (EL i vs))))
Proof
  strip_tac >>
  drule_all eval_loadbyte >> strip_tac >>
  `FLOOKUP s.locals (strlit "acc") = SOME (ValWord (n2w acc))` by fs [loopInv_def] >>
  `EL i vs < 256` by (fs [loopInv_def, EVERY_EL]) >>
  `acc < 16777216` by fs [loopInv_def] >>
  (* The `eval s (LoadByte ..) = SOME (ValWord (n2w (EL i vs)))` fact is now an
     assumption (from `drule_all eval_loadbyte`); it is more specific than the
     `eval_def` LoadByte clause, so under `asm_simp_tac (srw_ss())` it drives the
     byte read and the raw `mem_load_byte` form never reappears — no abbreviation
     needed.  The reduction of the nested Op/Panop leaves
       0xFFFFFFw && 31w * n2w acc + n2w (EL i vs) = n2w (dstep acc (EL i vs)). *)
  asm_simp_tac (srw_ss())
    [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, pan_op_def,
     WORD_ADD_0, word_and_T_local] >>
  (* Fold the word sum to `n2w (31*acc + byte)`: force `31w = n2w 31` then the
     n2w mul/add homomorphisms; `mask24` turns `0xFFFFFF &&` into `MOD 2^24`,
     `dstep_def` unfolds the RHS, and the residual `31*acc` vs `acc*31` is closed
     by the srw_ss arithmetic normaliser (NOT `MULT_COMM` — adding it to srw_ss
     loops against the built-in numeral-first multiplication ordering). *)
  `(31w:word64) = n2w 31` by EVAL_TAC >>
  asm_simp_tac std_ss [word_mul_n2w, word_add_n2w] >>
  rewrite_tac [mask24, dstep_def] >>
  simp []
QED

(* ---------------------------------------------------------------------------
   §9  The loop BODY, one iteration: real `panSem$evaluate` of `scanBody` (the
   two `Annot`-wrapped assigns) writes `n2w (dstep acc (EL i vs))` into `«acc»`,
   advances `«i»`, preserves the clock, and RE-ESTABLISHES the invariant at
   `(dstep acc (EL i vs), i+1)`.  The memory relation is threaded (the body
   writes only locals, so `memRel` survives).
   --------------------------------------------------------------------------- *)
Theorem evaluate_scanBody:
  loopInv vs bufw offw acc i s /\ i < LENGTH vs ==>
    ?s2. evaluate (scanBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         loopInv vs bufw offw (dstep acc (EL i vs)) (i + 1) s2
Proof
  strip_tac >>
  drule_all eval_digest_expr >> strip_tac >>
  `strlit "acc" <> strlit "i" /\ strlit "i" <> strlit "acc" /\
   strlit "len" <> strlit "acc" /\ strlit "len" <> strlit "i" /\
   strlit "buf" <> strlit "acc" /\ strlit "buf" <> strlit "i" /\
   strlit "off" <> strlit "acc" /\ strlit "off" <> strlit "i"` by EVAL_TAC >>
  `FLOOKUP s.locals (strlit "acc") = SOME (ValWord (n2w acc)) /\
   FLOOKUP s.locals (strlit "i") = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals (strlit "len") = SOME (ValWord (n2w (LENGTH vs))) /\
   FLOOKUP s.locals (strlit "buf") = SOME (ValWord bufw) /\
   FLOOKUP s.locals (strlit "off") = SOME (ValWord offw) /\
   memRel vs (bufw + offw) s /\ i <= LENGTH vs /\ LENGTH vs < 2n ** 63 /\
   EVERY (\x. x < 256) vs` by fs [loopInv_def] >>
  qabbrev_tac `dv = (n2w (dstep acc (EL i vs))):word64` >>
  qabbrev_tac `sA = set_var (strlit "acc") (ValWord dv) s` >>
  qabbrev_tac `sB = set_var (strlit "i") (ValWord (n2w (i + 1))) sA` >>
  `sA.clock = s.clock` by simp [Abbr `sA`, set_var_def] >>
  `sB.clock = sA.clock` by simp [Abbr `sB`, set_var_def] >>
  (* step 1: Annot no-op then Assign «acc» = the digest value *)
  `evaluate (Annot (strlit "location") (strlit "(37:6 37:45)"), s) = (NONE, s)`
     by simp [evaluate_def] >>
  `evaluate (Assign Local (strlit "acc")
       (Op And
          [Op Add
             [Panop Mul [Var Local (strlit "acc"); Const (31w:word64)];
              LoadByte (Op Add [Var Local (strlit "buf");
                                Var Local (strlit "off");
                                Var Local (strlit "i")])];
           Const (0xFFFFFFw:word64)]), s) = (NONE, sA)`
     by (asm_simp_tac (srw_ss()) [Once evaluate_def, Abbr `sA`, Abbr `dv`,
             is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  `evaluate (Seq (Annot (strlit "location") (strlit "(37:6 37:45)"))
       (Assign Local (strlit "acc")
          (Op And
             [Op Add
                [Panop Mul [Var Local (strlit "acc"); Const (31w:word64)];
                 LoadByte (Op Add [Var Local (strlit "buf");
                                   Var Local (strlit "off");
                                   Var Local (strlit "i")])];
              Const (0xFFFFFFw:word64)])), s) = (NONE, sA)`
     by (irule Seq_NONE >> qexists_tac `s` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  (* step 2: Annot no-op then Assign «i» = i+1 *)
  `FLOOKUP sA.locals (strlit "i") = SOME (ValWord (n2w i))`
     by simp [Abbr `sA`, set_var_def, FLOOKUP_UPDATE] >>
  `evaluate (Annot (strlit "location") (strlit "(38:6 38:13)"), sA) = (NONE, sA)`
     by simp [evaluate_def] >>
  `evaluate (Assign Local (strlit "i")
       (Op Add [Var Local (strlit "i"); Const (1w:word64)]), sA) = (NONE, sB)`
     by (asm_simp_tac (srw_ss()) [Once evaluate_def, eval_def, OPT_MMAP_def,
               wordLangTheory.word_op_def, word_add_n2w, WORD_ADD_0,
               Abbr `sB`, is_valid_value_def, lookup_kvar_def, shape_of_def]) >>
  `evaluate (Seq (Annot (strlit "location") (strlit "(38:6 38:13)"))
       (Assign Local (strlit "i")
          (Op Add [Var Local (strlit "i"); Const (1w:word64)])), sA)
     = (NONE, sB)`
     by (irule Seq_NONE >> qexists_tac `sA` >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  (* assemble the outer Seq *)
  `evaluate (scanBody, s) = (NONE, sB)`
     by (simp [scanBody_def] >> irule Seq_NONE >> qexists_tac `sA` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `sB` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp [] >>
  (* re-establish the invariant *)
  `dstep acc (EL i vs) < 16777216` by simp [dstep_lt] >>
  `sB.memory = s.memory /\ sB.memaddrs = s.memaddrs /\ sB.be = s.be`
     by simp [Abbr `sB`, Abbr `sA`, set_var_def] >>
  `memRel vs (bufw + offw) sB` by fs [memRel_def] >>
  `i + 1 <= LENGTH vs` by fs [] >>
  simp [loopInv_def, Abbr `sB`, Abbr `sA`, set_var_def, FLOOKUP_UPDATE,
        Abbr `dv`] >>
  fs []
QED

(* ---------------------------------------------------------------------------
   §10  One iteration of the emitted `While`: guard live + clock > 0 reduces
   `evaluate (scanLoop, s)` to `evaluate (scanLoop, s2)` at the next
   (accumulator, index), spending exactly one clock tick.
   --------------------------------------------------------------------------- *)
Theorem scanLoop_unfold:
  loopInv vs bufw offw acc i s /\ i < LENGTH vs /\ s.clock <> 0 ==>
  ?s2. evaluate (scanLoop, s) = evaluate (scanLoop, s2) /\
       loopInv vs bufw offw (dstep acc (EL i vs)) (i + 1) s2 /\
       s2.clock = s.clock - 1
Proof
  strip_tac >>
  `eval s (Cmp Less (Var Local (strlit "i")) (Var Local (strlit "len")))
     = SOME (ValWord 1w)` by (drule eval_loop_guard >> fs []) >>
  `loopInv vs bufw offw acc i (dec_clock s)`
     by (simp [dec_clock_def] >> irule loopInv_clock >> fs []) >>
  drule_all evaluate_scanBody >> strip_tac >>
  qexists_tac `s2` >>
  conj_tac
  >- (
      CONV_TAC (LAND_CONV
        (ONCE_REWRITE_CONV [scanLoop_def] THENC
         ONCE_REWRITE_CONV [evaluate_def])) >>
      simp [GSYM scanLoop_def]) >>
  conj_tac >- fs [] >>
  fs [dec_clock_def]
QED

(* ---------------------------------------------------------------------------
   §11  LINK A FOR THE LOOP — the general-clock loop-invariant induction over
   the clocked `While`.  With clock >= remaining iterations, running the emitted
   `While` from `(acc,i)` TERMINATES and leaves `«acc»` = `n2w (FOLDL dstep acc
   (DROP i vs))` — the Lean digest continued from `(acc,i)`.
   --------------------------------------------------------------------------- *)
Theorem scanLoop_fold_bounded:
  !k vs bufw offw acc i s.
    loopInv vs bufw offw acc i s /\ LENGTH vs - i <= k /\
    LENGTH vs - i <= s.clock ==>
    ?s'. evaluate (scanLoop, s) = (NONE, s') /\
         FLOOKUP s'.locals (strlit "acc")
           = SOME (ValWord (n2w (FOLDL dstep acc (DROP i vs))))
Proof
  Induct_on `k`
  >- (
    rpt strip_tac >>
    `~(i < LENGTH vs)` by fs [] >>
    drule eval_loop_guard >> strip_tac >>
    `DROP i vs = []` by (irule DROP_LENGTH_TOO_LONG >> fs []) >>
    simp [scanLoop_def, Once evaluate_def] >>
    fs [loopInv_def]) >>
  rpt strip_tac >>
  Cases_on `i < LENGTH vs`
  >- (
    `s.clock <> 0` by fs [] >>
    drule_all scanLoop_unfold >> strip_tac >>
    last_x_assum (qspecl_then
       [`vs`,`bufw`,`offw`,`dstep acc (EL i vs)`,`i + 1`,`s2`] mp_tac) >>
    impl_tac >- fs [] >>
    strip_tac >>
    qexists_tac `s'` >>
    `DROP i vs = EL i vs :: DROP (i + 1) vs`
       by (`DROP i vs = EL i vs :: DROP (SUC i) vs`
             by (irule DROP_EL_CONS_local >> fs []) >>
           fs [arithmeticTheory.ADD1]) >>
    `FOLDL dstep acc (DROP i vs)
       = FOLDL dstep (dstep acc (EL i vs)) (DROP (i + 1) vs)`
       by asm_simp_tac (srw_ss()) [FOLDL] >>
    fs []) >>
  drule eval_loop_guard >> strip_tac >>
  `DROP i vs = []` by (irule DROP_LENGTH_TOO_LONG >> fs []) >>
  simp [scanLoop_def, Once evaluate_def] >>
  fs [loopInv_def]
QED

(* ---------------------------------------------------------------------------
   §12  The headline, specialised to a whole scan from acc=0, i=0: the emitted
   `While` computes EXACTLY the Lean digest fold over the ENTIRE viewed slice,
   given clock >= |vs|.  `FOLDL dstep 0 vs` is the HOL twin of the in-bounds arm
   of the Lean `C0.boundScan` digest.
   --------------------------------------------------------------------------- *)
Theorem scanLoop_refines_digest:
  loopInv vs bufw offw 0 0 s /\ LENGTH vs <= s.clock ==>
  ?s'. evaluate (scanLoop, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "acc")
         = SOME (ValWord (n2w (FOLDL dstep 0 vs)))
Proof
  strip_tac >>
  qspecl_then [`LENGTH vs`,`vs`,`bufw`,`offw`,`0`,`0`,`s`] mp_tac
    scanLoop_fold_bounded >>
  impl_tac >- fs [] >>
  strip_tac >> qexists_tac `s'` >> fs []
QED

(* ---------------------------------------------------------------------------
   §13  Bridge to the Lean SPEC's own fold presentation.  C0/C1's `boundScan`
   in-bounds arm is `scanFrom a off len 0`, the LEFT-recursive digest over the
   arena view `a[off .. off+len)`.  `scanFrom` here is byte-identical to
   `boundScanLinkA$scanFrom` (C1) with C1's `step` = this theory's `dstep`
   (both `(acc*31+b) MOD 16777216`).  `foldl_dstep_scanFrom` proves the pure
   list fact that the `FOLDL dstep` the loop computes over the viewed slice
   `TAKE len (DROP off a)` IS `scanFrom a off len` — so the loop result is the
   Lean spec's scan, not merely a coincidentally-shaped fold.
   --------------------------------------------------------------------------- *)
Definition scanFrom_def:
  (scanFrom a off 0 acc = acc) /\
  (scanFrom a off (SUC n) acc = scanFrom a (off + 1) n (dstep acc (EL off a)))
End

Theorem foldl_dstep_scanFrom:
  !len off a acc. off + len <= LENGTH a ==>
    FOLDL dstep acc (TAKE len (DROP off a)) = scanFrom a off len acc
Proof
  Induct >> rw [scanFrom_def] >>
  `off < LENGTH a` by fs [] >>
  `DROP off a = EL off a :: DROP (SUC off) a`
     by (irule DROP_EL_CONS_local >> fs []) >>
  `TAKE (SUC len) (DROP off a) = EL off a :: TAKE len (DROP (SUC off) a)`
     by asm_simp_tac (srw_ss()) [] >>
  `SUC off + len <= LENGTH a` by fs [] >>
  first_x_assum (qspecl_then [`SUC off`,`a`,`dstep acc (EL off a)`] mp_tac) >>
  impl_tac >- fs [] >>
  asm_simp_tac (srw_ss()) [FOLDL, ADD1]
QED

(* The whole-scan headline against the Lean SPEC's `scanFrom`: taking the loop's
   viewed slice `vs` to be the actual arena view `TAKE len (DROP off a)` (what the
   FFI `@load_vec` + `memRel` establish at loop entry — the standard whole-program
   boundary, C3 §5) with the in-bounds side `off + len <= LENGTH a`, the emitted
   `While` leaves `«acc»` holding EXACTLY `n2w (scanFrom a off len 0)` = the
   in-bounds arm of the Lean `boundScan a off len` digest. *)
Theorem scanLoop_refines_scanFrom:
  loopInv (TAKE len (DROP off a)) bufw offw 0 0 s /\
  LENGTH (TAKE len (DROP off a)) <= s.clock /\ off + len <= LENGTH a ==>
  ?s'. evaluate (scanLoop, s) = (NONE, s') /\
       FLOOKUP s'.locals (strlit "acc")
         = SOME (ValWord (n2w (scanFrom a off len 0)))
Proof
  strip_tac >>
  drule_all scanLoop_refines_digest >> strip_tac >>
  qexists_tac `s'` >> conj_tac >- fs [] >>
  `FOLDL dstep 0 (TAKE len (DROP off a)) = scanFrom a off len 0`
     by (irule foldl_dstep_scanFrom >> fs []) >>
  fs []
QED

val _ = export_theory ();

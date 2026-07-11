(* ===========================================================================
   C28 probe, PART A — THE TRANSFORM-STAGE STORE LOOP (new machinery).

   The decision/gate stages (C13..C27) compile to a reported SCALAR
   (`report_vec (n2w decision)`).  A TRANSFORM stage produces OUTPUT BYTES: it
   writes response-header bytes into the response buffer.  C26 closed
   `securityheadersStage`'s HSTS decision core but named the residual: the whole
   `(wireHeaders policy).foldl ResponseBuilder.addHeader` BYTE effect.

   This theory compiles THAT byte effect's kernel — the in-place multi-byte
   write — to Pancake, run against the REAL `panSem$evaluate`.  The deployed
   security-header set is a compile-time CONSTANT block (see C26 §1: the deployed
   policy renders a fixed 4-header list).  The emitted transform stages that
   constant block (the read-only header data) and COPIES it byte-by-byte into the
   response output buffer via a `While` + `StoreByte` loop.

   THE MODEL WRITER IT REALISES: drorb `Datapath/Refine.lean`
     storeFrom buf base []        = buf
     storeFrom buf base (b :: bs) = storeFrom (buf.set! base b) (base+1) bs
   — one `set!` per byte, no fresh allocation (the zero-copy in-place write) —
   with `storeFrom_get!_at` : `(storeFrom buf base bs).get! (base+i) = bs[i]`
   (the write is byte-for-byte faithful).  `copyLoop_writes` below is the EMITTED
   analogue of `storeFrom_get!_at`, proven against `panSem$evaluate`: after the
   compiled loop, `mem_load_byte (out + n2w j) = SOME (n2w (EL j bs))` for every
   in-range `j` — the machine wrote EXACTLY the source bytes.

   No FFI in the loop itself; the loop is pure memory effect.  Kernel-checked.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib
     finite_mapTheory combinTheory miscTheory;
open panLangTheory panSemTheory panPropsTheory;
open panAutoTheory;        (* signed_lt_n2w64 *)
open c14GenericTheory;     (* noFFI, noFFI_io_events, Seq_thread *)

val _ = new_theory "transformCopyLoop";

val gd64 = prove(“good_dimindex (:64)”, EVAL_TAC);

(* n2w is injective on the signed-positive range (both < 2^63 < 2^64). *)
Theorem n2w_lt63_11:
  a < 2n ** 63 /\ b < 2n ** 63 ==>
    (((n2w a):word64) = n2w b <=> a = b)
Proof
  rw [] >> `dimword (:64) = 2n ** 64` by EVAL_TAC >>
  `a < dimword (:64) /\ b < dimword (:64)` by fs [] >>
  metis_tac [n2w_11, LESS_MOD]
QED

Theorem w2w_byte:
  !x. x < 256 ==> (w2w ((n2w x):word8) : word64) = n2w x
Proof
  rw [w2w_def, w2n_n2w] >> `dimword (:8) = 256` by EVAL_TAC >> fs [] >>
  `x MOD 256 = x` by (irule LESS_MOD >> fs []) >> fs []
QED

Theorem DROP_EL_CONS_local:
  !n l. n < LENGTH l ==> DROP n l = EL n l :: DROP (SUC n) l
Proof
  Induct >> Cases_on `l` >> fs []
QED

(* ---------------------------------------------------------------------------
   BYTE-MEMORY read/write lemmas.  A `StoreByte` updates one word (the byte-
   aligned word containing the target) via `set_byte`.  We need the read-back:
   what we store is read back at the same address (the faithful write), and a
   read at any OTHER byte address is unchanged (the disjoint write).
   --------------------------------------------------------------------------- *)

(* read-back at the SAME address: the byte you stored. *)
Theorem mem_load_store_byte_same:
  byte_align (wa:word64) IN dm /\ m (byte_align wa) = Word v ==>
    mem_load_byte ((byte_align wa =+ Word (set_byte wa b v be)) m) dm be wa
      = SOME b
Proof
  rpt strip_tac >>
  `get_byte wa (set_byte wa b v be) be = b`
     by (irule good_dimindex_get_byte_set_byte >> EVAL_TAC) >>
  simp [mem_load_byte_def, APPLY_UPDATE_THM] >> fs []
QED

(* read at a DIFFERENT byte address is unchanged by the store. *)
Theorem mem_load_store_byte_ne:
  (wr:word64) <> wa /\ m (byte_align wa) = Word v ==>
    mem_load_byte ((byte_align wa =+ Word (set_byte wa b v be)) m) dm be wr
      = mem_load_byte m dm be wr
Proof
  strip_tac >> Cases_on `byte_align wr = byte_align wa`
  >- (
    (* same word, different byte lane *)
    `get_byte wr (set_byte wa b v be) be = get_byte wr v be`
       by (irule get_byte_set_byte_diff >> fs [gd64]) >>
    simp [mem_load_byte_def, APPLY_UPDATE_THM] >> fs [])
  >- (
    (* different word: the update misses byte_align wr entirely *)
    simp [mem_load_byte_def, APPLY_UPDATE_THM] >> fs [])
QED

(* ---------------------------------------------------------------------------
   THE SOURCE relation (identical to the C5/C6/C16 byte-read relation `memRel`):
   the staged constant block `bs` is readable byte-by-byte at `src`.
   --------------------------------------------------------------------------- *)
Definition memRel_def:
  memRel (bs:num list) (src:word64) (s:(64,'ffi) panSem$state) <=>
    !j. j < LENGTH bs ==>
        mem_load_byte s.memory s.memaddrs s.be (src + n2w j)
          = SOME ((n2w (EL j bs)):word8)
End

(* A byte address is WRITABLE: its containing word is a mapped data word. *)
Definition byteWritable_def:
  byteWritable (s:(64,'ffi) panSem$state) (w:word64) <=>
    byte_align w IN s.memaddrs /\ ?v. s.memory (byte_align w) = Word v
End

(* the source word-region is DISJOINT from the output word-region: no store into
   the output ever aliases a source word (so the source read survives the write).
   Established by the load_vec oracle staging (non-overlapping regions). *)
Definition disjWords_def:
  disjWords (src:word64) (out:word64) (len:num) <=>
    !j k. j < len /\ k < len ==>
          byte_align (out + n2w j) <> byte_align (src + n2w k)
End

(* ---------------------------------------------------------------------------
   THE STORE-LOOP INVARIANT.  Index `i` at «i», length at «n», source/out base
   pointers pinned; the source is still readable (`memRel`), the FIRST `i` output
   bytes already hold the source bytes (the `storeFrom` partial write), the whole
   output region is writable, and the two regions are word-disjoint.
   --------------------------------------------------------------------------- *)
Definition copyInv_def:
  copyInv (bs:num list) (src:word64) (out:word64) (i:num)
          (s:(64,'ffi) panSem$state) <=>
    FLOOKUP s.locals «i»   = SOME (ValWord (n2w i)) /\
    FLOOKUP s.locals «n»   = SOME (ValWord (n2w (LENGTH bs))) /\
    FLOOKUP s.locals «src» = SOME (ValWord src) /\
    FLOOKUP s.locals «out» = SOME (ValWord out) /\
    memRel bs src s /\
    (!j. j < i ==>
         mem_load_byte s.memory s.memaddrs s.be (out + n2w j)
           = SOME ((n2w (EL j bs)):word8)) /\
    (!j. j < LENGTH bs ==> byteWritable s (out + n2w j)) /\
    disjWords src out (LENGTH bs) /\
    i <= LENGTH bs /\ LENGTH bs < 2n ** 63 /\ EVERY (\x. x < 256) bs
End

Theorem copyInv_clock:
  copyInv bs src out i s ==> copyInv bs src out i (s with clock := ck)
Proof
  rw [copyInv_def, memRel_def, byteWritable_def]
QED

(* ---------------------------------------------------------------------------
   THE EMITTED LOOP.  guard: signed `i < n`; body: `st8 out+i, ld8u src+i; i++`.
   `copyBody` is EXACTLY the `storeFrom` step (one byte store per iteration).
   --------------------------------------------------------------------------- *)
Definition copyGuard_def:
  copyGuard = Cmp Less (Var Local «i») (Var Local «n»)
End

Definition copyBody_def:
  copyBody =
    Seq (StoreByte (Op Add [Var Local «out»; Var Local «i»])
                   (LoadByte (Op Add [Var Local «src»; Var Local «i»])))
        (Assign Local «i» (Op Add [Var Local «i»; Const 1w]))
End

Definition copyLoop_def:
  copyLoop = While copyGuard copyBody
End

(* guard is 1w exactly while i < LENGTH bs (signed order = nat order in range). *)
Theorem eval_copyGuard:
  copyInv bs src out i s ==>
    eval s copyGuard = SOME (ValWord (if i < LENGTH bs then 1w else 0w))
Proof
  strip_tac >>
  `FLOOKUP s.locals «i» = SOME (ValWord (n2w i)) /\
   FLOOKUP s.locals «n» = SOME (ValWord (n2w (LENGTH bs))) /\
   i <= LENGTH bs /\ LENGTH bs < 2n ** 63` by fs [copyInv_def] >>
  `i < 2n ** 63` by (irule LESS_EQ_LESS_TRANS >> qexists_tac `LENGTH bs` >> fs []) >>
  `(n2w i:word64 < n2w (LENGTH bs)) = (i < LENGTH bs)`
     by (irule signed_lt_n2w64 >> fs []) >>
  simp [copyGuard_def, eval_def, asmTheory.word_cmp_def]
QED

(* the per-iteration source read: eval of `ld8u src+i` = the i-th model byte. *)
Theorem eval_copySrc:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    eval s (LoadByte (Op Add [Var Local «src»; Var Local «i»]))
      = SOME (ValWord ((n2w (EL i bs)):word64))
Proof
  strip_tac >>
  `EL i bs < 256` by (fs [copyInv_def, EVERY_EL]) >>
  `mem_load_byte s.memory s.memaddrs s.be (src + n2w i)
      = SOME ((n2w (EL i bs)):word8)` by (fs [copyInv_def, memRel_def]) >>
  `FLOOKUP s.locals «src» = SOME (ValWord src) /\
   FLOOKUP s.locals «i» = SOME (ValWord (n2w i))` by fs [copyInv_def] >>
  simp [eval_def, OPT_MMAP_def, wordLangTheory.word_op_def, WORD_ADD_0, w2w_byte]
QED

(* ---------------------------------------------------------------------------
   ONE ITERATION.  `copyBody` stores the i-th source byte into `out+i`,
   advances `i`, and re-establishes `copyInv` at `i+1`.  This is the emitted
   `storeFrom` step; its post-condition preserves the source read (word-disjoint
   store), extends the written prefix by one faithful byte, and keeps the region
   writable.  ~ mirrors `storeFrom` recursion in drorb Datapath/Refine.lean.
   --------------------------------------------------------------------------- *)
(* --- ABSTRACT store-effect lemmas (state-free): the whole-region reasoning
   for ONE byte store at `out + n2w i`, factored out of the state machinery. --- *)

(* the written prefix EXTENDS by one faithful byte (the emitted `storeFrom` step
   analogue of drorb `storeFrom_get!_at`). *)
Theorem store_prefix_extend:
  byte_align ((out:word64) + n2w i) IN dm /\ m (byte_align (out + n2w i)) = Word v /\
  EL i bs < 256 /\ i < LENGTH (bs:num list) /\ LENGTH bs < 2n ** 63 /\
  (!j. j < i ==> mem_load_byte m dm be (out + n2w j) = SOME ((n2w (EL j bs)):word8)) ==>
  !j. j < i + 1 ==>
      mem_load_byte
        ((byte_align (out + n2w i) =+ Word (set_byte (out + n2w i) ((n2w (EL i bs)):word8) v be)) m)
        dm be (out + n2w j) = SOME ((n2w (EL j bs)):word8)
Proof
  rpt strip_tac >> Cases_on `j = i`
  >- (gvs [] >> irule mem_load_store_byte_same >> fs [])
  >- (`j < i` by fs [] >>
      `mem_load_byte m dm be (out + n2w j) = SOME ((n2w (EL j bs)):word8)` by fs [] >>
      `(out + n2w j) <> (out + n2w i)`
         by (`j < 2n ** 63 /\ i < 2n ** 63` by fs [] >> `j <> i` by fs [] >>
             `(n2w j :word64) <> n2w i` by metis_tac [n2w_lt63_11] >>
             fs [WORD_EQ_ADD_LCANCEL]) >>
      `mem_load_byte
         ((byte_align (out + n2w i) =+ Word (set_byte (out + n2w i) ((n2w (EL i bs)):word8) v be)) m)
         dm be (out + n2w j) = mem_load_byte m dm be (out + n2w j)`
         by (irule mem_load_store_byte_ne >> fs []) >>
      fs [])
QED

(* the SOURCE read survives the store (word-disjoint regions): the emitted
   analogue of drorb `denote_storeFrom_disjoint`. *)
Theorem store_source_preserve:
  m (byte_align ((out:word64) + n2w i)) = Word v /\ i < len /\
  disjWords src out len /\
  (!j. j < len ==> mem_load_byte m dm be (src + n2w j) = SOME ((n2w (EL j (bs:num list))):word8)) ==>
  !j. j < len ==>
      mem_load_byte
        ((byte_align (out + n2w i) =+ Word (set_byte (out + n2w i) b v be)) m)
        dm be (src + n2w j) = SOME ((n2w (EL j bs)):word8)
Proof
  rpt strip_tac >>
  `byte_align (out + n2w i) <> byte_align (src + n2w j)`
     by (fs [disjWords_def] >> first_x_assum (qspecl_then [`i`,`j`] mp_tac) >> fs []) >>
  `src + n2w j <> out + n2w i` by (CCONTR_TAC >> fs []) >>
  `mem_load_byte
     ((byte_align (out + n2w i) =+ Word (set_byte (out + n2w i) b v be)) m)
     dm be (src + n2w j) = mem_load_byte m dm be (src + n2w j)`
     by (irule mem_load_store_byte_ne >> fs []) >>
  fs []
QED

(* the output region stays WRITABLE across the store (set_byte keeps `Word`). *)
Theorem store_region_writable:
  byte_align ((out:word64) + n2w i) IN dm /\ m (byte_align (out + n2w i)) = Word v /\
  (!j. j < len ==> byte_align (out + n2w j) IN dm /\ ?w. m (byte_align (out + n2w j)) = Word w) ==>
  !j. j < len ==>
      byte_align (out + n2w j) IN dm /\
      ?w. ((byte_align (out + n2w i) =+ Word (set_byte (out + n2w i) b v be)) m)
            (byte_align (out + n2w j)) = Word w
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `byte_align (out + n2w j) IN dm /\ ?w. m (byte_align (out + n2w j)) = Word w`
     by (first_x_assum (qspec_then `j` mp_tac) >> fs []) >>
  conj_tac >- fs [] >>
  Cases_on `byte_align (out + n2w j) = byte_align (out + n2w i)` >>
  simp [APPLY_UPDATE_THM] >> fs [] >> metis_tac []
QED

Theorem copyBody_step:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    ?s2. evaluate (copyBody, s) = (NONE, s2) /\ s2.clock = s.clock /\
         copyInv bs src out (i+1) s2
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
  (* the stored byte is the low byte of the loaded word = the model byte *)
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
  (* --- evaluate the increment --- *)
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
  qexists_tac `sI` >>
  `sI.clock = s.clock` by simp [Abbr `sI`, Abbr `sS`] >>
  `sI.memory = m2 /\ sI.memaddrs = s.memaddrs /\ sI.be = s.be`
     by simp [Abbr `sI`, Abbr `sS`] >>
  `FLOOKUP sI.locals «i» = SOME (ValWord (n2w (i+1))) /\
   FLOOKUP sI.locals «n» = SOME (ValWord (n2w (LENGTH bs))) /\
   FLOOKUP sI.locals «src» = SOME (ValWord src) /\
   FLOOKUP sI.locals «out» = SOME (ValWord out)`
     by (simp [Abbr `sI`, Abbr `sS`, FLOOKUP_UPDATE] >> fs [copyInv_def]) >>
  (* extract each side fact SEPARATELY (so the store lemmas' premises discharge) *)
  `memRel bs src s` by fs [copyInv_def] >>
  `disjWords src out (LENGTH bs)` by fs [copyInv_def] >>
  `LENGTH bs < 2n ** 63` by fs [copyInv_def] >>
  `EVERY (\x. x < 256) bs` by fs [copyInv_def] >>
  `!j. j < LENGTH bs ==> byteWritable s (out + n2w j)` by fs [copyInv_def] >>
  `!j. j < i ==> mem_load_byte s.memory s.memaddrs s.be (out + n2w j)
                   = SOME ((n2w (EL j bs)):word8)` by fs [copyInv_def] >>
  `i < LENGTH bs` by fs [] >>
  (* THE THREE re-established memory relations about `m2`, each closed by ONE
     abstract store lemma (`ho_match_mp_tac`, premises discharged by `fs`) — the
     source read survives (`store_source_preserve`), the written prefix extends
     (`store_prefix_extend`), the region stays writable (`store_region_writable`). *)
  `!j. j < LENGTH bs ==>
       mem_load_byte m2 s.memaddrs s.be (src + n2w j) = SOME ((n2w (EL j bs)):word8)`
     by (qunabbrev_tac `m2` >> ho_match_mp_tac store_source_preserve >> fs [memRel_def]) >>
  `!j. j < i + 1 ==>
       mem_load_byte m2 s.memaddrs s.be (out + n2w j) = SOME ((n2w (EL j bs)):word8)`
     by (qunabbrev_tac `m2` >> ho_match_mp_tac store_prefix_extend >> fs []) >>
  `!j. j < LENGTH bs ==>
       byte_align (out + n2w j) IN s.memaddrs /\ ?w. m2 (byte_align (out + n2w j)) = Word w`
     by (qunabbrev_tac `m2` >> ho_match_mp_tac store_region_writable >> fs [] >>
         rpt strip_tac >> first_x_assum (qspec_then `j` mp_tac) >> fs [byteWritable_def]) >>
  (* assemble copyInv at i+1: rewrite sI's memory to m2 and discharge each conjunct *)
  simp [copyInv_def, memRel_def, byteWritable_def] >> rw [] >> fs []
QED

(* ---------------------------------------------------------------------------
   THE BOUNDED WHILE INDUCTION (mirrors C16 `foldLoop_bounded`, but the invariant
   carries the WRITTEN-PREFIX memory relation — the genuinely new content).
   From the per-step, the whole clocked loop runs to `i = LENGTH bs` with the
   full output prefix written.
   --------------------------------------------------------------------------- *)
Theorem copyLoop_iter:
  copyInv bs src out i s /\ i < LENGTH bs /\ s.clock <> 0 ==>
    ?s2. evaluate (copyLoop, s) = evaluate (copyLoop, s2) /\
         copyInv bs src out (i+1) s2 /\ s2.clock = s.clock - 1
Proof
  strip_tac >>
  `eval s copyGuard = SOME (ValWord 1w)` by (drule eval_copyGuard >> fs []) >>
  `copyInv bs src out i (dec_clock s)`
     by (simp [dec_clock_def] >> irule copyInv_clock >> fs []) >>
  drule_all copyBody_step >> strip_tac >>
  qexists_tac `s2` >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >> simp [] >>
  `evaluate (copyLoop, s) = evaluate (copyLoop, s2)`
     by (simp [copyLoop_def] >>
         CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >> simp []) >>
  fs []
QED

Theorem copyLoop_bounded:
  !k i (s:(64,'ffi) panSem$state).
    copyInv bs src out i s /\ LENGTH bs - i <= k /\ LENGTH bs - i <= s.clock ==>
    ?s'. evaluate (copyLoop, s) = (NONE, s') /\
         copyInv bs src out (LENGTH bs) s'
Proof
  Induct
  >- ((* k = 0: i = LENGTH bs, guard false, exit *)
      rpt strip_tac >> `i = LENGTH bs` by fs [copyInv_def] >>
      `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
      qexists_tac `s` >>
      `evaluate (copyLoop, s) = (NONE, s)`
         by (simp [copyLoop_def, Once evaluate_def]) >> fs [])
  >- (rpt strip_tac >> Cases_on `i < LENGTH bs`
      >- ((* an iteration runs *)
          `s.clock <> 0` by fs [] >>
          drule_all copyLoop_iter >> strip_tac >>
          `LENGTH bs - (i + 1) <= k` by fs [] >>
          `LENGTH bs - (i + 1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`s2`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >> qexists_tac `s'` >> fs [])
      >- ((* guard false at s: terminal *)
          `i = LENGTH bs` by fs [copyInv_def] >>
          `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
          qexists_tac `s` >>
          `evaluate (copyLoop, s) = (NONE, s)`
             by (simp [copyLoop_def, Once evaluate_def]) >> fs []))
QED

(* ---------------------------------------------------------------------------
   THE HEADLINE — the emitted analogue of drorb `storeFrom_get!_at`.
   From a fresh (i = 0) state with clock >= |bs|, the compiled copy loop writes
   EXACTLY the source bytes into the output buffer: reading back byte `j` yields
   the j-th model byte `n2w (EL j bs)`.  This is the in-place multi-byte write of
   the transform stage, proven against `panSem$evaluate` — the machine writes the
   right bytes.
   --------------------------------------------------------------------------- *)
Theorem copyLoop_writes:
  copyInv bs src out 0 s /\ LENGTH bs <= s.clock ==>
    ?s'. evaluate (copyLoop, s) = (NONE, s') /\
         (!j. j < LENGTH bs ==>
              mem_load_byte s'.memory s'.memaddrs s'.be (out + n2w j)
                = SOME ((n2w (EL j bs)):word8)) /\
         FLOOKUP s'.locals «out» = SOME (ValWord out)
Proof
  strip_tac >>
  qspecl_then [`LENGTH bs`,`0`,`s`] mp_tac copyLoop_bounded >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> rpt conj_tac
  >- fs []
  >- (rpt strip_tac >> fs [copyInv_def])
  >- fs [copyInv_def]
QED

(* the copy loop makes NO FFI call — its whole effect is the in-place byte write;
   hence it leaves the observable trace unchanged (used by any wrapper that
   reports the written buffer). *)
Theorem copyLoop_noFFI:
  noFFI copyLoop
Proof
  simp [copyLoop_def, copyBody_def] >> EVAL_TAC
QED

Theorem copyLoop_io_events:
  evaluate (copyLoop, s) = (NONE, s') ==> s'.ffi.io_events = s.ffi.io_events
Proof
  strip_tac >> irule noFFI_io_events >>
  qexists_tac `copyLoop` >> qexists_tac `NONE` >>
  conj_tac >- simp [copyLoop_noFFI] >> first_assum ACCEPT_TAC
QED

(* ===========================================================================
   C30 ADDITION — the copy loop on the GENUINE PARSED while body.

   `copyBodyA` is the VERBATIM Annot-wrapped `while` body the CakeML-verified
   parser emits for copy.pnk (dumped, transcribed exactly, location Annots
   included) — leanc OUT of the TCB.  `copyLoopA = While copyGuard copyBodyA` is
   the emitted loop.  The two transparent location Annots are behaviourally
   invisible, so `copyBodyA` evaluate-equals the annot-free `copyBody`, and the
   whole PART-A store-loop machinery (`copyBody_step`, the abstract store lemmas,
   the bounded `While` induction) carries with a ONE-LINE bridge per step.
   =========================================================================== *)

(* an Annot-prefixed statement is transparent, as a rewrite. *)
Theorem Annot_Seq_eq:
  !l m X (s:(64,'ffi) panSem$state).
    evaluate (Seq (Annot l m) X, s) = evaluate (X, s)
Proof
  rpt gen_tac >> Cases_on `evaluate (X,s)` >> metis_tac [Annot_Seq]
QED

(* the VERBATIM emitted while body (Annot-wrapped) from the parser. *)
Definition copyBodyA_def:
  copyBodyA =
    Seq
      (Seq (Annot «location» «(23:8 23:25)»)
           (StoreByte (Op Add [Var Local «out»; Var Local «i»])
                      (LoadByte (Op Add [Var Local «src»; Var Local «i»]))))
      (Seq (Annot «location» «(24:4 24:11)»)
           (Assign Local «i» (Op Add [Var Local «i»; Const 1w])))
End

Definition copyLoopA_def:
  copyLoopA = While copyGuard copyBodyA
End

(* the parsed body evaluate-equals the annot-free `copyBody` (the two Annots are
   behaviourally invisible). *)
Theorem copyBodyA_body_eq:
  !(s:(64,'ffi) panSem$state). evaluate (copyBodyA, s) = evaluate (copyBody, s)
Proof
  gen_tac >> simp [copyBodyA_def, copyBody_def] >>
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, Annot_Seq_eq])) >>
  CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def])) >>
  REFL_TAC
QED

(* the per-step fill-in, on the parsed body — bridged to `copyBody_step`. *)
Theorem copyBodyA_step:
  copyInv bs src out i s /\ i < LENGTH bs ==>
    ?s2. evaluate (copyBodyA, s) = (NONE, s2) /\ s2.clock = s.clock /\
         copyInv bs src out (i+1) s2
Proof
  strip_tac >> drule_all copyBody_step >> strip_tac >>
  qexists_tac `s2` >> simp [copyBodyA_body_eq]
QED

Theorem copyLoopA_iter:
  copyInv bs src out i s /\ i < LENGTH bs /\ s.clock <> 0 ==>
    ?s2. evaluate (copyLoopA, s) = evaluate (copyLoopA, s2) /\
         copyInv bs src out (i+1) s2 /\ s2.clock = s.clock - 1
Proof
  strip_tac >>
  `eval s copyGuard = SOME (ValWord 1w)` by (drule eval_copyGuard >> fs []) >>
  `copyInv bs src out i (dec_clock s)`
     by (simp [dec_clock_def] >> irule copyInv_clock >> fs []) >>
  drule_all copyBodyA_step >> strip_tac >>
  qexists_tac `s2` >>
  `s2.clock = s.clock - 1` by fs [dec_clock_def] >> simp [] >>
  `evaluate (copyLoopA, s) = evaluate (copyLoopA, s2)`
     by (simp [copyLoopA_def] >>
         CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >> simp []) >>
  fs []
QED

Theorem copyLoopA_bounded:
  !k i (s:(64,'ffi) panSem$state).
    copyInv bs src out i s /\ LENGTH bs - i <= k /\ LENGTH bs - i <= s.clock ==>
    ?s'. evaluate (copyLoopA, s) = (NONE, s') /\
         copyInv bs src out (LENGTH bs) s'
Proof
  Induct
  >- (rpt strip_tac >> `i = LENGTH bs` by fs [copyInv_def] >>
      `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
      qexists_tac `s` >>
      `evaluate (copyLoopA, s) = (NONE, s)`
         by (simp [copyLoopA_def, Once evaluate_def]) >> fs [])
  >- (rpt strip_tac >> Cases_on `i < LENGTH bs`
      >- (`s.clock <> 0` by fs [] >>
          drule_all copyLoopA_iter >> strip_tac >>
          `LENGTH bs - (i + 1) <= k` by fs [] >>
          `LENGTH bs - (i + 1) <= s2.clock` by fs [] >>
          last_x_assum (qspecl_then [`i+1`,`s2`] mp_tac) >>
          impl_tac >- fs [] >> strip_tac >> qexists_tac `s'` >> fs [])
      >- (`i = LENGTH bs` by fs [copyInv_def] >>
          `eval s copyGuard = SOME (ValWord 0w)` by (drule eval_copyGuard >> fs []) >>
          qexists_tac `s` >>
          `evaluate (copyLoopA, s) = (NONE, s)`
             by (simp [copyLoopA_def, Once evaluate_def]) >> fs []))
QED

Theorem copyLoopA_writes:
  copyInv bs src out 0 s /\ LENGTH bs <= s.clock ==>
    ?s'. evaluate (copyLoopA, s) = (NONE, s') /\
         (!j. j < LENGTH bs ==>
              mem_load_byte s'.memory s'.memaddrs s'.be (out + n2w j)
                = SOME ((n2w (EL j bs)):word8)) /\
         FLOOKUP s'.locals «out» = SOME (ValWord out)
Proof
  strip_tac >>
  qspecl_then [`LENGTH bs`,`0`,`s`] mp_tac copyLoopA_bounded >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> rpt conj_tac
  >- fs []
  >- (rpt strip_tac >> fs [copyInv_def])
  >- fs [copyInv_def]
QED

(* copyLoopA runs the counter «i» to completion: at exit «i» = n2w (LENGTH bs).
   copyLoopA_locals covers every var EXCEPT «i», so a two-loop caller that RESETS
   «i» (Assign i := 0 before the second loop) needs this to discharge the
   Pancake is_valid_value shape check on «i». *)
Theorem copyLoopA_i_final:
  copyInv bs src out 0 s /\ LENGTH bs <= s.clock ==>
    ?s'. evaluate (copyLoopA, s) = (NONE, s') /\
         FLOOKUP s'.locals «i» = SOME (ValWord (n2w (LENGTH bs)))
Proof
  strip_tac >>
  qspecl_then [`LENGTH bs`,`0`,`s`] mp_tac copyLoopA_bounded >>
  impl_tac >- fs [] >> strip_tac >>
  qexists_tac `s'` >> fs [copyInv_def]
QED

Theorem copyLoopA_noFFI:
  noFFI copyLoopA
Proof
  simp [copyLoopA_def, copyBodyA_def, noFFI_def]
QED

Theorem copyLoopA_io_events:
  evaluate (copyLoopA, s) = (NONE, s') ==> s'.ffi.io_events = s.ffi.io_events
Proof
  strip_tac >> irule noFFI_io_events >>
  qexists_tac `copyLoopA` >> qexists_tac `NONE` >>
  conj_tac >- simp [copyLoopA_noFFI] >> first_assum ACCEPT_TAC
QED

val _ = export_theory ();

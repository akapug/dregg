(* ===========================================================================
   C20 — the FFI-oracle contract + the verbatim emitted `main` body for the
   deployed cache-key-hash program.  The control block is at `ctrl` = @base:
   [0)=arena length, [8)=result slot; the arena is at ctrl+32 (the byte relation
   `memRel` the fold loop reads via the `base` local).  `hashMainBody` is the
   VERBATIM body of «main» in hashBytesProg (the verified parser's output on
   hashbytes.pnk) with the C20 `hashLoopCore` constant folded in for the emitted
   `While` (leanc out of TCB — the surgery fires only if the parsed subterm IS the
   loop core).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory hashBytesLoopTheory hashCoreTheory c14GenericTheory;
open hashBytesLinkBInstTheory;   (* hashBytesProg, hashBytesProg_def *)

val _ = new_theory "hashWrapperLinkA";

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

(* --- store the fold result `acc` at ctrl+8 --- *)
Theorem evaluate_store_ctrl_acc:
  !s ba w.
    FLOOKUP s.locals «ctrl» = SOME (ValWord ba) /\
    FLOOKUP s.locals «acc» = SOME (ValWord w) /\
    (ba + 8w) IN s.memaddrs ==>
    evaluate (Store (Op Add [Var Local «ctrl»; Const 8w]) (Var Local «acc»), s) =
      (NONE, s with memory := ((ba + 8w) =+ Word w) s.memory)
Proof
  rpt strip_tac >>
  simp [evaluate_def, eval_def, OPT_MMAP_def, wordLangTheory.word_op_def,
        flatten_def, mem_stores_def, mem_store_def]
QED

(* ---------------------------------------------------------------------------
   The staged control block + arena the load_vec oracle establishes.
   --------------------------------------------------------------------------- *)
Definition hashCtrlStaged_def:
  hashCtrlStaged (input:num list) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w (LENGTH input)) /\
    (ba + 8w) IN s.memaddrs /\
    memRel input (ba + 32w) s /\
    LENGTH input < 2n ** 63 /\ EVERY (\x. x < 256) input
End

(* ---------------------------------------------------------------------------
   THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract.
   (L) @load_vec stages the control block + arena (per hashCtrlStaged).
   (R) @report_vec emits the result word `w` (read from ctrl+8) onto the trace.
   --------------------------------------------------------------------------- *)
Definition hashFFI_def:
  hashFFI (input:num list) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «base» = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 16w)
                     (Var Local «base») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         hashCtrlStaged input s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (!(s:(64,'ffi) panSem$state) (w:word64).
           FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
           (s.base_addr + 8w) IN s.memaddrs /\
           s.memory (s.base_addr + 8w) = Word w ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Op Add [Var Local «ctrl»; Const 8w])
                     (Const 8w) (Var Local «ctrl») (Const 8w), s) = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++ [IO_event (ffi$ExtCall «report_vec») (word_to_bytes w F) rb])
End

(* ---------------------------------------------------------------------------
   hashMainBody = the VERBATIM body of «main» in hashBytesProg (parser output),
   with the emitted `While` folded to the constant `hashLoopCore` (ML surgery).
   --------------------------------------------------------------------------- *)
val funcs_body = (REWRITE_CONV [hashBytesProg_def] THENC EVAL)
                   “functions hashBytesProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = Term.inst [Type.alpha |-> “:64”] body_tm;
val coreUnfolded = (REWRITE_CONV [hashLoopCore_def, foldGuard_def, hashBodyA_def]
                      “hashLoopCore”) |> concl |> rhs |> Term.inst [Type.alpha |-> “:64”];
val hashLoopCore64 = Term.inst [Type.alpha |-> “:64”] “hashLoopCore”;
val body_core   = Term.subst [coreUnfolded |-> hashLoopCore64] body64;
val hashMainBody_def =
  new_definition("hashMainBody_def", “hashMainBody = ^body_core”);

val _ = if Term.free_in hashLoopCore64 body_core then ()
        else raise Fail "hashLoopCore substitution did not fire";

val _ = export_theory ();

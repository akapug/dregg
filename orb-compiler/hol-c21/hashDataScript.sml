(* ===========================================================================
   C21 — the FOLD-SPECIFIC DATA for the deployed cache-key hash: the staged
   control block relation, the FFI-oracle contract, and the `main` body with the
   proven loop core folded in (the ML surgery).  These are the per-fold inputs
   `mk_foldWrapper` consumes; the whole-program wrapper PROOF is generated.

   (Extracted from the C20 hand stack `hashWrapperLinkAScript.sml`; the ctrl-keyed
   eval/store lemmas it also carried now live in the shared `foldWrapCommon`.)
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory hashBytesLoopTheory hashCoreTheory;
open hashBytesLinkBInstTheory;   (* hashBytesProg, hashBytesProg_def *)

val _ = new_theory "hashData";

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

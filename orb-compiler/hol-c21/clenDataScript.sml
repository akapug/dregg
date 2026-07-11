(* ===========================================================================
   C21 — the FOLD-SPECIFIC DATA for the Content-Length decimal fold: the staged
   control-block relation, the FFI-oracle contract, and the `main` body with the
   proven loop core folded in (the ML surgery).  Structurally identical to the
   hash fold's data (same control-block convention: arena length at ctrl, arena at
   ctrl+32, result slot at ctrl+8) — the only per-fold difference is which loop
   core is folded into `main`.  These are the per-fold inputs `mk_foldWrapper`
   consumes; the whole-program wrapper PROOF is generated.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory clenCoreTheory;
open clenLinkBInstTheory;   (* clenProg, clenProg_def *)

val _ = new_theory "clenData";

Definition clenCtrlStaged_def:
  clenCtrlStaged (input:num list) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w (LENGTH input)) /\
    (ba + 8w) IN s.memaddrs /\
    memRel input (ba + 32w) s /\
    LENGTH input < 2n ** 63 /\ EVERY (\x. x < 256) input
End

Definition clenFFI_def:
  clenFFI (input:num list) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «base» = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 16w)
                     (Var Local «base») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         clenCtrlStaged input s.base_addr s1 /\
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

(* clenMainBody = the VERBATIM body of «main» in clenProg (parser output), with
   the emitted `While` folded to the constant `clenLoopCore` (ML surgery). *)
val funcs_body = (REWRITE_CONV [clenProg_def] THENC EVAL)
                   “functions clenProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = Term.inst [Type.alpha |-> “:64”] body_tm;
val coreUnfolded = (REWRITE_CONV [clenLoopCore_def, foldGuard_def, clenBodyA_def]
                      “clenLoopCore”) |> concl |> rhs |> Term.inst [Type.alpha |-> “:64”];
val clenLoopCore64 = Term.inst [Type.alpha |-> “:64”] “clenLoopCore”;
val body_core   = Term.subst [coreUnfolded |-> clenLoopCore64] body64;
val clenMainBody_def =
  new_definition("clenMainBody_def", “clenMainBody = ^body_core”);

val _ = if Term.free_in clenLoopCore64 body_core then ()
        else raise Fail "clenLoopCore substitution did not fire";

val _ = export_theory ();

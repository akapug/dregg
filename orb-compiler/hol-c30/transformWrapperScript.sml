(* ===========================================================================
   C30 — the FFI-oracle contract + the verbatim emitted `main` body for the
   TRANSFORM (constant secheaders) program.  The staging (established by the FFI
   driver @load_vec) puts:
     ctrl = @base ;  out = ctrl+32 (writable output buffer) ;
     src  = ctrl+4096 (read-only source block = the constant header bytes).
   `transformMainBody` is the VERBATIM body of «main» in transformProg (the
   verified parser's output on copy.pnk) with the emitted `While` folded to the
   constant `copyLoopA` (ML surgery — fires only if the parsed subterm IS the
   store-loop core, so leanc stays OUT of the TCB).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open c14GenericTheory transformCopyLoopTheory transformSecHeadersTheory;
open transformLinkBInstTheory;   (* transformProg, transformProg_def *)

val _ = new_theory "transformWrapper";

(* ---------------------------------------------------------------------------
   The staged source block + writable output region the load_vec oracle
   establishes (mirrors C20 hashCtrlStaged; a byte block + scratch instead of a
   length word + result slot).
   --------------------------------------------------------------------------- *)
Definition transformStaged_def:
  transformStaged (bs:num list) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    memRel bs (ba + 4096w) s /\
    (!j. j < LENGTH bs ==> byteWritable s ((ba + 32w) + n2w j)) /\
    disjWords (ba + 4096w) (ba + 32w) (LENGTH bs) /\
    LENGTH bs < 2n ** 63 /\ EVERY (\x. x < 256) bs
End

(* transformStaged is a pure memory/value property (locals-agnostic): it frames
   across any state with the same memory. *)
Theorem transformStaged_frame:
  transformStaged bs ba s /\ s'.memory = s.memory /\
  s'.memaddrs = s.memaddrs /\ s'.be = s.be ==>
  transformStaged bs ba s'
Proof
  rw [transformStaged_def, memRel_def, byteWritable_def] >>
  fs [memRel_def, byteWritable_def]
QED

(* the staged block + the loop locals establish the C28 store-loop invariant. *)
Theorem transformStaged_copyInv:
  transformStaged bs ba s /\
  FLOOKUP s.locals «i» = SOME (ValWord 0w) /\
  FLOOKUP s.locals «n» = SOME (ValWord (n2w (LENGTH bs))) /\
  FLOOKUP s.locals «src» = SOME (ValWord (ba + 4096w)) /\
  FLOOKUP s.locals «out» = SOME (ValWord (ba + 32w)) ==>
  copyInv bs (ba + 4096w) (ba + 32w) 0 s
Proof
  rw [transformStaged_def, copyInv_def] >> fs []
QED

(* ---------------------------------------------------------------------------
   THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract.
   (L) @load_vec stages the source block at src=ctrl+4096 (byte-readable) and the
       output region [out, out+|bs|) writable & word-disjoint (per transformStaged).
   (R) @report_vec emits the OUTPUT BUFFER (|bs| bytes read from out) onto the
       observable trace as EXACTLY `MAP n2w bs` (the response-BYTE transform's
       observable, the multi-byte analogue of C20's single-word report).
   --------------------------------------------------------------------------- *)
Definition transformFFI_def:
  transformFFI (bs:num list) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «out» = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 8w)
                     (Var Local «out») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         transformStaged bs s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (!(s:(64,'ffi) panSem$state).
           FLOOKUP s.locals «out» = SOME (ValWord (s.base_addr + 32w)) /\
           (!j. j < LENGTH bs ==>
                mem_load_byte s.memory s.memaddrs s.be ((s.base_addr + 32w) + n2w j)
                  = SOME ((n2w (EL j bs)):word8)) ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Var Local «out»)
                     (Const (n2w (LENGTH bs))) (Var Local «out») (Const 8w), s)
           = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++
           [IO_event (ffi$ExtCall «report_vec»)
              (MAP (\b. (n2w b):word8) bs) rb])
End

(* ---------------------------------------------------------------------------
   transformMainBody = the VERBATIM «main» body of transformProg (parser output),
   with the emitted `While` folded to the constant `copyLoopA` (ML surgery).
   --------------------------------------------------------------------------- *)
val funcs_body = (REWRITE_CONV [transformProg_def] THENC EVAL)
                   “functions transformProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = Term.inst [Type.alpha |-> “:64”] body_tm;
val coreUnfolded = (REWRITE_CONV [copyLoopA_def, copyGuard_def, copyBodyA_def]
                      “copyLoopA”) |> concl |> rhs |> Term.inst [Type.alpha |-> “:64”];
val copyLoopA64 = Term.inst [Type.alpha |-> “:64”] “copyLoopA”;
val body_core   = Term.subst [coreUnfolded |-> copyLoopA64] body64;
val transformMainBody_def =
  new_definition("transformMainBody_def", “transformMainBody = ^body_core”);

val _ = if Term.free_in copyLoopA64 body_core then ()
        else raise Fail "copyLoopA substitution did not fire";

val _ = export_theory ();

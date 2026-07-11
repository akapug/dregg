(* ===========================================================================
   C32 — the FFI-oracle contract + the verbatim emitted `main` body for the
   two-loop REQUEST-DEPENDENT transform (reflect.pnk).  Staging (established by
   @load_vec):  input at src=ctrl+4096 (byte-readable), scratch mid=ctrl+2048
   writable, output out=ctrl+32 writable, all three word-disjoint.
   reflectMainBody is the VERBATIM body of «main» in reflectProg (verified-parser
   output) — NO ML surgery at all (the two parsed While loops are bridged to the
   C30 copyLoopA store core inside the refinement via reflectSeam.While_body_ext,
   Annots being behaviourally invisible), so leanc is OUT of the TCB by
   construction.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open transformCopyLoopTheory reflectSeamTheory reflectLinkBInstTheory;

val _ = new_theory "reflectWrapper";

(* ---------------------------------------------------------------------------
   The staged input + writable scratch + writable output the load_vec oracle
   establishes.  input at src=ba+4096 ; scratch mid=ba+2048 ; output out=ba+32.
   --------------------------------------------------------------------------- *)
Definition reflectStaged_def:
  reflectStaged (req:num list) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    memRel req (ba + 4096w) s /\
    (!j. j < LENGTH req ==> byteWritable s ((ba + 2048w) + n2w j)) /\
    (!j. j < LENGTH req ==> byteWritable s ((ba + 32w) + n2w j)) /\
    disjWords (ba + 4096w) (ba + 2048w) (LENGTH req) /\
    disjWords (ba + 4096w) (ba + 32w)   (LENGTH req) /\
    disjWords (ba + 2048w) (ba + 32w)   (LENGTH req) /\
    LENGTH req < 2n ** 63 /\ EVERY (\x. x < 256) req
End

(* reflectStaged is a pure memory/value property (locals-agnostic). *)
Theorem reflectStaged_frame:
  reflectStaged req ba s /\ s'.memory = s.memory /\
  s'.memaddrs = s.memaddrs /\ s'.be = s.be ==>
  reflectStaged req ba s'
Proof
  rw [reflectStaged_def, memRel_def, byteWritable_def] >>
  fs [memRel_def, byteWritable_def]
QED

(* loop1 entry invariant: source = input at src=ba+4096, dest = scratch mid=ba+2048. *)
Theorem reflectStaged_copyInv1:
  reflectStaged req ba s /\
  FLOOKUP s.locals «i» = SOME (ValWord 0w) /\
  FLOOKUP s.locals «n» = SOME (ValWord (n2w (LENGTH req))) /\
  FLOOKUP s.locals «src» = SOME (ValWord (ba + 4096w)) /\
  FLOOKUP s.locals «out» = SOME (ValWord (ba + 2048w)) ==>
  copyInv req (ba + 4096w) (ba + 2048w) 0 s
Proof
  rw [reflectStaged_def, copyInv_def] >> fs []
QED

(* ---------------------------------------------------------------------------
   THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract.
   (L) @load_vec stages the request block at src=ctrl+4096 (byte-readable), the
       scratch region [mid, mid+|req|) and output [out, out+|req|) writable &
       pairwise word-disjoint (per reflectStaged).
   (R) @report_vec emits the OUTPUT BUFFER (|req| bytes at out) as EXACTLY
       `MAP n2w req` — the reflected request bytes (the request-dependent output).
   --------------------------------------------------------------------------- *)
Definition reflectFFI_def:
  reflectFFI (req:num list) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «out» = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 8w)
                     (Var Local «out») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         reflectStaged req s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (!(s:(64,'ffi) panSem$state).
           FLOOKUP s.locals «out» = SOME (ValWord (s.base_addr + 32w)) /\
           (!j. j < LENGTH req ==>
                mem_load_byte s.memory s.memaddrs s.be ((s.base_addr + 32w) + n2w j)
                  = SOME ((n2w (EL j req)):word8)) ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Var Local «out»)
                     (Const (n2w (LENGTH req))) (Var Local «out») (Const 8w), s)
           = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++
           [IO_event (ffi$ExtCall «report_vec»)
              (MAP (\b. (n2w b):word8) req) rb])
End

(* ---------------------------------------------------------------------------
   reflectMainBody = the VERBATIM «main» body of reflectProg (parser output).
   NO surgery: the two While loops stay exactly as parsed; they are bridged to
   copyLoopA in the refinement (leanc OUT by construction).
   --------------------------------------------------------------------------- *)
val funcs_body = (REWRITE_CONV [reflectProg_def] THENC EVAL)
                   “functions reflectProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = Term.inst [Type.alpha |-> “:64”] body_tm;
val reflectMainBody_def =
  new_definition("reflectMainBody_def", “reflectMainBody = ^body64”);

val _ = export_theory ();

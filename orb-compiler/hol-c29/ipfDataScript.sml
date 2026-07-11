(* ===========================================================================
   C29 — the ipfilter stage's fold-data: ipfMainBody = «main» of ipfProg with the
   single CIDR-prefix-scan While folded to cidrLoop and the gate to ipfGate.  The
   staging + FFI contract (ipfStaged/ipfFFI) are the single-arena analogue of
   C24's travStaged/travFFI.  Surgery RAISES if a hand core is not a genuine parser
   subterm (leanc OUT of the TCB).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory ipfCoreTheory ipfLinkBInstTheory;

val _ = new_theory "ipfData";

(* ---- what @load_vec establishes: the address arena + its length staged ---- *)
Definition ipfStaged_def:
  ipfStaged (input:num list) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w (LENGTH input)) /\
    (ba + 8w) IN s.memaddrs /\
    memRel input (ba + 32w) s /\
    LENGTH input < 2n ** 63 /\
    EVERY (\x. x < 256) input
End

(* ---- THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract. ---- *)
Definition ipfFFI_def:
  ipfFFI (input:num list) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «base» = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 16w)
                     (Var Local «base») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         ipfStaged input s.base_addr s1 /\
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

(* ---- ipfMainBody = «main» of ipfProg with the While -> cidrLoop and the gate
   -> ipfGate (ML surgery; RAISES if a hand core is not a genuine parser subterm) ---- *)
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val funcs_body = (REWRITE_CONV [ipfProg_def] THENC EVAL) “functions ipfProg”
                   |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = inst64 body_tm;

val cidrLoopU = (REWRITE_CONV [cidrLoop_def, foldGuard_def, cidrBody_def] “cidrLoop”)
                 |> concl |> rhs |> inst64;
val gateU    = (REWRITE_CONV [ipfGate_def] “ipfGate”) |> concl |> rhs |> inst64;
val cidrL = inst64 “cidrLoop”;
val gate = inst64 “ipfGate”;

val body1 = Term.subst [cidrLoopU |-> cidrL] body64;
val body2 = Term.subst [gateU |-> gate] body1;

val ipfMainBody_def =
  new_definition ("ipfMainBody_def", “ipfMainBody = ^body2”);

val _ = if Term.free_in cidrL body2 then () else raise Fail "cidrLoop surgery did not fire";
val _ = if Term.free_in gate body2 then () else raise Fail "ipfGate surgery did not fire";

val _ = export_theory ();

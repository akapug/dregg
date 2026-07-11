(* ===========================================================================
   C24 — the traversal stage's fold-data: travMainBody = «main» of travProg with
   the single escape-scan While folded to escLoop and the gate to travGate.  The
   staging + FFI contract (travStaged/travFFI) are the single-arena analogue of
   C22's cacheStaged/cacheFFI.  Surgery RAISES if a hand core is not a genuine
   parser subterm (leanc OUT of the TCB).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory travCoreTheory travLinkBInstTheory;

val _ = new_theory "travData";

(* ---- what @load_vec establishes: the path arena + its length staged ---- *)
Definition travStaged_def:
  travStaged (input:num list) (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w (LENGTH input)) /\
    (ba + 8w) IN s.memaddrs /\
    memRel input (ba + 32w) s /\
    LENGTH input < 2n ** 63 /\
    EVERY (\x. x < 256) input
End

(* ---- THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract. ---- *)
Definition travFFI_def:
  travFFI (input:num list) (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «base» = SOME (ValWord (s.base_addr + 32w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 16w)
                     (Var Local «base») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         travStaged input s.base_addr s1 /\
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

(* ---- travMainBody = «main» of travProg with the While -> escLoop and the gate
   -> travGate (ML surgery; RAISES if a hand core is not a genuine parser subterm) ---- *)
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val funcs_body = (REWRITE_CONV [travProg_def] THENC EVAL) “functions travProg”
                   |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
val body64      = inst64 body_tm;

val escLoopU = (REWRITE_CONV [escLoop_def, foldGuard_def, escBody_def] “escLoop”)
                 |> concl |> rhs |> inst64;
val gateU    = (REWRITE_CONV [travGate_def] “travGate”) |> concl |> rhs |> inst64;
val escL = inst64 “escLoop”;
val gate = inst64 “travGate”;

val body1 = Term.subst [escLoopU |-> escL] body64;
val body2 = Term.subst [gateU |-> gate] body1;

val travMainBody_def =
  new_definition ("travMainBody_def", “travMainBody = ^body2”);

val _ = if Term.free_in escL body2 then () else raise Fail "escLoop surgery did not fire";
val _ = if Term.free_in gate body2 then () else raise Fail "travGate surgery did not fire";

val _ = export_theory ();

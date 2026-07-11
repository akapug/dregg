(* ===========================================================================
   C22 — the FOLD-DATA for the composed cache-key stage: the staged control
   block + two arenas + age, the FFI-oracle contract (@load_vec / @report_vec),
   and the `main` body with BOTH proven loop cores + the gate folded in (ML
   surgery).  The single trusted assumption is the FFI contract; the surgery
   RAISES if the hand cores are not genuine parser subterms (leanc out of TCB).

   Control block at @base:  mlen@0  tlen@+8  age@+16  result@+24
   method arena @+64  tgt arena @+2112.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory hashBytesLoopTheory cacheKeyCoreTheory;
open cacheKeyLinkBInstTheory;   (* cacheKeyProg, cacheKeyProg_def *)

val _ = new_theory "cacheKeyData";

(* ---- what @load_vec establishes: both arenas + lengths + age staged ---- *)
Definition cacheStaged_def:
  cacheStaged (method:num list) (tgt:num list) (age:num)
              (ba:word64) (s:(64,'ffi) panSem$state) <=>
    ba IN s.memaddrs /\ s.memory ba = Word (n2w (LENGTH method)) /\
    (ba + 8w) IN s.memaddrs /\ s.memory (ba + 8w) = Word (n2w (LENGTH tgt)) /\
    (ba + 16w) IN s.memaddrs /\ s.memory (ba + 16w) = Word (n2w age) /\
    (ba + 24w) IN s.memaddrs /\
    memRel method (ba + 64w) s /\ memRel tgt (ba + 2112w) s /\
    LENGTH method < 2n ** 63 /\ LENGTH tgt < 2n ** 63 /\ age < 4294967296 /\
    EVERY (\x. x < 256) method /\ EVERY (\x. x < 256) tgt
End

(* ---- THE SINGLE NAMED TRUSTED ASSUMPTION — the FFI-oracle contract. ---- *)
Definition cacheFFI_def:
  cacheFFI (method:num list) (tgt:num list) (age:num)
           (s0:(64,'ffi) panSem$state) <=>
    (!(s:(64,'ffi) panSem$state). s.base_addr = s0.base_addr /\
         FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
         FLOOKUP s.locals «base» = SOME (ValWord (s.base_addr + 64w)) ==>
       ?s1 loadEv.
         evaluate (ExtCall «load_vec» (Var Local «ctrl») (Const 32w)
                     (Var Local «base») (Const 4096w), s) = (NONE, s1) /\
         s1.clock = s.clock /\ s1.locals = s.locals /\
         s1.memaddrs = s.memaddrs /\ s1.be = s.be /\
         s1.base_addr = s.base_addr /\ s1.structs = s.structs /\
         cacheStaged method tgt age s.base_addr s1 /\
         s1.ffi.io_events = s.ffi.io_events ++ loadEv) /\
    (!(s:(64,'ffi) panSem$state) (w:word64).
           FLOOKUP s.locals «ctrl» = SOME (ValWord s.base_addr) /\
           (s.base_addr + 24w) IN s.memaddrs /\
           s.memory (s.base_addr + 24w) = Word w ==>
       ?s2 rb.
         evaluate (ExtCall «report_vec» (Op Add [Var Local «ctrl»; Const 24w])
                     (Const 8w) (Var Local «ctrl») (Const 8w), s) = (NONE, s2) /\
         s2.clock = s.clock /\
         s2.ffi.io_events =
           s.ffi.io_events ++ [IO_event (ffi$ExtCall «report_vec») (word_to_bytes w F) rb])
End

(* ---- cacheMainBody = «main» of cacheKeyProg with both While loops folded to
   cacheLoop1/cacheLoop2 and the gate to cacheGate (ML surgery; RAISES if a hand
   core is not a genuine parser subterm). ---- *)
val funcs_body = (REWRITE_CONV [cacheKeyProg_def] THENC EVAL)
                   “functions cacheKeyProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val body64      = inst64 body_tm;

val cl1u = (REWRITE_CONV [cacheLoop1_def, foldGuard_def, cacheBodyA1_def] “cacheLoop1”)
             |> concl |> rhs |> inst64;
val cl2u = (REWRITE_CONV [cacheLoop2_def, foldGuard_def, cacheBodyA2_def] “cacheLoop2”)
             |> concl |> rhs |> inst64;
val cgu  = (REWRITE_CONV [cacheGate_def] “cacheGate”) |> concl |> rhs |> inst64;
val cl1  = inst64 “cacheLoop1”;
val cl2  = inst64 “cacheLoop2”;
val cg   = inst64 “cacheGate”;

val body1 = Term.subst [cl1u |-> cl1] body64;
val body2 = Term.subst [cl2u |-> cl2] body1;
val body3 = Term.subst [cgu  |-> cg ] body2;

val cacheMainBody_def =
  new_definition("cacheMainBody_def", “cacheMainBody = ^body3”);

val _ = if Term.free_in cl1 body3 then () else raise Fail "cacheLoop1 surgery did not fire";
val _ = if Term.free_in cl2 body3 then () else raise Fail "cacheLoop2 surgery did not fire";
val _ = if Term.free_in cg  body3 then () else raise Fail "cacheGate surgery did not fire";

val _ = export_theory ();

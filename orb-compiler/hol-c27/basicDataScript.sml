(* ===========================================================================
   C27 — the Basic-auth stage's fold-data: basicMainBody = «main» of basicProg
   with the two While loops folded to cacheLoop1/cacheLoop2 (REUSED from C22) and
   the gate to basicGate.  The staging + FFI contract are REUSED verbatim from
   C22 (cacheStaged/cacheFFI - identical control-block layout: presented arena
   @+64, configured arena @+2112, pad scalar @+16, result @+24).  Surgery RAISES
   if a hand core is not a genuine parser subterm (leanc out of the TCB).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory hashBytesLoopTheory cacheKeyCoreTheory basicCoreTheory;
open basicLinkBInstTheory;

val _ = new_theory "basicData";

val funcs_body = (REWRITE_CONV [basicProg_def] THENC EVAL)
                   “functions basicProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val body64      = inst64 body_tm;

val cl1u = (REWRITE_CONV [cacheLoop1_def, foldGuard_def, cacheBodyA1_def] “cacheLoop1”)
             |> concl |> rhs |> inst64;
val cl2u = (REWRITE_CONV [cacheLoop2_def, foldGuard_def, cacheBodyA2_def] “cacheLoop2”)
             |> concl |> rhs |> inst64;
val cgu  = (REWRITE_CONV [basicGate_def] “basicGate”) |> concl |> rhs |> inst64;
val cl1  = inst64 “cacheLoop1”;
val cl2  = inst64 “cacheLoop2”;
val cg   = inst64 “basicGate”;

val body1 = Term.subst [cl1u |-> cl1] body64;
val body2 = Term.subst [cl2u |-> cl2] body1;
val body3 = Term.subst [cgu  |-> cg ] body2;

val basicMainBody_def =
  new_definition("basicMainBody_def", “basicMainBody = ^body3”);

val _ = if Term.free_in cl1 body3 then () else raise Fail "cacheLoop1 surgery did not fire";
val _ = if Term.free_in cl2 body3 then () else raise Fail "cacheLoop2 surgery did not fire";
val _ = if Term.free_in cg  body3 then () else raise Fail "basicGate surgery did not fire";

val _ = export_theory ();

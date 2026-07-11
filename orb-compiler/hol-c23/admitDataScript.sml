(* ===========================================================================
   C23 — the SECOND stage's fold-data: admitMainBody = «main» of admitProg with
   the two While loops folded to cacheLoop1/cacheLoop2 (REUSED from C22) and the
   gate to admitGate.  The staging + FFI contract are REUSED verbatim from C22
   (cacheStaged/cacheFFI — identical control-block layout).  Surgery RAISES if a
   hand core is not a genuine parser subterm (leanc out of the TCB).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory rich_listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory pairTheory;
open foldLoopSchemaTheory hashBytesLoopTheory cacheKeyCoreTheory admitCoreTheory;
open admitLinkBInstTheory;

val _ = new_theory "admitData";

val funcs_body = (REWRITE_CONV [admitProg_def] THENC EVAL)
                   “functions admitProg” |> concl |> rhs;
val main_triple = funcs_body |> listSyntax.dest_list |> #1 |> hd;
val body_tm     = main_triple |> pairSyntax.strip_pair |> (fn xs => List.nth (xs, 2));
fun inst64 t = Term.inst [Type.alpha |-> “:64”] t;
val body64      = inst64 body_tm;

val cl1u = (REWRITE_CONV [cacheLoop1_def, foldGuard_def, cacheBodyA1_def] “cacheLoop1”)
             |> concl |> rhs |> inst64;
val cl2u = (REWRITE_CONV [cacheLoop2_def, foldGuard_def, cacheBodyA2_def] “cacheLoop2”)
             |> concl |> rhs |> inst64;
val agu  = (REWRITE_CONV [admitGate_def] “admitGate”) |> concl |> rhs |> inst64;
val cl1  = inst64 “cacheLoop1”;
val cl2  = inst64 “cacheLoop2”;
val ag   = inst64 “admitGate”;

val body1 = Term.subst [cl1u |-> cl1] body64;
val body2 = Term.subst [cl2u |-> cl2] body1;
val body3 = Term.subst [agu  |-> ag ] body2;

val admitMainBody_def =
  new_definition("admitMainBody_def", “admitMainBody = ^body3”);

val _ = if Term.free_in cl1 body3 then () else raise Fail "cacheLoop1 surgery did not fire";
val _ = if Term.free_in cl2 body3 then () else raise Fail "cacheLoop2 surgery did not fire";
val _ = if Term.free_in ag  body3 then () else raise Fail "admitGate surgery did not fire";

val _ = export_theory ();

(* ===========================================================================
   RUNG 2 (hol-c33): FRONT stages of compile_prog_max for tinyProg discharged to
   CONCRETE terms by EVAL with reg_alg := 0 (Simple allocator).  pan_to_word +
   word_to_word + word_to_stack + max_depth are EVAL-tractable (sub-second);
   the ENCODER (from_stack) is the EVAL wall and is done via cv_compute in the
   companion theory tinyConcrete.  tinyProg is defined MONOMORPHIC at :64 so all
   word-width type variables are pinned (dimindex(:64) reduces -> concrete).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open panPtreeConversionTheory panLangTheory;
open backendTheory word_to_wordTheory word_to_stackTheory pan_to_wordTheory
     x64_configTheory pan_to_targetProofTheory;

val _ = new_theory "tinyFront";
val _ = Globals.max_print_depth := 0;

(* --- parse tiny.pnk with the verified parser; bind tinyProg MONOMORPHIC :64 --- *)
val src = let val is = TextIO.openIn "tiny.pnk"
              val s = TextIO.inputAll is val _ = TextIO.closeIn is in s end;
val srcTm = stringSyntax.fromMLstring src;
val parse_thm = EVAL (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE srcTm]);
val prog_tm0 = rand (rhs (concl parse_thm));
val prog_tm  = inst [alpha |-> ``:64``] prog_tm0;   (* pin the word width to 64 *)
val tinyProg_def = new_definition("tinyProg_def",
                     mk_eq(mk_var("tinyProg", type_of prog_tm), prog_tm));
val _ = computeLib.add_funs [tinyProg_def];

Theorem tinyProg_is_parser_output:
  parse_topdecs_to_ast ^srcTm = INL tinyProg
Proof
  REWRITE_TAC [tinyProg_def] THEN
  MATCH_ACCEPT_TAC (INST_TYPE [alpha |-> ``:64``] parse_thm)
QED

(* --- config: x64 backend config with the Simple allocator (reg_alg 0) --- *)
Definition tinyC_def:
  tinyC = x64_backend_config with
            word_to_word_conf :=
              (x64_backend_config.word_to_word_conf with reg_alg := 0)
End

fun defineFrom name tm =
  new_definition(name ^ "_def", mk_eq(mk_var(name, type_of tm), tm));

(* L1: pan_to_word (types pinned by tinyProg:64) *)
val L1raw = EVAL ``pan_to_word$compile_prog x64_config.ISA tinyProg``;
val pw_tm = rhs (concl L1raw);
val TINY_PW_def = defineFrom "TINY_PW" pw_tm;
val _ = computeLib.add_funs [TINY_PW_def];
val L1 = save_thm("L1",
  L1raw |> CONV_RULE (RHS_CONV (REWR_CONV (SYM TINY_PW_def))));

(* L2: word_to_word with reg_alg 0 *)
val L2raw = EVAL ``word_to_word$compile tinyC.word_to_word_conf x64_config TINY_PW``;
val (col_tm, wprog_tm) = pairSyntax.dest_pair (rhs (concl L2raw));
val tiny_wprog_def = defineFrom "tiny_wprog" wprog_tm;
val _ = computeLib.add_funs [tiny_wprog_def];
val L2 = save_thm("L2",
  L2raw |> CONV_RULE (RHS_CONV (REWRITE_CONV [SYM tiny_wprog_def])));

(* L3: word_to_stack.  Extract components via FST/SND projections (robust to
   tuple nesting), leaving the unused fs component literal. *)
val L3raw = EVAL ``word_to_stack$compile x64_config F tiny_wprog``;
val tiny_bm_def = defineFrom "tiny_bm"
  (rhs (concl (EVAL ``FST (word_to_stack$compile x64_config F tiny_wprog)``)));
val tiny_cprime_def = defineFrom "tiny_cprime"
  (rhs (concl (EVAL ``FST (SND (word_to_stack$compile x64_config F tiny_wprog))``)));
val tiny_stackprog_def = defineFrom "tiny_stackprog"
  (rhs (concl (EVAL ``SND (SND (SND (word_to_stack$compile x64_config F tiny_wprog)))``)));
val _ = computeLib.add_funs [tiny_cprime_def];
val L3 = save_thm("L3",
  L3raw |> CONV_RULE (RHS_CONV (REWRITE_CONV
             [SYM tiny_bm_def, SYM tiny_cprime_def, SYM tiny_stackprog_def])));

(* L4: max_depth (stack_max) *)
val L4raw = EVAL ``max_depth tiny_cprime.stack_frame_size
                    (full_call_graph InitGlobals_location (fromAList tiny_wprog))``;
val max_tm = rhs (concl L4raw);
val tiny_stackmax_def = defineFrom "tiny_stackmax" max_tm;
val L4 = save_thm("L4",
  L4raw |> CONV_RULE (RHS_CONV (REWR_CONV (SYM tiny_stackmax_def))));

(* --- assemble: compile_prog_max front reduced, from_stack left symbolic --- *)
Theorem tiny_frontprog_eq:
  mc.target.config = x64_config ==>
  compile_prog_max tinyC mc tinyProg =
    (from_stack x64_config tinyC LN tiny_stackprog tiny_bm, tiny_stackmax)
Proof
  strip_tac >>
  rewrite_tac [compile_prog_max_def] >>
  first_assum (fn th => rewrite_tac [th]) >>
  simp [L1, L2, L3, L4]
QED

val _ = export_theory ();

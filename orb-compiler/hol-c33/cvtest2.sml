val _ = load "backend_x64_cvTheory";
val _ = load "backend_x64Theory";
val _ = load "panPtreeConversionTheory";
val _ = load "pan_to_wordTheory";
val _ = load "word_to_wordTheory";
val _ = load "word_to_stackTheory";
val _ = load "backendTheory";
val _ = load "x64_configTheory";
val _ = load "cv_transLib";
open HolKernel boolLib bossLib Parse;
open panPtreeConversionTheory panLangTheory;
val _ = Globals.max_print_depth := 6;
fun say s = (print s; TextIO.flushOut TextIO.stdOut);
say "=== loaded ===\n";
val src = let val is = TextIO.openIn "tiny.pnk"
              val s = TextIO.inputAll is val _ = TextIO.closeIn is in s end;
val srcTm = stringSyntax.fromMLstring src;
val prog_tm = inst [alpha |-> ``:64``] (rand (rhs (concl (EVAL (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE srcTm])))));
val tinyProg_def = new_definition("tinyProg_def", mk_eq(mk_var("tinyProg", type_of prog_tm), prog_tm));
val _ = computeLib.add_funs [tinyProg_def];

Definition tinyC_def:
  tinyC = x64_backend_config with
            word_to_word_conf := (x64_backend_config.word_to_word_conf with reg_alg := 0)
End
val pw_tm = rhs (concl (EVAL ``pan_to_word$compile_prog x64_config.ISA tinyProg``));
val TINY_PW_def = new_definition("TINY_PW_def", mk_eq(mk_var("TINY_PW", type_of pw_tm), pw_tm));
val _ = computeLib.add_funs [TINY_PW_def];
val wprog_tm = snd (pairSyntax.dest_pair (rhs (concl
  (EVAL ``word_to_word$compile (x64_backend_config.word_to_word_conf with reg_alg := 0) x64_config TINY_PW``))));
val tiny_wprog_def = new_definition("tiny_wprog_def", mk_eq(mk_var("tiny_wprog", type_of wprog_tm), wprog_tm));
val _ = computeLib.add_funs [tiny_wprog_def];
val p_tm  = rhs (concl (EVAL ``SND (SND (SND (word_to_stack$compile x64_config F tiny_wprog)))``));
val bm_tm = rhs (concl (EVAL ``FST (word_to_stack$compile x64_config F tiny_wprog)``));
val tiny_stackprog_def = new_definition("tiny_stackprog_def", mk_eq(mk_var("tiny_stackprog", type_of p_tm), p_tm));
val tiny_bm_def = new_definition("tiny_bm_def", mk_eq(mk_var("tiny_bm", type_of bm_tm), bm_tm));
say "=== defs done; cv_trans the data + config ===\n";

fun tryit name f = (f (); say (name ^ ": OK\n")) handle e => say (name ^ ": EXN " ^ General.exnMessage e ^ "\n");
val _ = tryit "cv_trans tinyC"          (fn () => ignore (cv_transLib.cv_trans tinyC_def));
val _ = tryit "cv_trans_deep stackprog" (fn () => ignore (cv_transLib.cv_trans_deep_embedding EVAL tiny_stackprog_def));
val _ = tryit "cv_trans_deep bm"        (fn () => ignore (cv_transLib.cv_trans_deep_embedding EVAL tiny_bm_def));
say "=== cv_eval bytes ===\n";
val t0 = Time.now();
val bytes_th = cv_transLib.cv_eval ``FST (THE (from_stack_x64 tinyC LN tiny_stackprog tiny_bm))``
   handle e => (say ("CVEXN: " ^ General.exnMessage e ^ "\n"); TRUTH);
say ("cv_eval bytes DONE: " ^ Time.toString(Time.-(Time.now(),t0)) ^ "\n");
val r = rhs (concl bytes_th);
val nbytes = (length (fst (listSyntax.dest_list r))) handle _ => ~1;
say ("byte list length = " ^ Int.toString nbytes ^ " termsize=" ^ Int.toString (term_size r) ^ "\n");
val _ = if nbytes > 0 then
  let val (els,_) = listSyntax.dest_list r
      val nums = map (fn t => numSyntax.int_of_term (rand t) handle _ => ~1) els
      val f8 = List.take(nums, Int.min(8,nbytes))
      val l8 = List.drop(nums, Int.max(0,nbytes-8))
  in say ("first8=" ^ String.concatWith "," (map Int.toString f8) ^ "  last8=" ^
          String.concatWith "," (map Int.toString l8) ^ "  sum=" ^ Int.toString (foldl op+ 0 nums) ^ "\n") end
  else ();
say "=== CVTEST2 DONE ===\n";

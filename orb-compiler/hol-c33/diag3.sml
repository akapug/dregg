val _ = load "stringLib";
val _ = load "panPtreeConversionTheory";
val _ = load "x64_configTheory";
val _ = load "x64_targetTheory";
val _ = load "pan_to_targetProofTheory";
open HolKernel boolLib bossLib Parse;
open panPtreeConversionTheory panLangTheory;
val _ = Globals.max_print_depth := 0;
fun say s = (print s; TextIO.flushOut TextIO.stdOut);
val _ = say "=== loaded ===\n";
val src = let val is = TextIO.openIn "tiny.pnk" val s = TextIO.inputAll is val _ = TextIO.closeIn is in s end;
val srcTm = stringSyntax.fromMLstring src;
val parse_thm = EVAL (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE srcTm]);
val prog_tm = rand (rhs (concl parse_thm));
val tinyProg_def = new_definition("tinyProg_def", mk_eq(mk_var("tinyProg", type_of prog_tm), prog_tm));
val _ = computeLib.add_funs [tinyProg_def];
val _ = say "-- EVAL word_to_word (single let-term, reg_alg 0) --\n";
val t0 = Time.now();
val thww = EVAL ``
   let asm_conf = x64_config in
   let wprog0 = pan_to_word$compile_prog asm_conf.ISA tinyProg in
     word_to_word$compile (x64_backend_config.word_to_word_conf with reg_alg := 0) asm_conf wprog0 ``;
val _ = say ("word_to_word DONE: " ^ Time.toString(Time.-(Time.now(),t0)) ^
             " termsize=" ^ Int.toString(term_size(rhs(concl thww))) ^ "\n");
val _ = say "=== DIAG3 DONE ===\n";

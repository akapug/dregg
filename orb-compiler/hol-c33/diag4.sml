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
fun timeEVAL name tm =
  let val t0 = Time.now()
      val th = EVAL tm
      val _ = say (name ^ ": " ^ Time.toString(Time.-(Time.now(),t0)) ^
                   " termsize=" ^ Int.toString(term_size(rhs(concl th))) ^ "\n")
  in th end;
val _ = say "-- through word_to_stack --\n";
val _ = timeEVAL "word_to_stack" ``
   let asm_conf = x64_config in
   let c = x64_backend_config with word_to_word_conf := (x64_backend_config.word_to_word_conf with reg_alg := 0) in
   let prog = pan_to_word$compile_prog asm_conf.ISA tinyProg in
   let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in
     word_to_stack$compile asm_conf F wprog ``;
val _ = say "-- full from_stack (compile_prog_max body) --\n";
val thfull = timeEVAL "from_stack_FULL" ``
   let asm_conf = x64_config in
   let c = x64_backend_config with word_to_word_conf := (x64_backend_config.word_to_word_conf with reg_alg := 0) in
   let prog = pan_to_word$compile_prog asm_conf.ISA tinyProg in
   let (col,wprog) = word_to_word$compile c.word_to_word_conf asm_conf prog in
   let (bm,c',fs,p) = word_to_stack$compile asm_conf F wprog in
     from_stack asm_conf c LN p bm ``;
val _ = say "=== DIAG4 DONE ===\n";

(* ============================================================
   RUNG 2 FINALE — assemble compile_prog_max tinyProg = SOME(concrete bytes)
   Generic front by EVAL (reg_alg 0 Simple, reg_alloc_aux discharged);
   encoder by cv_eval over from_stack_x64 + re-derived _x64->generic bridge.
   ============================================================ *)
val _ = load "wordsLib"; val _ = load "backend_x64Theory"; val _ = load "backend_x64_cvTheory";
val _ = load "cv_transLib"; val _ = load "cv_typeTheory"; val _ = load "reg_allocComputeLib";
val _ = load "stringLib"; val _ = load "panPtreeConversionTheory"; val _ = load "pan_to_wordTheory";
val _ = load "word_to_wordTheory"; val _ = load "word_to_stackTheory"; val _ = load "backendTheory";
val _ = load "backend_asmTheory"; val _ = load "x64_targetTheory"; val _ = load "x64_configTheory";
val _ = load "asmTheory"; val _ = load "lab_to_targetTheory"; val _ = load "pan_to_targetProofTheory";
open HolKernel boolLib bossLib Parse;
open panPtreeConversionTheory panLangTheory;
fun say s = (print s; TextIO.flushOut TextIO.stdOut);
val _ = Globals.max_print_depth := 6;
val rconc = rhs o concl;
fun defineFrom name tm = new_definition(name ^ "_def", mk_eq(mk_var(name, type_of tm), tm));

(* ---------- FRONT (all generic, EVAL) ---------- *)
val src = let val is=TextIO.openIn "tiny.pnk" val s=TextIO.inputAll is val _=TextIO.closeIn is in s end;
val prog_tm = inst [alpha |-> ``:64``] (rand (rconc (EVAL (Term [QUOTE "parse_topdecs_to_ast ", ANTIQUOTE (stringSyntax.fromMLstring src)]))));
val tinyProg_def = defineFrom "tinyProg" prog_tm;
val _ = computeLib.add_funs [tinyProg_def];
val _ = new_definition("tinyC_def",
  ``tinyC = x64_backend_config with word_to_word_conf :=
             (x64_backend_config.word_to_word_conf with reg_alg := 0)``);
val tinyC_def = definition "tinyC_def";
val _ = computeLib.add_funs [tinyC_def];

(* L1 pan_to_word *)
val L1raw = EVAL ``pan_to_word$compile_prog x64_config.ISA tinyProg``;
val TINY_PW_def = defineFrom "TINY_PW" (rconc L1raw);
val _ = computeLib.add_funs [TINY_PW_def];
val L1 = L1raw |> CONV_RULE (RHS_CONV (REWR_CONV (SYM TINY_PW_def)));

(* L2 word_to_word reg_alg 0 (generic; reg_alloc_aux discharged) *)
val L2raw = EVAL ``word_to_word$compile tinyC.word_to_word_conf x64_config TINY_PW``;
val hasRAA2 = can (find_term (fn t => (fst(dest_const t)="reg_alloc_aux") handle _ => false)) (rconc L2raw);
val _ = say ("L2 reg_alloc_aux present = " ^ Bool.toString hasRAA2 ^ "\n");
val (col_tm, wprog_tm) = pairSyntax.dest_pair (rconc L2raw);
val tiny_wprog_def = defineFrom "tiny_wprog" wprog_tm;
val _ = computeLib.add_funs [tiny_wprog_def];
val L2 = L2raw |> CONV_RULE (RHS_CONV (REWRITE_CONV [SYM tiny_wprog_def]));

(* L3 word_to_stack *)
val L3raw = EVAL ``word_to_stack$compile x64_config F tiny_wprog``;
val tiny_bm_def = defineFrom "tiny_bm" (rconc (EVAL ``FST (word_to_stack$compile x64_config F tiny_wprog)``));
val tiny_cprime_def = defineFrom "tiny_cprime" (rconc (EVAL ``FST (SND (word_to_stack$compile x64_config F tiny_wprog))``));
val tiny_stackprog_def = defineFrom "tiny_stackprog" (rconc (EVAL ``SND (SND (SND (word_to_stack$compile x64_config F tiny_wprog)))``));
val _ = computeLib.add_funs [tiny_cprime_def];
val L3 = L3raw |> CONV_RULE (RHS_CONV (REWRITE_CONV [SYM tiny_bm_def, SYM tiny_cprime_def, SYM tiny_stackprog_def]));

(* L4 max_depth *)
val L4raw = EVAL ``max_depth tiny_cprime.stack_frame_size (full_call_graph InitGlobals_location (fromAList tiny_wprog))``;
val tiny_stackmax_def = defineFrom "tiny_stackmax" (rconc L4raw);
val L4 = L4raw |> CONV_RULE (RHS_CONV (REWR_CONV (SYM tiny_stackmax_def)));

val tiny_frontprog_eq = prove(
  ``mc.target.config = x64_config ==>
    compile_prog_max tinyC mc tinyProg =
      (from_stack x64_config tinyC LN tiny_stackprog tiny_bm, tiny_stackmax)``,
  strip_tac >>
  rewrite_tac [pan_to_targetProofTheory.compile_prog_max_def] >>
  first_assum (fn th => rewrite_tac [th]) >>
  simp [L1, L2, L3, L4]);
val _ = say "=== FRONT DONE (tiny_frontprog_eq proven) ===\n";

(* ---------- ENCODER BRIDGE CHAIN (_x64 -> generic backend_asm) ---------- *)
val asm_conf = ``x64_config``;
val cfgdef = x64_targetTheory.x64_config_def;
val lemma = TypeBase.accessors_of (type_of asm_conf)
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
    |> map (fn tm => mk_icomb(tm,asm_conf))
    |> map (fn tm => SIMP_CONV (srw_ss()) [cfgdef] tm) |> LIST_CONJ;
structure bx = backend_x64Theory; structure ba = backend_asmTheory;
val membridges = ref ([]: thm list);
fun mk_bridge nm (gth, xdef) = let
    val th1 = gth |> DefnBase.one_line_ify NONE |> SPEC_ALL
    val (c,args) = th1 |> concl |> dest_eq |> fst |> strip_comb
    val tm = first (fn t => can (match_term t) asm_conf) args
    val (i,s) = match_term tm asm_conf
    val th2 = INST i (INST_TYPE s th1)
    val red = th2 |> REWRITE_RULE (!membridges)
                  |> SIMP_RULE (srw_ss()) [lemma, combinTheory.o_DEF]
                  |> REWRITE_RULE (!membridges)
    val x64th = xdef |> SPEC_ALL
  in if aconv (rhs (concl red)) (rhs (concl x64th)) then let
       val bridge = TRANS red (SYM x64th)
       val bargs = snd (strip_comb (rhs (concl bridge)))
       val curried = bridge |> GENL bargs |> REWRITE_RULE [GSYM FUN_EQ_THM]
       val _ = membridges := (curried :: !membridges)
     in curried end
     else (say ("MISMATCH " ^ nm ^ "\n"); TRUTH)
  end handle e => (say ("FAIL " ^ nm ^ " : " ^ General.exnMessage e ^ "\n"); TRUTH);
val _ = mk_bridge "enc_line" (ba.enc_line_def, bx.enc_line_x64_def);
val _ = mk_bridge "enc_sec" (ba.enc_sec_def, bx.enc_sec_x64_def);
val _ = mk_bridge "enc_sec_list" (ba.enc_sec_list_def, bx.enc_sec_list_x64_def);
val b_ela = prove(
  ``!xs labs ffis pos acc ok. enc_lines_again labs ffis pos x64_config xs (acc,ok) =
      enc_lines_again_x64 labs ffis pos xs (acc,ok)``,
  Induct_on `xs` >> TRY (Cases_on `h`) >> rpt gen_tac >>
  ONCE_REWRITE_TAC[bx.enc_lines_again_x64_def] >> gvs[ba.enc_lines_again_def, lemma]);
val _ = membridges := (b_ela :: !membridges);
val b_esa = prove(
  ``!xs pos labs ffis. enc_secs_again pos labs ffis x64_config xs = enc_secs_again_x64 pos labs ffis xs``,
  Induct_on `xs` >> TRY (Cases_on `h`) >> rpt gen_tac >>
  ONCE_REWRITE_TAC[bx.enc_secs_again_x64_def] >> gvs[ba.enc_secs_again_def, b_ela, lemma] >>
  rpt (pairarg_tac >> gvs[b_ela, lemma]));
val _ = membridges := (b_esa :: !membridges);
val _ = mk_bridge "reg_ok" (asmTheory.reg_ok_def, bx.reg_ok_x64_def);
val _ = mk_bridge "fp_reg_ok" (asmTheory.fp_reg_ok_def, bx.fp_reg_ok_x64_def);
val _ = mk_bridge "fp_ok" (asmTheory.fp_ok_def, bx.fp_ok_x64_def);
val _ = mk_bridge "reg_imm_ok" (asmTheory.reg_imm_ok_def, bx.reg_imm_ok_x64_def);
val _ = mk_bridge "arith_ok" (asmTheory.arith_ok_def, bx.arith_ok_x64_def);
val _ = mk_bridge "inst_ok" (asmTheory.inst_ok_def, bx.inst_ok_x64_def);
val _ = mk_bridge "cmp_ok" (asmTheory.cmp_ok_def, bx.cmp_ok_x64_def);
val _ = mk_bridge "asm_ok" (asmTheory.asm_ok_def, bx.asm_ok_x64_def);
val _ = mk_bridge "line_ok_light" (lab_to_targetTheory.line_ok_light_def, bx.line_ok_light_x64_def);
val _ = mk_bridge "sec_ok_light" (lab_to_targetTheory.sec_ok_light_def, bx.sec_ok_light_x64_def);
val b_rll = prove(
  ``!clock pos init_labs ffis sec_list. remove_labels_loop clock x64_config pos init_labs ffis sec_list =
      remove_labels_loop_x64 clock pos init_labs ffis sec_list``,
  Induct_on `clock` >> rpt gen_tac >>
  ONCE_REWRITE_TAC[ba.remove_labels_loop_def] >> ONCE_REWRITE_TAC[bx.remove_labels_loop_x64_def] >>
  gvs ([lemma, b_esa] @ !membridges) >> rpt (pairarg_tac >> gvs ([lemma, b_esa] @ !membridges)));
val _ = membridges := (b_rll :: !membridges);
val _ = mk_bridge "remove_labels" (ba.remove_labels_def, bx.remove_labels_x64_def);
val _ = mk_bridge "compile_lab" (ba.compile_lab_def, bx.compile_lab_x64_def);
val _ = mk_bridge "lab_to_target" (ba.lab_to_target_def, bx.lab_to_target_x64_def);
val _ = mk_bridge "from_lab" (ba.from_lab_def, bx.from_lab_x64_def);
val b_fs = mk_bridge "from_stack" (ba.from_stack_def, bx.from_stack_x64_def);
val _ = say ("=== ENCODER BRIDGE DONE: " ^ thm_to_string b_fs ^ " ===\n");

(* ---------- from_stack_thm / from_lab_thm re-derived (backend_asm -> backend) ---------- *)
val from_lab_thm = prove(
  ``from_lab asm_conf c names p bm =
      SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ==>
    ?c1. backend$from_lab asm_conf c names p bm = SOME (bytes,bm1,c1) /\
         LENGTH bytes = bytes_len /\ LENGTH bm1 = bm1_len``,
  gvs [ba.from_lab_def, backendTheory.from_lab_def]
  \\ gvs [ba.attach_bitmaps_def |> DefnBase.one_line_ify NONE, AllCaseEqs()] \\ rw []
  \\ gvs [ba.compile_lab_def, ba.lab_to_target_def,
          lab_to_targetTheory.compile_def, lab_to_targetTheory.compile_lab_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ pop_assum kall_tac \\ gvs [AllCaseEqs()]
  \\ rpt (pairarg_tac \\ gvs []) \\ gvs [backendTheory.attach_bitmaps_def]);
val from_stack_thm = prove(
  ``from_stack asm_conf c names p bm =
      SOME (bytes,bytes_len,bm1,bm1_len,ffi_names,shmem_len,syms,conf_str) ==>
    ?c1. backend$from_stack asm_conf c names p bm = SOME (bytes,bm1,c1) /\
         LENGTH bytes = bytes_len /\ LENGTH bm1 = bm1_len``,
  gvs [ba.from_stack_def, backendTheory.from_stack_def] \\ rw []
  \\ drule from_lab_thm \\ strip_tac \\ gvs []);
val _ = say "=== from_stack_thm re-derived ===\n";

(* ---------- ENCODER via cv_eval (from_stack_x64 over Simple stackprog) ---------- *)
val tinyC_eq = EVAL ``tinyC``;                    (* tinyC = <concrete config> *)
val tinyC_val = rconc tinyC_eq;
val _ = cv_transLib.cv_trans_deep_embedding EVAL tiny_stackprog_def;
val _ = cv_transLib.cv_trans_deep_embedding EVAL tiny_bm_def;
val enc_input = ``from_stack_x64 ^tinyC_val LN tiny_stackprog tiny_bm``;
val enc = cv_transLib.cv_eval_raw enc_input;
val enc_hol0 = CONV_RULE (RAND_CONV EVAL) enc;   (* from_stack_x64 <val> LN ... = SOME(...) *)
val enc_hol = REWRITE_RULE [SYM tinyC_eq] enc_hol0;  (* rewrite <val> -> tinyC constant *)
val enc_hr = rconc enc_hol;
val is_some = optionSyntax.is_some enc_hr;
val _ = say ("encoder result is SOME: " ^ Bool.toString is_some ^ "\n");
val payload = optionSyntax.dest_some enc_hr;
val comps = pairSyntax.strip_pair payload;   (* [bytes, bytes_len, bm1, bm1_len, ffi, shmem, syms, conf] *)
val bytes_tm = List.nth (comps, 0);
val bm1_tm   = List.nth (comps, 2);
val (byte_els,_) = listSyntax.dest_list bytes_tm;
val nbytes = length byte_els;
fun byteval t = numSyntax.int_of_term (rand t) handle _ => (numSyntax.int_of_term t handle _ => ~1);
val nums = map byteval byte_els;
val allconc = List.all (fn n => n>=0 andalso n<256) nums;
val _ = say ("BYTE COUNT = " ^ Int.toString nbytes ^ "  all_concrete_0_255 = " ^ Bool.toString allconc ^ "\n");
val f8 = List.take(nums, Int.min(8,nbytes));
val l8 = List.drop(nums, Int.max(0,nbytes-8));
val _ = say ("first8 = [" ^ String.concatWith "," (map Int.toString f8) ^ "]\n");
val _ = say ("last8  = [" ^ String.concatWith "," (map Int.toString l8) ^ "]\n");
val fh = TextIO.openOut "tiny_bytes_simple.hex";
val _ = TextIO.output(fh, String.concatWith " " (map (fn n => StringCvt.padLeft #"0" 2 (Int.fmt StringCvt.HEX n)) nums));
val _ = TextIO.closeOut fh;
val _ = say "wrote tiny_bytes_simple.hex\n";

(* ---------- COMPOSE ---------- *)
val enc_asm = REWRITE_RULE [GSYM b_fs] enc_hol;   (* from_stack x64_config tinyC LN tiny_stackprog tiny_bm = SOME(...) *)
val bk_from_stack = MATCH_MP from_stack_thm enc_asm;   (* ?c1. backend$from_stack x64_config tinyC LN tiny_stackprog tiny_bm = SOME(bytes,bm1,c1) /\ ... *)
val _ = say ("bk_from_stack: " ^ thm_to_string bk_from_stack ^ "\n");

val tiny_compile_prog_max_concrete = prove(
  ``mc.target.config = x64_config ==>
    ?c1. compile_prog_max tinyC mc tinyProg =
           (SOME (^bytes_tm, ^bm1_tm, c1), tiny_stackmax)``,
  strip_tac >>
  imp_res_tac tiny_frontprog_eq >>
  strip_assume_tac bk_from_stack >>
  qexists_tac `c1` >>
  asm_rewrite_tac[] );
val _ = say "\n===== MILESTONE THEOREM (byte list shown as head..tail) =====\n";
val _ = Globals.max_print_depth := 100;
(* structural print: replace the 1868-byte list literal with a marker for readability *)
val ms_concl = concl tiny_compile_prog_max_concrete;
val _ = say ("LHS/structure: mc.target.config = x64_config ==> ?c1. compile_prog_max tinyC mc tinyProg = (SOME(<BYTES>, <bm1 len=" ^ Int.toString (length (fst (listSyntax.dest_list bm1_tm))) ^ ">, c1), tiny_stackmax)\n");
val _ = say ("BYTES: length=" ^ Int.toString nbytes ^ " head6=[" ^ String.concatWith "," (map Int.toString (List.take(nums,6))) ^ "] tail6=[" ^ String.concatWith "," (map Int.toString (List.drop(nums, nbytes-6))) ^ "]\n");
val allnum = List.all (fn t => numSyntax.is_numeral (rand t) handle _ => numSyntax.is_numeral t) byte_els;
val _ = say ("every byte element is a concrete numeral (n2w N): " ^ Bool.toString allnum ^ "\n");
val hasRAA = can (find_term (fn t => (fst(dest_const t)="reg_alloc_aux") handle _ => false)) (concl tiny_compile_prog_max_concrete);
val (ors,axs) = Tag.dest_tag (Thm.tag tiny_compile_prog_max_concrete);
val nhyp = length (hyp tiny_compile_prog_max_concrete);
val _ = say ("MILESTONE oracles=[" ^ String.concatWith "," ors ^ "] axioms=[" ^ String.concatWith "," axs ^
             "] hyps=" ^ Int.toString nhyp ^ " reg_alloc_aux=" ^ (if hasRAA then "TRUE-BAD" else "FALSE-GOOD") ^
             " bytes=" ^ Int.toString nbytes ^ " concrete=" ^ Bool.toString allconc ^ "\n");
(* ---------- machine_sem over CONCRETE bytes, compile hyp discharged ---------- *)
val pts = pan_to_targetProofTheory.pan_to_target_compile_semantics |> INST_TYPE [alpha |-> ``:64``];
val pts_i = pts |> Q.INST [`c` |-> `tinyC`, `pan_code` |-> `tinyProg`,
                           `bytes` |-> [ANTIQUOTE bytes_tm], `bitmaps` |-> [ANTIQUOTE bm1_tm],
                           `stack_max` |-> `tiny_stackmax`];
val (ante, cncl) = dest_imp (concl pts_i);
val conjs = boolSyntax.strip_conj ante;
fun is_compile c = (same_const (fst (strip_comb (lhs c))) ``compile_prog_max``) handle _ => false;
val compile_conj = valOf (List.find is_compile conjs);
val rest = filter (not o is_compile) conjs;
val cprime = List.last (pairSyntax.strip_pair (optionSyntax.dest_some (fst (pairSyntax.dest_pair (rhs compile_conj)))));
val _ = say ("cprime var = " ^ term_to_string cprime ^ "\n");
val rest_tm = list_mk_conj rest;
val bco = valOf (List.find (fn c => (fst (dest_const (fst (strip_comb c))) = "backend_config_ok") handle _ => false) conjs);
val mtc_tm = hd (snd (strip_comb bco));   (* mc.target.config, with pts_i's exact mc type *)
val hyp_tm = mk_eq(mtc_tm, ``x64_config``);
val ms_goal = mk_imp(hyp_tm, mk_exists(cprime, mk_imp(rest_tm, cncl)));
val tiny_bytes_machine_code_concrete = prove(ms_goal,
  strip_tac >>
  first_assum (strip_assume_tac o MATCH_MP tiny_compile_prog_max_concrete) >>
  qexists_tac `c1` >> disch_then strip_assume_tac >>
  first_assum (fn th =>
     let val c1t = List.last (pairSyntax.strip_pair
                     (optionSyntax.dest_some (fst (pairSyntax.dest_pair (rhs (concl th))))))
     in mp_tac (INST [cprime |-> c1t] pts_i) end) >>
  asm_rewrite_tac[]);
val _ = say "\n===== machine_sem CONCRETE THEOREM =====\n";
val ms2 = concl tiny_bytes_machine_code_concrete;
val (ms2_hyp, ms2_body) = dest_imp ms2;
val (ms2_c1, ms2_imp) = dest_exists ms2_body;
val (ms2_ante, ms2_concl) = dest_imp ms2_imp;
val n_surv = length (boolSyntax.strip_conj ms2_ante);
val _ = say ("structure: (" ^ term_to_string ms2_hyp ^ ") ==> ?c'. (<" ^ Int.toString n_surv ^ " surviving runtime antecedents incl pan_installed over concrete bytes>) ==> CONCL\n");
val _ = Globals.max_print_depth := 40;
val _ = say ("CONCL: " ^ term_to_string ms2_concl ^ "\n");
val hasPI = can (find_term (fn t => (fst(dest_const t)="pan_installed") handle _ => false)) ms2_ante;
val _ = say ("pan_installed present in surviving antecedents: " ^ Bool.toString hasPI ^ "\n");
val (mors,maxs) = Tag.dest_tag (Thm.tag tiny_bytes_machine_code_concrete);
val mnhyp = length (hyp tiny_bytes_machine_code_concrete);
val hasMS = can (find_term (fn t => (fst(dest_const t)="machine_sem") handle _ => false)) (concl tiny_bytes_machine_code_concrete);
val hasCPM = can (find_term (fn t => (fst(dest_const t)="compile_prog_max") handle _ => false)) (concl tiny_bytes_machine_code_concrete);
val _ = say ("MACHINE_SEM oracles=[" ^ String.concatWith "," mors ^ "] axioms=[" ^ String.concatWith "," maxs ^
             "] hyps=" ^ Int.toString mnhyp ^ " has_machine_sem=" ^ Bool.toString hasMS ^
             " compile_prog_max_still_present=" ^ Bool.toString hasCPM ^ "\n");

val _ = say "=== ASSEMBLE DONE ===\n";
val _ = OS.Process.exit OS.Process.success;

val _ = load "backend_x64Theory"; val _ = load "backend_asmTheory";
val _ = load "x64_targetTheory"; val _ = load "lab_to_targetTheory";
val _ = load "asmTheory"; val _ = load "wordsLib";
open HolKernel boolLib bossLib Parse;
fun say s = (print s; TextIO.flushOut TextIO.stdOut);
val asm_conf = ``x64_config``;
val cfgdef = x64_targetTheory.x64_config_def;
val lemma = TypeBase.accessors_of (type_of asm_conf)
    |> map (rator o fst o dest_eq o concl o SPEC_ALL)
    |> map (fn tm => mk_icomb(tm,asm_conf))
    |> map (fn tm => SIMP_CONV (srw_ss()) [cfgdef] tm) |> LIST_CONJ;
say "=== lemma built ===\n";
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
       val _ = say ("OK   " ^ nm ^ "\n")
     in curried end
     else (say ("MISMATCH " ^ nm ^ "\n"); TRUTH)
  end handle e => (say ("FAIL " ^ nm ^ " : " ^ General.exnMessage e ^ "\n"); TRUTH);
fun add_rec nm th = (membridges := (th :: !membridges); say ("REC-OK " ^ nm ^ "\n"); th);
(* --- non-recursive leaves --- *)
val _ = mk_bridge "enc_line" (ba.enc_line_def, bx.enc_line_x64_def);
val _ = mk_bridge "enc_sec" (ba.enc_sec_def, bx.enc_sec_x64_def);
val _ = mk_bridge "enc_sec_list" (ba.enc_sec_list_def, bx.enc_sec_list_x64_def);
(* --- enc_lines_again (recursive on line list) --- *)
val b_ela = prove(
  ``!xs labs ffis pos acc ok.
      enc_lines_again labs ffis pos x64_config xs (acc,ok) =
      enc_lines_again_x64 labs ffis pos xs (acc,ok)``,
  Induct_on `xs` >> TRY (Cases_on `h`) >> rpt gen_tac >>
  ONCE_REWRITE_TAC[bx.enc_lines_again_x64_def] >>
  gvs[ba.enc_lines_again_def, lemma]);
val _ = add_rec "enc_lines_again" b_ela;
(* --- enc_secs_again (recursive on section list) --- *)
val b_esa = prove(
  ``!xs pos labs ffis.
      enc_secs_again pos labs ffis x64_config xs =
      enc_secs_again_x64 pos labs ffis xs``,
  Induct_on `xs` >> TRY (Cases_on `h`) >> rpt gen_tac >>
  ONCE_REWRITE_TAC[bx.enc_secs_again_x64_def] >>
  gvs[ba.enc_secs_again_def, b_ela, lemma] >>
  rpt (pairarg_tac >> gvs[b_ela, lemma]));
val _ = add_rec "enc_secs_again" b_esa;
(* --- asm ok predicates --- *)
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
(* --- remove_labels_loop (recursive on clock) --- *)
val b_rll = prove(
  ``!clock pos init_labs ffis sec_list.
      remove_labels_loop clock x64_config pos init_labs ffis sec_list =
      remove_labels_loop_x64 clock pos init_labs ffis sec_list``,
  Induct_on `clock` >> rpt gen_tac >>
  ONCE_REWRITE_TAC[ba.remove_labels_loop_def] >>
  ONCE_REWRITE_TAC[bx.remove_labels_loop_x64_def] >>
  gvs ([lemma, b_esa] @ !membridges) >>
  rpt (pairarg_tac >> gvs ([lemma, b_esa] @ !membridges)));
val _ = add_rec "remove_labels_loop" b_rll;
(* --- cascade --- *)
val _ = mk_bridge "remove_labels" (ba.remove_labels_def, bx.remove_labels_x64_def);
val _ = mk_bridge "compile_lab" (ba.compile_lab_def, bx.compile_lab_x64_def);
val _ = mk_bridge "lab_to_target" (ba.lab_to_target_def, bx.lab_to_target_x64_def);
val _ = mk_bridge "from_lab" (ba.from_lab_def, bx.from_lab_x64_def);
val b_fs = mk_bridge "from_stack" (ba.from_stack_def, bx.from_stack_x64_def);
say "=== ENC FULL DONE ===\n";
say ("from_stack bridge: " ^ thm_to_string b_fs ^ "\n");
val _ = OS.Process.exit OS.Process.success;

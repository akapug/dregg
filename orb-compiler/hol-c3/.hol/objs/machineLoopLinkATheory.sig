signature machineLoopLinkATheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val loopBody_def : thm
    val loopInv_def : thm
    val machineLoop_def : thm
    val memRel_def : thm
  
  (*  Theorems  *)
    val DROP_EL_CONS_local : thm
    val Seq_NONE : thm
    val eval_loadbyte : thm
    val eval_loop_guard : thm
    val evaluate_loopBody : thm
    val fix_clock_id : thm
    val loopInv_clock : thm
    val machineLoop_fold_bounded : thm
    val machineLoop_refines_run : thm
    val machineLoop_unfold : thm
    val w2w_byte : thm
end

signature machineStepLinkATheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val mRel_def : thm
    val mstep_def : thm
    val stepBody_def : thm
  
  (*  Theorems  *)
    val eval_cap_guard : thm
    val eval_class_guard : thm
    val evaluate_stepBody : thm
    val mstep_le : thm
    val signed_lt_n2w64 : thm
    val stepBody_refines_step : thm
end

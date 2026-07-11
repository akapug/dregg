signature boundScanTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val arena_def : thm
    val boundScan_def : thm
    val scanFrom_def : thm
    val step_def : thm
  
  (*  Theorems  *)
    val scanFrom_compute : thm
    val vec_0_16 : thm
    val vec_0_17 : thm
    val vec_0_3 : thm
    val vec_10_8 : thm
    val vec_14_2 : thm
    val vec_16_0 : thm
    val vec_16_1 : thm
    val vec_4_10 : thm
end

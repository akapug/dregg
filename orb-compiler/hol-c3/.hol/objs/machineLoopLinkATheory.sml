structure machineLoopLinkATheory :> machineLoopLinkATheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading machineLoopLinkATheory ... "
    else ()
  
  open Type Term Thm
  local open machineStepLinkATheory in end;
  
  structure TDB = struct
    val path =
      OS.Path.base (#(FILE)) ^ ".dat"
    val timestamp = HOLFileSys.modTime path
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "machineLoopLinkA",
        hash = "db068f8c10dbc5fa874ed2a76740bd223d55accd",
        path = path
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  val () = Theory.record_metadata
    "machineLoopLinkA" {timestamp=TDB.timestamp, path=TDB.path}
  
  fun op w2w_byte _ = () val op w2w_byte = TDB.find "w2w_byte"
  fun op memRel_def _ = () val op memRel_def = TDB.find "memRel_def"
  fun op machineLoop_unfold _ = ()
  val op machineLoop_unfold = TDB.find "machineLoop_unfold"
  fun op machineLoop_refines_run _ = ()
  val op machineLoop_refines_run = TDB.find "machineLoop_refines_run"
  fun op machineLoop_fold_bounded _ = ()
  val op machineLoop_fold_bounded = TDB.find "machineLoop_fold_bounded"
  fun op machineLoop_def _ = ()
  val op machineLoop_def = TDB.find "machineLoop_def"
  fun op loopInv_def _ = () val op loopInv_def = TDB.find "loopInv_def"
  fun op loopInv_clock _ = ()
  val op loopInv_clock = TDB.find "loopInv_clock"
  fun op loopBody_def _ = () val op loopBody_def = TDB.find "loopBody_def"
  fun op fix_clock_id _ = () val op fix_clock_id = TDB.find "fix_clock_id"
  fun op evaluate_loopBody _ = ()
  val op evaluate_loopBody = TDB.find "evaluate_loopBody"
  fun op eval_loop_guard _ = ()
  val op eval_loop_guard = TDB.find "eval_loop_guard"
  fun op eval_loadbyte _ = ()
  val op eval_loadbyte = TDB.find "eval_loadbyte"
  fun op Seq_NONE _ = () val op Seq_NONE = TDB.find "Seq_NONE"
  fun op DROP_EL_CONS_local _ = ()
  val op DROP_EL_CONS_local = TDB.find "DROP_EL_CONS_local"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "machineLoopLinkA"

end

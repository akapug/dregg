structure machineStepLinkATheory :> machineStepLinkATheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading machineStepLinkATheory ... "
    else ()
  
  open Type Term Thm
  local open panSemTheory in end;
  
  structure TDB = struct
    val path =
      OS.Path.base (#(FILE)) ^ ".dat"
    val timestamp = HOLFileSys.modTime path
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "machineStepLinkA",
        hash = "b64e3d2739b9127cfd41e25fdcf45bdeaaa528b1",
        path = path
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  val () = Theory.record_metadata
    "machineStepLinkA" {timestamp=TDB.timestamp, path=TDB.path}
  
  fun op stepBody_refines_step _ = ()
  val op stepBody_refines_step = TDB.find "stepBody_refines_step"
  fun op stepBody_def _ = () val op stepBody_def = TDB.find "stepBody_def"
  fun op signed_lt_n2w64 _ = ()
  val op signed_lt_n2w64 = TDB.find "signed_lt_n2w64"
  fun op mstep_le _ = () val op mstep_le = TDB.find "mstep_le"
  fun op mstep_def _ = () val op mstep_def = TDB.find "mstep_def"
  fun op mRel_def _ = () val op mRel_def = TDB.find "mRel_def"
  fun op evaluate_stepBody _ = ()
  val op evaluate_stepBody = TDB.find "evaluate_stepBody"
  fun op eval_class_guard _ = ()
  val op eval_class_guard = TDB.find "eval_class_guard"
  fun op eval_cap_guard _ = ()
  val op eval_cap_guard = TDB.find "eval_cap_guard"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "machineStepLinkA"

end

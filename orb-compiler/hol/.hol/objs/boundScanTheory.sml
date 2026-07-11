structure boundScanTheory :> boundScanTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading boundScanTheory ... "
    else ()
  
  open Type Term Thm
  local open holTheory in end;
  
  structure TDB = struct
    val path =
      OS.Path.base (#(FILE)) ^ ".dat"
    val timestamp = HOLFileSys.modTime path
    val thydata = 
      TheoryReader.load_thydata {
        thyname = "boundScan",
        hash = "5d7b3582a874af6478a3f1bb2169e1fd691ab947",
        path = path
      }
    fun find s = #1 (valOf (Symtab.lookup thydata s))
  end
  val () = Theory.record_metadata
    "boundScan" {timestamp=TDB.timestamp, path=TDB.path}
  
  fun op vec_4_10 _ = () val op vec_4_10 = TDB.find "vec_4_10"
  fun op vec_16_1 _ = () val op vec_16_1 = TDB.find "vec_16_1"
  fun op vec_16_0 _ = () val op vec_16_0 = TDB.find "vec_16_0"
  fun op vec_14_2 _ = () val op vec_14_2 = TDB.find "vec_14_2"
  fun op vec_10_8 _ = () val op vec_10_8 = TDB.find "vec_10_8"
  fun op vec_0_3 _ = () val op vec_0_3 = TDB.find "vec_0_3"
  fun op vec_0_17 _ = () val op vec_0_17 = TDB.find "vec_0_17"
  fun op vec_0_16 _ = () val op vec_0_16 = TDB.find "vec_0_16"
  fun op step_def _ = () val op step_def = TDB.find "step_def"
  fun op scanFrom_def _ = () val op scanFrom_def = TDB.find "scanFrom_def"
  fun op scanFrom_compute _ = ()
  val op scanFrom_compute = TDB.find "scanFrom_compute"
  fun op boundScan_def _ = ()
  val op boundScan_def = TDB.find "boundScan_def"
  fun op arena_def _ = () val op arena_def = TDB.find "arena_def"
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "boundScan"

end

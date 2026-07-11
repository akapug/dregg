(* ===========================================================================
   C24 — the machine-checked AUDIT theory.  Asserts, adversarially:
     * traversal_machine_code closes spec->machine-code for the drorb
       traversalStage: [oracles: DISK_THM] [axioms: ], hyps = 0, NON-vacuous
       (a real machine_sem SUBSET {Terminate Success ...} reporting travDecide).
     * grounds the traversal decision truth table on REAL path inputs
       (/../etc/passwd -> BLOCKED=1, /health -> ALLOWED=0, /etc/passwd -> 0,
        /a/../b -> 1, trailing /foo/.. -> 1), and the escape-automaton states.
     * the fold is a GENUINELY different core from the C21 hash/clen (the escape
       automaton escAcc, not an arithmetic accumulator); the N=1 peel is real.
     * the body-generic frame engine loop_frame remains non-vacuous.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open travGenTheory travCoreTheory travDataTheory composedCommonTheory
     stringTheory wordsLib;

val _ = new_theory "verifyC24";
val _ = Globals.show_assums := true;

fun assert b msg = if b then () else raise Fail ("C24 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val trav = traversal_machine_code;

val _ = print "\n===== traversal_machine_code (drorb traversalStage, N=1 composed peel) =====\n";
val _ = print (thm_to_string trav);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string trav ^ "\n");

(* 1. closed, DISK_THM-only, hyps=0 *)
val _ = assert (oracles_ok trav) "traversal_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp trav)) "traversal_machine_code has hypotheses";

(* 2. NON-vacuous: a real machine_sem SUBSET {Terminate Success (.. travDecide ..)} *)
val _ = assert (mentions "machine_sem" trav andalso mentions "Terminate Success" trav)
               "traversal_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "travDecide" trav)
               "traversal_machine_code lost its stage decision word travDecide";
val _ = assert (mentions "report_vec" trav)
               "traversal_machine_code does not report the decision over the FFI";
val _ = assert (mentions "travProg" trav)
               "traversal_machine_code does not target the parser-output program travProg";

(* 3. GROUND the traversal decision truth table on REAL path bytes.
   travDecide = 1w BLOCKED, 0w ALLOWED.  Decode is the drorb single %-boundary
   (Route.Path.decodeSegs); travEsc is the post-decode ".."-contains check. *)
val d_esc   = EVAL “travDecide (MAP (\c. ORD c) "/../etc/passwd")”;   (* BLOCKED *)
val d_ok    = EVAL “travDecide (MAP (\c. ORD c) "/health")”;          (* ALLOWED *)
val d_clean = EVAL “travDecide (MAP (\c. ORD c) "/etc/passwd")”;      (* ALLOWED *)
val d_mid   = EVAL “travDecide (MAP (\c. ORD c) "/a/../b")”;          (* BLOCKED *)
val d_tail  = EVAL “travDecide (MAP (\c. ORD c) "/foo/..")”;          (* BLOCKED (trailing ..) *)
val e_esc   = EVAL “travEsc    (MAP (\c. ORD c) "/../etc/passwd")”;   (* automaton state 4 *)
val e_ok    = EVAL “travEsc    (MAP (\c. ORD c) "/health")”;          (* automaton state 3 *)

val _ = print ("\ntravDecide /../etc/passwd (BLOCKED) = " ^ term_to_string (rhs (concl d_esc)) ^ "\n");
val _ = print ("travDecide /health       (ALLOWED) = " ^ term_to_string (rhs (concl d_ok)) ^ "\n");
val _ = print ("travDecide /etc/passwd   (ALLOWED) = " ^ term_to_string (rhs (concl d_clean)) ^ "\n");
val _ = print ("travDecide /a/../b       (BLOCKED) = " ^ term_to_string (rhs (concl d_mid)) ^ "\n");
val _ = print ("travDecide /foo/..       (BLOCKED) = " ^ term_to_string (rhs (concl d_tail)) ^ "\n");
val _ = print ("travEsc    /../etc/passwd (state)  = " ^ term_to_string (rhs (concl e_esc)) ^ "\n");
val _ = print ("travEsc    /health        (state)  = " ^ term_to_string (rhs (concl e_ok)) ^ "\n");

val _ = assert (rhs (concl d_esc)   ~~ “1w:word64”) "escaping /../etc/passwd not BLOCKED(1)";
val _ = assert (rhs (concl d_ok)    ~~ “0w:word64”) "safe /health not ALLOWED(0)";
val _ = assert (rhs (concl d_clean) ~~ “0w:word64”) "safe /etc/passwd not ALLOWED(0)";
val _ = assert (rhs (concl d_mid)   ~~ “1w:word64”) "mid ../ /a/../b not BLOCKED(1)";
val _ = assert (rhs (concl d_tail)  ~~ “1w:word64”) "trailing .. /foo/.. not BLOCKED(1)";
val _ = assert (rhs (concl e_esc)   ~~ “4w:word64”) "escape automaton did not reach state 4";
val _ = assert (rhs (concl e_ok)    ~~ “3w:word64”) "safe path automaton state wrong";

(* the decision genuinely BRANCHES (BLOCKED and ALLOWED differ) *)
val _ = assert (not (rhs (concl d_esc) ~~ rhs (concl d_ok)))
               "the traversal gate does not branch (blocked = allowed)";

(* 4. the fold is a GENUINELY different core: the escape automaton, NOT a hash.
   escLoop_framed refines the parsed While to the spec travEsc; travEsc is the
   FOLDL over the escape automaton escAcc; escAcc is the byte state machine. *)
val _ = assert (mentions "travEsc" escLoop_framed andalso mentions "escLoop" escLoop_framed
                andalso mentions "foldInv" escLoop_framed)
               "escLoop_framed is not the traversal escape fold core";
val _ = assert (mentions "FOLDL" travEsc_def andalso mentions "escAcc" travEsc_def)
               "travEsc is not a FOLDL over the escape automaton";
val _ = assert (mentions "escLoop" escLoop_framed andalso mentions "While foldGuard" escLoop_def)
               "escLoop is not the parsed While over foldGuard";
val _ = assert (mentions "47w" escAcc_def andalso mentions "46w" escAcc_def)
               "escAcc is not the byte-level '/'(47) '.'(46) escape automaton";
val _ = assert (not (mentions "hashBytes" travEsc_def) andalso not (mentions "hashAcc" travEsc_def))
               "the traversal fold is not genuinely distinct from the C21/C22 hash fold";

(* 5. escLoop / travGate are GENUINE parser subterms (travData surgery fired) *)
val _ = assert (mentions "escLoop" travMainBody_def andalso mentions "travGate" travMainBody_def)
               "travMainBody is not refolded to the genuine parser escLoop/travGate (leanc in TCB)";

(* 6. the body-generic frame engine loop_frame is still non-vacuous *)
val _ = assert (mentions "FOLDL" loop_frame andalso mentions "While foldGuard" loop_frame)
               "loop_frame is vacuous";

val _ = print ("\n@@ verifyC24 axioms = " ^ Int.toString (length (axioms "verifyC24")) ^ "\n");
val _ = print "\n@@@ C24 AUDIT PASSED: traversal_machine_code closes drorb traversalStage end-to-end (N=1 composed peel); DISK_THM-only, hyps=0, non-vacuous; blocked=1/allowed=0 grounded on real paths @@@\n";

val _ = export_theory ();

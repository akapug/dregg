(* ===========================================================================
   C29 — the machine-checked AUDIT theory.  Asserts, adversarially:
     * ipfilter_machine_code closes spec->machine-code for the drorb ipfilterStage:
       [oracles: DISK_THM] [axioms: ], hyps = 0, NON-vacuous (a real machine_sem
       SUBSET {Terminate Success ...} reporting ipfDecide over the client address).
     * grounds the admit truth table on REAL client IPs (encodeAddr byte-strings):
         10.0.0.0 / 10.1.2.3 (inside deny 10.0.0.0/8) -> ipfDecide 0w BLOCKED,
         127.0.0.0 (loopback) / 11.0.0.0 (adjacent /8) -> ipfDecide 1w ADMIT,
         no-address ([4]) -> 1w ADMIT (the deployed permissive default),
         a v6 client -> 1w ADMIT (family separation),
       and the prefix-matcher states (9w = deny prefix matched, 10w = mismatch sink).
     * the fold is a GENUINELY different core from the C21 hash / C24 escape
       automaton (the CIDR prefix matcher cidrAcc; the N=1 peel is real).
     * the body-generic frame engine loop_frame remains non-vacuous.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open ipfGenTheory ipfCoreTheory ipfDataTheory composedCommonTheory
     listTheory wordsLib;

val _ = new_theory "verifyC29";
val _ = Globals.show_assums := true;

fun assert b msg = if b then () else raise Fail ("C29 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val ipf = ipfilter_machine_code;

val _ = print "\n===== ipfilter_machine_code (drorb ipfilterStage, N=1 composed peel) =====\n";
val _ = print (thm_to_string ipf);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string ipf ^ "\n");

(* 1. closed, DISK_THM-only, hyps=0 *)
val _ = assert (oracles_ok ipf) "ipfilter_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp ipf)) "ipfilter_machine_code has hypotheses";

(* 2. NON-vacuous: a real machine_sem SUBSET {Terminate Success (.. ipfDecide ..)} *)
val _ = assert (mentions "machine_sem" ipf andalso mentions "Terminate Success" ipf)
               "ipfilter_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "ipfDecide" ipf)
               "ipfilter_machine_code lost its stage decision word ipfDecide";
val _ = assert (mentions "report_vec" ipf)
               "ipfilter_machine_code does not report the decision over the FFI";
val _ = assert (mentions "ipfProg" ipf)
               "ipfilter_machine_code does not target the parser-output program ipfProg";

(* 3. GROUND the admit truth table on REAL client IPs (encodeAddr byte-strings:
   family tag 4=v4 / 6=v6, then one 0/1 byte per address bit).
   ipfDecide = 1w ADMIT, 0w BLOCKED.  deployRuleset = one deny rule 10.0.0.0/8
   (10 = 00001010), default-admit. *)
(* 10.0.0.0 : 4 :: 00001010 :: rest(0) — inside the deny /8 *)
val d_blk0  = EVAL “ipfDecide ([4;0;0;0;0;1;0;1;0] ++ REPLICATE 24 0)”;
val m_blk0  = EVAL “ipfMatch  ([4;0;0;0;0;1;0;1;0] ++ REPLICATE 24 0)”;
(* 10.1.2.3 : same 9-byte deny prefix, differing tail (early-exit absorbs it) *)
val d_blk1  = EVAL “ipfDecide ([4;0;0;0;0;1;0;1;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;1;0;0;0;0;0;0;0;1;1])”;
(* 127.0.0.0 : 4 :: 01111111 :: rest — loopback, outside deny -> admit *)
val d_ok0   = EVAL “ipfDecide ([4;0;1;1;1;1;1;1;1] ++ REPLICATE 24 0)”;
val m_ok0   = EVAL “ipfMatch  ([4;0;1;1;1;1;1;1;1] ++ REPLICATE 24 0)”;
(* 11.0.0.0 : 4 :: 00001011 :: rest — adjacent /8, differs at the LAST prefix bit *)
val d_ok1   = EVAL “ipfDecide ([4;0;0;0;0;1;0;1;1] ++ REPLICATE 24 0)”;
(* no address ([4]) : the deployed permissive default -> admit *)
val d_none  = EVAL “ipfDecide [4]”;
val m_none  = EVAL “ipfMatch  [4]”;
(* a v6 client (tag 6) : family separation -> admit *)
val d_v6    = EVAL “ipfDecide ([6] ++ REPLICATE 32 0)”;

val _ = print ("\nipfDecide 10.0.0.0  (BLOCKED) = " ^ term_to_string (rhs (concl d_blk0)) ^ "\n");
val _ = print ("ipfMatch  10.0.0.0  (state)   = " ^ term_to_string (rhs (concl m_blk0)) ^ "\n");
val _ = print ("ipfDecide 10.1.2.3  (BLOCKED) = " ^ term_to_string (rhs (concl d_blk1)) ^ "\n");
val _ = print ("ipfDecide 127.0.0.0 (ADMIT)   = " ^ term_to_string (rhs (concl d_ok0)) ^ "\n");
val _ = print ("ipfMatch  127.0.0.0 (state)   = " ^ term_to_string (rhs (concl m_ok0)) ^ "\n");
val _ = print ("ipfDecide 11.0.0.0  (ADMIT)   = " ^ term_to_string (rhs (concl d_ok1)) ^ "\n");
val _ = print ("ipfDecide no-addr   (ADMIT)   = " ^ term_to_string (rhs (concl d_none)) ^ "\n");
val _ = print ("ipfMatch  no-addr   (state)   = " ^ term_to_string (rhs (concl m_none)) ^ "\n");
val _ = print ("ipfDecide v6-client (ADMIT)   = " ^ term_to_string (rhs (concl d_v6)) ^ "\n");

val _ = assert (rhs (concl d_blk0) ~~ “0w:word64”) "10.0.0.0 not BLOCKED(0)";
val _ = assert (rhs (concl m_blk0) ~~ “9w:word64”) "10.0.0.0 deny prefix did not fully match (state 9)";
val _ = assert (rhs (concl d_blk1) ~~ “0w:word64”) "10.1.2.3 not BLOCKED(0)";
val _ = assert (rhs (concl d_ok0)  ~~ “1w:word64”) "127.0.0.0 not ADMIT(1)";
val _ = assert (rhs (concl m_ok0)  ~~ “10w:word64”) "127.0.0.0 did not hit the mismatch sink (state 10)";
val _ = assert (rhs (concl d_ok1)  ~~ “1w:word64”) "11.0.0.0 (adjacent /8) not ADMIT(1)";
val _ = assert (rhs (concl d_none) ~~ “1w:word64”) "no-address not ADMIT(1) (permissive default)";
val _ = assert (rhs (concl m_none) ~~ “1w:word64”) "no-address matcher state wrong";
val _ = assert (rhs (concl d_v6)   ~~ “1w:word64”) "v6 client not ADMIT(1) (family separation)";

(* the decision genuinely BRANCHES (ADMIT and BLOCKED differ) *)
val _ = assert (not (rhs (concl d_blk0) ~~ rhs (concl d_ok0)))
               "the ipfilter gate does not branch (blocked = admit)";

(* 4. the fold is a GENUINELY different core: the CIDR prefix matcher, NOT a hash
   nor the C24 escape automaton.  cidrLoop_framed refines the parsed While to the
   spec ipfMatch; ipfMatch is the FOLDL over cidrAcc; cidrAcc is the deny-prefix
   byte matcher (family tag 4w + the 8 bits of 10 = 00001010). *)
val _ = assert (mentions "ipfMatch" cidrLoop_framed andalso mentions "cidrLoop" cidrLoop_framed
                andalso mentions "foldInv" cidrLoop_framed)
               "cidrLoop_framed is not the CIDR prefix fold core";
val _ = assert (mentions "FOLDL" ipfMatch_def andalso mentions "cidrAcc" ipfMatch_def)
               "ipfMatch is not a FOLDL over the CIDR prefix matcher";
val _ = assert (mentions "cidrLoop" cidrLoop_framed andalso mentions "While foldGuard" cidrLoop_def)
               "cidrLoop is not the parsed While over foldGuard";
val _ = assert (mentions "4w" cidrAcc_def andalso mentions "9w" cidrAcc_def)
               "cidrAcc is not the byte-level deny-prefix matcher (tag 4w / state 9w)";
val _ = assert (not (mentions "hashBytes" ipfMatch_def) andalso not (mentions "hashAcc" ipfMatch_def)
                andalso not (mentions "escAcc" ipfMatch_def))
               "the ipfilter fold is not genuinely distinct from the C21 hash / C24 escape fold";

(* 5. cidrLoop / ipfGate are GENUINE parser subterms (ipfData surgery fired) *)
val _ = assert (mentions "cidrLoop" ipfMainBody_def andalso mentions "ipfGate" ipfMainBody_def)
               "ipfMainBody is not refolded to the genuine parser cidrLoop/ipfGate (leanc in TCB)";

(* 6. the body-generic frame engine loop_frame is still non-vacuous *)
val _ = assert (mentions "FOLDL" loop_frame andalso mentions "While foldGuard" loop_frame)
               "loop_frame is vacuous";

val _ = print ("\n@@ verifyC29 axioms = " ^ Int.toString (length (axioms "verifyC29")) ^ "\n");
val _ = print "\n@@@ C29 AUDIT PASSED: ipfilter_machine_code closes drorb ipfilterStage end-to-end (N=1 composed peel); DISK_THM-only, hyps=0, non-vacuous; blocked=0/admit=1 grounded on real client IPs @@@\n";

val _ = export_theory ();

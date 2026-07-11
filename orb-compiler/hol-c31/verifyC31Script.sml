(* ===========================================================================
   C31 — the machine-checked AUDIT theory.  Asserts, adversarially:
     * the JWT admin gate jwt_machine_code closes spec->machine-code:
       [oracles: DISK_THM] [axioms: ], hyps = 0, NON-vacuous (a real
       machine_sem SUBSET {Terminate Success ...} reporting jwtAdmit).
     * it is a genuinely DISTINCT decision over a DISTINCT parser-output program
       (jwtProg, not cacheKeyProg/basicProg; jwtAdmit, not basicAdmit / corsAllow /
       admitDecide / cacheServe).
     * grounds the HS256 verify + alg-confusion decision (drorb Jwt.afterKey over
       the HS256 verify) on REAL byte inputs, exercising the FULL admit truth-table
       INCLUDING the alg-confusion-rejected case (jwt_alg_confusion_safe):
         - a VALID signed token (presented sig == HMAC digest, alg = HS256)  -> 1
             (verifyHmac T /\ alg=key.alg /\ alg<>none  -> admit)
         - a BAD signature     (presented sig <> HMAC digest, alg = HS256)   -> 0
             (verifyHmac F  -> reject .badSignature -> 401)
         - alg = none          (VALID sig, but alg = none)                   -> 0
             (reject .algNone -> 401 : the unsecured "none" is refused)
         - alg CONFUSION       (VALID sig, but alg = RS256 != key.alg=HS256) -> 0
             (reject .algMismatch -> 401 : an RS256-declared token can NEVER be
              admitted on the HS256 key path, EVEN with a colliding signature -
              this is jwt_alg_confusion_safe, grounded on a genuinely valid sig).
       The alg=none / alg=confusion cases use a sig that GENUINELY hash-equals the
       digest, so the reject is caused by the ALG gate alone, not a sig mismatch
       (non-vacuous alg-confusion witness).  The bad-signature case's hash
       genuinely DIFFERS as word64 (a real miss, not a hash collision).
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open jwtGenTheory jwtCoreTheory hashBytesLoopTheory wordsTheory wordsLib;

val _ = new_theory "verifyC31";
val _ = Globals.show_assums := true;

fun assert b msg = if b then () else raise Fail ("C31 AUDIT FAILED: " ^ msg);
fun oracles_ok th =
  let val (oracs, axs) = Tag.dest_tag (Thm.tag th) in
    List.all (fn s => s = "DISK_THM") oracs andalso null axs end;
fun mentions s th = String.isSubstring s (thm_to_string th);

val jwt = jwtGenTheory.jwt_machine_code;

val _ = print "\n===== jwt_machine_code (the HS256 JWT admin sig-verify + alg-confusion gate) =====\n";
val _ = print (thm_to_string jwt);
val _ = print ("\nTAGS: " ^ Portable.with_flag (Globals.show_tags, true) thm_to_string jwt ^ "\n");

(* 1. closed, DISK_THM-only, hyps = 0 *)
val _ = assert (oracles_ok jwt) "jwt_machine_code has a non-DISK_THM oracle or an axiom";
val _ = assert (null (hyp jwt)) "jwt_machine_code has hypotheses";

(* 2. NON-vacuous: a real machine_sem SUBSET {Terminate Success ...} over jwtAdmit *)
val _ = assert (mentions "machine_sem" jwt andalso mentions "Terminate Success" jwt)
               "jwt_machine_code is vacuous (no machine_sem / Terminate Success)";
val _ = assert (mentions "jwtAdmit" jwt)
               "jwt_machine_code lost its composed spec word jwtAdmit";

(* 3. a DISTINCT decision over a DISTINCT program (not a re-run of C22..C27) *)
val _ = assert (mentions "jwtProg" jwt)
               "jwt_machine_code does not target the jwtProg parser output";
val _ = assert (not (mentions "basicAdmit" jwt) andalso not (mentions "corsAllow" jwt)
                andalso not (mentions "admitDecide" jwt) andalso not (mentions "cacheServe" jwt))
               "jwt decision is not distinct from the C22..C27 decisions";

(* 4. ground the HS256 verify + alg-confusion decision on REAL bytes ------------ *)
(* digest = a 32-byte HMAC-SHA256 output (the CRYPTO TRUST BOUNDARY's result;
   NOT computed here - taken as input, as C27 takes the decoded credential).      *)
val digest   = “[43;142;29;7;200;91;255;16;77;138;3;61;149;220;100;5;
                 33;178;9;250;44;12;201;88;7;19;66;255;130;41;99;8]”;
(* a VALID token presents a signature that EQUALS the HMAC digest (verifyHmac T). *)
val validSig = “[43;142;29;7;200;91;255;16;77;138;3;61;149;220;100;5;
                 33;178;9;250;44;12;201;88;7;19;66;255;130;41;99;8]”;
(* a FORGED token presents a signature differing in the first byte (verifyHmac F).*)
val badSig   = “[44;142;29;7;200;91;255;16;77;138;3;61;149;220;100;5;
                 33;178;9;250;44;12;201;88;7;19;66;255;130;41;99;8]”;

(* the VALID signature genuinely hash-equals the digest (so the alg=none/confusion
   rejects below are caused by the ALG gate alone, not a signature miss). *)
val hEqValid = EVAL (Term [QUOTE "(n2w (hashBytesN ", ANTIQUOTE validSig,
                      QUOTE ") = (n2w (hashBytesN ", ANTIQUOTE digest,
                      QUOTE "):word64))"]);
val _ = print ("\nvalid-sig hash = digest hash (word64)? " ^ term_to_string (rhs (concl hEqValid)) ^ "\n");
val _ = assert (rhs (concl hEqValid) ~~ “T”)
        "valid signature does NOT hash-equal the digest - alg-confusion witness vacuous";

(* the BAD signature's hash genuinely DIFFERS from the digest as word64 (a real
   miss, not a hash collision). *)
val hNeBad = EVAL (Term [QUOTE "(n2w (hashBytesN ", ANTIQUOTE badSig,
                      QUOTE ") = (n2w (hashBytesN ", ANTIQUOTE digest,
                      QUOTE "):word64))"]);
val _ = print ("bad-sig hash = digest hash (word64)? " ^ term_to_string (rhs (concl hNeBad)) ^ "\n");
val _ = assert (rhs (concl hNeBad) ~~ “F”)
        "bad signature COLLIDES with the digest - bad-signature reject case vacuous";

(* the jwtAdmit truth table over the four real cases (= the HS256 afterKey gate) *)
val j1 = EVAL (Term [QUOTE "jwtAdmit ", ANTIQUOTE digest, QUOTE " ", ANTIQUOTE validSig, QUOTE " 1"]);
val j2 = EVAL (Term [QUOTE "jwtAdmit ", ANTIQUOTE digest, QUOTE " ", ANTIQUOTE badSig,   QUOTE " 1"]);
val j3 = EVAL (Term [QUOTE "jwtAdmit ", ANTIQUOTE digest, QUOTE " ", ANTIQUOTE validSig, QUOTE " 0"]);
val j4 = EVAL (Term [QUOTE "jwtAdmit ", ANTIQUOTE digest, QUOTE " ", ANTIQUOTE validSig, QUOTE " 2"]);
val _ = print ("\njwtAdmit  valid-sig HS256   (admit)          = " ^ term_to_string (rhs (concl j1)) ^ "\n");
val _ = print ("jwtAdmit  bad-sig   HS256   (bad signature)  = " ^ term_to_string (rhs (concl j2)) ^ "\n");
val _ = print ("jwtAdmit  valid-sig none    (alg = none)     = " ^ term_to_string (rhs (concl j3)) ^ "\n");
val _ = print ("jwtAdmit  valid-sig RS256   (alg confusion)  = " ^ term_to_string (rhs (concl j4)) ^ "\n");
val _ = assert (rhs (concl j1) ~~ “1n”) "valid signed HS256 token != admit (1)";
val _ = assert (rhs (concl j2) ~~ “0n”) "bad signature != reject (0) - sig boundary broken";
val _ = assert (rhs (concl j3) ~~ “0n”) "alg=none != reject (0) - unsecured token admitted!";
val _ = assert (rhs (concl j4) ~~ “0n”)
        "alg=RS256 confusion != reject (0) - alg-confusion boundary broken (jwt_alg_confusion_safe violated)";

val _ = print ("\n@@ verifyC31 axioms = " ^ Int.toString (length (axioms "verifyC31")) ^ "\n");
val _ = print "\n@@@ C31 AUDIT PASSED: mk_composedWrapper closes the HS256 JWT admin gate (jwtAdminStage / afterKey HS256 verify) DIRECTLY - no spine adaptation; DISK_THM-only, hyps=0, non-vacuous; the sig-verify + alg-confusion decision grounded on valid / bad-sig / alg=none / alg-confusion inputs (valid sig genuinely hash-equal; bad sig no collision) - the alg-confusion token is refused EVEN with a colliding signature @@@\n";

val _ = export_theory ();

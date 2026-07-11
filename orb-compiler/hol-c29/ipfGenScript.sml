(* ===========================================================================
   C29 — the ipfilter CIDR admission gate stage closed spec->machine-code by ONE
   mk_composedWrapper1 call (the N = 1 peel of the C23 composed generator, first
   exercised in C24).  Single CIDR-prefix-scan fold (cidrLoop) + the
   matched-state->admit gate (ipfGate); the generator emits
   MainRefine + Sem + Install + EndToEnd -> ipfilter_machine_code.
   =========================================================================== *)
open HolKernel boolLib bossLib Parse;
open arithmeticTheory listTheory wordsTheory wordsLib finite_mapTheory;
open panLangTheory panSemTheory panPropsTheory;
open foldLoopSchemaTheory composedCommonTheory
     ipfCoreTheory ipfDataTheory ipfLinkBInstTheory;
open panComposedLib;

val _ = new_theory "ipfGen";

val res = panComposedLib.mk_composedWrapper1
  { prefix = "ipfilter",
    ffiName = "ipfFFI", ffiDef = ipfFFI_def, ffiArgs = "input",
    stagedDef = ipfStaged_def, clockBound = "LENGTH input", arena0 = "32w",
    fold0 = { arenaOff="32w", lenOff=NONE, lenExpr="LENGTH input", memArg="input",
              loopName="cidrLoop", framed=cidrLoop_framed, noFFI=cidrLoop_noFFI,
              accWord="ipfMatch input", saveVar="acc" },
    decVar = "dec", gateName="ipfGate", gateThm=evaluate_ipfGate,
    storeOff="8w", resultWord="ipfDecide input",
    mainBodyName="ipfMainBody", mainBodyDef=ipfMainBody_def,
    progName="ipfProg", progDef=ipfProg_def, linkB=ipfProg_linkB,
    unfoldCore=[ipfMainBody_def, cidrLoop_def, foldGuard_def, cidrBody_def, ipfGate_def] };

val _ = export_theory ();

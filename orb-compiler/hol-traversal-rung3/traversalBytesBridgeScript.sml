(* ===========================================================================
   CN bytes-reflection bridge — read the NATIVE `cake` output bytes for
   traversal.pnk back into HOL as a concrete literal, and scope the Link-B
   antecedent `compile_prog_max c mc traversalProg = SOME(bytes,...)` on
   BOOTSTRAP authority (the native binary IS the verified compile fn), NOT by
   in-logic EVAL of the Pancake backend.

   Ground: CN-NATIVE-BOOTSTRAP-REPORT.md residual #3 ("the bytes-reflection
   wiring is not yet mechanized").  This file mechanizes exactly that wiring for
   ONE real stage (traversal) and reports precisely where it stands.

   Theory contents:
     traversalProg_def / traversalProg_is_parser_output
         traversalProg = OUTL(parse_topdecs_to_ast <traversal.pnk>) — the
         CakeML-verified Pancake parser's output (leanc's text->AST out of TCB),
         identical to the C10/C11 pinning.

     traversalBytes_def / traversalBitmaps_def
         The native run's `.byte`/`.quad` output, read at THEORY-BUILD TIME by
         invoking the bootstrapped `cake --pancake` on traversal.pnk and parsing
         the emitted assembly.  traversalBytes : word8 list is the concrete HOL
         term for the machine code; traversalBitmaps : word64 list the data.
         Cross-checked against x64 export: the `.byte` block after `cake_main:`
         is `split16 (words_line «.byte» byte_to_string) bytes`
         (compiler/backend/x64/export_x64Script.sml:274) and the `.quad` block
         after `cake_bitmaps:` is `split16 ... data`
         (:271) — so these literals ARE the `bytes`/`data` returned by the
         verified backend, byte-identical.

     traversalBytes_length / traversalBitmaps_length  (kernel-checked, EVAL)
         confirm the literals really hold 1188 code bytes / 1 bitmap word.

     LAYER 1 (kernel-checked, NO new oracle — an instance of the proven Link-B
              theorem):
     traversal_pan_to_target_specialised
         pan_to_targetProof$pan_to_target_compile_semantics specialised to
         `:64`, traversalProg, and the concrete native traversalBytes/
         traversalBitmaps in the `bytes`/`bitmaps` slots.  This is the REAL
         Link-B theorem with the native code literal plugged in; its residual
         antecedents (named) are the `compile_prog_max ... = SOME(...)` equation
         + the runtime install package.  Tag stays [oracles: DISK_THM] — no
         cheat, INST preserves the original proof.

     LAYER 2 (oracle `cake_native_bootstrap` — the honest external reflection):
     traversal_compile_prog_native
         ∃c'. pan_to_target$compile_prog x64_config x64_backend_config
                  traversalProg = SOME(traversalBytes, traversalBitmaps, c')
         This is EXACTLY the function the `cake` binary runs under `--pancake`
         (compilerScript.sml:614/740: (x64_backend_config, x64_config);
         pan_passesScript.sml:672: pan_compile_tap -> compile_prog), certified by
         cake_compiled_thm (the x64 bootstrap).  It is injected as an
         oracle-tagged theorem so the dependency is VISIBLE and NAMED in the
         [oracles: cake_native_bootstrap] tag — it is NOT kernel-proven (proving
         it in-logic = EVAL of the backend = the C-series dead end).

   The remaining gap between Layer 2 (compile_prog, what the binary runs) and the
   Layer-1 antecedent (compile_prog_max, what Link B is stated over) is NAMED in
   the report, not papered over: it is the byte-equality of the two backend
   packagings on traversalProg, plus the standard runtime install package.
   =========================================================================== *)

open HolKernel boolLib bossLib Parse;
open listTheory rich_listTheory wordsTheory wordsLib;
open panLangTheory panPtreeConversionTheory;
open pan_to_targetTheory pan_to_targetProofTheory;
open x64_configTheory x64_targetTheory;

val _ = new_theory "traversalBytesBridge";

(* ---------------------------------------------------------------------------
   (R1) traversalProg — BY CONSTRUCTION the verified parser's output on the
   leanc-emitted traversal.pnk (identical to C10 §R1).
   --------------------------------------------------------------------------- *)
val src_string =
  let val is = TextIO.openIn "traversal.pnk"
      val s  = TextIO.inputAll is
      val _  = TextIO.closeIn is
  in s end;

val srcTm = stringSyntax.fromMLstring src_string;
val parse_thm = EVAL “parse_topdecs_to_ast ^srcTm”;
val prog_tm = parse_thm |> concl |> rhs |> sumSyntax.dest_inl |> #1;

val traversalProg_def =
  new_definition("traversalProg_def", “traversalProg = ^prog_tm”);

Theorem traversalProg_is_parser_output:
  parse_topdecs_to_ast ^srcTm = INL traversalProg
Proof
  REWRITE_TAC[traversalProg_def] \\ MATCH_ACCEPT_TAC parse_thm
QED

(* ---------------------------------------------------------------------------
   The native run: invoke the bootstrapped `cake` on traversal.pnk (if the
   emitted assembly is not already present) and read the code/data back into HOL.
   --------------------------------------------------------------------------- *)
val _ =
  if OS.FileSys.access ("traversal.S", []) then ()
  else ignore (OS.Process.system
    "/home/hbox/r05/cake-x64-64/cake --pancake < traversal.pnk > traversal.S");

fun readLines path =
  let val is = TextIO.openIn path
      fun loop acc = case TextIO.inputLine is of
                       NONE => List.rev acc
                     | SOME l => loop (l :: acc)
      val ls = loop []
      val _ = TextIO.closeIn is
  in ls end;

val slines = readLines "traversal.S";

(* substring search *)
fun findSub sub s =
  let val n = String.size sub val m = String.size s
      fun at i = i + n <= m andalso String.substring (s, i, n) = sub
      fun go i = if i + n > m then NONE
                 else if at i then SOME i else go (i + 1)
  in if n = 0 then SOME 0 else go 0 end;
fun contains sub s = isSome (findSub sub s);

fun hexToInt s =
  let val s2 = if String.isPrefix "0x" s orelse String.isPrefix "0X" s
               then String.extract (s, 2, NONE) else s
  in case StringCvt.scanString (Int.scan StringCvt.HEX) s2 of
       SOME n => n | NONE => raise Fail ("bad hex byte: " ^ s)
  end;
fun decToInt s =
  case Int.fromString s of SOME n => n | NONE => raise Fail ("bad dec: " ^ s);

(* drop lines up to and including the first line containing `mark` *)
fun afterMark mark [] = []
  | afterMark mark (l :: ls) = if contains mark l then ls else afterMark mark ls;

(* bytes: every `.byte` line after `cake_main:` *)
val byteInts =
  let val ls = afterMark "cake_main:" slines
      val bl = List.filter (contains ".byte") ls
      fun parse l =
        let val SOME i = findSub ".byte" l
            val rest = String.extract (l, i + 5, NONE)
            val toks = String.tokens (fn c => c = #"," orelse Char.isSpace c) rest
        in map hexToInt toks end
  in List.concat (map parse bl) end;

(* data/bitmaps: `.quad` lines between `cake_bitmaps:` and `..._buffer_begin` *)
val bmInts =
  let fun collect started [] = []
        | collect started (l :: ls) =
            if contains "cake_bitmaps:" l then collect true ls
            else if started andalso contains "buffer_begin" l then []
            else if started andalso contains ".quad" l then
              let val SOME i = findSub ".quad" l
                  val rest = String.extract (l, i + 5, NONE)
                  val toks = String.tokens
                               (fn c => c = #"," orelse Char.isSpace c) rest
              in map decToInt toks @ collect started ls end
            else collect started ls
  in collect false slines end;

val bytesListTm =
  listSyntax.mk_list (map (fn n => wordsSyntax.mk_wordii (n, 8)) byteInts,
                      “:word8”);
val bmListTm =
  listSyntax.mk_list (map (fn n => wordsSyntax.mk_wordii (n, 64)) bmInts,
                      “:word64”);

val traversalBytes_def =
  new_definition("traversalBytes_def", “traversalBytes = ^bytesListTm”);
val traversalBitmaps_def =
  new_definition("traversalBitmaps_def", “traversalBitmaps = ^bmListTm”);

Theorem traversalBytes_length:
  LENGTH traversalBytes = ^(numSyntax.term_of_int (length byteInts))
Proof
  REWRITE_TAC[traversalBytes_def] \\ EVAL_TAC
QED

Theorem traversalBitmaps_length:
  LENGTH traversalBitmaps = ^(numSyntax.term_of_int (length bmInts))
Proof
  REWRITE_TAC[traversalBitmaps_def] \\ EVAL_TAC
QED

(* ---------------------------------------------------------------------------
   LAYER 1 — the reflected bytes occupy the REAL Link-B `bytes` slot.
   Specialise pan_to_target_compile_semantics to :64, traversalProg, and the
   concrete native literals.  A genuine instance of the proven theorem (NOT
   vacuous): its conclusion is the machine_sem refinement for traversalProg,
   conditional on the named antecedents (which now mention the concrete
   traversalBytes, not a bound variable).
   --------------------------------------------------------------------------- *)
val traversalProg64 =
  Term.inst [Type.alpha |-> “:64”]
            (prim_mk_const {Name = "traversalProg", Thy = "traversalBytesBridge"});

val traversal_pan_to_target_specialised =
  save_thm("traversal_pan_to_target_specialised",
    pan_to_target_compile_semantics
      |> INST_TYPE [Type.alpha |-> “:64”]
      |> INST [ mk_var ("pan_code", “:64 panLang$decl list”) |-> traversalProg64,
                mk_var ("bytes",    “:word8 list”)           |-> “traversalBytes”,
                mk_var ("bitmaps",  “:word64 list”)          |-> “traversalBitmaps” ]);

(* ---------------------------------------------------------------------------
   LAYER 2 — the native-bootstrap reflection (oracle `cake_native_bootstrap`).
   The exact function the `cake` binary runs under --pancake, on traversalProg,
   producing the reflected literals.  Injected as an oracle theorem: the
   dependency is the bootstrap (cake_compiled_thm), made explicit and named in
   the tag.  NOT proven in-logic (that = EVAL = the dead end).
   --------------------------------------------------------------------------- *)
val native_eq_tm =
  “∃c'. pan_to_target$compile_prog x64_target$x64_config
           x64_config$x64_backend_config traversalProg =
             SOME (traversalBytes, traversalBitmaps, c')”;

val traversal_compile_prog_native =
  save_thm("traversal_compile_prog_native",
           mk_oracle_thm "cake_native_bootstrap" ([], native_eq_tm));

(* ---------------------------------------------------------------------------
   Verification dump (tags + shapes) — written to bridge.out for the report.
   --------------------------------------------------------------------------- *)
val _ =
  let val os = TextIO.openOut "bridge.out"
      fun p s = TextIO.output (os, s)
  in
    p ("byteInts length = " ^ Int.toString (length byteInts) ^ "\n");
    p ("bmInts    length = " ^ Int.toString (length bmInts) ^ "\n");
    p ("bmInts values    = " ^ String.concatWith "," (map Int.toString bmInts) ^ "\n");
    p ("--- traversalBytes_length ---\n" ^ thm_to_string traversalBytes_length ^ "\n");
    p ("--- traversalBitmaps_length ---\n" ^ thm_to_string traversalBitmaps_length ^ "\n");
    p ("--- traversal_compile_prog_native (LAYER 2, oracle) ---\n"
       ^ thm_to_string traversal_compile_prog_native ^ "\n");
    let val (orc1, ax1) = Tag.dest_tag (Thm.tag traversal_compile_prog_native)
    in p ("LAYER2 oracles = [" ^ String.concatWith "," orc1 ^ "]  axioms = ["
          ^ String.concatWith "," ax1 ^ "]\n") end;
    let val (orc2, ax2) = Tag.dest_tag (Thm.tag traversal_pan_to_target_specialised)
        val c = concl traversal_pan_to_target_specialised
        val ante1 = c |> dest_imp |> #1 |> strip_conj |> hd
    in p ("--- traversal_pan_to_target_specialised (LAYER 1) ---\n");
       p ("LAYER1 oracles = [" ^ String.concatWith "," orc2 ^ "]  axioms = ["
          ^ String.concatWith "," ax2 ^ "]\n");
       p ("LAYER1 antecedent conj1 = " ^ term_to_string ante1 ^ "\n")
    end;
    (* fully-qualified constant identity (3-deep: Thy$Name) in the LAYER 2 term *)
    let val (_, body) = dest_exists native_eq_tm
        val (lhs, _) = dest_eq body
        val (f, args) = strip_comb lhs
        fun qn t = let val {Thy, Name, ...} = dest_thy_const t
                   in Thy ^ "$" ^ Name end
    in p ("LAYER2 head const   = " ^ qn f ^ "\n");
       p ("LAYER2 arg1 (asm)   = " ^ qn (el 1 args) ^ "\n");
       p ("LAYER2 arg2 (cfg)   = " ^ qn (el 2 args) ^ "\n");
       p ("LAYER2 arg3 (prog)  = " ^ qn (el 3 args) ^ "\n")
    end;
    p ("theory axioms (traversalBytesBridge) = "
       ^ Int.toString (length (axioms "traversalBytesBridge")) ^ "\n");
    TextIO.closeOut os
  end;

val _ = export_theory ();

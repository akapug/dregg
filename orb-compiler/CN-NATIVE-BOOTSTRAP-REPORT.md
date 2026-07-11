# CN REPORT — the SENSIBLE full-compilation path: the NATIVE bootstrapped `cake` binary compiles real serve stages to x64 in MILLISECONDS, certified by the bootstrap theorem — NOT by in-logic EVAL of the compiler

**Date:** 2026-07-10 · **Machine:** hbox (i9-12900) for the native `cake` + CakeML/HOL4 source.
**Native compiler:** `/home/hbox/r05/cake-x64-64/cake` (CakeML `ccfc23cbadf4…`, built 2026-06-18).
**Proof tree:** `/home/hbox/src/cakeml` at `ed31510b3` (2026-06-29) — the exact tree C1–C31 used.
This is the **COMPILER track** (HOL4/CakeML/Pancake), disjoint from the drorb cons-list Lean work.

---

## 0. TL;DR

The C-series compiled Pancake to machine code by **EVAL-ing the CakeML backend inside
the HOL4 kernel** — discharging `compile_prog_max c mc prog = (SOME (bytes,…),…)` by
`EVAL`. That is why "Rung 2" was a **1868-byte toy**: in-logic EVAL of the Pancake
backend (`pan_to_word ∘ word_to_word ∘ word_to_stack ∘ from_stack`) has no
`cv_compute` setup in this tree (C11 §3.3), so it is astronomically expensive and
does not scale to a real program.

**The fix, demonstrated here:** the native bootstrapped `cake` binary **is** the
verified compiler (proven once by the x64 bootstrap theorem `cake_compiled_thm`).
Running it on a real serve stage's `.pnk` produces the identical `bytes` in
**~7 milliseconds** — and their correctness comes from the **bootstrap theorem**,
not from re-EVAL-ing the compiler per program.

- **Scale win (measured):** `boundscan.pnk` (1694 B, the real C0/C10/C11 stage) →
  **10 340 B of x64 assembly in 0.007 s** (avg over 100 runs); `parseline.pnk`
  (3200 B) → 14 448 B in ~0.01 s. All seven real stages compile in **milliseconds**,
  and the output **assembles to a real ELF object** (`boundscan.o`, 8260 B of
  `.text`). In-logic EVAL of the same compile is the galactic-lifespan dead-end.
- **Correctness basis:** `cake_compiled_thm` (`x64BootstrapProof`) — the binary's
  machine semantics refines the verified compiler `compile` function ∘
  `compile_correct_eval` (`backendProof`). The `--pancake` path is exactly
  `compile_pancake` = `parse_topdecs_to_ast` (the **same verified parser** the
  C-series pins `…_is_parser_output` to) → `pan_compile` = `compile_prog_max`. So
  the native `bytes` are the verified backend's output, discharging the C11/C20
  Link-B antecedent **without in-logic EVAL**.
- **Verdict:** **Yes** — native-`cake` + bootstrap is the tractable full-compilation
  path. It is how CakeML is *meant* to be used, and it unblocks the compiler track
  from the in-logic dead-end. The honest residuals are (a) a version skew (binary is
  14 commits behind the proof checkout), (b) the bootstrap proof is an
  **upstream/CI** dependency not rebuilt locally, and (c) the "reflect the native
  bytes back into HOL as a literal" wiring is not yet mechanized.

---

## 1. The native compilation — a REAL (non-toy) stage, size + TIME (the scale win)

The stage: `boundscan.pnk` — the region/view bounds-check + rolling-digest byte scan,
the **exact** program the C0 model, C1 Link-A, C10, and C11 Link-B all target
(`/home/hbox/hol-c10/boundscan.pnk`, 1694 bytes; its own header even documents the
invocation). It contains a real `while` loop, FFI calls (`@load_vec`/`@report_vec`),
shaped loads (`lds`/`ld8`), an `if/else`, and word arithmetic — a genuine serve
fragment, not `tinyProg`.

**The command (my-hand-runnable, verbatim):**

```
ssh hbox@hbox.local
/home/hbox/r05/cake-x64-64/cake --pancake < /home/hbox/hol-c10/boundscan.pnk > boundscan.S
cc -c boundscan.S -o boundscan.o          # proves it is real machine code
```

**Measured (hbox):**

| stage `.pnk` | src bytes | x64 `.S` bytes | native compile time |
|---|---:|---:|---:|
| `boundscan`   | 1694 | 10 340 | **0.007 s** (avg / 100 runs) |
| `arenascan`   | 1538 | 10 277 | < 0.01 s |
| `arenawrite`  | 2478 | 12 527 | ~0.01 s |
| `collect`     | 2048 | 10 089 | < 0.01 s |
| `freelist`    | 1969 |  9 527 | < 0.01 s |
| `machinestep` | 1729 | 10 089 | < 0.01 s |
| `parseline`   | 3200 | 14 448 | ~0.01 s |

`boundscan.S` contains real x64 (`pushq %rbp` / `movq %rsp,%rbp` / `leaq cake_main(%rip)`
/ `imul` / `callq wcdecl(ffiload_vec)` …); `cc -c` assembles it to
`boundscan.o` = `ELF 64-bit … x86-64`, **8260 bytes of `.text`** (0x2044). This is
real, linkable machine code produced natively in single-digit milliseconds.

**Contrast with the dead end:** the C-series produced its machine bytes by
`EVAL`-ing `compile_prog_max` in the HOL4 kernel. `compile_prog_max` (below) is the
*entire* Pancake→x64 backend as a logical function; the Pancake backend has **no
`cv_compute`** in this tree (C11 §3.3), so evaluating it in-logic on a real program
is the "bazillions of GB / galactic lifespan" cost — which is exactly why Rung 2 was
capped at a 1868-byte toy. The native binary computes the *same function* in 7 ms.

---

## 2. The correctness chain — bootstrap, no in-logic EVAL (the honest part)

The subtle claim is **not** "native is fast" (that is trivially shown, §1). It is:
*the native bytes are certified as the verified compiler's output — by a theorem,
not by re-running the compiler in the kernel.* Here is the chain, with the actual
theorem/definition names in this tree.

### (a) The Pancake→machine-code compiler is proven correct — `pan_to_target_compile_semantics`

`/home/hbox/src/cakeml/pancake/proofs/pan_to_targetProofScript.sml:1257`, verified
(`check_thm` at line 2506). This is Link B. Its structure (abbreviated):

```
compile_prog_max c mc pan_code = (SOME (bytes, bitmaps, c'), stack_max) ∧
  <program-level side conditions on pan_code> ∧
  <standard x64 machine-state install package: backend_config_ok, mc_conf_ok,
   mc_init_ok, register/heap/bitmap layout, pan_installed bytes … ms …> ∧
  semantics_decls s «main» pan_code ≠ Fail ⇒
  machine_sem mc ffi ms ⊆ extend_with_resource_limit' …
    {semantics_decls s «main» pan_code}
```

where (line 1147)

```
compile_prog_max c mc prog =
  let prog = pan_to_word$compile_prog … prog in
  let (col,wprog) = word_to_word$compile … prog in
  let (bm,c',fs,p) = word_to_stack$compile … wprog in
    (from_stack … p bm, max)
```

i.e. `compile_prog_max` **is** the whole verified Pancake backend as a HOL function.
The C11 (`boundScanProg_linkB`) and C20 (`hash_machine_code`) reports already
instantiated this theorem at concrete emitted programs and discharged the
program-level side conditions against the *real* backend constants. **The one
antecedent that stayed a bound variable is** `compile_prog_max c mc prog = (SOME
(bytes,…),…)` — "until run to concrete bytes, `bytes` is a bound variable"
(C11 §3.3). Discharging it in-logic = EVAL-ing `compile_prog_max` = the dead end.

### (b) The native binary IS that verified compiler — `cake_compiled_thm` (the bootstrap)

`/home/hbox/src/cakeml/compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml`:

- `compiler64_compiled` (`x64BootstrapScript.sml:29`, via `eval_cake_compile_x64`) —
  the CakeML compiler, expressed as a CakeML source program `compiler64_prog`, has
  been compiled to the concrete x64 image that **is** the `cake` binary.
- `cake_compiled_thm` (`x64BootstrapProofScript.sml:83`) — composes
  `compile_correct_eval` (the backend correctness theorem,
  `backendProofScript.sml:4199`) applied to `compiler64_compiled` with the
  non-failure of the compiler's own source semantics. Net effect: **every behaviour
  of the running `cake` binary refines the semantics of `compiler64_prog`** — i.e.
  running the binary computes exactly the verified `compile` function.

The companion `compile_correct_applied` / `candle_top_level_soundness` in the same
file, plus `val _ = cake_compiled_thm |> check_thm`, are the "no cheats" gate.

### (c) The `--pancake` path is the verified function — same parser the C-series pins

`compiler/compilerScript.sml:283`, `compile_pancake_def` — what the binary runs under
`--pancake`:

```
compile_pancake asm_conf c input =
  case panPtreeConversion$parse_topdecs_to_ast input of      (* THE verified parser *)
  | INR errs => … ParseError …
  | INL funs =>
      case static_check funs of
      | (error e, …) => … StaticError …
      | (return (), warns) =>
          case pan_passes$pan_compile_tap asm_conf c funs of  (* = compile_prog_max *)
          | (SOME (bytes,data,c),td) => M_success (bytes,data,c) …
```

`parse_topdecs_to_ast` is **the identical parser** the C-series pins its emitted
programs to (`hashBytesProg_is_parser_output`: `parse_topdecs_to_ast "…" = INL
hashBytesProg`, C20 §2; `boundScanProg_is_parser_output`, C11 §2). So **leanc stays
out of the TCB on the native path too**: the binary parses the emitted text with the
verified parser, then runs `pan_compile` = `compile_prog_max`.

### The composition (why NO in-logic EVAL is needed)

Put (a)+(b)+(c) together. Run `cake --pancake < stage.pnk` → concrete `bytes₀`. Then:

- By **(c)+(b)**, those `bytes₀` are exactly `compile_prog_max c mc prog` for the
  parsed `prog` — the binary computed the verified backend function, certified by
  the bootstrap theorem. **No `EVAL` of `compile_prog_max` in the kernel.**
- Therefore the Link-B antecedent `compile_prog_max c mc prog = (SOME (bytes₀,…),…)`
  is discharged **on bootstrap authority** — you instantiate `bytes := bytes₀` from
  the native run instead of grinding the backend through the kernel.
- Link B (a) then delivers `machine_sem mc ffi ms ⊆ … {semantics_decls s «main»
  prog}`, and the C-series Link-A refinements rewrite `semantics_decls` into the Lean
  spec's result word — the C20 `hash_machine_code` shape.

So the correctness basis is **`compile_correct` ∘ `bootstrap`**, a *principled*
substitute for per-program in-logic EVAL. This is precisely the "x64 target-config
proof against the bootstrapped compiler" that C11-BACKEND §3 named as the intended
discharge.

---

## 3. Honest residuals — what native+bootstrap trusts, vs what is locally kernel-checked

Native-compiled bytes are **not** in-logic-proven bytes; their certification is a
*different and principled* basis. Precisely:

1. **Version skew (named dependency).** The binary is CakeML `ccfc23c` (2026-06-18);
   the proof checkout is `ed31510b3` (2026-06-29). `git merge-base --is-ancestor`
   confirms **`ccfc23c` is an ancestor of `ed31510`, 14 commits behind** — same
   lineage, binary slightly older. The `pan_to_target` proof, the parser, and the
   Link-A/Link-B theorems live at `ed31510`; the *binary's own* Pancake passes are
   the `ccfc23c` versions. For an airtight single-tree claim, either rebuild the
   binary at `ed31510` (re-bootstrap) or confirm the 14 commits don't touch
   `pancake/` or the backend. Until then the binary is a **released `cake`**, and its
   correctness rests on the CakeML release's bootstrap proof — a named dependency,
   *exactly like trusting an EverCrypt release build*.

2. **The bootstrap proof is upstream/CI, not rebuilt locally.**
   `x64BootstrapProofTheory.dat` is **not built** anywhere on hbox (only the
   `…Script.sml` is present) — building it is the multi-hour whole-compiler bootstrap
   the CakeML project runs in CI. Locally, `compile_correct_eval` (backend
   correctness, `backendProofTheory.dat`) **is** built. So the bootstrap *composition*
   `cake_compiled_thm` is a named upstream theorem we depend on, not one this tree
   re-checked. (This is normal CakeML practice — the bootstrap is proven once.)

3. **The bytes-reflection wiring is not yet mechanized.** Reading `bytes₀` off the
   native run and asserting `compile_prog_max … = SOME (bytes₀,…)` *as a closed HOL
   theorem* still needs the concrete byte list reflected back into HOL and the
   equality justified by the bootstrap (a `by-eval-on-the-binary` bridge). Nobody has
   wired that reflection step yet; in the C-series `bytes` remains a bound variable.
   The native path makes it **available** (instantiate on bootstrap authority) where
   in-logic EVAL made it **intractable** — but the mechanized bridge is a residual.

Everything else is unchanged from C11/C20: `[oracles: DISK_THM] [axioms:]`, 0 cheats;
the single FFI-oracle contract (`@load_vec`/`@report_vec`); the standard x64
machine-state install package. **None of it is leanc.**

---

## 4. The full-compilation plan — emit `.pnk` → native `cake` → bootstrap-certified code

The sensible path to compiling the **whole serve** (contrasted with the dead EVAL
approach):

```
Lean serve stage ──EmitPancake (proof-producing)──▶ stage.pnk
      │                                                  │
      │ (Link A: C1/C13/C16/C19/C20 refinements)         │ native, ~7 ms/stage
      ▼                                                  ▼
  Lean spec  ◀════ semantics_decls ════  cake --pancake  ──▶  stage.S ──cc──▶ machine code
                         ▲                                          │
                         └──── Link B: pan_to_target_compile_semantics
                              instantiated at parse_topdecs_to_ast(stage.pnk),
                              bytes discharged by cake_compiled_thm (bootstrap),
                              NOT by in-logic EVAL of compile_prog_max
```

- **Emit.** `Dsl/EmitPancake.lean` is the proof-producing Lean→Pancake generator
  (`emitRegion : RegionSpec → PFun` reproduces `boundscan`; total, core-Lean,
  `#print axioms` empty). It drives the loop-free fragment + the stage bodies. The
  emission surface is the honest subset (`Var/Const/@base`, `+ * < &`, `lds/ld8`,
  `var/assign/if/while/st/@ffi/return`) — the operators C0/C1 exercised and proved.
- **Native compile.** `cake --pancake < stage.pnk` — milliseconds, §1.
- **Certify.** Link B at `parse_topdecs_to_ast(stage.pnk)` (leanc out — same verified
  parser, §2c), `bytes` from the native run on bootstrap authority (§2), Link-A
  refinement to the Lean spec (the C20 `hash_machine_code` template — closed
  end-to-end for the `Cache.hashBytes` fold).

**Why in-logic EVAL never scaled (the contrast):** it discharges the *same* Link-B
`bytes` antecedent by evaluating `compile_prog_max` (the full backend) in the HOL4
kernel. No `cv_compute` for the Pancake backend in this tree ⇒ super-linear kernel
term blow-up ⇒ the 1868-byte toy ceiling. The native binary replaces that single
antecedent's discharge with a 7 ms run + a one-time bootstrap theorem.

**The gap to a full serve compilation** (three concrete items, none is leanc, none is
the backend metatheory):

1. **Translation coverage (Link A).** The C-series has closed Link A for the fold
   family (`hashBytes` end-to-end, C20) and the loop-free decisions (bounds, CORS,
   sec-headers, ipfilter, JWT, C11/C18/C25–C31); the **loops in the remaining stages**
   (arena scan/write, parseline, freelist) each still need their `While`-invariant +
   FFI-trace refinement (C11 §4, the named front-end residual). `mk_wrapper` as a
   reusable fold-e2e generator is the C20 §5 residual that makes these cheap.
2. **The `.pnk`→native bytes-reflection bridge** (§3.3) — mechanize "the native run's
   bytes discharge Link B on bootstrap authority" as a repeatable step, so each
   stage's end-to-end theorem instantiates concrete `bytes` instead of a variable.
3. **Runtime-install antecedents.** The standard x64 machine-state install package
   (`pan_installed`, register/heap layout) + the per-stage FFI-oracle contract
   (`@load_vec`/`@report_vec`) — discharged in a full end-to-end by the x64
   target-config proof; the runtime that places the image and drives the FFI is the
   `basis_ffi.c` + per-stage `*_ffi.c` shim (present alongside the binary).

---

## 5. Verdict

- **Is native-`cake` + bootstrap the tractable full-compilation path?** **Yes.** It is
  how CakeML is designed to be used: the compiler is proven correct **once** (the x64
  bootstrap, `cake_compiled_thm`), and thereafter every program is compiled by
  *running the verified binary* — milliseconds — with correctness inherited from the
  bootstrap theorem, never from re-EVAL-ing the compiler. Measured here: real serve
  stages (1.5–3.2 KB `.pnk`, with loops + FFI) → 9.5–14.4 KB of assemblable x64 in
  **~7 ms each**.
- **What it unblocks.** The compiler track was stuck on the in-logic EVAL dead-end —
  the reason Rung 2 was a 1868-byte toy. The native path removes that ceiling: the
  Link-B `compile_prog_max = SOME(bytes,…)` antecedent, previously an intractable
  kernel EVAL, is now a 7 ms native run discharged on bootstrap authority. Every real
  stage compiles today; the whole serve becomes a *translation-coverage* problem
  (finish the loop Link-A refinements + the bytes-reflection bridge), **not** a
  compiler-cost problem.
- **The honest boundary.** Native-compiled ≠ in-logic-proven bytes. The certification
  is `compile_correct ∘ bootstrap` — principled, but it rests on (a) the CakeML
  release's bootstrap proof (upstream/CI, not rebuilt locally), (b) a 14-commit
  version skew between the binary (`ccfc23c`) and the proof checkout (`ed31510`),
  same lineage, resolvable by a re-bootstrap, and (c) an unmechanized bytes-reflection
  step. State all three; none is leanc, and none reintroduces the EVAL cost.

## 6. Reproduction (hbox)

```
ssh hbox@hbox.local
CAKE=/home/hbox/r05/cake-x64-64/cake
$CAKE --version                                   # CakeML ccfc23c…, x64
$CAKE --help | grep -A1 pancake                   # --pancake takes a pancake program
$CAKE --pancake < /home/hbox/hol-c10/boundscan.pnk > boundscan.S   # ~7 ms
cc -c boundscan.S -o boundscan.o && size boundscan.o               # ELF, 8260 B .text
# theorem names:
#  Link B  : pancake/proofs/pan_to_targetProofScript.sml:1257  pan_to_target_compile_semantics
#  backend : compiler/backend/proofs/backendProofScript.sml:4199  compile_correct_eval
#  bootstrap: compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml:83  cake_compiled_thm
#  --pancake route: compiler/compilerScript.sml:283  compile_pancake_def (parse_topdecs_to_ast → pan_compile)
```

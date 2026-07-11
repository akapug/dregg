# C20 REPORT — the FIRST real serve FOLD is CLOSED END-TO-END: the deployed cache-key hash `Cache.hashBytes` now has a single kernel-checked theorem `spec → machine code`

Every observable behaviour of the x64 machine code CakeML emits for the fold is the
one terminating trace whose reported result word is EXACTLY `n2w (hashBytesN input)`
= the deployed Lean `Cache.hashBytes input` mod 2^64. `hashBytesProg` is the
CakeML-verified parser's output (`parse_topdecs_to_ast "…fun main() {…}" = INL
hashBytesProg`), so **leanc is fully out of the TCB**; the wrapper's `Term.subst`
demonstrably fires against a genuine parser subterm (the emitted `While` IS the
proven loop core). `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats, `~/hol-c20`
green on hbox (full `Holmake` exit 0, incl. the `verifyHash20` audit theory).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) for HOL4/CakeML.
**HOL4 Trindemossen-2 stdknl, CakeML `ed31510b3`** — the exact tree C1–C19 used.
**Dir:** `docs/engine/probes/compiler/hol-c20/` (built on hbox `~/hol-c20`). Sibling
agents own `hol-c16..c19` (done); C20 stayed out.

---

## 0. What this probe answers

C19 closed the loop **CORE** of the deployed cache-key hash (`hashLoop_refines`: the
emitted `While foldGuard hashBody` computes `n2w (hashBytesN input)`, C16 schema +
~8-line fill-in). C19 §5 scoped what remained to the whole-program
`machine_sem = Terminate Success (…)` theorem: the **fuel-budgeted whole-program
wrapper**, plus **emit+parse** the fold so the end-to-end pins to the *parsed*
program (leanc out of TCB). This is Gate A's critical path — the first fold e2e
unblocks every downstream serve fold toward compiling the whole serve.

**Verdict up front: the first real serve fold is CLOSED end-to-end.** The wrapper
landed as a **bespoke hand-adaptation of the C13 boundScan loop-wrapper stack**
(551 new meaningful lines), *not* via a reusable `mk_wrapper` generator — that
generalization remains the residual (§5). The proof-engineering friction that
surfaced was entirely at the **composition seam**, not the metatheory (§4).

## 1. THE closed end-to-end theorem

`hash_machine_code` (theory `hashEndToEnd`), verbatim `show_tags`:

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ (compile_prog_max c mc hashBytesProg = (SOME (bytes,bitmaps,c'),stack_max) ∧
   s.code = FEMPTY ∧ s.locals = FEMPTY ∧ s.globals = FEMPTY ∧
   FDOM s.eshapes = FDOM (get_eids (functions hashBytesProg)) ∧
   backend_config_ok mc.target.config c ∧ mc_conf_ok mc ∧
   mc_init_ok mc.target.config c mc ∧ mc.target.config.ISA ≠ Ag32 ∧
   … (the standard pan_to_target install package) … ∧
   pan_installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names
     (heap_regs c.stack_conf.reg_names) mc c'.lab_conf.shmem_extra ms
     (wlab_wloc ∘ s.memory) s.memaddrs s.sh_memaddrs) ∧
   hashFFI input s ∧ (∃K. 0 < K ∧ LENGTH input < K) ⇒
   ∃loadEv rb.
     machine_sem mc ffi ms ⊆
     extend_with_resource_limit'
       (option_lt stack_max (SOME (FST (read_limits mc.target.config c mc ms))))
       {Terminate Success
          (s.ffi.io_events ++ loadEv ++
           [IO_event (ExtCall «report_vec»)
              (word_to_bytes (n2w (hashBytesN input)) F) rb])}
```

Read literally: *for any machine state into which CakeML's `pan_to_target` has
installed the x64 code compiled from `hashBytesProg`, every behaviour of the
running machine is a single `Terminate Success` whose final FFI event reports the
8-byte little-endian word `n2w (hashBytesN input)`* — the deployed hash the cache
key is built from, mod 2^64. `hashBytesN input = FOLDL (\a x. a*257 + x + 1) 0
input` is the drorb `Cache.hashBytes` re-declared over nats (byte-identical to
`Reactor/Stage/Cache.lean:115`).

The result word is delivered by the `@report_vec` FFI, which reads the fold
accumulator the program `st`ores at `ctrl+8` — the "buffer-write equivalent" the
charge allowed. `hashFFI` is the single named FFI-oracle contract (`@load_vec`
stages the control block + arena; `@report_vec` emits the result word); it is the
only trusted assumption and it is **not** leanc.

## 2. leanc is OUT of the TCB — the subject is the parser's output, and the surgery fires

`hashBytesProg_is_parser_output` (theory `hashBytesLinkBInst`, via the
`panAutoLib.mk_linkB` generator, C11/C14/C18 procedure):

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ parse_topdecs_to_ast
    "…// the deployed cache-key hash as Pancake …
     fun main() {
       var ctrl = @base;
       var base = ctrl + 32;
       @load_vec(ctrl, 16, base, 4096);
       var len = lds 1 ctrl;
       var acc = 0;  var i = 0;  var b = 0;
       while i < len { b = ld8 (base + i); acc = acc * 257 + b + 1; i = i + 1; }
       st ctrl + 8, acc;
       @report_vec(ctrl + 8, 8, ctrl, 8);
       return 0;
     }" = INL hashBytesProg
```

So `hashBytesProg` — the subject of the whole end-to-end — is exactly what the
**CakeML-verified Pancake parser** produces on `hashbytes.pnk`. leanc never enters:
the emitted source is checked by the verified parser, not trusted.

**The surgery genuinely fires.** `hashMainBody` is built by `Term.subst`-ing the
proven loop-core constant `hashLoopCore` into the parsed `main` body at the
position of the emitted `While`. A machine check confirms the substitution landed
against a real parser subterm:

```
NUM hashLoopCore subterms in hashMainBody = 1   (at type :64 panLang$prog)
```

`hashWrapperLinkAScript.sml` raises `Fail "hashLoopCore substitution did not fire"`
at build time unless `Term.free_in hashLoopCore body`; the theory builds, so the
parsed `While` **is** the constant whose refinement C19/C20 proved — the emit and
the proof are pinned to the same term, not merely the same syntax. (The emitted
body is the C19 `hashBody` modulo three transparent `Annot`s the parser inserts;
`Panop Mul` for `*`, 3-ary `Op Add` for `+`, `LoadByte` byte read — all matched.)

## 3. The chain (each `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats)

| theory | headline theorem | role |
|---|---|---|
| `hashBytesLoop` (C19, carried) | `hashLoop_refines`, `hashBytes_word` | word fold = `n2w (hashBytes …)` + Nat→word homomorphism |
| `foldLoopSchema` (C16, carried verbatim) | `foldLoop_refines` | program-agnostic fold-loop schema |
| `hashCore` | `hashLoopCore_refines` | **the real fold core on the PARSED body** `hashBodyA` (~8-line `hashBodyA_step` fill-in) → `n2w (hashBytesN input)` |
| `frameProbe` | `While_frame` | `ctrl` locals-frame is preserved across the loop |
| `hashWrapperLinkA` | `hashFFI_def`, `hashMainBody_def` | the FFI-oracle contract + the parsed `main` with `hashLoopCore` folded in |
| `hashMainRefine` | `hashMainBody_refines` | whole `main` body → `Return 0` with the result word staged (the C13 `boundScanMainRefine` analogue) |
| `hashSem` | `main_semantics` | fuel-budgeted clock-lift `Call main → Terminate Success trace` (C13 `boundScanSem` analogue) |
| `hashInstall` | `hashBytesProg_semantics_decls` | decls-level whole-program Link A |
| `hashBytesLinkBInst` | `hashBytesProg_linkB`, `…_is_parser_output` | CakeML backend Link B (via `mk_linkB`) |
| `hashEndToEnd` | **`hash_machine_code`** | **Link A ∘ Link B = spec → machine code** |

`hashLoopCore_refines`, verbatim:

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ∀input bs s.
    foldInv input bs 0 0w s ∧ LENGTH input ≤ s.clock ⇒
    ∃s'. evaluate (hashLoopCore,s) = (NONE,s') ∧
         FLOOKUP s'.locals «acc» = SOME (ValWord (n2w (hashBytesN input)))
```

**Wrapper stages** (each a hand-adaptation of its C13 counterpart, with the C19-§5
changes made concrete):

- **loop core → framed** (`hashCore`): `While_frame` (reusable: a `While` whose body
  keeps local `v` keeps `v`) gives the `«ctrl»` locals-frame the post-loop store needs.
- **WrapperLinkA** (`hashWrapperLinkA`): the `hashCtrlStaged` **array-staging** clause
  (`memRel input (ba+32) s`, the arena the loop reads via `base`) replaces the
  loop-free N-scalar reads; `hashFFI` contract; `hashMainBody` surgery. One
  convention friction: the C19 core pins the arena to local `base` while the C13
  wrapper convention pins `base` to the control block — resolved by naming the
  control pointer `ctrl` (arena = `ctrl+32` = `base`), so the **C19 core body drops
  in verbatim** and only three tiny `ctrl`-keyed eval/store lemmas are added.
- **MainRefine** (`hashMainRefine`): the clock-budget antecedent `LENGTH input ≤
  s0.clock`; applies the fuel-budgeted `evaluate_hashLoopCore_framed`; result read
  from `acc`, stored at `ctrl+8`.
- **Sem** (`hashSem`): `call_main_run`/`main_semantics` carry `LENGTH input ≤
  (dec_clock …).clock` and the clock witness (C13 `clock := SUC budget`, not the
  loop-free `:= 1`).

## 4. What actually cost proof-engineering — the composition seam, not the metatheory

The C19 §5 forecast ("mechanical, no new metatheory") held for the **shape** of
the wrapper — every step exists in the C13 boundScan stack. The friction was
entirely in **closing the final composition** `hash_machine_code`, and it is worth
recording because it recurs for every fold e2e:

1. **`metis_tac []` / `DECIDE_TAC` drown in the whole-machine install package.** The
   `semantics_decls` antecedent needs `∃K. 0 < K ∧ LENGTH input < K`. Handing it
   (or the `SUC (LENGTH input)`-witnessed `0 < SUC n ∧ n < SUC n`) to
   `metis`/`DECIDE` with ~30 `pan_installed` / `compile_prog_max` / word-arith
   assumptions in scope makes the first-order / Presburger search fail
   (`FOL_FIND: no solution found`, resp. `DECIDE_TAC: NO_TAC`) even though the goal
   is trivially true; `simp` fails differently (it normalizes `SUC n → n+1`, so
   `LESS_SUC_REFL` can no longer fire). **Fix:** discharge the side-condition from a
   **clean** helper `exists_big : ⊢ ∀n. ∃K. 0 < K ∧ n < K` (proved away from the
   polluted context, where `DECIDE` is trivial) via `MATCH_ACCEPT_TAC`, which
   ignores the assumption clutter entirely. This is a reusable pattern for every
   whole-program composition: prove the small side-conditions in a clean context,
   then `MATCH_ACCEPT`.
2. **`match_mp_tac hashBytesProg_linkB` closes by `first_assum ACCEPT_TAC` alone.**
   The Link-B package's antecedent-only variables (`bytes, bitmaps, c', cbspace,
   data_sp`) are all present as hypotheses (they arrived via the goal's own package
   conjuncts), so no existential-witness gymnastics are needed once the package is
   split — but the `metis` fallback must be dropped, or it re-drowns.

No new axioms, no new metatheory — the deployed-serve friction is a
**tactic-hygiene** lesson about assumption pollution at the whole-machine seam.
(The final composition, `hashEndToEnd`, is 50 meaningful lines once this is right.)

## 5. Is `mk_wrapper` now a fold-e2e generator? — NO; that is the honest residual

**The wrapper is a bespoke hand-adaptation of the C13 template, not a generator
call.** `grep mk_wrapper *Script.sml` is empty; `panWrapperLib.mk_wrapper` (carried,
482 lines) is **not invoked** anywhere in C20. Only the **Link-B** step is a
generator (`panAutoLib.mk_linkB`, 9-line call site). The whole-program **Link-A**
wrapper was written per-file by hand (`hashMainRefine` 171, `hashSem` 63,
`hashInstall` 41, `hashWrapperLinkA` 89, `frameProbe` 35, `hashEndToEnd` 50), each
mirroring its C13 counterpart. (Because `mk_wrapper` was not touched, the C14/C15
loop-free regression is trivially intact — those wrappers live in `hol-c16` and are
untouched.)

So the C19 §5 "extend `mk_wrapper` into a reusable generator" charge is **not
landed**. What IS proven is the stronger, concrete thing it was meant to validate:
**a real serve fold does close spec→machine-code by this stack**, and the stack is
now a known-good template whose four stages are already parameterized by ⟨core-framed
thm, `ctrlStaged`, FFI contract, `mainBody`, spec word, clock-budget var⟩. Turning it
into a function `mk_fold_wrapper { core=…, ffi=…, prog=… }` that emits the six
theories is the next mechanical step — the composition tactic (§4) is the fixed
part.

**Line budget (new C20 hand-code, meaningful non-comment lines):**

| component | lines |
|---|---:|
| loop core on the parsed body (`hashCore`, incl. ~8-line `hashBodyA_step`) | 93 |
| whole-program wrapper residual (`hashMainRefine`+`hashSem`+`hashInstall`+`hashWrapperLinkA`+`frameProbe`+`hashEndToEnd`) | 458 |
| — of which the final composition (`hashEndToEnd`) | 50 |
| Link B (generator call, `hashBytesLinkBInst`) | 9 |
| **total NEW C20** | **551** |

(Carried verbatim, not re-counted: the C16 schema `foldLoopSchema` 288, C19 core
`hashBytesLoop` 157, C15 `panAuto` 124, C14 `c14Generic` 215, libs 607.) For
scale: C13's single bespoke boundScan loop-wrapper was ~629 lines *for the loop
Link-A proof alone*; C20 delivers the **full** fold e2e (core + wrapper + LinkB +
composition) in 551, because the loop core reuses the C16 schema (~8-line fill-in)
and Link B is a generator.

## 6. Trust ledger (unchanged from C13–C19; none of it is leanc)

Every C20 theory is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats.
`DISK_THM` is the benign CakeML disk-export tag — no `cheat`, no `mk_thm`, no
axiom, identical footing to C11–C19. The end-to-end rests only on: the CakeML
backend correctness (Link B), the C16 fold schema (reused verbatim), the C19
Nat→word homomorphism, and the **single named FFI-oracle contract `hashFFI`**
(`@load_vec` / `@report_vec`). leanc is out: the subject is the verified-parser
output and the wrapper surgery fires against a real parser subterm (§2).

## 7. Path to composing `cacheEmptyStage` (`keyOf` = two `hashBytes` folds + the C18 `isFresh` gate)

`cacheEmptyStage` (stage 4 of `deployStagesFull2`) looks up a key built by `keyOf`
(`Cache.lean:118`), which runs `hashBytes` over the method bytes **and** the target
bytes, then a cache freshness check. With C20 the fold e2e is a template; the
compose needs:

1. **Sequence two fold cores.** `keyOf` = `{ method := hashBytes req.method,
   uri := hashBytes req.target, … }`. Each `hashBytes` is now C20's closed core;
   the compose is two `hashLoopCore` invocations over two arena regions (distinct
   `base`/`ctrl` offsets, distinct result slots) threaded through one `main` — a
   `Seq` of two framed loops, each preserving the other's `acc` via the
   `While_frame` lemma already in `frameProbe`. No new fold metatheory.
2. **The C18 `isFresh` scalar gate.** C18 closed the loop-free freshness decision;
   sequencing it after the two folds is scalar-after-fold (both cores are `noFFI`,
   so the trace threading is the same forward-wrap).
3. **The generator (§5) makes this cheap.** Once `mk_fold_wrapper` exists, the
   two-fold `keyOf` body is: two generator calls + one scalar gate + one
   composition — the residual that C20 quantifies but does not yet mechanize.

## 8. Verdict

- **Is the first real serve fold closed END-TO-END?** **Yes.** `hash_machine_code`:
  `machine_sem mc ffi ms ⊆ extend_with_resource_limit' … {Terminate Success (…
  word_to_bytes (n2w (hashBytesN input)) F …)}`, `[oracles: DISK_THM] [axioms: ]`,
  hyps = 0, 0 cheats, over the **parser-output** `hashBytesProg` (leanc out),
  green on hbox.
- **Is `mk_wrapper` now a fold-e2e generator?** **No** — the wrapper is a bespoke
  551-line hand-adaptation of the C13 template; only Link B is a generator. The
  generator extension is the precisely-scoped residual (§5).
- **Total hand-proof lines?** **551 new meaningful lines** (core-on-parsed-body 93 +
  whole-program wrapper 458, of which the final composition is 50), reusing the
  C16 schema and C19 homomorphism verbatim.
- **Friction found?** Not metatheory — **assumption pollution at the whole-machine
  composition seam** (`metis`/`DECIDE`/`simp` all drown among the `pan_installed`
  package); fixed by discharging side-conditions from a clean helper (`exists_big`)
  via `MATCH_ACCEPT_TAC`. Reusable for every whole-program composition.
- **Path to `cacheEmptyStage`?** Two C20 fold cores sequenced (framed by the
  existing `While_frame`) + the C18 `isFresh` scalar gate; cheap once the §5
  generator lands.

## 9. Files (`docs/engine/probes/compiler/hol-c20/`, built on hbox `~/hol-c20`)

- `hashbytes.pnk` — the emitted Pancake source (the fold + control-block I/O).
- `hashBytesLinkBInstScript.sml` — Link B + `hashBytesProg_is_parser_output` (`mk_linkB`).
- `hashCoreScript.sml` — the real fold core on the **parsed** body `hashBodyA`
  (~8-line `hashBodyA_step`), `hashLoopCore_refines`, the `ctrl`-frame corollary.
- `frameProbeScript.sml` — `While_frame` (loop preserves the `ctrl` local).
- `hashWrapperLinkAScript.sml` — `hashFFI` FFI-oracle contract + `hashMainBody`
  (parsed `main` with `hashLoopCore` substituted; the surgery-fired assertion).
- `hashMainRefineScript.sml` — `hashMainBody_refines` (whole `main` → `Return 0`).
- `hashSemScript.sml` — `main_semantics` (fuel-budgeted clock-lift).
- `hashInstallScript.sml` — `hashBytesProg_semantics_decls` (decls-level Link A).
- `hashEndToEndScript.sml` — **`hash_machine_code`** (the final composition).
- `verifyHash20Script.sml` — the machine-checked audit theory (prints all headline
  theorems with `show_tags`; builds green in the chain).
- carried verbatim: `foldLoopSchemaScript.sml` (C16), `hashBytesLoopScript.sml`
  (C19), `panAutoScript.sml` (C15), `c14GenericScript.sml` (C14),
  `panWrapperLib.sml` / `panAutoLib.sml` (libs).
- `Holmakefile` — includes the CakeML pancake/semantics/proofs dirs; build with
  `CAKEMLDIR=/home/hbox/src/cakeml`.

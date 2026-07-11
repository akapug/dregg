# RUNG 2 — first CONCRETE verified-silicon bytes for tinyProg

Status: **register allocation discharged to concrete + 1868 concrete x64 bytes
produced**, both as real `[oracles:DISK_THM][axioms:] hyps=0` theorems (cv_compute
is fully proof-producing — no extra cv oracle). The single remaining gap to a
fully-assembled `compile_prog_max tinyProg = SOME(<bytes>)` theorem is the
`_x64 = generic` bridge chain (characterised below).

Work done on hbox in `~/hol-c33` (cv theories prebuilt). Reproducer: `phaseD.sml`
(clean byte producer) and `phaseB.sml` (reg-alloc step). Source: `tiny.pnk`.

## The unlock (what the prior lane and the 5-step plan both got wrong)

Two premises in the 5-step plan are false, and the real path is different:

1. **Pre-alloc passes are NOT EVAL-reducible.** `word_common_subexp_elim`
   (word_cse) stalls under EVAL: it uses `balanced_map$lookup/insert` keyed by
   `listCmp` (the `instrs_mem`/`loads_mem` maps). It leaves ~21 residual
   lambdas; everything from `copy_prop` on inherits the residue. Adding
   balanced_map defs to the compset makes it worse (147 residuals). So the graph
   slice cannot be computed by EVAL. (`reg_alg:=0` also never discharges —
   with an empty `col_oracle` word_alloc still calls the real allocator and
   EVAL leaves `reg_alloc_aux ... M_success/M_failure` symbolic. This is why the
   prior `tiny_frontprog_eq` was symbolic and its proof failed.)

2. **cv_eval/cv_eval_raw CANNOT take a word-containing term as INPUT.**
   `cv_eval ``(n2w 65):word64``` → `Encountered non-cv constant: (:64)`. The
   real bootstrap avoids this by running the *whole* pipeline as one cv
   computation from a word-free dec-list; words only appear internally / as
   outputs (converted back via `from_to_word`).

**The actual unlock: `cv_trans_deep_embedding` DOES handle a word program —
provided `wordsLib` is loaded so EVAL reduces `from_word (n2w k) = Num (w2n k)`.**
Without `wordsLib` the deep embedding leaves `w2n (n2w k)` un-reduced and reports
a spurious "non-cv constant: n2w". With it, the word program becomes a cv
constant and cv_eval_raw runs. The config must be **inlined** (its 15 `ARB`
fields choke deep-embedding but are fine inlined — cv_rep handles them lazily,
exactly as `eval_cake_compileLib` passes the EVAL'd config literal).

## Recipe (all verified on hbox)

```
load wordsLib (critical), backend_x64Theory, backend_x64_cvTheory, cv_transLib,
     cv_typeTheory, reg_allocComputeLib, pan_to_wordTheory, ...
TINY_PW = pan_to_word$compile_prog x64_config.ISA tinyProg      (EVAL; monomorphic :64)
cv_trans_deep_embedding EVAL TINY_PW_def                        (OK, needs wordsLib)
# STEP 1 (graphs, config INLINED literal — not deep-embedded):
graphs = cv_eval_raw ``FST (to_livesets_0_x64 (<x64cfg-literal>, TINY_PW, LN))``   (termsize 808)
oracle = reg_allocComputeLib.get_oracle_raw reg_alloc.Irc graphs
# STEP 2 (reg-alloc discharge — the crux):
cv_eval ``word_to_word_inlogic_x64 <|reg_alg:=0; col_oracle:=oracle|> TINY_PW``
   = SOME (col, wprog)    is SOME=T   reg_alloc_aux=FALSE   (find_term verified)
# STEP 3 word_to_stack (EVAL, clean, residual_abs=0):
word_to_stack$compile x64_config F wprog = (bm,c',fs,p)
# STEP 4 encoder (deep-embed stackprog+bm, inline config):
enc = cv_eval_raw ``from_stack_x64 <x64cfg> LN tiny_stackprog tiny_bm``
enc |> CONV_RULE (RAND_CONV EVAL)   = SOME([1868 concrete bytes], ..., c', ...)
   reg_alloc_aux=FALSE   is SOME=T
```

The IRC oracle computed (a valid colouring, no allocation left in the logic):
- fn 64 (InitGlobals): `SOME {0↦0}`
- fn 65 (main): `SOME {0↦0; 2↦1; 4↦2; 6↦3; 8↦4; 13↦0; 17↦1; 21↦1; 25↦2; 37↦1; 45↦4; 49↦2; 55↦9; 61↦0; 65↦1}`

## The bytes (first non-fake verified silicon)

- length: **1868 bytes**, all concrete numerals in [0,255]
- first 8: `48 89 C8 48 29 F0 48 C1`  (mov rax,rcx; sub rax,rsi; shr rax,4 …)
- last 8:  `31 FF 49 83 C6 10 FF E0`  (xor edi,edi; add r14,16; jmp rax)
- byte sum: 195105
- sha256:  `5f102422151389f5e0868893c04da9c65f327585ac145fccd5bc2aa449acd393`
- full hex: `tiny_bytes.hex`

Tags of both the reg-alloc theorem and the encoder theorem:
`[oracles:DISK_THM][axioms:] hyps=0`. No cv oracle, no axioms, no hypotheses.

## Remaining gap: `_x64` → generic bridge (to assemble compile_prog_max)

`compile_prog_max` uses `word_to_word$compile` and `backend$from_stack`. The cv
results are over the `_x64` in-logic functions. The generic bridge theorems
`word_to_word_inlogic_thm` and `from_stack_thm` are stated for the GENERIC
functions, so we need:
- `word_to_word_inlogic_x64 wc p = word_to_word_inlogic x64_config wc p`
- `from_stack_x64 c names p bm = backend_asm$from_stack x64_config c names p bm`

`backend_asmLib.define_target_specific_backend` PROVES these internally
(`asm_spec`'s `d` equations `X x64_config = X_x64`) but does NOT export them —
the `[allow_rebind]` unfolded-body `_x64_def`s overwrite the bridge equations, so
only `compile_cake_x64_thm` survives (and that is dec-list only).

**Continuation (precise):** re-derive the bridges BOTTOM-UP, one small lemma per
function (`remove_labels_loop`, `remove_labels`, `compile_lab`, `lab_to_target`,
`from_lab`, `from_stack`; and `inst_select`, `get_forced`, `word_alloc_inlogic`,
`each_inlogic` [needs induction on the prog list], `word_to_word_inlogic`), each
proved by `rewrite[X_x64_def, X_def]` + EVAL of ONLY the x64_config accessors.
Do NOT use `DEPTH_CONV EVAL` over the whole goal — that OOMs (77 GB observed) on
the encoder terms. Then: word_to_word_inlogic_thm → `word_to_word$compile … =
(col,wprog)`; from_stack_thm → `backend$from_stack … = SOME(bytes,bm1,c1)`;
chain into `compile_prog_max tinyC mc tinyProg` (hyp `mc.target.config =
x64_config`), and `tiny_stackmax` via EVAL of `max_depth`. That closes
`compile_prog_max tinyC mc tinyProg = (SOME(<1868 literal bytes>,bm1,c'),max)`
with reg_alloc_aux-free, and feeds `pan_to_target_compile_semantics` (`c'` is the
back-translated config the `pan_installed` hypothesis needs).

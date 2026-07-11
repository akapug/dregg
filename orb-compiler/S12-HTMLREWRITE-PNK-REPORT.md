# S12-HTMLREWRITE-PNK — the streaming-tokenizer body-rewrite loop, as a `.pnk`

**Date:** 2026-07-10 · **Machine:** hbox (24-core, io_uring) · **Compiler:**
`/home/hbox/r05/cake-x64-64/cake` (CakeML x64 bootstrap) · **Working dir (hbox):**
`/home/hbox/htmlrewrite/`.
**Closes:** the residual named in `FUSED-SERVE-PNK-REPORT.md` §4/§5.1 and
`PNK-MANIFEST.md` §4 item 1 — *"**S12 `HtmlRewrite`** … has **no `.pnk` at all** and is
the streaming-tokenizer body-rewrite loop residual."* S12 was the last uncomposed
`deployStagesFull2` stage with no Pancake image.
**Owned files (DreggNet tree):** `docs/engine/probes/compiler/htmlrewrite.pnk`,
`docs/engine/probes/compiler/htmlrewrite_ffi.c`, and this report.

---

## 0. TL;DR — measured, verified by *running* it against real Lean ground truth

- **The S12 tokenizer is now a Pancake while-loop.** `htmlrewrite.pnk` (`rewrite_html`)
  walks the response body buffer one byte at a time, carrying the deployed `feedF`
  2-mode state (`text=0` / `tag=1`) and the two transition bytes (`<`=60 opens a tag,
  `>`=62 closes it), emitting the tag-stripped body. This is the loop the manifest said
  had never been expressed.
- **Native-compiles clean:** `cake --pancake < htmlrewrite.pnk` → **0 parse errors**,
  **best-of-20 = 7 ms**, ASM 11 264 B, **CODE = 1 348 B** of emitted x64 machine-code
  operands.
- **Assembles to a valid ELF object:** `cc -c htmlrewrite.S -o htmlrewrite.o` →
  `ELF 64-bit LSB relocatable, x86-64`, `.text = 8 260 B`, `.data = 40 B`, md5
  `f145d96dfcb5d58009dfc27f567c14f0`.
- **Links AND runs end-to-end:** `cc -O2 htmlrewrite.S basis_ffi.c htmlrewrite_ffi.c -o
  htmlrewrite -lm` → running PIE executable.
- **Byte-identical to the DEPLOYED `rewriteBytes` — differentially verified.** 8 bodies
  driven through the executable produce **exactly** the bytes the real Lean
  `Reactor.Stage.HtmlRewrite.rewriteBytes` computes (ground truth pulled from `lake env
  lean` `#eval`, §3), including the subtle cases (`>` in text is kept; `<<>>text` → `>text`).

**Honest fidelity (stated precisely — this is a FAITHFUL port, not a skeleton):** the
`.pnk` computes the **deployed rewriteBytes byte-transform exactly** on every input — it
is a faithful port of the stage's **observable semantics**. It is **not** a
transliteration of the Lean engine's internal data structures: it does not materialise
the `Token` list or the `curRev` buffer. It does not need to — `renderTok` maps
`text → bytes`, `tag → []`, so the observable output is *exactly* the text-mode bytes,
which is a 2-state byte filter. The dense refinement (`rewriteBytesDense_refines`) already
proved the token accumulator is an implementation detail of the **same byte function**,
so collapsing it loses nothing observable. Fidelity in one line: **faithful to the
deployed rewriteBytes semantics (differentially validated against Lean), re-expressed as
the equivalent streaming filter — no representation-level replica is claimed, and it is
not a shaped shell.**

---

## 1. The tokenizer, and why the loop is the whole transform

Ground (drorb):

- `HtmlRewrite/Basic.lean` — the streaming machine `feedF : FState → Byte → FState`.
  In `text` mode, `<` (60) *flushes the text run and opens a tag*; any other byte extends
  the text run. In `tag` mode, `>` (62) *closes the tag*; any other byte extends the tag.
- `Reactor/Stage/HtmlRewrite.lean` — `rewriteBytes bs = rewriteState (tokenizeFast bs)`,
  where `renderTok (Token.text b) = b` and `renderTok (Token.tag _) = []`, and
  `rewriteState` appends a trailing `Mode.text` run but **drops** a trailing `Mode.tag`.
- `Datapath/HtmlRewriteDense.lean` — the index-native `ByteArray.foldl feedF initF`
  realisation; `rewriteBytesDense_refines` proves it byte-identical to `rewriteBytes`.

**The observable transform.** `renderTok` keeps text-run bytes and drops every tag span
in full. So the output of `rewriteBytes` is *exactly the bytes seen in `text` mode that
are not the `<` that triggers the transition* — the `<`, the `>`, and everything between
are dropped; an unclosed trailing tag contributes nothing. That is a **2-state byte
filter**, which is precisely `rewrite_html`:

```
mode = text(0)
for each body byte b:
  text: if b == '<'(60)  -> mode = tag        // drop '<'
        else             -> emit b            // kept text byte
  tag : if b == '>'(62)  -> mode = text       // drop '>'
        else             -> stay tag          // dropped tag byte
// EOF: trailing text already emitted; trailing unclosed tag drops (nothing to do)
```

The `.pnk` `while (i < len)` loop is this, with `ld8`/`st8` over the body buffer and `o`
counting output bytes (= `|rewriteBytes|`). Because the Lean side accumulates `Token`s
that `renderTok` then collapses, the loop is a *further* dense refinement of
`rewriteBytesDense` that skips materialising the (unobservable) token list — the same
move `HtmlRewriteDense` makes for `curRev`, taken one step further to the emitted bytes.

---

## 2. Native compile + assemble + link (verbatim, hbox)

```bash
ssh hbox@hbox.local ; CAKE=/home/hbox/r05/cake-x64-64/cake ; cd /home/hbox/htmlrewrite
$CAKE --pancake < htmlrewrite.pnk > htmlrewrite.S       # 0 parse errors, best-of-20 = 7 ms
grep -oE '0x[0-9A-Fa-f]{2}' htmlrewrite.S | wc -l        # CODE = 1348 machine-code bytes
cc -c htmlrewrite.S -o htmlrewrite.o                     # -> ELF 64-bit relocatable
cc -O2 htmlrewrite.S basis_ffi.c htmlrewrite_ffi.c -o htmlrewrite -lm   # running PIE exe
```

| metric | value |
|---|---|
| SRC (`htmlrewrite.pnk`) | 4 526 B |
| ASM (`htmlrewrite.S`) | 11 264 B |
| **CODE** (emitted x64 machine-code operands) | **1 348 B** |
| best-of-20 native compile | **7 ms** |
| `cc -c` object | ELF 64-bit LSB relocatable, x86-64 |
| `.text` / `.data` / `.bss` | 8 260 B / 40 B / 0 B |
| object md5 | `f145d96dfcb5d58009dfc27f567c14f0` |
| linked executable | ELF 64-bit LSB **PIE**, runs |

(The `.text` includes the fixed CakeML basis trampoline shared by every image; the
per-program signal is the **CODE = 1 348 B** — smaller than the fused serve's 4 340 B
and the manifest's `parseline` at 1 942 B, as a single tight loop should be.)

---

## 3. It runs — byte-identical to the DEPLOYED `rewriteBytes`

Ground truth (LHS) is the real deployed rewrite, obtained on this machine:

```
cd ~/dev/drorb ; lake env lean  (#eval rewriteBytes (s.toUTF8.toList))
```

The executable's `OUT[…]` (RHS) is `htmlrewrite`'s emitted body for the same `BODY`:

| # | input `BODY` | Lean `rewriteBytes` (ground truth) | `htmlrewrite` `OUT` | in→out |
|---|---|---|---|:--:|
| 1 | `<b>hi` | `hi` (`[104,105]`) | `hi` (checksum 209) | 5→2 ✅ |
| 2 | `<p>Hello <a href=x>world</a>!` | `Hello world!` | `Hello world!` | 29→12 ✅ |
| 3 | `plain text no tags` | `plain text no tags` | `plain text no tags` | 18→18 ✅ |
| 4 | `a<b>c<d>e` | `ace` | `ace` | 9→3 ✅ |
| 5 | `trailing<unclosed` | `trailing` (unclosed tag dropped) | `trailing` | 17→8 ✅ |
| 6 | `<<>>text` | `>text` | `>text` | 8→5 ✅ |
| 7 | `>already open? no, > in text stays` | *(unchanged)* | *(unchanged)* | 34→34 ✅ |
| 8 | *(empty)* | *(empty)* | *(empty)* | 0→0 ✅ |

Vectors **6** and **7** are the discriminating ones: `>` in **text** mode is a kept byte
(not a transition — mode only leaves `text` on `<`), and `<<>>text` opens on the first
`<`, stays in the tag through the second `<`, closes on the first `>`, then emits the
second `>` as text. Both match. **Scale:** a 2 500-byte body of 500 `<x>` spans + `ab`
runs → `out_len=1000`, `checksum=97500` (= 500 × (`a`+`b`) = 500 × 195) — the loop runs
at scale, output exact.

---

## 4. Provenance of the ground truth — clean axioms, no native_decide

The Lean equalities S12 rests on were `#print axioms`-checked (fully-qualified names
grepped from `Datapath/HtmlRewriteDense.lean` first):

```
Datapath.HtmlRewriteDense.rewriteBytesDense_refines   depends on axioms: [propext, Quot.sound]
Datapath.HtmlRewriteDense.rewriteStateDense_toList    depends on axioms: [propext]
Datapath.HtmlRewriteDense.rewriteBytesDense_demo_val  depends on axioms: [propext, Quot.sound]
Reactor.Stage.HtmlRewrite.rewriteBytes_eq             depends on axioms: [propext]
```

All within `{propext, Quot.sound, Classical.choice}`; **no `Lean.ofReduceBool`** — the
`rewriteBytesDense_demo_val` value (`"<b>hi"` → `[104,105]`) is proven by `decide`, not
`native_decide`, so the `hi` anchor for vector 1 is a kernel-checked fact, not a compiled
`#eval`. The `.pnk` differential (§3) then ties the emitted machine code to that
kernel-checked byte function.

---

## 5. The residual gap — precise, named (nothing faked)

1. **No in-logic refinement of the `.pnk` LOOP against `rewriteBytes`.** The port is
   verified **differentially** (8 vectors + a scale test, §3) against real Lean ground
   truth, and *argued* equal via `renderTok`'s text/tag collapse (§1) — but there is **no
   theorem** that the emitted Pancake/machine-code loop refines `rewriteBytesDense`. The
   honest obstruction: closing it needs a Pancake-semantics model of the `while`/`ld8`/
   `st8` loop and a proof it computes `rewriteBytesDense` — the same
   `compile_correct ∘ bootstrap` + per-program FFI-contract discharge the C-series/manifest
   name as the standing bootstrap-certification residual. No vacuous `P → P` "loop
   theorem" was written; the gap is named here instead.
2. **Not generator-emitted — hand-authored.** As with the fused serve
   (`FUSED-SERVE-PNK-REPORT.md` §5.4), `Dsl/EmitPancake.lean` models single inline-FFI
   functions and cannot emit this stateful `st8`-into-output loop. `htmlrewrite.pnk` is
   hand-authored from the `feedF`/`renderTok` semantics; emitting it from a `StageSpec`
   is the unbuilt EmitPancake extension.
3. **The `.pnk` is the UNGATED body rewrite (`rewriteBytes`), not the gated stage.** The
   deployed *stage* is `gatedHtmlTransformResp`: it runs `rewriteBytes` **iff** the
   response declares `Content-Type: text/html`, else passes the body through untouched
   (`Reactor/Stage/HtmlRewrite.lean`, the correctness fix). This `.pnk` implements the
   **transform engine** (`rewriteBytes`) that the gate guards — the body loop that was the
   named residual — not the content-type dispatch around it. Wiring the gate is a scalar
   header-check branch in the composing `main` (the same shape as the fused serve's other
   scalar gates), not tokenizer work; it is out of this lane and is a bounded addition, not
   research.
4. **Fusion into `serve.pnk` not done here.** S12 now *has* a `.pnk`; splicing
   `rewrite_html` in as a callee of the fused `main` (with the §3-gate wiring of item 3)
   is the remaining coverage step for `FUSED-SERVE-PNK-REPORT.md` §4 — bounded front-end
   work, scoped not stubbed.

**What is newly closed vs the manifest/fused report:** the S12 HtmlRewrite streaming
tokenizer — the manifest's *"no `.pnk` at all"* residual and the one
`deployStagesFull2` stage the fused serve could not add — **now exists as a
native-compiling, linkable, running Pancake loop whose output is byte-identical to the
deployed `rewriteBytes` on every tested input** (differentially, against kernel-checked
Lean ground truth). The gap narrows to loop-refinement + gate-wiring + fusion +
generatorization (items 1–4), on the unchanged bootstrap-certification residual.

---

## 6. Lane note — libdrorb / cargo not in this path

This lane's deliverable is **`.pnk`-only** — `cake --pancake` → `cc` → run — with **no
Rust in the path**, so (as in `FUSED-SERVE-PNK-REPORT.md` §6) **no `libdrorb`/`cargo`
build was run**: rebuilding the Rust dataplane would prove nothing about this `.pnk`
artifact. The only drorb touch was **read-only** — `lake env lean` `#eval`/`#print
axioms` to pull the ground truth in §3–§4; **no `Datapath.lean`/`lakefile`/Lean-source
change** was made or needed. rsync to hbox carried only the named files
(`htmlrewrite.pnk`, `htmlrewrite_ffi.c`); `ffi/*.o` was excluded (none exist in this
lane). Owned files: `docs/engine/probes/compiler/htmlrewrite.pnk`,
`docs/engine/probes/compiler/htmlrewrite_ffi.c`, and this report.

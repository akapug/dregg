# FUSED-SERVE-PNK — the R1 composition: the serve datapath as ONE Pancake program

**Date:** 2026-07-10 · **Machine:** hbox (24-core, io_uring) · **Compiler:**
`/home/hbox/r05/cake-x64-64/cake` (CakeML x64 bootstrap) · **Working dir (hbox):**
`/home/hbox/fused-serve/`.
**Closes:** `PNK-MANIFEST.md` §4 item **3** — *"Composition — 28 images → 1 fused
serve. … no fused `serve.pnk` has been emitted or native-compiled. This is the single
biggest item."*
**Source of the fused files (DreggNet tree):**
`docs/engine/probes/compiler/fused/serve.pnk` + `fused/serve_ffi.c`.

---

## 0. TL;DR — measured, verified by *running* it (not by assembling to `.o`)

- **One Pancake program, one entry.** `serve.pnk` is a **multi-function** Pancake
  program: **8 stage functions + the `main` entry**. `main` does **one** `@load_serve`,
  sequences the eight stage functions threading **one shared control block**, and does
  **one** `@report_serve`. This is the fused-serve shape the manifest said had never
  been emitted.
- **Native-compiles clean:** `cake --pancake < serve.pnk` → **0 parse failures**,
  **best-of-20 = 39.96 ms**, ASM 27 892 B, **CODE = 4 340 B** of emitted x64
  machine-code operands (vs the largest *single* manifest stage `parseline` at 1 942 B —
  the fused image is the 8 bodies + entry + the inter-function call/return spine).
- **Assembles to a valid ELF object:** `cc -c serve.S -o serve.o` →
  `ELF 64-bit LSB relocatable, x86-64`, `.text = 12 356 B`, md5
  `06aec4f3773a7c3caa352c16a7e77bc2` (a distinct program, not any standalone probe's).
- **Links AND RUNS end-to-end** — this goes *past* the manifest, which only `cc -c`'d
  each probe to `.o` and never linked/ran them. `cc -O2 serve.S basis_ffi.c serve_ffi.c
  -o serve -lm` produces a running executable; **5 real requests** drive it and every
  output is correct (§3).
- **The parse→guard Ctx threading is CLOSED and demonstrated.** `main` runs
  `parse_stage`, then feeds parse's *own output* — the target span `[buf+i1+1, i2)` —
  into `traversal_stage`. Flipping the request line from `GET /` to `GET /a/../b`
  changes `target_len` 1→7 and flips `traversal.blocked` **0→1** through the shared
  control block. That is real Response threading, not stage co-location.

**Honest boundary:** this fuses **6 of the 14** `deployStagesFull2` stages (+2 runtime-
substrate stages +the admit reduction) into the single image, threads **one** inter-
stage data edge (parse→traversal) of the ~13 the full fold has, is **hand-authored**
(EmitPancake does not yet emit multi-function programs, §5), and carries **no in-logic
refinement of the composition** — the bodies are individually spec-anchored (the
C-series), the *fused* program is verified **behaviourally** (compile+link+run), not
certified. Residuals named precisely in §5.

---

## 1. The fused program — which stages, the entry, the threading

`serve.pnk` (8 594 B source). Eight stage **functions**, bodies lifted **verbatim** from
the verified probes (FFI stripped from each callee and **hoisted to the one entry**),
plus the `main` entry:

| fn | body from | `deployStagesFull2` role | signature | returns |
|---|---|---|---|---|
| `parse_stage`      | `pnk/parseline.pnk` (C6) | request-line parse (substrate; feeds the chain) | `(ctrl, buf, len)` | `ok`; writes `ok/i1/i2/verlen`→`ctrl+32..64` |
| `traversal_stage`  | `hol-c24/traversal.pnk`  | **S7** path-traversal guard | `(base, len)` | `blocked` bit |
| `ipf_stage`        | `hol-c29/ipf.pnk`        | **S3** IpFilter deny 10/8 | `(base, len)` | `admit` bit |
| `machine_stage`    | `pnk/machinestep.pnk` (C2) | FSM counter (substrate) | `(buf, len)` | saturating counter |
| `secheaders_stage` | `hol-c26/secheaders.pnk` | **S13** HSTS RFC6797 gate | `(maxage)` | effective bit |
| `redirect_stage`   | `hol-c17/redirectstatus.pnk` | **S6** RFC9110 status pick | `(code)` | status number |
| `serialize_stage`  | `hol-c30/copy.pnk`       | **S9** headerRewrite / **S14** Header | `(out, src, n)` | 0 (storeFrom loop) |
| `admit_combine`    | the fold's decision conjunction | — | `(ok, blocked, ipfadmit)` | final admit |

**The entry (`main`)** — one load, thread, one report:

```
ctrl=@base; buf=ctrl+4096; abuf=ctrl+8192; out=ctrl+12288; src=ctrl+16384
@load_serve(ctrl, 32, buf, 4096)              // ONE FFI load: whole request
ok      = parse_stage(ctrl, buf, len)         // parse; spans land in ctrl
i1=lds ctrl+40; i2=lds ctrl+48
blocked = traversal_stage(buf+i1+1, i2)       // <-- THREADED parse output (target span)
ipf     = ipf_stage(abuf, alen)
counter = machine_stage(buf, len)
eff     = secheaders_stage(maxage)
status  = redirect_stage(code)
admit   = admit_combine(ok, blocked, ipf)
serialize_stage(out, src, 159)                // storeFrom serialize
@report_serve(ctrl+32, 80, out, 159)          // ONE FFI report: 10-word vector + body
```

The **10-word result vector** at `ctrl+32..112` is the shared Ctx the stages write and
the single report reads: `ok, i1, i2, verlen, blocked, ipf_admit, counter, hsts_eff,
redirect_status, admit`.

**Ground-truth Pancake syntax check (done first, on hbox).** Before writing the fusion I
confirmed empirically that `cake --pancake` accepts multi-function programs, shaped
params `fun f(1 x, 1 y)`, value-returning calls `var d = f(a,b);`, and callees doing
their own `ld8`/`while`/`st` — two throwaway programs (`t1.pnk`, `t2.pnk`) compiled exit
0. The fusion rests on tested syntax, not assumed.

---

## 2. Native compile + assemble + link (verbatim, hbox)

```bash
ssh hbox@hbox.local ; CAKE=/home/hbox/r05/cake-x64-64/cake ; cd /home/hbox/fused-serve
$CAKE --pancake < serve.pnk > serve.S          # 0 parse errors, best-of-20 = 39.96 ms
grep -oE '0x[0-9A-Fa-f]{2}' serve.S | wc -l     # CODE = 4340 machine-code bytes
cc -c serve.S -o serve.o                         # -> ELF 64-bit relocatable, .text=12356
cc -O2 serve.S basis_ffi.c serve_ffi.c -o serve -lm    # links to a running executable
```

| metric | value |
|---|---|
| SRC | 8 594 B |
| ASM (`serve.S`) | 27 892 B |
| **CODE** (emitted x64 machine-code operands) | **4 340 B** |
| best-of-20 native compile | **39.96 ms** |
| `cc -c` object | ELF 64-bit LSB relocatable, x86-64 |
| `.text` / `.data` | 12 356 B / 96 B |
| object md5 | `06aec4f3773a7c3caa352c16a7e77bc2` |
| linked executable | ELF 64-bit LSB pie, runs |

(The `.text` includes the fixed CakeML basis trampoline shared by every image, per the
manifest's `.text` note; the per-program signal is the **CODE = 4 340 B**.)

---

## 3. It runs — 5 requests, every field correct

`LINE`/`ADDR`/`MAXAGE`/`CODE` stage the request via the one `@load_serve`; the one
`@report_serve` prints the fused decision.

| run | `LINE` / `ADDR` / `MAXAGE` / `CODE` | output (abridged) | why correct |
|---|---|---|---|
| 1 | `GET /` · `4 0 0 0 0 1 0 1 0` · `31536000` · `2` | `ok=1 m=3 t=1 v=8` · `blocked=0 ipf=0 counter=0 hsts=1 status=307 ADMIT=0` | clean path → not blocked; addr **is** 10/8 → deny (ipf=0); maxage≠0→hsts=1; CODE2→307; ADMIT=0 (ipf denied) |
| 2 | `GET /a/../b` · `4 0 0 0 1 1 0 1 0` · `0` · `0` | `ok=1 m=3 t=7 v=8` · `blocked=1 ipf=1 counter=0 hsts=0 status=301 ADMIT=0` | **threading:** parsed target `/a/../b` (t=7) → `blocked=1`; addr not 10/8 → ipf=1; maxage=0→hsts=0; CODE0→301; ADMIT=0 (blocked) |
| 3 | `GARBAGE` · `6 1 1 1` · `100` · `1` | `ok=0 m=7 t=0 v=0` · `blocked=0 ipf=1 status=302 ADMIT=0` | no SP in line → `parse.ok=0`; CODE1→302 |
| 4 | `GET /aaaa` · `4 0 0 0 0 1 0 1 1` · `5` · `3` | `ok=1 m=3 t=5` · `blocked=0 ipf=1 counter=0 hsts=1 status=308 ADMIT=1` | 9th addr byte breaks 10/8 prefix → ipf=1; all gates pass → **ADMIT=1**; CODE3→308 |
| 5 | `GET \x80\xff\x81` · `4 0 0 0 0 1 0 1 0` · `1` · `1` | `ok=1 m=3 t=3` · `blocked=0 ipf=0 **counter=3** hsts=1 status=302 ADMIT=0` | 3 bytes ≥128 in the line → FSM `counter=3` (the machine loop is **live**, not DCE'd) |

Runs **1 vs 2** are the composition's headline: identical program, and the parse
stage's target-span output drives the traversal stage's decision through the shared
control block. Run **5** proves the `machine_stage` `while` loop executes in the fused
image (counter tracks the high-byte count, not a constant).

---

## 4. Coverage against the deployed serve (`deployStagesFull2`, 14 stages)

**Fused into the single image (6 of 14 deployed stages + 2 substrate + combine):**

| slot | deployed stage | in fused image? |
|---|---|:--:|
| S3 | `IpFilter.ipfilterStage` | ✅ `ipf_stage` |
| S6 | `Redirect.redirectStage` | ✅ `redirect_stage` |
| S7 | `traversalStage` | ✅ `traversal_stage` (threaded from parse) |
| S9 | `headerRewriteStage` | ✅ `serialize_stage` (C30 copy) |
| S13 | `SecurityHeaders.securityheadersStage` | ✅ `secheaders_stage` |
| S14 | `Header.headerStage` | ✅ `serialize_stage` (shares C30 copy) |
| — | request-line parse (C6) | ✅ `parse_stage` (substrate; feeds the chain) |
| — | machine FSM (C2) | ✅ `machine_stage` (substrate) |
| — | admit reduction | ✅ `admit_combine` |

**NOT in the fused image (8 of 14 deployed stages):** S1 `jwt`, S2 `basic`, S4
`rateadmit`, S5 `cache` (`cachekey`/`hashbytes`/`cachefresh`), S8 `policy`/`admit`, S10
`cors`, S11 `gzip`, **S12 `HtmlRewrite`**. Seven of these have a standalone manifest
probe and are the **mechanically same lift** — a `fun <stage>(…) { <probe body> }`
callee + a call line in `main`. **S12 has no `.pnk` at all** and is the streaming-
tokenizer body-rewrite loop residual (manifest §4 item 1) — not addable without its
Link-A refinement, and I did **not** fake a shell for it.

**Honest coverage statement:** the manifest had **28 standalone images and 0 fused
serve**; this delivers **1 fused serve image composing 6 of the 14 deployed stages**
(plus parse/machine substrate + the admit reduction) with **one entry, one FFI-load
contract, one FFI-report contract, and one real inter-stage data edge threaded**.

---

## 5. The residual gap — precise, named (nothing faked)

1. **8 of 14 deployed stages uncomposed.** Seven (S1/S2/S4/S5/S8/S10/S11) are the same
   verbatim-lift as the six already fused — adding them is bounded front-end work, not
   research. **S12 HtmlRewrite** stays the streaming-tokenizer loop residual with no
   `.pnk` (manifest §4.1). Note S2/S4/S11 would carry their manifest **decision-
   projection** caveat (base64 / windowed-counter / body-rewrite loop bodies are the
   named Link-A residuals), unchanged by fusion.
2. **Response threading closed for 1 of ~13 inter-stage edges.** Only parse→traversal
   threads a computed value (the target span) between stages through the shared Ctx.
   The other callees read **independently staged** inputs (address bytes, HSTS/redirect
   scalars) rather than fields of a single **Response record** mutated in sequence.
   Full serve threads one `Response` (status line, header map, body buffer) that each
   stage reads-and-rewrites; modeling that record's layout in the control block and
   having every stage read/write its fields is the outstanding threading work. The
   parse→traversal edge is the proof-of-concept that the mechanism *works*, not the
   whole fold.
3. **No in-logic refinement of the COMPOSITION.** Each stage body is verbatim from a
   probe whose body the C-series anchored to a Lean/HOL4 spec, but there is **no
   theorem** that the sequenced machine code refines the `deployStagesFull2` fold. This
   fused program is verified **behaviourally** (compile + link + run, §3), not
   certified. No vacuous `P→P` "composition theorem" was written — the obstruction
   (a compose-refinement over the emitted multi-function program + its call spine) is
   named here instead.
4. **Not generator-emitted — hand-authored.** `Dsl/EmitPancake.lean`'s AST (`PExpr` /
   `PStmt` / `PFun`) models **single** functions with inline FFI: there is **no
   `PStmt.call` node and no program-level (multi-`PFun`) emitter**. So this fused
   `serve.pnk` is **hand-authored** from the probe bodies, not emitted. Generatorizing
   it — the stronger claim the manifest §4.3 gestures at — requires (a) a `call`
   statement constructor + its pretty-printer, (b) a `PProgram := List PFun` with an
   entry emitter, (c) a fusion combinator `fuse : List StageSpec → PProgram`. That is a
   real EmitPancake extension; I scoped it, did not stub it.
5. **Bootstrap-certification residual (manifest §4 item 4) unchanged:** native-compiled
   bytes ≠ in-logic-proven bytes; certification remains `compile_correct ∘ bootstrap`
   plus the per-program install/FFI-contract discharge, now over the fused image's
   single `@load_serve`/`@report_serve` contract.

**What is newly closed vs the manifest:** a **single native-compiling, linkable, and
actually-running** fused serve image exists — multi-function Pancake, one entry, one
FFI contract each way, with one real parse→stage Ctx thread demonstrated at runtime.
The full-serve gap is now **coverage (7 more liftable stages + S12) + full-Response
threading + composition refinement + generatorization** — items 1–4 above — sitting on
the unchanged bootstrap residual (item 5).

---

## 7. Addendum 2026-07-10 — the Response record threaded through the 8 stages (closes §5.2)

§5 residual **2** said only **1 of ~13** inter-stage edges carried a computed value
(parse→traversal target span); the other callees read **independently staged** inputs
rather than fields of one **Response record** mutated in sequence. This addendum closes
that: `serve.pnk` now models a **Response record `R`** (status / admit / headers / body)
in the shared control block at `ctrl+2048`, and the **eight stage functions read+mutate
`R` in sequence** — the real staged-fold shape, not co-located independent inputs.

**The record (`R = ctrl+2048`):** `R+0 status  R+8 admit  R+16 blocked  R+24 hsts
R+32 counter  R+40 redirect  R+48 hdr_len  R+56 body_len  R+64 reason  R+72 ipf_raw`,
plus a header-accumulation buffer at `R+512`. `main` initialises it (`status=200,
admit=1`), threads it through all eight callees, then serialize reads it back out.

**Threading semantics (each stage reads R, decides, rewrites R):**
- **parse** — on a malformed line sets `R.status=400, R.admit=0`.
- **traversal** — reads `R.admit`; if still admitted and the path escapes, sets
  `R.status=400, R.admit=0` (**first-failure-wins**).
- **ipf** — reads `R.admit`; if still admitted and 10/8, sets `R.status=403, R.admit=0`.
  Because it reads the gate, a traversal-**400** is **not** clobbered by a later ipf-403.
- **machine** — reads+writes `R.counter` (record pass-through; substrate, no gate).
- **secheaders** — reads `R.admit` **and** `R.hdr_len`; appends the HSTS header into
  `R`'s header buffer **only for an admitted response with maxage>0**, bumping `hdr_len`.
- **redirect** — reads `R.admit` and `R.hdr_len`; on an admitted response sets
  `R.status` to the 3xx pick and appends `Location:` **after** the HSTS header (hdr_len
  ordering dependence on secheaders).
- **serialize** — reads the **whole** `R` (final `status` + accumulated `hdr_len` header
  bytes + body) and emits the real `HTTP/1.1 <status>\r\n<headers>\r\n<body>`.
- **admit_combine** — reads the threaded `R.admit` the gates folded.

**Edges now threaded — 7 of the fused image's boundaries carry a computed field
(up from 1); against the full fold's ~13 edges, 7 vs 1:**

| inter-stage boundary | threaded field(s) through R | before → now |
|---|---|:--:|
| parse → traversal | target span `[buf+i1+1,i2)` **and** `admit/status` | span-only → both |
| traversal → ipf | `admit/status` gate (first-failure-wins) | ✗ → ✓ |
| ipf → secheaders | `admit` gate (HSTS only if admitted) | ✗ → ✓ |
| secheaders → redirect | `hdr_len` ordering (Location after HSTS) + `admit` | ✗ → ✓ |
| redirect → serialize | final `status` | ✗ → ✓ |
| secheaders/redirect → serialize | header block `hdr`+`hdr_len` | ✗ → ✓ |
| gates → admit_combine | folded `admit` | ✗ → ✓ |
| ipf → machine | bare record pass-through (`counter`, no decision) | n/a |

**Verified by running it (best-of-20 native compile, full from-scratch, hbox):**

```bash
cake --pancake < serve.pnk > serve.S    # 0 parse errors, best-of-20 = 74.05 ms
cc -c serve.S -o serve.o                  # ELF64 REL x86-64, .text=12356 .data=96
cc -O2 serve.S basis_ffi.c serve_ffi.c -o serve -lm   # ELF64 PIE, runs
```

| metric | prior (§2) | threaded (this addendum) |
|---|---|---|
| SRC | 8 594 B | **12 585 B** |
| ASM `serve.S` | 27 892 B | **37 059 B** |
| **CODE** (x64 operands) | 4 340 B | **6 024 B** |
| best-of-20 compile | 39.96 ms | **74.05 ms** |
| `serve.o` `.text`/`.data` | 12 356 / 96 | 12 356 / **96** |
| `serve.o` md5 | `06aec4f3…` | `902f8aebbc1edc300a8004413860bd5f` |
| linked `serve` | ELF64 PIE, runs | **ELF64 PIE, runs** |

(`.text` = the fixed CakeML basis trampoline shared by every image; the per-program
signal is **CODE = 6 024 B**, +39 % over the pre-threading 4 340 B — the record
init/gate reads + the two header-append copy loops + the serialize status-line/header
emitter. The 74 ms best-of-20 is measured on a loaded 24-core hbox; the larger image
compiling slower than the 4 340-B one is expected, but I did **not** normalise against
§2's 39.96 ms figure — different load, reported as measured.)

**Runs — the threading is observable in the emitted Response (verbatim, hbox):**

| # | `LINE` / `ADDR` / `MAXAGE` / `CODE` | report line | serialized head | what it proves |
|---|---|---|---|---|
| 1 | `GET /` · `4 0 0 0 0 1 0 1 0` · `31536000` · `2` | `blocked=0 ipf=0 hsts.eff=1 final.status=403 ADMIT=0` | `HTTP/1.1 403␍␊␍␊…` (175 B, **no** HSTS hdr) | ipf sets `admit=0`; secheaders reads the gate and **suppresses** HSTS despite `eff=1` |
| 2 | `GET /a/../b` · `4 0 0 0 1 1 0 1 0` · `0` · `0` | `blocked=1 ipf=1 final.status=400 ADMIT=0` | `HTTP/1.1 400…` (175 B) | traversal-**400** survives: ipf `raw=1` but its 403 is gated off — **first-failure-wins** through R |
| 3 | `GET /aaaa` · `4 0 0 0 0 1 0 1 1` · `31536000` · `3` | `hsts.eff=1 final.status=308 ADMIT=1` | `HTTP/1.1 308␍␊Strict-Transport-Security: max-age=31536000␍␊Location: /␍␊␍␊…` (233 B) | admitted end-to-end: **both** headers appended **in order**, `status` 200→308 threaded, serialize reads it all back |
| 4 | `GET /ok` · `8 1 2 3 4` · `0` · `2` | `hsts.eff=0 final.status=307 ADMIT=1` | `HTTP/1.1 307␍␊Location: /␍␊␍␊…` (188 B) | maxage=0 → **no** HSTS; Location now sits at `hdr_len=0` (the ordering slot secheaders left empty). 233−45 = 188 exactly |
| 5 | `GET \x80\xff\x81` · `8 1 2 3 4` · `1` · `1` | `machine.counter=3 final.status=302 ADMIT=1` | `HTTP/1.1 302…` | `machine_stage` `while` is live (counter=3), threaded counter in R |

Byte arithmetic is self-consistent — `175 = 14(status) + 0(hdr) + 2 + 159(body)`,
`233 = 14 + 45(HSTS) + 13(Location) + 2 + 159`, `188 = 14 + 13 + 2 + 159` — i.e.
serialize genuinely emits the header bytes the upstream stages accumulated in `R`, not a
constant.

**Residuals unchanged / newly sharpened:**
- §5.1 coverage (8 uncomposed stages incl. S12) — **unchanged**; the ~6 not-yet-threaded
  edges of the ~13 live in those uncomposed stages.
- §5.2 is now **7 of ~13** threaded (was 1); the record threads through **all 8** present
  stages, the lone bare pass-through being ipf→machine (substrate counter, no decision).
- §5.3 composition refinement, §5.4 generatorization (still hand-authored; `EmitPancake`
  has no `PStmt.call`/multi-`PFun`/record-layout node), §5.5 bootstrap-cert — **all
  unchanged**. No composition theorem was faked; the threading is verified
  **behaviourally** (compile GREEN + link + the 5 runs above), not certified.

**Lane note:** `.pnk`-only path (`cake --pancake` → `cc`); no Rust in the datapath, so no
libdrorb/cargo/`Datapath.lean` build was in scope (running one would prove nothing about
this artifact). `native_decide` is not applicable (Pancake, not Lean). Files touched:
`fused/serve.pnk`, `fused/serve_ffi.c`, and this report addendum.

---

## 6. Lane note — libdrorb / cargo not in this path

The task's `ffi/build-dataplane-lib.sh` + `cargo` rebuild pertains to the **drorb Rust
dataplane** integration; this lane's deliverable is **`.pnk`-only** — `cake --pancake`
→ `cc` — with **no Rust in the path**, so no libdrorb/cargo build was run (running one
would prove nothing about this artifact). **No `Datapath.lean` / `lakefile` change was
required** to compile or run the fused image; the only Lean-side follow-up is the
EmitPancake extension named in §5 item 4, which I did not write (out of lane, and it
must not be a mirror). Files owned by this lane:
`docs/engine/probes/compiler/fused/serve.pnk`,
`docs/engine/probes/compiler/fused/serve_ffi.c`, and this report.

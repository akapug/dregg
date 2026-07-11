# C29 REPORT — the deployed `ipfilterStage` CIDR admission gate is closed spec→machine-code by the N=1 composed generator; the CIDR walk's early-exit fit as a bounded accumulate-and-absorb fold (0 axioms, leanc out)

Gate A asked whether **stage 3 of `Reactor.Deploy.deployStagesFull2`** —
`ipfilterStage`, the CIDR **admission gate** (`WireIpFilter.deployAdmits` =
`IpFilter.permits deployRuleset`, an ordered deny-precedence CIDR-ruleset walk
that matches the client IP and early-exits) — could be closed end-to-end, and
whether its **fold-over-rules-with-early-exit** fit the existing generator or
needed a new fold-schema variant. **C29 lands it.** `ipfilter_machine_code`
(theory `ipfGen`) is a full spec→machine-code theorem for the **CIDR admission
gate**, produced by **one `mk_composedWrapper1` call** — the same **N=1 peel** of
the C23 composed generator that C24 first exercised. **No new fold machinery was
needed.**

**Verdict up front.**
- **Is `ipfilterStage` closed end-to-end?** **Yes.** `ipfilter_machine_code` is
  `[oracles: DISK_THM] [axioms: ]`, **hyps = 0, 0 cheats**, non-vacuous — a real
  `machine_sem mc ffi ms ⊆ extend_with_resource_limit' … {Terminate Success (…
  report_vec … (word_to_bytes (ipfDecide input) F) …)}` that reports the **actual
  admit decision word** over the client-address byte input. leanc is out of the
  TCB: `ipfProg` is the CakeML **verified parser's** output on `ipf.pnk`, and the
  fold body / gate the proof reasons about are **genuine parser subterms** (the
  `ipfData` surgery raises if they are not).
- **Did the CIDR walk's early-exit fit the generator, or need a new fold variant?**
  **It fit — no new machinery.** The deployed ruleset is **one** deny rule
  (`10.0.0.0/8`) with default-admit, so the deny-precedence **ruleset walk
  collapses** to a single CIDR-prefix match + a negate gate. The prefix match's
  early-exit is expressed as a **bounded accumulate-and-absorb fold** (a
  position-carrying matcher with two absorbing sinks: `9w` = deny prefix fully
  matched, `10w` = a prefix byte mismatched) — **decision-equivalent, no true
  early break needed**. This is exactly the task's "a fold that computes 'any rule
  matches' is decision-equivalent" path. The generator applied at **N=1**
  (`mk_composedWrapper1`), the **same one C24 used** — a single fold + scalar gate.
- **Is it non-vacuous / grounded?** **Yes.** `verifyC29` machine-checks the admit
  truth table on **real client IPs** (encoded via `Reactor.Stage.IpFilter.encodeAddr`):

  | client IP (encoded byte-string) | `ipfMatch` state | `ipfDecide` |
  |---|:---:|:---:|
  | `10.0.0.0` (inside deny `/8`) | `9w` (prefix matched) | **`0w` BLOCKED** |
  | `10.1.2.3` (inside deny `/8`, differing tail) | `9w` | **`0w` BLOCKED** |
  | `127.0.0.0` (loopback) | `10w` (mismatch sink) | `1w` ADMIT |
  | `11.0.0.0` (adjacent `/8`, differs at last prefix bit) | `10w` | `1w` ADMIT |
  | no address (`[4]`, the accept default) | `1w` | `1w` ADMIT |
  | a v6 client (tag `6`) | `10w` | `1w` ADMIT (family separation) |

  These reproduce drorb's own concrete witnesses `deployAdmits_blocked`
  (`10.0.0.0 → false`) and `deployAdmits_clean` (`127.0.0.0 → true`), and the
  documented permissive default (no stashed `client.ip` ⇒ admit).

**Date:** 2026-07-07 · **Machine:** hbox (i9-12900) · **HOL4 Trindemossen-2
stdknl, CakeML `ed31510b3`** — the exact tree C1–C24 used. **Dir:**
`docs/engine/probes/compiler/hol-c29/` (built on hbox `~/hol-c29`, full `Holmake`
exit 0, idempotent). Sibling agents own `hol-c16..c28`; C29 stayed out of them and
copied `hol-c24`'s extended `panComposedLib` (with `mk_composedWrapper1`) +
`composedCommon`/`foldLoopSchema`/`panAuto(Lib)` + the fold/gate deps.

---

## 1. Ground truth — the REAL `ipfilterStage` (drorb `Reactor/Stage/IpFilter.lean`)

`ipfilterStage` (`:127`) is a GATE: its request phase runs the REAL admission
decision on the context's client address and, on a rejected address,
short-circuits the whole pipeline with a serializer-built `forbidden403`;
otherwise it passes through. Its decision is `deployAdmits` (`:83`):

```
deployAdmits a = IpFilter.permits deployRuleset a
deployRuleset  = { rules := [(denyCidr, Action.deny)], defaultDeny := false }
denyCidr       = { family := .v4, net := [F,F,F,F,T,F,T,F], len := 8 }   -- 10.0.0.0/8
```

`IpFilter.permits` (`IpFilter.lean:87`) is the **ordered deny-precedence** decision:

```
permits rs a = if matchesDeny rs a then false        -- any deny rule matches → reject
               else if matchesAllow rs a then true   -- else any allow rule matches → permit
               else !rs.defaultDeny                   -- else the default toggle
matchesDeny  rs a = rs.rules.any (λ r. r.2 = deny  ∧ matchCidr r.1 a)   -- fold-over-rules, EARLY EXIT
matchesAllow rs a = rs.rules.any (λ r. r.2 = allow ∧ matchCidr r.1 a)
matchCidr c a = decide (c.family = a.family ∧ a.bits.take c.len = c.net.take c.len)
```

**The exact spine: a fold-over-rules-WITH-EARLY-EXIT (`List.any`, stop on first
matching CIDR) whose body is a CIDR prefix match, then a `defaultDeny` gate.**
Two inputs feed it: the client `Addr` (family tag + bits) and the `Ruleset`.

**The deployed ruleset collapses the outer walk.** With `rules = [(denyCidr,
deny)]` and `defaultDeny = false`: `matchesDeny a = matchCidr denyCidr a` (one deny
rule), `matchesAllow a = F` (no allow rules), so

```
deployAdmits a  =  ¬ (matchCidr denyCidr a)  =  ¬ (a.family = v4 ∧ a.bits.take 8 = 00001010)
```

i.e. **admit iff the client is NOT in `10.0.0.0/8`** — the single remaining loop is
the 8-bit CIDR **prefix match**, itself a bounded compare with early-exit on the
first differing bit.

## 2. The stage, modelled and emitted (`ipf.pnk` → verified parser → `ipfProg`)

The client address enters as its `encodeAddr` byte-string: a family tag byte
(`4`=v4 / `6`=v6) then one `0`/`1` byte per address bit. `cidrAcc : word64 →
word64 → word64` (`ipfCore`) is the **CIDR-prefix matcher automaton** over those
bytes, matching against the 9-byte deny prefix `T = [4,0,0,0,0,1,0,1,0]` (the tag
byte + the 8 network bits of `10 = 00001010`):

- state `k ∈ 0..8` = the first `k` bytes of `T` matched in sequence (on track;
  next expected byte is `T[k]`);
- state `9` = **all 9 matched** → the client IS in `10.0.0.0/8` (ABSORBING — the
  remaining 24 address bits are ignored: **the ruleset walk's early-exit rendered
  as an accumulate-and-absorb bounded fold, no true break**);
- state `10` = a prefix byte **mismatched** → never in the deny block (ABSORBING sink).

`ipfMatch input = FOLDL cidrAcc 0w (MAP n2w input)`; `ipfDecide input = if
ipfMatch input = 9w then 0w else 1w` (`0` = BLOCKED/deny, `1` = ADMIT) —
decision-equivalent to `deployAdmits` for the deployed single-deny-rule ruleset
(deny-precedence with one deny rule + default-admit = **negate the single CIDR
prefix match**). It is a **genuinely different fold core** from the C21 hash
Horner and the C24 escape automaton (the audit asserts `cidrAcc`/`ipfMatch`
mention neither `hashBytes`/`hashAcc` nor `escAcc`). `matchCidr`'s `.take`
truncation is named as the drorb boundary; the fold is the concrete matcher.

`ipf.pnk` is emitted on the C0–C24 path (one arena, control block `[len | result
| … | address bytes @+32]`), parsed by the **CakeML-verified**
`parse_topdecs_to_ast` → `ipfProg` (`ipfLinkBInst`, `mk_linkB`). `ipfCore`
**extracts** `cidrBody` / the while-loop / `ipfGate` as genuine subterms of
`ipfProg` (no hand transcription); `ipfData`'s surgery refolds the deployed
`ipfMainBody` to `cidrLoop`/`ipfGate` and **raises if they are not parser
subterms** — leanc stays out of the TCB.

## 3. The theorem (`ipfGen`, verbatim `show_tags`)

```
[oracles: DISK_THM] [axioms: ]   (hyps = 0)
⊢ ( … pan_to_target install package over ipfProg … ∧ pan_installed … ) ∧
    ipfFFI input s ∧ (∃K. 0 < K ∧ LENGTH input < K) ⇒
  ∃loadEv rb.
    machine_sem mc ffi ms ⊆ extend_with_resource_limit' …
      {Terminate Success
         (s.ffi.io_events ++ loadEv ++
          [IO_event (ExtCall «report_vec»)
             (word_to_bytes (ipfDecide input) F) rb])}
```

`ipfFFI` is the single named FFI-oracle contract (`@load_vec` stages the address
arena + length; `@report_vec` emits the admit word) — the single-arena analogue
of C24's `travFFI`. It is the only trusted assumption; the theorem carries **no
axioms** (`verifyC29`: `axioms = 0`).

## 4. What the stage cost — the honest quantification

| piece | lines | kind |
|---|---:|---|
| `cidrAcc` / `ipfMatch` / `ipfDecide` spec | ~19 | the stage decision (10-state prefix matcher) |
| `cidrBody` / `cidrLoop` / `ipfGate` | **0** | EXTRACTED from `ipfProg` (genuine subterms) |
| **`cidrBody_step`** (the new fold-core step) | **~90** | dominated by 13 guard-eval facts (10 acc-states × 3 byte values); the cascade collapses via the panAutoLib `imp_res_tac evaluate_If_reduce` idiom — **no case explosion** |
| `cidrBody_mem` / `cidrBody_ctrl` / `cidrLoop_noFFI` | ~20 | mem/ctrl frame facts (branchy body ⇒ `AllCaseEqs` blast) |
| **`cidrLoop_framed`** (via body-generic `loop_frame`) | **~29** | one `loop_frame` instantiation (the C23 engine, reused unchanged) |
| `evaluate_ipfGate` (the one gate lemma) | **~18** | 1-arm `Cmp Equal` gate (state = `9w` ⇒ blocked) |
| `ipfStaged`/`ipfFFI` + `ipfMainBody` surgery | ~75 | single-arena analogue of C24's `travStaged`/`travFFI` |
| **whole-program wrapper (MainRefine+Sem+Install+EndToEnd)** | **0** | one `mk_composedWrapper1` call (13-line spine record) |

**One-time infrastructure: none new.** `mk_composedWrapper1` (the N=1 peeler) was
written in C24 and **carried verbatim**; C29 reused it via a single generator
call with **zero** additions to `panComposedLib`. The prefix matcher's `cidrBody`
is wider than C24's escape automaton (10 vs 5 states), so its step lemma is a bit
larger, but the reduction is *cheaper* per goal: the `imp_res_tac
evaluate_If_reduce` cascade idiom collapses the 10-way `if`-nest in a **single
goal** (the 13 guard-eval facts + `rw []`), avoiding the `2^n` `Cases_on` blow-up.

**Per-stage cost, then:** its new fold core (`cidrBody` + `~90`-line step +
`~29`-line framed core) + its `~18`-line gate lemma + a `13`-line record + one
generator call. The whole-program wrapper is again **0 hand lines**.

## 5. Did the early-exit / CIDR fit the generator? — the spine-shape answer

**Yes, cleanly, at N=1 — and this is the point of the probe.** The deployed
`ipfilterStage` is **N=1** (one fold + gate), the same class C24's `traversalStage`
established. The two ways the CIDR gate *could* have broken the generator both
dissolved:

1. **The ruleset walk (`List.any`, early-exit on first matching CIDR).** At the
   deployed ruleset it is **one deny rule**, so `matchesDeny` = a single
   `matchCidr` and `matchesAllow` = `F`. The outer fold-over-rules **collapses**;
   no loop-over-rules survives to compile.
2. **The prefix match's early-exit (stop on first differing bit).** Expressed as a
   **bounded accumulate-and-absorb fold** — two absorbing states (`9w` matched,
   `10w` failed) mean once the 8-bit verdict is fixed the fold ignores the rest.
   **No true early break, no new fold-schema variant** — the ordinary
   `foldLoopSchema` (`foldInv`/`foldGuard`/`loop_frame`) carries it, exactly as it
   carried the hash Horner (C21) and the escape automaton (C24).

**This general-loop-class gate is now BOUNDED.** After C29 the deployed stage
classes are unchanged from C24's map except that the **CIDR walk** moved out of
the open "general loops" bucket:
- **scalar-branch** (redirect, rate) — one line each. Done.
- **single-fold value reports** (Content-Length) — `mk_foldWrapper`. Done.
- **single-fold + gate** gates (traversal [C24], **CIDR admission [C29]**) — one
  `mk_composedWrapper1` call + a fold core + a gate lemma. Done (N=1).
- **two-fold + gate** gates (cache-key, `(method,route)` admission) — one
  `mk_composedWrapper` call. Done (N=2).
- **genuine general loops** (parse `While` [C13], DEFLATE, JWT FSM) — still open,
  the standing residual.

**The residual, named precisely.** What is *not* yet closed is a **multi-rule
ruleset** (N ≥ 2 CIDRs, mixed allow/deny under deny-precedence). That reintroduces
the outer `List.any` walk over rules as a real loop whose body is itself a
`matchCidr` sub-fold — a **nested** fold. It is still **bounded-fold-expressible**
(a widened accumulator tracking `deny-matched-yet ∨ allow-matched-yet` over the
rules, with the prefix matcher as the inner absorb-fold), *not* bespoke per-loop
metatheory like DEFLATE — but it needs either a two-level fold schema or a
per-rule unrolling, neither of which C29 wrote. The deployed gate (one deny rule)
does not need it, so `ipfilterStage` **as deployed** is fully closed; a
richer-ruleset variant is the next mechanical step, not open research.

## 6. Trust ledger (unchanged from C13–C24; none of it is leanc)

`ipfilter_machine_code` is `[oracles: DISK_THM] [axioms: ]`, hyps = 0, 0 cheats
(`verifyC29` asserts this adversarially + non-vacuity + the grounded truth table
+ that the fold is genuinely distinct from the hash/escape cores). `DISK_THM` is
the benign CakeML disk-export tag. The theorem rests only on: CakeML backend
correctness (Link B via `mk_linkB`), the C16 fold schema, the body-generic
`composedCommon.loop_frame` frame engine (reused unchanged), and the single named
FFI contract `ipfFFI`. `mk_composedWrapper1` and `mk_linkB` carry **no trust** —
they only assemble kernel-checked proofs; the generator writes zero axioms
(`verifyC29`: `axioms = 0`). The HOL fold `ipfMatch`/`ipfDecide` is the byte-level
model of the deployed decision `deployAdmits` (drorb `IpFilter.permits
deployRuleset`); its grounding is the truth table matching drorb's concrete
witnesses `deployAdmits_blocked`/`deployAdmits_clean` — the same modelling posture
C24 took for `travDecide` vs `escapesSegs`. The full `Holmake` (whole `hol-c29`
tree, including C22/C23 rebuilt against the carried `panComposedLib` — so C29's
stage did **not** break the existing generators) is **exit 0, idempotent**.

## 7. Files (`docs/engine/probes/compiler/hol-c29/`, built on hbox `~/hol-c29`)

**The stage (new):**
- `ipf.pnk` — the emitted single-fold + gate program.
- `ipfLinkBInstScript.sml` — Link B (`mk_linkB` on `ipf.pnk`).
- `ipfCoreScript.sml` — `cidrAcc`/`ipfMatch`/`ipfDecide` spec; `cidrBody`/
  `cidrLoop`/`ipfGate` extracted from `ipfProg`; `cidrBody_step`/`_mem`/`_ctrl`,
  `cidrLoop_framed` (via `loop_frame`), `evaluate_ipfGate`.
- `ipfDataScript.sml` — `ipfStaged`/`ipfFFI` + `ipfMainBody` surgery (raises if
  `cidrLoop`/`ipfGate` are not parser subterms).
- `ipfGenScript.sml` — the **one** `mk_composedWrapper1` call → `ipfilter_machine_code`.
- `verifyC29Script.sml` — the adversarial audit (DISK_THM-only, hyps = 0,
  non-vacuous; the `ipfDecide` truth table on real IPs + the matcher states; the
  fold is distinct from the hash/escape cores; `loop_frame` non-vacuous).

**Carried verbatim from C24 (one-time infra, no new lines):**
- `panComposedLib.sml` — including `mk_composedMainRefine1` / `mk_composedWrapper1`
  (the N=1 peel), reused unchanged by C29's single generator call.

Build: `CAKEMLDIR=/home/hbox/src/cakeml`, full `Holmake` exit 0.

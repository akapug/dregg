# drorb ROADMAP — the path to a proven superset

Standing goal: drorb = world's first VERIFIED network engine strictly EXCEEDING its unverified
reference. Current honest number (my-hand col-5 grep): **99 HAVE-PROVEN = 37%** | 126 PARTIAL | 24 MISSING.
This is the strategic plan; GOAL.md is the terse running log.

## THE DEPLOYMENT GRADIENT (the honesty spine — read first)
"Deployed-and-proven" is a LADDER, not a bit. A live-wiring swarm climbs only ONE rung. The number can
inflate into "true-in-a-selftest" if we chase rung 2 alone. A genuine SUPERSET needs the DEPLOYED SERVE
(rungs 3-4), not a selftest that proves the model in isolation.

1. **Inert** — proven, in no binary → `PARTIAL`
2. **Live-wired** — proven, runs in a *selftest exe* → `HAVE-PROVEN[drorb-native]`   ← fast swarms do THIS
3. **Braided** — runs in the *actual dataplane serve*, flag-gated → `HAVE-PROVEN[braid-gated]`
4. **Default-on** — the deployed engine does it BY DEFAULT → `HAVE-PROVEN` (real)

Weight toward rungs 3-4 (braids + prove-what-runs) even though rung-2 live-wirings are faster — else the
37% becomes a selftest number, not an engine number.

## THREE TRACKS (run in parallel — disjoint files)

### Track A — BREADTH (row-count, rung 2, fast)
No-crypto live-wiring swarms move inert PARTIAL → runs-in-selftest. Drains the ~100 real inert rows.
- **Swarm A1 (DONE-ish):** DnsRecords/CacheDisk/ProxyLb/H2Engine/StickTable/WsFrame.
- **Swarm A2:** the big inert clusters left — dn(15: DNSSEC/EDNS/SRV), pk(14: OCSP/cert-chain/CT-audit),
  px(13: retry/mirror/shadow/hedging), me(9: relay-mesh), ad(6: introspection), cl(7: H3-receive).
  After A2 the inert bucket is mostly emptied — breadth coverage near-complete.
- STOP pretending these move fast: cq(9)/io(7)/qu(4) kernel-perf PARTIAL — deferred by measurement.

### Track B — DEPTH (real-deployed, rungs 3-4, the honest-superset work)
- **Swarm B1 — BRAID into the deployed serve (NEXT, depth-first per ember).** Take stages live-wiring only
  SELFTESTED and braid them into the actual dataplane serve (like braid a/b/c), each a composition proof,
  verified with a real curl. Moves "true-in-selftest" → "the deployed engine does it, flag-gated." Targets:
  response-shaping + security + o11y stages that belong in the serve.
- **Swarm B2 — prove-what-runs (the 15 HAVE).** The deployed dataplane ALREADY runs these (o11y metrics
  ob×3, h1 edges×2, admin×2, SSE, access-log) but they are UNPROVEN. HAVE → HAVE-PROVEN on the REAL
  deployed path — highest honesty-per-row (proving what actually ships, not a model).
- **Braids-default-on (deployment-design, deliberate).** Config-driven middleware defaults so the deployed
  engine runs the full feature set WITHOUT DRORB_BRAID = the "operable as a real homelab server" axis.

### Track D — PROOF INFRASTRUCTURE (the force-multiplier — compounds ALL of the above)
Verified-braiding is not just row-moving; it BUILDS proof strategy. `prepend_pass` already proved the
principle — one axiom-free general lemma turned every pass-through braid from a bespoke proof into a
one-liner. INVEST in the calculus so each new braid (and each new proof) gets CHEAPER + FASTER:
- **The braid calculus:** generalize the composition obligations into reusable lemmas —
  `prepend_pass` (pass-through, DONE), a general `braid_gate` (short-circuit-with-status, subsumes the
  conn/stick/slow/conditional bespoke proofs), a general `braid_transform` (response-map-at-onion-position,
  subsumes errorpage/variants/autoindex/compress). Each generalization retires N bespoke proofs.
- **A `braid_stage` tactic:** picks the right lemma + discharges the onion-order / status-stable /
  byte-identity-when-off side conditions automatically — so a new stage's composition proof is a one-liner,
  not 40 lines. Turns the braid swarm from "prove each" into "apply the tactic."
- **Payoff compounds beyond braids:** the same composition/refinement tactics sharpen the effect-scheduler
  refinements (drive_*_refines), the live-wiring faithfulness proofs, and eventually the Pancake emit_correct
  proofs. Faster proofs = more rows per swarm + less agent time = the whole climb accelerates.
- **Sequence:** build the calculus lemmas + tactic FIRST (a dedicated lane), THEN the braid swarm USES them
  (cheaper per stage). Measure the win: bespoke-proof-lines-before vs tactic-lines-after.

### Track C — COMPILER (the moat / longevity; HOL4+Lean, disjoint background)
The honest ladder (Rung 0 was the retracted fake):
- **Rung 1 (DONE):** C-series machine_sem theorems with HYPOTHESIS bytes (reflect_bytes_machine_code, tag
  [oracles:DISK_THM][axioms:] my-hand-verified).
- **Rung 2 (IN FLIGHT):** concrete LITERAL bytes for a small prog via cv_compute (plain EVAL blocked by
  reg-alloc intractability — cv_compute is the fix). = first NON-FAKE verified silicon.
- **Rung 3:** concrete bytes for a real SERVE stage (cache-hash / header-serialize), not a toy — the
  compiler track meeting the engine track: verified silicon for something the engine RUNS.
- **Pancake Phase C (parallel, Lean-side):** emit_correct for more stage-kinds toward a GENERIC emit
  (region done; loops/calls/memory next) → marching to **Gate A** (whole-serve compile, removes leanc
  from the TCB long-run). leanc+Rust runs the cloud NOW; the verified compiler is the longevity play.

## SEQUENCING
Run breadth + depth + compiler in parallel (disjoint files). Bias the NEXT engine swarm to DEPTH (B1
braid) — we have a big inert-selftest lead already; the superset needs the deployed serve.

## HONEST NORTH-STAR MATH
~100 real inert PARTIAL + 15 HAVE + ~8 real MISSING ≈ **~123 movable rows** at 6-8/swarm ≈ ~15-18 swarms to
approach the ledger ceiling. The LAST MILE is NOT swarmable: real-headscale interop (~90% new untrusted
I/O, blocked on headscale), netstack me.6/7 (greenfield), default-on operability (deployment-design),
Gate A (the compiler climb). Those are hand-built, honestly. The swarms get us to the doorstep; the last
mile is real engineering + the breadstuffs cut.

## ARCHITECTURAL FINDING (braids-default-on R2, f2edd1a): the rung-4 serve-stage CEILING
CORS reaches rung-4 (config-driven default-on, curl-verified). But conn-limit/rate/stick/slowloris CANNOT — they read per-connection/per-source STANDING state (conn-active, request-rate, stick-count) that the sans-IO serve fold (ctxOfMetered supplies only client.ip + rate-seq) does not carry. Confirmed live: 30 reqs at max-connections=4 -> all 404, ZERO 503. These are ACCEPT-PATH (reactor) concerns, NOT serve-stages. => a NEW track: REACTOR-LEVEL MIDDLEWARE — wire the standing-counter store + gating into the accept path (blocking/uring/kqueue), proven at the reactor level (like the recycle/copy-once laws), curl-verified (a real conn flood -> 503). This is the honest "operable homelab" path for DoS-protection middleware; serve-stage default-on has a ceiling. Deferred-but-named (real operability, bigger reactor job).

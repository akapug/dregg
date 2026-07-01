# 00 — CHARTER

The keel. Every other doc, decision, and artifact inherits this. If a choice
conflicts with an invariant here, the invariant wins or the charter is amended
deliberately (not drifted past).

## Mission

**Liberate The Network Orchestrator.**

Elide built a Cloudflare-tier network-server product — `elide orb` / "The Network
Orchestrator" (`netorb`) — and fenced it behind a premium license + an EAP
timebomb (it phones home which features you use). The core of that work is
ember's own engineering. The mission is to **rebuild it clean-room as ember's own
AGPL work — better than the locked version — and give it to the world free and
un-rug-pullable.**

"Better" is concrete and provable:
- **Verified.** The locked orb is fast but unverifiable. Ours is fast *and* proven
  — it cannot silently serve plaintext for a misconfigured `auto-https`, cannot
  open a port the config didn't declare, cannot leave an admin surface
  unauthenticated. *They locked a fast orb; we free a fast orb that can't lie.*
- **The net PD of the verifiable cloud.** The engine is the verified, line-rate
  network protection-domain of the dregg/deos seL4 capability OS — the long-range
  reach of the capability fabric (CapTP at distance n).
- **Un-rug-pullable.** AGPL-3.0: network-use copyleft means it cannot be taken
  private again — not by Elide, not by anyone, not by a future us.

## The twin requirement (the reason the project exists)

**Highest possible performance AND highest possible assurance. Zero compromise.**

These are not traded off. They bind on *different layers* (CR-5) and the design
makes the fastest shape and the most-provable shape identical (CR-1). Any plan,
artifact, or review that trades one for the other is rejected.

## Charter invariants (CR-*) — non-negotiable

- **CR-1 — Formal-first.** The *model* is the primary artifact; the implementation
  is **generated** from verified models, correct-by-construction. We never
  hand-write an implementation and verify it after the fact. (Bug class:
  `impl-first-bolt-on-proof`.)

- **CR-2 — Zero unverified code on the path.** Every line that ships is
  generated-and-verified (CakeML / Pancake / Vale verified-asm) or it does not
  ship. There is **no "audited-but-unproven" perimeter** and **no fall-back to
  unverified C/asm** for performance. What remains trusted is a *small, explicitly
  named environment-axiom set* (the NIC DMA contract, the seL4 kernel, the
  hardware, modular-arithmetic wraparound) — the same floor l4v stands on, made
  explicit, never hidden. **Honesty clause:** if the trusted environment-axiom set
  ever includes the **TLS record-layer FSM** and/or the **QUIC transport engine**
  short-term (because their full refinement chains land after first ship), the set
  **names them explicitly** as axioms — and each carries a **successor verification
  rung** (a named ADR-rung that retires the axiom into proof). An unnamed trusted
  protocol engine is a `laundered-vacuity` violation, not an axiom. (Bug class:
  `audited-not-proved` / `unverified-fast-path` / `unnamed-trusted-engine`.)

- **CR-3 — Clean-room; oracles are read, never ported.** The Elide tree
  (an internal Elide HTTP-engine source tree) is the *semantic oracle* for the engine; the dregg Lean kernel
  is the oracle for dregg semantics. We **read** them to learn what the models must
  capture and we **diff** generated artifacts against them on the real workload. We
  never copy a line. The provenance firewall is a fresh repo + fresh authorship +
  the language/representation being genuinely re-derived. (Bug class:
  `oracle-as-source` / `ported-not-rederived`.)

- **CR-4 — Own the compiler.** We do not trust an external compiler on the path. We
  own and verify the DSL front-end + the domain-specific codegen passes, on top of
  CakeML/Pancake's *verified backend* (which we inherit, not rebuild). The
  compiler-correctness theorem is what discharges the routine per-instance
  obligations globally. (Bug class: `trusted-compiler`.)

- **CR-5 — Confinement is the assurance; line-rate is the perf; they live on
  different layers.** The **cold control plane** (the orchestrator standup, runs
  once at boot) proves the *negative*: nothing listens / routes / exposes /
  authorizes that the spec did not declare, and no declared security property
  silently degrades. The **hot dataplane** (per-packet) hits the line-rate budget
  *by verified means*. Heavy proof goes on the cold plane (zero runtime cost); raw
  speed goes on the hot plane. Never trade. (Bug class: `silent-policy-degrade` /
  `verified-but-slow-shipped`.)

- **CR-6 — No laundered vacuity, ever.** Inherited verbatim from the dregg/ HATCHERY
  discipline (and `decision-spirit` #21): an obligation is discharged honestly or
  the unmet part is handed back explicitly. A `sorry`, an unverified premise, a
  matched-buggy-oracle, a stubbed step is **never** laundered into a false "proved"
  or "done." Non-vacuity is verified by **reading the term / the diff / the cited
  evidence**, not by trusting a green check. (Bug class: `laundered-vacuity`.)

## Definition of done (project-level)

The project is done when **all** hold:

1. A single verified refinement chain exists from the **declared server-node spec**
   down through the orchestrator standup, the protocol/parser/IO models, the
   verified compiler, to **machine code** — with the only trusted base being the
   prover kernel + the named CR-2 environment axioms.
2. The engine runs as the **dregg seL4 Microkit net PD(s)**, serving CapTP +
   **HTTP/1/2/3** + the **reverse/forward/L4 proxy dataplanes** + the **mesh data
   plane**, at **line rate on a real multi-queue NIC** (the `22-PERFORMANCE.md`
   budget), feeding the existing `turn_in`/cap-gate.
3. It is published **AGPL-3.0** from a fresh repo with clean provenance, the license
   gate deleted, and every formerly-premium feature free.
4. The confinement theorem (CR-5 negative-safety) is proven against the real config
   types, and **ranges over the full set of 7 confinement soft-spots** (none
   dropped, none laundered — CR-6):
   1. **TLS-mode fallback** — enforce-or-refuse, NEVER silently downgrade
      (`auto-https` + missing-email must not silently become plaintext); generalized
      to the whole `ExposeMethod` fallback chain (auto → Funnel → ACME →
      self-signed → plain).
   2. **address/label → port key-inference** — the orb's inference rules transcribed
      VERBATIM as explicit spec (domain → `:443` + auto-TLS; address → listen;
      label → explicit), with `realize()` proven to honor them.
   3. **runtime-injected dynamism** — **MODELED SEPARATELY** (not excluded) for the
      auth/TLS-issuance subset: on-demand-TLS authz, JWT rotation, health-driven
      upstream state, glob routing, MITM cert-gen, live tunnels.
   4. **proxy/MITM CA** — a host-glob-scoped trust anchor; the CA private key NEVER
      leaves its PD; trust-store injection bounded + declared.
   5. **CONNECT-IP / UDP / MASQUE egress** — a declared-destination-gated capability
      (`ConnectIpAcl`).
   6. **0-RTT / early-data anti-replay bound** — a proven replay-safety property
      (`StrikeRegister` + single-use ticket).
   7. **CGI / process-exec** — an explicit capability obligation vs the seL4
      minimal-cap net PD (which holds only the NIC cap + `turn_in`).

   **Positive-safety dual.** Alongside the negative confinement, the **declared
   resource bounds** (`maxConnections`, `BodyLimit`, `ConnectionLimit`, `RateLimit`,
   per-phase timeouts) are **ENFORCED at every admission point** — *no client can
   exhaust the reactor.*

   **Confinement is a transition-system invariant**, not a single static `C`: for
   every admin mutation / SIGHUP reload `δ`, `realize(apply(δ,C)) ≡
   declared(apply(δ,C))`, with **reload atomicity** — no double-bound-listener
   window, no degraded-TLS window.

Done is not "looks done." Done is "the obligation is discharged and a human can read
the term." (CR-6.)

## Definition of done (per artifact)

Each model / pass / rung is done only when: its proof obligations are discharged or
explicitly handed back (CR-6); it agrees with the oracle on the real workload where
an oracle exists (CR-3); for dataplane artifacts, it meets the perf budget by
verified means (CR-5); and the "wall + lever" is named for anything left open
(`decision-spirit` #9 — documented-honestly is not done; a named gap needs a
successor action).

**Fuzz-coverage criterion (no attacker-facing surface loses coverage).** The orb
shipped **~14 fuzz targets** across its attacker-facing parsers/state-machines.
Each one is, in our tree, **either** (a) **subsumed by a proof** — the property the
fuzzer was hunting for is now a discharged theorem on the verified model — **or**
(b) **a named environment-axiom carrying a continuous fuzz net** — the axiom is
listed (CR-2) and the orb's corresponding fuzz target is ported and run
continuously against our artifact as the successor-rung's standing evidence. There
is **no third option**: an attacker-facing surface that is neither proven nor
fuzz-netted is a `laundered-vacuity` gap (CR-6), not "done."

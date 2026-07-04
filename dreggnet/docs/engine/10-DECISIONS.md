# 10 — DECISIONS (ADR log)

Locked decisions are settled; do not relitigate them — build on them. Open
decisions carry a **default** the fleet proceeds on autonomously plus a
**revisit-trigger** (the evidence that would reopen them). Per `decision-spirit`,
the fleet decides by default and escalates only genuine human-only calls; a novel
fork not covered here is resolved by picking the most Charter-aligned option,
logging it as a new ADR, and proceeding.

Format: **ADR-n — decision — rationale — (status)**.

## Locked

- **ADR-1 — Formal-first, generate-don't-write.** Models are primary; impl is
  emitted from verified models. *Why:* the only way to "zero unverified code" at
  scale; the httpe abstractions are already latent formal objects. (CR-1.) **LOCKED.**

- **ADR-2 — Clean-room; AGPL-3.0; fresh repo.** The engine code + proofs live in a
  fresh repo, clean history, AGPL from commit #1, zero Elide lineage in the tree.
  Elide/Lean are oracles, read-only. *Why:* liberation requires genuinely-independent
  reimplementation by the rights-holder; AGPL makes it un-rug-pullable. (CR-2, CR-3.)
  **LOCKED.** *(Repo location: see ADR-O1 open.)*

- **ADR-3 — Prover/compiler stack = the HOL family + own the compiler.**
  Executable/compiled path → **HOL4 + CakeML + Pancake** (one logic; CakeML's
  verified backend inherited). Crypto + heavy metatheory → **Isabelle/HOL** (the
  existing `uc-crypthol` AFP/CryptHOL foothold), bridged to HOL4 via **OpenTheory**.
  We own + verify the DSL front-end and domain codegen passes; we do **not**
  hand-write-then-verify Rust, and we do not trust an external optimizing compiler.
  *Why:* verified compilation to machine code (deeper than verify-Rust-source over
  unverified rustc); ember's homeland (CakeML devs, l4v); CakeML-compiling the
  kernel later deletes the `sel4-musl`/GMP/libuv hack. (CR-4.) **LOCKED.**

- **ADR-4 — The engine IS the dregg seL4 net PD(s).** Not a standalone server bolted
  onto dregg. It fills the `net` (raw-NIC driver) + `net_client` (protocol/ingress)
  seats of the existing 6-PD Microkit assembly (`~/dev/breadstuffs/sel4/dregg.system`),
  joined by `sel4-shared-ring-buffer`, feeding the existing `turn_in`/Ed25519 cap
  gate, confined by the already-l4v-proven cap algebra (`SeL4Composition.lean`).
  *Why:* the seat already exists (R6, "the virtio/smoltcp tail"); the engine is its
  productionization. **LOCKED.**

- **ADR-5 — Integration seam = the CapTP `Netlayer`.** The engine implements
  `captp/src/netlayer.rs`'s OCapN-style `Netlayer` trait carrying postcard
  `WireMessage` frames, preserving `CapSession` epoch/import-export/GC/promise-
  pipelining semantics. *Why:* "swap the netlayer, the cap semantics don't move" —
  the cleanest drop-in; CapTP is the cap fabric at distance n. **LOCKED.**

- **ADR-6 — Drop PKL.** The Elide orb's PKL config (a GraalVM-native evaluator) is
  not used. The declarative server-node spec is our own, given a formal semantics
  directly. *Why:* the config IS the apex spec — it must be ours and formalizable;
  no GraalVM dependency. **LOCKED.**

- **ADR-7 — The DSL has ~4 primitives.** `machine` (sans-IO transition system),
  `region`/`view` (flat byte region + typed offset views), `linear`
  (acquire→use→release-once resource), `shared` (concurrent object w/ declared
  invariant). Each carries a formal semantics + a proof schema; the engine is their
  composition. *Why:* the scholar study reduced the whole engine to these shapes;
  they are simultaneously the fastest and the most-generatable. **LOCKED.**

- **ADR-8 — Perf architecture = shared-nothing, run-to-completion, zero-copy,
  kernel-bypass, hardware-sharded.** NIC RSS/flow-steering shards connections to
  per-core queues; zero-copy DMA into per-core rings; the parser reads in place; no
  per-packet alloc/syscall/cross-core-sync. *Why:* the per-packet budget is a few
  hundred cycles; and **single-threaded-reactor confinement (the perf design) is
  exactly what licenses 80% of the pure-functional models (the proof design)** —
  one choice buys both. (CR-1, CR-5.) **LOCKED.**

- **ADR-9 — Cell is not the config atom.** The atomic dregg unit is the hash-linked
  data attesting a transformation (the turn/receipt chain); a cell is the fold of
  those. The config-*applied* is a transformation witnessed by receipt-shaped
  hash-linked data — not "a cell." *Why:* ember correction; fits the receipt
  discipline (`receipt` crate / `Receipt.lean` `chain_tamper_evident`). **LOCKED.**

## Open (proceed on the default; revisit on the trigger)

- **ADR-O1 — Repo location & name.** *Default:* a fresh repo named `dreggnet`
  (project name confirmed; "deosnet" was only the spirit's distinctive name). Plans
  currently live in `DreggNet/docs/engine/`; migrate to the fresh repo's `docs/`
  when it exists. *Revisit-trigger:* ember specifies a different location/name.

- **ADR-O2 — First metal NIC target.** *Default:* a well-documented multi-queue NIC
  (Intel E810/X710 family — RSS, Flow Director, sDDF-friendly) to nail the verified
  raw-NIC driver pattern. *Revisit-trigger:* a decision to make the SW/HW co-design
  story real from day one shifts this to **Corundum (open 100G FPGA NIC RTL)** — the
  moat play. Both are on the roadmap; this is only *which first*.

- **ADR-O3 — Develop-substrate sequencing.** *Default:* develop the sans-IO core
  over **Linux (io_uring/AF_XDP)** first, then port the substrate to **seL4/sDDF**
  unchanged (the sans-IO design makes the core substrate-portable). *Revisit-trigger:*
  a hard requirement for zero-Linux-in-the-lineage even during development → seL4-first.

- **ADR-O4 — Kernel reformalization (Track K).** *Default:* run as a **low-priority
  parallel track**, not blocking the engine. Reformalize only the **77-module
  `Exec.FFI` closure** (not the category-theory metatheory) into HOL4 and
  CakeML-compile it (deletes the musl-shim); the cat-theory metatheory stays in Lean
  / migrates to Isabelle later. The existing Lean kernel is the oracle (diff-test).
  *Revisit-trigger:* the vertical-proof (done-criterion #1) requires the kernel's
  abstract soundness, not just its executable closure → pull the metatheory port in.

- **ADR-O5 — Config substrate (post-PKL).** *Default:* a small declarative spec with
  a direct formal semantics; bootstrap on **rpkl** (Apache PKL toolchain, no GraalVM)
  *only if* a PKL-shaped surface is wanted early. *Revisit-trigger:* maturity →
  express the spec as receipt-shaped hash-linked data (ADR-9), unifying it with the
  Microkit `.system` assembly into one verifiable declarative layer.

## Network-orchestrator scope ADRs (the full feature surface)

These resolve the divergence audit's plan-delta: the engine must cover the
*whole* Network Orchestrator surface the orb had, plus the forgotten ones (§5).
**Default = IN.** Omission is not a scope decision — a feature that vanishes by
silence is a CR-6 laundered vacuity, so each is named explicitly even when the
call is "yes, in." The done-criterion #2 (Charter) the dataplane work serves now
reads: *serves CapTP + HTTP/1/2/3 + the reverse/forward/L4 proxy dataplanes + the
mesh data plane, at line rate on a real multi-queue NIC, feeding turn_in/cap-gate.*

- **ADR-N1 — WebRTC, gRPC + gRPC-Web, `expose --persist`, embedded CT log are IN.**
  *Decision:* all four are in-scope first-class, not silently dropped. WebRTC and
  gRPC/gRPC-Web are additional ingress dataplanes feeding the same turn_in/cap-gate
  (ADR-4) and modeled as `machine` transition systems (ADR-7) like every other
  protocol; gRPC-Web is the HTTP/2-framing-over-HTTP/1 transcode, not a new auth
  surface. `expose --persist` (the persistent expose daemon) is a control-plane
  lifecycle mode, not a dataplane primitive — it is a long-lived supervised
  reconcile loop whose every mutation is a transition δ subject to the confinement
  invariant (ADR-N5), not a one-shot. The embedded CT log is in as a positive
  capability (it issues + monitors, it does not relax any confinement obligation).
  *Why:* the audit found these absent from the plan only by omission; default-IN
  forbids reading omission as exclusion. (CR-6.) **DECIDED (IN; WebRTC sequenced
  AFTER the mesh + QUIC ranks — ember's call: it reuses their DTLS/ICE/crypto
  foundations, so building it later avoids duplicating the handshake/crypto work.
  Scope IN, sequencing resolved; mirrors 21-FORMAL ADR-N1).**

- **ADR-N2 — CGI / process-exec under the seL4 minimal-cap net PD.** *Decision:*
  model CGI/process-exec as a **separate dregg PD** with its own capability set,
  reached over CapTP, **not** as an ambient `fork+exec` inside the net PD. The net
  PD holds the minimal cap set (the NIC cap + `turn_in`); spawning a CGI child is a
  distinct capability obligation (soft-spot #7) that the net PD demonstrably does
  *not* possess, so it cannot be smuggled in as an "and also it runs processes."
  A CGI request becomes a cap-gated turn to the exec PD, which is where the
  process-spawn authority lives and is separately confined. *Why:* preserves
  ADR-4's minimal-cap net PD and the cap algebra (`SeL4Composition.lean`); the orb
  ran CGI in-process, but the seL4 substrate makes that a genuine privilege
  escalation we refuse to launder. **DECIDED (separate cap-gated exec PD) — ember
  confirmed the PD-split over dropping CGI. The exec authority becomes explicit and
  declared (a cap-gated turn to the exec PD), strictly more assured than the orb's
  in-process exec.**

- **ADR-N3 — Zero-downtime upgrade on a static-PD substrate.** *Decision:* achieve
  the orb's hot-reload/zero-downtime-upgrade property by **PD respawn + capability
  handoff** (a new net PD instance is stood up, the listening-socket / NIC-queue
  caps are handed to it, the old PD drains and retires), **not** by a Linux-style
  in-process `re-exec`/`fork` — which ADR-4's static seL4 PD model forbids (no fork
  on seL4). This reconciles with ADR-4: the PD is static, but the *assembly* can
  rebind a cap from old→new instance atomically. The reload-atomicity clause of the
  confinement invariant (ADR-N5: no double-bound-listener window, no degraded-TLS
  window) is the correctness obligation the handoff must discharge. *Why:* the orb's
  zero-downtime story is real and wanted, but its mechanism (re-exec, fd-passing
  within one process) is unavailable on a static-PD substrate; cap handoff is the
  substrate-native equivalent. **DECIDED (cap handoff) — ember confirmed.**
  *Grounding (ember):* cap migration + persistence is an **existing firmament role**
  — the checkpoint/restore substrate ("a PD checkpoint IS a dregg snapshot",
  `breadstuffs/docs/FIRMAMENT.md`), with the cap algebra already proven in
  `metatheory/Dregg2/Firmament/`. It is NOT net-new design. The named work is
  realizing it under **Microkit specifically**, which is statically-architected and
  does not provide live cap rebind/migration out of the box — so the firmament
  cap-migration/persistence substrate must be ported/extended onto the Microkit
  assembly. *Prerequisite to chart before the upgrade rungs (R4.11 / R7):* the
  firmament's existing cap-migration + persistence design
  (`~/dev/breadstuffs/sel4/dregg-firmament/`, `metatheory/Dregg2/Firmament/`) and the
  precise Microkit gap.

- **ADR-N4 — TLS record FSM + QUIC engine trust status.** *Decision:* the TLS-record
  state machine and the QUIC transport engine are **own-verified `machine`s**
  (ADR-7), produced on the formal-first path (ADR-1) — they are *not* axiomatized
  trusted blobs. This resolves the 21↔22 contradiction: rung **21-FORMAL** had
  axiomatized rustls as a trusted boundary, while rung **22** + **CR-2** forbid
  unverified crypto in the lineage. The reconciliation: the *cryptographic
  primitives* (AEAD, KDF, signature) may sit behind the explicitly-enlarged **CR-2
  axiom** with a named **successor rung (R5.4)** that discharges them (via the Isabelle/
  CryptHOL `uc-crypthol` foothold, ADR-3), but the *record-layer / handshake / QUIC
  transport FSM* — the part that decides plaintext-vs-encrypted, key epochs, and
  0-RTT acceptance — is a verified machine, because that FSM is exactly where
  soft-spots #1 (TLS-mode fallback) and #6 (0-RTT anti-replay) live and must be
  proven, not trusted. So: axiom shrinks to the primitives; the FSM is verified.
  *Why:* axiomatizing the whole of rustls (21-FORMAL) would swallow the confinement
  soft-spots into a trusted blob, which CR-2/CR-6 forbid; axiomatizing only the
  primitives keeps the security-deciding logic inside the proof. **DECIDED (verified
  FSM, axiom narrowed to primitives + successor rung R5.4).**

- **ADR-N5 — Runtime SocketPolicy as defense-in-depth; live policy mutation.**
  *Decision:* the static confinement theorem — for every admin mutation / SIGHUP
  reload δ, `realize(apply(δ,C)) ≡ declared(apply(δ,C))` with reload atomicity — is
  the primary guarantee. A **runtime `SocketPolicy`** (the dynamic admission/egress
  check at each accept/connect/exec point) is retained as **defense-in-depth**, not
  as the proof: it is the belt to the theorem's suspenders, and it is also where the
  positive-safety dual lives — declared resource bounds (`maxConnections`,
  `BodyLimit`, `ConnectionLimit`, `RateLimit`, per-phase timeouts) are *enforced at
  every admission point* so no client can exhaust the reactor (ADR-8's
  single-threaded reactor is exactly what makes "exhaust the reactor" a real DoS
  axis). On **live `ArcSwap` policy mutation** (hot-swapping the policy object while
  connections are in flight): we **model it, we do not forbid it** — a live swap is
  a transition δ and must satisfy the same invariant (no window in which an
  in-flight connection is governed by neither the old nor the new policy, no
  degraded-TLS window). The confinement property is therefore a **transition-system
  invariant, not a single static C**: it ranges over all 7 soft-spots after every δ,
  including the policy-swap δ itself. *Why:* a static-only theorem would be silent
  exactly during reloads/swaps — the moment operators actually change posture — so
  the invariant must be closed under mutation; the runtime policy then catches
  anything the model's abstraction gap missed. (CR-6: the runtime check is real
  enforcement, not a hand-back.) **DECIDED (model live mutation, keep runtime policy
  as defense-in-depth).**

- **ADR-N6 — Transport scope: verified QUIC/H3; TCP is a named axiom.** *Decision:* a
  verified TCP/IP stack is **OUT of scope** (a multi-year stack in its own right).
  Instead: **QUIC/H3 is the first-class verified transport** (F-6, R2.5), and the
  general TCP/IP below the HTTP/1/2 and CapTP-over-TCP listeners is a **named CR-2
  environment axiom** — a trusted boundary like the NIC DMA contract, *named not
  hidden*, with **no successor rung** (verified TCP is explicitly not a goal, so this
  is not a laundered "we'll prove it later"). Pleasing sub-decision: **run CapTP over
  QUIC** (not only TCP) — QUIC's multiplexing / 0-RTT / NAT-traversal /
  connection-migration are exactly what CapTP wants — so the *entire verified path*
  is QUIC-based and TCP-HTTP/1/2 is the legacy compat shim over the TCP axiom. *Why:*
  concentrate the verification budget on the transport that matters (and that the
  dreggnet cloud's primary path uses), keep CR-2 honest, and unify the verified
  transport on one engine. **DECIDED (QUIC/H3 verified + CapTP-over-QUIC; TCP a named
  axiom, no successor rung).**

- **ADR-N7 — Non-interference + the cross-layer property set; cap-domain-parametric
  (obligation X-5).** *Decision:* the confinement theorem (inbound negative-safety) is
  joined by a cross-layer property set that makes "a fully formal model of ALL network
  activity" literal: **no-undeclared-egress** (the engine connects out only where the
  config declares — kills SSRF/exfil; the outbound dual of confinement) and
  **total-accounting** (every byte/connection/CPU-tick metered, conserved, receipted —
  see ADR-N8) are **IN now as theorems**; **non-interference** (no information flow
  between tenant/exposure cap-domains except via declared mediated channels) is **IN
  as a design-for-and-prove goal**, grounded in the l4v-proven seL4 cap-partition
  (`SeL4Composition`) extended to the byte layer; **end-to-end secrecy**
  (ciphertext → declared-plaintext → declared-handler, no cross-layer leak) is
  **named-but-deferred** (the one hard IFC theorem — not laundered, explicitly later).
  *Method for NI:* prefer **NI-by-construction** — make every model
  **cap-domain-parametric** (scoped to a cap-domain; cross-domain interaction ONLY via
  declared channels) so isolation is structural and the proof reduces to the channels;
  reach for an abstract partition spec + **security-preserving refinement** (NOT
  vanilla refinement — the refinement paradox can leak; cf. the seL4 NI proof) only
  where by-construction is insufficient; keep the refinement shallow, not a tower,
  unless forced. *Standing obligation* **X-5 — cap-domain-parametric, no ambient
  cross-domain flow** (add to 21-FORMAL's cross-cutting obligations): every model
  carries its cap-domain, adopted from rung one so NI stays achievable even before it
  is proven. **DECIDED (NI in-scope, NI-by-construction + X-5; egress + accounting as
  theorems now; e2e-secrecy deferred-named).**

- **ADR-N8 — Unifications adopted as architecture (framing, not new builds).**
  *Decision:* adopt these as first-class architecture — they are cheap (reuse of
  existing substrate) and they weld the verified netstack to the dregg core:
  - **Accounting = conservation.** The netstack's rate/conn/body/bandwidth limits + the
    hosting-lease meter + the billing-tick are ONE conserving-accounting model (dregg's
    `Payable`/`StandingObligation`/conservation law). The DoS-safety theorem and the
    cloud billing are the *same* proof. (Realizes `total-accounting`, ADR-N7.)
  - **Observability = receipts.** Logs/metrics/traces and the CT-log are *views* over
    the dregg receipt chain (`chain_tamper_evident`, re-witnessable). Every network
    event emits a receipt; dashboards are projections — not a bolt-on logging system.
    (Subsumes the observability gap-group.)
  - **Cap-fabric as the spine.** A listener/route/connection/tenant/lease/egress/CA/turn
    is a capability at distance n; the netstack is the cap fabric's network reach.
    Confinement, the lease, the session, and accounting are facets of one cap discipline.
  - **Session + one migration theorem.** HTTP/CapTP/QUIC/WS/mesh/WebRTC are cap-scoped
    sessions with one lifecycle; the four migration mechanisms (orb-memfd, kTLS
    secret-inject, H2 mid-stream, firmament PD-checkpoint) become one
    *migration-preserves-the-session-invariant* theorem.
  - **Time-as-input + the DSL composition theorem.** Time is an explicit sans-IO input
    (the kernel tick a named axiom), unifying every timer; the composition theorem (the
    4 primitives compose soundly) makes the DSL a *calculus*, not a kit.
  **DECIDED (adopt all five as architecture; weave into 20-ARCHITECTURE).**

## Decision-spirit anchors (how to resolve anything not above)

When a fork isn't covered: apply the spirit's Tier-0 gates (premise-live?
ground-truth? cheapest-probe?), select the heuristics the choice touches, pick the
most Charter-aligned reversible path, write the ADR, and continue. Never hand an
option-menu to the human for a call the docs + spirit can make. Escalate only:
destructive/irreversible ops, public/shared pushes, credentials, brand/release
names, or genuine vision calls.

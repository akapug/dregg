# 21 — FORMAL MODEL (the difficulty-ranked build order)

The technical spine. Derived from a deep scholar study of the Elide
`httpe`/`iocoreo`/`cq` in-memory representations (the oracle, an internal Elide HTTP-engine source tree, and
the vendored copy `DreggNet/net/`). **Headline: the engine is ~80%
pure-functional.** Only four sharp objects need heavy concurrent machinery.

For each representation the formal artifact is a triple: **the type** (datatype),
**the invariant** (a `wf` predicate the prover carries), **the transition
structure** (relations / `step` functions). Write the pure ranks as HOL/CakeML and
**generate** from them (ADR-1); reserve Iris for ranks 5–7; treat rank 8 as the
trusted/known-fragile perimeter to *fix by construction*.

Oracle file:line citations live in the memory note `dreggnet-formal-model-skeleton`
and the scholar transcript; this doc is the build order.

## Pure-functional pillars — formalize + generate FIRST (most of the surface)

- **Rank 1 — the arena request model.** `ParsedRequest` + the HPACK/QPACK
  arena-decode results + `PseudoHeaders`. All are "immutable byte arena +
  `(name_tag, off, len)` triples," identical across H1 (pointer-arithmetic), HPACK,
  QPACK; a high-bit-tagged sidecar union (`SIDECAR_OFFSET_BASE = 0x8000_0000`)
  partitions arena vs mutation offsets. **Model:** record + `wf_parsed_request`
  (every range `off+len ≤ arena.len()` or in-sidecar; all ranges valid UTF-8). The
  UTF-8 predicate becomes an **explicit hypothesis discharged by the EverParse
  parser proof** — not `from_utf8_unchecked` folklore. *Difficulty:* pure & easy.
  **Write this first** — highest leverage, cleanest, sets the discipline.

- **Rank 2 — the connection FSM.** `ProtocolState` (19 variants) / `ConnectionState`
  / the per-stream states. `step : State × Input → State × Output*`, sans-IO; the
  parse step is typed `Complete{body_offset} | Incomplete | Error`. Biggest
  datatype, **zero concurrency.** Axiomatize the embedded codecs (rustls
  `UnbufferedServerConnection`, `H2Connection`, `WsDecoder`) as **effect interfaces**
  so the connection FSM proves independently of TLS internals. *Difficulty:* pure
  (large).

- **Rank 3 — the slab + generation epochs.** `ConnSlab` = a verified
  `fd ⇀ ConnectionState` map (two-level array `fd_index`/`slots` + LIFO `free`-list
  data refinement; coupling invariant = the fd↔slot bijection). The generation
  counter is a **monotone process epoch** (skip-0) tagging each connection
  incarnation; the stale-event guard is `event.epoch == current_epoch(fd)`
  (ABA/fd-reuse defense). *Difficulty:* pure, **+1 explicit axiom** (`u64`
  wraparound — assume no wrap within an fd's lifetime, or model `ℤ/2^64` and prove
  no two simultaneously-relevant incarnations collide).

- **Rank 4 — the pools.** `BufferPool` (7 size classes 1K–64K) + `RecvBufferPool`
  (2-class, LIFO, reactor-local; the "idle connection holds zero heap" diet —
  reclaim only when `recv_len==0`). **Model:** `Fin n → list (capacity-tagged
  buffer)` with exact-capacity + length-cap invariants. *Difficulty:* pure &
  trivial — do these as warm-ups to fix conventions.

## The four sharp points — heavy machinery, delimited

- **Rank 5 — SPSC `Ring<T>`.** The one object needing **Iris logical atomicity** +
  release/acquire memory-model reasoning. Invariant `head ≤ tail ≤ head + capacity`
  (free-running counters, masked only on index); per-slot init-permission tokens
  (slot `i` init ⟺ `head ≤ i < tail`); single-producer/single-consumer enforced at
  the type level (`Cell` makes `Sender` `!Sync`; `&mut self` makes `Receiver`
  single-consumer). Canonical Iris SPSC proof exists. `CachePad` is a logical no-op.

- **Rank 6 — the one-shot `CrossFuture`/`CompletionSlot`.** A 3-state atomic token
  (`PENDING→COMPLETED|CANCELLED`) with a single payload cell and a complete-vs-drop
  race. **Iris-light** (a one-shot RA); much simpler than the ring (no indices/laps).
  The FFI `i64` handle is an affine resource crossing an opaque boundary.

- **Rank 7 — `BufRing` + `BufRingLease`.** A bounded `count × buf_size` byte matrix
  + a **DMA-shared tail = one device axiom** (the kernel/NIC only consumes entries
  below the `Release`-published tail, fills buffers, returns `(bid, len)` with
  `len ≤ buf_size`). The lease is a **separation-logic token** (own `bid`'s row
  until drop; recycle-exactly-once). `WakerCell` (a small lock-invariant object)
  rides along.

## The trusted/fragile perimeter

- **Rank 8 — `PooledBuf` / `BorrowedBuf`.** The linear-resource perimeter, and the
  project's one known-unsound spot: `PooledBuf`'s `*mut BufferPool` has no lifetime
  guard (a documented `ROBOTODO` — a `Bytes` escaping to another thread after CQ
  teardown dereferences a dangling pointer). **Fix by construction (CR-2):** replace
  `*mut` with a handle carrying a validity proposition, so "pool outlives buffer"
  is a *checked side-condition*, not folklore. `BorrowedBuf` (caller-owned/foreign
  memory) is a labeled trusted axiom — and **largely vanishes in the clean-room**
  (no JVM ByteBufs), leaving essentially the one NIC device axiom.

## Four cross-cutting obligations (carry globally as model parameters)

- **X-1 — single-threaded-reactor confinement.** Licenses ~all the metal's
  `unsafe impl Send`/`!Sync`/raw-pointer code. Make it a top-level model parameter
  ("this lives on core/thread T"). **Discharged by the seL4 per-core shared-nothing
  PD architecture (ADR-8)** — the perf design *is* the confinement proof.
- **X-2 — validated-UTF-8** on every arena range → a **parser-discharged
  hypothesis** (EverParse). Ranks 1 + the parser *compose*: the parser closes the
  arena's only open hypothesis.
- **X-3 — modular wraparound** (`u64` generation, `u16` BufRing tail) → explicit
  modular-arithmetic assumptions.
- **X-4 — exactly-once recycle/return linearity**, shared by `BufRingLease`,
  `PooledBuf`, and the `DispatchDecision` guards → **one** separation-logic token
  discipline reused across all of them (don't reinvent per object).

## The Network-Orchestrator feature ranks (F-1 … F-13) — the dataplane bulk

Ranks 1–8 model the *reactor substrate*. The Network Orchestrator's actual feature
surface — routing, middleware, proxy/MITM, L4/SNI, QUIC, mesh, the parser zoo,
caching, anti-replay — rides on top and is **overwhelmingly pure** (the same ~80%
verdict holds). These close the divergence-audit plan-delta: the substrate was
modeled, the orchestrator features were **not**. Default for every feature: **IN**.
Each F-rank carries the same triple (type / invariant / transition) and a difficulty
tag drawn from {pure-functional, machine, shared, device}.

- **F-1 — Router / dispatch.** Type: ordered `[RouteMatch → Handler]`. The relation
  `dispatch : Request → Route list → Handler option` is **total, deterministic, and
  first-match-decidable**; a `RouteMatch` is an **AND-conjunction** over
  path/host/method/header/query predicates. Invariant: `dispatch` returns the
  *least-index* matching route (well-defined tie-break, no ambiguity). Transition:
  pure fold. *Difficulty:* **pure-functional**. **Closes** the "no routing model"
  gap; the §2 address/label→port key-inference soft-spot composes here (inferred
  listener keys feed the route table).

- **F-2 — Middleware-as-machine.** Each middleware is a **pure step** over
  `(Request, Decision) → (Request, Decision)`; the chain is a fold with short-circuit
  on `Deny`. Model the auth family as **decision relations with anti-bypass
  theorems**: jwt (alg-**allowlist**, no `none`, no alg-confusion), basic (bcrypt
  verify), `auth_request` (subrequest verdict), tailscale (**deny-before-allow**),
  `ip_filter` (CIDR with **deny-precedence**). Anti-bypass theorem shape: *no input
  drives the chain to `Allow` without the guarding middleware having itself returned
  `Allow`* — there is no path around the gate. *Difficulty:* **machine** (small FSMs)
  over pure predicates. **Closes** the auth/authz subset of the §3 runtime-injected
  dynamism (MODELED SEPARATELY here, **not** excluded).

- **F-3 — Proxy-director.** Load-balancer selection `select : UpstreamStatus vector
  → Upstream` is a **pure fn** (round-robin / least-conn / hash, total over the status
  vector). Circuit-breaker and health-probe are **machine FSMs**:
  closed→open→half-open, with the property **half-open admits exactly one probe** (a
  single-token guard). The upstream pool is a **linear/shared** resource (lease
  discipline reused from X-4). *Difficulty:* **machine**. **Closes** §3 health-driven
  upstream-state dynamism; the positive-safety `ConnectionLimit`/pool bounds attach
  here.

- **F-4 — Forward-proxy + MITM.** The proxy-rule interception relation is
  **first-match** (same decidability shape as F-1). MITM cert generation carries a
  **cert-cache** (host → leaf, generated-once); the **proxy CA is a scope-bounded
  trust anchor** — host-glob-scoped, and **the CA private key never leaves its PD**
  (a confinement obligation, §4). Trust-store injection is bounded+declared.
  *Difficulty:* **machine** + one **device**/PD axiom (CA key custody). **Closes** §4
  proxy/MITM-CA soft-spot.

- **F-5 — L4 / SNI.** ClientHello **SNI extraction is an EverParse/region parser**
  (no hand byte-poking into the handshake). L4 route selection is a **pure fn** over
  the extracted SNI/ALPN. Key property: **splice-without-termination** — the L4 path
  forwards bytes without ever decrypting (not in the TLS trust path here; contrast
  F-4). *Difficulty:* **pure-functional** (parser + selection fn). **Closes** the "no
  L4/SNI dataplane" gap.

- **F-6 — QUIC connection / stream FSM.** Same **sans-IO** shape as Rank 2 (`step :
  State × Input → State × Output*`, zero concurrency). QUIC wire parsers (initial /
  frame / varint / transport-params / ack-ranges) are **EverParse**. State covers
  0-RTT, loss-detection, and congestion-control bookkeeping. **Honesty (wall+lever):**
  where a full QUIC state proof is out of reach this rung is explicitly
  **verify-vs-named-axiom-with-fuzz-net** — the FSM is checked against a *named* axiom
  carrying a **continuous fuzz net**, never silently trusted. *Difficulty:* **pure**
  (large) + named axioms. **Closes** the "H3/QUIC unmodeled" gap; composes with the
  §6 anti-replay bound (F-9).

- **F-7 — Mesh.** Five sub-ranks: (a) **Noise-IK handshake FSM**; (b) the
  **WireGuard transform** (ChaCha20-Poly1305) discharged via **HACL\*/Vale** verified
  crypto; (c) **DERP framing** parser; (d) **DISCO NaCl-box** (sealed-box predicate);
  (e) the **smoltcp netstack** interface as an effect boundary. The mesh **control
  FSM + netmap apply** are **cold-path** (config-rate, not packet-rate) — model as
  machine, not perf-critical. *Difficulty:* **machine** + borrowed crypto axioms
  (HACL\*). **Closes** the "mesh data plane entirely unmodeled" gap; the mesh data
  plane is part of the amended Done-Criterion #2 served set.

- **F-8 — Parser-coverage.** EverParse parsers for the orb's full wire zoo:
  **CGI-response, FastCGI, SOCKS 4/4a/5, PROXY-protocol v1/v2, DNS message,
  Capsule-Protocol (MASQUE)**. Each carries the **orb's existing fuzz corpus as the
  continuous net** (regression + differential against the oracle). *Difficulty:*
  **pure-functional**. **Closes** the parser-surface gap; the Capsule parser is the
  wire half of the §5 CONNECT-IP/UDP/MASQUE soft-spot.

- **F-9 — Anti-replay.** `StrikeRegister` + **single-use resumption ticket** as a
  **shared object** with an explicit **replay-safety invariant**: *a ticket / early-
  data unit is accepted at most once* (0-RTT early-data is replay-bounded).
  *Difficulty:* **shared** (one single-use separation-logic token, reused from X-4).
  **Closes** the §6 0-RTT/early-data anti-replay soft-spot.

- **F-10 — Cache-semantics.** RFC 7234 **freshness / revalidation** as a **pure fn**
  (`is_fresh`, `must_revalidate`, age computation — total over response metadata +
  clock). **Request-coalescing single-flight** is a **shared** object (the in-flight
  map admits one origin fetch per key; followers attach). *Difficulty:*
  **pure-functional** + one **shared** object. **Closes** the caching gap.

- **F-11 — Cookie-jar + DNS-resolver.** Cookie predicates (**Secure / SameSite /
  HttpOnly**) as **theorems** (a Secure cookie is never emitted over plaintext; a
  `SameSite=Strict` cookie is never attached cross-site). The resolver **cache +
  Happy-Eyeballs** racing is a **machine** (dual-stack connect FSM with the RFC-8305
  timer). *Difficulty:* **pure-functional** (predicates) + **machine** (resolver).
  **Closes** the client-state gap.

- **F-12 — TLS-record FSM + H2 framing successor rung (resolves the 21↔22
  contradiction; ADR-N4).** Rank 2 axiomatizes rustls/H2 as **effect interfaces**; doc
  22 wants them proven — a live contradiction. **Resolution (ADR-N4):** *either*
  schedule them as the explicit **successor rung R5.4** *or* re-label them **enlarged
  CR-2 axioms carrying a fuzz net** — pick per object, but **name the choice** (no
  silent gap between 21 and 22). The TLS-record/handshake FSM (read/write half-states,
  **no plaintext-after-close**, the plaintext-vs-encrypted / key-epoch / 0-RTT-accept
  decision) is verified as a `machine` and the crypto primitives narrow to the CR-2
  axiom that **R5.4** retires; H2 framing (HEADERS/CONTINUATION/SETTINGS/flow-control)
  gets the named-axiom-with-fuzz-net treatment. *Difficulty:* **pure** (FSM) + named
  CR-2 axiom + fuzz net. **Closes** the 21↔22 divergence the audit flagged; the TLS/QUIC
  trust-status resolution is ADR-N4.

- **F-13 — CGI / StaticFiles confinement.** **StaticFiles:** a theorem that **no
  served path escapes root** (canonicalize-then-prefix-check; no `..` / symlink /
  percent-encoding escape). **CGI:** **process-exec is an explicit capability
  obligation** weighed against the net PD's minimal cap set (§7) — the net PD holds
  only the NIC cap + `turn_in`; spawning a CGI process is an **additional declared
  capability**, not ambient. *Difficulty:* **pure-functional** (path theorem) + one
  capability ADR. **Closes** the §7 CGI/process-exec soft-spot. **See ADR-N2.**
  The StaticFiles no-path-escape theorem lands as a roadmap rung at **R4.9**.

## The confinement theorem (the residual hand-proof, ranging over 7 soft-spots)

The auto-discharge note below names "the confinement theorem" as residual; make it
precise. **Confinement is a transition-system invariant**, not a single static `C`:
for every admin mutation / SIGHUP reload `δ`,

    realize(apply(δ, C)) ≡ declared(apply(δ, C))

with **reload atomicity** — **no double-bound-listener window, no degraded-TLS
window** across the swap. The realized network behavior never exceeds the declared
config, *and stays that way under every reconfiguration step.*

The theorem **ranges over all 7 confinement soft-spots** (canonical numbering; none
may be laundered to vacuity — CR-6; every obligation below is real or explicitly
handed-back, none is a soft-spot we secretly mean to skip):

1. **TLS-mode fallback — enforce-or-refuse, never silent downgrade.** auto-https +
   missing-email must **refuse**, not silently become plaintext. Generalize over the
   whole `ExposeMethod` fallback chain (auto → Funnel → ACME → self-signed → plain):
   every downgrade edge is either *declared* or *refused* — no silent edge exists.
2. **address/label→port key-inference.** Transcribe the orb's rules **verbatim** as
   explicit spec — domain→`:443`+auto-TLS; address→listen; label→explicit — and prove
   `realize()` honors them (composes with F-1).
3. **runtime-injected dynamism — MODELED SEPARATELY (not excluded).** The
   auth/TLS-issuance subset — on-demand-TLS authz, JWT rotation, health-driven
   upstream state, glob routing, MITM cert-gen, live tunnels — is modeled by
   F-2/F-3/F-4/F-9, never waved away.
4. **proxy / MITM CA** — a host-glob-scoped trust anchor; **CA private key never
   leaves its PD**; trust-store injection bounded+declared (F-4).
5. **CONNECT-IP / UDP / MASQUE egress** — a **declared-destination-gated** capability
   (`ConnectIpAcl`): no egress to an undeclared destination (wire half in F-8).
6. **0-RTT / early-data anti-replay bound** — the proven replay-safety property
   (StrikeRegister + single-use ticket, F-9).
7. **CGI / process-exec** — an explicit capability obligation vs the seL4 minimal-cap
   net PD (holds only the NIC cap + `turn_in`); process-exec is additional+declared
   (F-13, ADR-N2).

**Positive-safety dual** (carry *alongside* the negative confinement, not instead of
it): the declared resource bounds — `maxConnections`, `BodyLimit`, `ConnectionLimit`,
`RateLimit`, per-phase timeouts — are **enforced at every admission point**.
Property: ***no client can exhaust the reactor.*** This is the liveness/availability
complement to "realized ≤ declared"; it attaches at F-3 (pool/conn limits) and Rank 2
(per-phase timeouts).

## ADRs for the genuine forks (FLAG-FOR-EMBER)

These are real scope/vision forks (not routine ranks); each picks the most
Charter-aligned option and is **flagged for ember**, but **none blocks** the build.

- **ADR-N1 — WebRTC / gRPC / `--persist` / CT-log: all IN; WebRTC *sequencing*
  flagged. FLAG-FOR-EMBER.** **Decision (IN-scope per the directive, with the
  most-Charter-aligned framing):** gRPC = a route/codec profile over the existing H2
  dataplane (in, cheap); `--persist` = a declared connection-reuse policy on F-3 (in);
  CT-log submission = a declared egress under the §5 `ConnectIpAcl` + an
  append-only-log obligation (in, but cold); **WebRTC = IN-scope too, but the one I'd
  flag** — its ICE/DTLS/SCTP stack is a large new parser+FSM surface (a whole sibling
  of F-6). The flag is **not** in-or-out (it is in); it is purely *sequencing*: whether
  WebRTC lands now vs. after the mesh ranks. *Flag:* ember to confirm WebRTC's phase
  placement (now vs. deferred past the mesh ranks) — scope is settled as IN (matches
  10-DECISIONS ADR-N1).

- **ADR-N2 — CGI process-exec under a minimal-cap net PD. FLAG-FOR-EMBER.** The orb
  shells out for CGI; the seL4 net PD is meant to hold *only* the NIC cap + `turn_in`.
  **Decision (most-Charter-aligned): IN, but never ambient** — process-exec is a
  *separately declared capability* the net PD does not possess by default; a CGI
  handler runs in a distinct exec-capable PD reached over a declared channel, so the
  net PD's minimal-cap proof is preserved. F-13 carries the obligation. *Flag:* ember
  to confirm we want CGI at all vs. dropping it for FastCGI-only (F-8).

- **ADR-N3 — zero-downtime upgrade on a static seL4 PD. FLAG-FOR-EMBER.** The orb does
  live binary upgrade; a static seL4 PD has no `exec`/`fork`. **Decision: model the
  *reload* path (SIGHUP config swap) as the transition-system invariant above
  (atomic, no double-bound-listener / no degraded-TLS window); treat full binary
  hot-upgrade as out-of-PD** — handled by a supervisor restarting the PD with state
  hand-off, not by the PD rewriting itself. *Flag:* ember to confirm supervisor-driven
  restart is an acceptable substitute for in-process hot-upgrade.

## How "~90% of the proofs auto-discharge" (CR-1, ADR-7)

Each DSL primitive emits a proof schema; the **routine obligation classes** —
in-bounds, no-overflow, totality, determinism, `wf`-preservation, exactly-once
linearity — are discharged by generated reflective tactics / SMT / Sledgehammer +
the compiler-correctness theorem. The DSL **surfaces exactly the residual** for
hand-proof: the rank 5–7 concurrent invariants, the F-rank anti-bypass / replay /
half-open / no-path-escape theorems and their named-axiom-with-fuzz-net rungs (F-6,
F-12), and the confinement theorem — now a **transition-system invariant ranging over
the 7 soft-spots** plus its positive-safety dual. That is the precise meaning of
"generate most of the specs and proofs semi-automatically."

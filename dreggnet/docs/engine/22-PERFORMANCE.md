# 22 — PERFORMANCE (the budget, as an acceptance criterion)

Per CR-5, line-rate is **not an aspiration — it is a done-criterion** for dataplane
artifacts, achieved *by verified means* (never by dropping to unverified code). This
doc fixes the budget the fleet measures against and the design rules that meet it.

## The budget (what "highest performance" means numerically)

- **Target: line rate.** At 100 GbE with minimum-size frames that is **~148 Mpps**;
  at 200/400 GbE, proportionally more. The binding constraint at small packets is
  **packets-per-second**, not bandwidth.
- **Per-packet budget on a core: a few hundred CPU cycles** (~tens of ns). This
  number dictates the design:
  - `malloc` is ~100 ns → **no per-packet allocation.**
  - a syscall is ~1 µs → **no per-packet syscall** (kernel-bypass / batched io_uring).
  - a cache miss is ~100 ns → **cache-resident hot state, prefetch, NUMA-local.**
  - a mispredict is ~tens of cycles → **branch-lean, data-oriented hot loops.**
- **HTTP-level target:** millions of requests/sec per box (Cloudflare-tier). The
  per-request budget is larger but the same rules (zero-alloc, zero-copy,
  run-to-completion) apply. Reference point: OxCaml's `httpz` hit 6.5M req/s
  *parsing* with zero heap allocation — the bar for the parse path.

## The design rules that hit it (ADR-8)

1. **NIC does the demux.** RSS / Flow-Director / programmable steering shards each
   connection (5-tuple, or QUIC-CID) to a fixed core's RX queue. **Zero software
   steering on the hot path.**
2. **Zero-copy DMA.** The NIC writes packets directly into the core's hugepage
   buffer ring (Rank 7's `BufRing` at raw-NIC descriptor level); the parser reads
   **in place** (the arena *is* the DMA buffer). No memcpy, NIC→parser.
3. **Run-to-completion, shared-nothing per core.** accept→parse→dispatch→respond on
   one core, no handoff, no lock, no cross-core atomic on the datapath. (This is X-1
   confinement — the perf design *is* the proof design.)
4. **Batched, no steady-state allocation.** multishot recv; provided buffers; pool
   everything (Ranks 4, 7, 8); arena parsing.
5. **Crypto:** kTLS or NIC-inline-TLS where the hardware offers it; else **HACL\*/Vale
   verified-asm** (competitive with hand-tuned C, *with* a proof). Never unverified
   crypto. *(Per **ADR-N4**: TLS record/handshake processing on the lineage is a
   **verified `machine` FSM** — the plaintext-vs-encrypted / key-epoch / 0-RTT decision
   is proven, not trusted — and only the crypto **primitives** are axiomatized, behind
   the narrowed CR-2 axiom that the named successor rung **R5.4** retires into proof. No
   unverified TLS logic ships on the hot path.)*
6. **Busy-poll at load, interrupt/coalesce at idle.**

## The orchestrator dataplane rules (ADR-8 cont.)

The six rules above are the *substrate* budget (NIC→parser). The Network Orchestrator
adds a proxy/tunnel/QUIC/WireGuard dataplane on top, and each piece has its own hot
path with its own way to silently regress. These rules are additive and carry
**component-level** acceptance criteria — a piece that meets rule 1–6 but blows its
own budget is still a fail. (Same CR-5 logic: the budget *is* the done-criterion, per
component, not just end-to-end.)

- **PF-1 — proxy hot-path budget.** The reverse/forward/L4 proxy dataplane (DONE-#2:
  CapTP + HTTP/1/2/3 + reverse/forward/L4 + mesh) runs **zero-copy splice**
  (NIC→upstream socket without a userspace bounce where the splice is legal),
  **upstream connection-pool reuse** (no per-request dial/TLS-handshake on a warm
  pool), a **two-tier (RAM+disk) cache hit path** that serves a hit without touching
  the origin, **request-coalescing** (N concurrent misses for the same key collapse to
  one upstream fetch), an explicit **buffer-vs-stream threshold** (small bodies
  buffered, large bodies streamed — the threshold is declared, not a heap-size
  accident), and **SSE / event-stream fan-out** (one upstream stream → many
  subscribers without re-pulling). Acceptance: each component states a throughput
  number (cache-hit req/s, pooled-vs-cold dial ratio, coalesce dedup factor under a
  thundering-herd, splice GB/s) and is measured against it. A coalescer that doesn't
  dedup, or a "pool" that silently dials per request, is a
  `claimed-fast-path-is-cold-path` bug.
- **PF-2 — UDP/QUIC datapath (send-side is not optional).** The QUIC datapath must
  use the kernel segmentation offloads on **both** directions: **GRO** (recv
  coalescing), **GSO** (send segmentation — one syscall emits many packets),
  **ECN** (congestion signal, not loss-only), and **pktinfo** (correct source-address
  selection on multi-homed). The send side gets the explicit fast paths the orb had
  and the recv-centric draft **omitted**: inline `MSG_DONTWAIT` (no blocking send
  syscall on the reactor), a `PendingSend` queue (backpressure without a stall), and
  **GSO-batched send** (the 2–4× QUIC lever). Acceptance: QUIC send throughput is
  measured with GSO on vs off and must show the batched-send win; a recv-only
  implementation that leaves the send path one-packet-per-syscall is a
  `send-path-left-on-the-floor` bug.
- **PF-3 — WireGuard per-packet crypto budget.** The mesh data plane's per-packet
  ChaCha20-Poly1305 must fit the per-packet cycle budget (rule above), achieved by
  **HACL\*/Vale verified-asm** (rule 5 — competitive with hand-tuned C, *with* a
  proof; never unverified crypto). The offload story is explicit: where the NIC/kernel
  offers inline crypto it is used; else the Vale kernel is the floor. Acceptance:
  WireGuard tunnel throughput at line-rate frame sizes with the verified crypto kernel
  on the hot path — a fast unverified ChaCha is the `unverified-fast-path` bug, a
  verified-but-unbatched one is `verified-but-slow-shipped`.
- **PF-4 — eBPF/AF_XDP CID steering is the *named* commodity-NIC mechanism for
  rule 1.** Rule 1 says "NIC does the demux (5-tuple **or QUIC-CID**)." On commodity
  hardware that is a wall: **stock NICs cannot RSS on a Connection-ID buried in the
  QUIC payload** — RSS hashes the 5-tuple, and a migrating QUIC connection keeps its
  CID across 5-tuples, so 5-tuple RSS mis-steers it. The named lever on the R4.4
  commodity path is **eBPF/AF_XDP CID steering**: an XDP program parses the CID and
  redirects to the owning core's `XSK`/RX queue in-kernel, before the userspace
  reactor. The **R6.2 asymptote** is **NIC-hardware CID steering** (Corundum / a P4
  pipeline that matches the CID field in silicon) — same property, zero CPU. This
  closes the rule-1 "or QUIC-CID" hole that commodity RSS can't honor on its own.
- **PF-5 — per-component throughput target for every external-crate replacement.**
  CR-2 says the verified artifact replaces the external crate; CR-5 says it may not
  regress perf. So **every** crate we displace carries a named throughput target the
  verified replacement must hit: the **concurrent cache** (lookups/s under contention
  vs the `moka`/`dashmap`-class baseline), the **token-bucket rate limiter**
  (decisions/s, no global-lock contention), the **h2 / HTTP-2 mux** (streams/s,
  frames/s, HOL-blocking-free). Acceptance: a replacement lands only with its
  component benchmark *and* the baseline it must beat-or-match; a verified replacement
  that silently halves throughput is caught here, not in prod. This is the explicit
  guard against the `verified-but-slow-shipped` bug at the crate granularity.
- **PF-6 — observability is zero-cost-when-disabled, proven by the gate predicate.**
  The tap / inspector / dns-tap / connection-debug hooks are all guarded by an
  `AtomicBool` gate. The acceptance criterion is not "the overhead is small" — it is
  **"the disabled path is provably free":** the gate predicate dominates every probe
  point, so when off the hot path executes the *same* instructions as a build with the
  observability compiled out (a relaxed-load + not-taken branch, nothing more). A tap
  that allocates, copies, or locks even when disabled is a
  `observability-taxes-the-hot-path` bug. (Verified-compiler note: the gate-dominance
  is checkable as a domain pass — the probe body is unreachable when the gate is
  false.)
- **PF-7 — no per-request `getaddrinfo` on the proxy hot path.** Name resolution is a
  **cold/warm-plane** activity, never a hot-path one. The proxy resolves upstreams via
  a resolver that lives off the datapath: results are pre-resolved / cached with TTL on
  the warm plane and handed to the reactor as ready addresses. A synchronous
  `getaddrinfo` (or any blocking resolve) on the request path is a hot-path syscall —
  it violates rule "no per-packet syscall" at the request granularity and stalls the
  run-to-completion core. This is the `blocking-resolve-on-the-reactor` bug, and it is
  a hard fail regardless of how fast the rest of the proxy is.

## How verification stays out of the runtime (CR-5, CR-4)

- Verification is **build-time**: verified code runs exactly as fast as its compiled
  output. There is no runtime proof overhead.
- The hot path is compiled by **our verified compiler** (CR-4) with **domain passes**
  — verified vectorization for the parse loops, verified zero-copy region fusion (the
  arena ops never materialize a copy), verified run-to-completion loop lowering,
  verified cache-line layout. Where an inner kernel's codegen is the binding
  constraint, the answer is **Vale verified-asm**, *never* unverified asm.
- The confinement/policy proofs live on the **cold control plane** — zero
  per-packet cost.

## Acceptance criteria (the measurement)

A dataplane rung is done only when it demonstrates, on its substrate:

- **Throughput** within the line-rate budget for the target NIC (R4.4 commodity
  Linux; R6.1 real multi-queue NIC), measured at the relevant packet/request sizes.
- **Zero steady-state heap allocation** on the hot path (instrument and assert).
- **Zero per-packet syscalls** on the kernel-bypass path.
- **Tail latency** bounded (no GC — there is none; no allocation spikes) — measure
  p50/p99/p999, not just mean.
- The perf was achieved **by verified means** — the generated/Vale code on the hot
  path is the *same artifact* as the proven one (CR-2). A perf win that required an
  unverified path is **not** a pass; it is a `verified-but-slow-shipped` /
  `unverified-fast-path` bug.
- **Component budgets met, not just the aggregate.** Each orchestrator dataplane piece
  (PF-1…PF-7) demonstrates *its own* number — proxy cache-hit/coalesce/splice (PF-1),
  GSO-batched QUIC send (PF-2), verified WireGuard crypto throughput (PF-3), CID
  steering at line rate on the R4.4 path (PF-4), and the beat-or-match benchmark for
  every displaced crate (PF-5). An end-to-end pass that hides a regressed component is
  not a pass.
- **Observability is provably free when off (PF-6).** The disabled tap/inspector/
  dns-tap path is the *same instruction stream* as an observability-compiled-out
  build (gate predicate dominates every probe), checked — not assumed.
- **No blocking resolve on the reactor (PF-7).** Assert there is no synchronous
  `getaddrinfo`/blocking resolve reachable from the request hot path; resolution is
  cold/warm-plane only.

## Notes

- The hardware-maximal patterns (multi-queue, RSS, zero-copy DMA, busy-poll) are
  architecture properties **independent of codegen** — they hold regardless of which
  backend the verified compiler targets, which is why the SW→FPGA→silicon retarget
  (R8.1) preserves them.
- Do not optimize before R4.2 has a working measured baseline; premature
  micro-optimization without the oracle-diff + the measurement violates
  `decision-spirit` #12/#18 (probe/premise first).

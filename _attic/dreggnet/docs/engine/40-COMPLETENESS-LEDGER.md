# 40 — COMPLETENESS LEDGER

**The completeness proof obligation, made into a work-list.** Every distinct
network *byte-path* and *cap-transition* in the dreggnet engine is a row here,
mapped to its DSL primitive, its formal rank, its roadmap rung, and a **status**.

Why this file is the keel of "a fully formal model of ALL network activity":

- **Completeness is a checked fact, not a hope.** The confinement theorem (CR-5,
  20-ARCHITECTURE) must range over *exactly* these rows. Every row is `modeled`
  or explicitly `out-of-scope` — a silently-missing row is CR-6 laundered vacuity.
- **It is the Wave-1 megaswarm work-list.** *One row = one DSL-model-unit = one
  HOL4 theory.* An agent claims a row, writes the model (using the proven arena
  theory `model/dreggnetArenaScript.sml` as the worked example), Holmake-verifies
  to green with zero cheats (D7), oracle-diffs, commits, marks the row `modeled`.
- **It is deployment-keyed.** Because the dreggnet cloud will *run* this, rows are
  real byte-paths/cap-transitions (ingress, proxy egress, mesh tunnel, cap handoff,
  cert issuance, observability tap) — "fully formal" and "actually deployed" track
  the same list.

**Provenance/cut:** first cut hand-built from the divergence-audit §1 surface +
the patched plans + the completeness scan. Granularity is feature-level; a granular
enumeration swarm (per sub-feature) is a planned refinement (it was rate-limited on
first attempt). Primitives: `region` (parser/byte-view), `machine` (sans-IO FSM),
`linear` (acquire→release-once resource), `shared` (concurrent object, Iris),
`crypto-axiom` (HACL*/Vale, retired by R5.4), `device-axiom` (NIC/kernel),
`composite` (a weld of the above). Status: **modeled** (a rank+rung covers it) ·
**GAP** (orb had it, plans don't yet name it) · **OOS** (deliberately out, with reason).

---

## A. HTTP ingress core

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| HTTP/1.1 request parse | wire → arena | region | Rank-1 / F-8 | R1.2/R1.3 | modeled |
| HTTP/2 frames + HPACK + flow-control | wire → arena + stream state | region+machine | Rank-2, R2.4 | R2.4 | modeled |
| HTTP/3 + QPACK over QUIC | wire → arena | region+machine | F-6, R2.4 | R2.5 | modeled |
| WebSocket codec + handshake (+over-h2/h3) | frame ↔ app | region+machine | R2.4 | R2.4 | modeled |
| chunked transfer + trailers | wire → body | region | Rank-1/R1.3 | R1.3 | modeled |
| response writer (CRLF-injection-free) | app → wire | machine | R2.4 | R2.4 | modeled |
| router / dispatch (first-match-determinism) | request → handler | machine | F-1 | R2.6 | modeled |
| 103 Early Hints | preliminary response | machine | F-1 | R2.6 | **GAP** (name it) |
| RFC 9218 Extensible Priorities | stream scheduling | machine | F-6/F-1 | R2.5 | **GAP** (verify) |
| SSE broadcaster fan-out | server→many | shared | F-1 | none-yet | **GAP** |
| Accept-Encoding q-value negotiation | header → codec | region | F-2 | R4.13 | modeled |
| per-phase timeout matrix + graceful drain | lifecycle | machine | Rank-2 | R2.1 | **GAP** (name positive-safety #G17) |

## B. Proxy & relay dataplanes

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| reverse-proxy director (LB select) | request → upstream | machine | F-3 | R4.5 | modeled |
| LB algos (RR/least-conn/ip-hash/consistent-hash/cookie) | select fn | machine | F-3 | R4.5 | modeled |
| upstream health checks | probe state | machine | F-3 | R4.5 | modeled |
| circuit breaker (Closed/Open/HalfOpen) | admission gate | machine | F-3 | R4.5 | modeled |
| upstream connection pool | reuse | linear/shared | F-3 | R4.5 | modeled |
| retry + idempotency gating | request replay | machine | F-3 | R4.5 | modeled |
| two-tier proxy cache (mem+disk, RFC 7234) | hit/miss/revalidate | machine | F-10 | R4.6 | modeled |
| request coalescing (single-flight) | dedup upstream | shared | F-10 | R4.6 | modeled |
| forward proxy plain + CONNECT blind tunnel | bidir splice | composite | F-4 | R4.7 | modeled |
| MITM TLS interception + proxy CA | decrypt+re-encrypt | composite+crypto-axiom | F-4 | R4.7 | modeled (soft-spot #4) |
| interception routing (URLPattern/glob) | match → action | machine | F-4 | R4.7 | modeled |
| upstream-proxy chaining (HTTP/SOCKS) | egress | machine | F-4 | R4.7 | **GAP** (verify) |
| MASQUE CONNECT-UDP (RFC 9298) | tunnel datagram | composite | F-4 | R4.7 | modeled (soft-spot #5) |
| MASQUE CONNECT-IP (RFC 9484) + Capsule (9297) | raw egress | composite | F-4 | R4.7 | modeled (soft-spot #5) |
| ConnectIpAcl egress allow-list | egress gate | machine | F-4 | R5.2 | modeled (soft-spot #5) |
| L4 TCP relay | opaque splice | linear | F-5 | R4.8 | modeled |
| L4 TLS-passthrough + ClientHello SNI extract | peek → route | region+machine | F-5 | R4.8 | modeled |
| L4 per-client UDP forward | datagram relay | machine | F-5 | R4.8 | **GAP** (verify) |
| SOCKS 4/4a/5 server | handshake FSM | region+machine | F-8 | R4.9 | modeled |
| CGI (RFC 3875, NPH) | request → process | composite | F-13 | R4.9 | modeled (cap-gated exec PD, ADR-N2) |
| FastCGI | request → socket | region+machine | F-8 | R4.9 | modeled |
| gRPC proxy + gRPC-Web transcode + health | h2 framing | machine | F-8/ADR-N1 | R4.x | modeled |

## C. Middleware suite (each a hot-path decision)

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| jwt_auth (alg-allowlist, anti-confusion) | token → decision | region+machine | F-2 | R4.13 | modeled |
| basic_auth (bcrypt) | cred → decision | machine | F-2 | R4.13 | modeled |
| auth_request subrequest | subreq → decision | machine | F-2 | R4.13 | modeled |
| acl engine | rule eval | machine | F-2 | R4.13 | modeled |
| rate_limit (governor token-bucket) | counter | shared | F-2 | R4.13 | modeled |
| ip_filter (CIDR deny-precedence) | addr → decision | machine | F-2 | R4.13 | modeled |
| tailscale_auth (whois, deny-before-allow) | identity → decision | machine | F-2 | R4.13 | modeled |
| security_headers / cors / headers / rewrite / request_id / redirect / error_page | header xform | machine | F-2 | R4.13 | modeled |
| connection_limit / slowloris / body_limit | resource gate | machine/shared | F-2/ADR-N5 | R4.13/R4.3 | modeled (positive-safety) |
| stick_table | shared counter | shared | F-2 | R4.13 | **GAP** (verify shared) |
| compress (brotli/zstd) | stream xform | crypto-axiom-adjacent | F-2 | R4.13/R10 | **GAP** (verified codec / ext-crate retirement) |
| html_rewriter (streaming) | body xform | machine | F-2 | R4.13 | **GAP** (verify) |
| access_log | event sink | machine | F-2 | R4.13 | modeled |

## D. Mesh (tailscale / wireguard)

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| Tailscale TS2021/Noise-IK control client | handshake + control | machine+crypto-axiom | F-7 | R-3 (control) | modeled |
| netmap poll + apply | control state | machine | F-7 | R-3 | modeled |
| MagicDNS / CentralResolver | name → addr | machine | F-7 | R-3 | modeled |
| mesh ACL / policy | decision | machine | F-7 | R-3 | modeled |
| WireGuard transform (Noise_IKpsk2 encap/decap) | packet crypto | machine+crypto-axiom | F-7 | R-3 (data) | modeled (HACL*/Vale) |
| smoltcp netstack inject/re-encap | packet ↔ stream | machine | F-7 | R-3 | modeled |
| DISCO NaCl-box NAT traversal (STUN/ICE) | discovery | machine+crypto-axiom | F-7 | R-3 | modeled |
| DERP NaCl-box relay | relay framing | region+machine | F-7 | R-3 | modeled |
| DNS forwarder (close orb ROBOTODO) | query relay | machine | F-7 | R-3 | modeled |

## E. TLS & PKI (the long tail)

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| TLS record-layer FSM + handshake | encrypted ↔ plaintext | machine | F-12 | R5.4 | modeled (axiom→R5.4, ADR-N4) |
| ALPN / SNI selection | hello → config | region+machine | F-12 | R5.4 | modeled |
| crypto primitives (AEAD/KDF/sig) | crypto | crypto-axiom | (axiom) | R5.4 (retire) | modeled-as-axiom |
| ACME DNS-01 / HTTP-01 | challenge FSM | machine | NEW: ACME | R-3/cold | **GAP** |
| on-demand TLS (ask-authz) | handshake-time issue | machine | NEW: on-demand | R4.3 | **GAP** (soft-spot #1 chain) |
| **OCSP stapling** | revocation status | region+machine | NEW: OCSP | NEW | **GAP** ⚠ |
| **mTLS / client-cert auth** | cert → identity | region+machine | NEW: mTLS | NEW | **GAP** ⚠ |
| **Certificate Transparency log (RFC 6962)** | Merkle tree/SCT/STH/proofs | composite | NEW: CT (reuse dregg Merkle/receipt!) | NEW | **GAP** ⚠ |
| ECH (encrypted client hello) | hello crypto | machine+crypto-axiom | NEW: ECH | NEW | **GAP** |
| 0-RTT / early-data anti-replay | replay window | shared | F-9 | R2.5/R5.2 | modeled (soft-spot #6) |
| session resumption (single-use ticket) | ticket state | shared | F-9 | R5.2 | modeled |
| PROXY protocol v1/v2 | prepend parse | region | F-8 | R4.9/R4.14 | modeled (spoof-defense) |
| private CA + MITM CA | key custody | linear | F-4 | R4.7 | modeled (soft-spot #4) |
| trust-store injection | OS/Firefox/JVM | composite | F-4 | R4.7 | **GAP** (bounded+declared proof) |
| kTLS handoff / NIC-inline TLS | kernel/NIC crypto | device-axiom | R3.3 | R3.3/R6 | modeled-as-axiom |

## F. Transport datapath

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| QUIC engine (handshake/loss/CC/stream/multipath/NAT/0-RTT) | conn state | machine | F-6 | R2.5 | modeled |
| QUIC parsers (initial/frame/varint/transport-params/ack) | wire | region | F-6/F-8 | R2.5 | modeled |
| io_uring CQ loop + multishot recv + provided buffers | syscall batch | composite | R3.3 | R3.3 | modeled |
| BufRing zero-copy DMA + lease | kernel buffer | shared+device-axiom | Rank-7 | R3.3 | modeled |
| size-classed/LIFO pools | reuse | linear | Rank-4 | R2.3 | modeled |
| SPSC ring + one-shot CrossFuture | inter-thread | shared | Rank-5/6 | R3.1/R3.2 | modeled |
| eBPF/AF_XDP CID-steering (steer.c → XSKMAP) | NIC demux | device-axiom | NEW: verified-P4-later | R4.4/R6.2 | modeled (PF-4) |
| AF_XDP UMEM / per-queue | zero-copy frames | device-axiom | R3.3 | R4.4 | modeled |
| GSO/GRO/ECN/pktinfo offload | UDP segmentation | device-axiom | R3.3 | PF-2 | modeled |
| UDP send-side fast paths | egress batch | machine | R3.3 | PF-2 | modeled |
| WebRTC (PeerConnection/datachannel/ICE/DTLS/SCTP) | conn+crypto | machine+crypto-axiom | NEW: WebRTC | NEW (after mesh, ADR-N1) | **GAP** (sequenced later) |
| generational socket handles (no ambient fd auth) | handle discipline | linear | F-13-adjacent | R3.3 | **GAP** (state the invariant) |

## G. Orchestrator cold plane + cap-transitions

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| config standup (render→lower→realize) | spec → fabric | composite | (confinement) | R4.3 | modeled |
| address/label→port key-inference | spec rule | machine | (confinement #2) | R4.3 | modeled (soft-spot #2) |
| admin API runtime mutations | δ transition | machine | (confinement-TS) | R5.2 | modeled (soft-spot #3) |
| SIGHUP reload (atomicity) | δ transition | machine | (confinement-TS) | R5.2 | modeled |
| zero-downtime upgrade → cap-handoff | cap migration | composite | NEW: upgrade-protocol | R4.11/R7 | modeled (ADR-N3; firmament substrate; **Microkit gap to chart**) |
| cert issuance lifecycle | cap → cert | machine | (TLS/PKI) | R-3 | **GAP** (with ACME) |
| expose/share | proxy + exposure | composite | F-3/F-4 | R4.x | modeled |
| cert command (PKI lifecycle) | issue/trust/inspect | composite | (TLS/PKI) | R-3 | **GAP** (with ACME/OCSP) |
| dev (live-reload) | watch → reload | machine | (control) | R4.x | modeled |
| runtime SocketPolicy (ArcSwap) | defense-in-depth | machine | ADR-N5 | R5.2 | modeled |
| expose --persist daemon | long-lived reconcile | machine | ADR-N1 | R4.x | modeled |

## H. Observability & client managers (the other long tail)

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| **Prometheus metrics (lock-free)** | counter export | shared | NEW: metrics | NEW | **GAP** ⚠ |
| **deep packet tap** | gated copy | machine | NEW: tap (gate predicate) | PF-6 | **GAP** ⚠ (info-leak if gate unproven) |
| network inspector (CDP) | event sink | machine | NEW: inspector (re-home off JVM) | NEW | **GAP** (D12 re-home) |
| DNS tap | gated copy | machine | NEW: tap | PF-6 | **GAP** |
| W3C trace-context | header propagate | region | NEW: trace | NEW | **GAP** |
| HAR export/recording | ring buffer | shared | NEW: recording | NEW | **GAP** (verify scope) |
| CQ DNS resolver (literal→hosts→TTL→MagicDNS→UDP→getaddrinfo) | name → addr | machine | F-11 | R4.15 | modeled (PF-7: no getaddrinfo on hot path) |
| Happy-Eyeballs v2 | dual-stack connect | machine | F-11 | R4.15 | modeled |
| download/session manager (priority/retry/Range-resume/CB) | client state | machine | NEW: client-mgr | NEW | **GAP** (verify in-scope) |
| cookie jar (RFC 6265bis Secure/HttpOnly/SameSite) | jar state | machine | F-11 | R4.15 | modeled |

## I. CapTP & dregg integration

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| Netlayer (dial/accept/ocapn://) | conn → CapSession | machine | (ADR-5) | R4.1 | modeled |
| postcard WireMessage framing | wire ↔ message | region | F-8 | R4.1 | modeled |
| CapSession epoch/import-export/GC/pipelining | ocap state | machine+linear | (ADR-5) | R4.1 | modeled |
| turn_in / Ed25519 SignedTurn gate | ingress auth | machine+crypto-axiom | (ADR-4) | R4.1 | modeled |
| lease-safety (HostingLease: never serve beyond cap/budget) | admission | machine | (confinement) | R5.3 | modeled |
| receipts (prev-hash-chained, re-witnessable) | attestation | composite | ADR-9 | R8(receipts) | modeled |
| cap-fabric at distance n (mint↔cell↔CapTP) | cap delegation | composite | Firmament (l4v-proven) | (existing) | modeled |
| per-tenant / per-exposure isolation | cap partition | composite | NEW: isolation | NEW | **GAP** (forgotten-feature §5.12) |

---

## J. Transport substrate & cross-layer properties (ADR-N6 / N7 / N8)

| item | flow | primitive | rank | rung | status |
|---|---|---|---|---|---|
| QUIC/H3 — the verified transport | datagram → stream | machine+region | F-6 | R2.5 | modeled |
| CapTP-over-QUIC | ocap ↔ QUIC stream | machine | ADR-N6 | R4.1 | modeled (the verified path) |
| TCP/IP (HTTP/1/2 + CapTP-over-TCP legacy) | wire ↔ stream | — | — | — | **axiom** (ADR-N6: named CR-2 axiom, no successor rung; NOT a verified rank) |
| time / deadlines (every timer) | tick → deadline | machine | NEW: time-as-input | — | modeled (sans-IO time-input; kernel-tick axiom) |
| DSL composition theorem | primitive ⊕ primitive | meta | NEW: composition | — | **GAP** (load-bearing — makes the DSL a calculus) |

**Cross-layer property theorems — what makes it "ALL network activity":**

| property | proves | status |
|---|---|---|
| confinement (inbound) | nothing runs/listens/exposes/authorizes undeclared | modeled (R5.2) |
| no-undeclared-egress | connects out only where declared (anti-SSRF/exfil; the dual) | **theorem, IN now** |
| total-accounting | every byte/conn/CPU-tick metered+conserved+receipted (= dregg conservation, ADR-N8) | **theorem, IN now (rides dregg)** |
| non-interference | no flow across tenant/exposure cap-domains except declared channels | **in-scope, design-for** — NI-by-construction via X-5; security-preserving refinement where needed; grounded in the l4v-proven seL4 cap-partition |
| end-to-end secrecy | ciphertext→declared-plaintext→declared-handler, no cross-layer leak | **deferred-named** (the one hard IFC theorem) |

**Standing obligation X-5 (cap-domain-parametric):** every model is scoped to a
cap-domain; no ambient cross-domain flow; cross-domain interaction only via declared
channels. Adopted from rung one so NI stays achievable. Joins X-1..X-4 (21-FORMAL).

**Unifications (ADR-N8):** accounting=conservation · observability=receipts ·
cap-fabric-spine · session+one-migration-theorem · time-as-input+composition. These
are *framings* (reuse of dregg substrate), not new builds — they collapse several
gap-rows above (the observability group, the limits, the migration mechanisms) into
the dregg core.

## Status rollup (first cut, feature-level)

- **modeled:** ~70 rows (the bulk — HTTP core, proxy, middleware, mesh, transport, CapTP, the confinement transitions).
- **GAP:** ~28 rows — the long tail. The headline tail (⚠): **OCSP stapling, mTLS/client-auth, CT-log (Merkle/SCT), Prometheus metrics, packet-tap/DNS-tap, inspector(CDP)**. Plus: ACME state machine, on-demand-TLS, ECH, trust-store-injection proof, WebRTC (sequenced later), per-tenant isolation, W3C-trace, HAR, download-manager, 103-early-hints, SSE, stick_table-as-shared, compress/html_rewriter verification, generational-handle invariant, several "verify" rows.
- **OOS:** 0 explicit yet (the deleted Elide-product surface — licensing/telemetry/TUF — is OOS by Charter, recorded in 10-DECISIONS, not as ledger rows).

## Consolidated GAP LIST → task #2 (close the long-tail plan gaps)

Grouped by where to add. Each becomes a rank (21-FORMAL) + rung (30-ROADMAP), or an explicit OOS ADR.

1. **TLS/PKI tail (highest — assurance-critical):** OCSP stapling · mTLS/client-auth · CT-log (RFC 6962 Merkle/SCT/STH/proofs — *reuse dregg's existing Merkle/receipt machinery*) · ACME (DNS-01/HTTP-01) state machine · on-demand-TLS ask-authz · ECH · trust-store-injection-bounded-proof. → new F-ranks (e.g. F-14 ACME, F-15 OCSP, F-16 mTLS, F-17 CT-log) + a PKI phase in Roadmap; the cert lifecycle (orchestrator G) and the `cert` command depend on these.
2. **Observability:** Prometheus metrics · packet-tap · DNS-tap · CDP inspector (re-home off JVM, D12) · W3C-trace · HAR. → new F-rank "observability: gated sinks + the proven zero-cost-when-disabled gate predicate" + PF-6 already names the gate; add the rung. (A1/A10: an unproven tap-gate is an info-leak.)
3. **Protocol extras:** 103 Early Hints · RFC 9218 priorities · SSE fan-out (shared). → fold into F-1/F-6 with named theorems + a rung.
4. **Client managers:** download/session manager · (Happy-Eyeballs/cookie/resolver already in F-11). → ADR (in/out) + F-rank if in.
5. **Misc to name/verify:** per-tenant/per-exposure isolation (forgotten §5.12) · generational-handle "no ambient fd authority" invariant · stick_table as `shared` · compress/html_rewriter verified-codec (ext-crate retirement track R10) · L4 UDP-forward / upstream-proxy-chaining (verify).
6. **WebRTC:** GAP-by-design (IN, sequenced after mesh ranks, ADR-N1) — give it its rank + a post-mesh rung.

When task #2 lands these into the plans (each GAP → modeled), this ledger's GAP count → 0 (modulo explicit OOS), and the confinement theorem's scope = the full row set. *That* is the completeness proof.

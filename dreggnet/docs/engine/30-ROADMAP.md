# 30 — ROADMAP (the rung ladder)

The sequenced work. Phases are roughly ordered by dependency + leverage
(`decision-spirit` #19: do what unblocks the most, secure a verified base before
stacking, irreversible/outward steps last). Within a phase, rungs may run parallel.
Tracks interleave: **F**ormal-model · **C**ompiler · **E**ngine/integration ·
**V**erification · **K**ernel-reformalization (parallel/optional, ADR-O4).

Each rung states: **goal · deliverable · done-criteria · deps.** A rung is done
only per the Charter per-artifact definition (obligations discharged or handed
back; oracle-diffed; perf-by-verified-means; walls named). No laundered vacuity
(CR-6).

**The sequencing wall (be un-surprised):** verified-compiler-first means **no
shippable fast dataplane exists until ~Phase 4.** Phases 0–3 produce proofs,
primitives, and a pure/generated engine — not a thing you can put traffic
through at line rate. This is the deliberate cost of securing a verified base
before stacking (`decision-spirit` #19); it is named here so it is a known wall,
not a Phase-4 surprise. The lever: every Phase 0–3 rung is a *banked* proof the
Phase-4 dataplane inherits for free.

---

## Phase 0 — Foundations (no engine code yet; ADR says don't be hasty)

- **R0.1 — Fresh repo + provenance firewall.** *Goal:* the clean-room home.
  *Deliverable:* a fresh `dreggnet` repo, AGPL-3.0 LICENSE at commit #1, clean
  history, `docs/` (migrate this plan set), CI skeleton. *Done:* repo exists,
  builds an empty workspace, AGPL headers templated; zero file copied from
  the internal Elide source tree. *Deps:* ADR-O1 (location).
- **R0.2 — Prover/compiler toolchain.** *Goal:* the stack is reproducibly
  installed + CI-checked. *Deliverable:* pinned HOL4 + CakeML + Pancake + Isabelle
  (+AFP for `uc-crypthol`) + OpenTheory, a hello-world that compiles a trivial
  CakeML program to machine code and a trivial Pancake program, both proof-checked
  in CI. *Done:* CI is green on a verified hello-world end-to-end; toolchain versions
  pinned. *Deps:* R0.1.
- **R0.3 — Oracle reference + diff harness.** *Goal:* the oracle is captured and
  mechanically diffable. *Deliverable:* `docs/engine/50-ORACLE.md` (compile the
  session charts: representations, protocol/codec/transport/pki, orb tier, dregg
  seL4/deos/CapTP, license manifest); a harness that can run an Elide engine
  build (or a recorded vector set) and capture canonical outputs to diff generated
  artifacts against. *Done:* the harness produces a stable oracle vector set for at
  least the H1 request path. *Deps:* R0.1.
- **R0.4 — DSL primitive design spike.** *Goal:* nail the `region`/`view` surface
  before building its pass. *Deliverable:* a short design note: the `region`/`view`
  surface syntax, the HOL4 semantics it denotes, the proof schema it auto-discharges
  (the in-bounds class), and how it lowers to CakeML/Pancake IR. *Done:* a worked
  paper example (the arena) typechecks on paper against the semantics; reviewed
  cross-family. *Deps:* R0.2; reads `21-FORMAL-MODEL.md` Rank 1.

## Phase 1 — The first verified pass + the first model (the seed crystal)

- **R1.1 — The `region`/`view` verified compiler pass.** *Goal:* the proof-producing
  loop, proven end-to-end on one primitive. *Deliverable:* the `region`/`view`
  primitive's HOL4 semantics; the lowering `region-op → CakeML/Pancake IR`; and the
  **preservation theorem** (the emitted code refines the primitive's semantics),
  inheriting the verified backend to machine code. *Done:* the theorem is proven (no
  `sorry`); a generated `region` op runs and its output matches the semantics on the
  vector set. *Deps:* R0.2, R0.4. **← THE FIRST STONE.**
- **R1.2 — The arena model (Rank 1) as the first generated instance.** *Goal:* the
  flagship pure model, generated + oracle-checked. *Deliverable:* `ParsedRequest`
  arena + `wf_parsed_request` expressed via the `region`/`view` primitive; generated
  code; the in-bounds obligations auto-discharged. *Done:* generated arena agrees
  with the Elide `ParsedRequest` on the R0.3 H1 vectors; the UTF-8 hypothesis is
  *explicit* (slated for R1.3). *Deps:* R1.1.
- **R1.3 — First EverParse parser + the UTF-8 discharge (X-2).** *Goal:* close the
  arena's open hypothesis with a verified parser. *Deliverable:* an EverParse (or
  HOL-native) verified parser for the H1 request line + headers (and the postcard
  `WireMessage` framing) emitting the arena; its correctness proof discharges the
  arena's UTF-8 + in-bounds hypotheses. *Done:* arena+parser compose; the request
  model has *no* open hypothesis except the named axioms; CVE-class smuggling
  defenses (CL+TE, dup-CL, chunked-not-last, null-byte) are theorems. *Deps:* R1.2.

## Phase 2 — The pure pillars (Ranks 2–4) — bulk of the engine, generated

- **R2.1 — `machine` primitive + the connection FSM (Rank 2).** Generate the
  `ProtocolState` `step` from the `machine` primitive; prove totality + that
  impossible payload accesses are unreachable; codecs as effect interfaces.
  *Done:* the FSM agrees with the oracle on the connection-lifecycle vectors;
  totality proven. *Deps:* R1.1, R1.2.
- **R2.2 — The slab + epochs (Rank 3).** The `fd ⇀ ConnectionState` data refinement
  + the monotone-epoch stale-event guard; X-3 wraparound axiom explicit. *Done:*
  the bijection invariant proven; stale-event rejection proven. *Deps:* R2.1.
- **R2.3 — The pools (Rank 4) + `linear` primitive.** The size-classed/LIFO pools;
  the `linear` primitive with the X-4 exactly-once-return token. *Done:* pool
  invariants proven; the linear discipline reused (not reinvented). *Deps:* R1.1.
- **R2.4 — The codecs (HPACK/QPACK/WS) + the response writer.** Generate the arena
  decode results + the sans-IO writer FSM (CRLF-injection-free by theorem; chunked
  framing correct). *Done:* codec outputs oracle-match; writer output has no
  attacker-CRLF (theorem). *Deps:* R1.3, R2.1.
- **R2.5 — QUIC + HTTP/3 transport model (F-6).** *Goal:* close the gap that H3 is
  a done-criterion (Charter #2) yet had no rung. *Deliverable:* the QUIC connection
  FSM as a `machine` instance (packet-number spaces, stream state, flow control),
  the QPACK coupling to R2.4, and the H3 frame layer over it; the **0-RTT /
  early-data path is modeled here** carrying the soft-spot #6 anti-replay
  obligation (StrikeRegister + single-use ticket) forward to its theorem in R5.2.
  *Done:* the QUIC/H3 FSM agrees with the oracle on the H3 request-path vectors;
  totality + impossible-payload-access proven (as R2.1); the 0-RTT replay-safety
  property is *stated* against this model. *Deps:* R2.1, R2.4; the dataplane wiring
  lands in R4.2. **← H3 starts pure, like everything else.**
- **R2.6 — Router / dispatch relation (F-1).** *Goal:* close the "no routing model"
  gap on the request hot path, pure like the rest of Phase 2 (mirrors R2.1's
  pure-FSM shape). *Deliverable:* the ordered `[RouteMatch → Handler]` table and the
  dispatch relation `dispatch : Request → Route list → Handler option` as a pure fold,
  with each `RouteMatch` an AND-conjunction over path/host/method/header/query
  predicates. *Done:* the **first-match-determinism theorem** — `dispatch` is total,
  deterministic, and returns the *least-index* matching route (well-defined tie-break,
  no ambiguity); the §2 address/label→port key-inference composes here (inferred
  listener keys feed the route table). *Deps:* R1.2, R1.3.

## Phase 3 — The concurrent core (Ranks 5–7) — the only Iris work

- **R3.1 — SPSC `Ring` (Rank 5).** Iris linearizability proof. *Done:* no `sorry`;
  loom/Kani as the continuous net beneath the proof. *Deps:* R0.2.
- **R3.2 — One-shot `CrossFuture` (Rank 6).** Iris-light one-shot proof. *Deps:* R0.2.
- **R3.3 — `BufRing` + lease (Rank 7).** The bounded-matrix model; the NIC/kernel
  **device axiom** stated explicitly (the one trusted boundary, CR-2); the lease as
  a sep-logic token (recycle-once). *Done:* the zero-copy recv path is sound modulo
  the named device axiom; `BufRingLease` wired through to the parser (closes the
  Elide eager-copy gap). *Deps:* R3.1 (shared discipline), R2.3 (linear token).
- **R3.4 — Fix `PooledBuf` by construction (Rank 8).** Replace `*mut BufferPool`
  with a validity-carrying handle; the dangling-drop becomes impossible. *Done:* the
  Elide `ROBOTODO` bug-class cannot be expressed in the model. *Deps:* R2.3.

## Phase 4 — Integration over Linux (ADR-O3 default substrate)

- **R4.1 — The CapTP `Netlayer` (ADR-5) over Linux.** Implement the `Netlayer`
  carrying postcard `WireMessage`, preserving `CapSession` semantics, over Linux
  TCP/AF_XDP. *Done:* dregg talks through the new netlayer; diff vs the silo-TCP
  netlayer; **this is the first proof the engine slots into dregg.** *Deps:* R1.3
  (framing parser), R2.1.
- **R4.2 — The zero-copy dataplane over io_uring/AF_XDP.** Wire Ranks 3 + the
  generated FSM into a running Linux dataplane; multishot recv, the lease path;
  wire the R2.5 QUIC/H3 FSM (incl. the UDP/GSO path) and the R4.5 reverse-proxy
  baseline through the same lease discipline. *Done:* serves **H1/H2/H3 + the
  reverse-proxy dataplane** at measured throughput on commodity Linux (the first
  realization of Charter done-criterion #2's data-plane list). *Deps:* R3.3, R2.4,
  R2.5, R4.5.
- **R4.3 — The certifying orchestrator (the cold plane, CR-5).** The gate-free orb
  driver: declarative-spec → standup of listeners/routes/TLS/mesh/proxy; deleting the
  license gate. Express config→standup as a certifying interpreter **over the FULL
  config types, not a subset** — the interpreter must total over every
  `ExposeMethod`, route, proxy, mesh, and bound the orb's surface admits, or refuse.
  *Done:* (a) a **config-surface parity checklist** is green: every key in the PKL
  oracle (`50-ORACLE.md`) maps to a modeled config type or an explicit
  handed-back/refused note — no silently-dropped key (CR-6); (b) the
  **timeout/limit/resource-bound config** (`maxConnections`, `BodyLimit`,
  `ConnectionLimit`, `RateLimit`, per-phase timeouts) is folded *into* the
  confinement config types as first-class positive-safety bounds, not a side table;
  (c) the orb stands up a multi-listener node from a spec; **the confinement theorem
  statement** is written against the real (full) config types (proof in Phase 5/V).
  *Deps:* R4.1, R4.2, R4.5.

### Phase 4 — proxy track (the dataplanes the orb actually shipped; default = IN)

Each proxy rung carries the same confinement skeleton: **deny-before-allow ACL**
(default-deny, an allow is an explicit declared cap), **no-SSRF** (every upstream
target is a declared destination, never an attacker-chosen address), and
**MITM-CA-scope** where a trust anchor is involved (soft-spot #4). All feed
`turn_in`/cap-gate; none may silently downgrade TLS (soft-spot #1).

- **R4.5 — Reverse-proxy director (F-3).** *Goal:* the orb's headline dataplane,
  generated. *Deliverable:* the director FSM (route → upstream selection →
  health-driven state → retry/buffering), the sans-IO core reusing R2.* codecs,
  load-balance + health-check as `machine` instances. *Done:* upstream selection is
  a declared-destination function (no-SSRF theorem: no request egresses to a
  non-declared upstream); director output oracle-matches the orb on the
  reverse-proxy vectors. *Deps:* R2.4, R4.1.
- **R4.6 — Proxy cache (F-10).** *Goal:* the HTTP cache as a verified store, not
  `http_cache_semantics` trust. *Deliverable:* a generated cache-key + freshness +
  revalidation model (the RFC 9111 subset the orb honored), keyed under the lease
  discipline. *Done:* cache decisions oracle-match; **no cache-key confusion**
  (distinct requests never alias) is a theorem; staleness obeys declared bounds.
  *Deps:* R4.5, R2.4.
- **R4.7 — Forward-proxy + MITM (F-4).** *Goal:* the interception path with its
  trust anchor *bounded by proof*. *Deliverable:* the forward-proxy FSM + the MITM
  cert-gen path; the CA modeled as a **host-glob-scoped trust anchor** whose
  **private key never leaves its PD** and whose trust-store injection is
  bounded+declared (soft-spot #4). *Done:* generated certs are scoped to the
  declared host-glob (theorem: no cert minted outside scope); the CA-key-confinement
  obligation is *stated here* and *discharged* in R5.2. *Deps:* R4.5; the runtime
  cert-gen dynamism is MODELED SEPARATELY (soft-spot #3).
- **R4.8 — L4 / SNI proxy (F-5).** *Goal:* the transport-layer proxy + SNI routing.
  *Deliverable:* the L4 splice FSM and SNI-peek router (route on declared SNI map,
  no TLS termination on the passthrough path). *Done:* routing is a total function
  of declared SNI rules → declared upstreams (no-SSRF); splice preserves the
  byte-stream (refinement). *Deps:* R4.5.
- **R4.9 — SOCKS + CGI/FastCGI + StaticFiles (F-8, F-13).** *Goal:* the egress +
  process-exec + static-serving surfaces, each as an explicit capability/confinement
  obligation. *Deliverable:* the SOCKS5 FSM (CONNECT/BIND/UDP-ASSOCIATE) gated by a
  **declared-destination ACL** (this is the same `ConnectIpAcl` shape as soft-spot #5
  for CONNECT-IP/UDP/MASQUE egress); the CGI/FastCGI path as an **explicit
  process-exec capability** (soft-spot #7) carried to its ADR (ADR-N2); and the
  **StaticFiles path-confinement theorem (F-13): no served path escapes root**
  (canonicalize-then-prefix-check; no `..` / symlink / percent-encoding escape).
  *Done:* SOCKS egress cannot reach a non-declared destination (theorem); the CGI
  exec-cap is named, not implicit; **no StaticFiles request resolves to a path outside
  the declared root (theorem)**; parser coverage tracked in R4.14. *Deps:* R4.5.
  **See ADR-N2 (CGI vs the minimal-cap net PD) — FLAG-FOR-EMBER.**
- **R4.10 — gRPC translation.** *Goal:* the gRPC ↔ HTTP/2 transcoding the orb did.
  *Deliverable:* the generated gRPC framing + trailers + status mapping over R2.4's
  H2 codec; the transcode as a refinement of the gRPC wire spec. *Done:* transcode
  output oracle-matches; trailer/status mapping is total. *Deps:* R2.4, R4.5.

### Phase 4 — integration + invariants (cont.)

- **R4.4 — Hardware-maximal on Linux (ADR-8).** Multi-queue, RSS/Flow-Director CID
  steering, busy-poll; prove the line-rate ceiling on commodity hardware. *Done:*
  meets `22-PERFORMANCE.md` budget on Linux. *Deps:* R4.2.
- **R4.11 — Verified upgrade / migration protocol (ADR-N3).** *Goal:* the orb's
  zero-downtime reload/handoff, but as a proven listener-set migration. *Deliverable:*
  the migration FSM where the new generation inherits exactly the declared listeners
  of the old; the property **migrated-set == pre-upgrade-set** (no listener silently
  dropped or added) and **binds exactly the inherited declared listeners**; reload
  atomicity (no double-bound-listener window, no degraded-TLS window — this is the
  transition-system face of R5.2). *Done:* the migration theorem statement is written
  against the config types; the Linux (fd-passing) realization runs. **ADR-N3
  reconciles this with the seL4 *static* PD model** (a seL4 PD does not fork/exec a
  successor): on seL4 the "upgrade" is a supervised PD-replacement with capability
  hand-back, NOT process self-replacement — most-Charter-aligned option chosen,
  **FLAG-FOR-EMBER** (zero-downtime-upgrade semantics on a static PD). *Deps:* R4.3;
  proof composes in R5.2.
- **R4.12 — Config-application receipts (ADR-9).** *Goal:* make "what the node
  actually realized" auditable, *after* the plain spec works (ordering per ADR-O5 —
  receipts are an increment on a working certifying interpreter, not a prerequisite).
  *Deliverable:* the certifying interpreter (R4.3) emits a signed **receipt** = the
  realized config + the discharged-obligation set + named hand-backs, diffable
  against `declared(C)`. *Done:* a receipt is produced per apply/SIGHUP; a tampered
  receipt fails the diff; receipts chain across R4.11 migrations. *Deps:* R4.3
  (ADR-O5 sequencing: spec-first), R4.11.
- **R4.13 — Middleware correctness + auth-bypass-impossibility (F-2).** *Goal:* the
  request-middleware chain (auth, rewrite, header-mut, rate-limit hooks) proven, not
  trusted. *Deliverable:* each middleware as a request→request transform with a
  stated invariant; the chain's composition theorem; the headline property
  **auth-bypass-impossibility** — no ordering/short-circuit/error path lets a request
  reach a protected upstream without the declared authz decision having run and
  passed. *Done:* the bypass-impossibility theorem holds across the full middleware
  lattice (incl. error and early-return edges); the auth/TLS-issuance runtime
  dynamism subset is MODELED SEPARATELY (soft-spot #3), not assumed static. *Deps:*
  R4.5.
- **R4.14 — Parser coverage + carry-forward fuzz corpus (F-8).** *Goal:* the
  *continuous net* under every parser (H1/H2/H3 framing, HPACK/QPACK, SOCKS, CGI/
  FastCGI, config). *Deliverable:* a coverage ledger mapping each shipped parser to
  its verified-or-fuzzed status; a carry-forward fuzz corpus (seeded from the oracle
  vectors + CVE-class smuggling cases) wired into CI as the standing net beneath the
  proofs — the parser analogue of R3.1's loom/Kani. *Done:* every parser is either a
  theorem (R1.3/R2.4/R2.5) or under continuous fuzz with the corpus carried forward
  release-to-release; no parser ships dark. *Deps:* R1.3, R2.4, R2.5, R4.9.
- **R4.15 — Client-state model: cookie-jar + resolver (F-11).** *Goal:* close the
  client-state gap (cookies + name resolution), the last unrung F-rank on the
  request/proxy path. *Deliverable:* the cookie predicates as **theorems** (a `Secure`
  cookie is never emitted over plaintext; a `SameSite=Strict` cookie is never attached
  cross-site; `HttpOnly` is honored), and the resolver **cache + Happy-Eyeballs**
  racing as a `machine` (the RFC-8305 dual-stack connect FSM with its timer). *Done:*
  the cookie predicates hold as theorems; the resolver FSM agrees with the oracle on
  the dual-stack-race vectors; resolution stays on the cold/warm plane (composes PF-7
  — no blocking resolve on the reactor). *Deps:* R2.4, R4.5.

## Phase 4.5 — The mesh data plane (the WireGuard/Tailnet surface; default = IN)

The orb carried a full mesh. It splits clean into a **cold control plane** (slow,
declarative, certifying-interpreter-shaped like R4.3) and a **hot data plane**
(the packet transform, line-rate, lease-disciplined like R4.2). The runtime
dynamism here (netmap updates, live tunnels, DERP relays) is MODELED SEPARATELY
(soft-spot #3), not excluded.

- **R4.5m — Control plane: Noise-IK client + netmap + MagicDNS + ACL.** *Goal:* the
  tailnet control surface as declarative config feeding the certifying interpreter.
  *Deliverable:* the Noise-IK handshake client FSM, the netmap (peer set + allowed-IPs)
  as a config type, MagicDNS name→peer resolution, and the tailnet **ACL as a
  deny-before-allow declared cap** (same skeleton as the proxy track). *Done:* the
  netmap realizes exactly the declared peer/route set (a confinement clause: no peer
  reachable that the ACL did not declare); MagicDNS resolution is total over the
  declared name set. *Deps:* R4.3 (shares the certifying-interpreter shape), R4.1.
- **R4.6m — Verified WireGuard crypto.** *Goal:* the WG cryptographic core proven,
  not borrowed. *Deliverable:* generated/verified Noise-protocol + ChaCha20-Poly1305
  + Curve25519 for the WG transform (the `uc-crypthol`/AFP path), with the
  key-confinement obligation (private keys never leave their PD — kin to soft-spot #4).
  *Done:* the WG handshake + transform refine the spec; no `sorry`; keys PD-confined.
  *Deps:* R0.2.
- **R4.7m — Hot data plane: WG transform + DERP + DISCO.** *Goal:* the packet path at
  line rate. *Deliverable:* the WG encrypt/decrypt transform on the R4.2 zero-copy
  lease path; DERP relay fallback (declared-relay-gated); DISCO endpoint discovery /
  path-up FSM. *Done:* the transform serves at measured throughput on the R4.2
  dataplane; relay/endpoint selection is a function of declared state (no
  attacker-chosen relay); the **mesh data plane** joins Charter done-criterion #2's
  list. *Deps:* R4.2, R4.5m, R4.6m.
- **R4.8m — DNS forwarder with proven teardown (closes the orb ROBOTODO).** *Goal:*
  the mesh DNS forwarder, fixing the orb's leak-on-teardown `ROBOTODO` by
  construction. *Deliverable:* the forwarder as a lease-disciplined resource whose
  in-flight queries + upstream sockets are released exactly once on teardown (the
  Rank-7/Rank-8 discipline reused). *Done:* **proven teardown** — no forwarder
  resource outlives its declared lease (the orb's `ROBOTODO` bug-class cannot be
  expressed); resolution obeys the declared upstream/ACL set. *Deps:* R4.5m, R3.4
  (the validity-carrying-handle discipline).

## Phase 5 — The seL4 net PD (port the substrate; ADR-4)

- **R5.1 — Port to the Microkit net + net_client PDs.** Replace virtio-single-queue
  with a raw-NIC sDDF/Pancake driver; the sans-IO core drops on unchanged. *Done:*
  the engine boots as the `net`/`net_client` seats, feeds `turn_in`, over
  `sel4-shared-ring-buffer`. *Deps:* R4.2, R4.3; reads the dregg `sel4/` oracle.
- **R5.2 — The confinement theorem (CR-5, the crown).** Prove confinement **as a
  transition-system invariant, not a single static `C`:** for every admin mutation /
  SIGHUP reload δ, `realize(apply(δ,C)) ≡ declared(apply(δ,C))`, with **reload
  atomicity** (no double-bound-listener window, no degraded-TLS window — composes
  R4.11). The theorem ranges over **all 7 confinement soft-spots** as explicit
  clauses:
  - **#1 — TLS-mode fallback = enforce-or-refuse across the *whole* fallback chain.**
    Not just "no silent downgrade" on auto-https+missing-email: the property is stated
    over the entire `ExposeMethod` chain (auto→Funnel→ACME→self-signed→plain) — every
    step either meets its declared assurance or **refuses**; no path silently lands on
    a weaker mode than declared. *(the enforce-or-refuse-across-the-whole-fallback-chain
    theorem.)*
  - **#2 — address/label→port key-inference as explicit spec.** The orb's inference
    rules transcribed VERBATIM (domain→:443+auto-TLS; address→listen; label→explicit),
    and `realize()` proven to honor them.
  - **#3 — runtime-injected dynamism MODELED SEPARATELY** (not "excluded") for the
    auth/TLS-issuance subset: on-demand-TLS authz, JWT rotation, health-driven upstream
    state, glob routing, MITM cert-gen (R4.7), live tunnels (R4.7m).
  - **#4 — proxy/MITM CA (R4.7/R4.6m):** a host-glob-scoped trust anchor; the CA
    private key **never leaves its PD**; trust-store injection bounded+declared.
  - **#5 — CONNECT-IP/UDP/MASQUE egress:** a declared-destination-gated capability
    (`ConnectIpAcl`; same shape as R4.9's SOCKS ACL).
  - **#6 — 0-RTT / early-data anti-replay (the 0-RTT replay-safety theorem):** the
    R2.5 early-data path is replay-safe — StrikeRegister + single-use ticket means no
    accepted 0-RTT request is processed twice.
  - **#7 — CGI / process-exec (R4.9):** an explicit capability obligation vs the seL4
    minimal-cap net PD (which holds only the NIC cap + `turn_in`) — see ADR-N2.

  **Positive-safety dual** (proven alongside the negative confinement): the declared
  resource bounds folded in at R4.3 (`maxConnections`, `BodyLimit`, `ConnectionLimit`,
  `RateLimit`, per-phase timeouts) are ENFORCED at *every* admission point — **no
  client can exhaust the reactor.** *Done:* no `sorry`; the negative-safety properties,
  the positive-safety bounds, and the transition-system invariant all hold. *Deps:*
  R4.3, R4.11, R2.5.
- **R5.3 — The lease-safety theorem.** "The net PD never admits a turn beyond the
  cap/budget" = the dregg `HostingLease.lean` discipline, restated engine-side and
  proven at ingress. *Done:* proven; diff vs the Lean oracle. *Deps:* R5.1.
- **R5.4 — TLS record/handshake FSM verification + crypto-primitive axiom retirement
  (discharges CR-2's TLS axiom; ADR-N4, F-12).** *Goal:* retire the trusted-rustls
  boundary R2.1 stood up — the part CR-2 forbids leaving unverified in the lineage —
  the named successor rung ADR-N4 and F-12 promise. *Deliverable:* the TLS
  record-layer + handshake FSM verified as a `machine` (ADR-7) — the FSM that decides
  plaintext-vs-encrypted, key epochs, and 0-RTT acceptance, i.e. exactly where
  soft-spots #1 (TLS-mode fallback) and #6 (0-RTT anti-replay) live — and the
  crypto-primitive axioms (AEAD/KDF/signature) retired into proof via the
  Isabelle/CryptHOL `uc-crypthol` foothold (ADR-3, ADR-N4). *Done:* the rustls
  effect-interface axiom from R2.1 is replaced by proof **or** a single named
  primitive-axiom (the narrowed CR-2 axiom), with no security-deciding logic left in
  the axiom; **F-12 discharged**; R5.2's soft-spot #1 clause now rests on a verified
  FSM, not a trusted blob, and feeds the narrowed TCB of R7.2. *Deps:* R2.1, R5.2; the
  `uc-crypthol` crypto track (R0.2, R4.6m).

## Phase 6 — Raw NIC + hardware sharding (ADR-O2)

- **R6.1 — Real multi-queue hardware NIC (E810 default).** The verified raw-NIC
  driver on real metal; line rate. *Deps:* R5.1.
- **R6.2 — (moat) Corundum FPGA + verified P4 steering.** The SW/HW co-design start;
  verified steering (Petr4/p4v). *Deps:* R6.1 or taken first per ADR-O2 revisit.

## Phase 7 — The vertical proof + kernel reformalization (close the chain)

- **R7.1 — Kernel reformalization (Track K, ADR-O4).** Reformalize the 77-module
  `Exec.FFI` closure into HOL4; CakeML-compile it; delete the `sel4-musl`/GMP/libuv
  hack. Lean = oracle (diff-test). *Done:* the executor PD runs CakeML-compiled
  verified machine code. *Deps:* R0.2; parallel from Phase 1.
- **R7.2 — Close the vertical proof (done-criterion #1).** Compose: conservation
  (kernel) → lease-safety → confinement → parsers/IO/FSM → verified compilation →
  seL4 (l4v) → the NIC device axiom. One refinement chain, one logic. *Done:* the
  composed theorem; the TCB is exactly the prover kernel + the named axioms.
  *Deps:* R5.2, R5.3, R7.1, R3.*.

## Phase 8+ — Silicon (the asymptote)

- **R8.1 — Verified RTL retarget.** Point the verified compiler at an FPGA/ASIC
  backend; re-prove the backend delta; the correctness theorem holds across the
  retarget. The custom-silicon dataplane stays verified. *Deps:* R6.2, R7.2.

---

## Standing tracks (run across phases, not gated to one rung)

- **T-RETIRE — External-crate retirement track.** *Goal:* the orb leaned on
  trusted external crates; each is a standing debt to retire to a generated verified
  replacement — but **only when the replacement meets a measured perf target**, never
  a regression for purity's sake. *Scope + landing rung:* `moka` (cache) → R4.6's
  verified store; `governor` (rate-limit) → R4.3's bound types + R5.2 enforcement;
  `h2` (HTTP/2) → R2.4's generated codec; `brotli` → a generated verified
  compressor; `http_cache_semantics` → R4.6's freshness model. *Done (per crate):*
  the generated replacement oracle-matches the crate's observable behavior AND meets
  its `22-PERFORMANCE.md` perf gate; only then is the dependency deleted. Until both
  gates are green the external crate stays — retirement is earned, not forced (CR-6:
  no laundered "we replaced it" that secretly regresses). *Deps:* per-crate landing
  rung above.

---

## Milestones (for the operator's fleet coordination / progress narration)

- **M1 — "the seed":** R1.1 + R1.2 + R1.3 green — the proof-producing loop works
  end-to-end and the request model is verified against the oracle.
- **M2 — "the pure engine":** Phases 2–3 — the whole engine generated/proven except
  integration; the four Iris proofs closed.
- **M3 — "talks to dregg":** R4.1 — the engine is a working CapTP netlayer.
- **M4 — "the freed orb":** R4.3 — gate-free orchestrator stands up a node from a
  spec; the liberation is real (AGPL, gate deleted).
- **M5 — "on the metal":** R5.1 + R6.1 — line-rate on a real NIC as the seL4 net PD.
- **M6 — "wire to NIC, one proof":** R7.2 — the vertical proof closes. Project
  done-criterion #1 met.

Each milestone is a batched, gated checkpoint (`decision-spirit` #19: batch the
costly at milestones, stream cheap verified increments between).

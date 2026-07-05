# 20 — ARCHITECTURE

The layered system, top to bottom, and the two unifications that make it coherent.

## The pipeline (one source → three outputs)

```
            ┌─────────────────────────────────────────────────────────┐
   SPEC →   │  Declarative server-node spec  (the apex artifact)       │  ADR-6, ADR-9
            │  — listeners, routes, TLS modes, middleware, caps —      │
            └───────────────────────────┬─────────────────────────────┘
                                        │ described in
            ┌───────────────────────────▼─────────────────────────────┐
   DSL  →   │  The engine DSL  (4 primitives — ADR-7)                  │
            │  machine · region/view · linear · shared                 │
            └───────────────────────────┬─────────────────────────────┘
                                        │ compiled by
            ┌───────────────────────────▼─────────────────────────────┐
COMPILER →  │  The verified compiler we OWN  (CR-4, ADR-3)             │
            │  our front-end + domain passes (verified vectorization,  │
            │  zero-copy region fusion, run-to-completion lowering)    │
            │  ── on top of ──  CakeML/Pancake verified backend        │
            └───────────────────────────┬─────────────────────────────┘
                     emits, all three from one description:
        ┌───────────────────┬───────────────────┬───────────────────┐
        ▼                   ▼                   ▼
   machine code        the formal model     ~90% of the proofs
   (line-rate)         (HOL4/Isabelle)      (routine obligations
                                             auto-discharged;
                                             ~10% residual by hand)
                                        │ runs as
            ┌───────────────────────────▼─────────────────────────────┐
SUBSTRATE → │  seL4 Microkit net PD(s)  (ADR-4)                        │
            │  net (raw-NIC driver) + net_client (protocol/ingress)    │
            │  joined by sel4-shared-ring-buffer → turn_in/cap gate    │
            └───────────────────────────┬─────────────────────────────┘
                                        │ on
            ┌───────────────────────────▼─────────────────────────────┐
  METAL  →  │  raw multi-queue NIC  (E810 → Corundum FPGA → silicon)   │  ADR-O2
            │  RSS/Flow-Director sharding · zero-copy DMA · busy-poll  │
            └─────────────────────────────────────────────────────────┘
```

The compiler is the **proof-producing translator**: the DSL description in →
{code, model, proofs} out. Owning + verifying it (CR-4) turns the routine
per-instance obligations into consequences of the *compiler-correctness theorem*,
leaving only the domain residual (the `shared` proofs + the confinement theorem)
for hand-proof.

## The three product tiers

The deliverable is not just the dataplane libraries; it is the operable orb. Three
tiers (the orchestration + operational tiers were never vendored into DreggNet —
they live in the internal Elide HTTP-engine source tree (`crates/cli`) as oracle):

1. **Engine libraries** — the protocol/IO/TLS/QUIC machines (the `httpe`/`iocoreo`/
   `transport`/`pki` surface). The hot dataplane. Carries CapTP + HTTP/1/2/3 **and the
   proxy dataplanes**: reverse proxy, forward proxy, L4 (TCP/UDP) proxy, SOCKS, and
   CONNECT-IP/MASQUE tunneling — each feeding `turn_in`/cap-gate. Protocol scope also
   includes **WebRTC (IN)** and **gRPC (IN)** as first-class tier-1 surfaces, not
   bolt-ons.
2. **Orchestration** (`orb`/`serve`/`server_infra`) — declarative-spec → configured
   multi-protocol node; the Tailscale/WireGuard/Funnel/DERP mesh; ACME/private-PKI;
   admin API; zero-downtime upgrade with live connection migration. The cold control
   plane.
   - **upgrade / fd-escrow seam** — zero-downtime upgrade requires handing live
     connections (their fds/sockets) from the outgoing image to the incoming one. On
     Linux this is `SCM_RIGHTS` fd-passing to an escrow; on seL4 there are no fds, so it
     **reconciles** to handing the NIC cap + ring-buffer endpoints + per-connection state
     caps across a PD swap (or in-place re-link), preserving the cold/hot split and the
     reload-atomicity clause of the confinement invariant (no double-bound-listener
     window during the swap). This is a genuine scope fork — zero-downtime upgrade on a
     *static* seL4 PD — captured as an ADR and **FLAG-FOR-EMBER**.
3. **Operational** (`expose`/`cert`/`dev`) — the deployable-product commands. Core:
   `expose`/`share` (one-command public HTTPS), `cert` (PKI/ACME lifecycle), `dev`
   (live-reload). Drop: `upgrade` (Elide TUF self-update), licensing, telemetry.

## The cold/hot split (CR-5) — why best-perf AND highest-assurance coexist

| | Cold control plane (tier 2) | Hot dataplane (tier 1) |
|---|---|---|
| Runs | once at boot / reload / cert-renew | per packet |
| Binds | **policy assurance** | **performance** |
| Verification | the heaviest — the confinement theorem; **zero runtime cost** | verified-by-construction; the compiler-correctness theorem; line-rate |
| Mesh | mesh **control** plane — peer/key/route negotiation, DERP/Funnel session setup, ACL distribution | mesh **data** plane — per-packet encrypt/decrypt/forward, verified-crypto, under the line-rate budget |
| Failure it prevents | exposed admin, wrong/degraded TLS, undeclared port, an undeclared peer/route | a dropped packet / a copy / an allocation on the hot path |

The confinement theorem (the orchestrator's crown) is a **transition-system
invariant**, not a single static check. For a well-formed spec `C`,
`realize(lower(render(C))) ≡ declared(C)` — nothing runs/listens/exposes/authorizes
that `C` didn't declare, and no declared security property silently degrades. Crucially
it must hold under *mutation*: for every admin API mutation / SIGHUP reload `δ`,
`realize(apply(δ,C)) ≡ declared(apply(δ,C))`, with **reload atomicity** — no
double-bound-listener window, no degraded-TLS window across the transition. Confinement
is the invariant preserved by every δ, not a property of one boot.

The theorem must range over **all seven** known soft-spots — the places where the
naïve `render`/`realize` is *not* 1:1 and silence would launder a security hole. Each
is an explicit clause (per CR-6, no laundered vacuity: each is real or explicitly
handed back, never a soft-spot we secretly mean to skip):

1. **TLS-mode fallback** — enforce-or-refuse, NEVER silently downgrade. `auto-https` +
   missing-email must not silently become plaintext; generalize to the whole
   `ExposeMethod` fallback chain (auto → Funnel → ACME → self-signed → plain): each
   step is a declared, refusable transition, never an ambient downgrade.
2. **address/label→port key-inference** — transcribe the orb's rules VERBATIM as
   explicit spec (domain → `:443` + auto-TLS; address → listen; label → explicit) and
   prove `realize()` honors them; the inference is hidden spec, so it becomes spec.
3. **runtime-injected dynamism** — **MODELED SEPARATELY** (not excluded) for the
   auth/TLS-issuance subset: on-demand-TLS authz, JWT rotation, health-driven upstream
   state, glob routing, MITM cert-gen, live tunnel channels.
4. **proxy/MITM CA** — a host-glob-scoped trust anchor; the CA private key NEVER leaves
   its PD; trust-store injection is bounded + declared.
5. **CONNECT-IP/UDP/MASQUE egress** — a declared-destination-gated capability
   (`ConnectIpAcl`); no egress to an undeclared destination.
6. **0-RTT / early-data anti-replay bound** — a proven replay-safety property
   (`StrikeRegister` + single-use ticket); early data is accepted only when replay-safe.
7. **CGI / process-exec** — an explicit capability obligation against the seL4
   minimal-cap net PD (which holds only the NIC cap + `turn_in`); spawning a process is
   a declared cap grant, not ambient authority. See ADR for the scope fork.

`render(C)` emits a concrete, inspectable **config-IR** — the `ConfigIR` (the orb's
`JsonRenderer` analog): a fully-resolved, normal-form description of every listener,
route, TLS mode, middleware chain, proxy/upstream binding, and resource bound, with all
inference (§2 key-inference, §1 fallback chains) already discharged. It is `ConfigIR`,
not the surface spec, that the cold-plane **certifying interpreter** consumes and
`lower`s; the confinement theorem is stated over it precisely because it is the artifact
where "what we will realize" is made explicit and machine-checkable.

**Positive-safety dual** (the negative confinement above says *nothing undeclared
happens*; this says *the declared bounds are kept*): the declared resource bounds —
`maxConnections`, `BodyLimit`, `ConnectionLimit`, `RateLimit`, per-phase timeouts — are
ENFORCED at every admission point. No client can exhaust the reactor. This is a proof
obligation of the cold plane as much as the negative confinement is.

## Unification 1 — the cap fabric at three distances

An seL4 capability and a dregg capability are the same abstraction at points on a
*distance parameter n* (firmament thesis, l4v-proven in
`metatheory/Dregg2/Firmament/`). The engine completes the fabric's reach:

```
n=1   kernel mint           (seL4, immediate revoke, synchronous commit)
n≈1   in-node delegation    (dregg cells)
n>1   CapTP handoff         (over THIS engine — the long-distance reach)
```

The engine carries the far end, as a PD holding **only** the NIC cap + `turn_in` —
the cap OS hosts its own cap-transport, confined by the caps it transports.

**Handle-as-capability.** Every resource the dataplane exposes — connections, streams,
upstreams, tunnels, cert slots — is named by an **opaque generational handle**, not a
raw fd or pointer. There is no ambient fd authority: holding a handle *is* the
authorization to act on that resource, and a stale generation fails closed rather than
aliasing a recycled slot. This is the n≈1 in-node face of the same cap fabric — the
fd-escrow seam (tier 2) hands *handles/caps*, never ambient descriptors, which is what
lets the seL4 reconciliation (no fds) be a re-mapping rather than a redesign.

## Unification 2 — the fastest shape IS the most-provable shape (CR-1)

A data-oriented transformation over flat regions with explicit ownership is:
cache-friendly, branch-lean, vectorizable, zero-alloc (**fast**) **and** a pure
function over byte-lists with *decidable* in-bounds obligations (**auto-provable**).
Pointer-chasing, hidden allocation, ambient mutability are slow *and* unprovable.
The DSL's primitives are chosen to sit exactly at this intersection — which is why
optimizing for speed and optimizing for generatable proof push the same direction.

## Migration path (substrate-portability, ADR-O3)

Because the protocol core is **sans-IO** (`(state, bytes) → (state', events, out)`),
the substrate is swappable under a fixed verified core:

```
develop over Linux/AF_XDP  →  port to seL4/sDDF (core unchanged)  →  FPGA-offloaded
                                                                     steering → silicon
```

The verified compiler is the SW/HW co-design vehicle (CR-4): the same DSL spec
emits verified machine code today and verified RTL tomorrow, with the correctness
theorem holding across the retarget. That is the moat — anyone can build the chip;
we can *prove* the chip runs the spec.

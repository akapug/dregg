# Sandstorm × DreggNet — defense-in-depth for a malicious grain on the overlay

This document is the **threat model** and the **layered defense** for the one case
that matters most in the integration: *a hostile third-party `.spk` app, sandboxed
as a grain, reachable on the dregg overlay.* It is the security companion to
`SANDSTORM-INTEGRATION-PLAN.md` (the architecture) and grounds the containment code
in `../sandstorm-bridge/` (`net.rs`, `limits.rs`, `tenant.rs`, `bridge.rs`,
`grain.rs`).

The premise is adversarial and unconditional: **assume the grain's code is fully
malicious.** A `.spk` is third-party code we did not write and do not trust. The
integration's whole value proposition — *run hundreds of catalog apps you verify
instead of trust* — only holds if a hostile app, even one a user has chosen to
expose on the overlay, is contained by construction. So we do not ask "is this app
safe"; we ask "what can the worst possible app do, and which independent layer stops
each thing."

---

## 1. Threat model

The grain is a process running attacker-controlled code. It is reachable by overlay
clients (the user chose to expose it). It is one of many grains, of many tenants, on
a host the user does not necessarily operate. Against that, the things a malicious
grain MUST NOT be able to do — each with the layer that stops it:

| # | Threat (what the hostile grain attempts) | Stopped by |
|---|---|---|
| T1 | **Escape the sandbox** to the host kernel / other processes | **L1** sandbox (ns + seccomp + tier) |
| T2 | **Reach the network** — the internet, a cloud metadata endpoint, another grain, or *the overlay itself* — except via an explicit cap | **L2** network isolation |
| T3 | **Gain authority beyond its caps** (ambient authority, confused-deputy) | **L3** capability bounds + **L7** the bridge choke |
| T4 | **Exhaust host resources** (CPU / memory / storage / unmetered runtime) | **L4** resource bounds |
| T5 | **Tamper the bytes a visitor sees** (a compromised host/operator serving lies) | **L5** verification (dregg-unique) |
| T6 | **See or affect another tenant's grain** | **L6** multi-tenancy + **L7** the bridge choke |
| T7 | **Find a side channel** around the mediated path (any I/O the supervisor didn't gate) | **L7** the bridge as the single choke point |

Two properties make this tractable rather than a wall of hopes:

1. **Defense-in-depth.** The layers are *independent*: a single failure does not
   breach. If the seccomp filter has a hole (L1), the grain still has no network
   (L2), no ambient authority (L3), no cross-tenant visibility (L6), and a bounded
   lease (L4). The attacker must defeat *every* relevant layer, not one.
2. **dregg adds layers Sandstorm-alone lacks.** Sandstorm gives L1/L2/L6 by
   construction and L3/L7 by *enforcement* (trust the supervisor). dregg makes L3/L7
   *provable* (the cap-mediation leaves a witnessed receipt) and adds **L5 entirely**
   (the served bytes are verifiable against a committed cell root — even a
   compromised host cannot tamper undetected). See §4.

---

## 2. The layers

Each layer is stated as: *the threat it owns · the Sandstorm mechanism · the dregg
realization · where it lives in code.*

### L1 — Sandbox (the grain process cannot escape) · owns T1

- **Sandstorm:** the supervisor `unshare()`s user/mount/IPC/UTS/PID **and network**
  namespaces, *forbids further namespace creation* (neutralizing the unprivileged-
  userns CVE class), `PR_SET_NO_NEW_PRIVS` + a **seccomp-bpf** syscall allowlist
  (blocks `ptrace`/`keyctl`/`bpf`/`mount`/further-seccomp), a read-only app-image
  bind-mount + read-write `/var`, no `/proc`/`/sys`, only `/dev/{null,zero,urandom}`,
  and `chroot`s away from the app FS.
- **dregg:** the **`Caged`** tier (native + seccomp-bpf + Landlock — the faithful
  analog of the supervisor) or, strictly stronger, the **`MicroVm`** tier
  (Firecracker, its own guest kernel behind KVM). **SBX deny-default + per-tenant**
  is the same starting posture (a fresh grain reaches nothing). A grain *never*
  routes weaker than `Caged`; an in-process wasm tier would be a silent isolation
  *downgrade* and is forbidden (`dreggnet-exec`'s `check_floor` rule).
- **Code:** `grain.rs::SandboxTier` (Caged / MicroVm; no weaker variant exists),
  `manifest.rs::grain_spec` (http-bridge apps → `Caged`, raw apps → `MicroVm`); the
  production jail is `dreggnet-exec`'s `CapTier` (`exec/src/lib.rs`,
  `docs/COMPUTE-TIERS.md`).
- **Residual (honest):** L1 is a kernel-isolation floor — a real seccomp/KVM escape
  is the standard sandbox-escape carrier, the reason **executing downloaded `.spk`
  code on a live tier is REVIEWED-GO** (`SANDSTORM-INTEGRATION-PLAN.md` §9) and the
  reason the strong default is `MicroVm` for anything but a vetted http-bridge shape.
  The point of L2–L7 is that an L1 escape still does not yield the network, authority,
  neighbours, or undetectable tampering.

### L2 — Network isolation (the critical layer for overlay-expose) · owns T2

This is the layer the overlay-expose decision turns on, and the one most prone to a
confused-deputy / SSRF mistake. The load-bearing distinction:

- **OUTBOUND (egress)** is **denied by default.** A grain has no ambient network — no
  interface but loopback, no DNS, no peer reach (Sandstorm's unshared net namespace).
  It may reach an external destination *only* through a powerbox-granted
  **`OutboundCap`** naming a **specific** host+port — one service, never "the
  internet" and never a wildcard. This is the dregg analog of Sandstorm's sanctioned
  HTTP-driver grain.
- **INBOUND (overlay-expose)** is **bridge-only.** Exposing a grain on the overlay
  publishes the **bridge endpoint** (`<name>.example.com`), through which clients
  reach the grain's HTTP — the bridge cap-gates the request and injects identity. It
  does **not** hand the grain a network handle. The grain never receives an overlay
  reference; it only ever sees the `BridgedRequest`s the bridge delivers.

**The crucial invariant: inbound exposure confers zero egress.** A hostile grain that
is reachable on the overlay still cannot itself reach out — not to the internet, not
to a neighbour, not even to the overlay it is exposed on. Exposing the bridge is not
giving the grain overlay access. The two directions are independent by construction;
conflating them is exactly the SSRF/confused-deputy hole this layer closes.

- **Code:** `net.rs` — `NetworkPolicy::confined()` (empty allow-list = deny-all),
  `grant_outbound`/`revoke_outbound`/`check_outbound` (the egress gate),
  `OutboundCap` (exact host+port, no globbing), `OverlayExposure::expose` (inbound;
  *never touches* a `NetworkPolicy` — proof in `net.rs` that exposure adds no egress).
  The egress gate is reached only through the bridge: `bridge.rs::HttpBridge::egress`.
  Tests: `net::tests::exposed_grain_still_cannot_reach_out`,
  `bridge::tests::a_grain_with_no_outbound_cap_cannot_egress`,
  `integration_tests::a_hostile_grain_is_refused_at_every_layer`.

### L3 — Capability bounds (no ambient authority) · owns T3

- **Sandstorm:** a new grain is *totally confined*; the only authority it ever holds
  is a Cap'n Proto capability the user handed it **through the powerbox**
  (designation = authorization). The supervisor enforces it holds only what it was
  given.
- **dregg:** the grain holds only powerbox-granted dregg caps, and a grant is a
  **strictly-attenuating** `Effect::GrantCapability` turn — `granted ⊆ held`, refused
  in-band otherwise (no amplification). The powerbox is the **sole** authority-gain
  path, user-mediated. **dregg adds:** the grant leaves a *witnessed receipt* — "user
  A delegated cap C (facets {view}) over grain G to app B" is provable to a third
  party who trusts neither host nor app (the confused-deputy immunity Sandstorm gives
  you, *plus a proof*).
- **Code:** `powerbox.rs` — `PowerboxGrant::mint` (refuses `Amplification` /
  `WrongTarget`), `DreggCapRef::dominates` (the submask attenuation order),
  descriptor→`Pred`→picker (`present`) so an app only ever receives a cap the user
  designated from their *own* held set. Tests: `over_granting_is_refused_in_band`,
  `you_cannot_grant_over_a_target_you_do_not_hold`,
  `from_query_refuses_a_cap_the_principal_does_not_hold`.

### L4 — Resource bounds (a grain cannot exhaust the host) · owns T4

- **Sandstorm:** loose — idle-shutdown frees a grain's RAM after ~90 s.
- **dregg:** economic and tight. A workload runs only under a **funded lease** ("no
  run beyond what the lease authorizes"), and four independent quotas — **uptime,
  CPU-ms, peak memory, stored bytes** — are charged against it. A charge that would
  exceed a bound is **fail-closed**: refused and not applied, and the grain is reaped.
  A hostile `.spk` cannot run unmetered, busy-loop the CPU, balloon memory, or fill
  the host disk. Idle grains sleep (bill only storage), so the meter stops without an
  operator in the loop.
- **Code:** `limits.rs::ResourceLease` (`bounded(...)`; `charge_uptime`/`charge_cpu`/
  `observe_mem`/`admit_storage`, each returning `LeaseError::Exhausted` without
  applying), wired into `grain.rs` (`meter_period` charges the lease;
  `charge_cpu`/`observe_mem`/`admit_storage`) and into the bridge's write path
  (`bridge.rs::serve_bounded` rolls back an over-quota write and answers `507`).
  Tests: `limits::tests::*`, `grain::tests::a_grain_that_outruns_its_lease_is_reaped`,
  `bridge::tests::a_storage_bomb_is_refused_and_rolled_back`.

### L5 — Verification (the dregg-unique layer) · owns T5

This layer has no Sandstorm analog. A Sandstorm host you must trust to serve a grain's
bytes honestly; a compromised or dishonest host/operator can serve whatever it likes.

- **dregg:** the grain's `/var` *is* a cell's umem heap, committing to a content-
  addressed **`data_root`**. The served output is wrapped so a visitor's browser
  **re-witnesses** that what it received binds to the committed grain cell. The host
  cannot tamper with a grain's served bytes (or lie about its state, or overcharge —
  every charge is a re-witnessable conserving `Transfer`) without the visitor
  catching it. This is the property no Sandstorm host, and no trusted-always-on host,
  offers: you *verify* the app instead of *trusting* the operator.
- **Code (this crate's stand-in):** `cell.rs::Umem::commit` (content-addressed
  `data_root`, order-free, re-witnessable; tested in
  `cell::tests::commit_is_order_free_and_content_addressed`) and the bridge committing
  a new `data_root` on every served write (`Served::new_data_root`). The production
  weld is breadstuffs' `turn/src/umem.rs` + the light-client / trustless-render path
  (`deos-view::render_trustless_cell_document`).

### L6 — Multi-tenancy (grains isolated from each other) · owns T6

- **Sandstorm:** by construction — each grain is its own sandbox, private to its
  creator, shared only by an explicit powerbox grant; there is no ambient way for
  grain A to learn grain B exists.
- **dregg:** a **tenant partition** above the owner. A grain belongs to a `TenantId`;
  the registry refuses every *ambient* cross-tenant operation — enumeration,
  lookup-by-id, and reach. A cross-tenant id returns the same `NotVisible` as a
  nonexistent id, so a probe leaks nothing about a neighbour's existence. Cross-tenant
  reach requires a powerbox cap (which routes through L3/L7, leaving a receipt), never
  ambient discovery.
- **Code:** `tenant.rs::TenantRegistry` (`visible_to` / `resolve` / `may_reach_-
  ambiently`), `grain.rs` (each grain carries a `TenantId`, per-owner by default,
  overridable via `with_tenant`). Tests: `tenant::tests::*`.

### L7 — The bridge as the single cap-gated choke point · owns T7 (and backs T3/T6)

- **Sandstorm:** the grain's *only* outside connection is a single Cap'n Proto socket
  on FD #3; `sandstorm-http-bridge` owns it, implements `WebSession`, and proxies
  HTTP-over-RPC to the in-sandbox `:8000` server — injecting the
  `X-Sandstorm-{User-Id,Username,Permissions,Session-Id}` headers. There is no other
  I/O surface.
- **dregg:** the bridge is the grain's *only* I/O path, in **both** directions:
  - **inbound** — `HttpBridge::serve` derives the `X-Sandstorm-*` headers from the
    holder's dregg cap (the cap's facets *become* `X-Sandstorm-Permissions`), and a
    cap that does not name *this* grain is inert (no ambient authority crosses the
    bridge);
  - **outbound** — `HttpBridge::egress` is the only egress, gated by the grain's
    `NetworkPolicy` (L2).
  Nothing bypasses it: a grain that cannot route through the bridge cannot do I/O at
  all. **dregg adds:** the mediation is *provable* — the permission an app acted under
  is the cap it held, witnessed, not an identity the host merely asserted.
- **Code:** `bridge.rs` — `serve` / `serve_bounded` (inbound choke + the
  cap-names-this-grain check), `egress` (outbound choke), `bridge_request` (headers
  derived from the cap, never a raw identity). Tests:
  `bridge::tests::a_cap_for_another_grain_is_inert`,
  `headers_are_derived_from_the_cap_facets`,
  `egress_is_allowed_only_through_a_granted_cap`.

---

## 3. Why the layers are independent (the defense-in-depth argument)

The threats and layers are deliberately cross-linked so that no single failure
breaches the grain:

- An **L1 sandbox escape** (a seccomp/KVM hole) still leaves the escapee with **no
  network** (L2 — the net namespace and the empty egress allow-list are separate from
  the syscall filter), **no ambient authority** (L3 — caps are held in dregg's
  c-list, not ambient in the process), **no cross-tenant visibility** (L6 — the
  registry partition is enforced above the process), and a **bounded lease** (L4).
- An **L2 egress bug** (a granted cap too wide) still cannot exfiltrate another
  *tenant's* data (L6) or act with authority the grain was not granted (L3), and the
  served bytes remain **verifiable** (L5) so tampering is caught.
- An **L7 bypass** (a side channel) is the thing L1+L2 jointly deny: the only socket
  is FD #3 / the bridge; there is no second surface to bypass *to*.
- **L5 is orthogonal to all of them** — even if the *host itself* is the attacker
  (every other layer is the host's to enforce), the visitor still re-witnesses the
  served bytes against the committed cell root. L5 is the layer that survives a
  compromised operator, which is precisely the trust dregg removes.

The attacker must defeat *every relevant layer*, and L5 must be defeated by breaking
cryptography (Poseidon2-CR / FRI soundness — the standard carriers), not by finding a
bug in our code.

---

## 4. How dregg adds layers Sandstorm-alone lacks

Sandstorm is an excellent object-capability runtime; the integration is a *welding*,
not a replacement. But three of the seven layers are strictly stronger on dregg:

- **L5 verification — entirely new.** Sandstorm has no notion of a verifiable served
  byte or a witnessed grain state; you trust the supervisor and the host. dregg makes
  the grain's data, its served bytes, and its bill each re-witnessable against a
  committed cell. *The host cannot lie about what it served or charged.* This is the
  category difference — verify, don't trust.
- **L3 capability bounds — from enforced to provable.** Sandstorm's supervisor
  *enforces* `granted ⊆ held`; dregg's grant is a *witnessed turn*, so a third party
  can check, after the fact and trusting no one, that an app holds exactly the
  authority it was granted and no more (confused-deputy immunity *with a proof*).
- **L7 the choke point — from trusted to witnessed.** The permission an app acts
  under is the cap it demonstrably held (derived per request, witnessed), not an
  ambient identity the host asserts on its behalf.

The payoff is the security thesis of the whole integration: **even a fully-malicious
`.spk` is contained — and the trust the user is required to extend is both minimized
and provable.** Sandstorm contains it; dregg lets you *verify* the containment.

---

## 5. Implementation status

| Layer | Modeled + tested in `sandstorm-bridge/` | Needs the production weld / an operator's live instance |
|---|---|---|
| L1 sandbox | `SandboxTier` (never-weaker-than-Caged), tier routing | `dreggnet-exec` Caged/MicroVm jail; executing real `.spk` code is REVIEWED-GO (Firecracker boot + jailer) — needs an operator's live Sandstorm as the behavioral oracle |
| L2 network | **`net.rs`** — confined default, exact-service egress caps, inbound≠egress invariant, the egress gate | wiring the gate into the Caged tier's `instantiate_with_caps` net-cap; the live overlay-expose lane (Caddy + cert) is REVIEWED-GO |
| L3 caps | `powerbox.rs` — attenuating grant, anti-amplification, descriptor→Pred picker | weld onto breadstuffs `starbridge-v2/powerbox.rs` + cipherclerk + a real `Effect::GrantCapability` receipt |
| L4 resources | **`limits.rs`** + `grain.rs` + `bridge.rs::serve_bounded` — four quotas, fail-closed | weld onto `bridge/`(lease) + `storage/meter.rs` + the StandingObligation settle rail |
| L5 verification | `cell.rs::Umem::commit` (content-addressed `data_root`) + per-write commit | weld onto `turn/src/umem.rs` + the light-client trustless render |
| L6 multi-tenant | **`tenant.rs`** — partition, no enumeration, no existence oracle | weld onto the real cell/tenant model + per-tenant SBX |
| L7 bridge choke | `bridge.rs` — inbound serve + outbound egress, cap-derived headers, cap-names-this-grain | weld onto `gateway/` + `webapp/router.rs` (the `WebSession` HTTP surface) |

`cargo test -p sandstorm-bridge` exercises every layer, including
`a_hostile_grain_is_refused_at_every_layer` — a fully-malicious grain attempting each
threat in turn, every one refused. **What needs an operator's live Sandstorm:** the L1
sandbox-escape surface (real seccomp/KVM behavior), real signed `.spk`s to test the
reader against, and real `WebSession`/permission traffic to differential-test the
bridge contract — the things you cannot prove against fixtures alone.

*Dated 2026-06-29. Verify file paths against HEAD before relying on a specific line.*

# Sandstorm × DreggNet — devnet-ready

This is the state of the Sandstorm integration after the prototype→devnet weld:
what is now wired onto the real DreggNet surfaces, the end-to-end proof that runs
locally, and the honest remaining before a grain serves on the live overlay.

The prior state was a sound but **detached** `sandstorm-bridge/` crate — its own
workspace + lock, no dependency on the real DreggNet crates — that *modelled* the
integration with real `.spk` crypto but ran the grain in-process. It is now a wired
workspace member whose load-bearing paths run on the real `dreggnet-exec`,
`dreggnet-webauth`, and `dreggnet-webapp` surfaces.

## What is now welded

### De-detached into the workspace
`sandstorm-bridge` is a `DreggNet` workspace member (the empty `[workspace]` table
is gone; the detached `Cargo.lock` is removed). It path-depends on `dreggnet-exec`,
`dreggnet-webauth`, and `dreggnet-webapp`, and resolves + builds + tests against the
one workspace lock.

### ① Grain workload → the real `dreggnet-exec` compute tier
`exec_workload.rs` runs a grain's request handler through the real
`dreggnet_exec::run_workload_with_input` at the grain's demanded tier, mapped to the
real `CapTier`:

- `SandboxTier::Caged → CapTier::Caged` — a real OS-sandboxed native process
  (seccomp-bpf + Landlock on Linux). An http-bridge app routes here.
- `SandboxTier::MicroVm → CapTier::MicroVm` — a per-grain Firecracker microVM behind
  the KVM boundary; refuses cleanly where `/dev/kvm`/firecracker are absent (never a
  silent downgrade).

and **never weaker** — the mapping has no wasm route, and `dreggnet-exec`'s
`check_floor` rule is the production backstop. The grain's request and its `/var`
(the cell umem heap) are marshalled into the workload input; the handler returns the
HTTP response + the new `/var`, and the achieved enforcement level is **surfaced**
(`OsSandbox` on a Linux Caged host, `Container` on a KVM MicroVm host, `None` where
the OS cannot cage — never hidden). The representative permissioned-notes handler
runs as a genuine `python3` subprocess through the tier; a real catalog grain swaps
in its `.spk` chroot entrypoint (the reviewed-go step below).

### ② Powerbox → the real `dreggnet-webauth` `dga1_` cap rail
`webauth_rail.rs` makes a grain capability a **real** `dreggnet_webauth::cred::Credential`
— the ed25519 caveat-chain `dga1_…` token (the same wire `dregg-auth` / the gateway's
forward-auth understands), rooted at the host's `RootKey`. A grain cap binds three
first-party caveats: `grain` (the target cell), `subject` (sealed-to-owner), and a
`cap` disjunction (the facet set). The bridge derives `X-Sandstorm-Permissions` by
asking the **real `Credential::verify`** which declared facets the cap admits for this
presenter over this grain — derived from the cap lattice, never asserted by the host.

Every powerbox security property now holds *cryptographically* on the real rail:
a **forged** cap (not signed by the host root) fails the ed25519 chain verify; a
**leaked** cap presented by a non-owner fails the `subject` caveat; a cap for
**another grain** fails the `grain` caveat; **amplification** is impossible because
`Credential::attenuate` only appends caveats (the facet set can only shrink). A
powerbox grant is the minted/attenuated credential (the DreggNet-side
`Effect::GrantCapability` artifact); the witnessed kernel turn itself lives in the
breadstuffs authority core (the in-circuit witness is the substrate swarm's lane).

### ③ Serving → the real `dreggnet-webapp` site surface
`serving.rs` serves a grain as a hosted cell through the real
`dreggnet_webapp::{WebRequest, WebResponse, SiteRegistry}` — the exact surface the
httpe `dreggnet-gateway` `SiteHostHandler` adopts (the gateway reads the `Host`
header off the socket and calls this same `SiteRegistry`). Routing is the real
`dreggnet_webapp::site_name_from_host` (`<name>.example.com` wildcard). `serve_grain`
routes by host, derives permissions from the presented `dga1_` cap, injects the
`X-Sandstorm-*` identity headers, runs the handler on the real exec tier, and returns
a real `WebResponse`. `publish_grain_snapshot` publishes the grain's served bytes as a
`SiteCell` through the real, cap-gated, receipted `SiteRegistry::publish` turn — the
verifiable-serving differentiator, so a visitor re-witnesses what they were served.

> The httpe `dreggnet-gateway` front (the `SiteHostHandler`/`httpe` socket layer) is
> the same dispatch over the same `SiteRegistry`; it is expressed against the
> server-agnostic `dreggnet-webapp` surface because the httpe net stack does not
> currently build on macOS (a pre-existing `nodeapi`/`IPV6_DROP_MEMBERSHIP` break,
> unrelated to this work). On Linux the gateway fronts this identical surface.

### ④ The real Cap'n Proto `.spk` wire — status
The `.spk` container is real today: the canonical 8-byte magic (`8fc6cdef451aea96`,
pinned + verified against upstream `package.capnp`), real xz decompression (bomb-
bounded), a real Ed25519 signature over the archive bytes, and the App ID = the
signing key. The inner archive uses a documented length-prefixed projection of the
real `capnp Signature ++ capnp Archive` stream (the field shapes mirror the schema
1:1). Swapping that single inner codec for the real capnp wire is **gated on a real
catalog `.spk` to differential-test against** — and that artifact
(`node-b:~/dregg-share/sample.spk`) was not reachable from the build host, so the swap
is the one named seam left open here. The differential harness is in place:
`tests/real_spk_fixture.rs` runs the moment a real `sample.spk` is dropped in
`fixtures/`, verifying the real container header and emitting the codec-swap signal;
the suite stays green until it lands. The mechanical swap is: vendor `package.capnp`
+ the `capnp` crate, decode the real `Signature`/`Archive` messages, keep everything
above it (magic, xz, signature, App ID, file lookup, grain launch) unchanged.

## The end-to-end proof (runs locally)

`tests/devnet_real_grain.rs` drives the whole welded path with no in-process stubs
for the load-bearing parts:

1. a real signed `.spk` is parsed + Ed25519-verified (App ID = the signing key),
   manifest decoded, grain spec derived (`Caged`);
2. the grain is a dregg cell with a funded lifecycle (create → wake → sleep/
   checkpoint → wake), `/var` a committed umem heap;
3. its powerbox cap is a real `dreggnet-webauth` `dga1_` credential, host-rooted,
   sealed to the holder;
4. each request is served through the real `dreggnet-webapp` surface
   (`<name>.example.com` routing, `X-Sandstorm-Permissions` from the cap);
5. the handler runs on the real `dreggnet-exec` tier (`CapTier::Caged`, real
   `python3`; enforcement surfaced);
6. the served snapshot is published + re-witnessed through the real cap-gated publish
   turn.

It proves: an editor's write is served and persists in the cell umem across a
sleep/wake checkpoint; a viewer (a real attenuated `view`-only `dga1_` cap) reads it
back and is refused a write (403); a forged cap (not host-rooted) is refused (403).
`cargo test -p sandstorm-bridge` is green (83 tests; the real-tier tests skip cleanly
where `python3` is absent).

## Honest remaining for devnet

- **Live grain-serving on an operator's instance** — gated on the overlay-expose lane
  (the L2 inbound-through-the-bridge expose + the Caddy/cert path). REVIEWED-GO. The
  code path is the same `SiteRegistry` serving proven here; what is missing is the
  live overlay + a real Sandstorm instance to serve against.
- **Executing an untrusted downloaded `.spk` on the live edge tier** — REVIEWED-GO.
  The representative handler runs through the real tier today; running arbitrary
  third-party `.spk` chroot code is the sandbox-escape surface and belongs in the
  Firecracker microVM (where KVM) + the SBX deny-default, with an operator's live Sandstorm
  as the behavioral oracle.
- **The real capnp `Archive`-wire swap (④)** — gated on `node-b:~/dregg-share/sample.spk`
  (unreachable from the build host). The differential harness auto-runs when it lands.
- **The differential test against real `WebSession` traffic** — confirm the
  `X-Sandstorm-*` header bytes (already `encodeUriComponent`-faithful) match a real
  `sandstorm-http-bridge` over an operator's instance.
- **The in-circuit witness** — making a light client (not just a re-executing
  validator) witness the powerbox delegation + the served bytes is the substrate
  swarm's lane (the breadstuffs authority/circuit core), not this weld.

The dividing line is the project standard: the code + verified local proof is
safe-autonomous (done); executing untrusted catalog code and operated public reality
are reviewed-go.

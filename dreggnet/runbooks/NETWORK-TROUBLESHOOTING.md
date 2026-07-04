# NETWORK-TROUBLESHOOTING — the mesh + gossip diagnostics

When nodes can't reach each other, the cause is almost always one of five things:
the overlay isn't up, the node bound the wrong interface, gossip is mapped tcp
instead of udp, there's no bootstrap seed, or the ACL blocks the port. This runbook
is the layered diagnostic — overlay (headscale) → bind → gossip ports →
reachability → ACL — grounded in the real mesh gotchas we hit (the bind scoping,
the self-mesh fix, the `:8022` ACL scrape).

The two transport layers, kept straight:

```
  overlay layer   headscale / WireGuard   100.64.0.0/10 — the private mesh fabric
                                          (MESH.md: control server, DERP, authkeys)
  gossip layer    blocklace QUIC          9420/udp — block + finalization-vote dissemination
                                          (rides ON the overlay, between overlay IPs)
```

A failure at the overlay layer breaks *everything*; a failure at the gossip layer
breaks consensus while ssh/HTTP over the overlay still work. Diagnose top-down.

---

## 1. Is the overlay up? (headscale)

```sh
# the control plane is alive:
curl -s https://headscale.dreggnet.example.com/health        # {"status":"pass"}

# who is on the mesh + their overlay addresses (from the edge):
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>
cd /opt/dreggnet
sudo docker compose exec headscale headscale nodes list          # online? correct addr/tag?
sudo tailscale status                                            # the edge's own peer view

# a direct NAT-traversed path (DERP fallback) between two boxes:
sudo tailscale ping 100.64.0.2          # edge → node-a
```

**The overlay gotchas (MESH.md):**

- **One control server per box.** `tailscaled` carries exactly one — joining
  headscale **displaces** any public Tailscale tailnet on that box (this bit
  node-a). Anything that relied on the public tailnet must move to the overlay.
- **Re-pointing an enrolled box** at headscale needs
  `tailscale up … --force-reauth`.
- **Remote joins wait on DNS** — they hit the public HTTPS endpoint, which needs the
  `headscale.dreggnet.example.com` A-record live + the LE cert issued
  (`DEPLOY.md`). DERP between remote nodes needs the region HostName to resolve too;
  until then traffic relays through the edge.

If `tailscale ping` fails, you have an overlay problem — stop here and fix the mesh
(MESH.md) before looking at gossip.

---

## 2. The bind — overlay IP, not loopback or `0.0.0.0` (MESH-2 scoping)

**The single most common gossip-won't-form cause.** A node must bind its gossip
listener to its **overlay IP** (`100.64.0.x`), not `127.0.0.1` and not `0.0.0.0`.
Two reasons:

1. **`0.0.0.0` silently disables self-advertisement.** The self-forming mesh
   (`node/src/blocklace_sync.rs`) only advertises a node's endpoint if it has a
   *routable* address; a non-routable bind (`0.0.0.0`) yields `None` and
   self-advertisement stays **off** — peers never learn to dial it back, so the mesh
   doesn't self-form. The confirming log line is **absent**:

   ```sh
   docker compose logs dregg-node | grep -i "self-advertisement enabled"
   #   present  → self-forming mesh is active (good)
   #   ABSENT   → bound non-routable; peers can't learn to reach this node
   ```

2. **Loopback is unreachable from peers** — obviously.

**Fix:** bind to the overlay IP. With `network_mode: host` (node-a / homelab) the
node binds the host's overlay interface directly; on a docker bridge (the edge) the
published port maps it. Set `--bind <overlay-ip>` explicitly when in doubt.

> This is the **MESH-2 scoping** rule: scope listeners to the overlay interface, not
> the wildcard. It also keeps the node off any public interface the box might have.

---

## 3. The gossip ports — `9420/udp`, and `9421` for a second instance

- **Gossip is `9420/udp`** (QUIC/quinn) — **UDP, not TCP.** A **tcp-only** port
  mapping **silently fails to peer** (`peer_count` stays 0, no error). On a docker
  bridge publish **`"9420:9420/udp"`**; with host networking it binds the interface
  directly (`NODE-OPS.md` §ports). The classic silent killer.

- **The node API is `:8420/tcp`** — `/status`, `/health`, `/api/cell/{id}`,
  faucet, turn submit. (Don't confuse the two; tcp/8420 working while udp/9420
  doesn't is exactly the "HTTP fine, consensus broken" signature.)

### Two instances on one box (the `node-a-rust` pattern)

Running a second node on the same host (e.g. a rust-only shadow alongside the
lean-shadowed one — `COMMITTEE-CHANGE.md`) needs **distinct ports** for the second
instance so they don't collide:

| instance | gossip | API |
|---|---|---|
| first (e.g. node-a) | `9420/udp` | `8420/tcp` |
| second (e.g. node-a-rust) | **`9421/udp`** | `8421/tcp` |

```sh
# second instance: distinct gossip + API ports, still bound to the overlay IP:
dregg-node run --data-dir /data2 --bind 100.64.0.2 --port 8421 --gossip-port 9421 \
  --key-file node2.key --federation-mode full --federation-peers 100.64.0.1:9420
```

Both bind the same overlay IP but different ports; peers reach the second at
`100.64.0.2:9421`. Make sure the ACL permits the extra gossip port if it's
restricted (§5).

---

## 4. Reachability over the overlay

```sh
# overlay path itself (layer 1) — covered above:
sudo tailscale ping 100.64.0.2

# the node API over the overlay (tcp/8420) — should always answer if the node is up:
curl -s http://100.64.0.2:8420/status | jq '{federation_mode,peer_count,dag_height}'

# gossip udp/9420 — nc -u is a COARSE probe (no QUIC handshake, so "open" is weak),
# but a hard refusal/timeout here means the port or ACL is wrong:
nc -uvz 100.64.0.2 9420

# the populated native peer gauge (the closest thing to a peer count metric):
curl -s http://100.64.0.2:8420/metrics | grep dregg_federation_peers_connected
```

> **No `dregg-node peers` CLI** (honest TODO). There is no command that dumps the
> peer table; read `peer_count` from `/status` and
> `dregg_federation_peers_connected` from `/metrics`. Per-peer dial/resolve detail
> only lives in the node logs (`grep -iE "peer|gossip|resolve|bootstrap"`).

### The bootstrap seed + the self-mesh fix

The mesh forms from a **single seed**: a node booted with one
`--federation-peers <peer>:9420` signs + broadcasts its own endpoint; peers record
the authenticated `identity → addr` binding and re-share it via gossip-of-peers, so
the whole committee learns every member's endpoint from one bootstrap. That is the
**self-forming mesh** (`node/src/blocklace_sync.rs`,
`"gossip self-advertisement enabled"`).

- **Before the self-mesh fix**, a node only formed links on **outbound dials** — no
  `--federation-peers` and no inbound dial → it sat alone even on a healthy overlay.
- **After it**, `--federation-peers` becomes an *optional override*, but it is still
  the **recommended explicit bootstrap** (it makes the seed deterministic). Always
  give a new/recovering node one live peer to dial.
- **Hostnames resolve at dial time** — a peer spec may be `host:port` (a genesis-
  emitted overlay hostname like `edge:9420`), not just `ip:port`. An **unresolvable**
  peer is logged **LOUDLY** (an `error`), never silently dropped — grep for it:

  ```sh
  docker compose logs dregg-node | grep -iE "resolve|unresolvable|bootstrap|peer"
  ```

(Full mesh-won't-form triage tree: `INCIDENT-RESPONSE.md` §2.)

---

## 5. The ACL — what each role may reach (and the `:8022` lesson)

The headscale ACL (`deploy/staging/headscale/acls.hujson`) scopes who reaches what.
If a port is reachable on the overlay but a *specific source* can't hit it, the ACL
is the suspect.

The shape (`MESH.md`):

- **ember / devices** → everything (the operator plane).
- **`tag:edge` → `tag:compute`** on `22, 8021, 8420, 9420` (the dispatch path:
  ssh, the compute `/fulfill`, the node API, gossip).
- **`tag:compute` → `tag:edge`** on `22, 5432, 8080, 8420` (postgres + the control
  surface + the node API back).

### The `:8022` thermal-scrape lesson

When the observability stack on the edge needed to scrape node-a's thermal
exporter, the existing ACL didn't permit that port — so the scrape silently failed
until the ACL was widened. The fix landed as
`feat(mesh): allow edge->node-a :8022 (thermal exporter) in the overlay ACL`
(DreggNet commit `704c0d5`). **The lesson: a new cross-box port (a new exporter, a
second node instance's `9421`, a new service) needs an explicit ACL grant** — the
mesh is deny-by-default between tags. When you add a port, add the ACL rule in the
same breath, then reload headscale.

```sh
# after editing acls.hujson, headscale picks up the policy (reload / restart):
sudo docker compose restart headscale     # or the policy-reload path per headscale version
```

> **Don't over-widen.** Grant the *specific* port from the *specific* tag, not a
> blanket open — the tag-scoped ACL is a real security boundary (the red-team note
> "the tailnet ACL shape holds", `docs/RED-TEAM-FINDINGS.md`).

---

## The five-question checklist

When gossip won't form, walk these in order — most failures are #1-3:

1. **Overlay up?** `tailscale ping <peer>` works? (§1) — if no, fix the mesh first.
2. **Bound right?** `"self-advertisement enabled"` in the logs? Bound to the overlay
   IP, not `0.0.0.0`/loopback? (§2)
3. **UDP?** Gossip published as `9420/udp` (not tcp)? Second instance on `9421`? (§3)
4. **Seeded?** A live `--federation-peers` bootstrap, resolvable (no LOUD resolve
   error)? (§4)
5. **ACL?** The source tag permitted on the gossip port? (§5)

## See also

- MESH.md — headscale: authkeys, the overlay map, the one-control-server gotcha.
- INCIDENT-RESPONSE.md §2 — the "peer won't mesh / peer_count 0" triage tree.
- NODE-OPS.md — the `9420/udp` gotcha, the compose units, bind modes.
- FEDERATION.md — what the mesh carries (blocks + finalization votes), the cross-
  node finality verify.
- COMMITTEE-CHANGE.md — the two-instances-one-box case + bootstrap on a re-roll.
- DEPLOY.md — the DNS records remote joins wait on, the edge security group ports.

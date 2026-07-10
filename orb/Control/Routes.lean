import Control
import Control.Distribute
/-!
# Control.Routes — subnet-route advertisement and approval

A **subnet router** is a mesh node that offers connectivity to IP prefixes
*beyond its own addresses* — a whole LAN behind it, say. In the public Tailscale
model this is `--advertise-routes` on the client (`tailcfg` carries the extra
prefixes in the node's `allowedIPs`) and route *approval* on the coordination
server (headscale's `nodes approve-routes` / the admin's route-approval step):
the server distributes a subnet route to peers **only after an operator approves
it**. An unapproved advertised route is never handed out, so cryptokey routing
never carries traffic toward the router for it.

This module models the two operations and ties them to the already-verified
netmap→WireGuard seam in `Control.Distribute`:

* `advertisedRoutes` — the subnet routes a node *offers* (its `allowedIPs`
  minus its own `addresses`): the prefixes an operator would see pending
  approval.
* `approveRoutes` — the node as *distributed* after approval: its own addresses
  (always self-routable) plus exactly the advertised routes the operator
  approved. This is the `Node` the netmap carries onward to `Node.toWgPeer`.

The headline (`route_needs_approval`) closes the loop with cryptokey routing:
after approval, WireGuard admits a destination toward the node only via one of
its own addresses or an operator-approved subnet route — never via an
advertised-but-unapproved one.
-/

namespace Control.Routes

open Control

/-- The **subnet routes** a node advertises: the entries of its `allowedIPs` that
are not among its own `addresses`. These are the prefixes reachable *through*
the node (a LAN behind a subnet router), as opposed to the node itself — exactly
the set an operator reviews for approval. -/
def advertisedRoutes (n : Node) : List Prefix :=
  n.allowedIPs.filter (fun p => ! n.addresses.contains p)

/-- The node **as distributed after route approval**. Its own `addresses` are
always retained (self-routing is never subject to approval); of the advertised
subnet routes, only those in `approved` are kept. This is the `Node` the
coordination server folds into peers' netmaps, and thence into WireGuard via
`Node.toWgPeer`. -/
def approveRoutes (approved : List Prefix) (n : Node) : Node :=
  { n with allowedIPs := n.addresses ++ (advertisedRoutes n).filter (fun p => approved.contains p) }

/-- **Self-routing survives approval.** Every one of the node's own addresses is
still in the distributed `allowedIPs` — route approval can only ever remove
advertised subnet routes, never the node's own reachability. -/
theorem own_addresses_kept (approved : List Prefix) (n : Node) :
    ∀ a ∈ n.addresses, a ∈ (approveRoutes approved n).allowedIPs := by
  intro a ha
  simp only [approveRoutes]
  exact List.mem_append.mpr (Or.inl ha)

/-- **Nothing enters the distributed set but own addresses and approved routes.**
Every prefix in the post-approval `allowedIPs` is either one of the node's own
addresses or an advertised subnet route the operator approved. No unapproved
advertised route is ever distributed. -/
theorem approved_or_own (approved : List Prefix) (n : Node) :
    ∀ p ∈ (approveRoutes approved n).allowedIPs,
      p ∈ n.addresses ∨ (p ∈ advertisedRoutes n ∧ approved.contains p = true) := by
  intro p hp
  simp only [approveRoutes] at hp
  rcases List.mem_append.mp hp with hown | hfilt
  · exact Or.inl hown
  · rw [List.mem_filter] at hfilt
    exact Or.inr hfilt

/-- **An unapproved advertised route is dropped.** A subnet route the node
advertises but the operator did not approve (and which is not one of the node's
own addresses) is absent from the distributed `allowedIPs` — hence unroutable
toward the node. -/
theorem unapproved_route_dropped (approved : List Prefix) (n : Node) (r : Prefix)
    (_hadv : r ∈ advertisedRoutes n) (hunapp : approved.contains r = false)
    (hown : r ∉ n.addresses) :
    r ∉ (approveRoutes approved n).allowedIPs := by
  intro hmem
  rcases approved_or_own approved n r hmem with h | ⟨_, happ⟩
  · exact hown h
  · rw [happ] at hunapp; exact Bool.noConfusion hunapp

/-- **Cryptokey routing admits a destination only via an own address or an
approved route** — the composition with the verified netmap→WireGuard seam.

Take the node as distributed after approval, `n' := approveRoutes approved n`. If
WireGuard cryptokey routing over `n'`'s translated allowed set admits `ip` (best
prefix length `k`), then there is a prefix in `n'`'s distributed `allowedIPs`
that matches `ip` — and by `approved_or_own` that prefix is either one of the
node's own addresses or an operator-approved advertised route. So after approval,
WireGuard carries traffic toward the node only for self-routing or approved
subnet routes; an unapproved advertised route can never be the admitting
prefix. -/
theorem route_needs_approval (approved : List Prefix) (n : Node) (ip : Bytes) (k : Nat)
    (h : Wireguard.Peer.bestPlen (Node.toWgPeer (approveRoutes approved n)).allowed ip = some k) :
    ∃ p ∈ (approveRoutes approved n).allowedIPs,
      p.matches ip = true ∧
        (p ∈ n.addresses ∨ (p ∈ advertisedRoutes n ∧ approved.contains p = true)) := by
  obtain ⟨p, hpmem, hpmatch, _⟩ :=
    Control.Distribute.wg_route_needs_allowed (approveRoutes approved n) ip k h
  exact ⟨p, hpmem, hpmatch, approved_or_own approved n p hpmem⟩

end Control.Routes

#print axioms Control.Routes.own_addresses_kept
#print axioms Control.Routes.approved_or_own
#print axioms Control.Routes.unapproved_route_dropped
#print axioms Control.Routes.route_needs_approval

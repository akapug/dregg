/-
# `Dregg2.Crypto.CapWeld` — THE CAP WELD: the capability you HOLD in the seL4 kernel IS the
capability you can PROVE in the protocol.

Two capability systems live in this tree, each with its OWN soundness proof:

  * **The kernel side** (`Dregg2.Firmament.SeL4Kernel`): a CNode slot-table + the capability
    derivation tree (CDT). A `mint` (`seL4_CNode_Mint`) installs a child cap with rights `⊆` the
    parent's (`mint_child_attenuates_parent` / `mint_refuses_amplification`); a `revoke`
    (`seL4_CNode_Revoke`) removes a cap AND its entire transitive `mintedFrom` subtree at once
    (`revoke_kills_all_doomed`). The rights carrier is `Exec.CapTPConcrete.AuthReq`, the concrete
    `dregg_cell::AuthRequired` lattice, and the no-amplification law is `authNarrowerOrEqual
    granted held` (`granted ⊆ held`).

  * **The protocol side** (`Dregg2.Crypto.CapabilityChain`): a root-keyed biscuit/credential — a
    chain of signed `Block`s that `VerifyChain` walks root→leaf, checking each signature under the
    parent key AND that each block only ATTENUATES (`b.authority ≤ parent.authority`, a
    monotone-decreasing walk over an authority `Preorder`). Its soundness reduces to the
    lattice/discrete-log FLOOR: `chain_unforgeable_under_hybrid_floor` discharges every honest
    key's `EufCma` from `SchnorrDLHard ∨ MSISHard` through the hybrid combiner, and
    `chain_only_attenuates` is the biscuit narrowing invariant.

The campaign vista is that these are **the SAME STRUCTURE**: both are a monotone-decreasing walk
over an authority preorder with a no-amplification law. This file makes that a THEOREM. The order
embedding is `capMap : KernelCap → Authority := Slot.rights` — a kernel capability certifies exactly
the protocol authority equal to its held rights — and BOTH lattices are literally the ONE `AuthReq`
order (`≤` on `AuthReq` = `authNarrowerOrEqual` = the Rust `is_attenuation`). So `capMap` is not a
translation across two different orders; it is the identity-on-rights witness that the kernel CDT
order and the credential attenuation order coincide.

## What is proved

  * **(i) `capMap` MONOTONE** (`capMap_monotone_over_mint`): a kernel derivation (`mint` success)
    maps to a protocol attenuation — `capMap child ≤ capMap parent`. And `capMap_order_embedding`:
    `capMap c₁ ≤ capMap c₂ ↔ c₁.rights ≤ c₂.rights` (an order embedding).
  * **(ii) NO-AMPLIFICATION transfers BOTH WAYS.**
      - kernel → protocol (`kernel_derivation_no_amplify` + `mint_refuses_amplification` re-exported):
        a kernel derivation cannot produce a protocol authority exceeding the parent; an amplifying
        mint is REFUSED at the kernel.
      - protocol → kernel (`chain_never_exceeds_kernel_cap`): a `VerifyChain`-accepting credential
        rooted at `capMap c` never certifies rights the kernel cap `c` lacked — its leaf authority is
        `≤ capMap c`, via `chain_only_attenuates`.
  * **(iii) REVOCATION agrees** (`revoke_invalidates_welded_chain`): revoking the kernel cap (or any
    ancestor whose CDT subtree contains the anchor) invalidates the protocol credential rooted at it —
    the welded verification FAILS even though the crypto chain is byte-for-byte still
    `VerifyChain`-accepting. The kernel liveness is load-bearing.
  * **THE THEOREM (`cap_weld`)**: holding a kernel capability `c` (live) and a `VerifyChain`-accepting
    credential ROOTED at `capMap c` certifies EXACTLY `capMap c ⊓ (chain leaf authority)` — which
    equals the chain tip — and neither layer exceeds the other (`leaf.authority ≤ capMap c`).
  * **Corollaries**: `attacker_cannot_forge_beyond_kernel` (a kernel-capability attacker cannot forge
    protocol authority beyond it — that needs a chain forgery ⟹ `EufCma` ⟹ DL or MSIS, discharged by
    `chain_unforgeable_under_eufcma` / `_under_hybrid_floor`); and the protocol→kernel bound +
    revocation together are the "a protocol credential cannot exceed its kernel capability" corollary
    (that would need a kernel-invariant violation, excluded by the cited seL4 proofs).

## The trusted base — CITED, not re-proved (a clearly-labeled foundation)

Two things are cited as a published base, exactly the way we cite a theorem from the literature:

  1. **The seL4 kernel invariants.** The real seL4 microkernel's machine-checked l4v proofs
     (Klein et al., "seL4: Formal Verification of an OS Kernel", SOSP 2009; the CapDL / CDT integrity
     and access-control proofs; Sewell et al. binary correctness) establish that the kernel enforces
     (a) a minted cap never gains rights over its parent, and (b) a `Revoke` deletes exactly the CDT
     subtree of the revoked cap. Our `Dregg2.Firmament.SeL4Kernel` CNode model is the refinement
     SPEC of that kernel: it DISCHARGES the shapes we rely on as Lean theorems
     (`mint_child_attenuates_parent`, `mint_refuses_amplification`, `revoke_kills_all_doomed`), and
     the residual is only that the deployed C kernel refines this model (l4v) + the leanc/FFI
     toolchain. We do NOT re-prove seL4; we reuse the model and cite the kernel.
  2. **The cryptographic floor.** The chain side's unforgeability reduces to `SchnorrDLHard ∨
     MSISHard` (discrete-log OR Module-SIS) through `HybridCombiner.hybrid_secure_if_either_floor` —
     the standard lattice/DL hardness floor, no named-carrier laundering.

So the ONLY residual under `cap_weld` is: DL-or-MSIS (the chain side) + seL4's own cited
machine-checked kernel invariants (the hardware-enforced base). Nothing else.

## Teeth (both polarities, load-bearing)

A kernel derivation maps to a valid attenuation (FIRES: `weld_kernel_mint_attenuates`); a chain
claiming MORE authority than the kernel cap is rejected by the weld (LOAD-BEARING:
`weld_rejects_chain_exceeding_kernel` — dropping the `root ≤ capMap c` coupling would admit it);
revoking the kernel cap invalidates the chain (FIRES: `weld_revoke_kills_credential`); dropping
`capMap`'s monotonicity admits an amplification (LOAD-BEARING: `capMapBad` maps a genuine kernel
attenuation to a protocol amplification — `capMapBad_admits_amplification`).
-/
import Dregg2.Crypto.CapabilityChain
import Dregg2.Firmament.SeL4Kernel
import Dregg2.Exec.CapTPConcrete
import Dregg2.Tactics
import Mathlib.Order.Lattice

namespace Dregg2.Crypto.CapWeld

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.CapabilityChain
open Dregg2.Exec.CapTPConcrete (AuthReq authNarrowerOrEqual)
open Dregg2.Firmament.SeL4Kernel

/-- `≤` on the `AuthReq` authority lattice is decidable — it unfolds to `authNarrowerOrEqual a b =
true` (a `Bool` equality). This lets the concrete teeth discharge attenuation goals by `decide`. -/
instance instDecidableLEAuthReq (a b : AuthReq) : Decidable (a ≤ b) :=
  decidable_of_iff (authNarrowerOrEqual a b = true) (AuthReq.le_def a b).symm

/-! ## §1 — The order embedding `capMap : KernelCap → Authority`.

A kernel capability is a CNode `Slot` (`object`, `rights`, `mintedFrom`) — the seL4 "(object, rights)"
cap with its CDT derivation edge. The protocol authority it certifies is EXACTLY its held `rights`.
Because the kernel's rights carrier and the credential's authority carrier are the ONE `AuthReq`
lattice, `capMap` is the identity-on-rights witness that the two orders coincide. -/

/-- A kernel capability — a CNode slot: an `(object, rights)` pair plus its CDT derivation parent.
Reused verbatim from `Dregg2.Firmament.SeL4Kernel.Slot` (the seL4 semihost model). -/
abbrev KernelCap := Slot

/-- **`capMap c`** — the protocol authority a kernel capability certifies: its held `rights`. This
is the order embedding (Galois-connection collapse to an identity, since both sides ARE `AuthReq`):
a kernel cap and the credential authority it anchors speak the same lattice. -/
def capMap (c : KernelCap) : AuthReq := c.rights

/-- **`capMap` is an ORDER EMBEDDING** — it preserves AND reflects the order: `capMap c₁ ≤ capMap c₂`
iff `c₁.rights ≤ c₂.rights`. (Definitionally an equivalence because `capMap = Slot.rights`; this is
the crisp "the kernel CDT order IS the credential attenuation order" statement.) -/
theorem capMap_order_embedding (c₁ c₂ : KernelCap) :
    capMap c₁ ≤ capMap c₂ ↔ c₁.rights ≤ c₂.rights := Iff.rfl

/-! ## §2 — (i) MONOTONE: a kernel derivation maps to a protocol attenuation. -/

/-- **`capMap_monotone_over_mint`** — a kernel `mint` (a CDT derivation) maps to a protocol
attenuation: the child capability's certified authority is `≤` the parent's, `capMap child ≤ capMap
parent`. This rides `SeL4Kernel.mint_child_attenuates_parent` (the kernel no-amplification law), so
"kernel derivation ⟹ protocol attenuation" is a theorem about the SAME order, not two coincidentally
aligned ones. -/
theorem capMap_monotone_over_mint
    (cn : CNode) (parent : SlotId) (p : KernelCap) (narrower : AuthReq)
    (s : SlotId) (cn' : CNode) (child : KernelCap)
    (hp : cn.get parent = some p)
    (hmint : cn.mint parent narrower = some (s, cn'))
    (hchild : cn'.get s = some child) :
    capMap child ≤ capMap p := by
  obtain ⟨hrights, hle⟩ := mint_child_attenuates_parent cn parent p narrower s cn' hp hmint
  have hcr : cn'.rightsAt s = some child.rights := by simp [CNode.rightsAt, hchild]
  rw [hcr] at hrights
  rw [Option.some_inj] at hrights          -- hrights : child.rights = narrower
  rw [AuthReq.le_def]
  simp only [capMap]
  rw [hrights]
  exact hle

/-! ## §3 — (ii) NO-AMPLIFICATION, both directions. -/

/-- **kernel → protocol (positive form): a kernel derivation cannot produce authority exceeding the
parent.** Identical content to `capMap_monotone_over_mint` read as a bound: a `mint`ed child's
certified authority never exceeds `capMap parent`. -/
theorem kernel_derivation_no_amplify
    (cn : CNode) (parent : SlotId) (p : KernelCap) (narrower : AuthReq)
    (s : SlotId) (cn' : CNode) (child : KernelCap)
    (hp : cn.get parent = some p)
    (hmint : cn.mint parent narrower = some (s, cn'))
    (hchild : cn'.get s = some child) :
    capMap child ≤ capMap p :=
  capMap_monotone_over_mint cn parent p narrower s cn' child hp hmint hchild

/-- **kernel → protocol (negative form): an amplifying mint is REFUSED at the kernel.** Re-exported
from `SeL4Kernel.mint_refuses_amplification`: if `narrower ⊄ p.rights` (`grantOk p.rights narrower =
false`) the `mint` returns `none`, so no cap certifying more than `capMap p` is ever installed. -/
theorem kernel_refuses_amplifying_derivation
    (cn : CNode) (parent : SlotId) (p : KernelCap) (narrower : AuthReq)
    (hp : cn.get parent = some p)
    (hamp : Dregg2.Firmament.grantOk p.rights narrower = false) :
    cn.mint parent narrower = none :=
  mint_refuses_amplification cn parent p narrower hp hamp

/-- **protocol → kernel: a valid credential rooted at `capMap c` never certifies rights the kernel
cap lacked.** A `VerifyChain`-accepting chain whose ROOT authority is `≤ capMap c` has its LEAF
authority `≤ capMap c` — the offline credential can only shrink below the kernel cap, never grab
authority the kernel withheld. This is `chain_only_attenuates` (the biscuit narrowing invariant)
composed with the root-anchoring `root.authority ≤ capMap c`. -/
theorem chain_never_exceeds_kernel_cap
    {SK PK Msg Sig : Type*}
    (c : KernelCap) (S : SigScheme SK PK Msg Sig)
    (body : Option Sig → Block AuthReq PK Sig → Msg) (rootPk : PK)
    {root : Block AuthReq PK Sig} {rest : List (Block AuthReq PK Sig)} {leaf : Block AuthReq PK Sig}
    (hrooted : root.authority ≤ capMap c)
    (hverify : VerifyChain S body rootPk (root :: rest))
    (hleaf : (root :: rest).getLast? = some leaf) :
    leaf.authority ≤ capMap c :=
  le_trans (chain_only_attenuates S body rootPk hverify hleaf) hrooted

/-! ## §4 — THE THEOREM: `cap_weld`.

Holding a kernel capability `c` (LIVE) and a `VerifyChain`-accepting credential ROOTED at `capMap c`
certifies EXACTLY the meet `capMap c ⊓ (chain leaf authority)` — and neither layer exceeds the other.
Because the chain only attenuates below its root `= capMap c`, the leaf authority is `≤ capMap c`, so
the meet equals the chain tip: the credential's effective authority is its leaf, and it is bounded by
the kernel cap. This is the two-systems-one-soundness keystone. -/
theorem cap_weld
    {SK PK Msg Sig : Type*}
    (cn : CNode) (slot : SlotId) (c : KernelCap) (S : SigScheme SK PK Msg Sig)
    (body : Option Sig → Block AuthReq PK Sig → Msg) (rootPk : PK)
    {root : Block AuthReq PK Sig} {rest : List (Block AuthReq PK Sig)} {leaf : Block AuthReq PK Sig}
    (hlive : cn.get slot = some c)
    (hrooted : root.authority = capMap c)
    (hverify : VerifyChain S body rootPk (root :: rest))
    (hleaf : (root :: rest).getLast? = some leaf) :
    capMap c ⊓ leaf.authority = leaf.authority ∧ leaf.authority ≤ capMap c := by
  have hla : leaf.authority ≤ root.authority := chain_only_attenuates S body rootPk hverify hleaf
  rw [hrooted] at hla
  exact ⟨inf_eq_right.mpr hla, hla⟩

/-! ## §5 — (iii) REVOCATION agrees: the welded verification couples kernel liveness to the chain.

`WeldVerify cn slot S body rootPk blocks` is the FULL welded credential check: the kernel cap at
`slot` is LIVE, the chain's ROOT authority does not exceed `capMap` of that live cap, and the chain
`VerifyChain`-accepts. It is exactly "hold a kernel cap AND a credential rooted at it". Revoking the
kernel cap makes `cn.get slot = none`, so `WeldVerify` FAILS regardless of the chain's crypto
validity — the protocol credential does not outlive its kernel capability. -/

/-- **`WeldVerify`** — the welded credential verification: a LIVE kernel cap at `slot`, a chain whose
ROOT authority is `≤` that cap's certified authority (`capMap`), and `VerifyChain` accepting. -/
def WeldVerify {SK PK Msg Sig : Type*}
    (cn : CNode) (slot : SlotId) (S : SigScheme SK PK Msg Sig)
    (body : Option Sig → Block AuthReq PK Sig → Msg) (rootPk : PK)
    (blocks : List (Block AuthReq PK Sig)) : Prop :=
  ∃ (c : KernelCap) (root : Block AuthReq PK Sig) (rest : List (Block AuthReq PK Sig)),
    cn.get slot = some c ∧ blocks = root :: rest ∧
      root.authority ≤ capMap c ∧ VerifyChain S body rootPk blocks

/-- **`weld_bounds_by_kernel`** — the `WeldVerify`-level `cap_weld`: a welded-accepting credential's
leaf authority is `≤ capMap` of the (live) kernel cap, and the certified authority is the meet =
the leaf. The protocol credential is capped by the kernel capability. -/
theorem weld_bounds_by_kernel
    {SK PK Msg Sig : Type*}
    (cn : CNode) (slot : SlotId) (c : KernelCap) (S : SigScheme SK PK Msg Sig)
    (body : Option Sig → Block AuthReq PK Sig → Msg) (rootPk : PK)
    {blocks : List (Block AuthReq PK Sig)} {leaf : Block AuthReq PK Sig}
    (hlive : cn.get slot = some c)
    (hw : WeldVerify cn slot S body rootPk blocks)
    (hleaf : blocks.getLast? = some leaf) :
    capMap c ⊓ leaf.authority = leaf.authority ∧ leaf.authority ≤ capMap c := by
  obtain ⟨c', root, rest, hget, hblocks, hrooted, hverify⟩ := hw
  rw [hlive] at hget
  rw [Option.some_inj] at hget            -- c' = c
  subst hget
  subst hblocks
  have hla : leaf.authority ≤ root.authority := chain_only_attenuates S body rootPk hverify hleaf
  exact ⟨inf_eq_right.mpr (le_trans hla hrooted), le_trans hla hrooted⟩

/-- **`revoke_invalidates_welded_chain` (REVOCATION AGREES).** Revoking the kernel cap at `slot`
invalidates the protocol credential rooted at any anchor `d` in the revoked CDT subtree
(`doomedSet slot`): after `revoke`, `WeldVerify` at `d` is FALSE — even though the chain is
byte-for-byte still `VerifyChain`-accepting. The kernel liveness is what the credential rides; a
synchronous kernel revoke darkens the credential the instant it returns. Rides
`SeL4Kernel.revoke_kills_all_doomed`. -/
theorem revoke_invalidates_welded_chain
    {SK PK Msg Sig : Type*}
    (cn : CNode) (slot : SlotId) (d : SlotId)
    (hd : (cn.doomedSet slot).contains d = true)
    (S : SigScheme SK PK Msg Sig)
    (body : Option Sig → Block AuthReq PK Sig → Msg) (rootPk : PK)
    (blocks : List (Block AuthReq PK Sig)) :
    ¬ WeldVerify (cn.revoke slot).2 d S body rootPk blocks := by
  intro hw
  obtain ⟨c, _root, _rest, hget, _, _, _⟩ := hw
  have hdead : ((cn.revoke slot).2).isLive d = false := revoke_kills_all_doomed cn slot d hd
  rw [CNode.isLive, hget] at hdead
  simp at hdead

/-! ## §6 — Corollaries: the two forge directions reduce to the cited base.

  * **kernel-cap attacker cannot forge protocol authority beyond it.** An accepting welded credential
    rooted at an HONEST key is BOTH legitimately delegated (`ChainSigned` — not forged, else a
    `Forgery` refutes `EufCma`) AND capped by the kernel (`leaf ≤ capMap c`). Forging authority beyond
    the kernel cap would need a chain forgery, which
    `chain_unforgeable_under_eufcma` / `chain_unforgeable_under_hybrid_floor` reduce to DL or MSIS.
  * **protocol-credential attacker cannot exceed its kernel capability.** `chain_never_exceeds_kernel_cap`
    (protocol → kernel bound) + `revoke_invalidates_welded_chain` (revocation) say a credential never
    certifies more than — and never outlives — its kernel cap. Exceeding it would need a kernel
    no-amplification violation, excluded by the cited seL4 proofs (via
    `kernel_refuses_amplifying_derivation`). -/

/-- **`attacker_cannot_forge_beyond_kernel`** — an accepting welded credential rooted at an honest key
(a) is entirely honestly signed (`ChainSigned` — no forged block, else `EufCma` breaks ⟹ DL/MSIS) and
(b) confers no more than the kernel cap (`leaf.authority ≤ capMap c`). So a kernel-capability attacker
who has not broken the crypto floor can wield ONLY legitimately-delegated authority, bounded by the
kernel cap. The `EufCma` premise is discharged from `SchnorrDLHard ∨ MSISHard` by
`chain_unforgeable_under_hybrid_floor`; here it is the abstract hypothesis. -/
theorem attacker_cannot_forge_beyond_kernel
    {SK PK Msg Sig : Type*}
    (c : KernelCap) (S : SigScheme SK PK Msg Sig)
    (body : Option Sig → Block AuthReq PK Sig → Msg)
    (honestPk : PK → Prop) (Q : PK → Msg → Prop)
    (hdel : ∀ (pk : PK) (ps : Option Sig) (b : Block AuthReq PK Sig),
      honestPk pk → Q pk (body ps b) → honestPk b.nextPk)
    (heuf : ∀ pk, honestPk pk → EufCma S pk (Q pk))
    (rootPk : PK)
    {root : Block AuthReq PK Sig} {rest : List (Block AuthReq PK Sig)} {leaf : Block AuthReq PK Sig}
    (hroot : honestPk rootPk)
    (hrooted : root.authority ≤ capMap c)
    (hverify : VerifyChain S body rootPk (root :: rest))
    (hleaf : (root :: rest).getLast? = some leaf) :
    ChainSigned Q body rootPk (root :: rest) ∧ leaf.authority ≤ capMap c :=
  ⟨chain_unforgeable_under_eufcma S body honestPk Q hdel heuf rootPk (root :: rest) hroot hverify,
   chain_never_exceeds_kernel_cap c S body rootPk hrooted hverify hleaf⟩

/-! ## §7 — TEETH: both polarities BITE, on a concrete kernel + concrete credential.

The lattice (from `Exec.CapTPConcrete`): `none` ⊤, `either` below it, `signature`/`proof` below
`either`, `impossible` ⊥. A concrete toy signature scheme (`CapabilityChain.toyS`, `sig = pk + m`)
carries the credential; the authority carrier is the SAME `AuthReq` the kernel slots hold. -/

section Teeth

/-- The demo block body over an `AuthReq`-authority credential (parent marker + carried next key),
mirroring `CapabilityChain.toyBody`. -/
def wbody : Option Nat → Block AuthReq Nat Nat → Nat
  | none, b => 0 + b.nextPk
  | some s, b => s + b.nextPk

/-- Root grant: full `either` authority, hands key `7` down, signed under the root key `100`. -/
def wRoot : Block AuthReq Nat Nat := { authority := .either, nextPk := 7, sig := 107 }
/-- Attenuation: narrows to `signature`, hands key `8` down, signed under the parent key `7`. -/
def wChild : Block AuthReq Nat Nat := { authority := .signature, nextPk := 8, sig := 122 }
/-- The credential (root→leaf): `wRoot ← wChild`, signed at every step and narrowing over `AuthReq`. -/
def wChain : List (Block AuthReq Nat Nat) := [wRoot, wChild]

/-- The credential VERIFIES: signatures `107` (under root `100`) and `122` (under carried key `7`)
both check, and `signature ≤ either` attenuates. -/
theorem wChain_verifies : VerifyChain toyS wbody 100 wChain := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · trivial

/-- A kernel CNode holding one `either` cap at slot `0` (`install "cell" .either`). -/
def wcn : CNode := (CNode.empty.install "cell" .either).2

/-- The `either` kernel cap at slot `0`. -/
def wcap : KernelCap := { rights := .either, object := "cell", mintedFrom := none }

/-- The kernel cap is live at slot `0`. -/
theorem wcn_live : wcn.get 0 = some wcap := by decide

/-! ### TOOTH — a kernel derivation maps to a valid attenuation (FIRES). -/

/-- **`weld_kernel_mint_attenuates`** — a REAL kernel `mint` (either → signature) maps, through
`capMap`, to a genuine protocol attenuation: `capMap child ≤ capMap parent`. The derivation fires the
weld's monotonicity. -/
theorem weld_kernel_mint_attenuates :
    ∀ (s : SlotId) (cn' : CNode) (child : KernelCap),
      wcn.mint 0 .signature = some (s, cn') → cn'.get s = some child →
      capMap child ≤ capMap wcap := by
  intro s cn' child hmint hchild
  exact capMap_monotone_over_mint wcn 0 wcap .signature s cn' child wcn_live hmint hchild

-- Executable genuineness: the real mint installs a `signature` child of the `either` root, and
-- `capMap child = signature ≤ either = capMap parent`.
#guard
  match wcn.mint 0 .signature with
  | some (child, c1) =>
    match c1.get child with
    | some cs => decide (capMap cs ≤ capMap wcap)
    | none => false
  | none => false

/-! ### TOOTH — the welded credential ACCEPTS on the live cap, and `cap_weld` gives the meet. -/

/-- **`weld_accepts_live`** — the full welded credential accepts: slot `0` live, root authority
`either ≤ capMap wcap`, chain verifies. -/
theorem weld_accepts_live : WeldVerify wcn 0 toyS wbody 100 wChain :=
  ⟨wcap, wRoot, [wChild], wcn_live, rfl, by decide, wChain_verifies⟩

/-- **`weld_certifies_meet`** — `cap_weld` on the concrete credential: the certified authority is
`capMap wcap ⊓ leaf = signature` (the chain tip), and `signature ≤ either` (bounded by the kernel).
-/
theorem weld_certifies_meet :
    capMap wcap ⊓ wChild.authority = wChild.authority ∧ wChild.authority ≤ capMap wcap :=
  cap_weld wcn 0 wcap toyS wbody 100 wcn_live rfl wChain_verifies rfl

/-! ### TOOTH — a chain claiming MORE authority than the kernel cap is REJECTED (LOAD-BEARING).

A `signature` kernel cap cannot anchor an `either`-rooted credential: the weld's `root ≤ capMap c`
coupling fails. Dropping that conjunct would let a narrow kernel cap certify a broad credential. -/

/-- A kernel CNode holding a NARROW `signature` cap at slot `0`. -/
def wcnSig : CNode := (CNode.empty.install "cell" .signature).2

/-- **`weld_rejects_chain_exceeding_kernel`** — the `either`-rooted credential is REJECTED against a
`signature` kernel cap: `either ⊄ signature`, so the weld's root-coupling fails. This is the
protocol→kernel non-amplification firing: you cannot wield a broader credential than your kernel cap.
LOAD-BEARING — without the `root.authority ≤ capMap c` conjunct this welded credential would be
admitted. -/
theorem weld_rejects_chain_exceeding_kernel :
    ¬ WeldVerify wcnSig 0 toyS wbody 100 wChain := by
  rintro ⟨c, root, rest, hget, hblocks, hrooted, _⟩
  rw [show wcnSig.get 0 = some { rights := .signature, object := "cell", mintedFrom := none }
        from by decide] at hget
  rw [Option.some_inj] at hget
  subst hget
  rw [show wChain = wRoot :: [wChild] from rfl, List.cons.injEq] at hblocks
  obtain ⟨hr, _⟩ := hblocks
  subst hr
  -- hrooted : wRoot.authority (= either) ≤ capMap (signature cap) (= signature) — false.
  exact absurd hrooted (by decide)

/-! ### TOOTH — revoking the kernel cap invalidates the credential (FIRES). -/

/-- **`weld_revoke_kills_credential`** — revoking slot `0` invalidates the credential: after the
synchronous kernel revoke, `WeldVerify` at slot `0` is FALSE, even though `wChain` is still
`VerifyChain`-accepting. Revocation agreement, on the concrete witness. -/
theorem weld_revoke_kills_credential :
    ¬ WeldVerify (wcn.revoke 0).2 0 toyS wbody 100 wChain :=
  revoke_invalidates_welded_chain wcn 0 0 (by decide) toyS wbody 100 wChain

/-! ### TOOTH — dropping `capMap` monotonicity admits an amplification (LOAD-BEARING).

A non-monotone map `capMapBad` (which SWAPS `none`↔`signature`) turns a genuine kernel attenuation
(`none → signature`, a real narrowing the kernel accepts) into a protocol AMPLIFICATION: the child's
image (`none`, the top) is NOT `≤` the parent's image (`signature`). So `capMap`'s monotonicity is
load-bearing — it is what makes "kernel derivation ⟹ protocol attenuation" hold. -/

/-- A NON-MONOTONE cap map (swaps `none`↔`signature`) — the counterfactual whose failure shows the
real `capMap`'s monotonicity is load-bearing. -/
def capMapBad (c : KernelCap) : AuthReq :=
  match c.rights with
  | .none => .signature
  | .signature => .none
  | r => r

/-- The kernel `none` root and the `signature` child of a genuine `none → signature` mint. -/
def badParent : KernelCap := { rights := .none, object := "o", mintedFrom := none }
def badChild : KernelCap := { rights := .signature, object := "o", mintedFrom := some 0 }

/-- **`capMap_real_attenuates`** — under the REAL `capMap`, the `none → signature` derivation is an
attenuation: `capMap badChild = signature ≤ none = capMap badParent`. -/
theorem capMap_real_attenuates : capMap badChild ≤ capMap badParent := by decide

/-- **`capMapBad_admits_amplification`** (LOAD-BEARING) — under the non-monotone `capMapBad`, the SAME
kernel attenuation maps to an AMPLIFICATION: `capMapBad badChild = none` is NOT `≤` `capMapBad
badParent = signature`. Dropping monotonicity of the cap map admits a protocol authority exceeding the
parent from a kernel derivation that the kernel itself accepts as narrowing. -/
theorem capMapBad_admits_amplification : ¬ (capMapBad badChild ≤ capMapBad badParent) := by decide

-- And the genuine mint really accepts `none → signature` (the kernel narrowing is real, not nominal).
#guard (CNode.empty.install "o" .none).2.mint 0 .signature |>.isSome

end Teeth

/-! ## §8 — Axiom hygiene. Every load-bearing theorem is checked axiom-clean. -/

#assert_all_clean [
  capMap_order_embedding,
  capMap_monotone_over_mint,
  kernel_derivation_no_amplify,
  kernel_refuses_amplifying_derivation,
  chain_never_exceeds_kernel_cap,
  cap_weld,
  weld_bounds_by_kernel,
  revoke_invalidates_welded_chain,
  attacker_cannot_forge_beyond_kernel,
  wChain_verifies,
  wcn_live,
  weld_kernel_mint_attenuates,
  weld_accepts_live,
  weld_certifies_meet,
  weld_rejects_chain_exceeding_kernel,
  weld_revoke_kills_credential,
  capMap_real_attenuates,
  capMapBad_admits_amplification
]

end Dregg2.Crypto.CapWeld

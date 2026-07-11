/-
# Metatheory.Bridge.ProofOfHoldings — non-custodial proof-of-holdings ⟹ weight.

The dreggic alternative to lock-and-mirror for PARTICIPATION. To vote / to carry
governance weight, a holder must NEVER surrender custody: no lock, no vault, no
wrapped token. dregg is already a Solana light client, so it reads the holder's OWN
finalized SPL token account, decodes the balance, and PROVES "wallet W holds `amount`
of mint M at finalized slot S". The holder keeps custody; nothing moves; weight is
granted BY PROOF.

This file is the Lean soundness model for that guarantee, mirroring the Rust
`bridge/src/solana_holdings.rs` shapes (`ProvenHolding`, `is_consensus_proven`, the
`LockProofTrust` ConsensusVerified/StructureOnly dial) and COMPOSING with the
`InterchainAdapter` finality-as-hypothesis pattern (`Metatheory.Bridge`): a foreign
slot's finalization is an ASSUMED oracle (`HoldingsProof.finalized`), never a global
`axiom` and never a laundered `def FooHard`.

THE TOP THEOREM (`weight_backed_and_noncustodial`): a granted weight `w` for identity
`v` is BACKED by a consensus-proven holding of `≥ w` at a finalized slot AND the grant
moved NO custody — the on-chain state after the grant is definitionally the state
before it (`grantWeight` is a pure read of the proof). Weight is real AND custody is
preserved.

NON-VACUITY (load-bearing, the `interchain_gate_discriminates` analog): the gate
DISCRIMINATES on BOTH axes. Same finalized slot, same holder, same amount — a
consensus-proven holding grants weight, but the SAME holding on the `rpc`
(StructureOnly) tier grants NONE (the fail-closed tier discriminator). And a weight
STRICTLY ABOVE the proven amount is never grantable (the amount-bound discriminator).
The unfinalized-slot and empty-oracle rejections mirror the Nomad-law default.

Kernel-clean: `#assert_axioms` hard-gates every theorem.
-/
import Dregg2.Tactics

namespace Metatheory.Bridge.ProofOfHoldings

/-! ## §1 — The trust dial, identities, and the proven holding.

`TrustTier` mirrors the Rust `LockProofTrust`: `consensusProven` is a real
stake-weighted ≥2/3 supermajority over a finalized bank hash (the only trustless
state); `rpc` is a plain-RPC read (`StructureOnly`) that MUST NOT grant weight. -/

/-- **`TrustTier`** — how a holding observation is trusted. `consensusProven` mirrors
`LockProofTrust::ConsensusVerified` (trustless); `rpc` mirrors
`LockProofTrust::StructureOnly` (a plain-RPC echo — NOT proof). -/
inductive TrustTier
  | consensusProven
  | rpc
deriving DecidableEq, Repr

/-- A governance identity (a wallet pubkey, abstracted). -/
abbrev VoterId := Nat
/-- Governance weight, in atomic units of the held asset. -/
abbrev Weight := Nat
/-- A finalized-chain slot number. -/
abbrev Slot := Nat
/-- An on-chain account pubkey. -/
abbrev Account := Nat

/-- **`ProvenHolding`** — the Lean mirror of `bridge/src/solana_holdings.rs`'s
`ProvenHolding`: at finalized `slot`, the account controlled by `owner` held `amount`
of `mint`. NON-CUSTODIAL: this is a snapshot proven over the holder's OWN account —
nothing was moved into a vault. `trust` carries the tier (proof vs rpc). -/
structure ProvenHolding where
  /-- The wallet that controls the SPL token account (its own custody, not a vault). -/
  owner  : Account
  /-- The SPL mint proven held. -/
  mint   : Nat
  /-- The balance proven at `slot`, in atomic units. -/
  amount : Nat
  /-- The finalized slot the holding was proven at (the snapshot point). -/
  slot   : Slot
  /-- Trust tier; weight is granted ONLY for `consensusProven`. -/
  trust  : TrustTier
deriving Repr

/-- **`ProvenHolding.isConsensusProven`** — mirrors the Rust `is_consensus_proven`:
`true` iff backed by a real supermajority over a finalized bank hash. An `rpc`
(StructureOnly) holding returns `false`. -/
def ProvenHolding.isConsensusProven (h : ProvenHolding) : Bool :=
  match h.trust with
  | .consensusProven => true
  | .rpc             => false

/-! ## §2 — The finalization oracle (assumed, never an axiom) and the weight-grant predicate.

`HoldingsProof.finalized` is the assumed light-client finality witness, exactly the
`InterchainAdapter.foreignFinal` pattern: supplied as DATA (a field), so it is an
explicit hypothesis, never a global `axiom`. -/

/-- **`HoldingsProof`** — the finalization view a holding is proven against.
`finalized : Slot → Prop` is the assumed light-client oracle "this foreign slot is
final" (the `foreignFinal` analog). The empty/fail-closed default is
`finalized ≡ False`. -/
structure HoldingsProof where
  finalized : Slot → Prop

/-- **`grantsWeight o h v w`** — the fail-closed weight-grant predicate. A holding `h`
grants weight `w` to identity `v` (under finalization oracle `o`) iff:

  * `h.trust = consensusProven` — the proof tier (an `rpc`/StructureOnly holding
    grants NOTHING),
  * `o.finalized h.slot` — the holding's slot is finalized,
  * `h.owner = v` — the weight accrues to the holder identity,
  * `w ≤ h.amount` — weight NEVER exceeds the proven balance.

Weight is thus a pure function of a consensus proof — never of a committee/oracle
verdict, never of surrendered custody. -/
def grantsWeight (o : HoldingsProof) (h : ProvenHolding) (v : VoterId) (w : Weight) : Prop :=
  h.trust = TrustTier.consensusProven ∧ o.finalized h.slot ∧ h.owner = v ∧ w ≤ h.amount

/-! ## §3 — The NON-CUSTODIAL grant operation: a pure read that mutates no balance.

On-chain state is a per-account balance map. `grantWeight` reads the proof and returns
a weight assignment AND the state — UNCHANGED. Custody is preserved by construction:
the post-state is definitionally the pre-state. -/

/-- On-chain state: each account's balance. -/
abbrev ChainState := Account → Nat

/-- **`grantWeight h slotFinal pre`** — the deployed grant. It reads `h` and the light
client's decidable finality verdict `slotFinal` (is `h.slot` final?) and returns `(the
weight assignment, the on-chain state)`. The state component is `pre` UNCHANGED: the
grant is a pure read of the proof and moves no custody.

The gate is `isConsensusProven && slotFinal` — the deployed function ENFORCES both the
proof tier AND finalization, so it faithfully executes the `grantsWeight` predicate
rather than being weaker than it (an `rpc` holding OR an unfinalized slot yields
`none`). `slotFinal` is a `Bool` — the light client's decidable verdict for the
`finalized` oracle — keeping this computable (the `#guard`s below evaluate it). In the
real verifier, a `ConsensusVerified` holding is already proven over a finalized bank
hash, so `slotFinal` is `true` on that path; it is carried explicitly here so the
function discriminates on finalization on its own, not only in the `Prop` spec. -/
def grantWeight (h : ProvenHolding) (slotFinal : Bool) (pre : ChainState) :
    Option (VoterId × Weight) × ChainState :=
  (if h.isConsensusProven && slotFinal then some (h.owner, h.amount) else none, pre)

/-! ## §4 — THE TOP THEOREM — granted weight is BACKED and NON-CUSTODIAL. -/

/-- **`weight_backed_and_noncustodial`** — the guarantee. If `w` is granted to `v`,
then (BACKING) there is a consensus-proven holding of `≥ w` at a finalized slot owned
by `v`, AND (NON-CUSTODIAL) the grant leaves the on-chain state definitionally
unchanged for every prior state — the holder's balance is untouched. Weight is real
AND custody is preserved. -/
theorem weight_backed_and_noncustodial
    (o : HoldingsProof) (h : ProvenHolding) (v : VoterId) (w : Weight)
    (hg : grantsWeight o h v w) (sf : Bool) (pre : ChainState) :
    (h.trust = TrustTier.consensusProven ∧ o.finalized h.slot ∧ w ≤ h.amount ∧ h.owner = v)
    ∧ (grantWeight h sf pre).2 = pre := by
  obtain ⟨htier, hfin, howner, hle⟩ := hg
  exact ⟨⟨htier, hfin, hle, howner⟩, rfl⟩

/-- The backing projection alone: any granted weight is backed by a consensus-proven
holding of at least that weight at a finalized slot. -/
theorem granted_weight_is_backed
    (o : HoldingsProof) (h : ProvenHolding) (v : VoterId) (w : Weight)
    (hg : grantsWeight o h v w) :
    h.trust = TrustTier.consensusProven ∧ o.finalized h.slot ∧ w ≤ h.amount :=
  ⟨hg.1, hg.2.1, hg.2.2.2⟩

/-- The non-custodial projection alone: the grant NEVER mutates the on-chain state, for
ANY holding and ANY prior state (proven or rpc — the grant is always a pure read). -/
theorem grant_preserves_custody (h : ProvenHolding) (sf : Bool) (pre : ChainState) :
    (grantWeight h sf pre).2 = pre := rfl

/-! ## §5 — Concrete data for the discriminators. Same holding, one axis varied. -/

/-- The finalization oracle: slot `0` is uninitialized/unfinalized (`1 ≤ slot`). -/
def demoOracle : HoldingsProof := ⟨fun s => 1 ≤ s⟩

/-- A consensus-proven holding: owner `7` holds `100` of mint `42` at finalized slot `5`. -/
def provenHolding : ProvenHolding :=
  { owner := 7, mint := 42, amount := 100, slot := 5, trust := .consensusProven }

/-- The SAME holding on the `rpc`/StructureOnly tier — ONLY the trust axis differs. -/
def rpcHolding : ProvenHolding := { provenHolding with trust := .rpc }

/-- The SAME proven holding but at the uninitialized slot `0` — ONLY the slot differs. -/
def zeroSlotHolding : ProvenHolding := { provenHolding with slot := 0 }

/-- The FAIL-CLOSED oracle: nothing is finalized (`finalized ≡ False`). -/
def emptyOracle : HoldingsProof := ⟨fun _ => False⟩

/-- A concrete pre-state: the holder (account `7`) holds `100`; everyone else `0`. -/
def preState : ChainState := fun a => if a = 7 then 100 else 0

/-! ## §6 — NON-VACUITY — the gate DISCRIMINATES on BOTH axes (trust tier AND amount). -/

/-- **TRUE side.** The consensus-proven holding grants its full weight `100` to owner
`7` at the finalized slot `5`. The credit gate is genuinely inhabited. -/
theorem proven_grants_weight : grantsWeight demoOracle provenHolding 7 100 :=
  ⟨rfl, (by decide : (1 : Nat) ≤ 5), rfl, Nat.le_refl 100⟩

/-- **TIER DISCRIMINATOR (fail-closed).** The SAME holding — same finalized slot, same
owner, same amount — grants NO weight on the `rpc` tier. The ONLY difference from the
TRUE side is the trust tier: weight requires a real proof, not an RPC echo. -/
theorem rpc_grants_no_weight : ¬ grantsWeight demoOracle rpcHolding 7 100 := by
  rintro ⟨htier, _, _, _⟩
  exact absurd htier (by decide)

/-- **AMOUNT DISCRIMINATOR.** A weight STRICTLY ABOVE the proven amount (`101 > 100`)
is NOT grantable, even from the consensus-proven holding at the finalized slot. Weight
can never exceed the proven balance. -/
theorem overweight_not_grantable : ¬ grantsWeight demoOracle provenHolding 7 101 := by
  rintro ⟨_, _, _, hle⟩
  exact absurd hle (by decide)

/-- **UNFINALIZED-SLOT REJECTION (Nomad-law analog).** The SAME proven holding at the
uninitialized slot `0` grants no weight: `demoOracle` does not finalize slot `0`. -/
theorem unfinalized_slot_grants_no_weight : ¬ grantsWeight demoOracle zeroSlotHolding 7 100 := by
  rintro ⟨_, hfin, _, _⟩
  have h0 : (1 : Nat) ≤ 0 := hfin
  omega

/-- **FAIL-CLOSED DEFAULT.** Under the empty oracle (`finalized ≡ False`), NO holding —
not even a consensus-proven one — grants any weight, for any identity/weight. -/
theorem emptyOracle_grants_nothing (h : ProvenHolding) (v : VoterId) (w : Weight) :
    ¬ grantsWeight emptyOracle h v w := by
  rintro ⟨_, hfin, _, _⟩; exact hfin

/-- **THE DISCRIMINATOR, ASSEMBLED** (the `interchain_gate_discriminates` analog): SAME
oracle, SAME holder — a consensus-proven holding of `100` grants `100`, but the SAME
holding on the `rpc` tier grants NOTHING, and `101` (over the proven amount) is never
grantable. The gate turns on BOTH the trust tier AND the amount bound. -/
theorem gate_discriminates_both_axes :
    grantsWeight demoOracle provenHolding 7 100
    ∧ ¬ grantsWeight demoOracle rpcHolding 7 100
    ∧ ¬ grantsWeight demoOracle provenHolding 7 101 :=
  ⟨proven_grants_weight, rpc_grants_no_weight, overweight_not_grantable⟩

/-! ## §7 — NON-CUSTODIAL, on concrete data — the holder's balance is untouched. -/

/-- **END-TO-END NON-CUSTODIAL WITNESS.** From the proven holding at `preState` (holder
`7` holds `100`): the grant yields the weight assignment `some (7, 100)` AND the
holder's balance is STILL `100` afterward — custody was never moved. -/
theorem demo_grant_is_noncustodial :
    (grantWeight provenHolding true preState).1 = some (7, 100)
    ∧ (grantWeight provenHolding true preState).2 7 = 100 := by
  refine ⟨rfl, ?_⟩
  show preState 7 = 100
  decide

/-- The `rpc` holding produces NO weight assignment even as a value (with a finalized
slot) — the gate is fail-closed at the operational layer too, not only in the `Prop`
predicate. -/
theorem rpc_grant_yields_none :
    (grantWeight rpcHolding true preState).1 = none := rfl

/-- **FINALIZATION DISCRIMINATOR at the operational layer.** The SAME consensus-proven
holding, but with the light client's finality verdict `false` (its slot not final),
yields NO weight from the deployed `grantWeight` — the function itself enforces
finalization, not just the `Prop` spec. -/
theorem unfinalized_grant_yields_none :
    (grantWeight provenHolding false preState).1 = none := rfl

/-! It runs (`#guard`): the proven+finalized holding grants `some (7,100)` and leaves the
holder's balance at `100`; the rpc holding, and the proven-but-unfinalized holding, both
grant `none`. -/

#guard (grantWeight provenHolding true preState).1 == some (7, 100)
#guard (grantWeight provenHolding true preState).2 7 == 100
#guard (grantWeight rpcHolding true preState).1 == none
#guard (grantWeight provenHolding false preState).1 == none
#guard provenHolding.isConsensusProven == true
#guard rpcHolding.isConsensusProven == false

/-! ## §8 — Axiom hygiene — every theorem kernel-clean (CI hard-gate). -/

#assert_axioms weight_backed_and_noncustodial
#assert_axioms granted_weight_is_backed
#assert_axioms grant_preserves_custody
#assert_axioms proven_grants_weight
#assert_axioms rpc_grants_no_weight
#assert_axioms overweight_not_grantable
#assert_axioms unfinalized_slot_grants_no_weight
#assert_axioms emptyOracle_grants_nothing
#assert_axioms gate_discriminates_both_axes
#assert_axioms demo_grant_is_noncustodial
#assert_axioms rpc_grant_yields_none
#assert_axioms unfinalized_grant_yields_none

#print axioms weight_backed_and_noncustodial
#print axioms gate_discriminates_both_axes

end Metatheory.Bridge.ProofOfHoldings

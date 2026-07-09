/-
# `Dregg2.Crypto.CapabilityChain` — biscuit/credential ATTENUATION SOUNDNESS, the first
protocol-level game riding on the hybrid-signature keystone.

`HybridCombiner.lean` proved the KEYSTONE: the `ed25519 ∧ ML-DSA` hybrid signature is EUF-CMA-unforgeable
if EITHER the discrete-log floor `SchnorrDLHard` OR the Module-SIS floor `MSISHard` holds
(`hybrid_secure_if_either_floor`). That is a statement about ONE signature. A `dregg-auth` **credential**
is a whole *chain* of them — a root-keyed biscuit whose blocks each carry the NEXT block's public key and
are SIGNED by the CURRENT key over their body `(caveats ‖ next_pubkey)`; verification walks root→leaf
checking every signature and that each block only ATTENUATES (shrinks authority). This file lifts the
one-signature keystone to the chain, proving the two credential guarantees the macaroon/biscuit lineage
leans on:

* **SOUNDNESS (`chain_unforgeable_under_eufcma`).** An adversary cannot produce a `VerifyChain`-accepting
  credential rooted at an honest key UNLESS it forges a signature under an honest key. Precisely: a forged
  accepting chain that was NOT entirely honestly signed yields a FRESH valid signature under an honest
  parent key — a `SigScheme.Forgery` — contradicting that key's `EufCma`. The reduction walks to the FIRST
  block not honestly signed; because every earlier block WAS honestly signed and an honest issuer only
  delegates to honest keys (`honestDelegation`), that block's parent key is honest, and its signature on a
  never-queried body is exactly the forgery. So `EufCma (each honest key) → chain soundness`.

* **ATTENUATION-ONLY (`chain_only_attenuates`).** `VerifyChain` enforces each block's authority ≤ its
  parent's (a monotone order on an authority lattice). Hence a valid chain can only SHRINK authority down
  root→leaf, never amplify — the macaroon/biscuit invariant, mirroring `Authority.Biscuit.biscuit_narrows`
  and `Authority.CDT.path_attenuates`.

## Anchoring in DL ∨ MSIS — no named-carrier laundering.

The chain's signatures ARE the hybrid signatures of `HybridCombiner`, so each honest key's `EufCma` is NOT
a re-asserted carrier: it is discharged by `hybrid_secure_if_either_floor` from `SchnorrDLHard ∨ MSISHard`
(`chain_unforgeable_under_hybrid_floor`). Chain soundness therefore reduces to the lattice/discrete-log
floor through the combiner — break one component, the other still holds. The `SigScheme`/`Forgery`/`EufCma`
model is REUSED verbatim from `HybridCombiner`; nothing new is assumed.

## Teeth (non-vacuous).

Over a concrete toy scheme (`sig = pk + m`, the demo oracle) and `Finset ℕ` authority: an honest chain is
ACCEPTED and its authority STRICTLY shrinks (`goodChain_verifies`, `goodChain_strictly_shrinks`); a chain
whose block is signed by a non-parent/attacker key is REJECTED (`forgedChain_rejected`); an AMPLIFYING
block (claims a right the parent lacks) is REJECTED even with a valid signature — attenuation-only is
load-bearing (`ampChain_rejected`); and an accepting chain need NOT be honestly signed absent the
unforgeability assumption, so the `EufCma` hypothesis is load-bearing, not decorative.
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

namespace Dregg2.Crypto.CapabilityChain

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

variable {SK PK Msg Sig Auth : Type*}

/-! ## The credential model — a root-keyed chain of attenuation blocks. -/

/-- **One block of the chain.** `authority` = the authority it confers (must be ≤ its parent's —
attenuation); `nextPk` = the public key the NEXT block down the chain verifies under (what makes offline
attenuation possible); `sig` = this block's signature, checked under its PARENT's key (the root block under
the issuer/root key), over the block body `body (parent-marker) block`. Mirrors `dregg-auth`'s `Block`
(`caveats`/`next_pub`/`sig`) and `Authority.Biscuit.Block`. -/
structure Block (Auth PK Sig : Type*) where
  /-- The authority this block confers (≤ its parent's — attenuation, never amplification). -/
  authority : Auth
  /-- The public key under which the NEXT block down the chain is verified. -/
  nextPk : PK
  /-- This block's signature — verified under the PARENT's key (root: under the root key). -/
  sig : Sig

/-! ### The walk — root-anchored signature chain that also narrows authority.

`body : Option Sig → Block → Msg` is the block-body encoding the parent signs: `none` at the root (the
issuer signs over the nonce ‖ caveats ‖ next_pubkey), `some parent.sig` at every deeper block (chaining
over the parent's signature, exactly `dregg-auth`'s `block_digest(prev_sig, caveats, next_pub, …)`). -/

/-- **`VerifyFrom parent blocks`** — the tail of the walk: `blocks` (root→leaf) verifies under `parent`,
each block's signature checking under the parent's `nextPk` AND its authority attenuating the parent's. -/
def VerifyFrom [LE Auth] (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg)
    (parent : Block Auth PK Sig) : List (Block Auth PK Sig) → Prop
  | [] => True
  | b :: rest =>
      S.verify parent.nextPk (body (some parent.sig) b) b.sig
        ∧ b.authority ≤ parent.authority
        ∧ VerifyFrom S body b rest

/-- **`VerifyChain rootPk blocks`** — the full credential verification: the head (root) block verifies
under the root key `rootPk` over its `none`-marked body, and the rest verifies from it. Root-anchored,
offline, deterministic — the executable `Credential::verify` chain face. -/
def VerifyChain [LE Auth] (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg)
    (rootPk : PK) : List (Block Auth PK Sig) → Prop
  | [] => True
  | b :: rest => S.verify rootPk (body none b) b.sig ∧ VerifyFrom S body b rest

/-! ### The honest-signing predicate — which blocks an honest key actually signed.

`Q : PK → Msg → Prop` is the per-key signing oracle of `HybridCombiner.EufCma`: `Q pk m` means honest key
`pk` signed message `m`. `ChainSigned`/`FromSigned` say EVERY block's body was honestly signed by its
parent key — the "honestly-delegated credential" a legitimate holder possesses. -/

/-- **`FromSigned parent blocks`** — every block below `parent` was honestly signed by its parent key. -/
def FromSigned (Q : PK → Msg → Prop) (body : Option Sig → Block Auth PK Sig → Msg)
    (parent : Block Auth PK Sig) : List (Block Auth PK Sig) → Prop
  | [] => True
  | b :: rest => Q parent.nextPk (body (some parent.sig) b) ∧ FromSigned Q body b rest

/-- **`ChainSigned rootPk blocks`** — the whole credential was honestly signed root→leaf: the root block
by the root key, every deeper block by its (honest) parent. This is "a validly-delegated credential". -/
def ChainSigned (Q : PK → Msg → Prop) (body : Option Sig → Block Auth PK Sig → Msg)
    (rootPk : PK) : List (Block Auth PK Sig) → Prop
  | [] => True
  | b :: rest => Q rootPk (body none b) ∧ FromSigned Q body b rest

/-! ## SOUNDNESS — a forged accepting chain yields a signature forgery on an honest key. -/

/-- **The reduction, tail form.** Walking from an honest `parent`, if the tail VERIFIES but was NOT
entirely honestly signed, the FIRST block not honestly signed is a fresh valid signature under an honest
parent key — a `Forgery`. The honest-parent invariant propagates by `hdel` (an honest key only signs off on
delegating to a key it deems honest — honest keygen). -/
theorem from_forgery [LE Auth]
    (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg)
    (honestPk : PK → Prop) (Q : PK → Msg → Prop)
    (hdel : ∀ (pk : PK) (ps : Option Sig) (b : Block Auth PK Sig),
      honestPk pk → Q pk (body ps b) → honestPk b.nextPk) :
    ∀ (blocks : List (Block Auth PK Sig)) (parent : Block Auth PK Sig),
      honestPk parent.nextPk → VerifyFrom S body parent blocks →
      ¬ FromSigned Q body parent blocks → ∃ pk, honestPk pk ∧ Forgery S pk (Q pk) := by
  intro blocks
  induction blocks with
  | nil => intro parent _ _ hns; exact absurd trivial hns
  | cons b rest ih =>
    intro parent hpar hverify hns
    obtain ⟨hv, _hatt, hrest⟩ := hverify
    by_cases hq : Q parent.nextPk (body (some parent.sig) b)
    · exact ih b (hdel parent.nextPk (some parent.sig) b hpar hq) hrest (fun hfr => hns ⟨hq, hfr⟩)
    · exact ⟨parent.nextPk, hpar, body (some parent.sig) b, b.sig, hq, hv⟩

/-- **The reduction, full form.** A `VerifyChain`-accepting credential rooted at an honest key that was NOT
entirely honestly signed exhibits a `Forgery` on some honest key. The root block itself may be the forgery
(if the root key never signed it); otherwise the walk descends via `from_forgery`. -/
theorem chain_forgery [LE Auth]
    (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg)
    (honestPk : PK → Prop) (Q : PK → Msg → Prop)
    (hdel : ∀ (pk : PK) (ps : Option Sig) (b : Block Auth PK Sig),
      honestPk pk → Q pk (body ps b) → honestPk b.nextPk)
    (rootPk : PK) (blocks : List (Block Auth PK Sig))
    (hroot : honestPk rootPk)
    (hverify : VerifyChain S body rootPk blocks)
    (hns : ¬ ChainSigned Q body rootPk blocks) :
    ∃ pk, honestPk pk ∧ Forgery S pk (Q pk) := by
  cases blocks with
  | nil => exact absurd trivial hns
  | cons b rest =>
    obtain ⟨hv, hrest⟩ := hverify
    by_cases hq : Q rootPk (body none b)
    · exact from_forgery S body honestPk Q hdel rest b
        (hdel rootPk none b hroot hq) hrest (fun hfr => hns ⟨hq, hfr⟩)
    · exact ⟨rootPk, hroot, body none b, b.sig, hq, hv⟩

/-- **SOUNDNESS (THE THEOREM) — `chain_unforgeable_under_eufcma`.** If every honest key is EUF-CMA-secure
(no forgery under it), then every `VerifyChain`-accepting credential rooted at an honest key IS entirely
honestly signed (`ChainSigned`): the adversary cannot produce an accepting chain carrying a block it forged,
because that block would be a `Forgery` refuting the parent key's `EufCma`. This is the biscuit/credential
soundness statement: a `verifyChain`-accepting credential extending an honest prefix could only have been
built by legitimate delegation — unless a signature was forged. -/
theorem chain_unforgeable_under_eufcma [LE Auth]
    (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg)
    (honestPk : PK → Prop) (Q : PK → Msg → Prop)
    (hdel : ∀ (pk : PK) (ps : Option Sig) (b : Block Auth PK Sig),
      honestPk pk → Q pk (body ps b) → honestPk b.nextPk)
    (heuf : ∀ pk, honestPk pk → EufCma S pk (Q pk))
    (rootPk : PK) (blocks : List (Block Auth PK Sig))
    (hroot : honestPk rootPk)
    (hverify : VerifyChain S body rootPk blocks) :
    ChainSigned Q body rootPk blocks := by
  by_contra hns
  obtain ⟨pk, hpk, hforge⟩ := chain_forgery S body honestPk Q hdel rootPk blocks hroot hverify hns
  exact heuf pk hpk hforge

/-! ## ATTENUATION-ONLY — a valid chain can only shrink authority (the biscuit invariant). -/

/-- **`verifyFrom_narrows`** — down a verifying tail, the leaf's authority is ≤ the parent's: each edge
attenuates, chained through transitivity of the authority order. -/
theorem verifyFrom_narrows [Preorder Auth]
    (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg) :
    ∀ (blocks : List (Block Auth PK Sig)) (parent : Block Auth PK Sig),
      VerifyFrom S body parent blocks →
      ∀ {leaf : Block Auth PK Sig}, blocks.getLast? = some leaf →
        leaf.authority ≤ parent.authority := by
  intro blocks
  induction blocks with
  | nil => intro parent _ leaf hl; simp at hl
  | cons b rest ih =>
    intro parent hvf leaf hl
    obtain ⟨_hv, hatt, hrest⟩ := hvf
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl; exact hatt
    | cons c rest' =>
      rw [List.getLast?_cons_cons] at hl
      exact le_trans (ih b hrest hl) hatt

/-- **ATTENUATION-ONLY — `chain_only_attenuates`.** In a `VerifyChain`-accepting credential the leaf block
confers no more authority than the root block: `leaf.authority ≤ root.authority`. Offline attenuation can
only RESTRICT — a holder appending signed blocks can never grant themselves an authority the issuer
withheld. The public-key credential analogue of `Authority.Biscuit.biscuit_narrows`. -/
theorem chain_only_attenuates [Preorder Auth]
    (S : SigScheme SK PK Msg Sig) (body : Option Sig → Block Auth PK Sig → Msg) (rootPk : PK)
    {root : Block Auth PK Sig} {rest : List (Block Auth PK Sig)} {leaf : Block Auth PK Sig}
    (hverify : VerifyChain S body rootPk (root :: rest))
    (hl : (root :: rest).getLast? = some leaf) :
    leaf.authority ≤ root.authority := by
  obtain ⟨_hv, hrest⟩ := hverify
  cases rest with
  | nil =>
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl; exact le_refl _
  | cons c rest' =>
    rw [List.getLast?_cons_cons] at hl
    exact verifyFrom_narrows S body (c :: rest') root hrest hl

/-! ## ANCHORING — chain soundness reduces to `SchnorrDLHard ∨ MSISHard` through the combiner.

The chain's signatures ARE the `ed25519 ∧ ML-DSA` hybrid signatures. So each honest key's `EufCma` is not
assumed — it is DISCHARGED by `HybridCombiner.hybrid_secure_if_either_floor` from the discrete-log floor OR
the Module-SIS floor. Chain soundness therefore holds if EITHER floor does. -/

/-- **`chain_unforgeable_under_hybrid_floor` — chain soundness if EITHER cryptographic floor holds.** With
the per-honest-key forking reductions (a hybrid forgery ⟹ a `DLSolver` on one side, two SelfTargetMSIS
solutions on the other — the `HybridCombiner` reductions, not carriers), a `VerifyChain`-accepting
`hybrid Cl Pq` credential rooted at an honest key is entirely honestly signed provided
`SchnorrDLHard C G ∨ MSISHard (augmented A t) …`. Each honest key's `EufCma` is produced by
`hybrid_secure_if_either_floor`; the ONLY floors invoked are discrete log and Module-SIS. -/
theorem chain_unforgeable_under_hybrid_floor [LE Auth]
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (honestPk : (PKc × PKp) → Prop) (Q : (PKc × PKp) → Msg → Prop)
    (body : Option (Sigc × Sigp) → Block Auth (PKc × PKp) (Sigc × Sigp) → Msg)
    (rootPk : PKc × PKp) (blocks : List (Block Auth (PKc × PKp) (Sigc × Sigp)))
    (dlFork : ∀ pk, honestPk pk → Forgery Cl pk.1 (Q pk) → DLSolver C G)
    (msisFork : ∀ pk, honestPk pk → Forgery Pq pk.2 (Q pk) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (hdel : ∀ (pk : PKc × PKp) (ps : Option (Sigc × Sigp))
        (b : Block Auth (PKc × PKp) (Sigc × Sigp)),
      honestPk pk → Q pk (body ps b) → honestPk b.nextPk)
    (rootHonest : honestPk rootPk)
    (hverify : VerifyChain (hybrid Cl Pq) body rootPk blocks) :
    ChainSigned Q body rootPk blocks := by
  refine chain_unforgeable_under_eufcma (hybrid Cl Pq) body honestPk Q hdel ?_ rootPk blocks
    rootHonest hverify
  intro pk hpk
  obtain ⟨a, b⟩ := pk
  exact hybrid_secure_if_either_floor Cl Pq a b (Q (a, b)) C G A t β
    (dlFork (a, b) hpk) (msisFork (a, b) hpk) hfloor

/-! ## Teeth — a concrete toy scheme makes the guarantees non-vacuous and computable.

`toyVerify pk m sig := (sig = pk + m)` stands in for a real signature `verify` (as `Authority.Biscuit`'s
`demoSig` stands in for ed25519); authority is `Finset ℕ` ordered by ⊆. The chain narrows read/write/grant
→ read/write. -/

/-- The demo signing "hash": `pk + m` (a signature is valid iff it equals this). -/
@[reducible] def toyHash (pk m : ℕ) : ℕ := pk + m

/-- The demo verification relation: `sig = toyHash pk m`. Reducible so `decide`/`rfl` see the `Eq`. -/
@[reducible] def toyVerify (pk m sig : ℕ) : Prop := sig = toyHash pk m

/-- The demo signature scheme over `ℕ` (stands in for the real `hybrid Cl Pq`). -/
@[reducible] def toyS : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign sk m := toyHash sk m
  verify := toyVerify

/-- The demo block body: the parent marker (`0` nonce at the root, the parent's `sig` deeper) plus the
carried next key — the essence of `block_digest(prev, next_pub)`. -/
def toyBody : Option ℕ → Block (Finset ℕ) ℕ ℕ → ℕ
  | none, b => 0 + b.nextPk
  | some s, b => s + b.nextPk

/-- Root grant: full authority `{1,2,3}`, hands key `7` down, signed under the root key `100`. -/
def b0 : Block (Finset ℕ) ℕ ℕ := { authority := {1, 2, 3}, nextPk := 7, sig := 107 }
/-- Attenuation: drops `3` (authority `{1,2}`), hands key `8` down, signed under the parent key `7`. -/
def b1 : Block (Finset ℕ) ℕ ℕ := { authority := {1, 2}, nextPk := 8, sig := 122 }

/-- An honest credential (root→leaf): `b0 ← b1`, signed at every step and narrowing. -/
def goodChain : List (Block (Finset ℕ) ℕ ℕ) := [b0, b1]

/-- **`goodChain_verifies`** — the honest credential is ACCEPTED: signatures `107` (under root `100`) and
`122` (under the carried key `7`) both check, and `{1,2} ⊆ {1,2,3}` attenuates. -/
theorem goodChain_verifies : VerifyChain toyS toyBody 100 goodChain := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · trivial

/-- **`goodChain_leaf_le_root`** — the keystone on the concrete credential, via `chain_only_attenuates`:
the leaf's `{1,2}` ≤ the root's `{1,2,3}`. -/
theorem goodChain_leaf_le_root : b1.authority ≤ b0.authority :=
  chain_only_attenuates toyS toyBody 100 goodChain_verifies rfl

/-- **`goodChain_strictly_shrinks`** — authority STRICTLY shrinks root→leaf (`{1,2} ⊂ {1,2,3}`): the
attenuation is real, not the identity edge. -/
theorem goodChain_strictly_shrinks : b1.authority ⊂ b0.authority := by decide

/-- A FORGED attenuation: signed by an attacker key (`sig = 9999`) that does not match the parent key `7`. -/
def b1forged : Block (Finset ℕ) ℕ ℕ := { authority := {1, 2}, nextPk := 8, sig := 9999 }

/-- **`forgedChain_rejected`** — a block signed by a non-parent/attacker key is REJECTED by `VerifyChain`
(`9999 ≠ 7 + body`). You cannot splice in a delegation you were not given the key to sign. -/
theorem forgedChain_rejected : ¬ VerifyChain toyS toyBody 100 [b0, b1forged] := by
  rintro ⟨-, hv1, -, -⟩
  exact absurd hv1 (by decide)

/-- An AMPLIFYING attenuation: a VALID signature (`122`) but claims `{1,2,3,4}` — a right the parent lacks. -/
def b1amp : Block (Finset ℕ) ℕ ℕ := { authority := {1, 2, 3, 4}, nextPk := 8, sig := 122 }

/-- **`ampChain_rejected` (attenuation-only is load-bearing)** — an amplifying block is REJECTED even
though its signature is valid: the ONLY failing conjunct is `{1,2,3,4} ⊆ {1,2,3}`. Offline delegation
cannot grab an authority the parent withheld. -/
theorem ampChain_rejected : ¬ VerifyChain toyS toyBody 100 [b0, b1amp] := by
  rintro ⟨-, -, hatt, -⟩
  exact absurd hatt (by decide)

/-- **`eufcma_is_load_bearing`** — an accepting credential need NOT be honestly signed absent the
unforgeability assumption: with an EMPTY honest oracle (`Q = ⊥`) the honest chain still VERIFIES (its
signatures check) yet is NOT `ChainSigned`. So `chain_unforgeable_under_eufcma`'s `EufCma` hypothesis is
what rules such a chain out — load-bearing, not decorative. -/
theorem eufcma_is_load_bearing : ¬ ChainSigned (fun _ _ => False) toyBody 100 goodChain := by
  rintro ⟨hq, -⟩; exact hq

/-- **A forgery target is inhabitable** — the `Forgery` the reduction lands on is real: against an honest
key with an empty query set, any signature over any message is a fresh valid forgery. This is the object
`chain_unforgeable_under_eufcma` refutes via `EufCma`. -/
example : Forgery toyS 7 (fun _ => False) :=
  ⟨123, toyHash 7 123, not_false, rfl⟩

-- The honest root/attenuation signatures verify under the correct parent keys…
#guard b0.sig == 100 + toyBody none b0
#guard b1.sig == b0.nextPk + toyBody (some b0.sig) b1
-- …the attacker-signed block FAILS its parent-key check (forgery caught on the wire)…
#guard !(b1forged.sig == b0.nextPk + toyBody (some b0.sig) b1forged)
-- …attenuation holds, amplification does not, and the shrink is strict.
#guard decide (b1.authority ⊆ b0.authority)
#guard decide (¬ (b1amp.authority ⊆ b0.authority))
#guard decide (b1.authority ⊂ b0.authority)

/-! ### Axiom hygiene. -/

#assert_all_clean [
  from_forgery,
  chain_forgery,
  chain_unforgeable_under_eufcma,
  verifyFrom_narrows,
  chain_only_attenuates,
  chain_unforgeable_under_hybrid_floor,
  goodChain_verifies,
  goodChain_leaf_le_root,
  goodChain_strictly_shrinks,
  forgedChain_rejected,
  ampChain_rejected,
  eufcma_is_load_bearing
]

end Dregg2.Crypto.CapabilityChain

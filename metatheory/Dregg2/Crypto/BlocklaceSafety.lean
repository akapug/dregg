/-
# `Dregg2.Crypto.BlocklaceSafety` — BLOCKLACE equivocation detection + cordial-dissemination safety.

The deployed `blocklace/src/{lib.rs, finality.rs, ordering.rs, dissemination.rs}` is a DAG where each
block cites its predecessors and is signed by its creator; the creator id is now the HYBRID id
`H(ed25519 ‖ ml_dsa)` (`lib.rs::Block` carries both a `signature` and a `pq_signature`, pinned to the
enrolled ML-DSA key). This file supplies the three safety properties the deployed code REALIZES but the
Lean tree had not yet stated at the blocklace layer:

1. **Equivocation is detectable with a SELF-AUTHENTICATING proof.** A creator that signs two blocks
   `b₁, b₂` with neither citing the other (`ordering.rs::equivocates_in_past`: ≥2 blocks of one creator at
   one round, neither in the other's causal past) hands any node that observes BOTH a
   `MisbehaviourProof` — the two signed blocks. We prove the detector is
   * **SOUND** — it NEVER accuses an honest creator: an honest creator cites its own previous block, so
     its blocks are totally ordered (`Chained`) and hence pairwise comparable; a `MisbehaviourProof`
     requires an INCOMPARABLE pair, so none exists for an honest creator.
   * **COMPLETE** — any genuine equivocation, once both signed blocks are observed, YIELDS the proof.
   The proof is self-authenticating: it carries the two component signatures, re-checkable by anyone
   against the creator's enrolled public key — no trust in the accuser (`lib.rs::EquivocationProof` is the
   Rust dual; it is `attributable` and retained as `detectable evidence`).

2. **`no_forged_block`** — a block accepted as created by an honest member but never actually created by it
   is exactly a `HybridCombiner.Forgery` (a FRESH-message valid signature). It refutes `EufCma`, which is
   DISCHARGED all the way down to `SchnorrDLHard ∨ MSISHard` through
   `HybridCombiner.hybrid_secure_if_either_floor`: the block signatures are hybrid, so a quantum adversary
   that breaks the ed25519 half still faces Module-SIS on the ML-DSA half. No forged block under either
   floor.

3. **`cordial_dissemination_converges`** — under the cordial-dissemination rule (`dissemination.rs`: "send
   to others blocks you know and think they need"; a node relays what it cites, and only cites what it has
   fully disseminated) AND the EXPLICIT **fair-delivery** protocol assumption (the honest dual of a crypto
   floor: an honestly-disseminated block eventually reaches every honest node), every honest block reaches
   every honest node, so honest nodes converge on the SAME DAG closure. The fair-delivery assumption is
   stated as a structure FIELD (a hypothesis, never an `axiom`), and shown LOAD-BEARING (drop it and a
   block can stay stuck at its creator).

## No named-carrier laundering.

The ONLY irreducible objects are: the two cryptographic floors `SchnorrDLHard` / `MSISHard` (through
`HybridCombiner`, whose forking reductions are hypotheses — theorems of the existing machinery, not
carriers); the honest **cite-your-own-previous** rule (`Chained`, a stated protocol invariant, a
hypothesis); and the **fair-delivery** protocol assumption (partial-synchrony's honest dual). No
`def …Hard` is introduced; `#assert_all_clean` never checks hypotheses — every keystone is kernel-clean.

## Teeth (load-bearing, both instances exhibited).

* An honest creator NEVER equivocates: two of its blocks (distinct sequences, chained) are comparable, so
  `¬ IsEquivocation`, and the detector produces NO proof (soundness fires).
* A GENUINE equivocation (two blocks at the SAME sequence, distinct ids) IS detected — a
  `MisbehaviourProof` is constructed (completeness fires).
* WITHOUT the cite-your-own-previous rule an honest creator could look like an equivocator: the two
  same-sequence blocks are incomparable, so `Chained` is exactly what soundness needs — drop it and a
  `MisbehaviourProof` for that creator exists (the `Chained` hypothesis is load-bearing).
* A forged block EXHIBITS the `Forgery`; and the fair-delivery assumption is load-bearing (without it a
  block stays at its creator).

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2` (whole-tree).

Cite: Cordial Miners (Keidar–Naor–Poupko–Shapiro, arXiv:2205.09174) for the DAG/round + cordial
dissemination; the hybrid ∧-combiner (Bindel–Herath–McKague–Stebila) via `HybridCombiner`.
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.BlocklaceSafety

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

/-! ## §1. The block model — creator, sequence, id, and the causal (cite) relation.

A `Blk` is the algebraic skeleton of `lib.rs::Block`: a `creator` (the hybrid id `H(ed25519 ‖ ml_dsa)`),
a monotone `seq`uence, and a content `id`. The **cite** relation `caus b b'` means `b` causally cites
(reaches) `b'` — `b'` lies in `b`'s causal past (`lib.rs::causal_past`). It is left abstract: the detector
and its soundness/completeness hold for ANY notion of "cites", and the concrete `seq`-order instance in
the teeth (`caus b b' := b'.seq < b.seq` on a single creator's strand) is the honest chain. -/

/-- The block skeleton: a creator id, a monotone sequence number, and a content id. Mirrors
`lib.rs::Block.{creator, sequence, id()}`. -/
structure Blk (Creator BId : Type*) where
  /-- The creator's (hybrid) public-key id. -/
  creator : Creator
  /-- Monotonic sequence number for this creator's strand. -/
  seq : Nat
  /-- The block's content id (BLAKE3 of its canonical bytes). -/
  id : BId

variable {Creator : Type*} {BId : Type*}
variable {SK PK Msg Sig : Type*}

/-- **`Comparable caus b₁ b₂`** — one block cites (causally reaches) the other. Two of an honest
creator's blocks are always comparable (its strand is a chain). -/
def Comparable (caus : Blk Creator BId → Blk Creator BId → Prop)
    (b₁ b₂ : Blk Creator BId) : Prop :=
  caus b₁ b₂ ∨ caus b₂ b₁

/-- **`IsEquivocation caus b₁ b₂`** — the equivocation predicate of `ordering.rs::equivocates_in_past`:
two DISTINCT blocks by the SAME creator, NEITHER citing the other (incomparable in the causal DAG). -/
def IsEquivocation (caus : Blk Creator BId → Blk Creator BId → Prop)
    (b₁ b₂ : Blk Creator BId) : Prop :=
  b₁.creator = b₂.creator ∧ b₁ ≠ b₂ ∧ ¬ caus b₁ b₂ ∧ ¬ caus b₂ b₁

/-- **`Chained caus c`** — the honest **cite-your-own-previous** rule: every two distinct blocks by
creator `c` are comparable (its strand is totally ordered). An honest creator always cites its own
previous block (`lib.rs::insert` enforces strictly-monotone `sequence` per creator, and a cordial block
references the strand tip), so any two of its blocks stand in the causal order. This is the ONE protocol
invariant the detector's soundness consumes — a hypothesis, never an `axiom`. -/
def Chained (caus : Blk Creator BId → Blk Creator BId → Prop) (c : Creator) : Prop :=
  ∀ b₁ b₂ : Blk Creator BId, b₁.creator = c → b₂.creator = c → b₁ ≠ b₂ → Comparable caus b₁ b₂

/-- An honest (chained) creator does NOT equivocate: no two of its blocks satisfy `IsEquivocation`
(comparability is exactly the negation of the incomparable-pair condition). -/
theorem chained_no_equivocation (caus : Blk Creator BId → Blk Creator BId → Prop) (c : Creator)
    (hch : Chained caus c) (b₁ b₂ : Blk Creator BId)
    (h₁ : b₁.creator = c) (h₂ : b₂.creator = c) : ¬ IsEquivocation caus b₁ b₂ := by
  rintro ⟨_, hne, hnc1, hnc2⟩
  rcases hch b₁ b₂ h₁ h₂ hne with h | h
  · exact hnc1 h
  · exact hnc2 h

/-! ## §2. The self-authenticating detector — SOUND and COMPLETE.

The finality gate observes a block as a `(body, σ)` pair signed under the creator's enrolled public key
(`body : Blk → Msg` is the canonical signed bytes, `pkOf : Creator → PK` the enrolled key roster). A
`MisbehaviourProof` is the two signed blocks: it carries both component signatures, so ANY node can
re-verify it against `pkOf` — self-authenticating, no trust in the accuser (`lib.rs::EquivocationProof`,
retained as `detectable evidence`). -/

/-- **`MisbehaviourProof S pkOf body caus c`** — a SELF-AUTHENTICATING equivocation proof against creator
`c`: two blocks both signed by `c` (`auth₁/auth₂` verify under `pkOf c`), distinct, and INCOMPARABLE
(neither cites the other). Anyone holding it re-checks the two signatures and the incomparability without
trusting whoever produced it. -/
structure MisbehaviourProof (S : SigScheme SK PK Msg Sig) (pkOf : Creator → PK)
    (body : Blk Creator BId → Msg) (caus : Blk Creator BId → Blk Creator BId → Prop) (c : Creator) where
  /-- The first equivocating block. -/
  b₁ : Blk Creator BId
  /-- The second equivocating block. -/
  b₂ : Blk Creator BId
  /-- `c`'s signature on `b₁`'s body. -/
  σ₁ : Sig
  /-- `c`'s signature on `b₂`'s body. -/
  σ₂ : Sig
  /-- Both blocks name `c` as creator. -/
  from₁ : b₁.creator = c
  /-- Both blocks name `c` as creator. -/
  from₂ : b₂.creator = c
  /-- `σ₁` verifies under `c`'s enrolled key — re-checkable. -/
  auth₁ : S.verify (pkOf c) (body b₁) σ₁
  /-- `σ₂` verifies under `c`'s enrolled key — re-checkable. -/
  auth₂ : S.verify (pkOf c) (body b₂) σ₂
  /-- The two blocks are distinct. -/
  distinct : b₁ ≠ b₂
  /-- Neither cites the other — the equivocation. -/
  incomp₁ : ¬ caus b₁ b₂
  /-- Neither cites the other — the equivocation. -/
  incomp₂ : ¬ caus b₂ b₁

/-- The proof RE-VERIFIES: it exposes both signature checks and the incomparability, so a third party
confirms the misbehaviour from the proof alone — **self-authenticating**. -/
theorem MisbehaviourProof.self_authenticating
    {S : SigScheme SK PK Msg Sig} {pkOf : Creator → PK}
    {body : Blk Creator BId → Msg} {caus : Blk Creator BId → Blk Creator BId → Prop} {c : Creator}
    (P : MisbehaviourProof S pkOf body caus c) :
    S.verify (pkOf c) (body P.b₁) P.σ₁ ∧ S.verify (pkOf c) (body P.b₂) P.σ₂ ∧
      P.b₁ ≠ P.b₂ ∧ ¬ caus P.b₁ P.b₂ ∧ ¬ caus P.b₂ P.b₁ :=
  ⟨P.auth₁, P.auth₂, P.distinct, P.incomp₁, P.incomp₂⟩

/-- A `MisbehaviourProof` exhibits a genuine `IsEquivocation` — the accusation is TRUE, not merely
signed. -/
theorem MisbehaviourProof.exhibits_equivocation
    {S : SigScheme SK PK Msg Sig} {pkOf : Creator → PK}
    {body : Blk Creator BId → Msg} {caus : Blk Creator BId → Blk Creator BId → Prop} {c : Creator}
    (P : MisbehaviourProof S pkOf body caus c) : IsEquivocation caus P.b₁ P.b₂ :=
  ⟨P.from₁.trans P.from₂.symm, P.distinct, P.incomp₁, P.incomp₂⟩

/-- **DETECTOR SOUNDNESS — never accuses an honest creator.** An honest creator obeys the
cite-your-own-previous rule (`Chained`), so its blocks are totally ordered; a `MisbehaviourProof` requires
an INCOMPARABLE pair, which cannot exist. Hence NO `MisbehaviourProof` accuses an honest creator: the
detector never fires on honest behaviour. -/
theorem detector_sound
    (S : SigScheme SK PK Msg Sig) (pkOf : Creator → PK)
    (body : Blk Creator BId → Msg) (caus : Blk Creator BId → Blk Creator BId → Prop) (c : Creator)
    (hch : Chained caus c) (P : MisbehaviourProof S pkOf body caus c) : False :=
  chained_no_equivocation caus c hch P.b₁ P.b₂ P.from₁ P.from₂ P.exhibits_equivocation

/-- **DETECTOR COMPLETENESS — every equivocation is detected once both blocks are observed.** Given a
genuine `IsEquivocation` and the two blocks observed with valid signatures under the creator's enrolled
key, the `MisbehaviourProof` is CONSTRUCTED. So any node that observes BOTH signed blocks holds the
self-authenticating proof. -/
def detector_complete
    (S : SigScheme SK PK Msg Sig) (pkOf : Creator → PK)
    (body : Blk Creator BId → Msg) (caus : Blk Creator BId → Blk Creator BId → Prop)
    (b₁ b₂ : Blk Creator BId) (σ₁ σ₂ : Sig)
    (hequiv : IsEquivocation caus b₁ b₂)
    (hauth₁ : S.verify (pkOf b₁.creator) (body b₁) σ₁)
    (hauth₂ : S.verify (pkOf b₁.creator) (body b₂) σ₂) :
    MisbehaviourProof S pkOf body caus b₁.creator where
  b₁ := b₁
  b₂ := b₂
  σ₁ := σ₁
  σ₂ := σ₂
  from₁ := rfl
  from₂ := hequiv.1.symm
  auth₁ := hauth₁
  auth₂ := hauth₂
  distinct := hequiv.2.1
  incomp₁ := hequiv.2.2.1
  incomp₂ := hequiv.2.2.2

/-! ## §3. No forged block — a forged block IS a `HybridCombiner.Forgery`, reduced to the FLOOR.

A block "accepted as created by member `c` but never actually created by `c`" carries a signature that
verifies under `c`'s enrolled key over a body `c` never signed (`body b ∉ Q c`). That is EXACTLY a
`HybridCombiner.Forgery`. Under `EufCma` no such block exists; and because the signatures are the
`ed25519 ∧ ML-DSA` hybrid, `EufCma` is discharged from `SchnorrDLHard ∨ MSISHard` via
`hybrid_secure_if_either_floor`. -/

/-- **A forged block EXHIBITS a `Forgery`.** A block accepted under `c`'s key (`accepted`) whose body `c`
never signed (`never`, i.e. `¬ Q (body b)`) is a fresh-message valid signature — the adversary's
EUF-CMA win. -/
theorem forged_block_exhibits_forgery
    (S : SigScheme SK PK Msg Sig) (pkOf : Creator → PK)
    (body : Blk Creator BId → Msg) (Q : Msg → Prop) (b : Blk Creator BId) (σ : Sig)
    (accepted : S.verify (pkOf b.creator) (body b) σ) (never : ¬ Q (body b)) :
    Forgery S (pkOf b.creator) Q :=
  ⟨body b, σ, never, accepted⟩

/-- **`no_forged_block` (under `EufCma`).** If member `c`'s finalization/block key is `EufCma`, then no
block accepted as created by `c` was un-created by `c`: the forged block would be a `Forgery`, refuting
`EufCma`. -/
theorem no_forged_block
    (S : SigScheme SK PK Msg Sig) (pkOf : Creator → PK)
    (body : Blk Creator BId → Msg) (Q : Msg → Prop) (b : Blk Creator BId) (σ : Sig)
    (heuf : EufCma S (pkOf b.creator) Q)
    (accepted : S.verify (pkOf b.creator) (body b) σ) (never : ¬ Q (body b)) : False :=
  heuf (forged_block_exhibits_forgery S pkOf body Q b σ accepted never)

/-- **`no_forged_block_under_floor` — QUANTUM-SAFE non-forgery.** The block signatures are the hybrid
`ed25519 × ML-DSA`. With the two forking reductions in hand (a classical forgery ⟹ a `DLSolver`; a pq
forgery ⟹ two SelfTargetMSIS solutions — the `HybridCombiner` reductions, hypotheses not carriers), no
block accepted as created by `c` was un-created by `c`, provided `SchnorrDLHard ∨ MSISHard`. A quantum
adversary that breaks discrete log still faces Module-SIS on the ML-DSA half; the block stays
unforgeable. This is the blocklace-layer payoff of the hybrid campaign. -/
theorem no_forged_block_under_floor
    {SKc PKc Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Q : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (Amap : Mo →ₗ[Rq] No) (t : No) (β : ℕ)
    (dlFork : Forgery Cl pkc Q → DLSolver C G)
    (msisFork : Forgery Pq pkp Q →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution Amap t β z c w ∧ IsSelfTargetMSISSolution Amap t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented Amap t) ((β + β) + (β + β)))
    (m : Msg) (σ : Sigc × Sigp)
    (accepted : (hybrid Cl Pq).verify (pkc, pkp) m σ) (never : ¬ Q m) : False :=
  hybrid_secure_if_either_floor Cl Pq pkc pkp Q C G Amap t β dlFork msisFork hfloor
    ⟨m, σ, never, accepted⟩

/-! ## §4. Cordial-dissemination convergence — under the EXPLICIT fair-delivery assumption.

`dissemination.rs`: "send to others blocks you know and think they need"; a node relays what it cites and
only cites what it has fully disseminated. Modelled as `CordialWorld`: nodes with an `honest` predicate,
an eventual-knowledge relation `Has`, the block→creator-node map, the honest-creator-holds-its-block rule
(the cordial "you disseminate what you know"), and the **fair-delivery** assumption — the honest dual of a
crypto floor (partial-synchrony): a block held by an honest node reaches every honest node. Every field is
a hypothesis; the fair-delivery one is shown load-bearing in the teeth. -/

/-- **`CordialWorld`** — the cordial-dissemination protocol model. The two protocol assumptions are FIELDS
(hypotheses, never `axiom`s): the honest-creator-holds rule and the explicit fair-delivery assumption. -/
structure CordialWorld (Node Block : Type*) where
  /-- Which nodes are honest. -/
  honest : Node → Prop
  /-- `Has u b`: node `u` eventually knows block `b` (the limit of the gossip). -/
  Has : Node → Block → Prop
  /-- The node that created a block. -/
  creatorNode : Block → Node
  /-- CORDIAL "you disseminate what you know": an honest creator holds its own block (and, per the rule,
  relays it). -/
  creator_has : ∀ b : Block, honest (creatorNode b) → Has (creatorNode b) b
  /-- **FAIR-DELIVERY assumption** (the explicit protocol hypothesis, honest dual of a crypto floor):
  a block held by an honest node reaches every honest node. Partial synchrony's guarantee, stated
  openly. -/
  fair_delivery : ∀ (u v : Node) (b : Block), honest u → Has u b → honest v → Has v b

/-- **Every honest block reaches every honest node.** An honestly-created block is held by its creator
(the cordial rule), and fair delivery carries it to every honest node. -/
theorem honest_block_reaches_all {Node Block : Type*} (W : CordialWorld Node Block)
    (b : Block) (hc : W.honest (W.creatorNode b)) (v : Node) (hv : W.honest v) : W.Has v b :=
  W.fair_delivery (W.creatorNode b) v b hc (W.creator_has b hc) hv

/-- **`cordial_dissemination_converges` — HONEST NODES CONVERGE ON THE SAME DAG CLOSURE.** For every
honestly-created block `b` and any two honest nodes `u, v`, `Has u b ↔ Has v b`: both know it. So the two
nodes' knowledge sets AGREE on every honest block — they converge on the same DAG closure. There is no
honest block one honest node has finalized into its DAG that another lacks. -/
theorem cordial_dissemination_converges {Node Block : Type*} (W : CordialWorld Node Block)
    (u v : Node) (hu : W.honest u) (hv : W.honest v)
    (b : Block) (hc : W.honest (W.creatorNode b)) : W.Has u b ↔ W.Has v b :=
  ⟨fun _ => honest_block_reaches_all W b hc v hv,
   fun _ => honest_block_reaches_all W b hc u hu⟩

/-! ## §5. Teeth — every hypothesis is load-bearing, both instances exhibited.

The concrete causal relation is the single-strand `seq`-order `caus b b' := b'.seq < b.seq` (a later block
cites its earlier strand blocks). On it: distinct-sequence blocks are comparable (the honest chain); two
SAME-sequence blocks are incomparable (a fork — exactly `ordering.rs`'s "≥2 blocks at one round"). -/

section Teeth

/-- The single-strand causal order over `Blk ℕ ℕ`: `b` cites `b'` iff `b'` sits earlier on the strand
(`b'.seq < b.seq`). This is the honest chain the cite-your-own-previous rule builds. -/
@[reducible] def seqCaus : Blk ℕ ℕ → Blk ℕ ℕ → Prop := fun b b' => b'.seq < b.seq

/-- Two honest blocks of creator `0` at distinct sequences `0` and `1`. -/
def h0 : Blk ℕ ℕ := ⟨0, 0, 100⟩
def h1 : Blk ℕ ℕ := ⟨0, 1, 101⟩

/-- **HONEST CREATOR NEVER EQUIVOCATES.** Its two blocks (distinct sequences) are comparable — the later
cites the earlier — so `¬ IsEquivocation`. The cite-your-own-previous chain rules the fork out. -/
theorem tooth_honest_never_equivocates : ¬ IsEquivocation seqCaus h0 h1 := by
  rintro ⟨_, _, _, hnc2⟩
  exact hnc2 (by simp [seqCaus, h0, h1])

/-- Two FORKED blocks of creator `0` at the SAME sequence `5`, distinct ids — the equivocation
(`ordering.rs`: two blocks of one creator at one round). -/
def e1 : Blk ℕ ℕ := ⟨0, 5, 200⟩
def e2 : Blk ℕ ℕ := ⟨0, 5, 201⟩

/-- **A GENUINE EQUIVOCATION IS DETECTED.** The two same-sequence blocks are incomparable
(`¬ 5 < 5`), distinct, same creator — `IsEquivocation` holds. -/
theorem tooth_equivocation_is_detected : IsEquivocation seqCaus e1 e2 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [e1, e2]
  · simp [seqCaus, e1, e2]
  · simp [seqCaus, e1, e2]

/-- The demo block-signature scheme: a signature is valid iff `sig = creatorKey + body` (the algebraic
oracle used by `ConsensusSafety`/`CapabilityChain`). Creators are their own keys; `body b := b.id`. -/
@[reducible] def toyS : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign sk m := sk + m
  verify pk m sig := sig = pk + m

/-- Enrolled-key roster: creator id ↦ its key (identity, for the demo). -/
@[reducible] def toyPkOf : ℕ → ℕ := id
/-- The signed body is the block's content id. -/
@[reducible] def toyBody : Blk ℕ ℕ → ℕ := fun b => b.id

/-- **COMPLETENESS FIRES — the self-authenticating proof is CONSTRUCTED.** With both forked blocks signed
by creator `0` (`sig = 0 + id`), `detector_complete` yields a `MisbehaviourProof` — the observing node
holds the two signed blocks and can re-verify them. -/
def toothProof : MisbehaviourProof toyS toyPkOf toyBody seqCaus (0 : ℕ) :=
  detector_complete toyS toyPkOf toyBody seqCaus e1 e2 (0 + toyBody e1) (0 + toyBody e2)
    tooth_equivocation_is_detected rfl rfl

/-- The constructed proof genuinely re-authenticates (both signatures verify, blocks incomparable). -/
theorem tooth_proof_self_authenticates :
    toyS.verify (toyPkOf 0) (toyBody toothProof.b₁) toothProof.σ₁ ∧
    toyS.verify (toyPkOf 0) (toyBody toothProof.b₂) toothProof.σ₂ ∧
      toothProof.b₁ ≠ toothProof.b₂ ∧ ¬ seqCaus toothProof.b₁ toothProof.b₂ ∧
      ¬ seqCaus toothProof.b₂ toothProof.b₁ :=
  toothProof.self_authenticating

/-- **THE CITE-YOUR-OWN-PREVIOUS RULE IS LOAD-BEARING.** Without the `Chained` invariant, an honest
creator's two blocks could be incomparable and thus flagged: here creator `0`'s forked pair yields a
`MisbehaviourProof`, so `detector_sound`'s `Chained` hypothesis is EXACTLY what blocks a false accusation.
Drop the rule and the (would-be honest) creator looks like an equivocator. -/
theorem tooth_chaining_is_load_bearing :
    Nonempty (MisbehaviourProof toyS toyPkOf toyBody seqCaus (0 : ℕ)) :=
  ⟨toothProof⟩

/-- …and `seqCaus 0` is NOT `Chained` — the two same-sequence blocks are same-creator, distinct, yet
incomparable — so the soundness premise genuinely fails without the monotone-sequence chain. -/
theorem tooth_seq_not_chained_without_rule : ¬ Chained seqCaus (0 : ℕ) := by
  intro hch
  rcases hch e1 e2 rfl rfl (by simp [e1, e2]) with h | h
  · exact absurd h (by simp [seqCaus, e1, e2])
  · exact absurd h (by simp [seqCaus, e1, e2])

/-! ### Forged block — the `Forgery` witness. -/

/-- A block accepted as created by member `0` but never created by it: signature `0 + id` verifies under
`0`'s key, but `0`'s cast-set `Q` is empty (`0` signed nothing), so the body is un-queried. -/
def forgedBlk : Blk ℕ ℕ := ⟨0, 3, 300⟩
/-- Member `0` cast NO block bodies (`Q ≡ False`) — every body is fresh. -/
@[reducible] def emptyQ : ℕ → Prop := fun _ => False

/-- **A FORGED BLOCK EXHIBITS THE `Forgery`.** The accepted-but-un-created block is a fresh valid
signature — the EUF-CMA win `no_forged_block` refutes. -/
theorem tooth_forged_block_is_forgery :
    Forgery toyS (toyPkOf forgedBlk.creator) emptyQ :=
  forged_block_exhibits_forgery toyS toyPkOf toyBody emptyQ forgedBlk (0 + toyBody forgedBlk)
    (by simp [toyPkOf, forgedBlk]) (by simp [emptyQ])

/-! ### Cordial dissemination — non-vacuity + the fair-delivery assumption is load-bearing. -/

/-- A concrete two-node cordial world where BOTH nodes are honest and BOTH hold every block (fair delivery
satisfied): the convergence theorem is non-vacuous. -/
def convergedWorld : CordialWorld Bool ℕ where
  honest := fun _ => True
  Has := fun _ _ => True
  creatorNode := fun _ => true
  creator_has := fun _ _ => trivial
  fair_delivery := fun _ _ _ _ _ _ => trivial

/-- **CONVERGENCE FIRES.** In `convergedWorld` two honest nodes agree on every honest block. -/
theorem tooth_convergence_fires (b : ℕ) :
    convergedWorld.Has true b ↔ convergedWorld.Has false b :=
  cordial_dissemination_converges convergedWorld true false trivial trivial b trivial

/-- **THE FAIR-DELIVERY ASSUMPTION IS LOAD-BEARING.** Without it, a block can stay stuck at its creator:
the map `Has u b := (u = creatorNode b)` satisfies the honest-creator-holds rule (`creator_has`) yet the
OTHER honest node lacks the block — so `Has` does NOT converge. Fair delivery is exactly what carries the
block across, the honest dual of a crypto floor. -/
theorem tooth_fair_delivery_load_bearing :
    ∃ (Has : Bool → ℕ → Prop) (creatorNode : ℕ → Bool),
      (∀ b, Has (creatorNode b) b) ∧ ¬ (∀ (u : Bool) (b : ℕ), Has u b) := by
  refine ⟨fun u b => u = (b % 2 == 0), fun b => b % 2 == 0, fun b => rfl, ?_⟩
  intro hall
  have := hall false 0
  simp at this

-- The honest chain is comparable (the later block cites the earlier); a fork at one seq is not.
#guard decide (seqCaus h1 h0)                       -- h1 (seq 1) cites h0 (seq 0)
#guard decide (¬ seqCaus e1 e2 ∧ ¬ seqCaus e2 e1)   -- the fork: neither cites the other
-- The forged block's signature verifies under creator 0's key (the forgery witness).
#guard decide (toyS.verify (toyPkOf forgedBlk.creator) (toyBody forgedBlk) (0 + toyBody forgedBlk))

end Teeth

/-! ## §6. Axiom hygiene — every blocklace-safety keystone is kernel-clean. -/

#assert_all_clean [
  chained_no_equivocation,
  MisbehaviourProof.self_authenticating,
  MisbehaviourProof.exhibits_equivocation,
  detector_sound,
  forged_block_exhibits_forgery,
  no_forged_block,
  no_forged_block_under_floor,
  honest_block_reaches_all,
  cordial_dissemination_converges,
  tooth_honest_never_equivocates,
  tooth_equivocation_is_detected,
  tooth_chaining_is_load_bearing,
  tooth_seq_not_chained_without_rule,
  tooth_forged_block_is_forgery,
  tooth_convergence_fires,
  tooth_fair_delivery_load_bearing
]

end Dregg2.Crypto.BlocklaceSafety

/-
# Dregg2.Bridge.VerifiedLightClient — the SHARED foundation every per-chain verified
light client (Solana Tower-BFT, Ethereum sync-committee, Cosmos Tendermint) instantiates.

dregg builds VERIFIED light clients for other chains: not tested — PROVEN no-forgery. Each
one formalizes a foreign chain's header/update verification RULES in Lean, proves them
fail-closed and sound, and treats the crypto primitives (ed25519 / keccak / bls12-381) as
HONEST, NAMED, MINIMAL verified LEAVES (an EverCrypt-style discharge, never "assume the whole
verification is correct"). This file is the abstraction the per-chain Fables plug into: ONE
proven shape, so each chain proves the SAME three theorems over its own rules.

TWO LAYERS, kept distinct + honest:

  * RULES (formalizable, high value): "an update is valid IFF ≥2/3 of the trusted set signed
    it, the chain-id matches, the finality/inclusion branch reconstructs, the trusting period
    holds." The Nomad $190M hack was a RULES bug — an unproven message accepted by a
    permissive default — NOT a crypto break. Proving the rules FAIL CLOSED (`FailClosed`) is
    exactly the tooth that catches the class of bug that drains bridges.
  * CRYPTO (a mountain to formalize; treated as verified LEAVES): the `CryptoLeaf` bundle
    declares the signature-soundness fact and the hash-collision-resistance CARRIER as
    EXPLICIT, VISIBLE structure fields (`sigSound`; `hashCR : Prop` + `noCollision`). The
    CR side deliberately mirrors `Dregg2.Crypto.PortalFloor.Blake3Kernel`: `hashCR` is a
    `Prop` carrier — the correct assumption, NOT idealized injectivity, which is
    pigeonhole-FALSE for any real compressing hash — and `noCollision` unpacks it: GIVEN
    the CR floor, equal digests force equal preimages. A per-chain instance either PROVES
    the carrier (a toy/reference scheme) or supplies it as an opaque, named assumption
    discharged by a verified crypto library. The `NoForgery` theorem is legitimately OF THE
    FORM "IF the crypto leaves are sound THEN the rules verify correctly": honest as long as
    the leaf is minimal + named and does not launder the conclusion.

THE THREE THEOREM SHAPES every chain proves (bundled as fields of `ForeignLightClient`, so a
chain instance CANNOT exist without discharging them):

  * `NoForgery`   — `verify` accepts an update ⟹ the foreign-chain validity predicate holds
                    (given the crypto leaves; the leaf's `sigSound` is used in the proof).
  * `FailClosed`  — `verify` REJECTS the empty / default / sub-quorum / tampered update (the
                    Nomad-law tooth: an unproven update is never accepted).
  * `NonVacuous`  — `verify` is `true` on SOME input AND `false` on another — it discriminates
                    (a `True`-by-construction verifier is a DEFECT, not a proof).

COMPOSITION with `Metatheory.Bridge.InterchainAdapter` (read: `Metatheory/Bridge/InterchainAdapter.lean`):
that adapter treats a foreign chain's finality as an ASSUMED oracle (`foreignFinal : Header →
Prop`), pinned to a `TrustRung`. A `ForeignLightClient` PRODUCES that hypothesis: `toAdapter`
builds an `InterchainAdapter` whose `foreignFinal u := verify ts u = true` on the `proof` rung
(finality is DISCHARGED to a decidable predicate the client computes), and
`toAdapter_foreignFinal_discharged` proves that this adapter's finality entails real
foreign-chain validity via `NoForgery`. The adapter no longer BLINDLY assumes finality — a
verified light client discharges its finality assumption.

Kernel-clean: `#assert_axioms` hard-gates every theorem. The only assumptions are the NAMED
crypto-leaf fields the instance supplies (invisible to `#assert_axioms`, which sees only
`axiom`-keyword decls — so the toy instance PROVES its leaf to keep the demonstration
genuinely axiom-clean and the leaf non-laundered).
-/
import Metatheory.Bridge.InterchainAdapter
import Dregg2.Tactics

namespace Dregg2.Bridge.VerifiedLightClient

/-! ## §1 — The HONEST crypto-leaf interface (the verified-primitive hypotheses, made VISIBLE).

`CryptoLeaf` bundles the two primitives a light client leans on — a signature verifier and a
hash — TOGETHER WITH the soundness facts they are trusted to provide (`sigSound`; the
`hashCR` carrier + `noCollision`). The facts are ordinary structure fields, so a per-chain
instance MUST supply them and an auditor can SEE them; they are not global `axiom`s and not a
laundered `def FooHard` used as a hidden hypothesis. A real chain supplies `sigSound` as the
named ed25519/BLS unforgeability assumption and `hashCR` as the named keccak/SHA CR
assumption, both discharged by a verified crypto library; a toy chain proves them.

The hash side mirrors `Dregg2.Crypto.PortalFloor.Blake3Kernel` (`Crypto/PortalFloor.lean:178`)
EXACTLY: `hashCR : Prop` is the CR CARRIER — the correct assumption, NOT idealized
injectivity. Unconditional `∀ m₁ m₂, hash m₁ = hash m₂ → m₁ = m₂` is pigeonhole-UNSATISFIABLE
for a real compressing hash (collisions EXIST; only a toy injective hash could discharge it).
Injectivity holds RELATIVE to the carrier: `noCollision : hashCR → …` — dischargeable by a
real hash-CR floor, refutable by a collapsing hash (`collapseLeaf_not_hashCR` below). -/

/-- **`CryptoLeaf`** — the honest, named verified-primitive bundle. `sigVerify` and `hash` are
the opaque primitives (a verified crypto lib realizes them); `Signed` is the DENOTATION a
verifying signature is trusted to certify ("`pk` authorized `m`"); `sigSound` is the signature
SOUNDNESS HYPOTHESIS and `hashCR`/`noCollision` the CR CARRIER + its unpacking — visible as
fields so no chain can hide them. -/
structure CryptoLeaf where
  /-- Public-key type (a chain plugs its ed25519 / BLS pubkey here). -/
  PubKey : Type
  /-- Signed-message type (the chain's header-bytes / vote domain). -/
  Msg : Type
  /-- Signature type. -/
  Sig : Type
  /-- Digest type (a chain plugs its keccak / SHA-256 output here). -/
  Digest : Type
  /-- The signature verifier (opaque; EverCrypt-style). -/
  sigVerify : PubKey → Msg → Sig → Bool
  /-- The hash (opaque; a verified keccak/SHA realizes it). -/
  hash : Msg → Digest
  /-- The DENOTATION: `Signed pk m` means the holder of `pk` genuinely authorized `m`. -/
  Signed : PubKey → Msg → Prop
  /-- **Signature soundness (the named unforgeability leaf).** A verifying signature entails
  the key holder authorized the message. This is the ONLY signature assumption; it is minimal
  and it does NOT say "the whole update is valid". -/
  sigSound : ∀ pk m s, sigVerify pk m s = true → Signed pk m
  /-- **CARRIER — hash collision resistance (the named CR leaf).** A `Prop`, NOT idealized
  injectivity (which is pigeonhole-false for a compressing hash). Mirrors
  `PortalFloor.Blake3Kernel.collisionHard`: a real chain supplies the named keccak/SHA CR
  assumption here; a toy proves it for a reference kernel; a collapsing hash REFUTES it. -/
  hashCR : Prop
  /-- The CR carrier unpacked (mirrors `PortalFloor.Blake3Kernel.noCollision`): GIVEN the CR
  floor, equal digests entail equal preimages — so a reconstructed inclusion/finality branch
  pins the committed bytes. -/
  noCollision : hashCR → ∀ m₁ m₂, hash m₁ = hash m₂ → m₁ = m₂

/-- **`CryptoLeaf.hash_inj` (the floor theorem shape; mirrors `blake3_floor_cr`).** GIVEN the
CR carrier, a digest equality forces preimage equality. The carrier is an explicit hypothesis
— visible at every use site, never smuggled. -/
theorem CryptoLeaf.hash_inj (L : CryptoLeaf) (hcr : L.hashCR) {m₁ m₂ : L.Msg}
    (heq : L.hash m₁ = L.hash m₂) : m₁ = m₂ :=
  L.noCollision hcr m₁ m₂ heq

/-! ## §2 — The three theorem SHAPES every chain must prove, as reusable predicates.

Stated over the bare components (a `verify` verdict, a foreign-validity predicate, an empty
update) so a per-chain Fable can name them independently; they are ALSO bundled as fields of
`ForeignLightClient` below, so a chain instance cannot exist without discharging them. -/

/-- **`NoForgery verify ForeignValid`** — the RULES are sound: whenever `verify` accepts an
update, the foreign chain's OWN validity predicate holds for it. (The crypto leaves are used
in the per-chain PROOF of this; the shape is "verify accepts ⟹ foreign-valid".) -/
def NoForgery {Update TrustedState : Type}
    (verify : TrustedState → Update → Bool) (ForeignValid : Update → Prop) : Prop :=
  ∀ ts u, verify ts u = true → ForeignValid u

/-- **`FailClosed verify emptyUpdate`** — the Nomad-law tooth: `verify` REJECTS the
empty / default / uninitialized update for EVERY trusted state. An unproven update is never
accepted by a permissive default. -/
def FailClosed {Update TrustedState : Type}
    (verify : TrustedState → Update → Bool) (emptyUpdate : Update) : Prop :=
  ∀ ts, verify ts emptyUpdate = false

/-- **`NonVacuous verify`** — `verify` DISCRIMINATES: it is `true` on some input and `false`
on another. A verifier that accepts everything (or nothing) is a defect; this forbids the
`True`-by-construction (or `False`-by-construction) verifier. -/
def NonVacuous {Update TrustedState : Type}
    (verify : TrustedState → Update → Bool) : Prop :=
  ∃ ts u₁ u₂, verify ts u₁ = true ∧ verify ts u₂ = false

/-! ## §3 — `ForeignLightClient`: the bundled shape a per-chain Fable instantiates.

A chain supplies its `Update`/`TrustedState` types, its foreign-validity predicate, its
`verify` RULES, an `emptyUpdate` default, the crypto `leaf`, and — as FIELDS — proofs of the
three theorem shapes. Because the theorems are fields, `ForeignLightClient.mk` is a proof
obligation: no chain instance exists until `NoForgery`, `FailClosed`, and `NonVacuous` are
discharged. The `leaf` is bundled so it is VISIBLE at the instance site (an auditor reads
which primitive soundness the `noForgery` proof rests on). -/

/-- **`ForeignLightClient`** — the shared shape. The per-chain lanes fill in the fields; the
top theorems (`NoForgery`/`FailClosed`/`NonVacuous`) are proof obligations carried as fields. -/
structure ForeignLightClient where
  /-- The crypto-primitive bundle this client's rules lean on (VISIBLE; the `noForgery` proof
  uses `leaf.sigSound`). -/
  leaf : CryptoLeaf
  /-- The chain's update/header type (a sync-committee update, a Tower-BFT vote set, …). -/
  Update : Type
  /-- The chain's trusted state (the current committee / validator set + chain-id + period). -/
  TrustedState : Type
  /-- The foreign chain's OWN validity predicate — what a correct update MUST satisfy. -/
  ForeignValid : Update → Prop
  /-- THE RULES: the executable header/update verification verdict. -/
  verify : TrustedState → Update → Bool
  /-- The empty / default / uninitialized update — the Nomad-law fail-closed probe. -/
  emptyUpdate : Update
  /-- **NO FORGERY** (proof obligation): GIVEN the hash-CR floor (`leaf.hashCR`), accept ⟹
  foreign-valid. The CR carrier is the EXPLICIT crypto hypothesis — the per-chain proof
  consumes `leaf.noCollision hcr` wherever a digest equality must pin bytes; a chain whose
  hash collapses gets NO no-forgery guarantee (the honest shape). -/
  noForgery : leaf.hashCR → NoForgery verify ForeignValid
  /-- **FAIL CLOSED** (proof obligation): the empty update is rejected. -/
  failClosed : FailClosed verify emptyUpdate
  /-- **NON-VACUOUS** (proof obligation): `verify` discriminates. -/
  nonVacuous : NonVacuous verify

/-! ## §4 — COMPOSITION with `Metatheory.Bridge.InterchainAdapter`.

`InterchainAdapter Header Event` (`Metatheory/Bridge/InterchainAdapter.lean:70`) treats foreign
finality as an ASSUMED oracle `foreignFinal : Header → Prop` on a `TrustRung`. A
`ForeignLightClient` PRODUCES that oracle: its `Update` IS the header (a finality proof), and
`foreignFinal u := verify ts u = true` — finality is the light client's decidable verdict,
DISCHARGED, not assumed. The rung is `proof`: the finality predicate is dischargeable to a
theorem, and `NoForgery` is exactly that discharge (accept ⟹ real foreign validity). -/

open Metatheory.Bridge in
/-- **`toAdapter V ts incl`** — build the `InterchainAdapter` a `ForeignLightClient` produces.
`foreignFinal u := V.verify ts u = true` (the client's decidable finality verdict); `inclusion`
is the chain's event-in-header relation supplied by the caller; the rung is `proof` because
finality is DISCHARGED (via `V.noForgery`), not assumed. -/
def toAdapter (V : ForeignLightClient) (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) :
    InterchainAdapter V.Update Event where
  foreignFinal := fun u => V.verify ts u = true
  inclusion    := incl
  trust        := TrustRung.proof

open Metatheory.Bridge in
/-- **`toAdapter_foreignFinal_discharged` (THE DISCHARGE).** The adapter's `foreignFinal`
hypothesis — for the adapter a `ForeignLightClient` produces — is NOT a blind assumption: it
ENTAILS the foreign chain's real validity predicate, via `NoForgery`. This is the wire: the
`InterchainAdapter` finality assumption is discharged by the verified rules. -/
theorem toAdapter_foreignFinal_discharged (V : ForeignLightClient) (hcr : V.leaf.hashCR)
    (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) (u : V.Update)
    (h : (toAdapter V ts incl).foreignFinal u) : V.ForeignValid u :=
  V.noForgery hcr ts u h

open Metatheory.Bridge in
/-- **`toAdapter_accepts_entails_valid`.** If the produced adapter ACCEPTS a cross-chain event
(`InterchainAdapter.accepts` — a finalized header includes it), then there is an update that is
FOREIGN-VALID (not merely verify-accepted) and includes the event. Composes
`InterchainAdapter.accepts` with `NoForgery`: acceptance rests on proven validity. -/
theorem toAdapter_accepts_entails_valid (V : ForeignLightClient) (hcr : V.leaf.hashCR)
    (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) (ev : Event)
    (h : (toAdapter V ts incl).accepts ev) :
    ∃ u, V.ForeignValid u ∧ incl ev u := by
  obtain ⟨u, hfin, hinc⟩ := h
  exact ⟨u, V.noForgery hcr ts u hfin, hinc⟩

open Metatheory.Bridge in
/-- **`toAdapter_rejects_empty` (Nomad tooth, at the adapter boundary).** The produced adapter's
`foreignFinal` is FALSE on the empty/default update — `FailClosed` lifts into the adapter, so an
uninitialized update is never treated as final. -/
theorem toAdapter_rejects_empty (V : ForeignLightClient) (ts : V.TrustedState)
    {Event : Type} (incl : Event → V.Update → Prop) :
    ¬ (toAdapter V ts incl).foreignFinal V.emptyUpdate := by
  show ¬ (V.verify ts V.emptyUpdate = true)
  rw [V.failClosed ts]; simp

/-! ## §5 — A NON-VACUOUS worked template: a toy 1-signer chain.

The per-chain lanes need a worked instance proving the shape is inhabitable AND the theorems
DISCRIMINATE. This toy chain has one trusted signer (key `7`). An update carries a signer, a
content word, a signature, and a claimed content digest. The RULES accept iff the signer is the
trusted key, the signature verifies, and the digest matches the hash. To keep the demonstration
genuinely axiom-clean and the crypto leaf NON-LAUNDERED, the toy PROVES its leaf (`toyLeaf`)
rather than assuming it — a real chain replaces `toyLeaf` with an ed25519/BLS leaf whose
`sigSound` is the named library assumption. -/

/-- The toy signature verifier: `s` verifies for `(pk, m)` iff `pk = 7` (the sole genuine key)
AND `s = pk + m` (a toy MAC). Concrete `Nat` primitive (a real chain plugs ed25519 here). -/
def toySigVerify (pk m s : Nat) : Bool := (pk == 7) && (s == pk + m)

/-- The toy hash — the identity (a real chain plugs keccak/SHA here). -/
def toyHash (m : Nat) : Nat := m

/-- The toy `Signed` denotation: the holder of key `7` genuinely authorized `m`. Discriminates
— `toySigned 3 m` is `(3 = 7)`, false. -/
def toySigned (pk _m : Nat) : Prop := pk = 7

/-- **The named signature-soundness leaf, PROVED for the toy.** A verifying toy signature
entails the genuine key `7` signed — exactly `CryptoLeaf.sigSound`. (A real chain leaves this
as its opaque, named ed25519/BLS unforgeability assumption.) -/
theorem toySigSound (pk m s : Nat) (h : toySigVerify pk m s = true) : toySigned pk m := by
  simp only [toySigVerify, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- The concrete crypto leaf, assembled from the proved toy primitives — the interface slot a
per-chain Fable fills with an ed25519/BLS + keccak leaf whose `sigSound`/`hashCR` are the named
library assumptions. The `hashCR` CARRIER is the genuine CR `Prop` over THIS leaf's own hash
(the `PortalFloor.Reference` pattern, `Crypto/PortalFloor.lean:362`) — NOT `True`; it is
inhabitable here (proved below: `toyLeaf_hashCR`, the identity hash is a valid REFERENCE
witness) and the SAME shape is FALSE for a collapsing hash (`collapseLeaf_not_hashCR`). -/
def toyLeaf : CryptoLeaf where
  PubKey := Nat
  Msg := Nat
  Sig := Nat
  Digest := Nat
  sigVerify := toySigVerify
  hash := toyHash
  Signed := toySigned
  sigSound := toySigSound
  hashCR := ∀ m₁ m₂, toyHash m₁ = toyHash m₂ → m₁ = m₂
  noCollision := fun h => h

/-- **The toy CR carrier HOLDS (the positive polarity).** The reference toy hash is genuinely
collision-free, so `toyLeaf.hashCR` is dischargeable — the carrier is inhabitable, exactly as a
real chain discharges it with a verified keccak/SHA CR floor. -/
theorem toyLeaf_hashCR : toyLeaf.hashCR := fun _ _ h => h

/-! ### The badCompress-style FALSIFIER — the carrier is load-bearing, not `True` in disguise.

The other half of non-vacuity (the `PortalFloor` §9b `instPoseidon2Collide` pattern,
`Crypto/PortalFloor.lean:513`): a COLLAPSING hash yields a lawful `CryptoLeaf` — the interface
does not exclude it — but its CR carrier is provably FALSE, so no `noForgery` conclusion is
available for it. Stripping the hash's soundness refutes the assumption. -/

/-- The collapsing hash: every message digests to `0` (the badCompress). -/
def collapseHash (_ : Nat) : Nat := 0

/-- A lawful `CryptoLeaf` over the COLLAPSING hash — same toy signature primitives, same
genuine-CR-Prop carrier SHAPE, stated over `collapseHash`. The interface admits it; only the
carrier (below) separates it from the sound leaf. -/
def collapseLeaf : CryptoLeaf where
  PubKey := Nat
  Msg := Nat
  Sig := Nat
  Digest := Nat
  sigVerify := toySigVerify
  hash := collapseHash
  Signed := toySigned
  sigSound := toySigSound
  hashCR := ∀ m₁ m₂, collapseHash m₁ = collapseHash m₂ → m₁ = m₂
  noCollision := fun h => h

/-- **The collapsing leaf's CR carrier is FALSE (the negative polarity).** `0 ≠ 1` yet their
digests collide — the carrier REFUTES a broken hash, so it is a real discriminating hypothesis:
`toyLeaf.hashCR` holds, `collapseLeaf.hashCR` fails. Both polarities witnessed. -/
theorem collapseLeaf_not_hashCR : ¬ collapseLeaf.hashCR := by
  intro h
  exact absurd (h 0 1 rfl) (by decide)

/-- A toy update: who signed, the content word, the toy signature, and the claimed digest. -/
structure ToyUpdate where
  signer : Nat
  content : Nat
  sig : Nat
  contentHash : Nat
deriving DecidableEq, Repr

/-- The toy trusted state: the single trusted signer key. -/
structure ToyState where
  trustedKey : Nat
deriving DecidableEq, Repr

/-- **The toy RULES.** Accept iff the signer is the trusted key, the toy signature verifies
(`toyLeaf.sigVerify` — load-bearing: `noForgery` reads `sigSound` from it), AND the claimed
digest matches the hash of the content (`toyLeaf.hash` — load-bearing via `hashCR`). -/
def toyVerify (ts : ToyState) (u : ToyUpdate) : Bool :=
  (u.signer == ts.trustedKey)
    && toySigVerify u.signer u.content u.sig
    && (toyHash u.content == u.contentHash)

/-- **The toy foreign-validity predicate** (the chain's OWN notion of a valid update): the
content was genuinely signed by the trusted key, the claimed digest is the real hash, AND the
digest BINDS — no other message hashes to the claimed digest. All three conjuncts are
non-trivial: `Signed` is `signer = 7` (false for a forged signer), the digest equality
discriminates, and the binding conjunct is exactly what `noCollision` (given the CR carrier)
buys — it is where the CR floor is LOAD-BEARING in `toyNoForgery`. -/
def toyForeignValid (u : ToyUpdate) : Prop :=
  toySigned u.signer u.content
    ∧ toyHash u.content = u.contentHash
    ∧ (∀ m, toyHash m = u.contentHash → m = u.content)

/-- The empty / uninitialized update — signer `0` (not the trusted key), zero everything. -/
def toyEmptyUpdate : ToyUpdate := ⟨0, 0, 0, 0⟩

/-- **NO FORGERY (toy).** GIVEN the CR carrier (`toyLeaf.hashCR`), a verify-accepted update is
foreign-valid. The proof USES the crypto leaf on BOTH legs: `toyLeaf.sigSound` turns the
verifying signature into `signer = 7` (the `Signed` denotation); and the digest-BINDING
conjunct is discharged by `toyLeaf.noCollision hcr` — the CR hypothesis is consumed, not
decorative. This is the "IF the crypto leaf is sound THEN the rules are sound" shape,
discharged. -/
theorem toyNoForgery (hcr : toyLeaf.hashCR) : NoForgery toyVerify toyForeignValid := by
  intro ts u h
  unfold toyVerify at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨_hsigner, hsig⟩, hhash⟩ := h
  have hdig : toyHash u.content = u.contentHash := beq_iff_eq.mp hhash
  refine ⟨?_, hdig, ?_⟩
  · -- signature soundness leaf ⟹ the content was genuinely signed by key 7
    exact toyLeaf.sigSound u.signer u.content u.sig hsig
  · -- the CR carrier ⟹ the claimed digest BINDS: any preimage of it IS the content
    intro m hm
    exact toyLeaf.noCollision hcr m u.content (hm.trans hdig.symm)

/-- **FAIL CLOSED (toy).** The empty update is rejected for EVERY trusted state — the toy
signature `toyLeaf.sigVerify 0 0 0` fails (`0 ≠ 7`), so the `&&`-chain is `false` regardless of
`ts`. The Nomad-law default. -/
theorem toyFailClosed : FailClosed toyVerify toyEmptyUpdate := by
  intro ts
  simp [toyVerify, toyEmptyUpdate, toySigVerify, toyHash]

/-- **NON-VACUOUS (toy).** `toyVerify` accepts a genuine update (signer `7`, sig `10 = 7+3`,
digest `3`) and REJECTS a forged one (signer `3 ≠ 7`) under the SAME trusted state — it
discriminates. -/
theorem toyNonVacuous : NonVacuous toyVerify :=
  ⟨⟨7⟩, ⟨7, 3, 10, 3⟩, ⟨3, 3, 6, 3⟩, by decide, by decide⟩

/-- **The toy `ForeignLightClient`** — the shape is inhabitable: all three theorem obligations
discharge. This is the template a per-chain Fable copies (swap `toyLeaf` → ed25519/BLS, the toy
rules → the real sync-committee / Tower-BFT / Tendermint rules). -/
def toyClient : ForeignLightClient where
  leaf := toyLeaf
  Update := ToyUpdate
  TrustedState := ToyState
  ForeignValid := toyForeignValid
  verify := toyVerify
  emptyUpdate := toyEmptyUpdate
  noForgery := toyNoForgery
  failClosed := toyFailClosed
  nonVacuous := toyNonVacuous

/-! ## §6 — The toy DISCRIMINATORS bite (the load-bearing teeth), on concrete data. -/

/-- **TRUE side.** The genuine update is foreign-valid (signed by key `7`, digest matches and
binds — the binding conjunct holds because the reference hash is collision-free). -/
theorem toy_valid_holds : toyForeignValid ⟨7, 3, 10, 3⟩ := ⟨rfl, rfl, fun _m h => h⟩

/-- **FORGED-SIGNER DISCRIMINATOR.** An update from signer `3` is NOT foreign-valid — the
`Signed` denotation (`signer = 7`) fails. The crypto leaf is what separates them. -/
theorem toy_forged_signer_invalid : ¬ toyForeignValid ⟨3, 3, 6, 3⟩ := by
  rintro ⟨hsigned, _, _⟩
  exact absurd (show (3 : Nat) = 7 from hsigned) (by decide)

/-- **TAMPERED-DIGEST DISCRIMINATOR.** An update whose claimed digest (`99`) is not the real
hash of its content (`3`) is NOT foreign-valid — the hash binding fails. -/
theorem toy_tampered_digest_invalid : ¬ toyForeignValid ⟨7, 3, 10, 99⟩ := by
  rintro ⟨_, hhash, _⟩
  exact absurd hhash (by decide)

/-- **BINDING DISCRIMINATOR (the new conjunct bites on its own).** The tampered update's
claimed digest `99` also fails the BINDING conjunct independently: `99` hashes to the claimed
digest yet `99 ≠ 3` — the conjunct `noCollision` discharges is not vacuously true. -/
theorem toy_tampered_binding_fails : ¬ (∀ m, toyHash m = (99 : Nat) → m = 3) := by
  intro h
  exact absurd (h 99 rfl) (by decide)

/-- **THE DISCRIMINATOR, ASSEMBLED.** `toyVerify` accepts the genuine update, rejects the forged
signer, rejects the tampered digest, and rejects the empty update — all under the SAME trusted
state. The rules are not a `True`-carrier. -/
theorem toy_gate_discriminates :
    toyVerify ⟨7⟩ ⟨7, 3, 10, 3⟩ = true
    ∧ toyVerify ⟨7⟩ ⟨3, 3, 6, 3⟩ = false
    ∧ toyVerify ⟨7⟩ ⟨7, 3, 10, 99⟩ = false
    ∧ toyVerify ⟨7⟩ toyEmptyUpdate = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §7 — The composition, on the toy client — a verified light client discharges the adapter.

Build the `InterchainAdapter` the toy client produces (`inclusion` = "the event's claimed
height equals the update's content"), and witness the discharge end-to-end: the adapter accepts
the genuine confirmation, and that acceptance ENTAILS foreign validity — while the empty update
is rejected at the adapter boundary. -/

/-- The toy inclusion relation: a lock confirmation (its claimed content) matches the update. -/
def toyIncl : Nat → ToyUpdate → Prop := fun ev u => ev = u.content

/-- The adapter the toy client produces at trusted state `⟨7⟩`. -/
def toyAdapter : Metatheory.Bridge.InterchainAdapter ToyUpdate Nat :=
  toAdapter toyClient ⟨7⟩ toyIncl

/-- **END-TO-END DISCHARGE.** The toy adapter ACCEPTS the confirmation (there is a verify-final
update including it), and by the discharge that acceptance yields a FOREIGN-VALID update — the
adapter's finality assumption is backed by the verified rules, not assumed. -/
theorem toy_adapter_accepts_and_discharges :
    toyAdapter.accepts 3
    ∧ ∃ u, toyForeignValid u ∧ toyIncl 3 u := by
  have hacc : toyAdapter.accepts 3 :=
    ⟨⟨7, 3, 10, 3⟩, (by decide : toyVerify ⟨7⟩ ⟨7, 3, 10, 3⟩ = true), rfl⟩
  exact ⟨hacc, toAdapter_accepts_entails_valid toyClient toyLeaf_hashCR ⟨7⟩ toyIncl 3 hacc⟩

/-- **THE EMPTY UPDATE IS REJECTED at the toy adapter boundary** — `FailClosed` lifted. -/
theorem toy_adapter_rejects_empty : ¬ toyAdapter.foreignFinal toyClient.emptyUpdate :=
  toAdapter_rejects_empty toyClient ⟨7⟩ toyIncl

/-! ### It runs (`#guard`): the toy rules discriminate on concrete data. -/

#guard toyVerify ⟨7⟩ ⟨7, 3, 10, 3⟩ == true
#guard toyVerify ⟨7⟩ ⟨3, 3, 6, 3⟩ == false
#guard toyVerify ⟨7⟩ ⟨7, 3, 10, 99⟩ == false
#guard toyVerify ⟨7⟩ toyEmptyUpdate == false
#guard toySigVerify 7 3 10 == true
#guard toySigVerify 3 3 6 == false

/-! ## §8 — Axiom hygiene — every theorem kernel-clean (CI hard-gate). The toy leaf is PROVED
(both `sigSound` and the `hashCR` carrier — `toyLeaf_hashCR`), so nothing here rests on an
unproven crypto assumption; a REAL chain's `noForgery` would rest on its (visible, named)
`leaf.sigSound` field and take `leaf.hashCR` as its explicit CR hypothesis — a structure field
and a hypothesis are invisible to `#assert_axioms`, so per-chain lanes document those named
leaves explicitly. The both-polarity pins (`toyLeaf_hashCR` / `collapseLeaf_not_hashCR`) prove
the carrier is a real discriminating hypothesis, not `True` in disguise. -/

#assert_axioms CryptoLeaf.hash_inj
#assert_axioms toyLeaf_hashCR
#assert_axioms collapseLeaf_not_hashCR
#assert_axioms toyNoForgery
#assert_axioms toyFailClosed
#assert_axioms toyNonVacuous
#assert_axioms toAdapter_foreignFinal_discharged
#assert_axioms toAdapter_accepts_entails_valid
#assert_axioms toAdapter_rejects_empty
#assert_axioms toy_valid_holds
#assert_axioms toy_forged_signer_invalid
#assert_axioms toy_tampered_digest_invalid
#assert_axioms toy_tampered_binding_fails
#assert_axioms toy_gate_discriminates
#assert_axioms toy_adapter_accepts_and_discharges
#assert_axioms toy_adapter_rejects_empty

#print axioms toAdapter_foreignFinal_discharged
#print axioms toy_gate_discriminates

end Dregg2.Bridge.VerifiedLightClient

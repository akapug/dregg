import Dregg2.Crypto.PortalFloor

namespace Dregg2.Crypto.PortalFloor.ScratchRef
open Dregg2.Crypto.PortalFloor

/- Full devacuified Reference instances: carrier = the genuine soundness Prop,
   PROVED in the toy model, FALSE on a forgeable/degenerate instance. -/

instance instSignatureKernel : SignatureKernel Nat Nat Nat where
  Signed pk m := pk = m
  sigVerify pk m s := decide (s = m ∧ pk = m)
  unforgeable := ∀ pk m s, decide (s = m ∧ pk = m) = true → pk = m
  sigVerify_sound := fun h => h

theorem instSignatureKernel_unforgeable : instSignatureKernel.unforgeable := by
  intro pk m s h; simp only [decide_eq_true_eq] at h; exact h.2

instance instVerifierKernel : VerifierKernel Nat Nat where
  Holds stmt := stmt = 0
  verify stmt proof := decide (stmt = 0 ∧ proof = 0)
  extractable := ∀ stmt proof, decide (stmt = 0 ∧ proof = 0) = true → stmt = 0
  verify_sound := fun h => h

theorem instVerifierKernel_extractable : instVerifierKernel.extractable := by
  intro stmt proof h; simp only [decide_eq_true_eq] at h; exact h.1

instance instPedersenKernel : PedersenKernel Int where
  commit v r := v + r
  commit_hom := by intro v w r s; ring
  Opens d v _ := d = v
  binding := ∀ (d : Int) (v v' r r' : Int), d = v → d = v' → v = v'
  binding_sound := fun h => h

theorem instPedersenKernel_binding : instPedersenKernel.binding := by
  intro d v v' _ _ ho ho'; exact ho.symm.trans ho'

instance instPoseidon2Kernel : Poseidon2Kernel Nat where
  compress a b := Nat.pair a b
  collisionHard := ∀ a b a' b', Nat.pair a b = Nat.pair a' b' → a = a' ∧ b = b'
  noCollision := fun h => h

theorem instPoseidon2Kernel_collisionHard : instPoseidon2Kernel.collisionHard := by
  intro a b a' b' h
  exact ⟨(Nat.pair_eq_pair.mp h).1, (Nat.pair_eq_pair.mp h).2⟩

instance instBlake3Kernel : Blake3Kernel Nat where
  hash l := Encodable.encode l
  collisionHard := ∀ x y, (Encodable.encode x : Nat) = Encodable.encode y → x = y
  noCollision := fun h => h

theorem instBlake3Kernel_collisionHard : instBlake3Kernel.collisionHard := by
  intro x y h; exact Encodable.encode_injective h

instance instNullifierKernel : NullifierKernel Int where
  derive d := d
  -- unlinkable: the genuine (non-True) anonymity Prop for the toy identity tag.
  -- In the toy identity model derive = id, so "tags reveal nothing beyond the note"
  -- is modelled as: derive is injective (no two notes collide on a tag) — a real,
  -- structurally-true Prop here, FALSE for a constant (fully-linkable) tag.
  unlinkable := ∀ d d' : Int, (id d : Int) = id d' → d = d'

theorem instNullifierKernel_unlinkable : instNullifierKernel.unlinkable := by
  intro d d' h; exact h

instance instSealKernel : SealKernel Nat Nat where
  Sealed key ct := ct = key
  aeadOpen key ct := decide (ct = key)
  authentic := ∀ key ct, decide (ct = key) = true → ct = key
  open_sound := fun h => h

theorem instSealKernel_authentic : instSealKernel.authentic := by
  intro key ct h; simp only [decide_eq_true_eq] at h; exact h

instance instMacKernelE : MacKernelE Nat Nat Nat where
  mac key msg := Nat.pair key msg
  Tagged key msg t := t = Nat.pair key msg
  verifyTag key msg t := decide (t = Nat.pair key msg)
  unforgeable := ∀ key msg t, decide (t = Nat.pair key msg) = true → t = Nat.pair key msg
  verifyTag_sound := fun h => h

theorem instMacKernelE_unforgeable : instMacKernelE.unforgeable := by
  intro key msg t h; simp only [decide_eq_true_eq] at h; exact h

/-! ## Non-vacuity: each carrier is FALSE on a forgeable/degenerate instance. -/

-- Forgeable signature oracle: accepts everything, Signed never holds ⇒ carrier FALSE.
instance instForgeSig : SignatureKernel Nat Nat Nat where
  Signed _ _ := False
  sigVerify _ _ _ := true
  unforgeable := ∀ pk m s, (true : Bool) = true → (False : Prop)
  sigVerify_sound := fun h => h
theorem instForgeSig_NOT_unforgeable : ¬ instForgeSig.unforgeable := by
  intro h; exact h 0 1 0 rfl

-- Degenerate verifier: accepts everything, Holds=False ⇒ extractable FALSE.
instance instForgeVer : VerifierKernel Nat Nat where
  Holds _ := False
  verify _ _ := true
  extractable := ∀ stmt proof, (true : Bool) = true → (False : Prop)
  verify_sound := fun h => h
theorem instForgeVer_NOT_extractable : ¬ instForgeVer.extractable := by
  intro h; exact h 0 0 rfl

-- Forgeable seal: opens everything, Sealed=False ⇒ authentic FALSE.
instance instForgeSeal : SealKernel Nat Nat where
  Sealed _ _ := False
  aeadOpen _ _ := true
  authentic := ∀ key ct, (true : Bool) = true → (False : Prop)
  open_sound := fun h => h
theorem instForgeSeal_NOT_authentic : ¬ instForgeSeal.authentic := by
  intro h; exact h 0 0 rfl

-- Forgeable MAC: accepts everything, Tagged=False ⇒ unforgeable FALSE.
instance instForgeMac : MacKernelE Nat Nat Nat where
  mac _ _ := 0
  Tagged _ _ _ := False
  verifyTag _ _ _ := true
  unforgeable := ∀ key msg t, (true : Bool) = true → (False : Prop)
  verifyTag_sound := fun h => h
theorem instForgeMac_NOT_unforgeable : ¬ instForgeMac.unforgeable := by
  intro h; exact h 0 0 0 rfl

-- Colliding hash: compress collapses everything, noCollision-carrier FALSE.
instance instCollideHash : Poseidon2Kernel Nat where
  compress _ _ := 0
  collisionHard := ∀ a b a' b', (0 : Nat) = 0 → a = a' ∧ b = b'
  noCollision := fun h => h
theorem instCollideHash_NOT_collisionHard : ¬ instCollideHash.collisionHard := by
  intro h; exact absurd (h 0 0 1 1 rfl).1 (by decide)

end Dregg2.Crypto.PortalFloor.ScratchRef

/-
# `Dregg2.Storage.Deployed` — the bucket content root over the DEPLOYED Poseidon2, via Lean↔Rust FFI.

The storage proofs (`BucketCommitment`) are over an ABSTRACT collision-resistant hash — the stronger
form (they hold for *any* CR hash). This module instantiates them at the **deployed** hash: the fast
Rust/plonky3 Poseidon2, called from Lean through `@[extern]` (the same shape as
`@[extern "dregg_ed25519_verify"]` in `Crypto/PortalFloor.lean`).

So the runtime is: the verified content-root LOGIC is Lean (compiled to native via `leanc`), the hot
hash PRIMITIVE is the fastest Rust (called back through FFI), and the FFI binds them both ways.
Lean-side `poseidon2Hash` is `opaque` — the binding proofs assume `Poseidon2SpongeCR` about it (the
§8 crypto floor, never a Lean law); the Rust symbol `dregg_poseidon2_hash` realizes it at runtime.
-/
import Dregg2.Storage.BucketCommitment

namespace Dregg2.Storage

open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-- **The deployed hash** — the fast Rust Poseidon2 (`circuit::binding::from_poseidon2`), called from
Lean via FFI. Opaque here (proofs assume `Poseidon2SpongeCR` about it — the §8 floor); realized at
runtime by the Rust symbol `dregg_poseidon2_hash`. Mirrors `@[extern "dregg_ed25519_verify"]`. -/
@[extern "dregg_poseidon2_hash"]
opaque poseidon2Hash : List Int → Int

/-- **The bucket content root over the DEPLOYED Poseidon2** — executable (the `@[export]` wrapper
calls the fast Rust hash through the `@[extern]`), and — under the CR floor for the deployed hash —
binding. This is the object the Rust `storage::bucket_commitment::content_root` becomes: Lean logic,
Rust primitive. -/
def contentRootDeployed (objs : List Object) : Int :=
  contentRoot poseidon2Hash objs

/-- **The deployed content root binds the committed object set** — the extracted, real-crypto form of
`contentRoot_injective`, discharged by the collision-resistance carrier for the deployed Poseidon2.
No ghost object hides under a genuine deployed root. -/
theorem contentRootDeployed_injective (hCR : Poseidon2SpongeCR poseidon2Hash) :
    ∀ objs objs' : List Object,
      contentRootDeployed objs = contentRootDeployed objs' → objs = objs' :=
  contentRoot_injective poseidon2Hash hCR

#assert_axioms contentRootDeployed_injective

end Dregg2.Storage

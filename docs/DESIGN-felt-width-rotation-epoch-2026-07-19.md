# DESIGN — the felt-width rotation epoch (Kind-E batch)

**2026-07-19.** Scopes the coordinated widening of the narrow *signed / public-input* payloads from
`docs/WOUND-felt-width-boundaries-2026-07-19.md` (findings #1, #2, #9, #11). These are batched
because each changes what a node **signs** or what a verifier **binds as a public input** — a wire /
Fiat-Shamir / VK change ("one rotation epoch"): old certs/proofs are not interchangeable with new
ones, so nodes (producers) and light clients (verifiers) must flip **together**.

Greenfield rule ([[feedback-no-greenfield-migration-theater]]): nothing is deployed, so there is NO
dual-accept, NO old-format compatibility window. Make the wide object, delete the narrow encoder,
fail-closed on the new layout.

---

## The load-bearing distinction: E1 (pure Rust) vs E2 (circuit must expose the wide root)

The naive read is "widen four signing/compare sites in Rust." That is wrong for three of the four.
Only #1 is a Rust-only change; #2/#9/#11 compare a value that is a **single public input of a
circuit**, so the wide value must first be **exposed by the descriptor's PI layout** — an AIR /
descriptor change, authored in Lean, Rust calls in. ⚠️ Tripwire: E2 touches circuit public inputs.

### E1 — pure Rust wire/signing change (wide value already in hand)

- **#1 BFT finality cert** (`lightclient/src/lib.rs`). The wide root already exists on the light
  client: `WholeChainProof.final_root: [BabyBear; SEG_ANCHOR_WIDTH]` is 8 felts (`lib.rs:142`), and
  it is bound to the aggregate proof by the segment tooth. The ONLY narrow thing is the cert
  interface bolted on top:
  - `FinalityCert.finalized_root: BabyBear` → `[BabyBear; 8]`.
  - `finality_signing_message(finalized_root: BabyBear, …)` → absorb all 8 felts (the committee
    signs the wide root).
  - the seam `agg.final_root[0] != finalized_root` → `agg.final_root != finalized_root8` (all lanes).
  - bump the domain tag `b"dregg-finality-cert-v1\0"` → `…-v2\0` (a signed value's shape changed).
  - No circuit change. This is the highest-value item and it is self-contained Rust.

### E2 — descriptor must expose an 8-felt root PI first (Lean AIR), then the Rust compare widens

Each of these compares an `expected_root` (1 felt) against a **single root public input** the circuit
pins. Widening requires the descriptor to expose the root as 8 PIs, i.e. a PI-layout change → new
`vk_hash` → new WIDE-registry entry. The wide root itself already exists as a computed value in every
case (the campaign widened the *roots*; it did not widen their *PI projections*).

- **#2 Federation membership** (`sdk/src/verify.rs:137`). `expected_federation_root` collapses the
  32-byte root to ONE felt; the compares are `blinded_pis[PI_ROOT_4ARY] != expected_root` and
  `bound_pis[FEDERATION_ROOT] != expected_root`. Contrast: the action binding 15 lines below already
  loops over `ACTION_BINDING_WIDTH` felts. Needs: the `blinded_membership` + `bound_presentation`
  descriptors expose an 8-felt root PI group; then `expected_federation_root` returns `[BabyBear; 8]`
  and both compares run over all lanes. Delete the 1-felt `u32`/`bytes_to_babybear` collapse.
- **#9 SenderAuthorized authorized-set** (`turn/src/executor/membership_verifier.rs:105`). The 4-ary
  membership descriptor pins `[leaf, root]` with a 1-felt `root` (`root_felt_from_slot` = low-4-bytes
  as `u32`). Needs: descriptor PI layout `[leaf, root0..root7]`; widen `root_felt_from_slot` +
  `authorized_set_root_bytes` + the `verify_vm_descriptor2(&desc, &wire.proof, &[leaf, root8…])` call.
- **#11 Freshness / revocation** (`sdk/src/full_turn_proof.rs:5248`). The non-revocation sub-proof
  exposes a 1-felt `revocation_root` PI (`sub_public_inputs.first()`). The wide root already exists in
  the rotated path (`circuit/src/effect_vm/trace_rotated.rs:1423`, `before_root8`/`after_root8`), so
  the accumulator computes 8 felts. Needs: the non-revocation descriptor exposes all 8 as PIs; widen
  the compare + `expected_revocation_root: [BabyBear; 8]`.

---

## Rotation mechanics (one epoch, all together)

1. **E2 descriptors regenerated in Lean.** Each root-PI-layout change is authored where the descriptor
   is authored (Lean emit → JSON → `WIDE_REGISTRY_STAGED_TSV`) — NOT hand-edited in Rust. New PI
   layout ⇒ new descriptor JSON ⇒ new blake3 `vk_hash` ⇒ new registry entry. `leg_is_wide` /
   `descriptor_by_name` dispatch picks them up by fingerprint (the classifier is already wide-correct
   after the #14 fix).
2. **E1 cert version bump.** `dregg-finality-cert-v1` → `-v2`; a `-v1` cert is refused post-flip.
3. **Rust compares widened + narrow encoders DELETED.** `felt_to_bytes32` at these sites,
   `expected_federation_root`'s 1-felt branch, `root_felt_from_slot`'s lane-0 read — removed so the
   narrow projection is not merely unused but *gone* (the type-wall philosophy: un-representable, not
   un-called). Type the widened roots as `[BabyBear; 8]` / `Faithful8` end to end.
4. **Producers + verifiers flip in lockstep.** Nodes emit the widened certs/proofs; light clients
   (wasm verify build) bind the widened PIs. Because it is one VK/registry epoch, there is no window
   where a v1 producer meets a v2 verifier.
5. **CI-wire a forge canary per site** (the discipline `offchain_root_forge_closed.rs` set): a lane-0
   collision pair that the narrow compare accepted and the wide compare REJECTS, run in CI so a
   regression is a red test, not a silent re-narrowing. An orphaned proof is a green nobody runs
   ([[project-felt-width-repair-campaign]]).

## Sequencing recommendation

- **Land #1 (E1) first and standalone** — it is pure Rust, self-contained, closes the worst finding,
  and does not need the descriptor regeneration pipeline. It can ship before the E2 descriptors exist.
- **Batch #2/#9/#11 (E2) as the descriptor-widening epoch** — one coordinated pass: author the three
  widened root-PI descriptors in Lean, regenerate the registry, widen the three Rust compares, delete
  the narrow encoders, CI-wire the three canaries. These share the "expose the 8-felt root PI"
  mechanism, so doing them together amortizes the emit/registry regeneration.

## Tripwire restated

E2 changes circuit public inputs. The widened root-PI descriptors are **Lean-authored AIR** — the
membership / bound-presentation / non-revocation descriptors' PI layouts are part of the circuit spec.
Say the substrate out loud when starting each; do NOT hand-widen a descriptor's PI vector in Rust.

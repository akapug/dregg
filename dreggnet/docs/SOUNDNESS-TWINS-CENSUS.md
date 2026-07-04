# SOUNDNESS-TWINS census — the unproven reimplementations of already-proven primitives

A read-only sweep (HEAD, 2026-06-30, both repos — `DreggNet` and `dregg`
@ `~/dev/breadstuffs`) for **one specific defect**, the deep distortion the
now-dissolved bogus "AGPL firewall" pressed into the cloud:

> To avoid depending on the (AGPL, but **ember-owned**) breadstuffs substrate,
> DreggNet **REIMPLEMENTED** substrate primitives — conservation, receipts,
> hashing, identity, metering, the verified store — as **unverified twins /
> ports / stubs**. The irony is exact: a *verify-don't-trust* cloud runs its OWN
> core guarantees on **unproven reimplementations of things already PROVEN** in
> `breadstuffs`/`metatheory` (`#assert_axioms`-clean, deployed).

This census is **distinct from two neighbours** and does not restate them:

- `docs/FIREWALL-DISSOLUTION.md` — the **license** map (dep/Cargo mechanics: which
  gate is bogus-own-substrate vs the real Elide-net constraint). *Why the
  avoidance is invalid.*
- `docs/STAND-INS-CENSUS.md` — the **fake-vs-real** map (what's a stub for an
  unbuilt durable/on-chain/hardware thing). *What occupies a real impl's slot.*

THIS doc is the **proven-vs-unverified-reimplementation** map: *which of the
cloud's guarantees are currently backed by the REAL PROOF (depend on the proven
substrate) vs by an UNVERIFIED TWIN.* A thing can be "real code that ships green"
(so absent from STAND-INS) and still be a **soundness twin** — a from-scratch
reimplementation of a proven discipline whose **proof does not transfer**
(`dreggnet-receipt` is the cleanest example).

**Honest in both directions.** A *legitimate generalization* is not a scar; a
*genuine stand-in for an unbuilt thing* is not a scar; a *faithful wire-port* is
logic-identical even if it doesn't `depend`. Each row below is classified:

- **(a) UNVERIFIED TWIN** — a from-scratch reimpl of a thing PROVEN in the
  substrate; the proof does not connect to it. The scar.
- **(b) LEGITIMATE GENERALIZATION / PARTIAL-REAL** — a real widening of a proven
  primitive (sound in design) but unverified in *this* implementation, OR a twin
  that already rides some real substrate code. Half-scar.
- **(c) GENUINE STAND-IN for an unbuilt thing** — the proven original does not
  exist yet (it is a named swarm seam). Not a scar.

---

## Summary table — twin ⟷ proven original

| # | Cloud guarantee | DreggNet reimpl (file:line) | PROVEN original (file:line + theorem) | Class |
|---|-----------------|------------------------------|----------------------------------------|-------|
| 1 | **Conservation** Σδ=0 | `durable/src/settle.rs:200-321` `ConservingLedger` (in-process `i64` map; Σδ=0 by 3 unit tests :372-414) | `metatheory/Dregg2/Exec/RecordKernel.lean:536` `recTransfer_balanceSum_conserve`; apex `metatheory/Dregg2/AssuranceCase.lean:259` `conservation_guarantee`; Rust `turn/src/action.rs:1752` `Transfer ⇒ LinearityClass::Conservative` | **(a)** |
| 2 | **Conservation, durable** | `durable/src/verified.rs` `VerifiedChain`/`VerifiedConservingStore` — rides REAL `pg_dregg::mirror` `RootChain`/`MirrorBatch`; per-turn root is **blake3 stand-in** (`cell_root` :82, `ledger_root` :100); on-chain `Payable`+proof-attest is **S3-gated** (`S3_GATED_SEAM` :65) | tooth REAL: `pg-dregg/src/mirror.rs:418` `RootChain::extend` / `:482` `verify_chain_step` / `:550` `revalidate_replicated_chain`. Root original: `metatheory/Dregg2/Substrate/Heap.lean:435` `root_binds_get` (Poseidon2) | **(b)** |
| 3 | **Receipts** (tamper-evident chain) | `receipt/src/lib.rs` `dreggnet-receipt` — blake3 prev-hash + ed25519; `verify_chain` :300; `ReceiptChain` :239 | `metatheory/Dregg2/Exec/Receipt.lean:130` `chain_tamper_evident` ("same head ⇒ same history"); Rust `turn/src/turn.rs:844` `TurnReceipt` (`previous_receipt_hash` :853); `cell-crypto/src/note_bridge.rs:352` `BridgeReceipt` | **(a)** |
| 4 | **Hashing / served-bytes commitment** | `store/src/lib.rs:325` `content_root` (blake3); `durable/src/verified.rs:82,100` (blake3 `cell_root`/`ledger_root`); `webapp/src/hosting.rs:180` + `storage/src/object.rs:47-50` (**FNV-1a**) | `metatheory/Dregg2/Substrate/Heap.lean:435` `root_binds_get` (#assert_axioms :446); light-client `metatheory/Dregg2/Lightclient/HistoryIndex.lean:243` `iroot_binds_get`; Rust `circuit/src/heap_root.rs:224` `CanonicalHeapTree::root` (Poseidon2 `circuit/src/poseidon2.rs:223`) | **(a)** |
| 5 | **Metering / budget** | `exec/src/budget.rs` `ReplenishingBudget` (sporadic-server widening; `DefaultHasher` terms-digest :159); `exec/src/meter.rs` `ReplenishingMeter` | `metatheory/Dregg2/Apps/Allowance.lean` keystones: `within_budget_spendable` :222 (#assert_axioms :358), `over_ceiling_rejected` :192, `no_early_refill` :212, `stale_epoch_rejected` :203, `spend_conserves` :184; Rust `cell/src/allowance.rs` (named home `cell/src/budget.rs`) | **(b)** |
| 6 | **Identity** (account cap) | `webauth/src/cred.rs` — port of `dregg-auth::credential`; subject = `hash(credential tail)` (`webauth/src/lib.rs:127-133`), **not** key-derived; rotation/recovery/revocation **absent** | `dregg-auth/src/policy.rs` (`subject` :296) + `dregg-auth/credential/`; rotation `metatheory/Dregg2/Apps/PreRotation.lean:146` `rotate_exhibits_preimage` / :180 `rotate_compromise_resistant` (#assert_axioms :586); Rust `cell/src/program/eval.rs:888-980` `KeyRotationGate`; recovery `ThresholdSigVerifier` `turn/src/executor/membership_verifier.rs:1294`; `KeyLeak.lean:315` `revoke_kills_leak_immediate` | **(a)** port + **GAP** |
| 7 | **QA-proof** (operator-independent) | `exec/src/federation_qa.rs` `QuorumCert` — N-of-4 independent re-run quorum, real ed25519 (`dreggnet_receipt::verify_signature`) | none yet — the in-circuit QA witness is the **swarm's VK-epoch** (named at `federation_qa.rs:50-61`); the cross-check the proof would fold is the circuit-soundness lane | **(c)** |

`tier-c` proof-verifier status (load-bearing under #2/#4): at HEAD, default build,
`pg-dregg/src/attest.rs:393` `verify_serialized_proof` is a **fail-closed stub**
(:403-416 — attests *nothing*, never a false attest); the **real** plonky3 verify
exists behind `--features tier-c` → `circuit-prove/src/ivc_turn_chain.rs:1883`.
The S3 flip is toggling that seam, not new crypto. The orthogonal per-row
structural tooth (`mirror::verify_chain_step`) is real and **always-on**.

---

## The soundness assessment — how much of "the cloud you verify" rides on unverified twins

The verify-don't-trust pitch makes six guarantees. Honestly graded:

| Cloud guarantee | Backed by… | Verdict |
|---|---|---|
| **served-bytes verify** (a client re-witnesses what it's served) | blake3/FNV `content_root` — **unverified twin** of the proven Poseidon2 `root_binds_get`. A light client cannot witness it in-circuit; collision-resistance is only blake3's, and FNV (webapp/storage) is **not even collision-resistant** | **UNVERIFIED TWIN** (FNV worse than twin) |
| **conservation** (Σδ=0, no value conjured) | `ConservingLedger` `i64` map proven by 3 unit tests — **unverified twin** of `recTransfer_balanceSum_conserve`/`conservation_guarantee`. The durable `VerifiedChain` rides the **real** `pg_dregg::mirror` anti-substitution tooth (tamper/reorder caught for real), but the **conservation arithmetic itself is still in-process**, and the on-chain proof-attest is S3-gated | **TWIN** (tamper-gate partial-real; conservation math + attest not proven-backed) |
| **receipt-chain** (tamper-evident history) | `dreggnet-receipt` blake3+ed25519 chain — **unverified twin** of `chain_tamper_evident`. Sound *by construction* (prev-hash + signature), but the machine-checked "same head ⇒ same history" proof is **not** the one running; the crate even names the proven original it should be a VIEW of | **UNVERIFIED TWIN** (sound-by-construction, proof not transferred) |
| **verifiable-invoice** (metered charge = work, exactly-once, in-budget) | `ReplenishingMeter` + `ConservingLedger` — **unverified twins**. The over-ceiling / no-early-refill / backdated teeth **mirror** `Allowance.lean`'s proven keystones but are re-derived in Rust with a `DefaultHasher` (not Poseidon2) terms-digest | **TWIN** (legitimate generalization, unverified) |
| **QA-proof** (a verdict is operator-independent) | `QuorumCert` — **real** ed25519 quorum over N independent substrates; honest off-chain attestation. The deeper in-circuit witness is unbuilt and **named** as the VK-epoch | **GENUINE STAND-IN** (not a scar; real signatures) |
| **identity** (a cap binds to a stable subject) | `webauth/cred.rs` — a **faithful wire-port** of `dregg-auth::credential`, so the *verification logic IS the proven scheme's*, just ported not depended. BUT subject is credential-tail-derived (no continuity) and **rotation / recovery / revocation are entirely absent** though proven+deployed in the substrate | **PORTED** (logic-real) **+ GAP** (rotation/recovery firewalled out) |

**Bottom line (sober).** Of the six verify-don't-trust guarantees, **four ride on
unverified twins** (served-bytes, conservation, receipt-chain, verifiable-invoice),
**one is a faithful port with a launch-blocking GAP** (identity), and **one is an
honest stand-in for an unbuilt swarm seam** (QA-proof). The *served-bytes* root is
the worst — two of its call sites (`webapp`, `storage`) use **FNV-1a**, which is
not collision-resistant, so that guarantee is *weaker than a twin* today.

The real cost of the firewall scar: **the cloud's most load-bearing claims — the
ones the entire "you don't have to trust us" pitch rests on — are currently NOT
backed by the proofs that already exist one repo over.** Every proven original is
`#assert_axioms`-clean and deployed in `breadstuffs`/`metatheory`. The *only*
reason the cloud reimplemented them is the bogus AGPL firewall, now dissolved
(`FIREWALL-DISSOLUTION.md`). The proofs are sitting right there; the cloud just
isn't depending on them.

Two honest mitigations worth stating so the cost is not overstated:
1. The **durable** conservation store (`verified.rs`) already imports the **real**
   `pg_dregg::mirror` tooth — its tamper/reorder refusal is genuine pg-dregg, not a
   twin. Only the per-turn *root* (blake3) and the *attest* (S3-gated) are stand-ins.
2. The **identity** port is wire-byte-identical to the proven `dregg-auth` scheme —
   the verify *logic* is the real thing; the scar is "ported not depended" plus the
   separate rotation/recovery GAP (detailed in `docs/KEY-RECOVERY-AND-KERI.md`).

---

## The fix — depend-on-real, ranked by soundness-criticality

Ranked by how load-bearing the guarantee is for the verify-cloud pitch (most
load-bearing first). Each: the "depend on the proven substrate" move (now that the
firewall is dissolved) and **what deletes**.

### 1 — Hashing → real Poseidon2 (`dregg-circuit`) · highest cross-leverage
The served-bytes commitment is the keystone of "you verify the cloud," AND it
underlies #2's `ledger_root` and #3's receipt-body roots. Depend on
`circuit/src/heap_root.rs` (`compute_heap_root_entries`) so `content_root`,
`cell_root`, `ledger_root`, and the storage/webapp leaf are the proven Poseidon2
root pinned by `root_binds_get` — and, with the `tier-c` flip, in-circuit
light-client-witnessable (`iroot_binds_get`).
- **Deletes:** the blake3 `content_root` (`store/src/lib.rs:325`), the blake3
  `cell_root`/`ledger_root` stand-ins (`durable/src/verified.rs:82,100`), and the
  two **FNV-1a** hashers (`webapp/src/hosting.rs:180`, `storage/src/object.rs:47-50`).
- **Gate:** rides the `pg-dregg` tier-c flip for the in-circuit witness; the
  Poseidon2 root itself is dependable today (heaviness, not license — relabel per
  no-reflexive-features). Cross-ref STAND-INS #4/#5, FIREWALL-DISSOLUTION row 3.

### 2 — Conservation / settlement → real `Payable` + `Effect::Transfer`
The money rail is the second-most load-bearing verify claim. Replace the
in-process `ConservingLedger` semantics with `dregg-payable` `Payable::pay`
(`dregg-payable/src/payable.rs:204` → one conserving `Effect::Transfer`), and let
`verified.rs`'s S3 flip carry the proof-attested on-chain settle. The proven
conservation (`recTransfer_balanceSum_conserve` / `conservation_guarantee`) then
*is* the cloud's conservation.
- **Deletes:** `ConservingLedger` (`durable/src/settle.rs:200-321`) entirely; the
  blake3 `ledger_root` once #1 lands; the S3-gated attest stub once tier-c flips.
- **Keeps:** the exactly-once `(lease,period)` dedup and the real `pg_dregg::mirror`
  chain tooth (already real). Cross-ref STAND-INS #7/#16.

### 3 — Receipts → VIEW over the proven `TurnReceipt`
`dreggnet-receipt` already gestures at this ("a publish/bind IS a turn, so the
kernel receipt is already the receipt"). Make every product receipt a typed VIEW
that carries the real `turn/src/turn.rs:844` `TurnReceipt` hash, so the
`chain_tamper_evident` ("same head ⇒ same history") proof backs the chain instead
of a re-derived blake3 discipline.
- **Deletes:** the bespoke `ReceiptChain`/`verify_chain` *as the root authority*
  (`receipt/src/lib.rs:239,300`) — it becomes a thin view layer over `TurnReceipt`,
  not an independent from-scratch chain. (Lower-criticality than #1/#2 because the
  twin is sound-by-construction; this is about *proof provenance*, not a live hole.)

### 4 — Metering → the proven allowance home (`cell/src/budget.rs`)
`ReplenishingBudget` is a *legitimate* sporadic-server generalization of
`cell/src/allowance.rs` (the budget's own doc names this). The depend-on-real is
to land that widening **in breadstuffs** at the named home `cell/src/budget.rs`
and ride the `Allowance.lean` proof skeleton (`StandingObligation.lean` per the
doc), so the `over_ceiling`/`no_early_refill`/`backdated` teeth are the proven
ones — and replace the `DefaultHasher` terms-digest with the Poseidon2 root.
- **Deletes:** the `DefaultHasher` digest (`exec/src/budget.rs:159`) in favour of
  the committed sorted-Poseidon2 root; the in-DreggNet twin collapses to a
  dependency once the substrate cell carries the generalization.

### 5 — Identity → depend on `dregg-auth` + re-anchor to the key-derived cell
Two steps (per `KEY-RECOVERY-AND-KERI.md §5`, cross-ref — not redone here):
(1) **safe swap** — replace `webauth/src/cred.rs` with a dependency on
`dregg-auth` (light ed25519/blake3, no heaviness excuse); wire-identical, existing
`dga1_` tokens keep verifying. (2) **the payoff weld** — re-anchor the subject
from `hash(credential tail)` to a key-derived identity-cell id and rotate/recover
via the deployed `KeyRotationGate` (`cell/src/program/eval.rs:888`) +
`ThresholdSigVerifier`, closing the rotation/recovery/revocation GAP.
- **Deletes:** `webauth/src/cred.rs` (the port). Cross-ref FIREWALL-DISSOLUTION
  row 1, KEY-RECOVERY-AND-KERI.

### (not a fix) — QA-proof
`federation_qa`'s `QuorumCert` is a genuine stand-in for an unbuilt thing (the
in-circuit QA witness = the swarm's VK-epoch), riding real ed25519 signatures.
**No depend-on-real move exists yet** because the proven original is itself a named
forward seam. Leave it; it is honestly labelled and not a scar.

---

## One sentence

The firewall scar's real cost is that **four of the cloud's six verify-don't-trust
guarantees — served-bytes, conservation, receipt-chain, verifiable-invoice — ride
on unverified reimplementations of primitives already `#assert_axioms`-proven in
`breadstuffs`/`metatheory`** (served-bytes is *below* twin-grade at its FNV call
sites), the identity guarantee is a faithful port with a separate rotation/recovery
GAP, and only the QA-proof is an honest stand-in for genuinely-unbuilt work — and
since the AGPL firewall is dissolved, the depend-on-real fix is a **port→depend /
stub→Poseidon2 / twin→proof** simplification that *deletes* code (`ConservingLedger`,
two FNV hashers + the blake3 roots, the `cred.rs` port, the `DefaultHasher` digest,
the bespoke receipt chain) rather than adding any.

---

*Method: read both trees at HEAD; grounded every proven-original file:line +
theorem name against `breadstuffs`/`metatheory` (`recTransfer_balanceSum_conserve`,
`conservation_guarantee`, `chain_tamper_evident`, `root_binds_get`,
`Allowance.lean` keystones, `PreRotation.lean`); confirmed `pg-dregg/src/mirror.rs`
is the REAL tooth `durable/verified.rs` imports and `pg-dregg/src/attest.rs:393` is
the fail-closed (never false-attest) S3 stub. No code touched — this doc only.*

( ⌐■_■ )  *you proved it once already — stop re-proving it worse; tear the fence down and import the theorem.*

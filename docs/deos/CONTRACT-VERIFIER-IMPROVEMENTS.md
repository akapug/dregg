# Contract-verifier improvements — map, classification, and a seeded brick

DREGG ships **two** contract verifiers, and they are different machines with
different frontiers:

- **(A) the on-chain PROOF verifier** — a third-party contract on another chain
  accepts a DREGG state transition because a Groth16(BN254) proof attests it.
  Entry point: the OCIP socket `chain/contracts/socket/DreggVerifier.sol`,
  wrapping the VK-epoch registry `DreggGroth16VerifierUpgradeable.sol`.
- **(B) the contract-SAFETY verifier** — `tools/dregg-audit/`, which decides
  whether an arbitrary contract is rug-safe (grep taxonomy + Halmos symbolic
  proof + codex adversarial pass).

This doc maps both, classifies every improvement opportunity
(BUILDABLE-NOW / RESEARCH / EMBER-GATED), recommends the top buildable-now one
per verifier, and records the seeded first-brick.

---

## (A) The on-chain proof verifier — what exists today

The socket verifies a Groth16(BN254) wrap of the DREGG whole-history STARK apex.
Its statement is a **fixed 25-lane public-input vector**
(`chain/contracts/socket/DreggVerifier.sol:33-46`,
`chain/contracts/DreggGroth16Verifier25.sol`):

```
[0..8)   genesis_root   — 8 BabyBear lanes: the DREGG state started from
[8..16)  final_root     — 8 BabyBear lanes: the DREGG state reached
[16]     num_turns      — how many turns were folded into this transition
[17..25) chain_digest   — 8 lanes: segment accumulator over every (old,new) pair
```

**Aggregation is already wired into the statement.** The `num_turns` lane and the
`chain_digest` segment-accumulator lanes mean the on-chain statement is *inherently*
an N-turn statement, not a single-clearing one. The prover side that produces it is
the universal-fold accumulator `circuit-prove/src/ivc_turn_chain.rs`
(`prove_turn_chain_recursive` folds an arbitrary finite K of finalized turns into
ONE root recursive proof; the root exposes exactly
`[genesis_root8, final_root8, num_turns, chain_digest8]` via the `expose_claim`
table, `ivc_turn_chain.rs:254-278`, and `verify_turn_chain_recursive` checks it in
three teeth: VK-pin, claimed-publics attestation, root batch-STARK).

This is not theoretical: a **real 2-turn fold** has been run end-to-end
(`docs/deos/CROSS-CHAIN-SETTLEMENT-REALNESS.md:17-24`): `prove_turn_chain_recursive`
over a 2-turn chain → `ir2_leaf_wrap` apex (264 s) → gnark `SettlementCircuit`
(4,980,767 R1CS constraints) → Groth16, and the resulting proof verifies on three
real verifiers (Base-Sepolia Solidity 7/7, Solana `alt_bn128` 2/2, Cosmos arkworks
BN254 5/5) at ~5.21M gas.

So the honest state of (A) is: **the aggregation MACHINERY and the on-chain
STATEMENT both exist and have been exercised at K=2.** The named gaps are elsewhere.

### (A) improvement table

| Improvement | What it buys | Classification | Effort |
|---|---|---|---|
| **Fold LIVE-node turns (the `FullTurnProof→FinalizedTurn` adapter)** | Makes a real node turn foldable into the wrap statement. | **DONE** — the adapter exists at HEAD (`dregg_turn::rotation_witness::finalized_turn_from_full_turn`, `turn/src/rotation_witness.rs:731`, fail-closed on missing/mismatched wide 8-felt anchors); the transfer-bodied both-polarity test `full_turn_wrap_adapter_binds_real_transfer_and_rejects_mismatch` (`sdk/src/full_turn_proof.rs:10091`) proves a real `FullTurnProof` and bridges it through the adapter. | — |
| **Scale K > 2 in the wrapped path** | Demonstrate the K-fold at K=4/8/16 through the wrap (the machinery folds arbitrary finite K; only K=2 has been wrapped). The scaling proof. | **BUILDABLE-NOW** | M–L (proving stack is heavy: 264 s/apex) |
| **Richer statements (mechanism-family / tier / batch tag)** | Attest *which mechanism* (a clearing vs a pool settlement vs a transfer batch) in the public statement, not just the root pair — lets a consumer gate on the kind of transition. | **BUILDABLE-NOW** (add exposed lanes to `expose_claim` + widen the 25-lane vector + regen VK) but **EMBER-GATED to deploy** (VK change). | M |
| **Clearing-proof attestor (`IClearingAttestor` rung 2)** | Wire the STARK→BN254→Groth16 pipeline to emit a *clearing* statement so the launchpad runs trust-minimized, not rung-1 replayable (`PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE.md:200-207`, the named weld). | **BUILDABLE-NOW** (pipeline exists; emit a clearing PI) | M–L |
| **More chains (Solana / Cosmos socket parity)** | The socket is "two checks — WHICH-dregg + IS-IT-VALID — on verifiers that already exist" (`OCIP-SECURITY-SOCKET.md:161-179`). EVM is fully wired; Solana/Cosmos verifiers verify the proof but lack the epoch-registry socket wrapper. | **BUILDABLE-NOW** | M |
| **Gas / calldata efficiency** | ~5.21M gas today; a smaller proof system or calldata packing lowers per-settlement cost. | **BUILDABLE-NOW** (measured, not yet optimized) | M |
| **Production Groth16 ceremony (dev → MPC)** | Today's proofs ride a single-party DEV ceremony (toxic-waste-known); a forger who ran the setup could forge. MPC closes it. | **EMBER-GATED** (`OCIP-SECURITY-SOCKET.md:185-192`) | — |
| **PQ on-chain verifier** | Classical BN254 pairing is a pragmatic choice; a post-quantum on-chain verifier (e.g. a STARK verified natively on-chain, or a PQ SNARK) removes the classical-pairing assumption. | **RESEARCH** (no production PQ on-chain verifier; gas-prohibitive today) | XL |

---

## (B) The contract-safety verifier — what exists today

`tools/dregg-audit/` runs four stages (`tools/dregg-audit/dregg-audit`,
`docs/deos/DREGG-AUDIT-SERVICE.md`):

- **A. rug-forensics** — deterministic grep over a **9-door taxonomy**
  (`RUG-FORENSICS-VS-DREGG.md`): owner/admin, mintable-supply, proxy/upgradeable,
  selfdestruct, honeypot, blacklist, pausable, **owner-drain/seize**, fee-manip.
  Each door reported PRESENT / ABSENT. **Heuristic, name-matched.**
- **B. formal verification** — Halmos symbolic proof against the **real compiled
  bytecode**, all inputs symbolic, bounded call depth. Halmos is chosen because
  solc's CHC engine is **unsound on custom-error guards**
  (`chain/formal-verification/README.md §1`). Auto-harness = `gen_fv_harness.py`.
- **C. adversarial** — codex hostile pass, every finding TRIAGE-REQUIRED.
- **D. triage/report**.

**The honest gap (now narrowed).** Originally only **2 of the 9 taxonomy doors were
PROVEN** (both INV-CAP); the rest were grep-only. The auto-harness
(`gen_fv_harness.py`) now proves **five** invariants — INV-CAP × 2 plus **INV-NODRAIN**
(owner-drain/seize, door #8), **INV-REENTRANCY** (an ETH-conservation guard) and
**INV-ACCESS-CONTROL** (privileged-op authority, door #1) — and the hand-written
`chain/formal-verification/` specs prove supply-authority, pool-solvency-floor, and the
both-polarity NoDrain/Reentrancy/Access-Control specs. So doors #1, #2, #8 and the
reentrancy class are decided by PROOF, not grep. The remaining doors (proxy-upgrade,
selfdestruct, honeypot transfer-gate, blacklist, pausable, fee-manip) are still
Stage-A grep + Stage-C codex — the next invariants on the same trajectory. See §The
named-next, now DONE below for the two just added.

### (B) improvement table

| Improvement | What it buys | Classification | Effort |
|---|---|---|---|
| **More invariants — turn grep'd doors into PROOFS** | Prove owner-drain-freedom / access-control / conservation, not grep them. Converts door #8 (owner-drain) from heuristic to a symbolic proof over the full external surface. **The audit catches more by proof.** | **BUILDABLE-NOW** ← **DONE (INV-NODRAIN + INV-ACCESS-CONTROL, see below)** | S–M per invariant |
| **Reentrancy-freedom invariant** | Prove no external call re-enters a state-mutating path (a Halmos property over a call-then-callback harness). Closes another taxonomy gap by proof. | **BUILDABLE-NOW** ← **DONE (INV-REENTRANCY, see below)** | M |
| **More contract types (pool / launchpad / arbitrary)** | The auto-harness only matches the ERC-20 supply-cap shape; pool-solvency and launchpad shapes are hand-written or scaffold-only. Add auto-templates for the pool + launchpad shapes. | **BUILDABLE-NOW** | M |
| **Deeper FV — unbounded (Kontrol/KEVM or Certora)** | Halmos is symbolic-**bounded** in call depth. Kontrol/KEVM (bytecode-unbounded, K-framework) or Certora (cloud prover) close the depth caveat. | **RESEARCH** here — Kontrol/KEVM not installed (heavy K setup), Certora needs a cloud key not present (`chain/formal-verification/README.md §1`). Not runnable in this env. | L–XL |
| **Assisted-fix (propose a fix WITH a proof)** | When a counterexample is found, propose the guarded rewrite AND prove the patched shape safe (assisted, not auto-applied). | **RESEARCH** (auto-repair is a research problem; the tool deliberately audits+proposes, does not auto-rewrite, `DREGG-AUDIT-SERVICE.md:22-25`) | L |
| **Codex-triage automation** | Auto-classify codex findings CONFIRMED-REAL / FALSE-POSITIVE / KNOWN-RESIDUAL by reproducing each against source with a generated failing test. | **BUILDABLE-NOW** (partial — reproduction is mechanizable; final confirm stays human) | M |

---

## Recommendation

**(A) proof verifier:** the highest-value *marginal* buildable-now brick is **scale
K > 2 / the clearing-proof attestor**, NOT "aggregate 2 turns" — that is already
done and cited. The live-node adapter (`FullTurnProof→FinalizedTurn`) exists
(`finalized_turn_from_full_turn`, `turn/src/rotation_witness.rs:731`); do not rebuild it.

**(B) safety verifier:** **more invariants — prove the grep'd doors.** This is the
crisp, self-contained, high-signal gap: 6 of 9 doors are heuristics (proxy-upgrade,
selfdestruct, honeypot transfer-gate, blacklist, pausable, fee-manip). Converting even
one to a proof is a genuine new capability — the owner-drain conversion (INV-NODRAIN,
the seed below) is the cited demonstration on the flagship rug sample.

**Top buildable-now overall: (B) more-invariants.** Best wow/effort — it is
self-contained (one Halmos spec + a harness-generator extension), fast (sub-second
symbolic runs), does not overlap the other live lanes, and it upgrades the audit
from "grep says seize is present" to "**proof says seize is an unauthorized
drain**." (A)'s aggregation is already wired at K=2, so its remaining bricks are
heavier and partly lane-owned.

---

## The seed — INV-NODRAIN (owner-drain / seize, proven not grep'd)

**What got built (two parts, both real, both run):**

1. **A hand-written canonical spec** —
   `chain/formal-verification/test/DreggNoDrainFV.t.sol`. The invariant
   (**INV-NODRAIN**): *for any holder `victim`, any single external call by a
   `caller != victim` holding `allowance(victim, caller) == 0` leaves
   `balanceOf(victim)` non-decreasing.* A contract satisfying it has no privileged
   seize door — the only ways a holder's balance may fall are the holder's own spend
   or an approved spender's move, both excluded by the antecedent, so any drop is an
   unauthorized drain. The spec proves it on the safe `DreggLaunchToken` (single call
   and a 2-call sequence) and includes a negative control `RuggableToken` with the
   HypervaultFi `seize(from,to,value) onlyOwner` door.

2. **Pipeline integration** — `tools/dregg-audit/gen_fv_harness.py` now emits
   `check_noUnauthorizedDrain` into the auto-harness whenever the token exposes
   public `balanceOf` + `allowance`, dispatching the standard ERC-20 surface **plus
   any detected privileged `(address,address,uint256)` mover** (the seize/rescue
   shape, `transferFrom` excluded as legitimately allowance-gated; internal helpers
   excluded by visibility). So `dregg-audit` decides door #8 (owner-drain/seize) by PROOF.

**The cited runs (Halmos 0.3.3, z3, solc 0.8.30, real compiled bytecode):**

Hand-written spec (`halmos --contract DreggNoDrainFV`):
```
[PASS] check_launchToken_noDrain_seq2            (paths: 96, time: 1.41s)
[PASS] check_launchToken_noUnauthorizedDrain     (paths: 15, time: 0.16s)
[FAIL] check_ruggable_seizeIsAProvenDrain        (paths:  8, time: 0.17s)  ← Counterexample: owner seizes a non-consenting holder
Symbolic test result: 2 passed; 1 failed
```

Pipeline auto-harness, MoonRugToken sample (unsafe — `seize` present):
```
[FAIL] check_noUnauthorizedDrain(...)  ← Counterexample (drain proven, not grep'd)
```
Pipeline auto-harness, DreggLaunchToken (safe — no privileged mover):
```
[PASS] check_noUnauthorizedDrain(...)  ← proven drain-free over the full surface
```

**The true count.** The `dregg-audit` auto-harness went from **2 proven invariants**
(both INV-CAP) to **3** (INV-CAP × 2 + INV-NODRAIN). On the flagship rug sample the
owner-drain door moved from a Stage-A grep "PRESENT" (heuristic) to a Stage-B
machine COUNTEREXAMPLE (proof). On the safe launch token the door is now **proven
absent** over the full external surface, not merely grep-absent.

**Honest scope of the seed.** This is a first-brick, not the finished improvement.
The auto-harness victim-seed (`try t.mint(victim, seed)`) is best-effort for the
common owner-mintable shape; where the deployer cannot mint, the check is vacuously
safe (`b0 = 0`) and the hand-written spec is the strong path — exactly the doc's
stated division of labor (auto for the common shape, hand-written for the rest). The
proof is symbolic-**bounded** in call depth like every sibling spec (single call +
a 2-step sequence).

## The named-next, now DONE — INV-REENTRANCY + INV-ACCESS-CONTROL (proven not grep'd)

The seed's named next invariants are now built, both as hand-written both-polarity
specs and wired into the auto-harness.

**INV-REENTRANCY (reentrancy-freedom)** — `chain/formal-verification/test/DreggReentrancyFV.t.sol`.
A state-changing function's external call cannot be re-entered to drain funds owed to
others. PROVEN on the inline CEI-correct `SafeVault` AND on the REAL
`DreggSolventPool.sell` (reserves updated BEFORE `_sendEth`, pool source 155-166) under
an adversarial re-entrant seller; the inline `ReentrantVault` (CEI VIOLATION — the ETH
send precedes the balance write) yields a re-entrant-drain COUNTEREXAMPLE. Reentrancy
FV is symbolic-**bounded in re-entry depth** (the attacker re-enters once) — the honest
sibling caveat. Cited runs (Halmos 0.3.3, solc 0.8.30, real bytecode):
```
[PASS] check_safeVault_noReentrantDrain    (paths:  5)   # CEI-correct, no drain
[PASS] check_pool_sellIsReentrancySafe     (paths: 15)   # REAL pool floor survives re-entry
[FAIL] check_reentrantVault_isAProvenDrain (paths:  6)   ← Counterexample (CEI-violation drain)
```
Non-vacuity (mutation canary): strengthening the safe assert to `>= victimDep + 1` →
Counterexample (paths: 9). Restored to green.

**INV-ACCESS-CONTROL (privileged-op authority)** — `chain/formal-verification/test/DreggAccessControlFV.t.sol`.
A privileged op (mint/pause/config) is callable only by its authorized role — an
unauthorized caller cannot change privileged state. PROVEN on `DreggLaunchToken.mint`
(minter-only) and the inline `GuardedAdmin` (owner-only setters, single + 2-call
sequence); the inline `UnguardedAdmin.setConfig` (the missing-`onlyOwner` bug) yields a
COUNTEREXAMPLE. This converts taxonomy door #1 (owner/admin) from a grep that only sees
the `owner`/`minter` field to a proof the guard actually confines the op. Cited runs:
```
[PASS] check_launchToken_mintIsMinterOnly         (paths:  4)
[PASS] check_guardedAdmin_privilegedOpsAuthorized (paths:  5)
[PASS] check_guardedAdmin_authorized_seq2         (paths: 10)
[FAIL] check_unguardedAdmin_missingCheckIsCaught  (paths:  3)  ← Counterexample (missing onlyOwner)
```

**Pipeline wiring + a new contrast sample.** `tools/dregg-audit/gen_fv_harness.py` now
emits `check_noReentrancyDrain` (an ETH-conservation guard: no single external call by an
attacker drains held ETH — the auto best-effort reentrancy form; the deep both-polarity
proof is the hand-written spec) and `check_privilegedOpsAuthorized` (mint confined to
`minter`/`owner`) alongside INV-CAP and INV-NODRAIN. A new sample
`tools/dregg-audit/samples/UnguardedMintToken.sol` is HARD-CAPPED and one-shot (so
INV-CAP holds) but its `mint` is missing the `minter` guard — the auto-run PROVES INV-CAP
yet returns an INV-ACCESS-CONTROL **counterexample**, the door INV-CAP alone misses. The
Stage-B report is now **per-invariant** (a counterexample on access-control is no longer
mislabelled "hard cap violated").

**The auto-harness cited runs** (`tools/dregg-audit/dregg-audit <c> --no-fv=off`):
```
DreggLaunchToken (safe):  5/5 PROVEN  (INV-CAP×2, INV-NODRAIN, INV-REENTRANCY, INV-ACCESS-CONTROL)
MoonRugToken (unsafe):    INV-CAP + INV-NODRAIN → COUNTEREXAMPLE; INV-ACCESS-CONTROL PROVEN (its mint IS onlyOwner — the rug is uncapped supply)
UnguardedMintToken:       INV-CAP + INV-NODRAIN + INV-REENTRANCY PROVEN; INV-ACCESS-CONTROL → COUNTEREXAMPLE (missing minter guard)
```

**The updated count.** The `dregg-audit` auto-harness went from **3 proven invariants**
(INV-CAP × 2 + INV-NODRAIN) to **5** (adding INV-REENTRANCY + INV-ACCESS-CONTROL). Two
more grep'd rug doors are now decided by machine proof — door #1 (owner/admin) proven
correctly-gated (not just grep-present) and the reentrancy class (never in the Stage-A
grep taxonomy) proven both polarities. Bounds are the sibling ones: symbolic-bounded call
depth, plus re-entry-depth bounded for reentrancy.

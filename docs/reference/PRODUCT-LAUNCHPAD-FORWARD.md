# PRODUCT — Launchpad + Settlement Forward Assessment

State assessment (per surface, cited to `file:line@HEAD`) + a ranked forward plan
toward a **real testnet-ready launchpad**. Written 2026-07-17, in parallel with the
FRI-soundness main thread; this lane is app-layer product only (no soundness/kernel).

**The bar** (`project-launch-readiness-audit`): a launch is real when it is
**off-laptop, dregg-not-in-the-loop, reproducible** — not "green on ember's laptop."
This doc measures the launchpad against that bar, not against the trail's optimism.
Everything below was verified against the code at HEAD; the forge suites were RUN
locally (122 Solidity tests pass — see §Verification).

---

## 1. Per-surface state

### A. Launchpad clearing — sealed-bid → uniform-price — **BUILT, on-chain-enforced**

`chain/contracts/launchpad/DreggLaunchpad.sol` (710 lines). The full lifecycle is real
Solidity, no mock mechanism:

- **Registration / no-hidden-supply**: `registerLaunch` reverts unless
  `saleSupply + creatorAllocation + poolAllocation == totalSupply`
  (`DreggLaunchpad.sol:255-257`); a hard-capped token minted exactly once into
  launchpad custody (`:270-273`).
- **Sealed commit → reveal**: `commitBid` stores only `H(price‖qty‖salt‖bidder)`
  (`:312-329`); `revealBid` is fail-closed off-phase and must open the exact seal
  (`BidMismatch`, `:337-361`). No peek, no late-switch — enforced on-chain.
- **Uniform-price clearing**: `finalizeClearing` → `_runClearing` (`:382-450`) verifies
  the caller-supplied `order` is a **permutation** of the revealed book
  (`_assertPermutation`, `:455-463`, O(n) bool-array — no-drop/no-insert), checks
  non-increasing price, and walks a marginal fill; the last filled price is the single
  uniform price every winner pays. This is the translation-validation pattern (untrusted
  search, checked on-chain). Its fairness is Lean-proved (`Market/Optimality.lean`,
  cited at `:376-377`); the on-chain code is a faithful **replayable** implementation.
- **Non-custodial settlement**: `settleBid` (`:477-499`) — every winner pays the SAME
  `clearingPrice`, refunded the remainder; a non-winner is fully refunded.
- **Liveness backstop**: `reclaimEscrow` (`:515-535`) + `REFUND_GRACE = 7 days`
  (`:133`) — a stuck launch (dead node, withholding attestor) becomes stall-then-refund,
  never loss. The clearing and refund windows are disjoint in time (`:387-393`).
- **Graduation into a solvency-floored pool**: `graduate` (`:602-638`) seeds a
  `DreggSolventPool` with a **disclosed** fraction (`graduationSeed`, `:583-588`); a
  wrong/hidden seeding reverts (`GraduationSeedMismatch`). The pool has no owner and no
  withdraw door (`DreggSolventPool.sol`), floor-guarded (`PoolFloorBreached`).
- **Creator vesting lock**: `claimCreatorAllocation` reverts before the disclosed cliff
  (`:564-573`) — the dev-dump guard.

**Verdict: this surface is genuinely built and adversarially tested.** The
`P0ParityLaunchLoop.t.sol` suite (747 lines, 10 tests) drives create→gate→launch→clear→
lock end-to-end and asserts the three pump.fun/p0 abuses (sniping / hidden supply /
LP-drain) are *unconstructable*, both polarities, honest pole first. Not a stub.

**Honest scale note (design, not a bug):** clearing consumes the whole book on-chain —
the caller submits `order` over all revealed bidders and each bidder settles in its own
tx (`:432`, `:477`). Fine at MVP/testnet scale; a launch with thousands of bidders would
hit the block gas ceiling. Batched settlement / off-chain-sorted-with-proof clearing is
a real scaling item, not needed for a first testnet launch.

### B. OCIP cross-chain socket — **BUILT (interface), DEMO-TRUST (ceremony)**

`chain/contracts/socket/DreggVerifier.sol` (243 lines) + `TrustsADreggClearing.sol`
(112 lines, a demo third-party consumer).

- The socket wraps the VK-epoch registry (`IGroth16VerifierRegistry`) so a VK rotation is
  an `advanceEpoch` tx invisible to consumers (`DreggVerifier.sol:206-242`). Fail-closed
  on a codeless registry (`:188-196`). This is real, correct wrapping code.
- `TrustsADreggClearing` gates its economic action on two on-chain checks: which-dregg
  (trusted-anchor equality, `:81-85`) and is-it-valid (real BN254 pairing through the
  socket, `:89-91`). Clean security-provider loop.
- **The trust residual is named in-code and is real** (`DreggVerifier.sol:52-61`): the
  registry's epoch-0 VK is a **single-party DEV Groth16 ceremony (toxic-waste-known)**.
  Whoever ran it could forge. This is a demonstration of the interface end-to-end, NOT
  production trust, until the MPC ceremony (ember-gated) replaces the epoch-0 VK.

**Verdict: the socket is a working, honestly-scoped interface demo. Production trust is
ceremony-gated, not code-gated** — the swap is an `advanceEpoch`, the socket is unchanged.

### C. Deployer-gate / proof-attestor — **BUILT; one honestly-named TRUSTED link**

`chain/contracts/launchpad/DreggDeployerGate.sol` (292 lines) — pluggable arms (bond /
public interview / private ZK-credential interview / cleared audit), operator-selected via
`acceptedArms` bitmask (`:32-41`, `:208-246`). Fail-closed on unknown/disabled/malformed
(`:245`). The **audit scoping** (`attestAuditFor` → `auditScope`, `:198-204`, checked at
`:239-240`) is what composes the token-factory into CREATE: a report cleared for one
disclosure cannot be spent on another. Real, tested (`DreggDeployerGate.t.sol` +
`P0ParityLaunchLoop`).

`chain/contracts/launchpad/DreggProofAttestor.sol` (319 lines) — the PROOF arm. A
launch's clearing is attested iff a real dregg Groth16 wrap proof, **bound to this
launch**, verifies through the socket (`attestClearing`, `:253-299`). The launch-binding
(`statementDigest(s) != bnd.statementDigest → false`, `:284`) is load-bearing and
mutation-canaried (`test_WrongLaunchProofIsRefused`). Clearing VALUES are NOT taken from
the proof — they are computed on-chain by `_runClearing` (rung-1 replayable), so a corrupt
binder can only refuse (liveness → refund), never misprice.

- **The TRUSTED link (real gap, honestly named, `DreggProofAttestor.sol:52-66`):** the
  25-lane dregg statement (`genesis_root · final_root · num_turns · chain_digest`) has NO
  lane for launch-id / clearing-price / book-commit. So a valid proof attests "a conserved
  dregg transition to `final_root` exists," NOT "and that transition IS launch #7's
  clearing at p*." The binder asserts the link; the circuit does not carry it. **Closing
  it is a circuit/statement change** (new lanes in the gnark `SettlementCircuit`, or a
  Poseidon2 inclusion of the tuple under `final_root`) — NOT wiring. Soundness-adjacent,
  ember-gated, big.

**Verdict: the gate is production-shaped; the proof-attestor is real but its rung-2 trust
rests on (i) the named TRUSTED link and (ii) the same DEV-ceremony VK as the socket.** The
launchpad pins the attestor SEAM, never an arm (`IClearingAttestor`), so rung-1
(`attestor == address(0)`, fully on-chain replayable) needs neither.

### D. Token-factory settlement path — **BUILT, real artifacts committed**

`tools/token-factory/` — spec → FV'd-emit → Halmos hard-cap proof → gate. The GOOD/RMOON
artifacts are **git-tracked** (`git ls-files tools/token-factory/artifacts/` = 8 files)
and READ + HASHED by `P0ParityLaunchLoop.t.sol:127-135` (not a stand-in hash). The
factory emits from the FV'd `DreggLaunchToken.sol` template (no owner/seize/pause/mint
door but the disclosed one-shot). `DreggSettlement` settlement path is live on-chain (see
§E) and its real-proof fixture verifies (`DreggSettlementRealProof.t.sol`, 7 tests pass).

**Note:** `tools/token-factory/artifacts/RMOON/*` shows **uncommitted working-tree drift**
(3 files modified — cosmetic; the P0 test's `**Verdict: REJECTED.**` / `COUNTEREXAMPLE
(cap breakable)` assertions still pass). Not this lane's file to commit; flagged for the
owning lane.

### E. What is actually deployed — **settlement yes (fixture), launchpad NO**

`chain/DEPLOYMENTS.md`: a real dregg proof settled on **Base-Sepolia (chainId 84532)**
on 2026-07-13 (`DreggSettlement 0x6c87b535…`, settle tx verified on-chain via the Solidity
pairing). Honest caveats in the doc: fixture proof (not a live user turn), dev
single-party ceremony. **The launchpad itself has never been broadcast** — the Robinhood
Chain deploy is dry-run-validated only (`script/DeployLaunchpad.s.sol`), held un-fired
(ember's button).

---

## 2. The frontier — the single most-blocking gap

**The entire on-chain product surface is "green on ember's laptop" — it is not
reproducible off this machine, and no CI touches it.** This is the exact disease named in
`project-launch-readiness-audit`, and it sits *underneath* every other gap: you cannot
have a trustworthy testnet launch of code a stranger (or a CI runner) cannot even compile.

Two compounding, verified wounds:

**W1 — the forge suite cannot build on a fresh clone.**
`chain/lib/forge-std` is an **orphaned submodule**: its gitdir exists
(`.git/modules/chain/lib/forge-std`, forge-std v1.16.2 @ `bf647bd6`), but there is **no
`.gitmodules`** and `chain/.gitignore:4` ignores `lib/`. So `git ls-files chain/lib/` is
empty — a fresh clone gets an empty `chain/lib/`, and `forge test`/`forge build` fail
immediately (`cannot find forge-std`). This is a classic `git add -A` / revert casualty
(the exact hazard CLAUDE.md warns about). No setup script or doc compensates (grep for
`forge install` across `chain/README`, `README`, `QUICKSTART`, `scripts/` = empty).

**W2 — no CI runs forge at all.** Grep across `.github/workflows/` for
`forge|foundry|\.sol|solidity|solc` = **empty**. The 122 passing Solidity tests
(launchpad 109 + settlement/routing 13) provide assurance ONLY when someone runs forge by
hand on a machine that happens to have forge-std present. The `repro-gate.yml` and `ci.yml`
gates are cargo-only; `dregg-chain` is a Rust crate whose Solidity contracts cargo never
compiles. So the marquee product surface has **zero automated, reproducible verification**.

W2 depends on W1 (CI can't run forge until forge-std is reproducibly present). Fix W1,
then W2, and the launchpad crosses from laptop-green to off-laptop-reproducible — the bar.

The ceremony (DEMO-TRUST) and the attestor TRUSTED-link are bigger and real, but they gate
**rung-2 production trust**, not a **rung-1 reproducible testnet launch** (rung-1 is fully
on-chain-enforced, needs no dregg proof, and is what the trail calls testnet-ready).

---

## 3. "Green on ember's laptop" wounds (summary)

| Wound | Evidence | Severity |
|---|---|---|
| forge-std orphaned submodule; `lib/` gitignored | `chain/.gitignore:4`; no `.gitmodules`; `.git/modules/chain/lib/forge-std` | **Frontier** — fresh clone can't build contracts |
| No forge/foundry CI job | grep of `.github/workflows/` = empty | **Frontier** — 122 tests only ever laptop-green |
| Launchpad never deployed | `DEPLOYMENTS.md` (only settlement live) | Expected (ember's button) — not a wound, but nothing frozen |
| DEV single-party Groth16 ceremony | `DreggVerifier.sol:52-61` | rung-2 trust — ember-gated MPC |
| Attestor clearing-binding is TRUSTED | `DreggProofAttestor.sol:52-66` | rung-2 trust — circuit change, ember-gated |
| RMOON factory artifacts uncommitted drift | `git diff tools/token-factory/artifacts/RMOON/` | Minor — another lane's file |

No **mock-presented-as-real** was found in the launchpad surfaces: `launchpad-web` reads
the real contract / real node with no mirror (`launchpad-web/README.md`), `_runClearing` is
real, the factory artifacts are real and hashed. The wounds are reproducibility + honestly-
named trust residuals, not disguised mocks. That is a genuinely good posture — the gap is
"nothing frozen / not reproducible off-laptop," exactly the disease, cleanly localized.

---

## 4. Ranked forward plan

Ranked by (unblocks-the-bar × safety-to-do-now). Each: what / why / effort / risk.

**P1 — Restore `forge-std` as a tracked git submodule; un-ignore it.** *(PROPOSED — ember)*
- *What:* re-register the orphaned submodule so a fresh clone gets forge-std. The metadata
  already exists (`.git/modules/chain/lib/forge-std`, v1.16.2 @ `bf647bd6`,
  origin `foundry-rs/forge-std`). Concretely:
  ```
  # add .gitmodules entry for chain/lib/forge-std (path + url + branch)
  # narrow chain/.gitignore so lib/ ignores build output but NOT lib/forge-std
  git submodule add -f https://github.com/foundry-rs/forge-std chain/lib/forge-std   # or restore gitlink
  git -C chain/lib/forge-std checkout bf647bd6   # pin the working version
  ```
- *Why:* the frontier (W1). Without it, off-laptop reproducibility is impossible and P2
  can't exist.
- *Effort:* ~30 min. *Risk:* MEDIUM — git-structural, changes every clone, touches a
  gitignore other lanes may rely on, and a half-done submodule is worse than the current
  documented state. Shared-tree git ops with parallel agents are hazardous (CLAUDE.md).
  **Ember-gated: hand the exact commands, don't fire in a shared tree.**

**P2 — Add a `forge test` CI workflow (`chain/`).** *(PROPOSED — blocked on P1)*
- *What:* a `.github/workflows/chain-forge.yml` that checks out with submodules, installs
  foundry (pinned), and runs `forge test` in `chain/` on push/PR.
- *Why:* the frontier (W2) — turns the 122 laptop-green tests into a reproducible gate.
- *Effort:* ~1 hr. *Risk:* LOW once P1 lands (the suite already passes; runs in ~50 ms of
  test time). RED until P1, so must follow it.

**P3 — Deploy rung-1 launchpad to a public testnet.** *(PROPOSED — ember's button)*
- *What:* `forge script DeployLaunchpad.s.sol --rpc-url robinhood_testnet --broadcast`
  (or base_sepolia), `attestor == address(0)` (rung-1 replayable), then run one real
  launch (register → commit → reveal → clear → settle → graduate) through `launchpad-web`.
- *Why:* the bar's "off-laptop, dregg-not-in-the-loop" — rung-1 needs no dregg proof, so
  it is honestly deployable today. This is the first *frozen, live* artifact.
- *Effort:* ~1 hr once P1/P2 give confidence. *Risk:* LOW (dry-run-validated,
  permissionless L2) but a real broadcast + funded key = **ember's decision**.

**P4 — MPC Groth16 ceremony to replace the epoch-0 DEV VK.** *(PROPOSED — ember-gated, big)*
- *What:* run a multi-party trusted setup; `advanceEpoch` the ceremony VK into the
  registry. Socket + attestor + settlement are unchanged (that is the whole point of the
  seam).
- *Why:* the only thing between DEMO-TRUST and production trust for rung-2 (attested
  clearings + cross-chain settlement). *Effort:* days + coordination. *Risk:* HIGH-value,
  process-heavy, ember-gated.

**P5 — Close the attestor TRUSTED clearing-binding link.** *(PROPOSED — ember-gated, big)*
- *What:* commit `(launchId, clearingPrice, bookCommit)` INSIDE the proof's public
  statement — new lanes in the gnark `SettlementCircuit`, or a Poseidon2 inclusion of the
  tuple under `final_root` verified on-chain — so `attestClearing` can bind them.
- *Why:* upgrades rung-2 from "a valid transition exists + trusted link" to "the attested
  transition IS this clearing." *Effort:* circuit + statement + verifier change (large).
  *Risk:* HIGH — soundness-adjacent, coordinate with the FRI/stark-kill thread. Ember-gated.

**P6 — Batched/scalable settlement + clearing.** *(PROPOSED — post-testnet)*
- *What:* batch `settleBid`; consider off-chain-sorted clearing with an on-chain-checked
  proof to lift the whole-book-on-chain gas ceiling.
- *Why:* pump.fun-scale books. *Effort:* medium. *Risk:* touches the clearing path →
  ember-gated; not needed for a first testnet launch.

---

## 5. What was EXECUTED vs PROPOSED

**EXECUTED (safe, verified):**
- This assessment doc (`docs/reference/PRODUCT-LAUNCHPAD-FORWARD.md`).
- **Verified reproducibility of the on-chain suite locally** by running the forge tests
  (below) — the evidence for the frontier finding, not a code change.

**PROPOSED (for ember — nothing risky fired):** P1–P6 above. Every one is either
git-structural in a shared tree (P1/P2), a real deploy/ceremony/button (P3/P4), or a
settlement/clearing/circuit change (P5/P6) — all correctly outside the "clear-cut, safe,
self-contained" bar. No settlement/clearing/consensus path was touched. No deploy fired.

The correct next move is **P1 → P2**: they convert the launchpad from laptop-green to
off-laptop-reproducible, which is the launch bar and the precondition for everything else.

---

## Verification (this session, on this machine)

```
chain$ forge test --match-contract 'DreggLaunchpad|P0Parity|DreggSocket|DreggDeployerGate|DreggLaunchpadProofAttestor'
  → 109 passed, 0 failed  (9 suites)
chain$ forge test --match-contract 'DreggSettlementRealProof|DrexRoutingE2E'
  → 13 passed, 0 failed
```
forge 1.7.1. Both runs depend on `chain/lib/forge-std` being present locally — the very
dependency a fresh clone lacks (§2 W1). That dependence IS the frontier finding.

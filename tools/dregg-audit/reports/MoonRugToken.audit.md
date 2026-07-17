# DREGG-kernel contract audit — `MoonRugToken.sol`

Pipeline: `tools/dregg-audit/dregg-audit` · Generated: 2026-07-17T06:20:28Z
Target: `/Users/ember/dev/breadstuffs/tools/dregg-audit/samples/MoonRugToken.sol`

> **Assisted-audit tool, not a certification.** Stages A (rug-forensics) and
> B (formal verification) are machine-decided. Stage C (codex) is an LLM
> adversarial pass whose findings are emitted **TRIAGE-REQUIRED** — a human
> must confirm each against source. This tool finds + proposes; it does **not**
> auto-rewrite to secure, and green here is **not** a security guarantee.

## A. Rug-forensics — the rug-door taxonomy

Deterministic scan for the rug doors dissected in
`docs/deos/RUG-FORENSICS-VS-DREGG.md` (owner-drain / hidden-mint / proxy-upgrade
/ honeypot / blacklist / pause / selfdestruct / fee-manipulation). A door marked
PRESENT is a *surface to review*, not proof of a rug; ABSENT means the pattern
does not occur in source (structural absence, the strongest anti-rug signal).

| # | Rug door | Verdict | Evidence (line:match) |
|---|----------|---------|-----------------------|
| 1 | owner/admin role | **PRESENT** | 48: `modifier onlyOwner() {`<br>49: `require(msg.sender == owner, "not owner");`<br>61: `function mint(address to, uint256 amount) external onlyOwner`<br>98: `function seize(address from, address to, uint256 value) exte`<br> |
| 2 | mintable supply (mint fn) | **PRESENT** | 61: `function mint(address to, uint256 amount) external onlyOwner`<br> |
| 3 | proxy / upgradeable | ABSENT | _(no match)_ |
| 4 | selfdestruct / kill | **PRESENT** | 118: `selfdestruct(payable(owner));`<br> |
| 5 | honeypot / transfer-gate | **PRESENT** | 42: `mapping(address => bool) public isWhitelisted; // SQUID `mar`<br>89: `require(!paused \|\| isWhitelisted[from], "trading paused");`<br>113: `isWhitelisted[a] = b;`<br> |
| 6 | blacklist | **PRESENT** | 43: `mapping(address => bool) public blacklisted;`<br>90: `require(!blacklisted[from], "blacklisted");`<br>109: `blacklisted[a] = b;`<br> |
| 7 | pausable / freeze | **PRESENT** | 104: `function setPaused(bool p) external onlyOwner {`<br> |
| 8 | owner-drain / seize | **PRESENT** | 98: `function seize(address from, address to, uint256 value) exte`<br> |
| 9 | fee / tax manipulation | ABSENT | _(no match)_ |

_No mint mitigation detected_: `mint` has **no visible one-shot latch or cap
enforcement** — a likely mintable-supply rug door. Stage B will attempt to
prove or refute the hard cap symbolically.

## B. Formal verification — Halmos symbolic proof

Auto-generated symbolic harness (`fv-workspace/test/GenFV.t.sol`) proving the
standard anti-rug invariants against the real compiled bytecode, all inputs
symbolic: **INV-CAP** (`totalSupply<=cap`, EVM twin of the Lean supply theorem
`execMintA_iff_spec`, `metatheory/Dregg2/Verify/KeystoneAuditSupply.lean:124`),
and — when the shape exposes them — **INV-NODRAIN** (owner-drain/seize),
**INV-REENTRANCY** (ETH-conservation guard) and **INV-ACCESS-CONTROL** (mint
confined to its `minter`/`owner` role). The deep both-polarity re-entry proof is
the hand-written spec `chain/formal-verification/DreggReentrancyFV.t.sol`.

```
Running 5 tests for test/GenFV.t.sol:GenFV
Counterexample: 
[FAIL] check_cap_singleCall(uint256,uint8,address,address,address,uint256) (paths: 14, time: 0.30s, bounds: [])
Counterexample: 
Counterexample: 
Counterexample: 
[FAIL] check_cap_twoMints(uint256,address,address,uint256,address,address,uint256) (paths: 14, time: 0.38s, bounds: [])
[PASS] check_noReentrancyDrain(uint256,address,uint8,address,address,uint256) (paths: 13, time: 0.46s, bounds: [])
Counterexample: 
[FAIL] check_noUnauthorizedDrain(uint256,address,uint256,uint8,address,address,address,uint256) (paths: 18, time: 0.64s, bounds: [])
[PASS] check_privilegedOpsAuthorized(uint256,address,address,uint256) (paths: 3, time: 0.06s, bounds: [])
Symbolic test result: 2 passed; 3 failed; time: 1.87s
```

| Invariant | Check | Verdict |
|-----------|-------|---------|
| INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply) | `check_cap_singleCall` | **COUNTEREXAMPLE** |
| INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply) | `check_cap_twoMints` | **COUNTEREXAMPLE** |
| INV-REENTRANCY — no external call drains held ETH (reentrancy, ETH-conservation form) | `check_noReentrancyDrain` | PROVEN |
| INV-NODRAIN — no unauthorized balance drain (door #8, owner-drain/seize) | `check_noUnauthorizedDrain` | **COUNTEREXAMPLE** |
| INV-ACCESS-CONTROL — privileged op confined to its role (door #1, owner/admin) | `check_privilegedOpsAuthorized` | PROVEN |

**Result: HALMOS FOUND 3 COUNTEREXAMPLE(S).** The invariant(s)
below are machine-DISPROVEN (CONFIRMED-REAL, no human triage — it is a proof):
- INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply)
- INV-CAP — hard cap `totalSupply<=cap` (door #2, mintable supply)
- INV-NODRAIN — no unauthorized balance drain (door #8, owner-drain/seize)

Still PROVEN (hold over all inputs, bounded): check_noReentrancyDrain check_privilegedOpsAuthorized .
(A door can pass one invariant and fail another — e.g. a mint that respects
the cap but is missing its access-check passes INV-CAP and fails
INV-ACCESS-CONTROL.)

## C. Adversarial audit — codex hostile pass (TRIAGE-REQUIRED)

Tool: `codex exec --sandbox read-only` (`codex-cli 0.144.1`). Raw
output captured at `MoonRugToken.codex.log`. Exit: 0. Each finding below is
**TRIAGE-REQUIRED** — codex errs both ways; confirm every one against source.

    FINDING: Unlimited owner minting makes the disclosed cap fictitious
    SEVERITY: Critical
    CLASS: Rug/exit vectors
    LOCATION: `mint()` — `totalSupply += amount` without checking `cap`
    WHY: The owner can mint an effectively unlimited number of tokens to itself at any time. After liquidity or market demand develops, it can dump those tokens into an AMM and extract the paired asset, collapsing the price and leaving buyers with worthless tokens. The public `cap` variable is never enforced and therefore provides deceptive assurance.
    FIX: Remove post-deployment minting, or enforce `totalSupply + amount <= cap` with an immutable cap and narrowly constrained, preferably one-shot, issuance authority.
    
    FINDING: Owner can directly steal any holder’s entire balance
    SEVERITY: Critical
    CLASS: Rug/exit vectors
    LOCATION: `seize()` — `balanceOf[from] -= value; balanceOf[to] += value`
    WHY: The owner can name any holder as `from` and itself as `to`, without an allowance or signature. It can take the holder’s complete balance, and the function bypasses the pause, blacklist, and normal transfer checks. Checked subtraction only prevents taking more than the recorded balance.
    FIX: Delete `seize()`; no administrative role should be able to debit arbitrary holder balances.
    
    FINDING: Pause and whitelist controls create a configurable honeypot
    SEVERITY: Critical
    CLASS: Rug/exit vectors
    LOCATION: `_transfer()`, `setPaused()`, and `setWhitelist()`
    WHY: The owner can whitelist the AMM pair and insider wallets, then set `paused = true`. Buys still work because the whitelisted pair is the sender, while ordinary holders cannot transfer tokens back to the pair to sell because they are not whitelisted. Insiders can remain able to sell while public buyers are trapped.
    FIX: Remove owner-controlled transfer gating after launch, or use a one-way trading-enablement mechanism that can never be disabled and cannot exempt insiders.
    
    FINDING: Owner can selectively and permanently freeze individual holders
    SEVERITY: High
    CLASS: Rug/exit vectors
    LOCATION: `_transfer()` — `require(!blacklisted[from], "blacklisted")`; `setBlacklist()`
    WHY: The owner can blacklist a holder immediately before that holder sells or transfers. The address may continue receiving tokens because only `from` is checked, but it can never dispose of them until the owner chooses to unblock it. This enables selective confiscation of liquidity and targeted retaliation.
    FIX: Remove the blacklist, or restrict any compliance mechanism through transparent governance, objective criteria, time limits, appeal procedures, and an emergency-only scope.
    
    FINDING: Owner can manipulate an AMM pair and drain its paired reserve
    SEVERITY: Critical
    CLASS: Any economic / mechanism-level manipulation
    LOCATION: `seize()` when `from` is an AMM pair
    WHY: An AMM pair is merely another address in `balanceOf`, so the owner can seize nearly all of the pair’s MOON balance. It can then call a typical pair’s `sync()` to establish a tiny MOON reserve while leaving the paired reserve intact, and sell seized or newly minted MOON back at the manipulated price. This can extract nearly all ETH, stablecoins, or other paired assets without owning LP tokens.
    FIX: Delete arbitrary balance seizure and unrestricted minting; balances belonging to contracts and users must change only through authorized ERC-20 transfers.
    
    FINDING: Owner-controlled selfdestruct is a chain-dependent kill and native-asset drain switch
    SEVERITY: High
    CLASS: Rug/exit vectors
    LOCATION: `kill()` — `selfdestruct(payable(owner))`
    WHY: On EVM environments with legacy `SELFDESTRUCT` behavior, the owner can delete the contract code and make every recorded token balance unusable. Under EIP-6780 semantics, an established contract generally is not deleted, but any native currency forced into the contract is still transferred to the owner. Thus the exact bricking impact is chain-dependent, but the privileged drain instruction remains.
    FIX: Remove `kill()` entirely; if asset recovery is required, implement a narrowly scoped recovery function that cannot affect token balances and is protected by a timelock and multisignature governance.
    
    FINDING: A permanent single-key owner controls every critical rug mechanism
    SEVERITY: High
    CLASS: Access control
    LOCATION: `owner`, `onlyOwner`, and all privileged setter, mint, seize, and kill functions
    WHY: The privileged functions are not missing their modifier; the access-control defect is that one deployer-controlled address holds unlimited, permanent authority. A malicious deployer or one compromised key can inflate supply, steal balances, trap sellers, manipulate pools, and invoke the kill switch. There is no timelock, multisignature requirement, role separation, or governance veto.
    FIX: Remove the rug-capable privileges themselves; for any genuinely necessary administration, use least-privilege roles, a multisignature, a public timelock, and irrevocable limits on what governance can change.
    
    FINDING: Allowance replacement is vulnerable to the standard approval race
    SEVERITY: Medium
    CLASS: Access control
    LOCATION: `approve()` — `allowance[msg.sender][spender] = value`
    WHY: When a user replaces an existing nonzero allowance, the spender can front-run the approval transaction and spend the old allowance. After the replacement transaction executes, the spender receives the new allowance and can spend that as well. The user may therefore lose both the old and new amounts.
    FIX: Require a nonzero allowance to be reset to zero before assigning another nonzero value, and provide atomic `increaseAllowance` and `decreaseAllowance` operations.
    
    FINDING: Transfers can irreversibly lock tokens at unusable addresses
    SEVERITY: Low
    CLASS: Denial-of-service, stuck/locked/unrecoverable funds
    LOCATION: `_transfer()` and `mint()` — no rejection of `address(0)` or `address(this)`
    WHY: A holder can transfer tokens to the zero address, where they are unrecoverable while `totalSupply` remains unchanged. Tokens sent to the token contract itself are also stuck because it has no recovery path. The owner can additionally mint to the zero address, creating nominal supply that can never circulate.
    FIX: Reject zero-address recipients in minting and transfers; either reject transfers to `address(this)` or provide a tightly scoped, non-owner-confiscatory recovery design.
    
    FINDING: No contract-level traditional LP-token removal path
    SEVERITY: Info
    CLASS: Rug/exit vectors
    LOCATION: Not applicable — no router, pair-burn, or LP-token custody functions
    WHY: This contract does not itself create, custody, lock, or remove LP tokens, so a conventional LP withdrawal cannot be established from this source alone. The deployer may still hold and remove LP tokens externally, which must be checked from deployment and on-chain liquidity records. The minting and pair-seizure paths already permit reserve extraction without LP removal.
    FIX: Independently verify that externally issued LP tokens are burned or credibly time-locked and disclose their ownership.
    
    FINDING: No proxy-upgrade or delegatecall backdoor is present
    SEVERITY: Info
    CLASS: Rug/exit vectors
    LOCATION: Not applicable — entire contract
    WHY: The supplied contract contains no proxy fallback, implementation slot, `delegatecall`, or upgrade function. Subject to confirming that this code is deployed directly rather than behind an external proxy, its runtime logic cannot be replaced through this source.
    FIX: Deploy the contract directly and verify the deployed runtime bytecode and proxy status on-chain.
    
    FINDING: No transfer fee or adjustable tax exists
    SEVERITY: Info
    CLASS: Rug/exit vectors
    LOCATION: Not applicable — `_transfer()`
    WHY: `_transfer()` moves exactly `value` from sender to recipient and contains no fee calculation or fee recipient. There is no tax-setting function, so a confiscatory transfer tax is not present in the supplied code. The pause, whitelist, and blacklist controls provide a more direct sell-blocking mechanism.
    FIX: No fee-specific change is required; remove the separate transfer-control rug mechanisms identified above.
    
    FINDING: No reentrancy-capable interaction path is present
    SEVERITY: Info
    CLASS: Reentrancy
    LOCATION: Not applicable — transfer, approval, minting, and seizure paths
    WHY: State-changing token functions make no arbitrary external calls and invoke no receiver hooks. `SELFDESTRUCT` is not an ordinary callback-producing call, so there is no reentrant state-update path in the supplied code.
    FIX: No reentrancy-specific remediation is required; retain this no-callback design if the contract is rewritten.
    
    FINDING: No exploitable unchecked arithmetic or rounding operation is present
    SEVERITY: Info
    CLASS: Integer over/underflow, precision/rounding loss, unchecked math
    LOCATION: `mint()`, `_transfer()`, `transferFrom()`, and `seize()`
    WHY: Solidity 0.8.20 checks the additions and subtractions, so insufficient balances, insufficient allowances, and numeric overflow revert atomically. The contract performs no division or fixed-point calculation that could introduce rounding loss. Ignoring `cap` is a critical authorization and supply-policy defect, not an arithmetic bypass.
    FIX: Retain checked arithmetic and add the missing explicit cap and address validations described above.
    

> OVERALL VERDICT: This contract rugs. The owner can steal any holder’s tokens through `seize()`, trap buyers with `setPaused(true)` plus selective whitelisting, freeze individual sellers with `setBlacklist()`, mint unlimited supply despite the advertised `cap`, and drain AMM paired assets through mint-and-dump or pair-balance seizure followed by reserve synchronization. On legacy EVMs, `kill()` can additionally brick every balance; under modern EIP-6780 rules it still transfers forced native currency to the owner. Separately, an approved spender can exploit allowance replacement, and users can irreversibly lose tokens by transferring them to unusable addresses.

## D. Triage summary

| Source | Finding | Verdict | Severity | Proposed fix |
|--------|---------|---------|----------|--------------|
| A (auto) | Rug doors present: owner/admin role mintable supply (mint fn) selfdestruct / kill honeypot / transfer-gate blacklist pausable / freeze owner-drain / seize | **REVIEW** | High | Remove/constrain each present door; see §A |
| B (auto/proof) | Hard-cap invariant | COUNTEREXAMPLE (3 invariant(s) violated) | Critical | If COUNTEREXAMPLE: add one-shot latch + `amount<=cap` guard (see `DreggLaunchToken.mint`) |
| C (codex) | see §C | **TRIAGE-REQUIRED** | per-finding | per-finding; human confirms vs source |

**Verdict legend.** Stage A/B rows are machine-decided. Stage C rows require a
human to mark each finding CONFIRMED-REAL / FALSE-POSITIVE / KNOWN-RESIDUAL
against the source (the `docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` division of labor:
codex hunts + reasons; a human verifies + reproduces). A confirmed bug should be
reproduced with a failing test before the proposed fix is applied by a developer.

---
_Assisted-audit tool — finds vulns + proposes fixes with a proof where a standard
invariant applies. NOT a push-button certification (needs human review); does NOT
auto-rewrite to secure (audit + propose; a developer applies)._

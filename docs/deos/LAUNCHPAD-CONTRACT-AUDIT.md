# DreggLaunchpad — Independent Adversarial Contract Audit

Date: 2026-07-14 · Scope: `chain/contracts/launchpad/` @ working tree on `2f7059594`
(the backstop lane: timeout-refund + CommitteeAttestor + fraud-proof).

Files audited (1325 LOC): `DreggLaunchpad.sol`, `DreggLaunchToken.sol`,
`DreggSolventPool.sol`, `CommitteeAttestor.sol`, `IClearingAttestor.sol`,
`ILaunchEligibility.sol`.

## Why this audit exists

The forge suite (41/41 before this audit) is **grading our own homework** — we wrote
both the contracts and the tests. This is an *independent* adversarial pass: feed the
full source to a hostile external auditor (codex / GPT-5.6-class, reasoning=xhigh),
then **triage every finding against the source** (a codex finding can be a false
positive — codex errs both ways), reproduce the real ones with a *failing* forge test,
and fix them. A confirmed bug is a WIN to be fixed and surfaced, not hidden.

## The codex run (cited, real)

- Tool: `codex-cli 0.144.1`, `codex exec --skip-git-repo-check`, reasoning effort `xhigh`.
- Invocation: all 6 contracts inlined verbatim into a hostile-auditor prompt covering
  every vuln class (reentrancy, access-control, integer/precision, the rug vectors,
  the uniform-price/commit-reveal economics, the timeout-refund disjoint-window, the
  committee-sig attestor, the fraud-proof, DoS, stuck/locked funds).
- Raw output captured (~4975 lines) at
  `…/scratchpad/codex_out.log` (session scratchpad); codex ran with repo access and,
  after its analysis, independently explored the tree and re-ran forge.

**Headline:** codex did NOT find a theft or rug vector — its overall verdict is a
custody-safety claim: *"no user asset held by the launchpad, token, or pool can be lost
or stolen; the worst outcome is a delayed or re-run clearing."* It DID independently
surface the **selective-non-reveal weakness class** (framing it as griefing, with a
"reveal-forfeit bond" hardening suggestion). Our triage then turned that weakness class
into a **concrete, exploitable, CONFIRMED stuck-funds defect** that codex's high-level
pass glossed — and fixed it. So codex's blanket "no asset can be lost" was, pre-fix,
slightly overstated: an unrevealed committer's escrow *was* a permanent loss.

## Findings, triaged

### CONFIRMED-REAL

#### C1 — Committed-but-unrevealed escrow is permanently LOCKED once a launch clears (Medium; stuck funds) — FIXED

`DreggLaunchpad.settleBid` / `reclaimEscrow`.

A bidder escrows ETH at `commitBid` and then never reveals. Once *any* caller lands a
valid `finalizeClearing` (phase → `Cleared`), that bidder's deposit is trapped forever:

- `settleBid` required `b.revealed` (`if (!b.revealed || b.settled) revert NothingToSettle()`),
  so an unrevealed committer cannot settle.
- `reclaimEscrow` refuses a cleared launch (`if (phase == Cleared || Finalized) revert
  LaunchAlreadyCleared()`), so the timeout backstop cannot refund them either.

There is **no third path** — the deposit is never counted in `proceeds` (only winners'
payments are) and never transferred out. It is dead-locked in the contract with no
beneficiary. This is *worse* than a forfeiture penalty (which would at least route the
funds somewhere): it is pure dead-weight loss.

**Griefing amplifier:** `finalizeClearing` is permissionless and allowed the instant
`block.timestamp >= revealEnd`. An attacker can force-clear a launch (even an empty book
with `order = []`) the moment the reveal window ends, deliberately trapping every
committed-but-unrevealed bidder *before* the refund window (`revealEnd + grace`) would
otherwise have opened.

**Intent inconsistency (why this is a bug, not a design choice):** the contract already
*intends* to refund unrevealed committers — `test_RefundWorksForCommittedButNeverRevealed`
proves an unrevealed committer reclaims their full escrow on the *stalled* (never-cleared)
path. The cleared path simply forgot the same case.

**Reproduction:** `test_UnrevealedCommitterRecoversAfterClearing`
(`chain/test/DreggLaunchpadAuditFixes.t.sol`): alice+bob reveal and clear a launch;
carol commits real ETH and never reveals. On the **pre-fix** contract the test fails with
`NothingToSettle()` (carol's escrow is unreachable). On the **fixed** contract carol
recovers her full escrow.

**Fix** (`DreggLaunchpad.settleBid`): make the settle path the canonical post-clear
escrow-exit for *any committed bidder*. Changed the guard `!b.revealed` → `!b.committed`,
so a committed-but-unrevealed bidder (`filled == 0`) is settled as a full refund
(`payment = clearingPrice * 0 = 0`, `refund = deposit`). The escrow is zeroed before the
external send (CEI preserved), and the settle/refund paths remain phase-disjoint (a
cleared launch settles; a stalled launch reclaims — never both). This also neutralizes the
force-clear griefing amplifier: a forced early clear now leaves every unrevealed committer
with a full refund via `settleBid`, never a loss.

Post-fix suite: **42/42** (`forge test --match-path "test/DreggLaunchpad*.t.sol"` — 4
suites, 42 passed, 0 failed), the +1 being the new exploit test.

### FALSE-POSITIVE / VERIFIED-SAFE (triaged against source; no change warranted)

- **Reentrancy on `reclaimEscrow` / `settleBid` / pool `buy`/`sell`.** All follow
  checks-effects-interactions: state is latched/zeroed *before* the external ETH send
  (`reclaimEscrow` sets `refunded=true; deposit=0` first; `settleBid` sets `settled=true;
  deposit=0` first; the pool updates reserves before `_sendEth`). `DreggLaunchToken` has no
  transfer callback (no ERC-777/hook surface), so token moves cannot reenter. The one
  cross-function path (a malicious winner's refund reentering `graduate`) only reaches a
  *successful* `graduate` once `proceeds == canonicalProceeds`, and every amount it moves
  is disclosed/enforced — no theft. Safe.

- **Second mint / hidden supply (honeypot / rug).** `DreggLaunchToken.mint` is
  `onlyMinter` + one-shot latch (`minted`) + `amount <= cap`; the launchpad mints exactly
  once for the full disclosed cap. `registerLaunch` reverts unless
  `sale + creator + pool == total` (`SupplyDoesNotClose`). No second door. Safe.

- **Pool drain / LP-pull / honeypot.** `DreggSolventPool` tracks reserves internally (a
  token donation cannot move price or accounting), guards every swap with the disclosed
  floor (`PoolFloorBreached`) and a non-decreasing-`k` check (`ConstantProductViolated`),
  and has no owner/withdraw door. Safe (this is the rung-6 solvency tooth).

- **Committee signature replay / malleability / dedup / quorum bypass.** `attestationDigest`
  binds `DOMAIN ‖ chainid ‖ address(this) ‖ launchId ‖ saleSupply ‖ clearingPrice ‖
  bookCommit` — non-replayable across chains, attestors, launches, and tuples. `_recover`
  normalizes `v` and rejects the upper-half `s` range (EIP-2 low-s, correct secp256k1
  half-order constant). `_quorumSigned` requires *strictly ascending* signer addresses, so a
  duplicated rogue signature counts at most once. `threshold` is `1..n` and set once.
  A malformed proof is caught by the `try/catch decodeSigs` and returns `false` (never
  reverts). Safe.

- **Disjoint clearing/refund window — IS it airtight?** Yes. `finalizeClearing` reverts for
  `block.timestamp >= revealEnd + REFUND_GRACE` (`ClearingWindowClosed`); `reclaimEscrow`
  reverts for `block.timestamp < revealEnd + REFUND_GRACE` (`RefundNotYetAvailable`). The
  boundary is exactly partitioned — no timestamp satisfies both. A cleared launch is
  never refundable (`LaunchAlreadyCleared`); a stale finalize after grace is refused. No
  double-refund (`refunded` latch + zeroed deposit), no refund-escaping-a-clearing. Airtight.

- **Settle refund underflow.** `refund = deposit - clearingPrice*filled`. For a winner,
  `deposit >= price*qty >= clearingPrice*filled` (reveal enforces `deposit >= price*qty`
  via `UnderCollateralized`; clearing price is the marginal *lowest* winning price ≤ the
  winner's own price; `filled <= qty`). For a non-winner/unrevealed, `filled == 0`. No
  underflow. Safe.

### KNOWN-RESIDUAL (named in source and/or by-design; not a new bug)

- **Selective non-reveal as a *manipulation/retraction* lever** (codex weakness-class #1).
  The sealed commit→reveal is the honest MVP privacy primitive; a bidder can withhold a
  reveal to retract a bid after committing. C1's fix guarantees this is at worst a
  self-inflicted no-op with a full refund (never a loss), but the *retraction/griefing
  lever itself* is an intrinsic limit of the commit-reveal primitive. The named upgrade is
  a reveal-forfeit bond (cheap, buildable) and, ultimately, shielded/ZK-sealed bids (DrEX
  rung 3, single-phase, no reveal round) — designed-not-built (`PRIVATE-DREGG-…` §5).

- **Fraud-proof arm (b) trusts the caller's `reservePrice`** (`CommitteeAttestor:212-217`,
  explicitly documented). A challenger supplying a *wrong* `reservePrice` can make the
  price-mismatch arm slash an *honest* committee (griefing); conversely a real fraud is
  only caught if a challenger supplies the *correct* `reservePrice`. Arm (a)
  (non-descending order) is unconditional and false-positive-free. As currently WIRED, the
  committee only *gates* an on-chain-computed clearing (price is recomputed in
  `_runClearing`), so a slash degrades launches to the timeout-refund backstop — a
  liveness fault, never theft. The named residual is binding `reservePrice`/`saleSupply`
  from the on-chain `scheduleCommit` (§5).

- **Tie-break selection among equal-price bids in `finalizeClearing` is caller-chosen**
  (a mild MEV surface — the finalizer picks which of several equal-priced bidders takes the
  marginal partial fill). The uniform clearing *price* is invariant to this choice, so it is
  a fairness nicety within the tie-freedom the Lean mechanism already permits, not a price
  or custody manipulation. Low/info.

- **Creator may skip graduation by withdrawing proceeds first.** `withdrawProceeds` sets
  phase `Finalized` and `graduate` reverts `ProceedsAlreadyWithdrawn` afterward — a *tested*
  by-design behavior (`test_CannotGraduateAfterProceedsWithdrawn`). Graduation (secondary
  liquidity) is not forced; winners already hold their tokens at the fair clearing price, so
  skipping it is a "no secondary market," not a custody loss. Anyone may `graduate` *before*
  withdrawal to force the disclosed liquidity. Info.

- **Unsold sale tokens / unclaimed creator+pool allocations remain in launchpad custody**
  (no burn). Token dust with no beneficiary path, by-design; not user funds. Info.

## codex as an auditor — gold vs mid

- **Gold:** excellent at *architecture / trust-model* reasoning — it correctly reconstructed
  the engine/custody separation, validated the committee-signature binding, the low-s/dedup
  discipline, the one-shot-mint and pool-floor teeth, and the disjoint-window claim, and it
  independently surfaced the **selective-non-reveal weakness class** with a sensible hardening
  (reveal-forfeit bond). Its custody verdict (no theft/rug) matches our independent read.
- **Mid:** it did *not* pinpoint the concrete exploitable defect (C1) — it framed non-reveal
  only as economic griefing and asserted a blanket "no asset can be lost," missing that the
  cleared-path escrow lockup is a *permanent loss* inconsistent with the stalled-path refund.
  It also meandered into repo-wide exploration rather than producing a crisp severity-ranked
  list. The concrete bug + failing test + fix came from **our triage**, which is exactly the
  division of labor: codex hunts and reasons about the design; we verify against source and
  reproduce.

## Net

- **One CONFIRMED-REAL bug** (C1, Medium stuck-funds) — fixed, with an exploit test that
  fails pre-fix (`NothingToSettle()`) and passes post-fix.
- No theft/rug/second-mint/pool-drain/reentrancy/signature vector confirmed — the custody
  teeth hold under adversarial review.
- Residuals are all either named-in-source (fraud-proof arm-b reservePrice, non-reveal
  primitive) or tested by-design (graduation-skip), consistent with the honest trust grades.
- Final: `forge test --match-path "test/DreggLaunchpad*.t.sol"` → **42 passed, 0 failed**.

### Changed files
- `chain/contracts/launchpad/DreggLaunchpad.sol` — C1 fix in `settleBid`.
- `chain/test/DreggLaunchpadAuditFixes.t.sol` — the exploit-then-confirm test.
- `docs/deos/LAUNCHPAD-CONTRACT-AUDIT.md` — this report.

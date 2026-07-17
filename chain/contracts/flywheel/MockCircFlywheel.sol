// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {DreggLaunchToken} from "../launchpad/DreggLaunchToken.sol";
import {MockAmm} from "./MockAmm.sol";

/// @title MockCircFlywheel
/// @notice A FAITHFUL mock of the CircuitLLM / $CIRC fee-flywheel, exactly as the
///         project describes it in "Where the CIRC Lives" (cited in
///         `docs/reference/CIRC-COMPETITIVE-ANALYSIS.md` §1.1): an autonomous LP
///         Agent that, per cycle,
///
///           "Splits the proceeds 50 / 50. Market-buys CIRC with one half, on-chain
///            at the market price. Pairs that CIRC with the other half (SOL) and
///            deposits it into the liquidity pool."
///
///         This is the REAL comparison target — not a strawman. Every honest gap
///         the analysis names is present BY CONSTRUCTION here, so the A/B suite
///         measures dregg against the actual mechanism:
///
///         - **Split enforced by a KEY, not a contract invariant** (§3): `splitBps`
///           is owner-settable via `setSplitBps`. The operator CAN deviate (skim,
///           re-weight, time it) and you only learn afterward. There is no
///           `SplitMismatch` revert here — that is precisely what CIRC lacks.
///         - **A front-runnable market buy** (§2.1e): the buy is a plain
///           `MockAmm.buy`, a public swap of known approximate size — the ideal
///           sandwich target. Nothing batches or seals it.
///         - **No conservation certificate** (§3): the recycle emits an event and
///           moves value; there is no `netFlow = 0` statement, no re-checkable proof
///           that value was neither minted nor skimmed.
///         - **No prev-hash-chained receipt** (§4.1E): a third party gets only a
///           block-explorer trace to eyeball, not a signed chain to re-derive.
///
///         It is not a rug — the LP-add is real (matching CIRC's locked-LP credit,
///         §2.2). The point is that its fairness is VISIBLE, never VERIFIED.
contract MockCircFlywheel {
    DreggLaunchToken public immutable token;
    MockAmm public immutable amm;
    address public owner;

    /// The split — SETTABLE BY THE OWNER'S KEY. This is the CIRC posture: "enforced
    /// by the team's signing key, not a contract invariant. The team CAN deviate."
    uint16 public splitBps; // bps of the accrued fee spent on the market buy

    event SplitChanged(uint16 oldBps, uint16 newBps); // the deviation is legal here
    event Recycled(uint256 accrued, uint256 buyHalf, uint256 poolHalf, uint256 tokenBought);

    error NotOwner();

    constructor(address token_, address amm_, uint16 splitBps_) {
        token = DreggLaunchToken(token_);
        amm = MockAmm(payable(amm_));
        owner = msg.sender;
        splitBps = splitBps_;
    }

    /// THE DEVIATION DOOR — the owner re-weights the split at will. Mirrors "the
    /// team can change the ratio, skim, time it, and you learn only afterward."
    /// There is no committed public input this is checked against: whatever the
    /// key sets, the recycle uses. (Contrast `RecycleFlywheel`: no such setter
    /// exists; a wrong split reverts `SplitMismatch`.)
    function setSplitBps(uint16 newBps) external {
        if (msg.sender != owner) revert NotOwner();
        emit SplitChanged(splitBps, newBps);
        splitBps = newBps;
    }

    /// One flywheel cycle: split the accrued fee by the CURRENT `splitBps`,
    /// market-buy the token with the buy-half (a front-runnable public swap), pair
    /// the bought token with the pool-half into the AMM. No cert, no receipt.
    function recycle(uint256 minTokenOut) external payable returns (uint256 tokenBought) {
        uint256 accrued = msg.value;
        uint256 buyHalf = (accrued * splitBps) / 10000;
        uint256 poolHalf = accrued - buyHalf;

        // MARKET BUY — the telegraphed, sandwichable swap.
        tokenBought = amm.buy{value: buyHalf}(minTokenOut);

        // PAIR + ADD LP (the "deposit into the liquidity pool" leg).
        if (tokenBought > 0 && poolHalf > 0) {
            token.approve(address(amm), tokenBought);
            amm.addLiquidity{value: poolHalf}(tokenBought);
        }

        emit Recycled(accrued, buyHalf, poolHalf, tokenBought);
    }

    receive() external payable {}
}

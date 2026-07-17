// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {DreggLaunchToken} from "../launchpad/DreggLaunchToken.sol";

/// @title MockAmm
/// @notice A faithful pump.fun/PumpSwap-style constant-product (`x·y=k`) AMM: a
///         PUBLIC, front-runnable swap venue with NO solvency floor and NO batch
///         clearing. This is the market the CIRC-style flywheel buys against
///         (`MockCircFlywheel`), and the surface a sandwich bot extracts MEV from.
///
///         It is deliberately a real, ordinary AMM — the CIRC flywheel's "market
///         buy CIRC on-chain at the market price" (§1.1 of
///         `docs/reference/CIRC-COMPETITIVE-ANALYSIS.md`) lands here as a plain
///         `buy()` any mempool observer can sandwich. It is the honest comparison
///         target, not a strawman: it prices exactly like a Raydium/PumpSwap pool.
contract MockAmm {
    DreggLaunchToken public immutable token;
    uint256 public reserveQuote; // wei
    uint256 public reserveToken; // token base units
    uint16 public immutable feeBps; // e.g. 30 = 0.30% (pump-style trade fee)

    event Bought(address indexed buyer, uint256 quoteIn, uint256 tokenOut);
    event Sold(address indexed seller, uint256 tokenIn, uint256 quoteOut);
    event LiquidityAdded(address indexed from, uint256 quoteIn, uint256 tokenIn);

    error ZeroInput();
    error NotInitialized();
    error TransferFromFailed();
    error TransferFailed();

    constructor(address token_, uint16 feeBps_) {
        token = DreggLaunchToken(token_);
        feeBps = feeBps_;
    }

    /// Seed / add liquidity (permissionless, no floor, no lock — a pump-style pool).
    function addLiquidity(uint256 tokenIn) external payable {
        if (msg.value == 0 || tokenIn == 0) revert ZeroInput();
        if (!token.transferFrom(msg.sender, address(this), tokenIn)) revert TransferFromFailed();
        reserveQuote += msg.value;
        reserveToken += tokenIn;
        emit LiquidityAdded(msg.sender, msg.value, tokenIn);
    }

    /// Market BUY: swap ETH in for tokens out at the current spot — the
    /// front-runnable operation. Output depends on the reserves AT EXECUTION, so
    /// a trade landed just before this one (a front-run) moves the price against
    /// the buyer: exactly the sandwich surface.
    function buy(uint256 minTokenOut) external payable returns (uint256 tokenOut) {
        if (reserveToken == 0) revert NotInitialized();
        if (msg.value == 0) revert ZeroInput();
        uint256 quoteInNet = (msg.value * (10000 - feeBps)) / 10000;
        tokenOut = (reserveToken * quoteInNet) / (reserveQuote + quoteInNet);
        require(tokenOut >= minTokenOut, "slippage");
        reserveQuote += msg.value;
        reserveToken -= tokenOut;
        if (!token.transfer(msg.sender, tokenOut)) revert TransferFailed();
        emit Bought(msg.sender, msg.value, tokenOut);
    }

    /// Market SELL: swap tokens in for ETH out (the sandwich back-run).
    function sell(uint256 tokenIn, uint256 minQuoteOut) external returns (uint256 quoteOut) {
        if (reserveToken == 0) revert NotInitialized();
        if (tokenIn == 0) revert ZeroInput();
        if (!token.transferFrom(msg.sender, address(this), tokenIn)) revert TransferFromFailed();
        uint256 tokenInNet = (tokenIn * (10000 - feeBps)) / 10000;
        quoteOut = (reserveQuote * tokenInNet) / (reserveToken + tokenInNet);
        require(quoteOut >= minQuoteOut, "slippage");
        reserveToken += tokenIn;
        reserveQuote -= quoteOut;
        (bool ok,) = payable(msg.sender).call{value: quoteOut}("");
        if (!ok) revert TransferFailed();
        emit Sold(msg.sender, tokenIn, quoteOut);
    }

    function spotPriceWeiPerToken() external view returns (uint256) {
        if (reserveToken == 0) return 0;
        return (reserveQuote * 1e18) / reserveToken;
    }

    function quoteBuy(uint256 quoteIn) external view returns (uint256) {
        if (reserveToken == 0 || quoteIn == 0) return 0;
        uint256 quoteInNet = (quoteIn * (10000 - feeBps)) / 10000;
        return (reserveToken * quoteInNet) / (reserveQuote + quoteInNet);
    }

    function reserves() external view returns (uint256 quote, uint256 tokenR) {
        return (reserveQuote, reserveToken);
    }

    receive() external payable {}
}

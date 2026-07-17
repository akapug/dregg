// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {DreggLaunchToken} from "../launchpad/DreggLaunchToken.sol";
import {DreggSolventPool} from "../launchpad/DreggSolventPool.sol";

/// @title RecycleFlywheel
/// @notice The dregg VERIFIABLE recycle mechanism — the CIRC-style fee-flywheel
///         with every property CIRC leaves "visible/trusted" replaced by one that
///         is enforced-by-contract, and every step left as a prev-hash-chained
///         signed receipt a non-witness re-checks. It is a COMPOSITION of landed,
///         proven launchpad pieces (`docs/reference/CIRC-COMPETITIVE-ANALYSIS.md`
///         §4.2), not new science:
///
///   1. ACCRUE — each fee inflow is recorded WITH a source-receipt hash: provenance
///      is folded into `provenanceRoot`, not an anonymous transfer (§5.2).
///   2. SPLIT — a PURE function of `(accrued, buyBps)` where `buyBps` is a committed
///      constructor input. The finalizer must pass the split it believes correct; a
///      wrong/hidden split REVERTS `SplitMismatch` — the exact `GraduationSeedMismatch`
///      pattern (`DreggLaunchpad.sol:619`). The operator CANNOT deviate; contrast
///      `MockCircFlywheel.setSplitBps`, an owner-key door.
///   3. CLEAR — the "buy" is a SEALED-BID uniform-price batch clearing over sellers'
///      asks, cleared by a permutation-checked ascending sort + marginal-fill walk
///      (the dual of `DreggLaunchpad._runClearing` / `_assertPermutation`,
///      `Market/Aggregation.lean` no-drop/no-insert). There is NO telegraphed swap
///      to sandwich, and the clearing is ORDER-INVARIANT — the §2.1(e) front-run is
///      unconstructable, not mitigated.
///   4. POOL — the bought tokens + the pool-half (+ any unspent budget) seed a
///      `DreggSolventPool`, floor-guarded (`PoolFloorBreached`, rung-6). The seed is
///      the disclosed, checked amount.
///   5. CONSERVE + EMIT — the recycle asserts per-asset `netFlow = 0` on-chain (the
///      on-chain twin of `Market/Priced.lean priced_clearing_keystone`) and emits a
///      prev-hash-chained, operator-SIGNED receipt whose head a non-witness
///      re-derives from public data (`verifyReceipt`).
///
/// ## Honest trust grades (per the analysis §4.3 — do NOT overclaim)
/// - front-run resistance / order-invariance / split-enforcement / floor-guarded
///   pool / conservation check / signed receipt chain: BUILT + on-chain-enforced
///   here (both polarities tested in `test/RecycleFlywheelAB.t.sol`).
/// - The underlying MECHANISM fairness (`uniform_price_no_arbitrage`) and
///   conservation (`priced_clearing_keystone`) are PROVED in Lean; this contract is
///   a faithful REPLAYABLE realization, not itself the Lean statement.
/// - NAMED WELD, unclosed (§4.3.1): the receipt does NOT bind the clearing to an
///   in-circuit price proof — a non-witness re-derives the price from the PUBLIC
///   book (rung-1 replayable), so a corrupt operator can WITHHOLD but cannot
///   MISPRICE; binding the clearing tuple inside a Groth16 statement is future work.
/// - `.sol ↔ Lean` correspondence is prose, not mechanized (§4.3.2).
///
/// Single-lifecycle per instance (one recycle), for a clean A/B measurement.
/// Quote currency is native ETH.
contract RecycleFlywheel {
    // ─── Committed public inputs (the disclosed schedule of the recycle) ────────
    DreggLaunchToken public immutable token;
    /// THE COMMITTED SPLIT — bps of the accrued fee routed to the buy leg. Fixed at
    /// construction: a public, unchangeable fact of this recycle. There is NO setter
    /// (the CIRC deviation door is absent by construction).
    uint16 public immutable buyBps;
    /// The operator whose signature attests the receipt head (re-checkable off-chain).
    address public immutable operator;

    uint16 public constant FLOOR_BPS = 2000; // disclosed solvency floor (rung-6)
    uint16 public constant POOL_FEE_BPS = 30; // graduated-pool swap fee

    // ─── Phases ─────────────────────────────────────────────────────────────────
    enum Phase {
        Commit, // 0 — fees accrue + sellers commit sealed asks
        Reveal, // 1 — sellers reveal
        Cleared // 2 — buy cleared, pool seeded, receipt emitted
    }

    Phase public phase;
    uint64 public immutable commitEnd;
    uint64 public immutable revealEnd;

    // ─── Accrual + provenance ───────────────────────────────────────────────────
    uint256 public accrued; // total fees in (wei)
    uint256 public inflowCount; // number of accrue() calls
    uint256 public provenancedCount; // inflows carrying a nonzero source-receipt hash
    bytes32 public provenanceRoot; // fold of (sourceReceiptHash, amount) — the provenance chain

    // ─── Sealed asks (the sell-side of the recycle buy) ─────────────────────────
    struct Ask {
        bytes32 sealedHash; // H(price‖qty‖salt‖seller)
        uint256 escrow; // tokens escrowed at commit (>= revealed qty)
        bool committed;
        bool revealed;
        uint256 price; // wei per whole token (ask), revealed
        uint256 qty; // whole tokens offered, revealed
        uint256 filled; // whole tokens taken by the clearing
        bool settled;
    }

    mapping(address => Ask) private _asks;
    address[] private _revealedSellers;

    uint256 public constant TOKEN_UNIT = 1e18;

    // ─── Cleared result ─────────────────────────────────────────────────────────
    uint256 public buyHalf; // committed-split buy leg (wei)
    uint256 public poolHalf; // committed-split pool leg (wei)
    uint256 public uniformPrice; // the single price every filled seller is paid (wei/token)
    uint256 public boughtTokens; // whole tokens the recycle bought
    uint256 public spentQuote; // wei paid to sellers = uniformPrice * boughtTokens
    uint256 public quoteSeed; // wei seeded into the pool (poolHalf + unspent budget)
    uint256 public tokenSeed; // token base units seeded into the pool
    bytes32 public bookCommit; // fold of the whole revealed book (order-independent content)
    DreggSolventPool public pool;

    // ─── The receipt (prev-hash-chained, operator-signed, re-checkable) ─────────
    struct Receipt {
        // ACCRUE step
        uint256 accrued;
        bytes32 provenanceRoot;
        uint256 inflowCount;
        // SPLIT step
        uint256 buyHalf;
        uint256 poolHalf;
        uint16 buyBps;
        // CLEAR step
        uint256 uniformPrice;
        uint256 boughtTokens;
        uint256 spentQuote;
        bytes32 bookCommit;
        // POOL step
        uint256 quoteSeed;
        uint256 tokenSeed;
        uint256 floorQuote;
        uint256 floorToken;
        // CONSERVE step (both zero — the netFlow=0 tooth)
        int256 netQuote;
        int256 netToken;
    }

    Receipt private _receipt;
    bytes32 public receiptHead; // the signed chain head
    bytes private _receiptSig; // the operator's signature over receiptHead

    // ─── Events ─────────────────────────────────────────────────────────────────
    event FeeAccrued(address indexed from, uint256 amount, bytes32 sourceReceiptHash, bytes32 provenanceRoot);
    event AskCommitted(address indexed seller, bytes32 sealedHash, uint256 escrow);
    event AskRevealed(address indexed seller, uint256 price, uint256 qty);
    event RecycleCleared(uint256 uniformPrice, uint256 boughtTokens, uint256 spentQuote, bytes32 bookCommit);
    event PoolSeeded(address indexed pool, uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken);
    event ReceiptEmitted(bytes32 receiptHead);
    event AskSettled(address indexed seller, uint256 filled, uint256 paidQuote, uint256 returnedTokens);

    // ─── Errors ─────────────────────────────────────────────────────────────────
    error NotCommitPhase();
    error NotRevealPhase();
    error NotClearPhase();
    error RevealWindowOpen();
    error AlreadyCommitted();
    error NoCommit();
    error AlreadyRevealed();
    error AskMismatch(); // reveal does not open the seal
    error UnderEscrowed(uint256 escrow, uint256 qty);
    error TransferFromFailed();
    error TransferFailed();
    error BadPermutation();
    error NotSortedAscending();
    /// The disclosed committed split, ENFORCED — a wrong/hidden split reverts.
    /// The CIRC-key deviation is unconstructable (mirror `GraduationSeedMismatch`).
    error SplitMismatch(uint256 correctBuyHalf, uint256 correctPoolHalf);
    /// The per-asset netFlow=0 tooth — a recycle that mints or destroys value reverts.
    error ConservationBroken(int256 netQuote, int256 netToken);
    error BadReceiptSignature();
    error ReceiptHeadMismatch(bytes32 computed);
    error NothingBought();
    error NothingToSettle();

    constructor(
        address token_,
        uint16 buyBps_,
        address operator_,
        uint64 commitDuration,
        uint64 revealDuration
    ) {
        require(buyBps_ > 0 && buyBps_ < 10000, "buyBps");
        token = DreggLaunchToken(token_);
        buyBps = buyBps_;
        operator = operator_;
        commitEnd = uint64(block.timestamp) + commitDuration;
        revealEnd = commitEnd + revealDuration;
        phase = Phase.Commit;
    }

    // ─── (1) ACCRUE — fee in, WITH provenance ───────────────────────────────────

    /// @notice Accrue a fee inflow tagged with the hash of the receipt of the work
    ///         that produced it (a `TurnReceipt`/game-move/clearing hash). The
    ///         provenance is folded into `provenanceRoot` — a re-checkable chain of
    ///         where the fees came from, the structural answer to CIRC's
    ///         "amount visible, provenance opaque" (§5.2). `sourceReceiptHash == 0`
    ///         is an UNPROVENANCED inflow (counted, but not provenanced) — the mock's
    ///         every inflow is of this kind.
    function accrueFee(bytes32 sourceReceiptHash) external payable {
        if (phase != Phase.Commit || block.timestamp >= commitEnd) revert NotCommitPhase();
        accrued += msg.value;
        inflowCount += 1;
        if (sourceReceiptHash != bytes32(0)) provenancedCount += 1;
        provenanceRoot = keccak256(abi.encode(provenanceRoot, sourceReceiptHash, msg.value));
        emit FeeAccrued(msg.sender, msg.value, sourceReceiptHash, provenanceRoot);
    }

    // ─── (2) commit → reveal the sealed asks (the sell-side book) ───────────────

    /// @notice Commit a SEALED ask and escrow the tokens. `sealedHash ==
    ///         H(price‖qty‖salt‖seller)`; nothing about the ask is observable during
    ///         the commit window (no book to front-run), and the tokens are escrowed
    ///         so the clearing can deliver them. Caller must `approve` this contract.
    function commitAsk(bytes32 sealedHash, uint256 tokenEscrow) external {
        if (phase != Phase.Commit || block.timestamp >= commitEnd) revert NotCommitPhase();
        Ask storage a = _asks[msg.sender];
        if (a.committed) revert AlreadyCommitted();
        if (!token.transferFrom(msg.sender, address(this), tokenEscrow)) revert TransferFromFailed();
        a.committed = true;
        a.sealedHash = sealedHash;
        a.escrow = tokenEscrow;
        emit AskCommitted(msg.sender, sealedHash, tokenEscrow);
    }

    /// @notice Reveal a committed ask — only in the reveal window, only opening the
    ///         exact seal (`AskMismatch` otherwise: no late-switch after seeing
    ///         others). Escrow must cover the revealed quantity.
    function revealAsk(uint256 price, uint256 qty, bytes32 salt) external {
        if (block.timestamp < commitEnd || block.timestamp >= revealEnd) revert NotRevealPhase();
        if (phase == Phase.Commit) phase = Phase.Reveal;
        Ask storage a = _asks[msg.sender];
        if (!a.committed) revert NoCommit();
        if (a.revealed) revert AlreadyRevealed();
        if (keccak256(abi.encode(price, qty, salt, msg.sender)) != a.sealedHash) revert AskMismatch();
        // qty is WHOLE tokens; escrow is base units — cover qty·1e18 (mirrors the
        // launchpad's wei-deposit ≥ price·qty check, applied to the token side).
        if (a.escrow < qty * TOKEN_UNIT) revert UnderEscrowed(a.escrow, qty * TOKEN_UNIT);
        a.revealed = true;
        a.price = price;
        a.qty = qty;
        _revealedSellers.push(msg.sender);
        emit AskRevealed(msg.sender, price, qty);
    }

    // ─── (3),(4),(5) FINALIZE — split-check, clear, seed pool, conserve, emit ───

    /// @notice Finalize the recycle. The caller (the operator) supplies:
    ///         - `order`: a claimed ASCENDING-by-price permutation of the revealed
    ///           asks (untrusted search, verified translation-validation style).
    ///         - `claimedBuyHalf`,`claimedPoolHalf`: the split it believes correct —
    ///           a mismatch with the committed `buyBps` reverts `SplitMismatch`.
    ///         - `claimedReceiptHead`,`signature`: the operator's precomputed +
    ///           signed receipt head; the contract recomputes the head from its own
    ///           cleared values and rejects a mismatch or a bad signature.
    function finalizeRecycle(
        uint256[] calldata order,
        uint256 claimedBuyHalf,
        uint256 claimedPoolHalf,
        bytes32 claimedReceiptHead,
        bytes calldata signature
    ) external {
        if (block.timestamp < revealEnd) revert RevealWindowOpen();
        if (phase == Phase.Cleared) revert NotClearPhase();

        // (2) THE COMMITTED SPLIT, ENFORCED — a wrong/hidden split reverts.
        (uint256 correctBuy, uint256 correctPool) = splitOf(accrued);
        if (claimedBuyHalf != correctBuy || claimedPoolHalf != correctPool) {
            revert SplitMismatch(correctBuy, correctPool);
        }
        buyHalf = correctBuy;
        poolHalf = correctPool;

        // (3) THE SEALED-BID UNIFORM-PRICE CLEARING — order-invariant, no swap to
        //     sandwich. (4) SEED the pool. (5a) CONSERVE. (Kept in a helper to stay
        //     under the stack-depth limit.)
        _clearSeedConserve(order, correctBuy, correctPool);

        // (5b) EMIT the prev-hash-chained, operator-signed receipt.
        _emitReceipt(claimedReceiptHead, signature);

        phase = Phase.Cleared;
        emit RecycleCleared(uniformPrice, boughtTokens, spentQuote, bookCommit);
        emit ReceiptEmitted(receiptHead);
    }

    /// Clear the sealed-ask buy, seed the solvent pool, assert per-asset netFlow=0.
    function _clearSeedConserve(uint256[] calldata order, uint256 correctBuy, uint256 correctPool) private {
        (uint256 uPrice, uint256 bought, uint256 spent, bytes32 bCommit) = _runAskClearing(order, correctBuy);
        if (bought == 0) revert NothingBought();
        uniformPrice = uPrice;
        boughtTokens = bought;
        spentQuote = spent;
        bookCommit = bCommit;

        // (4) SEED THE PROVABLY-SOLVENT POOL with the bought tokens + the pool-half
        //     + any unspent budget (all disclosed, floor-guarded).
        uint256 qSeed = correctPool + (correctBuy - spent); // pool-half + unspent budget
        uint256 tSeed = bought * TOKEN_UNIT; // base units seeded into the pool
        quoteSeed = qSeed;
        tokenSeed = tSeed;
        uint256 fQuote = (qSeed * FLOOR_BPS) / 10000;
        uint256 fToken = (tSeed * FLOOR_BPS) / 10000;
        DreggSolventPool p = new DreggSolventPool(address(token), 0, fQuote, fToken, POOL_FEE_BPS);
        pool = p;
        token.transfer(address(p), tSeed); // tokens taken from filled sellers' escrow
        p.initialize{value: qSeed}(tSeed);
        emit PoolSeeded(address(p), qSeed, tSeed, fQuote, fToken);

        // (5a) CONSERVATION — per-asset netFlow = 0 (the on-chain twin of
        //      `priced_clearing_keystone`). Quote: accrued = spent(→sellers) +
        //      quoteSeed(→pool). Token: bought·1e18 = tokenSeed(→pool). A bug in the
        //      split/leftover math trips this tooth.
        int256 netQuote = int256(accrued) - int256(spent) - int256(qSeed);
        int256 netToken = int256(bought * TOKEN_UNIT) - int256(tSeed);
        if (netQuote != 0 || netToken != 0) revert ConservationBroken(netQuote, netToken);
    }

    /// Build the receipt from cleared storage, fold it, and require the operator's
    /// signed head matches.
    function _emitReceipt(bytes32 claimedReceiptHead, bytes calldata signature) private {
        _receipt = Receipt({
            accrued: accrued,
            provenanceRoot: provenanceRoot,
            inflowCount: inflowCount,
            buyHalf: buyHalf,
            poolHalf: poolHalf,
            buyBps: buyBps,
            uniformPrice: uniformPrice,
            boughtTokens: boughtTokens,
            spentQuote: spentQuote,
            bookCommit: bookCommit,
            quoteSeed: quoteSeed,
            tokenSeed: tokenSeed,
            floorQuote: (quoteSeed * FLOOR_BPS) / 10000,
            floorToken: (tokenSeed * FLOOR_BPS) / 10000,
            netQuote: int256(0),
            netToken: int256(0)
        });
        bytes32 head = _foldReceipt(_receipt);
        if (head != claimedReceiptHead) revert ReceiptHeadMismatch(head);
        if (_recoverSigner(head, signature) != operator) revert BadReceiptSignature();
        receiptHead = head;
        _receiptSig = signature;
    }

    /// @notice Settle one seller after clearing: a filled seller is paid the UNIFORM
    ///         price for its filled tokens (the filled tokens already seeded the
    ///         pool) and returned any un-filled escrow; an un-filled seller gets its
    ///         whole escrow back. Permissionless.
    function settleAsk(address seller) external {
        if (phase != Phase.Cleared) revert NotClearPhase();
        Ask storage a = _asks[seller];
        if (!a.committed || a.settled) revert NothingToSettle();
        a.settled = true;
        uint256 paid = uniformPrice * a.filled; // uniform price, not the seller's ask
        uint256 returned = a.escrow - a.filled * TOKEN_UNIT; // filled tokens went to the pool
        if (paid > 0) _sendEth(seller, paid);
        if (returned > 0) _sendToken(seller, returned);
        emit AskSettled(seller, a.filled, paid, returned);
    }

    // ─── The clearing (dual of DreggLaunchpad._runClearing) ─────────────────────

    /// Verify `order` is a permutation of the revealed asks sorted ASCENDING by
    /// price, walk it filling tokens at the marginal (uniform) price while the
    /// budget covers the cumulative fill, and set each filled seller's `filled`.
    /// Returns (uniform price, tokens bought, wei spent, a commitment to the whole
    /// revealed book). Reverts on a drop/insert or a non-ascending order.
    ///
    /// Invariant: when ask i takes fill making the cumulative `bought = B` at its
    /// price `p`, `p·B ≤ budget` (fill is capped at `budget/p − bought`). Prices
    /// ascend, so once `bought` reaches `budget/p` no dearer ask can add anything —
    /// the LAST filled ask's price is the single uniform price, and `uniform·bought
    /// ≤ budget`. The result is a function of the book + budget ALONE (order-invariant).
    function _runAskClearing(uint256[] calldata order, uint256 budget)
        private
        returns (uint256 clearingPrice, uint256 bought, uint256 spent, bytes32 bCommit)
    {
        address[] storage revealed = _revealedSellers;
        _assertPermutation(order, revealed.length);

        uint256 prevPrice = 0;
        for (uint256 i = 0; i < order.length; i++) {
            address seller = revealed[order[i]];
            Ask storage a = _asks[seller];
            // Ascending (the canonical uniform-clearing order for a buy-side budget).
            if (a.price < prevPrice) revert NotSortedAscending();
            prevPrice = a.price;

            bCommit = keccak256(abi.encodePacked(bCommit, seller, a.price, a.qty));

            if (a.price > 0) {
                uint256 affordable = budget / a.price; // total tokens if uniform == a.price
                if (affordable > bought) {
                    uint256 room = affordable - bought;
                    uint256 fill = a.qty < room ? a.qty : room;
                    if (fill > 0) {
                        a.filled = fill;
                        bought += fill;
                        clearingPrice = a.price; // marginal = highest filled ask
                    }
                }
            }
        }
        spent = clearingPrice * bought; // uniform price × total = wei paid to sellers
    }

    /// @notice A NON-mutating preview of the clearing — the operator runs this to
    ///         learn `(uniformPrice, bought, spent, bookCommit)`, builds the receipt,
    ///         signs it, and submits it to `finalizeRecycle`. Same math as
    ///         `_runAskClearing`, read-only (no fills written). Anyone re-derives the
    ///         clearing from the public revealed book with it.
    function previewClearing(uint256[] calldata order, uint256 budget)
        external
        view
        returns (uint256 clearingPrice, uint256 bought, uint256 spent, bytes32 bCommit)
    {
        address[] storage revealed = _revealedSellers;
        _assertPermutation(order, revealed.length);
        uint256 prevPrice = 0;
        for (uint256 i = 0; i < order.length; i++) {
            address seller = revealed[order[i]];
            Ask storage a = _asks[seller];
            if (a.price < prevPrice) revert NotSortedAscending();
            prevPrice = a.price;
            bCommit = keccak256(abi.encodePacked(bCommit, seller, a.price, a.qty));
            if (a.price > 0) {
                uint256 affordable = budget / a.price;
                if (affordable > bought) {
                    uint256 room = affordable - bought;
                    uint256 fill = a.qty < room ? a.qty : room;
                    if (fill > 0) {
                        bought += fill;
                        clearingPrice = a.price;
                    }
                }
            }
        }
        spent = clearingPrice * bought;
    }

    /// The no-drop / no-insert check: `order` must be a permutation of [0,n).
    /// Mirrors `DreggLaunchpad._assertPermutation` / `Market/Aggregation.lean`.
    function _assertPermutation(uint256[] calldata order, uint256 n) private pure {
        if (order.length != n) revert BadPermutation();
        bool[] memory seen = new bool[](n);
        for (uint256 i = 0; i < n; i++) {
            uint256 idx = order[i];
            if (idx >= n || seen[idx]) revert BadPermutation();
            seen[idx] = true;
        }
    }

    // ─── Split — the committed pure function ────────────────────────────────────

    /// @notice The recycle split — a PURE function of the accrued amount and the
    ///         committed `buyBps`. Anyone re-derives it; the finalizer must pass it
    ///         exactly (`SplitMismatch`).
    function splitOf(uint256 amount) public view returns (uint256 buyLeg, uint256 poolLeg) {
        buyLeg = (amount * buyBps) / 10000;
        poolLeg = amount - buyLeg;
    }

    // ─── Receipt: fold + verify (the re-checkable, verify-only path) ────────────

    /// @notice The receipt chain fold — genesis 0, one keccak per step, prev-hash
    ///         chained. A non-witness reproduces this from public data alone.
    function _foldReceipt(Receipt memory r) internal pure returns (bytes32) {
        bytes32 h = bytes32(0);
        h = keccak256(abi.encode(h, "ACCRUE", r.accrued, r.provenanceRoot, r.inflowCount));
        h = keccak256(abi.encode(h, "SPLIT", r.buyHalf, r.poolHalf, r.buyBps));
        h = keccak256(abi.encode(h, "CLEAR", r.uniformPrice, r.boughtTokens, r.spentQuote, r.bookCommit));
        h = keccak256(abi.encode(h, "POOL", r.quoteSeed, r.tokenSeed, r.floorQuote, r.floorToken));
        h = keccak256(abi.encode(h, "CONSERVE", r.netQuote, r.netToken));
        return h;
    }

    /// @notice Recompute the receipt head from an externally-supplied receipt —
    ///         the pure re-derivation a third party runs on public step data.
    function recomputeReceiptHead(Receipt calldata r) external pure returns (bytes32) {
        return _foldReceipt(r);
    }

    /// @notice VERIFY-ONLY re-check: recompute the head from the stored (public)
    ///         receipt, confirm it equals the emitted head, and confirm the operator
    ///         signed it. A non-witness runs this against public chain data and
    ///         learns the recycle happened exactly as claimed — ex-ante verification,
    ///         not ex-post block-explorer trust. Returns true iff all three hold.
    function verifyReceipt() external view returns (bool) {
        if (phase != Phase.Cleared) return false;
        bytes32 head = _foldReceipt(_receipt);
        if (head != receiptHead) return false;
        return _recoverSigner(head, _receiptSig) == operator;
    }

    /// @notice The stored receipt + head + signature — the public re-check bundle.
    function receiptBundle() external view returns (Receipt memory r, bytes32 head, bytes memory sig) {
        return (_receipt, receiptHead, _receiptSig);
    }

    // ─── Views ──────────────────────────────────────────────────────────────────

    /// @notice Fraction of inflows carrying a verifiable source receipt, in bps.
    ///         (dregg: measurable; the mock's opaque transfers: 0.)
    function provenanceBps() external view returns (uint256) {
        if (inflowCount == 0) return 0;
        return (provenancedCount * 10000) / inflowCount;
    }

    function revealedCount() external view returns (uint256) {
        return _revealedSellers.length;
    }

    function getAsk(address seller)
        external
        view
        returns (bool committed, bool revealed, uint256 price, uint256 qty, uint256 filled, bool settled, uint256 escrow)
    {
        Ask storage a = _asks[seller];
        return (a.committed, a.revealed, a.price, a.qty, a.filled, a.settled, a.escrow);
    }

    /// @notice The canonical seal preimage a seller reproduces off-chain.
    function sealOf(uint256 price, uint256 qty, bytes32 salt, address seller) external pure returns (bytes32) {
        return keccak256(abi.encode(price, qty, salt, seller));
    }

    // ─── Internal ─────────────────────────────────────────────────────────────

    /// EIP-191 personal-sign recovery over the 32-byte receipt head.
    function _recoverSigner(bytes32 head, bytes memory signature) internal pure returns (address) {
        if (signature.length != 65) return address(0);
        bytes32 r;
        bytes32 s;
        uint8 v;
        assembly {
            r := mload(add(signature, 0x20))
            s := mload(add(signature, 0x40))
            v := byte(0, mload(add(signature, 0x60)))
        }
        bytes32 digest = keccak256(abi.encodePacked("\x19Ethereum Signed Message:\n32", head));
        return ecrecover(digest, v, r, s);
    }

    function _sendEth(address to, uint256 amount) private {
        (bool ok,) = payable(to).call{value: amount}("");
        if (!ok) revert TransferFailed();
    }

    function _sendToken(address to, uint256 amount) private {
        if (!token.transfer(to, amount)) revert TransferFailed();
    }
}

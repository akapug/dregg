// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IDreggSettlement} from "./IDreggSettlement.sol";
import {DreggMerkle} from "./DreggMerkle.sol";

/// @title DreggStateOracle
/// @notice A RICHER on-chain client of dregg: it turns the bare settlement
///         root-tracker (`DreggSettlement`) into a queryable STATE ORACLE that
///         any EVM contract can use to PROVE a fact about dregg state on-chain.
///
/// The bare `DreggSettlement` advances a single `provenRoot` and answers only
/// "is this root proven?". This oracle adds the two rungs that make dregg's
/// on-chain presence usable by other contracts (RWA vaults, DeFi markets,
/// governance) — the highest-value first being on-chain INCLUSION PROOFS:
///
///  1. EPOCH + SUB-ROOT HISTORY (`recordEpoch` / `epochOf` / `subRoots`):
///     a history of settled state roots, each carrying its exposed dregg
///     SUB-ROOTS — the nullifier root, the commitments root, the balance root,
///     the heap root. These are the roots the dregg state commitment binds
///     (`metatheory Dregg2.Circuit.StateCommit`: `RestHashIffFrame` lists
///     `nullifierRoot`, `revokedRoot`, `commitmentsRoot`, `heaps` among the
///     hashed components; `circuit/src/effect_vm_descriptors.rs` shows the
///     per-turn nullifier/commitment inserts are already PI-bound). Keeping a
///     HISTORY (not just the latest) gives reorg-safety and lets a proof made
///     against a since-superseded root still verify — the same reason
///     `DreggSettlement._provenRoots` is a set, not a scalar.
///
///  2. INCLUSION-PROOF VERIFICATION (`proveHolding` / `proveNullifierSpent` /
///     `verifyAgainstSubRoot`): given a settled epoch, verify a keccak Merkle
///     inclusion proof that a balance / holding / nullifier / commitment leaf
///     is in the corresponding sub-root. THIS is what makes the client usable:
///     an RWA contract can gate on "address A holds >= N in dregg", a market can
///     check "this note is unspent", a bridge can honor "this withdrawal leaf is
///     committed" — all as a pure, EVM-cheap function of a proven root.
///
/// ## Trust grades (honest)
///
/// - The INCLUSION CHECK itself (`DreggMerkle.verifyInclusion`) is SOUND given
///   the sub-root: a forged leaf/path cannot reach the root (keccak CR). This is
///   the buildable-now, no-weld component.
/// - Binding a SUB-ROOT to the settled state is proof-bound only once dregg's
///   settlement proof EXPOSES the sub-roots as public inputs. Today they are
///   committed INSIDE the Poseidon2 state root (via `restHash`) but not extracted
///   as separate lanes, so opening them on-chain would need Poseidon2 (heavy).
///   Until the exposure weld lands (extra apex claim lanes → shrink → new
///   Groth16 VK — the SAME class of weld as the outbound message root in
///   `DreggSettlement`), sub-roots are recorded by an authorized RECORDER and
///   are only as trustworthy as that recorder. The one binding enforced now: the
///   epoch's TOP state root MUST be a genuinely proven root
///   (`settlement.isProvenRoot`), so the oracle can never record an epoch for a
///   state dregg never settled.
///
/// This contract is ADDITIVE: it reads `DreggSettlement` through the existing
/// `IDreggSettlement` interface and adds no new trust to the settlement path.
contract DreggStateOracle {
    using DreggMerkle for bytes32;

    // ─── Sub-root kinds ───────────────────────────────────────────────────────

    /// The dregg state sub-roots this oracle exposes. Order is pinned; it is the
    /// index into `Epoch.subRoots`.
    enum SubRoot {
        Balance, // 0 — (address|cell => balance) leaves: "A holds >= N"
        Nullifier, // 1 — spent-nullifier set: "this note is spent"
        Commitments, // 2 — note-commitment set: "this note exists"
        Heap // 3 — umem heap root: "this cell holds value V"
    }

    uint256 internal constant NUM_SUBROOTS = 4;

    // ─── Types ────────────────────────────────────────────────────────────────

    struct Epoch {
        bytes32 stateRoot; // the settled dregg state root (packLanes key)
        uint64 height; // cumulative proven height at this epoch
        bool exists;
        bytes32[NUM_SUBROOTS] subRoots; // keccak MIRROR sub-roots (see trust grades)
    }

    // ─── Immutables / roles ────────────────────────────────────────────────────

    /// The bare settlement client this oracle enriches. Read-only dependency.
    IDreggSettlement public immutable settlement;

    /// The authorized sub-root recorder (the dregg operator / relayer). Until the
    /// sub-root exposure weld lands, sub-roots are operator-attested — but every
    /// recorded epoch's state root is checked against `settlement.isProvenRoot`,
    /// so a recorder can never invent a state dregg did not settle.
    address public immutable recorder;

    // ─── State ─────────────────────────────────────────────────────────────────

    /// Epoch by settled state root (packLanes key). History, not just latest.
    mapping(bytes32 => Epoch) private _epochs;

    /// Ordered list of recorded state roots (for enumeration / reorg windows).
    bytes32[] public epochRoots;

    // ─── Events ────────────────────────────────────────────────────────────────

    event EpochRecorded(bytes32 indexed stateRoot, uint64 height);
    event SubRootsRecorded(
        bytes32 indexed stateRoot,
        bytes32 balanceRoot,
        bytes32 nullifierRoot,
        bytes32 commitmentsRoot,
        bytes32 heapRoot
    );

    /// An inbound command/deposit commitment for dregg to ingest (the eth→dregg
    /// leg). dregg's relayer/light-client watches this log and mirrors the
    /// commitment into state. Value custody (if any) is held by a companion
    /// escrow (see `DreggEscrow` in the design doc); this event is the
    /// instruction channel.
    event InboundCommitment(bytes32 indexed commitment, address indexed from, bytes payload);

    // ─── Errors ────────────────────────────────────────────────────────────────

    error NotRecorder(address caller);
    error SettlementHasNoCode(address settlement);
    error StateRootNotProven(bytes32 stateRoot);
    error ZeroStateRoot();
    error EpochAlreadyRecorded(bytes32 stateRoot);
    error UnknownEpoch(bytes32 stateRoot);

    // ─── Constructor ────────────────────────────────────────────────────────────

    constructor(IDreggSettlement settlement_, address recorder_) {
        // Fail closed: a codeless settlement address would make isProvenRoot a
        // vacuous staticcall (the census fail-open pattern).
        if (address(settlement_).code.length == 0) {
            revert SettlementHasNoCode(address(settlement_));
        }
        settlement = settlement_;
        recorder = recorder_;
    }

    modifier onlyRecorder() {
        if (msg.sender != recorder) revert NotRecorder(msg.sender);
        _;
    }

    // ─── Rung 1: epoch + sub-root history ───────────────────────────────────────

    /// @notice Record an epoch: a settled state root together with its exposed
    ///         keccak-mirror sub-roots. The state root MUST already be proven by
    ///         the settlement contract (the one binding enforced today).
    /// @param stateRoot the settled dregg state root (a `packLanes` key).
    /// @param height    cumulative proven height at this epoch.
    /// @param subRootVec [Balance, Nullifier, Commitments, Heap] mirror roots.
    function recordEpoch(
        bytes32 stateRoot,
        uint64 height,
        bytes32[NUM_SUBROOTS] calldata subRootVec
    ) external onlyRecorder {
        if (stateRoot == bytes32(0)) revert ZeroStateRoot();
        // The load-bearing binding: only a genuinely settled state can be an
        // epoch. Sub-roots ride on a proven state root, never a fabricated one.
        if (!settlement.isProvenRoot(stateRoot)) revert StateRootNotProven(stateRoot);
        if (_epochs[stateRoot].exists) revert EpochAlreadyRecorded(stateRoot);

        Epoch storage e = _epochs[stateRoot];
        e.stateRoot = stateRoot;
        e.height = height;
        e.exists = true;
        for (uint256 i = 0; i < NUM_SUBROOTS; i++) {
            e.subRoots[i] = subRootVec[i];
        }
        epochRoots.push(stateRoot);

        emit EpochRecorded(stateRoot, height);
        emit SubRootsRecorded(
            stateRoot,
            subRootVec[uint256(SubRoot.Balance)],
            subRootVec[uint256(SubRoot.Nullifier)],
            subRootVec[uint256(SubRoot.Commitments)],
            subRootVec[uint256(SubRoot.Heap)]
        );
    }

    /// @notice Whether an epoch has been recorded for `stateRoot`.
    function hasEpoch(bytes32 stateRoot) external view returns (bool) {
        return _epochs[stateRoot].exists;
    }

    /// @notice The height recorded for `stateRoot` (reverts if unknown).
    function epochHeight(bytes32 stateRoot) external view returns (uint64) {
        if (!_epochs[stateRoot].exists) revert UnknownEpoch(stateRoot);
        return _epochs[stateRoot].height;
    }

    /// @notice The full sub-root vector for a recorded epoch.
    function subRoots(bytes32 stateRoot) external view returns (bytes32[NUM_SUBROOTS] memory) {
        if (!_epochs[stateRoot].exists) revert UnknownEpoch(stateRoot);
        return _epochs[stateRoot].subRoots;
    }

    /// @notice A single sub-root of a recorded epoch.
    function subRootOf(bytes32 stateRoot, SubRoot kind) public view returns (bytes32) {
        if (!_epochs[stateRoot].exists) revert UnknownEpoch(stateRoot);
        return _epochs[stateRoot].subRoots[uint256(kind)];
    }

    /// @notice Number of recorded epochs.
    function epochCount() external view returns (uint256) {
        return epochRoots.length;
    }

    // ─── Rung 2: inclusion-proof verification (THE usable surface) ──────────────

    /// @notice Verify a keccak Merkle inclusion of `leaf` in a specific sub-root
    ///         of a recorded epoch. The generic primitive; the helpers below are
    ///         typed sugar over it.
    /// @return true iff `leaf` at `index` is included under the epoch's `kind` sub-root.
    function verifyAgainstSubRoot(
        bytes32 stateRoot,
        SubRoot kind,
        bytes32 leaf,
        uint256 index,
        bytes32[] calldata siblings
    ) public view returns (bool) {
        bytes32 root = subRootOf(stateRoot, kind); // reverts on unknown epoch
        return DreggMerkle.verifyInclusion(root, leaf, index, siblings);
    }

    /// @notice Prove that `account` holds `balance` in dregg at `stateRoot`.
    ///         The balance leaf is `keccak(0x00 ++ keccak(account ++ balance))`
    ///         (encodeLeaf over the (account,balance) commitment). An RWA/DeFi
    ///         contract gates entitlements on this — e.g. "A holds >= N" by
    ///         proving A's exact balance leaf and comparing off the returned value.
    function proveHolding(
        bytes32 stateRoot,
        address account,
        uint256 balance,
        uint256 index,
        bytes32[] calldata siblings
    ) external view returns (bool) {
        bytes32 element = keccak256(abi.encodePacked(account, balance));
        bytes32 leaf = DreggMerkle.encodeLeaf(element);
        return verifyAgainstSubRoot(stateRoot, SubRoot.Balance, leaf, index, siblings);
    }

    /// @notice Prove that `nullifier` is spent in dregg at `stateRoot` (present in
    ///         the nullifier set). A market/bridge checks double-spend with this.
    function proveNullifierSpent(
        bytes32 stateRoot,
        bytes32 nullifier,
        uint256 index,
        bytes32[] calldata siblings
    ) external view returns (bool) {
        bytes32 leaf = DreggMerkle.encodeLeaf(nullifier);
        return verifyAgainstSubRoot(stateRoot, SubRoot.Nullifier, leaf, index, siblings);
    }

    /// @notice Prove that `commitment` (a note commitment) exists in dregg at
    ///         `stateRoot` (present in the commitments set).
    function proveCommitmentExists(
        bytes32 stateRoot,
        bytes32 commitment,
        uint256 index,
        bytes32[] calldata siblings
    ) external view returns (bool) {
        bytes32 leaf = DreggMerkle.encodeLeaf(commitment);
        return verifyAgainstSubRoot(stateRoot, SubRoot.Commitments, leaf, index, siblings);
    }

    // ─── Rung 3: inbound commitments (eth → dregg, the instruction channel) ─────

    /// @notice Emit an inbound commitment for dregg to ingest. This is the
    ///         eth→dregg leg's instruction channel: dregg's relayer/light-client
    ///         watches `InboundCommitment` and mirrors the commitment into state.
    ///         Value custody (deposits) is handled by a companion escrow that
    ///         calls this; on its own it carries only instructions/commitments.
    function submitInbound(bytes32 commitment, bytes calldata payload) external {
        emit InboundCommitment(commitment, msg.sender, payload);
    }
}

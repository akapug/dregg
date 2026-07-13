// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import {DreggStateOracle} from "../contracts/DreggStateOracle.sol";
import {DreggMerkle} from "../contracts/DreggMerkle.sol";
import {IDreggSettlement} from "../contracts/IDreggSettlement.sol";

/// Minimal `IDreggSettlement` mock: the oracle only reads `isProvenRoot`, and
/// its constructor requires the settlement address to have code. Everything else
/// is stubbed. `setProven` lets the test mark a root as genuinely settled.
contract MockSettlement is IDreggSettlement {
    mapping(bytes32 => bool) public proven;

    function setProven(bytes32 root, bool v) external {
        proven[root] = v;
    }

    function isProvenRoot(bytes32 root) external view returns (bool) {
        return proven[root];
    }

    function isProvenMessageRoot(bytes32) external pure returns (bool) {
        return false;
    }

    function provenRoot() external pure returns (bytes32) {
        return bytes32(0);
    }

    function provenRootLanes() external pure returns (uint32[8] memory l) {
        return l;
    }

    function genesisAnchor() external pure returns (bytes32) {
        return bytes32(0);
    }

    function genesisAnchorLanes() external pure returns (uint32[8] memory l) {
        return l;
    }

    function genesisEstablished() external pure returns (bool) {
        return true;
    }

    function provenHeight() external pure returns (uint64) {
        return 0;
    }

    function verifyingKeyHash() external pure returns (bytes32) {
        return bytes32(0);
    }

    function settle(
        uint256[2] calldata,
        uint256[2][2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint256[2] calldata,
        uint32[8] calldata,
        uint32[8] calldata,
        uint32,
        uint32[8] calldata,
        bytes32
    ) external {}
}

/// THE INCLUSION-PROOF TEST: a genuine keccak Merkle inclusion of a real dregg
/// nullifier leaf verifies against a recorded epoch's nullifier sub-root; every
/// forgery polarity (wrong leaf, tampered sibling, wrong index, wrong epoch)
/// rejects. The tree is a REAL positional keccak Merkle tree over dregg
/// nullifier elements — the EVM-native mirror of dregg's nullifier sub-root
/// (`metatheory Dregg2.Circuit.StateCommit` binds `nullifierRoot`; this is its
/// keccak mirror, the same construction as the outbound message root). The
/// verifier logic is the real artifact; soundness is keccak collision-resistance.
contract DreggStateOracleTest is Test {
    MockSettlement settlement;
    DreggStateOracle oracle;

    address recorder = address(0xDEE6);

    // A settled dregg state root (a packLanes key). Marked proven on the mock.
    bytes32 stateRoot = keccak256("dregg.state.root.epoch.42");

    // The real dregg nullifier elements committed in this epoch's nullifier set.
    // (Canonical 32-byte nullifier values — the tree leaves are encodeLeaf of these.)
    bytes32[] nullifiers;

    // The built tree (level 0 = padded leaves … top = [root]).
    bytes32[][] levels;
    bytes32 nullifierRoot;

    function setUp() public {
        settlement = new MockSettlement();
        settlement.setProven(stateRoot, true);
        oracle = new DreggStateOracle(IDreggSettlement(address(settlement)), recorder);

        // Five genuine nullifier elements (odd count → padding exercised).
        nullifiers.push(keccak256("nullifier:note-a"));
        nullifiers.push(keccak256("nullifier:note-b"));
        nullifiers.push(keccak256("nullifier:note-c"));
        nullifiers.push(keccak256("nullifier:note-d"));
        nullifiers.push(keccak256("nullifier:note-e"));

        // Build the positional keccak Merkle tree over encodeLeaf(nullifier).
        bytes32[] memory leaves = new bytes32[](nullifiers.length);
        for (uint256 i = 0; i < nullifiers.length; i++) {
            leaves[i] = DreggMerkle.encodeLeaf(nullifiers[i]);
        }
        levels = _buildTree(leaves);
        nullifierRoot = levels[levels.length - 1][0];

        // Record the epoch: state root proven, nullifier sub-root = our mirror.
        bytes32[4] memory sub;
        sub[uint256(DreggStateOracle.SubRoot.Nullifier)] = nullifierRoot;
        vm.prank(recorder);
        oracle.recordEpoch(stateRoot, 42, sub);
    }

    // ─── Polarity 1: GENUINE inclusion verifies ────────────────────────────────

    function test_GenuineNullifierInclusionVerifies() public view {
        // Every real nullifier in the set proves spent.
        for (uint256 i = 0; i < nullifiers.length; i++) {
            (uint256 index, bytes32[] memory siblings) = _proof(i);
            assertTrue(
                oracle.proveNullifierSpent(stateRoot, nullifiers[i], index, siblings),
                "genuine nullifier inclusion must verify"
            );
        }
    }

    function test_GenericVerifyAgainstSubRootVerifies() public view {
        (uint256 index, bytes32[] memory siblings) = _proof(2);
        bytes32 leaf = DreggMerkle.encodeLeaf(nullifiers[2]);
        assertTrue(
            oracle.verifyAgainstSubRoot(
                stateRoot, DreggStateOracle.SubRoot.Nullifier, leaf, index, siblings
            ),
            "generic sub-root inclusion must verify"
        );
    }

    // ─── Polarity 2: FORGERIES reject ──────────────────────────────────────────

    /// A nullifier NOT in the set cannot be proven with any honest sibling path.
    function test_ForgedNullifierRejects() public view {
        (uint256 index, bytes32[] memory siblings) = _proof(1);
        bytes32 notInSet = keccak256("nullifier:never-spent");
        assertFalse(
            oracle.proveNullifierSpent(stateRoot, notInSet, index, siblings),
            "a nullifier not in the set must NOT verify"
        );
    }

    /// A tampered sibling breaks the path — the recomputed root differs.
    function test_TamperedSiblingRejects() public view {
        (uint256 index, bytes32[] memory siblings) = _proof(3);
        require(siblings.length > 0, "need a sibling to tamper");
        siblings[0] = bytes32(uint256(siblings[0]) ^ 1); // flip one bit
        assertFalse(
            oracle.proveNullifierSpent(stateRoot, nullifiers[3], index, siblings),
            "a tampered sibling must NOT verify"
        );
    }

    /// The right leaf with the WRONG index (a valid index for a different leaf)
    /// must not verify — position is bound.
    function test_WrongIndexRejects() public view {
        (, bytes32[] memory siblings) = _proof(0);
        // Present leaf 0 with the siblings for index 0 but claim index 1.
        bytes32 leaf = DreggMerkle.encodeLeaf(nullifiers[0]);
        assertFalse(
            oracle.verifyAgainstSubRoot(
                stateRoot, DreggStateOracle.SubRoot.Nullifier, leaf, 1, siblings
            ),
            "a genuine leaf at a wrong index must NOT verify"
        );
    }

    /// A genuine proof presented against the WRONG sub-root kind (Commitments,
    /// which is zero here) must not verify.
    function test_WrongSubRootKindRejects() public view {
        (uint256 index, bytes32[] memory siblings) = _proof(2);
        bytes32 leaf = DreggMerkle.encodeLeaf(nullifiers[2]);
        assertFalse(
            oracle.verifyAgainstSubRoot(
                stateRoot, DreggStateOracle.SubRoot.Commitments, leaf, index, siblings
            ),
            "inclusion under a different (empty) sub-root must NOT verify"
        );
    }

    // ─── Epoch / binding behavior ───────────────────────────────────────────────

    /// The oracle refuses to record an epoch for a state dregg never settled.
    function test_RecordEpochRejectsUnprovenRoot() public {
        bytes32 bogus = keccak256("never.settled");
        bytes32[4] memory sub;
        vm.prank(recorder);
        vm.expectRevert(
            abi.encodeWithSelector(DreggStateOracle.StateRootNotProven.selector, bogus)
        );
        oracle.recordEpoch(bogus, 1, sub);
    }

    /// Only the recorder may record epochs.
    function test_OnlyRecorderCanRecord() public {
        bytes32[4] memory sub;
        vm.expectRevert(
            abi.encodeWithSelector(DreggStateOracle.NotRecorder.selector, address(this))
        );
        oracle.recordEpoch(stateRoot, 1, sub);
    }

    /// Querying inclusion against an unrecorded epoch reverts (UnknownEpoch).
    function test_InclusionAgainstUnknownEpochReverts() public {
        bytes32 unknown = keccak256("unrecorded.epoch");
        (uint256 index, bytes32[] memory siblings) = _proof(0);
        bytes32 leaf = DreggMerkle.encodeLeaf(nullifiers[0]);
        vm.expectRevert(
            abi.encodeWithSelector(DreggStateOracle.UnknownEpoch.selector, unknown)
        );
        oracle.verifyAgainstSubRoot(
            unknown, DreggStateOracle.SubRoot.Nullifier, leaf, index, siblings
        );
    }

    function test_EpochHistoryExposed() public view {
        assertTrue(oracle.hasEpoch(stateRoot));
        assertEq(oracle.epochHeight(stateRoot), 42);
        assertEq(oracle.epochCount(), 1);
        assertEq(
            oracle.subRootOf(stateRoot, DreggStateOracle.SubRoot.Nullifier),
            nullifierRoot
        );
    }

    // ─── Positional keccak Merkle tree helpers (mirror DreggMerkle) ─────────────

    /// Build all levels of a positional keccak tree; pads level 0 to a power of
    /// two with `DreggMerkle.EMPTY_LEAF`. levels[0] = leaves, last level = [root].
    function _buildTree(bytes32[] memory leaves) internal pure returns (bytes32[][] memory) {
        // Pad to next power of two.
        uint256 n = 1;
        while (n < leaves.length) n <<= 1;
        bytes32[] memory level = new bytes32[](n);
        for (uint256 i = 0; i < n; i++) {
            level[i] = i < leaves.length ? leaves[i] : DreggMerkle.EMPTY_LEAF;
        }

        // Count levels: log2(n) + 1.
        uint256 depth = 0;
        for (uint256 t = n; t > 1; t >>= 1) depth++;
        bytes32[][] memory out = new bytes32[][](depth + 1);
        out[0] = level;

        uint256 lvl = 0;
        while (level.length > 1) {
            uint256 half = level.length / 2;
            bytes32[] memory parent = new bytes32[](half);
            for (uint256 i = 0; i < half; i++) {
                parent[i] = keccak256(abi.encodePacked(level[2 * i], level[2 * i + 1]));
            }
            lvl++;
            out[lvl] = parent;
            level = parent;
        }
        return out;
    }

    /// The inclusion proof for leaf `index`: the sibling at each level, bottom→top.
    function _proof(uint256 index) internal view returns (uint256, bytes32[] memory) {
        uint256 depth = levels.length - 1;
        bytes32[] memory siblings = new bytes32[](depth);
        uint256 idx = index;
        for (uint256 l = 0; l < depth; l++) {
            uint256 sib = idx ^ 1;
            siblings[l] = levels[l][sib];
            idx >>= 1;
        }
        return (index, siblings);
    }
}

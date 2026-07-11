// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/DreggCredentialGate.sol";

/// @dev Mock SP1 Verifier that always succeeds (shared pattern with vault tests).
contract MockSP1VerifierForGate {
    bool public shouldPass = true;

    function setShouldPass(bool _pass) external {
        shouldPass = _pass;
    }

    function verifyProof(
        bytes32, /* vkey */
        bytes calldata, /* publicValues */
        bytes calldata /* proofBytes */
    ) external view {
        require(shouldPass, "MockSP1Verifier: proof rejected");
    }
}

contract DreggCredentialGateTest is Test {
    DreggCredentialGate public gate;
    MockSP1VerifierForGate public verifier;

    bytes32 constant PROGRAM_VKEY = bytes32(uint256(0xcafe));
    bytes32 constant FED_ROOT = bytes32(uint256(0xfed));
    bytes32 constant PRED_HASH = keccak256("age >= 18");

    address admin = address(this);
    address user = address(0xBEEF);

    function setUp() public {
        verifier = new MockSP1VerifierForGate();
        gate = new DreggCredentialGate(address(verifier), PROGRAM_VKEY, admin);

        // Trust our test federation root.
        gate.setFederationTrust(FED_ROOT, true);
    }

    // ─── Admin / VK Governance ──────────────────────────────────────────────

    function test_adminCanSetFederationTrust() public {
        bytes32 newRoot = bytes32(uint256(0xabc));
        gate.setFederationTrust(newRoot, true);
        assertTrue(gate.trustedFederations(newRoot));
    }

    function test_adminCanRevokeFederationTrust() public {
        gate.setFederationTrust(FED_ROOT, false);
        assertFalse(gate.trustedFederations(FED_ROOT));
    }

    function test_nonAdminCannotSetFederationTrust() public {
        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.setFederationTrust(FED_ROOT, false);
    }

    // ─── Credential Verification ────────────────────────────────────────────

    function test_verifyCredentialReturnsTrue() public view {
        bytes32 nullifier = keccak256("verifyNull");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory proofBytes = hex"1234";
        bytes memory sp1Proof = abi.encode(proofBytes, publicValues);

        bool result = gate.verifyCredential(FED_ROOT, PRED_HASH, sp1Proof);
        assertTrue(result);
    }

    function test_verifyCredentialRevertsUntrustedFederation() public {
        bytes32 untrusted = bytes32(uint256(0x999));
        bytes memory sp1Proof = abi.encode(hex"1234", abi.encode(true, untrusted, PRED_HASH, bytes32(0)));

        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.UntrustedFederation.selector, untrusted));
        gate.verifyCredential(untrusted, PRED_HASH, sp1Proof);
    }

    function test_verifyCredentialReturnsFalseOnInvalidProof() public {
        verifier.setShouldPass(false);
        bytes memory sp1Proof = abi.encode(hex"bad0", abi.encode(true, FED_ROOT, PRED_HASH, bytes32(0)));

        bool result = gate.verifyCredential(FED_ROOT, PRED_HASH, sp1Proof);
        assertFalse(result);
    }

    // ─── Mint With Credential ───────────────────────────────────────────────

    function test_mintWithCredential() public {
        uint256 tokenId = 1;
        bytes32 nullifier = keccak256("mintNull1");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory sp1Proof = abi.encode(hex"5678", publicValues);

        vm.prank(user);
        gate.mintWithCredential(tokenId, FED_ROOT, PRED_HASH, sp1Proof);

        assertEq(gate.tokenOwner(tokenId), user);
        assertEq(gate.balanceOf(user), 1);
        // The bare presentation nullifier is the replay key: one mint per credential.
        assertTrue(gate.usedNullifiers(nullifier));
    }

    function test_mintRejectsDuplicateNullifierSameToken() public {
        // Replaying the same nullifier against the SAME tokenId must revert.
        bytes32 nullifier = keccak256("mintNull2");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory sp1Proof = abi.encode(hex"5678", publicValues);

        vm.prank(user);
        gate.mintWithCredential(1, FED_ROOT, PRED_HASH, sp1Proof);

        vm.prank(user);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.NullifierAlreadyUsed.selector, nullifier));
        gate.mintWithCredential(1, FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_mintRejectsReplayAcrossTokenIds() public {
        // SOUNDNESS: tokenId is a caller argument the proof never binds, so one
        // credential presentation must NOT be replayable to mint a second (different)
        // tokenId. The bare nullifier is the key: the second mint reverts.
        bytes32 nullifier = keccak256("mintNull3");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory sp1Proof = abi.encode(hex"5678", publicValues);

        vm.prank(user);
        gate.mintWithCredential(10, FED_ROOT, PRED_HASH, sp1Proof);

        vm.prank(user);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.NullifierAlreadyUsed.selector, nullifier));
        gate.mintWithCredential(11, FED_ROOT, PRED_HASH, sp1Proof);

        assertEq(gate.tokenOwner(10), user);
        assertEq(gate.tokenOwner(11), address(0));
        assertEq(gate.balanceOf(user), 1);
    }

    function test_mintRejectsAlreadyMintedToken() public {
        uint256 tokenId = 42;
        bytes32 null1 = keccak256("mintNullA");
        bytes32 null2 = keccak256("mintNullB");

        bytes memory sp1Proof1 = abi.encode(hex"aa", abi.encode(true, FED_ROOT, PRED_HASH, null1));
        bytes memory sp1Proof2 = abi.encode(hex"bb", abi.encode(true, FED_ROOT, PRED_HASH, null2));

        vm.prank(user);
        gate.mintWithCredential(tokenId, FED_ROOT, PRED_HASH, sp1Proof1);

        // Different user tries to mint same tokenId.
        address user2 = address(0xCAFE);
        vm.prank(user2);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.TokenAlreadyMinted.selector, tokenId));
        gate.mintWithCredential(tokenId, FED_ROOT, PRED_HASH, sp1Proof2);
    }

    // ─── Vote With Credential ───────────────────────────────────────────────

    function test_voteWithCredential() public {
        uint256 proposalId = 7;
        bytes32 nullifier = keccak256("voteNull1");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory sp1Proof = abi.encode(hex"707e", publicValues);

        vm.prank(user);
        gate.voteWithCredential(proposalId, true, FED_ROOT, PRED_HASH, sp1Proof);

        (uint256 yes, uint256 no) = gate.getVotes(proposalId);
        assertEq(yes, 1);
        assertEq(no, 0);
    }

    function test_voteRejectsDoubleVote() public {
        uint256 proposalId = 8;
        bytes32 nullifier = keccak256("voteNull2");
        bytes memory publicValues = abi.encode(true, FED_ROOT, PRED_HASH, nullifier);
        bytes memory sp1Proof = abi.encode(hex"707e", publicValues);

        vm.prank(user);
        gate.voteWithCredential(proposalId, true, FED_ROOT, PRED_HASH, sp1Proof);

        vm.prank(user);
        vm.expectRevert(abi.encodeWithSelector(DreggCredentialGate.AlreadyVoted.selector, proposalId, nullifier));
        gate.voteWithCredential(proposalId, false, FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_voteAllowsSameNullifierDifferentProposal() public {
        bytes32 nullifier1 = keccak256("voteMulti1");
        bytes32 nullifier2 = keccak256("voteMulti2");
        bytes memory sp1Proof1 = abi.encode(hex"01", abi.encode(true, FED_ROOT, PRED_HASH, nullifier1));
        bytes memory sp1Proof2 = abi.encode(hex"02", abi.encode(true, FED_ROOT, PRED_HASH, nullifier2));

        vm.prank(user);
        gate.voteWithCredential(1, true, FED_ROOT, PRED_HASH, sp1Proof1);

        vm.prank(user);
        gate.voteWithCredential(2, false, FED_ROOT, PRED_HASH, sp1Proof2);

        (uint256 yes1, ) = gate.getVotes(1);
        (, uint256 no2) = gate.getVotes(2);
        assertEq(yes1, 1);
        assertEq(no2, 1);
    }

    // ─── Proof Failure ──────────────────────────────────────────────────────

    function test_mintRevertsOnInvalidProof() public {
        verifier.setShouldPass(false);
        bytes32 nullifier = keccak256("failMint");
        bytes memory sp1Proof = abi.encode(hex"0bad", abi.encode(true, FED_ROOT, PRED_HASH, nullifier));

        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.ProofVerificationFailed.selector);
        gate.mintWithCredential(99, FED_ROOT, PRED_HASH, sp1Proof);
    }

    // ─── Fail-Closed Verifier (codeless address must never accept) ──────────

    function test_constructorRejectsCodelessVerifier() public {
        address codeless = address(0x5678);
        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        new DreggCredentialGate(codeless, PROGRAM_VKEY, admin);
    }

    function test_verifyCredentialRevertsWhenVerifierLosesCode() public {
        bytes memory sp1Proof = abi.encode(
            hex"1234",
            abi.encode(true, FED_ROOT, PRED_HASH, keccak256("codelessNull"))
        );

        // Strip the verifier's code: the raw staticcall would now succeed
        // vacuously, so the call-time guard must reject.
        vm.etch(address(verifier), "");

        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        gate.verifyCredential(FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_mintRevertsWhenVerifierLosesCode() public {
        bytes memory sp1Proof = abi.encode(
            hex"1234",
            abi.encode(true, FED_ROOT, PRED_HASH, keccak256("codelessMint"))
        );

        vm.etch(address(verifier), "");

        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        gate.mintWithCredential(77, FED_ROOT, PRED_HASH, sp1Proof);
    }

    function test_voteRevertsWhenVerifierLosesCode() public {
        bytes memory sp1Proof = abi.encode(
            hex"1234",
            abi.encode(true, FED_ROOT, PRED_HASH, keccak256("codelessVote"))
        );

        vm.etch(address(verifier), "");

        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.VerifierNotContract.selector);
        gate.voteWithCredential(3, true, FED_ROOT, PRED_HASH, sp1Proof);
    }

    // ─── Two-Step Admin Rotation ────────────────────────────────────────────

    function test_adminRotationTwoStep() public {
        address newAdmin = address(0xAD31);

        gate.proposeAdmin(newAdmin);
        assertEq(gate.pendingAdmin(), newAdmin);
        assertEq(gate.admin(), admin); // proposal alone does NOT rotate

        vm.prank(newAdmin);
        gate.acceptAdmin();
        assertEq(gate.admin(), newAdmin);
        assertEq(gate.pendingAdmin(), address(0));

        // New admin holds the power...
        bytes32 newRoot = bytes32(uint256(0x1111));
        vm.prank(newAdmin);
        gate.setFederationTrust(newRoot, true);
        assertTrue(gate.trustedFederations(newRoot));

        // ...and the old admin has lost it.
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.setFederationTrust(newRoot, false);
    }

    function test_proposeAdminRejectsNonAdmin() public {
        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.proposeAdmin(user);
    }

    function test_acceptAdminRejectsNonPending() public {
        gate.proposeAdmin(address(0xAD31));

        vm.prank(user); // not the proposed admin
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.acceptAdmin();
    }

    function test_acceptAdminRejectsWhenNothingProposed() public {
        vm.prank(user);
        vm.expectRevert(DreggCredentialGate.Unauthorized.selector);
        gate.acceptAdmin();
    }
}

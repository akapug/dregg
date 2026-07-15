// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../contracts/launchpad/DreggDeployerGate.sol";
import "../contracts/DreggCredentialGate.sol";

/// @dev Mock SP1 Verifier (shared pattern with DreggCredentialGate.t.sol).
contract MockSP1VerifierForDeployerGate {
    bool public shouldPass = true;

    function setShouldPass(bool _pass) external {
        shouldPass = _pass;
    }

    function verifyProof(bytes32, bytes calldata, bytes calldata) external view {
        require(shouldPass, "MockSP1Verifier: proof rejected");
    }
}

/// The deployer-gate, both polarities, composing the REAL DreggCredentialGate for
/// the reveal-nothing private interview arm.
contract DreggDeployerGateTest is Test {
    DreggDeployerGate gate;
    DreggCredentialGate credGate;
    MockSP1VerifierForDeployerGate verifier;

    address admin = address(0xA11CE);
    address deployer = address(0xBEEF);
    address scammer = address(0xBAD);
    bytes32 fedRoot = keccak256("interview-passed-federation");
    bytes32 programVkey = keccak256("dregg-credential-vkey");
    bytes32 launchParams = keccak256("Meridian Grid schedule");
    uint256 constant MIN_BOND = 10 ether;

    function setUp() public {
        vm.prank(admin);
        gate = new DreggDeployerGate(admin, MIN_BOND);

        verifier = new MockSP1VerifierForDeployerGate();
        credGate = new DreggCredentialGate(address(verifier), programVkey, admin);
        vm.prank(admin);
        credGate.setFederationTrust(fedRoot, true);

        // Enable all four arms and wire the credential gate.
        vm.startPrank(admin);
        gate.setAcceptedArms(uint8(0x0F));
        gate.setCredentialGate(credGate, fedRoot);
        vm.stopPrank();
    }

    // ─── helpers ──────────────────────────────────────────────────────────────
    function bondCap() internal view returns (bytes memory) {
        return abi.encode(gate.ARM_BOND(), bytes(""));
    }

    function interviewPublicCap(bytes32 commitment) internal view returns (bytes memory) {
        return abi.encode(gate.ARM_INTERVIEW_PUBLIC(), abi.encode(commitment));
    }

    function auditCap(bytes32 reportHash) internal view returns (bytes memory) {
        return abi.encode(gate.ARM_AUDIT(), abi.encode(reportHash));
    }

    function privateInterviewCap(bytes32 nullifier) internal view returns (bytes memory) {
        bytes memory publicValues = abi.encode(true, fedRoot, gate.INTERVIEW_PREDICATE(), nullifier);
        bytes memory sp1Proof = abi.encode(bytes("proof"), publicValues);
        return abi.encode(gate.ARM_INTERVIEW_PRIVATE(), abi.encode(fedRoot, sp1Proof));
    }

    // ─── (a) BOND ARM ───────────────────────────────────────────────────────────
    function test_bond_gatedDeployerAuthorized() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();

        assertTrue(gate.authorizeDeploy(deployer, launchParams, bondCap()));
    }

    function test_bond_ungatedDeployerRejected() public {
        // scammer never posted a bond.
        assertFalse(gate.authorizeDeploy(scammer, launchParams, bondCap()));
    }

    function test_bond_underMinRejected() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 1 ether}(); // below MIN_BOND
        assertFalse(gate.authorizeDeploy(deployer, launchParams, bondCap()));
    }

    function test_bond_slashedBelowMinRejected() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 12 ether}();
        assertTrue(gate.authorizeDeploy(deployer, launchParams, bondCap()));

        // Fraud-proof slashes the bond below the floor → no longer authorized.
        vm.prank(admin); // admin is the default slasher
        gate.slash(deployer, 5 ether, address(0xF00D));
        assertFalse(gate.authorizeDeploy(deployer, launchParams, bondCap()));
    }

    // ─── (b) INTERVIEW ARM — public commitment ───────────────────────────────────
    function test_interviewPublic_passedAuthorized() public {
        bytes32 commitment = keccak256("verdict:PASS:meridian:nonce");
        vm.prank(admin); // admin is the default attester
        gate.attestInterview(commitment, true);
        assertTrue(gate.authorizeDeploy(deployer, launchParams, interviewPublicCap(commitment)));
    }

    function test_interviewPublic_notPassedRejected() public {
        bytes32 commitment = keccak256("verdict:FAIL:quantumyield:nonce");
        // never attested → rejected.
        assertFalse(gate.authorizeDeploy(scammer, launchParams, interviewPublicCap(commitment)));
    }

    function test_interviewPublic_onlyAttesterCanAttest() public {
        bytes32 commitment = keccak256("x");
        vm.prank(scammer);
        vm.expectRevert(DreggDeployerGate.Unauthorized.selector);
        gate.attestInterview(commitment, true);
    }

    // ─── (b') INTERVIEW ARM — private (reveal-nothing, composes credential gate) ──
    function test_interviewPrivate_validCredentialAuthorized() public {
        verifier.setShouldPass(true);
        bytes32 nullifier = keccak256("presentation-1");
        assertTrue(gate.authorizeDeploy(deployer, launchParams, privateInterviewCap(nullifier)));
    }

    function test_interviewPrivate_forgedProofRejected() public {
        verifier.setShouldPass(false); // the SP1 verifier rejects a forged proof
        bytes32 nullifier = keccak256("presentation-forged");
        assertFalse(gate.authorizeDeploy(scammer, launchParams, privateInterviewCap(nullifier)));
    }

    function test_interviewPrivate_replayRejected() public {
        verifier.setShouldPass(true);
        bytes32 nullifier = keccak256("presentation-replay");
        bytes memory cap = privateInterviewCap(nullifier);
        assertTrue(gate.authorizeDeploy(deployer, launchParams, cap));
        // Same nullifier again → sybil replay blocked. Build the cap before
        // arming expectRevert so the helper's view-calls do not consume it.
        vm.expectRevert(
            abi.encodeWithSelector(DreggDeployerGate.NullifierAlreadyUsed.selector, nullifier)
        );
        gate.authorizeDeploy(deployer, launchParams, cap);
    }

    function test_interviewPrivate_wrongFederationRejected() public {
        verifier.setShouldPass(true);
        bytes32 nullifier = keccak256("presentation-wrongfed");
        bytes32 wrongFed = keccak256("some-other-federation");
        bytes memory publicValues =
            abi.encode(true, wrongFed, gate.INTERVIEW_PREDICATE(), nullifier);
        bytes memory sp1Proof = abi.encode(bytes("proof"), publicValues);
        bytes memory cap = abi.encode(gate.ARM_INTERVIEW_PRIVATE(), abi.encode(wrongFed, sp1Proof));
        assertFalse(gate.authorizeDeploy(scammer, launchParams, cap));
    }

    // ─── (c) AUDIT ARM ────────────────────────────────────────────────────────────
    function test_audit_clearedAuthorized() public {
        bytes32 reportHash = keccak256("audit-report-meridian");
        vm.prank(admin); // default auditor
        gate.attestAudit(reportHash, true);
        assertTrue(gate.authorizeDeploy(deployer, launchParams, auditCap(reportHash)));
    }

    function test_audit_uncleaerdRejected() public {
        bytes32 reportHash = keccak256("audit-report-never-ran");
        assertFalse(gate.authorizeDeploy(scammer, launchParams, auditCap(reportHash)));
    }

    // ─── PLUGGABLE — disabled arm is rejected even if condition holds ─────────────
    function test_disabledArmRejected() public {
        // Operator accepts ONLY the audit arm (compute the mask before pranking
        // so the ARM_AUDIT() read does not consume the prank).
        uint8 auditOnly = uint8(1 << gate.ARM_AUDIT());
        vm.prank(admin);
        gate.setAcceptedArms(auditOnly);

        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 50 ether}();
        // Bond condition holds, but the bond arm is disabled → rejected.
        bytes memory cap = bondCap();
        assertFalse(gate.authorizeDeploy(deployer, launchParams, cap));
    }

    function test_emptyCapabilityRejected() public {
        assertFalse(gate.authorizeDeploy(scammer, launchParams, bytes("")));
    }

    // ─── BOND lifecycle ──────────────────────────────────────────────────────────
    function test_slashOnlyBySlasher() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 10 ether}();
        vm.prank(scammer);
        vm.expectRevert(DreggDeployerGate.Unauthorized.selector);
        gate.slash(deployer, 1 ether, scammer);
    }

    function test_withdrawBond() public {
        vm.deal(deployer, 100 ether);
        vm.prank(deployer);
        gate.postBond{value: 10 ether}();
        uint256 before = deployer.balance;
        vm.prank(deployer);
        gate.withdrawBond();
        assertEq(deployer.balance, before + 10 ether);
        assertEq(gate.bondOf(deployer), 0);
    }
}

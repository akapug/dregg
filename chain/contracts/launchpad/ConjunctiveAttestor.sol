// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IClearingAttestor} from "./IClearingAttestor.sol";

/// @title ConjunctiveAttestor — "AND" over `IClearingAttestor` arms.
/// @notice The pluggability made concrete. `DreggLaunchpad` pins the
///         `IClearingAttestor` SEAM and never an arm, so a deployment already
///         chooses committee (`CommitteeAttestor`), proof (`DreggProofAttestor`),
///         or neither (`address(0)` → rung-1 REPLAYABLE only). This contract adds
///         the remaining choice — BOTH — without the launchpad learning anything
///         new: it is itself just an `IClearingAttestor`.
///
/// A clearing is attested iff EVERY arm attests it. That is the conservative
/// composition: the trust of the conjunction is the trust of the STRONGEST arm
/// (an adversary must defeat all of them), and its liveness is that of the
/// WEAKEST (any arm withholding stalls the launch into the timeout-refund
/// backstop, `DreggLaunchpad.reclaimEscrow` — a liveness fault, never a theft).
/// A disjunctive ("either arm suffices") composition would invert both, taking
/// the trust of the weakest arm — it is deliberately NOT offered here.
///
/// `proof` is `abi.encode(bytes[] armProofs)`, one blob per arm, in constructor
/// order. Each arm receives its own blob and the same clearing tuple. A
/// malformed envelope, a wrong arm count, or a reverting arm all yield false —
/// never a revert — so the launchpad's typed `ClearingNotAttested` stays the
/// single refusal reason and a hostile arm cannot brick a launch.
contract ConjunctiveAttestor is IClearingAttestor {
    IClearingAttestor[] private _arms;

    error NoArms();
    error ZeroArm();
    error DuplicateArm(address arm);
    error ArmHasNoCode(address arm);

    constructor(IClearingAttestor[] memory arms_) {
        uint256 n = arms_.length;
        if (n == 0) revert NoArms();
        for (uint256 i = 0; i < n; i++) {
            address a = address(arms_[i]);
            if (a == address(0)) revert ZeroArm();
            // Fail closed: a codeless arm's staticcall would "succeed" and could
            // be decoded as an accept.
            if (a.code.length == 0) revert ArmHasNoCode(a);
            for (uint256 j = 0; j < i; j++) {
                if (address(arms_[j]) == a) revert DuplicateArm(a);
            }
            _arms.push(arms_[i]);
        }
    }

    function armCount() external view returns (uint256) {
        return _arms.length;
    }

    function armAt(uint256 i) external view returns (IClearingAttestor) {
        return _arms[i];
    }

    /// @notice True iff EVERY arm attests the clearing under its own blob.
    function attestClearing(
        uint256 launchId,
        uint256 saleSupply,
        uint256 clearingPrice,
        bytes32 bookCommit,
        bytes calldata proof
    ) external view returns (bool) {
        bytes[] memory armProofs;
        // A malformed envelope decodes to nothing → not an attestation → false.
        try this.decodeArmProofs(proof) returns (bytes[] memory decoded) {
            armProofs = decoded;
        } catch {
            return false;
        }
        if (armProofs.length != _arms.length) return false;

        for (uint256 i = 0; i < _arms.length; i++) {
            // A reverting arm counts as a refusal, never a brick.
            try _arms[i].attestClearing(launchId, saleSupply, clearingPrice, bookCommit, armProofs[i]) returns (
                bool ok
            ) {
                if (!ok) return false;
            } catch {
                return false;
            }
        }
        return true;
    }

    /// External so `attestClearing` can `try/catch` a malformed `abi.decode`
    /// without reverting the view.
    function decodeArmProofs(bytes calldata proof) external pure returns (bytes[] memory) {
        return abi.decode(proof, (bytes[]));
    }
}

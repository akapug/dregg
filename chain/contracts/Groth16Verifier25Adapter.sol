// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IGroth16Verifier25} from "./IGroth16Verifier25.sol";

/// Adapter from the gnark-GENERATED settlement verifier
/// (DreggGroth16Verifier25.sol, emitted by chain/gnark
/// settlement_snark_test.go via groth16 VerifyingKey.ExportSolidity) to the
/// bool-returning `IGroth16Verifier25` shape `DreggSettlement` consumes.
///
/// The generated contract's `verifyProof(uint256[8] proof,
/// uint256[2] commitments, uint256[2] commitmentPok, uint256[25] input)`
/// REVERTS on an invalid proof and returns nothing on success; this adapter
/// staticcalls it and maps revert -> false. Fail-closed notes:
///
///   - a CODELESS inner address would make the staticcall "succeed"; the
///     constructor refuses one (and `DreggSettlement`'s constructor
///     independently refuses a codeless adapter);
///   - the 8 proof words are forwarded in gnark `MarshalSolidity` order,
///     which is exactly a ++ b[0] ++ b[1] ++ c (EIP-197 word order).
contract Groth16Verifier25Adapter is IGroth16Verifier25 {
    error InnerVerifierHasNoCode(address inner);

    address public immutable inner;

    constructor(address inner_) {
        if (inner_.code.length == 0) revert InnerVerifierHasNoCode(inner_);
        inner = inner_;
    }

    function verifyProof(
        uint256[2] calldata a,
        uint256[2][2] calldata b,
        uint256[2] calldata c,
        uint256[2] calldata commitments,
        uint256[2] calldata commitmentPok,
        uint256[25] calldata publicInputs
    ) external view returns (bool) {
        uint256[8] memory proof = [
            a[0], a[1],
            b[0][0], b[0][1],
            b[1][0], b[1][1],
            c[0], c[1]
        ];
        (bool ok, ) = inner.staticcall(
            abi.encodeWithSignature(
                "verifyProof(uint256[8],uint256[2],uint256[2],uint256[25])",
                proof,
                commitments,
                commitmentPok,
                publicInputs
            )
        );
        return ok;
    }
}

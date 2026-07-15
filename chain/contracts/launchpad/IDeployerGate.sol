// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IDeployerGate
/// @notice OPTIONAL *deployer*-eligibility gate for a dregg launchpad — the
///         complement to `ILaunchEligibility` (which gates BIDDERS). If the
///         launchpad pins a deployer gate, `registerLaunch` requires
///         `authorizeDeploy(...) == true` before it will create a launch.
///
/// ## Why gate the deployer (the community insight, ember-endorsed)
/// "launchpads should tokengate or socially gatekeep the deployers; thousands of
/// scam coins would disappear." Our launchpad already makes the MECHANISM
/// unruggable (disclosed supply, one-shot mint, sealed clearing, vesting lock,
/// solvency-floored pool — the contract cannot rug). This gates WHO may deploy:
/// a deployer must present a **deploy capability** issued only when a pluggable
/// **gate arm** is satisfied — a conduct BOND (economic, slashable), a passed
/// **skeptical-Opus INTERVIEW** (social; a scammer cannot hype past a hard-to-
/// convince reviewer), or a cleared **AUDIT**.
///
/// ## Gate the deployer WITHOUT doxxing (the dreggic differentiator)
/// The interview arm can be presented as an *anonymous credential* — the
/// deployer proves "I hold an interview-passed credential" through
/// `DreggCredentialGate` (ring membership + `keccak256("interview-passed")`
/// predicate), revealing NOTHING about their identity, the interview, or which
/// attestation. The gate learns only "gated: true". A scammer cannot produce the
/// proof; an honest builder is not KYC-doxxed.
///
/// ## The intended `registerLaunch` hook (a 3-line diff, mirroring the bidder
/// gate at `DreggLaunchpad.sol` commitBid line 274):
/// ```solidity
/// if (address(deployerGate) != address(0)
///     && !deployerGate.authorizeDeploy(msg.sender, keccak256(abi.encode(s)), capability))
///     revert DeployerNotGated(msg.sender);
/// ```
interface IDeployerGate {
    /// @param deployer          the address attempting to register a launch.
    /// @param launchParamsHash  a commitment to the launch's disclosed schedule
    ///                          (`keccak256(abi.encode(Schedule))`) — the scope
    ///                          the capability is bound to.
    /// @param capability        the deploy capability: `abi.encode(uint8 arm,
    ///                          bytes armData)` selecting and evidencing the arm.
    /// @return true iff `deployer` is authorized to deploy `launchParamsHash`.
    /// @dev NOT `view`: the ZK/interview arm burns a per-deploy nullifier for
    ///      sybil-resistance, so authorization can modify state.
    function authorizeDeploy(address deployer, bytes32 launchParamsHash, bytes calldata capability)
        external
        returns (bool);
}

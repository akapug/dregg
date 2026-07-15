// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {IClearingAttestor} from "./IClearingAttestor.sol";
import {DreggLaunchpad} from "./DreggLaunchpad.sol";
import {IDreggVerifier, DreggAttestation} from "../socket/DreggVerifier.sol";

/// @title DreggProofAttestor — the PROOF arm of `IClearingAttestor`.
/// @notice The v2 attestor: a launch's clearing is attested iff a REAL dregg
///         Groth16(BN254) wrap proof verifies on-chain, through the OCIP socket
///         (`contracts/socket/DreggVerifier.sol`), for the dregg state
///         transition BOUND to this launch. No signatures, no committee — the
///         attestation is a verified proof or it is nothing.
///
/// This contract does NOT reimplement the pairing or pin a VK. It calls
/// `IDreggVerifier.verifyStatement`, which targets the VK-epoch registry's
/// CURRENT epoch — so a VK rotation (a GAP-flip, the nullifier flip, a
/// re-genesis) is absorbed by the registry and is invisible here and to the
/// launchpad (`OCIP-SECURITY-SOCKET.md`).
///
/// ## ⚑ WHAT THIS PROOF ATTESTS — read this before trusting it
///
/// The dregg wrap statement is 25 pinned lanes (`DreggAttestation.Statement`):
/// `genesis_root[8] · final_root[8] · num_turns · chain_digest[8]`. It carries
/// NO launch id, NO clearing price, NO book commitment — there is no lane for
/// them. So a valid proof attests EXACTLY this and no more:
///
///   > There exists a sequence of `num_turns` VALID dregg turns carrying
///   > `genesis_root` to `final_root` — each turn the sound exercise of a
///   > proof-carrying token over owned state: a conserved, rule-abiding
///   > state transition of THIS dregg instance.
///
/// It does NOT attest "and that transition was launch #7's clearing at price
/// p*". Nothing in the 25 lanes says so. That link is asserted by the BINDER
/// (`bindLaunch`) and is TRUSTED — see §Trust below. Naming this is the point:
/// the alternative is the unbound-attestation bug, where any valid proof about
/// the instance would attest any launch's clearing.
///
/// ## What is NOT trusted — the clearing VALUES
///
/// The clearing price and fills are NOT taken from the proof, the binder, or
/// anyone. `DreggLaunchpad._runClearing` computes them ON-CHAIN from the public
/// revealed book by a permutation-checked (no-drop/no-insert) descending walk +
/// a marginal fill — the rung-1 REPLAYABLE mechanism whose fairness is proved in
/// Lean (`Market/Optimality.lean:130 uniform_price_no_arbitrage`,
/// `uniform_price_envy_free`). Anyone re-derives them from public reveals. This
/// attestor GATES that on-chain result; it is not its source. So a corrupt
/// binder CANNOT misprice a launch — it can only refuse to attest (a liveness
/// fault → the launch stalls into the timeout-refund backstop,
/// `DreggLaunchpad.reclaimEscrow`), exactly like a withholding committee.
///
/// ## Trust (honest, and it is the whole residual)
///
///  - VERIFIED (real BN254 pairing, on-chain): a conserved dregg transition
///    reaching `final_root` EXISTS on the pinned instance, and the proof is
///    bound to THIS launch's committed params (`scheduleCommit`) and cannot be
///    replayed onto another launch, attestor, or chain.
///  - REPLAYABLE (pure on-chain function of public data): the clearing price /
///    fills / book commitment.
///  - TRUSTED (named, not proved): that the bound dregg transition IS this
///    launch's clearing. The binder asserts it; the circuit does not carry it.
///    CLOSING this needs the clearing tuple committed INSIDE the proof's public
///    statement — i.e. new statement lanes (launch id + clearing commit) in the
///    gnark `SettlementCircuit`, or a Poseidon2 inclusion of the tuple under
///    `final_root` verified on-chain. Both are a CIRCUIT/STATEMENT change, not
///    wiring, and are NOT done here.
///  - DEMO-TRUST: the registry's epoch-0 VK is a SINGLE-PARTY DEV ceremony
///    (toxic-waste-known, `chain/DEPLOYMENTS.md`) — whoever ran it could forge a
///    proof. This is a demonstration of the interface end-to-end, NOT production
///    trust, until the MPC ceremony (ember-gated) replaces the epoch-0 VK. That
///    swap is an `advanceEpoch` on the registry; this contract is unchanged.
///
/// The launchpad pins the `IClearingAttestor` SEAM, never an arm: a deployment
/// picks this (proof), `CommitteeAttestor` (signatures), `ConjunctiveAttestor`
/// (both must attest), or `address(0)` (rung-1 REPLAYABLE only).
contract DreggProofAttestor is IClearingAttestor {
    /// Domain tag: binds a binding/digest to THIS attestor kind + version, so it
    /// cannot be replayed against a different attestor or scheme.
    bytes32 public constant DOMAIN = keccak256("DreggProofAttestor.v1");

    /// The OCIP socket — the VK-rotation-absorbing entry point. We never see a
    /// verifying key, an epoch, or the pairing.
    IDreggVerifier public immutable socket;

    /// The launchpad whose launches this attestor serves. Read-only here: we ask
    /// it for a launch's committed `scheduleCommit` so a binding cannot be made
    /// against params the launch never committed.
    DreggLaunchpad public immutable launchpad;

    /// The party authorized to BIND a dregg transition to a launch (the dregg
    /// instance operator / clearing runner). Trusted for the LINK only — never
    /// for the price, and it cannot forge a proof.
    address public immutable binder;

    /// The genesis anchor of the ONE dregg instance this attestor trusts. A
    /// statement about a foreign dregg chain is refused before the pairing.
    uint32[8] private _trustedAnchor;

    /// The dregg transition bound to a launch. One-shot: set once, never
    /// replaced, so the binder picks ONE transition per launch and can never
    /// swap it after seeing the clearing.
    struct Binding {
        bytes32 statementDigest; // the exact 25-lane statement that may attest
        bytes32 scheduleCommit; // the launch's committed params at bind time
        uint256 saleSupply; // the sale supply those params disclose
        bool set;
    }

    mapping(uint256 => Binding) private _bindings;

    error NotBinder(address caller);
    error AlreadyBound(uint256 launchId);
    error NoSuchLaunch(uint256 launchId);
    error ScheduleMismatch(uint256 launchId);
    error UntrustedDreggInstance(bytes32 attestedGenesis, bytes32 trustedAnchor);
    error SocketHasNoCode(address socket);
    error LaunchpadHasNoCode(address launchpad);
    error ZeroBinder();

    event LaunchBound(
        uint256 indexed launchId,
        bytes32 indexed statementDigest,
        bytes32 scheduleCommit,
        uint256 saleSupply
    );

    /// @param socket_        the OCIP socket wrapping the VK-epoch registry.
    /// @param launchpad_     the launchpad served (read for `scheduleCommit`).
    /// @param trustedAnchor_ the genesis root of the dregg instance trusted.
    /// @param binder_        the party authorized to bind transitions to launches.
    constructor(
        IDreggVerifier socket_,
        DreggLaunchpad launchpad_,
        uint32[8] memory trustedAnchor_,
        address binder_
    ) {
        // Fail closed: a codeless dependency would make the staticcalls below
        // "succeed" and could accept anything (the census-flagged pattern the
        // socket and settlement contracts both refuse).
        if (address(socket_).code.length == 0) revert SocketHasNoCode(address(socket_));
        if (address(launchpad_).code.length == 0) revert LaunchpadHasNoCode(address(launchpad_));
        if (binder_ == address(0)) revert ZeroBinder();
        socket = socket_;
        launchpad = launchpad_;
        _trustedAnchor = trustedAnchor_;
        binder = binder_;
    }

    function trustedAnchor() external view returns (uint32[8] memory) {
        return _trustedAnchor;
    }

    function bindingOf(uint256 launchId) external view returns (Binding memory) {
        return _bindings[launchId];
    }

    /// The VK epoch a fresh attestation is checked against (the registry's
    /// current epoch — advanced by the registry, never pinned here).
    function currentEpoch() external view returns (uint256) {
        return socket.currentEpoch();
    }

    // ─── The launch binding (the anti-replay tooth) ─────────────────────────────

    /// @notice The domain-separated digest of a dregg statement AS BOUND TO THIS
    ///         ATTESTOR. Binds chainId + this attestor's address + all 25 lanes,
    ///         so a binding is non-replayable across chains and attestors.
    function statementDigest(DreggAttestation.Statement memory s) public view returns (bytes32) {
        return keccak256(
            abi.encode(
                DOMAIN, block.chainid, address(this), s.genesisRoot, s.finalRoot, s.numTurns, s.chainDigest
            )
        );
    }

    /// @notice BIND one dregg transition to one launch — the assertion "this
    ///         transition is launch `launchId`'s clearing." Callable once per
    ///         launch, by the binder only.
    ///
    ///         Two on-chain checks make the binding non-forgeable in the ways
    ///         that matter:
    ///           1. `schedule` must be EXACTLY the launch's committed params
    ///              (`DreggLaunchpad.checkSchedule` — keccak against the
    ///              on-chain `scheduleCommit`). So the binder cannot bind a
    ///              launch under invented params, and the `saleSupply` recorded
    ///              here is the DISCLOSED one, not the binder's claim.
    ///           2. the statement's `genesisRoot` must be the trusted dregg
    ///              instance's anchor — a proof about a foreign dregg chain can
    ///              never be bound.
    ///
    ///         What it does NOT check (and cannot): that the transition really
    ///         IS this launch's clearing. That is the named trusted link.
    ///
    ///         Binding a statement with no valid proof is a LIVENESS fault, not
    ///         a theft: `attestClearing` then returns false forever, the launch
    ///         never reaches `Cleared`, and every bidder reclaims escrow through
    ///         `DreggLaunchpad.reclaimEscrow`.
    function bindLaunch(
        uint256 launchId,
        DreggLaunchpad.Schedule calldata schedule,
        DreggAttestation.Statement calldata statement
    ) external {
        if (msg.sender != binder) revert NotBinder(msg.sender);
        if (_bindings[launchId].set) revert AlreadyBound(launchId);

        bytes32 sc = launchpad.scheduleCommitOf(launchId);
        if (sc == bytes32(0)) revert NoSuchLaunch(launchId);
        // (1) the disclosed params must be the launch's COMMITTED params.
        if (!launchpad.checkSchedule(launchId, schedule)) revert ScheduleMismatch(launchId);

        // (2) the statement must be about the dregg instance we trust.
        bytes32 attestedGenesis = DreggAttestation.packLanes(statement.genesisRoot);
        bytes32 anchor = DreggAttestation.packLanes(_trustedAnchor);
        if (attestedGenesis != anchor) revert UntrustedDreggInstance(attestedGenesis, anchor);

        bytes32 digest = statementDigest(statement);
        _bindings[launchId] =
            Binding({statementDigest: digest, scheduleCommit: sc, saleSupply: schedule.saleSupply, set: true});

        emit LaunchBound(launchId, digest, sc, schedule.saleSupply);
    }

    // ─── The attestor seam (view, per IClearingAttestor) ────────────────────────

    /// @notice True iff a REAL dregg proof, BOUND TO THIS LAUNCH, verifies
    ///         on-chain through the socket against the registry's current VK
    ///         epoch.
    ///
    ///         `proof` is `abi.encode(DreggAttestation.Proof, DreggAttestation.Statement)`.
    ///
    ///         Every arm returns FALSE rather than reverting (mirroring
    ///         `CommitteeAttestor`), so a bad attestation leaves the launch in
    ///         its pre-final, refundable state via the launchpad's typed
    ///         `ClearingNotAttested` — it never bricks the launch:
    ///           - no binding for this launch                    → false
    ///           - the launch's params changed since binding     → false
    ///           - `saleSupply` != the bound disclosed supply    → false
    ///           - the statement is not THE bound statement      → false  ⚑ the
    ///             launch binding: a proof bound to launch A presented for
    ///             launch B has a different digest and cannot attest.
    ///           - a foreign dregg instance                      → false
    ///           - a forged/tampered proof (pairing fails)       → false
    ///           - a malformed `proof` blob / ill-formed lanes   → false
    ///
    ///         ⚑ `clearingPrice` and `bookCommit` are intentionally NOT bound
    ///         here, and this is the honest residual, not an oversight: the
    ///         25-lane dregg statement has no lane to carry them, so binding
    ///         them would be a lie dressed as a check. Their correctness comes
    ///         from `_runClearing` computing them on-chain from the public book
    ///         (rung-1 REPLAYABLE, the Lean-proved uniform-price mechanism) —
    ///         NOT from this proof. `saleSupply` IS bound, because it is a
    ///         disclosed field of the committed `Schedule`.
    function attestClearing(
        uint256 launchId,
        uint256 saleSupply,
        uint256, /* clearingPrice — see the note above: not carried by the statement */
        bytes32, /* bookCommit    — see the note above: not carried by the statement */
        bytes calldata proof
    ) external view returns (bool) {
        Binding memory bnd = _bindings[launchId];
        if (!bnd.set) return false;

        // The launch's committed params must not have moved under the binding.
        if (launchpad.scheduleCommitOf(launchId) != bnd.scheduleCommit) return false;
        // The supply being cleared must be the disclosed, committed supply.
        if (saleSupply != bnd.saleSupply) return false;

        // A malformed blob decodes to nothing → not an attestation → false.
        DreggAttestation.Proof memory p;
        DreggAttestation.Statement memory s;
        try this.decodeAttestation(proof) returns (
            DreggAttestation.Proof memory p_, DreggAttestation.Statement memory s_
        ) {
            p = p_;
            s = s_;
        } catch {
            return false;
        }

        // ⚑ THE LAUNCH BINDING: only the statement bound to THIS launch attests.
        // Load-bearing, mutation-canaried: deleting this line makes a genuine
        // proof for launch A attest launch B (`test_WrongLaunchProofIsRefused`
        // is the canary and goes RED).
        if (statementDigest(s) != bnd.statementDigest) return false;

        // WHICH dregg — refuse a foreign instance before the pairing.
        if (DreggAttestation.packLanes(s.genesisRoot) != DreggAttestation.packLanes(_trustedAnchor)) {
            return false;
        }

        // IS IT VALID — the real BN254 pairing, current VK epoch, through the
        // socket. `verifyStatement` reverts on a non-canonical lane (ill-formed,
        // not a forgery); we stay fail-closed and report false either way.
        try socket.verifyStatement(p, s) returns (bool ok) {
            return ok;
        } catch {
            return false;
        }
    }

    /// External so `attestClearing` can `try/catch` a malformed `abi.decode`
    /// without reverting the view (keeping it honest: malformed → false).
    function decodeAttestation(bytes calldata proof)
        external
        pure
        returns (DreggAttestation.Proof memory, DreggAttestation.Statement memory)
    {
        return abi.decode(proof, (DreggAttestation.Proof, DreggAttestation.Statement));
    }

    /// Helper for off-chain callers / the Rust binder: the exact `proof` blob
    /// `finalizeClearing` expects for a proof-attested launch.
    function encodeAttestation(
        DreggAttestation.Proof calldata p,
        DreggAttestation.Statement calldata s
    ) external pure returns (bytes memory) {
        return abi.encode(p, s);
    }
}

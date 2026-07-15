// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title IClearingAttestor
/// @notice OPTIONAL dregg-clearing-proof attestor for a launch's uniform-price
///         clearing. If a launch pins an attestor, `finalizeClearing` requires
///         it to attest that the (saleSupply, clearingPrice, bookCommit) the
///         contract COMPUTED on-chain is the dregg fair clearing.
///
/// ## The two fairness rungs (graded honestly, `DREGG-LAUNCHPAD-DESIGN.md` §2.2)
///
/// 1. REPLAYABLE (always on): the launchpad computes the uniform clearing price
///    on-chain from the revealed book by a permutation-checked descending sort
///    (no-drop / no-insert, mirroring `Market/Aggregation.lean`) + a marginal-fill
///    walk. Anyone re-derives it from public reveals. This faithfully IMPLEMENTS
///    the mechanism whose fairness is PROVED in Lean:
///      - `Market/Optimality.lean:130 uniform_price_no_arbitrage` (every leg
///        value-neutral at ONE price),
///      - `uniform_price_envy_free` (same-direction bidders clear at the same
///        rate) — i.e. every winner pays the SAME clearing price.
///
/// 2. PROVED (when an attestor is pinned): a genuine dregg Groth16(BN254) proof
///    verifies on-chain through the OCIP socket (`contracts/socket/DreggVerifier.sol`)
///    before the clearing is accepted — the SAME settlement pattern as
///    `DreggSettlement.settle` (verify a real dregg proof through the VK-epoch
///    registry). This is the anti-fake tooth: the gate is not a signature, it is
///    a verified proof.
///
/// ## Honest scope — what rung 2 does and does NOT attest today
///
/// BUILT: `DreggProofAttestor` is a concrete arm that verifies a REAL dregg wrap
/// proof through the real socket + registry (`DreggLaunchpadProofAttestor.t.sol`,
/// both polarities, against the real `settlement_groth16.json` fixture). It is no
/// longer a mock and no longer a named weld.
///
/// ⚑ But read `DreggProofAttestor.sol` §Trust before reading "PROVED" as more
/// than it is. The dregg wrap statement is 25 pinned lanes — `genesis_root[8] ·
/// final_root[8] · num_turns · chain_digest[8]`. It has NO lane for a launch id,
/// a clearing price, or a book commitment. So the proof attests *a conserved,
/// rule-abiding dregg state transition on the pinned instance* — NOT "and that
/// transition was this launch's clearing at price p*". `DreggProofAttestor` binds
/// the transition to the launch by an on-chain, one-shot registration tied to the
/// launch's committed `scheduleCommit` (so a proof for one launch can never
/// attest another), and that BINDING is a trusted assertion by the binder, not a
/// theorem.
///
/// What this costs is nothing, because rung 1 already carries the price: the
/// clearing price / fills / book commit are computed ON-CHAIN by `_runClearing`
/// from the public revealed book, so no attestor is their source — an attestor
/// only GATES them. A corrupt binder or committee therefore cannot misprice a
/// launch; it can only withhold (a liveness fault → the timeout-refund backstop).
///
/// The REMAINING weld is the STATEMENT, and it is circuit work, not wiring: for a
/// proof to attest the clearing itself, the clearing tuple must ride INSIDE the
/// proof's public statement — either by folding clearing-bodied turns into the
/// apex so the generic transition contains the clearing, or by giving
/// `circuit-prove/src/cert_f_air.rs` an apex → shrink → Groth16 path and a
/// statement shape the socket accepts. Neither exists today; today's real fixture
/// folds `IncrementNonce` turns.
///
/// A launch may pin: nothing (rung 1 REPLAYABLE only), `CommitteeAttestor`
/// (k-of-n signatures), `DreggProofAttestor` (a verified proof), or
/// `ConjunctiveAttestor` (both must attest). The launchpad pins this SEAM and
/// never an arm.
interface IClearingAttestor {
    /// @param launchId     the launch whose clearing is being attested.
    /// @param saleSupply   the disclosed number of tokens sold in the raise.
    /// @param clearingPrice the uniform price the launchpad computed on-chain.
    /// @param bookCommit   a commitment to the revealed book the clearing ran over
    ///                     (keccak over the revealed (bidder, price, qty) tuples).
    /// @param proof        the attestation blob — ARM-DEFINED and opaque here
    ///                     (`CommitteeAttestor`: `abi.encode(bytes[] signatures)`;
    ///                     `DreggProofAttestor`: `abi.encode(Proof, Statement)`;
    ///                     `ConjunctiveAttestor`: `abi.encode(bytes[] armProofs)`).
    /// @return true iff this arm attests the clearing. ⚑ HOW MUCH of the tuple an
    ///         arm can actually BIND is arm-specific and is not uniform: the
    ///         committee signs the whole tuple; the proof arm binds `launchId` +
    ///         `saleSupply` (via the committed schedule) but CANNOT bind
    ///         `clearingPrice`/`bookCommit`, because the dregg statement has no
    ///         lane for them. Read the arm's own §Trust before reading a `true`
    ///         here as "the price is proved" — it is not, and it does not need to
    ///         be: rung 1 computes the price on-chain from the public book.
    ///         Implementations MUST return false (never revert) on a bad
    ///         attestation, so the launchpad's typed `ClearingNotAttested` is the
    ///         single refusal reason and a launch stays refundable.
    function attestClearing(
        uint256 launchId,
        uint256 saleSupply,
        uint256 clearingPrice,
        bytes32 bookCommit,
        bytes calldata proof
    ) external view returns (bool);
}

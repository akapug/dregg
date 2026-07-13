//! **Trustless proof-of-LOCK** — the honest successor to the M-of-N oracle-attested
//! Solana asset lock (`docs/deos/INTERCHAIN-MODEL.md`: "Solana lock/unlock =
//! oracle-attested"). This drives the PRODUCTION, trustless entry
//! [`verify_lock_proof_consensus_anchored`] against a bank-state-provenance cluster
//! fixture — the SAME ≥2/3-stake + accounts-inclusion + governance-pinned-anchor
//! machinery the inbound holdings proof
//! ([`dregg_bridge::solana_holdings::prove_holding_consensus_anchored`]) uses,
//! pointed at the bridge's *vault* account (carrying a lock record) instead of the
//! holder's own token account.
//!
//! What a pass PROVES (not attests): at a finalized Solana slot, ≥2/3 of the
//! epoch's effective stake — derived from bank state and trusted only back to a
//! governance-pinned [`WeakSubjectivityAnchor`], each counted vote signed by the
//! vote account's on-chain authorized voter — voted a bank hash whose committed
//! accounts hash includes the bridge vault account holding `amount` of `$DREGG`
//! under the lock program. The lock is CONSENSUS-VERIFIED (proof-carrying),
//! replacing the oracle's word.
//!
//! Both polarities run by default (no `SOLANA_*` env gate):
//! - (a) a genuine ≥2/3-stake anchored lock proof verifies to
//!   [`LockProofTrust::ConsensusVerified`] and mirror-mints conserved credit;
//! - (b) the SAME proof with its votes truncated below 2/3 is refused
//!   ([`LockProofError::StakeBelowThreshold`]) — the stake teeth;
//! - (c) an imposter-signed vote (not the on-chain authorized voter) is dropped,
//!   pushing the tally below 2/3 (refused);
//! - (d) a forged (wrong-root) weak-subjectivity anchor is refused
//!   ([`LockProofError::Provenance`] — the derived table does not match the pin);
//! - (e) a proof escrowing into a FOREIGN vault (not the bridge's) cannot mint
//!   ([`LockProofError::ClaimMismatch`]) even when its consensus is internally
//!   valid — proving the lock is in THE bridge's program account, not merely
//!   somewhere on Solana;
//! - (f) the structure-only [`verify_lock_proof`] over the SAME proof reaches only
//!   [`LockProofTrust::StructureOnly`] (the honesty dial — no consensus checked).
//!
//! Honest scope: the consensus check here is OFF-CIRCUIT (re-executor-grade, not a
//! succinct AIR — the Option-B wrapper is `SolanaConsensusStatement`, named-not-built)
//! and the live snapshot/geyser vote feed is pending (the fixture stands in for it).
//! This is the exact accounting `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md` names.

use dregg_bridge::midnight::EpochKey;
use dregg_bridge::solana_mirror::{MirrorConfig, MirrorState};
use dregg_bridge::solana_provenance::{ProvenanceError, WeakSubjectivityAnchor};
use dregg_bridge::solana_trustless::{
    LockProofError, LockProofTrust, ProofMintError, fixtures, verify_lock_proof,
    verify_lock_proof_consensus_anchored,
};
use dregg_turn::action::Effect;
use dregg_types::CellId;

/// The configured `$DREGG` SPL mint the lock verifier binds to.
const DREGG_MINT: [u8; 32] = [0xABu8; 32];
/// The mirror `AssetId`.
const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];
/// The bridge lock program that owns the vault account.
const LOCK_PROGRAM: [u8; 32] = [0x07u8; 32];
/// The canonical bridge vault account (the escrow the lock must land in).
const VAULT: [u8; 32] = [0x22u8; 32];

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

/// The bridge mirror config: the vault + lock program the fixture escrows into,
/// mint bounds, and (by default) no pinned anchor.
fn config() -> MirrorConfig {
    MirrorConfig {
        spl_mint: DREGG_MINT,
        asset: MIRROR_ASSET,
        oracle_keys: Vec::<EpochKey>::new(), // unused by the trustless anchored path
        min_amount: 1,
        max_amount: 1_000_000,
        vault_account: VAULT,
        lock_program: LOCK_PROGRAM,
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    }
}

/// Three validators, 400/400/200 stake (total 1000): all three voting = 100% of
/// stake (clears 2/3); a single 400-stake validator alone (40%) does not.
const CLUSTER: [(u8, u64); 3] = [(11, 400), (12, 400), (13, 200)];

// ---- (a) accept: a genuine ≥2/3-stake anchored lock is CONSENSUS-VERIFIED -----

#[test]
fn anchored_lock_verifies_and_mints_consensus_verified() {
    let cfg = config();
    let (proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );

    // The ONLY trusted input is the governance-pinned weak-subjectivity anchor;
    // the stake table is derived from bank state INSIDE the call.
    let trust = verify_lock_proof_consensus_anchored(
        &proof,
        &cfg.spl_mint,
        cfg.min_amount,
        cfg.max_amount,
        &anchor,
        true, // require PoH against the bounded-anchor policy
        Some(&policy),
    )
    .expect("a genuine anchored lock proof verifies trustlessly");
    assert_eq!(trust, LockProofTrust::ConsensusVerified);

    // And it drives the value-bearing mint end-to-end (conserved credit).
    let mut mirror = MirrorState::new(config());
    let (mint, mint_trust) = mirror
        .mint_against_lock_proof_anchored(&proof, &anchor, true, Some(&policy))
        .expect("consensus-verified lock mirror-mints");
    assert_eq!(mint_trust, LockProofTrust::ConsensusVerified);
    assert_eq!(mint.amount, 500);
    match mint.effect {
        Effect::Mint { target, amount, .. } => {
            assert_eq!(target, cid(1));
            assert_eq!(amount, 500);
        }
        ref other => panic!("expected Effect::Mint, got {other:?}"),
    }
    assert_eq!(mirror.live_supply, 500);
    assert_eq!(mirror.currently_locked, 500);
    assert!(mirror.invariant_holds());
}

// ---- (b) reject: below 2/3 stake is refused (the stake teeth) -----------------

#[test]
fn anchored_lock_below_two_thirds_is_refused() {
    let cfg = config();
    let (mut proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );
    // Keep only the first validator's vote: 400/1000 = 40% of real stake.
    proof.consensus.votes.truncate(1);

    let err = verify_lock_proof_consensus_anchored(
        &proof,
        &cfg.spl_mint,
        cfg.min_amount,
        cfg.max_amount,
        &anchor,
        false,
        Some(&policy),
    )
    .unwrap_err();
    assert_eq!(
        err,
        LockProofError::StakeBelowThreshold {
            voted: 400,
            total: 1000
        }
    );

    // And nothing mints.
    let mut mirror = MirrorState::new(config());
    assert!(matches!(
        mirror
            .mint_against_lock_proof_anchored(&proof, &anchor, false, Some(&policy))
            .unwrap_err(),
        ProofMintError::Proof(LockProofError::StakeBelowThreshold { .. })
    ));
    assert_eq!(mirror.live_supply, 0);
    assert_eq!(mirror.currently_locked, 0);
    assert!(mirror.invariant_holds());
}

// ---- (c) reject: an imposter-signed vote (not the authorized voter) drops out --

#[test]
fn anchored_lock_unauthorized_voter_is_refused() {
    let cfg = config();
    let (mut proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );
    // Re-sign validator 0's vote with an imposter key: its stake (400) no longer
    // counts, leaving 400+200 = 600/1000 < 2/3.
    let imposter = dregg_bridge::solana_provenance::fixtures::sk(99);
    let va0 = [11u8 ^ 0xA5; 32]; // the fixture's va derivation for seed 11
    proof.consensus.votes[0] = dregg_bridge::solana_provenance::fixtures::tower_sync_tx(
        &imposter,
        &va0,
        proof.consensus.slot,
        proof.consensus.bank_hash,
    );
    assert_eq!(
        verify_lock_proof_consensus_anchored(
            &proof,
            &cfg.spl_mint,
            cfg.min_amount,
            cfg.max_amount,
            &anchor,
            false,
            Some(&policy),
        )
        .unwrap_err(),
        LockProofError::StakeBelowThreshold {
            voted: 600,
            total: 1000
        }
    );
}

// ---- (d) reject: a forged (wrong-root) weak-subjectivity anchor ---------------

#[test]
fn anchored_lock_wrong_anchor_root_is_refused() {
    let cfg = config();
    let (proof, _anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );
    // An attacker supplies a DIFFERENT anchor root than the genuine distribution
    // reconstructs to (e.g. their own 100%-self-stake table).
    let forged = WeakSubjectivityAnchor {
        epoch: proof.consensus.epoch,
        stake_table_root: [0xDEu8; 32],
    };
    let err = verify_lock_proof_consensus_anchored(
        &proof,
        &cfg.spl_mint,
        cfg.min_amount,
        cfg.max_amount,
        &forged,
        false,
        Some(&policy),
    )
    .unwrap_err();
    assert!(matches!(
        err,
        LockProofError::Provenance(ProvenanceError::AnchorRootMismatch { .. })
    ));
}

// ---- (e) reject: a lock escrowed into a FOREIGN vault cannot mint --------------

#[test]
fn anchored_lock_into_foreign_vault_cannot_mint() {
    // The proof's consensus + inclusion are internally valid, but the lock record
    // sits in vault [0x22;32] while the bridge is configured to escrow into a
    // DIFFERENT canonical vault — so it did not lock into OUR bridge. Without this
    // gate an attacker mints having escrowed nothing into the bridge.
    let (proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );
    let mut cfg = config();
    cfg.vault_account = [0x99u8; 32]; // not the fixture's vault
    let mut mirror = MirrorState::new(cfg);
    assert_eq!(
        mirror
            .mint_against_lock_proof_anchored(&proof, &anchor, false, Some(&policy))
            .unwrap_err(),
        ProofMintError::Proof(LockProofError::ClaimMismatch)
    );
    assert_eq!(mirror.live_supply, 0);
    assert_eq!(mirror.currently_locked, 0);
    assert!(mirror.invariant_holds());
}

// ---- (f) the honesty dial: structure-only is NOT consensus --------------------

#[test]
fn structure_only_verify_is_not_consensus_verified() {
    let cfg = config();
    let (proof, _anchor, _policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );
    // The SAME proof through the structure-only entry: checks structure + binding
    // but runs NO consensus — it can NEVER reach ConsensusVerified.
    let trust = verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount)
        .expect("structure + binding are well-formed");
    assert_eq!(trust, LockProofTrust::StructureOnly);
    assert_ne!(trust, LockProofTrust::ConsensusVerified);
}

// ---- pinned anchor: an attacker's anchor is refused before consensus ----------

#[test]
fn anchored_mint_pins_the_governance_anchor() {
    let (proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );

    let mut cfg = config();
    cfg.pinned_anchor_epoch = Some(anchor.epoch);
    cfg.pinned_anchor_root = Some(anchor.stake_table_root);

    // A different (attacker-chosen) anchor: same epoch, forged root → refused
    // before any consensus check runs.
    let forged = WeakSubjectivityAnchor {
        epoch: anchor.epoch,
        stake_table_root: [0xABu8; 32],
    };
    let mut m1 = MirrorState::new(cfg.clone());
    assert_eq!(
        m1.mint_against_lock_proof_anchored(&proof, &forged, true, Some(&policy))
            .unwrap_err(),
        ProofMintError::Proof(LockProofError::AnchorNotPinned)
    );
    assert_eq!(m1.live_supply, 0);

    // The genuine, governance-pinned anchor mints.
    let mut m2 = MirrorState::new(cfg);
    let (mint, trust) = m2
        .mint_against_lock_proof_anchored(&proof, &anchor, true, Some(&policy))
        .expect("pinned anchor mints");
    assert_eq!(trust, LockProofTrust::ConsensusVerified);
    assert_eq!(mint.amount, 500);
    assert!(m2.invariant_holds());
}

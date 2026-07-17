//! CHARACTERIZATION of a real gap (2026-07-17 4swarm/fic-apps): the poll's TALLY
//! board is NOT bound to the ballots. `record_tally(choice, new_tally)` writes an
//! arbitrary caller-supplied `new_tally` straight into the poll's `Monotonic`
//! tally slot, gated ONLY by `Signature` (the poll operator's own key) + the
//! `Monotonic` caveat (which merely forbids a DECREASE). Nothing on-ledger checks
//! that a tally increment corresponds to a real, unconsumed ballot's `VOTE` write.
//!
//! Consequence: the poll operator can post any tally >= the current one WITHOUT a
//! single ballot ever being cast. The README claims "monotone, **tamper-evident**
//! tallies — **enforced by the verified executor**", but tally INFLATION is neither
//! prevented nor on-ledger-evident. The `WriteOnce(VOTE)` tooth gives
//! one-vote-per-BALLOT-CELL, but that guarantee does NOT compose into
//! "the tally equals the count of cast ballots".
//!
//! The sibling app `collective-choice` fixed EXACTLY this class (see its
//! `tests.rs::forged_quorum_single_actor_inflating_a_tally_slot_is_refused`): its
//! quorum gate is an `AffineLe` weight-quorum PLUS a `CountGe` witness over the
//! DISTINCT approver set PLUS a one-vote nullifier. privacy-voting's tally has
//! none of those — the `record_tally` value is trusted bookkeeping.
//!
//! MISSING CAPABILITY (named, not faked): a ballot->tally binding — a nullifier /
//! `CountGe`-over-distinct-ballots gate so the executor refuses a tally increment
//! that is not backed by a fresh, unconsumed ballot's `VOTE` write. Until that
//! exists, the tally is operator-attested, not executor-enforced.
//!
//! This test pins the CURRENT (insecure) behavior. If a real ballot-binding fix
//! lands, this test SHOULD go red and force an update — that is the tooth working
//! in reverse (it makes the gap visible, so a fix cannot land silently).

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, field_from_u64};
use starbridge_privacy_voting::{TALLY_YES_SLOT, VOTE_YES, build_record_tally_action, seed_poll};

#[test]
fn poll_operator_forges_a_tally_with_zero_ballots_cast() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x9au8; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");

    // Open a poll. NO ballot is minted, NO `cast_vote` is ever submitted.
    seed_poll(&executor, "did the community approve X?");
    let poll = cclerk.cell_id();

    // The tally board starts empty.
    assert_eq!(
        executor.cell_state(poll).unwrap().fields[TALLY_YES_SLOT],
        field_from_u64(0),
        "genesis tally is zero"
    );

    // The poll operator posts an arbitrary YES tally of 1_000_000 with ZERO
    // ballots behind it. The executor accepts it: 1_000_000 >= 0 satisfies
    // Monotonic, and the Signature is the operator's own.
    let forged = build_record_tally_action(&cclerk, poll, VOTE_YES, 1_000_000);
    executor
        .submit_action(&cclerk, forged)
        .expect("THE GAP: an unbacked tally of 1,000,000 commits with no ballots");

    // The published board now reads a million YES votes that never happened.
    assert_eq!(
        executor.cell_state(poll).unwrap().fields[TALLY_YES_SLOT],
        field_from_u64(1_000_000),
        "THE GAP: the tally is inflated with no ballot->tally binding"
    );
}

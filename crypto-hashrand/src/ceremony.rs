//! The beacon CEREMONY — the commit round then the reveal round, driven as a
//! message-passing protocol over a [`Channel`], mirroring crypto-hermine's
//! Raccoon commit → reveal ceremony.
//!
//! Every party runs [`run_beacon_ceremony`] concurrently against the same
//! channel:
//!
//! 1. **Commit** — broadcast the hash commitment [`CommitMsg`] (`cmᵢ`, never
//!    `cᵢ`). The transport's round barrier freezes the COMPLETE commitment set
//!    before anyone can proceed.
//! 2. **Reveal** — broadcast [`RevealMsg`] (`cᵢ`), only reachable once every
//!    commitment is in. Each reveal is verified against the frozen commitment;
//!    an equivocating party (`cᵢ' ≠ committed`) is CAUGHT and NAMED
//!    ([`BeaconError::Equivocation`]).
//!
//! The output is the hash-combine over the verified reveals ([`beacon::combine`]);
//! every honest party assembles the SAME [`BeaconOutput`].
//!
//! # The commit-then-reveal boundary IS the round barrier
//!
//! A party obtains the commitment set only from [`Channel::recv_round`], which
//! completes only when every party's commitment is in — so a party cannot reveal
//! until every contribution is bound to its hash, and cannot rush a reveal into
//! the commit round ([`ChannelError::DuplicateSend`]). This is precisely what
//! makes the beacon unbiasable AND unpredictable: an adversary must commit
//! before seeing any honest reveal, and the honest reveal then moves the output.

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::beacon::{self, BeaconOutput, Commitment, Contribution};
use crate::channel::{Channel, ChannelError};

/// Round 1 broadcast: party `party`'s hash commitment `cmᵢ` (never `cᵢ`).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct CommitMsg {
    /// The committing party's 1-based index.
    pub party: u64,
    /// The commitment `cmᵢ = H("commit", i, cᵢ)`.
    pub cm: Commitment,
}

/// Round 2 broadcast: party `party`'s revealed contribution `cᵢ`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct RevealMsg {
    /// The revealing party's 1-based index.
    pub party: u64,
    /// The revealed contribution `cᵢ`.
    pub c: Contribution,
}

/// Why a beacon ceremony refused to complete.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BeaconError {
    /// The transport refused (round violation).
    Channel(ChannelError),
    /// Party `from` sent bytes that do not decode to the round's message type,
    /// or a message whose embedded party index contradicts the sender.
    BadMessage {
        /// The party whose message was rejected.
        from: u64,
    },
    /// Party `party` revealed a contribution that does NOT open the commitment
    /// it broadcast in round 1 — equivocation, caught by the commit-binding
    /// check. This is the rushing/bias defense's teeth.
    Equivocation {
        /// The equivocating party.
        party: u64,
    },
}

impl From<ChannelError> for BeaconError {
    fn from(e: ChannelError) -> Self {
        BeaconError::Channel(e)
    }
}

/// Serde-encode one round message for the wire.
pub(crate) fn encode<T: Serialize>(msg: &T) -> Vec<u8> {
    serde_json::to_vec(msg).expect("beacon messages serialize infallibly")
}

/// Decode party `from`'s round message, or reject it by name.
fn decode<T: DeserializeOwned>(from: u64, bytes: &[u8]) -> Result<T, BeaconError> {
    serde_json::from_slice(bytes).map_err(|_| BeaconError::BadMessage { from })
}

/// Run ONE party's side of the beacon: commit `cᵢ`, freeze the commitment set,
/// reveal `cᵢ`, verify every reveal against its commitment, and combine. All
/// `n = channel.parties()` parties run this concurrently against the same
/// channel; every honest party returns the SAME [`BeaconOutput`].
///
/// `c` is this party's local secret contribution (a party samples it from a
/// CSPRNG in deployment; the tests derive it deterministically so the ceremony
/// is a differential against the in-process [`beacon::combine`]).
pub fn run_beacon_ceremony<C: Channel>(
    channel: &mut C,
    c: &Contribution,
) -> Result<BeaconOutput, BeaconError> {
    let me = channel.me();

    // Round 1 (COMMIT): broadcast only the hash commitment cmᵢ.
    let cm = beacon::commit(me, c);
    channel.broadcast(encode(&CommitMsg { party: me, cm }))?;
    let round1 = channel.recv_round()?;

    // Freeze the complete commitment set (party → cm). Wire hygiene: the
    // embedded party index IS the sender.
    let mut commitments: Vec<(u64, Commitment)> = Vec::with_capacity(round1.len());
    for (from, bytes) in &round1 {
        let msg: CommitMsg = decode(*from, bytes)?;
        if msg.party != *from {
            return Err(BeaconError::BadMessage { from: *from });
        }
        commitments.push((msg.party, msg.cm));
    }

    // Round 2 (REVEAL): only reachable once every commitment is in.
    channel.broadcast(encode(&RevealMsg { party: me, c: *c }))?;
    let round2 = channel.recv_round()?;

    // Verify each reveal against the FROZEN commitment; equivocation is caught
    // and named. The verified reveals are the committed contribution multiset.
    let mut reveals: Vec<(u64, Contribution)> = Vec::with_capacity(round2.len());
    for ((from, bytes), (cparty, cm)) in round2.iter().zip(commitments.iter()) {
        let msg: RevealMsg = decode(*from, bytes)?;
        if msg.party != *from || msg.party != *cparty {
            return Err(BeaconError::BadMessage { from: *from });
        }
        if !beacon::verify_opening(msg.party, cm, &msg.c) {
            return Err(BeaconError::Equivocation { party: msg.party });
        }
        reveals.push((msg.party, msg.c));
    }

    Ok(beacon::combine(&reveals))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::beacon::derive_contribution;
    use crate::channel::LocalNetwork;
    use std::sync::Arc;

    const SEED: u64 = 0x00de_add0_b3ac;

    /// Drive one ceremony per party on its own thread (the transport's round
    /// barrier synchronizes them), collecting outputs in party order.
    fn run_parties<T, F>(net: &LocalNetwork, f: F) -> Vec<T>
    where
        T: Send + 'static,
        F: Fn(crate::channel::LocalChannel) -> T + Send + Sync + 'static,
    {
        let f = Arc::new(f);
        let handles: Vec<_> = net
            .channels()
            .into_iter()
            .map(|chan| {
                let f = Arc::clone(&f);
                std::thread::spawn(move || f(chan))
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("party thread"))
            .collect()
    }

    /// AGREEMENT: `n` parties run the commit → reveal beacon over the in-memory
    /// transport; every party assembles the SAME output, and it is exactly the
    /// in-process combine (a differential, not just self-green).
    #[test]
    fn beacon_agrees_across_parties() {
        const N: u64 = 5;
        let net = LocalNetwork::new(N).unwrap();
        let outputs = run_parties(&net, move |mut chan| {
            let c = derive_contribution(SEED, chan.me());
            run_beacon_ceremony(&mut chan, &c).expect("honest beacon completes")
        });

        assert_eq!(outputs.len(), N as usize);
        for out in &outputs[1..] {
            assert_eq!(out, &outputs[0], "all parties agree on the beacon output");
        }

        // Differential: the agreed output IS the combine over every party's
        // committed contribution.
        let reveals: Vec<(u64, Contribution)> =
            (1..=N).map(|i| (i, derive_contribution(SEED, i))).collect();
        assert_eq!(outputs[0], beacon::combine(&reveals));
    }

    /// UNBIASABILITY over the ceremony: fixing the honest party's contribution,
    /// an adversarial coalition running the SAME ceremony with DIFFERENT
    /// contributions cannot reproduce the honest-included output — the honest
    /// contribution is baked in and moves the beacon.
    #[test]
    fn ceremony_output_moves_with_honest_contribution() {
        const N: u64 = 4;
        // Run once with the honest party (party 1) contributing c1.
        let run = |honest_seed: u64, adv_seed: u64| -> BeaconOutput {
            let net = LocalNetwork::new(N).unwrap();
            let outs = run_parties(&net, move |mut chan| {
                let me = chan.me();
                // Party 1 honest; parties 2..N adversarial.
                let seed = if me == 1 { honest_seed } else { adv_seed };
                let c = derive_contribution(seed, me);
                run_beacon_ceremony(&mut chan, &c).expect("beacon completes")
            });
            outs[0]
        };

        let baseline = run(SEED, SEED);
        // Adversary changes ITS contributions: output changes, but…
        let adv_changed = run(SEED, SEED ^ 0xffff);
        assert_ne!(baseline, adv_changed);
        // …with the SAME honest contribution the beacon is well-defined; and a
        // DIFFERENT honest contribution changes it too — the honest slot is
        // injective, so no coalition below threshold pins the output.
        let honest_changed = run(SEED ^ 0x1, SEED);
        assert_ne!(baseline, honest_changed);
    }

    /// COMMIT-BINDING / equivocation teeth over the ceremony: a party whose
    /// round-2 reveal does not open its round-1 commitment is CAUGHT and NAMED.
    /// Driven single-threaded so the refusal is observable.
    #[test]
    fn ceremony_catches_equivocation() {
        const N: u64 = 3;
        let net = LocalNetwork::new(N).unwrap();
        let mut chans = net.channels();

        // Everyone commits honestly to cᵢ.
        let contribs: Vec<Contribution> = (1..=N).map(|i| derive_contribution(SEED, i)).collect();
        for (idx, chan) in chans.iter_mut().enumerate() {
            let party = idx as u64 + 1;
            chan.broadcast(encode(&CommitMsg {
                party,
                cm: beacon::commit(party, &contribs[idx]),
            }))
            .unwrap();
        }
        // Freeze the commitment round for every endpoint.
        for chan in chans.iter_mut() {
            let r1 = chan.recv_round().unwrap();
            assert_eq!(r1.len(), N as usize);
        }

        // Parties 1 and 2 reveal honestly; party 3 EQUIVOCATES (reveals a
        // different contribution than it committed).
        chans[0]
            .broadcast(encode(&RevealMsg {
                party: 1,
                c: contribs[0],
            }))
            .unwrap();
        chans[1]
            .broadcast(encode(&RevealMsg {
                party: 2,
                c: contribs[1],
            }))
            .unwrap();
        let forged = derive_contribution(0xdead, 3);
        assert_ne!(forged, contribs[2]);
        chans[2]
            .broadcast(encode(&RevealMsg {
                party: 3,
                c: forged,
            }))
            .unwrap();

        // An honest party (party 1) collects the reveals and CATCHES party 3's
        // equivocation against the frozen commitment set.
        let r2 = chans[0].recv_round().unwrap();
        let commitments: Vec<(u64, Commitment)> = (1..=N)
            .map(|i| (i, beacon::commit(i, &contribs[(i - 1) as usize])))
            .collect();
        let mut caught = None;
        for ((from, bytes), (cparty, cm)) in r2.iter().zip(commitments.iter()) {
            let msg: RevealMsg = serde_json::from_slice(bytes).unwrap();
            assert_eq!(msg.party, *from);
            assert_eq!(msg.party, *cparty);
            if !beacon::verify_opening(msg.party, cm, &msg.c) {
                caught = Some(msg.party);
            }
        }
        assert_eq!(caught, Some(3), "the equivocating party is named");
    }

    /// THE round-structure tooth: a party cannot reveal before every commitment
    /// is in, and cannot rush its reveal into the commit round.
    #[test]
    fn commit_reveal_barrier() {
        const N: u64 = 3;
        let net = LocalNetwork::new(N).unwrap();
        let mut chans = net.channels();
        let contribs: Vec<Contribution> = (1..=N).map(|i| derive_contribution(SEED, i)).collect();

        // Parties 1 and 2 commit; party 3 has not.
        chans[0]
            .broadcast(encode(&CommitMsg {
                party: 1,
                cm: beacon::commit(1, &contribs[0]),
            }))
            .unwrap();
        chans[1]
            .broadcast(encode(&CommitMsg {
                party: 2,
                cm: beacon::commit(2, &contribs[1]),
            }))
            .unwrap();

        // Party 1 cannot obtain the commitment set (round incomplete)…
        assert_eq!(
            chans[0].try_recv_round().unwrap_err(),
            ChannelError::RoundIncomplete
        );
        // …nor rush its reveal INTO the commit round: one message per party.
        assert_eq!(
            chans[0]
                .broadcast(encode(&RevealMsg {
                    party: 1,
                    c: contribs[0]
                }))
                .unwrap_err(),
            ChannelError::DuplicateSend
        );

        // Party 3 commits; the barrier opens; only NOW is the reveal sendable —
        // with every contribution already bound to its hash commitment.
        chans[2]
            .broadcast(encode(&CommitMsg {
                party: 3,
                cm: beacon::commit(3, &contribs[2]),
            }))
            .unwrap();
        let round1 = chans[0].try_recv_round().unwrap();
        assert_eq!(round1.len(), 3);
        chans[0]
            .broadcast(encode(&RevealMsg {
                party: 1,
                c: contribs[0],
            }))
            .unwrap();
    }
}

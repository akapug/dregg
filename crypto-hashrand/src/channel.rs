//! The synchronous broadcast-round transport — the pairwise-secure-channel
//! substrate the beacon ceremony drives against, mirroring crypto-hermine's
//! ceremony transport.
//!
//! A HashRand-style beacon assumes pairwise secure channels and a per-round
//! barrier. This module gives that seam ([`Channel`]) plus an in-memory
//! reference network ([`LocalNetwork`]) for `n` parties: broadcasts land in
//! shared per-round slots, and [`Channel::recv_round`] completes a round only
//! when EVERY party has broadcast — THE ROUND BARRIER that makes commit-then-
//! reveal meaningful (a party cannot reveal until every commitment is in, and
//! cannot inject a second message into the commit round —
//! [`ChannelError::DuplicateSend`]).
//!
//! Messages are opaque bytes at this seam (the ceremony serde-encodes its round
//! messages), so a real network transport can implement the same trait without
//! knowing the protocol.

use std::sync::{Arc, Condvar, Mutex};

/// Why a transport operation refused.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ChannelError {
    /// The current round is not complete — some party has not broadcast yet
    /// (surfaced by the non-blocking [`LocalChannel::try_recv_round`]).
    RoundIncomplete,
    /// This party already broadcast in the current round: one message per party
    /// per round — the tooth that keeps a rushed second message (an early
    /// reveal) out of the commit round.
    DuplicateSend,
}

/// A synchronous broadcast-round transport, one endpoint per party.
///
/// * parties are `1..=parties()`, this endpoint is party [`Channel::me`];
/// * [`Channel::broadcast`] sends this party's ONE message for the current
///   round (a second send is [`ChannelError::DuplicateSend`]);
/// * [`Channel::recv_round`] yields ALL parties' messages for the current round
///   — `(party, bytes)` in ascending party order, self included — and advances
///   to the next round, completing only when every party has broadcast.
pub trait Channel {
    /// This endpoint's 1-based party index.
    fn me(&self) -> u64;
    /// The number of parties on the channel.
    fn parties(&self) -> u64;
    /// Broadcast this party's message for the current round.
    fn broadcast(&mut self, bytes: Vec<u8>) -> Result<(), ChannelError>;
    /// Receive the complete current round (waiting if necessary) and advance.
    fn recv_round(&mut self) -> Result<Vec<(u64, Vec<u8>)>, ChannelError>;
}

/// The shared state behind a [`LocalNetwork`]: `rounds[r][p-1]` is party `p`'s
/// broadcast for round `r`.
struct NetInner {
    n: usize,
    rounds: Vec<Vec<Option<Vec<u8>>>>,
}

impl NetInner {
    fn ensure_round(&mut self, round: usize) {
        while self.rounds.len() <= round {
            self.rounds.push(vec![None; self.n]);
        }
    }

    fn round_complete(&self, round: usize) -> bool {
        self.rounds
            .get(round)
            .is_some_and(|row| row.iter().all(Option::is_some))
    }

    fn collect_round(&self, round: usize) -> Vec<(u64, Vec<u8>)> {
        self.rounds[round]
            .iter()
            .enumerate()
            .map(|(i, m)| (i as u64 + 1, m.clone().expect("round complete")))
            .collect()
    }
}

/// The in-memory reference transport for `n` parties: broadcasts land in shared
/// per-round slots; [`Channel::recv_round`] blocks (condvar) until the round is
/// complete. Bytes really are routed as bytes — each ceremony message crosses a
/// serde encode/decode, so the messages provably survive a byte transport.
pub struct LocalNetwork {
    shared: Arc<(Mutex<NetInner>, Condvar)>,
    n: u64,
}

impl LocalNetwork {
    /// A fresh network of `n ≥ 1` parties.
    pub fn new(n: u64) -> Option<Self> {
        if n == 0 {
            return None;
        }
        Some(Self {
            shared: Arc::new((
                Mutex::new(NetInner {
                    n: n as usize,
                    rounds: Vec::new(),
                }),
                Condvar::new(),
            )),
            n,
        })
    }

    /// One endpoint per party, all starting at round 0. Take them once, at
    /// ceremony start (endpoints share the round history).
    pub fn channels(&self) -> Vec<LocalChannel> {
        (1..=self.n)
            .map(|me| LocalChannel {
                shared: Arc::clone(&self.shared),
                me,
                n: self.n,
                round: 0,
            })
            .collect()
    }
}

/// One party's endpoint on a [`LocalNetwork`].
pub struct LocalChannel {
    shared: Arc<(Mutex<NetInner>, Condvar)>,
    me: u64,
    n: u64,
    round: usize,
}

impl LocalChannel {
    /// Non-blocking receive: the complete current round, or
    /// [`ChannelError::RoundIncomplete`] if some party has not broadcast — the
    /// observable form of the round barrier (blocking [`Channel::recv_round`]
    /// waits where this refuses).
    pub fn try_recv_round(&mut self) -> Result<Vec<(u64, Vec<u8>)>, ChannelError> {
        let (lock, _) = &*self.shared;
        let inner = lock.lock().expect("local network lock");
        if !inner.round_complete(self.round) {
            return Err(ChannelError::RoundIncomplete);
        }
        let out = inner.collect_round(self.round);
        self.round += 1;
        Ok(out)
    }
}

impl Channel for LocalChannel {
    fn me(&self) -> u64 {
        self.me
    }

    fn parties(&self) -> u64 {
        self.n
    }

    fn broadcast(&mut self, bytes: Vec<u8>) -> Result<(), ChannelError> {
        let (lock, cvar) = &*self.shared;
        let mut inner = lock.lock().expect("local network lock");
        inner.ensure_round(self.round);
        let slot = &mut inner.rounds[self.round][(self.me - 1) as usize];
        if slot.is_some() {
            return Err(ChannelError::DuplicateSend);
        }
        *slot = Some(bytes);
        cvar.notify_all();
        Ok(())
    }

    fn recv_round(&mut self) -> Result<Vec<(u64, Vec<u8>)>, ChannelError> {
        let (lock, cvar) = &*self.shared;
        let mut inner = lock.lock().expect("local network lock");
        while !inner.round_complete(self.round) {
            inner = cvar.wait(inner).expect("local network lock");
        }
        let out = inner.collect_round(self.round);
        self.round += 1;
        Ok(out)
    }
}

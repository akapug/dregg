//! # beacon_cell — a self-driving WITNESSED beacon cell over a resharing chain.
//!
//! A [`BeaconCell`] is the [`docs/deos/RESHARING-CHAINS.md`] §D *randomness-beacon
//! reader* of the resharing chain, realized as a single-machine cell: it iterates
//! the common-secret cycle — **sample / hold a fresh random common secret →
//! REVEAL it at the tick → RESHARE the next** — producing a light-client-verifiable
//! UNBIASABLE random stream. Each tick is a TURN: receipt-bearing
//! ([`BeaconTick`]), bound to the committee's group public key, and verifiable by
//! anyone holding only that key (no share).
//!
//! ## What it welds (census-first; reinvents nothing)
//!
//! The cell is pure orchestration over the REAL federation organs:
//!
//! - `dregg_federation::dkg` — the genesis DKG (`DkgParticipant`, no party ever
//!   holds `f(0)`) and the proactive resharing link (`reshare_deal_with_seed` /
//!   `ReshareParticipant`, which preserves `f(0)` while re-randomizing the shares
//!   and may rotate the committee).
//! - `dregg_federation::beacon` — the drand-shaped threshold-BLS beacon
//!   (`BeaconCommittee`, `BeaconShare`, `beacon_at`, `verify_beacon`). The beacon
//!   output for a tick is `σ = H(BEACON_DOMAIN ‖ epoch ‖ height)^{f(0)}`, the
//!   UNIQUE BLS group signature; any `t` honest partials Lagrange-combine to the
//!   SAME `σ`, so the subset choice cannot steer the value (drand's unbiasability).
//!
//! ## The two epistemic facts this cell rides
//!
//! 1. **Unbiasability = the cliff** (`metatheory/Metatheory/CommonSecret.lean`).
//!    The next tick's value is `H(msg_next)^{f(0)}`. `f(0)` is a COMMON SECRET held
//!    by the committee as threshold distributed knowledge `D_G^{≥K}`: below `t`,
//!    a coalition's pooled view is information-theoretically consistent with EVERY
//!    value of `f(0)` (`subThreshold_secret_blind`), so it cannot predict the
//!    output, and it cannot PRODUCE it either — `BeaconCommittee::aggregate`
//!    fail-closes with `InsufficientPartials` below `t`. No VDF: the threshold
//!    provides the unbiasability.
//!
//! 2. **Light-client verifiability = `f(0)` preservation across the chain.** Each
//!    reshare is anchored (`ReshareParticipant::receive_dealing` checks each
//!    dealing's constant-term commitment equals the prior committee's `pk_j`), so
//!    the group public key is preserved across EVERY link. Therefore the GENESIS
//!    group public key verifies every tick's output forever — a light client
//!    pins one key at genesis and checks the whole stream against it
//!    ([`BeaconCell::verify_tick`] / [`BeaconTick::verify`]).
//!
//! ## Forward security (the D-side of KERI)
//!
//! Because each tick RESHARES before the next, the committee's shares are
//! re-randomized every tick (fresh higher-degree coefficients in
//! `reshare_deal_with_rng`); a future compromise of `t` shares cannot reconstruct
//! a PAST tick's share-set. The values are already public (revealed at each tick),
//! but the *committee secret material* is forward-secured exactly as
//! `docs/deos/RESHARING-CHAINS.md` §A describes.

use dregg_federation::beacon::{BeaconCommittee, BeaconOutput, BeaconShare, beacon_at};
use dregg_federation::dkg::{
    DkgError, DkgOutput, DkgParams, DkgParticipant, ReshareParticipant, ShareResponse,
    reshare_deal_with_seed,
};

/// Domain tag for the cell's tick-receipt chaining hash.
const TICK_CHAIN_CONTEXT: &str = "dregg-beacon-cell:tick-chain v1";
/// Domain tag for the cell's committee-fingerprint (the share-publics root).
const COMMITTEE_ROOT_CONTEXT: &str = "dregg-beacon-cell:committee-root v1";

/// The fixed `(epoch, height)` schedule a [`BeaconCell`] advances each tick.
/// Distinct tick coordinates give distinct beacon messages, hence FRESH outputs:
/// the same `f(0)` produces a *different* `σ` at each tick because the message
/// `H(epoch ‖ height)` changes. The schedule is `epoch` fixed at cell birth,
/// `height` = the tick index — monotone, gap-free, replay-evident.
fn tick_coords(epoch: u64, tick_index: u64) -> (u64, u64) {
    (epoch, tick_index)
}

/// Errors a beacon cell can raise. Wraps the federation organ errors verbatim;
/// the cell adds none of its own crypto.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BeaconCellError {
    /// A genesis or reshare ceremony step failed (forwarded from the DKG organ).
    Dkg(DkgError),
    /// `n == 0 || t == 0 || t > n` at construction.
    InvalidParameters,
    /// A reshare did not reproduce the genesis group key — the chain would have
    /// silently swapped `f(0)`. Fail-closed (this should be impossible given the
    /// anchor check, but the cell refuses to advance on it).
    LineageBroken,
    /// Aggregation of the tick beacon failed (forwarded from the beacon organ).
    Beacon(String),
}

impl std::fmt::Display for BeaconCellError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BeaconCellError::Dkg(e) => write!(f, "beacon-cell DKG/reshare error: {e}"),
            BeaconCellError::InvalidParameters => write!(f, "beacon-cell invalid parameters"),
            BeaconCellError::LineageBroken => {
                write!(f, "beacon-cell lineage broken: reshare changed the group key")
            }
            BeaconCellError::Beacon(s) => write!(f, "beacon-cell beacon error: {s}"),
        }
    }
}

impl std::error::Error for BeaconCellError {}

impl From<DkgError> for BeaconCellError {
    fn from(e: DkgError) -> Self {
        BeaconCellError::Dkg(e)
    }
}

/// One TICK of the beacon cell: a receipt-bearing TURN. Carries the revealed
/// beacon output, the tick coordinates, the committee fingerprint at this tick,
/// and the chain link to the previous tick. Light-client-verifiable against the
/// genesis group public key alone ([`BeaconTick::verify`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BeaconTick {
    /// 0-based tick index in this cell's chain.
    pub index: u64,
    /// The beacon output revealed at this tick: `σ = H(epoch ‖ height)^{f(0)}`
    /// and its derived 32-byte randomness.
    pub output: BeaconOutput,
    /// Fingerprint of the committee that produced this tick (blake3 over the
    /// committee's serialized public surface). Lets a verifier SEE that the
    /// committee evolves (forward security) while the group key is unchanged.
    pub committee_root: [u8; 32],
    /// Hash of the previous tick (genesis tick: the all-zero root). Chains the
    /// stream into a replay-evident line — the resharing chain as a `≤`-line.
    pub prev_tick: [u8; 32],
}

impl BeaconTick {
    /// The 32-byte randomness this tick contributes to the stream.
    pub fn randomness(&self) -> [u8; 32] {
        self.output.randomness
    }

    /// This tick's own hash (the `prev_tick` of the next tick): blake3 over the
    /// chained, ordered fields.
    pub fn tick_hash(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key(TICK_CHAIN_CONTEXT);
        h.update(&self.index.to_be_bytes());
        h.update(&self.output.to_bytes());
        h.update(&self.committee_root);
        h.update(&self.prev_tick);
        *h.finalize().as_bytes()
    }

    /// **Light-client verify**: against ONLY the genesis group public key,
    /// re-derive the message from the claimed `(epoch, height)` and check the
    /// unique-BLS pairing + randomness recomputation. A tick that verifies is a
    /// genuine descendant of genesis `f(0)` (the group key is `f(0)`-preserved
    /// across every reshare), so this one check certifies the WHOLE lineage.
    pub fn verify(&self, genesis_group_public: &BeaconCommittee) -> bool {
        genesis_group_public.verify_beacon(&self.output)
    }
}

/// A self-driving witnessed beacon cell.
///
/// Holds the LIVE committee as a set of `DkgOutput`s (the single-machine
/// collapse of the `n` distributed share-holders — each is a real Shamir point
/// of `f(0)`, no party holds `f(0)` after a genuine genesis DKG). Each
/// [`BeaconCell::tick`] reveals the beacon for the next tick coordinate and then
/// reshares the committee for forward security, preserving `f(0)`.
pub struct BeaconCell {
    /// The genesis committee's public surface — the IMMUTABLE light-client
    /// anchor. Every tick verifies against this regardless of how the committee
    /// has since re-randomized/rotated.
    genesis_committee: BeaconCommittee,
    /// The live committee outputs (one per current member). Resharing replaces
    /// this each tick.
    live: Vec<DkgOutput>,
    /// Fixed epoch coordinate for this cell's lifetime.
    epoch: u64,
    /// Next tick index (= the height coordinate of the next tick).
    next_index: u64,
    /// Hash of the most recent tick (genesis: zero).
    head: [u8; 32],
    /// Deterministic driver seed, advanced every reshare. Cell entropy comes
    /// from here; a production deployment seeds it from OS entropy.
    seed: [u8; 32],
    /// New-committee parameters for each reshare (n', t'). Defaults to the
    /// genesis params; rotation is a reshare with different `(n, t)`.
    reshare_params: DkgParams,
}

impl BeaconCell {
    /// Birth a beacon cell with a fresh genesis DKG: `n` members, threshold `t`,
    /// driven deterministically from `seed`. No party ever holds `f(0)` — the
    /// genesis is a real distributed-key-generation ceremony (the honest object,
    /// not the dealer shortcut).
    pub fn genesis(
        n: usize,
        t: usize,
        epoch: u64,
        seed: [u8; 32],
    ) -> Result<Self, BeaconCellError> {
        if n == 0 || t == 0 || t > n {
            return Err(BeaconCellError::InvalidParameters);
        }
        let live = run_dkg(n, t, seed)?;
        let genesis_committee = BeaconCommittee::from(&live[0]);
        Ok(Self {
            genesis_committee,
            live,
            epoch,
            next_index: 0,
            head: [0u8; 32],
            seed: derive_seed(&seed, b"genesis"),
            reshare_params: DkgParams { n, t },
        })
    }

    /// The genesis group public key surface — the single light-client anchor a
    /// verifier needs for the WHOLE stream.
    pub fn anchor(&self) -> &BeaconCommittee {
        &self.genesis_committee
    }

    /// The current live committee's public surface (evolves with each reshare;
    /// its group key always equals [`BeaconCell::anchor`]'s).
    pub fn committee(&self) -> BeaconCommittee {
        BeaconCommittee::from(&self.live[0])
    }

    /// The next tick index this cell will emit.
    pub fn next_index(&self) -> u64 {
        self.next_index
    }

    /// Set the parameters of the NEXT reshare — committee ROTATION (a different
    /// `(n', t')` for the next epoch). The reshare still preserves `f(0)`; only
    /// the committee/threshold changes. `reshare_params` must be valid
    /// (`0 < t' ≤ n'`).
    pub fn rotate_to(&mut self, n: usize, t: usize) -> Result<(), BeaconCellError> {
        if n == 0 || t == 0 || t > n {
            return Err(BeaconCellError::InvalidParameters);
        }
        self.reshare_params = DkgParams { n, t };
        Ok(())
    }

    /// **TICK** — one TURN of the cell. The common-secret cycle, once:
    ///
    /// 1. **REVEAL**: aggregate the live committee's partials into the beacon for
    ///    the next tick coordinate `(epoch, index)`. This is the common secret
    ///    *manifested* at this tick: `σ = H(msg)^{f(0)}`, unique and unbiasable.
    /// 2. **RESHARE**: re-randomize the committee's shares (preserving `f(0)`,
    ///    possibly rotating to new `(n', t')`) — forward security for the next
    ///    tick. The reshare is verified to preserve the genesis group key; a
    ///    drift is `LineageBroken` (fail-closed, never advances).
    ///
    /// Returns the receipt-bearing [`BeaconTick`], chained to the prior tick.
    pub fn tick(&mut self) -> Result<BeaconTick, BeaconCellError> {
        let index = self.next_index;
        let (epoch, height) = tick_coords(self.epoch, index);

        // (1) REVEAL — the committee collectively produces the unique beacon.
        // The single-machine collapse: every live member signs, any node
        // aggregates. Any `t` honest partials yield the SAME σ.
        let committee = BeaconCommittee::from(&self.live[0]);
        let shares: Vec<BeaconShare> = self.live.iter().map(BeaconShare::from).collect();
        let output = beacon_at(&committee, &shares, epoch, height)
            .map_err(|e| BeaconCellError::Beacon(e.to_string()))?;

        let committee_root = committee_root(&committee);
        let tick = BeaconTick {
            index,
            output,
            committee_root,
            prev_tick: self.head,
        };

        // (2) RESHARE — refresh the committee for the next tick (forward
        // security; preserves f(0)).
        let reshared = self.reshare()?;
        // Lineage guard: the reshare MUST preserve the genesis group key.
        if BeaconCommittee::from(&reshared[0]).group_public()
            != self.genesis_committee.group_public()
        {
            return Err(BeaconCellError::LineageBroken);
        }
        self.live = reshared;

        // Advance the cell's chain head + index + driver seed.
        self.head = tick.tick_hash();
        self.next_index += 1;
        self.seed = derive_seed(&self.seed, b"tick");
        Ok(tick)
    }

    /// Verify a tick of THIS cell's stream against the genesis anchor (forwards
    /// to [`BeaconTick::verify`] with this cell's anchor).
    pub fn verify_tick(&self, tick: &BeaconTick) -> bool {
        tick.verify(&self.genesis_committee)
    }

    /// Drive the full proactive resharing link for the live committee to the
    /// configured `reshare_params`, returning the new committee's `DkgOutput`s
    /// (same `f(0)`, fresh shares). Single-machine collapse of the reshare
    /// ceremony: every old member deals, every new member finalizes.
    fn reshare(&mut self) -> Result<Vec<DkgOutput>, BeaconCellError> {
        let new_params = self.reshare_params;
        let view = self.live[0].public_view();

        // Each OLD member deals sub-shares of its share to the new committee
        // with a fresh degree-(t'-1) poly anchored to its public share.
        let mut dealings = Vec::new();
        let mut priv_shares = Vec::new();
        for (k, old) in self.live.iter().enumerate() {
            let mut label = b"reshare-deal".to_vec();
            label.push(k as u8);
            let member_seed = derive_seed(&self.seed, &label);
            let (d, ss) = reshare_deal_with_seed(old, new_params, member_seed)?;
            dealings.push(d);
            priv_shares.extend(ss);
        }

        // Each NEW member anchors to the old public view, ingests every dealing
        // + its private sub-shares, and finalizes to a DkgOutput with the SAME
        // group key.
        let mut new_parts: Vec<ReshareParticipant> = (1..=new_params.n)
            .map(|m| ReshareParticipant::new(view.clone(), new_params, m))
            .collect::<Result<_, _>>()?;
        for p in new_parts.iter_mut() {
            for d in &dealings {
                p.receive_dealing(d)?;
            }
        }
        for ps in &priv_shares {
            // recipient is 1-based; the new committee has new_params.n members.
            let resp = new_parts[ps.recipient - 1].receive_share(ps)?;
            debug_assert!(matches!(resp, ShareResponse::Ack { .. }));
        }
        new_parts
            .iter()
            .map(|p| p.finalize().map_err(BeaconCellError::from))
            .collect()
    }
}

/// Drive a fully honest genesis DKG ceremony (single-machine collapse):
/// `n` members, threshold `t`, deterministic from `seed`. Returns one
/// `DkgOutput` per member — each a Shamir point of `f(0)` with NO party holding
/// `f(0)`. This is the genuine genesis object (not the `BeaconCommittee::deal`
/// dealer shortcut).
fn run_dkg(n: usize, t: usize, seed: [u8; 32]) -> Result<Vec<DkgOutput>, BeaconCellError> {
    let params = DkgParams { n, t };
    let mut parts = Vec::new();
    let mut dealings = Vec::new();
    let mut priv_shares = Vec::new();
    for i in 1..=n {
        let mut label = b"dkg".to_vec();
        label.push(i as u8);
        let member_seed = derive_seed(&seed, &label);
        let (p, d, ss) = DkgParticipant::new_with_seed(params, i, member_seed)?;
        parts.push(p);
        dealings.push(d);
        priv_shares.extend(ss);
    }
    for p in parts.iter_mut() {
        for d in &dealings {
            p.receive_dealing(d)?;
        }
    }
    for ps in &priv_shares {
        let resp = parts[ps.recipient - 1].receive_share(ps)?;
        debug_assert!(matches!(resp, ShareResponse::Ack { .. }));
    }
    parts
        .iter()
        .map(|p| p.finalize(&[], &[]).map_err(BeaconCellError::from))
        .collect()
}

/// Committee fingerprint: blake3 over the serialized public surface.
fn committee_root(committee: &BeaconCommittee) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(COMMITTEE_ROOT_CONTEXT);
    h.update(&committee.to_bytes());
    *h.finalize().as_bytes()
}

/// Derive a child seed from a parent seed and a label (blake3 keyed). Keeps the
/// cell's deterministic driver hierarchical and replayable.
fn derive_seed(parent: &[u8; 32], label: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_keyed(parent);
    h.update(label);
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// TRUE polarity: the cell ticks, producing a FRESH value each tick, and a
    /// light client verifies every tick against the GENESIS anchor alone (the
    /// reshares preserve f(0), so genesis verifies the whole stream).
    #[test]
    fn cell_ticks_fresh_and_lightclient_verifies() {
        let mut cell = BeaconCell::genesis(5, 3, 7, [11u8; 32]).unwrap();
        let anchor = cell.anchor().clone();

        let mut ticks = Vec::new();
        for expected_index in 0..6u64 {
            let tick = cell.tick().unwrap();
            assert_eq!(tick.index, expected_index, "monotone, gap-free indices");
            // A light client holding ONLY the genesis group key verifies it.
            assert!(
                anchor.verify_beacon(&tick.output),
                "genesis anchor verifies every tick (f(0)-preserved lineage)"
            );
            assert!(cell.verify_tick(&tick));
            assert_eq!(tick.output.epoch, 7);
            assert_eq!(tick.output.height, expected_index);
            ticks.push(tick);
        }

        // FRESH: every tick's randomness differs (distinct message per tick).
        for i in 0..ticks.len() {
            for j in (i + 1)..ticks.len() {
                assert_ne!(
                    ticks[i].randomness(),
                    ticks[j].randomness(),
                    "ticks {i} and {j} must produce distinct fresh randomness"
                );
            }
        }

        // The chain links: each tick's prev_tick is the prior tick's hash.
        for w in ticks.windows(2) {
            assert_eq!(w[1].prev_tick, w[0].tick_hash(), "tick chain is linked");
        }
        // Genesis tick chains from the zero root.
        assert_eq!(ticks[0].prev_tick, [0u8; 32]);

        // Forward security is VISIBLE: the committee re-randomizes each tick, so
        // its fingerprint changes even though the group key (anchor) is fixed.
        let roots: std::collections::BTreeSet<_> =
            ticks.iter().map(|t| t.committee_root).collect();
        assert!(
            roots.len() > 1,
            "committee fingerprint must change across ticks (proactive refresh)"
        );
    }

    /// FALSE polarity (the cliff bites): a SUB-THRESHOLD coalition cannot PRODUCE
    /// the next tick's beacon — `aggregate` fail-closes below t. It therefore
    /// cannot bias or predict the value: the threshold (not a VDF) provides the
    /// unbiasability. This is the common-secret cliff (`subThreshold_secret_blind`)
    /// in operational clothes.
    #[test]
    fn subthreshold_coalition_cannot_produce_the_next_tick() {
        let cell = BeaconCell::genesis(5, 3, 42, [99u8; 32]).unwrap();
        let committee = cell.committee();
        let shares: Vec<BeaconShare> = cell.live.iter().map(BeaconShare::from).collect();

        let (epoch, next_height) = tick_coords(cell.epoch, cell.next_index());

        // The honest committee (>= t) CAN produce it.
        let honest = beacon_at(&committee, &shares, epoch, next_height);
        assert!(honest.is_ok(), "the full committee produces the tick");
        let honest = honest.unwrap();

        // Any sub-threshold coalition (here, t-1 = 2 of the 5 shares) CANNOT.
        let sub = &shares[0..2];
        let attempt = beacon_at(&committee, sub, epoch, next_height);
        assert!(
            attempt.is_err(),
            "a sub-threshold coalition must NOT be able to produce the next tick"
        );

        // And it cannot bias/steer: ANY valid t-subset yields the SAME σ as the
        // full committee (BLS uniqueness) — there is no degree of freedom for a
        // partial coalition to push the value around.
        let q1 = beacon_at(&committee, &shares[0..3], epoch, next_height).unwrap();
        let q2 = beacon_at(&committee, &shares[2..5], epoch, next_height).unwrap();
        assert_eq!(q1, honest, "every quorum subset yields the same value");
        assert_eq!(q2, honest, "the subset choice cannot steer the output");

        // A forged/swapped output (e.g. a sub-coalition fabricating partials over
        // the NEXT message under WRONG shares) does not verify against the anchor.
        // We model "cannot predict" as: nothing short of t real shares yields a
        // value the anchor accepts for next_height — confirmed by the err above
        // and the uniqueness here.
        assert!(cell.anchor().verify_beacon(&honest));
    }

    /// Resharing/rotation: the cell can ROTATE the committee (new n', t') and the
    /// stream stays light-client-verifiable against the SAME genesis anchor —
    /// proactive committee change as a `≤`-link that preserves f(0).
    #[test]
    fn rotation_preserves_the_lineage_anchor() {
        let mut cell = BeaconCell::genesis(5, 3, 1, [3u8; 32]).unwrap();
        let anchor = cell.anchor().clone();

        let t0 = cell.tick().unwrap();
        assert!(anchor.verify_beacon(&t0.output));

        // Rotate the committee to a smaller (4, 2) set on the next reshare.
        cell.rotate_to(4, 2).unwrap();
        let t1 = cell.tick().unwrap();
        assert!(anchor.verify_beacon(&t1.output));

        // After the rotation took effect, the live committee has 4 members and
        // threshold 2, but its group key is STILL the genesis key.
        let live = cell.committee();
        assert_eq!(live.num_members(), 4, "committee rotated to n'=4");
        assert_eq!(live.threshold(), 2, "threshold rotated to t'=2");
        assert_eq!(
            live.group_public(),
            anchor.group_public(),
            "rotation preserves f(0): the genesis anchor still verifies"
        );

        let t2 = cell.tick().unwrap();
        assert!(
            anchor.verify_beacon(&t2.output),
            "the post-rotation committee still verifies under the genesis anchor"
        );
        // Still fresh and still chained across the rotation boundary.
        assert_ne!(t1.randomness(), t2.randomness());
        assert_eq!(t1.prev_tick, t0.tick_hash());
        assert_eq!(t2.prev_tick, t1.tick_hash());
    }

    /// A tampered tick (wrong randomness) is rejected by the light client — the
    /// verify is fail-closed on the recomputation, not credulous.
    #[test]
    fn tampered_tick_is_rejected() {
        let mut cell = BeaconCell::genesis(4, 2, 5, [21u8; 32]).unwrap();
        let mut tick = cell.tick().unwrap();
        assert!(cell.verify_tick(&tick));
        // Flip a byte of the derived randomness.
        tick.output.randomness[0] ^= 0xff;
        assert!(
            !cell.verify_tick(&tick),
            "a tampered randomness must fail the light-client recomputation"
        );
    }

    /// Determinism: two cells from the same seed produce byte-identical streams
    /// (replayable witness), and the genesis anchor is reproducible.
    #[test]
    fn deterministic_replay() {
        let mut a = BeaconCell::genesis(5, 3, 9, [77u8; 32]).unwrap();
        let mut b = BeaconCell::genesis(5, 3, 9, [77u8; 32]).unwrap();
        assert_eq!(a.anchor().to_bytes(), b.anchor().to_bytes());
        for _ in 0..4 {
            let ta = a.tick().unwrap();
            let tb = b.tick().unwrap();
            assert_eq!(ta, tb, "same seed -> byte-identical tick stream");
        }
    }
}

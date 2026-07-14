//! The indexed XOF draw stream and its unbiased bounded mapping.
//!
//! A verified [`Seed`] expands into a fixed, indexed stream of 64-bit draws. The
//! stream is a pure function of `(seed, index)`, so any verifier reconstructs the
//! exact same values. Bounded outcomes use a **fixed-width, reject-free** mapping
//! (wide multiply-and-shift), never data-dependent rejection sampling — see
//! [`DrawStream::draw_bounded`] for why that matters for non-grindability.

use serde::{Deserialize, Serialize};

use crate::error::DrawError;
use crate::util::absorb_len_prefixed;

/// Domain tag for a single indexed draw.
pub const DOMAIN_DRAW: &[u8] = b"dregg-dice/draw/v1";
/// Domain tag for the whole-transcript commitment.
pub const DOMAIN_TRANSCRIPT: &[u8] = b"dregg-dice/draw-transcript/v1";

/// A verified 32-byte randomness seed. Produced only by a
/// [`RandomnessSource::seed`](crate::RandomnessSource::seed) verifier, never
/// constructed from thin air by callers on the trust path (test code may use
/// [`Seed::from_bytes`]).
#[derive(Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Seed([u8; 32]);

impl Seed {
    /// Wrap raw bytes as a seed. Intended for tests and for source verifiers
    /// inside this crate; the seed's soundness comes from the derivation that
    /// produced these bytes, not from this constructor.
    #[inline]
    pub fn from_bytes(bytes: [u8; 32]) -> Seed {
        Seed(bytes)
    }

    /// The raw 32 bytes.
    #[inline]
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl core::fmt::Debug for Seed {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Seed(")?;
        for b in &self.0[..4] {
            write!(f, "{b:02x}")?;
        }
        write!(f, "…)")
    }
}

/// A deterministic, indexed stream of draws derived from a verified seed.
///
/// `draw_count` fixes the number of legal indices (`0..draw_count`); it is bound
/// into the [`EventId`](crate::EventId), so a verifier that reconstructs the
/// stream and requests a different range diverges detectably.
#[derive(Clone, Debug)]
pub struct DrawStream {
    seed: Seed,
    draw_count: u32,
}

impl DrawStream {
    /// Build a stream over `0..draw_count` from a verified seed.
    pub fn new(seed: Seed, draw_count: u32) -> DrawStream {
        DrawStream { seed, draw_count }
    }

    /// The number of legal indices.
    #[inline]
    pub fn draw_count(&self) -> u32 {
        self.draw_count
    }

    /// The raw, uniform 64-bit draw at `index`, ignoring the `draw_count` bound.
    /// Used internally by the transcript and by the checked accessors.
    fn raw(&self, index: u32) -> u64 {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_DRAW);
        h.update(self.seed.as_bytes());
        h.update(&index.to_le_bytes());
        let mut buf = [0u8; 8];
        h.finalize_xof().fill(&mut buf);
        u64::from_le_bytes(buf)
    }

    /// The uniform 64-bit draw at `index`.
    ///
    /// Returns [`DrawError::IndexOutOfRange`] for `index >= draw_count`: the legal
    /// range is fixed by the request before the seed exists, so an out-of-range
    /// draw is never part of a valid transcript.
    pub fn draw(&self, index: u32) -> Result<u64, DrawError> {
        if index >= self.draw_count {
            return Err(DrawError::IndexOutOfRange {
                index,
                draw_count: self.draw_count,
            });
        }
        Ok(self.raw(index))
    }

    /// An unbiased draw in `0..n` using a fixed-width, **reject-free** mapping.
    ///
    /// The construction is the wide multiply-and-shift (the fixed-width variant of
    /// Lemire's method, without the rejection step):
    ///
    /// ```text
    /// draw_bounded(index, n) = ((raw(index) as u128 * n as u128) >> 64) as u64
    /// ```
    ///
    /// A uniform 64-bit `x` is scaled into `0..n` by taking the high word of the
    /// 128-bit product. This is **not** modulo reduction (`x % n`), which biases
    /// toward small residues whenever `n` does not divide `2^64`. The remaining
    /// bias here is at most `n / 2^64` — negligible for game-scale bounds (for a
    /// d20 the bias is < 2⁻⁵⁹).
    ///
    /// Crucially the mapping consumes **exactly one** raw draw per index,
    /// regardless of the value drawn. Rejection sampling (Lemire's discard step,
    /// or `loop { x = raw(); if x < threshold { .. } }`) would make the number of
    /// raw draws *depend on the values seen* — so `draw_count` could no longer be
    /// bound up-front, and a party could grind by choosing inputs that make the
    /// sampler consume a favorable number of draws. A fixed-width mapping keeps
    /// the transcript length a public constant, which is what lets `draw_count`
    /// live inside the `EventId`.
    pub fn draw_bounded(&self, index: u32, n: u64) -> Result<u64, DrawError> {
        if n == 0 {
            return Err(DrawError::ZeroBound);
        }
        let x = self.draw(index)?;
        Ok(((x as u128 * n as u128) >> 64) as u64)
    }

    /// A 1-based die roll in `1..=sides` (convenience over [`Self::draw_bounded`]).
    pub fn draw_die(&self, index: u32, sides: u64) -> Result<u64, DrawError> {
        Ok(self.draw_bounded(index, sides)? + 1)
    }

    /// A **provably-fair weighted selection** over a *committed* weight table: returns
    /// the index of the tier the draw at `index` falls into, where tier `i` is chosen
    /// with probability `weights[i] / Σ weights`.
    ///
    /// The construction is a CDF over **exactly one** [`Self::draw_bounded`]: a single
    /// unbiased draw in `0..Σweights` is walked against the cumulative weights, and the
    /// first tier whose running total exceeds it wins. Like every other draw here it
    /// consumes exactly one raw draw per `index`, so it stays inside the fixed
    /// transcript (`draw_count` is unchanged) and the whole selection is re-derivable by
    /// any verifier from `(seed, index)` and the *same committed weights*.
    ///
    /// **The weights must be committed** — a Rust `const` table, or a table hashed into
    /// the [`RandomnessRequest`](crate::RandomnessRequest) — so they cannot be swapped
    /// after the seed is fixed. Given the commitment, "I drew the legendary tier" is a
    /// claim anyone re-derives, not one they must be trusted on: this is the mechanism
    /// behind provable rarity (a 1/1000 tier is simply a small weight, re-checkable at
    /// the tail of the CDF without any impractical repeated-slot table).
    ///
    /// Returns [`DrawError::ZeroBound`] if `weights` is empty or sums to zero, and
    /// [`DrawError::WeightsOverflow`] if the weights sum past `u64::MAX`.
    pub fn weighted(&self, index: u32, weights: &[u64]) -> Result<usize, DrawError> {
        let total: u128 = weights.iter().map(|&w| w as u128).sum();
        if total == 0 {
            return Err(DrawError::ZeroBound);
        }
        let n = u64::try_from(total).map_err(|_| DrawError::WeightsOverflow)?;
        let pick = self.draw_bounded(index, n)? as u128;
        let mut acc: u128 = 0;
        for (i, &w) in weights.iter().enumerate() {
            acc += w as u128;
            if pick < acc {
                return Ok(i);
            }
        }
        // `pick < total` always holds (draw_bounded yields `0..n`), so the loop returns
        // above; the final tier closes the CDF as a total function for the type-checker.
        Ok(weights.len() - 1)
    }

    /// A commitment over the entire transcript: the seed, the draw count, and
    /// every raw draw `0..draw_count` in order.
    ///
    /// A verifier that re-derives the seed recomputes this and compares it to the
    /// evidence's `draw_transcript_commitment`. Any change to the seed inputs, or
    /// to `draw_count` (adding/removing a draw), moves this value — so grinding
    /// and skipped/extra draws are both detectable.
    pub fn transcript_commitment(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        absorb_len_prefixed(&mut h, DOMAIN_TRANSCRIPT);
        h.update(self.seed.as_bytes());
        h.update(&self.draw_count.to_le_bytes());
        for i in 0..self.draw_count {
            h.update(&self.raw(i).to_le_bytes());
        }
        *h.finalize().as_bytes()
    }
}

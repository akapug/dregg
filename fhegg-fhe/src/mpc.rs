//! OUTPUT-BOUNDARY MPC — the one-process no-viewer crossing PoC.
//!
//! `docs/deos/OUTPUT-BOUNDARY-MPC.md` is the design; this is the working PoC.
//!
//! ## The construction, in one paragraph
//!
//! The additive RLWE/BFV fold (`crate::additive::bfv_fold`) turns N encrypted
//! orders into two aggregate curve ciphertexts — encrypted demand `D[p]` and
//! supply `S[p]` over K price buckets — with cheap carry-free adds
//! (`ADDITIVE-FOLD-ENVELOPE.md`: ~10^5× the exact-integer TFHE fold). The clearing
//! price `p*` is DELIBERATELY public. So we do NOT pay for the comparison inside
//! TFHE and we do NOT scheme-switch BFV→TFHE. Instead, at the OUTPUT BOUNDARY the
//! `n` parties collectively decrypt only a masked aggregate and locally derive
//! additive plaintext shares (the mask/decrypt/re-share construction lives in
//! `crate::boundary`; real n-of-n BFV custody lives in `crate::threshold`) and run
//! the crossing `p* = argmax_j min(D[j],S[j])` in a **secret-shared MPC**,
//! revealing ONLY `p*` and the cleared volume `V*`. This module is that MPC.
//!
//! ## Security scope
//!
//! The comparison runs over additive shares with a real GMW/Beaver-triple online
//! phase. Every opened AND message is a one-time-pad-masked bit (`x ⊕ a`, `a` a
//! fresh uniform shared triple bit). This gives the circuit's standard semi-honest
//! algebraic privacy argument. The implementation here, however, simulates every
//! party in one process, generates triples through a simulated dealer, and records
//! only the public transcript. It is not an authenticated distributed runtime or
//! a malicious-security theorem. The current BFV custody path is n-of-n and its
//! party key shares are reusable.
//!
//! ## What "reveal only (p*, V*)" means (the leakage argument)
//!
//! The crossing computes `p* = argmax_p min(D[p], S[p])` (ties to the lowest p)
//! by an OBLIVIOUS argmax — a balanced tournament whose gate schedule is fixed by
//! `(K, b)`, not by the inputs — and opens ONLY the argmax index `p*` and its
//! volume `V* = min(D[p*], S[p*])`. No sign bit `[D[p] ≥ S[p]]`, no per-bucket
//! comparison, and no curve height is ever opened. (The earlier "open the sign
//! vector, take the last crossing" shortcut both mis-cleared — the volume peak can
//! sit one bucket above the crossing — AND leaked the crossing index, which is
//! strictly more than `p*`.) Every other protocol message is a one-time-pad-masked
//! Beaver reveal — uniform and input-independent — so a simulator given only
//! `(p*, V*)` reproduces this public transcript distribution (the masked pads plus
//! the p*- and V*-bit openings). Extending that correspondence through real party
//! processes, transport, BFV shares, and adaptive/malicious behavior is separate.
//!
//! ## What is real here vs. abstracted (honest)
//!
//! - **REAL:** boolean (GF(2)) additive secret sharing among `n` parties; a real
//!   Beaver-triple AND gate whose opened values are one-time-pad masked; a real
//!   bit-sliced secure `≥` comparator; a real secure `min`; an oblivious argmax
//!   crossing (secure MUX on a secret compare bit). The simulated party shares do
//!   not individually reveal a coefficient; the one-process convenience entry
//!   point does receive the clear curves in order to generate those shares.
//! - **PREPROCESSING (standard MPC assumption):** the Beaver triples are produced
//!   by a simulated offline dealer (the SPDZ "offline phase"). In production the
//!   triples come from OT/HE preprocessing AMONG the parties — the ONLINE phase
//!   below is information-theoretically secure GIVEN the triples, and it is the
//!   online phase that carries the reveal-only-`p*` property.
//! - **ABSTRACTED (labelled):** this module's convenience path models the boundary
//!   by sharing clear committed coefficients (`share_int`). `boundary.rs` pins the
//!   mask/decrypt/re-share identity; `threshold.rs` independently pins n-of-n BFV
//!   keygen and smudged decrypt shares. Their distributed composition is not in
//!   this module.

use std::time::{Duration, Instant};

use rand::Rng;

use crate::{order_increment, Order, Side};

/// A boolean secret shared additively over GF(2) among `n` parties: the cleartext
/// bit is `⊕_i share[i]`. Any `n-1` shares are uniform and independent of the
/// secret, so a below-threshold coalition learns nothing from its shares alone.
pub type Bit = Vec<u8>;

/// A `b`-bit integer, boolean-shared bit-by-bit, LSB first (`bits[0]` = 2^0).
pub type SharedInt = Vec<Bit>;

/// A Beaver multiplication triple over GF(2): shared `a`, `b`, `c` with `c = a·b`
/// (= `a AND b`). Consumed one-per-AND-gate in the online phase.
#[derive(Clone)]
pub struct Triple {
    pub a: Bit,
    pub b: Bit,
    pub c: Bit,
}

/// The public transcript of one MPC crossing: every bit that is ever OPENED
/// (broadcast to all parties). This is exactly the input-dependent part of each
/// party's view beyond its own random shares. We record it to DEMONSTRATE the
/// privacy property: the `masked` bits are one-time-pad masked (uniform,
/// input-independent), and `revealed_*` depends only on the public output.
#[derive(Clone, Default)]
pub struct Transcript {
    /// Every `d = x ⊕ a` / `e = y ⊕ b` opened inside a Beaver AND gate. These are
    /// the protocol messages. Each is uniform because `a`,`b` are fresh uniform.
    pub masked: Vec<u8>,
    /// The opened clearing-price index `p*` bits (LSB first) — the argmax result.
    pub revealed_pstar: Vec<u8>,
    /// The opened cleared volume `V*` bits (the only value output besides `p*`).
    pub revealed_vstar: Vec<u8>,
    /// AND gates executed (= triples consumed) — the online multiplicative cost.
    pub and_gates: usize,
    /// Modeled sequential AND-depth. A distributed party runtime that batches
    /// all same-depth Beaver openings would use this many protocol rounds; this
    /// one-process PoC does not itself execute or measure network scheduling.
    pub rounds: usize,
}

impl Transcript {
    /// Validate the complete public transcript schema for a `(k,b)` crossing.
    /// This is deliberately stricter than checking only the index width: an
    /// appended output bit or unaccounted masked opening must make the leakage
    /// tooth red.
    pub fn is_reveal_only(&self, k: usize, b: usize) -> bool {
        let canonical_bits = |bits: &[u8]| bits.iter().all(|&bit| bit <= 1);
        self.revealed_pstar.len() == index_bits(k)
            && self.revealed_vstar.len() == b
            && self
                .and_gates
                .checked_mul(2)
                .is_some_and(|expected| self.masked.len() == expected)
            && canonical_bits(&self.masked)
            && canonical_bits(&self.revealed_pstar)
            && canonical_bits(&self.revealed_vstar)
    }
}

// ---------------------------------------------------------------------------
// Boolean-share primitives (XOR is local/free; AND needs a Beaver triple).
// ---------------------------------------------------------------------------

/// Share a public bit as a constant (party 0 carries it; the rest hold 0). Used
/// for circuit constants; no secrecy needed.
pub fn share_const(bit: u8, n: usize) -> Bit {
    let mut v = vec![0u8; n];
    v[0] = bit & 1;
    v
}

/// Split a secret bit into `n` uniform XOR shares. The first `n-1` shares are
/// fresh uniform; the last absorbs the parity, so any `n-1` shares are uniform
/// and independent of `bit`.
pub fn share_bit<R: Rng>(bit: u8, n: usize, rng: &mut R) -> Bit {
    let mut v = vec![0u8; n];
    let mut acc = 0u8;
    for s in v.iter_mut().take(n - 1) {
        let r: u8 = rng.gen_range(0..=1);
        *s = r;
        acc ^= r;
    }
    v[n - 1] = (bit & 1) ^ acc;
    v
}

/// Bit-decompose a caller-visible `value` into `b` boolean-shared bits (LSB first).
/// Boundary protocols must supply the value shares without first revealing the
/// coefficient; this convenience primitive is not a BFV partial decrypt.
pub fn share_int<R: Rng>(value: u64, b: usize, n: usize, rng: &mut R) -> SharedInt {
    assert!(
        b >= 64 || value < (1u64 << b),
        "value {value} overflows {b} bits"
    );
    (0..b)
        .map(|i| share_bit(((value >> i) & 1) as u8, n, rng))
        .collect()
}

/// Open a shared bit to its cleartext (`⊕_i share[i]`). This is a broadcast; the
/// caller decides whether opening this bit is safe (a one-time-padded Beaver
/// message or an explicitly public output bit — never a sign bit or raw curve
/// coefficient in the current rule).
pub fn open(x: &Bit) -> u8 {
    x.iter().fold(0u8, |a, &s| a ^ (s & 1))
}

/// Local XOR of two shared bits (no communication).
pub fn xor(x: &Bit, y: &Bit) -> Bit {
    x.iter().zip(y).map(|(&a, &b)| a ^ b).collect()
}

/// XOR a PUBLIC constant into a shared bit (party 0 only) — local.
pub fn xor_const(x: &Bit, c: u8) -> Bit {
    let mut v = x.clone();
    v[0] ^= c & 1;
    v
}

/// Logical NOT of a shared bit = XOR with public 1 — local.
pub fn not(x: &Bit) -> Bit {
    xor_const(x, 1)
}

/// AND a PUBLIC bit into a shared bit — local (`0` kills, `1` keeps).
fn and_public(pubbit: u8, x: &Bit) -> Bit {
    if pubbit & 1 == 1 {
        x.clone()
    } else {
        vec![0u8; x.len()]
    }
}

/// The Beaver-triple AND gate — the ONE interactive primitive. To compute
/// `[z] = [x]·[y]` (GF(2) AND) from a triple `(a,b,c=a·b)`:
///   d = open(x ⊕ a),  e = open(y ⊕ b)         // masked reveals — uniform pad
///   [z] = [c] ⊕ d·[b] ⊕ e·[a] ⊕ d·e            // local recombination
/// The opened `d`,`e` are one-time-pad masked by the fresh uniform `a`,`b`, so
/// they leak nothing about `x`,`y`. Records `d`,`e` into the transcript.
pub fn and_gate(x: &Bit, y: &Bit, t: &Triple, tr: &mut Transcript) -> Bit {
    let d = open(&xor(x, &t.a));
    let e = open(&xor(y, &t.b));
    tr.masked.push(d);
    tr.masked.push(e);
    tr.and_gates += 1;

    // [z] = [c] ⊕ d·[b] ⊕ e·[a] ⊕ (d·e as public const)
    let mut z = t.c.clone();
    z = xor(&z, &and_public(d, &t.b));
    z = xor(&z, &and_public(e, &t.a));
    z = xor_const(&z, d & e);
    z
}

/// Generate a Beaver triple over GF(2) (simulated offline dealer — the SPDZ
/// offline phase). `a`,`b` uniform; `c = a AND b`; each shared among `n` parties.
pub fn gen_triple<R: Rng>(n: usize, rng: &mut R) -> Triple {
    let a: u8 = rng.gen_range(0..=1);
    let b: u8 = rng.gen_range(0..=1);
    let c = a & b;
    Triple {
        a: share_bit(a, n, rng),
        b: share_bit(b, n, rng),
        c: share_bit(c, n, rng),
    }
}

/// A pool of preprocessed triples, consumed by the online phase.
pub struct TriplePool {
    triples: Vec<Triple>,
    next: usize,
}

impl TriplePool {
    pub fn generate<R: Rng>(count: usize, n: usize, rng: &mut R) -> Self {
        TriplePool {
            triples: (0..count).map(|_| gen_triple(n, rng)).collect(),
            next: 0,
        }
    }
    fn take(&mut self) -> &Triple {
        let t = &self.triples[self.next];
        self.next += 1;
        t
    }
    pub fn consumed(&self) -> usize {
        self.next
    }
}

// ---------------------------------------------------------------------------
// The secure comparator + crossing.
// ---------------------------------------------------------------------------

/// Secure `[a ≥ b]` on two `b`-bit boolean-shared integers → one shared bit.
///
/// MSB-first bit ripple: track `gt` (a>b decided by the most-significant differing
/// bit so far) and `eq` (all higher bits equal). `a ≥ b` iff `a > b` OR `a == b`,
/// and those are mutually exclusive so `geq = gt ⊕ eq_final`. ~3·b AND gates;
/// its AND-depth is `max(b, 2)`: all per-bit `this_gt` gates run in the first
/// round while the `eq` prefix is a `b`-deep chain. Independent comparisons at
/// one tournament level batch into those same rounds.
pub fn geq(a: &SharedInt, b: &SharedInt, pool: &mut TriplePool, tr: &mut Transcript) -> Bit {
    let n = a[0].len();
    let bits = a.len();
    let mut gt = share_const(0, n);
    let mut eq = share_const(1, n);
    for i in (0..bits).rev() {
        let nb = not(&b[i]);
        // this_gt = a_i AND (NOT b_i)
        let this_gt = {
            let t = pool.take().clone();
            and_gate(&a[i], &nb, &t, tr)
        };
        // gt ⊕= eq_prefix AND this_gt
        let contrib = {
            let t = pool.take().clone();
            and_gate(&eq, &this_gt, &t, tr)
        };
        gt = xor(&gt, &contrib);
        // eq_prefix AND= NOT(a_i XOR b_i)
        let eq_i = not(&xor(&a[i], &b[i]));
        let t = pool.take().clone();
        eq = and_gate(&eq, &eq_i, &t, tr);
    }
    xor(&gt, &eq)
}

/// Secure `min(a, b)` on two `b`-bit boolean-shared integers → shared bits.
/// `lt = [a < b] = NOT[a ≥ b]`; `min_i = b_i ⊕ (lt AND (a_i ⊕ b_i))` (pick `a`
/// when `lt`). ~b extra AND gates. Used to reveal ONLY `V*`, never both heights.
pub fn secure_min(
    a: &SharedInt,
    b: &SharedInt,
    pool: &mut TriplePool,
    tr: &mut Transcript,
) -> SharedInt {
    let ge = geq(a, b, pool, tr);
    let lt = not(&ge);
    a.iter()
        .zip(b)
        .map(|(ai, bi)| {
            let dxor = xor(ai, bi);
            let t = pool.take().clone();
            let sel = and_gate(&lt, &dxor, &t, tr);
            xor(bi, &sel)
        })
        .collect()
}

/// Open a shared integer to cleartext (used ONLY for the public outputs V*).
pub fn open_int(x: &SharedInt) -> u64 {
    x.iter()
        .enumerate()
        .fold(0u64, |acc, (i, bit)| acc | ((open(bit) as u64) << i))
}

/// An upper bound on the Beaver triples one crossing consumes: `K` per-bucket
/// `secure_min` (`4b` each) plus the `K-1` internal nodes of the balanced argmax
/// tournament (each node is a `geq` = `3b`, a `b`-bit value MUX, and an
/// `index_bits`-bit index MUX). A small `+b` slack keeps the pool safely sized.
/// Over-allocation is harmless (`consumed()` reports the actual count); an
/// under-count would panic in `pool.take()`.
pub fn triples_needed(k: usize, b: usize) -> usize {
    let idx = index_bits(k);
    k * (4 * b) + k.saturating_sub(1) * (4 * b + idx) + b
}

/// Bit-width of a bucket index over `k` buckets — enough to hold the largest
/// index `k-1` (at least 1). `p*` is opened as this many bits.
pub fn index_bits(k: usize) -> usize {
    ceil_log2(k).max(1)
}

/// Exact Beaver-opening depth of [`geq`] under the batched circuit schedule.
///
/// Every bit's `a_i AND !b_i` and the first equality-prefix gate run at depth 1.
/// The equality prefix then advances one bit per round; its corresponding
/// `eq_prefix AND this_gt` gates join as soon as their prefix is ready. Thus a
/// normal multi-bit comparison has depth `b`; the one-bit edge case needs two
/// rounds because `this_gt` must be produced before it is gated by `eq`.
pub fn geq_rounds(b: usize) -> usize {
    assert!(b >= 1, "at least one value bit");
    if b < 2 {
        2
    } else {
        b
    }
}

/// Exact modeled online depth of [`mpc_crossing`].
///
/// All `K` secure minima batch in `geq_rounds(b) + 1` rounds (comparison plus
/// one parallel MUX round). The balanced argmax has `ceil(log2 K)` levels, and
/// every level has that same comparison-plus-MUX depth. Odd candidates are
/// carried locally to the next level without adding a round.
pub fn crossing_rounds(k: usize, b: usize) -> usize {
    assert!(k >= 1, "at least one price bucket");
    assert!(b >= 1, "at least one value bit");
    (geq_rounds(b) + 1) * (1 + ceil_log2(k))
}

/// A PUBLIC integer as a boolean-shared constant (party 0 carries the bits, LSB
/// first). No secrecy — used for the argmax's candidate bucket indices (and by
/// `crate::boundary`'s mod-t reduction, whose modulus `t` is public).
pub fn const_int(value: u64, bits: usize, n: usize) -> SharedInt {
    (0..bits)
        .map(|i| share_const(((value >> i) & 1) as u8, n))
        .collect()
}

/// Oblivious multiplexer on boolean-shared integers: returns `a` when `cond`=1,
/// else `b`, bit-by-bit `out_i = b_i ⊕ (cond ∧ (a_i ⊕ b_i))`. One AND gate per
/// bit; opens only the (one-time-pad-masked) Beaver reveals, never `cond` itself.
pub fn select_int(
    cond: &Bit,
    a: &SharedInt,
    b: &SharedInt,
    pool: &mut TriplePool,
    tr: &mut Transcript,
) -> SharedInt {
    a.iter()
        .zip(b)
        .map(|(ai, bi)| {
            let dxor = xor(ai, bi);
            let t = pool.take().clone();
            let sel = and_gate(cond, &dxor, &t, tr);
            xor(bi, &sel)
        })
        .collect()
}

/// The public result of an output-boundary MPC crossing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Crossing {
    /// clearing price bucket p* = argmax_j min(D[j],S[j]), ties to the lowest j.
    /// `None` if the book never clears (the max executed volume is 0).
    pub p_star: Option<usize>,
    /// cleared volume V* = min(D[p*], S[p*]).
    pub v_star: u64,
}

/// THE OUTPUT-BOUNDARY MPC CROSSING. Inputs are the already-secret-shared
/// aggregate curves `d_shared[p]`, `s_shared[p]` (the threshold-BFV
/// partial-decrypt-into-shares of the folded curves). Reveals ONLY `(p*, V*)`.
///
/// The uniform-price rule is `p* = argmax_p min(D[p],S[p])` (ties to the lowest
/// p), `V* = min(D[p*],S[p*])`. We compute it OBLIVIOUSLY — no per-bucket
/// quantity or comparison is ever opened:
///
/// 1. Per bucket, `v[p] = secure_min(D[p], S[p])` — a secret-shared volume.
/// 2. A balanced, data-oblivious tournament reduces adjacent ordered candidates.
///    A node keeps the left candidate on `[left_v ≥ right_v]`; because every
///    left subtree contains only lower indices than its right sibling, equality
///    deterministically keeps the globally lowest index. An odd final candidate
///    is carried to the next level unchanged. The schedule depends only on
///    `(K,b)`, never on secret data.
/// 3. Open ONLY `best_idx` (= p*) and `best_v` (= V*). Nothing else — not the
///    sign vector, not any curve height — is ever revealed.
pub fn mpc_crossing(
    d_shared: &[SharedInt],
    s_shared: &[SharedInt],
    pool: &mut TriplePool,
    tr: &mut Transcript,
) -> Crossing {
    let k = d_shared.len();
    assert_eq!(k, s_shared.len());
    assert!(k >= 1, "at least one price bucket");
    let n = d_shared[0][0].len();
    let idx_bits = index_bits(k);

    // (1) per-bucket executed volume v[p] = min(D[p], S[p]) — NEVER opened.
    let vols: Vec<SharedInt> = (0..k)
        .map(|p| secure_min(&d_shared[p], &s_shared[p], pool, tr))
        .collect();

    // (2) BALANCED OBLIVIOUS ARGMAX. At every node the left candidate represents
    //     a strictly lower contiguous range of original indices than the right.
    //     Selecting left on `left_v ≥ right_v` therefore composes the global
    //     lowest-index tie rule. Pairing/carrying is public and depends only on K.
    let mut level: Vec<(SharedInt, SharedInt)> = vols
        .into_iter()
        .enumerate()
        .map(|(p, value)| (value, const_int(p as u64, idx_bits, n)))
        .collect();
    while level.len() > 1 {
        let mut next = Vec::with_capacity((level.len() + 1) / 2);
        let mut candidates = level.into_iter();
        while let Some(left) = candidates.next() {
            if let Some(right) = candidates.next() {
                let left_wins = geq(&left.0, &right.0, pool, tr);
                let value = select_int(&left_wins, &left.0, &right.0, pool, tr);
                let index = select_int(&left_wins, &left.1, &right.1, pool, tr);
                next.push((value, index));
            } else {
                // A public odd-size carry: no gate, opening, or secret branch.
                next.push(left);
            }
        }
        level = next;
    }
    let (best_v, best_idx) = level.pop().expect("K >= 1");
    tr.rounds += crossing_rounds(k, best_v.len());

    // (3) reveal ONLY (p*, V*). V*==0 means the book never clears.
    let v_star = open_int(&best_v);
    let idx = open_int(&best_idx) as usize;
    tr.revealed_pstar = (0..idx_bits).map(|i| ((idx >> i) & 1) as u8).collect();
    tr.revealed_vstar = (0..best_v.len())
        .map(|i| ((v_star >> i) & 1) as u8)
        .collect();
    let p_star = if v_star == 0 { None } else { Some(idx) };

    Crossing { p_star, v_star }
}

/// One-process convenience: share two caller-visible cleartext curves and run the
/// MPC circuit, returning `(Crossing, Transcript, triples_consumed)`. This models
/// the MPC input shares; it does not perform BFV partial decryption or a network
/// handoff. `b` = bit-width of the curve coefficients.
pub fn cross_curves<R: Rng>(
    demand: &[u64],
    supply: &[u64],
    b: usize,
    n: usize,
    rng: &mut R,
) -> (Crossing, Transcript, usize) {
    let k = demand.len();
    let mut pool = TriplePool::generate(triples_needed(k, b), n, rng);
    let d_shared: Vec<SharedInt> = demand.iter().map(|&v| share_int(v, b, n, rng)).collect();
    let s_shared: Vec<SharedInt> = supply.iter().map(|&v| share_int(v, b, n, rng)).collect();
    let mut tr = Transcript::default();
    let cross = mpc_crossing(&d_shared, &s_shared, &mut pool, &mut tr);
    let used = pool.consumed();
    (cross, tr, used)
}

// ---------------------------------------------------------------------------
// The SIMULATOR — the crisp statement of "reveals only (p*, V*)".
// ---------------------------------------------------------------------------

/// A simulator that, given ONLY the public output `(p*, V*)` and circuit shape
/// `(k,b)`, produces a public [`Transcript`] identically distributed to this
/// one-process circuit's recorded transcript. It is a public-transcript lemma,
/// not a full corrupted-party/network-view simulator.
///
/// It works because: (a) every opened `masked` bit is a one-time-pad, so the
/// simulator samples it uniform, and the argmax runs the SAME gate count on every
/// input (data-oblivious), so that count depends only on `(k, b)`; (b) the opened
/// `p*` index bits are a deterministic function of `p*`; (c) `V*` is given. No
/// curve coefficient is ever needed.
pub fn simulate<R: Rng>(cross: &Crossing, k: usize, b: usize, rng: &mut R) -> Transcript {
    let mut tr = Transcript::default();
    let idx_bits = index_bits(k);
    // (a) masked bits: exactly as many as the real run (2 opens per AND gate),
    //     each sampled uniform. The real run's gate count is data-oblivious:
    //     K secure_min (4b each) + the K-1 nodes of the balanced argmax (geq 3b
    //     + value MUX b + index MUX idx_bits), independent of the outcome.
    let and_gates = k * (4 * b) + k.saturating_sub(1) * (4 * b + idx_bits);
    for _ in 0..(2 * and_gates) {
        tr.masked.push(rng.gen_range(0..=1));
    }
    tr.and_gates = and_gates;
    tr.rounds = crossing_rounds(k, b);
    // (b) p* index bits — determined by p* alone (0 when the book never clears).
    let idx = cross.p_star.unwrap_or(0);
    tr.revealed_pstar = (0..idx_bits).map(|i| ((idx >> i) & 1) as u8).collect();
    // (c) V* bits — determined by V* alone (0 when no clear).
    tr.revealed_vstar = (0..b).map(|i| ((cross.v_star >> i) & 1) as u8).collect();
    tr
}

// ===========================================================================
// PURE-MPC INFORMATION-THEORETIC FOLD — Tier-0 "unconditional no-viewer".
//
// The output-boundary construction above folds under BFV (an LWE/RLWE —
// COMPUTATIONAL — scheme) and only shares at the boundary; below the threshold
// its no-viewer rests on LWE hardness for the fold. This block removes the
// computational assumption from the FOLD entirely:
//
//   * Each order's per-bucket contribution is additively secret-shared DIRECTLY
//     over the ring Z_{2^b} (`share_arith`). Any coalition of ≤ n-1 parties sees
//     shares that are UNIFORM and PERFECTLY (information-theoretically)
//     independent of the secret — no assumption to break, secure against
//     UNBOUNDED compute. (Contrast: a BFV ciphertext of the same value is only
//     COMPUTATIONALLY hiding — an unbounded adversary recovers the plaintext by
//     breaking LWE.)
//   * The fold — aggregate demand/supply per bucket — is each party LOCALLY
//     summing its own shares mod 2^b (`fold_arith`): FREE, no communication, no
//     crypto, and the result is again a perfect additive sharing of the sum.
//   * To feed the existing boolean Beaver-triple comparator, the folded
//     arithmetic shares are converted to boolean shares once at the boundary
//     (`a2b`, a real MPC subprotocol — a secret-shared ripple-carry sum of the
//     parties' arithmetic shares). Then the UNCHANGED `mpc_crossing` runs and
//     reveals ONLY (p*, V*).
//
// Threshold (stated honestly): additive (n-of-n) sharing is PERFECTLY HIDING
// against any ≤ n-1 SEMI-HONEST parties given the (simulated-dealer) Beaver
// triples — the online phase opens only one-time-padded bits and is itself
// information-theoretically secure. Robust/malicious security and dealer-free
// IT triple generation are the classic HONEST-MAJORITY regime (t < n/2, BGW);
// SPDZ-style MACs push to all-but-one but put a computational assumption back in
// the (offline) preprocessing. All-collude reconstruction is unavoidable for
// clearing over hidden data — the theorem, not a gap. This PoC establishes the
// semi-honest, below-threshold, PERFECT-HIDING fold; §8 of the design doc keeps
// the malicious-secure + real-preprocessing frontier.
// ===========================================================================

/// An integer additively secret-shared over the ring `Z_{2^b}`: the cleartext is
/// `(Σ_i shares[i]) mod 2^b`. Any `n-1` shares are uniform over `Z_{2^b}` and
/// PERFECTLY independent of the secret (information-theoretic, not computational).
/// Share ADDITION is LOCAL — this is what makes the fold free and unconditional.
pub type ArithShare = Vec<u64>;

/// `2^b - 1` (the ring mask), or all-ones for `b ≥ 64`.
#[inline]
fn ring_mask(b: usize) -> u64 {
    if b >= 64 {
        u64::MAX
    } else {
        (1u64 << b) - 1
    }
}

/// Additively secret-share `value` over `Z_{2^b}` among `n` parties. The first
/// `n-1` shares are fresh uniform ring elements; the last absorbs the residue.
/// Perfect hiding: for EVERY secret, any `n-1` of the shares are uniform and
/// independent of it — demonstrated exactly by enumeration in the bench.
pub fn share_arith<R: Rng>(value: u64, b: usize, n: usize, rng: &mut R) -> ArithShare {
    let m = ring_mask(b);
    assert!(
        b >= 64 || value <= m,
        "value {value} overflows {b}-bit ring"
    );
    let mut v = vec![0u64; n];
    let mut acc = 0u64;
    for s in v.iter_mut().take(n - 1) {
        let r = rng.gen::<u64>() & m;
        *s = r;
        acc = acc.wrapping_add(r) & m;
    }
    v[n - 1] = value.wrapping_sub(acc) & m;
    v
}

/// Reconstruct an arithmetic sharing to its cleartext `(Σ shares) mod 2^b`.
pub fn open_arith(shares: &ArithShare, b: usize) -> u64 {
    let m = ring_mask(b);
    shares.iter().fold(0u64, |a, &s| a.wrapping_add(s & m) & m)
}

/// THE INFORMATION-THEORETIC FOLD — each party LOCALLY sums its own shares of the
/// per-order contributions mod `2^b`. No communication, no crypto, no LWE: FREE.
/// The output is again a perfect additive sharing (of the aggregate). This is the
/// unconditional replacement for `additive::bfv_fold`.
pub fn fold_arith(order_shares: &[ArithShare], n: usize, b: usize) -> ArithShare {
    let m = ring_mask(b);
    let mut acc = vec![0u64; n];
    for sh in order_shares {
        for (a, &s) in acc.iter_mut().zip(sh) {
            *a = a.wrapping_add(s) & m;
        }
    }
    acc
}

/// Secure ADD of two `b`-bit boolean-shared integers, `(x + y) mod 2^b`, via a
/// secret-shared ripple-carry adder. `sum_i = x_i ⊕ y_i ⊕ c_i`; the 1-AND carry
/// `c_{i+1} = c_i ⊕ (x_i ⊕ c_i)·(y_i ⊕ c_i)`. `b-1` AND gates, depth `b`.
pub fn secure_add(
    x: &SharedInt,
    y: &SharedInt,
    pool: &mut TriplePool,
    tr: &mut Transcript,
) -> SharedInt {
    let bits = x.len();
    let n = x[0].len();
    let mut carry = share_const(0, n);
    let mut out = Vec::with_capacity(bits);
    for i in 0..bits {
        out.push(xor(&xor(&x[i], &y[i]), &carry));
        if i + 1 < bits {
            let xc = xor(&x[i], &carry);
            let yc = xor(&y[i], &carry);
            let t = pool.take().clone();
            let prod = and_gate(&xc, &yc, &t, tr);
            carry = xor(&carry, &prod);
        }
    }
    out
}

/// ARITHMETIC → BOOLEAN share conversion (A2B), the one boundary bridge between
/// the free arithmetic fold and the boolean comparator. Each party `i` locally
/// boolean-shares its own arithmetic share `x_i` (it knows it in the clear); the
/// `n` boolean-shared values are then summed with `secure_add` (a balanced adder
/// tree in deployment) to yield the boolean sharing of `x = Σ x_i mod 2^b`.
/// Cost: `(n-1)·(b-1)` AND gates; depth `⌈log₂ n⌉·b`.
pub fn a2b<R: Rng>(
    arith: &ArithShare,
    b: usize,
    pool: &mut TriplePool,
    tr: &mut Transcript,
    rng: &mut R,
) -> SharedInt {
    let n = arith.len();
    let m = ring_mask(b);
    let mut acc = share_int(arith[0] & m, b, n, rng);
    for share in arith.iter().skip(1) {
        let xi = share_int(share & m, b, n, rng);
        acc = secure_add(&acc, &xi, pool, tr);
    }
    acc
}

/// `⌈log₂ n⌉` — the adder-tree depth for summing `n` party values in A2B.
fn ceil_log2(n: usize) -> usize {
    let mut d = 0usize;
    let mut x = 1usize;
    while x < n {
        x <<= 1;
        d += 1;
    }
    d
}

/// Triples one PURE crossing consumes: `2·K` A2B conversions (demand + supply),
/// each `(n-1)·(b-1)` ANDs, plus the boolean crossing (`triples_needed`).
pub fn triples_needed_pure(k: usize, b: usize, n: usize) -> usize {
    2 * k * (n - 1) * (b - 1) + triples_needed(k, b)
}

/// The result of one PURE-MPC (information-theoretic-fold) crossing, with the
/// phase timings that make the "fold is now free" claim measurable.
pub struct PureRun {
    pub cross: Crossing,
    pub transcript: Transcript,
    /// Wall time of the FOLD (local share addition). Essentially zero — no crypto.
    pub fold: Duration,
    /// Wall time of the A2B boundary conversion (the only added MPC vs. the fold).
    pub a2b: Duration,
    /// Wall time of the boolean crossing (identical to the BFV-path crossing).
    pub crossing: Duration,
    pub triples_used: usize,
    pub a2b_and_gates: usize,
    pub crossing_and_gates: usize,
}

/// THE PURE-MPC CROSSING — no BFV, no LWE anywhere in the fold path. Shares each
/// order's per-bucket increment directly (`share_arith`), folds LOCALLY
/// (`fold_arith`, free + information-theoretic), converts the aggregate to boolean
/// shares (`a2b`), then runs the UNCHANGED `mpc_crossing`, revealing only (p*,V*).
pub fn cross_book_pure<R: Rng>(
    orders: &[Order],
    k: usize,
    b: usize,
    n: usize,
    rng: &mut R,
) -> PureRun {
    let mut pool = TriplePool::generate(triples_needed_pure(k, b, n), n, rng);

    // (1) Trader-side: expand each order to its K-bucket unary increment and
    //     additively secret-share EACH bucket contribution over Z_{2^b}. Demand =
    //     bids, supply = asks. No party ever holds a plaintext increment.
    let mut demand_orders: Vec<Vec<ArithShare>> = Vec::new();
    let mut supply_orders: Vec<Vec<ArithShare>> = Vec::new();
    for o in orders {
        let inc = order_increment(o, k);
        let shared: Vec<ArithShare> = inc
            .iter()
            .map(|&q| share_arith(q as u64, b, n, rng))
            .collect();
        match o.side {
            Side::Bid => demand_orders.push(shared),
            Side::Ask => supply_orders.push(shared),
        }
    }

    // (2) THE FOLD — LOCAL per-party sum of shares, per bucket. FREE + UNCONDITIONAL.
    let fold_one = |orders: &[Vec<ArithShare>]| -> Vec<ArithShare> {
        (0..k)
            .map(|p| {
                let col: Vec<ArithShare> = orders.iter().map(|o| o[p].clone()).collect();
                if col.is_empty() {
                    vec![0u64; n]
                } else {
                    fold_arith(&col, n, b)
                }
            })
            .collect()
    };
    let t0 = Instant::now();
    let d_arith = fold_one(&demand_orders);
    let s_arith = fold_one(&supply_orders);
    let fold_dt = t0.elapsed();

    // (3) A2B — the one boundary bridge to the boolean comparator.
    let mut tr = Transcript::default();
    let t0 = Instant::now();
    let d_shared: Vec<SharedInt> = d_arith
        .iter()
        .map(|a| a2b(a, b, &mut pool, &mut tr, rng))
        .collect();
    let s_shared: Vec<SharedInt> = s_arith
        .iter()
        .map(|a| a2b(a, b, &mut pool, &mut tr, rng))
        .collect();
    let a2b_dt = t0.elapsed();
    let a2b_ands = tr.and_gates;
    // A2B depth: n party-values summed by a balanced adder tree, buckets parallel.
    tr.rounds += ceil_log2(n) * b;

    // (4) THE CROSSING — the existing Beaver-triple GEQ crossing, unchanged.
    let t0 = Instant::now();
    let cross = mpc_crossing(&d_shared, &s_shared, &mut pool, &mut tr);
    let crossing_dt = t0.elapsed();
    let crossing_ands = tr.and_gates - a2b_ands;

    PureRun {
        cross,
        transcript: tr,
        fold: fold_dt,
        a2b: a2b_dt,
        crossing: crossing_dt,
        triples_used: pool.consumed(),
        a2b_and_gates: a2b_ands,
        crossing_and_gates: crossing_ands,
    }
}

// ---------------------------------------------------------------------------
// The PERFECT-HIDING demonstration — the load-bearing information-theoretic
// property, shown EXACTLY (by enumeration), not statistically.
// ---------------------------------------------------------------------------

/// Enumerate the FULL randomness space of `share_arith(secret, b, n)` and return
/// the exact histogram of what a `coalition` (a set of party indices, size ≤ n-1)
/// observes. If, for two different secrets, these histograms are IDENTICAL, the
/// coalition's view is provably independent of the secret — PERFECT (information-
/// theoretic) hiding, secure against unbounded compute. (For additive sharing the
/// histogram is in fact the uniform "every tuple exactly once" for any size-`n-1`
/// coalition and any secret — this function proves it rather than asserting it.)
///
/// Randomness = the free shares `(r_0..r_{n-2}) ∈ Z_{2^b}^{n-1}`; the last share is
/// `secret - Σ r`. Only feasible for small `b·(n-1)`; use `b ≤ 8`, `n ≤ 3`.
pub fn coalition_view_histogram(
    secret: u64,
    b: usize,
    n: usize,
    coalition: &[usize],
) -> std::collections::BTreeMap<Vec<u64>, u64> {
    let m = ring_mask(b);
    let size = (m as u128 + 1) as u64; // 2^b
    let free = n - 1; // number of free shares r_0..r_{n-2}
    let mut hist: std::collections::BTreeMap<Vec<u64>, u64> = std::collections::BTreeMap::new();
    // Enumerate all (r_0..r_{free-1}) ∈ [0,2^b)^{free}.
    let total: u128 = (size as u128).pow(free as u32);
    for idx in 0..total {
        let mut shares = vec![0u64; n];
        let mut rem = idx;
        let mut acc = 0u64;
        for s in shares.iter_mut().take(free) {
            let r = (rem % size as u128) as u64;
            rem /= size as u128;
            *s = r;
            acc = acc.wrapping_add(r) & m;
        }
        shares[n - 1] = secret.wrapping_sub(acc) & m;
        let view: Vec<u64> = coalition.iter().map(|&i| shares[i]).collect();
        *hist.entry(view).or_insert(0) += 1;
    }
    hist
}

#[cfg(test)]
mod pure_tests {
    use super::*;
    use crate::{reference_clear, Order, Side};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    fn arith_share_roundtrips_and_folds_locally() {
        let mut rng = StdRng::seed_from_u64(1);
        let b = 16;
        // A perfect additive sharing reconstructs, and LOCAL fold == plaintext sum.
        let vals = [3u64, 40, 7, 255, 1000];
        let shares: Vec<ArithShare> = vals
            .iter()
            .map(|&v| share_arith(v, b, 4, &mut rng))
            .collect();
        for (&v, sh) in vals.iter().zip(&shares) {
            assert_eq!(open_arith(sh, b), v);
        }
        let folded = fold_arith(&shares, 4, b);
        assert_eq!(open_arith(&folded, b), vals.iter().sum::<u64>());
    }

    #[test]
    fn perfect_hiding_is_exact_and_secret_independent() {
        // Every size-(n-1) coalition sees a view whose EXACT distribution is
        // identical for different secrets — perfect (information-theoretic) hiding.
        let (b, n) = (8usize, 3usize);
        for coal in [vec![0usize, 1], vec![0, 2], vec![1, 2]] {
            let h0 = coalition_view_histogram(0, b, n, &coal);
            let h199 = coalition_view_histogram(199, b, n, &coal);
            assert_eq!(h0, h199, "coalition view depends on the secret");
            let counts: std::collections::BTreeSet<u64> = h0.values().copied().collect();
            assert_eq!(counts.len(), 1, "coalition view is not uniform");
        }
    }

    #[test]
    fn mpc_crossing_workbook_and_counter_witness() {
        // The shared uniform-price rule on the two named witnesses, run through the
        // real secret-shared Beaver-triple crossing (share curves -> MPC argmax).
        let mut rng = StdRng::seed_from_u64(11);
        // workbook: min=(3,8,6) => p*=1, V*=8.
        let (c, tr, _) = cross_curves(&[10u64, 10, 6], &[3u64, 8, 8], 16, 3, &mut rng);
        assert_eq!(c.p_star, Some(1));
        assert_eq!(c.v_star, 8);
        assert!(tr.is_reveal_only(3, 16));
        let mut extra_output = tr.clone();
        extra_output.revealed_vstar.push(0);
        assert!(
            !extra_output.is_reveal_only(3, 16),
            "an appended unmasked output bit must break the leakage tooth"
        );
        let mut extra_open = tr.clone();
        extra_open.masked.push(0);
        assert!(
            !extra_open.is_reveal_only(3, 16),
            "an unaccounted masked opening must break the transcript schema"
        );
        let mut noncanonical = tr.clone();
        noncanonical.revealed_pstar[0] = 2;
        assert!(!noncanonical.is_reveal_only(3, 16));
        // counter-witness that BREAKS largest-crossing: min=(5,9) => p*=1, V*=9.
        let (c2, _, _) = cross_curves(&[10u64, 9], &[5u64, 20], 16, 3, &mut rng);
        assert_eq!(c2.p_star, Some(1));
        assert_eq!(c2.v_star, 9);
        // a genuinely-no-clear book (no asks) => V*=0 => None.
        let (c3, _, _) = cross_curves(&[10u64, 8], &[0u64, 0], 16, 3, &mut rng);
        assert_eq!(c3.p_star, None);
        assert_eq!(c3.v_star, 0);
    }

    #[test]
    fn balanced_argmax_preserves_lowest_index_ties_in_odd_brackets() {
        let mut rng = StdRng::seed_from_u64(0x71E_B0A7);

        // An all-way tie must survive every left-vs-right merge as index zero.
        let all_tied = [9u64; 5];
        let (c0, _, _) = cross_curves(&all_tied, &all_tied, 8, 3, &mut rng);
        assert_eq!(
            c0,
            Crossing {
                p_star: Some(0),
                v_star: 9
            }
        );

        // Equal maxima meet both inside a pair and across tournament levels.
        let middle_tie = [1u64, 7, 7, 7, 7];
        let (c1, _, _) = cross_curves(&middle_tie, &middle_tie, 8, 3, &mut rng);
        assert_eq!(
            c1,
            Crossing {
                p_star: Some(1),
                v_star: 7
            }
        );

        // Index 4 is the odd carry out of level zero. When it later ties index 3,
        // the ordered-subtree invariant must still select the lower index 3.
        let carried_tie = [1u64, 1, 1, 11, 11];
        let (c2, _, _) = cross_curves(&carried_tie, &carried_tie, 8, 3, &mut rng);
        assert_eq!(
            c2,
            Crossing {
                p_star: Some(3),
                v_star: 11
            }
        );

        // This is the mutation tooth: changing the merge predicate from `>=` to
        // strict `>` selects the right-hand index 4 in every witness above.
    }

    #[test]
    fn balanced_crossing_matches_reference_for_power_and_non_power_shapes() {
        let mut rng = StdRng::seed_from_u64(0xBA1A_CED);
        for &k in &[1usize, 2, 3, 5, 7, 8, 9, 31, 64, 65, 255, 256] {
            for trial in 0..3 {
                let n_orders = 12 + trial * 7;
                let book: Vec<Order> = (0..n_orders)
                    .map(|_| Order {
                        side: if rng.gen::<bool>() {
                            Side::Bid
                        } else {
                            Side::Ask
                        },
                        limit: rng.gen_range(0..k),
                        qty: rng.gen_range(1..=31),
                    })
                    .collect();
                let reference = reference_clear(&book, k);
                let demand: Vec<u64> = reference.demand.iter().map(|&v| v as u64).collect();
                let supply: Vec<u64> = reference.supply.iter().map(|&v| v as u64).collect();
                let (got, tr, used) = cross_curves(&demand, &supply, 16, 3, &mut rng);

                assert_eq!(got.p_star, reference.p_star, "K={k}, trial={trial}");
                assert_eq!(got.v_star, reference.v_star as u64, "K={k}, trial={trial}");
                assert_eq!(tr.rounds, crossing_rounds(k, 16));
                assert_eq!(used, tr.and_gates);
                assert_eq!(
                    used,
                    k * (4 * 16) + k.saturating_sub(1) * (4 * 16 + index_bits(k))
                );
                assert!(tr.is_reveal_only(k, 16));
            }
        }
    }

    #[test]
    fn balanced_round_ledger_is_logarithmic_not_sequential() {
        let b = 16;
        let r64 = crossing_rounds(64, b);
        let r256 = crossing_rounds(256, b);
        assert_eq!(r64, 119);
        assert_eq!(r256, 153);
        assert_eq!(r256 - r64, 2 * (b + 1));

        let old_sequential = |k: usize| 3 * b + (k - 1) * (3 * b + index_bits(k));
        assert!(r64 < old_sequential(64) / 20);
        assert!(r256 < old_sequential(256) / 80);

        // Different secrets with the same public shape execute exactly the same
        // gate/opening schedule; only their one-time-padded masked bits differ.
        let mut rng = StdRng::seed_from_u64(0xD47A_0B1E);
        let zeros = vec![0u64; 65];
        let ramp: Vec<u64> = (0..65).map(|i| i as u64).collect();
        let (cz, tz, _) = cross_curves(&zeros, &zeros, b, 3, &mut rng);
        let (_, tr, _) = cross_curves(&ramp, &ramp, b, 3, &mut rng);
        assert_eq!(tz.and_gates, tr.and_gates);
        assert_eq!(tz.masked.len(), tr.masked.len());
        assert_eq!(tz.rounds, tr.rounds);

        let simulated = simulate(&cz, 65, b, &mut rng);
        assert_eq!(simulated.and_gates, tz.and_gates);
        assert_eq!(simulated.masked.len(), tz.masked.len());
        assert_eq!(simulated.rounds, tz.rounds);
    }

    #[test]
    fn pure_crossing_matches_plaintext() {
        let mut rng = StdRng::seed_from_u64(7);
        let k = 48;
        let book: Vec<Order> = (0..64)
            .map(|i| Order {
                side: if i % 2 == 0 { Side::Bid } else { Side::Ask },
                limit: (i * 5) % k,
                qty: 1 + (i as u16 % 6),
            })
            .collect();
        let reference = reference_clear(&book, k);
        let run = cross_book_pure(&book, k, 16, 4, &mut rng);
        assert_eq!(run.cross.p_star, reference.p_star);
        assert_eq!(run.cross.v_star as u32, reference.v_star);
        assert!(run.transcript.is_reveal_only(k, 16));
    }
}

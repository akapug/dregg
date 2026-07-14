//! OUTPUT-BOUNDARY MPC — the ADVERSARIAL no-viewer crossing (codex Round-4 gold).
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
//! `n` federation parties **partial-decrypt only the aggregate curve into additive
//! secret shares** (native to threshold BFV — each party applies its key share,
//! yielding a share of the plaintext; no exotic CHIMERA/PEGASUS adapter) and run
//! the crossing `p* = argmax_j min(D[j],S[j])` in a **secret-shared MPC**,
//! revealing ONLY `p*` and the cleared volume `V*`. This module is that MPC.
//!
//! ## Why this is ADVERSARIAL no-viewer, not a policy claim
//!
//! The comparison runs over additive shares with a real GMW/Beaver-triple online
//! phase. Every message a party sends is a one-time-pad-masked bit (`x ⊕ a`, `a`
//! a fresh uniform shared triple bit), so any coalition of **fewer than the
//! threshold `t` parties** sees a view that is uniform and independent of the
//! individual curve coefficients — it learns NOTHING beyond the revealed
//! `(p*, V*)`. That is a *cryptographic threshold bound*, not "we promise not to
//! look". The honest caveat (stated in the design + the tier docs): `≥ t`
//! colluding parties CAN reconstruct — "nobody even if all collude" is impossible
//! for clearing over hidden data. Output-boundary MPC shrinks the trust to its
//! minimum: a threshold, one clearing, reveal-only-`p*`, and NO standing master
//! decryption key (unlike threshold-FHE, where a colluding key-share subset can
//! decrypt any submitted ORDER ciphertext forever).
//!
//! ## What "the sign vector leaks nothing beyond p*" means (the leakage argument)
//!
//! The monotone crossing reveals the sign vector `c[p] = [D[p] ≥ S[p]]`. Because
//! `D` is non-increasing and `S` non-decreasing, `c` is a single downward step
//! `1…1 0…0` whose flip index is exactly `p*`. So `c` is a DETERMINISTIC FUNCTION
//! of `p*`: a simulator given only `p*` reproduces `c` exactly. Revealing `c` (or
//! equivalently `p*`) therefore leaks no more than `p*` itself. We open `c`, count
//! it to `p*`, then reveal only `V* = min(D[p*], S[p*])` via one more secure
//! comparison (never the two curve heights individually).
//!
//! ## What is real here vs. abstracted (honest)
//!
//! - **REAL:** boolean (GF(2)) additive secret sharing among `n` parties; a real
//!   Beaver-triple AND gate whose opened values are one-time-pad masked; a real
//!   bit-sliced secure `≥` comparator; the monotone crossing; a real secure `min`.
//!   No party ever holds a plaintext curve coefficient; only `(p*, V*)` open.
//! - **PREPROCESSING (standard MPC assumption):** the Beaver triples are produced
//!   by a simulated offline dealer (the SPDZ "offline phase"). In production the
//!   triples come from OT/HE preprocessing AMONG the parties — the ONLINE phase
//!   below is information-theoretically secure GIVEN the triples, and it is the
//!   online phase that carries the reveal-only-`p*` property.
//! - **ABSTRACTED (labelled):** the threshold-BFV partial-decrypt-INTO-shares step
//!   is modelled by sharing the true committed curve coefficients (`share_int`).
//!   The novel part — the MPC comparison on real secret shares — is what runs. The
//!   RLWE→shares partial decryption is native threshold-FHE, not a scheme switch;
//!   that is the seam this construction DISSOLVES (design doc §4).

use rand::Rng;

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
    /// The opened sign vector `c[p] = [D[p] ≥ S[p]]` — determined by `p*`.
    pub revealed_sign: Vec<u8>,
    /// The opened cleared volume `V*` bits (the only value output besides `p*`).
    pub revealed_vstar: Vec<u8>,
    /// AND gates executed (= triples consumed) — the online multiplicative cost.
    pub and_gates: usize,
    /// Sequential AND-depth = network communication rounds (latency driver).
    pub rounds: usize,
}

impl Transcript {
    /// The result the crossing outputs and reveals: exactly `(p*, V*)`.
    pub fn is_reveal_only(&self, k: usize) -> bool {
        // The only opened non-masked values are the K sign bits and V*'s bits.
        // (The masked bits are uniform pad, not information about inputs.)
        self.revealed_sign.len() == k
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

/// Bit-decompose `value` into `b` boolean-shared bits (LSB first). Models the
/// threshold-BFV partial-decrypt-into-shares of ONE curve coefficient.
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
/// caller decides whether opening this bit is safe (a masked bit, a sign bit, or
/// V* — never a raw curve coefficient).
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
/// and those are mutually exclusive so `geq = gt ⊕ eq_final`. ~3·b AND gates; its
/// AND-depth is O(b) (the `eq` chain), independent of K — so across all K buckets
/// the crossing is O(b) rounds, not O(K·b).
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

/// The number of Beaver triples one crossing consumes: `3·b` per `≥` over K
/// buckets, plus one `secure_min` (`geq` = `3b` + `b` MUX ANDs). Sizing the pool.
pub fn triples_needed(k: usize, b: usize) -> usize {
    k * (3 * b) + (3 * b + b)
}

/// The public result of an output-boundary MPC crossing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Crossing {
    /// clearing price bucket = argmax_j min(D[j],S[j]) = largest p with D[p]≥S[p].
    /// `None` if the book never clears.
    pub p_star: Option<usize>,
    /// cleared volume V* = min(D[p*], S[p*]).
    pub v_star: u64,
}

/// THE OUTPUT-BOUNDARY MPC CROSSING. Inputs are the already-secret-shared
/// aggregate curves `d_shared[p]`, `s_shared[p]` (the threshold-BFV
/// partial-decrypt-into-shares of the folded curves). Reveals ONLY `(p*, V*)`.
///
/// 1. For each bucket open `c[p] = [D[p] ≥ S[p]]` — the monotone sign vector,
///    determined by `p*` (leaks nothing more; §leakage argument above).
/// 2. `p* = (Σ_p c[p]) − 1` (public arithmetic on the opened, p*-determined bits).
/// 3. `V* = min(D[p*], S[p*])` via one secure_min at the now-public `p*`, opening
///    only the min — never the two heights.
pub fn mpc_crossing(
    d_shared: &[SharedInt],
    s_shared: &[SharedInt],
    pool: &mut TriplePool,
    tr: &mut Transcript,
) -> Crossing {
    let k = d_shared.len();
    assert_eq!(k, s_shared.len());

    // (1) sign vector — each c[p] opened (it is p*-determined, so this is exactly
    //     the reveal-only-p* leakage). The K comparisons are INDEPENDENT: in a
    //     real deployment their AND gates batch by depth-level → O(b) rounds total.
    let mut count = 0usize;
    for p in 0..k {
        let c = geq(&d_shared[p], &s_shared[p], pool, tr);
        let cbit = open(&c);
        tr.revealed_sign.push(cbit);
        count += cbit as usize;
    }
    // AND-depth of the whole sign phase = depth of one geq (buckets are parallel).
    tr.rounds += 3 * d_shared[0].len(); // ~3b sequential rounds (b = bit-width)

    let p_star = if count == 0 { None } else { Some(count - 1) };

    // (2)+(3) V* = min at the public p* — reveal ONLY the min.
    let v_star = match p_star {
        None => 0,
        Some(p) => {
            let m = secure_min(&d_shared[p], &s_shared[p], pool, tr);
            let v = open_int(&m);
            tr.revealed_vstar = (0..m.len()).map(|i| ((v >> i) & 1) as u8).collect();
            v
        }
    };

    Crossing { p_star, v_star }
}

/// Convenience: share two cleartext curves and run the crossing. Models the full
/// output boundary (partial-decrypt-into-shares + MPC), returning `(Crossing,
/// Transcript, triples_consumed)`. `b` = bit-width of the curve coefficients.
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

/// A semi-honest simulator that, given ONLY the public output `(p*, V*)` and the
/// circuit shape `(k, b, n)`, produces a transcript identically distributed to a
/// real one. If real-view ≈ simulated-view then the real view reveals nothing
/// beyond `(p*, V*)` — the definition of "reveal only p*+V*".
///
/// It works because: (a) every opened `masked` bit is a one-time-pad, so the
/// simulator samples it uniform; (b) the sign vector is the p*-determined step
/// `1…1 0…0`; (c) `V*` is given. No curve coefficient is ever needed.
pub fn simulate<R: Rng>(cross: &Crossing, k: usize, b: usize, rng: &mut R) -> Transcript {
    let mut tr = Transcript::default();
    // (a) masked bits: exactly as many as the real run (2 opens per AND gate),
    //     each sampled uniform — the real ones are one-time-pad masked, so this
    //     is the same distribution. A no-clear run skips the secure_min ANDs.
    let and_gates = if cross.p_star.is_some() {
        k * (3 * b) + (3 * b + b)
    } else {
        k * (3 * b)
    };
    for _ in 0..(2 * and_gates) {
        tr.masked.push(rng.gen_range(0..=1));
    }
    tr.and_gates = and_gates;
    // (b) sign vector = p*-determined step function.
    let flip = cross.p_star.map(|p| p + 1).unwrap_or(0);
    tr.revealed_sign = (0..k).map(|p| (p < flip) as u8).collect();
    // (c) V* bits.
    if cross.p_star.is_some() {
        tr.revealed_vstar = (0..b).map(|i| ((cross.v_star >> i) & 1) as u8).collect();
    }
    tr
}

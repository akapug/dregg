//! Native Metal (MSL) BabyBear NTT — the hand-tuned M2 Max kernel, measured
//! head-to-head against the TUNED wgpu/WGSL probe (`../wgpu-babybear-ntt`,
//! post zero-init/bounds-check fixes: 55-97% of copy ceiling).
//!
//! Native levers exercised here (MEASURED verdicts inline):
//!   1. NATIVE wide multiply — `mulhi(u32,u32)`: the p3 monty-31 reduce is 4
//!      hardware muls (WGSL pays a 16-bit-split emulation, ~9+ muls).
//!      ALU probe: ~320 Gmul/s native vs 60-106 for the WGSL split — a real
//!      3-5x ALU win that buys ~NOTHING end-to-end (the NTT is bandwidth-
//!      bound; butterfly math hides entirely behind memory).
//!   2. Coalesced pass structure (four-step style): pass A (K_FA) reads
//!      global rows LINEARLY (bit-reversal folded into the threadgroup-tile
//!      write, where scatter is cheap) and runs stages 1..B1 in an 8 KB tile
//!      (small tile = occupancy; this pass1 went 135 -> 186 GB/s vs the
//!      old bitrev-read + 32 KB-tile version); register-tier RADIX passes do
//!      R<=5 stages in registers, zero threadgroup memory. fa8/8 + radix
//!      chains are the winning plans on every shape. Generic MID passes
//!      (threadgroup butterflies) lose to RADIX everywhere.
//!   3. simdgroup shuffles — 32-wide `simd_shuffle_xor` butterflies (`simd`
//!      MID/F1 variants): measured SLOWER than plain threadgroup butterflies
//!      on every shape (the kernel is memory-bound; the shuffle re-gathers
//!      cost more than the barriers they remove).
//!   4. uint4 vectorization — K_FA4 (16 B/lane global load/store): neutral
//!      (scalar u32 access already saturates the same ~180 GB/s pass-1
//!      plateau). K_RADIX4 (vector radix): SLOWER (register pressure +
//!      per-component twiddle gathers). The copy ceiling needs uint4; the
//!      NTT passes don't benefit.
//!   5. Threadgroup-width tuning (RadixW /1024): neutral. NOTE: exceeding a
//!      pipeline's register-limited maxTotalThreadsPerThreadgroup silently
//!      drops threads — the parity gate catches it; the builder clamps.
//!   6. Legacy 2-pass fused plans (the v1 shape, strided pass-1 loads) kept
//!      for the technique-by-technique attribution.
//!
//!   7. tw2 split twiddles (PORTED FROM THE WGPU PROBE — an API-neutral
//!      algorithmic lever, not a native one): TW(i) = mmul(tw_hi[i>>S],
//!      tw_lo[i&mask]) confines the strided passes' twiddle gathers to two
//!      cache-resident tables (direct tw[j << big_shift] touches one distinct
//!      line per lane of a 4 MiB table). THE biggest single end-to-end lever
//!      measured here: radix passes went ~215-235 -> 360-610 GB/s, whole-NTT
//!      times improved 15-25%. Parity stays bit-exact (Montgomery product of
//!      canonical Montgomery forms).
//!
//! OUTCOME (M2 Max, interleaved A/B/A/B vs the tuned wgpu probe, both
//! carrying tw2): a SPLIT DECISION inside +-15% — wgpu wins the two 2^15
//! batch shapes by ~6-13%, native wins 2^18x16 / 2^21x1 / 2^21x8 by ~3-14%;
//! run-to-run variance on this shared machine is of the same order. Both
//! plateau at the same structural wall: the four-step first pass (strided
//! row gather + bitrev tile fold) runs at 45-56% of copy bandwidth on this
//! memory system regardless of API, and everything after it is pass-count.
//! No native-ONLY lever (mulhi ALU, simdgroup shuffles, uint4, occupancy
//! hints) moves the end-to-end number materially: the kernel is bandwidth-
//! bound, and the portable wgpu backend is NOT leaving meaningful Apple-GPU
//! performance on the table. Verdict: stay portable — one wgpu backend, no
//! native-Metal seam.
//!
//! Parity discipline identical to the wgpu probe: every plan is value-exact
//! against pinned Plonky3 rev 82cfad7 `Radix2DitParallel` on every shape
//! before it is timed; data stays in Montgomery form end-to-end.
//!
//! Run: `cargo run --release` (this crate opts out of the root workspace).

use metal::{
    Buffer, CommandQueue, CompileOptions, ComputePipelineState, Device, MTLResourceOptions, MTLSize,
};
use objc::rc::autoreleasepool;
use p3_baby_bear::BabyBear;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::integers::QuotientMap;
use p3_field::{PrimeField32, TwoAdicField};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rand::Rng;

const P: u32 = 0x7800_0001; // BabyBear prime
const MU: u32 = 0x8800_0001; // P^{-1} mod 2^32 (p3 MONTY_MU)
const SPEC_BW: f64 = 400.0e9; // Apple spec: M2 Max unified memory bandwidth

// ---------- host-side BabyBear helpers (identical to the wgpu probe) ----------

fn to_mont(a: u32) -> u32 {
    (((a as u64) << 32) % P as u64) as u32
}

fn montmul(a: u32, b: u32) -> u32 {
    let x = a as u64 * b as u64;
    let t = (x as u32).wrapping_mul(MU);
    let u = t as u64 * P as u64;
    let xhi = (x >> 32) as u32;
    let uhi = (u >> 32) as u32;
    let (r, borrow) = xhi.overflowing_sub(uhi);
    if borrow {
        r.wrapping_add(P)
    } else {
        r
    }
}

fn from_mont(a: u32) -> u32 {
    montmul(a, 1)
}

fn mulmod(a: u64, b: u64) -> u64 {
    a * b % P as u64
}

fn powmod(mut b: u64, mut e: u64) -> u64 {
    let mut acc = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            acc = mulmod(acc, b);
        }
        b = mulmod(b, b);
        e >>= 1;
    }
    acc
}

fn bitrev(i: u32, bits: u32) -> u32 {
    i.reverse_bits() >> (32 - bits)
}

/// Reference radix-2 DIT NTT in canonical form (convention lock vs p3).
fn cpu_ref_ntt(x: &[u32], logn: u32) -> Vec<u32> {
    let n = 1usize << logn;
    assert_eq!(x.len(), n);
    let w = BabyBear::two_adic_generator(logn as usize).as_canonical_u32() as u64;
    let mut a: Vec<u64> = (0..n)
        .map(|i| x[bitrev(i as u32, logn) as usize] as u64)
        .collect();
    for s in 1..=logn {
        let m = 1usize << s;
        let wm = powmod(w, (n >> s) as u64);
        for k in (0..n).step_by(m) {
            let mut t = 1u64;
            for j in 0..m / 2 {
                let v = mulmod(t, a[k + j + m / 2]);
                let u = a[k + j];
                a[k + j] = (u + v) % P as u64;
                a[k + j + m / 2] = (u + P as u64 - v) % P as u64;
                t = mulmod(t, wm);
            }
        }
    }
    a.into_iter().map(|v| v as u32).collect()
}

// ---------- MSL ----------

const PRELUDE: &str = r#"
#include <metal_stdlib>
using namespace metal;

constant uint P = 0x78000001u;
constant uint MU = 0x88000001u;

// Montgomery product, exactly the p3 monty-31 reduce, on NATIVE wide muls:
// r = hi(a*b) - hi((lo(a*b)*MU)*P), +P on borrow. 4 hardware 32-bit muls.
inline uint mmul(uint a, uint b) {
    uint hi = mulhi(a, b);
    uint t = (a * b) * MU;
    uint tp = mulhi(t, P);
    uint r = hi - tp;
    return (hi < tp) ? r + P : r;
}

inline uint addp(uint a, uint b) { uint s = a + b; return (s >= P) ? s - P : s; }
inline uint subp(uint a, uint b) { return (a < b) ? a - b + P : a - b; }

// vectorized (uint4) variants — mulhi/select are component-wise native
inline uint4 mmul4(uint4 a, uint4 b) {
    uint4 hi = mulhi(a, b);
    uint4 t = (a * b) * MU;
    uint4 tp = mulhi(t, P);
    uint4 r = hi - tp;
    return select(r, r + P, hi < tp);
}
inline uint4 addp4(uint4 a, uint4 b) { uint4 s = a + b; return select(s, s - P, s >= P); }
inline uint4 subp4(uint4 a, uint4 b) { return select(a - b, a - b + P, a < b); }

// threadgroup tile index swizzle (bank-conflict fold; identity when disabled)
inline uint swz(uint i) { return $SWZEXPR; }

// Twiddle accessor. Direct: TW(i) = tw[i]. Split ("tw2", from the wgpu probe):
// TW(i) = mmul(tw_hi[i>>S], tw_lo[i&(2^S-1)]) = mont(w^i) EXACTLY (Montgomery
// product of Montgomery forms; canonical residues, so parity is bit-identical).
// The point: strided radix/mid passes index tw[j << big_shift] — one distinct
// cache line PER LANE across the n/2-entry table (4 MiB at n=2^21). The split
// confines all twiddle reads to two small cache-resident tables.
inline uint TW(constant uint* tw, uint i) { return $TWEXPR; }
"#;

/// uint4 grid-strided copy: the achievable-bandwidth ceiling kernel.
const K_COPY4: &str = r#"
kernel void k_copy4(device uint4* dst [[buffer(0)]],
                    const device uint4* src [[buffer(1)]],
                    uint3 gid [[thread_position_in_grid]]) {
    uint i = gid.x;
    dst[i] = src[i];
    dst[i + $CSTRIDE] = src[i + $CSTRIDE];
    dst[i + 2u * $CSTRIDE] = src[i + 2u * $CSTRIDE];
    dst[i + 3u * $CSTRIDE] = src[i + 3u * $CSTRIDE];
}
"#;

/// Chained Montgomery-mul ALU probe (native mulhi vs the wgpu 16-bit split).
const K_MULBENCH: &str = r#"
kernel void k_mulbench(device uint* out [[buffer(0)]],
                       const device uint* src [[buffer(1)]],
                       uint3 gid [[thread_position_in_grid]]) {
    uint i = gid.x;
    uint x = src[i];
    uint y = src[i ^ 1u];
    for (uint k = 0u; k < 128u; k++) { x = mmul(x, y); }
    out[i] = x;
}
"#;

/// Bit-reversal gather: data[i] = src[rev(i)]; one column per gid.y.
const K_BITREV: &str = r#"
kernel void k_bitrev(device uint* data [[buffer(0)]],
                     const device uint* src [[buffer(1)]],
                     uint3 gid [[thread_position_in_grid]]) {
    uint i = gid.x;
    uint off = gid.y * $NN;
    data[off + i] = src[off + (reverse_bits(i) >> $RSH)];
}
"#;

/// One global DIT stage (multipass baseline; stage constants baked).
const K_STAGE: &str = r#"
kernel void k_stage(device uint* data [[buffer(0)]],
                    const device uint* src [[buffer(1)]],
                    constant uint* tw [[buffer(2)]],
                    uint3 gid [[thread_position_in_grid]]) {
    uint bf = gid.x;
    uint off = gid.y * $NN;
    uint j = bf & ($HALF - 1u);
    uint i1 = off + ((bf >> ($SS - 1u)) << $SS) + j;
    uint i2 = i1 + $HALF;
    uint t = mmul(data[i2], tw[j << $TSH]);
    uint u = data[i1];
    data[i1] = addp(u, t);
    data[i2] = subp(u, t);
}
"#;

/// PASS A — coalesced bitrev-fold + stages 1..B1 (four-step first pass).
/// tile = 2^B1 rows x NC columns; column c handles output block
/// z = rev(rz0+c). Loads: global rows are read in LINEAR order (u ascending;
/// the bit-reversal is folded into the threadgroup-tile write index, where
/// scatter is cheap) — for each row u the NC lanes read NC CONSECUTIVE global
/// addresses, and consecutive k iterations touch consecutive rows, so the
/// DRAM stream is fully sequential. Writes: lanes span u — contiguous
/// 2^B1-element runs per column. Reads src, writes data.
const K_FA: &str = r#"
kernel void k_fa(device uint* data [[buffer(0)]],
                 const device uint* src [[buffer(1)]],
                 constant uint* tw [[buffer(2)]],
                 uint lid [[thread_index_in_threadgroup]],
                 uint3 tg [[threadgroup_position_in_grid]]) {
    threadgroup uint tile[$TILE];
    uint off = tg.y * $NN;
    uint rz0 = tg.x * $NC;
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        uint c = sl & ($NC - 1u);
        uint u = sl >> $LNC;
        tile[swz(((reverse_bits(u) >> (32u - $B1)) << $LNC) + c)] =
            src[off + (u << ($LOGN - $B1)) + rz0 + c];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint s = 1u; s <= $B1; s++) {
        uint h = 1u << (s - 1u);
        for (uint k = 0u; k < $HBT; k++) {
            uint bfi = lid + k * $WGSZ;
            uint c = bfi & ($NC - 1u);
            uint qb = bfi >> $LNC;
            uint j = qb & (h - 1u);
            uint i1 = ((((qb >> (s - 1u)) << s) + j) << $LNC) + c;
            uint i2 = i1 + (h << $LNC);
            uint t = mmul(tile[swz(i2)], tw[j << ($LOGN - s)]);
            uint u2 = tile[swz(i1)];
            tile[swz(i1)] = addp(u2, t);
            tile[swz(i2)] = subp(u2, t);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        uint u = sl & ((1u << $B1) - 1u);
        uint c = sl >> $B1;
        uint z = reverse_bits(rz0 + c) >> (32u - ($LOGN - $B1));
        data[off + (z << $B1) + u] = tile[swz((u << $LNC) + c)];
    }
}
"#;

/// PASS A, uint4-vectorized global access: same schedule as K_FA but the
/// global load reads uint4 (16 B/lane; NC/4 vector-columns per row) and the
/// global store writes uint4 (4 consecutive u per lane). Butterfly stages are
/// identical scalar threadgroup code. Requires NC>=4, WW>=4, TILE/4>=WGSZ.
/// The swizzle must preserve aligned-4 runs (use SWZ_XOR4 / SWZ_ID).
const K_FA4: &str = r#"
kernel void k_fa4(device uint* data [[buffer(0)]],
                  const device uint* src [[buffer(1)]],
                  constant uint* tw [[buffer(2)]],
                  uint lid [[thread_index_in_threadgroup]],
                  uint3 tg [[threadgroup_position_in_grid]]) {
    threadgroup uint tile[$TILE];
    const device uint4* src4 = (const device uint4*)src;
    device uint4* data4 = (device uint4*)data;
    uint off4 = tg.y * ($NN >> 2u);
    uint rz0 = tg.x * $NC;
    for (uint k = 0u; k < $TPT4; k++) {
        uint sl = lid + k * $WGSZ;
        uint c4 = sl & (($NC >> 2u) - 1u);
        uint u = sl >> ($LNC - 2u);
        uint4 v = src4[off4 + (u << ($LOGN - $B1 - 2u)) + (rz0 >> 2u) + c4];
        uint tb = swz(((reverse_bits(u) >> (32u - $B1)) << $LNC) + (c4 << 2u));
        tile[tb] = v.x; tile[tb + 1u] = v.y; tile[tb + 2u] = v.z; tile[tb + 3u] = v.w;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint s = 1u; s <= $B1; s++) {
        uint h = 1u << (s - 1u);
        for (uint k = 0u; k < $HBT; k++) {
            uint bfi = lid + k * $WGSZ;
            uint c = bfi & ($NC - 1u);
            uint qb = bfi >> $LNC;
            uint j = qb & (h - 1u);
            uint i1 = ((((qb >> (s - 1u)) << s) + j) << $LNC) + c;
            uint i2 = i1 + (h << $LNC);
            uint t = mmul(tile[swz(i2)], tw[j << ($LOGN - s)]);
            uint u2 = tile[swz(i1)];
            tile[swz(i1)] = addp(u2, t);
            tile[swz(i2)] = subp(u2, t);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
    for (uint k = 0u; k < $TPT4; k++) {
        uint sl = lid + k * $WGSZ;
        uint u4 = sl & ((1u << ($B1 - 2u)) - 1u);
        uint c = sl >> ($B1 - 2u);
        uint z = reverse_bits(rz0 + c) >> (32u - ($LOGN - $B1));
        uint u0 = u4 << 2u;
        uint4 v = uint4(tile[swz(((u0     ) << $LNC) + c)],
                        tile[swz(((u0 + 1u) << $LNC) + c)],
                        tile[swz(((u0 + 2u) << $LNC) + c)],
                        tile[swz(((u0 + 3u) << $LNC) + c)]);
        data4[off4 + (z << ($B1 - 2u)) + u4] = v;
    }
}
"#;

/// Register-tier radix pass, uint4-vectorized: each thread owns 4 CONSECUTIVE
/// low-offset lanes (one uint4) of a closed 2^R butterfly group — 16 B/lane
/// global transactions, twiddles fetched per component from constant memory.
/// Register cost = 2^(R+2) u32, so R<=4. Requires S0>=2.
const K_RADIX4: &str = r#"
kernel void k_radix4(device uint* data [[buffer(0)]],
                     const device uint* src [[buffer(1)]],
                     constant uint* tw [[buffer(2)]],
                     uint3 gid [[thread_position_in_grid]]) {
    device uint4* data4 = (device uint4*)data;
    uint off4 = gid.y * ($NN >> 2u);
    uint t0 = gid.x;
    uint lo4 = t0 & ((1u << ($S0 - 2u)) - 1u);
    uint hi = t0 >> ($S0 - 2u);
    uint base = off4 + lo4 + (hi << ($S0 - 2u + $RR));
    uint4 x[$RSZ];
    #pragma clang loop unroll(full)
    for (uint m = 0u; m < $RSZ; m++) { x[m] = data4[base + (m << ($S0 - 2u))]; }
    uint lo = lo4 << 2u;
    #pragma clang loop unroll(full)
    for (uint t = 1u; t <= $RR; t++) {
        uint ht = 1u << (t - 1u);
        uint sh = $LOGN - $S0 - t;
        #pragma clang loop unroll(full)
        for (uint p = 0u; p < ($RSZ >> 1); p++) {
            uint mlow = p & (ht - 1u);
            uint m1 = ((p >> (t - 1u)) << t) + mlow;
            uint m2 = m1 + ht;
            uint j = lo + (mlow << $S0);
            uint4 w = uint4(TW(tw, (j      ) << sh), TW(tw, (j + 1u) << sh),
                            TW(tw, (j + 2u) << sh), TW(tw, (j + 3u) << sh));
            uint4 tt = mmul4(x[m2], w);
            uint4 u2 = x[m1];
            x[m1] = addp4(u2, tt);
            x[m2] = subp4(u2, tt);
        }
    }
    #pragma clang loop unroll(full)
    for (uint m = 0u; m < $RSZ; m++) { data4[base + (m << ($S0 - 2u))] = x[m]; }
}
"#;

/// Generic MID pass (threadgroup butterflies): stages g0+1..g0+F on tiles of
/// 2^C coalescing bits x 2^F butterfly bits at offset g0. In place on data.
/// tg.x decomposes into a (bits [C,g0)) and b (bits [g0+F, logn)).
const K_MID: &str = r#"
kernel void k_mid(device uint* data [[buffer(0)]],
                  const device uint* src [[buffer(1)]],
                  constant uint* tw [[buffer(2)]],
                  uint lid [[thread_index_in_threadgroup]],
                  uint3 tg [[threadgroup_position_in_grid]]) {
    threadgroup uint tile[$TILE];
    uint off = tg.y * $NN;
    uint aa = (tg.x & $AM) << $CC;
    uint base = off + ((tg.x >> $ASH) << $BSH) + aa;
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        uint q = sl >> $CC;
        uint lo = sl & ((1u << $CC) - 1u);
        tile[swz(sl)] = data[base + lo + (q << $G0)];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint t = 1u; t <= $FF; t++) {
        for (uint k = 0u; k < $HBT; k++) {
            uint bf = lid + k * $WGSZ;
            uint qb = bf >> $CC;
            uint lo = bf & ((1u << $CC) - 1u);
            uint jq = qb & ((1u << (t - 1u)) - 1u);
            uint q1 = ((qb >> (t - 1u)) << t) + jq;
            uint q2 = q1 + (1u << (t - 1u));
            uint i1 = (q1 << $CC) + lo;
            uint i2 = (q2 << $CC) + lo;
            uint j = aa + lo + (jq << $G0);
            uint tt = mmul(tile[swz(i2)], TW(tw, j << ($LOGN - $G0 - t)));
            uint u2 = tile[swz(i1)];
            tile[swz(i1)] = addp(u2, tt);
            tile[swz(i2)] = subp(u2, tt);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        uint q = sl >> $CC;
        uint lo = sl & ((1u << $CC) - 1u);
        data[base + lo + (q << $G0)] = tile[swz(sl)];
    }
}
"#;

/// Generic MID pass, simdgroup-shuffle variant: butterfly stages whose q-bit
/// fits a lane bit run in registers via simd_shuffle_xor; one re-gather per
/// 5-stage block instead of a barrier per stage.
const K_MIDS_HEAD: &str = r#"
kernel void k_mids(device uint* data [[buffer(0)]],
                   const device uint* src [[buffer(1)]],
                   constant uint* tw [[buffer(2)]],
                   uint lid [[thread_index_in_threadgroup]],
                   uint3 tg [[threadgroup_position_in_grid]]) {
    threadgroup uint tile[$TILE];
    uint off = tg.y * $NN;
    uint aa = (tg.x & $AM) << $CC;
    uint base = off + ((tg.x >> $ASH) << $BSH) + aa;
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        uint q = sl >> $CC;
        uint lo = sl & ((1u << $CC) - 1u);
        tile[swz(sl)] = data[base + lo + (q << $G0)];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    // block 1: stages 1..B1E — q bits 0..QB-1 in lane bits 0..QB-1
    for (uint k = 0u; k < $TPT; k++) {
        uint v = lid + k * $WGSZ;
        uint rest = v >> $QB;
        uint i = ((v & ((1u << $QB) - 1u)) << $CC)
               | (rest & ((1u << $CC) - 1u))
               | ((rest >> $CC) << ($CC + $QB));
        uint x = tile[swz(i)];
        uint lo = i & ((1u << $CC) - 1u);
        uint q = i >> $CC;
        for (uint t = 1u; t <= $B1E; t++) {
            uint ht = 1u << (t - 1u);
            uint jq = q & (ht - 1u);
            uint j = aa + lo + (jq << $G0);
            uint wv = TW(tw, j << ($LOGN - $G0 - t));
            uint xt = (q & ht) ? mmul(x, wv) : x;
            uint other = simd_shuffle_xor(xt, ht);
            x = (q & ht) ? subp(other, xt) : addp(xt, other);
        }
        tile[swz(i)] = x;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
"#;

const K_MIDS_BLOCK2: &str = r#"
    // block 2: stages 6..F — q bits F-5..F-1 in lane bits
    for (uint k = 0u; k < $TPT; k++) {
        uint v = lid + k * $WGSZ;
        uint i = ((v & 31u) << ($CC + $FF - 5u))
               | ((v >> 5) & ((1u << ($CC + $FF - 5u)) - 1u));
        uint x = tile[swz(i)];
        uint lo = i & ((1u << $CC) - 1u);
        uint q = i >> $CC;
        for (uint t = 6u; t <= $FF; t++) {
            uint ht = 1u << (t - 1u);
            uint m = 1u << (t + 4u - $FF);
            uint jq = q & (ht - 1u);
            uint j = aa + lo + (jq << $G0);
            uint wv = TW(tw, j << ($LOGN - $G0 - t));
            uint xt = (q & ht) ? mmul(x, wv) : x;
            uint other = simd_shuffle_xor(xt, m);
            x = (q & ht) ? subp(other, xt) : addp(xt, other);
        }
        tile[swz(i)] = x;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
"#;

const K_MIDS_TAIL: &str = r#"
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        uint q = sl >> $CC;
        uint lo = sl & ((1u << $CC) - 1u);
        data[base + lo + (q << $G0)] = tile[swz(sl)];
    }
}
"#;

/// Register-tier radix-2^R pass: stages s0+1..s0+R entirely in registers,
/// zero threadgroup memory, perfectly coalesced rows (lanes span the low
/// bits, each of the 2^R strided rows is a contiguous lane-run). In place.
const K_RADIX: &str = r#"
kernel void k_radix(device uint* data [[buffer(0)]],
                    const device uint* src [[buffer(1)]],
                    constant uint* tw [[buffer(2)]],
                    uint3 gid [[thread_position_in_grid]]) {
    uint off = gid.y * $NN;
    uint t0 = gid.x;
    uint lo = t0 & ((1u << $S0) - 1u);
    uint hi = t0 >> $S0;
    uint base = off + lo + (hi << ($S0 + $RR));
    uint x[$RSZ];
    #pragma clang loop unroll(full)
    for (uint m = 0u; m < $RSZ; m++) { x[m] = data[base + (m << $S0)]; }
    #pragma clang loop unroll(full)
    for (uint t = 1u; t <= $RR; t++) {
        uint ht = 1u << (t - 1u);
        #pragma clang loop unroll(full)
        for (uint p = 0u; p < ($RSZ >> 1); p++) {
            uint mlow = p & (ht - 1u);
            uint m1 = ((p >> (t - 1u)) << t) + mlow;
            uint m2 = m1 + ht;
            uint j = lo + (mlow << $S0);
            uint tt = mmul(x[m2], TW(tw, j << ($LOGN - $S0 - t)));
            uint u2 = x[m1];
            x[m1] = addp(u2, tt);
            x[m2] = subp(u2, tt);
        }
    }
    #pragma clang loop unroll(full)
    for (uint m = 0u; m < $RSZ; m++) { data[base + (m << $S0)] = x[m]; }
}
"#;

/// Legacy fused pass 1 (v1): bitrev folded into a STRIDED load (the wgpu
/// probe's original plan) — kept for attribution. Threadgroup butterflies.
const K_F1_TG: &str = r#"
kernel void k_f1(device uint* data [[buffer(0)]],
                 const device uint* src [[buffer(1)]],
                 constant uint* tw [[buffer(2)]],
                 uint lid [[thread_index_in_threadgroup]],
                 uint3 tg [[threadgroup_position_in_grid]]) {
    threadgroup uint tile[$TILE];
    uint off = tg.y * $NN;
    uint w = tg.x;
    for (uint k = 0u; k < $TPT; k++) {
        uint u = lid + k * $WGSZ;
        tile[swz(reverse_bits(u) >> (32u - $EE))] = src[off + u * $WW + w];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint s = 1u; s <= $EE; s++) {
        uint h = 1u << (s - 1u);
        for (uint k = 0u; k < $HBT; k++) {
            uint bf = lid + k * $WGSZ;
            uint j = bf & (h - 1u);
            uint i1 = ((bf >> (s - 1u)) << s) + j;
            uint i2 = i1 + h;
            uint t = mmul(tile[swz(i2)], tw[j << ($LOGN - s)]);
            uint u2 = tile[swz(i1)];
            tile[swz(i1)] = addp(u2, t);
            tile[swz(i2)] = subp(u2, t);
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
    }
    uint ga = reverse_bits(w) >> (32u - ($LOGN - $EE));
    uint base = off + ga * $TILE;
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        data[base + sl] = tile[swz(sl)];
    }
}
"#;

/// Legacy fused pass 1, simd-shuffle variant (3 shuffle blocks; needs E>=11).
const K_F1S: &str = r#"
kernel void k_f1s(device uint* data [[buffer(0)]],
                  const device uint* src [[buffer(1)]],
                  constant uint* tw [[buffer(2)]],
                  uint lid [[thread_index_in_threadgroup]],
                  uint3 tg [[threadgroup_position_in_grid]]) {
    threadgroup uint tile[$TILE];
    uint off = tg.y * $NN;
    uint w = tg.x;
    for (uint k = 0u; k < $TPT; k++) {
        uint u = lid + k * $WGSZ;
        tile[swz(reverse_bits(u) >> (32u - $EE))] = src[off + u * $WW + w];
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    uint lane = lid & 31u;
    uint tw2 = tw[(lane & 1u) << ($LOGN - 2u)];
    uint tw3 = tw[(lane & 3u) << ($LOGN - 3u)];
    uint tw4 = tw[(lane & 7u) << ($LOGN - 4u)];
    uint tw5 = tw[(lane & 15u) << ($LOGN - 5u)];
    for (uint k = 0u; k < $TPT; k++) {
        uint i = lid + k * $WGSZ;
        uint x = tile[swz(i)];
        {
            uint other = simd_shuffle_xor(x, 1u);
            x = (lane & 1u) ? subp(other, x) : addp(x, other);
        }
        { uint xt = (lane & 2u) ? mmul(x, tw2) : x;
          uint other = simd_shuffle_xor(xt, 2u);
          x = (lane & 2u) ? subp(other, xt) : addp(xt, other); }
        { uint xt = (lane & 4u) ? mmul(x, tw3) : x;
          uint other = simd_shuffle_xor(xt, 4u);
          x = (lane & 4u) ? subp(other, xt) : addp(xt, other); }
        { uint xt = (lane & 8u) ? mmul(x, tw4) : x;
          uint other = simd_shuffle_xor(xt, 8u);
          x = (lane & 8u) ? subp(other, xt) : addp(xt, other); }
        { uint xt = (lane & 16u) ? mmul(x, tw5) : x;
          uint other = simd_shuffle_xor(xt, 16u);
          x = (lane & 16u) ? subp(other, xt) : addp(xt, other); }
        tile[swz(i)] = x;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint k = 0u; k < $TPT; k++) {
        uint v = lid + k * $WGSZ;
        uint i = (v & ~1023u) | ((v & 31u) << 5) | ((v >> 5) & 31u);
        uint x = tile[swz(i)];
        for (uint s = 6u; s <= 10u; s++) {
            uint h = 1u << (s - 1u);
            uint m = 1u << (s - 6u);
            uint j = i & (h - 1u);
            uint wv = tw[j << ($LOGN - s)];
            uint xt = (i & h) ? mmul(x, wv) : x;
            uint other = simd_shuffle_xor(xt, m);
            x = (i & h) ? subp(other, xt) : addp(xt, other);
        }
        tile[swz(i)] = x;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    for (uint k = 0u; k < $TPT; k++) {
        uint v = lid + k * $WGSZ;
        uint i = ((v & 31u) << ($EE - 5u)) | ((v >> 5) & ((1u << ($EE - 5u)) - 1u));
        uint x = tile[swz(i)];
        for (uint s = 11u; s <= $EE; s++) {
            uint h = 1u << (s - 1u);
            uint m = 1u << (s - 1u - ($EE - 5u));
            uint j = i & (h - 1u);
            uint wv = tw[j << ($LOGN - s)];
            uint xt = (i & h) ? mmul(x, wv) : x;
            uint other = simd_shuffle_xor(xt, m);
            x = (i & h) ? subp(other, xt) : addp(xt, other);
        }
        tile[swz(i)] = x;
    }
    threadgroup_barrier(mem_flags::mem_threadgroup);
    uint ga = reverse_bits(w) >> (32u - ($LOGN - $EE));
    uint base = off + ga * $TILE;
    for (uint k = 0u; k < $TPT; k++) {
        uint sl = lid + k * $WGSZ;
        data[base + sl] = tile[swz(sl)];
    }
}
"#;

const SWZ_ID: &str = "i";
const SWZ_XOR: &str = "i ^ ((i >> 5) & 31u) ^ ((i >> 10) & 31u)";
// swizzle restricted to bits 2..4: preserves aligned uint4 runs (for K_FA4)
const SWZ_XOR4: &str = "i ^ ((i >> 5) & 28u) ^ ((i >> 10) & 28u)";

const TW_DIRECT: &str = "tw[i]";

fn prelude(swz: &str, twexpr: &str) -> String {
    PRELUDE.replace("$SWZEXPR", swz).replace("$TWEXPR", twexpr)
}

/// tw2 split accessor (see PRELUDE comment): hi table lives at element offset
/// n/2 in the tw buffer; lo table is the head of the main table.
fn tw_split(logn: u32) -> String {
    let tws = logn / 2;
    format!(
        "mmul(tw[{}u + (i >> {}u)], tw[i & {}u])",
        1u32 << (logn - 1),
        tws,
        (1u32 << tws) - 1
    )
}

fn subst(template: &str, pairs: &[(&str, u32)]) -> String {
    let mut s = template.to_string();
    for (k, v) in pairs {
        s = s.replace(k, &format!("{v}u"));
    }
    s
}

// ---------- Metal harness ----------

struct Gpu {
    device: Device,
    queue: CommandQueue,
    buf_work: Buffer,
    buf_src: Buffer,
    buf_tw: Buffer,
}

const BUF_U32S: usize = 1 << 24; // 64 MiB working set (same as the wgpu probe)

#[derive(Clone)]
struct Step {
    pipe: ComputePipelineState,
    groups: (u64, u64),
    wgsz: u64,
}

impl Gpu {
    fn new() -> Self {
        let device = Device::system_default().expect("no Metal device");
        println!(
            "device: {} (unified memory: {}, max threadgroup mem: {} B)",
            device.name(),
            device.has_unified_memory(),
            device.max_threadgroup_memory_length()
        );
        let queue = device.new_command_queue();
        let sz = (BUF_U32S * 4) as u64;
        let opts = MTLResourceOptions::StorageModeShared;
        let buf_work = device.new_buffer(sz, opts);
        let buf_src = device.new_buffer(sz, opts);
        let buf_tw = device.new_buffer(8 << 20, opts);
        Gpu {
            device,
            queue,
            buf_work,
            buf_src,
            buf_tw,
        }
    }

    fn pipeline(&self, msl: &str, func: &str, label: &str) -> ComputePipelineState {
        let options = CompileOptions::new();
        let lib = self
            .device
            .new_library_with_source(msl, &options)
            .unwrap_or_else(|e| panic!("MSL compile failed for {label}: {e}\n---\n{msl}"));
        let f = lib
            .get_function(func, None)
            .unwrap_or_else(|e| panic!("no function {func} in {label}: {e}"));
        self.device
            .new_compute_pipeline_state_with_function(&f)
            .unwrap_or_else(|e| panic!("pipeline failed for {label}: {e}"))
    }

    fn write_buf(&self, buf: &Buffer, data: &[u32]) {
        assert!(data.len() * 4 <= buf.length() as usize);
        unsafe {
            std::ptr::copy_nonoverlapping(data.as_ptr(), buf.contents() as *mut u32, data.len());
        }
    }

    /// Encode `iters` repetitions of the plan in ONE command buffer / ONE
    /// serial compute encoder; wall seconds per iteration, best of `reps`
    /// after a warmup (same protocol as the wgpu probe).
    fn time_plan(&self, plan: &[Step], iters: u32, reps: u32) -> f64 {
        let run = || -> f64 {
            autoreleasepool(|| {
                let t0 = std::time::Instant::now();
                let cb = self.queue.new_command_buffer();
                let enc = cb.new_compute_command_encoder();
                enc.set_buffer(0, Some(&self.buf_work), 0);
                enc.set_buffer(1, Some(&self.buf_src), 0);
                enc.set_buffer(2, Some(&self.buf_tw), 0);
                for _ in 0..iters {
                    for s in plan {
                        enc.set_compute_pipeline_state(&s.pipe);
                        enc.dispatch_thread_groups(
                            MTLSize::new(s.groups.0, s.groups.1, 1),
                            MTLSize::new(s.wgsz, 1, 1),
                        );
                    }
                }
                enc.end_encoding();
                cb.commit();
                cb.wait_until_completed();
                t0.elapsed().as_secs_f64() / iters as f64
            })
        };
        run(); // warmup
        (0..reps).map(|_| run()).fold(f64::MAX, f64::min)
    }

    fn read_work(&self, n_u32: usize) -> Vec<u32> {
        let mut out = vec![0u32; n_u32];
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.buf_work.contents() as *const u32,
                out.as_mut_ptr(),
                n_u32,
            );
        }
        out
    }
}

// ---------- pass descriptors + plan builder ----------

#[derive(Clone, Debug)]
enum Pass {
    /// coalesced 2D bitrev-fold + stages 1..b1 (reads src, writes data)
    Fa {
        b1: u32,
        nc: u32,
    },
    /// Fa with uint4 global loads/stores
    Fa4 {
        b1: u32,
        nc: u32,
    },
    /// stages g0+1..g0+f on 2^c-coalesced tiles, in place
    Mid {
        g0: u32,
        f: u32,
        c: u32,
        simd: bool,
    },
    /// stages s0+1..s0+r in registers, in place
    Radix {
        s0: u32,
        r: u32,
    },
    /// Radix with explicit threadgroup width (coalescing-span tuning)
    RadixW {
        s0: u32,
        r: u32,
        w: u32,
    },
    /// Radix with uint4 lanes (4 consecutive lo per thread), in place
    Radix4 {
        s0: u32,
        r: u32,
    },
    /// legacy strided fused pass 1: bitrev fold + stages 1..e (reads src)
    F1 {
        e: u32,
        simd: bool,
    },
    Bitrev,
    Stage {
        s: u32,
    },
}

fn build_step(gpu: &Gpu, pass: &Pass, logn: u32, ncols: usize) -> Step {
    let n = 1u64 << logn;
    let wgsz: u32 = 256;
    match *pass {
        Pass::Fa { b1, nc } => {
            let tile = (1u32 << b1) * nc;
            assert!(tile * 4 <= gpu.device.max_threadgroup_memory_length() as u32);
            let msl = format!(
                "{}{}",
                prelude(SWZ_XOR, TW_DIRECT),
                subst(
                    K_FA,
                    &[
                        ("$TILE", tile),
                        ("$TPT", tile / wgsz),
                        ("$HBT", tile / 2 / wgsz),
                        ("$WGSZ", wgsz),
                        ("$NN", n as u32),
                        ("$LOGN", logn),
                        ("$B1", b1),
                        ("$NC", nc),
                        ("$LNC", nc.trailing_zeros()),
                    ],
                )
            );
            Step {
                pipe: gpu.pipeline(&msl, "k_fa", &format!("fa{b1}/{nc}")),
                groups: ((n >> b1) / nc as u64, ncols as u64),
                wgsz: wgsz as u64,
            }
        }
        Pass::Fa4 { b1, nc } => {
            let tile = (1u32 << b1) * nc;
            assert!(tile * 4 <= gpu.device.max_threadgroup_memory_length() as u32);
            assert!(nc >= 4 && logn - b1 >= 2 && tile / 4 >= wgsz && b1 >= 2);
            let msl = format!(
                "{}{}",
                prelude(SWZ_XOR4, TW_DIRECT),
                subst(
                    K_FA4,
                    &[
                        ("$TILE", tile),
                        ("$TPT4", tile / 4 / wgsz),
                        ("$HBT", tile / 2 / wgsz),
                        ("$WGSZ", wgsz),
                        ("$NN", n as u32),
                        ("$LOGN", logn),
                        ("$B1", b1),
                        ("$NC", nc),
                        ("$LNC", nc.trailing_zeros()),
                    ],
                )
            );
            Step {
                pipe: gpu.pipeline(&msl, "k_fa4", &format!("fa4 {b1}/{nc}")),
                groups: ((n >> b1) / nc as u64, ncols as u64),
                wgsz: wgsz as u64,
            }
        }
        Pass::Mid { g0, f, c, simd } => {
            let tile = 1u32 << (c + f);
            assert!(tile * 4 <= gpu.device.max_threadgroup_memory_length() as u32);
            assert!(g0 >= c && g0 + f <= logn);
            let common = [
                ("$TILE", tile),
                ("$TPT", tile / wgsz),
                ("$HBT", tile / 2 / wgsz),
                ("$WGSZ", wgsz),
                ("$NN", n as u32),
                ("$LOGN", logn),
                ("$G0", g0),
                ("$FF", f),
                ("$CC", c),
                ("$AM", (1 << (g0 - c)) - 1),
                ("$ASH", g0 - c),
                ("$BSH", g0 + f),
                ("$QB", f.min(5)),
                ("$B1E", f.min(5)),
            ];
            let (src, name, swzx) = if simd {
                let mut s = K_MIDS_HEAD.to_string();
                if f > 5 {
                    s.push_str(K_MIDS_BLOCK2);
                }
                s.push_str(K_MIDS_TAIL);
                (s, "k_mids", SWZ_XOR)
            } else {
                (K_MID.to_string(), "k_mid", SWZ_ID)
            };
            let msl = format!("{}{}", prelude(swzx, &tw_split(logn)), subst(&src, &common));
            Step {
                pipe: gpu.pipeline(
                    &msl,
                    name,
                    &format!("mid{g0}+{f}/{c}{}", if simd { "s" } else { "" }),
                ),
                groups: (n >> (f + c), ncols as u64),
                wgsz: wgsz as u64,
            }
        }
        Pass::Radix { s0, r } => {
            assert!(s0 + r <= logn && r <= 5);
            let msl = format!(
                "{}{}",
                prelude(SWZ_ID, &tw_split(logn)),
                subst(
                    K_RADIX,
                    &[
                        ("$NN", n as u32),
                        ("$LOGN", logn),
                        ("$S0", s0),
                        ("$RR", r),
                        ("$RSZ", 1 << r),
                    ],
                )
            );
            Step {
                pipe: gpu.pipeline(&msl, "k_radix", &format!("radix{s0}+{r}")),
                groups: ((n >> r) / wgsz as u64, ncols as u64),
                wgsz: wgsz as u64,
            }
        }
        Pass::RadixW { s0, r, w } => {
            assert!(s0 + r <= logn && r <= 5 && (n >> r) % w as u64 == 0);
            let msl = format!(
                "{}{}",
                prelude(SWZ_ID, &tw_split(logn)),
                subst(
                    K_RADIX,
                    &[
                        ("$NN", n as u32),
                        ("$LOGN", logn),
                        ("$S0", s0),
                        ("$RR", r),
                        ("$RSZ", 1 << r),
                    ],
                )
            );
            let pipe = gpu.pipeline(&msl, "k_radix", &format!("radixw{s0}+{r}/{w}"));
            // register pressure caps threads/threadgroup; exceeding the cap
            // silently drops threads (caught by the parity gate) — clamp to
            // the pipeline's limit, rounded down to a power of two.
            let wmax = pipe.max_total_threads_per_threadgroup() as u32;
            let w_eff = 1u32 << 31 - w.min(wmax).leading_zeros();
            Step {
                pipe,
                groups: ((n >> r) / w_eff as u64, ncols as u64),
                wgsz: w_eff as u64,
            }
        }
        Pass::Radix4 { s0, r } => {
            assert!(s0 >= 2 && s0 + r <= logn && r <= 4);
            let threads = (n as u64 >> 2) >> r;
            assert!(threads % wgsz as u64 == 0);
            let msl = format!(
                "{}{}",
                prelude(SWZ_ID, &tw_split(logn)),
                subst(
                    K_RADIX4,
                    &[
                        ("$NN", n as u32),
                        ("$LOGN", logn),
                        ("$S0", s0),
                        ("$RR", r),
                        ("$RSZ", 1 << r),
                    ],
                )
            );
            Step {
                pipe: gpu.pipeline(&msl, "k_radix4", &format!("radix4 {s0}+{r}")),
                groups: (threads / wgsz as u64, ncols as u64),
                wgsz: wgsz as u64,
            }
        }
        Pass::F1 { e, simd } => {
            let tile = 1u32 << e;
            let ww = 1u64 << (logn - e);
            let common = [
                ("$TILE", tile),
                ("$TPT", tile / wgsz),
                ("$HBT", tile / 2 / wgsz),
                ("$WGSZ", wgsz),
                ("$NN", n as u32),
                ("$LOGN", logn),
                ("$EE", e),
                ("$WW", ww as u32),
            ];
            let (src, name) = if simd {
                (K_F1S, "k_f1s")
            } else {
                (K_F1_TG, "k_f1")
            };
            let msl = format!("{}{}", prelude(SWZ_ID, TW_DIRECT), subst(src, &common));
            Step {
                pipe: gpu.pipeline(&msl, name, &format!("f1 E={e}")),
                groups: (ww, ncols as u64),
                wgsz: wgsz as u64,
            }
        }
        Pass::Bitrev => {
            let msl = format!(
                "{}{}",
                prelude(SWZ_ID, TW_DIRECT),
                subst(K_BITREV, &[("$NN", n as u32), ("$RSH", 32 - logn)])
            );
            Step {
                pipe: gpu.pipeline(&msl, "k_bitrev", "bitrev"),
                groups: (n / 256, ncols as u64),
                wgsz: 256,
            }
        }
        Pass::Stage { s } => {
            let msl = format!(
                "{}{}",
                prelude(SWZ_ID, TW_DIRECT),
                subst(
                    K_STAGE,
                    &[
                        ("$NN", n as u32),
                        ("$HALF", 1 << (s - 1)),
                        ("$SS", s),
                        ("$TSH", logn - s)
                    ],
                )
            );
            Step {
                pipe: gpu.pipeline(&msl, "k_stage", &format!("stage{s}")),
                groups: (n / 2 / 256, ncols as u64),
                wgsz: 256,
            }
        }
    }
}

/// The plan sweep per logn. Every plan covers stages 1..logn exactly once.
fn plans_for(logn: u32) -> Vec<(String, Vec<Pass>)> {
    use Pass::*;
    let mut v: Vec<(String, Vec<Pass>)> = Vec::new();
    // multipass reference (RISC0-architecture equivalent)
    let mut mp = vec![Bitrev];
    for s in 1..=logn {
        mp.push(Stage { s });
    }
    v.push(("multipass".into(), mp));
    // legacy 2-pass fused (strided pass1) — v1 best configs
    let e = 11;
    v.push((
        format!("fused2 E={e} tg"),
        vec![
            F1 { e, simd: false },
            Mid {
                g0: e,
                f: logn - e,
                c: 2 * e - logn,
                simd: false,
            },
        ],
    ));
    v.push((
        format!("fused2 E={e} simd"),
        vec![
            F1 { e, simd: true },
            Mid {
                g0: e,
                f: logn - e,
                c: 2 * e - logn,
                simd: true,
            },
        ],
    ));
    // coalesced four-step-style plans
    match logn {
        15 => {
            v.push((
                "fa8/32+mid(8,7)".into(),
                vec![
                    Fa { b1: 8, nc: 32 },
                    Mid {
                        g0: 8,
                        f: 7,
                        c: 5,
                        simd: false,
                    },
                ],
            ));
            v.push((
                "fa8/16+mid(8,7)".into(),
                vec![
                    Fa { b1: 8, nc: 16 },
                    Mid {
                        g0: 8,
                        f: 7,
                        c: 5,
                        simd: false,
                    },
                ],
            ));
            v.push((
                "fa8/8+mid(8,7)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Mid {
                        g0: 8,
                        f: 7,
                        c: 5,
                        simd: false,
                    },
                ],
            ));
            v.push((
                "fa8/32+mids(8,7)".into(),
                vec![
                    Fa { b1: 8, nc: 32 },
                    Mid {
                        g0: 8,
                        f: 7,
                        c: 5,
                        simd: true,
                    },
                ],
            ));
            v.push((
                "fa8/32+radix(8,4)+radix(12,3)".into(),
                vec![
                    Fa { b1: 8, nc: 32 },
                    Radix { s0: 8, r: 4 },
                    Radix { s0: 12, r: 3 },
                ],
            ));
            v.push((
                "fa8/8+radix(8,4)+radix(12,3)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 4 },
                    Radix { s0: 12, r: 3 },
                ],
            ));
            v.push((
                "fa7/16+radix(7,4)+radix(11,4)".into(),
                vec![
                    Fa { b1: 7, nc: 16 },
                    Radix { s0: 7, r: 4 },
                    Radix { s0: 11, r: 4 },
                ],
            ));
            v.push((
                "fa6/32+radix(6,5)+radix(11,4)".into(),
                vec![
                    Fa { b1: 6, nc: 32 },
                    Radix { s0: 6, r: 5 },
                    Radix { s0: 11, r: 4 },
                ],
            ));
            v.push((
                "fa8/8+radixw(8,4/1024)+radixw(12,3/1024)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    RadixW {
                        s0: 8,
                        r: 4,
                        w: 1024,
                    },
                    RadixW {
                        s0: 12,
                        r: 3,
                        w: 1024,
                    },
                ],
            ));
            v.push((
                "fa8/4+radix(8,4)+radix(12,3)".into(),
                vec![
                    Fa { b1: 8, nc: 4 },
                    Radix { s0: 8, r: 4 },
                    Radix { s0: 12, r: 3 },
                ],
            ));
            v.push((
                "fa9/8+radix(9,3)+radix(12,3)".into(),
                vec![
                    Fa { b1: 9, nc: 8 },
                    Radix { s0: 9, r: 3 },
                    Radix { s0: 12, r: 3 },
                ],
            ));
            v.push((
                "fa10/8+radix(10,5)".into(),
                vec![Fa { b1: 10, nc: 8 }, Radix { s0: 10, r: 5 }],
            ));
            v.push((
                "fa10/4+radix(10,5)".into(),
                vec![Fa { b1: 10, nc: 4 }, Radix { s0: 10, r: 5 }],
            ));
            v.push((
                "fa4:8/8+radix(8,4)+radix(12,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 4 },
                    Radix { s0: 12, r: 3 },
                ],
            ));
            v.push((
                "fa4:8/8+radix4(8,4)+radix4(12,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 3 },
                ],
            ));
            v.push((
                "fa4:8/16+radix4(8,4)+radix4(12,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 16 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 3 },
                ],
            ));
        }
        18 => {
            v.push((
                "fa10/8+mid(10,8)".into(),
                vec![
                    Fa { b1: 10, nc: 8 },
                    Mid {
                        g0: 10,
                        f: 8,
                        c: 5,
                        simd: false,
                    },
                ],
            ));
            v.push((
                "fa10/8+mids(10,8)".into(),
                vec![
                    Fa { b1: 10, nc: 8 },
                    Mid {
                        g0: 10,
                        f: 8,
                        c: 5,
                        simd: true,
                    },
                ],
            ));
            v.push((
                "fa8/32+radix(8,5)+radix(13,5)".into(),
                vec![
                    Fa { b1: 8, nc: 32 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 5 },
                ],
            ));
            v.push((
                "fa8/8+radix(8,5)+radix(13,5)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 5 },
                ],
            ));
            v.push((
                "fa8/8+radixw(8,5/1024)+radixw(13,5/1024)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    RadixW {
                        s0: 8,
                        r: 5,
                        w: 1024,
                    },
                    RadixW {
                        s0: 13,
                        r: 5,
                        w: 1024,
                    },
                ],
            ));
            v.push((
                "fa7/16+radix(7,4)+radix(11,4)+radix(15,3)".into(),
                vec![
                    Fa { b1: 7, nc: 16 },
                    Radix { s0: 7, r: 4 },
                    Radix { s0: 11, r: 4 },
                    Radix { s0: 15, r: 3 },
                ],
            ));
            v.push((
                "fa6/32+radix(6,4)+radix(10,4)+radix(14,4)".into(),
                vec![
                    Fa { b1: 6, nc: 32 },
                    Radix { s0: 6, r: 4 },
                    Radix { s0: 10, r: 4 },
                    Radix { s0: 14, r: 4 },
                ],
            ));
            v.push((
                "fa8/4+radix(8,5)+radix(13,5)".into(),
                vec![
                    Fa { b1: 8, nc: 4 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 5 },
                ],
            ));
            v.push((
                "fa9/8+radix(9,5)+radix(14,4)".into(),
                vec![
                    Fa { b1: 9, nc: 8 },
                    Radix { s0: 9, r: 5 },
                    Radix { s0: 14, r: 4 },
                ],
            ));
            v.push((
                "fa8/8+radix(8,4)+radix(12,3)+radix(15,3)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 4 },
                    Radix { s0: 12, r: 3 },
                    Radix { s0: 15, r: 3 },
                ],
            ));
            v.push((
                "fa8/8+mid(8,5)+radix(13,5)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Mid {
                        g0: 8,
                        f: 5,
                        c: 5,
                        simd: false,
                    },
                    Radix { s0: 13, r: 5 },
                ],
            ));
            v.push((
                "fa4:8/8+radix(8,5)+radix(13,5)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 5 },
                ],
            ));
            v.push((
                "fa4:8/8+radix4(8,4)+radix4(12,3)+radix4(15,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 3 },
                    Radix4 { s0: 15, r: 3 },
                ],
            ));
            v.push((
                "fa4:8/8+radix4(8,4)+radix4(12,3)+radix(15,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 3 },
                    Radix { s0: 15, r: 3 },
                ],
            ));
            v.push((
                "fa4:8/16+radix4(8,4)+radix4(12,3)+radix4(15,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 16 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 3 },
                    Radix4 { s0: 15, r: 3 },
                ],
            ));
        }
        21 => {
            v.push((
                "fa8/32+mid(8,7)+mid(15,6)".into(),
                vec![
                    Fa { b1: 8, nc: 32 },
                    Mid {
                        g0: 8,
                        f: 7,
                        c: 5,
                        simd: false,
                    },
                    Mid {
                        g0: 15,
                        f: 6,
                        c: 5,
                        simd: false,
                    },
                ],
            ));
            v.push((
                "fa8/8+mids(8,7)+mids(15,6)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Mid {
                        g0: 8,
                        f: 7,
                        c: 5,
                        simd: true,
                    },
                    Mid {
                        g0: 15,
                        f: 6,
                        c: 5,
                        simd: true,
                    },
                ],
            ));
            v.push((
                "fa10/8+mid(10,6)+radix(16,5)".into(),
                vec![
                    Fa { b1: 10, nc: 8 },
                    Mid {
                        g0: 10,
                        f: 6,
                        c: 5,
                        simd: false,
                    },
                    Radix { s0: 16, r: 5 },
                ],
            ));
            v.push((
                "fa8/32+radix(8,5)+radix(13,4)+radix(17,4)".into(),
                vec![
                    Fa { b1: 8, nc: 32 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 4 },
                    Radix { s0: 17, r: 4 },
                ],
            ));
            v.push((
                "fa8/8+radix(8,5)+radix(13,4)+radix(17,4)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 4 },
                    Radix { s0: 17, r: 4 },
                ],
            ));
            v.push((
                "fa8/4+radix(8,5)+radix(13,4)+radix(17,4)".into(),
                vec![
                    Fa { b1: 8, nc: 4 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 4 },
                    Radix { s0: 17, r: 4 },
                ],
            ));
            v.push((
                "fa9/8+radix(9,4)+radix(13,4)+radix(17,4)".into(),
                vec![
                    Fa { b1: 9, nc: 8 },
                    Radix { s0: 9, r: 4 },
                    Radix { s0: 13, r: 4 },
                    Radix { s0: 17, r: 4 },
                ],
            ));
            v.push((
                "fa8/8+radix(8,5)+radix(13,5)+radix(18,3)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 5 },
                    Radix { s0: 18, r: 3 },
                ],
            ));
            v.push((
                "fa8/8+radixw(8,5/1024)+radixw(13,5/1024)+radixw(18,3/1024)".into(),
                vec![
                    Fa { b1: 8, nc: 8 },
                    RadixW {
                        s0: 8,
                        r: 5,
                        w: 1024,
                    },
                    RadixW {
                        s0: 13,
                        r: 5,
                        w: 1024,
                    },
                    RadixW {
                        s0: 18,
                        r: 3,
                        w: 1024,
                    },
                ],
            ));
            v.push((
                "fa7/16+radix(7,5)+radix(12,5)+radix(17,4)".into(),
                vec![
                    Fa { b1: 7, nc: 16 },
                    Radix { s0: 7, r: 5 },
                    Radix { s0: 12, r: 5 },
                    Radix { s0: 17, r: 4 },
                ],
            ));
            v.push((
                "fa6/32+radix(6,5)+radix(11,5)+radix(16,5)".into(),
                vec![
                    Fa { b1: 6, nc: 32 },
                    Radix { s0: 6, r: 5 },
                    Radix { s0: 11, r: 5 },
                    Radix { s0: 16, r: 5 },
                ],
            ));
            v.push((
                "fa4:8/8+radix(8,5)+radix(13,5)+radix(18,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix { s0: 8, r: 5 },
                    Radix { s0: 13, r: 5 },
                    Radix { s0: 18, r: 3 },
                ],
            ));
            v.push((
                "fa4:8/8+radix4(8,4)+radix4(12,4)+radix(16,5)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 4 },
                    Radix { s0: 16, r: 5 },
                ],
            ));
            v.push((
                "fa4:9/8+radix4(9,4)+radix4(13,4)+radix4(17,4)".into(),
                vec![
                    Fa4 { b1: 9, nc: 8 },
                    Radix4 { s0: 9, r: 4 },
                    Radix4 { s0: 13, r: 4 },
                    Radix4 { s0: 17, r: 4 },
                ],
            ));
            v.push((
                "fa4:8/8+radix4(8,4)+radix4(12,3)+radix4(15,3)+radix4(18,3)".into(),
                vec![
                    Fa4 { b1: 8, nc: 8 },
                    Radix4 { s0: 8, r: 4 },
                    Radix4 { s0: 12, r: 3 },
                    Radix4 { s0: 15, r: 3 },
                    Radix4 { s0: 18, r: 3 },
                ],
            ));
        }
        _ => {}
    }
    v
}

// ---------- shapes + main ----------

struct ShapeResult {
    label: String,
    ntotal: usize,
    best_gpu_s: f64,
    best_plan: String,
    best_passes: u32,
    cpu1_s: f64,
    cpu12_s: f64,
}

fn main() {
    // 1. Convention lock: host reference DIT vs pinned p3.
    {
        let logn = 10u32;
        let n = 1usize << logn;
        let mut rng = rand::thread_rng();
        let x: Vec<u32> = (0..n).map(|_| rng.gen_range(0..P)).collect();
        let refv = cpu_ref_ntt(&x, logn);
        let dft = Radix2DitParallel::<BabyBear>::default();
        let p3v: Vec<u32> = dft
            .dft(x.iter().map(|&v| BabyBear::from_int(v)).collect())
            .iter()
            .map(|v| v.as_canonical_u32())
            .collect();
        assert_eq!(refv, p3v, "convention lock failed: host DIT != p3 dft");
        println!("convention lock: host radix-2 DIT == p3 Radix2DitParallel::dft (n=2^{logn}) ✓");
    }

    let gpu = Gpu::new();
    let mut rng = rand::thread_rng();
    let all_input: Vec<u32> = (0..BUF_U32S).map(|_| rng.gen_range(0..P)).collect();
    let all_mont: Vec<u32> = all_input.iter().map(|&v| to_mont(v)).collect();

    // 2. Copy ceiling.
    gpu.write_buf(&gpu.buf_src, &all_mont);
    let nvec4 = (BUF_U32S / 4) as u64;
    let stride_v4 = (nvec4 / 4) as u32;
    let copy_pipe = gpu.pipeline(
        &subst(
            &format!("{}{}", prelude(SWZ_ID, TW_DIRECT), K_COPY4),
            &[("$CSTRIDE", stride_v4)],
        ),
        "k_copy4",
        "copy4",
    );
    let bytes_copy = (BUF_U32S * 8) as f64; // read + write
    let t_copy = gpu.time_plan(
        &[Step {
            pipe: copy_pipe,
            groups: (stride_v4 as u64 / 256, 1),
            wgsz: 256,
        }],
        30,
        5,
    );
    let ceiling = bytes_copy / t_copy;
    println!(
        "copy ceiling (64 MiB read+write): {:.1} GB/s ({:.0}% of 400 GB/s spec)",
        ceiling / 1e9,
        ceiling / SPEC_BW * 100.0
    );

    // 2b. ALU probe: chained Montgomery muls with native mulhi.
    {
        let pipe = gpu.pipeline(
            &format!("{}{}", prelude(SWZ_ID, TW_DIRECT), K_MULBENCH),
            "k_mulbench",
            "mulbench",
        );
        let lanes = 1u64 << 22;
        let t = gpu.time_plan(
            &[Step {
                pipe,
                groups: (lanes / 256, 1),
                wgsz: 256,
            }],
            10,
            5,
        );
        println!(
            "native monty-mul ALU probe: {:.1} Gmul/s (4M lanes x 128 chained; wgpu 16-bit-split measured 60-106)",
            lanes as f64 * 128.0 / t / 1e9
        );
    }

    // 3. NTT shapes (same as the tuned wgpu probe).
    let shapes: &[(u32, usize)] = &[(15, 64), (15, 256), (18, 16), (21, 1), (21, 8)];
    let mut results: Vec<ShapeResult> = Vec::new();

    for &(logn, ncols) in shapes {
        let n = 1usize << logn;
        let ntotal = n * ncols;
        assert!(ntotal <= BUF_U32S);
        println!(
            "\n=== NTT 2^{logn} x {ncols} cols ({} Melem, {} MiB) ===",
            ntotal >> 20,
            ntotal * 4 >> 20
        );

        let input = &all_input[..ntotal];
        gpu.write_buf(&gpu.buf_src, &all_mont[..ntotal]);

        // twiddles: mont(w^t), t < n/2
        let w = BabyBear::two_adic_generator(logn as usize).as_canonical_u32() as u64;
        let mut twv = Vec::with_capacity(n / 2 + (n / 2 >> (logn / 2)) as usize);
        let mut acc = 1u64;
        for _ in 0..n / 2 {
            twv.push(to_mont(acc as u32));
            acc = mulmod(acc, w);
        }
        // tw2 hi-table appendix: tw[n/2 + k] = mont(w^(k << tws))
        let tws = logn / 2;
        for k in 0..(n / 2) >> tws {
            twv.push(twv[k << tws]);
        }
        gpu.write_buf(&gpu.buf_tw, &twv);

        // p3 expected + CPU baselines
        let mat_vals: Vec<BabyBear> = (0..ntotal)
            .map(|i| {
                let (r, c) = (i / ncols, i % ncols);
                BabyBear::from_int(input[c * n + r])
            })
            .collect();
        let mat = RowMajorMatrix::new(mat_vals, ncols);
        let dft = Radix2DitParallel::<BabyBear>::default();
        let m1 = mat.clone();
        let t0 = std::time::Instant::now();
        let expected_m = dft.dft_batch(m1).to_row_major_matrix();
        let cpu12_first = t0.elapsed().as_secs_f64();
        let m2 = mat.clone();
        let t0 = std::time::Instant::now();
        let _ = dft.dft_batch(m2).to_row_major_matrix();
        let cpu12_s = cpu12_first.min(t0.elapsed().as_secs_f64());
        let pool1 = rayon::ThreadPoolBuilder::new()
            .num_threads(1)
            .build()
            .unwrap();
        let m3 = mat.clone();
        let t0 = std::time::Instant::now();
        let _ = pool1.install(|| dft.dft_batch(m3).to_row_major_matrix());
        let cpu1_s = t0.elapsed().as_secs_f64();
        println!(
            "p3 CPU Radix2DitParallel: 1 thread {:.1} ms ({:.0} Melem/s), full rayon {:.1} ms ({:.0} Melem/s)",
            cpu1_s * 1e3,
            ntotal as f64 / cpu1_s / 1e6,
            cpu12_s * 1e3,
            ntotal as f64 / cpu12_s / 1e6
        );
        let expected: Vec<u32> = {
            let mut e = vec![0u32; ntotal];
            for r in 0..n {
                for c in 0..ncols {
                    e[c * n + r] = expected_m.values[r * ncols + c].as_canonical_u32();
                }
            }
            e
        };

        let check_parity = |label: &str| -> bool {
            let got = gpu.read_work(ntotal);
            let mut bad = 0usize;
            for i in 0..ntotal {
                if from_mont(got[i]) != expected[i] {
                    bad += 1;
                    if bad <= 3 {
                        println!(
                            "  MISMATCH [{label}] idx {i} (col {}, row {}): gpu {} expected {}",
                            i / n,
                            i % n,
                            from_mont(got[i]),
                            expected[i]
                        );
                    }
                }
            }
            if bad == 0 {
                println!("  PARITY [{label}]: all {ntotal} values match p3 ✓");
                true
            } else {
                println!("  PARITY FAILED [{label}]: {bad}/{ntotal} mismatches");
                false
            }
        };

        let mut best: Option<(f64, String, u32)> = None;
        let mut parity_all = true;

        for (label, passes) in plans_for(logn) {
            let plan: Vec<Step> = passes
                .iter()
                .map(|p| build_step(&gpu, p, logn, ncols))
                .collect();
            let npasses = plan.len() as u32;
            gpu.time_plan(&plan, 1, 0); // run once for parity
            parity_all &= check_parity(&label);
            let iters = if npasses > 4 {
                ((1u32 << 24) / ntotal as u32 * 2).max(4)
            } else {
                ((1u32 << 26) / ntotal as u32).clamp(8, 256)
            };
            let t = gpu.time_plan(&plan, iters, 3);
            report_plan(&label, t, ntotal, npasses, ceiling, &mut best);
            // per-pass attribution for the multi-pass (non-multipass) plans
            if npasses <= 4 {
                let bytes1 = ntotal as f64 * 8.0;
                let mut parts: Vec<String> = Vec::new();
                for (i, st) in plan.iter().enumerate() {
                    let ti = gpu.time_plan(std::slice::from_ref(st), iters, 3);
                    parts.push(format!(
                        "p{} {:.3} ms ({:.0} GB/s, {:.0}%)",
                        i + 1,
                        ti * 1e3,
                        bytes1 / ti / 1e9,
                        bytes1 / ti / ceiling * 100.0
                    ));
                }
                println!("    {}", parts.join(" + "));
            }
        }

        if !parity_all {
            println!("PARITY FAILURE — aborting");
            std::process::exit(1);
        }
        let (bt, bl, bp) = best.unwrap();
        results.push(ShapeResult {
            label: format!("2^{logn} x {ncols}"),
            ntotal,
            best_gpu_s: bt,
            best_plan: bl,
            best_passes: bp,
            cpu1_s,
            cpu12_s,
        });
    }

    // 4. Summary.
    println!("\n================= SUMMARY (native Metal) =================");
    println!(
        "copy ceiling: {:.1} GB/s measured ({:.0}% of 400 GB/s M2 Max spec)",
        ceiling / 1e9,
        ceiling / SPEC_BW * 100.0
    );
    for r in &results {
        let traffic = r.best_passes as f64 * 8.0 * r.ntotal as f64;
        let gbps = traffic / r.best_gpu_s;
        let melems = r.ntotal as f64 / r.best_gpu_s / 1e6;
        println!(
            "{:>10}  best {:<38} {:>8.3} ms  {:>6.0} Melem/s  {:>5.1} GB/s eff ({} passes)  {:>3.0}% of ceiling  {:>3.0}% of spec | cpu1 {:>7.1} ms, cpu-rayon {:>6.1} ms  (gpu = {:>5.1}x cpu1, {:>4.1}x rayon)",
            r.label,
            r.best_plan,
            r.best_gpu_s * 1e3,
            melems,
            gbps / 1e9,
            r.best_passes,
            gbps / ceiling * 100.0,
            gbps / SPEC_BW * 100.0,
            r.cpu1_s * 1e3,
            r.cpu12_s * 1e3,
            r.cpu1_s / r.best_gpu_s,
            r.cpu12_s / r.best_gpu_s,
        );
    }
    println!("\nnote: 'GB/s eff' counts passes x (read+write) actually performed;");
    println!("'%-of-ceiling' is vs the measured copy kernel, the honest achievable peak.");
}

fn report_plan(
    label: &str,
    t: f64,
    ntotal: usize,
    passes: u32,
    ceiling: f64,
    best: &mut Option<(f64, String, u32)>,
) {
    let traffic = passes as f64 * 8.0 * ntotal as f64;
    let gbps = traffic / t;
    println!(
        "  {label}: {:.3} ms  ({:.0} Melem/s, {passes} passes, eff {:.1} GB/s = {:.0}% of ceiling, {:.0}% of 400 GB/s spec)",
        t * 1e3,
        ntotal as f64 / t / 1e6,
        gbps / 1e9,
        gbps / ceiling * 100.0,
        gbps / SPEC_BW * 100.0
    );
    if best.as_ref().map_or(true, |(bt, _, _)| t < *bt) {
        *best = Some((t, label.to_string(), passes));
    }
}

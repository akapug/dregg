#!/usr/bin/env python3
"""kem_delta_frontier.py — the compression <-> delta <-> ciphertext-size frontier for a
Kyber/ML-KEM-style lattice KEM (the KEM analog of the FRI parameter frontier).

INSIGHT (ember): a tight decryption-failure delta bound is an EFFICIENCY lever, not just
exactness. delta trades against ciphertext size via the compression parameters (d_u, d_v):
more compression -> smaller ciphertext -> larger rounding error -> higher delta. The gap
between a CONSERVATIVE proven delta and the TRUE (exact-convolution) delta is bandwidth left
on the table for any *tunable* variant.

This script computes the EXACT per-coefficient decryption-failure distribution by direct
(non-negative) convolution -- no FFT (FFT's signed inverse loses the ~1e-50 tail; direct
convolution of non-negative PMFs keeps it to double-precision relative error). It grounds
every formula in the dregg Lean sources:

  * compress/decompress:  metatheory/Dregg2/Crypto/MlKemCodec.lean:141-148
  * centered error cErr:   metatheory/Dregg2/Crypto/MlKemDelta.lean:2738  (dv), general d here
  * noise decomposition:   metatheory/Dregg2/Crypto/MlKemDelta.lean:11,556
        e_total = e^T r - s^T e1 + e2 + Dv - s^T Du
  * CBD(eta=2) law:        MlKemDelta.lean:812  weights (1,4,6,4,1)/16
  * fail threshold 832:    MlKemDelta.lean:156-157  (832 <= |ez|), q/4 window
  * params k=3,n=256,q=3329, eta1=eta2=2, standard d_u=10,d_v=4 -> 1088-byte ciphertext.
"""

import numpy as np

Q = 3329
N = 256          # ring degree (message coefficients)
K = 3            # module rank (ML-KEM-768)
ETA1 = 2
ETA2 = 2
THRESH = 832     # fail iff |w| >= 832  (MlKemDelta.lean:156)

# ---------------------------------------------------------------------------
# FIPS 203 Compress_d / Decompress_d  (MlKemCodec.lean:141-148), exact integer arithmetic.
def compress(d, x):
    base = 1 << d
    return ((2 * base * (x % Q) + Q) // (2 * Q)) % base

def decompress(d, y):
    base = 1 << d
    return (2 * Q * (y % base) + base) // (2 * base)

def cErr_value(d, x):
    """Centered compression rounding error, MlKemDelta.lean:2738 generalized to any d."""
    return ((decompress(d, compress(d, x)) - x + (Q // 2)) % Q) - (Q // 2)

# ---------------------------------------------------------------------------
# A PMF is (offset, probs): value v = offset + i has prob probs[i].
def pmf_normalize(counts, total, offset):
    return (offset, np.asarray(counts, dtype=np.float64) / total)

def cbd_pmf(eta):
    """CBD(eta): sum of eta bits minus eta bits; support [-eta,eta], binomial weights."""
    from math import comb
    size = 2 * eta + 1
    counts = np.array([comb(2 * eta, k) for k in range(size)], dtype=np.float64)
    return pmf_normalize(counts, counts.sum(), -eta)

def cErr_pmf(d):
    """Exact distribution of cErr_d(x) for x uniform on [0,Q)."""
    vals = [cErr_value(d, x) for x in range(Q)]
    lo, hi = min(vals), max(vals)
    counts = np.zeros(hi - lo + 1, dtype=np.float64)
    for v in vals:
        counts[v - lo] += 1.0
    return pmf_normalize(counts, Q, lo)

def conv(a, b):
    """Convolve two PMFs (direct, non-negative -> tail-accurate)."""
    (oa, pa), (ob, pb) = a, b
    return (oa + ob, np.convolve(pa, pb))

def product_pmf(a, b):
    """PMF of X*Y for independent X~a, Y~b."""
    (oa, pa), (ob, pb) = a, b
    acc = {}
    for i, pi in enumerate(pa):
        if pi == 0.0:
            continue
        x = oa + i
        for j, pj in enumerate(pb):
            if pj == 0.0:
                continue
            acc[x * (ob + j)] = acc.get(x * (ob + j), 0.0) + pi * pj
    lo, hi = min(acc), max(acc)
    counts = np.zeros(hi - lo + 1)
    for v, p in acc.items():
        counts[v - lo] = p
    return (lo, counts)

def nfold(pmf, n):
    """n-fold self-convolution via exponentiation by squaring (direct convolution)."""
    result = (0, np.array([1.0]))  # delta at 0
    base = pmf
    while n > 0:
        if n & 1:
            result = conv(result, base)
        n >>= 1
        if n > 0:
            base = conv(base, base)
    return result

def tail_prob(pmf, thresh):
    """Pr[|value| >= thresh]."""
    off, p = pmf
    idx = np.arange(off, off + len(p))
    return float(p[np.abs(idx) >= thresh].sum())

# ---------------------------------------------------------------------------
def per_coeff_delta(du, dv, chi_chi_1536):
    """Exact per-coefficient decryption-failure probability Pr[|e_total| >= 832].

    e_total = e^T r - s^T e1 + e2 + Dv - s^T Du
      e^T r, s^T e1 : each K*N=768 products chi*chi  -> 1536 chi*chi (precomputed)
      s^T Du        : K*N=768 products chi * cErr_du
      e2            : one chi
      Dv            : one cErr_dv
    """
    chi = cbd_pmf(ETA1)
    e2 = cbd_pmf(ETA2)
    su = product_pmf(cbd_pmf(ETA1), cErr_pmf(du))   # s_i * Du_i
    su_768 = nfold(su, K * N)
    w = conv(chi_chi_1536, su_768)
    w = conv(w, e2)
    w = conv(w, cErr_pmf(dv))
    return tail_prob(w, THRESH)

def ct_bytes(du, dv):
    """ML-KEM ciphertext size = 32*(d_u*k + d_v) bytes."""
    return 32 * (du * K + dv)

def log2(p):
    import math
    return float('-inf') if p <= 0 else math.log2(p)

# ---------------------------------------------------------------------------
def main():
    import math
    # Precompute the du-INDEPENDENT part: 1536 products chi*chi (e^T r and s^T e1 combined).
    chi_chi = product_pmf(cbd_pmf(ETA1), cbd_pmf(ETA1))
    chi_chi_1536 = nfold(chi_chi, 2 * K * N)

    print("=" * 78)
    print("dregg KEM delta<->compression<->ciphertext-size frontier")
    print(f"q={Q} k={K} n={N} eta1={ETA1} eta2={ETA2} fail-threshold |w|>={THRESH}")
    print("=" * 78)

    # Sanity: standard ML-KEM-768 (du=10, dv=4).
    p_std = per_coeff_delta(10, 4, chi_chi_1536)
    print(f"\nSTANDARD ML-KEM-768 (du=10, dv=4), ciphertext {ct_bytes(10,4)} B:")
    print(f"  per-coefficient delta   = 2^{log2(p_std):.2f}")
    print(f"  assembled (union n=256) = 2^{log2(p_std*256):.2f}   [FIPS-style count]")
    print(f"  assembled (union k*n=768)= 2^{log2(p_std*768):.2f}   [Lean MlKemDelta count]")
    print(f"  conservative proven      = 2^-153  (rZ_decapsFailure_le_delta153, MlKemDelta.lean:3182)")

    # cErr support/near-uniformity cross-check vs Lean cErr_bound / cErrFiber_le_16.
    e4 = cErr_pmf(4)
    off, p = e4
    vals = np.arange(off, off + len(p))
    support = (vals[p > 0].min(), vals[p > 0].max())
    counts = (p * Q).round().astype(int)
    print(f"\n  cErr_4 support = [{support[0]},{support[1]}] (Lean cErr_bound: [-104,104])")
    print(f"  cErr_4 max fiber count = {counts.max()} (Lean cErrFiber_le_16: <=16)")

    # ---- The frontier: grid-search (du,dv) for min ciphertext meeting a delta target ----
    DU_RANGE = range(6, 12)
    DV_RANGE = range(2, 8)
    targets = [("2^-128  (128-bit matched)", 2.0**-128),
               ("2^-164  (FIPS ML-KEM-768)", 2.0**-164)]

    print("\n" + "=" * 78)
    print("FULL GRID  (per-coeff delta and assembled delta over n=256; ciphertext bytes)")
    print("=" * 78)
    print(f"{'du':>3} {'dv':>3} {'ct_B':>6} {'log2 per-coeff':>15} {'log2 assembled(256)':>21}")
    grid = {}
    for du in DU_RANGE:
        for dv in DV_RANGE:
            pc = per_coeff_delta(du, dv, chi_chi_1536)
            grid[(du, dv)] = pc
            asm = pc * 256
            print(f"{du:>3} {dv:>3} {ct_bytes(du,dv):>6} {log2(pc):>15.2f} {log2(asm):>21.2f}")

    # For each target: min-ciphertext config under TIGHT (exact) vs CONSERVATIVE bound.
    # TIGHT: use the exact assembled delta = per_coeff*256.
    # CONSERVATIVE: model the conservative bound's LOOSENESS. The deployed conservative
    #   proof (2^-153 vs true assembled ~2^-171 at standard params) is ~18 bits loose on
    #   the ASSEMBLED bound. We apply that same ~18-bit penalty to the exact assembled
    #   delta at each (du,dv) as the conservative surrogate (the Chernoff route's method
    #   slack is roughly config-independent in bits; MlKemDelta.lean:74-77).
    p_std_asm = p_std * 256
    # The deployed conservative proof certifies 2^-153 while the exact assembled delta is
    # ~2^-168: the conservative bound is WEAKER by this many bits. As a config-independent
    # surrogate (the Chernoff-route method slack is ~constant in bits, MlKemDelta.lean:74-77)
    # we WEAKEN (raise) the exact delta by this margin to model what the conservative proof
    # could certify at each (du,dv).
    CONS_PENALTY_BITS = (-153.0) - log2(p_std_asm)  # >0 : bits the conservative bound is looser
    print(f"\nConservative-bound looseness at standard params: proven 2^-153 vs "
          f"exact assembled 2^{log2(p_std_asm):.2f} "
          f"= {CONS_PENALTY_BITS:.2f} bits of unused delta margin")

    print("\n" + "=" * 78)
    print("MIN-CIPHERTEXT CONFIG PER DELTA TARGET  (tight exact vs conservative surrogate)")
    print("=" * 78)
    for name, tgt in targets:
        lt = log2(tgt)
        def best(pen_bits):
            # pen_bits > 0 weakens (raises) delta -> less negative log2 -> harder to meet target.
            cands = []
            for (du, dv), pc in grid.items():
                asm_bits = log2(pc * 256) + pen_bits  # conservative surrogate = looser (higher delta)
                if asm_bits <= lt:
                    cands.append((ct_bytes(du, dv), du, dv, asm_bits))
            return min(cands) if cands else None
        bt = best(0.0)
        bc = best(CONS_PENALTY_BITS)
        print(f"\nTarget assembled delta <= {name}:")
        if bt:
            print(f"  TIGHT (exact conv):   du={bt[1]} dv={bt[2]}  ciphertext {bt[0]} B  "
                  f"(assembled 2^{bt[3]:.1f})")
        else:
            print("  TIGHT: no config in grid meets target")
        if bc:
            print(f"  CONS  (+{CONS_PENALTY_BITS:.0f} bit slack): du={bc[1]} dv={bc[2]}  "
                  f"ciphertext {bc[0]} B  (assembled 2^{bc[3]:.1f})")
        else:
            print(f"  CONS: no config in grid meets target under +{CONS_PENALTY_BITS:.0f}-bit slack")
        if bt and bc:
            print(f"  >>> tight bound saves {bc[0]-bt[0]} bytes/ciphertext "
                  f"({100*(bc[0]-bt[0])/bc[0]:.1f}%) at this target")

    print("\n" + "=" * 78)
    print("APPLICABILITY VERDICT")
    print("=" * 78)
    print("dregg deploys STANDARD ML-KEM-768 (dregg-pq/src/hybrid_kem.rs:61,371 MlKem768,")
    print("ml-kem v0.2.3) inside X-Wing / X25519MLKEM768. d_u=10,d_v=4 are FIPS-203-FIXED:")
    print("tuning them breaks interop with every conformant peer AND voids the FIPS")
    print("guarantee. So for the DEPLOYED KEM the tight-delta win is EXACTNESS ONLY")
    print("(2^-153 -> ~2^-171 assembled), NOT bandwidth. The byte savings above are the")
    print("quantified prize for a FUTURE dregg-native / custom lattice KEM that does not")
    print("need FIPS interop -- the map for whether firing the tight-delta formalization")
    print("(radix-2 interval-FFT campaign) buys deployable bandwidth.")


if __name__ == "__main__":
    main()

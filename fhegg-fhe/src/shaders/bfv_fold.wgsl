// BFV RNS fold-add — the aggregation hot path (memory-bandwidth bound at scale), on the GPU.
//
// One invocation = one output coefficient LANE (poly, rns-row, coeff). It sums that lane across all N
// input ciphertexts under the SAME conditional-subtract modular add the CPU `add_row` does
// (bfv_lean.rs:464: `s = a+b; if s>=q { s-q }`), so GPU and CPU agree bit-for-bit.
//
// WGSL has no u64. RNS residues are < q < 2^37, and every intermediate stays < 2q < 2^38, so a u64 carried
// as vec2<u32> = (lo, hi) with hi < 64 is exact — no Barrett, just add-with-carry + a compare-and-subtract.
// Summing N residues mod q is order-independent, so accumulate-and-reduce-each-step == the CPU pairwise fold.

struct Meta {
    n_cts   : u32,   // how many ciphertexts to fold
    n_lanes : u32,   // coefficient lanes per ciphertext (P * R * degree)
    row_len : u32,   // lanes per rns-row (= degree) — to pick this lane's modulus
    _pad    : u32,
    // three RNS moduli as (lo, hi); lane's row index = (lane / row_len) % 3
    q0 : vec2<u32>, q1 : vec2<u32>, q2 : vec2<u32>,
};

@group(0) @binding(0) var<uniform>              params : Meta;
@group(0) @binding(1) var<storage, read>        input  : array<u32>;  // N * n_lanes coeffs, each 2 u32 (lo,hi)
@group(0) @binding(2) var<storage, read_write>  output : array<u32>;  // n_lanes coeffs, each 2 u32

fn add64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let lo = a.x + b.x;
    let carry = select(0u, 1u, lo < a.x);   // wrapped => carry
    let hi = a.y + b.y + carry;
    return vec2<u32>(lo, hi);
}
fn ge64(a: vec2<u32>, b: vec2<u32>) -> bool {
    return a.y > b.y || (a.y == b.y && a.x >= b.x);
}
fn sub64(a: vec2<u32>, b: vec2<u32>) -> vec2<u32> {
    let borrow = select(0u, 1u, a.x < b.x);
    let lo = a.x - b.x;
    let hi = a.y - b.y - borrow;
    return vec2<u32>(lo, hi);
}
fn addmod(acc: vec2<u32>, x: vec2<u32>, q: vec2<u32>) -> vec2<u32> {
    var s = add64(acc, x);
    if (ge64(s, q)) { s = sub64(s, q); }     // one subtract suffices: acc<q, x<q => s<2q
    return s;
}

@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let lane = gid.x;
    if (lane >= params.n_lanes) { return; }

    // pick this lane's modulus by its rns-row
    let row = (lane / params.row_len) % 3u;
    var q = params.q0;
    if (row == 1u) { q = params.q1; }
    if (row == 2u) { q = params.q2; }

    var acc = vec2<u32>(0u, 0u);
    for (var ct: u32 = 0u; ct < params.n_cts; ct = ct + 1u) {
        let base = (ct * params.n_lanes + lane) * 2u;
        let x = vec2<u32>(input[base], input[base + 1u]);
        acc = addmod(acc, x, q);
    }
    let o = lane * 2u;
    output[o]      = acc.x;
    output[o + 1u] = acc.y;
}

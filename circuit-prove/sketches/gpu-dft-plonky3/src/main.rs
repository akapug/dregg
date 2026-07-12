//! `GpuDft` — a wgpu-backed implementation of the pinned Plonky3 (82cfad7)
//! `TwoAdicSubgroupDft<BabyBear>` trait: THE FIRST measurable GPU-prover
//! wiring increment (docs/deos/GPU-PROVER-WIRING-PLAN.md).
//!
//! What this is: the measured NTT kernels from ../wgpu-babybear-ntt, wired
//! BEHIND the exact trait seam `TwoAdicFriPcs::commit` calls
//! (fri/src/two_adic_pcs.rs:316-318 — `coset_lde_batch(evals, log_blowup,
//! shift)` with `shift = Val::GENERATOR / domain.shift()`), producing the
//! same `Evaluations = BitReversedMatrixView<RowMajorMatrix<BabyBear>>` type
//! as `Radix2DitParallel` (radix_2_dit_parallel.rs:146) so the PCS's
//! `.bit_reverse_rows().to_row_major_matrix()` stays free for both backends.
//!
//! Everything the trait costs is included in the measurement: the row-major
//! host layout (GPU transpose in/out), the iDFT half of the LDE, the coset
//! shift, the zero-pad (realized as the RISC0-style stage-skip: the first
//! `added_bits` DIT stages of a zero-padded input are pure replication, done
//! inside the expand kernel), the bit-reversed output row order, upload and
//! readback. Parity gate: bit-exact equality vs `Radix2DitParallel` on every
//! shape, both for `dft_batch` and `coset_lde_batch`.
//!
//! Data stays in Montgomery form end-to-end: `BabyBear` is repr(transparent)
//! over a Montgomery-form u32 (monty_31.rs:35-42), so upload/readback are
//! raw `&[u32]` casts — zero conversion, the unified-memory marshal story.
//!
//! Also included (CPU-only, for the wiring plan's Amdahl breakdown): the
//! outer-config BN254 MMCS commit rate — `MultiField32PaddingFreeSponge` +
//! `TruncatedPermutation` over `Poseidon2Bn254<3>` (the exact
//! `dregg_outer_config.rs:142-156` stack, dummy round constants — timing is
//! constant-independent) — measured at shrink-scale leaf counts.

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Instant;

use p3_baby_bear::BabyBear;
use p3_bn254::{Bn254, Poseidon2Bn254};
use p3_commit::Mmcs;
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::integers::QuotientMap;
use p3_field::{Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_matrix::bitrev::{BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_poseidon2::ExternalLayerConstants;
use p3_symmetric::{MultiField32PaddingFreeSponge, TruncatedPermutation};
use rand::Rng;
use rayon::prelude::*;

const P: u32 = 0x7800_0001; // BabyBear prime (baby_bear.rs:18)

// ---------------------------------------------------------------------------
// Host-side BabyBear helpers (canonical <-> Montgomery), same as the probes.
// ---------------------------------------------------------------------------

fn to_mont(a: u32) -> u32 {
    (((a as u64) << 32) % P as u64) as u32
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

/// `BabyBear` is repr(transparent) over its Montgomery-form u32
/// (monty-31/src/monty_31.rs:35-42) — reinterpret slices/Vecs directly.
fn bb_as_u32s(v: &[BabyBear]) -> &[u32] {
    unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u32, v.len()) }
}

fn u32s_into_bb(mut v: Vec<u32>) -> Vec<BabyBear> {
    // All GPU outputs are reduced (< P): mmul/addp/subp keep the Montgomery
    // invariant, so every u32 is a valid MontyField31 representation.
    let ptr = v.as_mut_ptr();
    let (len, cap) = (v.len(), v.capacity());
    std::mem::forget(v);
    unsafe { Vec::from_raw_parts(ptr as *mut BabyBear, len, cap) }
}

// ---------------------------------------------------------------------------
// WGSL kernels. The Montgomery core + fused-tile + register-radix kernels are
// the parity-proven ones from ../wgpu-babybear-ntt (GPU-PROVER-PROTOTYPE.md
// §9: 60-73% of measured memory-bandwidth ceiling on production shapes).
// New for the trait wiring: tiled transposes (row-major <-> column-contig)
// and the LDE "expand" kernel (iDFT finalize + coset scale + zero-pad
// stage-skip + bit-reversal, one fused pass).
// ---------------------------------------------------------------------------

const PRELUDE: &str = r#"
const P: u32 = 0x78000001u;
const MU: u32 = 0x88000001u;

// 32x32 -> 64 multiply via 16-bit split (WGSL has no u64 and no mulhi).
fn mul64(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xffffu; let a1 = a >> 16u;
    let b0 = b & 0xffffu; let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = p01 + p10;
    let carry_mid = select(0u, 0x10000u, mid < p01);
    let mid_lo = mid << 16u;
    let lo = p00 + mid_lo;
    let carry_lo = select(0u, 1u, lo < p00);
    let hi = p11 + (mid >> 16u) + carry_mid + carry_lo;
    return vec2<u32>(lo, hi);
}

// Montgomery product, exactly the p3 monty-31 reduce (utils.rs:105).
fn mmul(a: u32, b: u32) -> u32 {
    let ab = mul64(a, b);
    let t = ab.x * MU;
    let tp = mul64(t, P);
    var r: u32 = ab.y - tp.y;
    if (ab.y < tp.y) { r += P; }
    return r;
}

fn addp(a: u32, b: u32) -> u32 {
    let s = a + b;
    return select(s, s - P, s >= P);
}

fn subp(a: u32, b: u32) -> u32 {
    var r = a - b;
    if (a < b) { r += P; }
    return r;
}

@group(0) @binding(0) var<storage, read_write> data: array<u32>;
@group(0) @binding(1) var<storage, read> src: array<u32>;
@group(0) @binding(2) var<storage, read> tw: array<u32>;
"#;

/// Tiled transpose, row-major (H x W, W arbitrary) -> column-contiguous
/// (data[c*H + r] = src[r*W + c]). Each workgroup handles $RPT vertical
/// 16x16 sub-tiles so the x-grid stays under the 65535 dispatch limit.
const K_TRANS_IN: &str = r#"
var<workgroup> tile: array<u32, 272>;
@compute @workgroup_size(16, 16)
fn main(@builtin(workgroup_id) wg: vec3<u32>, @builtin(local_invocation_id) l: vec3<u32>) {
    let c0 = wg.y * 16u;
    for (var k = 0u; k < $RPT; k++) {
        let r0 = (wg.x * $RPT + k) * 16u;
        let cr = c0 + l.x;
        if (cr < $W) { tile[l.y * 17u + l.x] = src[(r0 + l.y) * $W + cr]; }
        workgroupBarrier();
        let cw = c0 + l.y;
        if (cw < $W) { data[cw * $H + r0 + l.x] = tile[l.x * 17u + l.y]; }
        workgroupBarrier();
    }
}
"#;

/// Tiled transpose out with bit-reversed row order: column-contiguous natural
/// (height N) -> row-major with row p stored at row bitrev(p)
/// (data[rev(p)*W + c] = src[c*N + p]) — the `Evaluations` inner layout that
/// makes the PCS's `.bit_reverse_rows().to_row_major_matrix()` free.
const K_TRANS_OUT_BITREV: &str = r#"
var<workgroup> tile: array<u32, 272>;
@compute @workgroup_size(16, 16)
fn main(@builtin(workgroup_id) wg: vec3<u32>, @builtin(local_invocation_id) l: vec3<u32>) {
    let c0 = wg.y * 16u;
    for (var k = 0u; k < $RPT; k++) {
        let p0 = (wg.x * $RPT + k) * 16u;
        let cr = c0 + l.y;
        if (cr < $W) { tile[l.y * 17u + l.x] = src[cr * $N + p0 + l.x]; }
        workgroupBarrier();
        let cw = c0 + l.x;
        let rp = reverseBits(p0 + l.y) >> $RSH;
        if (cw < $W) { data[rp * $W + cw] = tile[l.x * 17u + l.y]; }
        workgroupBarrier();
    }
}
"#;

/// LDE expand: one fused pass realizing (a) the iDFT finalize (index
/// reversal j -> (H-j) mod H plus the 1/H scale, folded into the shiftpow
/// table), (b) the coset scale shift^j, (c) the zero-pad to N = H << eb, and
/// (d) the first eb DIT stages of the size-N NTT — which on a zero-padded
/// input are pure replication (butterfly partner is always in the zero
/// region for s <= eb), the RISC0 ntt.metal stage-skip. Output is the
/// bit-reversed-layout state ready for DIT stages eb+1..logN.
/// state[p] = coeff[bitrev_N(p) mod H], coeff[j] = dft_H[(H-j) mod H] * sp[j].
const K_EXPAND: &str = r#"
@compute @workgroup_size(256)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let p = gid.x;
    let c = gid.y;
    let jj = (reverseBits(p) >> $RSHN) & $HM1;
    let jsrc = ($H - jj) & $HM1;
    data[c * $N + p] = mmul(src[c * $H + jsrc], tw[$SPOFF + jj]);
}
"#;

/// 2D-tiled first NTT pass (from the probe): folds the bit-reversal into the
/// load and runs stages 1..E1 in an 8-16 KiB shared tile over 2^LB adjacent
/// columns of the strided view; global reads/writes are coalesced runs.
/// Input: `src` column-contiguous natural order. Output: `data`.
const K_FUSED1B: &str = r#"
var<workgroup> tile: array<u32, $TILE>;
@compute @workgroup_size($WGSZ)
fn main(@builtin(local_invocation_id) l: vec3<u32>, @builtin(workgroup_id) wg: vec3<u32>) {
    let lid = l.x;
    let off = wg.y * $NN;
    let c0 = wg.x << $LB;
    for (var k = 0u; k < $TPT; k++) {
        let slot = lid + k * $WGSZ;
        let u = slot >> $LB;
        let b = slot & ((1u << $LB) - 1u);
        tile[((reverseBits(u) >> (32u - $E1)) << $LB) + b] = src[off + u * $WW + c0 + b];
    }
    workgroupBarrier();
    for (var s = 1u; s <= $E1; s++) {
        let half = 1u << (s - 1u);
        for (var k = 0u; k < $HBT; k++) {
            let sb = lid + k * $WGSZ;
            let b = sb & ((1u << $LB) - 1u);
            let bf = sb >> $LB;
            let j = bf & (half - 1u);
            let i1 = ((((bf >> (s - 1u)) << s) + j) << $LB) + b;
            let i2 = i1 + (half << $LB);
            let t = mmul(tile[i2], TW(j << ($LOGN - s)));
            let u2 = tile[i1];
            tile[i1] = addp(u2, t);
            tile[i2] = subp(u2, t);
        }
        workgroupBarrier();
    }
    for (var b2 = 0u; b2 < (1u << $LB); b2++) {
        let g = reverseBits(c0 + b2) >> (32u - ($LOGN - $E1));
        let obase = off + (g << $E1);
        for (var k = 0u; k < ($TILE >> $LB) / $WGSZ; k++) {
            let u = lid + k * $WGSZ;
            data[obase + u] = tile[(u << $LB) + b2];
        }
    }
}
"#;

/// Register-tier radix-2^R kernel (from the probe): R DIT stages
/// (stages L+1..L+R of the global size-2^LOGN DIT) fully unrolled in
/// registers, in-place on `data`. No workgroup memory, no barriers.
fn radix_kernel(n: u32, logn: u32, l: u32, r: u32, wgsz: u32) -> String {
    let m = 1u32 << r;
    let mut s = String::new();
    s.push_str(&format!(
        "@compute @workgroup_size({wgsz})\nfn main(@builtin(global_invocation_id) gid: vec3<u32>) {{\n    let t = gid.x;\n    let off = gid.y * {n}u;\n"
    ));
    if l == 0 {
        s.push_str(&format!(
            "    let tlow = 0u;\n    let base = off + (t << {r}u);\n"
        ));
    } else {
        s.push_str(&format!(
            "    let tlow = t & {}u;\n    let base = off + ((t >> {l}u) << {}u) + tlow;\n",
            (1u32 << l) - 1,
            l + r
        ));
    }
    for v in 0..m {
        s.push_str(&format!("    var r{v} = data[base + {}u];\n", v << l));
    }
    for st in 0..r {
        let lowmask = (1u32 << st) - 1;
        for p in 0..(m >> 1) {
            let v0 = ((p & !lowmask) << 1) | (p & lowmask);
            let v1 = v0 | (1 << st);
            let jlit = (p & lowmask) << l;
            let sh = logn - l - st - 1;
            s.push_str(&format!(
                "    {{ let tt = mmul(r{v1}, TW(({jlit}u + tlow) << {sh}u)); let uu = r{v0}; r{v0} = addp(uu, tt); r{v1} = subp(uu, tt); }}\n"
            ));
        }
    }
    for v in 0..m {
        s.push_str(&format!("    data[base + {}u] = r{v};\n", v << l));
    }
    s.push_str("}\n");
    s
}

/// Twiddle accessor at a baked element offset into the shared `tw` buffer
/// (the buffer holds [tw_N | tw_H | shiftpow] regions for the LDE flow).
fn tw_def(off: u32) -> String {
    format!("fn TW(i: u32) -> u32 {{ return tw[{off}u + i]; }}\n")
}

fn subst(template: &str, pairs: &[(&str, u32)]) -> String {
    let mut s = template.to_string();
    for (k, v) in pairs {
        s = s.replace(k, &format!("{v}u"));
    }
    s
}

/// Split `total` DIT stages into register-radix chunk sizes <= 5 (5s and 4s
/// preferred; never emits a trailing 1 unless total == 1).
fn split_stages(total: u32) -> Vec<u32> {
    let mut out = Vec::new();
    let mut rem = total;
    while rem > 0 {
        match rem {
            6 => {
                out.extend([3, 3]);
                rem = 0;
            }
            7 => {
                out.extend([4, 3]);
                rem = 0;
            }
            r if r <= 5 => {
                out.push(r);
                rem = 0;
            }
            _ => {
                out.push(5);
                rem -= 5;
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// GPU context + the GpuDft trait impl
// ---------------------------------------------------------------------------

struct Bufs {
    a: wgpu::Buffer,
    b: wgpu::Buffer,
    read: wgpu::Buffer,
    /// capacity of a/b/read in u32s
    cap_u32s: usize,
    bg_ab: wgpu::BindGroup, // data = a (rw), src = b (ro)
    bg_ba: wgpu::BindGroup, // data = b (rw), src = a (ro)
}

struct GpuCtx {
    device: wgpu::Device,
    queue: wgpu::Queue,
    bgl: wgpu::BindGroupLayout,
    pipe_layout: wgpu::PipelineLayout,
    pipelines: HashMap<String, wgpu::ComputePipeline>,
    tw_buf: wgpu::Buffer,
    tw_cap_u32s: usize,
    /// (logh, logn, shift_canonical) currently uploaded in tw_buf
    tw_key: Option<(u32, u32, u32)>,
    bufs: Option<Bufs>,
    max_buf_u32s: usize,
    adapter_name: String,
}

impl GpuCtx {
    fn new() -> Option<Self> {
        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))?;
        let info = adapter.get_info();
        let lims = adapter.limits();
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: None,
                required_features: wgpu::Features::empty(),
                required_limits: lims.clone(),
                memory_hints: Default::default(),
            },
            None,
        ))
        .ok()?;
        let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
            label: None,
            entries: &[
                wgpu::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: false },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                wgpu::BindGroupLayoutEntry {
                    binding: 1,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: true },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
                wgpu::BindGroupLayoutEntry {
                    binding: 2,
                    visibility: wgpu::ShaderStages::COMPUTE,
                    ty: wgpu::BindingType::Buffer {
                        ty: wgpu::BufferBindingType::Storage { read_only: true },
                        has_dynamic_offset: false,
                        min_binding_size: None,
                    },
                    count: None,
                },
            ],
        });
        let pipe_layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
            label: None,
            bind_group_layouts: &[&bgl],
            push_constant_ranges: &[],
        });
        let max_buf_u32s = (lims
            .max_buffer_size
            .min(lims.max_storage_buffer_binding_size as u64)
            .min(1 << 31) as usize)
            / 4;
        // twiddle buffer starts small, grows on demand
        let tw_cap_u32s = 1 << 20;
        let tw_buf = device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("tw"),
            size: (tw_cap_u32s * 4) as u64,
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        Some(GpuCtx {
            device,
            queue,
            bgl,
            pipe_layout,
            pipelines: HashMap::new(),
            tw_buf,
            tw_cap_u32s,
            tw_key: None,
            bufs: None,
            max_buf_u32s,
            adapter_name: format!("{} ({:?})", info.name, info.backend),
        })
    }

    fn make_bind_groups(
        &self,
        a: &wgpu::Buffer,
        b: &wgpu::Buffer,
    ) -> (wgpu::BindGroup, wgpu::BindGroup) {
        let mk = |data: &wgpu::Buffer, src: &wgpu::Buffer| {
            self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: None,
                layout: &self.bgl,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: data.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: src.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: self.tw_buf.as_entire_binding(),
                    },
                ],
            })
        };
        (mk(a, b), mk(b, a))
    }

    fn ensure_bufs(&mut self, need_u32s: usize) {
        let need = need_u32s.next_power_of_two().max(1 << 22);
        if self.bufs.as_ref().map_or(true, |b| b.cap_u32s < need) {
            let sz = (need * 4) as u64;
            let mk = |label: &str| {
                self.device.create_buffer(&wgpu::BufferDescriptor {
                    label: Some(label),
                    size: sz,
                    usage: wgpu::BufferUsages::STORAGE
                        | wgpu::BufferUsages::COPY_SRC
                        | wgpu::BufferUsages::COPY_DST,
                    mapped_at_creation: false,
                })
            };
            let a = mk("work_a");
            let b = mk("work_b");
            let read = self.device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("read"),
                size: sz,
                usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });
            let (bg_ab, bg_ba) = self.make_bind_groups(&a, &b);
            self.bufs = Some(Bufs {
                a,
                b,
                read,
                cap_u32s: need,
                bg_ab,
                bg_ba,
            });
        }
    }

    /// Ensure the tw buffer holds [tw_N (n/2) | tw_H (h/2) | shiftpow (h)]
    /// for the given (logh, logn, shift). For plain DFT flows logh == logn
    /// and the shiftpow region is unused. Returns (twn_off, twh_off, sp_off).
    fn ensure_twiddles(&mut self, logh: u32, logn: u32, shift_c: u32) -> (u32, u32, u32) {
        let n = 1usize << logn;
        let h = 1usize << logh;
        let twn_off = 0u32;
        let twh_off = (n / 2) as u32;
        let sp_off = twh_off + (h / 2) as u32;
        let total = sp_off as usize + h;
        if self.tw_key == Some((logh, logn, shift_c)) {
            return (twn_off, twh_off, sp_off);
        }
        if self.tw_cap_u32s < total {
            let cap = total.next_power_of_two();
            self.tw_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
                label: Some("tw"),
                size: (cap * 4) as u64,
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
                mapped_at_creation: false,
            });
            self.tw_cap_u32s = cap;
            // bind groups reference the old tw buffer — rebuild
            if let Some(b) = &self.bufs {
                let (bg_ab, bg_ba) = self.make_bind_groups(&b.a, &b.b);
                let bufs = self.bufs.as_mut().unwrap();
                bufs.bg_ab = bg_ab;
                bufs.bg_ba = bg_ba;
            }
        }
        let mut tv = vec![0u32; total];
        let wn = BabyBear::two_adic_generator(logn as usize).as_canonical_u32() as u64;
        let mut acc = 1u64;
        for t in 0..n / 2 {
            tv[t] = to_mont(acc as u32);
            acc = mulmod(acc, wn);
        }
        let wh = BabyBear::two_adic_generator(logh as usize).as_canonical_u32() as u64;
        let mut acc = 1u64;
        for t in 0..h / 2 {
            tv[twh_off as usize + t] = to_mont(acc as u32);
            acc = mulmod(acc, wh);
        }
        // shiftpow[j] = mont( (1/h) * shift^j )  — the iDFT 1/h scale folded in.
        let hinv = powmod(h as u64, (P - 2) as u64);
        let mut acc = hinv;
        for j in 0..h {
            tv[sp_off as usize + j] = to_mont(acc as u32);
            acc = mulmod(acc, shift_c as u64);
        }
        self.queue
            .write_buffer(&self.tw_buf, 0, bytemuck::cast_slice(&tv));
        self.tw_key = Some((logh, logn, shift_c));
        (twn_off, twh_off, sp_off)
    }

    fn pipeline(&mut self, key: String, wgsl: &str) -> wgpu::ComputePipeline {
        if let Some(p) = self.pipelines.get(&key) {
            return p.clone();
        }
        // Trusted module + no workgroup zero-init: both measured as decisive
        // on Metal (GPU-PROVER-PROTOTYPE.md §9, "the two toolchain taxes").
        // Sound here: kernels are index-audited and every tile slot is
        // written before read; parity vs p3 re-validates every run.
        let module = unsafe {
            self.device.create_shader_module_trusted(
                wgpu::ShaderModuleDescriptor {
                    label: Some(&key),
                    source: wgpu::ShaderSource::Wgsl(wgsl.into()),
                },
                wgpu::ShaderRuntimeChecks::unchecked(),
            )
        };
        let p = self
            .device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(&key),
                layout: Some(&self.pipe_layout),
                module: &module,
                entry_point: Some("main"),
                compilation_options: wgpu::PipelineCompilationOptions {
                    zero_initialize_workgroup_memory: false,
                    ..Default::default()
                },
                cache: None,
            });
        self.pipelines.insert(key, p.clone());
        p
    }
}

/// Which buffer a dispatch writes (selects the bind group).
#[derive(Clone, Copy, PartialEq)]
enum Target {
    A,
    B,
}

/// wgpu-backed `TwoAdicSubgroupDft<BabyBear>`. `Default` is cheap (trait
/// bound, dft/src/traits.rs:27); device acquisition is lazy on first use and
/// falls back to `Radix2DitParallel` forever if no adapter (or for heights
/// below the GPU-worthwhile threshold).
#[derive(Clone, Default)]
pub struct GpuDft {
    cpu: Radix2DitParallel<BabyBear>,
    ctx: Arc<OnceLock<Option<Mutex<GpuCtx>>>>,
}

/// Heights below this stay on the CPU path (dispatch overhead dominates).
const MIN_GPU_LOG_H: u32 = 12;
const E1: u32 = 8; // fused first-pass stages (tile 2^(E1+LB) u32 = 8 KiB)
const LB: u32 = 3; // adjacent columns per fused1b workgroup

impl GpuDft {
    fn gpu(&self) -> Option<&Mutex<GpuCtx>> {
        self.ctx
            .get_or_init(|| GpuCtx::new().map(Mutex::new))
            .as_ref()
    }

    pub fn adapter_name(&self) -> Option<String> {
        self.gpu().map(|m| m.lock().unwrap().adapter_name.clone())
    }

    /// The full GPU LDE/DFT flow. `added_bits == 0` with `shift == ONE` and
    /// `idft == false` is the plain forward DFT. Returns the bit-reversed-row
    /// inner matrix (natural row i stored at row bitrev(i)).
    fn gpu_flow(
        &self,
        ctx: &mut GpuCtx,
        mat: &RowMajorMatrix<BabyBear>,
        added_bits: u32,
        shift: BabyBear,
        lde: bool,
    ) -> Vec<u32> {
        let h = mat.height();
        let w = mat.width();
        let logh = h.trailing_zeros();
        let logn = logh + added_bits;
        let n = 1usize << logn;
        let shift_c = shift.as_canonical_u32();
        let (twn_off, twh_off, sp_off) = ensure_tw(ctx, logh, logn, shift_c, lde);

        // Column chunking: both work buffers must hold n * wb u32s.
        let wb_max = (ctx.max_buf_u32s / n).min(w).max(1);
        let mut out: Vec<u32> = Vec::new();
        let single = wb_max >= w;
        if !single {
            out = vec![0u32; n * w];
        }

        let vals = bb_as_u32s(&mat.values);
        let mut c0 = 0usize;
        while c0 < w {
            let wb = wb_max.min(w - c0);
            ctx.ensure_bufs(n * wb);

            // 1. upload the chunk's rows (row-major h x wb)
            if single {
                let bufs = ctx.bufs.as_ref().unwrap();
                ctx.queue
                    .write_buffer(&bufs.a, 0, bytemuck::cast_slice(vals));
            } else {
                let mut staging = vec![0u32; h * wb];
                staging
                    .par_chunks_mut(wb)
                    .enumerate()
                    .for_each(|(r, dst)| dst.copy_from_slice(&vals[r * w + c0..r * w + c0 + wb]));
                let bufs = ctx.bufs.as_ref().unwrap();
                ctx.queue
                    .write_buffer(&bufs.a, 0, bytemuck::cast_slice(&staging));
            }

            // 2. build the dispatch plan
            let mut plan: Vec<(wgpu::ComputePipeline, Target, (u32, u32))> = Vec::new();
            let wgsz = 256u32;

            // 2a. transpose in: A (row-major) -> B (column-contiguous)
            {
                let row_tiles = (h as u32) / 16;
                let rpt = row_tiles.div_ceil(32768).max(1);
                let key = format!("trans_in_h{logh}_w{w}_wb{wb}_rpt{rpt}");
                let wgsl = format!(
                    "{}{}",
                    PRELUDE,
                    subst(
                        K_TRANS_IN,
                        &[("$H", h as u32), ("$W", wb as u32), ("$RPT", rpt)]
                    )
                );
                let p = ctx.pipeline(key, &wgsl);
                plan.push((
                    p,
                    Target::B,
                    (row_tiles.div_ceil(rpt), (wb as u32).div_ceil(16)),
                ));
            }

            // 2b. size-h NTT: fused1b (B -> A) + register-radix chunks in-place on A
            {
                let tile1 = 1u32 << (E1 + LB);
                let key = format!("fused1b_l{logh}_two{twh_off}");
                let wgsl = format!(
                    "{}{}{}",
                    PRELUDE,
                    tw_def(twh_off),
                    subst(
                        K_FUSED1B,
                        &[
                            ("$TILE", tile1),
                            ("$TPT", tile1 / wgsz),
                            ("$HBT", tile1 / 2 / wgsz),
                            ("$WGSZ", wgsz),
                            ("$NN", h as u32),
                            ("$LOGN", logh),
                            ("$E1", E1),
                            ("$LB", LB),
                            ("$WW", (h as u32) >> E1),
                        ],
                    )
                );
                let p = ctx.pipeline(key, &wgsl);
                plan.push((p, Target::A, ((h as u32) >> (E1 + LB), wb as u32)));
                let mut l = E1;
                for r in split_stages(logh - E1) {
                    let key = format!("radix_l{logh}_s{l}_r{r}_two{twh_off}");
                    let wgsl = format!(
                        "{}{}{}",
                        PRELUDE,
                        tw_def(twh_off),
                        radix_kernel(h as u32, logh, l, r, wgsz)
                    );
                    let p = ctx.pipeline(key, &wgsl);
                    plan.push((p, Target::A, (((h as u32) >> r).div_ceil(wgsz), wb as u32)));
                    l += r;
                }
            }

            let final_src = if lde {
                // 2c. expand: A (dft_h, natural col-contig) -> B (post-eb-stage
                // bit-reversed state of the size-n DIT, coset-scaled)
                {
                    let key = format!("expand_h{logh}_n{logn}_sp{sp_off}");
                    let wgsl = format!(
                        "{}{}",
                        PRELUDE,
                        subst(
                            K_EXPAND,
                            &[
                                ("$RSHN", 32 - logn),
                                ("$HM1", (h - 1) as u32),
                                ("$H", h as u32),
                                ("$N", n as u32),
                                ("$SPOFF", sp_off),
                            ],
                        )
                    );
                    let p = ctx.pipeline(key, &wgsl);
                    plan.push((p, Target::B, ((n as u32).div_ceil(wgsz), wb as u32)));
                }
                // 2d. size-n DIT stages eb+1..logn, in-place on B (stage-skip:
                // the first eb stages were replication, done by expand)
                let mut l = added_bits;
                for r in split_stages(logn - added_bits) {
                    let key = format!("radix_l{logn}_s{l}_r{r}_two{twn_off}");
                    let wgsl = format!(
                        "{}{}{}",
                        PRELUDE,
                        tw_def(twn_off),
                        radix_kernel(n as u32, logn, l, r, wgsz)
                    );
                    let p = ctx.pipeline(key, &wgsl);
                    plan.push((p, Target::B, (((n as u32) >> r).div_ceil(wgsz), wb as u32)));
                    l += r;
                }
                Target::B
            } else {
                Target::A
            };

            // 2e. transpose out with bit-reversed rows: (natural col-contig) ->
            // row-major, row p at bitrev(p)
            let read_from = {
                let row_tiles = (n as u32) / 16;
                let rpt = row_tiles.div_ceil(32768).max(1);
                let key = format!("trans_out_n{logn}_w{w}_wb{wb}_rpt{rpt}");
                let wgsl = format!(
                    "{}{}",
                    PRELUDE,
                    subst(
                        K_TRANS_OUT_BITREV,
                        &[
                            ("$N", n as u32),
                            ("$W", wb as u32),
                            ("$RSH", 32 - logn),
                            ("$RPT", rpt),
                        ],
                    )
                );
                let p = ctx.pipeline(key, &wgsl);
                let tgt = if final_src == Target::B {
                    Target::A
                } else {
                    Target::B
                };
                plan.push((p, tgt, (row_tiles.div_ceil(rpt), (wb as u32).div_ceil(16))));
                tgt
            };

            // 3. encode + submit + read back
            let bufs = ctx.bufs.as_ref().unwrap();
            let mut enc = ctx.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                for (pipe, tgt, (x, y)) in &plan {
                    pass.set_bind_group(
                        0,
                        match tgt {
                            Target::A => &bufs.bg_ab,
                            Target::B => &bufs.bg_ba,
                        },
                        &[],
                    );
                    pass.set_pipeline(pipe);
                    pass.dispatch_workgroups(*x, *y, 1);
                }
            }
            let out_buf = match read_from {
                Target::A => &bufs.a,
                Target::B => &bufs.b,
            };
            enc.copy_buffer_to_buffer(out_buf, 0, &bufs.read, 0, (n * wb * 4) as u64);
            ctx.queue.submit([enc.finish()]);
            let slice = bufs.read.slice(..(n * wb * 4) as u64);
            slice.map_async(wgpu::MapMode::Read, |_| {});
            ctx.device.poll(wgpu::Maintain::Wait);
            {
                let mapped = slice.get_mapped_range();
                let chunk: &[u32] = bytemuck::cast_slice(&mapped);
                if single {
                    out = chunk.to_vec();
                } else {
                    out.par_chunks_mut(w)
                        .zip(chunk.par_chunks(wb))
                        .for_each(|(dst, srcrow)| dst[c0..c0 + wb].copy_from_slice(srcrow));
                }
            }
            bufs.read.unmap();
            c0 += wb;
        }
        out
    }
}

/// Free-fn shim (borrow-checker friendliness for the twiddle setup).
fn ensure_tw(ctx: &mut GpuCtx, logh: u32, logn: u32, shift_c: u32, lde: bool) -> (u32, u32, u32) {
    if lde {
        ctx.ensure_twiddles(logh, logn, shift_c)
    } else {
        // plain DFT: only the size-h table is needed; lay it out the same way
        ctx.ensure_twiddles(logh, logn, 1)
    }
}

impl TwoAdicSubgroupDft<BabyBear> for GpuDft {
    type Evaluations = BitReversedMatrixView<RowMajorMatrix<BabyBear>>;

    fn dft_batch(&self, mat: RowMajorMatrix<BabyBear>) -> Self::Evaluations {
        let h = mat.height();
        if h < (1 << MIN_GPU_LOG_H) || !h.is_power_of_two() || mat.width() == 0 {
            return self.cpu.dft_batch(mat);
        }
        let Some(gm) = self.gpu() else {
            return self.cpu.dft_batch(mat);
        };
        let mut ctx = gm.lock().unwrap();
        let out = self.gpu_flow(&mut ctx, &mat, 0, BabyBear::ONE, false);
        RowMajorMatrix::new(u32s_into_bb(out), mat.width()).bit_reverse_rows()
    }

    fn coset_lde_batch(
        &self,
        mat: RowMajorMatrix<BabyBear>,
        added_bits: usize,
        shift: BabyBear,
    ) -> Self::Evaluations {
        let h = mat.height();
        if h < (1 << MIN_GPU_LOG_H) || !h.is_power_of_two() || mat.width() == 0 {
            return self.cpu.coset_lde_batch(mat, added_bits, shift);
        }
        let Some(gm) = self.gpu() else {
            return self.cpu.coset_lde_batch(mat, added_bits, shift);
        };
        let mut ctx = gm.lock().unwrap();
        let out = self.gpu_flow(&mut ctx, &mat, added_bits as u32, shift, true);
        RowMajorMatrix::new(u32s_into_bb(out), mat.width()).bit_reverse_rows()
    }
}

// ---------------------------------------------------------------------------
// Harness: parity gate + prover-scale head-to-head + Amdahl component bench
// ---------------------------------------------------------------------------

fn rand_matrix(rows: usize, cols: usize, rng: &mut impl Rng) -> RowMajorMatrix<BabyBear> {
    let values: Vec<BabyBear> = (0..rows * cols)
        .map(|_| BabyBear::from_int(rng.gen_range(0..P)))
        .collect();
    RowMajorMatrix::new(values, cols)
}

/// The exact expression `TwoAdicFriPcs::commit` evaluates per matrix
/// (two_adic_pcs.rs:316-318): LDE, bit-reverse the rows, materialize.
fn pcs_lde<D: TwoAdicSubgroupDft<BabyBear>>(
    dft: &D,
    mat: RowMajorMatrix<BabyBear>,
    log_blowup: usize,
    shift: BabyBear,
) -> RowMajorMatrix<BabyBear> {
    dft.coset_lde_batch(mat, log_blowup, shift)
        .bit_reverse_rows()
        .to_row_major_matrix()
}

fn main() {
    let mut rng = rand::thread_rng();
    let gpu_dft = GpuDft::default();
    let cpu_dft = Radix2DitParallel::<BabyBear>::default();
    let shift = BabyBear::GENERATOR; // what the PCS passes for trace commits

    let Some(name) = gpu_dft.adapter_name() else {
        eprintln!("NO GPU ADAPTER — cannot run the increment gate");
        std::process::exit(1);
    };
    println!("adapter: {name}");
    println!(
        "threads: {} (rayon), CPU baseline = Radix2DitParallel (pinned p3 82cfad7)\n",
        rayon::current_num_threads()
    );

    // ---------------- 1. parity gate ----------------
    println!("== parity gate (bit-exact vs Radix2DitParallel) ==");
    let mut all_ok = true;
    // dft_batch shapes (height, width) — powers of two and awkward widths
    for &(logh, w) in &[(12u32, 5usize), (13, 32), (15, 7), (16, 64)] {
        let mat = rand_matrix(1 << logh, w, &mut rng);
        let got = gpu_dft.dft_batch(mat.clone()).to_row_major_matrix();
        let want = cpu_dft.dft_batch(mat).to_row_major_matrix();
        let ok = got.values == want.values;
        all_ok &= ok;
        println!(
            "  dft_batch 2^{logh} x {w}: {}",
            if ok { "OK" } else { "MISMATCH" }
        );
    }
    // coset_lde_batch shapes (height, width, added_bits, shift)
    let shift2 = BabyBear::from_int(1234567u32);
    for &(logh, w, ab, s) in &[
        (12u32, 3usize, 1usize, shift),
        (13, 10, 3, shift),
        (14, 33, 2, shift2),
        (15, 64, 3, shift),
    ] {
        let mat = rand_matrix(1 << logh, w, &mut rng);
        let got = gpu_dft
            .coset_lde_batch(mat.clone(), ab, s)
            .to_row_major_matrix();
        let want = cpu_dft.coset_lde_batch(mat, ab, s).to_row_major_matrix();
        let ok = got.values == want.values;
        all_ok &= ok;
        println!(
            "  coset_lde_batch 2^{logh} x {w} +{ab} bits: {}",
            if ok { "OK" } else { "MISMATCH" }
        );
    }
    if !all_ok {
        println!("\nPARITY FAILURE — gate red, aborting");
        std::process::exit(1);
    }
    println!("  all parity checks green\n");

    // ---------------- 2. prover-scale head-to-head ----------------
    // The shrink prover's real LDE shapes: log_blowup 3 (blowup 8,
    // dregg_outer_config.rs:127), degree_bits [9,9,15,14,15] (HORIZONLOG
    // 2026-07-12) -> the big tables are 2^15 rows -> 2^18-row LDEs. Widths
    // bracket the unknown per-table column counts (total opened cols ~752
    // per WRAP-NATIVE-HASH-DECISION.md). 2^18 x 32 is the tall stress shape
    // (a 2^21-row LDE, the blowup-64-era size).
    println!("== prover-scale: pcs-shaped coset_lde_batch (blowup 8, shift = GENERATOR) ==");
    println!("   (timed expression = dft.coset_lde_batch(mat, 3, g).bit_reverse_rows().to_row_major_matrix(),");
    println!(
        "    exactly two_adic_pcs.rs:316-318; GPU time includes upload, transposes, readback)"
    );
    let mut rows_summary: Vec<String> = Vec::new();
    for &(logh, w) in &[(15u32, 64usize), (15, 256), (15, 452), (18, 32)] {
        let ab = 3usize;
        let mat = rand_matrix(1 << logh, w, &mut rng);

        // parity at full scale first (uses the same warmed pipelines)
        let got = pcs_lde(&gpu_dft, mat.clone(), ab, shift);
        let want = pcs_lde(&cpu_dft, mat.clone(), ab, shift);
        assert_eq!(
            got.values, want.values,
            "FULL-SCALE PARITY FAILURE at 2^{logh} x {w}"
        );

        // CPU: best of 3
        let mut cpu_best = f64::MAX;
        for _ in 0..3 {
            let m = mat.clone();
            let t0 = Instant::now();
            let r = pcs_lde(&cpu_dft, m, ab, shift);
            cpu_best = cpu_best.min(t0.elapsed().as_secs_f64());
            std::hint::black_box(&r.values[0]);
        }
        // GPU: best of 3 (pipelines + twiddles warmed by the parity run)
        let mut gpu_best = f64::MAX;
        for _ in 0..3 {
            let m = mat.clone();
            let t0 = Instant::now();
            let r = pcs_lde(&gpu_dft, m, ab, shift);
            gpu_best = gpu_best.min(t0.elapsed().as_secs_f64());
            std::hint::black_box(&r.values[0]);
        }
        let n_out = (1usize << (logh + ab as u32)) * w;
        let line = format!(
            "  2^{logh} x {w:>3} -> 2^{} LDE ({:>4} MiB out): CPU {:>8.1} ms | GPU {:>7.1} ms | {:>5.1}x  (parity OK)",
            logh + ab as u32,
            n_out * 4 >> 20,
            cpu_best * 1e3,
            gpu_best * 1e3,
            cpu_best / gpu_best
        );
        println!("{line}");
        rows_summary.push(line);
    }

    // dft_batch head-to-head at one prover-adjacent shape (the quotient-eval
    // and opening paths also call plain dft/idft)
    {
        let mat = rand_matrix(1 << 18, 64, &mut rng);
        let got = gpu_dft.dft_batch(mat.clone()).to_row_major_matrix();
        let want = cpu_dft.dft_batch(mat.clone()).to_row_major_matrix();
        assert_eq!(got.values, want.values, "dft_batch full-scale parity");
        let mut cpu_best = f64::MAX;
        let mut gpu_best = f64::MAX;
        for _ in 0..3 {
            let m = mat.clone();
            let t0 = Instant::now();
            let _ = std::hint::black_box(cpu_dft.dft_batch(m).to_row_major_matrix().values[0]);
            cpu_best = cpu_best.min(t0.elapsed().as_secs_f64());
            let m = mat.clone();
            let t0 = Instant::now();
            let _ = std::hint::black_box(gpu_dft.dft_batch(m).to_row_major_matrix().values[0]);
            gpu_best = gpu_best.min(t0.elapsed().as_secs_f64());
        }
        println!(
            "  dft_batch 2^18 x 64 (materialized natural order): CPU {:>8.1} ms | GPU {:>7.1} ms | {:>5.1}x",
            cpu_best * 1e3,
            gpu_best * 1e3,
            cpu_best / gpu_best
        );
    }

    // ---------------- 3. Amdahl component: the outer BN254 MMCS commit ----------------
    // The OTHER seam (the hash-dominated one). CPU-only measurement of the
    // exact dregg_outer_config.rs:142-156 stack: MultiField32PaddingFreeSponge
    // <BabyBear, Bn254, Poseidon2Bn254<3>, 3, 2, 1> leaves + TruncatedPermutation
    // compress, MerkleTreeMmcs commit (rayon-parallel). Round constants are
    // dummies — Poseidon2 timing is constant-independent.
    println!("\n== Amdahl component (CPU): outer BN254-native MMCS commit rate ==");
    {
        let initial: Vec<[Bn254; 3]> = (0..4)
            .map(|i| [0u64, 1, 2].map(|j| Bn254::from_int(i * 3 + j + 1)))
            .collect();
        let terminal: Vec<[Bn254; 3]> = (0..4)
            .map(|i| [0u64, 1, 2].map(|j| Bn254::from_int(100 + i * 3 + j)))
            .collect();
        let internal: Vec<Bn254> = (0..56).map(|i| Bn254::from_int(200 + i as u64)).collect();
        let perm =
            Poseidon2Bn254::<3>::new(ExternalLayerConstants::new(initial, terminal), internal);
        type OuterHash = MultiField32PaddingFreeSponge<BabyBear, Bn254, Poseidon2Bn254<3>, 3, 2, 1>;
        type OuterCompress = TruncatedPermutation<Poseidon2Bn254<3>, 2, 1, 3>;
        let hash = OuterHash::new(perm.clone()).expect("rate < width");
        let compress = OuterCompress::new(perm);
        let mmcs = MerkleTreeMmcs::<BabyBear, Bn254, OuterHash, OuterCompress, 2, 1>::new(
            hash, compress, 0,
        );
        for &(logr, w) in &[(14u32, 452usize), (16, 452)] {
            let rows = 1usize << logr;
            let mat = rand_matrix(rows, w, &mut rng);
            let t0 = Instant::now();
            let (_c, _d) = mmcs.commit(vec![mat]);
            let dt = t0.elapsed().as_secs_f64();
            // leaf perms: 16 BabyBear limbs per t=3/rate-2 permutation
            // (8 limbs per rate slot x 2 slots); plus ~rows compresses.
            let perms = rows * w.div_ceil(16) + rows;
            println!(
                "  commit 2^{logr} x {w}: {:>7.2} s  (~{:.2} Mperm, {:>6.2} us/perm rayon, {:>5.2} Mperm/s)",
                dt,
                perms as f64 / 1e6,
                dt / perms as f64 * 1e6,
                perms as f64 / dt / 1e6
            );
        }
        println!("  (scale: a 2^18-row x 452-col LDE commit = ~7.6M leaf perms -> extrapolate from the rate above)");
    }

    println!("\nGATE GREEN: parity bit-exact vs Radix2DitParallel on every shape; speedups above.");
}

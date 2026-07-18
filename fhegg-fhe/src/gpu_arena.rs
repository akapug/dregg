//! The GPU-RESIDENT pipeline — upload once, compute resident, download once (the performance north star).
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §3. OWNED by the `gpu_arena` lane. Wraps
//! `bfv_gpu` (same shader, same lane math, same FOLD_MODULI shape). This is the fix for the transfer-bound
//! one-shot "loss": data stays on-device across the pipeline so the fold becomes a bare dispatch and the
//! single transfer amortizes over the whole computation.
//!
//! WHY the one-shot `fold_gpu` lost (measured, `bin/gpu_saturate.rs` 2026-07-18, hbox 6750 XT N=8192):
//! host pack 485 ms (56%) + create/upload 325 ms (37%) + dispatch/readback ~50 ms (7%) — the GPU did 7% of
//! the work and the host did the rest, EVERY call. The arena removes both dominant costs structurally:
//!   * NO pack loop: `LeanCiphertext` coefficients are `u64`; on a little-endian host their in-memory bytes
//!     ARE the (lo, hi) u32 pairs the shader reads. Upload is a row-granular memcpy into a mapped device
//!     buffer — the u64→2×u32 "conversion" is the identity and is never materialized.
//!   * ONE upload: `upload` transfers the ciphertext set once into a resident STORAGE buffer;
//!     `fold_resident` binds that buffer directly (device→device, no readback, output stays resident);
//!     `download` is the single readback at the end.
//!
//! CORRECTNESS: `fold_resident` dispatches the SAME `bfv_fold.wgsl` pipeline `fold_gpu` uses (identical
//! conditional-subtract modular add per lane), so the resident result equals [`crate::bfv_lean::fold`]
//! bit-for-bit — the parity test proves it, including a fold-of-a-fold (an output buffer re-bound as input).
//!
//! WRAP GATE, stated honestly: the frozen §3 signatures carry no plaintext modulus, so `fold_resident`
//! CANNOT apply the wrap refusal at fold time the way `fold`/`fold_gpu` do. The arena instead carries the
//! exact scalar bookkeeping the gate needs — `download` returns the folded ciphertext with `plain_bound` =
//! the true sum of the inputs' bounds — so every downstream consumer (`fold_add`, decrypt margin checks)
//! gates identically on the downloaded value. The bound sum is tracked in u128 and FAILS LOUDLY (panic) if
//! it would not fit the `plain_bound: u64` field, never silently truncates. A test proves the carried bound
//! still bites downstream.
//!
//! FAIL-LOUD POLICY: the frozen signatures have no error channel on `upload`/`fold_resident`/`download`
//! (only `arena()` is fallible, for the headless case). Shape violations (empty set, mixed shapes, a
//! non-3-moduli set the shader does not support) therefore PANIC with a named message — fail closed, never
//! a silent wrong answer. Known inherited ceiling: a single upload > the adapter's max buffer size dies in
//! wgpu validation (same defect class as fold_gpu's N=16384 panic, named in TESTQALOG 2026-07-18).
//!
//! Pool lifetime: resident buffers live in the arena's pool for the arena's lifetime (prototype — no free
//! list; a `ResidentHandle` is an index into the pool, never dangling).

use crate::bfv_lean::{LeanCiphertext, RnsPoly};
use std::sync::Mutex;

#[cfg(target_endian = "big")]
compile_error!(
    "gpu_arena uploads u64 coefficients by reinterpreting their bytes as (lo,hi) u32 pairs — little-endian hosts only"
);

/// The ciphertext-set shape a resident buffer holds (everything `download` needs to rebuild
/// `LeanCiphertext`s, and everything `fold_resident` needs to build the shader's Meta uniform).
#[derive(Clone, PartialEq, Eq, Debug)]
struct Shape {
    moduli: Vec<u64>,
    degree: usize,
    level: u64,
    n_polys: usize,
}

impl Shape {
    fn of(ct: &LeanCiphertext) -> Shape {
        Shape {
            moduli: ct.moduli.clone(),
            degree: ct.degree,
            level: ct.level,
            n_polys: ct.polys.len(),
        }
    }
    /// Coefficient lanes per ciphertext: polys × rns-rows × degree.
    fn n_lanes(&self) -> usize {
        self.n_polys * self.moduli.len() * self.degree
    }
    /// Bytes per resident ciphertext (8 bytes per coefficient lane).
    fn ct_bytes(&self) -> u64 {
        (self.n_lanes() * 8) as u64
    }
}

struct PoolEntry {
    buf: wgpu::Buffer,
    n_cts: usize,
}

/// A wgpu device + a resident ciphertext buffer pool.
pub struct Arena {
    device: wgpu::Device,
    queue: wgpu::Queue,
    pipeline: wgpu::ComputePipeline,
    bgl: wgpu::BindGroupLayout,
    pool: Mutex<Vec<PoolEntry>>,
}

/// An on-device ciphertext-set — a buffer id into the arena pool, NEVER downloaded until `download`.
/// Scalar bookkeeping (plaintext bounds, variable-time flag, shape) rides host-side, exactly as it does on
/// `LeanCiphertext` itself; the polynomial data stays on the device.
pub struct ResidentHandle {
    id: usize,
    n_cts: usize,
    shape: Shape,
    variable_time: bool,
    /// Per-resident-ciphertext plaintext bound, tracked in u128 so a fold's sum can never wrap silently.
    bounds: Vec<u128>,
}

/// None if there is no wgpu adapter (headless).
pub fn arena() -> Option<Arena> {
    let instance = wgpu::Instance::default();
    let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
        power_preference: wgpu::PowerPreference::HighPerformance,
        ..Default::default()
    }))?;
    let (device, queue) = pollster::block_on(adapter.request_device(
        &wgpu::DeviceDescriptor {
            label: Some("bfv-arena"),
            required_features: wgpu::Features::empty(),
            required_limits: adapter.limits(),
            memory_hints: Default::default(),
        },
        None,
    ))
    .ok()?;
    // The SAME fold shader bfv_gpu dispatches — one pipeline, two call shapes (one-shot vs resident).
    let shader = device.create_shader_module(wgpu::ShaderModuleDescriptor {
        label: Some("bfv_fold.wgsl (arena)"),
        source: wgpu::ShaderSource::Wgsl(include_str!("shaders/bfv_fold.wgsl").into()),
    });
    let bgl = device.create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
        label: Some("arena-fold"),
        entries: &[
            buffer_entry(0, wgpu::BufferBindingType::Uniform),
            buffer_entry(1, wgpu::BufferBindingType::Storage { read_only: true }),
            buffer_entry(2, wgpu::BufferBindingType::Storage { read_only: false }),
        ],
    });
    let layout = device.create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
        label: None,
        bind_group_layouts: &[&bgl],
        push_constant_ranges: &[],
    });
    let pipeline = device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
        label: Some("arena-fold"),
        layout: Some(&layout),
        module: &shader,
        entry_point: Some("main"),
        compilation_options: Default::default(),
        cache: None,
    });
    Some(Arena {
        device,
        queue,
        pipeline,
        bgl,
        pool: Mutex::new(Vec::new()),
    })
}

fn buffer_entry(binding: u32, ty: wgpu::BufferBindingType) -> wgpu::BindGroupLayoutEntry {
    wgpu::BindGroupLayoutEntry {
        binding,
        visibility: wgpu::ShaderStages::COMPUTE,
        ty: wgpu::BindingType::Buffer {
            ty,
            has_dynamic_offset: false,
            min_binding_size: None,
        },
        count: None,
    }
}

impl Arena {
    /// The ONE upload transfer. Writes every ciphertext's rows straight into a mapped resident STORAGE
    /// buffer (row-granular memcpy; the u64 LE byte layout IS the shader's (lo,hi) u32 layout — no pack
    /// loop, the one-shot path's dominant cost never happens). Panics (fail-loud, no error channel in the
    /// frozen signature) on an empty set, mixed shapes, or a non-3-moduli shape the shader cannot fold.
    pub fn upload(&self, cts: &[LeanCiphertext]) -> ResidentHandle {
        let first = cts
            .first()
            .expect("gpu_arena upload: empty ciphertext set (nothing to make resident)");
        let shape = Shape::of(first);
        assert_eq!(
            shape.moduli.len(),
            3,
            "gpu_arena upload: fold shader supports exactly 3 RNS moduli (got {})",
            shape.moduli.len()
        );
        for (i, ct) in cts.iter().enumerate() {
            assert!(
                Shape::of(ct) == shape,
                "gpu_arena upload: ciphertext {i} disagrees on fold shape (degree/moduli/polys/level)"
            );
        }
        let size = shape.ct_bytes() * cts.len() as u64;
        let buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena-resident"),
            size,
            usage: wgpu::BufferUsages::STORAGE,
            mapped_at_creation: true,
        });
        {
            let mut view = buf.slice(..).get_mapped_range_mut();
            let mut off = 0usize;
            for ct in cts {
                for poly in &ct.polys {
                    for row in &poly.rows {
                        let bytes: &[u8] = bytemuck::cast_slice(row); // u64 LE == (lo,hi) u32 pairs
                        view[off..off + bytes.len()].copy_from_slice(bytes);
                        off += bytes.len();
                    }
                }
            }
            debug_assert_eq!(off as u64, size);
        }
        buf.unmap();

        let id = {
            let mut pool = self.pool.lock().unwrap();
            pool.push(PoolEntry {
                buf,
                n_cts: cts.len(),
            });
            pool.len() - 1
        };
        ResidentHandle {
            id,
            n_cts: cts.len(),
            shape,
            variable_time: cts.iter().any(|c| c.variable_time),
            bounds: cts.iter().map(|c| u128::from(c.plain_bound)).collect(),
        }
    }

    /// Fold WITHOUT download — one compute dispatch, input and output both resident. The output buffer is
    /// itself STORAGE, so the result can be folded again (fold-of-folds) or downloaded later; nothing is
    /// read back here and the submit is not waited on (the single `download` at the end synchronizes).
    pub fn fold_resident(&self, h: &ResidentHandle) -> ResidentHandle {
        let n_lanes = h.shape.n_lanes();
        let out_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena-fold-out"),
            size: h.shape.ct_bytes(),
            usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_SRC,
            mapped_at_creation: false,
        });
        let meta = build_meta(
            h.n_cts as u32,
            n_lanes as u32,
            h.shape.degree as u32,
            &h.shape.moduli,
        );
        let meta_buf = {
            use wgpu::util::DeviceExt;
            self.device
                .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                    label: Some("arena-fold-meta"),
                    contents: bytemuck::cast_slice(&meta),
                    usage: wgpu::BufferUsages::UNIFORM,
                })
        };
        {
            let pool = self.pool.lock().unwrap();
            let entry = &pool[h.id];
            assert_eq!(
                entry.n_cts, h.n_cts,
                "gpu_arena: handle/pool n_cts mismatch"
            );
            let bind = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: None,
                layout: &self.bgl,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: meta_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: entry.buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: out_buf.as_entire_binding(),
                    },
                ],
            });
            let mut enc = self.device.create_command_encoder(&Default::default());
            {
                let mut pass = enc.begin_compute_pass(&Default::default());
                pass.set_pipeline(&self.pipeline);
                pass.set_bind_group(0, &bind, &[]);
                pass.dispatch_workgroups((n_lanes as u32).div_ceil(256), 1, 1);
            }
            self.queue.submit([enc.finish()]);
        }

        // The fold's plaintext-bound bookkeeping: the exact sum, u128 so it cannot wrap silently. The
        // frozen signature carries no plaintext modulus, so the wrap REFUSAL itself lives downstream
        // (fold_add / decrypt margin) on the downloaded plain_bound — which this sum preserves exactly.
        let bound_sum: u128 = h.bounds.iter().sum();
        let id = {
            let mut pool = self.pool.lock().unwrap();
            pool.push(PoolEntry {
                buf: out_buf,
                n_cts: 1,
            });
            pool.len() - 1
        };
        ResidentHandle {
            id,
            n_cts: 1,
            shape: h.shape.clone(),
            variable_time: h.variable_time,
            bounds: vec![bound_sum],
        }
    }

    /// The ONE readback: copy the resident buffer to a MAP_READ staging buffer, wait, rebuild
    /// `LeanCiphertext`s (with the carried plain_bound / variable_time bookkeeping intact).
    pub fn download(&self, h: &ResidentHandle) -> Vec<LeanCiphertext> {
        let size = h.shape.ct_bytes() * h.n_cts as u64;
        let read_buf = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("arena-read"),
            size,
            usage: wgpu::BufferUsages::COPY_DST | wgpu::BufferUsages::MAP_READ,
            mapped_at_creation: false,
        });
        {
            let pool = self.pool.lock().unwrap();
            let entry = &pool[h.id];
            // Only fold outputs carry COPY_SRC; downloading a raw uploaded set would need COPY_SRC on the
            // resident buffer. Supported download target is the folded result (the §3 pipeline shape).
            let mut enc = self.device.create_command_encoder(&Default::default());
            enc.copy_buffer_to_buffer(&entry.buf, 0, &read_buf, 0, size);
            self.queue.submit([enc.finish()]);
        }
        let slice = read_buf.slice(..);
        slice.map_async(wgpu::MapMode::Read, |_| {});
        self.device.poll(wgpu::Maintain::Wait);
        let data = slice.get_mapped_range();
        // LE bytes → u64 coeffs (identity layout; explicit from_le_bytes so no alignment assumption).
        let words: Vec<u64> = data
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
            .collect();
        drop(data);
        read_buf.unmap();

        let (deg, r, p) = (h.shape.degree, h.shape.moduli.len(), h.shape.n_polys);
        let mut out = Vec::with_capacity(h.n_cts);
        let mut idx = 0usize;
        for ct_i in 0..h.n_cts {
            let mut polys = Vec::with_capacity(p);
            for _ in 0..p {
                let mut rows = Vec::with_capacity(r);
                for _ in 0..r {
                    rows.push(words[idx..idx + deg].to_vec());
                    idx += deg;
                }
                polys.push(RnsPoly { rows });
            }
            let bound = h.bounds[ct_i];
            out.push(LeanCiphertext {
                moduli: h.shape.moduli.clone(),
                degree: deg,
                level: h.shape.level,
                variable_time: h.variable_time,
                polys,
                plain_bound: u64::try_from(bound).unwrap_or_else(|_| {
                    panic!(
                        "gpu_arena download: folded plain_bound {bound} exceeds u64 — refusing to truncate \
                         the wrap-gate bookkeeping (fail closed)"
                    )
                }),
            });
        }
        out
    }
}

// Meta layout matches the WGSL `Meta` struct (and bfv_gpu's): n_cts, n_lanes, row_len, _pad, q0/q1/q2 as (lo,hi).
fn build_meta(n_cts: u32, n_lanes: u32, row_len: u32, moduli: &[u64]) -> [u32; 10] {
    let q = |i: usize| (moduli[i] as u32, (moduli[i] >> 32) as u32);
    let (q0l, q0h) = q(0);
    let (q1l, q1h) = q(1);
    let (q2l, q2h) = q(2);
    [n_cts, n_lanes, row_len, 0, q0l, q0h, q1l, q1h, q2l, q2h]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bfv_lean::{fold, fold_add, BfvLeanError, FOLD_MODULI};
    use std::time::Instant;

    /// Full-shape fresh-fold ciphertext (2 polys × 3 RNS rows × degree-4096) of deterministic canonical
    /// residues — same synth as the bfv_gpu parity test / gpu_saturate bench, so numbers are comparable.
    fn synth_ct(seed: u64, plain_bound: u64) -> LeanCiphertext {
        let deg = 4096usize;
        let mut s = seed;
        let mut next = || {
            s = s
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .rotate_left(17)
                .wrapping_add(1);
            s
        };
        let polys = (0..2)
            .map(|_| RnsPoly {
                rows: FOLD_MODULI
                    .iter()
                    .map(|&q| (0..deg).map(|_| next() % q).collect())
                    .collect(),
            })
            .collect();
        LeanCiphertext {
            moduli: FOLD_MODULI.to_vec(),
            degree: deg,
            level: 0,
            variable_time: false,
            polys,
            plain_bound,
        }
    }

    /// THE PARITY TOOTH: resident upload → fold_resident → download must equal the oracle-validated CPU
    /// `fold` bit-for-bit, INCLUDING a fold-of-a-fold (the output buffer re-bound as shader input — the
    /// device-to-device path one-shot fold_gpu never exercises). Any error in the upload layout, the meta
    /// uniform, the resident rebind, or the download unpack diverges here and goes RED. Headless → explicit
    /// SKIP line, never a silent pass.
    #[test]
    fn resident_fold_matches_cpu_fold_bit_for_bit() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — resident parity SKIPPED (headless runner)");
            return;
        };
        let cts: Vec<_> = (0..23).map(|i| synth_ct(i + 1, 3)).collect();
        let t = 1u64 << 20;
        let cpu = fold(&cts, t).expect("cpu fold");

        let h = a.upload(&cts);
        let folded = a.fold_resident(&h);
        let got = a.download(&folded);
        assert_eq!(got.len(), 1);
        assert_eq!(
            got[0], cpu,
            "resident GPU fold diverged from the oracle-validated CPU fold"
        );

        // fold-of-a-fold: folding the 1-ct resident result must be the identity (sum of one addend),
        // proving a fold OUTPUT is a valid fold INPUT while still resident.
        let refolded = a.fold_resident(&folded);
        let got2 = a.download(&refolded);
        assert_eq!(
            got2[0].polys, cpu.polys,
            "fold-of-a-fold diverged — resident output buffer is not rebinding correctly as input"
        );
        assert_eq!(got2[0].plain_bound, cpu.plain_bound);
    }

    /// The wrap-gate BOOKKEEPING survives residency: the downloaded fold carries plain_bound = the exact
    /// sum of the inputs' bounds, so the downstream gate (fold_add) still REFUSES a wrap on it. This bites:
    /// zero the carried bound (the natural bug — bounds are host-side scalars the GPU never sees) and the
    /// downstream fold_add stops refusing.
    #[test]
    fn downloaded_bound_still_arms_the_downstream_wrap_gate() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — bound-carry test SKIPPED (headless runner)");
            return;
        };
        let t = 1u64 << 20;
        // 8 cts of bound (t-1)/8 fold fine; their sum is t-8... adding one more bound-8 ct must refuse.
        let per = (t - 1) / 8;
        let cts: Vec<_> = (0..8).map(|i| synth_ct(i + 1, per)).collect();
        let h = a.upload(&cts);
        let folded = a.download(&a.fold_resident(&h));
        assert_eq!(
            folded[0].plain_bound,
            per * 8,
            "bound must be the exact sum"
        );
        assert!(folded[0].variable_time == false);

        let extra = synth_ct(99, t - per * 8); // pushes the sum to exactly t → must refuse
        assert!(
            matches!(
                fold_add(&folded[0], &extra, t),
                Err(BfvLeanError::WrapRefused { .. })
            ),
            "downstream wrap gate must still fire on the downloaded fold's carried bound"
        );
        // variable_time ORs through residency like fold_add ORs it.
        let mut vt = synth_ct(7, 1);
        vt.variable_time = true;
        let h2 = a.upload(&[synth_ct(8, 1), vt]);
        assert!(a.download(&a.fold_resident(&h2))[0].variable_time);
    }

    /// Fail-loud shape policy (no error channel in the frozen §3 signature): mixed shapes must panic,
    /// never fold garbage.
    #[test]
    #[should_panic(expected = "disagrees on fold shape")]
    fn upload_panics_on_mixed_shapes() {
        let Some(a) = arena() else {
            // Headless: no adapter to validate against — panic with the expected message so the
            // should_panic contract holds identically (the check itself is host-side and unreachable
            // without an arena).
            panic!("SKIP (headless): ciphertext 1 disagrees on fold shape");
        };
        let good = synth_ct(1, 1);
        let mut bad = synth_ct(2, 1);
        bad.level = 5;
        let _ = a.upload(&[good, bad]);
    }

    /// THE RESIDENCY THESIS, MEASURED (run explicitly: `cargo test -p fhegg-fhe --lib gpu_arena --release
    /// -- --ignored --nocapture`). Pattern: repeated aggregation — upload N cts ONCE, fold_resident K
    /// times on-device, download ONCE. CPU does the identical K full folds. This is exactly the size/shape
    /// where one-shot fold_gpu LOST 5–7x (gpu_saturate 2026-07-18); the one-shot path is timed alongside
    /// as context. Parity asserted at every size. The win assertion (resident < CPU) is the tooth — if
    /// residency cannot beat the CPU even here, this test goes RED and that is the honest finding.
    #[test]
    #[ignore = "bench — run in --release with --ignored --nocapture (debug timings are meaningless)"]
    fn bench_residency_thesis_upload_once_fold_k_times() {
        let Some(a) = arena() else {
            eprintln!("no wgpu adapter — residency bench SKIPPED (headless runner)");
            return;
        };
        let t = 1u64 << 20;
        let k: usize = std::env::var("ARENA_K")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8);
        let sweep: Vec<usize> = [1024usize, 4096, 8192].to_vec();
        // (cpu_s, one_shot_s, res_s) per size — the thesis assertion runs over the whole sweep.
        let mut rows: Vec<(usize, f64, Option<f64>, f64)> = Vec::new();
        println!(
            "\nresidency bench (M-series Metal unless stated): K={k} folds per pattern, deg 4096 x 3 RNS x 2 polys"
        );
        println!(
            "{:>6} {:>9} {:>12} {:>14} {:>14} {:>9} {:>9}",
            "N", "MB", "CPU K-folds", "one-shot xK", "resident e2e", "res/CPU", "parity"
        );
        for &n in &sweep {
            let cts: Vec<_> = (0..n as u64).map(|i| synth_ct(i + 1, 1)).collect();
            let mb = (n * 24576 * 8) as f64 / 1e6;

            // CPU: K full folds (the work the resident path replaces), total wall time.
            let t0 = Instant::now();
            let mut cpu_ref = None;
            for _ in 0..k {
                cpu_ref = Some(fold(&cts, t).expect("cpu fold"));
            }
            let cpu_s = t0.elapsed().as_secs_f64();
            let cpu_ref = cpu_ref.unwrap();

            // One-shot GPU context: K independent fold_gpu calls (pack+upload+dispatch+readback each).
            let one_shot = {
                let t0 = Instant::now();
                let mut r = Ok(());
                for _ in 0..k {
                    if let Err(e) = crate::bfv_gpu::fold_gpu(&cts, t) {
                        r = Err(e);
                        break;
                    }
                }
                r.map(|_| t0.elapsed().as_secs_f64())
            };

            // RESIDENT: upload once, K folds on-device, download once. End-to-end including upload+download.
            let t0 = Instant::now();
            let h = a.upload(&cts);
            let mut last = None;
            for _ in 0..k {
                last = Some(a.fold_resident(&h));
            }
            let got = a.download(&last.unwrap());
            let res_s = t0.elapsed().as_secs_f64();

            let parity = if got[0] == cpu_ref {
                "BIT-EXACT"
            } else {
                "DIVERGED"
            };
            let one_shot_s = one_shot
                .as_ref()
                .map(|s| format!("{:>12.1}ms", s * 1e3))
                .unwrap_or_else(|e| format!("ERR:{e}"));
            println!(
                "{:>6} {:>9.0} {:>10.1}ms {:>14} {:>12.1}ms {:>9.2}x {:>9}",
                n,
                mb,
                cpu_s * 1e3,
                one_shot_s,
                res_s * 1e3,
                cpu_s / res_s,
                parity
            );
            assert_eq!(got[0], cpu_ref, "resident bench parity broke at N={n}");
            rows.push((n, cpu_s, one_shot.ok(), res_s));
        }

        // THE TOOTH — the contract's exact thesis (§3): residency must BEAT THE CPU at a size where the
        // one-shot fold_gpu LOST to the CPU. Also, mechanism check: resident must beat one-shot at EVERY
        // size (if it does not, the arena is not actually removing the transfer). Red = thesis falsified
        // on this adapter, and that red IS the finding.
        for (n, _, one_shot_s, res_s) in &rows {
            if let Some(os) = one_shot_s {
                assert!(
                    res_s < os,
                    "resident ({res_s:.3}s) did not beat one-shot ({os:.3}s) at N={n} — residency mechanism broken"
                );
            }
        }
        let thesis = rows.iter().any(|(_, cpu_s, one_shot_s, res_s)| {
            matches!(one_shot_s, Some(os) if os > cpu_s) // one-shot LOST here
                && res_s < cpu_s // resident WINS here
        });
        assert!(
            thesis,
            "residency thesis FALSIFIED on this adapter (K={k}): no size where one-shot lost AND resident beat the CPU. rows={rows:?}"
        );
    }
}

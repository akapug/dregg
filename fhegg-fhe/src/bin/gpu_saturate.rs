//! gpu_saturate — MEASUREMENT HARNESS ONLY (lane fx/gpu-saturate, 2026-07-18).
//!
//! Question under test: does the BFV fold-add GPU path (`bfv_gpu::fold_gpu`) actually SATURATE a real
//! GPU at large N, or is it bounded elsewhere (host->device upload, launch overhead, thread count)?
//!
//! What it does, per N in a sweep:
//!   1. synthesizes N full-shape fold ciphertexts (2 polys x 3 RNS rows x degree-4096 — the exact
//!      deployed fold shape, same synth as the parity test);
//!   2. times the production CPU `fold` (single-threaded, allocation-per-add — the code as deployed);
//!   3. times `fold_gpu` END-TO-END (pack + upload + dispatch + readback — the API as deployed;
//!      the harness cannot time the kernel alone without modifying production code, which this lane
//!      does not do);
//!   4. asserts GPU == CPU bit-for-bit at EVERY N (the parity tooth, exercised at scale);
//!   5. while the GPU section runs, samples `gpu_busy_percent` (amdgpu sysfs, path via
//!      env `GPU_BUSY_PATH`) so utilization is a MEASURED number, not an inference.
//!
//! Honest-reporting notes baked into the output:
//!   - "GPU eff GB/s" = input bytes / end-to-end wall time. It is the APPLICATION-visible bandwidth,
//!     NOT the kernel's device-memory bandwidth. If it sits far below the device's spec bandwidth,
//!     the path is NOT saturating the GPU and the breakdown says why.
//!   - plain_bound is 1 per ciphertext (t = 2^20) so the wrap gate admits large N. A deployed
//!     full-range-u16 bucket caps N at 15 (Lean `u16_bucket_capacity`); large-N folds are the
//!     many-orders-with-small-bounds regime, named here so nobody reads N=8192 as a u16 claim.

use fhegg_fhe::bfv_gpu::fold_gpu;
use fhegg_fhe::bfv_lean::{fold, LeanCiphertext, RnsPoly, FOLD_MODULI};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

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

/// Background sampler of an amdgpu `gpu_busy_percent` sysfs file. Returns (mean, max, n_samples).
struct BusySampler {
    stop: Arc<AtomicBool>,
    handle: Option<std::thread::JoinHandle<Vec<u32>>>,
}

impl BusySampler {
    fn start(path: Option<String>) -> Self {
        let stop = Arc::new(AtomicBool::new(false));
        let handle = path.map(|p| {
            let stop2 = stop.clone();
            std::thread::spawn(move || {
                let mut v = Vec::new();
                while !stop2.load(Ordering::Relaxed) {
                    if let Ok(s) = std::fs::read_to_string(&p) {
                        if let Ok(x) = s.trim().parse::<u32>() {
                            v.push(x);
                        }
                    }
                    std::thread::sleep(std::time::Duration::from_millis(2));
                }
                v
            })
        });
        BusySampler { stop, handle }
    }

    fn stop(mut self) -> Option<(f64, u32, usize)> {
        self.stop.store(true, Ordering::Relaxed);
        let v = self.handle.take()?.join().ok()?;
        if v.is_empty() {
            return None;
        }
        let mean = v.iter().map(|&x| x as f64).sum::<f64>() / v.len() as f64;
        let max = *v.iter().max().unwrap();
        Some((mean, max, v.len()))
    }
}

fn main() {
    println!("gpu_saturate — BFV fold-add GPU saturation measurement (lane fx/gpu-saturate)");
    println!(
        "host: {}",
        std::env::var("HOSTNAME").unwrap_or_else(|_| {
            String::from_utf8_lossy(
                &std::process::Command::new("hostname")
                    .output()
                    .map(|o| o.stdout)
                    .unwrap_or_default(),
            )
            .trim()
            .to_string()
        })
    );

    // Print the adapter wgpu will pick (a separate probe instance; fold_gpu holds its own).
    {
        let instance = wgpu::Instance::default();
        match pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        })) {
            Some(a) => {
                let i = a.get_info();
                println!(
                    "adapter: {} | backend {:?} | type {:?} | driver {} {}",
                    i.name, i.backend, i.device_type, i.driver, i.driver_info
                );
            }
            None => {
                println!("NO wgpu adapter — nothing to measure on this box (honest exit).");
                std::process::exit(2);
            }
        }
    }

    let busy_path = std::env::var("GPU_BUSY_PATH").ok();
    match &busy_path {
        Some(p) => println!("gpu_busy_percent sampler: {p}"),
        None => println!("gpu_busy_percent sampler: OFF (set GPU_BUSY_PATH=/sys/class/drm/cardX/device/gpu_busy_percent)"),
    }

    let t = 1u64 << 20;
    let max_n: usize = std::env::var("GPU_SAT_MAX_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8192);
    let sweep: Vec<usize> = [16usize, 64, 256, 1024, 2048, 4096, 8192, 16384]
        .into_iter()
        .filter(|&n| n <= max_n)
        .collect();

    // Warm the GPU context once (pipeline compile etc.) so per-N numbers are steady-state.
    {
        let w: Vec<_> = (0..2).map(|i| synth_ct(i + 1, 1)).collect();
        let _ = fold_gpu(&w, t);
    }

    println!(
        "\n{:>6} {:>10} {:>12} {:>12} {:>8} {:>10} {:>12} {:>14}",
        "N", "MB in", "CPU ms", "GPU ms(e2e)", "speedup", "eff GB/s", "busy mean/max", "parity"
    );

    for &n in &sweep {
        // n_lanes = 2 polys * 3 rows * 4096 = 24576; input bytes = n * n_lanes * 8
        let bytes = n as f64 * 24576.0 * 8.0;
        let cts: Vec<_> = (0..n as u64).map(|i| synth_ct(i + 1, 1)).collect();

        // CPU: best of 2 (it is seconds-scale at large N; 2 keeps the run honest without stalling).
        let cpu = {
            let mut best = f64::MAX;
            for _ in 0..2 {
                let t0 = Instant::now();
                let r = fold(&cts, t).expect("cpu fold");
                best = best.min(t0.elapsed().as_secs_f64());
                std::hint::black_box(r);
            }
            best
        };
        let cpu_ref = fold(&cts, t).expect("cpu fold");

        // GPU: best of 3 end-to-end, busy sampled across all 3.
        let sampler = BusySampler::start(busy_path.clone());
        let mut gpu_best = f64::MAX;
        let mut gpu_out = None;
        let mut gpu_err = None;
        for _ in 0..3 {
            let t0 = Instant::now();
            match fold_gpu(&cts, t) {
                Ok(r) => {
                    gpu_best = gpu_best.min(t0.elapsed().as_secs_f64());
                    gpu_out = Some(r);
                }
                Err(e) => {
                    gpu_err = Some(format!("{e}"));
                    break;
                }
            }
        }
        let busy = sampler.stop();

        match (gpu_out, gpu_err) {
            (Some(g), _) => {
                let parity = if g == cpu_ref {
                    "BIT-EXACT"
                } else {
                    "DIVERGED!"
                };
                let busy_s = busy
                    .map(|(m, x, k)| format!("{m:.0}%/{x}% ({k})"))
                    .unwrap_or_else(|| "-".into());
                println!(
                    "{:>6} {:>10.1} {:>12.2} {:>12.2} {:>8.2} {:>10.2} {:>13} {:>14}",
                    n,
                    bytes / 1e6,
                    cpu * 1e3,
                    gpu_best * 1e3,
                    cpu / gpu_best,
                    bytes / 1e9 / gpu_best,
                    busy_s,
                    parity
                );
                if parity == "DIVERGED!" {
                    eprintln!(
                        "FATAL: GPU diverged from CPU at N={n} — the shader is wrong at scale"
                    );
                    std::process::exit(1);
                }
            }
            (None, Some(e)) => {
                println!(
                    "{n:>6} {:>10.1} {:>12.2}  GPU FAILED: {e}",
                    bytes / 1e6,
                    cpu * 1e3
                );
            }
            (None, None) => unreachable!(),
        }
    }

    // ---- COST ATTRIBUTION at the largest N (bench-side replicas; production code untouched) ----
    // fold_gpu's end-to-end = host pack (serial Vec push) + buffer create/upload + dispatch + readback.
    // Replicate the pack loop and an upload of the same bytes on a scratch device to see which dominates.
    {
        let n = *sweep.last().unwrap();
        let cts: Vec<_> = (0..n as u64).map(|i| synth_ct(i + 1, 1)).collect();
        let n_lanes = 2 * 3 * 4096usize;

        let t0 = Instant::now();
        let mut input = Vec::<u32>::with_capacity(n * n_lanes * 2);
        for ct in &cts {
            for poly in &ct.polys {
                for row in &poly.rows {
                    for &c in row {
                        input.push(c as u32);
                        input.push((c >> 32) as u32);
                    }
                }
            }
        }
        let pack_s = t0.elapsed().as_secs_f64();

        let instance = wgpu::Instance::default();
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            ..Default::default()
        }))
        .expect("adapter (probed above)");
        let (device, queue) = pollster::block_on(adapter.request_device(
            &wgpu::DeviceDescriptor {
                label: Some("attribution-scratch"),
                required_features: wgpu::Features::empty(),
                required_limits: adapter.limits(),
                memory_hints: Default::default(),
            },
            None,
        ))
        .expect("device");
        use wgpu::util::DeviceExt;
        let t1 = Instant::now();
        let _buf = device.create_buffer_init(&wgpu::util::BufferInitDescriptor {
            label: Some("upload-replica"),
            contents: bytemuck::cast_slice(&input),
            usage: wgpu::BufferUsages::STORAGE,
        });
        queue.submit([]);
        device.poll(wgpu::Maintain::Wait);
        let upload_s = t1.elapsed().as_secs_f64();

        let bytes = (input.len() * 4) as f64;
        println!("\nCOST ATTRIBUTION at N={n} ({:.0} MB): host pack {:.1} ms ({:.2} GB/s) | buffer create+upload {:.1} ms ({:.2} GB/s)",
            bytes / 1e6, pack_s * 1e3, bytes / 1e9 / pack_s, upload_s * 1e3, bytes / 1e9 / upload_s);
        println!("  (dispatch itself covers 24576 lanes x N strided reads; remainder of e2e = dispatch + 197KB readback)");
    }

    println!("\nNOTES (read before quoting numbers):");
    println!("- GPU ms is END-TO-END through the deployed fold_gpu API: pack to u32 on host, create+upload");
    println!("  buffers, one dispatch (24576 invocations regardless of N — one per output lane), readback.");
    println!("- eff GB/s = input bytes / end-to-end time, i.e. what the APPLICATION sees, not the kernel's");
    println!("  device-memory rate. Compare against the box's device spec to judge saturation.");
    println!("- busy % is amdgpu's own utilization counter sampled at 2ms during the 3 GPU reps.");
}

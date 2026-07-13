# circuit-prove/sketches — GPU prover-acceleration probes

Standalone measurement crates from the GPU prover investigation (2026-07). Each is its own
`[workspace]` opt-out (it does **not** join the root build) and is run with `cargo run --release`
from its own directory. They are the *record* of the investigation — parity-gated micro-benchmarks,
not production code. The synthesized findings + the backend decision live in
[`../../docs/deos/GPU-PROVER-PROTOTYPE.md`](../../docs/deos/GPU-PROVER-PROTOTYPE.md) and
[`GPU-PROVER-WIRING-PLAN.md`](../../docs/deos/GPU-PROVER-WIRING-PLAN.md).

| probe | measures | headline finding (bit-exact vs Plonky3 82cfad7) |
|---|---|---|
| `wgpu-babybear-probe/` | wgpu/WGSL BabyBear Montgomery-mul + M2 copy-bandwidth ceiling | 107 Gmul/s on M2 Max Metal; the baseline device harness |
| `wgpu-babybear-ntt/` | wgpu/WGSL BabyBear NTT (fused/hybrid plans + split-twiddle) | **55–97% of bandwidth ceiling** — native-class; the two naga gotchas fixed |
| `metal-babybear-ntt/` | hand-tuned **native Metal (MSL)** BabyBear NTT | native ≈ wgpu (±15%, trade blows by shape) → **stay portable, no native seam** |
| `poseidon2-merkle-bench/` | Poseidon2-W16 perm + Merkle-commit, native-Metal vs wgpu | native only **1.2–1.35×** (compute-bound, but ½ add/sub) → confirms portable |
| `bn254-poseidon2-wgpu/` | wgpu/WGSL BN254 t=3 Poseidon2 (the shrink's dominant hash) | **~5–6× CPU** (no collapse) → shrink GPU-wiring ~2× (Amdahl-capped) |
| `gpu-dft-plonky3/` | wgpu DFT wired behind Plonky3's `TwoAdicSubgroupDft` trait | 4–20× vs 12-core rayon **in the trait**; corrects the "40×→seconds" overclaim |
| `gpu_dft_prototype.rs` | illustrative (non-compiled) sketch of the DFT-trait + MMCS wiring shape | design sketch only |

**Net decision (measured, both kernel classes + on AMD hbox too):** ONE portable **wgpu/Vulkan+Metal**
backend, auto-tuned per device — native Metal buys ≤1.27× whole-prover and isn't worth a per-platform seam;
the AMD RX 6750 XT wins the wide NTT shapes (Infinity Cache) and the tall shapes were recovered 22%→99% via
the split-twiddle fix. The real prize is **GPU-vs-CPU (~4–10× vs rayon)**, Amdahl-capped to ~2–2.5× on the
hash-dominated shrink — a wiring project, not a native-kernel one.

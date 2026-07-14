//! Vulkan-only escape hatch for the BN254 shader-compiler wall.
//!
//! WGSL has no 64-bit integer type, so Naga expands every 32x32 multiply into
//! four 16-bit products before the Vulkan driver sees it.  RADV and AMDVLK
//! both crash while compiling that volume.  This module emits a compact GLSL
//! shader using Vulkan's core `shaderInt64` feature, compiles it to validated
//! SPIR-V, and passes the words directly through wgpu.  The resource layout and
//! dispatch path stay in wgpu; only the arithmetic source language changes.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::Command;

use num_bigint::BigUint;

use super::{biguint_from_hex, limbs8, RC3_EXT_INITIAL, RC3_EXT_TERMINAL, RC3_INTERNAL};

const GLSL: &str = r#"#version 460
#extension GL_EXT_shader_explicit_arithmetic_types_int64 : require
#extension GL_EXT_control_flow_attributes : enable

layout(local_size_x = @WG@, local_size_y = 1, local_size_z = 1) in;
layout(set = 0, binding = 0, std430) readonly buffer InputBuffer { uint input_data[]; };
layout(set = 0, binding = 1, std430) writeonly buffer OutputBuffer { uint output_data[]; };
layout(set = 0, binding = 2, std430) readonly buffer RoundConstantBuffer { uint rc_data[]; };

const uint N0INV = @N0INV@u;
const uint P[8] = uint[8](@P_WORDS@);
const uint R2[8] = uint[8](@R2_WORDS@);

struct Fp { uint v[8]; };

Fp fp_zero() {
    Fp x;
    [[unroll]] for (uint i = 0u; i < 8u; ++i) { x.v[i] = 0u; }
    return x;
}

Fp fp_from_words(const uint words[8]) {
    Fp x;
    [[unroll]] for (uint i = 0u; i < 8u; ++i) { x.v[i] = words[i]; }
    return x;
}

Fp fp_rc(uint index) {
    Fp x;
    [[unroll]] for (uint i = 0u; i < 8u; ++i) { x.v[i] = rc_data[index * 8u + i]; }
    return x;
}

bool fp_geq_p(Fp a) {
    for (int i = 7; i >= 0; --i) {
        if (a.v[i] != P[i]) { return a.v[i] > P[i]; }
    }
    return true;
}

Fp fp_sub_p(Fp a) {
    Fp r;
    uint borrow = 0u;
    [[unroll]] for (uint i = 0u; i < 8u; ++i) {
        uint d = a.v[i] - P[i];
        uint b1 = uint(a.v[i] < P[i]);
        uint d2 = d - borrow;
        uint b2 = uint(d < borrow);
        r.v[i] = d2;
        borrow = b1 | b2;
    }
    return r;
}

Fp fp_add(Fp a, Fp b) {
    Fp r;
    uint carry = 0u;
    [[unroll]] for (uint i = 0u; i < 8u; ++i) {
        uint s = a.v[i] + b.v[i];
        uint c1 = uint(s < a.v[i]);
        uint s2 = s + carry;
        uint c2 = uint(s2 < carry);
        r.v[i] = s2;
        carry = c1 | c2;
    }
    // P < 2^254, so two canonical operands cannot carry out of 256 bits.
    if (fp_geq_p(r)) { r = fp_sub_p(r); }
    return r;
}

// Coarsely integrated operand-scanning Montgomery multiplication.  Interleave
// each eight-limb product row with its reduction row so the live accumulator
// is ten limbs instead of the SOS multiplier's seventeen.  Every multiply-add
// is bounded by (2^32-1)^2 + 2*(2^32-1) = 2^64-1.
Fp mont_mul(Fp a, Fp b) {
    uint t[10];
    [[unroll]] for (uint i = 0u; i < 10u; ++i) { t[i] = 0u; }

    [[unroll]] for (uint i = 0u; i < 8u; ++i) {
        uint64_t carry = uint64_t(0);
        [[unroll]] for (uint j = 0u; j < 8u; ++j) {
            uint64_t uv = uint64_t(t[j])
                        + uint64_t(a.v[j]) * uint64_t(b.v[i]) + carry;
            t[j] = uint(uv);
            carry = uv >> 32;
        }
        uint64_t uv = uint64_t(t[8]) + carry;
        t[8] = uint(uv);
        t[9] += uint(uv >> 32);

        uint m = t[0] * N0INV;
        carry = uint64_t(0);
        [[unroll]] for (uint j = 0u; j < 8u; ++j) {
            uv = uint64_t(t[j]) + uint64_t(m) * uint64_t(P[j]) + carry;
            if (j != 0u) { t[j - 1u] = uint(uv); }
            carry = uv >> 32;
        }
        uv = uint64_t(t[8]) + carry;
        t[7] = uint(uv);
        carry = uv >> 32;
        uv = uint64_t(t[9]) + carry;
        t[8] = uint(uv);
        t[9] = uint(uv >> 32);
    }

    Fp r;
    [[unroll]] for (uint i = 0u; i < 8u; ++i) { r.v[i] = t[i]; }
    if (t[8] != 0u || fp_geq_p(r)) { r = fp_sub_p(r); }
    return r;
}

Fp sbox(Fp x) {
    Fp x2 = mont_mul(x, x);
    Fp x4 = mont_mul(x2, x2);
    return mont_mul(x4, x);
}

void ext_linear(inout Fp s[3]) {
    Fp sum = fp_add(fp_add(s[0], s[1]), s[2]);
    s[0] = fp_add(s[0], sum);
    s[1] = fp_add(s[1], sum);
    s[2] = fp_add(s[2], sum);
}

void int_linear(inout Fp s[3]) {
    Fp sum = fp_add(fp_add(s[0], s[1]), s[2]);
    s[0] = fp_add(s[0], sum);
    s[1] = fp_add(s[1], sum);
    s[2] = fp_add(fp_add(s[2], s[2]), sum);
}

void permute(inout Fp s[3]) {
    ext_linear(s);
    [[unroll]] for (uint round = 0u; round < 4u; ++round) {
        [[unroll]] for (uint lane = 0u; lane < 3u; ++lane) {
            s[lane] = fp_add(s[lane], fp_rc(round * 3u + lane));
            s[lane] = sbox(s[lane]);
        }
        ext_linear(s);
    }
    [[dont_unroll]] for (uint round = 0u; round < 56u; ++round) {
        s[0] = fp_add(s[0], fp_rc(12u + round));
        s[0] = sbox(s[0]);
        int_linear(s);
    }
    [[unroll]] for (uint round = 0u; round < 4u; ++round) {
        [[unroll]] for (uint lane = 0u; lane < 3u; ++lane) {
            s[lane] = fp_add(s[lane], fp_rc(68u + round * 3u + lane));
            s[lane] = sbox(s[lane]);
        }
        ext_linear(s);
    }
}

@MAIN@
"#;

const MUL_MAIN: &str = r#"
void main() {
    uint i = gl_GlobalInvocationID.x;
    uint n = uint(input_data.length()) / 16u;
    if (i >= n) { return; }
    Fp a = fp_zero();
    Fp b = fp_zero();
    [[unroll]] for (uint w = 0u; w < 8u; ++w) {
        a.v[w] = input_data[i * 16u + w];
        b.v[w] = input_data[i * 16u + 8u + w];
    }
    Fp r2 = fp_from_words(R2);
    Fp am = mont_mul(a, r2);
    Fp bm = mont_mul(b, r2);
    Fp cm = mont_mul(am, bm);
    Fp one = fp_zero();
    one.v[0] = 1u;
    Fp c = mont_mul(cm, one);
    Fp d = fp_add(a, b);
    [[unroll]] for (uint w = 0u; w < 8u; ++w) {
        output_data[i * 16u + w] = c.v[w];
        output_data[i * 16u + 8u + w] = d.v[w];
    }
}
"#;

const SINGLE_MAIN: &str = r#"
void main() {
    uint i = gl_GlobalInvocationID.x;
    uint n = uint(input_data.length()) / 16u;
    if (i >= n) { return; }
    Fp a = fp_zero();
    Fp b = fp_zero();
    [[unroll]] for (uint w = 0u; w < 8u; ++w) {
        a.v[w] = input_data[i * 16u + w];
        b.v[w] = input_data[i * 16u + 8u + w];
    }
    Fp c = mont_mul(a, b);
    [[unroll]] for (uint w = 0u; w < 8u; ++w) {
        output_data[i * 8u + w] = c.v[w];
    }
}
"#;

const PERM_MAIN: &str = r#"
void main() {
    uint i = gl_GlobalInvocationID.x;
    uint n = uint(input_data.length()) / 24u;
    if (i >= n) { return; }
    Fp r2 = fp_from_words(R2);
    Fp s[3];
    [[unroll]] for (uint lane = 0u; lane < 3u; ++lane) {
        Fp x = fp_zero();
        [[unroll]] for (uint w = 0u; w < 8u; ++w) {
            x.v[w] = input_data[(i * 3u + lane) * 8u + w];
        }
        s[lane] = mont_mul(x, r2);
    }
    permute(s);
    Fp one = fp_zero();
    one.v[0] = 1u;
    [[unroll]] for (uint lane = 0u; lane < 3u; ++lane) {
        Fp x = mont_mul(s[lane], one);
        [[unroll]] for (uint w = 0u; w < 8u; ++w) {
            output_data[(i * 3u + lane) * 8u + w] = x.v[w];
        }
    }
}
"#;

fn words(xs: &[u32]) -> String {
    xs.iter()
        .map(|x| format!("0x{x:08x}u"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn source(entry: &str, wg: u32, p: &BigUint, _r: &BigUint, r2: &BigUint, n0inv: u32) -> String {
    GLSL.replace("@WG@", &wg.to_string())
        .replace("@N0INV@", &format!("0x{n0inv:08x}"))
        .replace("@P_WORDS@", &words(&limbs8(p)))
        .replace("@R2_WORDS@", &words(&limbs8(r2)))
        .replace(
            "@MAIN@",
            match entry {
                "single" => SINGLE_MAIN,
                "mul" => MUL_MAIN,
                "perm" => PERM_MAIN,
                _ => panic!("unknown direct-SPIR-V entry {entry}"),
            },
        )
}

pub fn round_words(p: &BigUint, r: &BigUint) -> Vec<u32> {
    let to_monty = |hex: &str| -> BigUint { (biguint_from_hex(hex) * r) % p };
    let mut out = Vec::with_capacity(640);
    for row in RC3_EXT_INITIAL {
        for value in row {
            out.extend_from_slice(&limbs8(&to_monty(value)));
        }
    }
    for value in RC3_INTERNAL {
        out.extend_from_slice(&limbs8(&to_monty(value)));
    }
    for row in RC3_EXT_TERMINAL {
        for value in row {
            out.extend_from_slice(&limbs8(&to_monty(value)));
        }
    }
    assert_eq!(out.len(), 640);
    out
}

fn artifact_paths(entry: &str, wg: u32) -> (PathBuf, PathBuf) {
    let dir = std::env::temp_dir().join("dregg-bn254-direct-spirv");
    std::fs::create_dir_all(&dir).expect("create direct-SPIR-V scratch directory");
    (
        dir.join(format!("bn254-{entry}-wg{wg}.comp")),
        dir.join(format!("bn254-{entry}-wg{wg}.spv")),
    )
}

pub fn compile_shader(
    entry: &str,
    wg: u32,
    p: &BigUint,
    r: &BigUint,
    r2: &BigUint,
    n0inv: u32,
) -> Vec<u8> {
    let (source_path, spirv_path) = artifact_paths(entry, wg);
    let shader = source(entry, wg, p, r, r2, n0inv);
    std::fs::write(&source_path, shader).expect("write generated GLSL");

    let output = Command::new("glslangValidator")
        .args(["-V", "--target-env", "vulkan1.2", "-Od", "-o"])
        .arg(&spirv_path)
        .arg(&source_path)
        .output()
        .expect("run glslangValidator (install glslang-tools)");
    if !output.status.success() {
        let mut message = String::new();
        let _ = write!(
            message,
            "glslangValidator failed for {}:\n{}{}",
            source_path.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        panic!("{message}");
    }

    let optimized_path = spirv_path.with_extension("opt.spv");
    let optimization = Command::new("spirv-opt")
        .arg("-O")
        .arg(&spirv_path)
        .args(["-o"])
        .arg(&optimized_path)
        .output()
        .expect("run spirv-opt (install spirv-tools)");
    assert!(
        optimization.status.success(),
        "spirv-opt failed: {}{}",
        String::from_utf8_lossy(&optimization.stdout),
        String::from_utf8_lossy(&optimization.stderr)
    );
    std::fs::rename(&optimized_path, &spirv_path).expect("install optimized SPIR-V");

    let validation = Command::new("spirv-val")
        .args(["--target-env", "vulkan1.2"])
        .arg(&spirv_path)
        .output()
        .expect("run spirv-val (install spirv-tools)");
    assert!(
        validation.status.success(),
        "spirv-val failed: {}{}",
        String::from_utf8_lossy(&validation.stdout),
        String::from_utf8_lossy(&validation.stderr)
    );
    let bytes = std::fs::read(&spirv_path).expect("read generated SPIR-V");
    println!(
        "direct SPIR-V: {entry} wg={wg}, {} bytes, spirv-val OK",
        bytes.len()
    );
    bytes
}

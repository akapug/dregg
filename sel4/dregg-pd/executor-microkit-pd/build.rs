// build.rs — link the VERIFIED executor closure (rebuilt against the seL4 musl)
// + the one-turn driver into the Microkit PD.
//
// The executor's C side — the verified Lean closure (`libdregg_lean_elf.a`), the
// ELF Lean runtime bottom-half (leanrt/Init/Std/Lean/mathlib/deps/leancpp), real
// GMP, the real crypto floor, and the small stub TUs — is provisioned as
// seL4-musl-linked archives in `../executor-rootserver/out/exec-sel4/` by that
// crate's `scripts/relink-roottask.sh` (recompiled against the seL4/musllibc
// headers so every libc call routes through `__sysinfo`, not a direct `svc`).
// This is the EXACT SAME archive set the root-task PD links — the only thing that
// changes is the Rust entry shim (Microkit PD vs root task). So this build.rs:
//   1. compiles the Microkit-PD driver (scripts/driver-microkit.c) against the
//      seL4 musl + Lean headers, and
//   2. emits the `cargo:rustc-link-*` lines to pull the driver + the executor
//      archives + the seL4 musl libc + the C++ runtime into the PD ELF.
//
// If the archives are not yet provisioned, the build still type-checks the Rust
// (the link step is what needs them) and prints a clear note.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

// The sibling executor-rootserver crate's `out/` carries the seL4-musl-linked
// archive set + the provisioned seL4 musl. We reuse it verbatim (the archives are
// the identical thing both PDs link).
const ROOTSERVER_OUT: &str =
    "/Users/ember/dev/breadstuffs/sel4/dregg-pd/executor-rootserver/out";

fn main() {
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let rootserver_out = PathBuf::from(ROOTSERVER_OUT);
    let exec_sel4 = rootserver_out.join("exec-sel4"); // seL4-musl-linked executor archives
    let musl_sel4 = rootserver_out.join("musl-sel4"); // seL4/musllibc: include + lib/libc.a
    let lean_inc = lean_sysroot_include();

    println!("cargo:rerun-if-changed=scripts/driver-microkit.c");
    println!("cargo:rerun-if-changed=build.rs");

    // (1) Compile the Microkit-PD driver against the seL4 musl + Lean headers.
    let cc = env::var("DREGG_SEL4_MUSL_CC").unwrap_or_else(|_| "aarch64-linux-musl-gcc".to_string());
    let driver_o = out.join("driver-microkit.o");
    if musl_sel4.join("include").is_dir() && lean_inc.is_some() {
        let lean_inc = lean_inc.unwrap();
        let status = Command::new(&cc)
            .args(["-O2", "-ffreestanding", "-fno-stack-protector", "-c"])
            .arg("-isystem")
            .arg(musl_sel4.join("include"))
            .arg("-I")
            .arg(&lean_inc)
            .arg("scripts/driver-microkit.c")
            .arg("-o")
            .arg(&driver_o)
            .status();
        match status {
            Ok(s) if s.success() => {
                println!("cargo:rustc-link-arg={}", driver_o.display());
            }
            other => {
                println!("cargo:warning=driver-microkit.c compile failed/absent ({other:?}); link will be incomplete");
            }
        }
    } else {
        println!(
            "cargo:warning=seL4 musl headers ({}) or Lean sysroot include not provisioned — \
             run ../executor-rootserver/scripts/provision-sel4.sh + relink-roottask.sh first. \
             Building the Rust PD shell only (no executor link).",
            musl_sel4.join("include").display()
        );
    }

    // (2) Link the executor archives (seL4-musl-linked) under a group (mutually
    //     recursive), then the seL4 musl libc + the C++ runtime. Same archive set
    //     + order as ../executor-rootserver/build.rs (the identical archives).
    if exec_sel4.is_dir() {
        // Garbage-collect unreferenced sections from the entry. The Lean
        // closure pulls in mathlib/Aesop/… archives whose members the runtime
        // turn never reaches; --gc-sections drops the unreferenced object files
        // so the embedded image (the initial-task footprint the seL4 loader must
        // place below its fixed load address) shrinks toward only the reachable
        // closure. (The .text is monolithic per object, so this drops whole
        // unreferenced members, not individual functions.)
        println!("cargo:rustc-link-arg=--gc-sections");
        println!("cargo:rustc-link-search=native={}", exec_sel4.display());
        // OVERRIDE objects FIRST (before the closure archive): init-stubs.o +
        // aux-defs.o + demo-wire.o + libc-compat.o define symbols that ALSO exist
        // in the closure archive; first-definition-wins avoids duplicate symbols.
        for o in OVERRIDE_OBJS {
            let p = exec_sel4.join(o);
            if p.exists() {
                println!("cargo:rustc-link-arg={}", p.display());
            } else {
                println!("cargo:warning=override object missing: {}", p.display());
            }
        }
        // --start-group over the recursive Lean archives. rustc invokes rust-lld
        // directly (gnu-lld flavor) — bare `--start-group`, NOT `-Wl,...`.
        println!("cargo:rustc-link-arg=--start-group");
        for a in GROUP_ARCHIVES {
            let p = exec_sel4.join(a);
            if p.exists() {
                println!("cargo:rustc-link-arg={}", p.display());
            } else {
                println!("cargo:warning=group archive missing: {}", p.display());
            }
        }
        println!("cargo:rustc-link-arg=--end-group");
        // GMP after the group.
        let gmp = exec_sel4.join("libgmp.a");
        if gmp.exists() {
            println!("cargo:rustc-link-arg={}", gmp.display());
        }
        // The static C++ runtime (libstdc++/libsupc++) + libgcc exception/atomic
        // helpers from the aarch64-linux-musl GCC. These statics have ZERO `svc`
        // (verified) — every syscall routes through the seL4 musl libc. Grouped
        // (libstdc++ <-> libgcc_eh <-> libsupc++ are recursive).
        for lib in cxx_runtime_archives() {
            let s = lib.to_string_lossy();
            if s.starts_with("--") {
                println!("cargo:rustc-link-arg={s}");
            } else if lib.exists() {
                println!("cargo:rustc-link-arg={s}");
            } else {
                println!("cargo:warning=C++ runtime archive missing: {s}");
            }
        }
        // The seL4 musl libc.a (also carries libm). -L is in .cargo/config.toml;
        // pull -lc explicitly so the runtime's malloc/write/... resolve to it.
        println!("cargo:rustc-link-search=native={}", musl_sel4.join("lib").display());
        println!("cargo:rustc-link-arg=-lc");
    } else {
        println!(
            "cargo:warning=executor seL4 archives ({}) not provisioned — run \
             ../executor-rootserver/scripts/relink-roottask.sh. The PD will not link \
             the verified turn yet.",
            exec_sel4.display()
        );
    }
}

/// Objects placed BEFORE the closure archive (first-definition-wins overrides the
/// archive member). Mirrors ../executor-rootserver/build.rs.
const OVERRIDE_OBJS: &[&str] = &["init-stubs.o", "aux-defs.o", "demo-wire.o", "libc-compat.o"];

/// The recursive-group archives + the panic-if-reached stubs, in relink order.
/// libgmp.a is appended after the group by the caller.
const GROUP_ARCHIVES: &[&str] = &[
    "libdregg_lean_elf.a",
    "libleanrt_elf.a",
    "libInit_elf.a",
    "libStd_elf.a",
    "libLean_elf.a",
    "libmathlib_elf.a",
    "libBatteries_elf.a",
    "libAesop_elf.a",
    "libQq_elf.a",
    "libProofWidgets_elf.a",
    "libPlausible_elf.a",
    "libImportGraph_elf.a",
    "libLeanSearchClient_elf.a",
    "libMetatheory_elf.a",
    "libleancpp_kernel_elf.a",
    // THE REAL CRYPTO FLOOR: the Lean-ABI shim object + the carried-crypto Rust
    // staticlib (Poseidon2 + BLAKE3). A hashing turn computes a real digest.
    "crypto-floor.o",
    "libdregg_crypto_floor.a",
    "kernel-stub.o",
    "dead-stub.o",
];

/// The static C++ runtime + libgcc archives from the aarch64-linux-musl GCC,
/// wrapped in a group (mutually recursive). Overridable via DREGG_MUSL_TOOLCHAIN.
fn cxx_runtime_archives() -> Vec<PathBuf> {
    let base = env::var("DREGG_MUSL_TOOLCHAIN").unwrap_or_else(|_| {
        "/opt/homebrew/Cellar/aarch64-unknown-linux-musl/15.2.0/toolchain".to_string()
    });
    let base = PathBuf::from(base);
    let stdcpp = base.join("aarch64-unknown-linux-musl/lib64");
    let gcc = base.join("lib/gcc/aarch64-unknown-linux-musl/15.2.0");
    let mut v = vec![PathBuf::from("--start-group")];
    v.push(stdcpp.join("libstdc++.a"));
    v.push(stdcpp.join("libsupc++.a"));
    v.push(gcc.join("libgcc.a"));
    v.push(gcc.join("libgcc_eh.a"));
    v.push(PathBuf::from("--end-group"));
    v
}

/// Locate the Lean sysroot's `include` (for `lean/lean.h`). `lean --print-prefix`
/// if `lean` is on PATH; else None.
fn lean_sysroot_include() -> Option<PathBuf> {
    let prefix = Command::new("lean")
        .arg("--print-prefix")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())?;
    let inc = Path::new(&prefix).join("include");
    if inc.is_dir() {
        Some(inc)
    } else {
        None
    }
}

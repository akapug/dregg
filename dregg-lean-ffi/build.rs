// build.rs — wire the Rust binary to the compiled Lean kernel + Lean runtime.
//
// We link against:
//   * libdregg_lean.a — a single static archive of the native objects emitted by the
//     Lean compiler for `Dregg2.Exec.FFI` and its ENTIRE transitive dependency
//     closure (Dregg2 modules + mathlib + batteries + aesop + Qq + … — ~8200 .o).
//     The archive lives next to this build.rs; it was produced by compiling each
//     module's `.c` (lake's `:c` facet) with `leanc -c` and archiving with `llvm-ar`.
//   * the Lean runtime + stdlib in the elan toolchain `lib/lean` dir
//     (leancpp/Init/Std/Lean/leanrt + gmp/uv/c++), discovered from the active toolchain.
//
// Toolchain paths are discovered from `lake env` (LEAN_SYSROOT) with a fallback to the
// pinned elan toolchain, so this stays robust to elan being on PATH.

use std::path::PathBuf;
use std::process::Command;

/// Locate the project's `metatheory` Lean directory relative to this crate, so
/// `lake env` runs against the project's pinned toolchain regardless of the host
/// (no hardcoded absolute paths — works on macOS dev boxes and the Linux deploy
/// box alike). `CARGO_MANIFEST_DIR` is `.../dregg-lean-ffi`; the sibling is
/// `.../metatheory`. An explicit `DREGG_METATHEORY_DIR` override wins if set.
fn metatheory_dir() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("DREGG_METATHEORY_DIR") {
        let p = PathBuf::from(dir);
        if p.join("lean-toolchain").exists() {
            return Some(p);
        }
    }
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let candidate = crate_dir.parent().map(|p| p.join("metatheory"));
    candidate.filter(|p| p.join("lean-toolchain").exists())
}

fn lean_sysroot() -> Option<PathBuf> {
    // Prefer `lake env` (authoritative for the project's toolchain). `DREGG_LEAN_SYSROOT`
    // overrides for environments where `lake` is not on PATH at build time.
    if let Ok(s) = std::env::var("DREGG_LEAN_SYSROOT") {
        if !s.trim().is_empty() {
            return Some(PathBuf::from(s.trim()));
        }
    }
    if let Some(meta) = metatheory_dir() {
        if let Ok(out) = Command::new("lake")
            .args(["env", "printenv", "LEAN_SYSROOT"])
            .current_dir(&meta)
            .output()
        {
            let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
            if !s.is_empty() {
                return Some(PathBuf::from(s));
            }
        }
    }
    None
}

/// Probe the archive for an exported symbol via `nm`, so the C shim only declares string
/// bridges whose underlying Lean `@[export]` actually exists in THIS archive. A stale
/// archive missing a later export (e.g. `dregg_exec_handler_turn`) would otherwise leave a
/// dangling reference that `-dead_strip` resolves by dropping the WHOLE shim object — taking
/// the forest-auth + init bridges with it. We fail-closed: absent ⇒ the bridge is compiled out.
fn archive_exports(archive: &std::path::Path, symbol: &str) -> bool {
    let Ok(out) = Command::new("nm").arg(archive).output() else {
        return false;
    };
    let text = String::from_utf8_lossy(&out.stdout);
    // A DEFINED symbol shows in the text section as `T <name>`. The C symbol name is mangled
    // with a leading underscore on Mach-O (macOS) but NOT on ELF (Linux), so accept both
    // ` T _<symbol>` and ` T <symbol>`.
    let mach_o = format!(" T _{symbol}");
    let elf = format!(" T {symbol}");
    text.lines()
        .any(|l| l.trim_end().ends_with(&mach_o) || l.trim_end().ends_with(&elf))
}

fn main() {
    println!("cargo::rustc-check-cfg=cfg(lean_lib_present)");
    println!("cargo::rustc-check-cfg=cfg(dregg_handler_present)");

    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let lean_archive = crate_dir.join("libdregg_lean.a");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=src/lean_init.c");
    println!("cargo:rerun-if-changed=libdregg_lean.a");

    if !lean_archive.exists() {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a absent — building marshal-only; \
             lean_available() will be false. Build via scripts/rebuild-dregg2-closure.sh."
        );
        return;
    }

    // Resolve the Lean sysroot BEFORE committing to the `lean_lib_present` cfg: linking the
    // archive requires the Lean runtime/stdlib from the toolchain. If we cannot find it, we must
    // NOT advertise `lean_lib_present` (that cfg drives `lean_available()` and the FFI link), or
    // the build would either fail to link or falsely claim the Lean kernel is available.
    let Some(sysroot) = lean_sysroot() else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a present but could not resolve the Lean \
             sysroot (no DREGG_LEAN_SYSROOT and `lake env` failed) — building marshal-only. \
             Install elan + the project toolchain, or set DREGG_LEAN_SYSROOT to the toolchain root."
        );
        return;
    };
    let lean_lib = sysroot.join("lib").join("lean");
    let lean_include = sysroot.join("include");

    println!("cargo:rustc-cfg=lean_lib_present");

    // The handler-cutover export is a SECONDARY path; older archives predate it. Only wire its
    // string bridge when the archive actually exports it (otherwise the dangling ref breaks the
    // whole shim under -dead_strip). The forest-auth gate is the load-bearing path and is always
    // present.
    let handler_present = archive_exports(&lean_archive, "dregg_exec_handler_turn");
    if handler_present {
        println!("cargo:rustc-cfg=dregg_handler_present");
    } else {
        println!(
            "cargo:warning=dregg-lean-ffi: libdregg_lean.a lacks `dregg_exec_handler_turn` — \
             the handler-cutover bridge is compiled out (forest-auth gate unaffected). \
             Rebuild the archive to enable shadow_exec_handler_turn."
        );
    }

    // Compile the C init shim (it uses the `static inline` runtime helpers from
    // <lean/lean.h>, which have no linkable symbol and so must be used from C).
    let mut shim = cc::Build::new();
    shim.file("src/lean_init.c").include(&lean_include);
    if handler_present {
        shim.define("DREGG_HANDLER_TURN", None);
    }
    shim.compile("dregg_ffi_shim");

    // Our archive of the compiled Lean kernel + transitive closure.
    println!("cargo:rustc-link-search=native={}", crate_dir.display());
    println!("cargo:rustc-link-lib=static=dregg_lean");

    // The Lean runtime + stdlib (mirrors `leanc --print-ldflags`).
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!("cargo:rustc-link-search=native={}", sysroot.join("lib").display());
    for lib in ["leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv"] {
        println!("cargo:rustc-link-lib=static={lib}");
    }
    // C++ runtime the Lean runtime needs. macOS/clang uses libc++ (`c++`); Linux/gcc uses
    // libstdc++ (`stdc++`). Pick by target OS so the same build.rs links on both hosts.
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if target_os == "macos" {
        println!("cargo:rustc-link-lib=dylib=c++");
    } else {
        // Linux (and other ELF targets): libstdc++. `m`/`dl`/`pthread` are pulled in by the
        // default Rust link, and gmp/uv are linked statically above.
        println!("cargo:rustc-link-lib=dylib=stdc++");
    }
}

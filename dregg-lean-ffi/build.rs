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
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
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
    //
    // We suppress cc's automatic `rustc-link-lib` directive (`cargo_metadata(false)`)
    // and emit our own `+whole-archive` directive below. Reason: the final link runs
    // under `-Wl,-dead_strip` with `-nodefaultlibs`, and on macOS ld64 the shim's
    // single object is otherwise dead-stripped before the linker has recorded the
    // binary's undefined references to `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`
    // (an archive-member-ordering hazard). Forcing the whole archive in guarantees the
    // bridge symbols are present regardless of link order — the empirical fix for the
    // `marshal_roundtrip` / `full_turn_differential` link failures.
    let mut shim = cc::Build::new();
    shim.file("src/lean_init.c").include(&lean_include);
    if handler_present {
        shim.define("DREGG_HANDLER_TURN", None);
    }
    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives, NOT
    // `rustc-link-arg`. WHY: with the package's `links = "dregg_lean"` key, build-script
    // `rustc-link-lib` / `rustc-link-search` directives PROPAGATE to every DOWNSTREAM binary
    // (the `dregg-turn` lean-shadow tests, the node, …) — whereas `rustc-link-arg` is local
    // to this crate's own targets only. The cross-crate propagation is exactly what the
    // shadow harness needs to resolve `dregg_ffi_init` / `dregg_exec_full_forest_auth_str`.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical fix for the
    // earlier `Undefined symbols` link failures). `+whole-archive` is a link-LIB modifier,
    // so it propagates too.
    shim.cargo_metadata(false);
    shim.compile("dregg_ffi_shim");
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let shim_archive = out_dir.join("libdregg_ffi_shim.a");

    // We drive the link with `rustc-link-lib` / `rustc-link-search` directives ONLY. With the
    // package's `links = "dregg_lean"` key these PROPAGATE to EVERY target that links this
    // crate's rlib — the `dregg-turn` lean-shadow tests + node (downstream) AND this crate's
    // own bins/tests (which `use dregg_lean_ffi` and so link the rlib). Emitting `rustc-link-arg`
    // in ADDITION would DOUBLE-link the shim for the FFI-crate-internal consumers (they'd see
    // the shim both via the propagated lib AND the arg) → "duplicate symbol" errors. So: one
    // mechanism. The standalone differential bins each carry `use dregg_lean_ffi as _;` to force
    // the rlib edge so they inherit these propagated directives.
    //
    // The shim is linked `+whole-archive` so its single bridge object survives the final
    // `-Wl,-dead_strip` regardless of archive-member ordering (the empirical link-failure fix).
    let _ = shim_archive;
    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!("cargo:rustc-link-lib=static:+whole-archive=dregg_ffi_shim");
    println!("cargo:rustc-link-search=native={}", crate_dir.display());
    println!("cargo:rustc-link-lib=static=dregg_lean");
    println!("cargo:rustc-link-search=native={}", lean_lib.display());
    println!("cargo:rustc-link-search=native={}", sysroot.join("lib").display());
    for name in ["leancpp", "Init", "Std", "Lean", "leanrt", "Lake", "gmp", "uv"] {
        println!("cargo:rustc-link-lib=static={name}");
    }
    if target_os == "macos" {
        println!("cargo:rustc-link-lib=dylib=c++");
    } else {
        println!("cargo:rustc-link-lib=dylib=stdc++");
    }
}

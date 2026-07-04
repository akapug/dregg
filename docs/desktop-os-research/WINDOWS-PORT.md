# Windows port of deos — status (empirically measured, 2026-06-19)

Built/tested in a Parallels **Windows 11 on ARM64** guest (`aarch64-pc-windows-msvc`) via `prlctl exec`,
editing on the Mac. Reusable host→guest sync: `scripts/win-guest-sync.sh` (Parallels `prl_fs` is broken on
this guest, so the repo is pushed to a local guest dir `C:\deos` over a range-capable HTTP server on the
host's Parallels-subnet IP — `python -m http.server` truncates through the exec channel; a 206-honoring
server + `curl -C -` resumes to a hash-verified copy).

## What BUILDS / RUNS on Windows today

- ✅ **`sel4-thin` client — builds AND runs on Windows ARM64.** `cargo build --release --no-default-features
  --features sel4-thin` → `starbridge-v2.exe` (3.0 MB, ARM64). Prints the mock world; the `http://…` arg
  exercises the real reqwest+rustls wire path. Packaged: `deos-thin-windows-arm64.zip` (git-ignored). A real,
  runnable Windows deos thin/verifier client — the Windows-viable deliverable today.
- ✅ **gpui on Windows — NOT a wall.** A minimal probe pinning gpui/gpui_platform at the starbridge rev
  (`407a6ff`) with the same `[patch]`es built the full 400+-crate tree incl. the `gpui_windows` DirectX
  backend green (`Finished in 3m31s`) and the probe binary linked+ran. `runtime_shaders` forwards to the
  absent `gpui_macos` on Windows and is inert (like x11/wayland on macOS); `gpui_windows` is pulled by its
  `cfg(target_os="windows")` target-dep. **No Cargo.toml change needed for gpui-ui on Windows.**

## ✅ native-full BUILT + RUNS via the `x86_64-pc-windows-gnu` lever (the real path)

A real native-full **`starbridge-v2.exe`** (93.7 MB, `coff-x86-64`) is built, links the **REAL verified Lean
executor** (`lean_available()==true`), and RUNS under WoA x64 emulation: `--headless` drives the embedded
verified executor through 5 committed turns (real receipts, computron metering) and the **dual fail-closed
refusal citing the executor's own reasons** — the cap-gate (`granted ⊄ held`) and the Stingray conservation
gate (draw would exceed the ceiling). Those verdicts can only come from the linked Lean executor; a
marshal-only build cannot produce them. Packaged: `deos-native-full-windows-x86_64.zip` (git-ignored).

**The architectural correction (overturns this doc's earlier premise):** the lever is **GNU, not MSVC.** The
pinned Lean Windows toolchain (`lean-4.30.0-windows`) is an **LLVM-MinGW distribution**
(`x86_64-w64-windows-gnu`) — its runtime/stdlib ship only as GNU `.a` archives of `coff-x86-64`. MSVC
`link.exe` *cannot* consume them: `LNK1143: no symbol for COMDAT section` on every `libleanrt.a`/`libleancpp.a`
member (GNU-vs-MSVC COMDAT divergence; no MSVC-ABI Lean runtime exists). So:
1. **Toolchain (guest):** rust `x86_64-pc-windows-gnu` std (on the nightly starbridge-v2 pins), VS BuildTools
   x64 cross, **`lean-4.30.0-windows`** (the MinGW Lean), LLVM tools, an llvm-mingw sysroot (for the Win32
   import libs + clang headers the stripped Lean clang lacks).
2. **The x86_64 Windows Lean `.lib`** (`libdregg_lean.a`, 517 MB / 8567 members): `lake update` (mathlib
   olean+C cache) → `lake build Dregg2.Exec.FFI` + the 4 gate modules → `leanc -c` every emitted `.c` →
   `llvm-ar rcs`.
3. **The build.rs Windows-GNU splice** (`cfg(windows)`-gated, Mac/Linux byte-identical — `cargo check -p
   dregg-lean-ffi` clean): `ar→llvm-ar`, `nm→llvm-nm`, `ranlib→llvm-ar s` (the `ar_tool`/`nm_tool` helpers
   return the old names off-Windows); the `windows_msvc` gate still hard-skips to marshal-only, **windows-gnu
   proceeds**; the link arm emits the exact `leanc -###` lib set + `windows_gnu_link_env()` (sysroot search
   paths, a synthesised `libntdll.a` from the live ntdll exports, the gcc/gcc_eh/unwind shims);
   `-dead_strip→--gc-sections`, no rpath.
4. `cargo build --release --features native-full --target x86_64-pc-windows-gnu` → exit 0; `--headless` proves
   the verified executor. A full *window* needs a display (the `gpui_windows` d3d11/dxgi/dcomp/dwrite backend
   IS linked).

**Honest scaffold note (HORIZONLOG):** the build needs a small out-of-band guest scaffold (the llvm-mingw
header/import-lib backfill + a global `C:\mingw-shim` ntdll/EH shim dir + cargo `rustflags`). `build.rs`
synthesises its OWN ntdll/gcc shims into `OUT_DIR`; the global shim dir is what lets sibling crates (redb-as-dll
etc.) link. Follow-up: fold the backfill into a `scripts/win-bootstrap` for one-command reproducibility.

ARM64-Windows native-full still waits on upstream ARM64-Windows Lean binaries (don't exist) — Lever 2, not
blocking; the x86_64 binary runs natively on Intel/AMD Windows and under WoA emulation (*most of ember's
friends*).

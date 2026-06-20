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

## The ONE remaining wall — native-full's Lean archive (architectural, not build.rs)

`dregg-lean-ffi/build.rs` early-returns on Windows → marshal-only stubs (`lean_available()==false`), so a
native-full Windows build would be a hollow shell (no real verified executor). The deeper blocker measured:
**there is no ARM64-Windows Lean toolchain.** elan ships only `x86_64-pc-windows-msvc`; Lean 4.31 ships only
`x86_64-windows`. So even a perfect ar/nm→lib.exe/dumpbin splice can only produce **x86_64 COFF** objects,
which cannot link into our **aarch64** Rust binary. (macOS has both arches; Windows does not.)

## The lever — build native-full for `x86_64-pc-windows-msvc`

The cleanest path to a *real* native-full Windows installer (the embedded verified executor + the gpui
window):
1. Provision the **x86_64** Windows toolchain (rustup `x86_64-pc-windows-msvc`, VS Build Tools x64, the
   `x86_64-windows` Lean toolchain) — all of which exist for Windows x64; the binary runs under Windows-on-ARM
   x64 emulation (and natively on real Intel/AMD Windows — *most of ember's friends*).
2. Build the **x86_64 Windows Lean `.lib`** (`lake`/`leanc` + the x86_64 Lean toolchain).
3. Write the **build.rs Windows-MSVC splice** (now finite + *testable*): `lib.exe`/`llvm-lib` (not `ar`),
   `dumpbin`/`llvm-nm` symbol scan, `/OPT:REF` (not `-dead_strip`), no rpath, static-CRT `.lib` link; lift the
   `gate_os=="windows"` early-return. `cfg(windows)`-gated so mac/linux are untouched.
4. Build `--features native-full` for x86_64-windows in the guest; verify `lean_available()` is true + the gpui
   window opens.

Once x86_64 is chosen, the splice can be *exercised* — so it's real engineering, not the dead/unverifiable
debt that writing an aarch64 splice (which can never link) would be. ARM64-Windows native-full waits on
upstream ARM64-Windows Lean binaries (don't exist today) — Lever 2, not blocking.

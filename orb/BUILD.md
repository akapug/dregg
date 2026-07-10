# Building & verifying drorb

drorb is a machine-checked network orchestrator: the semantics are proven in
Lean 4, compiled to C by `leanc`, and linked into a native Rust dataplane. This
document is the reproducible build contract — a fresh checkout on **macOS** or
**Linux** with the documented dependencies builds, verifies, and passes
conformance via one command:

```sh
scripts/ci.sh          # from-scratch build + sorry-scan + dataplane link + conformance
scripts/ci.sh --quick  # the above minus the (slow) conformance suite
```

CI runs exactly this (`.github/workflows/ci.yml`, macOS + Linux matrix).

---

## Dependencies

| Dependency | Version / source | Why |
|---|---|---|
| **elan + Lean** | `leanprover/lean4:v4.17.0` (pinned in `lean-toolchain`) | Compiles the proofs; provides `leanc` and the Lean runtime the dataplane links. Install [elan](https://github.com/leanprover/elan); it puts `lean`/`lake` under `$HOME/.elan/bin` and reads the pinned version from `lean-toolchain`. |
| **Rust (cargo)** | nightly, pinned in `rust-toolchain.toml` | The native dataplane host, the AES-GCM fallback (`libaes_fallback.a`), and the workspace twins. Install via [rustup](https://rustup.rs). |
| **C toolchain** | Xcode CLT (macOS) / `build-essential` (Linux) | Compiles the FFI shims (`ffi/*.c`) and `leanc`-emitted C. Provides `cc` and `ar`. |
| **HACL*/EverCrypt** | gcc-compatible dist with `libevercrypt.a` | The F\*-verified crypto backend (Ed25519/X25519/AES-GCM/HKDF/SHA/ChaCha20) behind the TLS 1.3, JWT, and QUIC seams. See below — this is the one heavy dependency. |
| **python3** | any 3.x | The `sorry`-scan and the conformance driver. |
| **aioquic** (optional) | `pip install aioquic` in a venv | The QUIC/H3 conformance *client*. Without it, the QUIC/H3 scenarios report `SKIPPED` (not `FAIL`) — the suite still passes. |

`io-uring` on Linux is the **vendored Rust `io-uring` crate** — no system
`liburing-dev` is required.

### HACL*/EverCrypt — the one real setup cost

The crypto seam links `libevercrypt.a`. Building it from the HACL* source dist is
the only heavyweight step:

```sh
git clone https://github.com/hacl-star/hacl-star.git ~/src/hacl-star
cd ~/src/hacl-star/dist/gcc-compatible
./configure
make -j libevercrypt.a
```

This produces `libevercrypt.a` and the extracted `EverCrypt_*.h` headers next to
it. The KaRaMeL runtime headers used by the crypto shims default to
`$(dirname "$HACL_DIST")/karamel` (i.e. `~/src/hacl-star/dist/karamel`); override
with `KRML=` if yours live elsewhere.

Because this build is slow (tens of minutes), **CI caches it** (`actions/cache`,
keyed on the pinned HACL* ref) and rebuilds only on a cache miss — see the
commented HACL-provisioning block in `.github/workflows/ci.yml`. For a first CI
activation you seed the cache once (or replace the build step with a download of
a prebuilt dist you host). It is honestly a prebuilt-artifact/cache step, not a
per-run build.

---

## Environment

`scripts/ci.sh` sets these to the project convention when unset; export them to
point elsewhere. If you build by hand, set them yourself:

```sh
export PATH="$HOME/.elan/bin:$PATH"                       # lean / lake
export HACL_DIST="$HOME/src/hacl-star/dist/gcc-compatible"
export LIBRARY_PATH="$HACL_DIST"                          # resolves -levercrypt at link
# macOS runtime dylib resolution:
export DYLD_LIBRARY_PATH="$HACL_DIST"
# Linux runtime (harmless; libevercrypt is linked static):
export LD_LIBRARY_PATH="$HACL_DIST"
```

`-levercrypt` is resolved via `LIBRARY_PATH` (= `HACL_DIST`), never a hard-coded
`-L` path, so the build is machine-independent.

---

## The one command

```sh
scripts/ci.sh
```

What it does, in order:

1. **Environment check** — verifies `lean`/`lake`/`cargo`/`cc`/`ar`/`python3` are
   present and that `HACL_DIST` holds `libevercrypt.a` + the EverCrypt headers.
   Clear, actionable error on anything missing.
2. **From-scratch proof build** — `rm -rf .lake/build && lake build`. Builds every
   `@[default_target]` verified library from a clean state.
3. **Tree-wide `sorry`/`sorryAx` scan** — strips Lean comments/docstrings (which
   routinely *mention* "`sorry`"), then fails if any literal `sorry`/`sorryAx`
   token survives in code.
4. **FFI prerequisites** — `libaes_fallback.a` (cargo) and the C shims
   (`cgi_exec`, `crypto_shim`, `derp_net`, `tls_p256_shim`, `mac_io`, `mac_udp`;
   plus `glibc_isoc23_compat` on Linux). These are what the dataplane host and the
   `orb*` exes link; a fresh checkout has none.
5. **Native dataplane link** — `ffi/build-dataplane-lib.sh` (archives the
   `leanc`-compiled proven serve into `libdrorb.a`) then `cargo build --release`
   (the Rust host that links it). Proves the whole verified→native chain resolves.
6. **Conformance** — `conformance/run.sh` drives the base + parity suites against
   the real binaries; the gate fails on any scenario `FAIL`. `--quick` skips this.

Exit code is non-zero on any real failure.

---

## Platform notes

- **macOS** — the `leanc`/host links pass `-Wl,-no_data_const` (an ld64
  `__DATA_CONST` workaround), applied automatically via `System.Platform.isOSX`
  in `lakefile.lean` (`osLink`) and in `crates/dataplane/build.rs`. No manual step.
- **Linux** — aws-lc (inside `libaes_fallback.a`) references the glibc≥2.38 C23
  symbols `__isoc23_sscanf` / `__isoc23_strto*`, which the Lean toolchain's older
  bundled glibc lacks at the final `leanc` exe link. `ffi/build-glibc-compat.sh`
  compiles ABI-identical aliases into `ffi/glibc_isoc23_compat.o`, which
  `osLink` inserts before the aws-lc archive. `scripts/ci.sh` runs it
  automatically on Linux. (The cargo-linked dataplane host uses the *system*
  linker/glibc and needs no shim.)
- **QUIC / H3** — need the `aioquic` Python client; without it those scenarios
  report `SKIPPED` and the suite still passes.

---

## Why the gate is from-scratch, not incremental

`lake` caches compiled `.olean` files under `.lake/build`. An **incremental**
`lake build` can report success while a proof no longer closes: if a dependency's
`.olean` is stale, Lake may replay the cached artifact instead of re-checking the
proof against the current sources. A green incremental build is therefore **not**
evidence that the current tree verifies.

The honest gate wipes `.lake/build` and rebuilds every proof from source
(`rm -rf .lake/build && lake build`). It is slower, and that is the point: it is
the only build whose green means *these sources, checked now, close every proof*.
FFI objects (`ffi/*.o`) and `target/release/libaes_fallback.a` live outside
`.lake/build`, so the wipe costs only Lean recompilation, not the C/Rust rebuild.

---

## Machine-readable output

- `conformance/results.json` — base suite verdicts + counts.
- `conformance/results_parity.json` — parity harness verdicts + counts.

`PASS`/`FAIL`/`UNWIRED`/`SKIPPED`: `FAIL` fails the gate; `UNWIRED`
(proven-but-not-yet-connected) and `SKIPPED` (optional client/tool absent) are
diagnostics, not failures.

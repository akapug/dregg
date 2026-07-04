# syntax=docker/dockerfile:1.7
#
# DreggNet container image — runs the Linux serving stack on a Mac via Docker.
#
# DEFAULT BUILD = the `dregg-cloud` operator CLI: the runnable "wasmi-tier exec"
# demo path. It drives control → bridge → durable → exec (owned wasmi sandbox),
# genuinely running a metered, durable, sandboxed workload (add(40,2)=42) in the
# owned pure-Rust wasmi sandbox; the stronger tiers are honest fail-closed seams.
# Its dependency closure does NOT pull the Linux-only `net/` (httpe) stack, so it
# builds and runs cleanly in a Linux container without the heavy Elide net closure.
#
# NOT THE DEFAULT = the httpe `dreggnet-gateway` (the fly-compatible machines
# API). It is a real serving binary: `dreggnet-gateway --port 8080` binds a TCP
# listener and serves the route table + lease gate over HTTP (see
# docs/RUN-LOCALLY.md "The gateway"). It is not the default build only because it
# pulls the full Linux-only Elide net closure (forked ntex/compio/rustls + capnp
# codegen), which is heavy. Build it here with
# `--build-arg BUILD_PKG=dreggnet-gateway` (pulls the whole net stack). The one
# remaining seam is the create→fulfill wire-up, documented in RUN-LOCALLY.md.
#
# The pinned nightly toolchain (rust-toolchain.toml: nightly-2026-03-24) is
# installed by rustup automatically from the toolchain file.

ARG RUST_IMAGE=rust:slim-bookworm

# ---------------------------------------------------------------------------
# build stage
# ---------------------------------------------------------------------------
FROM ${RUST_IMAGE} AS build

# What to build. Defaults to the runnable CLI demo path.
ARG BUILD_PKG=dreggnet-cli
ARG CARGO_PROFILE=release
ARG BUILD_FEATURES=

ENV CARGO_TERM_COLOR=always \
    DEBIAN_FRONTEND=noninteractive

# System deps the net closure expects:
#  - build-essential + perl: native build scripts (and openssl-sys `vendored`,
#    which durable requests on Linux, compile from source).
#  - libssl-dev + pkg-config: the high-level `openssl` crate is pulled into the
#    CLI graph with a non-vendored openssl-sys, so the build links Debian's
#    system OpenSSL.
#  - cmake + clang: kept for any transitive native build script. The owned wasmi
#    interpreter is pure-Rust and needs no cmake/clang/native compute-engine tree.
#  - git + ca-certificates: fetch the [patch.crates-io] git forks.
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        perl \
        pkg-config \
        libssl-dev \
        cmake \
        clang \
        git \
        ca-certificates \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src

# Install the pinned nightly toolchain FIRST (its own cached layer), so editing
# source does not re-trigger a toolchain download.
COPY rust-toolchain.toml ./
RUN rustup show

# The whole workspace (the .dockerignore trims target/ and .git/). The compute
# engine is the owned in-crate wasmi sandbox — no submodule, all sources ship in
# the context.
COPY . .

# Build + lift the binary out of the BuildKit cache mount in the same step.
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/usr/local/cargo/git \
    --mount=type=cache,target=/src/target \
    set -eux; \
    prof_flag=""; out_dir="debug"; \
    if [ "$CARGO_PROFILE" = "release" ]; then prof_flag="--release"; out_dir="release"; fi; \
    feat_flag=""; \
    if [ -n "$BUILD_FEATURES" ]; then feat_flag="--features $BUILD_FEATURES"; fi; \
    cargo build --locked -p "$BUILD_PKG" $prof_flag $feat_flag; \
    mkdir -p /out; \
    # Lift any produced binaries (the CLI produces `dregg-cloud`).
    find "target/${out_dir}" -maxdepth 1 -type f -perm -u+x ! -name '*.so' \
        \( -name 'dregg-cloud' -o -name 'dreggnet-*' \) -exec cp -v {} /out/ \; ; \
    ls -la /out

# ---------------------------------------------------------------------------
# runtime stage — slim image with the CLI binary
# ---------------------------------------------------------------------------
FROM debian:bookworm-slim AS runtime

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates \
        libssl3 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=build /out/ /usr/local/bin/

# A writable home for the CLI's lease/workload registry + the bundled SQLite
# durable store.
ENV DREGGNET_STATE_DIR=/var/lib/dreggnet
RUN mkdir -p /var/lib/dreggnet
WORKDIR /var/lib/dreggnet

# A turnkey end-to-end demo: open a funded lease, run a metered durable workload,
# print the lifecycle + meter. `docker compose run --rm dreggnet dreggnet-demo`.
RUN cat > /usr/local/bin/dreggnet-demo <<'EOF' \
 && chmod +x /usr/local/bin/dreggnet-demo
#!/bin/sh
set -e
WORK="${DREGGNET_STATE_DIR:-/var/lib/dreggnet}"
cd "$WORK"
printf '(module (func (export "run") (result i32) (i32.const 42)))\n' > workload.wat
echo "==> dregg-cloud lease open --cap-tier sandboxed --budget 100"
OUT=$(dregg-cloud lease open --cap-tier sandboxed --budget 100)
echo "$OUT"
LEASE=$(echo "$OUT" | sed -n 's/^lease opened: //p')
echo
echo "==> dregg-cloud run --lease $LEASE --lang wat --source workload.wat"
dregg-cloud run --lease "$LEASE" --lang wat --source workload.wat
echo
echo "==> dregg-cloud status"
dregg-cloud status
EOF

# Not a daemon: default to help. compose keeps the container alive (sleep) so you
# can `docker compose exec dreggnet dregg-cloud ...` or run `dreggnet-demo`.
CMD ["dregg-cloud", "--help"]

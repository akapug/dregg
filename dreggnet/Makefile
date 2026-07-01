# DreggNet — one command to build, lint, and validate the repo.
#
#   make test        the full offline-green gauntlet (default; env-gated lanes skip cleanly)
#   make test-fast   the quick unit subset (lib tests only, no integration/e2e)
#   make lint        cargo fmt --check + clippy
#   make build       build the service stack + binaries (macOS/Linux portable)
#
# Gated lanes (documented in docs/TESTING.md), run only with their env present:
#   make test-pg       Postgres durable resume   (needs DATABASE_URL)
#   make test-verify   verified on-chain read    (needs DREGGNET_LIVE_NODE, AGPL dregg-verify)
#   make test-net      the Linux gateway/net stack (Linux only)
#
# Toolchain is pinned by rust-toolchain.toml (nightly-2026-03-24, edition 2024).

# The portable service stack — the always-green offline path (matches CI's macOS job).
SERVICE_CRATES := -p dreggnet-cli -p dreggnet-durable -p dreggnet-exec \
                  -p dreggnet-bridge -p dreggnet-control -p dreggnet-webapp -p dreggnet-ops

.DEFAULT_GOAL := test
.PHONY: test test-fast test-pg test-verify test-net test-workload bench bench-smoke lint fmt fmt-fix clippy build build-gateway clean help

# The service crates that carry a `[[bench]]` (hand-rolled `harness = false`
# timing harnesses, offline — no criterion). All honor BENCH_* env knobs.
BENCH_CRATES := -p dreggnet-exec -p dreggnet-durable -p dreggnet-webapp

## test: the full offline-green gauntlet (service stack + any env-present gated lane)
test:
	@bash scripts/test.sh

## test-fast: the quick unit subset — lib tests only, no integration/e2e
test-fast:
	cargo test --lib $(SERVICE_CRATES)

## test-pg: the Postgres durable-resume lane (needs DATABASE_URL=postgres://…)
test-pg:
	@test -n "$$DATABASE_URL" || { echo "set DATABASE_URL=postgres://user:pass@host/db first"; exit 1; }
	cargo test -p dreggnet-durable --features pg --test durable_resume_pg -- --ignored --test-threads=1

## test-verify: the verified on-chain read lane (needs DREGGNET_LIVE_NODE; AGPL dregg-verify)
test-verify:
	@test -n "$$DREGGNET_LIVE_NODE" || { echo "set DREGGNET_LIVE_NODE=host:port (a live dregg node) first"; exit 1; }
	cargo test -p dreggnet-bridge --features dregg-verify --test verified_read_live -- --ignored --nocapture

## test-net: the Linux gateway + net/ stack (httpe, transport, tailscale, …) — Linux only
test-net:
	cargo test -p httpe -p transport -p tailscale -p wireguard -p dns -p pki

## test-workload: the workload-simulation suite (docs/WORKLOAD-TEST-PLAN.md) — gated
##   out of `make test` (not in the service-crate set; every scenario is #[ignore]d).
##   Scale it up with DREGGNET_WL_* env knobs; soak with DREGGNET_WL_DURATION=8h.
test-workload:
	cargo test -p dreggnet-workload --release -- --ignored --nocapture --test-threads=1

## bench: the service-stack characterization benches (exec/durable/webapp) — full
##   iteration counts. Scale per bench with BENCH_ITERS / BENCH_WIDE_ITERS /
##   BENCH_WIDE_N / BENCH_DISK_ITERS / BENCH_DURABLE_ITERS env knobs.
bench:
	cargo bench $(BENCH_CRATES)

## bench-smoke: compile every bench + run each at tiny iteration counts — a
##   correctness/regression smoke (the CI bench lane), NOT a perf gate.
##   BENCH_ITERS stays >=4 (the durable bench scales its step sweep by /4).
##   BENCH_DISK_ITERS=0 skips the durable bench's slow on-disk duroxide path
##   (run-to-completion + crash-resume) — too slow + I/O-contention-flaky for a
##   smoke gate; `make bench` (default 50) exercises it for real.
bench-smoke:
	BENCH_ITERS=4 BENCH_DISK_ITERS=0 BENCH_DURABLE_ITERS=4 \
	BENCH_WIDE_ITERS=4 BENCH_WIDE_N=1,2 \
	cargo bench $(BENCH_CRATES)

## lint: format check + clippy (clippy advisory, mirrors CI)
lint: fmt clippy

## fmt: check formatting (hard gate in CI)
fmt:
	cargo fmt --all -- --check

## fmt-fix: apply formatting
fmt-fix:
	cargo fmt --all

## clippy: lint the gateway/net stack (-D warnings; advisory in CI)
clippy:
	cargo clippy $(SERVICE_CRATES) -- -D warnings

## build: build the service stack + its binaries (macOS/Linux portable)
build:
	cargo build $(SERVICE_CRATES)

## build-gateway: cross-build the Linux-only httpe gateway from any host (needs cargo-zigbuild)
build-gateway:
	cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-gateway

## clean: cargo clean
clean:
	cargo clean

## help: list targets
help:
	@grep -E '^## ' $(MAKEFILE_LIST) | sed 's/^## /  /'

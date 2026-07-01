#!/usr/bin/env bash
#
# DreggNet STAGING deploy — cross-build locally, ship binaries, run on the box.
#
# The box stays SMALL: we do NOT compile Rust on it (a 2 GB box OOMs building the
# DreggNet/net closure). Instead we cross-build the gateway + cli with
# `cargo zigbuild --target x86_64-unknown-linux-gnu` on this Mac, rsync the
# binaries + the compose to the box, and `docker compose up -d` there. The only
# thing the box "builds" is the trivial COPY-binary-into-debian-slim runtime
# image (seconds, no Rust).
#
# The dregg NODE is a separate story: it links a host-native Lean archive and
# CANNOT be cross-compiled — see README.md ("The dregg node") and build_node().
#
# Usage:
#   BOX_HOST=ec2-1-2-3-4.compute-1.amazonaws.com \
#   SSH_KEY=~/.ssh/dreggnet-staging.pem \
#     deploy/staging/deploy.sh            # build + ship + up
#
#   deploy/staging/deploy.sh build        # cross-build only
#   deploy/staging/deploy.sh ship         # rsync only (assumes built)
#   deploy/staging/deploy.sh up           # docker compose up on the box
#
set -euo pipefail

# ---- config (override via env) ---------------------------------------------
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"

# Pin a baseline glibc so the gnu binary runs on the box's libc. zigbuild lets us
# target a specific glibc version; 2.31 (Ubuntu 20.04 / Debian 11) is a safe
# floor that debian:bookworm-slim (the runtime image) satisfies.
TARGET="${TARGET:-x86_64-unknown-linux-gnu.2.31}"
TARGET_DIR="${TARGET%%.*}"          # the actual rustc target triple (strip the .2.31)

BOX_USER="${BOX_USER:-ubuntu}"
BOX_HOST="${BOX_HOST:-}"            # the staging box's public DNS / IP (required to ship/up)
SSH_KEY="${SSH_KEY:-$HOME/.ssh/dreggnet-staging.pem}"
REMOTE_DIR="${REMOTE_DIR:-/opt/dreggnet}"

STAGE_DIR="$HERE/.stage"           # local staging area assembled before rsync

ssh_box() { ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new "$BOX_USER@$BOX_HOST" "$@"; }

require_box() {
  [ -n "$BOX_HOST" ] || { echo "ERROR: set BOX_HOST=<public-dns-or-ip>" >&2; exit 2; }
}

# ---- step 1: cross-build the DreggNet serving binaries ----------------------
build() {
  command -v cargo-zigbuild >/dev/null || { echo "ERROR: cargo-zigbuild not installed (cargo install cargo-zigbuild; brew install zig)" >&2; exit 2; }
  rustup target add "$TARGET_DIR" >/dev/null 2>&1 || true

  echo "==> cross-building gateway + cli + ops for $TARGET"
  # NOTE: the gateway pulls the heavy Linux-only Elide net closure (httpe: forked
  # ntex/compio/rustls + capnp codegen) and the exec/durable/polyana closure. The
  # cli is pure-Rust over the control plane. The ops dashboard is pure-std (no
  # httpe) + sqlx-postgres for the meter outbox. A cold build is heavy; if `exec/`
  # is mid-flight (polyana-improvement lane) it may transiently fail — that is the
  # documented exec-green dependency, NOT a deploy bug. Fail loudly, do not ship
  # stale artifacts.
  # `dreggnet-provider` (W3) is the autonomous orchestrator daemon the compose's
  # `provider` service runs; it lives in dreggnet-control (default features =
  # node-trusted cell-API read, Lean-free, so it cross-builds with zigbuild like the
  # rest — the light-client-VERIFIED read is the `--features dregg-verify` deploy
  # choice, which links the verified core and is built on a Lean-capable box).
  ( cd "$REPO_ROOT" && cargo zigbuild --locked --release --target "$TARGET" \
      -p dreggnet-gateway -p dreggnet-cli -p dreggnet-ops -p dreggnet-webauth \
      -p dreggnet-control )

  echo "==> collecting binaries into $STAGE_DIR/bin"
  rm -rf "$STAGE_DIR"; mkdir -p "$STAGE_DIR/bin"
  local out="$REPO_ROOT/target/$TARGET_DIR/release"
  for b in dreggnet-gateway dreggnet dreggnet-ops dreggnet-webauth dregg-authctl dreggnet-provider; do
    [ -f "$out/$b" ] || { echo "ERROR: expected binary $out/$b not found" >&2; exit 1; }
    cp -v "$out/$b" "$STAGE_DIR/bin/"
  done
  cp "$HERE/docker-compose.yml" "$HERE/Dockerfile.runtime" "$HERE/Caddyfile" "$STAGE_DIR/"
  # The headscale mesh control config + ACL policy. Must be staged so the rsync
  # --delete in ship() does NOT wipe /opt/dreggnet/headscale on the box (the
  # headscale DB itself lives in a docker named volume and is untouched).
  cp -r "$HERE/headscale" "$STAGE_DIR/headscale"
  # The PUBLIC portal (portal.example.com): the baked static site (index.html,
  # cell.html, portal.js, styles.css) is committed under deploy/staging/portal; the
  # wasm light-client bundle (~15MB, kept out of git) is copied fresh from breadstuffs
  # at stage time. Regenerate the static site with:
  #   cd ~/dev/breadstuffs/deos-view && cargo run --no-default-features --features web \
  #     --example portal_bake -- ~/dev/DreggNet/deploy/staging/portal
  cp -r "$HERE/portal" "$STAGE_DIR/portal"
  # The published minisites (static web hosting): `sites/<name>/…` is mounted into
  # the gateway (`/srv/sites`) and published at boot as `<name>.example.com`. Must
  # be staged so the rsync --delete does not wipe /opt/dreggnet/sites on the box.
  [ -d "$HERE/sites" ] && cp -r "$HERE/sites" "$STAGE_DIR/sites" || mkdir -p "$STAGE_DIR/sites"
  BREADSTUFFS="${BREADSTUFFS:-$HOME/dev/breadstuffs}"
  if [ -d "$BREADSTUFFS/wasm/pkg" ]; then
    mkdir -p "$STAGE_DIR/portal/pkg"
    cp "$BREADSTUFFS"/wasm/pkg/dregg_wasm* "$STAGE_DIR/portal/pkg/" 2>/dev/null || true
    echo "==> portal: copied the wasm light-client bundle from $BREADSTUFFS/wasm/pkg"
  else
    echo "WARNING: $BREADSTUFFS/wasm/pkg not found — the portal ships WITHOUT the in-tab" >&2
    echo "         trustless-verify engine (the live network view still works). Set BREADSTUFFS." >&2
  fi
  [ -f "$HERE/.env" ] && cp "$HERE/.env" "$STAGE_DIR/.env" || cp "$HERE/.env.example" "$STAGE_DIR/.env"
  echo "==> staged:"; ls -la "$STAGE_DIR" "$STAGE_DIR/bin"
}

# ---- the dregg node: build a linux/amd64 IMAGE (NOT cross-compilable) -------
# dregg-node links libdregg_lean.a (host-native Lean objects) unconditionally, so
# zigbuild can't produce a runnable x86_64-linux binary from this arm64 Mac. The
# node ships as a pre-built linux/amd64 image. Build it on a Lean-capable builder:
#   - a beefy CI runner / x86_64 EC2 build box with elan/lake + warm mathlib, OR
#   - `docker buildx --platform linux/amd64` from breadstuffs' docker/Dockerfile
#     (node target) on a builder that has the Lean toolchain.
# Then push to a registry (GHCR/ECR) or `docker save | ssh box docker load`, and
# set DREGG_NODE_IMAGE in .env. This script does not attempt it from the Mac.
build_node() {
  echo "dregg-node is NOT cross-compilable (host-native Lean archive)." >&2
  echo "Build a linux/amd64 image on a Lean-capable builder, e.g. from breadstuffs:" >&2
  echo "  cd ~/dev/breadstuffs && docker buildx build --platform linux/amd64 \\" >&2
  echo "    --target node -f docker/Dockerfile -t <registry>/dregg-node:staging --push ." >&2
  echo "  (the builder needs elan/lake + warm mathlib for build.rs to splice the Lean archive)" >&2
  echo "Then set DREGG_NODE_IMAGE in deploy/staging/.env and re-run 'up'." >&2
}

# ---- step 2: ship the staged dir to the box --------------------------------
ship() {
  require_box
  [ -d "$STAGE_DIR" ] || { echo "ERROR: nothing staged; run 'build' first" >&2; exit 1; }
  echo "==> rsync $STAGE_DIR/ -> $BOX_USER@$BOX_HOST:$REMOTE_DIR/"
  ssh_box "sudo mkdir -p $REMOTE_DIR && sudo chown -R $BOX_USER $REMOTE_DIR"
  rsync -avz --delete -e "ssh -i $SSH_KEY -o StrictHostKeyChecking=accept-new" \
    "$STAGE_DIR/" "$BOX_USER@$BOX_HOST:$REMOTE_DIR/"
}

# ---- step 3: bring the stack up on the box ---------------------------------
up() {
  require_box
  echo "==> docker compose up -d on the box"
  ssh_box "cd $REMOTE_DIR && docker compose up -d --build && docker compose ps"
}

down() { require_box; ssh_box "cd $REMOTE_DIR && docker compose down"; }
logs() { require_box; ssh_box "cd $REMOTE_DIR && docker compose logs -f --tail=100"; }

case "${1:-all}" in
  build)      build ;;
  build-node) build_node ;;
  ship)       ship ;;
  up)         up ;;
  down)       down ;;
  logs)       logs ;;
  all)        build; ship; up ;;
  *) echo "usage: $0 {all|build|build-node|ship|up|down|logs}" >&2; exit 2 ;;
esac

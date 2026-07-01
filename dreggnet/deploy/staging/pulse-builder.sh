#!/usr/bin/env bash
#
# pulse-builder.sh — PULSE a stoppable Lean-capable linux/amd64 build box to bake
# the dregg-node:staging image, then stop it so we pay compute only during a build.
#
# WHY THIS EXISTS
#   dregg-node links `libdregg_lean.a` (the native objects the Lean compiler emits
#   for the verified kernel's whole transitive closure: Dregg2 + mathlib + ...).
#   That archive is HOST-NATIVE and CANNOT be cross-compiled from the arm64 Mac.
#   So the node is built natively on a linux/amd64 box that has the Lean toolchain
#   (elan/lake + mathlib) AND the rust nightly the workspace pins.
#
#   Standing that box up for every build is wasteful; leaving it running is
#   expensive. The fix: a STOPPABLE builder whose EBS root volume persists the
#   toolchain + the cargo/lake/leanc caches. We START it, BUILD, STOP it. Idle
#   cost is just the EBS (~$6.4/mo for 80 GB gp3); compute is paid only while
#   running (~$0.34/hr for c5.2xlarge).
#
# ONE-COMMAND RE-PULSE (start -> build -> ship -> stop):
#   deploy/staging/pulse-builder.sh build
#
# SUBCOMMANDS
#   start     aws ec2 start-instances + wait for running + wait for SSH
#   stop      aws ec2 stop-instances + wait for stopped
#   status    print instance state, public IP, and the cost note
#   setup     install the toolchain on the builder (idempotent; run once, then
#             it persists on the EBS so future pulses skip it)
#   sync      push the breadstuffs source (git archive HEAD) to the builder
#   compile   on the builder: lake build the Lean closure -> linux libdregg_lean.a,
#             then cargo build --release -p dregg-node, then docker build the
#             dregg-node:staging image, then docker save -> a gzipped tarball
#   pull      copy the image tarball back to this machine (deploy/staging/.artifacts)
#   ship      copy the image tarball to the staging box + docker load there
#   build     start -> setup -> sync -> compile -> pull -> ship -> stop  (the pulse)
#
# All steps are idempotent and fail loud (set -euo pipefail).
set -euo pipefail

# ---- config (override via env) ---------------------------------------------
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# The pulse builder (a STOPPED-by-default Lean-capable linux/amd64 EC2 box).
INSTANCE_ID="${INSTANCE_ID:-<INSTANCE_ID>}"
AWS_REGION="${AWS_REGION:-us-east-1}"
export AWS_DEFAULT_REGION="$AWS_REGION"

SSH_KEY="${SSH_KEY:-$HOME/.ssh/dreggnet-staging.pem}"
BUILDER_USER="${BUILDER_USER:-ubuntu}"

# Local breadstuffs checkout (source of truth; we ship `git archive HEAD`).
BREADSTUFFS="${BREADSTUFFS:-$HOME/dev/breadstuffs}"

# mathlib pin matching breadstuffs/metatheory/lakefile.toml (path require resolves
# to ~/src/mathlib4 on the builder, i.e. ../../../src/mathlib4 from breadstuffs).
MATHLIB_URL="${MATHLIB_URL:-https://github.com/leanprover-community/mathlib4.git}"
MATHLIB_REV="${MATHLIB_REV:-1c2b90b13009c65b090d95a83c98e248deafb6f1}"

# The rust toolchain the workspace pins (breadstuffs/rust-toolchain.toml = nightly).
RUST_CHANNEL="${RUST_CHANNEL:-nightly}"

IMAGE_TAG="${IMAGE_TAG:-dregg-node:staging}"
IMAGE_TARBALL="dregg-node-staging.tar.gz"

# Remote layout on the builder (all on the persistent EBS root volume).
R_SRC="/home/$BUILDER_USER/dev/breadstuffs"
R_MATHLIB="/home/$BUILDER_USER/src/mathlib4"
R_BUILD="/home/$BUILDER_USER/dregg-build"          # caches + image context + tarball
R_OBJCACHE="$R_BUILD/objcache"                       # persistent leanc -c object cache

# The staging box that runs the node (to receive the image). Optional for `ship`.
STAGING_HOST="${STAGING_HOST:-<BUILDER_HOST>}"
STAGING_USER="${STAGING_USER:-ubuntu}"

ARTIFACTS="$HERE/.artifacts"

# ---- helpers ----------------------------------------------------------------
log() { printf '\n==> %s\n' "$*" >&2; }
die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }

builder_ip() {
  aws ec2 describe-instances --instance-ids "$INSTANCE_ID" \
    --query 'Reservations[0].Instances[0].PublicIpAddress' --output text
}
builder_state() {
  aws ec2 describe-instances --instance-ids "$INSTANCE_ID" \
    --query 'Reservations[0].Instances[0].State.Name' --output text
}

ssh_builder() {
  local ip; ip="$(builder_ip)"
  [ -n "$ip" ] && [ "$ip" != "None" ] || die "builder has no public IP (is it running? run: $0 start)"
  ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new -o ServerAliveInterval=30 \
      "$BUILDER_USER@$ip" "$@"
}

wait_ssh() {
  local ip; ip="$(builder_ip)"
  log "waiting for SSH on $ip ..."
  for i in $(seq 1 40); do
    if ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new -o ConnectTimeout=5 \
         "$BUILDER_USER@$ip" 'true' 2>/dev/null; then
      log "SSH up."; return 0
    fi
    sleep 8
  done
  die "SSH never came up on $ip"
}

# ---- lifecycle --------------------------------------------------------------
start() {
  local st; st="$(builder_state)"
  log "builder $INSTANCE_ID state: $st"
  if [ "$st" != "running" ]; then
    log "starting builder ..."
    aws ec2 start-instances --instance-ids "$INSTANCE_ID" >/dev/null
    aws ec2 wait instance-running --instance-ids "$INSTANCE_ID"
  fi
  wait_ssh
  log "builder running at $(builder_ip)"
}

stop() {
  log "stopping builder $INSTANCE_ID ..."
  aws ec2 stop-instances --instance-ids "$INSTANCE_ID" >/dev/null
  aws ec2 wait instance-stopped --instance-ids "$INSTANCE_ID"
  log "builder STOPPED (idle cost = EBS only)."
}

status() {
  cat >&2 <<EOF
==> builder $INSTANCE_ID
    region:  $AWS_REGION
    state:   $(builder_state)
    ip:      $(builder_ip)
    cost:    ~\$0.34/hr while running (c5.2xlarge), EBS-only (~\$6.4/mo, 80 GB gp3) when stopped
EOF
}

# ---- toolchain (idempotent; persists on the EBS) ----------------------------
setup() {
  log "installing toolchain on the builder (idempotent) ..."
  ssh_builder MATHLIB_URL="$MATHLIB_URL" MATHLIB_REV="$MATHLIB_REV" \
              RUST_CHANNEL="$RUST_CHANNEL" R_MATHLIB="$R_MATHLIB" bash -s <<'REMOTE'
set -euo pipefail

# system build deps
if ! dpkg -s build-essential >/dev/null 2>&1; then
  sudo apt-get update
  sudo DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    build-essential clang lld llvm cmake pkg-config libssl-dev libgmp-dev \
    git curl ca-certificates unzip
fi

# docker (for the node image build/save)
if ! command -v docker >/dev/null 2>&1; then
  curl -fsSL https://get.docker.com | sudo sh
  sudo usermod -aG docker "$USER"
fi

# elan (Lean toolchain manager) — installs the leanprover channel lazily on first lake use
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
grep -q '.elan/bin' "$HOME/.profile" 2>/dev/null || echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.profile"

# rustup + the pinned nightly
if [ ! -x "$HOME/.cargo/bin/rustup" ]; then
  curl --proto '=https' --tlsv1.2 -fsSL https://sh.rustup.rs \
    | sh -s -- -y --default-toolchain "$RUST_CHANNEL" --profile minimal
fi
"$HOME/.cargo/bin/rustup" toolchain install "$RUST_CHANNEL" --profile minimal 2>/dev/null || true
"$HOME/.cargo/bin/rustup" default "$RUST_CHANNEL"
grep -q '.cargo/env' "$HOME/.profile" 2>/dev/null || echo 'source "$HOME/.cargo/env"' >> "$HOME/.profile"

# mathlib at the pinned rev (the lakefile path-require resolves here:
# breadstuffs/../../../src/mathlib4 == ~/src/mathlib4)
mkdir -p "$(dirname "$R_MATHLIB")"
if [ ! -d "$R_MATHLIB/.git" ]; then
  git clone --filter=blob:none "$MATHLIB_URL" "$R_MATHLIB"
fi
git -C "$R_MATHLIB" fetch --depth 1 origin "$MATHLIB_REV" || git -C "$R_MATHLIB" fetch origin
git -C "$R_MATHLIB" checkout -q "$MATHLIB_REV"

echo "toolchain setup OK"
REMOTE
  log "toolchain ready (elan + rust $RUST_CHANNEL + docker + mathlib @ $MATHLIB_REV)"
}

# ---- ship the source (git archive HEAD; no 200G working tree) ---------------
sync() {
  [ -d "$BREADSTUFFS/.git" ] || die "no breadstuffs checkout at $BREADSTUFFS"
  log "shipping breadstuffs source (git archive HEAD) to the builder ..."
  local ip; ip="$(builder_ip)"
  ssh_builder "mkdir -p '$R_SRC'"
  git -C "$BREADSTUFFS" archive --format=tar HEAD \
    | gzip \
    | ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new "$BUILDER_USER@$ip" \
        "tar xzf - -C '$R_SRC'"
  log "source synced to $R_SRC"
}

# ---- the build on the builder ----------------------------------------------
compile() {
  log "building dregg-node:staging on the builder (lake + cargo + docker) ..."
  ssh_builder R_SRC="$R_SRC" R_BUILD="$R_BUILD" R_OBJCACHE="$R_OBJCACHE" \
              IMAGE_TAG="$IMAGE_TAG" IMAGE_TARBALL="$IMAGE_TARBALL" \
              RUST_CHANNEL="$RUST_CHANNEL" bash -s <<'REMOTE'
set -euo pipefail
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
source "$HOME/.cargo/env" 2>/dev/null || true
NCPU="$(nproc)"
mkdir -p "$R_BUILD" "$R_OBJCACHE"

cd "$R_SRC"

# 1) Build the Lean closure and (re)seed the LINUX libdregg_lean.a.
#    The git-tracked seed in the tree is the arm64-mac archive; on linux/amd64 we
#    must produce native x86_64 objects. We reuse the project's own seed script,
#    pointing its object cache at the persistent EBS dir so re-pulses are
#    incremental (lake is incremental on oleans; leanc -c is cached per .o).
# Pull mathlib's prebuilt oleans so we don't re-elaborate all of mathlib (hours).
# Only Dregg2's own modules then need elaboration; the :c codegen + leanc -c of
# the whole closure (the unavoidable heavy part) follows in the seed script.
echo "==> lake exe cache get (download prebuilt mathlib oleans)"
( cd metatheory && lake exe cache get || true )

echo "==> lake build Dregg2.Exec.FFI (full transitive :c closure) — heavy, parallel x$NCPU"
( cd metatheory && lake build Dregg2.Exec.FFI )

echo "==> compiling the :c closure -> native x86_64 objects -> libdregg_lean.a"
TMPDIR="$R_OBJCACHE" ./dregg-lean-ffi/scripts/seed-dregg2-closure.sh
file dregg-lean-ffi/libdregg_lean.a | sed 's/^/    /'

# 2) Build the node binary natively (links the freshly-seeded linux archive).
echo "==> cargo build --release -p dregg-node"
cargo +"$RUST_CHANNEL" build --release -p dregg-node
test -x target/release/dregg-node || { echo "FATAL: dregg-node binary not produced"; exit 1; }
file target/release/dregg-node | sed 's/^/    /'

# 3) Wrap the binary in the runtime image (docker/Dockerfile.node).
echo "==> docker build $IMAGE_TAG"
CTX="$R_BUILD/imgctx"
rm -rf "$CTX"; mkdir -p "$CTX"
cp target/release/dregg-node "$CTX/dregg-node"
cp docker/Dockerfile.node "$CTX/Dockerfile.node"
sudo docker build -f "$CTX/Dockerfile.node" -t "$IMAGE_TAG" "$CTX"
sudo docker images "$IMAGE_TAG"

# 4) Save the image to a gzipped tarball for shipping to staging.
echo "==> docker save $IMAGE_TAG -> $R_BUILD/$IMAGE_TARBALL"
sudo docker save "$IMAGE_TAG" | gzip > "$R_BUILD/$IMAGE_TARBALL"
ls -la "$R_BUILD/$IMAGE_TARBALL"
echo "BUILD OK"
REMOTE
  log "node image built + saved on the builder"
}

pull() {
  mkdir -p "$ARTIFACTS"
  local ip; ip="$(builder_ip)"
  log "pulling image tarball to $ARTIFACTS/$IMAGE_TARBALL"
  scp -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new \
    "$BUILDER_USER@$ip:$R_BUILD/$IMAGE_TARBALL" "$ARTIFACTS/$IMAGE_TARBALL"
  ls -la "$ARTIFACTS/$IMAGE_TARBALL"
}

ship() {
  [ -n "$STAGING_HOST" ] || die "set STAGING_HOST=<staging-box-ip> to ship the image"
  local ip; ip="$(builder_ip)"
  log "shipping image builder -> staging ($STAGING_HOST) and docker load"
  # stream builder -> staging directly (no local round-trip needed)
  ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new "$BUILDER_USER@$ip" \
    "cat '$R_BUILD/$IMAGE_TARBALL'" \
    | ssh -i "$SSH_KEY" -o StrictHostKeyChecking=accept-new "$STAGING_USER@$STAGING_HOST" \
        "gunzip -c | sudo docker load"
  log "image loaded on staging as $IMAGE_TAG"
}

build() {
  start
  setup
  sync
  compile
  pull
  if [ -n "$STAGING_HOST" ]; then ship || log "ship skipped/failed (build artifact is saved on the builder + pulled locally)"; fi
  stop
  log "PULSE COMPLETE — image $IMAGE_TAG baked; builder STOPPED."
}

case "${1:-status}" in
  start)   start ;;
  stop)    stop ;;
  status)  status ;;
  setup)   setup ;;
  sync)    sync ;;
  compile) compile ;;
  pull)    pull ;;
  ship)    ship ;;
  build|all) build ;;
  *) echo "usage: $0 {build|start|setup|sync|compile|pull|ship|stop|status}" >&2; exit 2 ;;
esac

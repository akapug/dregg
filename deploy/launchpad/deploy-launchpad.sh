#!/bin/bash
# deploy-launchpad.sh — one-command deploy of the dregg LAUNCHPAD web layer onto hbox,
# + a keyless testnet-deploy DRY-RUN for the launchpad contract.
#
# MIRRORS deploy/games/deploy-hbox.sh (the games pattern) — SAME shape:
# BUILD -> SNAPSHOT -> INSTALL (user systemd unit) -> RELOAD -> HEALTH -> auto-revert.
# The launchpad web layer is `launchpad-web/server.mjs` (a Node app, so BUILD = `npm ci`,
# NOT cargo). It serves the create / bid / token-page / replayable-discovery product over
# the fair-launch engine and READS the on-chain DreggLaunchpad; the browser drives the
# real contract with the USER's own wallet. rung-1 (attestor=0, permissionless finalize)
# needs ZERO dregg — the launchpad-web + the on-chain contracts are the whole thing.
#
# ⚠⚠ USE `--funnel`. THE DEFAULT (GATEWAY) PATH TARGETS A TOPOLOGY THAT DOES NOT EXIST.
# Verified 2026-07-15 (deploy/README.md): the AWS edge (100.64.0.x) and hbox-dregg
# (100.95.240.73 on skunk-emperor) are on DIFFERENT TAILNETS that cannot reach each
# other, and there is NO Caddy on the edge — so the gateway path below has nothing to
# install into. What ACTUALLY runs is `--funnel` -> dregg-launchpad-web-funnel.service
# (loopback:8785) + `tailscale funnel --https=8443` -> https://hbox-dregg.<tailnet>.ts.net:8443.
# See deploy/launchpad/RUNBOOK.md and deploy/games/RUNBOOK-FUNNEL.md.
#
# STALE (kept for the hbox-side shape, which is sound):
# Real topology (docs/deos/DEVNET-DEPLOYMENT-REALITY.md — the SAME channel games uses):
# DNS -> AWS GATEWAY (public, its OWN Caddy for *.dregg.fg-goose.online) -> TAILSCALE ->
# hbox (tailnet node hbox-dregg, 100.95.240.73). Caddy lives on the GATEWAY, not hbox.
# THIS SCRIPT RUNS ON hbox and handles ONLY the hbox side: npm ci + the one user unit.
# The gateway Caddy block is a SEPARATE step (`./deploy-launchpad.sh gateway`, run ON
# THE GATEWAY) that ADDS a NEW launchpad site-block NEXT TO the games block — it does
# not edit the games block.
#
# ⚠ WHAT THIS SCRIPT DOES NOT DO (ember-gated flips — printed as MANUAL banners, never
# executed):
#   - (0) add the AWS gateway to the TAILNET (the SHARED prerequisite with games) — the
#     private channel to hbox-dregg; without it the gateway cannot reach :8785;
#   - place ~/.config/dregg/launchpad.env (LAUNCHPAD_ADDRESS etc.), chmod 600;
#   - the CONTRACT testnet broadcast (funded key + --broadcast) — see `contract-dryrun`
#     which SIMULATES it keylessly and prints the exact ember-runs-this command;
#   - point DNS launchpad.dregg.fg-goose.online -> the gateway;
#   - add the launchpad site block to the gateway Caddy + reload it (`gateway` step);
#   - the go-live decision.
#
# Usage (on hbox unless noted):
#   ./deploy-launchpad.sh                  # GATEWAY variant (stale topology): npm ci -> install -> health
#   ./deploy-launchpad.sh --funnel         # TAILSCALE-FUNNEL variant: NO gateway leg. npm ci + install
#                                          #   the web unit bound 127.0.0.1:8785 (DREGG_NODE=:8420),
#                                          #   health-check localhost:8785, then PRINT the ember-gated
#                                          #   `tailscale funnel --https=8443 8785` public-exposure flip
#                                          #   (never run). See deploy/launchpad/RUNBOOK.md.
#   ./deploy-launchpad.sh --dry-run        # print every step; NO side effects (safe anywhere)
#   ./deploy-launchpad.sh contract-dryrun  # keyless forge SIMULATION of the testnet deploy
#   ./deploy-launchpad.sh gateway          # ON THE GATEWAY (stale): validate launchpad Caddy block + banner
#   ./deploy-launchpad.sh health           # just run the health gate
#   ./deploy-launchpad.sh releases         # list rollback snapshots
#   ./deploy-launchpad.sh rollback [S]     # restore the unit from snapshot S + restart
#
# Knobs (env):
#   LP_REPO_DIR      repo checkout on hbox        (default $HOME/dev/breadstuffs)
#   LP_ENV           the stack env file           (gateway: launchpad.env; --funnel: launchpad-funnel.env)
#   STATE_DIR        scratch state + snapshots     (default $HOME/.local/state/dregg-launchpad)
#   USER_UNIT_DIR    user systemd unit dir         (default $HOME/.config/systemd/user)
#   HEALTH_URL       liveness probe                (gateway: http://100.95.240.73:8785/api/config;
#                    --funnel: http://127.0.0.1:8785/api/config — Funnel serves the loopback port)
#   HEALTH_TIMEOUT   gate timeout, seconds         (default 120)
#   KEEP             snapshots retained            (default 5)
#   AUTO_REVERT      0 disables the auto-revert    (default 1)
#   CADDY_FILE       GATEWAY Caddy config (gateway step only)  (default /etc/caddy/Caddyfile)
#   LP_BLOCK         launchpad site block to validate on the gateway (default caddy/Caddyfile.launchpad)
#   SKIP_CADDY       DEFAULT 1: no Caddy on hbox (Caddy lives on the gateway).
#   DEPLOY_RPC       contract-dryrun: foundry rpc alias/url for a READ-ONLY sim
#                    (unset -> pure LOCAL simulation, no network; e.g. base_sepolia)
set -euo pipefail

# ── flags + config ───────────────────────────────────────────────────────────
DRY_RUN=0
FUNNEL=0
ARGS=()
for a in "$@"; do
  case "$a" in
    --dry-run) DRY_RUN=1 ;;
    --funnel)  FUNNEL=1 ;;
    *) ARGS+=("$a") ;;
  esac
done
set -- "${ARGS[@]:-up}"

LP_REPO_DIR="${LP_REPO_DIR:-$HOME/dev/breadstuffs}"
STATE_DIR="${STATE_DIR:-$HOME/.local/state/dregg-launchpad}"
USER_UNIT_DIR="${USER_UNIT_DIR:-$HOME/.config/systemd/user}"
HEALTH_TIMEOUT="${HEALTH_TIMEOUT:-120}"
KEEP="${KEEP:-5}"
AUTO_REVERT="${AUTO_REVERT:-1}"
CADDY_FILE="${CADDY_FILE:-/etc/caddy/Caddyfile}"
LP_BLOCK="${LP_BLOCK:-}"
SKIP_CADDY="${SKIP_CADDY:-1}"
DEPLOY_RPC="${DEPLOY_RPC:-}"

# ── topology fork: FUNNEL vs the default GATEWAY topology ─────────────────────
# FUNNEL=1 (--funnel): Tailscale-Funnel variant — the pattern that ACTUALLY RUNS. The
#   web server binds LOOPBACK (127.0.0.1:8785 — Funnel proxies the local port), reads
#   launches node-driven off the durable hbox :8420 node, and there is NO gateway/Caddy
#   leg at all. The public-exposure flip is `tailscale funnel --https=8443 8785`, printed
#   as an ember-gated banner (never run). See deploy/launchpad/RUNBOOK.md.
# FUNNEL=0 (default): the STALE gateway topology (the tailnets cannot reach each other;
#   deploy/README.md). The web server binds the tailnet iface (100.95.240.73:8785) so the
#   AWS gateway's Caddy could reverse-proxy over Tailscale — but that gateway is not on
#   hbox's tailnet, so this path cannot go public. Kept for the sound hbox-side shape.
if [[ "$FUNNEL" == "1" ]]; then
  UNIT="dregg-launchpad-web-funnel.service"
  LP_ENV="${LP_ENV:-$HOME/.config/dregg/launchpad-funnel.env}"
  # Funnel serves a LOCAL port — the on-hbox health probe hits loopback.
  HEALTH_URL="${HEALTH_URL:-http://127.0.0.1:8785/api/config}"
else
  UNIT="dregg-launchpad-web.service"
  LP_ENV="${LP_ENV:-$HOME/.config/dregg/launchpad.env}"
  # The web server binds the Tailscale iface (hbox-dregg 100.95.240.73:8785), NOT
  # localhost — so the on-hbox health probe must hit the tailnet IP, not 127.0.0.1.
  HEALTH_URL="${HEALTH_URL:-http://100.95.240.73:8785/api/config}"
fi

RELEASES_DIR="$STATE_DIR/releases"
SRC_DIR="$LP_REPO_DIR/deploy/launchpad"
WEB_DIR="$LP_REPO_DIR/launchpad-web"
CHAIN_DIR="$LP_REPO_DIR/chain"
# The web unit's basename minus .service — for `journalctl --user -u <unit>`.
UNIT_NAME="${UNIT%.service}"

log()  { echo "[deploy-launchpad] $*"; }
warn() { echo "[deploy-launchpad] ⚠ $*" >&2; }
die()  { echo "[deploy-launchpad] FATAL: $*" >&2; exit 1; }

# run(): the side-effect wrapper. In --dry-run it PRINTS and returns 0; otherwise runs.
run() {
  if [[ "$DRY_RUN" == "1" ]]; then
    echo "    [dry-run] $*"
    return 0
  fi
  "$@"
}

# gated(): a step the script REFUSES to automate — prints the manual banner, does nothing.
gated() { echo "    ── EMBER-GATED (manual) ── $*"; }

gated_banner() {
  cat <<'BANNER'
[deploy-launchpad] ═══════════════════════════════════════════════════════════════
[deploy-launchpad]  EMBER-GATED FLIPS this script does NOT perform (do them first /
[deploy-launchpad]  around the run — see deploy/launchpad/RUNBOOK.md):
[deploy-launchpad]    (0) add the AWS GATEWAY to the TAILNET (reach hbox-dregg :8785)
[deploy-launchpad]        — the SHARED prerequisite with deploy/games (one join covers both)
[deploy-launchpad]    (b) place ~/.config/dregg/launchpad.env (LAUNCHPAD_ADDRESS) + chmod 600
[deploy-launchpad]    (c) the CONTRACT testnet BROADCAST (funded key + --broadcast) —
[deploy-launchpad]        `./deploy-launchpad.sh contract-dryrun` simulates it keylessly first
[deploy-launchpad]    (a) DNS: launchpad.dregg.fg-goose.online -> the gateway
[deploy-launchpad]    (caddy) ON THE GATEWAY: ./deploy-launchpad.sh gateway (add block + reload)
[deploy-launchpad]    (go-live) the go-live decision
[deploy-launchpad] ═══════════════════════════════════════════════════════════════
BANNER
}

# ── the FUNNEL-variant ember-gated banner (--funnel) ─────────────────────────
funnel_gated_banner() {
  cat <<'BANNER'
[deploy-launchpad] ═══════════════════════════════════════════════════════════════
[deploy-launchpad]  FUNNEL VARIANT (--funnel): NO gateway, NO Caddy, NO DNS.
[deploy-launchpad]  EMBER-GATED steps this script does NOT perform (see
[deploy-launchpad]  deploy/launchpad/RUNBOOK.md):
[deploy-launchpad]    (a) the durable hbox node :8420 must be UP (deploy/node/RUNBOOK.md)
[deploy-launchpad]        — node-driven launches read from it; OR run the EVM contract
[deploy-launchpad]        lane (step c) with DREGG_NODE= empty + LAUNCHPAD_ADDRESS set
[deploy-launchpad]    (b) place ~/.config/dregg/launchpad-funnel.env (loopback bind) + chmod 600
[deploy-launchpad]    (d) PUBLIC-EXPOSURE FLIP: `tailscale funnel --https=8443 8785`  ← the
[deploy-launchpad]        single decision that makes the demo public at
[deploy-launchpad]        https://hbox-dregg.<tailnet>.ts.net:8443 (printed after health passes)
[deploy-launchpad] ═══════════════════════════════════════════════════════════════
BANNER
}

# print_funnel_flip(): after a passing health gate, print the exact (ember-gated)
# `tailscale funnel` command that flips the demo public. NEVER executed here. Games
# holds public :443 (`tailscale funnel 8790`); the launchpad takes the SECOND funnel
# port :8443 (Funnel supports 443/8443/10000). See RUNBOOK.md "Topology" option (A).
print_funnel_flip() {
  echo "[deploy-launchpad]"
  echo "[deploy-launchpad]  ── EMBER-GATED PUBLIC-EXPOSURE FLIP (run by hand when ready) ──"
  echo "[deploy-launchpad]    tailscale funnel --bg --https=8443 8785   # serve 127.0.0.1:8785 publicly (8443->8785)"
  echo "[deploy-launchpad]    tailscale funnel status                   # confirm https://hbox-dregg.<tailnet>.ts.net:8443"
  echo "[deploy-launchpad]  Take it down:"
  echo "[deploy-launchpad]    tailscale funnel --https=8443 off"
  echo "[deploy-launchpad]  (deploy/launchpad/RUNBOOK.md steps d–f)"
}

# ── preflight ────────────────────────────────────────────────────────────────
preflight() {
  log "preflight"
  [[ -d "$LP_REPO_DIR" ]] || die "repo not found: $LP_REPO_DIR (set LP_REPO_DIR)"
  [[ -d "$SRC_DIR" ]] || die "deploy/launchpad not found under $LP_REPO_DIR — right checkout/branch?"
  [[ -d "$WEB_DIR" ]] || die "launchpad-web not found under $LP_REPO_DIR"
  if [[ ! -f "$LP_ENV" ]]; then
    warn "env file $LP_ENV MISSING — ember must place it (bind + source)."
    if [[ "$FUNNEL" == "1" ]]; then
      gated "place $LP_ENV from deploy/launchpad/.env.example with LAUNCHPAD_HOST=127.0.0.1"
      gated "  (LOOPBACK — Funnel serves the local port) + DREGG_NODE=http://127.0.0.1:8420"
      gated "  (node-driven) or DREGG_NODE= empty + LAUNCHPAD_ADDRESS (EVM lane); then chmod 600"
    else
      gated "place $LP_ENV from deploy/launchpad/.env.example, then chmod 600"
    fi
    [[ "$DRY_RUN" == "1" ]] || die "cannot start the unit without $LP_ENV; place it and re-run"
  fi
  run mkdir -p "$STATE_DIR" "$USER_UNIT_DIR" "$RELEASES_DIR"
}

# ── build (npm ci — the launchpad web layer is a Node app, NOT cargo) ─────────
build() {
  log "build (npm ci): launchpad-web (installs ethers for the vendored UMD + indexer)"
  # npm ci is reproducible from package-lock.json; falls back to npm install if no lock.
  if [[ -f "$WEB_DIR/package-lock.json" ]]; then
    run bash -c "cd '$WEB_DIR' && npm ci --no-audit --no-fund"
  else
    run bash -c "cd '$WEB_DIR' && npm install --no-audit --no-fund"
  fi
}

# ── snapshots (rollback point) ───────────────────────────────────────────────
# A Node app has no binary to swap; the deployable artifact is the launchpad-web source
# tree (the shared repo working tree) + node_modules. The HONEST rollback the script
# owns is the systemd UNIT FILE + a git-rev provenance marker: a code rollback is a git
# operation on the SHARED tree, which is ember's call (never swarm-safe to automate). On
# a failed health gate we restore the PRIOR unit + restart (or stop if none) so we never
# leave a broken thing running.
record_release() {
  local stamp dir
  stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  dir="$RELEASES_DIR/$stamp"
  run mkdir -p "$dir"
  if [[ "$DRY_RUN" != "1" ]]; then
    git -C "$LP_REPO_DIR" rev-parse HEAD > "$dir/GIT_REV" 2>/dev/null || echo "unknown" > "$dir/GIT_REV"
    # snapshot the CURRENTLY-INSTALLED unit (the pre-deploy one), if any, for revert.
    [[ -f "$USER_UNIT_DIR/$UNIT" ]] && cp -p "$USER_UNIT_DIR/$UNIT" "$dir/$UNIT" || true
    ls -1 "$RELEASES_DIR" 2>/dev/null | sort | head -n -"$KEEP" | while read -r old; do
      [[ -n "$old" ]] && rm -rf "${RELEASES_DIR:?}/$old"
    done
  fi
  log "snapshot recorded: $stamp"
  echo "$stamp"
}

list_releases() {
  [[ -d "$RELEASES_DIR" ]] || { log "no snapshots yet"; return 0; }
  local s
  for s in $(ls -1 "$RELEASES_DIR" | sort); do
    echo "  $s  rev=$(cut -c1-12 "$RELEASES_DIR/$s/GIT_REV" 2>/dev/null || echo '?')"
  done
}

restore_release() {
  local stamp="${1:-}" dir
  [[ -n "$stamp" ]] || stamp="$(ls -1 "$RELEASES_DIR" 2>/dev/null | sort | tail -1)"
  [[ -n "$stamp" ]] || die "no snapshot to roll back to"
  dir="$RELEASES_DIR/$stamp"
  [[ -d "$dir" || "$DRY_RUN" == "1" ]] || die "no such snapshot: $stamp"
  log "restoring the unit from snapshot $stamp (+restart)"
  if [[ -f "$dir/$UNIT" || "$DRY_RUN" == "1" ]]; then
    run cp -p "$dir/$UNIT" "$USER_UNIT_DIR/$UNIT"
    run systemctl --user daemon-reload
    run systemctl --user restart "$UNIT"
  else
    warn "snapshot $stamp had no prior unit (first deploy) — STOPPING the unit so nothing broken runs"
    run systemctl --user stop "$UNIT"
  fi
  log "NOTE: the launchpad-web SOURCE stays at the repo's current rev; only the UNIT reverted."
}

# ── install the user unit ─────────────────────────────────────────────────────
install_unit() {
  log "install user systemd unit: $UNIT"
  run cp "$SRC_DIR/$UNIT" "$USER_UNIT_DIR/$UNIT"
  run systemctl --user daemon-reload
  # survive logout so the unit keeps running (deploy/hbox/RUNBOOK.md).
  run loginctl enable-linger "$USER"
  run systemctl --user enable "$UNIT"
}

install_caddy() {
  # Funnel variant: there is NO Caddy leg at all — Tailscale Funnel is the public edge
  # (TLS + hostname). Skip unconditionally.
  if [[ "$FUNNEL" == "1" ]]; then
    log "FUNNEL variant — no Caddy / no gateway leg; Tailscale Funnel is the edge."
    log '  public-exposure flip is `tailscale funnel --https=8443 8785` (ember-gated; printed after health).'
    return 0
  fi
  if [[ "$SKIP_CADDY" == "1" ]]; then
    log "SKIP_CADDY=1 (default) — no Caddy on hbox; the gateway holds Caddy."
    log "  add the launchpad block ON THE GATEWAY: ./deploy-launchpad.sh gateway (RUNBOOK step d)"
    return 0
  fi
  log "install Caddyfile block -> $CADDY_FILE (LEGACY on-hbox Caddy; NOT the real topology)"
  run bash -c "caddy validate --adapter caddyfile --config '$SRC_DIR/caddy/Caddyfile.launchpad'"
  warn "SKIP_CADDY=0 puts Caddy on hbox — NOT the gateway<->Tailscale<->hbox topology."
}

# gateway_install(): the SEPARATE gateway step. Run ON THE AWS GATEWAY (not hbox), AFTER
# the gateway is on the tailnet (step 0). Validates the launchpad site block; the append+
# reload are ember-gated (they touch the gateway's system Caddy, NEXT TO the games block).
gateway_install() {
  local block dst
  block="${LP_BLOCK:-$SRC_DIR/caddy/Caddyfile.launchpad}"
  dst="$CADDY_FILE"
  log "GATEWAY STEP — add the launchpad site block to the gateway Caddy ($dst) + reload"
  [[ -f "$block" ]] || die "launchpad block not found: $block (set LP_BLOCK, or run from a repo checkout)"
  run bash -c "caddy validate --adapter caddyfile --config '$block'"
  gated "the gateway must be ON THE TAILNET (step 0) so it can reach 100.95.240.73:8785"
  gated "APPEND the block to $dst (NEXT TO the games + devnet blocks; do NOT edit theirs):"
  gated "    sudo sh -c 'cat \"$block\" >> \"$dst\"'   # or paste it in by hand"
  gated "then validate the WHOLE merged config + reload:"
  gated "    sudo caddy validate --adapter caddyfile --config \"$dst\""
  gated "    sudo systemctl reload caddy"
  gated "DNS launchpad.dregg.fg-goose.online -> the gateway must resolve for Let's Encrypt"
  log "block validated; the append+reload are ember-gated manual steps above."
}

# contract_dryrun(): keyless forge SIMULATION of the launchpad testnet deploy. NO
# --broadcast, NO key required (the script uses the well-known anvil dev key only to make
# a keyless sim possible; see DeployLaunchpad.s.sol). Prints the exact ember-runs-this
# broadcast command. With DEPLOY_RPC set (e.g. base_sepolia) it simulates READ-ONLY
# against the real testnet RPC; unset -> a pure local simulation (no network).
contract_dryrun() {
  log "CONTRACT DEPLOY DRY-RUN (keyless SIMULATION — NO --broadcast, no funded key)"
  [[ -d "$CHAIN_DIR" ]] || die "chain/ not found under $LP_REPO_DIR"
  local rpc_args=""
  if [[ -n "$DEPLOY_RPC" ]]; then
    rpc_args="--rpc-url $DEPLOY_RPC"
    log "  READ-ONLY simulation against RPC alias/url: $DEPLOY_RPC (no tx sent)"
  else
    log "  pure LOCAL simulation (no network). Set DEPLOY_RPC=base_sepolia for a testnet-RPC sim."
  fi
  run bash -c "cd '$CHAIN_DIR' && forge script script/DeployLaunchpad.s.sol:DeployLaunchpad $rpc_args -vvv"
  echo ""
  gated "THE EMBER-RUNS-THIS BROADCAST (a real tx on the testnet — funded key required):"
  gated "  export DEPLOYER_PRIVATE_KEY=0x<funded testnet key>          # EMBER input"
  gated "  # Base-Sepolia:"
  gated "  export BASE_SEPOLIA_RPC_URL=https://sepolia.base.org"
  gated "  (cd $CHAIN_DIR && forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \\"
  gated "       --rpc-url base_sepolia --broadcast --verify -vvv)"
  gated "  # Robinhood Chain (46630) instead:"
  gated "  export ROBINHOOD_TESTNET_RPC_URL=https://rpc.testnet.chain.robinhood.com"
  gated "  (cd $CHAIN_DIR && forge script script/DeployLaunchpad.s.sol:DeployLaunchpad \\"
  gated "       --rpc-url robinhood_testnet --broadcast -vvv)"
  gated "then put the printed 'DreggLaunchpad :' address into ~/.config/dregg/launchpad.env"
  gated "as LAUNCHPAD_ADDRESS and (re)run ./deploy-launchpad.sh on hbox."
  log "rung-1 (attestor=0, permissionless finalize) needs ZERO dregg — the deployed"
  log "contract + launchpad-web are the whole thing (PRIVATE-DREGG-PUBLIC-LAUNCHPAD-ARCHITECTURE §2.3)."
}

# ── health gate (mirrors deploy/games) ───────────────────────────────────────
health_gate() {
  if [[ "$DRY_RUN" == "1" ]]; then
    echo "    [dry-run] curl -fsS -m 5 $HEALTH_URL  (poll up to ${HEALTH_TIMEOUT}s; expect 200 JSON config)"
    return 0
  fi
  local deadline=$((SECONDS + HEALTH_TIMEOUT))
  log "health gate: $HEALTH_URL (up to ${HEALTH_TIMEOUT}s)"
  while ((SECONDS < deadline)); do
    if curl -fsS -m 5 "$HEALTH_URL" >/dev/null 2>&1; then
      log "health gate PASSED"
      return 0
    fi
    log "  waiting for $HEALTH_URL ..."
    sleep 5
  done
  log "health gate FAILED after ${HEALTH_TIMEOUT}s; recent log:"
  journalctl --user -u "$UNIT_NAME" --no-pager -n 30 2>/dev/null || true
  return 1
}

# ── the gated deploy ─────────────────────────────────────────────────────────
deploy_up() {
  if [[ "$FUNNEL" == "1" ]]; then
    funnel_gated_banner
  else
    gated_banner
  fi
  preflight
  local snap
  snap="$(record_release | tail -1)"
  build
  install_unit
  install_caddy
  run systemctl --user enable --now "$UNIT"
  if health_gate; then
    log "launchpad web HEALTHY on the new release ($snap was the rollback point)"
    if [[ "$FUNNEL" == "1" ]]; then
      log "the web unit is up on 127.0.0.1:8785 (loopback) — NOT yet public."
      print_funnel_flip
      log "smoke test after the flip (deploy/launchpad/RUNBOOK.md step e): open the public"
      log "URL, connect a wallet, run a launch end-to-end (node-driven off :8420, or the EVM lane)."
    else
      log "smoke test next (deploy/launchpad/RUNBOOK.md step e): open the URL, connect a"
      log "wallet, run a rung-1 OPEN launch end-to-end on the testnet."
    fi
    return 0
  fi
  if [[ "$AUTO_REVERT" == "1" ]]; then
    warn "health gate failed — AUTO-REVERTING (restore prior unit / stop) from $snap"
    restore_release "$snap"
    die "new release failed the health gate; reverted (see snapshot $snap)"
  fi
  die "new release failed the health gate (AUTO_REVERT=0; left as-is)"
}

case "${1:-up}" in
  up)               deploy_up ;;
  contract-dryrun)  contract_dryrun ;;
  gateway)          gateway_install ;;
  health)           health_gate ;;
  releases)         list_releases ;;
  rollback)         restore_release "${2:-}"; health_gate ;;
  *)                die "unknown subcommand: $1 (up | contract-dryrun | gateway | health | releases | rollback [stamp] | --dry-run)" ;;
esac

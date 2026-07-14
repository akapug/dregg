#!/bin/bash
# deploy-hbox.sh — one-command deploy of the dregg GAMES stack onto hbox.
#
# The automated flow: BUILD (dreggnet-web-server + dregg-discord-bot) -> SNAPSHOT
# (rollback point) -> INSTALL (user systemd units + the Caddyfile) -> RELOAD ->
# HEALTH-CHECK (/health). A failed health gate AUTO-REVERTS to the snapshot. This
# turns the go-live into a small, safe flip, NOT a new build.
#
# Grounded in the existing deploy infra (deploy/aws/update.sh + update-gated.sh):
# the build->install->reload->health->rollback shape is theirs, re-homed onto
# hbox USER units (deploy/hbox/RUNBOOK.md discipline) and the standalone games
# web server (docs/DEPLOY-PLAN.md Phase 0).
#
# ⚠ WHAT THIS SCRIPT DOES NOT DO (ember-gated flips — printed as MANUAL banners,
# never executed):
#   - place the Discord token / secrets (~/.config/dregg/games.env, chmod 600);
#   - STOP THE OLD BOT FIRST (graviton's dregg-discord-bot, or a prior hbox run) —
#     two bots on one token double-fire every command;
#   - point DNS demo.dregg.net -> hbox;
#   - open hbox :80/:443 (ufw + port-forward) for Let's Encrypt / Caddy;
#   - flip the demo public (the go-live decision).
#
# Usage:
#   ./deploy-hbox.sh                 # build -> install -> reload -> health (+ auto-revert)
#   ./deploy-hbox.sh --dry-run       # print every step; NO side effects (safe anywhere)
#   ./deploy-hbox.sh health          # just run the health gate
#   ./deploy-hbox.sh releases        # list rollback snapshots
#   ./deploy-hbox.sh rollback [S]    # revert binaries to snapshot S (default newest) + restart
#
# Knobs (env):
#   GAMES_REPO_DIR   repo checkout on hbox        (default $HOME/dev/breadstuffs)
#   GAMES_ENV        the stack env file           (default $HOME/.config/dregg/games.env)
#   STATE_DIR        durable db + snapshots        (default $HOME/.local/state/dregg-games)
#   USER_UNIT_DIR    user systemd unit dir         (default $HOME/.config/systemd/user)
#   HEALTH_URL       web server liveness probe     (default http://127.0.0.1:8790/health)
#   HEALTH_TIMEOUT   gate timeout, seconds         (default 120)
#   KEEP             snapshots retained            (default 5)
#   AUTO_REVERT      0 disables the auto-revert    (default 1)
#   CADDY_FILE       system Caddy config target    (default /etc/caddy/Caddyfile)
#   SKIP_CADDY       1 skips the Caddy leg (web+bot only; Caddy on the gateway)
#   SKIP_BOT         1 skips the bot leg (web demo only)
set -euo pipefail

# ── flags + config ───────────────────────────────────────────────────────────
DRY_RUN=0
ARGS=()
for a in "$@"; do
  case "$a" in
    --dry-run) DRY_RUN=1 ;;
    *) ARGS+=("$a") ;;
  esac
done
set -- "${ARGS[@]:-up}"

GAMES_REPO_DIR="${GAMES_REPO_DIR:-$HOME/dev/breadstuffs}"
GAMES_ENV="${GAMES_ENV:-$HOME/.config/dregg/games.env}"
STATE_DIR="${STATE_DIR:-$HOME/.local/state/dregg-games}"
USER_UNIT_DIR="${USER_UNIT_DIR:-$HOME/.config/systemd/user}"
HEALTH_URL="${HEALTH_URL:-http://127.0.0.1:8790/health}"
HEALTH_TIMEOUT="${HEALTH_TIMEOUT:-120}"
KEEP="${KEEP:-5}"
AUTO_REVERT="${AUTO_REVERT:-1}"
CADDY_FILE="${CADDY_FILE:-/etc/caddy/Caddyfile}"
SKIP_CADDY="${SKIP_CADDY:-0}"
SKIP_BOT="${SKIP_BOT:-0}"

RELEASES_DIR="$STATE_DIR/releases"
SRC_DIR="$GAMES_REPO_DIR/deploy/games"
BINARIES=(dreggnet-web-server)
UNITS=(dregg-web-games.service)
if [[ "$SKIP_BOT" != "1" ]]; then
  BINARIES+=(dregg-discord-bot)
  UNITS+=(dregg-games-bot.service)
fi

# Per-binary source path. dreggnet-web is a ROOT-workspace member (built into the
# root target/); dregg-discord-bot is a SEPARATE workspace (excluded from root —
# sqlx/libsqlite3-sys links-conflict; discord-bot/Cargo.toml), so it builds into
# ITS OWN target/. The two live in different dirs — never assume one BIN_DIR.
bin_src() {
  case "$1" in
    dreggnet-web-server) echo "$GAMES_REPO_DIR/target/release/dreggnet-web-server" ;;
    dregg-discord-bot)   echo "$GAMES_REPO_DIR/discord-bot/target/release/dregg-discord-bot" ;;
    *) die "unknown binary: $1" ;;
  esac
}

log()  { echo "[deploy-games] $*"; }
warn() { echo "[deploy-games] ⚠ $*" >&2; }
die()  { echo "[deploy-games] FATAL: $*" >&2; exit 1; }

# run(): the side-effect wrapper. In --dry-run it PRINTS the command and returns 0;
# otherwise it executes it. Every mutating command goes through run().
run() {
  if [[ "$DRY_RUN" == "1" ]]; then
    echo "    [dry-run] $*"
    return 0
  fi
  "$@"
}

# gated(): a step the script REFUSES to automate — it prints the manual banner and
# does nothing, in both dry-run and real mode.
gated() {
  echo "    ── EMBER-GATED (manual) ── $*"
}

# ── the ember-gated banner (printed at the top of every real run) ────────────
gated_banner() {
  cat <<'BANNER'
[deploy-games] ══════════════════════════════════════════════════════════════
[deploy-games]  EMBER-GATED FLIPS this script does NOT perform (do them first /
[deploy-games]  around the run — see deploy/games/RUNBOOK.md):
[deploy-games]    (b) place ~/.config/dregg/games.env (tokens) + chmod 600
[deploy-games]    (c) STOP THE OLD BOT FIRST (graviton / prior hbox) — double-fire
[deploy-games]    (a) DNS: demo.dregg.net -> hbox
[deploy-games]    (g) open hbox :80/:443 (ufw + port-forward) for Caddy/LetsEncrypt
[deploy-games]    (go-live) flip the demo public
[deploy-games] ══════════════════════════════════════════════════════════════
BANNER
}

# ── preflight ────────────────────────────────────────────────────────────────
preflight() {
  log "preflight"
  [[ -d "$GAMES_REPO_DIR" ]] || die "repo not found: $GAMES_REPO_DIR (set GAMES_REPO_DIR)"
  [[ -d "$SRC_DIR" ]] || die "deploy/games not found under $GAMES_REPO_DIR — is this the right checkout / branch?"
  if [[ ! -f "$GAMES_ENV" ]]; then
    warn "env file $GAMES_ENV MISSING — ember must place it (tokens + bind + DATABASE_URL)."
    gated "place $GAMES_ENV from deploy/games/.env.example, then chmod 600"
    [[ "$DRY_RUN" == "1" ]] || die "cannot start units without $GAMES_ENV; place it and re-run"
  fi
  run mkdir -p "$STATE_DIR" "$USER_UNIT_DIR" "$RELEASES_DIR"
}

# ── build ────────────────────────────────────────────────────────────────────
build() {
  log "build (cargo --release): ${BINARIES[*]}"
  # web server: root workspace member.
  run bash -c "cd '$GAMES_REPO_DIR' && cargo build --release -p dreggnet-web --bin dreggnet-web-server"
  # bot: its OWN workspace — build from within discord-bot/ (NOT `-p` from root,
  # which fails: it is `exclude`d from the root workspace).
  if [[ "$SKIP_BOT" != "1" ]]; then
    run bash -c "cd '$GAMES_REPO_DIR/discord-bot' && cargo build --release --bin dregg-discord-bot"
  fi
}

# ── snapshots (rollback point) ───────────────────────────────────────────────
record_release() {
  local stamp dir b src
  stamp="$(date -u +%Y%m%dT%H%M%SZ)"
  dir="$RELEASES_DIR/$stamp"
  run mkdir -p "$dir"
  if [[ "$DRY_RUN" != "1" ]]; then
    git -C "$GAMES_REPO_DIR" rev-parse HEAD > "$dir/GIT_REV" 2>/dev/null || echo "unknown" > "$dir/GIT_REV"
  fi
  for b in "${BINARIES[@]}"; do
    src="$(bin_src "$b")"
    [[ -x "$src" ]] && run cp -p "$src" "$dir/$b"
  done
  # prune to newest $KEEP
  if [[ "$DRY_RUN" != "1" ]]; then
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
  local stamp="${1:-}" dir b
  [[ -n "$stamp" ]] || stamp="$(ls -1 "$RELEASES_DIR" 2>/dev/null | sort | tail -1)"
  [[ -n "$stamp" ]] || die "no snapshot to roll back to"
  dir="$RELEASES_DIR/$stamp"
  [[ -d "$dir" || "$DRY_RUN" == "1" ]] || die "no such snapshot: $stamp"
  log "rolling back binaries to snapshot $stamp"
  for b in "${BINARIES[@]}"; do
    [[ -x "$dir/$b" || "$DRY_RUN" == "1" ]] && run cp -p "$dir/$b" "$(bin_src "$b")"
  done
  restart_units
  log "NOTE: the repo stays at its current rev; only the BINARIES reverted to $stamp."
}

# ── install units + caddy ────────────────────────────────────────────────────
install_units() {
  log "install user systemd units: ${UNITS[*]}"
  local u
  for u in "${UNITS[@]}"; do
    run cp "$SRC_DIR/$u" "$USER_UNIT_DIR/$u"
  done
  run systemctl --user daemon-reload
  # survive logout so the user units keep running (deploy/hbox/RUNBOOK.md).
  run loginctl enable-linger "$USER"
  for u in "${UNITS[@]}"; do
    run systemctl --user enable "$u"
  done
}

install_caddy() {
  if [[ "$SKIP_CADDY" == "1" ]]; then
    log "SKIP_CADDY=1 — Caddy leg skipped (Caddy on the gateway per OPS-RUNBOOK topology B)"
    return 0
  fi
  log "install Caddyfile -> $CADDY_FILE (system caddy; needs sudo + hbox :80/:443 open)"
  # Validate the Caddyfile before installing it (adapt=caddyfile).
  run bash -c "caddy validate --adapter caddyfile --config '$SRC_DIR/caddy/Caddyfile.games'"
  run sudo cp "$SRC_DIR/caddy/Caddyfile.games" "$CADDY_FILE"
  run sudo systemctl reload caddy
  gated "DNS demo.dregg.net -> hbox and hbox :80/:443 must be OPEN for Let's Encrypt to issue"
}

restart_units() {
  local u
  for u in "${UNITS[@]}"; do
    run systemctl --user restart "$u"
  done
}

start_units() {
  local u
  for u in "${UNITS[@]}"; do
    run systemctl --user enable --now "$u"
  done
}

# ── health gate (mirrors deploy/aws/update-gated.sh) ─────────────────────────
health_gate() {
  if [[ "$DRY_RUN" == "1" ]]; then
    echo "    [dry-run] curl -fsS -m 5 $HEALTH_URL  (poll up to ${HEALTH_TIMEOUT}s; expect 200 {\"status\":\"ok\"})"
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
  journalctl --user -u dregg-web-games --no-pager -n 30 2>/dev/null || true
  return 1
}

# ── the gated deploy ─────────────────────────────────────────────────────────
deploy_up() {
  gated_banner
  preflight
  local snap
  snap="$(record_release | tail -1)"
  build
  install_units
  install_caddy
  start_units
  if health_gate; then
    log "games stack HEALTHY on the new release ($snap was the rollback point)"
    log "smoke test next (deploy/games/RUNBOOK.md step e): open the URL, play a game, /descent in Discord."
    return 0
  fi
  if [[ "$AUTO_REVERT" == "1" ]]; then
    warn "health gate failed — AUTO-REVERTING to $snap"
    restore_release "$snap"
    health_gate || die "rolled back to $snap but the gate STILL fails — page ember"
    die "new release failed the health gate; auto-reverted to $snap"
  fi
  die "new release failed the health gate (AUTO_REVERT=0; left as-is)"
}

case "${1:-up}" in
  up)        deploy_up ;;
  health)    health_gate ;;
  releases)  list_releases ;;
  rollback)  restore_release "${2:-}"; health_gate ;;
  *)         die "unknown subcommand: $1 (up | health | releases | rollback [stamp] | --dry-run)" ;;
esac

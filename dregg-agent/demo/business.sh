#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# dregg-agent — a REAL, flexible, live operator agent you can audit.
#
#   bash demo/business.sh "<natural-language goal>" [--budget N] [--caps a,b,…] [...]
#   bash demo/business.sh                      # uses a real default goal
#
# Hands a LIVE model (NVIDIA Nemotron) an arbitrary goal + a budget + a cap
# bundle, then runs a REAL reason→act→observe loop: the model decides the next
# tool call, every call is cap-gated + metered + receipted and runs FOR REAL (a
# real shell / fs / http / git, or the real Stripe Skills — provision a SaaS, pay
# a vendor). Then it PROVES the run: re-witnesses run.json offline (host
# untrusted) and shows a tampered line caught.
#
# THE STRIPE SKILLS BEAT (the hackathon headline): a second, deterministic beat
# drives the two real Stripe Skills for Hermes —
#   • stripe_provision  → `stripe projects add neon/postgres` (the agent provisions
#                          its own SaaS), cap-gated to `provision:neon`;
#   • stripe_pay        → `@stripe/link-cli` pay (the agent pays for a service it
#                          uses), cap-gated to `pay:openai`, the amount drawn from
#                          the budget cell — an over-budget pay is refused before
#                          money moves, and an ungranted vendor is cap-refused.
# It runs against the recorded transport offline and the LIVE CLIs the moment a
# test key (~/.stripekey or $STRIPE_API_KEY) + the Stripe CLIs are present.
#
# This is NOT a script. Hand it a different goal and the agent genuinely adapts.
# A model key in ~/.nvidiakey (or $NVIDIA_API_KEY) drives the open-goal beat live;
# without one, the bundled recorded transcripts replay (tools still run for real).
#
# Flags after the goal pass straight through, e.g.:
#   bash demo/business.sh "clone https://github.com/octocat/Hello-World and \
#       run any tests, then report" --caps shell,fs,git:github.com --budget 800
#   bash demo/business.sh --replay demo/resp.json     # replay a captured run
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
RUN_JSON="${RUN_JSON:-$HERE/run.json}"
SKILLS_JSON="${SKILLS_JSON:-$HERE/skills-run.json}"

# A leading non-flag argument is the goal; the rest pass through.
RUN_ARGS=()
if [[ $# -gt 0 && "${1:0:2}" != "--" ]]; then
  RUN_ARGS+=(--goal "$1"); shift
fi
RUN_ARGS+=("$@")

banner() { echo; echo "════════════════════════════════════════════════════════════════════"; echo "  $1"; echo "════════════════════════════════════════════════════════════════════"; }

# Build once (the live path needs the `live-brain` feature for the model + http).
banner "BUILDING dregg-agent (one-time)"
cargo build -q -p dregg-agent --bin dregg-agent --features live-brain --manifest-path "$REPO_ROOT/Cargo.toml"
BIN="$REPO_ROOT/target/debug/dregg-agent"

# Is a live model key available? If not, replay the bundled transcript (the
# tools — including the Stripe Skills — still execute for real / recorded).
HAVE_MODEL_KEY=0
if [[ -n "${NVIDIA_API_KEY:-}" || -f "$HOME/.nvidiakey" ]]; then HAVE_MODEL_KEY=1; fi

# ── BEAT 1: the open-goal operator run (live model, or the bundled replay) ──
banner "BEAT 1 — the live operator agent on an open goal"
if [[ "$HAVE_MODEL_KEY" -eq 1 && ! " ${RUN_ARGS[*]} " == *" --replay "* ]]; then
  "$BIN" run --budget 5000 --out "$RUN_JSON" "${RUN_ARGS[@]}"
else
  echo "  (no model key — replaying a bundled transcript; tools run for real)"
  "$BIN" run --budget 5000 --replay "$HERE/skills-replay.json" --no-scale \
      --out "$RUN_JSON" "${RUN_ARGS[@]}"
fi
"$BIN" verify "$RUN_JSON"
"$BIN" verify --tamper "$RUN_JSON"

# ── BEAT 2: the STRIPE SKILLS — provision a SaaS + pay for a service, bounded ──
banner "BEAT 2 — the real Stripe Skills for Hermes (provision + pay, bounded + proven)"
echo "  The agent provisions its own SaaS (stripe_provision) and pays for a service"
echo "  it uses (stripe_pay) — each cap-gated per provider/vendor, drawn from the"
echo "  budget cell, and receipted. Ungranted vendor → cap-refused; over-budget pay"
echo "  → refused before money moves. Live with ~/.stripekey + the Stripe CLIs."
echo
"$BIN" run --budget 5000 --caps provision:neon,pay:openai \
    --replay "$HERE/skills-replay.json" --no-scale --out "$SKILLS_JSON"
"$BIN" verify "$SKILLS_JSON"
"$BIN" verify --tamper "$SKILLS_JSON"

echo
echo "Done. Receipts at: $RUN_JSON  and  $SKILLS_JSON"
echo "Re-verify them yourself, offline:  $BIN verify $SKILLS_JSON"
echo "Arm the LIVE Stripe leg:  put a test key in ~/.stripekey + install the Stripe CLIs"
echo "Hand the agent a DIFFERENT goal to see it adapt:"
echo "  bash demo/business.sh \"list the 3 newest files in your workdir and summarize them\""

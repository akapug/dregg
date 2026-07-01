#!/usr/bin/env bash
# ─────────────────────────────────────────────────────────────────────────────
# dregg-agent — THE ~2-MINUTE FILM.
#
#   The autonomous business you can audit — Hermes + dregg + DreggNet cloud.
#
# A single paced run that tells the arc for the Hermes Agent-Accelerated-Business
# Hackathon (NVIDIA × Stripe × Nous):
#
#   COLD OPEN → OPERATE (the live Hermes/Nemotron brain) → SPEND (bounded; the
#   over-budget pay REFUSED, no money moved) → SCALE (sub-agent fork, attenuated)
#   → PROVE (verify ✓ → tamper → BadSignature) → CLOUD (hosted verifiable agent +
#   durable metered execution survives kill -9 exactly-once) → CLOSE.
#
# HONEST throughout. Each beat is labelled recorded-vs-live:
#   • OPERATE runs a RECORDED-LIVE Nemotron transcript (genuine model output,
#     captured once over the real NVIDIA endpoint, then replayed) — the TOOLS
#     execute for REAL (a real `git clone`, real fs, a real shell). On a box with
#     working egress, drop `REPLAY=…` and it drives the model LIVE (see re-film).
#   • The two Stripe Skills run the RECORDED transport (no `~/.stripekey` here);
#     with a test key + the Stripe CLIs the SAME calls shell the real commands.
#   • Two turns in the transcript are labelled [INJECTED PROBE] — the ungranted
#     vendor + the over-budget pay. They are OUR adversarial inputs (not the
#     model's decisions), there to make the teeth bite on camera.
#   • The DreggNet crash-resume is a REAL binary killed with a REAL SIGKILL.
#
# Usage:   demo/film.sh
# Env:     DREGGNET_DIR   a DreggNet checkout for the live crash-resume cloud beat
#                         (default: ~/dev/DreggNet; narrated caption if absent).
#          PACE           per-line reveal seconds (default 0.09; 0 = instant).
#          NO_CLEAR=1     skip the screen clears (for logging).
# ─────────────────────────────────────────────────────────────────────────────
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${DREGG_AGENT_BIN:-$REPO_ROOT/target/debug/dregg-agent}"
DREGGNET_DIR="${DREGGNET_DIR:-$HOME/dev/DreggNet}"
PACE="${PACE:-0.09}"
RUN_JSON="$(mktemp -t dregg-film-run).json"

# ── presentation ─────────────────────────────────────────────────────────────
if [ -t 1 ]; then
  B=$(printf '\033[1m'); D=$(printf '\033[2m'); R=$(printf '\033[0m')
  CY=$(printf '\033[36m'); GR=$(printf '\033[32m'); RD=$(printf '\033[31m')
  YL=$(printf '\033[33m'); MG=$(printf '\033[35m'); WT=$(printf '\033[97m')
else
  B=""; D=""; R=""; CY=""; GR=""; RD=""; YL=""; MG=""; WT=""
fi
cls()   { [ "${NO_CLEAR:-0}" = 1 ] || clear; }
# nap N — dwell N×NAPX seconds (NAPX tunes overall pacing without touching beats).
nap()   { sleep "$(awk "BEGIN{print ${1:-1}*${NAPX:-1}}")"; }
# reveal piped output line-by-line at a filmic pace (the output is REAL; we only
# reveal it steadily so a viewer can follow the reason→act→observe loop).
slow()  { if [ "$PACE" = 0 ]; then cat; else while IFS= read -r l; do printf '%s\n' "$l"; sleep "$PACE"; done; fi; }
rule()  { printf '%s%s────────────────────────────────────────────────────────────────────%s\n' "$D" "$CY" "$R"; }
banner(){ printf '\n%s%s  %s%s\n' "$B" "$CY" "$1" "$R"; rule; }
cap()   { printf '   %s%s%s\n' "$D" "$1" "$R"; }
say()   { printf '   %s%s%s\n' "$WT" "$1" "$R"; }
wow()   { printf '\n%s%s  ➤ %s%s\n\n' "$B" "$YL" "$1" "$R"; }

# ── COLD OPEN ────────────────────────────────────────────────────────────────
cls
cat <<EOF


     ${B}${MG}═══════════════════════════════════════════════════════════════$R

              $B$WT d r e g g - a g e n t $R
              $B$MG the autonomous business you can audit $R

     ${B}${MG}═══════════════════════════════════════════════════════════════$R


       ${WT}An AI agent that ${GR}earns${WT}, ${YL}spends${WT}, and runs a business —$R
       ${WT}and ${CY}proves${WT}${WT} it stayed inside its box.$R


       ${D}Hermes${R} ${D}(the brain) ·${R} ${D}dregg${R} ${D}(verify-don't-trust) ·${R} ${D}DreggNet${R} ${D}(cloud)${R}
       ${D}NVIDIA × Stripe × Nous — Agent-Accelerated-Business Hackathon${R}
EOF
nap 5

# ── THE SETUP ────────────────────────────────────────────────────────────────
banner "THE SETUP — one agent, on a leash"
say "A real model gets a natural-language goal, a BUDGET, and a CAP bundle."
say "Every tool-call is ${B}cap-gated · metered · receipted${R}${WT} and runs FOR REAL.${R}"
cap "brain   NVIDIA Nemotron  (llama-3.3-nemotron-super-49b-v1)"
cap "budget  5000¢ ceiling    caps  shell · fs · git · provision:neon · pay:openai"
cap "funding a metered ledger cell (the earn-side Stripe webhook→mint rail lives"
cap "        in DreggNet; here the budget cell IS the spend ceiling)"
cap "label   RECORDED-LIVE Nemotron transcript, replayed — the TOOLS run for real"
nap 4

# ── OPERATE + SPEND + THE TEETH (one coherent run) ───────────────────────────
banner "OPERATE + SPEND — the brain runs the job, bounded"
say "It clones a repo, reads it, provisions its own DB, pays for inference —"
say "then we ${RD}inject two hostile commands${R}${WT} and watch the teeth bite.${R}"
nap 2
"$BIN" run --goal "run the small business end-to-end" \
    --caps shell,fs,git:github.com,http:api.github.com,provision:neon,pay:openai \
    --budget 5000 --replay "$HERE/business-run.json" --out "$RUN_JSON" \
    2>&1 | sed -n '/reason →/,/audit it yourself/p' | slow
nap 4
wow "THE CLIMAX: the over-budget pay was REFUSED in-band — no money moved."
say "${D}Ungranted vendor → cap-refused. Over-budget → refused before any spend.${R}"
say "${D}A sub-agent forked with a strictly NARROWER bundle it cannot amplify.${R}"
nap 4

# ── PROVE ────────────────────────────────────────────────────────────────────
banner "PROVE — re-witness the whole run offline, trusting no host"
say "Anyone can re-verify the receipt chain from the file alone:"
nap 1
"$BIN" verify "$RUN_JSON" 2>&1 | sed -n '/GOAL/,/VERDICT/p' | slow
nap 3
banner "THE TEETH — flip ONE receipted line; the proof shatters"
say "We forge the receipt: \"it barely spent anything\" (50¢ → 1¢)."
nap 1
"$BIN" verify --tamper "$RUN_JSON" 2>&1 | sed -n '/tamper/,/VERDICT/p' | slow
nap 4

# ── CLOUD — DreggNet ─────────────────────────────────────────────────────────
banner "DreggNet CLOUD — the hosted verifiable agent"
say "Host the agent for someone else? A raw shell could read the operator's keys."
say "So a ${B}hosted session refuses it${R}${WT} — confined tools only:${R}"
nap 1
printf '   %s$ dregg-agent attach --account acct:tenant --caps %sshell%s,fs,http:… --budget 500%s\n' "$D" "$RD" "$D" "$R"
attach_msg="$( { echo ":quit" | "$BIN" attach --account acct:tenant \
    --caps shell,fs,http:api.github.com --budget 500 2>&1 || true; } | head -1 )"
printf '   %s✗ %s%s\n' "$RD" "${attach_msg%% — *}" "$R" | fold -s -w 70 | slow
cap "confined tools only (fs, http:, git:, pay:, provision:, cell:); the receipt"
cap "chain still holds. Restore shell with per-tenant OS isolation (named next step)."
nap 3

banner "DreggNet CLOUD — durable metered execution, exactly-once"
if [ -x "$DREGGNET_DIR/target/debug/dreggnet-crash-resume" ] || [ -f "$DREGGNET_DIR/demo/crash-resume.sh" ]; then
  say "A metered workload runs on DreggNet. We ${RD}kill -9${R}${WT} it mid-flight —${R}"
  say "a brand-new process resumes from the on-disk checkpoint:"
  nap 1
  ( cd "$DREGGNET_DIR" && RUST_LOG=error bash demo/crash-resume.sh 2>&1 ) \
    | grep -E 'PHASE|step1|step2|meter|checkpoint|kill -9|is gone|resumed|real executions|charged \(total\)|exactly-once proven' \
    | grep -vE 'not run yet|│|double-pay' | slow
  nap 2
  wow "Crash survived: step 1 replayed, step 2 ran once, the meter charged EXACTLY twice."
else
  say "${D}(DreggNet checkout not found — set DREGGNET_DIR for the live crash-resume.)${R}"
  say "A metered durable workload survives a real SIGKILL and resumes exactly-once:"
  cap "step 1 replayed from checkpoint · step 2 ran once · meter charged exactly twice"
fi
cap "DreggNet runs the lease on a multi-operator federation (honest devnet;"
cap "finality hardening in progress) — the substrate stays open + light-client-witnessed."
nap 4

# ── CLOSE ────────────────────────────────────────────────────────────────────
cls
cat <<EOF


     ${B}${MG}═══════════════════════════════════════════════════════════════$R

        ${WT}An autonomous agent that ${GR}earns${WT}, ${YL}spends${WT}, and ${CY}scales${WT} —$R
        ${WT}and ${CY}proves${WT}${WT} it stayed in its box.$R

        ${B}${GR}verify-don't-trust, all the way down.$R

     ${B}${MG}═══════════════════════════════════════════════════════════════$R


        ${B}Hermes${R}${D} · the brain (Nous)${R}    ${B}NVIDIA${R}${D} · Nemotron${R}    ${B}Stripe${R}${D} · the Skills${R}

        ${D}dregg — open, formally-verified ocap substrate (AGPL).  DreggNet — the cloud.${R}
        ${D}re-verify any run yourself:  dregg-agent verify <run.json>${R}

EOF
nap 5
rm -f "$RUN_JSON"

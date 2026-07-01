# dregg-agent — the ~2-minute film

**The autonomous business you can audit — Hermes + dregg + DreggNet cloud.**
For the Hermes Agent-Accelerated-Business Hackathon (NVIDIA × Stripe × Nous).

One command records the whole arc:

```sh
demo/film.sh            # plays the ~2-min arc in your terminal
```

The rendered deliverable (kept local, gitignored — regenerate any time):

| file | what | size |
|------|------|------|
| `demo/film.mp4`  | the video (share this) | ~3.9 MB, **1:51** |
| `demo/film.gif`  | the loop (tweet / README) | ~6.8 MB |
| `demo/film.cast` | the asciinema recording (reproducible source) | ~14 KB |

## The arc (what a judge sees)

```
COLD OPEN → SETUP → OPERATE + SPEND (the teeth) → PROVE → CLOUD → CLOSE
```

A real model gets a natural-language goal, a **budget**, and a **cap bundle**. It
runs a genuine reason→act→observe loop; every tool-call is **cap-gated · metered ·
receipted** and runs **for real**. Then anyone re-verifies the whole run offline,
and a one-line tamper shatters the proof. Then the cloud face: a hosted agent that
can't exfiltrate the operator's keys, and durable metered execution that survives a
real `kill -9` exactly-once.

## Timed shot-list + narration (for a voiceover re-film / the tweet)

Times are the ~1:51 cut; the on-screen banners already carry the words, so the
voiceover is optional. Trim/extend by setting `NAPX` (dwell) and `PACE` (line
reveal) — see below.

| # | ~time | on screen | voiceover (optional) |
|---|-------|-----------|----------------------|
| 1 | 0:00–0:12 | **Title card** — "the autonomous business you can audit" | *"An AI agent that earns, spends, and runs a business — and proves it stayed inside its box."* |
| 2 | 0:12–0:24 | **THE SETUP** — brain (Nemotron), budget, caps, funding, the honesty label | *"A real model, a budget, a capability bundle. Every tool-call is cap-gated, metered, and receipted."* |
| 3 | 0:24–0:55 | **OPERATE + SPEND** — the reason→act→observe loop: `git_clone` → `list_dir` → `fs_read` → `shell` → `stripe_provision` → `stripe_pay`, then two red refusals | *"It clones a repo, reads it, provisions its own database, pays for the inference it used. Then we inject two hostile commands."* |
| 4 | 0:55–1:05 | **THE CLIMAX** (yellow callout) — over-budget pay REFUSED in-band, no money moved; ungranted vendor cap-refused; sub-agent forked strictly narrower | *"The over-budget payment is refused before any money moves. An ungranted vendor is refused. A sub-agent forks with a strictly narrower bundle it cannot amplify."* |
| 5 | 1:05–1:20 | **PROVE** — `verify` re-witnesses offline: chain ✓ signed+unbroken, bound ✓, scale ✓ | *"Anyone re-verifies the receipt chain from the file alone — no trusted host."* |
| 6 | 1:20–1:32 | **THE TEETH** — forge one line (50¢→1¢) → **`BadSignature`** (red) | *"Forge one receipted line — 'it barely spent anything' — and the proof shatters."* |
| 7 | 1:32–1:40 | **CLOUD / hosted** — `attach` refuses `shell` (operator-key exfil), confined tools only | *"Host it for someone else, and a raw shell — which could read the operator's keys — is refused."* |
| 8 | 1:40–1:50 | **CLOUD / durable** — metered workload, real `kill -9`, resume: step 1 replayed, step 2 once, meter charged exactly twice; federation caption | *"Durable metered execution survives a real crash exactly-once — no compute, no charge duplicated. On a multi-operator federation."* |
| 9 | 1:50–end | **Close card** — tagline + Hermes / NVIDIA / Stripe | *"An autonomous agent that earns, spends, scales — and proves it stayed in its box. Verify-don't-trust, all the way down."* |

## Tweet copy (draft)

> An AI agent that earns, spends, and runs a business — and **proves** it stayed
> in its box. 🧠 @NousResearch Hermes / NVIDIA Nemotron reasons + acts. Every
> tool-call is cap-gated, metered, receipted. The over-budget spend? Refused, no
> money moved. Tamper one line → `BadSignature`. Verify-don't-trust, all the way
> down. #dregg

## What is live vs recorded (honest — read this before you post)

- **The model is real.** The OPERATE transcript in `demo/business-run.json` is
  **genuine NVIDIA Nemotron output** (`llama-3.3-nemotron-super-49b-v1`), captured
  once over the real endpoint (`integrate.api.nvidia.com/v1`) by
  `demo/capture-transcript.py`, then **replayed**. Replay re-feeds the model's own
  decisions; **the tools execute for real** — the `git clone`, the `list_dir`, the
  `fs_read`, the `shell git log` all genuinely run against a real workdir on every
  playback. The film labels this "RECORDED-LIVE Nemotron transcript, replayed."
  *(We replay rather than call live only so the take is clean + deterministic and
  because this recording box has no outbound TLS for the agent's HTTP client; on a
  normal box, drop the replay and it drives the model live — see re-film below.)*
- **Two turns are injected, and labelled.** The ungranted-vendor pay and the
  over-budget pay are `[INJECTED PROBE]` turns in `business-run.json` — **our**
  adversarial inputs, not the model's decisions — there to make the teeth bite on
  camera. The first six turns + the finish are the model's genuine decisions.
- **The Stripe Skills leg is recorded** (no `~/.stripekey` present). The two Skills
  (`stripe_provision` → Stripe Projects, `stripe_pay` → Stripe Link) shell the
  **real** CLIs in test mode the moment a test key + the CLIs are present; without
  them a faithful recorded transport runs, labelled *"(Stripe Skill live leg needs
  the CLI + a test key)"* — never a fake "✓ paid". The budget draw is always real.
- **The receipts, the cap-gate, the budget refusal, the verify, and the tamper are
  100% real** — they re-witness `run.json` with no host trusted, on every run.
- **The DreggNet crash-resume is real:** a real `dreggnet-crash-resume` binary,
  killed with a real `SIGKILL`, resumed by a brand-new process over an on-disk
  SQLite store.
- **The federation is the honest devnet.** The film says "multi-operator
  federation (honest devnet; finality hardening in progress)" — no live-n=5-mainnet
  claim.

## Re-film it — the exact setup

**Terminal:** a clean, wide, dark terminal. Recommended: 100×34, a good monospace
(JetBrains Mono / Menlo / Fira Code), font size ≥ 15, a dark theme.

**Record + render (what produced the committed artifacts):**

```sh
# 0. build once
cargo build -q -p dregg-agent --bin dregg-agent --features live-brain

# 1. record the film to an asciicast (headless works without an interactive TTY)
DREGGNET_DIR=~/dev/DreggNet PACE=0.14 NAPX=2.2 \
  asciinema rec --headless --window-size 100x34 --output-format asciicast-v2 \
    --command "bash demo/film.sh" demo/film.cast

# 2. render a gif  (brew install agg)
agg --theme dracula --font-size 15 --line-height 1.35 \
    --idle-time-limit 30 --last-frame-duration 4 demo/film.cast demo/film.gif

# 3. render an mp4 (brew install ffmpeg)
ffmpeg -y -i demo/film.gif -movflags +faststart -pix_fmt yuv420p \
    -vf "scale=trunc(iw/2)*2:trunc(ih/2)*2" demo/film.mp4
```

Tune the length: `NAPX` scales every dwell (2.2 → ~1:51; 1.7 → ~1:28; 1.0 →
~0:52), `PACE` is the per-line reveal (seconds; `PACE=0` = instant). `DREGGNET_DIR`
points at a DreggNet checkout for the live crash-resume beat (a narrated caption
shows if it's absent).

**Screen-recording (voiceover) version:** run `demo/film.sh` in your terminal and
QuickTime/OBS-record it, reading the shot-list narration above. For an extra-strong
opener, first show it driving the model **truly live** (needs outbound HTTPS from
the agent's HTTP client):

```sh
export NVIDIA_API_KEY=$(cat ~/.nvidiakey)     # or leave ~/.nvidiakey in place
dregg-agent run --brain nemotron \
  --goal "clone https://github.com/octocat/Hello-World, read the README, and \
          report what the repo is; then finish" \
  --caps shell,fs,git:github.com --budget 5000
```

Re-capture a fresh genuine transcript any time (for a different goal / model):

```sh
python3 demo/capture-transcript.py demo/business-run.json   # writes a real Nemotron replay
```

That writes the model's **genuine** business turns (clone → read → provision →
pay → finish). The committed `demo/business-run.json` is that output with the two
`[INJECTED PROBE]` turns (ungranted vendor + over-budget pay) spliced in **before**
the finish — they are visibly labelled inside the file, and they are the only
non-model turns in it.

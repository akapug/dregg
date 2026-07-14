# Deploy plan — public demo + testnet (2026-07-14, from the deploy scout)

HEADLINE: the fastest public demo needs NEITHER the node, NOR a testnet, NOR the 45-min prover. dreggnet-web hosts all 5 games
+ the no-cheat leaderboard + stranger-run re-verification ENTIRELY IN-PROCESS, and its "verify" is deterministic REPLAY
re-execution (a stranger re-runs your run and confirms it), NOT a STARK check. The one blocker: dreggnet-web is a LIBRARY with
no server bin. The honest framing: the demo verifies by REPLAY (= the blog's "anyone re-runs your run and confirms it", true
today); the STARK fold (private-strategy, portable proof) is the labeled Phase-3 UPGRADE.

## RANKED PATH
- PHASE 0 (~1-2 days) — THE STANDALONE WEB DEMO (no node/testnet/prover). Build a dreggnet-web SERVER BIN (~15-line core: mount
  router()/catalog_router()/descent_router() + a TcpListener + axum::serve + /health + a bind env) [IN FLIGHT] + minimal
  persistence (sqlite or ephemeral) + wire the do-once surfaces/adventure into the catalog + front with Caddy on demo.dregg.net
  (TLS/rate-limit). Everything else (5 games, the clickable automatafl board, tug, the re-verified leaderboard, stranger-run
  replay-verify) is BUILT + green (dreggnet-web/src/{lib.rs, descent.rs}). => a stranger opens a URL + plays a game they can't
  cheat at.
- PHASE 1 (hours, parallel) — THE DISCORD DAILY. The bot is COMPLETE (reveal cron + live drand + /descent + sqlite + two deploy
  targets + deploy/hbox/RUNBOOK.md). Ops only: place prod tokens (DISCORD_TOKEN/APP_ID/BOT_SECRET), set DESCENT_ANNOUNCE_
  CHANNEL_ID, STOP GRAVITON'S BOT FIRST (two bots on one token double-fire).
- PHASE 2 (hours single-box / days multi-host) — THE TESTNET FEDERATION. One-command genesis (deploy/genesis/generate.sh) +
  one-command EC2 bring-up + Caddy TLS + gated deploy/rollback (deploy/aws) + real BFT + Lean finality + a runnable local n=4
  (scripts/federation-local.sh). GAP: re-genesis with an ML-DSA roster (ALSO lights up the beacon's PQ finalized-root half —
  today's genesis carries no ML-DSA roster so the federation can't furnish a hybrid quorum yet); n>=4 for fault slack (n=3 is
  unanimity-fragile); multi-host distribution is manual (keys/DNS/cross-host QUIC :9420); repoint off the devnet fg-goose.online.
- PHASE 3 — PORTABLE STARK PROOFS (the hard upgrade, NOT demo-blocking). STATUS: the async match-fold PROVING SERVICE is BUILT
  (dreggnet-prove-service — enqueue -> a worker folds OFF the play path -> status/wait, bounded + metered, the proof correctness-
  identical to the foreground fold, a forged match rejected). So proving is OFF-PATH now (the UX fix). ⚠ HONEST: the fold is NOT
  yet GPU-accelerated — it routes through prove_turn_chain_recursive's CPU recursion config (Radix2DitParallel + MerkleTreeMmcs);
  the GPU recursion variant (GpuDft + GpuFoldValMmcs) EXISTS + is runtime-dispatched but wiring it into the fold's per-layer
  aggregation is a circuit-prove change (the named ~2x lever; the inner 241s MMCS is the order-of-magnitude piece). So it's still
  ~45min, just off-path. ALSO: wgpu SIGSEGVs on persvati's headless driver (needs a working-GPU box, e.g. hbox if its driver is
  sound). NAMED NEXT: the GPU-recursion wire into prove_turn_chain_recursive; finish prove-in-browser wasm (the on-device
  commitment + the full VERIFY-in-browser landed; the full PROVE isn't); the service->board submit wire (dreggnet-game-board).
  Verify is succinct + K-independent (sub-second) so per-entry server verify is cheap regardless.
- PHASE 4 — THE EXTENSION (off critical path — it's the wallet). Store docs all READY; rebuild (./build.sh) + submit; the ~50MB
  wasm is an MV3 size/perf review risk.

## HONEST BLOCKERS
1. dreggnet-web has NO server bin — THE one blocker to a public game demo (~15 lines) [IN FLIGHT].
2. the 45-min fold has no production runner — but the demo's no-cheat = REPLAY re-execution, so this is a Phase-3 upgrade not a
   Phase-0 blocker.
3. testnet single-box (no multi-host turnkey; n=3 unanimity-fragile; genesis stale w/ no ML-DSA roster -> beacon PQ half can't
   quorum yet).
4. bot prod tokens + stop-graviton (pure ops).
5. extension rebuild + gitignored 50MB artifact (off critical path).
6. no dedicated games-web ops runbook — but docs/ops/OPS-RUNBOOK.md's gateway<->hbox topology (WireGuard, localhost-bind,
   systemd, health probes, rollback) transfers wholesale.
Hosting: an AWS Graviton EC2 gateway (public) + hbox (x86 build/host) + persvati (build); Caddy = TLS+CORS+reverse-proxy;
Prometheus/Grafana monitoring built. Domain: the app/demo = demo.dregg.net (a subdomain; ~/dev/dregg-site is the marketing
site). Key files: dreggnet-web/src/{lib.rs,descent.rs}, node/src/{lib.rs,api.rs,prove_pool.rs,finalization_votes.rs}, procgen-
dregg/src/beacon.rs, scripts/federation-local.sh, deploy/{genesis,aws,hbox}/, docs/ops/OPS-RUNBOOK.md, discord-bot/src/{main.rs,
reveal_cron.rs}, extension/build.sh.

<!-- ⚑ One of MANY concurrent /goal lanes — see GOALS-INDEX.md. This is the
     multichain-settlement lane ONLY. Edit only this file; never clobber another lane's.
     COORDINATION: stark-kill owns trace_rotated.rs + the AIR/rotated-proof pipeline + the
     Rung-3 fold ladder in circuit/. THIS lane owns chain/gnark (the EVM-settlement wrap),
     the bridge/light-client crates, dregg-governance's cross-chain spine, dregg-deploy. -->

# GOAL — MULTICHAIN SETTLEMENT: dregg as the trustless plug for every chain

North star: proof-carrying settlement + non-custodial proof-of-holdings governance across
Solana/EVM/Cosmos, the STARK→EVM wrap made actually-efficient, verified light-client rules
progressing toward folded (rung-3) verified light clients.

## Threads (priority; reassess as I learn)
1. **THE WRAP** (linchpin) — BN254-native-hash re-arch (docs/deos/WRAP-NATIVE-HASH-DECISION.md).
   Landed: native poseidon2_bn254 / merkle_bn254 / challenger_bn254 (measured ~61×). Next:
   MultiField challenger pack/split → Rust shrink layer (DreggOuterConfig) → Rust↔gnark transcript
   differential → residual levers (blowup↓queries @130-bit; cut w24's 452 cols; GKR-batch openings)
   → drive ~5M toward ~1-2M. Measure each step. (End-to-end apex proof blocked on the rotated-proof
   pipeline break — stark-kill's, NOT mine.)
2. **VERIFIED LC → FOLDED (rung 3)** — pilot folding ONE chain's verified verification as a
   recursion-foldable CellProgram leaf via DECO machinery (VERIFIED-LIGHTCLIENT-FOLD-PATH.md),
   cheapest-crypto-first. Upgrade a chain's no-forgery toward the DecoUnforgeable game-reduction.
3. **CROSS-CHAIN COMPLETION** — gov-spine residuals (EVM/Cosmos edge conversions; u128→u64
   fail-closed narrow; multi-network ChainId); widen sockets (post-Electra rotation dual-depth;
   Base OP-stack finality; Cosmos bisection).
4. **Opportunistic** — deploy-gate policies; workspace-vs-target consolidation (member-not-default
   for the light-client crates IF the dep graph joins cleanly — check, don't guess).

## Disciplines (these ARE the goal)
adversarial-auditor per lane · verify myself (lake/cargo/go) · commit by NAMED files · Fable
subagents model:'fable' · commits sign Opus 4.8 · honest scoping (rung-2≠rung-3; verified-RULES ≠
verified-chain) · NEVER touch trace_rotated.rs / files another terminal edits · maintained libs for
foreign crypto · HORIZONLOG every follow-up · measure before believing a lever · disjoint waves.

## Current thrust
Wave 1: (A) gnark MultiField challenger [wrap] · (scout) rung-3 fold grounding · workspace dep-check.

## Next 3 moves
1. Launch gnark MultiField challenger (Fable) + rung-3 fold-pilot grounding scout (Fable).
2. Dep-check: can eth-lightclient/cosmos-lightclient join the workspace (member-not-default)? →
   decides the cross-chain edge-conversion shape.
3. Launch cross-chain edge lanes (shaped by #2) + widen-sockets.

## Done-log
- (init 07-12) lane adopted. Already committed this session: native-hash gnark gadgets (~61×),
  verified-LC rules CR-floored (Tendermint/ETH/MPT), cross-chain gov spine, deploy-gate supply-bit
  policies. Baseline green.

# The commitment-width dial — N felts by permanence-of-damage

> **Status: design, post the variadic insight (ember + the basin, 2026-06-19).** Supersedes the
> "flip everything to 8-felt" framing. The faithful-commitment campaign built the N=8 machinery + proved
> the whole flag-day pipeline coherent (`2afa37206`); this reframes the *live flip* as a **variadic**
> switch: each effect-class commits at the width its damage-permanence requires, not a blanket 8.

## The mechanism is already parametric

The squeeze width is a knob, not a rewrite:
- `chip_lookup_sound_N` (`DescriptorIR2.lean`) takes `permOut : List ℤ → List ℤ` and forces **every**
  output column = the genuine permutation output — for whatever length `permOut` returns. Width-generic.
- The deployed chip AIR already constrains the **full 16-lane permutation** and merely returns `state[0]`;
  exposing N lanes is "return more of an already-computed AIR" (N ∈ {1..16}).
- The commitment chain carries an N-felt carrier (`wire_commit_8`/`wireCommitR8` are the N=8 instance;
  `hash_many`/the 1-felt path is N=1). `wideAppend` appends an N-felt carrier + N PI pins.

So a per-descriptor `commit_felts : N` parameter selects the width; the proof lever discharges any N.

## Why a dial and not a constant — the beacon bound

dregg's security is **liveness, not finality** ("the recent present is verifiable, the past is a haze").
The commitment folds the nonce, forces `nonce_after = nonce_before + 1`, and chains (`OLD_COMMIT` =
prior `NEW_COMMIT`) — so a forgery is not a free collision but a **constrained, racing** one: the forged
state must (a) collide the commit, (b) be a provably-reachable post-state, **and** (c) chain to the *current*
head — which advances every turn and depends on what *other* participants do (multi-causal, unpredictable, so
no pre-grinding). The attacker grinds against the live head inside the freshness window before it moves.

**Safe iff `T_turn < 2^(N·15.45) / R_attacker`** (collision = birthday ≈ N·15.45 bits, BabyBear felt ≈
30.9 bits; R = grinds/sec). The constrained-collision (reachable + chain-fitting) only strengthens this.

| N | digest bits | collision bits | safe-window vs 4090 (~2³³/s) | vs petascale (~2⁵⁰/s) |
|---|---|---|---|---|
| 1 | 31  | ~15 | **microseconds — broken** | broken |
| 2 | 62  | ~31 | turns < ~0.25 s | broken |
| 3 | 93  | ~46 | turns < ~2.3 h | turns < ~0.06 s |
| **4** | 124 | ~62 | **~17 years** | **turns < ~68 min** |
| 8 | 247 | ~124 | infeasible | infeasible |

**N=4 is the sweet-spot** for anything live: practically unforgeable even against petascale at any turn
cadence under ~an hour, at half the N=8 overhead.

## The hard caveat — where the beacon bound breaks

The beacon saves you only when **damage is transient**. A forged stale signal / guarded-hole open /
witness-receipt is inert once the head moves and detection fires. But a forged **value transfer or mint**
is permanent — *the value already flowed*; the head advancing does not un-mint it. Conservation can tolerate
**zero** successful forgeries, so it needs N high enough that grinding never succeeds even once — the
freshness window is irrelevant. **The beacon protects liveness; it does not protect conservation.**

## The dial — N by permanence-of-damage (the per-effect-class assignment)

| effect class | damage if forged | permanence | **N** |
|---|---|---|---|
| value: transfer, burn, mint, bridgeMint, note-spend | double-spend / mint-from-nothing | **permanent** (beacon can't un-flow) | **8** |
| authority movers: setPermissions, setVK, seal/unseal/destroy, makeSovereign | wrong authority on a cell | permanent-but-detectable/reversible | **6** (or 8) |
| capability open / attenuate / delegate | unauthorized cap exercise | semi-permanent (revocable) | **4–6** |
| coordination: guarded-hole open, intent, conditional-turn, queue/inbox | a stale/forged signal | **transient** (freshness-bounded) | **4** |
| pure liveness: heartbeat / receipt-witness / presence | a missed/forged pulse | transient, self-healing | **2** |

The width is **fixed per effect-class by the protocol and bound into the VK** — the light client reads which
N a proof-type uses from the pinned descriptor, NOT from an off-circuit negotiation (else it is the same
off-circuit-trust hole the whole campaign is closing). The prover does not choose N; the effect-class does.

## What's proven vs. remaining

PROVEN + green (additive, live wire untouched): the N=1 (live) and N=8 instances; the parametric lever
`chip_lookup_sound_N`; the full 8-felt flag-day pipeline (producer mints a wide proof, executor anchors the
16 PIs, forged anchor rejected — `sovereign_rotated_wide` 2/2); `wire_commit_8_chip` (the cell≡circuit
byte-twin). REMAINING:
1. **Instantiate the intermediate widths** (N=2, 4, 6) — generalize the N=8 producers/`wideAppend`/registry to
   parametric N (small: the lever is already generic; the producers loop the carrier 13× for any N).
2. **The per-effect-class N table** above, bound into the descriptor/VK.
3. **THE LIVE FLIP = the variadic switch** (irreversible VK epoch, **ember-gated**): repoint each live
   effect-class onto its N-width proven producer + executor anchoring, re-emit, re-pin the VK. After the
   intermediate widths exist, this is one per-class knob-turn, not a rewrite.

The light client trusts the published state once the flip lands: each transition binds at the width its
permanence demands — ~124-bit where a forgery is permanent, beacon-bounded ~62-bit where freshness carries it.

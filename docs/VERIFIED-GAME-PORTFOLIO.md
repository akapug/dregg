# The Verified-Game Portfolio — automatafl + multiway-tug (2026-07)

Two new games as the dregg engine's 2nd/3rd customers — the platform proof. Both are verified games: rules modeled in Lean,
a verified STARK for the mechanics, cards/pieces on the real executor, playable as Offerings on every surface + provable
in-tab (the extension's generic prover). NB the mechanics are a CUSTOM VK (a bespoke AIR / a Custom leaf in the fold), NOT
plain StateConstraint teeth — teeth handle the simple state-shape + validity; the Custom AIR proves the complex transition.

## The shared architecture (per game)
1. Vendor the reference rules engine (both are real Rust engines) as the deterministic `applyTurn` reference.
2. Model the STATE: simple scalars as dregg-schema register components; the board/deck/hand as a heap COLLECTION (the
   16-register model doesn't hold a 121-cell board or a 21-card deck).
3. The SIMPLE teeth lower via game-turn-slice's compiler (validity, counts, win-thresholds, conservation).
4. The COMPLEX transition = a hand-authored CUSTOM AIR (a Custom leaf), TRANSLATION-VALIDATION shape (the mover computes the
   next state off-circuit; the circuit re-checks each rule against the witnessed next-state).
5. The LEAN: model the rules + prove the AIR REFINES applyTurn ("the circuit accepts iff next == applyTurn(old, moves)") —
   the game-level analogue of the evalSimpleCtx_*_iff constraint twins. This is "the verified STARK for the mechanics."
6. The STARK: the Custom leaf -> prove_turn_chain_recursive (fold) -> verify_history — REUSE (generic over any CellProgram).
7. The Offering + frontends (the DungeonOffering template) + the extension binding + a `<dregg-*>` element (reuse).

## SHARED UPSTREAM GATE: Lane-D (ours now, as the IMT terminal)
The multi-turn fold is blocked on the 169->178 carrier-geometry migration (WIDE_NUM_CARRIERS 57->60 etc.) — the same
"Lane-D" that gated The Descent's ZK-leaderboard. SINGLE-LEAF proves in-tree today; a whole match-as-one-succinct-proof
waits on Lane-D. Unblocking it serves EVERY game (Descent + both new ones). We own the circuit now — claim it first.

## multiway-tug = HANAMIKOJI (the closer-to-built one — ship first)
A 2-player geisha card game (~335-LOC Rust engine, o1Labs/Corey Richardson): 7 geisha (charm [2,2,2,3,3,4,5]=21), a 21-card
deck, a hidden 6-card hand, 4 once-per-round actions (Secret/Discard/Gift/Competition), win at >=11 charm OR >=4 geisha.
Conservation is the game's own design (a Card Drop-bomb — cards only move, never destroyed = dregg conservation).
WHY CLOSER TO BUILT: starbridge-apps/TUSSLE is a near-identical 2-party commit->reveal->resolve VERIFIED game (the
template); cards-as-assets mostly built (dreggnet-asset + E1/E2 packs); JointTurn.lean + tussle give forge-proof 2-party
resolution (NOT the hard part). THE FRONTIER: the zk HIDDEN-HAND — the fog project_for gives who-may-look but no value-
binding; the deep-new is "prove a legal play without revealing the hand" via commit-each-hand-as-a-Poseidon2-Merkle-root +
each play carries StateConstraint::Witnessed{MerkleMembership} (a real tooth proving the card is in the committed hand,
revealing nothing) + the blind pick as a sealed-auction reveal. Phases: 0 rules-on-executor (M, ~1-2wk, huge reuse) · 1
cards-as-assets+packs (M) · 2 the zk hidden-hand (L, the frontier, rails exist) · 3 the STARK fold (L, Lane-D-gated;
Witnessed/Cases/HeapField teeth are named lowering-Blockers) · 4 Lean proof (L, parallel — conservation/one-action/win-
safety as Good predicates on Boundary/JointTurn) · 5 Offering+frontends+launch (M, reuse tussle/card.rs). HARDEST: Phase 2
(the value-binding hidden-hand); multiplayer is NOT hard.

## automatafl = an original SIMULTANEOUS-MOVE cellular-automaton game (the deeper one — second)
NOT a Tafl variant. ~1.4k-LOC Rust engine + a wasm web client. An 11x11 grid of {Repulsor,Attractor,Automaton,Vacuum};
players SIMULTANEOUSLY submit a secret move, reveal together, moves resolve, then the AUTOMATON ("Daemon") takes one
autonomous step; win = steer the Daemon into your goal (NO capture). THE CENTER OF GRAVITY: the board-transition AIR — the
simultaneous SCC move-resolution (a dep graph + Tarjan + chains/cycles/merges + occlusion raycast) + the Daemon's raycast
decision are BEYOND the teeth (AllowedTransitions/Reachable/PrefixOf are out-of-scope residuals) -> a big hand-authored
Custom AIR. Simple teeth that lower: move-validity (rook-align via AffineEq, in-bounds via InRangeTwoSided) + win-check
(FieldEquals). Phases: A vendor the engine (S) · B mutable-enum-grid encoding (M — a new schema archetype wrapper; the
HeapAtom::InRangeTwoSided/MemberOf atoms exist) · C the lowering teeth (S-M) · D the board-transition AIR (LARGE, NEW —
staged D1 Daemon-only -> D2 occlusion -> D3 full SCC) · E Lean applyTurn + the refinement theorem (LARGE, NEW — no game
precedent, the idiom exists) · F the Offering with a BATCH N-move advance (M — the crowd machinery picks 1 carrier,
automatafl carries N) · G frontends+launch (M, port rust/web). HARDEST: D (the AIR) + E (the Lean refinement).

## RECOMMENDED SEQUENCING
1. CLAIM LANE-D (the multi-turn fold geometry migration) — ours now; unblocks every game's match-as-one-proof.
2. multiway-tug/Hanamikoji FIRST — closer to built (tussle template), lower complexity, and it exercises the zk-hidden-hand
   (the differentiated "nobody sees your hand, nobody cheats" card game). Validates the platform with the cheaper game.
3. automatafl SECOND — the deep board-transition-AIR + Lean-refinement subproject; the flagship "verified boardgame with
   machine-checked rules." The Custom-VK/Lean-emit muscle built for #2 carries over.
Both leaning on: the Custom-VK/custom-leaf path, the verified-emit-from-Lean discipline (RotatedLayout Legal idiom), the
generic fold+verify_history backend, the Offering/extension/frontend reuse. The portfolio (Descent roguelite + Hanamikoji
TCG + automatafl boardgame) = three genres, one verifiable engine — the platform claim, proven.

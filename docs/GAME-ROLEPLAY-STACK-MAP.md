# The dregg game / roleplay / MUD stack — map (2026-07-12)

From a 4-explorer read-only census. The headline: **the substrate is unusually complete; the gaps are BINDINGS +
a few features, not reinvention.** Two verifiable-game substrates exist and are converging.

## Two substrates
- **attested-dm/** (Path B) — the RICHEST rules engine + `.dungeon` DSL (rooms/exits/objectives/items/combat/hostile/
  NPC/topic/spell/consumable/status/weapon — first-class DIALOGUE: `Npc`/`GameAction::Talk`/`DialogueRule`; SAVE/LOAD +
  an OVERWORLD of regions with travel gated on verified completion) + UN-JAILBREAKABLE attested narration. BUT on a
  local BLAKE3 toy ledger + fixture attestation. dungeon-on-dregg calls it "the LARP being replaced."
- **spween → dungeon-on-dregg → DungeonOffering → /dungeon** (Path A, DEPLOYED) — on the real circuit-proven executor.
  The 6 universes + the proven richer-mechanics modules (combat/dice_combat/skills/spells/progression/mud/multicell/
  collective). `narrator.rs` bridges attested-dm's narration attestation onto the real `TurnReceipt`.

## The four layers — what EXISTS (build on these)
- RULES: attested-dm::game (dialogue, combat, spells, loot-with-verifiable-randomness) + dungeon-on-dregg's executor
  mechanics. Dialogue is a first-class typed mechanic ALREADY (a new conversation = a new DialogueRule, not an engine).
- AI: the metered/budgeted Narrator (Bedrock->Nova->gemma->scripted, a hard USD BudgetLedger, per-run $0.05 cap, credit
  gate); the sealed BYO-key layer; the cap-gated confined Hermes brain (receipted). Game narrator is TRUSTED but SAFE
  (the executor resolves, the AI has no authority). The attestation CROWN (deos-hermes/attest.rs — zkoracle/tlsn,
  injection-free) EXISTS but isn't wired to the game narrator (fixture default). `Narrator::converse` supports
  TOOL-CALLING (unused) — the hook for an AI-DM that ACTS.
- WORLD/SOCIAL: progression.rs (a real gated character sheet — XP/level/class/abilities — but STANDALONE, not wired into
  /dungeon); mud.rs + node/shared_world.rs (multi-player live receipt-stream sync); collective.rs (the signed party
  ballot); multicell.rs (cross-cell world gating). CRUX: one-shot vs persistent — within a run persistent+verifiable;
  ACROSS runs ONE-SHOT (fresh seeded ephemeral cell). Identity persists (cipherclerk->stable CellId); character state
  does NOT.
- CONTENT: the spween DSL (Twine/Ink-class: passages/choices/conditions/effects) -> compiler -> real executor teeth;
  procgen-dregg (provably-fair, seed-committed, 6 biomes); ugc-dregg (PUBLISH universe + SUBMIT completion, no-cheat
  leaderboard, content-addressed); the /gallery (durable, re-verifies every row on boot). Monetization = the AI-narrated
  /dungeon (credits gate AI narration). NO creator economy (authorship free, author = an unverified NAME, no royalties/
  paid-universes/remix/fork). DSL ceiling: no dialogue trees, no var-op-var, no arithmetic, no in-DSL randomness;
  combat/spells live in Rust, not authorable.

## The gaps are BINDINGS + features (prioritized)
1. CROSS-RUN CHARACTER PERSISTENCE — wire progression.rs (proven, standalone) to the persistent per-user identity +
   durable persistence (redb/pg-dregg, named-unbuilt). Characters carry + level across runs. Biggest bang, smallest reach.
2. THE OVERWORLD / persistent MUD — re-home attested-dm's overworld (regions, travel gated on completion) onto the real
   executor. The world becomes a map that opens as you honestly clear dungeons.
3. NPCs/DIALOGUE ON THE DEPLOYED PATH — attested-dm HAS the dialogue mechanic; port it onto CellProgram teeth (like the
   other mechanics) OR expose it in the spween DSL. (The just-landed HeapFieldLteOther cross-key atom is exactly the
   "var op var" comparison the DSL lacks.)
4. ATTESTED AI-DM — wire attest.rs (the crown) into the game narrator so in-game AI decisions are ATTESTED, not just
   cost-metered. + use the unused tool-calling converse so the AI-DM ACTS.
5. CREATOR ECONOMY — wire the existing pieces (content-addressing + $DREGG pay + cclerk signing) into publishing:
   verified author identity, paid/premium universes, royalties, remix/fork lineage. A universe marketplace.
6. DSL EXPRESSIVENESS — dialogue trees, var-op-var (HeapFieldLteOther), expose the Rust mechanics in the author language.

## The HeapAtom AIR (separate, ready)
DeltaEquals + HeapFieldLteOther to caveat PARITY: VK-safe (new PI-manifest tags 20/21, NOT AIR polynomials), off the hot
carrier-geometry, the cross-key fits the existing 7-felt RotCaveatEntry. Stage DeltaEquals first (fixing a real tag-8
mismatch: tag 8 = FIELD_DELTA is EXACT re-eval, so tagHeapAtom's `8->deltaBounded` should be `8->deltaEquals`), then the
cross-key RelCaveat bridge. Both remain host-evaluated (the named HeapCaveatRuntimeDischarge premise) — parity with the
existing heap surface, not the register-slot live re-eval (which structurally can't read a heap key).

# Frontend plan — making the features + games playable (2026-07-14, from the frontend scout)

THE DO-ONCE PATH (confirmed, ~80% of the work): an Offering's render()->Surface IS a deos_view::ViewNode, and the web/
discord/telegram/wechat renderers cover every node. Write render->ViewNode ONCE per feature -> web is a one-line
catalog register, discord is free via the generic /offering adapter (or a ~400-line market.rs-clone shell). dreggnet-market
is the working reference (the only new-domain crate that impls Offering + a ViewNode surface). NONE of the features expose an
Offering yet.

RANKED PLAN:
- Tier A (do-once wins — each lights up 4 surfaces): TradeOffering (clone market, S-M); Quest/FactionOffering (dungeon-shaped,
  the CompiledStory/WorldCell is the template, S); register in dreggnet-web catalog_default_host (one line each, XS); Craft/
  Companion/Tavern/PartyOffering (party uses advance_collective, M each).
- Tier B (read-surfaces, one ViewNode each): an INVENTORY Offering (read owned dreggnet-asset notes -> a Grid/Table), a CHEEVO
  showcase, a GUILD page (S each).
- Tier C (the games — a core touch + one new node): (1) ADD render_for(session, viewer) to the Offering trait (defaulted =
  render, additive) — the HIDDEN-HAND fix, gates multiway-tug (Offering::render has no viewer param today); then TugOffering
  (compose the 7-guild-lane Table + a hand Row + action buttons). (2) ADD a coordinate-grid ViewNode to deos-view/tree.rs + its
  4 renderers, then AutomataflOffering (n-generic grid + rook-line legal-move highlighting; the board already composes from the
  existing Grid node, the grid ViewNode is the clean primitive). ⚠ HOLD until the game fold lanes land (they edit the game
  crates).
- Tier D (the visual layer — greenfield, partly spwashi-gated): E1 traits_root on the asset (⚠ TCB-adjacent — ride the mint_
  seed, NON-breaking), E2 DrawStream::weighted, E3 a traitsJson() getter — Rust, buildable now (M). The <dregg-sprite> element
  + spwashi's render(traits)->svg renderers are HIS deliverable (gated on the human). For in-tree board/sprite regions, wire
  through the existing Tile{handle,w,h} node (the host-painted escape hatch, already renders per-surface) rather than a bespoke
  sprite node.
THE EXTENSION is OFF the do-once path by design (closed-shadow port-fed elements hand-roll their own DOM per element — dregg-
descent.ts is the pattern; a <dregg-*> per feature is bespoke).
Key files: dreggnet-offerings/{lib.rs,host.rs}, deos-view/src/{tree.rs,web.rs,discord.rs}, dreggnet-web/src/lib.rs, dreggnet-
market/src/lib.rs (reference), discord-bot/src/commands/{offering.rs,market.rs}, docs/CONTENT-AND-ASSET-SPEC.md.

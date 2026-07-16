# Frontend map — the do-once path, and where every feature + game surfaces

THE DO-ONCE PATH (built, load-bearing): an Offering's render()->Surface IS a deos_view::ViewNode, and the web/
discord/telegram/wechat renderers cover every node. render->ViewNode is written ONCE per feature -> web is a one-line
catalog register, discord rides the generic /offering adapter. The trait carries render_for(session, viewer)
(defaulted = render, dreggnet-offerings/src/lib.rs:508) — the HIDDEN-HAND primitive: a surface shows each viewer
only their own hand.

WHAT SURFACES EXIST (each impls the ONE Offering trait; the web catalog drives all of them through the same generic
open/advance/render/verify path):
- Feature surfaces (dreggnet-surfaces/src/): trade, craft, companion, tavern, party, inventory, cheevo, guild —
  registered as a set by dreggnet_surfaces::register_surfaces (lib.rs:164). trade/inventory/craft stand on the ONE
  shared asset ledger (world.rs SharedWorld — object identity, not name convention: forge a Greatblade and it IS in
  your inventory and listable on your stall, the same note-cell).
- Games: TugOffering (dregg-multiway-tug/src/surface.rs; the web catalog wraps it in the seat-claiming SeatedTug
  adapter) and AutomataflOffering (dregg-automatafl/src/surface.rs; claims seats natively). Boards ride
  ViewNode::CoordGrid (deos-view/src/tree.rs:239), the coordinate-addressed leaf board node, rendered per-surface.
- Catalog: dreggnet-web catalog_default_host (lib.rs:1197) registers dungeon · council · market · tug · automatafl;
  register_non_game_offerings (lib.rs:1261) adds doc/names/compute/grain/hermes; register_surfaces adds the eight
  feature surfaces — the whole portfolio behind one catalog router.
- Visual layer: dreggnet-sprite (deterministic AssetId -> dregg-dice DrawStream -> trait vector -> layered SVG;
  same asset => byte-identical SVG), rarity drawn by the provably-fair DrawStream::weighted table draw (E2), wasm
  getters spriteSvg/traitsJson (wasm/src/bindings_sprite.rs, E3), and the <dregg-sprite> element
  (extension/src/elements/dregg-sprite.ts). The asset NoteDesc carries a first-class committed trait_root
  (E1, dreggnet-asset/src/lib.rs:162) — in note_digest, carried WriteOnce; AssetWorld::mint_with_traits commits
  an explicit content root, plain mint a deterministic derivation of the AssetId.

NAMED SEAMS (open, labeled — not built):
- Quest/FactionOffering (dungeon-shaped; the CompiledStory/WorldCell would be the template) has no surface.
- register_surfaces mounts ONE demo world per registration — a single-player world all sessions share. Per-player
  worlds want a SessionConfig that carries the viewer's identity (today it carries only a seed); named, not faked.
- THE EXTENSION is OFF the do-once path by design (closed-shadow port-fed elements hand-roll their own DOM per
  element — extension/src/elements/dregg-descent.ts is the pattern; a <dregg-*> per feature is bespoke).

Key files: dreggnet-offerings/{lib.rs,host.rs}, deos-view/src/{tree.rs,web.rs,discord.rs}, dreggnet-web/src/lib.rs,
dreggnet-surfaces/src/, dreggnet-market/src/lib.rs (the original reference impl), discord-bot/src/commands/
{offering.rs,market.rs}, docs/CONTENT-AND-ASSET-SPEC.md.

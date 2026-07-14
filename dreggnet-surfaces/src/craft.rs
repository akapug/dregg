//! # `CraftOffering` — a **playable forge loop** over [`dreggnet_craft`].
//!
//! The economy's first real SINK, surfaced as an Offering. A crafter picks a recipe, the forge
//! CONSUMES its input materials (real owned notes, provably destroyed on-chain — the
//! [`dreggnet_craft`] sink tooth), rolls a **provably-fair** quality off a committed beacon
//! ([`roll_craft`]), and MINTS a real owned output note whose content address binds the recipe +
//! inputs + roll. Every `advance` fires a real craft turn on the substrate.
//!
//! ## Honest scope
//!
//! This is a *playable* Offering: a legal craft mints a real output (and commits a genuine
//! owner-signed turn on the freshly-forged note, carried as the [`Outcome::Landed`] receipt); an
//! illegal one — too few live inputs for the recipe floor, or inputs already consumed — is a real
//! [`CraftError`](dreggnet_craft::CraftError) refusal that mints NOTHING (anti-ghost). The forge's
//! internal input-sink spends are themselves real committed turns; the Offering additionally
//! commits an owner-claim turn on the output to carry a first-class [`TurnReceipt`] for the render
//! seam. NAMED NEXT (not built here): weighted-quality tiers + catalysts + recipe trees (the
//! `dreggnet_craft` residuals), and routing a commissioned craft through the escrow-market swap.

use dreggnet_asset::AssetId;
use dreggnet_craft::{CraftForge, CraftQuality, Recipe, roll_craft};
use dreggnet_offerings::{
    Action, DreggIdentity, Offering, OfferingError, Outcome, RunCost, SessionConfig, Surface,
    VerifyReport,
};
use procgen_dregg::CommittedSeed;

use crate::{action_menu, menu, pill, row, section, short_hex, text};
use deos_view::ViewNode;

/// The affordance verb a crafter fires to forge a recipe (`arg` = the recipe index).
pub const TURN_CRAFT: &str = "craft";

/// The crafter label (owns every material + every forged output in the shared [`CraftForge`]).
const CRAFTER: &str = "crafter";

/// A raw material — a real owned [`dreggnet_asset`] note the forge can consume as a craft input.
struct Material {
    asset: AssetId,
    name: String,
}

/// A recipe on the bench — the [`Recipe`] (its id + input floor), a display label, and the
/// material indices it draws its inputs from.
struct Bench {
    recipe: Recipe,
    label: String,
    /// Indices into [`CraftSession::materials`] this recipe consumes.
    inputs: Vec<usize>,
}

/// A forged output — the crafted note's id, the recipe that forged it, and its fair-draw quality.
struct Forged {
    asset: AssetId,
    recipe_label: String,
    quality: CraftQuality,
    roll: u64,
}

/// **A live forge session** over the real [`CraftForge`] — the crafter's materials, the recipes on
/// the bench, the forged outputs, the committed beacon the fair draw anchors to, and the committed
/// craft-turn count.
pub struct CraftSession {
    forge: CraftForge,
    crafter: String,
    beacon: CommittedSeed,
    materials: Vec<Material>,
    benches: Vec<Bench>,
    outputs: Vec<Forged>,
    turns: usize,
}

impl CraftSession {
    /// Whether material `idx` is still a live, unconsumed note (read off the forge's own on-chain
    /// destroyed-set — an immutable read).
    fn material_live(&self, idx: usize) -> bool {
        self.materials
            .get(idx)
            .map(|m| !self.forge.is_destroyed(m.asset))
            .unwrap_or(false)
    }

    /// How many of a bench's input materials are still live (the recipe is craftable iff this
    /// meets the recipe's input floor).
    fn live_inputs(&self, b: &Bench) -> usize {
        b.inputs.iter().filter(|&&i| self.material_live(i)).count()
    }

    /// The number of committed craft turns so far.
    pub fn turns(&self) -> usize {
        self.turns
    }
    /// The number of outputs forged.
    pub fn output_count(&self) -> usize {
        self.outputs.len()
    }
    /// How many materials are still live (unconsumed).
    pub fn live_material_count(&self) -> usize {
        (0..self.materials.len())
            .filter(|&i| self.material_live(i))
            .count()
    }
}

/// **The craft offering** — a stateless factory over the forge substrate. Each [`open`](Offering::open)
/// stocks a fresh crafter with materials + a bench of recipes.
pub struct CraftOffering;

impl CraftOffering {
    /// A fresh craft offering.
    pub fn new() -> Self {
        CraftOffering
    }

    fn do_craft(&self, s: &mut CraftSession, idx: usize) -> Outcome {
        // Copy the bench's craft context into locals so the forge can be borrowed mutably below.
        let Some(bench) = s.benches.get(idx) else {
            return Outcome::Refused(format!("no recipe #{idx} on the bench"));
        };
        let recipe = bench.recipe.clone();
        let label = bench.label.clone();
        let input_assets: Vec<AssetId> = bench
            .inputs
            .iter()
            .filter_map(|&i| s.materials.get(i))
            .map(|m| m.asset)
            .collect();

        // The fair draw off the committed beacon (deterministic in beacon/recipe/inputs).
        let draw = roll_craft(&s.beacon, &recipe, &input_assets);

        // THE FORGE: re-verify the fair draw, destroy the inputs on-chain (the sink), mint the
        // output. A forged draw or an unavailable/too-few-input craft is refused with NO mint.
        match s.forge.craft(&s.crafter, &draw, &recipe) {
            Ok(out) => {
                // A genuine committed owner-signed turn on the freshly-forged note — the crafter
                // claims what it forged. Carries the first-class receipt for the seam.
                let claim = s
                    .forge
                    .assets_mut()
                    .transfer(out.asset_id, &s.crafter, &s.crafter)
                    .expect("the crafter can claim its own freshly-minted output note");
                s.outputs.push(Forged {
                    asset: out.asset_id,
                    recipe_label: label,
                    quality: out.quality,
                    roll: draw.roll,
                });
                s.turns += 1;
                Outcome::Landed {
                    receipt: claim.spend,
                    ended: false,
                }
            }
            Err(e) => Outcome::Refused(format!("craft `{label}` refused: {e}")),
        }
    }
}

impl Default for CraftOffering {
    fn default() -> Self {
        CraftOffering::new()
    }
}

impl Offering for CraftOffering {
    type Session = CraftSession;

    fn open(&self, cfg: SessionConfig) -> Result<CraftSession, OfferingError> {
        let mut forge = CraftForge::new();
        // The crafter's materials — real owned notes the forge can consume.
        let mats = [
            "Iron Ore",
            "Oak Hilt",
            "Star Iron",
            "Void Glass",
            "Salvaged Scrap",
        ];
        let materials = mats
            .iter()
            .enumerate()
            .map(|(i, name)| Material {
                asset: forge
                    .mint_material(CRAFTER, format!("dreggnet-surfaces/mat-{i}").as_bytes()),
                name: (*name).to_string(),
            })
            .collect();
        // The bench — three recipes. Greatblade + Relic each consume a live pair (both craftable);
        // Masterwork needs THREE inputs but only one is wired, so its floor cannot be met (a real
        // RecipeUnsatisfied refusal is always reachable).
        let benches = vec![
            Bench {
                recipe: Recipe::new("forge:greatblade", 2),
                label: "Greatblade".to_string(),
                inputs: vec![0, 1],
            },
            Bench {
                recipe: Recipe::new("forge:relic", 2),
                label: "Relic".to_string(),
                inputs: vec![2, 3],
            },
            Bench {
                recipe: Recipe::new("forge:masterwork", 3),
                label: "Masterwork".to_string(),
                inputs: vec![4],
            },
        ];
        // The committed beacon (a Descent day-seed stand-in); the seed pins a deterministic day.
        let byte = cfg.seed.map(|s| s as u8).unwrap_or(7);
        Ok(CraftSession {
            forge,
            crafter: CRAFTER.to_string(),
            beacon: CommittedSeed::from_bytes([byte; 32]),
            materials,
            benches,
            outputs: Vec::new(),
            turns: 0,
        })
    }

    fn actions(&self, s: &CraftSession) -> Vec<Action> {
        s.benches
            .iter()
            .enumerate()
            .map(|(i, b)| {
                let have = s.live_inputs(b);
                Action::new(
                    format!(
                        "Forge {} ({}/{} inputs)",
                        b.label, have, b.recipe.min_inputs
                    ),
                    TURN_CRAFT,
                    i as i64,
                    have >= b.recipe.min_inputs,
                )
            })
            .collect()
    }

    fn advance(&self, s: &mut CraftSession, input: Action, _actor: DreggIdentity) -> Outcome {
        let idx = input.arg.max(0) as usize;
        match input.turn.as_str() {
            TURN_CRAFT => self.do_craft(s, idx),
            other => Outcome::Refused(format!("unknown craft affordance: {other}")),
        }
    }

    /// Re-verify every forged output's provenance (its content-addressed lineage re-derives + the
    /// asset layer re-reads it live), and every consumed input is provably gone on-chain.
    fn verify(&self, s: &CraftSession) -> VerifyReport {
        for f in &s.outputs {
            let report = s.forge.asset_provenance(f.asset);
            if !report.verified {
                return VerifyReport::broken(
                    s.turns,
                    format!(
                        "`{}` provenance broke: {:?}",
                        f.recipe_label, report.reasons
                    ),
                );
            }
        }
        for m in &s.materials {
            if s.forge.is_destroyed(m.asset) {
                let report = s.forge.asset_provenance(m.asset);
                if report.verified {
                    return VerifyReport::broken(
                        s.turns,
                        format!("`{}` was consumed but still verifies live", m.name),
                    );
                }
            }
        }
        VerifyReport::ok(s.turns)
    }

    fn render(&self, s: &CraftSession) -> Surface {
        let mut children: Vec<ViewNode> = Vec::new();

        children.push(section(
            "Forge",
            "muted",
            vec![text(format!(
                "crafter {} · live materials {} · forged {} · turns {}",
                s.crafter,
                s.live_material_count(),
                s.output_count(),
                s.turns,
            ))],
        ));

        // The materials — a Table with a live/consumed status pill + provenance version count.
        let mut mat_rows: Vec<ViewNode> = vec![row(vec![
            text("Material"),
            text("Status"),
            text("Provenance"),
        ])];
        for (i, m) in s.materials.iter().enumerate() {
            let (status, tag) = if s.material_live(i) {
                ("live", "good")
            } else {
                ("consumed", "muted")
            };
            let versions = s.forge.asset_provenance(m.asset).length;
            mat_rows.push(row(vec![
                text(&m.name),
                pill(status, tag),
                text(format!("v{versions}")),
            ]));
        }
        children.push(section(
            "Materials",
            "accent",
            vec![ViewNode::Table(mat_rows)],
        ));

        // The recipes — a Section{Menu} of craft affordances (a below-floor recipe shows dimmed).
        let acts = action_menu(self.actions(s));
        if !acts.is_empty() {
            children.push(section("Recipes", "accent", vec![menu(acts)]));
        }

        // The forged outputs — a Table binding each to its recipe + fair-draw quality.
        if !s.outputs.is_empty() {
            let mut out_rows: Vec<ViewNode> = vec![row(vec![
                text("Item"),
                text("Quality"),
                text("Roll"),
                text("Owner"),
            ])];
            for f in &s.outputs {
                let tag = match f.quality {
                    CraftQuality::Legendary => "warn",
                    CraftQuality::Rare => "accent",
                    _ => "muted",
                };
                let owner = s
                    .forge
                    .owner_of(f.asset)
                    .map(|pk| short_hex(&pk))
                    .unwrap_or_else(|| "—".into());
                out_rows.push(row(vec![
                    text(&f.recipe_label),
                    pill(f.quality.label(), tag),
                    text(format!("{}/100", f.roll)),
                    text(owner),
                ]));
            }
            children.push(section(
                "Forged",
                "genuine",
                vec![ViewNode::Table(out_rows)],
            ));
        }

        children.push(section(
            "Verified turns",
            "genuine",
            vec![text(s.turns.to_string())],
        ));

        Surface(section(
            "DreggNet Forge — a provably-fair craft loop",
            "accent",
            children,
        ))
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

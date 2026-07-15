//! The **recipe catalog** — typed, multi-input, tiered recipes, and what a craft
//! produces. A [`Recipe`] names the exact multiset of material *kinds* it consumes, the
//! committed outcome/quality weight tables its draws are taken over, and the
//! [`OutputSpec`] it forges — a real [`dreggnet_gear::StatBlock`] or a companion egg. A
//! [`RecipeBook`] is the registered set a forge crafts against; a craft can only present a
//! recipe the book holds, so the weight tables (the rarity odds) are committed, not
//! per-craft.

use std::collections::HashMap;

use dreggnet_gear::{GearSlot, StatBlock};

use crate::quality::CraftQuality;

/// A material's **kind** — the semantic type a recipe requires (e.g. `"ore:iron"`,
/// `"essence:frost"`). A material asset carries its kind in the forge; a recipe consumes a
/// *multiset* of kinds, so "a greatblade needs two iron and one oak-hilt" is a typed
/// requirement, not merely "three of anything".
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct MaterialKind(pub String);

impl MaterialKind {
    /// A kind from a label.
    pub fn new(kind: &str) -> MaterialKind {
        MaterialKind(kind.to_string())
    }

    /// The kind's label.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl From<&str> for MaterialKind {
    fn from(s: &str) -> MaterialKind {
        MaterialKind::new(s)
    }
}

/// A gear **template** — the base stat block a recipe forges, before the quality tier
/// scales it. The crafted [`StatBlock`]'s stats are `base * quality.stat_percent() / 100`,
/// and its rarity is the fair tier, so a legendary craft is a materially stronger, real,
/// equippable item.
#[derive(Clone, Debug)]
pub struct GearTemplate {
    /// The slot the forged gear occupies.
    pub slot: GearSlot,
    /// The rune / affix id the forged gear carries (fixed by the recipe).
    pub rune: u64,
    /// The base offensive stat (scaled by the quality tier).
    pub base_might: u64,
    /// The base defensive stat (scaled by the quality tier).
    pub base_ward: u64,
    /// The base utility stat (scaled by the quality tier).
    pub base_guile: u64,
}

impl GearTemplate {
    /// The real [`dreggnet_gear::StatBlock`] this template forges at `quality` — the shared
    /// gear schema (rarity is the tier's [`CraftQuality::gear_rarity`], stats scaled by the
    /// tier's [`CraftQuality::stat_percent`]).
    pub fn stat_block(&self, quality: CraftQuality) -> StatBlock {
        let pct = quality.stat_percent();
        StatBlock {
            rarity: quality.gear_rarity(),
            slot: self.slot,
            might: self.base_might * pct / 100,
            ward: self.base_ward * pct / 100,
            guile: self.base_guile * pct / 100,
            rune: self.rune,
        }
    }
}

/// What a recipe forges. A crafted output is a REAL cross-crate artifact, not an opaque
/// note: either a [`dreggnet_gear::StatBlock`] (equippable by the `Armory`) or a companion
/// egg (a species + granted rarity `dreggnet_companion` hatches from).
#[derive(Clone, Debug)]
pub enum OutputSpec {
    /// A piece of gear — a scaled [`StatBlock`] from this template.
    Gear(GearTemplate),
    /// A companion egg of `species` — hatched (elsewhere) at the granted rarity.
    CompanionEgg {
        /// The species label (e.g. `"companion:frostwyrm"`).
        species: String,
    },
}

/// The concrete artifact a resolved craft produces — a real [`StatBlock`] or a species+
/// rarity egg. Purely a function of `(recipe output, granted quality)`, so there is no
/// forgery surface on the artifact itself: the forge derives it, the crafter never supplies
/// it. Its [`Self::content_digest`] binds into the output asset's content address.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CraftedArtifact {
    /// A forged piece of gear carrying a real, equippable stat block.
    Gear(StatBlock),
    /// A forged companion egg — the species + the shared-schema rarity it hatches at.
    CompanionEgg {
        /// The species label.
        species: String,
        /// The rarity the egg hatches at (the shared `dungeon_on_dregg::loot::Rarity`).
        rarity: dungeon_on_dregg::loot::Rarity,
    },
}

impl CraftedArtifact {
    /// A stable content digest of the artifact — the gear block's own
    /// [`StatBlock::traits_root`] (the exact commitment `dreggnet-gear` mints under), or a
    /// domain-separated hash of the egg's species + rarity. Folded into the craft commitment
    /// so the output asset id binds the concrete item, not just its tier tag.
    pub fn content_digest(&self) -> [u8; 32] {
        match self {
            CraftedArtifact::Gear(block) => block.traits_root(),
            CraftedArtifact::CompanionEgg { species, rarity } => {
                let mut h = blake3::Hasher::new_derive_key("dreggnet-craft-egg-artifact-v1");
                h.update(&(species.len() as u64).to_le_bytes());
                h.update(species.as_bytes());
                h.update(&[rarity_tag(*rarity)]);
                *h.finalize().as_bytes()
            }
        }
    }
}

/// A stable byte tag for the shared loot rarity (the loot layer keeps its own tag private).
fn rarity_tag(r: dungeon_on_dregg::loot::Rarity) -> u8 {
    use dungeon_on_dregg::loot::Rarity;
    match r {
        Rarity::Common => 0,
        Rarity::Uncommon => 1,
        Rarity::Rare => 2,
        Rarity::Legendary => 3,
    }
}

/// A **recipe** — a typed, tiered forging plan. Its `id` binds into the craft seed + the
/// output's content address; its `inputs` are the exact multiset of material kinds it
/// consumes (the real sink); its committed `outcome_weights` / `quality_weights` fix the
/// odds; its `output` is what it forges.
#[derive(Clone, Debug)]
pub struct Recipe {
    /// The recipe's stable id (e.g. `"forge:greatblade"`).
    pub id: String,
    /// The exact multiset of material kinds this recipe consumes (order-independent).
    pub inputs: Vec<MaterialKind>,
    /// The committed `[Botch, Partial, Success]` outcome weights (must sum `> 0`).
    pub outcome_weights: [u64; 3],
    /// The committed `[Common, Uncommon, Rare, Legendary]` quality weights (must sum `> 0`).
    pub quality_weights: [u64; 4],
    /// What this recipe forges.
    pub output: OutputSpec,
}

impl Recipe {
    /// A **safe** gear recipe — always succeeds (outcome weights all on `Success`), default
    /// rarity odds (`~3%` legendary). The minimal shape the crate shipped, now typed +
    /// output-bound.
    pub fn gear(id: &str, inputs: &[&str], template: GearTemplate) -> Recipe {
        Recipe {
            id: id.to_string(),
            inputs: inputs.iter().map(|k| MaterialKind::new(k)).collect(),
            outcome_weights: [0, 0, 1],
            quality_weights: DEFAULT_QUALITY_WEIGHTS,
            output: OutputSpec::Gear(template),
        }
    }

    /// A **risky** recipe — the given `[botch, partial, success]` odds. A botch eats the
    /// materials for nothing; a partial forges one tier down. The gamble a deeper sink adds.
    pub fn risky(
        id: &str,
        inputs: &[&str],
        outcome_weights: [u64; 3],
        quality_weights: [u64; 4],
        output: OutputSpec,
    ) -> Recipe {
        Recipe {
            id: id.to_string(),
            inputs: inputs.iter().map(|k| MaterialKind::new(k)).collect(),
            outcome_weights,
            quality_weights,
            output,
        }
    }

    /// The number of inputs (the real sink floor) this recipe consumes.
    pub fn input_count(&self) -> usize {
        self.inputs.len()
    }

    /// The required input kinds as a sorted-count multiset (for the atomic input match).
    pub fn required_kinds(&self) -> HashMap<MaterialKind, usize> {
        let mut m: HashMap<MaterialKind, usize> = HashMap::new();
        for k in &self.inputs {
            *m.entry(k.clone()).or_insert(0) += 1;
        }
        m
    }

    /// Is this recipe well-formed — at least one input, and both weight tables non-degenerate
    /// (sum `> 0`)? A degenerate recipe would make the fair draw ill-defined.
    pub fn is_well_formed(&self) -> bool {
        !self.inputs.is_empty()
            && self.outcome_weights.iter().sum::<u64>() > 0
            && self.quality_weights.iter().sum::<u64>() > 0
    }
}

/// The default `[Common, Uncommon, Rare, Legendary]` quality weights — the crate's original
/// flat-band feel (`60 / 25 / 12 / 3`), now a committed CDF over
/// [`procgen_dregg`]'s provably-fair `weighted` draw.
pub const DEFAULT_QUALITY_WEIGHTS: [u64; 4] = [60, 25, 12, 3];

/// The **recipe catalog** — the registered set a forge crafts against. A craft can only
/// present a recipe the book holds (by id), so the weight tables (the odds) and the typed
/// input requirements are committed to the catalog, never chosen per-craft.
#[derive(Clone, Debug, Default)]
pub struct RecipeBook {
    recipes: HashMap<String, Recipe>,
}

impl RecipeBook {
    /// An empty catalog.
    pub fn new() -> RecipeBook {
        RecipeBook {
            recipes: HashMap::new(),
        }
    }

    /// The **starter catalog** — a real, varied set: safe and risky gear recipes across the
    /// three slots + a companion-egg recipe. Every recipe is well-formed.
    pub fn starter() -> RecipeBook {
        let mut book = RecipeBook::new();
        book.register(Recipe::gear(
            "forge:greatblade",
            &["ore:iron", "ore:iron", "haft:oak"],
            GearTemplate {
                slot: GearSlot::Weapon,
                rune: 0x01,
                base_might: 40,
                base_ward: 0,
                base_guile: 4,
            },
        ));
        book.register(Recipe::gear(
            "forge:aegis",
            &["ore:iron", "ore:iron", "hide:drake"],
            GearTemplate {
                slot: GearSlot::Armor,
                rune: 0x02,
                base_might: 0,
                base_ward: 36,
                base_guile: 6,
            },
        ));
        book.register(Recipe::gear(
            "forge:charm",
            &["essence:frost", "silver:leaf"],
            GearTemplate {
                slot: GearSlot::Trinket,
                rune: 0x07,
                base_might: 6,
                base_ward: 6,
                base_guile: 24,
            },
        ));
        // A risky relic forge: a real chance to botch (lose the materials) or forge a flawed
        // partial, with a fatter legendary tail as the reward for the risk.
        book.register(Recipe::risky(
            "forge:relic",
            &["ore:star-iron", "essence:void", "essence:void"],
            [20, 30, 50],
            [30, 30, 25, 15],
            OutputSpec::Gear(GearTemplate {
                slot: GearSlot::Weapon,
                rune: 0x1f,
                base_might: 60,
                base_ward: 10,
                base_guile: 10,
            }),
        ));
        // A companion egg — a real cross-crate output (species + shared-schema rarity).
        book.register(Recipe::risky(
            "forge:frostwyrm-egg",
            &["essence:frost", "essence:frost", "shell:ancient"],
            [10, 20, 70],
            DEFAULT_QUALITY_WEIGHTS,
            OutputSpec::CompanionEgg {
                species: "companion:frostwyrm".to_string(),
            },
        ));
        book
    }

    /// Register (or replace) a recipe. Returns `false` (and does not register) if the recipe
    /// is not well-formed — a degenerate recipe never enters the catalog.
    pub fn register(&mut self, recipe: Recipe) -> bool {
        if !recipe.is_well_formed() {
            return false;
        }
        self.recipes.insert(recipe.id.clone(), recipe);
        true
    }

    /// The recipe with `id`, if the catalog holds it.
    pub fn get(&self, id: &str) -> Option<&Recipe> {
        self.recipes.get(id)
    }

    /// Every registered recipe id (sorted, for a stable listing).
    pub fn ids(&self) -> Vec<String> {
        let mut ids: Vec<String> = self.recipes.keys().cloned().collect();
        ids.sort();
        ids
    }

    /// How many recipes the catalog holds.
    pub fn len(&self) -> usize {
        self.recipes.len()
    }

    /// Is the catalog empty?
    pub fn is_empty(&self) -> bool {
        self.recipes.is_empty()
    }
}

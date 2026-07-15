//! The **provably-fair craft draw** — the two committed-weight selections a forge resolves
//! and re-verifies. A [`CraftDraw`] is the receipt of a real draw: the beacon + recipe +
//! (sorted) inputs it came from, the committed craft seed, and the outcome band + quality
//! tier the seed fixed. [`reverify_craft`] re-derives the whole thing from the committed
//! context + the recipe's public weight tables, so a forged (fabricated / rewritten)
//! outcome is caught before any input is spent.

use dreggnet_asset::AssetId;
use procgen_dregg::CommittedSeed;

use crate::CraftError;
use crate::quality::{CraftOutcome, CraftQuality};
use crate::recipe::{CraftedArtifact, OutputSpec, Recipe};

/// The stream index of the OUTCOME-band draw (botch / partial / success).
const OUTCOME_DRAW_INDEX: u32 = 0;
/// The stream index of the QUALITY-tier draw (common .. legendary).
const QUALITY_DRAW_INDEX: u32 = 1;

/// The domain tag folded into a craft seed derivation (so a craft draw stream can never
/// collide with the loot / dungeon-generation streams that share the beacon).
const DOMAIN_CRAFT_SEED: &[u8] = b"dreggnet-craft/craft-seed/v1";

/// The domain tag for a craft's content commitment (the output asset's mint seed).
const DOMAIN_CRAFT_COMMIT: &[u8] = b"dreggnet-craft/craft-commitment/v2";

/// Derive the **craft seed** for an attempt from a committed beacon value, the recipe id,
/// and the (sorted) input asset ids — a domain-separated hash, so the outcome is a
/// reproducible, input-bound draw a verifier who holds the same context re-derives. The
/// input ids are sorted so the seed is independent of the order the inputs are listed.
pub fn derive_craft_seed(
    beacon: &CommittedSeed,
    recipe_id: &str,
    input_ids: &[[u8; 32]],
) -> CommittedSeed {
    let mut sorted = input_ids.to_vec();
    sorted.sort_unstable();
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_CRAFT_SEED.len() as u64).to_le_bytes());
    h.update(DOMAIN_CRAFT_SEED);
    h.update(beacon.as_bytes());
    h.update(&(recipe_id.len() as u64).to_le_bytes());
    h.update(recipe_id.as_bytes());
    h.update(&(sorted.len() as u64).to_le_bytes());
    for id in &sorted {
        h.update(id);
    }
    CommittedSeed::from_bytes(*h.finalize().as_bytes())
}

/// A resolved, provably-fair craft outcome: the beacon + recipe + (sorted) input ids it
/// came from, the committed craft seed, the outcome band the first draw fixed, and the raw
/// quality tier the second draw fixed. This is the receipt of a real draw —
/// [`reverify_craft`] re-derives it from the committed context + the recipe's public weight
/// tables, so a forged (fabricated / rewritten) outcome is caught before any input is spent.
#[derive(Clone, Debug)]
pub struct CraftDraw {
    /// The committed beacon value the outcome is anchored to (its unpredictability root; in
    /// the flagship this is the verified drand-beacon day-seed).
    pub beacon: CommittedSeed,
    /// The recipe id the craft was forged under.
    pub recipe_id: String,
    /// The input asset ids consumed, SORTED (order-independent).
    pub input_ids: Vec<[u8; 32]>,
    /// The committed craft seed the fair draws were taken from ([`derive_craft_seed`]).
    pub craft_seed: CommittedSeed,
    /// The outcome band the first fair draw fixed (over the recipe's `outcome_weights`).
    pub outcome: CraftOutcome,
    /// The raw quality tier the second fair draw fixed (over the recipe's `quality_weights`)
    /// — the tier BEFORE a partial outcome's downgrade. See [`Self::granted_quality`].
    pub tier: CraftQuality,
}

impl CraftDraw {
    /// The quality actually GRANTED to the output: `tier` on a success, one tier down on a
    /// partial, and `None` on a botch (no output). This is the tier the minted item carries.
    pub fn granted_quality(&self) -> Option<CraftQuality> {
        self.outcome.granted_quality(self.tier)
    }

    /// The display line for a craft outcome (the band/tier are content-bound).
    pub fn describe(&self) -> String {
        match self.granted_quality() {
            Some(q) => format!(
                "{} craft of `{}` from {} inputs ({} tier {})",
                q.label(),
                self.recipe_id,
                self.input_ids.len(),
                self.outcome.label(),
                self.tier.label(),
            ),
            None => format!(
                "botched craft of `{}` from {} inputs (materials consumed)",
                self.recipe_id,
                self.input_ids.len(),
            ),
        }
    }
}

/// Draw the outcome band + quality tier off a committed craft seed and a recipe's weight
/// tables. Shared by [`roll_craft`] and [`reverify_craft`] so the honest and the re-verified
/// paths are the same code.
fn draw_bands(
    craft_seed: &CommittedSeed,
    recipe: &Recipe,
) -> Result<(CraftOutcome, CraftQuality), CraftError> {
    let (_req, _ev, stream) = procgen_dregg::verified_stream(craft_seed);
    let outcome_idx = stream
        .weighted(OUTCOME_DRAW_INDEX, &recipe.outcome_weights)
        .map_err(|e| CraftError::Forged(format!("the outcome draw did not resolve: {e:?}")))?;
    let outcome = CraftOutcome::from_index(outcome_idx)
        .ok_or_else(|| CraftError::Forged("the outcome index is out of the band table".into()))?;
    let tier_idx = stream
        .weighted(QUALITY_DRAW_INDEX, &recipe.quality_weights)
        .map_err(|e| CraftError::Forged(format!("the quality draw did not resolve: {e:?}")))?;
    let tier = CraftQuality::from_index(tier_idx)
        .ok_or_else(|| CraftError::Forged("the quality index is out of the tier table".into()))?;
    Ok((outcome, tier))
}

/// **Roll a real, provably-fair craft outcome** for a recipe over a set of input assets
/// under a committed beacon. Derives the committed craft seed, runs the VERIFIED procgen
/// stream, and reads the outcome band + quality tier off the recipe's committed weight
/// tables. Deterministic in `(beacon, recipe_id, input_ids)` — the same context always
/// re-derives the identical outcome (a crafter cannot grind a favourable result without
/// different inputs or a different beacon).
pub fn roll_craft(beacon: &CommittedSeed, recipe: &Recipe, inputs: &[AssetId]) -> CraftDraw {
    let mut input_ids: Vec<[u8; 32]> = inputs.iter().map(|a| a.bytes()).collect();
    input_ids.sort_unstable();
    let craft_seed = derive_craft_seed(beacon, &recipe.id, &input_ids);
    let (outcome, tier) = draw_bands(&craft_seed, recipe)
        .expect("a well-formed recipe's committed weight tables resolve the fair draws");
    CraftDraw {
        beacon: *beacon,
        recipe_id: recipe.id.clone(),
        input_ids,
        craft_seed,
        outcome,
        tier,
    }
}

/// **Re-verify a craft outcome is a real fair draw** — the tooth that refuses a forged
/// craft. Recomputes the craft seed from the claimed beacon + recipe + input ids (a mismatch
/// = a forged context), re-derives the honest outcome band + quality tier from the committed
/// seed over the recipe's committed weight tables, and confirms the claimed band + tier are
/// exactly the fair draw's. A fabricated legendary — a claim with no real draw, or a
/// rewritten band/tier — fails here. The `recipe` supplies the committed weight tables, so
/// a craft cannot present its own odds.
pub fn reverify_craft(draw: &CraftDraw, recipe: &Recipe) -> Result<(), CraftError> {
    // 0. The draw must be under THIS recipe (its committed weights are the ones checked).
    if draw.recipe_id != recipe.id {
        return Err(CraftError::Forged(format!(
            "the draw's recipe `{}` is not the presented recipe `{}`",
            draw.recipe_id, recipe.id
        )));
    }
    // 1. The craft seed must be the honest binding of the claimed context.
    let expect_seed = derive_craft_seed(&draw.beacon, &draw.recipe_id, &draw.input_ids);
    if expect_seed != draw.craft_seed {
        return Err(CraftError::Forged(
            "the craft seed is not bound to the claimed beacon/recipe/inputs".to_string(),
        ));
    }
    // 2. Re-derive the honest outcome band + quality tier (the fair, reproducible draws).
    let (true_outcome, true_tier) = draw_bands(&draw.craft_seed, recipe)?;
    // 3. The claimed band + tier must be the fair draws' — a rewritten flex is caught.
    if true_outcome != draw.outcome {
        return Err(CraftError::Forged(format!(
            "the claimed outcome {:?} is not the fair draw {:?}",
            draw.outcome, true_outcome
        )));
    }
    if true_tier != draw.tier {
        return Err(CraftError::Forged(format!(
            "the claimed tier {:?} is not the fair draw {:?}",
            draw.tier, true_tier
        )));
    }
    Ok(())
}

/// Resolve the concrete artifact a craft produces from the recipe's [`OutputSpec`] and the
/// GRANTED quality — a real [`dreggnet_gear::StatBlock`] or a species+rarity companion egg.
/// A pure function of `(recipe.output, quality)`: the forge derives it, the crafter never
/// supplies it, so there is no forgery surface on the artifact.
pub fn resolve_artifact(recipe: &Recipe, quality: CraftQuality) -> CraftedArtifact {
    match &recipe.output {
        OutputSpec::Gear(template) => CraftedArtifact::Gear(template.stat_block(quality)),
        OutputSpec::CompanionEgg { species } => CraftedArtifact::CompanionEgg {
            species: species.clone(),
            rarity: quality.loot_rarity(),
        },
    }
}

/// The craft's **content commitment** — the mint seed the output asset is minted under,
/// binding the recipe id, the (sorted) input ids, the outcome band, the granted quality, and
/// the concrete artifact's own content digest (the gear block's `traits_root`, or the egg's
/// species+rarity). The output [`AssetId`] is derived from `blake3(crafter_pk ‖ this)`, so
/// the item's content address itself encodes exactly what was forged from what.
pub fn craft_commitment(draw: &CraftDraw, artifact: &CraftedArtifact) -> Vec<u8> {
    let quality = draw
        .granted_quality()
        .expect("a commitment is only taken for a minting outcome (success/partial)");
    let mut h = blake3::Hasher::new();
    h.update(&(DOMAIN_CRAFT_COMMIT.len() as u64).to_le_bytes());
    h.update(DOMAIN_CRAFT_COMMIT);
    h.update(draw.beacon.as_bytes());
    h.update(&(draw.recipe_id.len() as u64).to_le_bytes());
    h.update(draw.recipe_id.as_bytes());
    h.update(&(draw.input_ids.len() as u64).to_le_bytes());
    for id in &draw.input_ids {
        h.update(id);
    }
    h.update(&[draw.outcome.tag(), quality.tag()]);
    h.update(&artifact.content_digest());
    h.finalize().as_bytes().to_vec()
}

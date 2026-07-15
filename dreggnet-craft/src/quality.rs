//! The **craft outcome** — the two provably-fair draws a forge resolves: the *outcome
//! band* (does the forge succeed, produce a flawed partial, or botch and eat the
//! materials?) and, on a success/partial, the *quality tier*. Both are a
//! [`procgen_dregg`] `DrawStream::weighted` selection over a **committed** weight table
//! (the recipe's), so "I forged a legendary" is a claim anyone re-derives from the seed +
//! the recipe's public weights — not one a crafter is trusted on.

use dreggnet_gear::Rarity as GearRarity;
use dungeon_on_dregg::loot::Rarity as LootRarity;

/// A crafted item's **quality** — the tier of the fair quality draw. Rarer tiers are a
/// smaller committed weight, so a [`CraftQuality::Legendary`] is a genuine tail whose
/// provenance (the recipe + inputs + seed it was forged from) anyone re-derives.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CraftQuality {
    /// The baseline craft — a serviceable output.
    Common,
    /// A fine craft.
    Uncommon,
    /// A masterwork.
    Rare,
    /// A legendary forging — the committed tail. A provable flex.
    Legendary,
}

impl CraftQuality {
    /// Every tier low→high, in the order the recipe's quality weight table lists them.
    pub const ALL: [CraftQuality; 4] = [
        CraftQuality::Common,
        CraftQuality::Uncommon,
        CraftQuality::Rare,
        CraftQuality::Legendary,
    ];

    /// The tier at weight-table index `i` (`0 = Common .. 3 = Legendary`).
    pub fn from_index(i: usize) -> Option<CraftQuality> {
        CraftQuality::ALL.get(i).copied()
    }

    /// This tier's index into the quality weight table.
    pub fn index(self) -> usize {
        match self {
            CraftQuality::Common => 0,
            CraftQuality::Uncommon => 1,
            CraftQuality::Rare => 2,
            CraftQuality::Legendary => 3,
        }
    }

    /// A stable byte tag (folded into the craft commitment so the quality is bound into
    /// the output's content address).
    pub(crate) fn tag(self) -> u8 {
        self.index() as u8
    }

    /// The tier one step lower (a partial/flawed craft downgrades; [`Self::Common`] is the
    /// floor).
    pub fn downgraded(self) -> CraftQuality {
        match self {
            CraftQuality::Legendary => CraftQuality::Rare,
            CraftQuality::Rare => CraftQuality::Uncommon,
            CraftQuality::Uncommon | CraftQuality::Common => CraftQuality::Common,
        }
    }

    /// The human label.
    pub fn label(self) -> &'static str {
        match self {
            CraftQuality::Common => "common",
            CraftQuality::Uncommon => "uncommon",
            CraftQuality::Rare => "rare",
            CraftQuality::Legendary => "legendary",
        }
    }

    /// The stat multiplier this tier applies to a gear template's base stats, in percent
    /// (`Common = 100%`, up to `Legendary = 250%`) — so a legendary craft is a materially
    /// better item, and the item's power is bound (via the stat block) to the fair tier.
    pub fn stat_percent(self) -> u64 {
        match self {
            CraftQuality::Common => 100,
            CraftQuality::Uncommon => 130,
            CraftQuality::Rare => 170,
            CraftQuality::Legendary => 250,
        }
    }

    /// The shared **gear** rarity this tier maps to — the SAME `dreggnet_gear::Rarity`
    /// schema the `Armory` equips, so a crafted gear output's rarity is the gear layer's
    /// own tier, not a craft-local parallel.
    pub fn gear_rarity(self) -> GearRarity {
        match self {
            CraftQuality::Common => GearRarity::Common,
            CraftQuality::Uncommon => GearRarity::Uncommon,
            CraftQuality::Rare => GearRarity::Rare,
            CraftQuality::Legendary => GearRarity::Legendary,
        }
    }

    /// The shared **loot** rarity this tier maps to — the `dungeon_on_dregg::loot::Rarity`
    /// a companion egg output is granted under (the tier `dreggnet_companion` hatches from).
    pub fn loot_rarity(self) -> LootRarity {
        match self {
            CraftQuality::Common => LootRarity::Common,
            CraftQuality::Uncommon => LootRarity::Uncommon,
            CraftQuality::Rare => LootRarity::Rare,
            CraftQuality::Legendary => LootRarity::Legendary,
        }
    }
}

/// A craft's **outcome band** — the FIRST fair draw, off the recipe's committed
/// `outcome_weights` table. A forge is not always a guaranteed success: a *risky* recipe
/// can [`Botch`](CraftOutcome::Botch) (the materials are still spent — the sink is real,
/// you gambled and lost them) or yield a flawed [`Partial`](CraftOutcome::Partial) (a real
/// output, one tier lower). A *safe* recipe weights the whole table onto
/// [`Success`](CraftOutcome::Success).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CraftOutcome {
    /// The forge failed: the inputs are consumed (the sink still fires) but NO output is
    /// minted. The gamble a risky recipe carries.
    Botch,
    /// A flawed forging: a real output is minted, but its quality is downgraded one tier.
    Partial,
    /// A clean forging: the output is minted at the drawn quality tier.
    Success,
}

impl CraftOutcome {
    /// Every band, in the order the recipe's `outcome_weights` table lists them.
    pub const ALL: [CraftOutcome; 3] = [
        CraftOutcome::Botch,
        CraftOutcome::Partial,
        CraftOutcome::Success,
    ];

    /// The band at weight-table index `i` (`0 = Botch, 1 = Partial, 2 = Success`).
    pub fn from_index(i: usize) -> Option<CraftOutcome> {
        CraftOutcome::ALL.get(i).copied()
    }

    /// This band's index into the outcome weight table.
    pub fn index(self) -> usize {
        match self {
            CraftOutcome::Botch => 0,
            CraftOutcome::Partial => 1,
            CraftOutcome::Success => 2,
        }
    }

    /// A stable byte tag (folded into the craft commitment).
    pub(crate) fn tag(self) -> u8 {
        self.index() as u8
    }

    /// Does this band mint an output at all? (A [`Botch`](Self::Botch) does not.)
    pub fn mints(self) -> bool {
        !matches!(self, CraftOutcome::Botch)
    }

    /// The human label.
    pub fn label(self) -> &'static str {
        match self {
            CraftOutcome::Botch => "botch",
            CraftOutcome::Partial => "partial",
            CraftOutcome::Success => "success",
        }
    }

    /// The quality actually granted for this band given the drawn tier: a
    /// [`Success`](Self::Success) grants `tier`, a [`Partial`](Self::Partial) grants
    /// `tier.downgraded()`, and a [`Botch`](Self::Botch) grants nothing.
    pub fn granted_quality(self, tier: CraftQuality) -> Option<CraftQuality> {
        match self {
            CraftOutcome::Success => Some(tier),
            CraftOutcome::Partial => Some(tier.downgraded()),
            CraftOutcome::Botch => None,
        }
    }
}

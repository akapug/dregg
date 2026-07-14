//! # `dreggnet-adventure` — THE DESCENT, integrated: the flagship as ONE coherent
//! verifiable RPG loop over the feature systems.
//!
//! `dreggnet-saga` proved the eight feature crates COMPOSE — but over a *synthetic*
//! errand universe built for the proof. This crate goes one level up and makes the
//! flagship itself the thing that exercises every system: it drives the REAL
//! [`dreggnet_offerings::daily_descent::DailyDescentOffering`] — the beacon-seeded
//! permadeath run, the persistent hardcore [`Character`](dreggnet_offerings::character::Character),
//! and the no-cheat board — as one continuous player loop, with the feature crates
//! wrapped around it and its ONE run object handed off object-identically.
//!
//! ## The loop (each `->` a real committed handoff on the shared substrate)
//!
//! **BEFORE the run — the loadout + the gate:**
//! 1. a **party** musters ([`dreggnet_party`]) — four seated roles, each cap = its mandate;
//! 2. the player equips **gear** ([`dreggnet_gear::Loadout`]) and brings a **companion**
//!    ([`dreggnet_companion::CompanionRoost`]) — the run LOADOUT, both owned assets keyed to
//!    the ONE [`PlayerIdentity`];
//! 3. a **faction**-gated quest-giver ([`dreggnet_quest::giver::FactionGatedGiverWorld`])
//!    gates the run's START: a player with no Ember standing is REFUSED the Descent-quest
//!    (the faction rep cell's `ObservedFieldEquals` fails closed); earning rep opens it.
//!
//! **THE RUN — the actual DailyDescentOffering:**
//! 4. the day's beacon-seeded permadeath world is opened + driven to the WIN on the real
//!    executor ([`drive_descent_to_win`]) — every move a real committed turn;
//! 5. the equipped gear ability + the level-N companion buff **AID it CROSS-CELL** — each a
//!    real [`ObservedFieldEquals`](dregg_app_framework) gate, REFUSED without the equipped
//!    gear / a level-N companion and COMMITTING with (non-vacuous, both legs driven);
//! 6. the run's loot drops as owned **assets** ([`dungeon_on_dregg::loot`] — a real fair draw
//!    bound to the run's committed day-seed).
//!
//! **AFTER — progression out (all off the ONE run object):**
//! 7. the run's single [`ugc_dregg::Completion`] **earns a CHEEVO** ([`dreggnet_cheevo`]),
//!    **sums into the GUILD** ([`dreggnet_guild`]), and **turns in the QUEST** (re-executed to
//!    the win via the shared no-cheat gate) — the SAME `&universe` + `&completion` into all
//!    three; a forged run earns none, sums into none, turns in none;
//! 8. the run's loot is **forged** ([`dreggnet_craft`]) into an item and **traded**
//!    ([`dreggnet_trade`]) to a buyer — the SAME crafted note-cell carried craft -> trade ->
//!    buyer with a continuous provenance lineage (the saga's reconciliation #1);
//! 9. a **season champion** ([`dregg_season`]) — the verified win enters the season-scoped
//!    no-cheat board and, ranking top-N, earns the hall-of-fame champion cheevo.
//!
//! ## The object-identity spine (the whole point)
//!
//! The Descent stops being a collection of standalone crates because ONE object flows the
//! whole way, never re-derived:
//!
//! * **the run** — a single `DailyDescentOffering` [`Completion`](ugc_dregg::Completion)
//!   (its [`Universe`](ugc_dregg::Universe) content-addressed by the day) is the object the
//!   cheevo anchors, the guild counts, the quest turns in on, and the season ranks — the same
//!   `&completion` by reference, one verified answer;
//! * **the item** — a single [`dreggnet_asset::AssetId`] note-cell is minted as the run's
//!   loot, forged, and traded in ONE ledger (craft -> trade adopts the forge's `AssetWorld`),
//!   its provenance lineage continuing rather than restarting;
//! * **the player** — ONE [`PlayerIdentity`] (reused verbatim from [`dreggnet_saga`]) is the
//!   party seat's ed25519 ballot key, the gear owner, the companion owner, the guild member,
//!   and the Descent player at once.
//!
//! ## Honest scope — wired vs. named reconciliations
//!
//! WIRED + DRIVEN (`cargo test -p dreggnet-adventure`): the faction-gated START (refused
//! without rep, opens with it), the real DailyDescentOffering run driven to the win, the gear
//! ability + companion buff aiding cross-cell (refused without the loadout, non-vacuous), the
//! ONE Completion earning the cheevo + summing the guild + turning in the quest (a forged run
//! caught at each), the looted note crafting + trading as the SAME note-cell, the season
//! champion cheevo, and the ONE identity across seat / gear / companion / guild.
//!
//! NAMED RECONCILIATIONS (deliberate, additive follow-ups — not built here):
//! * **The aid cells vs. the literal Descent world-cell.** The gear ability and the companion
//!   buff each host their OWN run-aid cell (the [`multicell`](dungeon_on_dregg::multicell)
//!   cross-cell pattern the two crates ship), gated on the equipped gear / the level-N
//!   companion. Binding those gates onto the ONE `DailyDescentOffering` world-cell (a single
//!   shared executor for run + gear + companion, and a production cross-node finalized-root
//!   channel) is the tighter wire — the same residual `dreggnet-gear` / `dreggnet-companion`
//!   already name in their own honest scope. The cross-cell PREDICATE is real here.
//! * **The quest turn-in.** The Descent-quest's START is the real `dreggnet-quest`
//!   `FactionGatedGiverWorld` (a faction-rep cross-cell gate). Its TURN-IN re-executes the
//!   SAME Descent `Completion` through the shared [`ugc_dregg::verify_completion`] no-cheat
//!   gate — the identical object the cheevo + guild consume. A dedicated `dreggnet-quest`
//!   giver whose turn-in gates directly on an arbitrary `Completion` (rather than the crate's
//!   built-in errand scene) is a named `dreggnet-quest` reconciliation.
//! * **The tavern front, kept light (the saga's reconciliation #4).** `dreggnet-tavern` pulls
//!   `dregg-node`/deos-host (mozjs), is async, and needs an `_exit(0)` to dodge a SpiderMonkey
//!   teardown SIGSEGV — pulling that elephant into this synchronous driven loop would make the
//!   green gate heavy + flaky. Presence + party-up are proven in `dreggnet-tavern`'s own e2e;
//!   the "(tavern presence -> party-up)" prelude is represented here by the light
//!   [`dreggnet_party`] muster. Named, deliberately not pulled.
//!
//! The driven loop lives in `#[cfg(test)] mod adventure`; run it with
//! `cargo test -p dreggnet-adventure`.

use dreggnet_offerings::Outcome;
use dreggnet_offerings::character::InMemoryCharacterStore;
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, DailyRun, GATE_HEAL, GATE_MEASURED, GATE_PRESS, HOARD_FORCE,
    HOARD_SEIZE, KEY_TAKE,
};
use procgen_dregg::CommittedSeed;

/// The ONE canonical player identity threaded across the crates — reused VERBATIM from
/// [`dreggnet_saga`]: it derives one name into the party seat's ed25519 ballot key, the guild
/// member handle, and the asset holder label (the gear owner / companion owner / craft +
/// trade holder). The same committed adapter the saga proved, applied to the flagship loop.
pub use dreggnet_saga::PlayerIdentity;

/// **Today's Descent day-seed** — a fixed committed seed standing in for a verified drand
/// day (the beacon-fetch is `dreggnet_offerings`' own named client seam). The day's world is a
/// pure function of it, so the loop reproduces a stable, winnable descent.
pub fn today_seed() -> CommittedSeed {
    CommittedSeed::from_bytes([0x7D; 32])
}

/// **A fresh hardcore Descent offering** over an in-memory character store — the real
/// flagship offering (permadeath ON; a fall PERISHES the persistent character). The loop
/// plays entirely `Local` (private + fast); settling to a node is the offering's own opt-in.
pub fn descent_offering() -> DailyDescentOffering<InMemoryCharacterStore> {
    DailyDescentOffering::new(InMemoryCharacterStore::new())
}

/// **Drive the day's descent to the WIN** — the real player loop, each step a real committed
/// [`DailyDescentOffering::advance`] turn on the day's world-cell. It reads the committed
/// narrative vars (`warden_hp` / `hp` / `heals_used`) and plays the honest survival line: fell
/// the warden with measured blows (binding wounds with the one field-dressing when a blow
/// would otherwise strand the run), press past the felled warden, take the key, press through
/// the beacon-drawn corridors, force the key-gated hoard-door, and seize the hoard (the win).
/// Every move is executor-refereed; a refusal aborts with the executor's own reason (no LARP).
pub fn drive_descent_to_win(
    offering: &DailyDescentOffering<InMemoryCharacterStore>,
    run: &mut DailyRun,
) -> Result<(), String> {
    // A bound on turns so a mis-driven run fails loud instead of looping forever.
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            return Ok(()); // the run has ended.
        };
        let choice = if room == "gate" {
            let warden = run.read_var("warden_hp");
            let hp = run.read_var("hp");
            let heals = run.read_var("heals_used");
            if warden == 0 {
                GATE_PRESS
            } else if hp >= 16 && (hp - 15 >= 16 || warden <= 15) {
                // Safe measured blow: either we can keep fighting, or this one fells the warden.
                GATE_MEASURED
            } else if heals == 0 {
                // A blow would strand us below the floor and the warden still stands — bind wounds.
                GATE_HEAL
            } else if hp >= 16 {
                GATE_MEASURED
            } else {
                return Err(format!(
                    "stranded at the warden (hp {hp}, warden {warden}, heals {heals})"
                ));
            }
        } else if room == "keyroom" {
            KEY_TAKE
        } else if room.starts_with("corridor") {
            CORRIDOR_ON
        } else if room == "hoardgate" {
            HOARD_FORCE
        } else if room == "hoard" {
            HOARD_SEIZE
        } else {
            return Err(format!("unexpected room `{room}`"));
        };

        match offering.advance(run, choice) {
            Outcome::Landed { ended, .. } => {
                if ended {
                    return Ok(());
                }
            }
            Outcome::Refused(why) => {
                return Err(format!("move refused at `{room}` (choice {choice}): {why}"));
            }
        }
    }
    Err("the descent did not end within the turn bound".to_string())
}

/// **A run-bound loot seed** — domain-separated over the run's committed day-seed and its
/// final committed fingerprint, so the run's loot drops are provably THIS run's (a different
/// day / a different run draws different loot). Used both as the fair-draw context for the
/// [`dungeon_on_dregg::loot`] vault and as the mint seed of the forge's material drops.
pub fn loot_seed(run: &DailyRun, idx: u64) -> Vec<u8> {
    let mut h = blake3::Hasher::new_derive_key("dreggnet-adventure/loot-drop/v1");
    h.update(run.day().seed.as_bytes());
    h.update(&run.final_commitment());
    h.update(&idx.to_le_bytes());
    h.finalize().as_bytes().to_vec()
}

#[cfg(test)]
mod adventure {
    //! THE DESCENT, integrated — driven end-to-end on the real layers. Each test drives one
    //! seam of the loop as real committed turns with the object-identity handoffs asserted;
    //! [`the_full_integrated_descent_loop_runs_end_to_end`] threads them all through one player.
    use super::*;

    use dregg_season::{CarryForwardPolicy, Season};
    use dreggnet_asset::AssetId;
    use dreggnet_cheevo::{Achievement, CheevoError, CheevoLedger};
    use dreggnet_companion::{CompanionRoost, roll_hatch};
    use dreggnet_craft::{CraftForge, Recipe, roll_craft};
    use dreggnet_gear::{Armory, Loadout, Rarity as GearRarity, StatBlock};
    use dreggnet_guild::Guild;
    use dreggnet_offerings::DreggIdentity;
    use dreggnet_party::{Party, PartyMove};
    use dreggnet_quest::giver::{EMBER_QUEST_VALUE, FactionGatedGiverWorld, GRANTED_SLOT};
    use dreggnet_trade::{LegSpec, TradeSide, TradeWorld};
    use dungeon_on_dregg::loot::{LootVault, reverify_drop, roll_drop};
    use ugc_dregg::{Completion, Universe, verify_completion};

    const HERO: &str = "Vael";
    const BUYER: &str = "Corvane";
    /// The Descent-quest's cheevo depth (a winning run presses well past this).
    const DEPTH_CHEEVO_MIN: u64 = 3;
    /// The buff / gear aid require a level-2 companion (cheap XP, a real cross-cell checkpoint).
    const COMPANION_AID_LEVEL: u64 = 2;

    fn hero() -> PlayerIdentity {
        PlayerIdentity::new(HERO)
    }

    /// Open + drive a full winning Descent run for `who`, returning the offering (owning the
    /// character store) and the WON run. The shared fixture the after-run handoff tests reuse.
    fn play_a_winning_descent(
        who: &PlayerIdentity,
    ) -> (DailyDescentOffering<InMemoryCharacterStore>, DailyRun) {
        let offering = descent_offering();
        let mut run = offering
            .open_from_seed(who.guild_member(), today_seed())
            .expect("today's descent opens for the player");
        drive_descent_to_win(&offering, &mut run).expect("the descent is driven to the win");
        assert!(run.is_won(), "the driven run reached the hoard (the win)");
        assert!(
            !run.is_dead(),
            "a survived win did not perish the character"
        );
        (offering, run)
    }

    /// Build the ONE run object the after-run handoffs share: the day's [`Universe`] and the
    /// run's single [`Completion`], authored + played by the one identity. `verify` confirms
    /// the run's own committed chain re-verifies before it is handed off.
    fn run_object(
        offering: &DailyDescentOffering<InMemoryCharacterStore>,
        run: &DailyRun,
        who: &PlayerIdentity,
    ) -> (Universe, Completion) {
        assert!(
            offering.verify(run).verified,
            "the won run's committed chain re-verifies"
        );
        let universe = run
            .day()
            .universe(who.name())
            .expect("the day publishes as a universe");
        let completion = offering
            .completion(run, who.name(), who.name())
            .expect("the won run builds its leaderboard completion");
        assert_eq!(
            completion.universe,
            universe.id(),
            "the completion is bound to THIS day's universe (object identity)"
        );
        (universe, completion)
    }

    // ── BEFORE: the faction-gated quest START (non-vacuous) ─────────────────────────────

    /// THE FACTION GATE on the run's START: a player with NO Ember standing is REFUSED the
    /// Descent-quest (the faction rep cell's cross-cell gate fails closed — a faction-locked
    /// player cannot start the run). Earning real faction standing opens the SAME quest-start.
    #[test]
    fn a_faction_locked_player_cannot_start_the_descent_then_can_once_rep_is_earned() {
        let giver = FactionGatedGiverWorld::deploy();

        // Faction-locked: the Descent-quest cannot be started (the faction ember_quest is unset).
        let refused = giver.grant_honest();
        assert!(
            refused.is_err(),
            "a no-rep player's Descent-quest start is refused by the faction gate, got {refused:?}"
        );
        assert_eq!(
            giver.read(giver.giver(), GRANTED_SLOT as usize),
            0,
            "anti-ghost: the quest was not started"
        );

        // Earn REAL faction standing (committed pledge + trial turns), and the SAME start opens.
        giver.earn_standing();
        giver
            .grant_honest()
            .expect("earning faction rep opens the Descent-quest start");
        assert_eq!(
            giver.read(giver.giver(), GRANTED_SLOT as usize),
            EMBER_QUEST_VALUE,
            "the Descent-quest is now started, matching the committed faction standing"
        );
    }

    // ── THE RUN: the loadout aids it cross-cell (non-vacuous, both legs) ─────────────────

    /// THE EQUIPPED GEAR AIDS THE RUN, cross-cell: the run-aid ability is REFUSED before the
    /// gear is equipped (the gear is not at the pinned finalized root — the `ObservedFieldEquals`
    /// fails closed) and COMMITS after a real equip. The equip is the only pivot — the aid is
    /// armed BECAUSE the equipped gear is owned + equipped.
    #[test]
    fn the_equipped_gear_ability_aids_the_run_cross_cell() {
        let hero = hero();
        let mut armory = Armory::new();
        armory.pubkey_of(hero.holder_label());
        // A legendary Descent weapon; its rune keys the run-aid ability.
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Legendary, 12, 0xDE5CE7),
        );
        let mut loadout = Loadout::new(armory, gear, None);

        // WITHOUT the equipped gear: the cross-cell run-aid is refused (fail-closed).
        let unarmed = loadout.gate.use_ability_honest();
        assert!(
            unarmed.is_err(),
            "the gear aid must refuse before the gear is equipped, got {unarmed:?}"
        );
        assert!(
            !loadout.gate.ability_unlocked(),
            "anti-ghost: the aid never fired"
        );

        // The owner equips (own + stamp) — the gear reaches its finalized equip root.
        loadout
            .equip(hero.holder_label())
            .expect("the one identity owns + equips the run gear");

        // WITH the equipped gear: the SAME aid turn commits — its admission read the peer cell.
        loadout
            .gate
            .use_ability_honest()
            .expect("the equipped gear aids the run cross-cell");
        assert!(loadout.gate.ability_unlocked());
    }

    /// THE LEVEL-N COMPANION BUFF AIDS THE RUN, cross-cell: a run buff requiring a level-2
    /// companion is REFUSED while the companion is below level 2 (its commitment is not the
    /// level-2 checkpoint — the `ObservedFieldEquals` fails closed) and COMMITS once the SAME
    /// companion is raised to level 2. The aid applies BECAUSE the companion is at the level.
    #[test]
    fn a_level_n_companion_buff_aids_the_run_cross_cell() {
        let hero = hero();
        let mut roost = CompanionRoost::new();
        roost.pubkey_of(hero.holder_label());
        // Hatch a companion from THIS day's committed seed (a run-bound fair draw).
        let draw = roll_hatch(&today_seed(), "companion:descent-drake", 0);
        let comp = roost
            .hatch(hero.holder_label(), &draw)
            .expect("the companion hatches from the run's seed");

        // Arm the run buff requiring a level-2 companion (pins the level-2 checkpoint).
        let gate = roost.arm_buff(&comp, COMPANION_AID_LEVEL);

        // BELOW LEVEL (level 1 < 2): the buff aid is refused (companion not at the checkpoint).
        roost.raise_to(&comp, 1).expect("raise to level 1");
        let below = roost.attempt_buff(&gate, hero.holder_label(), true);
        assert!(
            below.is_err(),
            "the companion buff must refuse below the required level, got {below:?}"
        );
        assert_eq!(
            roost.buff_value(&gate),
            0,
            "anti-ghost: the buff did not apply"
        );

        // AT LEVEL: raise the SAME companion to level 2 — now at the checkpoint; the buff commits.
        roost
            .raise_to(&comp, COMPANION_AID_LEVEL)
            .expect("raise to the required level");
        roost
            .attempt_buff(&gate, hero.holder_label(), true)
            .expect("the level-2 companion aids the run cross-cell");
        assert_eq!(
            roost.buff_value(&gate),
            COMPANION_AID_LEVEL,
            "the buff applied to the companion's level value"
        );
    }

    // ── THE RUN's loot as owned assets ──────────────────────────────────────────────────

    /// THE RUN'S LOOT DROPS AS OWNED ASSETS: a real fair draw off the run's committed day-seed
    /// mints a `dreggnet-asset` note owned by the player, whose provenance re-verifies and
    /// whose id is bound to the run it dropped from. A forged (rewritten) drop mints nothing.
    #[test]
    fn the_runs_loot_drops_as_owned_assets() {
        let hero = hero();
        let (_offering, run) = play_a_winning_descent(&hero);

        let mut vault = LootVault::new();
        let owner_pk = vault.pubkey_of(hero.holder_label());
        let drop = roll_drop(&run.day().seed, "boss:the-warden", 0);
        reverify_drop(&drop).expect("the run's drop is a real fair draw");

        let item = vault
            .claim(hero.holder_label(), &drop)
            .expect("the run's loot drops as an owned asset");
        assert_eq!(
            vault.owner_of(item.asset_id),
            Some(owner_pk),
            "the player owns the looted asset"
        );
        assert!(
            vault.verify_asset_provenance(item.asset_id).verified,
            "the looted asset's provenance re-verifies"
        );

        // A FORGED drop (a rewritten roll the seed never produced) mints nothing.
        let mut forged = drop.clone();
        forged.roll = if forged.roll == 99 { 98 } else { 99 };
        let refused = vault.claim(hero.holder_label(), &forged);
        assert!(
            refused.is_err(),
            "a forged loot claim mints nothing, got {refused:?}"
        );
    }

    // ── AFTER: the ONE Completion -> cheevo + guild + quest (object-identical) ───────────

    /// HANDOFF — the SAME `Completion` earns a CHEEVO, sums into the GUILD, and turns in the
    /// QUEST. One `&universe` + one `&completion` by reference into all three; each answers with
    /// the identical verified turns off the one run. Object-identical: nobody re-derives the run.
    #[test]
    fn the_one_completion_earns_a_cheevo_sums_the_guild_and_turns_in_the_quest() {
        let hero = hero();
        let (offering, run) = play_a_winning_descent(&hero);
        let (universe, completion) = run_object(&offering, &run, &hero);

        // (a) THE CHEEVO — earned over the SAME completion; soulbound to the hero.
        let mut cheevos = CheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &universe,
                &completion,
                Achievement::ReachedDepth {
                    var: "depth".to_string(),
                    min: DEPTH_CHEEVO_MIN,
                },
            )
            .expect("the verified descent earns the depth cheevo");

        // (b) THE GUILD — sums the SAME clear (identical &universe + &completion).
        let mut guild = Guild::form("The Descent Vanguard");
        let hero_id = hero.guild_member();
        guild.admit(&hero_id);
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero_id, &universe, &completion)
            .expect("the guild sums the same verified clear");

        // (c) THE QUEST TURN-IN — the SAME completion re-executed through the shared no-cheat
        // gate (the object the cheevo + guild consumed). The Descent-quest turns in on the win.
        let quest_turns = verify_completion(&universe, &completion)
            .expect("the Descent-quest turns in on the verified win");

        // The one run, three consumers, one answer.
        assert_eq!(
            cheevo.turns, guild_turns,
            "the cheevo + guild agree on the one run's turns"
        );
        assert_eq!(
            quest_turns, guild_turns,
            "the quest turn-in agrees on the one run's turns"
        );
        assert_eq!(
            cheevo.universe,
            universe.id(),
            "the cheevo anchors THIS day's universe"
        );
        assert_eq!(
            guild.stats().verified_clears,
            1,
            "exactly the one clear entered"
        );
        assert_eq!(guild.stats().total_turns, guild_turns);
    }

    /// THE REFUSAL LEGS (non-vacuous): a FORGED run earns NO cheevo and sums into NO guild off
    /// the same tamper; a NON-MEMBER cannot inflate the guild; and a verified run that MISSES
    /// the predicate earns nothing.
    #[test]
    fn a_forged_run_earns_no_cheevo_and_sums_into_no_guild() {
        let hero = hero();
        let (offering, run) = play_a_winning_descent(&hero);
        let (universe, honest) = run_object(&offering, &run, &hero);

        // FORGE: retcon the opening move to an ineligible one — on replay it refuses (the press
        // needs a felled warden), so the no-cheat re-execution fails.
        let mut forged = honest.clone();
        forged.play.steps[0].choice_index = GATE_PRESS;

        let mut cheevos = CheevoLedger::new();
        let earned = cheevos.earn(
            &universe,
            &forged,
            Achievement::ReachedDepth {
                var: "depth".to_string(),
                min: DEPTH_CHEEVO_MIN,
            },
        );
        assert!(
            matches!(earned, Err(CheevoError::RunRejected(_))),
            "a forged descent earns no cheevo, got {earned:?}"
        );

        let mut guild = Guild::form("The Descent Vanguard");
        let hero_id = hero.guild_member();
        guild.admit(&hero_id);
        let summed = guild.board_mut().record_clear(&hero_id, &universe, &forged);
        assert!(
            summed.is_err(),
            "a forged clear cannot inflate the guild, got {summed:?}"
        );
        assert_eq!(
            guild.stats().verified_clears,
            0,
            "anti-ghost: nothing counted"
        );

        // A NON-MEMBER's honest clear is refused too — the roster is the cap set.
        let stranger = DreggIdentity("Nyx-the-unenrolled".to_string());
        let refused = guild
            .board_mut()
            .record_clear(&stranger, &universe, &honest);
        assert!(
            refused.is_err(),
            "a non-member cannot inflate the guild, got {refused:?}"
        );

        // A verified run that MISSES the predicate earns nothing (non-vacuous predicate leg).
        let unreachable = cheevos.earn(
            &universe,
            &honest,
            Achievement::ReachedDepth {
                var: "depth".to_string(),
                min: 999,
            },
        );
        assert!(
            matches!(unreachable, Err(CheevoError::PredicateNotMet(_))),
            "the run does not reach depth 999, so it earns nothing, got {unreachable:?}"
        );
    }

    // ── AFTER: the looted note crafts + trades as the SAME note-cell ─────────────────────

    /// THE LOOTED NOTE CRAFTS + TRADES AS THE SAME ASSET: the run's loot (two owned material
    /// drops seeded by the run) is forged into one item; the trade ADOPTS the forge's ledger
    /// (no re-mint), so the EXACT crafted note is sold to the buyer with a CONTINUOUS provenance
    /// lineage (mint(craft) -> escrow -> buyer) in ONE ledger. A non-owner cannot offer it.
    #[test]
    fn the_looted_note_crafts_and_trades_as_the_same_asset() {
        let hero = hero();
        let (_offering, run) = play_a_winning_descent(&hero);

        // The run's loot -> two owned material drops in the forge (seeded by the run).
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:descent-relic", 2);
        let m1 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 1));
        let m2 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 2));

        // Forge the relic — a fair craft draw anchored to the run's final committed fingerprint.
        let beacon = CommittedSeed::from_bytes(run.final_commitment());
        let draw = roll_craft(&beacon, &recipe, &[m1, m2]);
        let output = forge
            .craft(hero.holder_label(), &draw, &recipe)
            .expect("the run's loot forges into the relic");
        let relic: AssetId = output.asset_id;
        assert!(
            forge.is_destroyed(m1) && forge.is_destroyed(m2),
            "the material drops were spent on-chain (the sink)"
        );

        // THE SHARED-LEDGER HANDOFF: the trade adopts the forge's `AssetWorld` (no re-mint).
        let mut market = TradeWorld::with_assets(forge.into_assets());
        assert_eq!(
            market.lineage_len(relic),
            1,
            "the traded note IS the craft's origin mint — the lineage continues from length 1"
        );
        assert_eq!(
            market.current_owner(relic),
            Some(market.pubkey_of(hero.holder_label())),
            "the crafted note is the trade world's own live note (no re-mint)"
        );

        // The atomic escrow swap moves THAT note to the buyer.
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(
            hero.holder_label(),
            LegSpec::Asset(relic),
            BUYER,
            LegSpec::Dregg(50),
        );
        market
            .deposit(&mut trade, TradeSide::A)
            .expect("the seller deposits the relic");
        market
            .deposit(&mut trade, TradeSide::B)
            .expect("the buyer deposits the value");
        market
            .settle(&mut trade)
            .expect("the swap settles atomically");

        // Continuous provenance: mint(craft) -> escrow -> buyer, all in ONE ledger.
        let report = market.verify_provenance(relic);
        assert!(
            report.verified,
            "the traded relic's full lineage re-verifies"
        );
        assert_eq!(
            report.length, 3,
            "the lineage LENGTH continued craft->trade (mint -> escrow -> buyer), not restarted"
        );
        assert_eq!(
            market.current_owner(relic),
            Some(market.pubkey_of(BUYER)),
            "the buyer now owns the identical NOTE the run's loot forged"
        );

        // Non-vacuous: a NON-OWNER cannot offer the relic (the scam-proof gate).
        let mut mallory =
            market.open_trade("Mallory", LegSpec::Asset(relic), BUYER, LegSpec::Dregg(1));
        let stolen = market.deposit(&mut mallory, TradeSide::A);
        assert!(
            stolen.is_err(),
            "a non-owner cannot deposit the relic, got {stolen:?}"
        );
    }

    // ── AFTER: a season champion -> the hall-of-fame cheevo ──────────────────────────────

    /// A SEASON CHAMPION -> the dregg-season HALL-OF-FAME: the verified win enters the
    /// season-scoped no-cheat board; ranking top-N, the one identity is a champion, and the
    /// champion predicate over the season board earns the hall-of-fame cheevo. A player who did
    /// not place earns nothing.
    #[test]
    fn a_season_champion_earns_the_hall_of_fame_cheevo() {
        let hero = hero();
        let (offering, run) = play_a_winning_descent(&hero);
        let (_universe, completion) = run_object(&offering, &run, &hero);

        // The season-scoped board (pinned to the real local VK-epoch). Publish the day's
        // universe (re-derived identical) + submit the verified win.
        let mut season = Season::genesis(
            1,
            dregg_epoch::local_manifest(),
            "the-descent:s1",
            1000,
            CarryForwardPolicy::hall_of_fame(3).with_prestige(),
        );
        let season_universe = run
            .day()
            .universe(hero.name())
            .expect("the day publishes as a universe");
        season.board.publish(season_universe);
        season
            .board
            .submit(completion)
            .expect("the verified win enters the season board");

        // The one identity ranks in the hall-of-fame.
        let champions = season.champions(3);
        assert!(
            !champions.is_empty(),
            "the verified win placed on the board"
        );
        assert_eq!(champions[0].player, hero.name(), "the hero is the champion");

        // The champion predicate over the season board earns the hall-of-fame cheevo.
        let mut cheevos = CheevoLedger::new();
        cheevos
            .earn_champion(&season, hero.name(), 3)
            .expect("the season champion earns the hall-of-fame cheevo");

        // Non-vacuous: a player who did not place earns nothing.
        let not_champ = cheevos.earn_champion(&season, "Nobody", 3);
        assert!(
            not_champ.is_err(),
            "a non-placing player earns no champion cheevo, got {not_champ:?}"
        );
    }

    // ── ONE identity across the crates ──────────────────────────────────────────────────

    /// ONE IDENTITY is the party seat, the gear owner, the companion owner, AND the guild
    /// member. A single [`PlayerIdentity`] derives every representation the loop keys on — the
    /// same actor present across the crates by one object, not look-alikes matched by name.
    #[test]
    fn the_one_identity_is_seat_gear_companion_and_guild() {
        // The mustered party seats canonical identities; take the Tank seat's name.
        let party = Party::muster();
        let hero = PlayerIdentity::new(party.seat(0).name());

        // (a) THE PARTY SEAT — the one identity derives the seat's ed25519 ballot key.
        assert_eq!(
            hero.seat_pk(),
            party.seat(0).electorate_seat().pk,
            "the one identity's custody key IS the party seat's ballot identity"
        );

        // (b) THE GEAR OWNER — the SAME holder label owns the forged run gear.
        let mut armory = Armory::new();
        let hero_pk = armory.pubkey_of(hero.holder_label());
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Rare, 8, 0xA1),
        );
        assert_eq!(
            armory.current_owner(&gear),
            Some(hero_pk),
            "the one identity owns its gear"
        );

        // (c) THE COMPANION OWNER — the SAME holder label owns the hatched companion.
        let mut roost = CompanionRoost::new();
        let comp = roost
            .hatch(
                hero.holder_label(),
                &roll_hatch(&today_seed(), "companion:fox", 0),
            )
            .expect("the companion hatches");
        assert_eq!(
            roost.owner_of(comp.asset_id),
            Some(hero_pk),
            "the one identity owns its companion (same holder key as its gear)"
        );

        // (d) THE GUILD MEMBER — the SAME identity is admitted + counts a verified clear.
        let (offering, run) = play_a_winning_descent(&hero);
        let (universe, completion) = run_object(&offering, &run, &hero);
        let mut guild = Guild::form("The Descent Vanguard");
        guild.admit(&hero.guild_member());
        let turns = guild
            .board_mut()
            .record_clear(&hero.guild_member(), &universe, &completion)
            .expect("the one identity's clear is counted");
        assert!(turns > 0);

        // The representations are ONE canonical name across the crates.
        assert_eq!(hero.name(), hero.holder_label());
        assert_eq!(hero.guild_member().as_str(), hero.name());
    }

    // ── THE FULL LOOP — one player, all the way through ─────────────────────────────────

    /// THE FULL INTEGRATED DESCENT LOOP — one player threaded through the whole thing:
    /// party -> loadout (gear + companion) -> faction-gated start -> the REAL DailyDescentOffering
    /// run (aided cross-cell by the loadout) -> one Completion -> cheevo + guild + quest turn-in
    /// -> loot craft + trade -> season champion. Each step a real committed turn; the handoffs
    /// asserted object-identical; the end state coherent.
    #[test]
    fn the_full_integrated_descent_loop_runs_end_to_end() {
        // ONE canonical identity threads the whole loop.
        let hero = PlayerIdentity::new(HERO);

        // (1) THE PARTY MUSTERS — four seated roles; the seat IS the one identity's ballot key.
        let mut party = Party::muster();
        assert_eq!(party.seat_count(), 4);
        assert!(
            party.act_in_role(0).committed(),
            "the Tank guards the front"
        );
        assert!(
            party.act(1, PartyMove::GuardFront).refused(),
            "nobody plays another seat's role"
        );
        assert!(party.split_loot(&[40, 20, 20, 20]).committed());

        // (2) THE LOADOUT — equip GEAR (aids the run cross-cell) + bring a level-N COMPANION.
        let mut armory = Armory::new();
        armory.pubkey_of(hero.holder_label());
        let gear = armory.forge(
            hero.holder_label(),
            StatBlock::weapon(GearRarity::Legendary, 12, 0xDE5CE7),
        );
        let mut loadout = Loadout::new(armory, gear, None);
        assert!(
            loadout.gate.use_ability_honest().is_err(),
            "the gear aid is refused before it is equipped"
        );
        loadout
            .equip(hero.holder_label())
            .expect("the one identity equips the run gear");
        loadout
            .gate
            .use_ability_honest()
            .expect("the equipped gear aids the run cross-cell");

        let mut roost = CompanionRoost::new();
        roost.pubkey_of(hero.holder_label());
        let comp = roost
            .hatch(
                hero.holder_label(),
                &roll_hatch(&today_seed(), "companion:descent-drake", 0),
            )
            .expect("the companion hatches");
        let buff = roost.arm_buff(&comp, COMPANION_AID_LEVEL);
        roost.raise_to(&comp, 1).expect("raise to level 1");
        assert!(
            roost
                .attempt_buff(&buff, hero.holder_label(), true)
                .is_err(),
            "the companion buff is refused below the required level"
        );
        roost
            .raise_to(&comp, COMPANION_AID_LEVEL)
            .expect("raise the companion to the aid level");
        roost
            .attempt_buff(&buff, hero.holder_label(), true)
            .expect("the level-N companion aids the run cross-cell");

        // (3) THE FACTION-GATED START — locked without rep, opens once standing is earned.
        let giver = FactionGatedGiverWorld::deploy();
        assert!(
            giver.grant_honest().is_err(),
            "a faction-locked player cannot start the Descent-quest"
        );
        giver.earn_standing();
        giver
            .grant_honest()
            .expect("earning faction rep opens the Descent-quest start");

        // (4) THE RUN — the ACTUAL DailyDescentOffering, opened + driven to the win.
        let offering = descent_offering();
        let mut run = offering
            .open_from_seed(hero.guild_member(), today_seed())
            .expect("the Descent run opens for the started quest");
        drive_descent_to_win(&offering, &mut run).expect("the Descent is driven to the win");
        assert!(run.is_won() && !run.is_dead(), "a survived win");
        assert!(
            run.character().xp() > 0,
            "the run earned the character real XP"
        );

        // (5) THE ONE RUN OBJECT — the day's universe + the single completion.
        let (universe, completion) = run_object(&offering, &run, &hero);

        // (6) CHEEVO + GUILD + QUEST — all off the SAME &universe + &completion.
        let mut cheevos = CheevoLedger::new();
        let cheevo = cheevos
            .earn(
                &universe,
                &completion,
                Achievement::ReachedDepth {
                    var: "depth".to_string(),
                    min: DEPTH_CHEEVO_MIN,
                },
            )
            .expect("the win earns the depth cheevo");
        let mut guild = Guild::form("The Descent Vanguard");
        guild.admit(&hero.guild_member());
        let guild_turns = guild
            .board_mut()
            .record_clear(&hero.guild_member(), &universe, &completion)
            .expect("the guild sums the same clear");
        let quest_turns =
            verify_completion(&universe, &completion).expect("the quest turns in on the win");
        assert_eq!(
            cheevo.turns, guild_turns,
            "cheevo + guild agree on the one run"
        );
        assert_eq!(quest_turns, guild_turns, "the quest turn-in agrees");

        // (7) THE LOOT -> CRAFT -> TRADE — the SAME note-cell to a buyer.
        let mut forge = CraftForge::new();
        let recipe = Recipe::new("forge:descent-relic", 2);
        let m1 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 1));
        let m2 = forge.mint_material(hero.holder_label(), &loot_seed(&run, 2));
        let draw = roll_craft(
            &CommittedSeed::from_bytes(run.final_commitment()),
            &recipe,
            &[m1, m2],
        );
        let relic = forge
            .craft(hero.holder_label(), &draw, &recipe)
            .expect("the loot forges the relic")
            .asset_id;
        let mut market = TradeWorld::with_assets(forge.into_assets());
        market.fund_dregg(BUYER, 100);
        let mut trade = market.open_trade(
            hero.holder_label(),
            LegSpec::Asset(relic),
            BUYER,
            LegSpec::Dregg(50),
        );
        market
            .deposit(&mut trade, TradeSide::A)
            .expect("seller deposits");
        market
            .deposit(&mut trade, TradeSide::B)
            .expect("buyer deposits");
        market
            .settle(&mut trade)
            .expect("the swap settles atomically");

        // (8) THE SEASON CHAMPION — the verified win enters the season board + earns the hall.
        let mut season = Season::genesis(
            1,
            dregg_epoch::local_manifest(),
            "the-descent:s1",
            1000,
            CarryForwardPolicy::hall_of_fame(3).with_prestige(),
        );
        season.board.publish(
            run.day()
                .universe(hero.name())
                .expect("the day publishes as a universe"),
        );
        season
            .board
            .submit(
                offering
                    .completion(&run, hero.name(), hero.name())
                    .expect("the run's completion for the season board"),
            )
            .expect("the verified win enters the season board");
        cheevos
            .earn_champion(&season, hero.name(), 3)
            .expect("the season champion earns the hall-of-fame cheevo");

        // ── THE END STATE IS COHERENT ──
        // the cheevo is SOULBOUND + re-verifies over the SAME run;
        cheevos
            .reverify_run(&cheevo, &universe, &completion)
            .expect("the earned cheevo independently re-verifies");
        // the relic is the buyer's, its provenance continuous (mint -> escrow -> buyer);
        assert_eq!(market.current_owner(relic), Some(market.pubkey_of(BUYER)));
        let prov = market.verify_provenance(relic);
        assert!(
            prov.verified && prov.length == 3,
            "the relic's lineage continued in one ledger"
        );
        // the guild rank reflects exactly the one verified clear;
        assert_eq!(guild.stats().verified_clears, 1);
        assert_eq!(guild.stats().total_turns, guild_turns);
        // the party's loot split stands as a committed ledger fact;
        assert_eq!(party.loot_share(0), 40);
        // the loadout aided the run (both gates fired);
        assert!(loadout.gate.ability_unlocked());
        assert_eq!(roost.buff_value(&buff), COMPANION_AID_LEVEL);
    }
}

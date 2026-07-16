# Design: World-Resolved, Verifiable Tactical Combat

Status: unadopted design (reference)  
Scope: a combat subsystem proposal for `attested-dm`  
Compatibility requirement: all existing games and the current `CombatEnemy` behavior continue to work unchanged.

## 0. Relation to the shipped engine

`attested-dm` ships a multi-combatant tactical encounter engine at HEAD, built on a much
simpler design than this document proposes — none of this document's API
(`resolve_combat_command`, `CombatRuleset`, `CombatState`, `CombatPhase`, draw manifests)
exists in the tree. The shipped engine (`attested-dm/src/game.rs`, `Combatant` /
`EncounterRule` around game.rs:923–1050) is turn-based and initiative-ordered, with a
closed ability set (`Strike` / `Guard` / cooldown `Special`), foes driven by a
deterministic AI folded into the same receipted turn as the player command, HP/cooldowns/
shields living as world flags, draws domain-separated through `dregg-dice` event kinds,
and replay verification end-to-end (`attested-dm/examples/combat.rs` drives a full fight).
It satisfies this document's core principle — the world resolves, the AI only narrates —
without this document's machinery.

What this document proposes beyond the shipped engine remains unbuilt: tactical zones and
range bands, rulesets as committed content (`.dungeon` `combat_ruleset` declarations and
ruleset roots), the closed `RuleEffect` algebra, general status stacks, action economy,
retreat routes, loot tables, and per-transition draw manifests. Read the rest of this
document as a reference design for those directions, not as the description or build plan
of what runs.

## 1. Decision summary

Combat is a deterministic state machine owned entirely by the world resolver. The AI may phrase a player's intent and narrate the result, but it never chooses targets, computes damage, invents legal moves, advances turns, or applies effects.

The subsystem is additive:

- Existing `GameAction::Attack` and simple `CombatEnemy` definitions keep their current authored meaning.
- Rich combat commands use the existing `GameAction::Use` surface with a reserved, typed combat payload. No new top-level `GameAction` variant is required.
- Entering an encounter creates a committed `CombatState`; leaving it produces a terminal outcome and ordinary cap-gated `WorldEffect`s.
- Every stochastic decision consumes a fixed, declared number of indexed `dregg-dice` draws.
- Replay commits to the combat ruleset and re-executes the same transition function, reproducing initiative, hit results, damage, statuses, rewards, and the next legal actor.

The central API is intentionally small:

```rust
pub fn resolve_combat_command(
    world: &WorldView,
    rules: &CombatRuleset,
    state: &CombatState,
    actor: CombatantId,
    command: CombatCommand,
    draws: &mut VerifiedDrawCursor<'_>,
) -> Result<CombatTransition, CombatError>;
```

This function is pure apart from consuming its explicitly supplied draw cursor. It returns effects and the next state; it does not mutate storage, narrate, or perform I/O.

## 2. Boundaries and non-goals

The engine owns:

- encounter creation and membership;
- initiative and turn/round progression;
- action legality and targeting;
- action economy, resources, and cooldowns;
- hit, defense, damage, healing, and status processing;
- defeat, retreat, victory, and reward eligibility;
- the exact draw plan and interpretation of every random result.

The AI owns only flavor:

- converting free-form prose into one closed typed command through the existing action parser;
- narrating the already-resolved `CombatEvent`s;
- optionally presenting legal actions returned by the engine.

The AI must not provide executable numeric fields such as damage, duration, DC, resource cost, target eligibility, or reward quantity. Flavor text is excluded from combat-state derivation and can be attached only after resolution.

Initial versions do not attempt free-form grids, continuous movement, simultaneous turns, hidden mutable dice tables, or arbitrary scripts. Position is represented by committed tactical zones and range bands. This gives useful tactics without introducing geometry ambiguity into replay.

## 3. Identity, commitments, and numeric policy

All identifiers are stable, content-address-independent keys resolved through the committed ruleset or encounter definition:

```rust
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Encode, Decode)]
pub struct EncounterId(pub [u8; 16]);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Encode, Decode)]
pub struct CombatantId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Encode, Decode)]
pub struct AbilityId(pub String);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Encode, Decode)]
pub struct StatusId(pub String);

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Encode, Decode)]
pub struct ItemId(pub String);
```

Simulation arithmetic uses integers only. Percentages are basis points (`0..=10_000`), and multipliers use fixed-point permyriad arithmetic with a specified rounding rule. No floating-point value enters a commitment or transition.

```rust
pub fn mul_bps_floor(value: u32, bps: u16) -> u32 {
    ((value as u64 * bps as u64) / 10_000) as u32
}
```

Every addition, subtraction, and multiplication is checked or saturating according to a ruleset-declared rule. The recommended policy is checked arithmetic during validation and saturating subtraction only for HP/resource depletion. Invalid content is rejected when the ruleset loads, not during a fight.

Canonical encoding must define map ordering, string normalization, enum discriminants, and integer widths. Ruleset roots, state hashes, and receipts use that canonical encoding.

## 4. Combat state machine

### 4.1 Phases

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum CombatPhase {
    /// Participants are committed; initiative has not yet been rolled.
    Creating,
    /// Initiative draws are consumed and a total order is established.
    Initiative,
    /// Exactly one living, non-withdrawn combatant may act.
    Acting { turn: TurnCursor },
    /// No more commands are accepted; terminal effects may be finalized once.
    Terminal(CombatOutcome),
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct TurnCursor {
    pub round: u32,
    pub initiative_index: u16,
    pub actor: CombatantId,
    pub turn_serial: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum CombatOutcome {
    Victory { winners: Vec<FactionId> },
    Defeat { defeated: Vec<FactionId> },
    Retreated { faction: FactionId, escaped: Vec<CombatantId> },
    Stalemate { reason: StalemateReason },
}
```

Allowed transitions are closed:

```text
Creating -> Initiative -> Acting <-> Acting -> Terminal
```

There is no transition out of `Terminal`. Encounter creation is a resolver effect triggered by committed world content, not by narration. Initiative is finalized before the first normal command. Each accepted command produces exactly one transition receipt, even if it contains multiple atomic events.

### 4.2 Encounter creation

An encounter definition identifies participants, spawn zones, victory conditions, retreat rules, and rewards. Creation snapshots all combat-relevant inputs from the committed world and ruleset. Mid-fight changes enter only through resolved combat effects; reading mutable external stats during damage calculation is forbidden.

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct CombatState {
    pub version: CombatEngineVersion,
    pub encounter_id: EncounterId,
    pub ruleset_root: Hash32,
    pub encounter_root: Hash32,
    pub phase: CombatPhase,
    pub combatants: BTreeMap<CombatantId, CombatantState>,
    pub initiative: Vec<InitiativeEntry>,
    pub zones: BTreeMap<ZoneId, ZoneState>,
    pub pending_rewards: RewardBundle,
    pub event_serial: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct CombatantState {
    pub id: CombatantId,
    pub source: CombatantSource,
    pub faction: FactionId,
    pub stats: CombatStats,
    pub hp: u32,
    pub resources: BTreeMap<ResourceId, ResourcePool>,
    pub cooldowns: BTreeMap<AbilityId, u16>,
    pub statuses: Vec<StatusStack>,
    pub abilities: Vec<AbilityId>,
    pub inventory: BTreeMap<ItemId, u16>,
    pub zone: ZoneId,
    pub life: LifeState,
    pub economy: ActionEconomy,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum LifeState {
    Active,
    Downed,
    Defeated,
    Withdrawn,
}
```

Creation validation rejects duplicate combatant IDs, missing abilities or zones, illegal initial resource values, absent factions, impossible victory conditions, and any participant whose snapshot cannot be canonically encoded. IDs are assigned deterministically from authored order after canonical expansion; authored maps may not rely on hash-map iteration.

### 4.3 Initiative

Each initiative-eligible combatant consumes exactly one bounded draw. The ordering key is total and stable:

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct InitiativeEntry {
    pub combatant: CombatantId,
    pub roll: u16,
    pub total: i32,
}

fn initiative_key(e: &InitiativeEntry) -> (Reverse<i32>, CombatantId) {
    (Reverse(e.total), e.combatant)
}
```

`total = initiative_stat + roll`; ties resolve by ascending `CombatantId`. The roll bound is specified by the ruleset, for example `1..=20`, and is drawn through `DrawStream::bounded` without rejection. Defeated or withdrawn participants are skipped when advancing. At the start of a new round, the order is normally stable; an ability may request a re-roll only if its definition includes the fixed draw cost and explicit reorder effect.

### 4.4 Turns and action economy

At turn start the engine, in this exact order:

1. increments the actor's turn serial;
2. resets the actor's per-turn action economy;
3. decrements turn-based cooldowns that tick at `TurnStart`;
4. processes `TurnStart` statuses in canonical status order;
5. checks terminal conditions;
6. if the actor can act, exposes legal commands; otherwise advances the turn.

At turn end it processes `TurnEnd` statuses, expires stacks, checks terminal conditions, then advances to the next eligible initiative entry. Round-end effects execute after the final initiative slot and before round increment.

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct ActionEconomy {
    pub actions: u8,
    pub bonus_actions: u8,
    pub reactions: u8,
    pub movement: u8,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct ActionCost {
    pub actions: u8,
    pub bonus_actions: u8,
    pub reactions: u8,
    pub movement: u8,
    pub resources: BTreeMap<ResourceId, u16>,
}
```

Costs are validated before draws are consumed. A rejected command consumes neither economy nor randomness and does not advance the turn. A successful command atomically pays all costs, sets cooldowns, applies events, and advances or retains priority as declared by the ability. In v1, every normal command ends the turn after one action; the richer economy is present in the state so later rulesets can permit bonus actions without a state migration.

Cooldown values are remaining eligible turns, not wall-clock time. A cooldown is set only after an ability successfully resolves. Resources satisfy `0 <= current <= max`, and costs are paid with checked subtraction.

### 4.5 Legal actions and targeting

The engine is the only authority for legality:

```rust
pub fn legal_commands(
    rules: &CombatRuleset,
    state: &CombatState,
    actor: CombatantId,
) -> Result<Vec<CommandTemplate>, CombatError>;

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum CombatCommand {
    Attack { ability: AbilityId, target: CombatantId },
    Defend { stance: AbilityId },
    UseAbility { ability: AbilityId, targets: Vec<TargetRef> },
    UseItem { item: ItemId, targets: Vec<TargetRef> },
    Flee { route: RetreatRouteId },
    Target { target: TargetRef },
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum TargetRef {
    Combatant(CombatantId),
    Zone(ZoneId),
    Self_,
}
```

`Target` sets an explicit committed focus used only by abilities whose targeting rule allows `CurrentTarget`; it never causes damage by itself. Prefer commands carrying their target directly. This avoids mutable conversational pronouns such as “hit it” affecting replay.

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct TargetRule {
    pub kind: TargetKind,
    pub faction: FactionFilter,
    pub life: LifeFilter,
    pub range: RangeRule,
    pub min: u8,
    pub max: u8,
    pub unique: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum RangeRule {
    SelfOnly,
    SameZone,
    AdjacentZone,
    WithinHops(u8),
    Any,
}
```

Target lists are canonicalized only if the ability declares order-insensitivity; otherwise authored order is meaningful and committed. Validation happens before draw planning. Each target must exist, satisfy faction/life/range filters, and be unique where required. Area selection expands to affected combatants in ascending `CombatantId` order.

### 4.6 Stats, hit, defense, and damage

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct CombatStats {
    pub max_hp: u32,
    pub attack: i32,
    pub armor: i32,
    pub initiative: i32,
    pub accuracy: i32,
    pub evasion: i32,
    pub power: i32,
    pub resistance: BTreeMap<DamageType, i16>, // basis points, validated range
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct DamageSpec {
    pub dice: FixedDice,
    pub flat: i32,
    pub scaling: ScalingStat,
    pub damage_type: DamageType,
    pub armor_rule: ArmorRule,
    pub minimum_on_hit: u16,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct FixedDice {
    pub count: u8,
    pub sides: u16,
}
```

The default v1 formula is intentionally auditable:

```text
attack_total  = d20 + attacker.accuracy + ability.hit_bonus
defense_total = 10 + defender.evasion + active_defense_bonus
hit           = attack_total >= defense_total

raw_damage    = sum(fixed damage dice) + flat + selected attacker scaling stat
armor_reduced = max(0, raw_damage - effective_armor)       // for ArmorRule::Flat
resisted      = floor(armor_reduced * (10_000 - resistance_bps) / 10_000)
final_damage  = max(minimum_on_hit, resisted)              // only after a hit
new_hp        = old_hp.saturating_sub(final_damage)
```

Natural criticals are not implicit. An ability that can crit declares a `CritRule`; its damage-draw count is still fixed. For example, “double dice on natural 20” always draws the base and critical dice, then ignores the critical portion on a non-critical hit. Misses likewise still consume all predeclared damage draws. This prevents draw-count branching.

Defense is derived from committed stats and active statuses. `Defend` normally applies a status such as `guarded` and ends the turn; the status definition supplies its defense modifier and expiry. Armor and resistance ranges are ruleset-validated. Healing is a separate effect and cannot be represented as negative damage.

### 4.7 Status stacks

Existing Shield and Poison timed flags become built-in status definitions with compatibility adapters.

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct StatusStack {
    pub status: StatusId,
    pub source: CombatantId,
    pub stacks: u16,
    pub potency: i32,
    pub remaining: Duration,
    pub applied_serial: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum Duration {
    Permanent,
    Turns(u16),
    Rounds(u16),
    UntilTurnStart(CombatantId),
    UntilTurnEnd(CombatantId),
    Charges(u16),
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum StackPolicy {
    UniqueRefresh,
    AddStacks { max: u16 },
    ReplaceIfStronger,
    Independent { max_instances: u16 },
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct StatusDef {
    pub id: StatusId,
    pub policy: StackPolicy,
    pub triggers: Vec<StatusTrigger>,
    pub modifiers: Vec<StatModifier>,
    pub tags: BTreeSet<StatusTag>,
}
```

Trigger execution order is deterministic: phase order, then status priority from the ruleset, then `StatusId`, source `CombatantId`, and `applied_serial`. A status cannot execute arbitrary code. It is composed from a closed effect algebra:

```rust
pub enum RuleEffect {
    DealDamage(DamageEffect),
    Heal(HealEffect),
    ApplyStatus(ApplyStatusEffect),
    RemoveStatus(RemoveStatusEffect),
    ModifyResource(ResourceEffect),
    MoveZone(MoveZoneEffect),
    SetCooldown(CooldownEffect),
    EmitFlag(FlagEffect),
}
```

Any stochastic trigger declares a fixed draw cost in its definition. To prevent unbounded trigger loops, status-triggered effects do not recursively trigger the same `(event_serial, status instance, trigger kind)` tuple, and each transition has a ruleset-wide maximum event count validated before commitment.

Compatibility mapping:

- `Shield(n turns)` -> `StatusId("shield")`, `UniqueRefresh`, defense/absorption modifier, `Turns(n)`.
- `Poison(n turns, potency)` -> `StatusId("poison")`, stacking policy chosen by the legacy adapter, `TurnStart` deterministic poison damage, `Turns(n)`.

### 4.8 Defeat, retreat, and rewards

When HP reaches zero, a combatant changes to the ruleset-defined zero-HP state (`Downed` or `Defeated`). The engine immediately checks terminal predicates after the complete atomic effect batch, not between dice within one ability.

Retreat is an ability-like command with a target route, cost, eligibility predicate, and fixed draw plan. A successful escape marks the actor `Withdrawn`; it does not delete them. Party retreat is terminal when the encounter's retreat predicate is satisfied. Failed retreat consumes the declared action and draws.

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct TerminalRules {
    pub victory: Predicate,
    pub defeat: Predicate,
    pub retreat: Option<RetreatRules>,
    pub max_rounds: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct RewardBundle {
    pub items: BTreeMap<ItemId, u16>,
    pub flags: BTreeSet<WorldFlag>,
    pub currency: BTreeMap<CurrencyId, u32>,
    pub grants: Vec<CapabilityGrant>,
}
```

Rewards are committed at encounter creation but materialize only once on the qualifying terminal transition. They become ordinary cap-gated `WorldEffect`s. The resolver validates capabilities before landing them. A receipt commits both the proposed reward events and the actually authorized world effects, so a replay can distinguish combat victory from effect authorization.

## 5. Typed command surface without a new `GameAction` variant

Rich combat commands ride the existing `GameAction::Use`, matching spell/item use and preserving the closed five-variant `GameAction` enum.

The recommended representation is a versioned, typed reserved payload, not a magic prose string:

```rust
pub enum UseTarget {
    World(ExistingUseTarget),
    Combat(CombatUse),
}

pub struct CombatUse {
    pub encounter: EncounterId,
    pub actor: CombatantId,
    pub command: CombatCommand,
}

// Existing top-level variant; field names are illustrative.
GameAction::Use {
    subject: UseSubject::CombatCommand,
    target: UseTarget::Combat(CombatUse { /* ... */ }),
}
```

If changing the internal `Use` payload would disturb serialization, encode the same structure as a versioned `UseInvocation::CombatV1` alongside the legacy representation and preserve old decoding. Do not encode commands as natural-language verbs.

Dispatch is scoped:

1. If no combat is active, legacy `Use` behavior is unchanged.
2. If combat is active and the payload is `CombatV1`, dispatch to `resolve_combat_command`.
3. If combat is active and the payload is an ordinary consumable, adapt it to `CombatCommand::UseItem` only when the committed item definition is combat-usable; otherwise reject it without draws.
4. Existing `GameAction::Attack` dispatches through the legacy adapter described below.

The parser may translate “guard,” “drink potion,” or “strike goblin” into a typed `CombatUse`, but the resolver returns the canonical legal result. On ambiguity, parsing fails or requests a target; it never lets narration choose implicitly.

Resolution returns semantic events suitable for flavor generation:

```rust
pub struct CombatTransition {
    pub prior_state_hash: Hash32,
    pub next_state: CombatState,
    pub events: Vec<CombatEvent>,
    pub world_effects: Vec<WorldEffect>,
    pub draw_manifest: DrawManifest,
}

pub enum CombatEvent {
    TurnStarted { actor: CombatantId },
    AbilityUsed { actor: CombatantId, ability: AbilityId },
    HitChecked { attacker: CombatantId, target: CombatantId, total: i32, defense: i32, hit: bool },
    DamageApplied { source: CombatantId, target: CombatantId, kind: DamageType, amount: u32, hp_after: u32 },
    StatusApplied { target: CombatantId, status: StatusId, stacks: u16 },
    ResourceSpent { actor: CombatantId, resource: ResourceId, amount: u16 },
    CombatantDefeated { combatant: CombatantId },
    CombatEnded { outcome: CombatOutcome },
}
```

Narration consumes these events after the receipt candidate is finalized. Narration text may be committed as presentation metadata, but it never feeds back into the state hash.

## 6. Verified randomness and replay

### 6.1 Fixed draw manifests

Every accepted transition has a draw plan derivable from only the pre-state, command, and committed ruleset. Validation and draw planning occur before any draw is consumed.

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct DrawManifest {
    pub stream_id: Hash32,
    pub start_index: u64,
    pub uses: Vec<DrawUse>,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct DrawUse {
    pub relative_index: u32,
    pub purpose: DrawPurpose,
    pub bound: NonZeroU32,
    pub value: u32,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub enum DrawPurpose {
    Initiative { combatant: CombatantId },
    Hit { ability: AbilityId, target: CombatantId },
    DamageDie { ability: AbilityId, target: CombatantId, die: u8 },
    CriticalDie { ability: AbilityId, target: CombatantId, die: u8 },
    Save { status: StatusId, target: CombatantId },
    Retreat { combatant: CombatantId },
    LootChoice { table: LootTableId, slot: u8 },
}
```

The plan declares exact purpose, order, bound, and count. Uses are contiguous from `start_index`; a transition cannot skip, duplicate, or consume an undeclared index. Bounded draws use the reject-free unbiased primitive supplied by `dregg-dice`; the combat engine must not implement modulo reduction or rejection sampling.

Initiative consumes one draw per eligible participant in ascending `CombatantId` order. Ability targets expand before planning, in canonical order. A hit ability consumes its hit and all possible damage/critical/status-save draws whether it hits or misses. Conditional effects select among already-drawn values rather than changing the count. Content whose maximum fixed plan cannot be derived is invalid.

```rust
pub trait CombatDraws {
    fn take(&mut self, purpose: DrawPurpose, bound: NonZeroU32)
        -> Result<u32, CombatError>;
    fn position(&self) -> u64;
}
```

The receipt binds the `dregg-dice` proof/commitment, stream identity, start/end indices, manifest, prior and next combat-state hashes, command, ruleset root, encounter root, semantic events, and authorized world effects.

### 6.2 Replay

`verify_replay` performs, for every combat receipt:

1. verify the hash-chain link and prior world/combat roots;
2. load the exact combat ruleset by `combat_ruleset_root` and encounter by `encounter_root`;
3. verify the `dregg-dice` stream proof and each indexed bounded value;
4. derive the expected draw plan from the pre-state and command;
5. require exact equality with the committed manifest;
6. re-run `resolve_combat_command` using a cursor over those verified draws;
7. require exact equality of events, world effects, next state, and hashes;
8. apply the ordinary capability checks for landed `WorldEffect`s.

Engine version is committed in each state/receipt. Historical versions remain replayable; a ruleset upgrade cannot reinterpret an old fight.

### 6.3 Crisp invariants

The implementation and property tests enforce:

1. **Turn authority:** an accepted command's actor equals `phase.Acting.actor`, except an explicitly modeled reaction whose trigger and reaction window are committed.
2. **Closed legality:** every accepted command appears in, or is an exact instantiation of, `legal_commands(pre_state, actor)`.
3. **Eligible targets:** every target exists and satisfies the ability's committed target rule at validation time.
4. **Atomic costs:** resources and economy are sufficient before resolution and never become negative or exceed their maxima.
5. **Committed derivation:** damage, healing, status potency, hit totals, and saves derive only from the pre-state, command, ruleset/encounter content, and verified declared draws.
6. **Fixed randomness:** accepted commands consume exactly their derived contiguous draw manifest; rejected commands consume zero draws.
7. **No hidden entropy:** time, process RNG, iteration order, AI text, locale, floating point, and external mutable state cannot affect transitions.
8. **HP bounds:** `0 <= hp <= max_hp`; damage cannot increase HP and healing cannot deal damage.
9. **Monotone serials:** turn and event serials strictly advance according to the transition rules and never wrap.
10. **Terminal finality:** terminal combat accepts no commands and grants rewards at most once.
11. **Deterministic ordering:** initiative ties, area targets, simultaneous statuses, loot slots, and effects have explicit total ordering.
12. **Replay identity:** equal pre-state, engine version, roots, command, and verified draws produce byte-identical canonical transition output.

## 7. Data-driven committed ruleset

### 7.1 Ruleset structure

```rust
#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct CombatRuleset {
    pub schema_version: u16,
    pub engine_version: CombatEngineVersion,
    pub initiative: InitiativeRules,
    pub damage: DamageRules,
    pub abilities: BTreeMap<AbilityId, AbilityDef>,
    pub statuses: BTreeMap<StatusId, StatusDef>,
    pub items: BTreeMap<ItemId, CombatItemDef>,
    pub enemies: BTreeMap<EnemyArchetypeId, CombatantDef>,
    pub loot_tables: BTreeMap<LootTableId, LootTable>,
    pub limits: CombatLimits,
}

#[derive(Clone, Debug, Eq, PartialEq, Encode, Decode)]
pub struct AbilityDef {
    pub id: AbilityId,
    pub tags: BTreeSet<AbilityTag>,
    pub cost: ActionCost,
    pub cooldown_turns: u16,
    pub target: TargetRule,
    pub hit: Option<HitRule>,
    pub effects: Vec<RuleEffect>,
    pub draw_shape: DrawShape,
}
```

`combat_ruleset_root = H(domain_separator || canonical_encode(ruleset))`. The encounter root commits the expanded encounter declaration and references the ruleset root. The compiler verifies all references, bounds, stack caps, draw shapes, trigger limits, loot quantities, and arithmetic ranges.

Rules are data, but the effect language is closed. Arbitrary Lua/Wasm/host callbacks are excluded because they make totality, draw planning, and historical replay substantially harder. New mechanics require a versioned engine/effect-algebra addition.

### 7.2 `.dungeon` declarations

Illustrative syntax (the precise parser grammar may follow existing DSL conventions):

```dungeon
combat_ruleset "core-v1" {
  initiative die d20

  status guarded {
    stack unique_refresh
    duration until_owner_turn_start
    modifier defense +2
  }

  status poison {
    stack add max 5
    duration turns 3
    on turn_start damage 1d4 type poison per_stack
    draws fixed 1_per_instance
  }

  ability strike {
    cost action 1
    target enemy living same_or_adjacent_zone count 1
    hit d20 + accuracy vs 10 + evasion
    damage 1d8 + power type physical armor flat minimum 1
    draws { hit 1; damage 1; }
  }

  ability guard {
    cost action 1
    target self
    apply_status guarded potency 2
    draws none
  }

  ability venom_bite {
    cost action 1
    cooldown turns 2
    target enemy living same_zone count 1
    hit d20 + accuracy vs 10 + evasion
    damage 1d6 + power type piercing armor flat minimum 1
    on_hit apply_status poison stacks 1 potency 1 duration turns 3
    draws { hit 1; damage 1; }
  }

  enemy cave_viper {
    hp 18
    stats { attack 2; armor 1; initiative 4; accuracy 3; evasion 2; power 2; }
    abilities [venom_bite, guard]
    resources {}
  }

  loot_table viper_cache fixed {
    item antidote quantity 1
    currency coin quantity 8
  }
}

encounter "viper-den" ruleset "core-v1" {
  trigger enter room "den"
  zone mouth adjacent [nest]
  zone nest adjacent [mouth]

  party player spawn mouth faction heroes
  spawn cave_viper as "den-viper" zone nest faction hostiles

  victory all faction hostiles defeated
  defeat all faction heroes defeated
  retreat faction heroes via mouth check d20 + initiative vs 12
  rewards loot viper_cache
  on_victory set_flag "viper_defeated"
}
```

Loot should be fixed by default. Random loot tables must declare a fixed number of slots and one bounded draw per slot; empty outcomes are explicit entries. No weighted selection may use rejection sampling or a variable number of draws.

The compiler emits canonical ruleset and encounter blobs plus their roots. Receipts reference roots, never filesystem paths or mutable symbolic “latest” versions.

## 8. Compatibility and migration

### 8.1 Legacy `CombatEnemy` as a degenerate encounter

The current one-enemy model is adapted, not replaced:

```rust
pub fn legacy_encounter(enemy: &CombatEnemy) -> ExpandedEncounter {
    ExpandedEncounter {
        participants: vec![
            legacy_player_combatant(),
            CombatantDef {
                max_hp: enemy.hp,
                attack: enemy.attack,
                armor: enemy.armor,
                abilities: vec![
                    legacy_enemy_attack(enemy.weapon_damage, enemy.unarmed_damage),
                ],
                ..legacy_defaults()
            },
        ],
        victory_rewards: RewardBundle {
            flags: [enemy.victory_flag.clone()].into_iter().collect(),
            ..Default::default()
        },
        mode: EncounterMode::LegacyRound,
        ..legacy_encounter_defaults()
    }
}
```

`EncounterMode::LegacyRound` is a committed compatibility ruleset, not a second ad hoc resolver. It encodes the present Attack round semantics: the player attack and enemy response occur in the same accepted legacy transition, using the same formulas and draw behavior as today. This is important: silently inserting initiative commands or extra player turns would change existing games.

Existing `GameAction::Attack` follows this path:

- if its target is a legacy `CombatEnemy`, lazily create or resume the degenerate encounter;
- execute the compatibility `legacy_attack_round` ability;
- project HP and wounds back into the same existing world fields/flags;
- on defeat, emit the existing `victory_flag` effect;
- preserve current receipt-visible outcomes and draw semantics under the legacy engine version.

Existing Shield/Poison flags are imported into status stacks on encounter entry and projected back on exit or after each legacy round, as needed for old save formats. Consumables continue through existing `Use` behavior unless they opt into a combat item definition.

### 8.2 Versioning strategy

Add fields with defaults and tagged decoding:

```rust
pub enum EncounterMode {
    LegacyRound,
    TacticalV1,
}

pub enum CombatEngineVersion {
    Legacy0,
    Tactical1,
}
```

Old dungeon files compile exactly as before and implicitly use `Legacy0`. Only a new `combat_ruleset` or tactical `encounter` declaration selects `Tactical1`. Old receipts verify through `Legacy0`; new code must retain that verifier. No bulk content migration is required for the five existing games.

Compatibility tests should pin canonical fixtures for each existing game: parsed action, draw manifest, effects, terminal flag, and receipt hash/replay result. This is the release gate for enabling the new subsystem.

## 9. Resolver integration

The world resolver remains the sole entry point:

```rust
pub fn resolve_action(
    map: &DungeonMap,
    world: &WorldState,
    action: &GameAction,
    draws: &mut VerifiedDrawCursor<'_>,
) -> Result<ResolvedAction, ResolveError> {
    match combat_dispatch(map, world, action)? {
        CombatDispatch::NotCombat => resolve_existing_action(map, world, action, draws),
        CombatDispatch::Legacy(input) => resolve_legacy_combat(map, world, input, draws),
        CombatDispatch::Tactical(input) => resolve_tactical_combat(map, world, input, draws),
    }
}
```

Combat state should live in a namespaced world component, committed by the ordinary world-state root. `WorldEffect::SetCombatState` (or an equivalent typed internal effect) is cap-gated to the combat resolver; authored AI output cannot directly construct it. External effects such as wounds, inventory consumption, movement after retreat, and victory flags remain normal `WorldEffect`s and retain their existing capability checks.

The receipt should include a combat extension:

```rust
pub struct CombatReceiptData {
    pub engine_version: CombatEngineVersion,
    pub ruleset_root: Hash32,
    pub encounter_root: Hash32,
    pub prior_combat_hash: Hash32,
    pub next_combat_hash: Hash32,
    pub command: Option<CombatCommand>,
    pub draw_manifest: DrawManifest,
    pub events_root: Hash32,
}
```

For non-combat actions this extension is absent. For legacy receipts, preserve the old encoding; the compatibility verifier may internally reconstruct equivalent combat inputs without changing historical bytes.

## 10. Failure model

Errors are typed and deterministic:

```rust
pub enum CombatError {
    NoActiveEncounter,
    WrongEncounter,
    NotActorsTurn { expected: CombatantId, actual: CombatantId },
    UnknownCombatant(CombatantId),
    UnknownAbility(AbilityId),
    IllegalTarget { target: TargetRef, reason: TargetError },
    InsufficientEconomy,
    InsufficientResource(ResourceId),
    OnCooldown { ability: AbilityId, remaining: u16 },
    InvalidLifeState(LifeState),
    DrawPlanMismatch,
    DrawStreamExhausted,
    RulesetInvalid(RulesetError),
    ArithmeticOverflow,
    TerminalEncounter,
    EffectLimitExceeded,
}
```

Failures before transition finalization produce no combat mutation, no world effects, and no draw consumption. Whether rejected attempts are separately hash-chained as non-state-changing receipts is a platform policy; if they are, the receipt commits the typed error and an empty draw manifest.

## 11. Phased build plan

### Phase 0: freeze compatibility

- Add golden replay fixtures for the five existing games and their `Attack`, Shield/Poison, consumable, wound, and victory-flag behavior.
- Document current random draw counts and receipt encodings.
- Introduce engine-version tags without changing serialized legacy output.

Exit gate: byte/semantic compatibility tests and existing replay tests are green.

### Phase 1: smallest tactical vertical slice (one day)

Build one 1v1 encounter with fixed initiative and ability definitions:

- `CombatState`, `Creating -> Initiative -> Acting -> Terminal`;
- two combatants, one zone, stable initiative (`1d20 + initiative`, ID tie-break);
- `strike` and `guard` abilities;
- one action per turn, HP, armor/evasion, and a cooldown/resource-ready data shape;
- typed `CombatCommand` carried by `GameAction::Use`;
- fixed hit plus damage manifests, consuming damage draws even on miss;
- victory terminal state and one flag reward;
- combat receipt extension and `verify_replay` re-execution;
- legacy `Attack` left untouched behind dispatch.

This slice deliberately omits items, retreat, multi-targeting, random loot, and general status triggers. `guard` may be a single built-in status. It is useful end to end and proves the hard boundary: typed intent -> declared verified draws -> deterministic transition -> replay-identical receipt.

Suggested implementation order:

1. Define canonical types and hashing.
2. Implement ruleset validation and two in-memory ability definitions.
3. Implement draw planning, then transition execution against a manifest cursor.
4. Add `UseInvocation::CombatV1` dispatch.
5. Bind transition data into receipts and replay.
6. Add deterministic unit/property tests and a small `.dungeon` fixture.

Exit gate: a complete 1v1 fight can be replayed from receipts alone, altered draw values or commands fail verification, out-of-turn/invalid-target commands consume zero draws, and existing games remain byte/behavior compatible.

### Phase 2: authored rules and status engine

- Add `.dungeon` ruleset/encounter parsing and canonical compilation.
- Add the closed `RuleEffect` algebra.
- Generalize Shield/Poison into deterministic stacks, durations, modifiers, and bounded triggers.
- Add consumable combat items, resources, and cooldown enforcement.
- Add ruleset linting for fixed draw shapes and arithmetic/event bounds.

Exit gate: all rules are root-committed, malformed/unbounded content fails compilation, and status ordering has permutation/property tests.

### Phase 3: tactical breadth

- Add zones, range, movement economy, multi-target and area abilities.
- Add downed/revive rules, explicit reactions, and retreat routes.
- Add fixed-slot verified loot tables.
- Expose `legal_commands` for UI/AI grounding.

Exit gate: target eligibility and effect ordering remain deterministic under randomized map/participant insertion order.

### Phase 4: legacy unification

- Route current `CombatEnemy` through `LegacyRound` adapter internally.
- Import/project Shield, Poison, wounds, consumables, and victory flags.
- Compare adapter output against Phase 0 fixtures.
- Keep the old verifier and encoding for historical receipts.

Exit gate: no changes are required in the five existing games, all pinned fixtures match, and new tactical encounters coexist with legacy enemies in one map.

### Phase 5: hardening and optimization

- Property-test replay identity, resource/HP bounds, target legality, and draw contiguity.
- Fuzz ruleset decoding and command validation.
- Add denial-of-service limits for participants, statuses, targets, rounds, and effects.
- Cache ruleset validation by root without making cache state semantically observable.
- Produce audit tooling that renders each receipt's formulas and draw purposes.

## 12. Test strategy

Minimum test families:

- table tests for hit, armor, resistance, minimum damage, and fixed-point rounding;
- initiative tie tests and insertion-order independence tests;
- invalid action tests proving zero state/draw changes;
- status-stack and trigger-order tests;
- property tests for HP/resource bounds and deterministic canonical encoding;
- manifest tests proving exact contiguous indices and fixed count on hit/miss/crit branches;
- replay mutation tests changing one stat, target, draw, bound, index, ruleset byte, event, or effect;
- terminal/reward idempotence tests;
- golden compatibility fixtures for all existing games.

The most valuable end-to-end assertion is:

```rust
let live = resolve_combat_command(pre, command, verified_draws)?;
let receipt = finalize_receipt(pre, command, live)?;
let replayed = verify_replay(genesis, receipts_through(&receipt))?;
assert_eq!(replayed.world_root, receipt.next_world_root);
assert_eq!(replayed.combat_hash, receipt.combat.next_combat_hash);
```

## 13. Final recommendations

1. Keep `GameAction` closed and carry a versioned `CombatCommand` through `Use`.
2. Model tactical combat as a committed sub-state of the world, not conversational session state.
3. Snapshot combatants at encounter creation and derive every outcome from that snapshot, committed rules, typed commands, and verified indexed draws.
4. Require fixed draw manifests. Consume all declared branch draws even when their branch is not taken.
5. Use a closed effect algebra and integer arithmetic; reject arbitrary scripts and floats.
6. Preserve current `Attack` semantics with a versioned `LegacyRound` degenerate encounter before attempting internal unification.
7. Ship the one-day 1v1 vertical slice first. It validates the architecture without putting the existing five games at risk.

This design makes combat richer without weakening the project's governing rule: the AI narrates, but the committed world resolves.

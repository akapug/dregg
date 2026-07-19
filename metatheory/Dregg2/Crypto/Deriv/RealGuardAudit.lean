/-
# Dregg2.Crypto.Deriv.RealGuardAudit — the decision procedure pointed at REAL dregg guards.

Every guard below traces to a real authored site (file:line cited at each `def`); none is a toy
minted for this module. The questions asked are the two the decision answers:

* SATISFIABILITY — `emptyFix cands fuel R`: `some false` = a satisfying frame EXISTS (the guard can
  fire); `some true` = the guard can NEVER fire at any word length (a brick, if the author expected
  it to fire); `none` = the worklist did not saturate in `fuel` (never happens below).
* EQUIVALENCE — `emptyFix` on `symDiff R S`: `some true` = the two spellings accept EXACTLY the
  same transitions; `some false` = a separating frame exists.
* SUBSUMPTION — `emptyFix` on `R ⋒ ¬S`: `some true` = every `R`-witness satisfies `S`.

RESOURCE DISCIPLINE (the 64GB/20min lesson, `SymbolicIntervals.lean` §6): everything here is the
CHEAP Bool-level route — raw `emptyFix` over the same candidate covers the proven decisions use
(`scalarCands` from `scalarLeaves?`, `atomCands` via `fixCands`), fired by `#guard` (compiled
evaluation). NO `@decide` / `of_decide_eq_*` through a `Decidable` instance anywhere in this file.
The verdicts inherit their meaning from the PROVEN cover + fixpoint theorems
(`emptyFix_some_iff`, `coverOfScalars`, `predRE_emptiness_decidable_cover`) without kernel-reducing
the instances.

## Semantic resolution (say it before quoting a verdict)

* The Lean atoms evaluate over `Int` records with absence (fail-closed); the Rust executor
  evaluates `FieldElement` (mod-p, u64 projections) over always-present slots. A verdict here is
  at `Int`-record resolution — the §2.3 field-vs-Int frontier of
  `docs/DESIGN-predicate-usefulness-targets.md` stands. For the small game/credential constants
  below (0..20, 18) the two agree; no verdict below leans on wraparound.
* Satisfiability is PER-FRAME ("does a post-state satisfying the guard exist"), not reachability
  ("can play reach it") — reachability is the trace-level question, out of scope by design (§2.2).

## FINDINGS (the honest summary — details at each guard)

Run on 15 in-fragment real guards (13 scalar, 2 pin): ALL SATISFIABLE — no never-firing guard, no
contradictory conjunction. The claimed goad/friendly mutual exclusion DECIDES as genuinely
exclusive; the executor-vs-renderer duplicate gate (dialogue.rs writes the SAME rule twice, once
as StateConstraints and once as plain Rust) DECIDES equivalent (non-syntactically — the conjuncts
are commuted); the age-predicate mismatch the anonymity test stages DECIDES non-equivalent with
subsumption exactly one-way. No two distinct real guards decided accidentally equivalent.

ONE decision-caught subtlety (§6a): the goad gate is authored as the hand-derived complement
`FieldLte(disposition, FLOOR - 1)` of the friendly floor `FieldGte(disposition, FLOOR)` — and the
decision says those spellings are NOT complements on the record substrate: they differ exactly on
the absent-`disposition` frame (the atom fails closed; the negation admits). Equivalent under a
presence restriction, and the deployed 8-slot Rust cell always has the field present, so this is
NOT a live bug there — it is a real semantic edge the doc-comments do not mention, surfaced by the
decision rather than by reading. Everything else: audited guards are correct as written, and this
file is the evidence, not a trophy.
-/
import Dregg2.Crypto.Deriv.PredicateLibrary
import Dregg2.Crypto.Deriv.SymbolicIntervals

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (derives null rigidRE)

namespace RealGuardAudit

/-- The candidate cover for a scalar-fragment guard — exactly the frames the PROVEN scalar
decision (`predRE_emptiness_decidable_scalar`) runs its worklist on (`coverOfScalars`' `.cands`).
Empty only outside the fragment, and every use below is behind a `scalarRE` membership witness. -/
def scalarFixCands (R : PredRE) : List Value :=
  match scalarLeaves? (leavesOf R) with
  | some A => scalarCands A
  | none   => []

/-! ## §1 The real guards — scalar (interval) fragment.

Vigil dialogue teeth (`dungeon-on-dregg/src/dialogue.rs`). Slots are compiled cell indices;
we name them by their scene variable (the compiler's `var_slots` key, `vigil_slot`). -/

/-- `disposition ≤ 3` — the GOAD gate: a warmed Keeper refuses the threat.
`dungeon-on-dregg/src/dialogue.rs:265-268` (`FieldLte { disposition,
HISTORY_DISPOSITION_FLOOR - 1 }`, floor = 4 at `:198`). -/
def goadGate : PredRE := .sym (.atom (.simple (.fieldLe "disposition" 3)))

/-- `disposition ≥ 4` — the friendly-topic warmth floor, compiler-emitted from the
designer-authored scene condition `{ disposition >= 4 }` (`dialogue.rs:147`; floor const `:198`;
compile-check `:540-543`). -/
def friendlyFloor : PredRE := .sym (.atom (.simple (.fieldGe "disposition" 4)))

/-- `menace = 0` — never-goaded: a goad permanently closes the friendly topic
(`dialogue.rs:279-283`, `FieldEquals { menace, 0 }`). -/
def neverGoaded : PredRE := .sym (.atom (.simple (.fieldEquals "menace" 0)))

/-- The full decidable slice of the LN_ASK_HISTORY case: compiled floor ∧ augmented never-goaded
(`dialogue.rs:274-283`; the case also carries a `WriteOnce`, which is reactive — §3). -/
def askHistoryGate : PredRE :=
  .sym (.and (.atom (.simple (.fieldGe "disposition" 4)))
             (.atom (.simple (.fieldEquals "menace" 0))))

/-- `disposition ≥ 5` — the grant's warmth atom (`dialogue.rs:315-319`,
`FieldGte { disposition, GRANT_DISPOSITION_FLOOR }`, floor = 5 at `:201`). -/
def grantWarmth : PredRE := .sym (.atom (.simple (.fieldGe "disposition" 5)))

/-- `disposition ≥ 5 ∧ topic_secret ≥ 1` — the LN_BEG_LEAVE GRANT gate (warmth AND the secret),
`dialogue.rs:313-323`; re-stapled onto every `passage_open`/`oil_given` write by the
`SlotChanged`-bound copy at `:341-352`. Two-field: rides the per-field product cover. -/
def grantGate : PredRE :=
  .sym (.and (.atom (.simple (.fieldGe "disposition" 5)))
             (.atom (.simple (.fieldGe "topic_secret" 1))))

/-- `passage_open ≥ 1` — the crossing gate, compiled from the scene condition
`{ passage_open >= 1 }` (`dialogue.rs:160`, doc `:189-192`). -/
def crossGate : PredRE := .sym (.atom (.simple (.fieldGe "passage_open" 1)))

/-! Bloodgate Trial stakes (`dungeon-on-dregg/src/bloodgate.rs`). -/

/-- `hp ≥ 1` — the survival floor on both trade blows: a blow you could not survive is refused
(compiler-lifted; asserted `bloodgate.rs:579-589`). -/
def survivalFloor : PredRE := .sym (.atom (.simple (.fieldGe "hp" 1)))

/-- `warden_hp ≤ 0` — the finish gate: felling the not-yet-beaten Warden is refused
(`bloodgate.rs:591-598`). -/
def finishGate : PredRE := .sym (.atom (.simple (.fieldLe "warden_hp" 0)))

/-- `hp ≤ 20` — the fall gate: you can only fall once too hurt to fight on
(`bloodgate.rs:600-606`; doc `:177-178`). -/
def fallGate : PredRE := .sym (.atom (.simple (.fieldLe "hp" 20)))

/-- `hands ≥ 2` — the hoard-stair gate: opens for the KEY (2), not the crown (1)
(designer-authored `{ hands >= 2 }` at `bloodgate.rs:146`; asserted `:626-632`). -/
def hoardStair : PredRE := .sym (.atom (.simple (.fieldGe "hands" 2)))

/-! Credential predicate requests (`credentials/`, T4 of the design doc). -/

/-- `age ≥ 18` — the canonical relying-party request
(`credentials/tests/roundtrip.rs:186`, `PredicateRequest::new("age", Predicate::Gte(18))`). -/
def ageGte18 : PredRE := .sym (.atom (.simple (.fieldGe "age" 18)))

/-- `age ≥ 1` — the holder-presented predicate the anonymity test stages AGAINST the `≥ 18`
expectation (`credentials/tests/anonymity_soundness.rs:242`). -/
def ageGte1 : PredRE := .sym (.atom (.simple (.fieldGe "age" 1)))

/-- `clearance_level ≥ 1` — a second real attribute predicate
(`credentials/tests/anonymity_soundness.rs:278`). -/
def clearanceGte1 : PredRE := .sym (.atom (.simple (.fieldGe "clearance_level" 1)))

-- All thirteen scalar guards are IN the interval fragment (computable membership, fail-closed):
#guard scalarRE goadGate && scalarRE friendlyFloor && scalarRE neverGoaded
    && scalarRE askHistoryGate && scalarRE grantWarmth && scalarRE grantGate
    && scalarRE crossGate && scalarRE survivalFloor && scalarRE finishGate
    && scalarRE fallGate && scalarRE hoardStair
    && scalarRE ageGte18 && scalarRE ageGte1 && scalarRE clearanceGte1

/-! ## §2 The real guards — pin (symbolic) fragment.

Audience routing (`cell/examples/predicate_language.rs`, the canonical T1 worked example).
The Rust `FieldElement` identities are modeled as digest pins (`digEq`). -/

/-- `audience = 0xA11CE` — exact audience routing: drop messages not addressed to self
(`cell/examples/predicate_language.rs:37-41`, `FieldEquals { 0, self_id }`). -/
def audienceExact : PredRE := .sym (.digEq "audience" 0xA11CE)

/-- `audience ∈ {0xA11CE, 0xB0B}` — the `AnyOf`-over-identities allowlist
(`cell/examples/predicate_language.rs:63-71`). -/
def audienceAnyOf : PredRE :=
  .sym (.or (.digEq "audience" 0xA11CE) (.digEq "audience" 0xB0B))

-- Both are pin-representable AND rigid — the fast fixpoint route applies:
#guard (atomsOfLeaves? (leavesOf audienceExact)).isSome
    && (atomsOfLeaves? (leavesOf audienceAnyOf)).isSome
    && rigidRE audienceExact && rigidRE audienceAnyOf

/-! ## §3 The real guards OUTSIDE the fragment — classified, with fail-closed witnesses.

* REACTIVE (old-vs-new): `WriteOnce` on `menace`/`topic_history`/`topic_secret`/`passage_open`/
  `oil_given` (`dialogue.rs:269,284-286,301-303,325-328`), on `downed`/`hands`
  (`bloodgate.rs:220-240`). Single-frame satisfiability would read them first-write-permissive;
  the property they encode is a TRACE invariant (§2.2 of the design doc).
* CROSS-FIELD: `BoundedBy { topic_secret ← topic_history }` (`dialogue.rs:294-303`),
  `FieldLteField { drunk ≤ held }` / `{ dc ≤ check_total }` (`bloodgate.rs:242-260`) — cross-field
  comparison over an infinite domain: no finite minterm/threshold cover exists.
* MULTI-FIELD AFFINE: `bandProgram` (`metatheory/Dregg2/Exec/Program.lean:973`,
  `affineLe [(2,bid),(-1,ask)] 100`), `consvProgram` (`:980`) — linear combinations, outside the
  per-field interval class (the QF-LIA frontier the design doc prices).
* REACTIVE+CONTEXT: the polis actor binding `AnyOf[Immutable{slot}, SenderIs{admin}]`
  (`metatheory/Dregg2/Apps/ChannelGroup.lean:115`) — `Immutable` is reactive, `SenderIs` reads
  turn context.
* CROSS-FIELD EUF: `ownerMatch`/`noSelfTransfer` (`PredicateLibrary.lean:91,95`) — wall already
  `#guard`-witnessed there.
* TYPE BOUNDARY: `Predicate::Gte(0)` on the TEXT attribute `department`
  (`credentials/tests/integration_present_verify_full.rs:257-258`) — deliberately not-a-predicate
  (the test asserts `NonPredicateAttribute`); nothing to decide.
* NOT `Pred` AT ALL: discord `RoleCapMap::holds` (`discord-bot/src/roles_caps.rs:220`) is a finite
  runtime map (decidable by enumeration, per T7); the templater guards
  (`Dregg2/Crypto/HandlebarsGuarded*.lean`) are span/delimiter guards over strings — a different
  language, not a policy `Pred`. -/

#guard scalarRE (.sym (.atom (.simple (.writeOnce "menace")))) = false
#guard scalarRE (.sym (.atom (.fieldLeField "drunk" "held"))) = false
#guard scalarRE (.sym (.atom (.fieldLeField "topic_secret" "topic_history"))) = false
#guard scalarRE (.sym (.atom (.affineLe [(2, "bid"), (-1, "ask")] 100))) = false
#guard (atomsOfLeaves? (leavesOf (.sym (.atom (.fieldLeField "dc" "check_total"))))).isSome == false

/-! ## §4 SATISFIABILITY — can each real guard EVER fire?

Verdict `some false` = NONEMPTY (a satisfying frame exists). A `some true` on any of these would
be a live bug (a gate no player/holder can ever pass). Result: ALL FIFTEEN SATISFIABLE. -/

#guard emptyFix (scalarFixCands goadGate)      128 goadGate      = some false
#guard emptyFix (scalarFixCands friendlyFloor) 128 friendlyFloor = some false
#guard emptyFix (scalarFixCands neverGoaded)   128 neverGoaded   = some false
#guard emptyFix (scalarFixCands askHistoryGate) 128 askHistoryGate = some false
#guard emptyFix (scalarFixCands grantWarmth)   128 grantWarmth   = some false
#guard emptyFix (scalarFixCands grantGate)     256 grantGate     = some false
#guard emptyFix (scalarFixCands crossGate)     128 crossGate     = some false
#guard emptyFix (scalarFixCands survivalFloor) 128 survivalFloor = some false
#guard emptyFix (scalarFixCands finishGate)    128 finishGate    = some false
#guard emptyFix (scalarFixCands fallGate)      128 fallGate      = some false
#guard emptyFix (scalarFixCands hoardStair)    128 hoardStair    = some false
#guard emptyFix (scalarFixCands ageGte18)      128 ageGte18      = some false
#guard emptyFix (scalarFixCands ageGte1)       128 ageGte1       = some false
#guard emptyFix (scalarFixCands clearanceGte1) 128 clearanceGte1 = some false
#guard emptyFix (fixCands audienceExact)       128 audienceExact = some false
#guard emptyFix (fixCands audienceAnyOf)       128 audienceAnyOf = some false

/-! ## §5 The DESIGNED exclusions and overlaps — claims in the code, now decided.

`dialogue.rs:43-45` claims the friendly and hostile paths "gate each other's lines": the goad
gate (`≤ 3`) and the full friendly gate (`≥ 4 ∧ menace = 0`) should be mutually exclusive. The
DECISION: their conjunction is EMPTY at every word length — the exclusion is real, not just
narrated. Conversely `bloodgate.rs` DESIGNS an overlap: at `hp ∈ [1, 20]` a player can both
fight (`≥ 1`) and fall (`≤ 20`) — the decision confirms the overlap band is nonempty. -/

/-- goad ∧ friendly — claimed mutually exclusive. -/
def goadVsHistory : PredRE := .inter goadGate askHistoryGate
#guard scalarRE goadVsHistory
#guard emptyFix (scalarFixCands goadVsHistory) 256 goadVsHistory = some true

/-- fight ∧ fall — designed to overlap on the `[1, 20]` band. -/
def fightOrFall : PredRE := .inter survivalFloor fallGate
#guard scalarRE fightOrFall
#guard emptyFix (scalarFixCands fightOrFall) 256 fightOrFall = some false

/-! ## §6 EQUIVALENCE — the same rule spelled twice, decided.

### 6a. The `FLOOR - 1` derivation (`dialogue.rs:268`)
The goad gate is AUTHORED as `FieldLte(disposition, HISTORY_DISPOSITION_FLOOR - 1)` — the author
computed the complement of `≥ 4` by hand as `≤ 3`. Is that spelling THE complement? The decision
says: not unconditionally. On an ABSENT `disposition` the atom `≤ 3` fails closed while
`¬(≥ 4)` admits (negation flips the fail-closed default) — so the two spellings differ exactly
on the absent-field frame, and agree everywhere the field is present. Both verdicts below are
decided, not narrated: raw pair NOT equivalent; presence-restricted pair EQUIVALENT. -/

/-- `¬(disposition ≥ 4)` — the complement spelling of the goad gate. -/
def goadAsComplement : PredRE := .sym (.not (.atom (.simple (.fieldGe "disposition" 4))))

def dGoad : PredRE := symDiff goadGate goadAsComplement
#guard scalarRE dGoad
-- NOT equivalent: the absent-`disposition` frame separates them (`≤ 3` fails closed, `¬(≥ 4)`
-- admits). Over the deployed 8-slot cell (fields always present) they agree; over the record
-- substrate the `FLOOR - 1` spelling is the STRICTER (fail-closed) one. Working as intended —
-- and the decision, not the doc-comment, is what says so:
#guard emptyFix (scalarFixCands dGoad) 256 dGoad = some false

/-- The two gates restricted to present-`disposition` frames: conjoin both spellings with a
domain guard `disposition ≥ 0 ∨ disposition ≤ 0` (present-and-scalar; total on present ints).
Under presence they ARE the same rule. -/
def dispPresent : PredRE :=
  .sym (.or (.atom (.simple (.fieldGe "disposition" 0))) (.atom (.simple (.fieldLe "disposition" 0))))
def dGoadPresent : PredRE := symDiff (.inter goadGate dispPresent) (.inter goadAsComplement dispPresent)
#guard scalarRE dGoadPresent
#guard emptyFix (scalarFixCands dGoadPresent) 512 dGoadPresent = some true

/-! ### 6b. Executor vs renderer — the SAME rule in two languages (`dialogue.rs`)
The history gate exists twice: as executor `StateConstraint`s (`:274-283`) and as the renderer's
plain-Rust availability check `menace == 0 && disposition >= HISTORY_DISPOSITION_FLOOR` (`:438`).
A drift here is a real class of bug (the NPC narrates a refusal the executor would admit, or
vice versa). The decision: EQUIVALENT — and not syntactically (the conjuncts are commuted). -/

/-- The renderer's spelling of the history gate (`dialogue.rs:438`), conjuncts in ITS order. -/
def historyRenderer : PredRE :=
  .sym (.and (.atom (.simple (.fieldEquals "menace" 0)))
             (.atom (.simple (.fieldGe "disposition" 4))))

def dHistory : PredRE := symDiff askHistoryGate historyRenderer
#guard scalarRE dHistory
#guard emptyFix (scalarFixCands dHistory) 4096 dHistory = some true

-- (The renderer's crossing check `passage_open >= 1` at `dialogue.rs:476` is the SAME AST as
-- `crossGate` — syntactic identity, nothing for the semantic decision to add. The secret-topic
-- pair (`:457` renderer `topic_history >= 1` vs executor `BoundedBy` at `:294-303`) CANNOT be
-- decided: the executor side is cross-field, out of fragment — a real pair the fragment must
-- grow to reach, named honestly.)

/-! ### 6c. The staged credential mismatch (`anonymity_soundness.rs:238-252`)
The test presents `age ≥ 1` against an expected `age ≥ 18` and REQUIRES rejection. The semantic
ground for that rejection: the two predicates are NOT equivalent, and subsumption runs exactly
one way — every `≥ 18` witness satisfies `≥ 1` (the minimal-disclosure reuse direction, T4), and
not conversely. -/

def dAge : PredRE := symDiff ageGte18 ageGte1
#guard scalarRE dAge
#guard emptyFix (scalarFixCands dAge) 256 dAge = some false          -- NOT equivalent

/-- `age ≥ 18 ⊆ age ≥ 1`: the stronger proof serves the weaker request. -/
def sAgeFwd : PredRE := .inter ageGte18 (.neg ageGte1)
#guard scalarRE sAgeFwd
#guard emptyFix (scalarFixCands sAgeFwd) 256 sAgeFwd = some true     -- subsumption HOLDS

/-- `age ≥ 1 ⊄ age ≥ 18`: the weaker proof does NOT serve the stronger request. -/
def sAgeBwd : PredRE := .inter ageGte1 (.neg ageGte18)
#guard scalarRE sAgeBwd
#guard emptyFix (scalarFixCands sAgeBwd) 256 sAgeBwd = some false    -- and only one way

/-! ### 6d. The audience widening (`predicate_language.rs:37-71`)
Exact routing vs the two-recipient allowlist: adding `0xB0B` must genuinely widen the policy
(if these decided equivalent, the `AnyOf` would be dead weight). Decision: NOT equivalent. -/

def dAudience : PredRE := symDiff audienceExact audienceAnyOf
#guard emptyFix (fixCands dAudience) 256 dAudience = some false

/-! ## §7 REDUNDANCY SWEEP — are any two distinct real guards accidentally the same policy?

Same-field neighbors and same-shape different-field pairs. All decide DISTINCT — no accidental
redundancy among the audited guards. -/

def dFloors : PredRE := symDiff friendlyFloor grantWarmth      -- `≥ 4` vs `≥ 5`, same field
#guard emptyFix (scalarFixCands dFloors) 256 dFloors = some false

def dFields : PredRE := symDiff ageGte1 clearanceGte1          -- same shape, different fields
#guard emptyFix (scalarFixCands dFields) 4096 dFields = some false

def dFlags : PredRE := symDiff crossGate ageGte1               -- `≥ 1` flags on different fields
#guard emptyFix (scalarFixCands dFlags) 4096 dFlags = some false

end RealGuardAudit

end Dregg2.Crypto.Deriv

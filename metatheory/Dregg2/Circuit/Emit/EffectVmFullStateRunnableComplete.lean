/-
# Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete — the GENERIC COMPLETENESS (`←`) leg + the
literal `⟺` for the WIDE full-state RUNNABLE descriptor, lifting the transfer completeness flagship
(`EffectVmEmitTransferComplete`) to the GENERIC `RunnableFullStateSpec St` engine.

## What the soundness engine gave and what this adds

`EffectVmFullStateRunnable.runnable_full_sound` is the SOUNDNESS half (`SAT ⟹ SEM`) over the generic
`RunnableFullStateSpec St`: a row satisfying the effect's WIDE runnable descriptor pins the FULL
17-field declarative post-state (`fullClause`), and `runnable_full_commit_binds_or_collides` is the
whole-state anti-ghost. Both are generic — every kernel-only effect tag rides them as a THIN instance
(only `decodeFull`).

This file supplies the COMPLEMENTARY half — COMPLETENESS (`SEM ⟹ SAT`) — at the SAME resolution: an
engine that turns a genuine `fullClause` (plus the honest-witness precondition `absorbsTo`) into a row
that GENUINELY SATISFIES the wide descriptor on BOTH deployed windows, and welds the two directions
into the literal biconditional `runnable_full_commit_iff`. The value the engine adds over a bespoke
per-tag completeness proof (the reusable, discharged-once crypto):

  * **the Poseidon carrier is CONSTRUCTED generically** — `wide_sites_of_carrier`: a row whose three
    GROUP-4 inter-digest aux columns hold the genuine inner `H4`s and whose `state_commit` holds their
    `H4` with the `sysRootsDigestCol` carrier SATISFIES the four wide hash sites (`wideHashSites`). The
    per-tag builder only has to FILL those aux columns honestly (mechanical — copy transfer's `semLoc`
    aux block); the site-walk is discharged here, once.
  * **the commit is FORCED to the genuine wire commit** — `runnable_forces_genuine_commit` (= the base
    `wide_commit_eq` read as a function `wireCommitOfRow`): the last window's hash-site leg pins
    `state_commit` to the genuine `H4`-of-`H4` of the 13 absorbed kernel columns + the side-table
    carrier — the SAME GROUP-4 chain the deployed prover runs. No free digest survives; the commit
    conjunct of the `⟺` bites.
  * **the `⟺` is assembled generically** — `runnable_full_commit_iff`: `→` composes `runnable_full_sound`
    with the forced commit; `←` is `runnable_full_complete`.

## The `⟺` shape is HONEST (per the transfer flagship + the non-rev template)

The commit is GATE-forced (the GROUP-4 hash sites), so a per-row `↔` is genuine here — NOT a degenerate
per-trace iff, and NOT lookup-enforced. The completeness witness is not vacuously satisfiable: the
`fullClause` gates real per-cell content (the reference instance's clause is `CellTransferSpec ∧ frozen
roots`, refutable — `canary_tamper_breaks_clause`) and the commit forces the genuine absorption
(`canary_tamper_moves_commit_or_collides`, `canary_bogus_commit_unsat`).

⚑ **WHERE THE VACUITY ACTUALLY WAS.** `runnable_full_commit_iff` itself never carried a hash floor —
it is unconditional and TRUE at deployed BabyBear parameters, as are all 17 per-tag `*_commit_iff`.
What WAS vacuous is the evidence around it: the mutation canary assumed `Poseidon2SpongeCR hash`
(FALSE at deployed parameters — `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), and so did the
whole-state anti-ghost `runnable_full_commit_binds` this file's docs cite as the meaning of the commit
conjunct. A true `⟺` whose non-degeneracy certificate is empty is the sharper form of the disease.
Both are now unconditional disjunctions naming an extracted collision pair.

## The reference instance + the demo

`transferRunnableCompleteSpec` is the VALIDATED REFERENCE `RunnableFullStateCompleteSpec CellState`:
its builder is transfer's `semTransferRow`, its completeness obligations project the (already proved)
`sem_transfer_satisfied`. `runnable_full_complete_demo` / `runnable_full_commit_iff_demo` discharge a
CONCRETE instance (`goodPre → demoPost`, `100 → 70`). Non-vacuous, both directions, canaried both ways.

## How a per-tag kernel-only instantiation looks (the follow-on fan is mechanical)

To amplify effect `X` to `air_accepts ⟺ spec` on the RUNNABLE descriptor, a farm task supplies a
`RunnableFullStateCompleteSpec` — the soundness `RunnableFullStateSpec` (already the standing pattern)
PLUS six completeness fields, all THIN because the crypto is discharged here:
  1. `buildRow`   — `X`'s witnessing row (`semLoc`-style column assignment; fill the aux GROUP-4 block
     as transfer does — the ONLY crypto touch, and `wide_sites_of_carrier` does the rest);
  2. `absorbsTo`  — `X`'s honest-witness precondition (the after-state's stored commit IS the genuine
     wire commit; the limbs are in range; the untouched roots are frozen) — the generic `hcommit`;
  3. `build_isRow` / `build_decode` — the row is an `X` row / decodes back (`X`'s `RowEncodes`);
  4. `build_carrier` — the aux GROUP-4 columns are honest (the `WideCarrier` predicate; mechanical);
  5. `build_active` / `build_last` / `build_ranges` — `X`'s per-row gates hold on the honest witness
     (the CONVERSE of `decodeFull` — `X`'s intent ⟹ its gates, e.g. transfer's `cellSpec_to_intent`
     ⟶ `transferVm_faithful.mpr`); this is `X`'s ONLY genuine per-tag proof obligation;
  6. `build_newcommit` — the row publishes `NEW_COMMIT = state_commit` (definitional).
Then `runnable_full_complete X` / `runnable_full_commit_iff X` fire with no new crypto.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; all imports
read-only; `runnable_full_sound` / `runnable_full_commit_binds` / `sem_transfer_satisfied` are
UNCHANGED (used as-is).
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmEmitTransferComplete

namespace Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (site0 site1 site2 IsTransferRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState TransferParams RowEncodes CellTransferSpec
   goodPre goodPost goodParams goodSpec_holds commitOf)
open Dregg2.Circuit.Emit.EffectVmEmitTransferComplete
  (semTransferRow sem_transfer_satisfied sem_isTransferRow sem_rowEncodes cellWireCommit demoPost)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound wideHashSites wideCommitOf wide_commit_eq
   transferVmDescriptorWide transferWide_constraints_eq TransferFullClause transferRunnableSpec
   goodPreRoots transferReference_clause_not_trivial)
open Dregg2.Circuit.Poseidon2Binding
  (Poseidon2SpongeCR SpongeColl group4Find group4Find_spec spongeColl_refutable_of_injective)
open Dregg2.Exec.SystemRoots (SysRoots)

set_option linter.unusedVariables false

/-! ## §1 — the GENERIC Poseidon-carrier constructor (the crypto, discharged once).

`WideCarrier hash env` is the honest-fill shape of the four GROUP-4 columns: the three inter-digest aux
columns hold the genuine inner `H4`s of the after-state block, and `state_after.state_commit` holds
their `H4` with the `sysRootsDigestCol` side-table carrier. `wide_sites_of_carrier` turns that into
`siteHoldsAll hash env wideHashSites` — the per-tag completeness builder fills the aux columns and the
site-walk is proved HERE, generically (the de-transfer'd `sem_sites`). -/

/-- **`WideCarrier hash env`** — the row's GROUP-4 carrier columns are honestly filled. Its four
conjuncts are exactly the four wide hash sites' defining equations read off `env.loc`; a per-tag
builder that assigns the aux block as transfer's `semLoc` does satisfies it by construction. -/
def WideCarrier (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop :=
  env.loc (auxCol aux_off.STATE_INTER1)
      = hash [env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI),
              env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0))]
  ∧ env.loc (auxCol aux_off.STATE_INTER2)
      = hash [env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2)),
              env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4))]
  ∧ env.loc (auxCol aux_off.STATE_INTER3)
      = hash [env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6)),
              env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT)]
  ∧ env.loc (saCol state.STATE_COMMIT)
      = hash [env.loc (auxCol aux_off.STATE_INTER1), env.loc (auxCol aux_off.STATE_INTER2),
              env.loc (auxCol aux_off.STATE_INTER3), env.loc sysRootsDigestCol]

/-- **`wide_sites_of_carrier` — the CONSTRUCTED Poseidon carrier (generic).** A row whose GROUP-4
columns are honestly filled (`WideCarrier`) satisfies the four wide hash sites. This is
`EffectVmEmitTransferComplete.sem_sites` lifted OFF transfer's concrete row: the site-walk over
`[site0, site1, site2, sysRootsAbsorbSite]` holds because each site's result column carries its genuine
digest. Discharged once — a per-tag completeness instance reuses it, never re-proving the site layer. -/
theorem wide_sites_of_carrier (hash : List ℤ → ℤ) (env : VmRowEnv) (hc : WideCarrier hash env) :
    siteHoldsAll hash env wideHashSites := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  simp only [siteHoldsAll, wideHashSites, siteHoldsAll.go, site0, site1, site2, sysRootsAbsorbSite,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil, List.getD]
  refine ⟨h1, h2, h3, ?_, trivial⟩
  rw [h1, h2, h3] at h4
  exact h4

/-! ## §2 — the genuine wire commit as a function of the row (the forced commit).

`wireCommitOfRow hash env` is the deployed `H4`-of-`H4` absorption of the 13 absorbed kernel columns +
the `system_roots` carrier — exactly `wide_commit_eq`'s RHS. On any row holding the wide sites the
published `state_commit` IS this function (no free digest survives): `runnable_forces_genuine_commit`. -/

/-- **`wireCommitOfRow hash env`** — the genuine wide commitment of the row's after-state absorbed
columns (`wideCommitOf` of the 12 scalar cols + the `sysRootsDigestCol` side-table carrier). This is
the deployed GROUP-4 absorption, byte-pinned to the circuit by `wide_commit_eq`, NOT a fresh mirror. -/
def wireCommitOfRow (hash : List ℤ → ℤ) (env : VmRowEnv) : ℤ :=
  wideCommitOf hash
    (env.loc (saCol state.BALANCE_LO)) (env.loc (saCol state.BALANCE_HI))
    (env.loc (saCol state.NONCE)) (env.loc (saCol (state.FIELD_BASE + 0)))
    (env.loc (saCol (state.FIELD_BASE + 1))) (env.loc (saCol (state.FIELD_BASE + 2)))
    (env.loc (saCol (state.FIELD_BASE + 3))) (env.loc (saCol (state.FIELD_BASE + 4)))
    (env.loc (saCol (state.FIELD_BASE + 5))) (env.loc (saCol (state.FIELD_BASE + 6)))
    (env.loc (saCol (state.FIELD_BASE + 7))) (env.loc (saCol state.CAP_ROOT))
    (env.loc sysRootsDigestCol)

/-- **`runnable_forces_genuine_commit` — the `→` commit content (generic).** A row holding the wide
hash sites has its published `state_commit` FORCED to the genuine `wireCommitOfRow` — the deployed
circuit pins it, no free digest survives. This is `wide_commit_eq` read as `wireCommitOfRow`. -/
theorem runnable_forces_genuine_commit (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hsites : siteHoldsAll hash env wideHashSites) :
    env.loc (saCol state.STATE_COMMIT) = wireCommitOfRow hash env :=
  wide_commit_eq hash env hsites

/-! ## §3 — `RunnableFullStateCompleteSpec St`: the per-tag completeness data.

Extends the SOUNDNESS spec (`RunnableFullStateSpec St`, carrying `decodeFull` for the `→`) with the
completeness bundle: a row `buildRow`, the honest-witness precondition `absorbsTo`, and the per-tag
obligations that the built row is an effect row / decodes / fills the GROUP-4 carrier / satisfies the
descriptor's gates + ranges on both windows / publishes `NEW_COMMIT = state_commit`. Only `build_active`
/ `build_last` (the effect's OWN per-row gates, the converse of `decodeFull`) are genuine per-tag proof
work; the crypto is discharged in §1/§2. -/
structure RunnableFullStateCompleteSpec (St : Type) extends RunnableFullStateSpec St where
  /-- The witnessing row builder for a semantic `(pre, post, postRoots)`. Takes `hash` because the
  GROUP-4 inter-digest aux columns carry genuine inner hashes (mirrors `semTransferRow hash pre p post`). -/
  buildRow      : (List ℤ → ℤ) → St → St → SysRoots → VmRowEnv
  /-- The honest-witness precondition (the generic `hcommit`): the after-state absorbs to the published
  commit, the range-checked limbs are in range, and the untouched side-tables are frozen. Discharged by
  construction on a genuine witness (the demo instance discharges it concretely). -/
  absorbsTo     : (List ℤ → ℤ) → St → St → SysRoots → Prop
  /-- The built row is a valid effect row (selector hot / NoOp cold). -/
  build_isRow   : ∀ hash pre post sr, isRow (buildRow hash pre post sr)
  /-- The built row decodes back to `(pre, post, sr)` under the honest-witness precondition. -/
  build_decode  : ∀ hash pre post sr, absorbsTo hash pre post sr →
                    decodeAfter (buildRow hash pre post sr) pre post sr
  /-- ENGINE HOOK: the built row fills the GROUP-4 carrier columns honestly (so the four wide hash sites
  hold via `wide_sites_of_carrier`), under the precondition. Mechanical per tag. -/
  build_carrier : ∀ hash pre post sr, absorbsTo hash pre post sr →
                    WideCarrier hash (buildRow hash pre post sr)
  /-- PER-TAG: from the full clause (+ precondition), the built row's per-descriptor constraints hold on
  the ACTIVE window (`true false` — gates + transitions + first pins fire). -/
  build_active  : ∀ hash pre post sr, fullClause pre post sr → absorbsTo hash pre post sr →
                    ∀ c ∈ descriptor.constraints, c.holdsVm (buildRow hash pre post sr) true false
  /-- PER-TAG: … on the LAST window (`true true` — first + last pins fire; gates/transitions vacuous). -/
  build_last    : ∀ hash pre post sr, fullClause pre post sr → absorbsTo hash pre post sr →
                    ∀ c ∈ descriptor.constraints, c.holdsVm (buildRow hash pre post sr) true true
  /-- PER-TAG: the built row's range teeth hold. -/
  build_ranges  : ∀ hash pre post sr, fullClause pre post sr → absorbsTo hash pre post sr →
                    ∀ r ∈ descriptor.ranges, r.holds (buildRow hash pre post sr)
  /-- The built row publishes `NEW_COMMIT = state_after.state_commit` (the commit link the `⟺` names). -/
  build_newcommit : ∀ hash pre post sr,
                      (buildRow hash pre post sr).pub pi.NEW_COMMIT
                        = (buildRow hash pre post sr).loc (saCol state.STATE_COMMIT)

/-- **`runnable_full_complete` — THE GENERIC COMPLETENESS CORE (`SEM ⟹ SAT`).** From a genuine
`fullClause` and the honest-witness precondition `absorbsTo`, the built row GENUINELY SATISFIES the
effect's WIDE runnable descriptor on BOTH deployed windows: the active window (`true false` — gates +
transitions + first pins) and the last window (`true true` — the commit + boundary pins). The four wide
hash sites are CONSTRUCTED (`wide_sites_of_carrier`); the gates/ranges are the per-tag obligations. This
is the generic analog of `EffectVmEmitTransferComplete.sem_transfer_satisfied`. -/
theorem runnable_full_complete {St : Type} (E : RunnableFullStateCompleteSpec St)
    (hash : List ℤ → ℤ) (pre post : St) (sr : SysRoots)
    (hclause : E.fullClause pre post sr) (habsorb : E.absorbsTo hash pre post sr) :
    satisfiedVm hash E.descriptor (E.buildRow hash pre post sr) true false
    ∧ satisfiedVm hash E.descriptor (E.buildRow hash pre post sr) true true := by
  have hsites : siteHoldsAll hash (E.buildRow hash pre post sr) E.descriptor.hashSites := by
    rw [E.usesWideSites]
    exact wide_sites_of_carrier hash _ (E.build_carrier hash pre post sr habsorb)
  exact ⟨⟨E.build_active hash pre post sr hclause habsorb, hsites,
            E.build_ranges hash pre post sr hclause habsorb⟩,
         ⟨E.build_last hash pre post sr hclause habsorb, hsites,
            E.build_ranges hash pre post sr hclause habsorb⟩⟩

/-- **`runnable_full_commit_iff` — THE GENERIC FLAGSHIP BICONDITIONAL.** For a genuine effect whose
after-state absorbs to the published commit (`absorbsTo`), the built row satisfies the WIDE runnable
descriptor on BOTH deployed windows IFF the decoded transition is the genuine FULL 17-field post-state
(`fullClause`) AND the published `NEW_COMMIT` is the genuine wire commit of the after-state.

  * `→` composes `runnable_full_sound` (the FULL-state soundness) with `runnable_forces_genuine_commit`
    (the last window's hash-site leg forces the commit — NOT the precondition).
  * `←` is `runnable_full_complete` (the constructed witness satisfies).

Both directions are real; the `↔` is two-valued in `fullClause` (a tampered post fails the clause —
`canary_tamper_breaks_clause`) AND in the commit (a tampered field moves the genuine wire commit —
`canary_tamper_moves_commit`; a bogus published commit is UNSAT — `canary_bogus_commit_unsat`). The
commit is the DEPLOYED GROUP-4 `wideCommitOf` absorption, not a re-authored mirror. -/
theorem runnable_full_commit_iff {St : Type} (E : RunnableFullStateCompleteSpec St)
    (hash : List ℤ → ℤ) (pre post : St) (sr : SysRoots)
    (habsorb : E.absorbsTo hash pre post sr) :
    (satisfiedVm hash E.descriptor (E.buildRow hash pre post sr) true false
      ∧ satisfiedVm hash E.descriptor (E.buildRow hash pre post sr) true true)
    ↔ (E.fullClause pre post sr
        ∧ (E.buildRow hash pre post sr).pub pi.NEW_COMMIT
            = wireCommitOfRow hash (E.buildRow hash pre post sr)) := by
  constructor
  · rintro ⟨hact, hlast⟩
    have hclause : E.fullClause pre post sr :=
      runnable_full_sound E.toRunnableFullStateSpec hash (E.buildRow hash pre post sr) pre post sr
        (E.build_isRow hash pre post sr) (E.build_decode hash pre post sr habsorb) hact
    refine ⟨hclause, ?_⟩
    have hsites : siteHoldsAll hash (E.buildRow hash pre post sr) wideHashSites := by
      have hs := hlast.2.1
      rwa [E.usesWideSites] at hs
    rw [E.build_newcommit hash pre post sr]
    exact runnable_forces_genuine_commit hash _ hsites
  · rintro ⟨hclause, _⟩
    exact runnable_full_complete E hash pre post sr hclause habsorb

/-! ## §4 — THE VALIDATED REFERENCE INSTANCE (transfer): the engine is non-vacuous.

The transfer `RunnableFullStateCompleteSpec CellState`: the soundness `transferRunnableSpec` PLUS the
completeness bundle, whose builder is transfer's `semTransferRow` and whose obligations PROJECT the
(already proved) `sem_transfer_satisfied`. `absorbsTo` bundles transfer's honest-witness hypotheses
(genuine commit, in-range limbs, frozen roots) — exactly the flagship `transferDescriptor_commit_iff`'s
`hcommit`/`hbLo`/`hbHi` preconditions. -/

section TransferReference

/-- **`transferRunnableCompleteSpec` — THE VALIDATED REFERENCE.** `buildRow` is transfer's
`semTransferRow`; `absorbsTo` is the honest-witness precondition (genuine wire commit + frozen roots +
in-range balance limbs); every completeness obligation projects `sem_transfer_satisfied`. THIN — the
only per-tag content is the (already proved) transfer soundness/faithfulness. NON-VACUOUS — `fullClause`
is `CellTransferSpec ∧ frozen roots`, refutable (`transferReference_clause_not_trivial`). -/
def transferRunnableCompleteSpec (p : TransferParams) (preRoots : SysRoots) :
    RunnableFullStateCompleteSpec CellState where
  toRunnableFullStateSpec := transferRunnableSpec p preRoots
  buildRow      := fun hash pre post _sr => semTransferRow hash pre p post
  absorbsTo     := fun hash _pre post sr =>
    post.commit = cellWireCommit hash post 0
    ∧ sr = preRoots
    ∧ (0 ≤ post.balLo ∧ post.balLo < 2 ^ 30)
    ∧ (0 ≤ post.balHi ∧ post.balHi < 2 ^ 30)
  build_isRow   := fun hash pre post _sr => sem_isTransferRow hash pre p post
  build_decode  := by
    intro hash pre post sr habsorb
    exact ⟨sem_rowEncodes hash pre p post, habsorb.2.1⟩
  build_carrier := by
    intro hash pre post sr habsorb
    refine ⟨rfl, rfl, rfl, ?_⟩
    exact habsorb.1
  build_active  := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hcspec, _hroots⟩ := hclause
    obtain ⟨hcommit, _hsr, hbLo, hbHi⟩ := habsorb
    exact (sem_transfer_satisfied hash pre p post hcommit hbLo hbHi hcspec).1.1
  build_last    := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hcspec, _hroots⟩ := hclause
    obtain ⟨hcommit, _hsr, hbLo, hbHi⟩ := habsorb
    exact (sem_transfer_satisfied hash pre p post hcommit hbLo hbHi hcspec).2.1
  build_ranges  := by
    intro hash pre post sr hclause habsorb
    obtain ⟨hcspec, _hroots⟩ := hclause
    obtain ⟨hcommit, _hsr, hbLo, hbHi⟩ := habsorb
    exact (sem_transfer_satisfied hash pre p post hcommit hbLo hbHi hcspec).1.2.2
  build_newcommit := by
    intro hash pre post sr
    rfl

/-! ### §4½ — the CONCRETE demo: BUILD a satisfying witness, and the both-windows `⟺`. -/

/-- **`runnable_full_complete_demo` — the engine, discharged concretely.** The demo transfer
(`goodPre → demoPost`, debit 30, `100 → 70`) GENUINELY SATISFIES the wide runnable descriptor on BOTH
windows, for ANY `hash` — constructed via the generic `runnable_full_complete`, not asserted. -/
theorem runnable_full_complete_demo (hash : List ℤ → ℤ) :
    satisfiedVm hash (transferRunnableCompleteSpec goodParams goodPreRoots).descriptor
        ((transferRunnableCompleteSpec goodParams goodPreRoots).buildRow hash goodPre (demoPost hash)
          goodPreRoots) true false
    ∧ satisfiedVm hash (transferRunnableCompleteSpec goodParams goodPreRoots).descriptor
        ((transferRunnableCompleteSpec goodParams goodPreRoots).buildRow hash goodPre (demoPost hash)
          goodPreRoots) true true :=
  runnable_full_complete (transferRunnableCompleteSpec goodParams goodPreRoots) hash
    goodPre (demoPost hash) goodPreRoots
    ⟨goodSpec_holds, rfl⟩
    ⟨rfl, rfl, ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩,
              ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩⟩

/-- **`runnable_full_commit_iff_demo` — the both-windows biconditional, concretely.** The demo instance
satisfies the wide descriptor on BOTH windows IFF the transition is the genuine full clause AND the
published `NEW_COMMIT` is the genuine wire commit — `air_accepts ⟺ spec`, discharged. -/
theorem runnable_full_commit_iff_demo (hash : List ℤ → ℤ) :
    (satisfiedVm hash (transferRunnableCompleteSpec goodParams goodPreRoots).descriptor
        ((transferRunnableCompleteSpec goodParams goodPreRoots).buildRow hash goodPre (demoPost hash)
          goodPreRoots) true false
      ∧ satisfiedVm hash (transferRunnableCompleteSpec goodParams goodPreRoots).descriptor
        ((transferRunnableCompleteSpec goodParams goodPreRoots).buildRow hash goodPre (demoPost hash)
          goodPreRoots) true true)
    ↔ ((transferRunnableCompleteSpec goodParams goodPreRoots).fullClause goodPre (demoPost hash)
          goodPreRoots
        ∧ ((transferRunnableCompleteSpec goodParams goodPreRoots).buildRow hash goodPre (demoPost hash)
            goodPreRoots).pub pi.NEW_COMMIT
            = wireCommitOfRow hash
                ((transferRunnableCompleteSpec goodParams goodPreRoots).buildRow hash goodPre
                  (demoPost hash) goodPreRoots)) :=
  runnable_full_commit_iff (transferRunnableCompleteSpec goodParams goodPreRoots) hash
    goodPre (demoPost hash) goodPreRoots
    ⟨rfl, rfl, ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩,
              ⟨by norm_num [demoPost, goodPost], by norm_num [demoPost, goodPost]⟩⟩

end TransferReference

/-! ## §5 — CANARIES: the biconditional is two-valued in BOTH conjuncts (anti-vacuity).

Both directions of the two-valued `↔`, and the load-bearing of the completeness construction. -/

/-- **`canary_tamper_moves_commit_or_collides` — the commit conjunct BITES, UNCONDITIONALLY.** An
honest after-state (`field[0] = 0`) and a tampered one (`field[0] = 7`) — every other absorbed column
equal — EITHER publish DIFFERENT `wideCommitOf` digests, OR the deployed sponge genuinely collides at
the pair `group4Find` returns. So the honest published `NEW_COMMIT` cannot ride a tampered after-state
without a real collision being exhibited. This is the whole-state tooth on the WIDE
(side-table-carrying) commitment.

⚑ **WHY THIS SHAPE.** The old canary concluded a bare `≠` from `Poseidon2SpongeCR hash`, which is FALSE
at deployed BabyBear parameters (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`). A canary IS the
evidence that the `⟺`'s commit conjunct is two-valued; a vacuous canary certifies nothing. This one
holds of the deployed sponge, so the `⟺`'s non-degeneracy is now witnessed at deployed parameters. -/
theorem canary_tamper_moves_commit_or_collides (hash : List ℤ → ℤ) :
    wideCommitOf hash 70 0 6 0 0 0 0 0 0 0 0 0 0
      ≠ wideCommitOf hash 70 0 6 7 0 0 0 0 0 0 0 0 0
    ∨ SpongeColl hash (group4Find hash [70, 0, 6, 0] [0, 0, 0, 0] [0, 0, 0, 0] 0
                                       [70, 0, 6, 7] [0, 0, 0, 0] [0, 0, 0, 0] 0) := by
  by_cases heq : wideCommitOf hash 70 0 6 0 0 0 0 0 0 0 0 0 0
      = wideCommitOf hash 70 0 6 7 0 0 0 0 0 0 0 0 0
  · refine Or.inr ?_
    unfold wideCommitOf at heq
    rcases group4Find_spec hash [70, 0, 6, 0] [0, 0, 0, 0] [0, 0, 0, 0] 0
        [70, 0, 6, 7] [0, 0, 0, 0] [0, 0, 0, 0] 0 heq with ⟨hA, _, _, _⟩ | hcoll
    · -- the first block agreed, but its fourth slot moved `0 → 7`: impossible.
      rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hA
      obtain ⟨_, _, _, hf0, _⟩ := hA
      norm_num at hf0
    · exact hcoll
  · exact Or.inl heq

/-- **⚑ THE NO-STRENGTH-LOST TOOTH.** The deleted canary is EXACTLY the injective special case.
Standalone bridge, NOT a hypothesis on the engine's `⟺`. -/
theorem canary_tamper_moves_commit_of_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    wideCommitOf hash 70 0 6 0 0 0 0 0 0 0 0 0 0
    ≠ wideCommitOf hash 70 0 6 7 0 0 0 0 0 0 0 0 0 := by
  rcases canary_tamper_moves_commit_or_collides hash with hne | hcoll
  · exact hne
  · exact absurd hcoll (spongeColl_refutable_of_injective hash hCR _)

/-- **`canary_tamper_breaks_clause` — the clause conjunct is REFUTABLE (the `↔` LHS is genuinely
two-valued).** A post-state whose `bal_lo` is NOT the signed move (`goodPre.balLo = 100`, demanding
`70`, but a forged `999`) FAILS the reference instance's `fullClause` — so a `True`/`P → P` bridge
could not separate this: the completeness witness gates real content. (This IS the base file's
`transferReference_clause_not_trivial` — the reference instance's `fullClause` is `TransferFullClause`.) -/
theorem canary_tamper_breaks_clause :
    ¬ (transferRunnableCompleteSpec goodParams goodPreRoots).fullClause goodPre
        { goodPost with balLo := 999 } goodPreRoots :=
  transferReference_clause_not_trivial

/-- **`canary_bogus_commit_unsat` — the constructed row is LOAD-BEARING (mutation direction).** A row
whose published `state_commit` is NOT the genuine `wireCommitOfRow` CANNOT hold the wide hash sites — so
a completeness witness with a wrong/removed GROUP-4 carrier REDS (the sites force the genuine commit).
The contrapositive of `runnable_forces_genuine_commit`: mutating the constructed commit breaks
`siteHoldsAll`, hence `satisfiedVm`, hence the `←` leg — the completeness construction is not vacuous. -/
theorem canary_bogus_commit_unsat (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hbogus : env.loc (saCol state.STATE_COMMIT) ≠ wireCommitOfRow hash env) :
    ¬ siteHoldsAll hash env wideHashSites :=
  fun hsites => hbogus (runnable_forces_genuine_commit hash env hsites)

/-! ## §6 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms wide_sites_of_carrier
#assert_axioms runnable_forces_genuine_commit
#assert_axioms runnable_full_complete
#assert_axioms runnable_full_commit_iff
#assert_axioms runnable_full_complete_demo
#assert_axioms runnable_full_commit_iff_demo
#assert_axioms canary_tamper_moves_commit_or_collides
#assert_axioms canary_tamper_moves_commit_of_injective
#assert_axioms canary_tamper_breaks_clause
#assert_axioms canary_bogus_commit_unsat

end Dregg2.Circuit.Emit.EffectVmFullStateRunnableComplete

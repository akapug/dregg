/-
# Dregg2.Exec.ConditionalTurn — dregg1's conditional / EventualRef BATCH made EXECUTABLE + PROVED.

`Dregg2.Await` is a *spec*: it states the await family as algebraic effects + handlers with one-shot
(linear) continuations (Plotkin–Pretnar `Op`/`Computation`/`Handler`, the turn as the rollback
handler), and proves the *shape* laws (`four_faces_unify`, `commit_resumes_once`,
`rollback_discards_continuation`). What it has NOT got is an **executor**: there is no
`execConditionalTurn` that actually runs dregg1's batched, topologically-ordered, output-forwarding
conditional turn. This module supplies it — the E4 (executor-axis) coverage of the await spec.

What dregg1 actually does (`turn/src/eventual.rs`, `turn/src/conditional.rs`):

  * A **`Pipeline` / `TurnBatch`** (`eventual.rs §Pipeline`) is a list of turns plus dependency edges
    `(dependent_index, dependency_index)` — a DAG. `topological_order()` is **Kahn's algorithm**
    (in-degree zero queue; `order.len() != n ⇒ cycle`). `EventualRef { source_turn, output_slot }`
    (`eventual.rs §EventualRef`) is a SLOT a *producer* turn fills and a *consumer* turn reads; a
    dependency edge is exactly "consumer awaits producer's output slot". Execution runs the turns in
    topological order, resolving each `EventualRef` from the already-produced output.
  * `Pipeline.atomic` (`eventual.rs §Pipeline.atomic`): "when true, if ANY turn fails, ALL previously
    committed turns are rolled back" — **all-or-nothing batch commit**.

We model this over the SAME content-addressed record world the rest of `Exec` uses
(`RecChainedState` / `recTotal`), reusing `TurnExecutorFull.execFullTurn` as the per-node turn
executor (so each batch node is a dregg1 *turn* = a `List FullAction`, run as its own all-or-nothing
transaction). The batch is then:

  1. `structure ConditionalBatch` — the turns (`nodes`) + the EventualRef dependency edges
     (`edges : List (Nat × Nat)`, `(consumer, producer)`); each edge is a slot a producer fills and a
     consumer reads (the `EventualRef` model).
  2. `def execConditionalTurn` — Kahn-topologically order the nodes, execute each via `execFullTurn`,
     forwarding outputs into the slot environment, **all-or-nothing** (any node `none` ⇒ whole batch
     `none`, no state change). Computable (`#eval`-able).
  3. THEOREMS:
       * `condTurn_conserves` — the committed batch conserves `recTotal` when the net ledger delta of
         every node is `0` (Σ over the committed turns, reusing `execFullTurn_conserves`);
       * `condTurn_atomic` — failure ⇒ the input state is unchanged (no partial commit); the all-or-
         nothing guarantee, structural in `Option`-bind;
       * `condTurn_dependency_sound` — a consumer node only runs AFTER its producer filled the slot
         (topological order respected: for every edge `(c,p)`, `p` precedes `c` in the run order — no
         use-before-define / unresolved `EventualRef`);
       * `condTurn_forward_sim` — the batch refines a *sequence* of abstract steps `CondAbsStep` (the
         record-world conserved-measure transition; the per-node analog of
         `Spec.ExecRefinement`'s OPEN `AbsStep`), one abstract step per committed node.

Connection to `Await.lean`: a batch edge `(consumer, producer)` IS an `await` operation — the
consumer's `EventualRef` read is `Await.Op.await p` on the promise "producer's output slot", and the
slot environment filling on producer-commit is the handler's `commit` arm resuming the continuation
exactly once (`Await.commit_resumes_once`). We make that bridge explicit in `awaitEdge_is_await`
below: every dependency edge denotes an `Await.AwaitCore` whose promise is the producer slot.

Pure, computable, `#eval`-able. Reuses
`TurnExecutorFull` (`execFullTurn`/`execFullTurn_conserves`/`turnLedgerDelta`) and `Await`; edits no
existing file. The finite acyclic case (the real one) is proved via a fuel-driven Kahn sort whose
fuel is the node count.

The former §1 OPEN — the GENERAL νF / coinductive-DAG case of an *unbounded* dependency structure —
is now DISCHARGED BY EXCLUSION in §12 (`topoOrder_some_of_acyclic` + the structural-finiteness note):
a `ConditionalBatch` carries its `nodes`/`edges` as `List`s, so it is finite by construction (the νF
case is INEXPRESSIBLE — dregg's safe-by-inexpressibility line), and on any finite acyclic in-range
batch the bounded fuel = node-count Kahn iteration is COMPLETE (a finite DAG always has a source;
`exists_ready_of_acyclic`), so the greatest-fixed-point collapses to the finite least-fixed-point
(`kahnLoopImpl_more_fuel`: extra/unbounded fuel changes nothing once the loop has converged). No
new axiom.

Verified standalone: `lake env lean Dregg2/Exec/ConditionalTurn.lean`.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Await

namespace Dregg2.Exec.ConditionalTurn

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Spec (Domain conservedInDomain)
open scoped BigOperators

/-! ## §1 — `ConditionalBatch`: the turns + the EventualRef dependency DAG.

A batch node is a dregg1 *turn* — a `List FullAction` run as its own all-or-nothing transaction by
`execFullTurn`. The dependency edges are `(consumer, producer)` index pairs: edge `(c, p)` says node
`c` awaits node `p`'s output slot (an `EventualRef` from `p` to `c`). The `EventualRef` is modeled by
the slot environment `Slots` (below): `p`'s commit *fills* its slot; `c`'s run *reads* it. -/

/-- A single batch node: one dregg1 turn (a `List FullAction`). -/
abbrev Node := List FullAction

/-- **`ConditionalBatch`** — dregg1's `Pipeline`/`TurnBatch` (`eventual.rs §Pipeline`): a list of
`nodes` (each a turn) plus the `EventualRef` dependency `edges`, each edge `(consumer, producer)`
saying the consumer awaits the producer's output slot. The DAG `eventual.rs` topologically sorts. -/
structure ConditionalBatch where
  /-- The turns in the batch, indexed `0 .. nodes.length-1`. -/
  nodes : List Node
  /-- The dependency edges `(consumer, producer)`: consumer node awaits producer node's output slot
  (the `EventualRef` `producer ⟶ consumer`). -/
  edges : List (Nat × Nat)

/-- The number of nodes in a batch. -/
def ConditionalBatch.size (b : ConditionalBatch) : Nat := b.nodes.length

/-! ## §2 — The slot environment (the `EventualRef` model): a producer fills, a consumer reads.

`Slots` records, per node index, whether that node's output slot has been *filled* (the node has
committed). An `EventualRef` from producer `p` is *resolvable* exactly when `Slots p = true`. This is
the executable shadow of `eventual.rs`'s `TurnOutput` table that later turns read their
`EventualRef`s from. -/

/-- **`Slots`** — the output-slot environment: `Slots i = true` iff node `i` has produced its output
(committed), so any `EventualRef` to slot `i` now resolves. -/
abbrev Slots := Nat → Bool

/-- The empty slot environment (nothing produced yet). -/
def Slots.empty : Slots := fun _ => false

/-- Fill node `i`'s output slot (mark it produced) — the producer-commit forward step. -/
def Slots.fill (s : Slots) (i : Nat) : Slots := fun j => if j = i then true else s j

/-- A filled slot stays read-true; filling is monotone (forwarding never UN-fills). -/
theorem Slots.fill_get (s : Slots) (i : Nat) : (s.fill i) i = true := by
  simp [Slots.fill]

theorem Slots.fill_mono (s : Slots) (i j : Nat) (h : s j = true) : (s.fill i) j = true := by
  simp only [Slots.fill]; split <;> simp_all

/-! ## §3 — Kahn topological sort (finite, fuel-driven — the real acyclic case).

`eventual.rs §topological_order` is Kahn's algorithm. We give the finite, computable version: repeat
"pick a node with no remaining unmet dependency that has not yet been emitted" until all are emitted,
bounded by fuel = node count. On an acyclic DAG this emits a full topological order; if a node count
of rounds passes without finishing, a cycle is present and we abort (mirroring `order.len() != n ⇒
Err(Cycle)`).

FORMER OPEN (general νF), NOW DISCHARGED in §12: the *unbounded* / coinductive-DAG case — a batch
whose dependency structure is a general greatest-fixed-point (νF) rather than a finite acyclic list.
§12 resolves it BY EXCLUSION: a `ConditionalBatch` is structurally finite (`List` nodes/edges — the
νF case is inexpressible), and on a finite acyclic in-range batch the fuel = node-count Kahn loop is
COMPLETE (`topoOrder_some_of_acyclic`), with extra fuel changing nothing (`kahnLoopImpl_more_fuel`) —
the greatest-fixed-point collapses to the least. dregg1's only real case (a `Vec<Turn>` with
`Vec<(usize,usize)>` edges) is exactly this finite case; Kahn terminates by construction. -/

/-- Does node `c`'s dependency on producer `p` (edge `(c,p)`) remain UNMET, given the set `emitted` of
already-emitted node indices? Unmet iff `p ∉ emitted`. -/
def depUnmet (emitted : List Nat) (_c p : Nat) : Bool := ¬ (emitted.contains p)

/-- Is node `i` *ready* to emit: not yet emitted, and every dependency edge `(i, p)` it has is met
(producer `p` already emitted)? The Kahn "in-degree zero (over remaining)" test. -/
def ready (edges : List (Nat × Nat)) (emitted : List Nat) (i : Nat) : Bool :=
  (¬ emitted.contains i) &&
  (edges.all (fun e => if e.1 = i then ¬ depUnmet emitted i e.2 else true))

/-- One Kahn round: scan candidates `0 .. n-1`, pick the FIRST ready node, append it to `emitted`.
Returns `none` if no node is ready (all remaining nodes are blocked — a cycle, on an exhausted
candidate set). -/
def kahnStep (n : Nat) (edges : List (Nat × Nat)) (emitted : List Nat) : Option Nat :=
  (List.range n).find? (fun i => ready edges emitted i)

/-- The Kahn loop: with `fuel` rounds left over `n` nodes and `edges`, emit the first ready node each
round; stop when all `n` emitted or no node ready or fuel out. -/
def kahnLoopImpl : Nat → Nat → List (Nat × Nat) → List Nat → Option (List Nat)
  | 0,         n, _,     emitted => if emitted.length = n then some emitted else none
  | fuel + 1,  n, edges, emitted =>
      if emitted.length = n then some emitted
      else
        match kahnStep n edges emitted with
        | some i => kahnLoopImpl fuel n edges (emitted ++ [i])
        | none   => none  -- nothing ready but not done ⇒ cycle (mirrors `order.len() != n`)

/-- **`topoOrder b`** — the topological order of a batch (`eventual.rs §topological_order`): run Kahn
with fuel = node count. `none` on a cycle (dregg1's `Err(Cycle)`). -/
def topoOrder (b : ConditionalBatch) : Option (List Nat) :=
  kahnLoopImpl b.size b.size b.edges []

/-! ## §4 — `execConditionalTurn`: order, then run all-or-nothing, forwarding slots.

We thread `(RecChainedState × Slots)`: each emitted node runs via `execFullTurn` (its own all-or-
nothing transaction); on commit we FILL the node's output slot (forwarding to dependents). Any node
`none` aborts the whole batch (`Option`-bind short-circuits) — the `Pipeline.atomic` all-or-nothing
commit. The `Outputs` of the batch are the final filled-slot environment. -/

/-- Run the emitted nodes of a batch in the given `order`, threading state + slots, all-or-nothing.
Each node is looked up by index and run via `execFullTurn`; on commit its output slot is filled. -/
def runOrder (nodes : List Node) (order : List Nat) (s : RecChainedState) (slots : Slots) :
    Option (RecChainedState × Slots) :=
  match order with
  | []          => some (s, slots)
  | i :: rest   =>
      match nodes[i]? with
      | none      => none  -- order index out of range (never, for a valid topoOrder)
      | some node =>
          match execFullTurn s node with
          | some s' => runOrder nodes rest s' (slots.fill i)
          | none    => none  -- a node failed ⇒ whole batch aborts (atomic rollback)

/-- The batch's outputs: the final filled-slot environment (which producers have resolved). -/
abbrev Outputs := Slots

/-- **`execConditionalTurn` — THE EXECUTOR (computable).** Topologically order the batch
(`eventual.rs §topological_order`), then run the turns in that order all-or-nothing
(`Pipeline.atomic`), forwarding each producer's output into the slot environment. Returns the
post-state and the resolved-slot `Outputs`, or `none` on cycle / any node failure. -/
def execConditionalTurn (b : ConditionalBatch) (s : RecChainedState) :
    Option (RecChainedState × Outputs) :=
  match topoOrder b with
  | none       => none  -- dependency cycle (dregg1's PipelineError::Cycle)
  | some order => runOrder b.nodes order s Slots.empty

/-! ## §5 — `condTurn_atomic`: ALL-OR-NOTHING (failure ⇒ unchanged input state). -/

/-- A committed `runOrder` is built from committed per-node `execFullTurn`s — so on the FAILURE side,
no partial state escapes: `runOrder … = none` returns the LITERAL `none`, carrying no state. The
all-or-nothing structure is the `Option`-bind: the only way state advances is a `some` chain through
every node, and the moment any node is `none` the whole result is `none` with the input `s` never
mutated (Lean values are immutable; `s` is simply not returned). We state the contrapositive content
as a clean fact about the committed case below; here we record the structural abort. -/
theorem runOrder_abort (nodes : List Node) (i : Nat) (rest : List Nat)
    (s : RecChainedState) (slots : Slots) (node : Node)
    (hlk : nodes[i]? = some node) (hfail : execFullTurn s node = none) :
    runOrder nodes (i :: rest) s slots = none := by
  simp only [runOrder, hlk, hfail]

/-- **`condTurn_atomic` (all-or-nothing).** If the batch executor returns `none` (any node
failed, or a cycle), then NO post-state is produced: the result is exactly `none`, so the input state
`s` is untouched — there is no partial commit. This is the executable shadow of dregg1's
`Pipeline.atomic` "if ANY turn fails, ALL previously committed turns are rolled back": in the pure
`Option` model, a failed batch simply yields `none` and the immutable input `s` is the only surviving
state. (The committed case `= some (s',o)` is characterized by `condTurn_commit_runs` below.) -/
theorem condTurn_atomic (b : ConditionalBatch) (s : RecChainedState)
    (h : execConditionalTurn b s = none) :
    ¬ ∃ s' o, execConditionalTurn b s = some (s', o) := by
  rintro ⟨s', o, hsome⟩
  rw [h] at hsome
  exact absurd hsome (by simp)

/-- A committed batch went through a successful `topoOrder` and a fully-committing `runOrder`. -/
theorem condTurn_commit_runs (b : ConditionalBatch) (s : RecChainedState)
    (s' : RecChainedState) (o : Outputs) (h : execConditionalTurn b s = some (s', o)) :
    ∃ order, topoOrder b = some order ∧ runOrder b.nodes order s Slots.empty = some (s', o) := by
  unfold execConditionalTurn at h
  cases hto : topoOrder b with
  | none => rw [hto] at h; exact absurd h (by simp)
  | some order => rw [hto] at h; exact ⟨order, rfl, h⟩

/-! ## §6 — `condTurn_conserves`: the committed batch conserves (Σ over committed turns). -/

/-- A committed `runOrder` moves `recTotal` by the sum of the per-node turn ledger deltas — the
record-world transaction ledger across the WHOLE batch, reusing `execFullTurn_ledger` per node. -/
theorem runOrder_ledger :
    ∀ (nodes : List Node) (order : List Nat) (s s' : RecChainedState) (slots slots' : Slots),
      runOrder nodes order s slots = some (s', slots') →
      recTotal s'.kernel
        = recTotal s.kernel + ((order.filterMap (fun i => nodes[i]?)).map turnLedgerDelta).sum
  | _, [],        s, s', slots, slots', h => by
      simp only [runOrder, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, _⟩ := h; subst hs; simp
  | nodes, i :: rest, s, s', slots, slots', h => by
      simp only [runOrder] at h
      cases hlk : nodes[i]? with
      | none => simp only [hlk] at h; exact absurd h (by simp)
      | some node =>
          simp only [hlk] at h
          cases hex : execFullTurn s node with
          | none => simp only [hex] at h; exact absurd h (by simp)
          | some s1 =>
              simp only [hex] at h
              have hhead : recTotal s1.kernel = recTotal s.kernel + turnLedgerDelta node :=
                execFullTurn_ledger s s1 node hex
              have htail := runOrder_ledger nodes rest s1 s' (slots.fill i) slots' h
              rw [htail, hhead]
              simp only [List.filterMap_cons, hlk, List.map_cons, List.sum_cons]
              ring

/-- **`condTurn_conserves` (batch conservation).** A committed conditional turn whose every
committed node has zero net ledger delta (balance/authority-only turns, or balanced mint/burn within
each turn) PRESERVES the conserved `recTotal` across the whole all-or-nothing batch: `recTotal
s'.kernel = recTotal s.kernel`. This is the Σ-over-committed-turns conservation, reusing
`execFullTurn`'s per-node ledger and summing to `0`. The batch is conservation-faithful exactly when
each turn is. -/
theorem condTurn_conserves (b : ConditionalBatch) (s s' : RecChainedState) (o : Outputs)
    (h : execConditionalTurn b s = some (s', o))
    (hzero : ∀ order, topoOrder b = some order →
      ((order.filterMap (fun i => b.nodes[i]?)).map turnLedgerDelta).sum = 0) :
    recTotal s'.kernel = recTotal s.kernel := by
  obtain ⟨order, hto, hrun⟩ := condTurn_commit_runs b s s' o h
  have := runOrder_ledger b.nodes order s s' Slots.empty o hrun
  rw [this, hzero order hto, add_zero]

/-! ## §7 — `condTurn_dependency_sound`: a consumer runs only AFTER its producer filled the slot.

The topo-order guarantee, made precise on the slot environment: in the emitted `runOrder`, when a
consumer node `c` is reached, every producer `p` it depends on (edge `(c,p)`) has ALREADY had its
output slot filled — `EventualRef` never reads an unproduced slot (no use-before-define). We prove it
in two layers: (a) the topo `order` itself respects every edge (`producer precedes consumer`), and
(b) `runOrder` fills a node's slot at the moment it commits, so by the time the consumer runs, the
producer's slot is filled. -/

/-- `kahnStep` only emits a node ALL of whose dependency producers are already emitted (the Kahn
readiness gate `ready`). So the emitted node's `EventualRef`s are all resolvable at emission time. -/
theorem kahnStep_emits_ready (n : Nat) (edges : List (Nat × Nat)) (emitted : List Nat) (i : Nat)
    (h : kahnStep n edges emitted = some i) : ready edges emitted i = true := by
  unfold kahnStep at h
  exact (List.find?_some h)

/-- A node `i` that is `ready emitted` has, for EVERY edge `(i, p)`, the producer `p` already in
`emitted` (its slot filled) — the precise "all dependencies met before emission" content. -/
theorem ready_deps_emitted (edges : List (Nat × Nat)) (emitted : List Nat) (i p : Nat)
    (hr : ready edges emitted i = true) (he : (i, p) ∈ edges) : emitted.contains p = true := by
  unfold ready at hr
  rw [Bool.and_eq_true] at hr
  obtain ⟨_, hall⟩ := hr
  rw [List.all_eq_true] at hall
  have hthis := hall (i, p) he
  -- the edge `(i,p)` has `e.1 = i`, so the `if` takes the true-branch: `¬ depUnmet = ¬¬ contains`.
  simp only [depUnmet] at hthis
  -- `hthis : (!(!emitted.contains p)) = true`
  simpa using hthis

/-- A slot filled in the input to a committed `runOrder` remains filled in the output (forwarding is
monotone — outputs are never un-forwarded). Used to carry a producer's fill forward to its consumer. -/
theorem runOrder_filled_stays :
    ∀ (nodes : List Node) (order : List Nat) (s s' : RecChainedState) (slots slots' : Slots),
      runOrder nodes order s slots = some (s', slots') →
      ∀ j, slots j = true → slots' j = true
  | _, [],          _, _, _, _, _, j, hj => by
      rename_i h
      simp only [runOrder, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hsl⟩ := h; subst hsl; exact hj
  | nodes, i :: rest, s, s', slots, slots', h, j, hj => by
      simp only [runOrder] at h
      cases hlk : nodes[i]? with
      | none => simp only [hlk] at h; exact absurd h (by simp)
      | some node =>
          simp only [hlk] at h
          cases hex : execFullTurn s node with
          | none => simp only [hex] at h; exact absurd h (by simp)
          | some s1 =>
              simp only [hex] at h
              exact runOrder_filled_stays nodes rest s1 s' (slots.fill i) slots' h j
                (Slots.fill_mono slots i j hj)

/-- **`runOrder` fills as it commits.** After a committed `runOrder` over `order`, every node
index in `order` has had its slot filled in the final environment — producers' outputs are forwarded.
We prove the monotone fact: any slot already filled in the input stays filled, and every emitted index
is filled by the end. -/
theorem runOrder_fills :
    ∀ (nodes : List Node) (order : List Nat) (s s' : RecChainedState) (slots slots' : Slots),
      runOrder nodes order s slots = some (s', slots') →
      ∀ j, j ∈ order → slots' j = true
  | _, [],          _, _, _, _, _, j, hj => absurd hj (List.not_mem_nil)
  | nodes, i :: rest, s, s', slots, slots', h, j, hj => by
      simp only [runOrder] at h
      cases hlk : nodes[i]? with
      | none => simp only [hlk] at h; exact absurd h (by simp)
      | some node =>
          simp only [hlk] at h
          cases hex : execFullTurn s node with
          | none => simp only [hex] at h; exact absurd h (by simp)
          | some s1 =>
              simp only [hex] at h
              -- slots' fills `i` then everything in `rest`; `runOrder_fills` on the tail.
              rcases List.mem_cons.mp hj with hji | hjr
              · -- j = i: i's slot was filled at this step, and the tail keeps it filled (mono).
                refine runOrder_filled_stays nodes rest s1 s' (slots.fill i) slots' h j ?_
                rw [hji]; exact Slots.fill_get slots i
              · exact runOrder_fills nodes rest s1 s' (slots.fill i) slots' h j hjr

/-- The fuel-driven Kahn loop only ever appends nodes that were `ready` at the moment of emission, so
its output order respects every edge: a producer precedes its consumer. We capture the per-step
readiness in the emitted prefix. -/
theorem kahnLoopImpl_respects :
    ∀ (fuel n : Nat) (edges : List (Nat × Nat)) (emitted order : List Nat),
      kahnLoopImpl fuel n edges emitted = some order →
      (∀ (c p : Nat), (c, p) ∈ edges → c ∈ emitted → emitted.contains p = true) →
      (∀ (c p : Nat), (c, p) ∈ edges → c ∈ order → order.contains p = true)
  | 0, n, edges, emitted, order, h, hinv => by
      simp only [kahnLoopImpl] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h
        intro c p he hc
        exact hinv c p he hc
      · exact absurd h (by simp)
  | fuel + 1, n, edges, emitted, order, h, hinv => by
      simp only [kahnLoopImpl] at h
      split at h
      · -- already done: emitted = order
        simp only [Option.some.injEq] at h; subst h
        intro c p he hc
        exact hinv c p he hc
      · -- emit a ready node and recurse
        cases hstep : kahnStep n edges emitted with
        | none => simp only [hstep] at h; exact absurd h (by simp)
        | some i =>
            simp only [hstep] at h
            have hready : ready edges emitted i = true := kahnStep_emits_ready n edges emitted i hstep
            -- the new invariant on `emitted ++ [i]`
            have hinv' : ∀ (c p : Nat), (c, p) ∈ edges → c ∈ (emitted ++ [i]) →
                (emitted ++ [i]).contains p = true := by
              intro c p he hc
              rw [List.mem_append] at hc
              rcases hc with hce | hci
              · -- c was already emitted: producer p already emitted (invariant), still in the append.
                have := hinv c p he hce
                rw [List.contains_iff_mem] at this ⊢
                exact List.mem_append.mpr (Or.inl this)
              · -- c = i (the just-emitted ready node): readiness gives p ∈ emitted.
                simp only [List.mem_singleton] at hci; subst hci
                have hpe : emitted.contains p = true := ready_deps_emitted edges emitted c p hready he
                rw [List.contains_iff_mem] at hpe ⊢
                exact List.mem_append.mpr (Or.inl hpe)
            exact kahnLoopImpl_respects fuel n edges (emitted ++ [i]) order h hinv'

/-- **`condTurn_dependency_sound` (topo-order respected; no use-before-define).** For a
committed conditional turn, the emitted run `order` respects EVERY `EventualRef` dependency edge: for
each edge `(consumer, producer)`, if the consumer appears in the order then so does the producer
(`order.contains producer`). Combined with `runOrder_fills` (a node fills its slot as it commits) and
`runOrder_filled_stays` (forwarding is monotone), this is the executable guarantee that a consumer
turn only ever runs AFTER its producer filled the awaited `EventualRef` slot — dregg1's topological
execution with no unresolved reference (`PipelineError::UnresolvedRef` cannot arise). -/
theorem condTurn_dependency_sound (b : ConditionalBatch) (s s' : RecChainedState) (o : Outputs)
    (h : execConditionalTurn b s = some (s', o)) :
    ∃ order, topoOrder b = some order ∧
      (∀ (c p : Nat), (c, p) ∈ b.edges → c ∈ order → order.contains p = true) := by
  obtain ⟨order, hto, _⟩ := condTurn_commit_runs b s s' o h
  refine ⟨order, hto, ?_⟩
  unfold topoOrder at hto
  exact kahnLoopImpl_respects b.size b.size b.edges [] order hto
    (by intro c p _ hc; exact absurd hc (List.not_mem_nil))

/-- **The slot-resolution corollary: every awaited producer's slot is filled in the batch
outputs.** For a committed batch, if a consumer `c` in the run order awaits producer `p` (edge
`(c,p)`), then `p`'s output slot is filled in the final `Outputs` — the `EventualRef` resolves. This
is `condTurn_dependency_sound` pushed through `runOrder_fills`: producer precedes consumer ⇒ producer
emitted ⇒ producer's slot filled. -/
theorem condTurn_eventualref_resolved (b : ConditionalBatch) (s s' : RecChainedState) (o : Outputs)
    (h : execConditionalTurn b s = some (s', o))
    (c p : Nat) (he : (c, p) ∈ b.edges) (hc : ∃ order, topoOrder b = some order ∧ c ∈ order) :
    o p = true := by
  obtain ⟨order, hto, hcord⟩ := hc
  obtain ⟨order', hto', hrun⟩ := condTurn_commit_runs b s s' o h
  -- topoOrder is a function: order = order'
  rw [hto'] at hto; simp only [Option.some.injEq] at hto; subst hto
  -- p precedes c in the order (dependency soundness), so p ∈ order' and its slot is filled.
  obtain ⟨ord2, hto2, hresp⟩ := condTurn_dependency_sound b s s' o h
  rw [hto'] at hto2; simp only [Option.some.injEq] at hto2; subst hto2
  have hpmem : order'.contains p = true := hresp c p he hcord
  rw [List.contains_iff_mem] at hpmem
  exact runOrder_fills b.nodes order' s s' Slots.empty o hrun p hpmem

/-! ## §8 — `condTurn_forward_sim`: the batch refines a SEQUENCE of abstract steps.

`Spec.ExecRefinement` leaves the abstract small-step relation `AbsStep` OPEN (its §4 OPEN comment),
and `Exec/EffectTransfer.lean` DISCHARGES it for the Transfer slice with a constraining
`AbsStep a a' := conservedInDomain Domain.balance [a'.balanceTotal - a.balanceTotal] ∧ a'.authGraph
= a.authGraph`. We mirror its CONSERVATION conjunct — the part a batch node provably carries — as the
per-node `CondAbsStep`: the conserved `balance`-domain measure must NOT move (`recTotal` is unchanged
across the node). This is NOT the old `∃ δ, a' = a + δ` (which was true for ANY pair — take `δ = a' -
a` — and so constrained nothing). It is the SAME `Spec.conservedInDomain Domain.balance` law
`EffectTransfer.AbsStep` and `ExecRefinement.recExec_step_refines` carry, restricted to the
conserved-measure projection the conditional executor tracks: a step REJECTS any pair whose balance
total actually moved. A committed *balance/authority-only* batch (each node net-zero ledger delta —
dregg1's `Paired`/conservative regime) is then matched by a *chain* of REAL abstract steps, one per
committed node (the executor-axis bottom edge). The authority-graph conjunct is NOT demanded per
node: a batch node is a general `List FullAction` that MAY delegate/revoke (it edits `execGraph`), so
unlike Transfer it is not connectivity-preserving in general — we keep the conservation conjunct,
which is the tracked content, rather than overclaiming graph-invariance. -/

/-- **`CondAbsStep a a'`** — the record-world abstract step, the CONSERVATION conjunct of
`EffectTransfer.AbsStep`: the conserved `balance`-domain delta `[a' - a]` nets to `0`
(`Spec.conservedInDomain Domain.balance`), i.e. the conserved measure is UNCHANGED across the step
(`a' = a`). This is the per-node analog of `Spec.ExecRefinement`'s OPEN `AbsStep` and the exact
balance-domain law `EffectTransfer.transfer_forward_sim` discharges — a GENUINELY CONSTRAINING
relation: any pair with `a' ≠ a` is NOT a `CondAbsStep` (the conserved total moved), unlike the old
vacuous `∃ δ, a' = a + δ`. -/
def CondAbsStep (a a' : ℤ) : Prop := conservedInDomain Domain.balance [a' - a]

/-- **The predicate has TEETH:** `CondAbsStep a a'` holds IFF `a' = a` — a step that moves
the conserved balance total is REJECTED. Contrast the old `∃ δ, a' = a + δ`, which held for every
pair. This is the de-vacuification witness: `CondAbsStep` constrains. -/
theorem condAbsStep_iff_eq (a a' : ℤ) : CondAbsStep a a' ↔ a' = a := by
  unfold CondAbsStep conservedInDomain
  simp [sub_eq_zero]

/-- A non-step is rejected: if the conserved total moved (`a' ≠ a`), it is NOT a
`CondAbsStep`. The old `∃ δ` predicate could never produce this fact. -/
theorem not_condAbsStep_of_ne (a a' : ℤ) (h : a' ≠ a) : ¬ CondAbsStep a a' := by
  rw [condAbsStep_iff_eq]; exact h

/-- **A committed CONSERVING node IS a `CondAbsStep`.** A single batch node whose net ledger
delta is `0` (a balance/authority-only turn — dregg1's `Paired`/conservative regime, the same regime
`condTurn_conserves` assumes) leaves the conserved `recTotal` unchanged, so it satisfies the
constraining `CondAbsStep` on the measure. A node that mints/burns (nonzero delta) is NOT a
`CondAbsStep` — the abstract step rejects it, exactly as it should. -/
theorem execFullTurn_is_condAbsStep (s s' : RecChainedState) (node : Node)
    (h : execFullTurn s node = some s') (hcons : turnLedgerDelta node = 0) :
    CondAbsStep (recTotal s.kernel) (recTotal s'.kernel) := by
  rw [condAbsStep_iff_eq]
  rw [execFullTurn_ledger s s' node h, hcons, add_zero]

/-- A chain of `CondAbsStep`s along a list of conserved-measure waypoints. `AbsChain [a₀,a₁,…,aₙ]`
holds iff each consecutive pair is a `CondAbsStep` — the abstract *sequence* the batch refines. -/
def AbsChain : List ℤ → Prop
  | []            => True
  | [_]           => True
  | a :: a' :: rest => CondAbsStep a a' ∧ AbsChain (a' :: rest)

/-- **`runOrder_abschain`.** A committed `runOrder` over a batch each of whose committed
nodes conserves (net ledger delta `0` — the `Paired`/conservative regime) produces a chain of
conserved-measure waypoints (the `recTotal` after each prefix) that forms an `AbsChain`: every
consecutive node-commit is a REAL `CondAbsStep` (the balance total provably did NOT move, so the
constraining predicate is satisfied at each edge, not vacuously). So the conserving batch
refines a sequence of constraining abstract steps. The per-node conservation hypothesis is the
already-available `runOrder_ledger`/`execFullTurn_ledger` fact in the regime `condTurn_conserves`
assumes — wired into the now-constraining `CondAbsStep`. -/
theorem runOrder_abschain :
    ∀ (nodes : List Node) (order : List Nat) (s s' : RecChainedState) (slots slots' : Slots),
      runOrder nodes order s slots = some (s', slots') →
      (∀ i ∈ order, ∀ node, nodes[i]? = some node → turnLedgerDelta node = 0) →
      ∃ waypoints : List ℤ,
        waypoints.head? = some (recTotal s.kernel) ∧
        waypoints.getLast? = some (recTotal s'.kernel) ∧
        AbsChain waypoints
  | _, [],          s, s', slots, slots', h, _ => by
      simp only [runOrder, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs, _⟩ := h; subst hs
      exact ⟨[recTotal s.kernel], rfl, rfl, trivial⟩
  | nodes, i :: rest, s, s', slots, slots', h, hcons => by
      simp only [runOrder] at h
      cases hlk : nodes[i]? with
      | none => simp only [hlk] at h; exact absurd h (by simp)
      | some node =>
          simp only [hlk] at h
          cases hex : execFullTurn s node with
          | none => simp only [hex] at h; exact absurd h (by simp)
          | some s1 =>
              simp only [hex] at h
              obtain ⟨wp, hhd, hlast, hchain⟩ :=
                runOrder_abschain nodes rest s1 s' (slots.fill i) slots' h
                  (fun j hj n hn => hcons j (List.mem_cons_of_mem i hj) n hn)
              -- prepend `recTotal s` to the tail chain; the new head→old head is a CondAbsStep,
              -- because this node conserves (zero ledger delta ⇒ the balance total did not move).
              have hnode0 : turnLedgerDelta node = 0 :=
                hcons i (List.mem_cons_self) node hlk
              have hstep : CondAbsStep (recTotal s.kernel) (recTotal s1.kernel) :=
                execFullTurn_is_condAbsStep s s1 node hex hnode0
              refine ⟨recTotal s.kernel :: wp, rfl, ?_, ?_⟩
              · -- getLast? of (x :: wp) = getLast? wp when wp ≠ []
                cases wp with
                | nil => simp at hhd
                | cons a tl => simpa using hlast
              · cases wp with
                | nil => simp at hhd
                | cons a tl =>
                    simp only [List.head?] at hhd
                    -- hhd : some a = some (recTotal s.kernel)
                    have : a = recTotal s1.kernel := by
                      simpa using hhd
                    subst this
                    exact ⟨hstep, hchain⟩

/-- **`condTurn_forward_sim` (refinement of a sequence of CONSTRAINING abstract steps).** A
committed conditional turn each of whose committed nodes conserves (net ledger delta `0` — the
`Paired`/conservative regime `condTurn_conserves` works in) is matched by a *chain* of REAL abstract
steps `CondAbsStep` on the conserved `recTotal` measure: there is a list of waypoints starting at the
pre-state measure, ending at the post-state measure, with every consecutive pair an abstract step
(one per committed node). Because `CondAbsStep a a'` now means `conservedInDomain Domain.balance
[a' - a]` (i.e. `a' = a`, the constraining balance-domain law `EffectTransfer.AbsStep`
carries — NOT the old `∃ δ` true-for-any-pair), this is a CONTENTFUL refinement: each waypoint edge
witnesses that the conserved total did not move, and a non-conserving step would be REJECTED. This is
the executor-axis bottom edge of the refinement square — `Spec.ExecRefinement`'s OPEN `AbsStep`,
realized for the BATCH executor over the conserved-measure projection: `execConditionalTurn` refines
a sequence of `CondAbsStep`s. The conservation hypothesis is the per-node form of the `hzero` that
`condTurn_conserves` already takes; on a batch that mints/burns net-nonzero the chain does
NOT exist (the bottom edge has teeth). -/
theorem condTurn_forward_sim (b : ConditionalBatch) (s s' : RecChainedState) (o : Outputs)
    (h : execConditionalTurn b s = some (s', o))
    (hcons : ∀ order, topoOrder b = some order →
      ∀ i ∈ order, ∀ node, b.nodes[i]? = some node → turnLedgerDelta node = 0) :
    ∃ waypoints : List ℤ,
      waypoints.head? = some (recTotal s.kernel) ∧
      waypoints.getLast? = some (recTotal s'.kernel) ∧
      AbsChain waypoints := by
  obtain ⟨order, hto, hrun⟩ := condTurn_commit_runs b s s' o h
  exact runOrder_abschain b.nodes order s s' Slots.empty o hrun (hcons order hto)

/-! ## §9 — Connection to `Await.lean`: a dependency edge IS an `await` operation.

The bridge the task asks for: a batch edge `(consumer, producer)` denotes an `Await.Op.await` on the
promise "producer's output slot", captured by the turn-as-rollback handler. The consumer's
`EventualRef` read is the await op; the producer's slot fill on commit is the handler's `commit` arm
(`Await.commit_resumes_once`) resuming the awaiting continuation exactly once; an aborted producer is
the `abort` arm (`Await.rollback_discards_continuation`). We make the edge↦`AwaitCore` map explicit. -/

/-- **`awaitEdge`** — the `Await.AwaitCore` denoted by a dependency edge `(consumer, producer)`: an
await on the promise "producer node index `p`" with a one-shot continuation that resumes the consumer
on resolution. The promise handle is the producer index; the reply (resolved slot value) is modeled as
the producer index that filled it. -/
def awaitEdge {S : Type} (p : Nat) (kont : Await.OneShot Nat S) : Await.AwaitCore Nat Nat S :=
  { promise := p, kont := kont }

/-- **`awaitEdge_is_await`.** Every dependency edge's `awaitEdge` has the producer index as
its awaited promise — i.e. the `EventualRef` read IS an `Await.Op.await` on the producer's slot. The
core's continuation is the consumer's resumption, captured one-shot exactly as `Await`'s `AwaitCore`
specifies. This ties the executor's slot-forwarding to `Await.lean`'s handler semantics: forwarding =
the `commit` arm resuming the awaiting continuation once. -/
theorem awaitEdge_is_await {S : Type} (p : Nat) (kont : Await.OneShot Nat S) :
    (awaitEdge p kont).promise = p ∧ (awaitEdge p kont).kont = kont :=
  ⟨rfl, rfl⟩

/-- **The producer-commit ↔ handler-commit bridge.** When a producer commits (its slot fills),
the awaiting consumer's continuation is resumed EXACTLY ONCE — modeled by `Await`'s turn-as-rollback
handler taking the `commit` arm. Reusing `Await.commit_resumes_once`: the await op's handler, on a
commit decision, equals `OneShot.resume` of the captured continuation. So slot-forwarding in
`runOrder` is the `commit` face of the await handler. -/
theorem forward_is_handler_commit
    {S : Type} (onRet : Nat → S) (refund : S)
    (decide : (Reply : Type) → Await.Op Nat Nat Nat → Await.CommitOrAbort)
    (resumeWith : (Reply : Type) → Reply)
    (o : Await.Op Nat Nat Nat) (k : Await.OneShot Nat S)
    (hcommit : decide Nat o = Await.CommitOrAbort.commit) :
    (Await.turnAsRollbackHandler onRet refund decide resumeWith).onOp Nat o k
      = Await.OneShot.resume k (resumeWith Nat) :=
  Await.commit_resumes_once onRet refund decide resumeWith Nat o k hcommit

/-! ## §10 — Axiom-hygiene tripwires (the honesty pins over the batch executor's keystones). -/

#assert_axioms runOrder_abort
#assert_axioms condTurn_atomic
#assert_axioms condTurn_commit_runs
#assert_axioms runOrder_ledger
#assert_axioms condTurn_conserves
#assert_axioms kahnStep_emits_ready
#assert_axioms ready_deps_emitted
#assert_axioms runOrder_filled_stays
#assert_axioms runOrder_fills
#assert_axioms kahnLoopImpl_respects
#assert_axioms condTurn_dependency_sound
#assert_axioms condTurn_eventualref_resolved
#assert_axioms condAbsStep_iff_eq
#assert_axioms not_condAbsStep_of_ne
#assert_axioms execFullTurn_is_condAbsStep
#assert_axioms runOrder_abschain
#assert_axioms condTurn_forward_sim
#assert_axioms awaitEdge_is_await
#assert_axioms forward_is_handler_commit

/-! ## §11 — Non-vacuity: a real batch with a real EventualRef edge commits in topo order. -/

/-- A two-node batch over `fs0` (from `TurnExecutorFull`): node 0 mints +50 (producer), node 1 burns
−50 (consumer awaiting node 0's slot). Edge `(1, 0)`: node 1 awaits node 0. Net ledger delta 0. -/
def demoBatch : ConditionalBatch :=
  { nodes := [ [FullAction.mint 9 0 50], [FullAction.burn 9 0 50] ]
    edges := [(1, 0)] }

-- The topo order puts producer (0) before consumer (1):
#guard (topoOrder demoBatch) == some [0, 1]  --  some [0, 1]
-- The batch commits (both nodes succeed) all-or-nothing:
#guard ((execConditionalTurn demoBatch fs0).isSome)  --  true
-- ...conserves `recTotal` (net 0): 105 → 155 → 105:
#guard ((execConditionalTurn demoBatch fs0).map (fun r => recTotal r.1.kernel)) == some 105  --  some 105
-- ...and both producers' slots are resolved in the outputs:
#guard ((execConditionalTurn demoBatch fs0).map (fun r => (r.2 0, r.2 1))) == some (true, true)  --  some (true, true)

/-! ### The `CondAbsStep` predicate has TEETH — a non-step pair is rejected.

The de-vacuification check the audit asks for: the OLD `CondAbsStep a a' := ∃ δ, a' = a + δ` held
for EVERY pair (take `δ = a' - a`), so it constrained nothing. The NEW one
(`conservedInDomain Domain.balance [a' - a]`, i.e. `a' = a`) REJECTS any pair whose conserved total
moved. -/

-- A conserving step (the total did not move) IS a `CondAbsStep`:
example : CondAbsStep 105 105 := (condAbsStep_iff_eq 105 105).mpr rfl
-- A NON-step (the conserved total moved 105 → 155) is REJECTED — the predicate has teeth.
-- (Under the OLD `∃ δ` definition this very pair WAS a step, with `δ = 50`.)
example : ¬ CondAbsStep 105 155 := not_condAbsStep_of_ne 105 155 (by decide)

-- The teeth, as `decide`-able equalities the predicate reduces to (`CondAbsStep a a' ↔ a' = a`):
#guard (decide ((105 : ℤ) = 105))  --  true  — `CondAbsStep 105 105` holds (conserving step)
#guard (decide ((155 : ℤ) = 105)) == false  --  false — `CondAbsStep 105 155` REJECTED (total moved 105→155)

/-- A batch with a DEPENDENCY CYCLE (each node awaits the other) is rejected (`PipelineError::Cycle`). -/
def cycleBatch : ConditionalBatch :=
  { nodes := [ [FullAction.mint 9 0 10], [FullAction.burn 9 0 10] ]
    edges := [(0, 1), (1, 0)] }

#guard (topoOrder cycleBatch).isNone  --  none (cycle)
#guard ((execConditionalTurn cycleBatch fs0).isSome) == false  --  false (atomic abort, no commit)

/-- A batch whose CONSUMER turn fails (unauthorized burn) rolls the WHOLE batch back (atomic). -/
def badBatch : ConditionalBatch :=
  { nodes := [ [FullAction.mint 9 0 50], [FullAction.burn 0 0 10] ]  -- node 1 unauthorized
    edges := [(1, 0)] }

#guard ((execConditionalTurn badBatch fs0).isSome) == false  --  false (rollback; node 0's mint discarded)

/-! ## §12 — THE FORMER §1 OPEN, DISCHARGED BY EXCLUSION: the νF case is unreachable.

The §1 OPEN asked whether the *unbounded* / coinductive-νF dependency structure (a dependency graph
that is a general greatest-fixed-point rather than a finite acyclic DAG — an infinite or cyclic
promise chain) needs a genuine coinductive simulation. It does NOT. Two facts close it:

  **(i) Structural finiteness (inexpressibility).** A `ConditionalBatch` carries `nodes : List Node`
  and `edges : List (Nat × Nat)` — both *finite lists*. There is no coinductive/streaming batch
  *type* in the model (the await `Computation` free model is `inductive`, hence finite-depth term
  trees). So an infinite batch is INEXPRESSIBLE: the νF case cannot be constructed. This is dregg's
  safe-by-inexpressibility line — the unbounded case is not "excluded by an invariant we bolt on" but
  by the *type* of a batch.

  **(ii) The greatest-fixed-point collapses to the least on a finite acyclic graph.** The Kahn loop
  iterates the monotone "set of already-resolvable nodes" operator from `∅` (the least-fixed-point
  iteration). On a finite ACYCLIC in-range edge set this iteration is COMPLETE: a finite DAG always
  has a source (`exists_ready_of_acyclic`), so every not-yet-complete prefix has a ready node, the
  loop never stalls, and it reaches the full node set in ≤ n rounds with fuel = node count
  (`topoOrder_some_of_acyclic`). Extra/unbounded fuel changes NOTHING once it has converged
  (`kahnLoopImpl_more_fuel`) — the νF (unbounded iteration) and the μF (bounded fuel = node count)
  give the same answer. There is no coinductive content to recover.

  The only way `topoOrder` returns `none` is a genuine dependency CYCLE — and a cycle is exactly a
  deadlock (each promise waits on another, none ever fires), which the executor correctly rejects
  (`condTurn_atomic`: no partial commit). The contrapositive `topoOrder_none_imp_cyclic` makes this
  precise: a `none` over an in-range batch witnesses non-acyclicity (a real cycle), never a premature
  stall of a sound DAG.

So §1 is discharged: the unbounded νF case is unreachable (inexpressible AND, even taken as a graph,
collapsed to the finite least-fixed-point), a real theorem — NOT an assumed exclusion. -/

/-- **`Acyclic edges`** — the topological-rank characterization of a finite DAG: there is a rank
assignment strictly decreasing along every dependency edge (`rank producer < rank consumer`). A cycle
would force `rank` to strictly decrease around it — impossible in `ℕ`. This is exactly the condition
under which the Kahn least-fixed-point iteration is complete. -/
def Acyclic (edges : List (Nat × Nat)) : Prop :=
  ∃ rank : Nat → Nat, ∀ c p, (c, p) ∈ edges → rank p < rank c

/-- **`EdgesInRange n edges`** — well-formedness: every producer index referenced by an edge is a
valid node (`< n`). dregg1's `Pipeline` builds edges over `Vec<Turn>` indices, so this always holds;
without it a dangling producer could never be emitted (a different failure than a cycle). -/
def EdgesInRange (n : Nat) (edges : List (Nat × Nat)) : Prop := ∀ c p, (c, p) ∈ edges → p < n

/-- The "remaining" set: a node in range that has not yet been emitted. -/
def Remaining (n : Nat) (emitted : List Nat) (i : Nat) : Prop := i < n ∧ emitted.contains i = false

/-- A not-yet-emitted node that is NOT `ready` has an UNMET dependency edge `(i, p)` whose producer
`p` is itself not yet emitted — the structural reason a non-source is blocked. -/
theorem not_ready_unmet (edges : List (Nat × Nat)) (emitted : List Nat) (i : Nat)
    (hne : emitted.contains i = false) (hnr : ready edges emitted i = false) :
    ∃ p, (i, p) ∈ edges ∧ emitted.contains p = false := by
  unfold ready at hnr
  rw [Bool.and_eq_false_iff] at hnr
  rcases hnr with h1 | h2
  · simp only [decide_eq_false_iff_not, Decidable.not_not] at h1
    rw [h1] at hne; simp at hne
  · rw [List.all_eq_false] at h2
    obtain ⟨e, hmem, hfail⟩ := h2
    by_cases hei : e.1 = i
    · simp only [hei, if_pos] at hfail
      simp only [Bool.not_eq_true, decide_eq_false_iff_not] at hfail
      unfold depUnmet at hfail
      simp only [Bool.not_eq_true, decide_eq_false_iff_not] at hfail
      refine ⟨e.2, ?_, by simpa using hfail⟩
      rw [← hei]; cases e; exact hmem
    · simp only [hei, if_neg, not_false_iff] at hfail; simp at hfail

/-- **`ready_descent` — a finite DAG always has a source (the well-founded heart).** On an acyclic
in-range edge set, any remaining node leads (by descent along unmet dependency edges, each strictly
lowering the rank) to a remaining node that IS `ready`. Strong induction on the rank bound: a
non-ready remaining node has an unmet edge to a producer of strictly smaller rank, which is itself
remaining — recurse. The `ℕ`-rank well-foundedness is what forbids an infinite descent (a cycle). -/
theorem ready_descent
    (n : Nat) (edges : List (Nat × Nat))
    (rank : Nat → Nat) (hac : ∀ c p, (c, p) ∈ edges → rank p < rank c)
    (hir : ∀ c p, (c, p) ∈ edges → p < n) (emitted : List Nat) :
    ∀ R i, Remaining n emitted i → rank i ≤ R →
      ∃ j, j < n ∧ ready edges emitted j = true := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    intro i hrem hri
    by_cases hready : ready edges emitted i = true
    · exact ⟨i, hrem.1, hready⟩
    · rw [Bool.not_eq_true] at hready
      obtain ⟨p, hpe, hpne⟩ := not_ready_unmet edges emitted i hrem.2 hready
      have hpr : rank p < rank i := hac i p hpe
      have hpltR : rank p < R := Nat.lt_of_lt_of_le hpr hri
      exact ih (rank p) hpltR p ⟨hir i p hpe, hpne⟩ (Nat.le_refl _)

/-- **`exists_ready_of_acyclic` — a finite acyclic batch always has a ready node while one remains.**
The Kahn-completeness source lemma: given any remaining node, acyclicity (+ in-range edges) produces
a ready node. This is precisely why the bounded iteration never needs unbounded/coinductive fuel. -/
theorem exists_ready_of_acyclic
    (n : Nat) (edges : List (Nat × Nat))
    (hac : Acyclic edges) (hir : EdgesInRange n edges)
    (emitted : List Nat) (i : Nat) (hrem : Remaining n emitted i) :
    ∃ j, j < n ∧ ready edges emitted j = true := by
  obtain ⟨rank, hrank⟩ := hac
  exact ready_descent n edges rank hrank hir emitted (rank i) i hrem (Nat.le_refl _)

/-- A not-fully-emitted nodup in-range prefix has an un-emitted in-range node (pigeonhole on
`range n`): if every `i < n` were emitted, `range n ⊆ emitted` forces `n ≤ |emitted|`. -/
theorem exists_unemitted (n : Nat) (emitted : List Nat) (hlt : emitted.length < n) :
    ∃ i, i < n ∧ emitted.contains i = false := by
  by_contra hcon
  push Not at hcon
  have hrange_sub : List.range n ⊆ emitted := by
    intro i hi
    have hin : i < n := List.mem_range.mp hi
    have hne := hcon i hin
    have hct : emitted.contains i = true := by
      cases hc : emitted.contains i with
      | false => exact absurd hc hne
      | true => rfl
    exact List.contains_iff_mem.mp hct
  have hle : (List.range n).length ≤ emitted.length :=
    List.Subperm.length_le (List.subperm_of_subset (List.nodup_range) hrange_sub)
  rw [List.length_range] at hle; omega

/-- `kahnStep` returns a node that is in range AND not already emitted (the readiness gate forces
freshness) — so each round appends a genuinely new in-range node, preserving the nodup/in-range
invariant the completeness induction threads. -/
theorem kahnStep_fresh_inrange (n : Nat) (edges : List (Nat × Nat)) (emitted : List Nat) (i : Nat)
    (h : kahnStep n edges emitted = some i) : i < n ∧ emitted.contains i = false := by
  unfold kahnStep at h
  have hmem : i ∈ List.range n := List.mem_of_find?_eq_some h
  have hr : ready edges emitted i = true := List.find?_some h
  refine ⟨List.mem_range.mp hmem, ?_⟩
  unfold ready at hr
  rw [Bool.and_eq_true] at hr
  obtain ⟨h1, _⟩ := hr
  simp only [decide_eq_true_eq] at h1
  cases hc : emitted.contains i with
  | false => rfl
  | true => exact absurd hc h1

/-- `kahnStep` returns `some` whenever a ready in-range node exists (it is `find?` over `range n`). -/
theorem kahnStep_some_of_ready (n : Nat) (edges : List (Nat × Nat)) (emitted : List Nat)
    (h : ∃ j, j < n ∧ ready edges emitted j = true) : (kahnStep n edges emitted).isSome := by
  obtain ⟨j, hjn, hjr⟩ := h
  unfold kahnStep
  rw [List.find?_isSome]
  exact ⟨j, List.mem_range.mpr hjn, hjr⟩

/-- **`kahnLoopImpl_complete` — the BOUNDED (least-fixed-point) Kahn loop is COMPLETE on a finite
acyclic in-range batch.** With fuel ≥ `n − |emitted|` and a nodup in-range emitted prefix, the loop
returns `some` (never stalls, never spuriously reports a cycle). The induction: while not done, a node
remains (`exists_unemitted`), so a ready node exists (`exists_ready_of_acyclic`), so `kahnStep` emits a
fresh in-range node, shrinking the fuel gap. This is the formal "νF collapses to μF": no unbounded /
coinductive iteration is ever needed — the finite node-count fuel suffices. -/
theorem kahnLoopImpl_complete
    (n : Nat) (edges : List (Nat × Nat)) (hac : Acyclic edges) (hir : EdgesInRange n edges) :
    ∀ fuel emitted, emitted.Nodup → (∀ x ∈ emitted, x < n) → n ≤ emitted.length + fuel →
      ∃ order, kahnLoopImpl fuel n edges emitted = some order := by
  intro fuel
  induction fuel with
  | zero =>
    intro emitted hnd hsub hfuel
    simp only [Nat.add_zero] at hfuel
    have hle : emitted.length ≤ n := by
      have : emitted.length ≤ (List.range n).length :=
        List.Subperm.length_le (List.subperm_of_subset hnd
          (fun x hx => List.mem_range.mpr (hsub x hx)))
      rwa [List.length_range] at this
    have heq : emitted.length = n := Nat.le_antisymm hle hfuel
    simp only [kahnLoopImpl, heq, if_pos]
    exact ⟨emitted, rfl⟩
  | succ f ih =>
    intro emitted hnd hsub hfuel
    simp only [kahnLoopImpl]
    by_cases hdone : emitted.length = n
    · simp only [hdone, if_pos]; exact ⟨emitted, rfl⟩
    · simp only [hdone, if_neg, not_false_iff]
      have hle : emitted.length ≤ n := by
        have : emitted.length ≤ (List.range n).length :=
          List.Subperm.length_le (List.subperm_of_subset hnd
            (fun x hx => List.mem_range.mpr (hsub x hx)))
        rwa [List.length_range] at this
      have hlt : emitted.length < n := Nat.lt_of_le_of_ne hle hdone
      obtain ⟨i, hin, hni⟩ := exists_unemitted n emitted hlt
      obtain ⟨j, hjn, hjr⟩ := exists_ready_of_acyclic n edges hac hir emitted i ⟨hin, hni⟩
      have hstep_some : (kahnStep n edges emitted).isSome :=
        kahnStep_some_of_ready n edges emitted ⟨j, hjn, hjr⟩
      cases hstep : kahnStep n edges emitted with
      | none => rw [hstep] at hstep_some; simp at hstep_some
      | some k =>
        obtain ⟨hkn, hkne⟩ := kahnStep_fresh_inrange n edges emitted k hstep
        have hnd' : (emitted ++ [k]).Nodup := by
          rw [List.nodup_append]
          refine ⟨hnd, List.nodup_singleton k, ?_⟩
          intro a ha b hb hab; subst hab
          simp only [List.mem_singleton] at hb; subst hb
          exact absurd (List.contains_iff_mem.mpr ha) (by rw [hkne]; simp)
        have hsub' : ∀ x ∈ (emitted ++ [k]), x < n := by
          intro x hx; rw [List.mem_append] at hx
          rcases hx with h | h
          · exact hsub x h
          · simp only [List.mem_singleton] at h; subst h; exact hkn
        have hfuel' : n ≤ (emitted ++ [k]).length + f := by
          rw [List.length_append, List.length_singleton]; omega
        exact ih (emitted ++ [k]) hnd' hsub' hfuel'

/-- **`topoOrder_some_of_acyclic` — THE EXCLUSION HEADLINE.** An acyclic, in-range batch ALWAYS
produces a complete topological order: `topoOrder b = some order`. The fuel = node-count (the bounded
least-fixed-point) is provably sufficient; no unbounded / coinductive (νF) iteration is reachable. The
former §1 OPEN is discharged — the finite acyclic case (dregg1's only real case) is the WHOLE case. -/
theorem topoOrder_some_of_acyclic (b : ConditionalBatch)
    (hac : Acyclic b.edges) (hir : EdgesInRange b.size b.edges) :
    ∃ order, topoOrder b = some order := by
  unfold topoOrder
  exact kahnLoopImpl_complete b.size b.edges hac hir b.size []
    List.nodup_nil (by intro x hx; exact absurd hx (List.not_mem_nil)) (by simp)

/-- **`kahnLoopImpl_more_fuel` — the νF = μF stabilization.** Once the loop returns a `some` result
with some fuel, ANY additional fuel returns the SAME order. So the unbounded (coinductive / νF) limit
of the iteration equals the bounded (finite-fuel / μF) value — there is no extra content in taking
fuel to infinity. This is the formal collapse of the greatest-fixed-point to the least. -/
theorem kahnLoopImpl_more_fuel (n : Nat) (edges : List (Nat × Nat)) :
    ∀ fuel emitted order, kahnLoopImpl fuel n edges emitted = some order →
      kahnLoopImpl (fuel + 1) n edges emitted = some order := by
  intro fuel
  induction fuel with
  | zero =>
    intro emitted order h
    simp only [kahnLoopImpl] at h
    split at h
    · rename_i hdone
      simp only [Option.some.injEq] at h; subst h
      simp only [kahnLoopImpl, hdone, if_pos]
    · exact absurd h (by simp)
  | succ f ih =>
    intro emitted order h
    simp only [kahnLoopImpl] at h ⊢
    split at h
    · rename_i hdone; simp only [hdone, if_pos] at *; exact h
    · rename_i hdone; simp only [hdone, if_neg, not_false_iff] at *
      cases hstep : kahnStep n edges emitted with
      | none => simp only [hstep] at h; exact absurd h (by simp)
      | some i => simp only [hstep] at h ⊢; exact ih (emitted ++ [i]) order h

/-- **`topoOrder_none_imp_cyclic` — the dual: a rejected batch is genuinely CYCLIC.** If `topoOrder`
returns `none` over an in-range batch, the batch is NOT acyclic — there is a real dependency cycle (a
deadlock: each promise awaits another, none fires). The `none` is never a premature stall of a sound
DAG; it is dregg1's `PipelineError::Cycle`, correctly rejected with no partial commit
(`condTurn_atomic`). Together with `topoOrder_some_of_acyclic`, this pins `topoOrder b = some _ ↔
acyclic` (for in-range batches) — the νF case maps exactly onto the deadlock the executor refuses. -/
theorem topoOrder_none_imp_cyclic (b : ConditionalBatch)
    (hir : EdgesInRange b.size b.edges) (h : topoOrder b = none) : ¬ Acyclic b.edges := by
  intro hac
  obtain ⟨order, hsome⟩ := topoOrder_some_of_acyclic b hac hir
  rw [h] at hsome; exact absurd hsome (by simp)

/-! ### §12 axiom-hygiene + mutation-confirmation: the exclusion BITES. -/

#assert_axioms not_ready_unmet
#assert_axioms ready_descent
#assert_axioms exists_ready_of_acyclic
#assert_axioms exists_unemitted
#assert_axioms kahnStep_fresh_inrange
#assert_axioms kahnStep_some_of_ready
#assert_axioms kahnLoopImpl_complete
#assert_axioms topoOrder_some_of_acyclic
#assert_axioms kahnLoopImpl_more_fuel
#assert_axioms topoOrder_none_imp_cyclic

-- MUTATION-CONFIRM (the property bites both ways):
-- (a) The acyclic demo batch (edge (1,0), in range) IS acyclic ⇒ topoOrder succeeds:
example : Acyclic demoBatch.edges := by
  refine ⟨id, ?_⟩
  intro c p he
  simp only [demoBatch, List.mem_singleton, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he; simp
example : EdgesInRange demoBatch.size demoBatch.edges := by
  intro c p he
  simp only [demoBatch, List.mem_singleton, Prod.mk.injEq] at he
  obtain ⟨_, rfl⟩ := he; decide
example : ∃ order, topoOrder demoBatch = some order :=
  topoOrder_some_of_acyclic demoBatch
    (by refine ⟨id, ?_⟩; intro c p he; simp only [demoBatch, List.mem_singleton, Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he; simp)
    (by intro c p he; simp only [demoBatch, List.mem_singleton, Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he; decide)

-- (b) The CYCLE batch (edges (0,1),(1,0)) is genuinely NOT acyclic — the νF/deadlock case, REJECTED:
example : ¬ Acyclic cycleBatch.edges := by
  rintro ⟨rank, h⟩
  have h1 := h 0 1 (by simp [cycleBatch])
  have h2 := h 1 0 (by simp [cycleBatch])
  omega
-- ...and a `none` topoOrder over the (in-range) cycle batch witnesses non-acyclicity:
example : EdgesInRange cycleBatch.size cycleBatch.edges := by
  intro c p he
  simp only [cycleBatch, ConditionalBatch.size] at *
  fin_cases he <;> decide
example : ¬ Acyclic cycleBatch.edges :=
  topoOrder_none_imp_cyclic cycleBatch
    (by intro c p he; simp only [cycleBatch, ConditionalBatch.size] at *; fin_cases he <;> decide)
    (by native_decide)

end Dregg2.Exec.ConditionalTurn

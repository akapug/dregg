# Polis sandbox — progress + metatheory questions (for gpt-5.5)

*Companion to `docs/POLIS.md` (the constitution) and `docs/POLIS-SANDBOX.md` (the runnable arena).
Everything below §1 is built, green, kernel-clean. §2 is where we want your formal-methods read —
we suspect we've been re-deriving a known theory and want the right names, the optimal objects, and
the soundness condition that lets the guarantee escape the toy.*

---

## 1. What's proven (the verified governance tower, ~24 Lean files)

A fully-in-Lean, kernel-checked multi-agent sandbox where scripted/bounded-optimizer agents act, a
**governor** filters each move, and the floor-preservation is proven against *all* controllers.

- **General governor.** `genGovStep step floor w m := if floor (step w m) then step w m else w`
  (admit-iff-the-post-state-satisfies-the-floor, else shield/stay). Proven, for arbitrary `State`,
  `step`, decidable `floor`:
  - `genGov_safe`: `∀ controller, ∀ n, floor (govTraj … n)` — the floor is an invariant of the
    governed dynamics for **every** opaque controller (controller never inspected).
  - `genGov_admits_benign` / `genGov_refuses_only_harmful`: gentle — admits exactly the
    floor-preserving moves, refuses exactly the floor-breaking ones.
  - `genGovStep_eq_envStep`: `genGovStep` **is** the constitution's `Polis.envAct` over the
    floor-policy with a stay-put shield — so `genGov_safe` is literally `polis_safety`.
- **Composition.** Floors form a meet-semilattice under `combineFloor f g := fun w => f w ∧ g w`:
  - `combine_safe` (the combined governor keeps both floors ∀ controller),
  - `combine_gentle`, and the keystone **`combine_monotone`**: a refusal by *either* component
    governor is a refusal by the combined governor — *adding a governance axis only grows the
    refusal set, never weakens it.*
- **The politician zoo** (each emergent ungoverned, prevented governed, `decide`-checked): foreclosure,
  **coalition** (collective — `coalition_single_erasure_insufficient`: erasing one member doesn't free
  the victim), laundering (claim-tier > earned), lock-in/hole-rent, resource-competition, and a unified
  3-axis world where one adversary mixes them.
- **Smart adversaries + the long game.** A myopic (one-step) governor is *provably fooled* by a lawful
  sequence (`myopic_strands_victim`); a **trajectory governor** that admits iff the victim can still
  `reachHome` within `k` catches it. An optimizer *discovers* the foreclosure move by search
  (`optimizer_discovers_domination`); a learner *converges* on it yet `can_never_strand`; a deceiver's
  long con is refused at any prefix. Crucially: **`*_withstands_all_attacks`** — by induction, an
  exhaustive adaptive searcher finds *no* stranding attack of *any depth* under the governor, over the
  gate world, the unified 3-axis world, and `Fin n` agents.
- **Liveness.** `victim_reaches_home_under_viability` / `all_agents_reach_home` (∀ n): under the
  trajectory governor the victim *actually reaches* home (not just "can"). Safety → actuality.
- **Graded / cumulative.** A max-plus (tropical) quantale grade; the **composed governor** (per-step
  floor ∧ cumulative-grade ≤ budget) catches *both* a single big jump *and* death-by-a-thousand-cuts;
  lone governors each miss one.
- **Grand.** `grand_no_adversary_captures`: one governor, the named adversaries (forecloser/launderer/
  hoarder) all refused via `combine_monotone`, ∀ controller.
- **Grounding.** `sandbox_safe_via_constitution` makes the sandbox a literal instance of
  `Polis.polis_safety`; `govTraj_eq_constitution_traj` proves the runnable governor *is* the verified
  envelope. A `lean_exe` runs that decision as a callable binary; a Mineflayer+Claude harness drives it
  end-to-end (scripted/no-LLM today).

**Honest limit:** agents are scripted/bounded Lean optimizers, not LLMs; worlds are small (decidable).
The `∀`-controller theorems *do* cover an LLM-as-controller — but only within the modeled `Move` type
and over the (unverified) world-projection. That gap is the heart of §2.

---

## 2. The metatheory questions (where we want your read)

### Q1 — Is our governor the *controllable-invariant / viability kernel*, and does that theory hand us the optimal object + the liveness extension?

`genGov_safe` is "the floor is an invariant of the governed dynamics for all controllers," and the
trajectory (viability) governor's `reachHome`-within-`k` is bounded liveness. This smells exactly like
**viability theory** (Aubin's viability kernel — the largest set from which a safe trajectory exists)
and **safety games** (Maler–Pnueli–Sifakis; the controllable-predecessor `CPre` fixpoint, the maximal
winning region). Concretely:

1. Is our `reachHome`-floor the **viability kernel** of the floor under the governed dynamics — i.e.
   the *largest* sub-floor closed under "∃ a controlled move keeping you in it"? We defined it
   operationally (`reachHome k`); is the right object the **greatest fixpoint** of the controllable
   predecessor, and should we be computing *that* (so the governor is provably the **most permissive**
   safe one, not just *a* safe one)?
2. Our `*_withstands_all_attacks` is an inductive invariant proof. Is the clean statement "the floor is
   a **controlled invariant** (∃ control keeping it) ⟺ the governor exists"? Does the safety-game
   literature give us the **maximal gentle governor** as `νX. floor ∧ CPre(X)` directly?
3. Liveness: we have bounded `reachHome`. Does the viability/Büchi-game machinery give the *unbounded*
   liveness (eventually-home) as a least-fixpoint, and is it decidable on our finite worlds? (We
   deliberately stayed bounded — `liveness_not_prefix_refutable` in `PolisMonitor` shows unbounded
   liveness has no finite bad-prefix witness — but a game-theoretic eventually-home might still be
   synthesizable.)

### Q2 — Is "meet of floors + `combine_monotone`" the right composition algebra, and is there a quantale account unifying the Boolean and graded governors?

We compose floors by `∧` and proved the governor-composition is monotone (more axes → more refusals).
The graded governor uses a max-plus quantale for cumulative harm. Questions:
- Is the Boolean governor the degenerate (2-element-quantale) case of a **graded viability** theory —
  i.e. floors valued in a quantale `Q`, a `Q`-valued controllable predecessor, the governor admitting
  iff the graded post-state stays ≤ a budget? Is there a known "quantitative safety game / energy game"
  framework (energy games, mean-payoff, the *quantitative `CPre`*) that subsumes both our Boolean and
  graded results, and would give us the cumulative-budget governor as a special case with decidability?
- Is the **combined governor optimal** in any precise sense — e.g. the *greatest* gentle governor among
  those enforcing all the component floors (a meet in a lattice of governors)? We have `combine_monotone`
  (monotone) and `combine_gentle`; is there a "least-restrictive-enforcing-the-meet" characterization?

### Q3 — The soundness condition that lets the `∀`-controller guarantee escape the toy (the projection problem).

The real gap to a real substrate (Minecraft, or anything) is not the controller — the theorems already
quantify over all controllers, so an LLM is covered. The gap is the **world-projection**: the harness's
`observeWorld`/`simulateAction` map real game state → the governed model, and that map is *unverified*.
For the verified `floor`-invariance to transfer to the real game we presumably need the projection to be
a **sound abstraction** — a simulation/refinement condition (the concrete dynamics simulate the abstract
governed model; the abstract floor is a sound over-approximation of "real harm"). Questions:
- What is the exact condition (a forward simulation? a Galois connection / abstract-interpretation
  soundness? a refinement à la your earlier `FlowRefine`/Büchi reply?) under which
  `genGov_safe` on the model implies "no real-world floor violation"?
- Is the right framing that the **governor is correct by construction but the *projection* is the
  trusted/obligation surface** — i.e. we move the trust from "the LLM behaves" to "the projection is a
  sound abstraction," which is a much smaller, checkable surface? Does that match how you'd want the
  Minecraft floor (no spawn-camping / resource-monopoly / griefing / everyone-keeps-a-path-home)
  related to the model floor?

### Q4 — Does the whole tower instantiate the polis constitution the way you intended, and is `least-restrictive` the right optimality notion?

`govStep = envAct` and `sandbox_safe_via_constitution` ground the sandbox in `Polis.polis_safety`. The
constitution also proved `envelope_least_restrictive`. Is least-restrictiveness the correct optimality
bar for a *governor*, or should it be the viability-kernel maximality of Q1 (they may coincide; we
haven't proven they do)? And does the grand `combine_monotone` composition correctly realize the
constitution's `CaptureBar.or` / amendment-monotonicity story, or are we conflating two different
monotonicities (refusal-set growth vs. floor-set shrinkage)?

---

## 3. The ask

Tell us **(a)** whether the governor/floor machinery is the controllable-invariant / viability-kernel /
safety-game object (and if so, the canonical references + the *maximal* governor we should be computing
instead of the operational `reachHome`); **(b)** whether a quantitative/energy-game framework subsumes
both our Boolean and graded governors (graded viability), with decidability we can import; **(c)** the
precise **projection-soundness** condition (simulation/Galois) under which the `∀`-controller invariance
transfers to a real substrate, so the trusted surface becomes the small, checkable *abstraction* rather
than the agent; and **(d)** whether `least-restrictive` or `viability-kernel-maximal` is the right
optimality notion tying the sandbox governor back to the constitution's envelope. These determine
whether we keep deepening operationally or refactor onto the canonical objects before the LLM/Minecraft
substrate lands.

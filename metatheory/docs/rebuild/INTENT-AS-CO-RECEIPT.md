# Intent as Co-Receipt — toward a first-class metatheory of web3

**Status:** living design spine (started 2026-06-03). Not a spec to freeze; the shape we build the
gallery auction (and eventually DeFi) against. Companion to the relativistic time-typing innovation
(§4 here) and the escrow→userspace decision (`EFFECT-FIDELITY-LEDGER.md`, §"missing state dimension").

> The turn has **two faces**: the **receipt** (it happened) and the **intent** (let it happen).
> They are adjoint through `Predicate ⊣ Witness`, funded by userspace escrow, time-typed as
> causal-or-frame, and conserved by the kernel. We had receipts; intent is the missing dual.

---

## 1. The duality: a co-receipt is a typed string-diagram *hole*

A **receipt** attests a *completed* turn — a full string diagram: boxes wired, inputs consumed,
outputs produced, conserved. An **intent** is its adjoint — the *same diagram with the interior left
as a typed hole*:

```
        ┌─────────────┐                         ┌─────────────┐
  A ───►│   (filled)  │───► C   RECEIPT     A ──►│   ▢ hole ▢  │──► C   INTENT
        └─────────────┘                         └─────────────┘
   "this happened, conserved"              "let this happen; I bring A, I require C"
```

**Fulfillment** = plugging a morphism `A → C` (or a chain `A → B → C`) into the hole so the whole
diagram type-checks and conserves — and the act of plugging *produces the receipt that discharges the
intent*. Receipt and intent annihilate into one completed turn:

```
  fulfill : Intent(A ⊢ C) ⊗ Morphism(A → C) ⟶ Receipt      (the hole is filled; co-receipt ↦ receipt)
```

In the coalgebra (`step : Carrier → Obs × (Admissible → Carrier)`): the **receipt is the output face**
(part of `Obs` — REORIENT face C, attestation, which we have); the **intent is the input-demand face**
— a constraint on which `Admissible` transitions are wanted, *plus the resources that fund them*.

---

## 2. The four faces of a Platonic intent

Generalizing the original conception ("a request for Something To Be Done with Resources To Do It
With"):

1. **Boundary (the type)** — `resources-offered : A  ⊗  outcomes-demanded : C`. The string-diagram
   interface / the typed hole. (dregg1's `MatchSpec` is a rich `C` side; the `A` side is thin.)
2. **Predicate (the requirement)** — a `Prop` on acceptable fillings: what counts as correct.
   (dregg1's `predicate_requirements` + Datalog `constraints`.)
3. **Resource (the funding)** — a **userspace-escrow cell-program** holding `A`, released to the
   filler exactly on the discharging receipt. ("Resources To Do It With" becomes first-class; this is
   where the escrow→userspace decision lands — an intent *is* escrow + a typed hole + a predicate.)
4. **Validity (the time)** — a **causal-or-frame** window, *typed* (§4). Replaces dregg1's raw
   `expiry: u64`. Anti-frontrunning becomes a causal type, not a timestamp race.

Fulfillment produces a conserved, attested receipt. The object unifies receipt⊣intent, demand⊣supply,
escrow, and time.

---

## 3. The adjunction: Need / Offer / Query is `Predicate ⊣ Witness`

dregg1's three-valued `IntentKind { Need, Offer, Query }` is one adjunction wearing three hats — our
already-proven `Laws` (`Predicate ⊣ Witness`, the demand⊣supply Galois connection):

- **Need** = the *predicate* / demand: "any filling must satisfy `P`."
- **Offer** = the *witness* / supply: "here is a morphism + a proof it satisfies `P`."
- **Query** = the *unit* / probe: "does a witness exist?" (discovery).

So intent inherits the whole Galois-connection theory for free; matching is the adjunction in action.

### Matching as a coend `∫^B` — the solver, first-class

Bilateral request-matching ("I want C, you offer C") is the easy case. A real **exchange** routes
demand to supply *through intermediate objects*: an intent `A ⊢ C` is filled by a chain
`A → B₁ → … → C` assembled from available offers, existentially over the intermediate `Bᵢ`. That
existential-over-the-middle is a **coend**:

```
  Match(A, C)  =  ∫^B  Offer(A → B) × Match(B, C)        (solver = coend assembly)
```

This is exactly what an intent **solver** does (route A→C through whatever B-steps exist), and it is
the profunctor-optic / Tambara-module composition law. Making the `∫^B` first-class from the start is
what makes dregg an *exchange*, not just a bilateral matcher — and it is the categorical content of an
AMM router, a multi-hop swap, a supply-chain of fulfillments.

**Tooling note:** the operadic substitution (plug a box into a hole) + the coend matching are the same
calculus as **profunctor optics** (get the resources / put the outcome) and **open games / compositional
game theory** (which are optic-based) — so the auction's mechanism-design content and the intent's
dataflow content share one formalism. See `INTENT-CO-RECEIPT-REFERENCES.md`.

---

## 4. Time, typed: causal vs frame (the relativistic innovation)

In a relativistic universe there is **no global "now"** — simultaneity is frame-dependent, so a raw
`expiry: u64` (dregg1) or a global `block_height` (the ledger world) presupposes a universal
simultaneity surface that does not exist. The honest model **refuses to conflate two different things
called "time"**:

- **Causal / ordering time** — *internal, monotone, verifiable*: happens-before, the lightcone partial
  order. This is the **lace / receipt chain**, which we maintain and proved monotone. A blocklace *is*
  a discrete causal set (the "volume" of a causal interval = its event count = "lace depth"). The
  causal order is the **more physical** of the two — frame-invariant — not the weaker cousin.
- **Per-cell proper time** — each cell's own monotone receipt chain (its worldline's proper time).
  Advances along the worldline; comparing two cells' proper times requires choosing a simultaneity
  surface.
- **Physical / wall-clock time** — irreducibly *external*: a **chosen reference frame** (a time
  authority's attestation), valid only within a **skew bound ±δ**. Byzantine clock-sync is literally
  "nodes computing an approximate common frame within bounded skew." Terrestrially δ ≈ µs and fine —
  but the model carries δ explicitly, never assumes it zero.

**The deadline language forces the distinction syntactically:**

```
  causal_after(event E)                 -- a lightcone fact: frame-invariant, on the lace, no trust
  frame_within(authority F, T, ±δ)      -- a frame convention: an attested predicate with explicit skew
```

You cannot write a deadline without declaring whether it is a **lightcone fact** or a **frame
convention** — so the relativistic honesty is load-bearing, not decorative. A court (or an
adjudicating cell) can always tell which *kind* of promise was made.

- **Anti-frontrunning** = "no one may fill before I reveal" = a **causal** constraint (happens-before
  on the lace) → *provably* enforced, not a timestamp gamble.
- **Wall-clock deadlines** (RFQ expiry, interest accrual) = **frame** predicates over a chosen
  time-authority issuer (reusing `Authority/Predicate` + `Credential` + discharge — *not* a new beacon
  portal; a "time authority" is a credential issuer whose attestation stream carries proven
  monotonicity + liveness + skew).
- **Single-machine principle** = the `n=1` / single-worldline limit: no spatial separation ⇒
  simultaneity unambiguous ⇒ all three times collapse to one local proper time. (Distribution =
  spacetime separation; the honest bounds are distributed bounds with a `c`-latency floor.)

---

## 5. DeFi as the natural application — with guarantees the others can't make

Every DeFi primitive = **intent + escrow + time + matching + conservation**, and each piece becomes
something formally held:

| Primitive | As intent-as-co-receipt | The guarantee we add |
|---|---|---|
| **Limit order / swap** | intent(give A, want C, price≥p) + escrow(A) + `causal` validity + solver-match | conservation (no value minted in the match, a kernel invariant); **frontrunning excluded** (ordering is a lightcone fact, not a gas race) |
| **AMM** | a *standing* Offer: a cell-program filling any swap on a pricing curve | curve invariant + conservation; the `∫^B` router is multi-hop by construction |
| **Lending** | intent(lend A, want A+interest by deadline) + escrow + `frame` deadline | interest is honestly wall-clock (attested frame + δ), liquidation a causal/frame condition |
| **Auction** (the gallery) | sealed-bid intents + escrow(bid) + `causal` reveal-order + winner predicate | conservation + sealed-bid privacy + **provable** no-reveal-before-commit |

**MEV is the control of the simultaneity surface** — who imposes a total order on intents. In a causal
model there is *no global order to capture*; fair ordering = "respect the lace's partial order + a fair
tie-break," which makes a class of MEV **structurally impossible** rather than auctioned. dregg's
causal-time-typing turns an economic problem into a typed invariant.

---

## 6. What dregg1 intent gets right / where it stops short

Right: content-addressed id, anonymous creator commitment, rich `MatchSpec` (action×resource, Datalog,
ZK `predicate_requirements`), anti-spam `stake_proof`, `fill_constraints` (partial-fill — DeFi already
anticipated). Stops short: **(1)** `expiry: u64` + `Constraint::NotExpiredAt(i64)` — the global-now
fiction (→ §4 causal/frame typing); **(2)** "Resources To Do It With" is just `min_budget` + a bond,
not a first-class escrowed bundle (→ §2 face 3); **(3)** `compound` is conjunction, not composition —
no dataflow / wiring (→ §3 the `∫^B` solver, string-diagram substitution); **(4)** Need/Offer/Query is
a flat enum, not recognized as one adjunction (→ §3).

---

## 7. First instance + open formalization questions

**First instance:** the gallery sealed-bid auction *is* an intent-matching system — build it against
this spine and prove (a) userspace-escrow ≥ kernel-escrow, (b) causal reveal-ordering excludes
frontrunning, (c) conservation across the settle. That proof validates the whole stack.

**Open (to formalize):**
- The receipt⊣intent adjunction *in Lean* (intent as a presheaf / the demand on the admissible
  alphabet; fulfillment as the counit).
- The `∫^B` solver-match as a coend / Tambara composition over the offer profunctor — and whether to
  reuse the optics already implicit in `JointTurn`/`Coordination`.
- The `causal_after` / `frame_within(F,T,δ)` deadline types, with `causal_after` grounded on the lace's
  partial order and `frame_within` as an attested `WitnessedPredicate` carrying δ.
- Conservation-across-a-fill as a corollary of the kernel per-asset invariant (the escrow inheritance).
- Open-game / compositional-mechanism framing of the auction (optic-based), tying the app's
  game-theory to the intent's dataflow via the shared optic calculus.

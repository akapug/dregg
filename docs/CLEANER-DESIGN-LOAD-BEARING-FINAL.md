# The Cleaner Design, Load-Bearing — final map across four dimensions

Status: **definitive design synthesis** (2026-07-12), from a two-round, 10-agent investigation (5 whole-system ideators
→ the eager synthesis `DREGGNET-CLEANER-DESIGN.md`; then 5 Surface-specific agents → `SURFACE-ONE-GATE-FOUR-PLANES.md`;
then 3 adversaries + 1 external-theory scholar over Session/Confinement/Verification). Every claim is grounded in the
real crates + the `Dregg2` Lean + the external literature. **This corrects the *algebra* asserted in
`DREGGNET-CLEANER-DESIGN.md`; the *duplication census* in that doc stands and is the real value.**

## The one finding (the same signature four times)

For **every** dimension the constructive synthesis over-collapsed in the **same** way: **the unification of the
*referee, the root, and the receipt-lens* is sound and worth doing; the *order/type algebra* asserted on top over-claims
a structure the code and the theory refute.** The traits/vocabularies the codebase already has (`Offering::type Session`
polymorphic; a rung-indexed report; the "attenuate-only + fail-closed + leaves a witness" shape) **already express the
correct unification** — a shared *interface/pattern*, not one carrier type. The collapse would *destroy* it.

> **Grow the proven core to fit the diversity — do not shrink the diversity to fit one carrier type.**

## The four-dimension map

| Dim | SOUND to unify (do) | OVER-CLAIM (refuted — don't) | KEEP DISTINCT (load-bearing) |
|---|---|---|---|
| **Surface** | the 2-D frustum gate (`is_attenuation ∧ read-cap-disclosure`); the `ViewNode → N backends` fan-out; receipts-leave-on-reads | "one `AffordanceSurface → lower → ViewNode`"; "`enabled = is_attenuation`"; "`project∘step` on every backend"; "N stateless backends"; "dual" / free `×` | **4 planes** (authority-actuation A / IR B *peer of A* / pixel-region C via opaque `Tile` / composition-ops D); the **4-conjunct gate** (`is_attenuation ∧ transition ∧ window ∧ disclosure` — last 3 Lean-proven irreducible); read/write **asymmetry** (`Offering = Σ over one Cell`) |
| **Session** | the **tenancy** object = c-list + receipt-fold; the metered-confined-**agent** family (`dregg_agent::Session`/`ConfinedSession`/`Hermes`/`Grain`/`Tenant.session`) genuinely unifies; use the real `ResidentBrain`, drop the mock | "~24 Sessions are one"; "`dregg_agent::Session` is canonical"; "one meter" | **transport-connection session** (CapTP vat / OSI-L5 — ephemeral, multiplexing, per-platform) **≠ tenancy session**; the canonical trunk is **lower**: `Cell · receipt-chain · lease/meter` (Lean names `Session:=Nat` = the GC epoch); **three meters** (tool-budget · rent-schedule · vat-phase); non-agent flavors (dungeon = replay-verified WorldCell, no lease/brain) stay peers |
| **Confinement** | **one `Referee::admit` evaluation point**; one root commitment; the "attenuate-only + fail-closed + witness" **shape** (the axis-disambiguation rename as *documentation*) | "three orthogonal axes = a free product lattice with one product `≼`"; "defense-in-depth = multiplication of 3 proven walls" | **authority is the only real product order** (`attenuate_le`, intra-axis); **ambient = `lower(authority)`** and **`Hosted` gates authority** (bidirectional dependency); **proof is *fibered over* ambient** (an OS escape forges the attested state) — a dependent order, not a product; the `*-property` is **proven partially OPEN** (`full_noninterference_fails`: deposit-signal + timing) so multiplication holds for **integrity only, not confidentiality**; the three teeth enforce at **three times in three processes** |
| **Verification** | one **rung-indexed** report/error; `*Receipt` retyped as **lenses** where they share a type (spween ≈ Offering literally share `TurnReceipt`); grain-R3 *is* the light-client leg (same `EngineSound` floor) | "4 rungs, each **strictly includes** the one below"; "one object, one root"; "any offering **inherits** rungs 2-3"; "`RecordVerify` = rung-1 replay" | rungs are an **orthogonal poset over scopes + trust-assumptions** (integrity/CRHF · transition-on-bound-inputs/determinism · checked-not-run/proof-soundness · canonicity/consensus) — inclusion fails **both** ways (zk-attest **hides** inputs replay binds; a light client **re-executes nothing**); **3 objects at 3 scopes over 3+ commitment schemes** (BLAKE3 blob vs Poseidon2 8-felt — identity only at the finalize re-stamp seam, 2 of ~51 effect families); rung 3 **unreachable-in-practice** (`WHOLE_HISTORY_GAP` — no rotated leg minted); `RecordVerify` is **rung0+rung1 on an untrusted transmitted record** |

## The genuinely-safe moves (measured duplications that survive scrutiny; each independently green; spine untouched)

These remove *real, counted* duplication without asserting any refuted algebra.

**Surface** (from `SURFACE-ONE-GATE-FOUR-PLANES.md`):
1. One affordance-transport codec (4 encodings of `{turn,arg}` → 1: `deos-view::{affordance_custom_id, parse_affordance_id}`).
2. Extract a `SurfaceBackend` trait in `deos-view`; move `dreggnet-web`/`telegram` renderers in; **delete the subset walkers**.
3. Dedupe `AffordanceSurface` (defined twice: starbridge-web-surface + deos-reflect).
4. `enabled` = the 2-D frustum **∧ `reactive_ok`** (as *one conjunct*, not the whole gate).
5. Bridge `deos-reflect::Presentation → ViewNode` (retire the parallel moldable projection).

**Session:**
6. Make `dreggnet-hermes`/`dreggnet-grain` present **over** the agent family (real `deos-hermes::ResidentBrain`; drop the mock-brain default) — the four agent-flavors genuinely share `{cell + receipt-chain + tool-budget + cap-bundle + brain}`. Keep `Offering::type Session` **polymorphic** (do NOT fix it to `Tenant`).
7. Collapse the **3 `LeaseTerms`** encodings (`hosted-lease::exec_terms_of` exists only to reconcile two) — verify it's the tenancy layer, keep the transport/connection session separate.

**Confinement:**
8. The axis-disambiguation **rename** (`Jail`/`EgressDoors`/`AuthorityProfile`/`HostFloor`) as *documentation of the shared shape* — but **do NOT** introduce `struct Confinement{authority, ambient, proof}` with a product `≼`. One `Referee::admit` evaluation point is fine; the product lattice is not.

**Verification:**
9. A `Rung` enum + receipts-as-lenses over `TurnReceipt` **where they share a type** (spween/Offering) — a rung-*indexed vocabulary*, **not** a strict-inclusion `TurnLadder`. Name grain + light-client as **distinct verifiers that compose at the head value**, and keep `WHOLE_HISTORY_GAP` explicit.

**Cross-cutting (from round 1, unrefuted):** the receipt/attestation family is large (125) and partly genuine duplication over `TurnReceipt` — but many witness **non-turn events** (I/O gates, message delivery, external-ledger attestations); a `ReceiptChain` trait is fine, folding all 125 into `TurnReceipt` lenses is not.

## What NOT to do
Do not build: one `AffordanceSurface`-that-lowers-to-`ViewNode`; `enabled = is_attenuation`; one concrete canonical `Session` absorbing the ~24 (or fixing `Offering::type Session`); `struct Confinement{...}` with a product `≼`; one `TurnLadder` with strict inclusion / one root / any-offering-inheritance. Each erases a distinction the repo's own Lean or the external literature refutes.

## Grounding
Lean: `Dregg2/Deos/*` (the 2-D frustum, `rerender_square` content-only, `Reactive.lean` irreducible gates, Compositor,
`membrane_two_viewers_distinct`); `CapTPGCConcrete.lean` (`Session:=Nat` = GC epoch), `Liveness.lean` (`Lease`);
`CredentialAttenuation.lean` (`attenuate_le` intra-authority), `InfoFlow/Confinement.lean` (`full_noninterference_fails`);
`WholeTurnTriangle.lean` + `AssuranceCaseGrounded.lean` (the `EngineSound` floor); `grain-verify` (`WHOLE_HISTORY_GAP`).
Theory: session types / CapTP vat / OSI-L5 (transport≠tenancy); Lampson-73 + Miller/Shapiro Capability-Myths +
Denning-76 + defense-in-depth-independence (confinement is a *dependent* order, covert channels are the total channel
set); Necula-Lee PCC + Valiant IVC + light-client (attestation is a *mode*, recursion *aggregates* within a mode; a
poset over scopes, not a ladder). **Signature everywhere: unify the referee/root/receipt-lens; keep the algebra (layer /
dependency / scope / read-write asymmetry) load-bearing and explicit.**

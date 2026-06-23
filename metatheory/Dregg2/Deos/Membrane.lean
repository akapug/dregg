/-
# Dregg2.Deos.Membrane — the rehydration membrane cannot amplify across hops (leg 2 of the crown).

`docs/deos/DEOS.md` §"the verified-deos program", target 2 (**Membrane non-amplification**):

  > The rehydration membrane composes `is_attenuation` across hops; prove `reshare A→B→C ⟹ C's
  > authority ⊆ B's held ⊆ A's` (the chained lattice law — lift the proven `is_attenuation` to
  > projection composition). The Rust `Membrane` in `starbridge-web-surface` is the realization; the
  > Lean is the proof it cannot amplify.

`docs/desktop-os-research/REHYDRATABLE-SURFACES.md` residual #1: "`Membrane::reshare` composes
attenuation across chained reacquisitions (A→B→C) by re-applying the REAL `is_attenuation` per hop,
refusing any hop where C would receive more than B held — the same `is_attenuation` lattice the cap
crown proves, lifted to projection composition."

This is NOT new mathematics. Each membrane hop is `Dregg2.Exec.attenuate` (the per-viewer projection),
and the chained-hop guarantee is `Dregg2.Exec.attenuate_subset` composed with `List.Subset.trans`. A
membrane reshare A→B→C is `attenuate (attenuate cap)`, and the keystone `reshare_chain_attenuates`
says C's conferred authority ⊆ B's held ⊆ A's — by transitivity of the EXISTING per-hop subset law.

## What is proven (all by REUSE — no membrane-local lattice)

  * `oneHop_attenuates` — a single membrane hop (one `attenuate`) confers a SUBSET of the held
    authority. This IS `Dregg2.Exec.attenuate_subset`, named as "one membrane projection".
  * `reshare` — the A→B→C reshare: `attenuate keepBC (attenuate keepAB cap)` — re-applying the REAL
    per-hop projection twice (the Rust `Membrane::reshare`). And `reshareN` — the n-hop chain,
    folding `attenuate` down a list of per-hop keep-sets.
  * **`reshare_chain_attenuates` (KEYSTONE)** — `reshare A→B→C ⟹ C ⊆ B ⊆ A`: the conferred authority
    after two hops is `⊆` after one hop is `⊆` the original held authority. The chained lattice law,
    `attenuate_subset` lifted to composition by `List.Subset.trans`. The proof the membrane cannot
    amplify across reacquisitions — by the existing kernel theorem, transitively.
  * `reshareN_attenuates` — the n-hop generalization: ANY chain of membrane reshares confers a subset
    of the original held authority (induction over the hop list). No matter how many times a surface
    is re-shared, the last holder's authority is bounded by the first holder's. Confinement survives
    arbitrarily-long delegation chains.
  * `reshare_refuses_amplification` — the negative tooth: if a hop's keep-set requests an authority
    the prior hop did not hold, that authority is NOT in the reshared cap's conferred set (a widening
    is darkened, not granted). A reshare cannot manufacture an authority a prior holder lacked.

Discipline: axiom-clean (`#assert_all_clean` at the close). `lake build
Dregg2` green (LOCAL). NO core-`Auth`/`Cap` edit — every hop is the REAL `Dregg2.Exec.attenuate` and
every subset is the REAL `capAuthConferred` ⊆; the membrane is a NAMING of iterated kernel attenuation.
-/
import Dregg2.Exec.AuthTurn
import Dregg2.Deos.Surface
import Dregg2.Tactics

namespace Dregg2.Deos.Membrane

open Dregg2.Authority (Cap Auth Label capAuthConferred)
open Dregg2.Exec (attenuate attenuate_subset)

/-! ## §1 — A membrane hop is a kernel attenuation (the per-viewer projection).

A membrane mediates a reacquisition: holder A hands holder B a view of a surface, attenuated to what B
may see. That hop is EXACTLY `Dregg2.Exec.attenuate` — the per-viewer projection. We name it and
restate its non-amplification. -/

/-- **`hop keep cap`** — one membrane reacquisition: project `cap` to keep only `keep` (the per-viewer
attenuation the membrane applies at the boundary). A NAMING of `Dregg2.Exec.attenuate` — no new
projection algebra. -/
def hop (keep : List Auth) (cap : Cap) : Cap := attenuate keep cap

/-- **A SINGLE MEMBRANE HOP ATTENUATES** — the authority conferred after one membrane projection is a
SUBSET of the held authority. This IS `Dregg2.Exec.attenuate_subset`, restated as "one membrane
reacquisition cannot amplify". The base case of the chain. -/
theorem oneHop_attenuates (keep : List Auth) (cap : Cap) :
    capAuthConferred (hop keep cap) ⊆ capAuthConferred cap :=
  attenuate_subset keep cap

/-! ## §2 — `reshare A→B→C`: re-applying the per-hop projection (the Rust `Membrane::reshare`).

The membrane reshare composes attenuation across chained reacquisitions: A→B keeps `keepAB`, then
B→C keeps `keepBC`. That is `hop keepBC (hop keepAB cap)` — re-applying the REAL `is_attenuation`
per hop, exactly as `starbridge-web-surface`'s `Membrane::reshare` does. -/

/-- **`reshare keepAB keepBC cap`** — the A→B→C two-hop reshare: A holds `cap`, projects to B keeping
`keepAB`, B re-shares to C keeping `keepBC`. `hop keepBC (hop keepAB cap)`. The Rust `Membrane::reshare`
(re-applying the REAL per-hop projection). -/
def reshare (keepAB keepBC : List Auth) (cap : Cap) : Cap := hop keepBC (hop keepAB cap)

/-- **`reshareN keeps cap`** — the n-hop reshare chain: fold `hop` down a list of per-hop keep-sets
(head = the FIRST hop A→B, applied first). Models a surface re-shared through an arbitrary delegation
chain A→B→C→…→Z, each hop the membrane's per-viewer projection. -/
def reshareN : List (List Auth) → Cap → Cap
  | [],            cap => cap
  | keep :: rest,  cap => reshareN rest (hop keep cap)

/-! ## §3 — THE KEYSTONE: the membrane cannot amplify across hops.

`reshare A→B→C ⟹ C ⊆ B ⊆ A`. The conferred authority after two membrane hops is `⊆` after one hop is
`⊆` the original held authority — the chained lattice law, `attenuate_subset` lifted to composition by
`List.Subset.trans`. The proof the membrane cannot amplify across reacquisitions. -/

/-- **THE TWO-HOP NON-AMPLIFICATION KEYSTONE.** `reshare A→B→C` confers a SUBSET of A's held
authority: C's conferred authority ⊆ B's conferred authority ⊆ A's held authority. The membrane
re-applies the REAL per-hop `is_attenuation` (`attenuate_subset`) at each hop, and the two subset
facts compose by `List.Subset.trans` — so a reshared surface, two hops out, grants no more than the
original holder held. The `docs/deos/DEOS.md` target-2 statement, as a theorem. -/
theorem reshare_chain_attenuates (keepAB keepBC : List Auth) (cap : Cap) :
    capAuthConferred (reshare keepAB keepBC cap) ⊆ capAuthConferred cap := by
  -- C ⊆ B (second hop) and B ⊆ A (first hop); compose by transitivity of ⊆ on the conferred lists.
  have hBC : capAuthConferred (hop keepBC (hop keepAB cap)) ⊆ capAuthConferred (hop keepAB cap) :=
    oneHop_attenuates keepBC (hop keepAB cap)
  have hAB : capAuthConferred (hop keepAB cap) ⊆ capAuthConferred cap :=
    oneHop_attenuates keepAB cap
  exact List.Subset.trans hBC hAB

/-- **THE MIDDLE-HOLDER BOUND** (the `C ⊆ B` half, stated explicitly for the doc's "⊆ B's held"
clause). The reshared cap C confers a subset of what the MIDDLE holder B held — so even ignoring A, C
never exceeds its immediate grantor B. The membrane bounds each hop locally, not just end-to-end. -/
theorem reshare_bounded_by_middle (keepAB keepBC : List Auth) (cap : Cap) :
    capAuthConferred (reshare keepAB keepBC cap) ⊆ capAuthConferred (hop keepAB cap) :=
  oneHop_attenuates keepBC (hop keepAB cap)

/-- **THE n-HOP GENERALIZATION.** ANY chain of membrane reshares confers a subset of the original held
authority: `reshareN keeps cap ⊆ cap` for every hop-list `keeps`. By induction over the chain — each
hop attenuates (`oneHop_attenuates`) and the inductive hypothesis bounds the tail; `List.Subset.trans`
composes. So no matter how many times a surface is re-shared down a delegation chain, the last holder's
authority is bounded by the first holder's. Confinement survives arbitrarily-long reacquisition
chains. -/
theorem reshareN_attenuates (keeps : List (List Auth)) (cap : Cap) :
    capAuthConferred (reshareN keeps cap) ⊆ capAuthConferred cap := by
  induction keeps generalizing cap with
  | nil => exact fun a ha => ha          -- no hops: identity, conferred set unchanged
  | cons keep rest ih =>
    -- reshareN (keep :: rest) cap = reshareN rest (hop keep cap); tail bound ∘ one-hop bound.
    have htail : capAuthConferred (reshareN rest (hop keep cap)) ⊆ capAuthConferred (hop keep cap) :=
      ih (hop keep cap)
    have hhead : capAuthConferred (hop keep cap) ⊆ capAuthConferred cap :=
      oneHop_attenuates keep cap
    exact List.Subset.trans htail hhead

/-! ## §4 — THE NEGATIVE TOOTH: a reshare cannot manufacture an unheld authority.

A widening is DARKENED, not granted: if a hop requests (via `keep`) an authority the prior hop did not
hold, that authority is simply absent from the reshared cap's conferred set — `attenuate` filters it
out. So a reshare cannot grant an authority a prior holder lacked, even if the keep-set names it. -/

/-- **A RESHARE CANNOT GRANT AN UNHELD AUTHORITY** (the anti-amplification tooth). If `a` is NOT in
A's held authority, then `a` is NOT in the conferred authority of ANY reshare of A's cap (one hop or a
whole chain) — because every hop is `⊆`-bounded by A (`reshareN_attenuates`). So naming `a` in a
downstream keep-set does not conjure it: the membrane refuses to amplify into an authority no prior
holder had. -/
theorem reshare_refuses_amplification (keeps : List (List Auth)) (cap : Cap) (a : Auth)
    (hunheld : a ∉ capAuthConferred cap) :
    a ∉ capAuthConferred (reshareN keeps cap) := by
  intro hmem
  exact hunheld (reshareN_attenuates keeps cap hmem)

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the chain attenuation BITES, both polarities. -/

section Witnesses

open Dregg2.Deos.Surface (Surface interactiveSurface)

/-- A full interactive surface on cell `7`: holder A may write, read, and grant. -/
def egA : Cap := Surface 7 [Auth.write, Auth.read, Auth.grant]

-- A→B keeps {write, read} (drop grant); B→C keeps {read} (drop write). C ends VIEW-only.
def egC : Cap := reshare [Auth.write, Auth.read] [Auth.read] egA

-- The two-hop reshare attenuated to exactly [read]: C holds a view-only surface (chain shrank A→C):
#guard capAuthConferred egC == [Auth.read]
-- A held grant; C does NOT (the chain darkened it — amplification refused across hops):
#guard (Auth.grant ∈ capAuthConferred egA : Bool)
#guard !(Auth.grant ∈ capAuthConferred egC : Bool)
-- A held write; C does NOT (the second hop dropped it):
#guard !(Auth.write ∈ capAuthConferred egC : Bool)
-- a 4-hop chain keeping ever-less ends at most read-only; never grows back grant/write:
#guard capAuthConferred (reshareN [[Auth.write, Auth.read], [Auth.read], [Auth.read], [Auth.read]] egA)
        == [Auth.read]
#guard !(Auth.grant ∈ capAuthConferred
          (reshareN [[Auth.write, Auth.read], [Auth.read], [Auth.read]] egA) : Bool)
-- AMPLIFICATION REFUSED: a downstream hop naming `grant` (which the prior hop dropped) does NOT regrant
-- it — the reshared cap still lacks grant (the filter darkens an unheld request):
#guard !(Auth.grant ∈ capAuthConferred (reshare [Auth.read] [Auth.read, Auth.grant] egA) : Bool)
-- and an authority A NEVER held (`call`) is absent from any reshare, even if a keep-set names it:
#guard !(Auth.call ∈ capAuthConferred (reshareN [[Auth.call], [Auth.call]] egA) : Bool)

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  oneHop_attenuates,
  reshare_chain_attenuates,
  reshare_bounded_by_middle,
  reshareN_attenuates,
  reshare_refuses_amplification
]

end Dregg2.Deos.Membrane

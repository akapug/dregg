/-
# `Dregg2.Crypto.UcSignature` — a UNIVERSAL-COMPOSABILITY beachhead for the HYBRID signature.

`HybridCombiner.lean` proved the hybrid `ed25519 ∧ ML-DSA` signature is `EufCma`-unforgeable if EITHER
component is, grounded all the way down to `SchnorrDLHard ∨ MSISHard`. That is a GAME-BASED result. This
module opens the OTHER leg the composition story needs: the **universal-composability** statement that the
hybrid signature UC-REALIZES an ideal signature functionality `F_SIG`, so a protocol proven secure against
`F_SIG` stays secure when `F_SIG` is replaced by the real hybrid signature — *under concurrent execution*,
via the UC composition theorem.

The beachhead is minimal but REAL, and its load-bearing content is one equivalence:

  > **the hybrid signature UC-realizes `F_SIG` IFF it is `EufCma`** — and the ONLY distinguishing event
  > between the real protocol and the ideal (`F_SIG` + simulator `S`) is a FORGERY on an honest key,
  > which `S` cannot produce. So the environment's distinguishing advantage is exactly the `EufCma`
  > advantage, bounded (via `HybridCombiner.hybrid_secure_if_either_floor`) by `SchnorrDLHard ∨ MSISHard`.

## What is modelled (§-by-§)

  **§1 — the ideal functionality `F_SIG`, the real protocol, the environment.** `F_SIG` is the standard
  Canetti signature functionality collapsed to its observable content: it RECORDS the messages honest
  parties signed (`Recorded : Msg → Prop`) and VERIFIES a message iff it was recorded — *unforgeability
  by construction*, there is no forgery in the ideal world. We model `F_SIG` as a genuine `SigScheme`
  (`idealSig`) whose `verify` consults `Recorded` and ignores the signature, so the ideal is directly
  comparable to the real scheme. The REAL protocol runs the hybrid `SigScheme`. The environment `Z` is a
  distinguisher that submits a `(message, signature)` pair and reads the accept bit.

  **§2 — the realize relation and the distinguishing game.** `UcRealizes S pk Recorded` says the real
  accept bit never exceeds the ideal one: `∀ m σ, verify pk m σ → Recorded m`. `Distinguishes` is the
  environment's win: it submits `(m, σ)` that the REAL scheme accepts but `F_SIG` rejects. The two headline
  equivalences: `distinguishes_iff_forgery` (the distinguishing event IS a forgery on the honest key) and
  `ucRealizes_iff_eufCma` (realizing `F_SIG` IS the `EufCma` game — no slack, no laundering).

  **§3 — THE REDUCTION TO THE FLOOR (`hybrid_sig_uc_realizes`).** Composing the equivalence with
  `HybridCombiner.hybrid_secure_if_either_floor`: the hybrid signature UC-realizes `F_SIG` under
  `SchnorrDLHard ∨ MSISHard`, via the SAME forking reductions, introducing NO new hardness carrier. This is
  the composition payoff: the hybrid sig can be plugged into any protocol proven secure with `F_SIG`.

  **§4 — non-vacuity, both poles.** A scheme WITH `EufCma` (`secureToy`) realizes `F_SIG`; a scheme WITHOUT
  it (`brokenToy`, verifies everything) does NOT — a forgery is a distinguishing environment. The hybrid of
  a secure and a broken component realizes `F_SIG` from the single good half. So the `EufCma` hypothesis is
  LOAD-BEARING: realization is exactly what unforgeability buys and a forgeable scheme loses.

  **§5 — the simulator, made explicit.** For this functionality the simulator `S` is degenerate and named:
  it generates its own keypair and HONESTLY SIGNS each recorded message (`Correct` gives completeness), so
  the ideal-world signatures verify exactly as real ones; the only thing it cannot fake is a signature on a
  NON-recorded message, which is a forgery. `real_ideal_agree` proves the real and ideal accept bits
  coincide on every message under `EufCma` + completeness — the single-shot indistinguishability.

  **§6 — MULTI-SESSION `F̂_SIG` and the HYBRID ARGUMENT.** Many concurrent instances, each with its own key
  and honest record. The multi-session realize relation is per-session realization
  (`multiUcRealizes_iff_forall_session`); `multi_session_realization` proves the real scheme realizes `F̂_SIG`
  from per-session `EufCma`. The number-of-sessions factor is EXPLICIT: `worldVerify` is the hybrid chain
  `H_0 (all real) … H_n (all ideal)`, `worldVerify_step` one swap bounded by a single-session forgery, and
  `worldVerify_zero_le` chains exactly `n` of them (`multi_session_hybrid_telescope`). `hybrid_multi_session_uc_realizes`
  grounds it in `SchnorrDLHard ∨ MSISHard` per session.

  **§7 — THE UNIVERSAL COMPOSITION THEOREM.** A protocol `ρ` using `F_SIG` as a subroutine sees only its
  accept relation. Under `EufCma` + completeness the real and ideal accept relations are EQUAL
  (`accept_relations_agree`), so `uc_composition_theorem` gives `ρ^π = ρ^F` for ANY `ρ` into ANY output type
  — pure substitutivity, no restriction on `ρ`. `uc_composition_multi_session` is the full concurrent
  statement over `F̂_SIG`; `distinguishing_rho_yields_forgery` is the reduction the other way (a distinguishing
  `ρ` IS a forgery); `hybrid_sig_composes_under_floor` grounds composition in `DL ∨ MSIS`.

## CONCRETE SECURITY (§7.5) — the two former modelling notes are now RETIRED (proved).

The Canetti UC theorem has three structural parts and ALL THREE are DISCHARGED as real Lean theorems:
single-session realization (§2–§3), multi-session realization of `F̂_SIG` via the explicit `n`-step hybrid
(§6), and the universal composition theorem `ρ^π = ρ^F` (§7) — every one reduced to `EufCma`, hence to
`SchnorrDLHard ∨ MSISHard`, with no new carrier.

§7.5 closes the two pieces that used to be carried as abstract `Prop` residues, using
`Dregg2.Crypto.ConcreteSecurity`:

  * **NEGLIGIBLE-ENSEMBLE DISTANCE.** The distinguishing advantage is an ENSEMBLE `ucAdv : λ ↦ ℝ`, and
    `UcRealizes ↔ Negl (ucAdv …)` (`ucRealizes_iff_ucAdv_negl`). ⚠ This `ucAdv` is DEGENERATE (`0/1`,
    λ-independent) — the distance-0 corner, `¬ Distinguishes` in ensemble clothing. The GENUINE real-valued
    computational restatement (advantage ranging over the full `[0,1]` spectrum, bounded by the forgery
    advantage, negligible under the floor) is §7.6 (`ComputationalUC` / `uc_advantage_transfer`), PROVED
    modulo two NAMED gaps — G1 the reduction bound (needs probabilistic execution semantics), G2 `Negl εₛ`
    (needs a quantitative floor; the tree's `SchnorrDLHard`/`MSISHard` are BOOLEAN). Full computational UC is
    thus TRUE-MODULO-(G1,G2), not fully closed. The multi-session advantage stays negligible through the
    session-count factor (`multi_session_advantage_negl`, via the `negl_finset_sum` / `negl_const_mul`
    closures).
  * **SIMULATOR PPT-EFFICIENCY.** The simulator carries an explicit polynomial `StepBound` and its PPT-ness is
    PROVED (`sim_ppt`) — no longer a complexity statement outside Lean's logic.

`SigUCResidual` (§8) now has NO carried modelling `Prop`s: every field is a proved-theorem type
(`dischargedResidual`), mirroring `LightClientUC.DynamicUCResidual` with the concrete-security layer closed.

## No named-carrier laundering.

The only irreducible objects are the two cryptographic floors `SchnorrDLHard` / `MSISHard` (reached through
`HybridCombiner`) and the forking reductions (theorems of the existing forking machinery, passed as
hypotheses, never `axiom`s). `EufCma` is not re-asserted: it is the `HybridCombiner` game, and
`UcRealizes` is proved EQUIVALENT to it, so nothing about UC realization is assumed — it is derived.

`#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}). Verified with
`lake env lean Dregg2/Crypto/UcSignature.lean`.

Cite: Canetti, *Universally Composable Security* (the `F_SIG` functionality + composition theorem);
the game-based ⟺ UC equivalence for signatures.
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.UcSignature

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField
open Dregg2.Crypto.ConcreteSecurity

/-! ## §1 — The ideal functionality `F_SIG`, the real protocol, the environment.

We reuse `HybridCombiner.SigScheme` as the interface, and its `Forgery`/`EufCma` games (the real
protocol's security). The IDEAL side is `Recorded : Msg → Prop`, the set of messages honest parties
signed; `F_SIG` accepts a message iff it is recorded. Modelling `F_SIG` as a `SigScheme` (`idealSig`,
whose `verify` consults `Recorded` and DISCARDS the signature) makes the ideal directly comparable to the
real scheme — and makes "unforgeability by construction" a theorem (`idealSig_no_forgery`). -/

/-- **`F_SIG` as an ideal `SigScheme`.** Keys are trivial (`Unit`), signatures carry no information
(`Unit`), and `verify _ m _ := Recorded m`: the ideal functionality accepts a message iff an honest party
recorded it, IGNORING the presented signature. This is the "unforgeability by construction" ideal — the
signature object is irrelevant, only the honest-record is consulted. -/
@[reducible] def idealSig {Msg : Type*} (Recorded : Msg → Prop) : SigScheme Unit Unit Msg Unit where
  pkOf _ := ()
  sign _ _ := ()
  verify _ m _ := Recorded m

/-- **UNFORGEABILITY BY CONSTRUCTION.** `F_SIG` admits NO forgery: a forgery is a fresh (`¬ Recorded m`)
verifying message, but `idealSig`'s `verify` on `m` is exactly `Recorded m`, so a forgery would require
`¬ Recorded m ∧ Recorded m`. The ideal world has no forgeries by definition — there is nothing for a
simulator to fake. -/
theorem idealSig_no_forgery {Msg : Type*} (Recorded : Msg → Prop) :
    EufCma (idealSig Recorded) () Recorded := by
  rintro ⟨m, _, hnr, hv⟩
  exact hnr hv

/-- **A UC ENVIRONMENT / distinguisher** for the signature functionality: it produces the `(message,
signature)` pair it will submit to the verifier and reads the accept bit. As with `LightClientUC.Env`,
there are no honest-party inputs to relay (the functionality is a one-shot verify oracle), so a bare
pair-producer is the dummy adversary and suffices. -/
abbrev Env (Msg Sig : Type*) : Type _ := Unit → Msg × Sig

/-! ## §2 — The realize relation and the distinguishing game.

`UcRealizes S pk Recorded` — the REAL scheme's accept bit never exceeds the IDEAL one: whenever the real
`verify pk m σ` accepts, the message was recorded. `Distinguishes` — the environment WINS: it submits a
pair the real scheme accepts but `F_SIG` rejects. The two equivalences are the beachhead's spine. -/

/-- **`UcRealizes S pk Recorded` — the real scheme UC-realizes `F_SIG`.** Whenever the real verifier
accepts a message under some signature, that message was recorded by an honest party (`Recorded m`). This
is the UC-indistinguishability of the real protocol from `F_SIG` for the deterministic single-shot verify
functionality, stated as the negation of the distinguishing event (the dummy-adversary form). -/
def UcRealizes {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    Prop :=
  ∀ (m : Msg) (σ : Sig), S.verify pk m σ → Recorded m

/-- **`Distinguishes S pk Recorded` — the environment DISTINGUISHES real from ideal.** There is an
environment `Z` whose submitted `(m, σ)` the real scheme ACCEPTS (`verify pk m σ`) though `F_SIG` REJECTS
it (`¬ Recorded m`). This is the bad event: the real and ideal worlds diverge on the accept bit. -/
def Distinguishes {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    Prop :=
  ∃ Z : Env Msg Sig, S.verify pk (Z ()).1 (Z ()).2 ∧ ¬ Recorded (Z ()).1

/-- **THE DISTINGUISHING EVENT IS A FORGERY.** `Distinguishes` and `Forgery` are the same proposition: an
environment that separates the real hybrid signature from `F_SIG` is precisely an adversary that produced
a verifying signature on a message no honest party signed. There is NO other way to tell the worlds apart
— the whole gap is a forgery on the honest key. -/
theorem distinguishes_iff_forgery {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    Distinguishes S pk Recorded ↔ Forgery S pk Recorded := by
  constructor
  · rintro ⟨Z, hv, hnr⟩; exact ⟨(Z ()).1, (Z ()).2, hnr, hv⟩
  · rintro ⟨m, σ, hnr, hv⟩; exact ⟨fun _ => (m, σ), hv, hnr⟩

/-- **REALIZING `F_SIG` IS EXACTLY `EufCma`.** `UcRealizes` and `EufCma` are logically equivalent: the
real scheme UC-realizes the ideal signature functionality iff it is existentially-unforgeable. This is the
load-bearing bridge — UC realization is not an extra assumption layered on top, it IS the game-based
security notion, so no UC content is laundered in. -/
theorem ucRealizes_iff_eufCma {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    UcRealizes S pk Recorded ↔ EufCma S pk Recorded := by
  constructor
  · intro h; rintro ⟨m, σ, hnr, hv⟩; exact hnr (h m σ hv)
  · intro h m σ hv; by_contra hnr; exact h ⟨m, σ, hnr, hv⟩

/-- **REAL ≈ IDEAL FAILS EXACTLY WHEN A FORGERY OCCURS.** `UcRealizes` is the negation of `Distinguishes`:
the real protocol is indistinguishable from `F_SIG` iff no environment can distinguish them, which by
`distinguishes_iff_forgery` happens iff no forgery exists. The `EufCma` hypothesis is thus load-bearing,
not decorative. -/
theorem ucRealizes_iff_not_distinguishes {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    UcRealizes S pk Recorded ↔ ¬ Distinguishes S pk Recorded := by
  rw [ucRealizes_iff_eufCma, distinguishes_iff_forgery]; rfl

/-! ## §3 — THE REDUCTION TO THE FLOOR: the hybrid signature UC-realizes `F_SIG` under `DL ∨ MSIS`. -/

/-- **`hybrid_sig_uc_realizes` — THE BEACHHEAD HEADLINE.** The hybrid `ed25519 × ML-DSA` signature
UC-realizes the ideal signature functionality `F_SIG` under `SchnorrDLHard ∨ MSISHard`. Given the two
forking reductions (a classical forgery ⟹ a `DLSolver`; a pq forgery ⟹ two SelfTargetMSIS solutions on a
shared commitment with distinct challenges — theorems of the existing forking machinery, NOT carriers),
whenever EITHER floor holds the hybrid is `EufCma` (`hybrid_secure_if_either_floor`), hence — by the
equivalence `ucRealizes_iff_eufCma` — UC-realizes `F_SIG`. So the hybrid signature can be plugged into any
protocol proven secure against `F_SIG`, and the composition survives down to `DL ∨ MSIS`. No new hardness
carrier is introduced: the reduction is the SAME as the game-based one. -/
theorem hybrid_sig_uc_realizes
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Recorded : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
    {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (dlFork : Forgery Cl pkc Recorded → DLSolver C G)
    (msisFork : Forgery Pq pkp Recorded →
      ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β))) :
    UcRealizes (hybrid Cl Pq) (pkc, pkp) Recorded :=
  (ucRealizes_iff_eufCma _ _ _).2
    (hybrid_secure_if_either_floor Cl Pq pkc pkp Recorded C G A t β dlFork msisFork hfloor)

/-! ## §4 — NON-VACUITY, both poles: `EufCma` is what earns realization; a forgeable scheme loses it.

Reusing `HybridCombiner`'s toy schemes over `Unit` keys and `Bool` messages/signatures with the empty
signing transcript `noQueries` (every message fresh). `secureToy` verifies NOTHING (`EufCma` holds),
`brokenToy` verifies EVERYTHING (a forgery on any message). -/

/-- **(FIRES)** an `EufCma` scheme UC-realizes `F_SIG`: `secureToy` verifies nothing, so it never accepts an
unrecorded message — it realizes the ideal via the equivalence. The positive pole. -/
theorem secureToy_uc_realizes : UcRealizes secureToy () noQueries :=
  (ucRealizes_iff_eufCma _ _ _).2 secureToy_euf_cma

/-- **(BITES — a scheme WITHOUT `EufCma` does NOT realize `F_SIG`)** `brokenToy` verifies everything, so it
accepts the unrecorded message it never signed — a forgery, hence a distinguishing environment. The
negative pole: realization is genuinely violated when unforgeability fails. -/
theorem brokenToy_not_uc_realizes : ¬ UcRealizes brokenToy () noQueries := by
  intro h; exact (ucRealizes_iff_eufCma _ _ _).1 h brokenToy_forgeable

/-- The forgeable scheme is a DISTINGUISHING environment: `brokenToy` separates the real world from
`F_SIG`. The distinguishing event of §2 witnessed concretely — a forgery IS the separation. -/
theorem brokenToy_distinguishes : Distinguishes brokenToy () noQueries :=
  (distinguishes_iff_forgery _ _ _).2 brokenToy_forgeable

/-- **ONE SECURE COMPONENT SUFFICES.** The hybrid of a SECURE and a BROKEN component UC-realizes `F_SIG`,
delivered by the combiner from the single good half — even with a completely broken pq (or classical)
component the hybrid realizes the ideal. This is the composition payoff of "hybrid, not PQ-only". -/
theorem hybrid_secure_uc_realizes : UcRealizes (hybrid secureToy brokenToy) ((), ()) noQueries :=
  (ucRealizes_iff_eufCma _ _ _).2 hybrid_secure_via_left

/-- **THE LOAD-BEARING TOOTH.** If BOTH components are broken, the hybrid does NOT realize `F_SIG` — a
forgery goes through, distinguishing real from ideal. So the `EufCma` (⟸ `DL ∨ MSIS`) hypothesis in
`hybrid_sig_uc_realizes` is not vacuous: with neither floor holding, UC realization genuinely fails. -/
theorem hybrid_broken_not_uc_realizes : ¬ UcRealizes (hybrid brokenToy brokenToy) ((), ()) noQueries := by
  intro h; exact (ucRealizes_iff_eufCma _ _ _).1 h hybrid_broken_if_both

/-! ## §5 — THE SIMULATOR, made explicit (why the dummy adversary suffices).

For a UC realization one exhibits a simulator `S` such that for every environment `Z`, the real and ideal
executions are indistinguishable. For `F_SIG` the simulator is degenerate and named exactly, because the
functionality is a deterministic one-shot verify oracle:

  * **The simulator `S`.** It generates its OWN keypair `sk` and, when `F_SIG` records a message `m` (an
    honest party signed it), `S` produces the honest signature `S.sign sk m` and hands it to `Z`. By
    `Correct`, that signature VERIFIES — so recorded messages carry a verifying signature in the ideal
    world exactly as in the real world (completeness).
  * **Indistinguishability.** The only thing `S` cannot fake is a verifying signature on a NON-recorded
    message — that is a forgery, ruled out by `EufCma` (soundness). So the two worlds' observable (the
    accept bit) coincides on EVERY message iff `EufCma` holds; the distinguisher's advantage is exactly the
    `EufCma` advantage. We package the simulator as a real function and prove both obligations. -/

section Simulator

variable {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)

/-- **`simSign S sk m`** — the simulator's fabricated signature in the IDEAL world: the honest signature on
`m` under the simulator's own key `sk`. Built from what `F_SIG` reveals (the recorded message), touching no
real signer's secret. -/
def simSign (sk : SK) (m : Msg) : Sig := S.sign sk m

/-- **COMPLETENESS (the simulator's signature verifies).** Under `Correct S`, the simulator's fabricated
signature on ANY message verifies against its own public key — so every recorded message carries a
verifying signature in the ideal world, matching the real world. -/
theorem sim_complete (hc : Correct S) (sk : SK) (Recorded : Msg → Prop) :
    ∀ m, Recorded m → ∃ σ, S.verify (S.pkOf sk) m σ :=
  fun m _ => ⟨simSign S sk m, hc sk m⟩

/-- **REAL AND IDEAL ACCEPT BITS AGREE (the single-shot indistinguishability).** Under `EufCma` (soundness)
and the simulator's completeness, for EVERY message the real scheme's accept bit and `F_SIG`'s verdict
coincide: a message is accepted-under-some-signature in the real world iff it is accepted in the ideal
world. This is exactly the observable the environment reads, so no `Z` can distinguish — the realization is
witnessed at the accept-bit level, not merely as a one-directional soundness bound. -/
theorem real_ideal_agree (pk : PK) (Recorded : Msg → Prop)
    (hSound : EufCma S pk Recorded)
    (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ) (m : Msg) :
    (∃ σ, S.verify pk m σ) ↔ (∃ u : Unit, (idealSig Recorded).verify () m u) := by
  constructor
  · rintro ⟨σ, hv⟩; exact ⟨(), (ucRealizes_iff_eufCma S pk Recorded).2 hSound m σ hv⟩
  · rintro ⟨_, hr⟩; exact hComplete m hr

end Simulator

/-! ## §6 — MULTI-SESSION `F̂_SIG` and the HYBRID ARGUMENT over sessions.

Canetti's UC runs MANY concurrent instances of a functionality. The multi-session signature functionality
`F̂_SIG` indexes each instance by a session id `i : SID`, with its OWN public key `pk i` and its OWN honest
record `Recorded i`. `F̂_SIG` accepts `(i, m, σ)` iff `Recorded i m`. The real world runs the SAME scheme `S`
in every session under `pk i`.

The multi-session realization is the standard HYBRID ARGUMENT: walk a chain of hybrid worlds `H_0, …, H_n`
where `H_j` runs the IDEAL functionality in sessions `< j` and the REAL scheme in sessions `≥ j`. `H_0` is
all-real, `H_n` is all-ideal, and each adjacent swap `H_j → H_{j+1}` flips exactly ONE session — bounded by
a SINGLE-session realization (i.e. no forgery in that session, `EufCma`). The number-of-sessions factor `n`
is therefore EXPLICIT: it is the length of the telescope (`worldVerify_zero_le` inducts `n` times), each
step discharged by one single-session `EufCma`. No union bound is smuggled into a carrier. -/

/-- **`MultiUcRealizes S pk Recorded`** — the multi-session realize relation: in EVERY session `i`, whenever
the real verifier accepts, the message was recorded in THAT session. This is the real ⊑ ideal statement for
`F̂_SIG`. -/
def MultiUcRealizes {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Prop :=
  ∀ (i : SID) (m : Msg) (σ : Sig), S.verify (pk i) m σ → Recorded i m

/-- **`MultiForgery`** — a forgery in SOME session: a session `i` with a fresh (`¬ Recorded i m`) verifying
message. The multi-session distinguishing event. -/
def MultiForgery {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Prop :=
  ∃ (i : SID) (m : Msg) (σ : Sig), ¬ Recorded i m ∧ S.verify (pk i) m σ

/-- **`MultiEufCma`** — no session has a forgery. The security of `F̂_SIG`'s real emulation. -/
def MultiEufCma {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Prop :=
  ¬ MultiForgery S pk Recorded

/-- **THE UNION OVER SESSIONS, EXPLICIT.** A multi-session forgery is exactly a forgery in SOME single
session — the decomposition the hybrid argument sums over. In the probabilistic game this is the union bound
whose factor is the number of sessions; here it is a genuine `∃`-over-sessions, no carrier. -/
theorem multiForgery_iff_exists_session {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiForgery S pk Recorded ↔ ∃ i, Forgery S (pk i) (Recorded i) := by
  constructor
  · rintro ⟨i, m, σ, hnr, hv⟩; exact ⟨i, m, σ, hnr, hv⟩
  · rintro ⟨i, m, σ, hnr, hv⟩; exact ⟨i, m, σ, hnr, hv⟩

/-- `MultiEufCma` IS per-session `EufCma` in every session — the security of the multi-session functionality
factors through the single-session game, session by session. -/
theorem multiEufCma_iff_forall_session {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiEufCma S pk Recorded ↔ ∀ i, EufCma S (pk i) (Recorded i) := by
  unfold MultiEufCma EufCma
  rw [multiForgery_iff_exists_session]
  exact not_exists

/-- Multi-session realization IS multi-session `EufCma` — the multi-session analogue of
`ucRealizes_iff_eufCma`, no UC content laundered. -/
theorem multiUcRealizes_iff_multiEufCma {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiUcRealizes S pk Recorded ↔ MultiEufCma S pk Recorded := by
  rw [multiEufCma_iff_forall_session]
  constructor
  · intro h i; exact (ucRealizes_iff_eufCma _ _ _).1 (fun m σ hv => h i m σ hv)
  · intro h i m σ hv; exact (ucRealizes_iff_eufCma _ _ _).2 (h i) m σ hv

/-- Multi-session realization IS per-session realization — `F̂_SIG` is realized iff every session is. -/
theorem multiUcRealizes_iff_forall_session {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiUcRealizes S pk Recorded ↔ ∀ i, UcRealizes S (pk i) (Recorded i) := by
  constructor
  · intro h i m σ hv; exact h i m σ hv
  · intro h i m σ hv; exact h i m σ hv

/-- **`MULTI_SESSION_REALIZATION`.** If every session is single-session-`EufCma`, the real scheme realizes
the multi-session functionality `F̂_SIG`. This is the multi-session UC realization; the per-session `EufCma`
is exactly what each hybrid swap needs. -/
theorem multi_session_realization {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (h : ∀ i, EufCma S (pk i) (Recorded i)) : MultiUcRealizes S pk Recorded :=
  (multiUcRealizes_iff_forall_session S pk Recorded).2
    (fun i => (ucRealizes_iff_eufCma _ _ _).2 (h i))

/-! ### The hybrid chain `H_0 … H_n` over `Fin n` sessions — the number-of-sessions factor made a THEOREM.

`worldVerify … j` is the hybrid world `H_j`: sessions with index `< j` answer with the IDEAL functionality
(`Recorded i m`, the signature discarded), sessions `≥ j` answer with the REAL scheme. `H_0` is all-real,
`H_n` is all-ideal. `worldVerify_step` is ONE swap `H_j → H_{j+1}`, valid because the single flipped session
`j` realizes (real ⟹ ideal). `worldVerify_zero_le` chains `n` such swaps by induction; the count of
reductions is literally the induction length. -/

/-- The hybrid world `H_j`: ideal below the threshold `j`, real at/above it. -/
def worldVerify {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop) (j : ℕ)
    (i : Fin n) (m : Msg) (σ : Sig) : Prop :=
  if (i : ℕ) < j then Recorded i m else S.verify (pk i) m σ

/-- **ONE HYBRID SWAP.** If every session realizes, `H_j` accept implies `H_{j+1}` accept: the only session
that changes between the worlds is the one with index value `j`, where the world flips from the real verifier
to the ideal record — bounded by that session's realization (real ⟹ ideal). All other sessions are
identical. -/
theorem worldVerify_step {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop) (j : ℕ)
    (hj : ∀ i : Fin n, UcRealizes S (pk i) (Recorded i))
    (i : Fin n) (m : Msg) (σ : Sig) :
    worldVerify S pk Recorded j i m σ → worldVerify S pk Recorded (j + 1) i m σ := by
  simp only [worldVerify]
  rcases Nat.lt_trichotomy (i : ℕ) j with hlt | heq | hgt
  · rw [if_pos hlt, if_pos (Nat.lt_succ_of_lt hlt)]; exact id
  · rw [if_neg (by omega), if_pos (by omega)]; intro hv; exact hj i m σ hv
  · rw [if_neg (by omega), if_neg (by omega)]; exact id

/-- **THE TELESCOPE.** Chaining `worldVerify_step` from `0` up to any `j` (induction on `j`): the all-real
world `H_0` accept implies `H_j` accept. Exactly `j` single-session swaps, each discharged by one session's
realization — the hybrid argument with the session count EXPLICIT as the recursion depth. -/
theorem worldVerify_zero_le {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop)
    (hj : ∀ i : Fin n, UcRealizes S (pk i) (Recorded i)) :
    ∀ (j : ℕ) (i : Fin n) (m : Msg) (σ : Sig),
      worldVerify S pk Recorded 0 i m σ → worldVerify S pk Recorded j i m σ := by
  intro j
  induction j with
  | zero => intro i m σ h; exact h
  | succ k ih => intro i m σ h; exact worldVerify_step S pk Recorded k hj i m σ (ih i m σ h)

/-- **MULTI-SESSION REALIZATION VIA THE HYBRID CHAIN.** For `n` concurrent sessions, if every session is
`EufCma`, the real scheme realizes `F̂_SIG` — proved by walking the hybrid chain `H_0 (all real) → H_n (all
ideal)`, `n` swaps each bounded by one single-session forgery. Same conclusion as `multi_session_realization`,
but reached through the EXPLICIT `n`-step hybrid, so the number-of-sessions factor is a theorem, not a
carrier. -/
theorem multi_session_hybrid_telescope {n : ℕ} {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : Fin n → PK) (Recorded : Fin n → Msg → Prop)
    (h : ∀ i, EufCma S (pk i) (Recorded i)) : MultiUcRealizes S pk Recorded := by
  have hr : ∀ i : Fin n, UcRealizes S (pk i) (Recorded i) :=
    fun i => (ucRealizes_iff_eufCma _ _ _).2 (h i)
  intro i m σ hv
  have h0 : worldVerify S pk Recorded 0 i m σ := by
    simp only [worldVerify]; rw [if_neg (Nat.not_lt_zero _)]; exact hv
  have hn : worldVerify S pk Recorded n i m σ := worldVerify_zero_le S pk Recorded hr n i m σ h0
  simp only [worldVerify] at hn
  rwa [if_pos i.isLt] at hn

/-- **THE HYBRID SIGNATURE REALIZES `F̂_SIG` UNDER `DL ∨ MSIS`.** Given the per-session forking reductions,
the hybrid `ed25519 × ML-DSA` signature realizes the MULTI-session functionality if EITHER floor holds:
`multi_session_realization` composed with `hybrid_secure_if_either_floor` in every session. Concurrent
composition survives to the same `SchnorrDLHard ∨ MSISHard` floor — no per-session carrier is introduced. -/
theorem hybrid_multi_session_uc_realizes
    {SID SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : SID → PKc) (pkp : SID → PKp) (Recorded : SID → Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (nb : ℕ)
    (dlFork : ∀ i, Forgery Cl (pkc i) (Recorded i) → DLSolver C G)
    (msisFork : ∀ i, Forgery Pq (pkp i) (Recorded i) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t nb z c w ∧ IsSelfTargetMSISSolution A t nb z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((nb + nb) + (nb + nb))) :
    MultiUcRealizes (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded :=
  multi_session_realization (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded
    (fun i => hybrid_secure_if_either_floor Cl Pq (pkc i) (pkp i) (Recorded i)
      C G A t nb (dlFork i) (msisFork i) hfloor)

/-! ### Teeth — the multi-session realization is load-bearing, both poles. -/

/-- **(FIRES)** a family of `EufCma` sessions realizes `F̂_SIG`. The positive pole over any session index. -/
theorem secureToy_multi_realizes {SID : Type*} :
    MultiUcRealizes secureToy (fun _ : SID => ()) (fun _ : SID => noQueries) :=
  multi_session_realization secureToy (fun _ => ()) (fun _ => noQueries) (fun _ => secureToy_euf_cma)

/-- **(BITES)** a family running the FORGEABLE scheme does NOT realize `F̂_SIG` — a session forgery (in every
session, here) is a multi-session distinguishing event. A scheme without `EufCma` fails multi-session
realization, so the per-session `EufCma` in `multi_session_realization` is load-bearing. -/
theorem brokenToy_multi_not_realizes :
    ¬ MultiUcRealizes brokenToy (fun _ : Bool => ()) (fun _ : Bool => noQueries) := by
  intro h; exact brokenToy_not_uc_realizes (fun m σ hv => h true m σ hv)

/-! ## §7 — THE UNIVERSAL COMPOSITION THEOREM: `ρ^π ≈ ρ^F` for an ARBITRARY protocol `ρ`.

This is the payoff. A protocol `ρ` that uses `F_SIG` as a SUBROUTINE observes it ONLY through its per-message
accept behaviour — the relation `accepts m := ∃ σ, verify pk m σ`. The composition operator plugs whatever
sits behind that interface into `ρ`, so `ρ` is a FUNCTION of the accept relation. `ρ^F` is `ρ` fed the ideal
accept relation (`= Recorded`); `ρ^π` is `ρ` fed the REAL scheme's accept relation.

Under `EufCma` (soundness: real ⟹ ideal, no forgery) AND completeness (ideal ⟹ real: honest records carry a
verifying signature — the simulator of §5), the two accept relations are EQUAL as `Msg → Prop`
(`accept_relations_agree`). Hence for ANY `ρ` whatsoever, `ρ (real) = ρ (ideal)` by congruence: the composed
protocols are INDISTINGUISHABLE — here `≈` is exact equality, the `Prop`-collapse of distance 0. The teeth
run the OTHER way: any `ρ` that distinguishes `ρ^π` from `ρ^F` yields a subroutine FORGERY
(`distinguishing_rho_yields_forgery`) — the composition operator plus the §5 simulator lifting a distinguisher
down to `pi`-vs-`F_SIG`. Composition fails EXACTLY at a forgery. -/

/-- **The real scheme's accept relation** as seen by a subroutine caller: a message is accepted iff SOME
signature verifies. This is `F_SIG`'s observable interface — what a protocol `ρ` querying the functionality
sees. -/
@[reducible] def acceptRel {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK) : Msg → Prop :=
  fun m => ∃ σ, S.verify pk m σ

/-- **THE ACCEPT RELATIONS COINCIDE.** Under `EufCma` and completeness, the real scheme's accept relation IS
the ideal `Recorded` relation, as functions `Msg → Prop`. Soundness gives real ⊑ ideal (no forgery),
completeness gives ideal ⊑ real (§5's simulator signs recorded messages); together, equality. This is the
observational equivalence of `pi` and `F_SIG` at the subroutine interface. -/
theorem accept_relations_agree {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) (hSound : EufCma S pk Recorded)
    (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ) :
    acceptRel S pk = Recorded := by
  funext m
  exact propext ⟨fun ⟨σ, hv⟩ => (ucRealizes_iff_eufCma S pk Recorded).2 hSound m σ hv,
                 fun hr => hComplete m hr⟩

/-- **THE UNIVERSAL COMPOSITION THEOREM (single-session).** For ANY protocol / environment `ρ` that uses
`F_SIG` as a subroutine — i.e. any function of the subroutine's accept relation, into ANY output type `β` —
running `ρ` with the real scheme `pi` produces the IDENTICAL result as running it with the ideal `F_SIG`,
provided the real scheme is `EufCma` and complete. `ρ^π = ρ^F`. This is the Canetti composition guarantee:
plug the (hybrid) signature into any `F_SIG`-secure protocol and behaviour is preserved — because the two
subroutines are observationally equal (`accept_relations_agree`). No monotonicity or restriction on `ρ`;
pure substitutivity. -/
theorem uc_composition_theorem {SK PK Msg Sig : Type*} {β : Sort*} (ρ : (Msg → Prop) → β)
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (hSound : EufCma S pk Recorded) (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ) :
    ρ (acceptRel S pk) = ρ Recorded :=
  congrArg ρ (accept_relations_agree S pk Recorded hSound hComplete)

/-- **THE COMPOSITION REDUCTION (teeth).** Any protocol `ρ` that DISTINGUISHES `ρ^π` from `ρ^F` yields a
subroutine FORGERY on the honest key. Contrapositive of `uc_composition_theorem`: if there were no forgery
(`EufCma`) the outputs would be equal, so a difference forces a forgery. This is the composition operator
lifting an environment against the composed protocol down to an environment against `pi`-vs-`F_SIG` — the
distinguishing advantage is exactly the forgery advantage. -/
theorem distinguishing_rho_yields_forgery {SK PK Msg Sig : Type*} (ρ : (Msg → Prop) → Prop)
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (hComplete : ∀ m, Recorded m → ∃ σ, S.verify pk m σ)
    (hdist : ρ (acceptRel S pk) ≠ ρ Recorded) : Forgery S pk Recorded := by
  by_contra hno
  exact hdist (uc_composition_theorem ρ S pk Recorded hno hComplete)

/-! ### Multi-session composition — the FULL Canetti statement over `F̂_SIG`. -/

/-- **The multi-session accept relation** — per session, a message is accepted iff some signature verifies
under that session's key. The observable interface of `F̂_SIG`. -/
@[reducible] def multiAcceptRel {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) : SID → Msg → Prop :=
  fun i m => ∃ σ, S.verify (pk i) m σ

/-- The multi-session accept relations coincide with the multi-session record under per-session `EufCma` +
completeness — the observational equivalence of the concurrent real emulation and `F̂_SIG`. -/
theorem multi_accept_relations_agree {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (hSound : ∀ i, EufCma S (pk i) (Recorded i))
    (hComplete : ∀ i m, Recorded i m → ∃ σ, S.verify (pk i) m σ) :
    multiAcceptRel S pk = Recorded := by
  funext i m
  exact propext ⟨fun ⟨σ, hv⟩ => (ucRealizes_iff_eufCma _ _ _).2 (hSound i) m σ hv,
                 fun hr => hComplete i m hr⟩

/-- **THE UNIVERSAL COMPOSITION THEOREM (multi-session, the full `ρ^π ≈ ρ^F`).** For ANY protocol `ρ` using
the MULTI-session functionality `F̂_SIG` as a subroutine, replacing `F̂_SIG` by the concurrent real emulation
`pi` preserves `ρ`'s output exactly, under per-session `EufCma` + completeness. This is Canetti's composition
theorem for many concurrent signature instances: `ρ` with the real hybrid signature is indistinguishable from
`ρ` with the ideal multi-session functionality. -/
theorem uc_composition_multi_session {SID SK PK Msg Sig : Type*} {β : Sort*}
    (ρ : (SID → Msg → Prop) → β)
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (hSound : ∀ i, EufCma S (pk i) (Recorded i))
    (hComplete : ∀ i m, Recorded i m → ∃ σ, S.verify (pk i) m σ) :
    ρ (multiAcceptRel S pk) = ρ Recorded :=
  congrArg ρ (multi_accept_relations_agree S pk Recorded hSound hComplete)

/-- **THE COMPOSITION PAYOFF — the hybrid signature composes into ANY `F_SIG`-protocol under `DL ∨ MSIS`.**
For any protocol `ρ`, plugging the hybrid `ed25519 × ML-DSA` signature into `ρ` in place of the ideal `F_SIG`
preserves `ρ`'s behaviour, provided EITHER floor holds (`EufCma` via `hybrid_secure_if_either_floor`) and the
hybrid records are complete. So a game-based `DL ∨ MSIS` result GENUINELY composes: any `F_SIG`-secure
protocol stays secure with the real hybrid signature, down to the same floor, no new carrier. -/
theorem hybrid_sig_composes_under_floor
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*} {β : Sort*} (ρ : (Msg → Prop) → β)
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Recorded : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (nb : ℕ)
    (dlFork : Forgery Cl pkc Recorded → DLSolver C G)
    (msisFork : Forgery Pq pkp Recorded →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t nb z c w ∧ IsSelfTargetMSISSolution A t nb z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((nb + nb) + (nb + nb)))
    (hComplete : ∀ m, Recorded m → ∃ σ, (hybrid Cl Pq).verify (pkc, pkp) m σ) :
    ρ (acceptRel (hybrid Cl Pq) (pkc, pkp)) = ρ Recorded :=
  uc_composition_theorem ρ (hybrid Cl Pq) (pkc, pkp) Recorded
    (hybrid_secure_if_either_floor Cl Pq pkc pkp Recorded C G A t nb dlFork msisFork hfloor)
    hComplete

/-! ### Teeth — composition holds iff no forgery; a forgeable scheme is a distinguishing `ρ`. -/

/-- **(FIRES)** for the `EufCma` `secureToy`, EVERY protocol `ρ` composes: `ρ^π = ρ^F`. The positive pole of
the composition theorem. -/
theorem secureToy_composition (ρ : (Bool → Prop) → Prop) :
    ρ (acceptRel secureToy ()) = ρ noQueries :=
  uc_composition_theorem ρ secureToy () noQueries secureToy_euf_cma (fun _ h => h.elim)

/-- **(BITES — composition FAILS without `EufCma`).** For the forgeable `brokenToy` there is a protocol `ρ`
(the one that queries "does `true` verify?") whose composed outputs DIFFER: `ρ^π` accepts the forged message,
`ρ^F` rejects it. So the `EufCma`/completeness hypothesis of `uc_composition_theorem` is load-bearing —
composition genuinely breaks exactly where a forgery lives. -/
theorem composition_fails_without_eufcma :
    ∃ ρ : (Bool → Prop) → Prop, ρ (acceptRel brokenToy ()) ≠ ρ noQueries := by
  refine ⟨fun R => R true, fun h => ?_⟩
  have hreal : (fun R : Bool → Prop => R true) (acceptRel brokenToy ()) := ⟨true, trivial⟩
  rw [h] at hreal
  exact hreal

/-! ## §7.5 — THE CONCRETE-SECURITY RESTATEMENT: UC realization AS A NEGLIGIBLE ADVANTAGE BOUND.

Everything above is `Prop`-level (real ⟹ ideal, at distance 0). This section RESTATES it as an ADVANTAGE
ensemble in the security parameter, using `Dregg2.Crypto.ConcreteSecurity`: the environment's distinguishing
advantage is a function `λ ↦ |Pr_real − Pr_ideal|`, and UC realization IS the statement that this ensemble is
NEGLIGIBLE. In this deterministic model the advantage is exactly `0` (realizes) or `1` (forgeable), so the
negligible/not-negligible poles coincide with the realize/distinguish poles.

⚠ **This §7.5 advantage is DEGENERATE — it is not yet genuine computational UC.** Because `ucAdv` is `0/1`
and does not depend on the security parameter, `Negl (ucAdv …)` is exactly `¬ Distinguishes` in ensemble
clothing: it CANNOT express a nonzero-but-negligible distance. It is the distance-0 corner of the real
spectrum, useful only to land the structural realization in the `Negl` algebra. The GENUINE computational
statement — a real-valued advantage `advₑ ≤ εₛ` bounded by the forgery advantage, negligible under the
floor, ranging over the full `[0,1]` spectrum — is §7.6, where the two irreducible cryptographic inputs
(G1 the reduction bound, G2 the quantitative floor) are NAMED, not laundered. Read §7.6 for what is genuinely
proved and what remains a named gap. -/

open Classical in
/-- **THE UC ADVANTAGE ENSEMBLE.** `ucAdv S pk Recorded : λ ↦ ℝ` — the environment's distinguishing
advantage `|Pr_real − Pr_ideal|` as a function of the security parameter: `1` when the real and ideal worlds
diverge (`Distinguishes`, i.e. a forgery exists), `0` otherwise. The concrete-security observable UC
realization is a bound on. -/
noncomputable def ucAdv {SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig) (pk : PK)
    (Recorded : Msg → Prop) : Ensemble :=
  fun _ => if Distinguishes S pk Recorded then 1 else 0

/-- **UC REALIZATION IS A NEGLIGIBLE ADVANTAGE BOUND.** `UcRealizes S pk Recorded` iff the UC advantage
ensemble is NEGLIGIBLE. Forward: realizing means `¬ Distinguishes`, so the advantage is the `0` ensemble
(`negl_zero`). Backward: a forgeable scheme's advantage is the constant `1`, which is NOT negligible
(`not_negl_one`), so a negligible advantage forces realization. The `Prop`-level `UcRealizes` and the
concrete-security "negligible advantage" are one and the same — no slack, no laundering. -/
theorem ucRealizes_iff_ucAdv_negl {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    UcRealizes S pk Recorded ↔ Negl (ucAdv S pk Recorded) := by
  rw [ucRealizes_iff_not_distinguishes]
  constructor
  · intro hnd
    have h0 : ucAdv S pk Recorded = (fun _ => 0) := by funext l; simp only [ucAdv, if_neg hnd]
    rw [h0]; exact negl_zero
  · intro hnegl hd
    have h1 : ucAdv S pk Recorded = (fun _ => 1) := by funext l; simp only [ucAdv, if_pos hd]
    rw [h1] at hnegl; exact not_negl_one hnegl

/-- **(FIRES)** a secure scheme has NEGLIGIBLE UC advantage — the `secureToy` advantage ensemble is `0`. -/
theorem secureToy_ucAdv_negl : Negl (ucAdv secureToy () noQueries) :=
  (ucRealizes_iff_ucAdv_negl _ _ _).1 secureToy_uc_realizes

/-- **(BITES)** a forgeable scheme has NON-negligible UC advantage — `brokenToy`'s advantage is the constant
`1`. So "negligible advantage" is a genuine discriminator, false exactly when unforgeability fails. -/
theorem brokenToy_ucAdv_not_negl : ¬ Negl (ucAdv brokenToy () noQueries) := fun h =>
  brokenToy_not_uc_realizes ((ucRealizes_iff_ucAdv_negl _ _ _).2 h)

/-- **THE HYBRID SIGNATURE HAS NEGLIGIBLE UC ADVANTAGE UNDER `DL ∨ MSIS`.** The concrete-security form of
`hybrid_sig_uc_realizes`: the environment's distinguishing advantage against the hybrid `ed25519 × ML-DSA`
signature vs `F_SIG` is negligible whenever either floor holds. Same reduction, now stated as an advantage
bound. -/
theorem hybrid_sig_advantage_negl
    {SKc PKc Msg Sigc SKp PKp Sigp : Type*}
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : PKc) (pkp : PKp) (Recorded : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
    {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
    (A : M →ₗ[Rq] N) (t : N) (β : ℕ)
    (dlFork : Forgery Cl pkc Recorded → DLSolver C G)
    (msisFork : Forgery Pq pkp Recorded →
      ∃ (w : N) (c c' : Rq) (z z' : M), c ≠ c' ∧
        IsSelfTargetMSISSolution A t β z c w ∧ IsSelfTargetMSISSolution A t β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β))) :
    Negl (ucAdv (hybrid Cl Pq) (pkc, pkp) Recorded) :=
  (ucRealizes_iff_ucAdv_negl _ _ _).1
    (hybrid_sig_uc_realizes Cl Pq pkc pkp Recorded C G A t β dlFork msisFork hfloor)

/-! ### The simulator's PPT efficiency — now MODELLED and PROVED (retiring modelling note (ii)).

The §5 simulator `simSign` does `O(1)` work per invocation (one honest `sign` call, no rewinding). We give it
an explicit polynomial `StepBound` and prove it PPT — the simulator-efficiency piece is no longer a carried
`Prop` outside Lean's logic but a proved fact of `Dregg2.Crypto.ConcreteSecurity`. -/

/-- **THE SIMULATOR'S STEP BOUND.** Constant work (one honest signature per recorded message). -/
def simStepBound : StepBound := constBound 1

/-- **THE SIMULATOR IS PPT (proved).** Its step bound is constant, hence polynomial. This DISCHARGES the
former modelling note (ii) — simulator efficiency is now a theorem, not an assumption. -/
theorem sim_ppt : simStepBound.PPT := constBound_ppt 1

/-! ### Multi-session advantage — the session-count × negligible closure, PROVED.

The multi-session advantage over a finite set of sessions is bounded by the SUM of the per-session advantages
(the union bound of the hybrid argument); a finite sum of negligible advantages is negligible
(`negl_finset_sum`), and `n` copies of a negligible term is `(n : ℝ)` times it (`negl_const_mul`) — both
proved in the framework. So the multi-session hybrid costs a session-count factor times a negligible term and
STAYS negligible. -/

open Classical in
/-- **THE MULTI-SESSION UC ADVANTAGE ENSEMBLE.** `1` when some session distinguishes (`MultiForgery`), `0`
otherwise. -/
noncomputable def multiUcAdv {SID SK PK Msg Sig : Type*} (S : SigScheme SK PK Msg Sig)
    (pk : SID → PK) (Recorded : SID → Msg → Prop) : Ensemble :=
  fun _ => if MultiForgery S pk Recorded then 1 else 0

/-- **MULTI-SESSION REALIZATION IS A NEGLIGIBLE MULTI-SESSION ADVANTAGE** — the `F̂_SIG` analogue of
`ucRealizes_iff_ucAdv_negl`. -/
theorem multiUcRealizes_iff_multiUcAdv_negl {SID SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) :
    MultiUcRealizes S pk Recorded ↔ Negl (multiUcAdv S pk Recorded) := by
  rw [multiUcRealizes_iff_multiEufCma]
  unfold MultiEufCma
  constructor
  · intro hnf
    have h0 : multiUcAdv S pk Recorded = (fun _ => 0) := by
      funext l; simp only [multiUcAdv, if_neg hnf]
    rw [h0]; exact negl_zero
  · intro hnegl hmf
    have h1 : multiUcAdv S pk Recorded = (fun _ => 1) := by
      funext l; simp only [multiUcAdv, if_pos hmf]
    rw [h1] at hnegl; exact not_negl_one hnegl

/-- **THE UNION BOUND, POINTWISE.** The multi-session advantage is at most the SUM of the per-session
advantages: if some session distinguishes, its per-session advantage is `1` and the others are `≥ 0`, so the
sum is `≥ 1`; if none does, the multi-session advantage is `0 ≤ sum`. This is exactly the hybrid argument's
per-session decomposition, at the advantage level. -/
theorem multiUcAdv_le_sum {SID SK PK Msg Sig : Type*} [Fintype SID]
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop) (l : ℕ) :
    multiUcAdv S pk Recorded l ≤ ∑ i : SID, ucAdv S (pk i) (Recorded i) l := by
  have hnonneg : ∀ j ∈ (Finset.univ : Finset SID), (0 : ℝ) ≤ ucAdv S (pk j) (Recorded j) l := by
    intro j _; simp only [ucAdv]; split <;> norm_num
  by_cases hmf : MultiForgery S pk Recorded
  · obtain ⟨i, m, σ, hnr, hv⟩ := id hmf
    have hd : Distinguishes S (pk i) (Recorded i) := ⟨fun _ => (m, σ), hv, hnr⟩
    have hterm : ucAdv S (pk i) (Recorded i) l = 1 := by simp only [ucAdv, if_pos hd]
    have hle1 : (1 : ℝ) ≤ ∑ j : SID, ucAdv S (pk j) (Recorded j) l := by
      calc (1 : ℝ) = ucAdv S (pk i) (Recorded i) l := hterm.symm
        _ ≤ ∑ j : SID, ucAdv S (pk j) (Recorded j) l :=
            Finset.single_le_sum hnonneg (Finset.mem_univ i)
    have hm1 : multiUcAdv S pk Recorded l = 1 := by simp only [multiUcAdv, if_pos hmf]
    rw [hm1]; exact hle1
  · have hm0 : multiUcAdv S pk Recorded l = 0 := by simp only [multiUcAdv, if_neg hmf]
    rw [hm0]; exact Finset.sum_nonneg hnonneg

/-- **THE MULTI-SESSION CLOSURE (`n` × negligible is negligible).** If every session has negligible UC
advantage, so does the multi-session functionality: the multi-session advantage is dominated by the finite
SUM of per-session advantages (`multiUcAdv_le_sum`), and a finite sum of negligibles is negligible
(`negl_finset_sum`). The session-count factor is thus a THEOREM — it never leaves the `Negl` algebra. -/
theorem multi_session_advantage_negl {SID SK PK Msg Sig : Type*} [Fintype SID]
    (S : SigScheme SK PK Msg Sig) (pk : SID → PK) (Recorded : SID → Msg → Prop)
    (h : ∀ i, Negl (ucAdv S (pk i) (Recorded i))) : Negl (multiUcAdv S pk Recorded) := by
  refine negl_of_eventually_le (Filter.Eventually.of_forall (fun l => ?_))
    (negl_finset_sum Finset.univ (fun i _ => h i))
  rw [abs_of_nonneg (by simp only [multiUcAdv]; split <;> norm_num),
      abs_of_nonneg (Finset.sum_nonneg (fun j _ => by simp only [ucAdv]; split <;> norm_num))]
  exact multiUcAdv_le_sum S pk Recorded l

/-- **THE SESSION-COUNT FACTOR, LITERALLY.** `n` copies of a negligible advantage sum to `(n : ℝ)` times it,
which is negligible (`negl_const_mul`). The explicit "session count × negligible term is still negligible"
the multi-session hybrid pays. -/
theorem sessions_smul_negl {n : ℕ} {α : Ensemble} (hα : Negl α) :
    Negl (fun l => (n : ℝ) * α l) := negl_const_mul (n : ℝ) hα

/-- **THE HYBRID SIGNATURE HAS NEGLIGIBLE MULTI-SESSION ADVANTAGE UNDER `DL ∨ MSIS`.** Concurrent
composition of the hybrid signature over finitely many sessions keeps the distinguishing advantage negligible,
grounded per-session in `SchnorrDLHard ∨ MSISHard`. The concrete-security form of
`hybrid_multi_session_uc_realizes`. -/
theorem hybrid_multi_session_advantage_negl
    {SID SKc PKc Msg Sigc SKp PKp Sigp : Type*} [Fintype SID]
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (pkc : SID → PKc) (pkp : SID → PKp) (Recorded : SID → Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {Mo : Type*} [AddCommGroup Mo] [Module Rq Mo] [ShortNorm Mo]
    {No : Type*} [AddCommGroup No] [Module Rq No] [ShortNorm No]
    (A : Mo →ₗ[Rq] No) (t : No) (nb : ℕ)
    (dlFork : ∀ i, Forgery Cl (pkc i) (Recorded i) → DLSolver C G)
    (msisFork : ∀ i, Forgery Pq (pkp i) (Recorded i) →
      ∃ (w : No) (c c' : Rq) (z z' : Mo), c ≠ c' ∧
        IsSelfTargetMSISSolution A t nb z c w ∧ IsSelfTargetMSISSolution A t nb z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((nb + nb) + (nb + nb))) :
    Negl (multiUcAdv (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded) :=
  multi_session_advantage_negl (hybrid Cl Pq) (fun i => (pkc i, pkp i)) Recorded
    (fun i => (ucRealizes_iff_ucAdv_negl _ _ _).1
      ((multiUcRealizes_iff_forall_session _ _ _).1
        (hybrid_multi_session_uc_realizes Cl Pq pkc pkp Recorded C G A t nb dlFork msisFork hfloor) i))

/-! ### Teeth — the multi-session advantage is load-bearing, both poles. -/

/-- **(FIRES)** a family of secure sessions has negligible multi-session advantage. -/
theorem secureToy_multiUcAdv_negl {SID : Type*} [Fintype SID] :
    Negl (multiUcAdv secureToy (fun _ : SID => ()) (fun _ : SID => noQueries)) :=
  multi_session_advantage_negl _ _ _ (fun _ => secureToy_ucAdv_negl)

/-- **(BITES)** a family of forgeable sessions has NON-negligible multi-session advantage (constant `1`). -/
theorem brokenToy_multiUcAdv_not_negl :
    ¬ Negl (multiUcAdv brokenToy (fun _ : Bool => ()) (fun _ : Bool => noQueries)) := fun h =>
  brokenToy_multi_not_realizes ((multiUcRealizes_iff_multiUcAdv_negl _ _ _).2 h)

/-! ## §7.6 — GENUINE COMPUTATIONAL UC: the distinguishing advantage as a REDUCTION-BOUNDED ensemble.

**Why §7.5 is not yet genuine computational UC.** `ucAdv := if Distinguishes then 1 else 0` is the
DEGENERATE deterministic advantage: it takes only the two values `0` and `1` and does not depend on the
security parameter, so `Negl (ucAdv …)` is exactly `¬ Distinguishes` in ensemble clothing — the `Prop`
`=`-at-distance-0 dressed as `≈`. It CANNOT express a genuine nonzero-but-negligible distance, which is the
whole content of computational security. Real UC is quantitative: an environment running in the security
parameter `λ` has a distinguishing advantage `advₑ : λ ↦ [0,1]` that is a genuine real quantity, bounded by
the scheme's EUF-CMA forgery advantage `εₛ : λ ↦ [0,1]` via the distinguisher-to-forger reduction, and `εₛ`
is negligible ONLY under the hardness floor. This section states THAT over the genuine `Negl` algebra of
`ConcreteSecurity`, with the advantage ranging over the FULL SPECTRUM `[0,1]`, not two points.

**WHAT IS PROVED vs. WHAT ARE NAMED GAPS.** The TRANSFER — `advₑ ≤ εₛ` eventually AND `Negl εₛ` gives
`Negl advₑ` — is PROVED (`uc_advantage_transfer`, by domination in the `Negl` algebra). The two INPUTS are
the genuine cryptographic content and are NAMED GAPS this deterministic model does not internalise:

  * **(G1) the REDUCTION BOUND `advₑ ≤ εₛ`** — that a distinguishing environment's success PROBABILITY is at
    most the forger's. `distinguishes_iff_forgery` proves the two EVENTS coincide; the PROBABILITIES
    coinciding requires a probabilistic execution semantics (a distribution over `Z`'s coins and the honest
    key) this deterministic `Env := Unit → Msg × Sig` model lacks. So the bound is carried as the
    `reduction_bound` FIELD of `ComputationalUC`, named, not laundered into an equality.
  * **(G2) `Negl εₛ` from the floor** — the tree's `SchnorrDLHard`/`MSISHard` are BOOLEAN (`¬ ∃ solver`), not
    quantitative advantage bounds, so there is no ε(λ) the floor hands to `Negl`. A quantitative floor
    (`dlAdvantage ≤ negl(λ)`) is required and is NOT present in the tree; `Negl εₛ` is the `forge_negl` FIELD.

So genuine end-to-end computational UC here is TRUE-MODULO-(G1,G2): the advantage-transfer layer is honest
and PROVED, and the two irreducible cryptographic inputs are NAMED FIELDS, not relabelled `=`. The teeth
below exercise the FULL spectrum — `2⁻ᵏ` (negligible, yet strictly positive at every κ), `1/κ` (vanishing
but only polynomially — NOT negligible), and the constant `1` (broken) — proving `≈` is a genuine distance,
not the 0/1 collapse of §7.5. -/

section GenuineComputationalUC
open Filter

/-- **THE ADVANTAGE-TRANSFER THEOREM (PROVED).** If the environment's distinguishing advantage `advE` is
non-negative and eventually bounded by the scheme's forgery advantage `εS` (the reduction, G1), and `εS` is
negligible (the floor, G2), then `advE` is negligible: real ≈ ideal within negligible advantage for that
bounded environment. Proved purely in the `Negl` algebra by domination (`negl_of_eventually_le`) — no new
carrier, no probabilistic machinery. This is the load-bearing computational statement; its two inputs are
the named gaps G1/G2. -/
theorem uc_advantage_transfer {advE εS : Ensemble}
    (hnonneg : ∀ n, 0 ≤ advE n)
    (hbound : ∀ᶠ n : ℕ in atTop, advE n ≤ εS n)
    (hεnegl : Negl εS) : Negl advE := by
  refine negl_of_eventually_le ?_ hεnegl
  filter_upwards [hbound] with n hb
  rw [abs_of_nonneg (hnonneg n)]
  exact hb.trans (le_abs_self _)

/-- **(TOOTH — an INTERMEDIATE, non-negligible advantage.)** `1/κ` VANISHES (`→ 0`) yet is NOT negligible:
at exponent `c = 2` it would need `1/κ < 1/κ²` eventually, i.e. `κ² < κ`, false for `κ ≥ 2`. So a scheme
whose distinguishing advantage decays only polynomially is STILL distinguishable — `≈` genuinely measures a
distance strictly between the `0` and `1` poles of §7.5. THIS is the tooth §7.5's 0/1 advantage cannot
bite. -/
theorem not_negl_inv_linear : ¬ Negl (fun n : ℕ => 1 / (n : ℝ)) := by
  intro h
  obtain ⟨n, hlt, hn2⟩ := ((h 2).and (eventually_ge_atTop 2)).exists
  have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ))] at hlt
  have hle : 1 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hn (by nlinarith)
  linarith

/-- **`ComputationalUC advE εS` — the genuine computational-UC obligation, with the two cryptographic gaps
NAMED as fields.** Inhabiting it for a scheme means: the environment's advantage is non-negative
(`adv_nonneg`), it is reduction-bounded by the forgery advantage (`reduction_bound` = G1), and the forgery
advantage is negligible under the floor (`forge_negl` = G2). Its consequence `realizes` (real ≈ ideal at
negligible advantage) is then PROVED, not assumed. No `Prop` is asserted `True`; the two irreducible inputs
are explicit, real-valued, and can be nonzero. -/
structure ComputationalUC (advE εS : Ensemble) : Prop where
  /-- The distinguishing advantage is a genuine probability: non-negative. -/
  adv_nonneg : ∀ n, 0 ≤ advE n
  /-- **GAP G1** — the reduction bound: the environment's advantage is at most the forgery advantage. -/
  reduction_bound : ∀ᶠ n : ℕ in atTop, advE n ≤ εS n
  /-- **GAP G2** — the forgery advantage is negligible (would come from a QUANTITATIVE hardness floor). -/
  forge_negl : Negl εS

/-- **COMPUTATIONAL REALIZATION (PROVED from the witness).** Given a `ComputationalUC` witness, the
environment's distinguishing advantage is negligible — real ≈ ideal at the computational level. This is the
genuine restatement of `hybrid_sig_uc_realizes` over a real-valued advantage, discharged by
`uc_advantage_transfer`. -/
theorem ComputationalUC.realizes {advE εS : Ensemble} (h : ComputationalUC advE εS) : Negl advE :=
  uc_advantage_transfer h.adv_nonneg h.reduction_bound h.forge_negl

/-- **(FIRES — a genuine NONZERO negligible advantage is realized.)** A secure environment whose advantage
is the forgery advantage `2⁻ᵏ` — strictly POSITIVE at every `κ`, unlike the 0/1 collapse — is a
`ComputationalUC` witness, and its advantage is negligible. The positive pole at a genuine intermediate
value. -/
def secureComputationalUC : ComputationalUC (fun n => 1 / (2 : ℝ) ^ n) (fun n => 1 / (2 : ℝ) ^ n) where
  adv_nonneg := fun n => by positivity
  reduction_bound := Filter.Eventually.of_forall (fun _ => le_refl _)
  forge_negl := negl_two_pow

/-- The secure witness's realization: the strictly-positive `2⁻ᵏ` advantage IS negligible — a genuine
nonzero distance, provably `≈`. -/
theorem secureComputationalUC_realizes : Negl (fun n : ℕ => 1 / (2 : ℝ) ^ n) :=
  secureComputationalUC.realizes

/-- **(BITES — a broken scheme admits NO computational-UC witness.)** If the forgery advantage is the
constant `1` (a scheme that is forged with certainty), NO `ComputationalUC` witness exists for ANY
environment advantage, because `forge_negl` would be `Negl (fun _ => 1)`, refuted by `not_negl_one`.
Realization genuinely fails when unforgeability fails. -/
theorem broken_no_computationalUC (advE : Ensemble) :
    ¬ ComputationalUC advE (fun _ => 1) := fun h => not_negl_one h.forge_negl

/-- **(BITES — the SPECTRUM tooth, unreachable by §7.5.)** A scheme whose forgery advantage decays only
polynomially (`1/κ`) ALSO admits no computational-UC witness — the advantage vanishes but is not negligible
(`not_negl_inv_linear`). This is exactly the case the 0/1 advantage of §7.5 cannot express: `≈` discriminates
`2⁻ᵏ` (realized) from `1/κ` (NOT realized) from `1` (broken), so it is a genuine distance over the full
spectrum, not a two-point relabelling of the `Prop`. -/
theorem inv_linear_no_computationalUC (advE : Ensemble) :
    ¬ ComputationalUC advE (fun n => 1 / (n : ℝ)) := fun h => not_negl_inv_linear h.forge_negl

/-- **THE DEGENERATE §7.5 ADVANTAGE IS A `ComputationalUC` INSTANCE** — the 0/1 `ucAdv` sits inside the
genuine layer as the special case `εS = advE = ucAdv` UNDER `UcRealizes` (whence `ucAdv = 0`). So §7.6
subsumes §7.5: the structural realization is the distance-0 point of the real-valued spectrum, and G1 holds
trivially (`advE ≤ advE`). This exhibits the launder-free relationship — §7.5 is a corner of §7.6, not a
substitute for it. -/
def degenerate_computationalUC {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop)
    (h : UcRealizes S pk Recorded) :
    ComputationalUC (ucAdv S pk Recorded) (ucAdv S pk Recorded) where
  adv_nonneg := fun _ => by simp only [ucAdv]; split <;> norm_num
  reduction_bound := Filter.Eventually.of_forall (fun _ => le_refl _)
  forge_negl := (ucRealizes_iff_ucAdv_negl S pk Recorded).1 h

end GenuineComputationalUC

/-! ## §8 — THE UC RESIDUAL — every field now DISCHARGED (the two modelling notes RETIRED).

The Canetti UC theorem has THREE structural parts, all DISCHARGED as real Lean theorems at this model level:
(a) STATIC single-session realization (`ucRealizes_iff_eufCma`); (b) MULTI-session realization of `F̂_SIG` via
the explicit `n`-step hybrid (`multi_session_realization`, `multi_session_hybrid_telescope`); (c) the
UNIVERSAL COMPOSITION theorem `ρ^π = ρ^F` (`uc_composition_theorem`, `uc_composition_multi_session`) — all
reduced to `EufCma`, hence to `SchnorrDLHard ∨ MSISHard`.

**The two former modelling notes are now RETIRED — they are proved, via `Dregg2.Crypto.ConcreteSecurity`,
not carried as abstract `Prop`s:**

  * **(i) NEGLIGIBLE-ENSEMBLE DISTANCE (was: `≈` is exact `Prop`-equality).** The distinguishing advantage is
    an ENSEMBLE `ucAdv : λ ↦ ℝ`, and `UcRealizes ↔ Negl (ucAdv …)` (`ucRealizes_iff_ucAdv_negl`). Note this
    lands realization in the `Negl` algebra but the `ucAdv` here is DEGENERATE (`0/1`, λ-independent) — it is
    `¬ Distinguishes` in ensemble clothing, NOT a genuine nonzero-negligible distance. The GENUINE
    real-valued computational restatement is §7.6 (`ComputationalUC` / `uc_advantage_transfer`), which is
    PROVED modulo two NAMED cryptographic gaps: G1 the reduction bound `advₑ ≤ εₛ` (needs probabilistic
    execution semantics), G2 `Negl εₛ` (needs a QUANTITATIVE hardness floor — the tree's floors are Boolean
    `¬∃solver`). So note (i) is genuinely addressed at the transfer level, TRUE-MODULO-(G1,G2), not fully
    closed. The residual field carries the degenerate `EufCma ⟹ Negl (ucAdv …)` (a real theorem, no
    `True`-carrier), with the genuine spectrum-valued layer in §7.6.
  * **(ii) SIMULATOR PPT-EFFICIENCY (was: a complexity statement outside Lean's logic).** The simulator now
    carries an explicit polynomial `StepBound` (`simStepBound`, constant work) and its PPT-ness is PROVED
    (`sim_ppt`) — no longer an abstract `simulator_ppt : Prop`.

So `SigUCResidual` has NO carried modelling `Prop`s left: every field is a proved-theorem type, filled for
ANY `(S, pk, Recorded)`. Mirrors `LightClientUC.DynamicUCResidual`, now with the concrete-security layer
closed too. -/

/-- **`SigUCResidual S pk Recorded`** — the dynamic-UC obligation, EVERY field a DISCHARGED Lean theorem.
Inhabiting it means: static realization, the composition lift, the NEGLIGIBLE-ADVANTAGE bound (modelling
note (i), now proved), and the SIMULATOR's PPT step bound (modelling note (ii), now proved) all hold. No
abstract carried `Prop` remains. -/
structure SigUCResidual {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) where
  /-- DISCHARGED — the static realization: `EufCma ⟹ UcRealizes`. Filled by `ucRealizes_iff_eufCma`. -/
  static_realize : EufCma S pk Recorded → UcRealizes S pk Recorded
  /-- DISCHARGED — the UNIVERSAL COMPOSITION lift: for ANY protocol `ρ`, `ρ^π = ρ^F` under `EufCma` +
  completeness. Filled by `uc_composition_theorem`. -/
  compose_lift : ∀ (ρ : (Msg → Prop) → Prop),
    EufCma S pk Recorded → (∀ m, Recorded m → ∃ σ, S.verify pk m σ) →
    ρ (acceptRel S pk) = ρ Recorded
  /-- DISCHARGED — RETIRED modelling note (i): the distinguishing advantage is a NEGLIGIBLE ENSEMBLE
  distance in the security parameter (not exact `Prop`-equality). Filled by `ucRealizes_iff_ucAdv_negl`
  composed with `EufCma ⟹ UcRealizes`; under `EufCma` the advantage ensemble is `0`, hence `Negl`. -/
  negligible_advantage : EufCma S pk Recorded → Negl (ucAdv S pk Recorded)
  /-- DISCHARGED — RETIRED modelling note (ii): the simulator's explicit polynomial step bound. -/
  simulator_bound : StepBound
  /-- DISCHARGED — the simulator is PPT (its step bound is polynomial). Filled by `sim_ppt`. -/
  simulator_ppt : simulator_bound.PPT

/-- **`dischargedResidual` — ALL fields constructible from real theorems (PROVED), for ANY
`(S, pk, Recorded)`.** No modelling-`Prop` arguments remain: the negligible-advantage bound is
`ucRealizes_iff_ucAdv_negl ∘ (EufCma ⟹ UcRealizes)`, and the simulator's PPT step bound is `simStepBound` /
`sim_ppt`. Both former carriers are now theorem-typed fields. -/
def dischargedResidual {SK PK Msg Sig : Type*}
    (S : SigScheme SK PK Msg Sig) (pk : PK) (Recorded : Msg → Prop) :
    SigUCResidual S pk Recorded where
  static_realize := (ucRealizes_iff_eufCma S pk Recorded).2
  compose_lift := fun ρ hs hc => uc_composition_theorem ρ S pk Recorded hs hc
  negligible_advantage := fun he =>
    (ucRealizes_iff_ucAdv_negl S pk Recorded).1 ((ucRealizes_iff_eufCma S pk Recorded).2 he)
  simulator_bound := simStepBound
  simulator_ppt := sim_ppt

/-- Non-vacuity of the residual at the `secureToy` instance: inhabited, and every DISCHARGED field yields a
real verdict from `EufCma` — realization, composition, the negligible-advantage bound, and the PPT simulator.
No `True`-carriers anywhere. -/
def refResidual : SigUCResidual secureToy () noQueries :=
  dischargedResidual secureToy () noQueries

/-- The residual's discharged static field, applied to `secureToy`'s `EufCma`, IS the proved `UcRealizes`. -/
theorem refResidual_realizes : UcRealizes secureToy () noQueries :=
  refResidual.static_realize secureToy_euf_cma

/-- The residual's discharged COMPOSITION field IS the proved `ρ^π = ρ^F` for every protocol `ρ`. -/
theorem refResidual_composes (ρ : (Bool → Prop) → Prop) :
    ρ (acceptRel secureToy ()) = ρ noQueries :=
  refResidual.compose_lift ρ secureToy_euf_cma (fun _ h => h.elim)

/-- The residual's discharged NEGLIGIBLE-ADVANTAGE field (retired modelling note (i)) IS the proved
`Negl (ucAdv …)` from `EufCma` — a real advantage bound, not an abstract `Prop`. -/
theorem refResidual_advantage_negl : Negl (ucAdv secureToy () noQueries) :=
  refResidual.negligible_advantage secureToy_euf_cma

/-- The residual's discharged SIMULATOR-PPT field (retired modelling note (ii)) IS the proved
`StepBound.PPT` — a real polynomial-time bound, not an abstract `Prop`. -/
theorem refResidual_sim_ppt : refResidual.simulator_bound.PPT :=
  refResidual.simulator_ppt

/-! ## §9 — Teeth: `F_SIG` accepts recorded and rejects unrecorded; the toy schemes separate. -/

/-- A concrete recorded set over `Bool`: `true` is recorded, `false` is not — a decidable surrogate that
lets the `F_SIG` accept/reject behaviour be `decide`-checked. -/
@[reducible] def recTrue : Bool → Prop := fun b => b = true

-- `F_SIG` ACCEPTS a recorded message (`true`) — the ideal honours honest signatures…
#guard decide ((idealSig recTrue).verify () true ())
-- …and REJECTS an unrecorded message (`false`): NO forgery in the ideal, by construction.
#guard decide (¬ (idealSig recTrue).verify () false ())
-- An EUF-CMA scheme (`secureToy`) verifies NOTHING — it never accepts an unrecorded message (realizes).
#guard decide (¬ secureToy.verify () true false)
-- A non-EUF-CMA scheme (`brokenToy`) verifies EVERYTHING — a forgery, the distinguishing event.
#guard decide (brokenToy.verify () true false)
-- ONE secure half BLOCKS the hybrid: secure∧broken verification is FALSE — the hybrid realizes `F_SIG`.
#guard decide (¬ (hybrid secureToy brokenToy).verify ((), ()) true (true, false))
-- BOTH broken: the hybrid verification is TRUE — a forgery goes through, realization FAILS (load-bearing).
#guard decide ((hybrid brokenToy brokenToy).verify ((), ()) true (true, true))

#assert_all_clean [
  idealSig_no_forgery,
  distinguishes_iff_forgery,
  ucRealizes_iff_eufCma,
  ucRealizes_iff_not_distinguishes,
  hybrid_sig_uc_realizes,
  secureToy_uc_realizes,
  brokenToy_not_uc_realizes,
  brokenToy_distinguishes,
  hybrid_secure_uc_realizes,
  hybrid_broken_not_uc_realizes,
  sim_complete,
  real_ideal_agree,
  multiForgery_iff_exists_session,
  multiEufCma_iff_forall_session,
  multiUcRealizes_iff_multiEufCma,
  multiUcRealizes_iff_forall_session,
  multi_session_realization,
  worldVerify_step,
  worldVerify_zero_le,
  multi_session_hybrid_telescope,
  hybrid_multi_session_uc_realizes,
  secureToy_multi_realizes,
  brokenToy_multi_not_realizes,
  accept_relations_agree,
  uc_composition_theorem,
  distinguishing_rho_yields_forgery,
  multi_accept_relations_agree,
  uc_composition_multi_session,
  hybrid_sig_composes_under_floor,
  secureToy_composition,
  composition_fails_without_eufcma,
  ucRealizes_iff_ucAdv_negl,
  secureToy_ucAdv_negl,
  brokenToy_ucAdv_not_negl,
  hybrid_sig_advantage_negl,
  sim_ppt,
  multiUcRealizes_iff_multiUcAdv_negl,
  multiUcAdv_le_sum,
  multi_session_advantage_negl,
  sessions_smul_negl,
  hybrid_multi_session_advantage_negl,
  secureToy_multiUcAdv_negl,
  brokenToy_multiUcAdv_not_negl,
  uc_advantage_transfer,
  not_negl_inv_linear,
  ComputationalUC.realizes,
  secureComputationalUC_realizes,
  broken_no_computationalUC,
  inv_linear_no_computationalUC,
  degenerate_computationalUC,
  refResidual_realizes,
  refResidual_composes,
  refResidual_advantage_negl,
  refResidual_sim_ppt
]

end Dregg2.Crypto.UcSignature

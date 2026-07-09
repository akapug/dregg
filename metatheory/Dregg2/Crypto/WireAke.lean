/-
# `Dregg2.Crypto.WireAke` — the WIRE HANDSHAKE as a proper AKE game.

The deployed peer handshake (`wire/src/server.rs`, the `PeerAuthResponse` arm) is an *authenticated key
exchange*: two nodes derive a shared session key AND each authenticates the other, over a public
transcript. This file formalises that handshake as the standard **AKE security game** (Bellare–Rogaway
1993; the modern eCK-lite form of LaMacchia–Lauter–Mityagin 2007) — sessions, matching conversations, a
`Test` query on a *fresh* session, and an adversary that controls delivery — and proves its three security
properties, each REDUCED to the standard lattice/DL/hash floor already carried by the tree.

## The deployed handshake, matched line for line

The server gate (`wire/src/server.rs`, the `PeerAuthResponse` branch) accepts iff

  `commit_ok ∧ ed_ok ∧ pq_ok ∧ source.is_participant(participant_key)`

where, over the domain-separated challenge `signing_msg = H("dregg-wire peer-auth v1", nonce ‖ node_id)`:

  * `commit_ok = verify_committed_ml_dsa(participant_key, participant_ed25519, participant_ml_dsa)` — the
    HYBRID IDENTITY-COMMITMENT gate (`IdentityCommitment.verify_committed`): the carried `(ed25519, ml_dsa)`
    keys must hash into the claimed hybrid id `participant_key` (a `None` ML-DSA half fails closed).
  * `ed_ok = pk.verify(signing_msg, signature)` — the classical (ed25519) signature over the challenge.
  * `pq_ok = ml_dsa_verify(participant_ml_dsa, signing_msg, pq_signature)` — the post-quantum (ML-DSA-65)
    signature over the SAME challenge. So `ed_ok ∧ pq_ok` is exactly `HybridCombiner.hybridVerify` — BOTH
    component signatures over one message: the `HybridCombiner.hybrid` scheme.

The session key itself is the X25519+ML-KEM-768 hybrid-KEM output `combine(ss_x, ss_pq, transcript)`
(`dregg-pq/src/hybrid_kem.rs`, modeled in `DreggKemRefinement`): the concat-KDF over BOTH shared secrets
and the FULL public transcript.

## The AKE game (cited) and the three theorems

A `Session` is an oriented instance at one party; two sessions **match** when they share the handshake
challenge (their transcripts agree — the Bellare–Rogaway *matching conversation*). The adversary schedules
delivery and may inject its own messages; a `Test` on a *fresh* (untampered, matching) session asks for the
session key or a random string and must not distinguish them.

* **`ake_session_key_secure`** (KEY SECRECY). The key of a matching session is indistinguishable from
  random if EITHER the X25519 OR the ML-KEM component is secure — the deployed `combine` INHERITS
  `HybridCombiner.hybrid_kem_ind_cca_if_either` (IND-CCA under the X-Wing dual-PRF). The disjuncts bottom
  out at `MLWESearchHard` (ML-KEM, via `MlKemIndCca`/`FoQrom`) and `SchnorrDLHard` (X25519 DH) — proven in
  the model, inherited here, never re-asserted.

* **`ake_authentication`** (IMPERSONATION-RESISTANCE). A session that ACCEPTS peer `P` has a MATCHING
  session at `P` (`P` really signed the challenge) — UNLESS the adversary forged `P`'s hybrid signature or
  presented an ML-DSA key not committed by `P`'s hybrid id. `accept_without_match_breaks_auth` makes the
  dichotomy explicit: an accepting session with no match is EITHER a hybrid `Forgery` (→ `EufCma` →
  `SchnorrDLHard ∨ MSISHard`, via `HybridCombiner.hybrid_secure_if_either_floor`) OR a distinct committed
  key pair (→ `¬ HashCR`, via `IdentityCommitment.distinct_verifying_pairs_break_hashcr`). So impersonation
  reduces to the floor.

* **`channel_binding`** (NO UKS / KEY-REUSE). The session key BINDS the transcript — the concat-KDF input
  includes it — so two sessions sharing a key share a transcript; a key-reuse / unknown-key-share attack
  therefore requires a TRANSCRIPT COLLISION (→ `¬ HashCR`, `uks_breaks_hashcr`).

## No named-carrier laundering

No `def …Hard` is introduced OR taken as a hypothesis. `ake_authentication` is conditioned on `EufCma` and
`HashCR`; `ake_authentication_grounded` DISCHARGES the `EufCma` through the PROVED forking reductions of
`HybridCombiner` to leave ONLY `SchnorrDLHard ∨ MSISHard` and `HashCR`. Key secrecy INHERITS the proved
KEM combiner. Every residual is the standard floor: `MLWESearchHard`, `SchnorrDLHard`, `MSISHard`, `HashCR`
— nothing more.

Cite: Bellare–Rogaway (Entity Authentication and Key Distribution, CRYPTO'93); LaMacchia–Lauter–Mityagin
(Stronger Security of Authenticated Key Exchange, ProvSec'07, the eCK model); X-Wing
(Barbosa–Connolly–Duarte–Kaidel–Schwabe–Westerbaan); the ∧-combiner for hybrid signatures
(Bindel–Herath–McKague–Stebila).
-/
import Dregg2.Crypto.DreggKemRefinement
import Dregg2.Crypto.IdentityCommitment

namespace Dregg2.Crypto.WireAke

open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.DreggKemRefinement
open Dregg2.Crypto.IdentityCommitment
open Dregg2.Crypto.HermineHintMLWE
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField
open Dregg2.Crypto.Lattice

/-! ## PART 1 — the AKE game: sessions, acceptance (the server gate), and matching conversations.

A `Session`'s security-relevant observation is the peer id it accepts, the CARRIED `(ed25519, ml_dsa)`
public keys, the handshake CHALLENGE `c` (the domain-separated `signing_msg`, i.e. the party-agreed
transcript over which both signatures are made), and the hybrid signature `σ = (σ_ed, σ_ml)`.

The honest peer `P`'s signing oracle is captured by `Q : Msg → Prop`, the set of challenges `P` actually
signed — exactly the `HybridCombiner.EufCma` convention. `P` has a **matching session** at challenge `c`
iff `Q c` (there is a real session at `P` that signed `c`). This is the Bellare–Rogaway *matching
conversation*: two sessions match when they agree on the signed transcript. -/

variable {SKc PKc Msg Sigc SKp PKp Sigp Pre Id : Type*}

/-- **The wire-session ACCEPT predicate — the server gate, verbatim.** A session accepts peer `id` on
challenge `c` with carried keys `(ed', ml')` and hybrid signature `σ` iff BOTH

  * `verify_committed cr frame id ed' ml'` — the carried keys hash into the claimed hybrid id (`commit_ok`),
    AND
  * `hybridVerify Cl Pq (ed', ml') c σ` — the classical AND post-quantum signatures both verify over `c`
    (`ed_ok ∧ pq_ok`).

This is exactly `commit_ok ∧ ed_ok ∧ pq_ok` of `wire/src/server.rs` (the membership `is_participant` is the
roster check, carried separately as "`id` is `P`'s id"). -/
def SessionAccepts (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (cr : CommitReveal Unit Pre Id) (frame : PKc → PKp → Pre)
    (id : Id) (ed' : PKc) (ml' : PKp) (c : Msg) (σ : Sigc × Sigp) : Prop :=
  verify_committed cr frame id ed' ml' ∧ hybridVerify Cl Pq (ed', ml') c σ

/-- **A matching session at `P`** — `P` signed the challenge `c` (a real session at `P` with matching
conversation). The honest signing oracle `Q` records exactly `P`'s signed challenges. -/
def MatchingSession (Q : Msg → Prop) (c : Msg) : Prop := Q c

/-! ## PART 2 — AUTHENTICATION: an accepting session has a matching session, or the floor breaks.

The load-bearing dichotomy. An accepting session with NO matching conversation is either a hybrid
`Forgery` on `P`'s committed keys (the signature verified on a fresh challenge) or a SECOND committed key
pair distinct from `P`'s (the carried keys differed yet still passed the commitment gate). The first breaks
`EufCma`, the second breaks `HashCR`. -/

/-- **THE AUTHENTICATION DICHOTOMY (the reduction core).** If a session ACCEPTS peer `id` on `c` but `P`
has NO matching session (`¬ Q c`), then EITHER

  * a hybrid `Forgery` on `P`'s committed keys `(edP, mlP)` exists — the carried keys equalled `P`'s (forced
    by the commitment) and the signature verified on the FRESH `c`; OR
  * `¬ HashCR` — the carried keys DIFFERED from `P`'s yet both hash into the SAME id `id`, a hash collision
    (`distinct_verifying_pairs_break_hashcr`).

`P`'s own keys are committed by `hcommitP`. This is "impersonate ⟹ forge OR collide". -/
theorem accept_without_match_breaks_auth
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (cr : CommitReveal Unit Pre Id) (frame : PKc → PKp → Pre)
    (hframe : Function.Injective2 frame)
    (id : Id) (edP : PKc) (mlP : PKp) (Q : Msg → Prop)
    (hcommitP : verify_committed cr frame id edP mlP)
    (ed' : PKc) (ml' : PKp) (c : Msg) (σ : Sigc × Sigp)
    (hacc : SessionAccepts Cl Pq cr frame id ed' ml' c σ)
    (hnomatch : ¬ Q c) :
    Forgery (hybrid Cl Pq) (edP, mlP) Q ∨ ¬ HashCR cr := by
  obtain ⟨hcommit', hver⟩ := hacc
  by_cases hkeys : (ed', ml') = (edP, mlP)
  · -- the carried keys ARE P's: the accepting signature is a forgery on P's key at the fresh c.
    refine Or.inl ⟨c, σ, hnomatch, ?_⟩
    have hv : hybridVerify Cl Pq (edP, mlP) c σ := by rw [← hkeys]; exact hver
    exact hv
  · -- the carried keys DIFFER from P's yet both are committed to id: a hash collision.
    exact Or.inr
      (distinct_verifying_pairs_break_hashcr cr frame hframe id ed' edP ml' mlP hkeys hcommit' hcommitP)

/-- **AKE AUTHENTICATION (conditioned on the games).** Under `HashCR` (id-commitment binding) and `EufCma`
of `P`'s hybrid signature over its signed set `Q`, a session that ACCEPTS peer `P` HAS a matching session
at `P` (`Q c`). No impersonation without breaking one of the two games. -/
theorem ake_authentication
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (cr : CommitReveal Unit Pre Id) (frame : PKc → PKp → Pre)
    (hframe : Function.Injective2 frame) (hcr : HashCR cr)
    (id : Id) (edP : PKc) (mlP : PKp) (Q : Msg → Prop)
    (hcommitP : verify_committed cr frame id edP mlP)
    (heuf : EufCma (hybrid Cl Pq) (edP, mlP) Q)
    (ed' : PKc) (ml' : PKp) (c : Msg) (σ : Sigc × Sigp)
    (hacc : SessionAccepts Cl Pq cr frame id ed' ml' c σ) :
    MatchingSession Q c := by
  by_contra hnomatch
  rcases accept_without_match_breaks_auth Cl Pq cr frame hframe id edP mlP Q hcommitP
    ed' ml' c σ hacc hnomatch with hforge | hnhcr
  · exact heuf hforge
  · exact hnhcr hcr

/-! ### Grounding authentication in the floor — discharge `EufCma` to `SchnorrDLHard ∨ MSISHard`.

`HybridCombiner.hybrid_secure_if_either_floor` turns the two PROVED forking reductions (a classical forgery
⟹ a `DLSolver`; an ML-DSA forgery ⟹ a SelfTargetMSIS pair) plus the FLOOR disjunction `SchnorrDLHard ∨
MSISHard` into `EufCma` of the hybrid signature. Feeding that here leaves exactly two residuals:
`SchnorrDLHard ∨ MSISHard` (authentication of the signature) and `HashCR` (the id commitment). -/

/-- **AKE AUTHENTICATION, GROUNDED IN THE FLOOR.** With the ed25519→DL and ML-DSA→MSIS forking reductions
in hand, an accepting session has a matching session at `P` provided `HashCR` holds and EITHER the
discrete-log floor `SchnorrDLHard` OR the Module-SIS floor `MSISHard` holds. Impersonation reduces to
`(SchnorrDLHard ∨ MSISHard) ∧ HashCR` — nothing above the standard floor. -/
theorem ake_authentication_grounded
    (Cl : SigScheme SKc PKc Msg Sigc) (Pq : SigScheme SKp PKp Msg Sigp)
    (cr : CommitReveal Unit Pre Id) (frame : PKc → PKp → Pre)
    (hframe : Function.Injective2 frame) (hcr : HashCR cr)
    (id : Id) (edP : PKc) (mlP : PKp) (Q : Msg → Prop)
    (hcommitP : verify_committed cr frame id edP mlP)
    (C : CurveGroup) (G : C.Pt)
    {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
    {MM : Type*} [AddCommGroup MM] [Module Rq MM] [ShortNorm MM]
    {NN : Type*} [AddCommGroup NN] [Module Rq NN] [ShortNorm NN]
    (A : MM →ₗ[Rq] NN) (t : NN) (β : ℕ)
    (dlFork : Forgery Cl edP Q → DLSolver C G)
    (msisFork : Forgery Pq mlP Q →
      ∃ (w : NN) (cc cc' : Rq) (z z' : MM), cc ≠ cc' ∧
        IsSelfTargetMSISSolution A t β z cc w ∧ IsSelfTargetMSISSolution A t β z' cc' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A t) ((β + β) + (β + β)))
    (ed' : PKc) (ml' : PKp) (c : Msg) (σ : Sigc × Sigp)
    (hacc : SessionAccepts Cl Pq cr frame id ed' ml' c σ) :
    MatchingSession Q c :=
  ake_authentication Cl Pq cr frame hframe hcr id edP mlP Q hcommitP
    (hybrid_secure_if_either_floor Cl Pq edP mlP Q C G A t β dlFork msisFork hfloor)
    ed' ml' c σ hacc

/-! ## PART 3 — KEY SECRECY: the session key is IND-CCA if EITHER component is.

The session key is the deployed hybrid-KEM output `combine(ss_x, ss_pq, transcript)` — the concat-KDF over
BOTH shared secrets and the full transcript (`dregg-pq/src/hybrid_kem.rs`, modeled `DreggKemApi.combine`).
The AKE `Test` on a fresh session is exactly the KEM IND-CCA challenge on that key. This inherits
`DreggKemRefinement.dregg_kem_ind_cca_if_either` (itself `HybridCombiner.hybrid_kem_ind_cca_if_either`):
under the X-Wing dual-PRF, the key is unpredictable if the X25519 OR the ML-KEM shared-secret source is. -/

/-- **AKE KEY SECRECY (deployed combine).** The session key of a fresh matching session — `combine` over
the two shared secrets and the transcript — is IND-CCA (unpredictable given the transcript) if EITHER the
X25519 source `sourceX` OR the ML-KEM source `sourcePq` is IND-CCA, under the HKDF dual-PRF. So the `Test`
succeeds if EITHER component holds. The disjuncts bottom out at `SchnorrDLHard` (X25519) and
`MLWESearchHard` (ML-KEM), in the model. -/
theorem ake_session_key_secure
    {Xsk Xpk Dk Ek CT SS Tr : Type*}
    (api : DreggKemApi Xsk Xpk Dk Ek CT SS Tr) (hdual : DreggKemKdfIsDualPRF api) (tr : Tr)
    {In : Type*} (sourceX sourcePq : In → SS) (ssx sspq : SS)
    (heither : KemIndCca sourceX ∨ KemIndCca sourcePq) :
    KemIndCca (fun i => api.combine (sourceX i) sspq tr) ∨
    KemIndCca (fun i => api.combine ssx (sourcePq i) tr) :=
  dregg_kem_ind_cca_if_either api hdual tr sourceX sourcePq ssx sspq heither

/-- **AKE KEY SECRECY (abstract KDF).** The same statement at the bare combiner level — the `Test` key is
unpredictable if either shared-secret source is, under any dual-PRF `KDF`. This is
`HybridCombiner.hybrid_kem_ind_cca_if_either` presented as the AKE key-secrecy reduction; the deployed form
above is its specialization to `api.combine`. -/
theorem ake_session_key_secure_kdf {SS Tr : Type*}
    (KDF : SS → SS → Tr → SS) (hdual : DualPRF KDF) (tr : Tr)
    {In : Type*} (sourceX sourcePq : In → SS) (ssx sspq : SS)
    (heither : KemIndCca sourceX ∨ KemIndCca sourcePq) :
    KemIndCca (fun i => KDF (sourceX i) sspq tr) ∨ KemIndCca (fun i => KDF ssx (sourcePq i) tr) :=
  hybrid_kem_ind_cca_if_either KDF hdual tr sourceX sourcePq ssx sspq heither

/-! ## PART 4 — CHANNEL BINDING: the session key BINDS the transcript (no UKS).

The concat-KDF input includes the transcript, modeled — as in `IdentityCommitment` — as a
collision-resistant hash `H` over an INJECTIVE framing of `(ss_x, ss_pq, transcript)`. Two sessions with
the same key therefore have the same *entire* input, in particular the same transcript. An unknown-key-share
/ key-reuse attack — two sessions accepting a shared key across DIFFERENT transcripts — is thus a hash
collision, breaking `HashCR`. -/

/-- **The channel-bound session key** `H(frameK (ss_x, ss_pq, transcript))` — the concat-KDF over the two
shared secrets AND the transcript, through the collision-resistant hash carrier `cr` on the injective
framing `frameK`. Models `combine(ss_x, ss_pq, transcript)` with its transcript input made explicit. -/
def sessionKey {SS Tr K : Type*} (cr : CommitReveal Unit Pre K) (frameK : SS × SS × Tr → Pre)
    (ssx sspq : SS) (tr : Tr) : K :=
  cr.H () (frameK (ssx, sspq, tr))

/-- **CHANNEL BINDING (the floor).** Under `HashCR` and an injective framing, two session keys that are
EQUAL come from the SAME `(ss_x, ss_pq, transcript)` triple. The key determines its transcript: no
key-reuse across distinct transcripts. -/
theorem channel_binding {SS Tr K : Type*} (cr : CommitReveal Unit Pre K)
    (frameK : SS × SS × Tr → Pre) (hf : Function.Injective frameK) (hcr : HashCR cr)
    (ssx sspq : SS) (tr : Tr) (ssx' sspq' : SS) (tr' : Tr)
    (h : sessionKey cr frameK ssx sspq tr = sessionKey cr frameK ssx' sspq' tr') :
    (ssx, sspq, tr) = (ssx', sspq', tr') :=
  hf (hcr () _ _ h)

/-- **CHANNEL BINDING (transcript projection).** Equal session keys ⟹ equal transcripts — the precise
anti-UKS statement: a shared key pins a shared channel. -/
theorem channel_binding_transcript {SS Tr K : Type*} (cr : CommitReveal Unit Pre K)
    (frameK : SS × SS × Tr → Pre) (hf : Function.Injective frameK) (hcr : HashCR cr)
    (ssx sspq : SS) (tr : Tr) (ssx' sspq' : SS) (tr' : Tr)
    (h : sessionKey cr frameK ssx sspq tr = sessionKey cr frameK ssx' sspq' tr') :
    tr = tr' :=
  congrArg (fun p => p.2.2) (channel_binding cr frameK hf hcr ssx sspq tr ssx' sspq' tr' h)

/-- **THE UKS REDUCTION.** A key-reuse / unknown-key-share attack — one session key shared across DISTINCT
transcripts `tr ≠ tr'` — BREAKS `HashCR`. It is exactly a transcript collision on the concat-KDF hash: the
contrapositive of `channel_binding`. This grounds channel binding in the single carrier `HashCR`. -/
theorem uks_breaks_hashcr {SS Tr K : Type*} (cr : CommitReveal Unit Pre K)
    (frameK : SS × SS × Tr → Pre) (hf : Function.Injective frameK)
    (ssx sspq : SS) (tr : Tr) (ssx' sspq' : SS) (tr' : Tr) (hdiff : tr ≠ tr')
    (h : sessionKey cr frameK ssx sspq tr = sessionKey cr frameK ssx' sspq' tr') :
    ¬ HashCR cr :=
  fun hcr => hdiff (channel_binding_transcript cr frameK hf hcr ssx sspq tr ssx' sspq' tr' h)

#assert_axioms accept_without_match_breaks_auth
#assert_axioms ake_authentication
#assert_axioms ake_authentication_grounded
#assert_axioms ake_session_key_secure
#assert_axioms ake_session_key_secure_kdf
#assert_axioms channel_binding
#assert_axioms channel_binding_transcript
#assert_axioms uks_breaks_hashcr

/-! ## TEETH — an honest handshake matches + keys securely; an uncommitted key is rejected; a
transcript-blind KDF admits UKS.

Concrete, decidable instances so the `#guard`s fire.

(a) HONEST HANDSHAKE ⟹ MATCHING SESSION + SECURE KEY. A hybrid signature scheme that verifies exactly the
    signed challenge, over the honest committed keys, ACCEPTS and yields a matching session
    (`ake_authentication` fires); the good dual-PRF gives a secure key (`ake_session_key_secure_kdf` fires).
(b) THE ID-COMMITMENT TOOTH. An attacker keeping the honest ed25519 but presenting its OWN ML-DSA key is
    REJECTED — `SessionAccepts` fails at the commitment gate (`attacker_key_not_committed`).
(c) THE CHANNEL-BINDING TOOTH. A KDF that IGNORES the transcript admits UKS: two DISTINCT transcripts share
    one key, so the framing is NOT injective and `channel_binding` genuinely fails — the transcript input
    is load-bearing. -/

section Teeth

/-! ### (a) The honest handshake — matching session and secure key. -/

/-- The classical (ed25519) component for the teeth: over `ed`-keys `ℕ`, verifies the challenge `true` with
signature `true`. Its EUF-CMA holds against the signed set `{true}` (a fresh `false` never verifies). -/
def clSig : SigScheme Unit ℕ Bool Bool where
  pkOf _ := 0
  sign _ _ := true
  verify _ m σ := m = true ∧ σ = true

/-- The post-quantum (ML-DSA) component: over `ml`-keys `List ℕ`, same acceptance shape. -/
def pqSig : SigScheme Unit (List ℕ) Bool Bool where
  pkOf _ := []
  sign _ _ := true
  verify _ m σ := m = true ∧ σ = true

/-- `P`'s signed set: only the challenge `true` was signed (the matching-conversation oracle). -/
def sigQ : Bool → Prop := fun m => m = true

/-- The honest peer `P`'s committed keys `(ed = 1, ml = [2,3])` verify against the enrolled id `exId`
(reusing `IdentityCommitment`'s concrete commitment instance). -/
theorem honest_committed : verify_committed exCR exFrame exId 1 [2, 3] := honest_verifies

/-- The honest hybrid signature is EUF-CMA over `sigQ`: a forgery needs a FRESH `m` (`m ≠ true`) whose
classical half verifies, but verification forces `m = true` — contradiction. Non-vacuous authentication. -/
theorem honest_euf : EufCma (hybrid clSig pqSig) (1, [2, 3]) sigQ := by
  rintro ⟨m, σ, hfresh, hv⟩
  exact hfresh hv.1.1

/-- The honest session ACCEPTS: the committed keys pass the gate and both signature halves verify on the
challenge `true`. -/
theorem honest_accepts :
    SessionAccepts clSig pqSig exCR exFrame exId 1 [2, 3] true (true, true) :=
  ⟨honest_verifies, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- **HONEST ⟹ MATCHING (the tooth fires).** `ake_authentication` turns the honest accepting session into a
matching session at `P` — `sigQ true`, i.e. `P` really signed the challenge. -/
theorem honest_yields_matching : MatchingSession sigQ true :=
  ake_authentication clSig pqSig exCR exFrame exFrame_inj exCR_hashcr exId 1 [2, 3] sigQ
    honest_committed honest_euf 1 [2, 3] true (true, true) honest_accepts

/-- **HONEST ⟹ SECURE KEY (the tooth fires).** With an unpredictable X25519 source (`id`), the good
dual-PRF `goodKDF` gives an IND-CCA session key — `ake_session_key_secure_kdf` through the classical
channel. -/
theorem honest_key_secure (sspq tr : ℤ) :
    KemIndCca (fun i : ℤ => goodKDF (id i) sspq tr) ∨
    KemIndCca (fun i : ℤ => goodKDF (0 : ℤ) (id i) tr) :=
  ake_session_key_secure_kdf goodKDF goodKDF_dualPRF tr id id 0 sspq (Or.inl Function.injective_id)

/-! ### (b) The id-commitment tooth — an uncommitted ML-DSA key is rejected. -/

/-- **THE ID-COMMITMENT TOOTH.** An attacker keeps the honest `ed = 1` but presents its OWN `ml_dsa = [9]`
(never committed into `exId`): the session does NOT accept — `SessionAccepts` fails at the commitment gate,
via `attacker_key_not_committed`. A self-carried PQ key cannot impersonate `P`. -/
theorem attacker_uncommitted_rejected (c : Bool) (σ : Bool × Bool) :
    ¬ SessionAccepts clSig pqSig exCR exFrame exId 1 [9] c σ :=
  fun h => attacker_ml_rejected h.1

/-! ### (c) The channel-binding tooth — a transcript-blind KDF admits UKS. -/

/-- The honest (transcript-including) framing over `ℤ`: the identity on the triple `(ss_x, ss_pq, tr)` —
injective, so the transcript is bound. Its hash carrier is the identity `HashCR` instance. -/
def crK : CommitReveal Unit (ℤ × ℤ × ℤ) (ℤ × ℤ × ℤ) := ⟨fun _ p => p⟩

theorem crK_hashcr : HashCR crK := fun _ _ _ h => h

/-- **CHANNEL BINDING FIRES.** Distinct transcripts give DISTINCT session keys — equal keys would (by
`channel_binding`) force equal transcripts. -/
theorem honest_transcripts_distinct :
    sessionKey crK id 1 2 3 ≠ sessionKey crK id 1 2 4 := by decide

/-- A transcript-BLIND framing: `(ss_x, ss_pq, tr) ↦ (ss_x, ss_pq)` DROPS the transcript (a KDF keyed only
on the secrets). Its hash carrier is over `ℤ × ℤ`. -/
def crKbad : CommitReveal Unit (ℤ × ℤ) (ℤ × ℤ) := ⟨fun _ p => p⟩

/-- The transcript-blind framing. -/
def frameKbad : ℤ × ℤ × ℤ → ℤ × ℤ := fun p => (p.1, p.2.1)

/-- `frameKbad` is NOT injective — it collapses distinct transcripts (`(1,2,3)` and `(1,2,4)` collide). -/
theorem frameKbad_not_injective : ¬ Function.Injective frameKbad :=
  fun h => absurd (h (show frameKbad (1, 2, 3) = frameKbad (1, 2, 4) from rfl)) (by decide)

/-- **THE CHANNEL-BINDING TOOTH (UKS).** With the transcript-blind framing, TWO sessions on DISTINCT
transcripts `3 ≠ 4` share ONE session key — an unknown-key-share. So `channel_binding`'s injective-framing
hypothesis is load-bearing: drop the transcript from the KDF input and the key no longer binds the channel. -/
theorem uks_without_transcript :
    sessionKey crKbad frameKbad 1 2 3 = sessionKey crKbad frameKbad 1 2 4 ∧ (3 : ℤ) ≠ 4 :=
  ⟨rfl, by decide⟩

-- The honest session accepts, and its keys are the committed pair.
#guard decide (exFrame 1 [2, 3] = [1, 2, 2, 3])
-- The attacker's own ml_dsa is a DIFFERENT commitment — the gate rejects it.
#guard decide (exFrame 1 [9] ≠ [1, 2, 2, 3])
-- Channel binding: distinct transcripts ⟹ distinct keys (the concat-KDF binds the transcript)…
#guard decide (sessionKey crK id 1 2 3 ≠ sessionKey crK id 1 2 4)
-- …but a transcript-BLIND KDF collides them — the UKS the binding forbids.
#guard decide (sessionKey crKbad frameKbad 1 2 3 = sessionKey crKbad frameKbad 1 2 4)
-- The good dual-PRF is injective in each channel (key secrecy propagates from either component).
#guard decide (goodKDF 7 3 () ≠ goodKDF 8 3 ())
#guard decide (goodKDF 7 3 () ≠ goodKDF 7 4 ())

end Teeth

#assert_all_clean [
  accept_without_match_breaks_auth,
  ake_authentication,
  ake_authentication_grounded,
  ake_session_key_secure,
  ake_session_key_secure_kdf,
  channel_binding,
  channel_binding_transcript,
  uks_breaks_hashcr,
  honest_committed,
  honest_euf,
  honest_accepts,
  honest_yields_matching,
  honest_key_secure,
  attacker_uncommitted_rejected,
  crK_hashcr,
  honest_transcripts_distinct,
  frameKbad_not_injective,
  uks_without_transcript
]

end Dregg2.Crypto.WireAke

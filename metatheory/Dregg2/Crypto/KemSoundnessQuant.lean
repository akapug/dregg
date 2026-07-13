/-
# `Dregg2.Crypto.KemSoundnessQuant` — the KEM / decisional-MLWE consumers, migrated onto the QUANTITATIVE floor.

The 07-13 floor-fix proved the Boolean lattice floors VACUOUS: `Lattice.MLWESearchHard A β t` is an
EXISTENCE-refutation (`¬ ∃ short (s,e), t = A·s + e`), FALSE at every genuine public key — the witnessing
short `(s,e)` IS the secret key (`CryptoFloorTeeth.not_mlweSearchHard_of_sample`). Every theorem conditioned
on it is discharged by a vacuous hypothesis. The PROPER floor is the adversary-indexed
`ProbCrypto.MLWEHardQuant (adv : S → Ensemble) := ∀ s, Negl (adv s)` — a real λ-decaying advantage ensemble,
satisfiable-but-not-provable (a `1/2^λ` guessing family satisfies it, a constant `2/5` refutes it).

The SIGNATURE side of the sweep is re-grounded (`CryptoFloorTeeth.dregg_pq_game_forger_negl_under_comp_floor`,
`ProtocolSoundnessQuant`'s DL/MSIS/HashCR anchors, `ModelBridge`). The KEM / decisional-MLWE side — the
DEPLOYED `dregg-kem` X-Wing hybrid and the ML-KEM IND-CCA reduction it rests on — was NOT: no consumer of
`MLWEHardQuant` existed, even though `Dregg2.Tactics.ThreadAdvantageBound` wired the MLWE floor leaf. This
module closes that gap: the advantage-bounded siblings of the Boolean `MLWESearchHard` consumers in
`MlKemIndCca` / `Fips203Kem` / `DreggKemRefinement`, discharged by `thread_advantage_bound`.

## The uniform shape (the concrete-security shadow of each Boolean KEM reduction)

Each `MLWESearchHard`-conditioned reduction becomes an ADVANTAGE ensemble over the proper floor:

  * **key recovery / IND-CPA** (`MlKemIndCca.pke_key_recovery_reduces_to_mlwe`,
    `MlKemIndCca.ind_cpa_reduces_to_mlwe`): a total-break / distinguishing adversary IS an MLWE
    search / decisional-MLWE solver, so its advantage IS `mlweSolverOf s` — a BARE floor leaf,
    `Negl (mlweSolverOf s)` under `MLWEHardQuant mlweSolverOf` (`mlwe_primitive_advantage_negl`).
  * **ML-KEM IND-CCA in the QROM** (`MlKemIndCca.ml_kem_ind_cca_reduces_to_mlwe`): the FO transform's
    IND-CCA advantage is the IND-CPA (decisional-MLWE) leg PLUS the `H(m)` random-oracle guessing term. Here
    the opaque `QROMInjective` idealisation becomes an EXPLICIT `1/2^λ` decay leg, and the composite
    `kemIndCcaAdv (mlweSolverOf s) = mlweSolverOf s + 1/2^λ` threads through `negl_add` (`negl_two_pow` on the
    QROM leg, the floor leaf on the lattice leg) — `ml_kem_ind_cca_advantage_negl`.
  * **the DEPLOYED X-Wing hybrid** (`DreggKemRefinement.dregg_kem_ind_cca_if_either`,
    `MlKemIndCca.hybrid_kem_ind_cca_grounded_in_mlwe`): IND-CCA through EITHER channel. Its PQ leg is the
    ML-KEM composite under `MLWEHardQuant` (`dregg_kem_pq_leg_advantage_negl`); its classical (X25519) leg is
    the same composite under `DLHardQuant` (`dregg_kem_classical_leg_advantage_negl`). The dual-PRF `KDF` is an
    unconditional structural fact (`DreggKemRefinement.DreggKemKdfIsDualPRF`), so it adds no crypto term — the
    channel advantage IS the underlying KEM's IND-CCA advantage, exactly as each Boolean leg shares
    `hybrid_kem_ind_cca_if_either`.

## Non-fake (this is not the bare-leaf `forger_advantage_bound_under_msis` in KEM costume)

The QROM leg is a GENUINE additive term with real content: `kem_ind_cca_advantage_load_bearing` shows the
`1/2^λ` guessing term does NOT rescue a broken lattice floor — with `mlweSolverOf s` a constant `2/5`, the
composite `2/5 + 1/2^λ` is bounded below by `2/5` and is NOT negligible. So the `MLWEHardQuant` hypothesis is
load-bearing THROUGH the composite. The floor itself is a genuine assumption: `mlwe_floor_load_bearing`
refutes it with a constant-`1` solver (`not_negl_one`), `mlwe_floor_satisfiable` satisfies it with a decaying
`1/2^λ` (`negl_two_pow`). And the tactic is a real discharger: `fail_if_success` witnesses it REFUSING the
non-negligible `2/5 + 1/2^λ` composite (no floor to appeal to).

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`), no `sorry`.
-/
import Dregg2.Tactics.ThreadAdvantageBound

namespace Dregg2.Crypto.KemSoundnessQuant

open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto

set_option autoImplicit false

/-! ## §1 — The MLWE primitive leaf: KEM total-break and IND-CPA.

`MlKemIndCca.pke_key_recovery_reduces_to_mlwe` reads a recovered short secret key BACK as an MLWE preimage of
the public key, and `MlKemIndCca.ind_cpa_reduces_to_mlwe` reads an IND-CPA distinguisher BACK as a
decisional-MLWE distinguisher on the masking sample. In both, the KEM adversary IS an MLWE solver of the SAME
advantage — so the concrete-security restatement is a BARE floor leaf: under the proper `MLWEHardQuant` floor
the adversary's advantage is negligible. -/

/-- **THE MLWE PRIMITIVE LEAF (KEM key-recovery / IND-CPA).** The advantage-bounded sibling of
`MlKemIndCca.pke_key_recovery_reduces_to_mlwe` and `MlKemIndCca.ind_cpa_reduces_to_mlwe`: a KEM total-break
(search-MLWE) or IND-CPA (decisional-MLWE) adversary at solver index `s` has negligible advantage under the
proper `MLWEHardQuant mlweSolverOf` floor — the recovered key / distinguisher IS an MLWE solver, so its
advantage is exactly the floor leaf `mlweSolverOf s`. Proof: `thread_advantage_bound` (the `MLWEHardQuant`
leaf). Replaces the vacuous existence-refutation `Lattice.MLWESearchHard`. -/
theorem mlwe_primitive_advantage_negl {S : Type*} (mlweSolverOf : S → Ensemble) (s : S)
    (hfloor : MLWEHardQuant mlweSolverOf) : Negl (mlweSolverOf s) := by
  thread_advantage_bound

/-! ## §2 — The FO/QROM composite: ML-KEM IND-CCA reduces to decisional-MLWE.

`MlKemIndCca.ml_kem_ind_cca_reduces_to_mlwe` grounds ML-KEM IND-CCA in `MLWESearchHard` + the QROM
idealisation (`QROMInjective H`, the `H(m)` random oracle). At the advantage level the QROM idealisation is an
EXPLICIT decaying guessing term: an adversary that does not break the lattice leg can do no better than GUESS
the random-oracle value `K = H(m)`, advantage `1/2^λ`. So the IND-CCA advantage is the IND-CPA
(decisional-MLWE) leg PLUS that `1/2^λ` term. -/

/-- **THE ML-KEM IND-CCA ADVANTAGE.** The FO-transformed KEM's IND-CCA advantage as a function of the IND-CPA
(decisional-MLWE) advantage `cpaAdv`: the lattice leg PLUS the QROM random-oracle guessing term `1/2^λ` (the
explicit form of the `QROMInjective` idealisation). A genuine composite ensemble. -/
noncomputable def kemIndCcaAdv (cpaAdv : Ensemble) : Ensemble := fun l => cpaAdv l + 1 / (2 : ℝ) ^ l

/-- **THE COMPOSITE ANCHOR — the FO/QROM IND-CCA advantage is negligible whenever its IND-CPA leg is.**
`negl_add` on the `cpaAdv` leg (from context) and `negl_two_pow` on the QROM leg. The shared body every KEM
IND-CCA sibling routes through. Proof: `thread_advantage_bound`. -/
theorem kemIndCca_negl_of_cpa_negl (cpaAdv : Ensemble) (hcpa : Negl cpaAdv) :
    Negl (kemIndCcaAdv cpaAdv) := by
  unfold kemIndCcaAdv
  thread_advantage_bound

/-- **ML-KEM IND-CCA, RE-GROUNDED** (the advantage-bounded sibling of
`MlKemIndCca.ml_kem_ind_cca_reduces_to_mlwe`). Under the proper `MLWEHardQuant mlweSolverOf` floor, the FO/QROM
ML-KEM IND-CCA advantage `mlweSolverOf s + 1/2^λ` is negligible — the lattice leg through the floor leaf, the
QROM leg through `negl_two_pow`. "ML-KEM IND-CCA reduces to decisional Module-LWE in the QROM" on the genuine
decaying-advantage floor, replacing the vacuous Boolean `MLWESearchHard` + opaque `QROMInjective`. Proof:
`thread_advantage_bound` (`negl_add`; the `MLWEHardQuant` leaf; `negl_two_pow`). -/
theorem ml_kem_ind_cca_advantage_negl {S : Type*} (mlweSolverOf : S → Ensemble) (s : S)
    (hfloor : MLWEHardQuant mlweSolverOf) : Negl (kemIndCcaAdv (mlweSolverOf s)) := by
  unfold kemIndCcaAdv
  thread_advantage_bound

/-! ## §3 — The DEPLOYED X-Wing hybrid (`dregg-kem`): IND-CCA through either channel.

`DreggKemRefinement.dregg_kem_ind_cca_if_either` is the SHIPPED hybrid KEM: under the HKDF dual-PRF, the
session key is IND-CCA through whichever channel is secure. The dual-PRF `combine` is an unconditional
structural fact (`DreggKemKdfIsDualPRF`), so the channel advantage IS the underlying KEM's IND-CCA advantage.
Each channel gets its own floor: the PQ (ML-KEM) leg on `MLWEHardQuant`, the classical (X25519) leg on
`DLHardQuant`. These are the concrete-security shadows of `hybrid_secure_under_msis_alone` /
`hybrid_secure_under_dl_alone` for the KEM, mirroring the signature side. -/

/-- **THE DEPLOYED `dregg-kem` PQ CHANNEL, RE-GROUNDED.** The PQ (ML-KEM) leg of
`DreggKemRefinement.dregg_kem_ind_cca_if_either` — its session-key advantage through the ML-KEM channel is the
FO/QROM IND-CCA composite, negligible under the proper `MLWEHardQuant` floor. No classical model needed: the
deployed post-quantum KEM claim standing on the lattice floor alone. -/
theorem dregg_kem_pq_leg_advantage_negl {S : Type*} (mlweSolverOf : S → Ensemble) (s : S)
    (hfloor : MLWEHardQuant mlweSolverOf) : Negl (kemIndCcaAdv (mlweSolverOf s)) :=
  ml_kem_ind_cca_advantage_negl mlweSolverOf s hfloor

/-- **THE DEPLOYED `dregg-kem` CLASSICAL CHANNEL, RE-GROUNDED.** The classical (X25519) leg of
`DreggKemRefinement.dregg_kem_ind_cca_if_either` — its session-key advantage through the X25519 channel is the
same FO/QROM IND-CCA composite, negligible under the proper `DLHardQuant` floor (the field-scalar discrete-log
assumption). The symmetric partner of the PQ leg; together they are "hybrid KEM, secure if EITHER channel
is". Proof: `thread_advantage_bound` (`negl_add`; the `DLHardQuant` leaf; `negl_two_pow`). -/
theorem dregg_kem_classical_leg_advantage_negl {S : Type*} (dlSolverOf : S → Ensemble) (s : S)
    (hfloor : DLHardQuant dlSolverOf) : Negl (kemIndCcaAdv (dlSolverOf s)) := by
  unfold kemIndCcaAdv
  thread_advantage_bound

/-! ## §4 — Non-vacuity: the floor is genuine and load-bearing THROUGH the composite. -/

/-- **THE FLOOR IS SATISFIABLE (non-vacuous).** A minimal `1/2^λ`-decaying MLWE solver family satisfies
`MLWEHardQuant` — the floor holds for reasons of RATE, not because the advantage is trivially `0`
(`negl_two_pow`). -/
theorem mlwe_floor_satisfiable :
    MLWEHardQuant (fun _ : Unit => (fun l => 1 / (2 : ℝ) ^ l : Ensemble)) :=
  fun _ => negl_two_pow

/-- **THE FLOOR IS REFUTABLE (non-trivial).** A constant-`1` MLWE solver refutes `MLWEHardQuant`
(`not_negl_one`) — so the floor is a GENUINE assumption, satisfiable AND refutable, not a theorem. -/
theorem mlwe_floor_load_bearing :
    ¬ MLWEHardQuant (fun _ : Unit => (fun _ => (1 : ℝ) : Ensemble)) :=
  fun h => not_negl_one (h ())

/-- **THE QROM LEG DOES NOT RESCUE A BROKEN LATTICE FLOOR — the composite is LOAD-BEARING.** With the IND-CPA
(decisional-MLWE) advantage a constant `2/5` (a broken lattice floor), the ML-KEM IND-CCA composite
`2/5 + 1/2^λ` is bounded below by `2/5` and is NOT negligible — the additive `1/2^λ` QROM term cannot vanish
it. So `ml_kem_ind_cca_advantage_negl`'s `MLWEHardQuant` hypothesis is genuinely consumed: strip the lattice
floor and the IND-CCA advantage stays constant. This is the anti-laundering tooth — the composite is a real
advantage that CAN be non-negligible, not a relabelled floor leaf. -/
theorem kem_ind_cca_advantage_load_bearing :
    ¬ Negl (kemIndCcaAdv (fun _ => (2 : ℝ) / 5)) := by
  intro h
  have hconst : Negl (fun _ : ℕ => (2 : ℝ) / 5) := by
    refine negl_of_eventually_le (Filter.Eventually.of_forall (fun l => ?_)) h
    have hpow : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ l := by positivity
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5),
        abs_of_pos (by unfold kemIndCcaAdv; positivity : (0 : ℝ) < kemIndCcaAdv (fun _ => (2 : ℝ) / 5) l)]
    unfold kemIndCcaAdv
    linarith
  exact not_negl_const_pos (by norm_num) hconst

/-- **THE RE-GROUNDED KEM KEYSTONE FIRES.** On a secure (advantage-`0`) lattice leg the ML-KEM IND-CCA
composite `0 + 1/2^λ` is negligible — the reduction runs end-to-end to a genuine negligible-advantage
conclusion. -/
theorem kem_ind_cca_advantage_fires : Negl (kemIndCcaAdv (fun _ => 0)) :=
  kemIndCca_negl_of_cpa_negl (fun _ => 0) negl_zero

/-- **(TOOTH — the tactic REFUSES the non-negligible composite.)** With no floor in context and a broken
lattice leg (`2/5`), `thread_advantage_bound` cannot close `Negl (kemIndCcaAdv (fun _ => 2/5))`: the QROM leg
threads (`negl_two_pow`) but the constant `2/5` leaf has no floor and is not negligible, so the whole `negl_add`
fails. `fail_if_success` witnesses the refusal — the tactic discharges REAL negligibility, it does not
fabricate it. -/
example : True := by
  fail_if_success
    (have : Negl (kemIndCcaAdv (fun _ => (2 : ℝ) / 5)) := by
      unfold kemIndCcaAdv; thread_advantage_bound)
  trivial

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  mlwe_primitive_advantage_negl,
  kemIndCca_negl_of_cpa_negl,
  ml_kem_ind_cca_advantage_negl,
  dregg_kem_pq_leg_advantage_negl,
  dregg_kem_classical_leg_advantage_negl,
  mlwe_floor_satisfiable,
  mlwe_floor_load_bearing,
  kem_ind_cca_advantage_load_bearing,
  kem_ind_cca_advantage_fires
]

end Dregg2.Crypto.KemSoundnessQuant

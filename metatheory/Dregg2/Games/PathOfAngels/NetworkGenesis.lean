/-
# Path of Angels — Lean-owned Signal authority-head genesis

`processNetworkGenesisWire` is the semantic half of the operator ceremony that
installs a `PoaSignalHeadV1`.  It accepts only one exact Lean-emitted Signal
configuration and a genuinely empty Canon/history image, then emits the exact
config and Canon JSON strings Rust is permitted to persist.

The external ceremony remains responsible for deployment-manifest/genesis
verification and detached curator-signature verification.  Lean deliberately
does not accept a signature-shaped value as if syntax implied authenticity.
The externally atomically verified tuple enters here together. Lean rederives
the deployment id and binds every identity that reaches game state to its exact
emission, but deliberately does not relabel external signature verification as
a Lean proof.
-/
import Dregg2.Games.PathOfAngels.NetworkGenesisWire

namespace Dregg2.Games.PathOfAngels.NetworkGenesis

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NetworkJudgeWire
open Dregg2.Games.PathOfAngels.NetworkGenesisWire

set_option autoImplicit false

private def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

abbrev DEPLOYMENT_IDENTITY_DOMAIN : String := "POA-SIGNAL-DEPLOYMENT-IDENTITY-V2"
abbrev PRODUCTION_POLICY_ZERO_ISSUANCE_SHA256 : String :=
  "8346263cf2fd50210353dca763dfb8f1271e1154e766ca93553ef3abc12a65ca"
abbrev PRODUCTION_POLICY_PLAYER_GRANT_SHA256 : String :=
  "8d477a883e96bde09d6fe01b407a6dca7c7c7633f4dd7488d311eb6782e988b8"

/-- The two exact production-policy images the external deployment verifier
accepts. The first is the historical zero-issuance deployment, which cannot pay
for a turn. The second differs in exactly one authenticated claim:
`generic_genesis_value_issued = true`, paired by `poa-curator` with one exact
issuer move into a freshly drawn player-grant cell. This is a closed set, not a
policy prefix or a caller-chosen digest. -/
def productionPolicyDigestAccepted (digest : Digest32) : Bool :=
  decide (Emit.bytes32Hex digest = PRODUCTION_POLICY_ZERO_ISSUANCE_SHA256 ∨
    Emit.bytes32Hex digest = PRODUCTION_POLICY_PLAYER_GRANT_SHA256)

theorem productionPolicyDigestAccepted_of_zero_issuance {digest : Digest32}
    (h : Emit.bytes32Hex digest = PRODUCTION_POLICY_ZERO_ISSUANCE_SHA256) :
    productionPolicyDigestAccepted digest = true := by
  simp [productionPolicyDigestAccepted, h]

theorem productionPolicyDigestAccepted_of_player_grant {digest : Digest32}
    (h : Emit.bytes32Hex digest = PRODUCTION_POLICY_PLAYER_GRANT_SHA256) :
    productionPolicyDigestAccepted digest = true := by
  simp [productionPolicyDigestAccepted, h]

theorem productionPolicyDigestAccepted_refuses_other {digest : Digest32}
    (hz : Emit.bytes32Hex digest ≠ PRODUCTION_POLICY_ZERO_ISSUANCE_SHA256)
    (hg : Emit.bytes32Hex digest ≠ PRODUCTION_POLICY_PLAYER_GRANT_SHA256) :
    productionPolicyDigestAccepted digest = false := by
  simp [productionPolicyDigestAccepted, hz, hg]

private def expectedConfig (input : GenesisInputWire) : SignalTriangulation.Config :=
  -- ⚠ `UNBOUND_RUN_SEED`: genesis describes the mission TEMPLATE, and a template
  -- has no instance.  The live seed is drawn per run by `HiddenInstance.runSeedFor`
  -- and checked by `Judged.admissionChecks`; nothing at genesis time can name it.
  Emit.signalTemplateConfig input.deployment.federationId
    input.content.sourceDigest
    input.content.signalContentDigest input.content.contentRoot input.content.activationDigest

private def expectedConfigWire (input : GenesisInputWire) : GameConfigWire :=
  .signal (SignalConfigWire.ofSemantic (expectedConfig input))

private def expectedCanon (input : GenesisInputWire) : CanonState :=
  CanonState.empty input.deployment.federationId input.content.contentRoot
    input.content.activationDigest (expectedConfig input).mission.contentSession
    (expectedConfig input).mission.epoch input.content.curatorKey

private def emptyInitialState : InitialStateWire := {
  world := WorldStateWire.ofSemantic WorldState.empty
  known := []
  alpha := []
  superseded := []
  consumedRuns := []
  playerCounters := []
  canonRevision := 0
  curatorCounter := 0
  transitionCount := 0
  lastTransitionDigest := zeroDigest
}

/-- Structural protocol tags are checked inside Lean even though an external
verifier already parsed them.  A ceremony cannot silently feed a future schema
to a v1 semantic evaluator. -/
def protocolTagChecks (input : GenesisInputWire) : Bool :=
  decide (input.deployment.schema = DEPLOYMENT_SCHEMA) &&
  decide (input.deployment.deploymentDomain = DEPLOYMENT_DOMAIN) &&
  decide (input.content.signatureSchema = CONTENT_SIGNATURE_SCHEMA)

/-- Exact deployment-id preimage used by `scripts/poa-devnet-manifest.mjs`.
Digest spellings come from Lean's lowercase canonical encoder, not caller text. -/
def deploymentIdPreimage (input : GenesisInputWire) : String :=
  let nul := String.singleton (Char.ofNat 0)
  DEPLOYMENT_DOMAIN ++ nul ++ Emit.bytes32Hex input.deployment.federationId ++
    nul ++ Emit.bytes32Hex input.deployment.genesisSha256

/-- The persisted Signal deployment coordinate commits to the exact public
manifest bytes and immutable production policy as well as the public
genesis-derived deployment id. -/
def deploymentDigestPreimage (input : GenesisInputWire) : String :=
  let nul := String.singleton (Char.ofNat 0)
  DEPLOYMENT_IDENTITY_DOMAIN ++ nul ++ Emit.bytes32Hex input.deployment.deploymentId ++
    nul ++ Emit.bytes32Hex input.deployment.manifestSha256 ++
    nul ++ Emit.bytes32Hex input.deployment.policySha256

/-- Recompute the public deployment identity inside Lean. External verification
must still hash and validate the actual genesis bytes named by `genesisSha256`. -/
def deploymentBindingChecks (input : GenesisInputWire) : Bool :=
  decide (sha256Wire? (deploymentIdPreimage input) = some input.deployment.deploymentId) &&
  productionPolicyDigestAccepted input.deployment.policySha256 &&
  decide (sha256Wire? (deploymentDigestPreimage input) =
    some input.deployment.deploymentDigest)

/-- Zero is excluded for every externally verified 32-byte identity consumed by
this ceremony. This predicate is only a precondition on an externally and
atomically verified tuple; it is not signature, manifest, or genesis-byte
verification. The activation counter also retains room for a successor. -/
def nonzeroExternalIdentityChecks (input : GenesisInputWire) : Bool :=
  decide (input.deployment.deploymentId ≠ zeroDigest) &&
  decide (input.deployment.deploymentDigest ≠ zeroDigest) &&
  decide (input.deployment.federationId ≠ zeroDigest) &&
  decide (input.deployment.genesisSha256 ≠ zeroDigest) &&
  decide (input.deployment.manifestSha256 ≠ zeroDigest) &&
  decide (input.deployment.policySha256 ≠ zeroDigest) &&
  decide (input.content.manifestSha256 ≠ zeroDigest) &&
  decide (input.content.contentRoot ≠ zeroDigest) &&
  decide (input.content.activationDigest ≠ zeroDigest) &&
  decide (input.content.sourceDigest ≠ zeroDigest) &&
  decide (input.content.signalContentDigest ≠ zeroDigest) &&
  decide (input.content.curatorKey ≠ zeroDigest) &&
  decide (0 < input.content.activationCounter) &&
  decide (input.content.activationCounter < WIRE_NAT_LIMIT)

/-- The complete caller-supplied config must be the exact Signal config emitted
from the authenticated identities.  This is the tooth that refuses a
caller-chosen target, mission id, artifact, session, seed, budget, reward,
privacy grade, ballot regime, or relic policy. -/
def missionScopeChecks (input : GenesisInputWire) : Bool :=
  decide (input.content.contentEpoch = (expectedConfig input).mission.epoch.value) &&
  decide (input.config = expectedConfigWire input)

/-- Genesis means no prior world mutation, canon action, run receipt, player
counter, transition, or predecessor digest.  Empty sparse tables are canonical;
an explicit zero player row is refused earlier by the syntax decoder. -/
def zeroStateChecks (input : GenesisInputWire) : Bool :=
  decide (input.initial = emptyInitialState)

def genesisChecks (input : GenesisInputWire) : Bool :=
  protocolTagChecks input && deploymentBindingChecks input &&
    nonzeroExternalIdentityChecks input &&
    missionScopeChecks input && zeroStateChecks input

theorem genesisChecks_requires_exact_config {input : GenesisInputWire}
    (accepted : genesisChecks input = true) : input.config = expectedConfigWire input := by
  simp only [genesisChecks, Bool.and_eq_true] at accepted
  have missionAccepted := accepted.1.2
  simp only [missionScopeChecks, Bool.and_eq_true, decide_eq_true_eq] at missionAccepted
  exact missionAccepted.2

theorem genesisChecks_requires_empty_state {input : GenesisInputWire}
    (accepted : genesisChecks input = true) : input.initial = emptyInitialState := by
  simp only [genesisChecks, Bool.and_eq_true] at accepted
  have stateAccepted := accepted.2
  simpa [zeroStateChecks] using stateAccepted

theorem genesisChecks_requires_positive_activation_counter {input : GenesisInputWire}
    (accepted : genesisChecks input = true) : 0 < input.content.activationCounter := by
  simp only [genesisChecks, Bool.and_eq_true] at accepted
  have identityAccepted := accepted.1.1.2
  simp only [nonzeroExternalIdentityChecks, Bool.and_eq_true,
    decide_eq_true_eq] at identityAccepted
  exact identityAccepted.1.2

/-! ## Proof-carrying emission -/

/-- A value of this type can only be produced after the strict checks and exact
SHA/Canon encoders succeed.  Its output bytes are the authority image; the
semantic values are retained so later proofs do not reason from reparsed Rust
objects. -/
structure AuthorizedGenesis where
  input : GenesisInputWire
  config : SignalTriangulation.Config
  canon : CanonState
  output : GenesisOutputWire
  checks : genesisChecks input = true
  config_from_lean : config = expectedConfig input
  canon_from_lean : canon = expectedCanon input
  output_authority_exact : output.authorityId = input.deployment.federationId
  output_deployment_exact : output.deploymentDigest = input.deployment.deploymentDigest
  output_declared_deployment_exact :
    output.declaredDeploymentId = input.deployment.deploymentId
  output_deployment_genesis_exact :
    output.deploymentGenesisSha256 = input.deployment.genesisSha256
  output_deployment_manifest_exact :
    output.deploymentManifestSha256 = input.deployment.manifestSha256
  output_deployment_policy_exact :
    output.deploymentPolicySha256 = input.deployment.policySha256
  output_manifest_exact : output.manifestSha256 = input.content.manifestSha256
  output_content_root_exact : output.contentRoot = input.content.contentRoot
  output_activation_exact : output.activationDigest = input.content.activationDigest
  output_curator_exact : output.curatorKey = input.content.curatorKey
  output_epoch_exact : output.contentEpoch = input.content.contentEpoch
  output_activation_counter_exact :
    output.activationCounter = input.content.activationCounter
  output_config_exact : output.configJson = (GameConfigWire.signal (SignalConfigWire.ofSemantic config)).toJson
  output_canon_exact : output.canonJson = (CanonStateWire.ofSemantic canon).toJson
  output_hashes_exact :
    sha256Wire? output.configJson = some output.configSha256 ∧
      sha256Wire? output.canonJson = some output.canonSha256
  output_coordinates_exact :
    output.authorityLanes9 = faithfulLanes9 output.authorityId ∧
    output.deploymentLanes9 = faithfulLanes9 output.deploymentDigest ∧
    output.deploymentGenesisLanes9 = faithfulLanes9 output.deploymentGenesisSha256 ∧
    output.manifestLanes9 = faithfulLanes9 output.manifestSha256 ∧
    output.contentRootLanes9 = faithfulLanes9 output.contentRoot ∧
    output.activationLanes9 = faithfulLanes9 output.activationDigest ∧
    output.curatorKeyLanes9 = faithfulLanes9 output.curatorKey ∧
    output.configSha256Lanes9 = faithfulLanes9 output.configSha256 ∧
      output.canonSha256Lanes9 = faithfulLanes9 output.canonSha256
  output_has_no_history :
    output.transitionCount = 0 ∧ output.worldSequence = 0 ∧ output.canonRevision = 0 ∧
      output.lastTransitionDigest = zeroDigest
  output_is_canonical_syntax : decodeGenesisOutputSyntax output.toJson = some output

/-- Build the one allowed authority head.  Notice that output config and Canon
are projected from `config`/`canon`, not copied from the request. -/
def authorizeGenesis (input : GenesisInputWire) : Option AuthorizedGenesis := do
  if checked : genesisChecks input then
    let config := expectedConfig input
    let canon := expectedCanon input
    let canonWire := CanonStateWire.ofSemantic canon
    let configJson := (GameConfigWire.signal (SignalConfigWire.ofSemantic config)).toJson
    let canonJson := canonWire.toJson
    match configDigestEq : sha256Wire? configJson with
    | none => none
    | some configSha256 =>
      match canonDigestEq : sha256Wire? canonJson with
      | none => none
      | some canonSha256 =>
        let output : GenesisOutputWire := {
          authorityId := input.deployment.federationId
          deploymentDigest := input.deployment.deploymentDigest
          declaredDeploymentId := input.deployment.deploymentId
          deploymentGenesisSha256 := input.deployment.genesisSha256
          deploymentManifestSha256 := input.deployment.manifestSha256
          deploymentPolicySha256 := input.deployment.policySha256
          manifestSha256 := input.content.manifestSha256
          contentRoot := input.content.contentRoot
          activationDigest := input.content.activationDigest
          curatorKey := input.content.curatorKey
          contentEpoch := input.content.contentEpoch
          activationCounter := input.content.activationCounter
          transitionCount := 0
          worldSequence := canon.world.sequence
          canonRevision := canon.revision
          lastTransitionDigest := zeroDigest
          configJson
          canonJson
          configSha256
          canonSha256
          authorityLanes9 := faithfulLanes9 input.deployment.federationId
          deploymentLanes9 := faithfulLanes9 input.deployment.deploymentDigest
          deploymentGenesisLanes9 := faithfulLanes9 input.deployment.genesisSha256
          manifestLanes9 := faithfulLanes9 input.content.manifestSha256
          contentRootLanes9 := faithfulLanes9 input.content.contentRoot
          activationLanes9 := faithfulLanes9 input.content.activationDigest
          curatorKeyLanes9 := faithfulLanes9 input.content.curatorKey
          configSha256Lanes9 := faithfulLanes9 configSha256
          canonSha256Lanes9 := faithfulLanes9 canonSha256
        }
        if canonical : decodeGenesisOutputSyntax output.toJson = some output then
          some {
            input, config, canon, output
            checks := checked
            config_from_lean := rfl
            canon_from_lean := rfl
            output_authority_exact := rfl
            output_deployment_exact := rfl
            output_declared_deployment_exact := rfl
            output_deployment_genesis_exact := rfl
            output_deployment_manifest_exact := rfl
            output_deployment_policy_exact := rfl
            output_manifest_exact := rfl
            output_content_root_exact := rfl
            output_activation_exact := rfl
            output_curator_exact := rfl
            output_epoch_exact := rfl
            output_activation_counter_exact := rfl
            output_config_exact := rfl
            output_canon_exact := rfl
            output_hashes_exact := by
              constructor
              · exact configDigestEq
              · exact canonDigestEq
            output_coordinates_exact := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            output_has_no_history := ⟨rfl, rfl, rfl, rfl⟩
            output_is_canonical_syntax := canonical
          }
        else none
  else none

theorem AuthorizedGenesis.config_is_exact_emission (genesis : AuthorizedGenesis) :
    genesis.input.config = .signal (SignalConfigWire.ofSemantic genesis.config) := by
  calc
    genesis.input.config = expectedConfigWire genesis.input :=
      genesisChecks_requires_exact_config genesis.checks
    _ = .signal (SignalConfigWire.ofSemantic (expectedConfig genesis.input)) := rfl
    _ = .signal (SignalConfigWire.ofSemantic genesis.config) :=
      congrArg (fun c => GameConfigWire.signal (SignalConfigWire.ofSemantic c))
        genesis.config_from_lean.symm

theorem AuthorizedGenesis.canon_is_empty (genesis : AuthorizedGenesis) :
    genesis.canon = CanonState.empty genesis.input.deployment.federationId
      genesis.input.content.contentRoot genesis.input.content.activationDigest
      genesis.config.mission.contentSession genesis.config.mission.epoch
      genesis.input.content.curatorKey := by
  rw [genesis.canon_from_lean, genesis.config_from_lean]
  rfl

theorem AuthorizedGenesis.persisted_coordinates_are_lean_bytes (genesis : AuthorizedGenesis) :
    genesis.output.authorityId = genesis.input.deployment.federationId ∧
    genesis.output.deploymentDigest = genesis.input.deployment.deploymentDigest ∧
    genesis.output.configJson =
      (GameConfigWire.signal (SignalConfigWire.ofSemantic genesis.config)).toJson ∧
    genesis.output.canonJson = (CanonStateWire.ofSemantic genesis.canon).toJson := by
  exact ⟨genesis.output_authority_exact, genesis.output_deployment_exact,
    genesis.output_config_exact, genesis.output_canon_exact⟩

/-! ## Validated output and canonical `String → String` authority evaluator -/

def processNetworkGenesisWire (bytes : String) : Option String := do
  let input ← decodeGenesisInput bytes
  let genesis ← authorizeGenesis input
  some genesis.output.toJson

/-- Export-ready refusal convention: empty string means rejection.  The future
FFI shim must transport this result and persist its embedded JSON strings
verbatim; it must not recreate either object with serde/Rust game logic. -/
@[export dregg_poa_network_genesis]
def networkGenesisFFI (bytes : String) : String :=
  (processNetworkGenesisWire bytes).getD ""

/-! ## Live epoch-1 fixture and independently computed byte pins

⚑ RE-POINTED 2026-08-05.  These five deployment constants named the DEAD three-validator
federation (`4ea83e8e…`, manifest sha `427a7a33…`).  `poa/deployments/epoch-1/` was moved
to the live solo federation in `fff0e8df7`, whose flag day named `release-receipt.json`
and `image-identity.mjs` as deleted but did NOT say that the old manifest sha was pinned
here and in `poa-curator`.  It was, in three places, and this is one of them.

Every value below was recomputed INDEPENDENTLY — a standalone SHA-256 over the exact
preimages, not read back out of `sha256Wire?` or out of Rust:

* `FIXTURE_FEDERATION_ID` / `FIXTURE_GENESIS_SHA256` are read from
  `poa/deployments/epoch-1/poa-devnet.json`.
* `FIXTURE_DEPLOYMENT_MANIFEST_SHA256` is `sha256(poa-devnet.json)`, which also appears
  in `release-lock.json`'s `files[]` — a genuinely separate producer, so this one has a
  second source and stays a two-implementation pin.
* `FIXTURE_DEPLOYMENT_ID` REDERIVES: `sha256(DEPLOYMENT_DOMAIN ‖ 0 ‖ fed ‖ 0 ‖ genesis)`
  reproduces the id the live manifest carries, so Lean and the JS that wrote the manifest
  agree without either being told the answer.  `fixture_deployment_id_rederived` is that
  check inside Lean.
* `FIXTURE_DEPLOYMENT_DIGEST` is `sha256(DEPLOYMENT_IDENTITY_DOMAIN ‖ 0 ‖ id ‖ 0 ‖
  manifest ‖ 0 ‖ policy)`, and `deploymentBindingChecks` recomputes it here.

⚑ RE-POINTED 2026-10-01: the CONTENT half (`FIXTURE_MANIFEST_SHA256`, content root,
activation digest, source/signal digests, curator key, activation counter) is the signed
POAG1 bundle at content epoch 1 counter 12 (`1af7a2617`,
`poa/artifacts/poag1/manifest.sig.json`).  It had sat at counter 2 since 2026-08-04 while
the bundle moved to 12, so the frozen `dregg-lean-ffi` genesis input stopped matching what
the node's ceremony encoder builds from the checked-in deployment, and
`poa_signal_genesis`'s fixture-evaluator tests refused it.  Every value was read from that
encoder's output (the tuple the linked Lean evaluator accepts), and `fixtureInputBytes` was
checked to render byte-identical to `poa-network-genesis-input-v1.json`.

⚑ **THE PINS NO LONGER EVALUATE IN THIS MODULE (2026-08-08).** This module is in the
`Dregg2.FFI` closure — the crypto archive's build root — and the thirty-five
`native_decide` pins below (the byte pins here plus the hostile ceremony fixtures) ran at
elaboration, so a stale genesis fixture was a hard failure of every Rust proving target in
the workspace (the compilation-unit coupling the stale-fixture outage measured — and this
module's deployment constants are exactly the kind that go stale on a re-genesis).  The
pins' STATEMENTS stay here, each as an evaluation-free `check_* : Bool` definition (a
`def` body elaborates without running).  The EVALUATION — each `check_* = true`, pinned by
`native_decide` + `#assert_compiled` — lives in `NetworkGenesisFixtures.lean`, rooted in
the `PathOfAngelsGuards` library: a plain `lake build` still runs every pin, and a stale
fixture reds the guard library instead of the archive.

Named residue: NONE — no construction here demands a proof as data. -/

/-! ## Hostile ceremony fixtures -/

#assert_axioms genesisChecks_requires_exact_config
#assert_axioms genesisChecks_requires_empty_state
#assert_axioms genesisChecks_requires_positive_activation_counter
#assert_axioms productionPolicyDigestAccepted_of_zero_issuance
#assert_axioms productionPolicyDigestAccepted_of_player_grant
#assert_axioms productionPolicyDigestAccepted_refuses_other
#assert_axioms AuthorizedGenesis.config_is_exact_emission
#assert_axioms AuthorizedGenesis.canon_is_empty
#assert_axioms AuthorizedGenesis.persisted_coordinates_are_lean_bytes

-- The thirty-five fixture pins (`native_decide` + `#assert_compiled`) live in
-- `NetworkGenesisFixtures.lean`, rooted in `PathOfAngelsGuards` — see the fixture
-- header above.

end Dregg2.Games.PathOfAngels.NetworkGenesis

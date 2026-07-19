// The Fiat-Shamir transcript re-derivation driven by the LEAN-EMITTED Poseidon2
// permutation — the in-circuit closure of the arbitrary-challenge hole at FULL
// real-transcript scale.
//
// WHAT THIS IS. The deployed shrink transcript is the MultiField32Challenger
// (multifield_challenger.go): a BN254 duplex sponge (challenger_bn254.go) driven
// by the BabyBear<->BN254 pack/split/tag adapter. Every challenge the verifier
// consumes — PermAlpha/PermBeta, the constraint-folding alpha, zeta, the FRI
// batch-combination alpha, the per-round FRI betas, and the per-query index — is
// a squeeze off that sponge. The DEPLOYED hand-Go SettlementCircuit already
// re-derives every one of them in-circuit (settlement_circuit.go:207-239,321) and
// binds them (assert squeeze == supplied sample; betas/indices drawn live inside
// VerifyFriNative), so a prover cannot supply an arbitrary challenge for given
// commitment roots.
//
// This file lets the SAME adapter drive the LEAN-EMITTED permutation instead of
// the hand-Go one: newEmittedPoseidon2Perm replays emitted/poseidon2_template.json
// (Lean-authored, `challengerReplay`/`Poseidon2Fr.permuteW` provenance, proven
// bit-exact to the deployed Poseidon2Bn254 by TestReplayTemplateMatchesGoPoseidon2KAT
// and the Lean `#guard` KAT) through ReplayTemplate, and NewMultiFieldChallengerWithPerm
// installs it. rederiveShrinkChallenges then runs the full deployed transcript
// schedule through that challenger, re-deriving and BINDING every challenge in
// exactly the deployed observe/sample order.
//
// SUBSTRATE, said out loud. The nonlinear crypto PRIMITIVE — the Poseidon2-BN254
// permutation, the sponge's only source of constraints beyond linear packing —
// is the Lean-emitted R1CS (Rust calls into the Lean artifact via ReplayTemplate;
// it does not re-author the permutation). NAMED RESIDUAL: the MultiField ADAPTER
// wrapping the permutation — the radix-2^31 8-limb reduce_packed PACK, the
// length-tagged rate-padded absorb, and the 7-limb base-p SPLIT with its
// canonicity/38-bit/lexicographic SOUNDNESS range checks (multifield_challenger.go)
// — is still hand-Go. Those split-soundness range checks are AIR-level constraints;
// emitting THEM from Lean is the follow-up enforcement lane ChallengerFr.lean's
// §"Classified seam" already names. The committed challenger_replay_template.json
// (ChallengerReplayEmit.lean) is the plain capacity-0 sponge CORE only — it models
// none of that adapter, so it cannot be chained as the transcript atom (see
// emitted_challenger_replay_diff_test.go §3 and the full-transcript differential);
// this driver therefore reuses the bare emitted PERMUTATION template, which the
// adapter drives, rather than the capacity-0 duplex template.
package friverifier

import (
	"fmt"

	"github.com/consensys/gnark/frontend"
)

// emittedPoseidon2TemplatePath is the committed Lean-emitted Poseidon2-BN254
// permutation template (the 3-in/3-out boundaried permutation ReplayTemplate
// chains as the sponge primitive).
const emittedPoseidon2TemplatePath = "emitted/poseidon2_template.json"

// newEmittedPoseidon2Perm returns a width-3 sponge permutation backed by the
// LEAN-EMITTED Poseidon2-BN254 template, replayed over the live state through
// ReplayTemplate. Binding the three state lanes to the template's [in0,in1,in2]
// boundary and reading back its solved [out0,out1,out2] emits exactly the
// permutation's R1CS (same constraint count as the hand-Go gadget,
// TestReplayTemplateConstraintCountVsHandGo). A replay error is a wiring/template
// bug, surfaced as a panic (matching splitToFieldOrderLimbs's NewHint panic).
func newEmittedPoseidon2Perm(tpl *Template) func(frontend.API, *[bn254SpongeWidth]frontend.Variable) {
	return func(api frontend.API, state *[bn254SpongeWidth]frontend.Variable) {
		outs, err := ReplayTemplate(api, *tpl, state[:])
		if err != nil {
			panic(fmt.Sprintf("emitted poseidon2 permutation replay: %v", err))
		}
		if len(outs) != bn254SpongeWidth {
			panic(fmt.Sprintf("emitted poseidon2 permutation: got %d outputs, want %d",
				len(outs), bn254SpongeWidth))
		}
		copy(state[:], outs)
	}
}

// shrinkTranscriptInputs bundles the REAL-transcript circuit inputs a challenge
// re-derivation stage consumes, in the deployed SettlementCircuit / apexShrinkReal
// shape: the structural replay script + FRI config, and the witness streams
// (flattened prefix observe/digest values, the pinned prefix sample challenges,
// the commitment roots, the final polynomial, the query-PoW witness, and the
// per-query openings). All frontend.Variable content lives in slices/structs so a
// zero-valued bundle carries no witness (the stage is skippable).
type shrinkTranscriptInputs struct {
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int

	PrefixObs     []frontend.Variable
	PrefixDigests []frontend.Variable
	PrefixSamples []frontend.Variable
	CommitRoots   []frontend.Variable
	FinalPoly     []BBExt
	PowWitness    frontend.Variable
	Queries       []FriNativeQueryOpening
}

// shrinkTranscriptMeta is the STRUCTURAL half of the emitted-permutation
// transcript re-derivation stage (the replay script, FRI config, roll-in
// schedule, and the Lean-emitted permutation template) — everything that is not
// witness. It is attached to VerifierFullCircuit out-of-band so the gnark schema
// walker ignores it; a nil meta means the stage is OFF (the structural skeleton's
// default), so adding the stage does not perturb the existing descriptor circuit.
type shrinkTranscriptMeta struct {
	script           []shrinkPrefixOp
	cfg              FriConfig
	r                int
	rollInAfterRound []int
	tpl              *Template
}

// rederive runs the emitted-permutation transcript re-derivation: it builds a
// MultiField challenger whose permutation is the Lean-emitted template and
// replays the supplied witness streams (`in`, whose structural fields it fills
// from the meta), binding every consumed challenge to the transcript.
func (m *shrinkTranscriptMeta) rederive(bb *BBApi, in *shrinkTranscriptInputs) {
	in.script = m.script
	in.cfg = m.cfg
	in.r = m.r
	in.rollInAfterRound = m.rollInAfterRound
	ch := NewMultiFieldChallengerWithPerm(bb, newEmittedPoseidon2Perm(m.tpl))
	rederiveShrinkChallenges(bb, ch, in)
}

// rederiveShrinkChallenges replays the FULL real shrink transcript through the
// supplied MultiField challenger — whose permutation is the caller's choice,
// hand-Go or Lean-emitted — in the EXACT deployed observe/sample order
// (settlement_circuit.go:224-239 prefix + fri_verify_native.go VerifyFriNative):
//
//   - prefix: observe_bb / observe_digest stream absorbs, and every sample_bb
//     squeeze is asserted equal to its pinned value — this binds PermAlpha,
//     PermBeta, the constraint-folding alpha, zeta, and the FRI batch alpha (the
//     challenges block 3 / open_input consume);
//   - FRI: VerifyFriNative draws each per-round beta and each per-query index
//     LIVE from the same sponge and binds them by verifying the fold chain and
//     Merkle openings against the committed roots/paths (a wrong beta or index
//     fails the fold == finalEval / recomputed-root == root checks).
//
// A tampered commitment root, absorbed value, or pinned challenge moves the
// squeeze and makes the constraint system UNSATISFIABLE: the challenges are bound
// to the transcript, not supplied freely. This is the deployed transcript replay,
// factored so the emit-driven verifier can run it through the Lean-emitted
// permutation.
func rederiveShrinkChallenges(bb *BBApi, ch *MultiFieldChallenger, in *shrinkTranscriptInputs) {
	api := bb.API()
	io, id, is := 0, 0, 0
	for _, op := range in.script {
		switch op.kind {
		case "observe_bb":
			ch.ObserveBabyBearSlice(in.PrefixObs[io : io+op.n])
			io += op.n
		case "observe_digest":
			// One event = ONE native absorb call (its own length tag).
			ch.ObserveBn254Digest(in.PrefixDigests[id : id+op.n])
			id += op.n
		case "sample_bb":
			for k := 0; k < op.n; k++ {
				api.AssertIsEqual(ch.SampleBabyBear(), in.PrefixSamples[is])
				is++
			}
		}
	}
	VerifyFriNative(bb, in.cfg, in.r, in.CommitRoots, in.FinalPoly, in.PowWitness,
		in.Queries, in.rollInAfterRound, ch)
}

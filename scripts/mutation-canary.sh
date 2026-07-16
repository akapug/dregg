#!/usr/bin/env bash
# mutation-canary.sh — empirical load-bearing/decorative map for the supply/burn proofs.
#
# Mutates the burn IMPLEMENTATION (recKBurnAsset in Exec/TurnExecutorFull/PerAsset.lean and
# issuerBurnK in IssuerMove.lean), lake-builds the NARROW supply/burn refinement chain, and reports which targets
# go RED vs stay GREEN. Each mutation is applied, built, then REVERTED (git restore) so mutations
# are independent. Run from anywhere; paths are repo-relative.
#
# USAGE:
#   scripts/mutation-canary.sh                 # run the full matrix (baseline + all mutations)
#   scripts/mutation-canary.sh <MUTATION>      # AUTH-DROP|CONSERVATION-BREAK|AVAILABILITY-DROP|DISTINCTNESS-DROP|BASELINE
#
# REGRESSION-GATE INTENT: post-repair, AUTH-DROP MUST go RED (an unconstrained burn authority must
# be caught by some proof). If AUTH-DROP stays fully GREEN, the burn authority is empirically
# unconstrained == decorative.
#
# DO NOT git commit from this script; it only mutates + restores tracked files in place.
set -uo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
META="$REPO/metatheory"
IM="$META/Dregg2/Exec/IssuerMove.lean"
TE="$META/Dregg2/Exec/TurnExecutorFull.lean"
# `TurnExecutorFull.lean` was SPLIT (be85abd07, byte-identical): the per-asset burn impl
# (`recKBurnAsset`) and the `fullActionInvA` keystone moved HERE; `$TE` is now a re-export shell.
# Mutations anchored on that text MUST target `$PA` — see the `subst` guard below.
PA="$META/Dregg2/Exec/TurnExecutorFull/PerAsset.lean"
ER="$META/Dregg2/Spec/ExecRefinement.lean"
EA="$META/Dregg2/Exec/EffectsAuthority.lean"

TARGETS=(
  Dregg2.Exec.IssuerMove
  Dregg2.Exec.TurnExecutorFull
  Dregg2.Circuit.Spec.supplydestruction
  Dregg2.Spec.FunctionalRefinement
  Dregg2.Circuit.RotatedKernelRefinementMintBurn
  Dregg2.Circuit.Inst.burnA
)

LOGDIR="${TMPDIR:-/tmp}/mutation-canary"
mkdir -p "$LOGDIR"

# Restore via FILE-COPY snapshots (taken at startup), NOT `git restore` — so an UNCOMMITTED working
# tree (the normal state during a repair) is preserved across mutations. `git restore` would discard
# uncommitted edits to these tracked files (a swarm-/repair-unsafe operation).
SNAPDIR="${TMPDIR:-/tmp}/mutation-canary"
mkdir -p "$SNAPDIR"
cp "$IM" "$SNAPDIR/IssuerMove.snap"
cp "$TE" "$SNAPDIR/TurnExecutorFull.snap"
cp "$PA" "$SNAPDIR/PerAsset.snap"
cp "$ER" "$SNAPDIR/ExecRefinement.snap"
cp "$EA" "$SNAPDIR/EffectsAuthority.snap"
restore() {
  cp "$SNAPDIR/IssuerMove.snap" "$IM"
  cp "$SNAPDIR/TurnExecutorFull.snap" "$TE"
  cp "$SNAPDIR/PerAsset.snap" "$PA"
  cp "$SNAPDIR/ExecRefinement.snap" "$ER"
  cp "$SNAPDIR/EffectsAuthority.snap" "$EA"
}

build_targets() {
  local log="$1"
  ( cd "$META" && lake build "${TARGETS[@]}" ) >"$log" 2>&1
  local rc=$?
  if [[ $rc -eq 0 ]] && ! grep -qE '^error:|: error:' "$log"; then
    return 0
  fi
  return 1
}

attribute() {
  echo "    Per-target attribution (built individually):"
  for t in "${TARGETS[@]}"; do
    local tl="$LOGDIR/attr-$t.log"
    if ( cd "$META" && lake build "$t" ) >"$tl" 2>&1 && ! grep -qE '^error:|: error:' "$tl"; then
      echo "      GREEN  $t"
    else
      echo "      RED    $t"
      grep -E ': error:|^error:' "$tl" | head -3 | sed 's/^/             /'
    fi
  done
}

run_one() {
  local name="$1"; shift
  echo "=================================================================="
  echo "MUTATION: $name"
  local log="$LOGDIR/$name.log"
  "$@"
  if build_targets "$log"; then
    echo "  RESULT: GREEN  (combined build succeeded — mutation NOT caught)"
  else
    echo "  RESULT: RED    (combined build failed — mutation caught)"
    attribute
  fi
  restore
  echo ""
}

# ---- the ANTI-DRIFT guard (every mutation MUST route through `subst`) ----
#
# WHY THIS EXISTS: a mutation whose anchor has drifted matches NOTHING and is a SILENT NO-OP. The
# canary then builds UNMUTATED code, sees GREEN, and reports "should-RED stayed GREEN" — i.e. it
# blames the PROOF for the canary's own blindness. That is not hypothetical: the byte-identical
# split of TurnExecutorFull.lean (be85abd07) moved every burn/keystone anchor into PerAsset.lean,
# so each `$TE` mutation silently no-op'd and the nightly gate misreported "a load-bearing proof
# regressed to decorative" for 3 days. The proof was fine the whole time.
#
# `subst` converts that ENTIRE failure class from a silent, misattributed GREEN into a loud, correctly
# -named FATAL: it applies the perl substitution and hard-fails unless the file's bytes actually
# changed. A no-op mutation can no longer be mistaken for a live one. `trap restore EXIT` is armed
# before any mutation runs, so a FATAL still restores the tree from the file-copy snapshots.
subst() {
  local name="$1" file="$2" expr="$3"
  local before after
  before="$(shasum -a 256 "$file" | cut -d' ' -f1)"
  perl -0pi -e "$expr" "$file"
  after="$(shasum -a 256 "$file" | cut -d' ' -f1)"
  if [[ "$before" == "$after" ]]; then
    echo "" >&2
    echo "FATAL: ANCHOR DRIFT — mutation $name matched nothing in ${file#$REPO/}" >&2
    echo "       the canary is blind, not the proof." >&2
    echo "       A mutation that matches nothing is a SILENT NO-OP: it builds UNMUTATED code," >&2
    echo "       goes GREEN, and gets misreported as 'a load-bearing proof regressed to decorative'." >&2
    echo "       FIX THE CANARY, NOT THE PROOF: re-anchor '$name' in scripts/mutation-canary.sh" >&2
    echo "       against the CURRENT text of that file (it was refactored out from under us)." >&2
    exit 1
  fi
}

# ---- the mutations (one-line patches to the impl defs) ----

mut_baseline() { :; }

# AUTH-DROP: replace the burn authority condition with `True` in BOTH impl defs — anyone can burn.
# The gate is now the Stage-3 SPLIT disjunction `(actor = cell ∨ mintAuthorizedB k.caps actor a = true)`
# (permissionless holder self-redeem ∨ issuer authority). Dropping the WHOLE disjunction — not just the
# `mintAuthorizedB` disjunct — is the strongest form of the same idea: burn authority is unconstrained.
mut_auth_drop() {
  subst AUTH-DROP "$PA" 's/if \(actor = cell \xe2\x88\xa8 mintAuthorizedB k\.caps actor a = true\) \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal cell a/if True \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k.bal cell a/'
  subst AUTH-DROP "$IM" 's/if \(actor = src \xe2\x88\xa8 mintAuthorizedB k\.caps actor \(issuerOf a\) = true\) \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal src a/if True \xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k.bal src a/'
}

# CONSERVATION-BREAK: debit the holder but DON'T credit the well (recBalCredit -amt, not the
# conserving recTransferBal). This breaks Sigma=0.
mut_conservation_break() {
  subst CONSERVATION-BREAK "$PA" 's/some \{ k with bal := recTransferBal k\.bal cell a a amt \}/some { k with bal := recBalCredit k.bal cell a (-amt) }/'
  subst CONSERVATION-BREAK "$IM" 's/some \{ k with bal := recTransferBal k\.bal src \(issuerOf a\) a amt \}/some { k with bal := recBalCredit k.bal src a (-amt) }/'
}

# AVAILABILITY-DROP: drop the `amt <= k.bal cell a` (resp. src a) precondition (allow over-burn)
# from the LIVE burn def only. Anchored on the multi-line LIVE shape (the `… k.bal cell a\n  ∧ cell ∈`
# wrap) so the single-line LEGACY def at recKBurnAssetLegacy is NOT touched.
mut_availability_drop() {
  # NO /g: the FIRST match is the LIVE def (PerAsset.lean:117). The same multi-line shape recurs on
  # the downstream `by_cases hg` proof lines; rewriting those TOO would weaken the mutation (a def and
  # its by_cases mutated CONSISTENTLY can still close the proof, masking the bite). Mutate the def only.
  subst AVAILABILITY-DROP "$PA" 's/\xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal cell a\n      \xe2\x88\xa7 cell \xe2\x88\x88 k\.accounts \xe2\x88\xa7 a/\xe2\x88\xa7 0 \xe2\x89\xa4 amt\n      \xe2\x88\xa7 cell \xe2\x88\x88 k.accounts \xe2\x88\xa7 a/'
  subst AVAILABILITY-DROP "$IM" 's/\xe2\x88\xa7 0 \xe2\x89\xa4 amt \xe2\x88\xa7 amt \xe2\x89\xa4 k\.bal src a\n      \xe2\x88\xa7 src \xe2\x88\x88 k\.accounts/\xe2\x88\xa7 0 \xe2\x89\xa4 amt\n      \xe2\x88\xa7 src \xe2\x88\x88 k.accounts/'
}

# DISTINCTNESS-DROP: drop `cell != a` (resp. `src != issuerOf a`).
mut_distinctness_drop() {
  subst DISTINCTNESS-DROP "$PA" 's/\xe2\x88\xa7 cell \xe2\x89\xa0 a\n      \xe2\x88\xa7 cellLifecycleLive k a = true then/\xe2\x88\xa7 cellLifecycleLive k a = true then/'
  subst DISTINCTNESS-DROP "$IM" 's/\xe2\x88\xa7 src \xe2\x89\xa0 issuerOf a\n      \xe2\x88\xa7 cellLifecycleLive k \(issuerOf a\) = true then/\xe2\x88\xa7 cellLifecycleLive k (issuerOf a) = true then/'
}

# AUTH-GRAPH-DROP: trivialize the INDEPENDENT authority-connectivity spec `authConnects`
# (`ExecRefinement.lean`) to `True` — i.e. drop the "holds a `c.target`-conferring cap" requirement
# the C-c1 authority-graph legs attest. Post-repair this MUST go RED: the non-vacuity tooth
# (`authConnects_nonvacuous`, which REFUTES an empty-slot connection) and the separation witness
# (`capLookup_refines_authConnects_separates`) cannot be proved against a `True` spec, so the
# severed authority-graph leg is empirically load-bearing, not decorative. If it stays GREEN, the
# `execGraph`-defeq sever did not produce a constraining reference.
mut_auth_graph_drop() {
  subst AUTH-GRAPH-DROP "$ER" 's/(def authConnects \(caps : Caps\) \(h : Label\) \(c : Spec\.Cap Label ExecRights\) : Prop :=\n)  \xe2\x88\x83 cap, cap \xe2\x88\x88 caps h \xe2\x88\xa7 authConnectsCap c\.target cap/${1}  True  -- AUTH-GRAPH-DROP mutation/'
}

# LEDGER-SPEC-DROP: trivialize the per-action ATTESTATION CONTENT of `fullActionInvA` by replacing its
# ObsAdvance conjunct (`s.log.length < s'.log.length`) with `True`. This is the value/ledger-side
# attestation the C-c1 keystones (`fullActionInvA` / `gatedActionInvG`) carry. Post-repair this MUST go
# RED: the `@[load_bearing]` non-vacuity witnesses (`fullActionInvA_nonvacuous` /
# `gatedActionInvG_nonvacuous`) REFUTE a same-state instance THROUGH that ObsAdvance conjunct, so a
# trivialized conjunct makes the witnesses unprovable and the (now-throwing) `#load_bearing_audit`
# verdict on those two specs FAILS — confirming the retargeted value leg is load-bearing, not decorative.
# If it stays GREEN, the `fullActionInvA` attestation content is empirically vacuous.
mut_ledger_spec_drop() {
  subst LEDGER-SPEC-DROP "$PA" "s/\\(s\\.log\\.length < s'\\.log\\.length\\) \\xe2\\x88\\xa7/(True) \\xe2\\x88\\xa7  -- LEDGER-SPEC-DROP mutation/"
}

# NONAMP-WEAKEN: trivialize the AUTHORITY non-amplification predicate `IsNonAmplifying` (the headline of
# guarantee A) toward `True` — i.e. drop the `granted ⊆ held` attenuation check that "amplification
# denied" rests on. Post-repair this MUST go RED: the `*_teeth` keystone-audit witnesses
# (`{introduce,attenuate,refresh}_non_amplifying_teeth`, all `¬ IsNonAmplifying heldRW grantAmp`) become
# `¬ True` and are UNPROVABLE, so the 8 `*_non_amplifying` keystones lose their discriminating tooth and
# `#keystone_audit_tagged` (in Dregg2.Verify.KeystoneAuditNonAmp) FAILS. If it stays GREEN, the
# non-amplification predicate is empirically vacuous (`:= True`) and the authority claim is decorative.
# Anchored on the `def IsNonAmplifying … : Prop :=\n  capAuthConferred granted ⊆ capAuthConferred held`
# body (EffectsAuthority.lean), leaving the signature intact.
mut_nonamp_weaken() {
  subst NONAMP-WEAKEN "$EA" 's/(def IsNonAmplifying \(held granted : ECap\) : Prop :=\n)  capAuthConferred granted \xe2\x8a\x86 capAuthConferred held/${1}  True  -- NONAMP-WEAKEN mutation/'
}

trap restore EXIT

# The AUTH-GRAPH-DROP mutation is caught by the load-bearing audit's non-vacuity tooth, which lives
# downstream of ExecRefinement — so that mutation also builds the audit module.
AUTH_GRAPH_TARGETS=(
  Dregg2.Spec.ExecRefinement
  Dregg2.Exec.AuthTurn
  Dregg2.Verify.LoadBearingAuditBroad
)

build_auth_graph() {
  local log="$1"
  ( cd "$META" && lake build "${AUTH_GRAPH_TARGETS[@]}" ) >"$log" 2>&1
  local rc=$?
  if [[ $rc -eq 0 ]] && ! grep -qE '^error:|: error:' "$log"; then return 0; fi
  return 1
}

# LEDGER-SPEC-DROP is caught by the throwing `#load_bearing_audit` (non-vacuity tooth) in the broad
# audit module, downstream of the mutated `fullActionInvA`.
LEDGER_SPEC_TARGETS=(
  Dregg2.Exec.TurnExecutorFull
  Dregg2.Exec.GatedForestCfg
  Dregg2.Verify.LoadBearingAuditBroad
)

build_ledger_spec() {
  local log="$1"
  ( cd "$META" && lake build "${LEDGER_SPEC_TARGETS[@]}" ) >"$log" 2>&1
  local rc=$?
  if [[ $rc -eq 0 ]] && ! grep -qE '^error:|: error:' "$log"; then return 0; fi
  return 1
}

run_ledger_spec() {
  echo "=================================================================="
  echo "MUTATION: LEDGER-SPEC-DROP"
  local log="$LOGDIR/LEDGER-SPEC-DROP.log"
  mut_ledger_spec_drop
  if build_ledger_spec "$log"; then
    echo "  RESULT: GREEN  (mutation NOT caught — fullActionInvA attestation is decorative!)"
  else
    echo "  RESULT: RED    (mutation caught — fullActionInvA value leg is load-bearing)"
    grep -E ': error:|^error:' "$log" | head -3 | sed 's/^/             /'
  fi
  restore  # FILE-COPY snapshot restore (preserves the uncommitted tree)
  echo ""
}

# NONAMP-WEAKEN is caught by the keystone-audit (the `*_teeth` non-vacuity witnesses + the throwing
# `#keystone_audit_tagged`) over the 8 `*_non_amplifying` keystones, in KeystoneAuditNonAmp.
NONAMP_TARGETS=(
  Dregg2.Exec.EffectsAuthority
  Dregg2.Verify.KeystoneAuditNonAmp
)

build_nonamp() {
  local log="$1"
  ( cd "$META" && lake build "${NONAMP_TARGETS[@]}" ) >"$log" 2>&1
  local rc=$?
  if [[ $rc -eq 0 ]] && ! grep -qE '^error:|: error:' "$log"; then return 0; fi
  return 1
}

run_nonamp() {
  echo "=================================================================="
  echo "MUTATION: NONAMP-WEAKEN"
  local log="$LOGDIR/NONAMP-WEAKEN.log"
  mut_nonamp_weaken
  if build_nonamp "$log"; then
    echo "  RESULT: GREEN  (mutation NOT caught — IsNonAmplifying is decorative (:= True)!)"
  else
    echo "  RESULT: RED    (mutation caught — the non-amplification keystones are load-bearing)"
    grep -E ': error:|^error:' "$log" | head -3 | sed 's/^/             /'
  fi
  restore  # FILE-COPY snapshot restore (preserves the uncommitted tree)
  echo ""
}

run_auth_graph() {
  echo "=================================================================="
  echo "MUTATION: AUTH-GRAPH-DROP"
  local log="$LOGDIR/AUTH-GRAPH-DROP.log"
  mut_auth_graph_drop
  if build_auth_graph "$log"; then
    echo "  RESULT: GREEN  (mutation NOT caught — authConnects leg is decorative!)"
  else
    echo "  RESULT: RED    (mutation caught — authConnects leg is load-bearing)"
    grep -E ': error:|^error:' "$log" | head -3 | sed 's/^/             /'
  fi
  restore  # FILE-COPY snapshot restore (preserves the uncommitted tree)
  echo ""
}

# GATE: the CI regression gate (nightly). Builds the C-c1 keystone modules UNMUTATED (baseline must
# be GREEN), then applies the two HEAD-targeting proof-integrity mutations and requires BOTH to go
# RED. A should-RED-stays-GREEN means a load-bearing proof (the C-c1 authority leg `authConnects` or
# the value leg `fullActionInvA`) regressed to decorative — exits nonzero.
#
# NOTE: a should-RED-stays-GREEN can no longer be caused by a drifted anchor — `subst` FATALs on a
# no-op mutation before any build runs, so a GREEN here is a real verdict about the proof, not the
# canary silently patching text that moved. (The legacy supply mutations AUTH-DROP/CONSERVATION-BREAK/…
# are re-anchored on HEAD and run under `ALL`; whether to add them to this gate is a separate call.)
run_gate() {
  local fail=0
  echo "=================================================================="
  echo "MUTATION GATE — C-c1 keystone falsifiability (nightly)"
  if build_auth_graph "$LOGDIR/gate-base-ag.log" && build_ledger_spec "$LOGDIR/gate-base-ls.log"; then
    echo "  BASELINE: GREEN ✓ (the C-c1 modules build unmutated)"
  else
    echo "  ⛔ BASELINE: RED — a pre-existing break; the gate cannot run. See $LOGDIR/gate-base-*.log"
    fail=1
  fi
  restore
  mut_auth_graph_drop
  if build_auth_graph "$LOGDIR/gate-AUTH-GRAPH-DROP.log"; then
    echo "  ⛔ AUTH-GRAPH-DROP: GREEN — the authConnects authority leg regressed to DECORATIVE"
    fail=1
  else
    echo "  AUTH-GRAPH-DROP: RED ✓ (authConnects authority leg is load-bearing)"
  fi
  restore
  mut_ledger_spec_drop
  if build_ledger_spec "$LOGDIR/gate-LEDGER-SPEC-DROP.log"; then
    echo "  ⛔ LEDGER-SPEC-DROP: GREEN — the fullActionInvA value leg regressed to DECORATIVE"
    fail=1
  else
    echo "  LEDGER-SPEC-DROP: RED ✓ (fullActionInvA value leg is load-bearing)"
  fi
  restore
  # NONAMP baseline (the keystone-audit family must build unmutated) then the weaken tooth.
  if build_nonamp "$LOGDIR/gate-base-nonamp.log"; then
    echo "  BASELINE(non-amp): GREEN ✓ (the KeystoneAuditNonAmp family builds unmutated)"
  else
    echo "  ⛔ BASELINE(non-amp): RED — a pre-existing break; see $LOGDIR/gate-base-nonamp.log"
    fail=1
  fi
  restore
  mut_nonamp_weaken
  if build_nonamp "$LOGDIR/gate-NONAMP-WEAKEN.log"; then
    echo "  ⛔ NONAMP-WEAKEN: GREEN — the non-amplification keystones regressed to DECORATIVE (:= True)"
    fail=1
  else
    echo "  NONAMP-WEAKEN: RED ✓ (the *_non_amplifying keystones are load-bearing)"
  fi
  restore
  echo "=================================================================="
  if [[ $fail -eq 0 ]]; then
    echo "MUTATION GATE: PASS (C-c1 keystones load-bearing; baseline green)"
  else
    echo "MUTATION GATE: FAIL (a load-bearing proof regressed to decorative — see ⛔ above)"
    exit 1
  fi
}

case "${1:-ALL}" in
  GATE)                run_gate ;;
  BASELINE)            run_one BASELINE            mut_baseline ;;
  AUTH-DROP)           run_one AUTH-DROP           mut_auth_drop ;;
  AUTH-GRAPH-DROP)     run_auth_graph ;;
  LEDGER-SPEC-DROP)    run_ledger_spec ;;
  NONAMP-WEAKEN)       run_nonamp ;;
  CONSERVATION-BREAK)  run_one CONSERVATION-BREAK  mut_conservation_break ;;
  AVAILABILITY-DROP)   run_one AVAILABILITY-DROP   mut_availability_drop ;;
  DISTINCTNESS-DROP)   run_one DISTINCTNESS-DROP   mut_distinctness_drop ;;
  ALL)
    run_one BASELINE            mut_baseline
    run_one AUTH-DROP           mut_auth_drop
    run_auth_graph
    run_ledger_spec
    run_nonamp
    run_one CONSERVATION-BREAK  mut_conservation_break
    run_one AVAILABILITY-DROP   mut_availability_drop
    run_one DISTINCTNESS-DROP   mut_distinctness_drop
    ;;
  *) echo "unknown mutation: $1"; exit 2 ;;
esac

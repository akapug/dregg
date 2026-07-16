#!/usr/bin/env bash
# check-p3-rev.sh -- enforce that every hardcoded emberian/plonky3-recursion
# fork rev in the repo matches the single source of truth, scripts/p3-rev.env.
#
# The fork rev resolves the whole workspace's recursion crates and thus the
# compiled verifier. It is pinned in the AUTHORITATIVE workspace deps (root
# Cargo.toml [workspace.dependencies] p3-recursion/p3-circuit/...) and mirrored
# into several CI workflows (sibling-clone REV) and wasm/Cargo.toml's comment.
# All of these MUST stay in lockstep or the built verifier forks silently.
#
# Scoping: root Cargo.toml ALSO pins base upstream Plonky3/Plonky3 at a different
# 40-hex rev, so its p3-recursion rev is isolated by matching only
# `plonky3-recursion` lines (never a blind grep of the whole file). For the CI
# workflows + wasm/Cargo.toml the only 40-hex tokens present are the fork rev.
#
# NOT enforced here (reported as a WARNING, see below): the VK-hash constant
# RECURSION_P3_REV in circuit-prove/src/recursive_witness_bundle.rs. It is a
# proving-system identifier folded into the deployed recursive VK hash, so
# changing it re-keys the VK -- a VK-epoch event on a different governance track
# than a lockstep gate. This script SURFACES a drift there but does not fail on
# it, because the fix is deliberately human-gated.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
env_file="$repo_root/scripts/p3-rev.env"

if [[ ! -f "$env_file" ]]; then
  echo "FAIL: single-source env missing: $env_file" >&2
  exit 1
fi
# shellcheck source=/dev/null
. "$env_file"

if [[ ! "${P3_REV:-}" =~ ^[0-9a-f]{40}$ ]]; then
  echo "FAIL: P3_REV in $env_file is not a 40-hex rev: '${P3_REV:-<unset>}'" >&2
  exit 1
fi

status=0

# --- Consumers whose ONLY 40-hex tokens are the fork rev: grep the whole file.
blind_files=(
  ".github/workflows/extension.yml"
  ".github/workflows/publish-sdk-ts.yml"
  ".github/workflows/pages.yml"
  "wasm/Cargo.toml"
)
for rel in "${blind_files[@]}"; do
  f="$repo_root/$rel"
  if [[ ! -f "$f" ]]; then
    echo "FAIL: consumer file missing: $rel" >&2
    status=1
    continue
  fi
  while IFS= read -r rev; do
    [[ -z "$rev" ]] && continue
    if [[ "$rev" != "$P3_REV" ]]; then
      echo "FAIL: $rel pins plonky3 rev $rev, expected $P3_REV" >&2
      status=1
    fi
  done < <(grep -ioE '[0-9a-f]{40}' "$f" | sort -u)
done

# --- Authoritative workspace pin: isolate the plonky3-recursion rev only
# (base Plonky3/Plonky3 is legitimately a different rev in the same file).
cargo="$repo_root/Cargo.toml"
if [[ ! -f "$cargo" ]]; then
  echo "FAIL: root Cargo.toml missing" >&2
  status=1
else
  while IFS= read -r rev; do
    [[ -z "$rev" ]] && continue
    if [[ "$rev" != "$P3_REV" ]]; then
      echo "FAIL: root Cargo.toml pins plonky3-recursion rev $rev, expected $P3_REV" >&2
      status=1
    fi
  done < <(grep 'plonky3-recursion' "$cargo" | grep -ioE '[0-9a-f]{40}' | sort -u)
fi

# --- WARN-only: the VK-hash constant (VK-epoch-gated, not a lockstep failure).
vk="$repo_root/circuit-prove/src/recursive_witness_bundle.rs"
if [[ -f "$vk" ]]; then
  vk_rev="$(grep 'RECURSION_P3_REV' "$vk" | grep -ioE '[0-9a-f]{40}' | head -1 || true)"
  if [[ -n "$vk_rev" && "$vk_rev" != "$P3_REV" ]]; then
    echo "WARN: RECURSION_P3_REV in recursive_witness_bundle.rs is $vk_rev, not $P3_REV" >&2
    echo "WARN:   this drifts the deployed VK-hash proving-system id from the actual" >&2
    echo "WARN:   fork rev. Fixing it re-keys the VK (a VK-epoch event) -- human-gated." >&2
  fi
fi

if [[ "$status" -eq 0 ]]; then
  echo "OK: all lockstep plonky3-recursion revs match P3_REV=$P3_REV"
fi
exit "$status"

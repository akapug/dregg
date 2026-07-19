#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "$0")/../.." && pwd)"
lean_dir="$repo_dir/metatheory"
artifact="$repo_dir/circuit/descriptors/dregg-cert-qp-portfolio6-s3-ir2.json"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

(cd "$lean_dir" && lake build Market.CertQpDescriptor >/dev/null)
(cd "$lean_dir" && lake env lean --run EmitCertQpDescriptor.lean >"$tmp")

if [[ "${1:-}" == "--check" ]]; then
  diff -u "$artifact" "$tmp"
  echo "regen --check: PASS — Lean CertQp emission matches the committed descriptor."
else
  cp "$tmp" "$artifact"
  echo "regenerated $artifact from Lean."
fi

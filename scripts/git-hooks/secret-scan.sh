#!/usr/bin/env sh
# secret-scan.sh — the shared secret-scanning engine behind the pre-commit + pre-push hooks.
#
# Today's incident was PROCESS: staging content sat on `main`, a routine `git push origin main`
# carried a secret public. This is the backstop that makes that unrepeatable — a real secret in a
# STAGED diff (pre-commit) or in a TO-BE-PUSHED commit (pre-push) BLOCKS the operation with a clear
# message. Known offline test fixtures + placeholders are allowlisted (.gitleaks.toml / the grep
# ignore list below) so it bites on real secrets without crying wolf.
#
# Prefers `gitleaks` (a real, maintained scanner) when on PATH; otherwise falls back to a POSIX-grep
# scan with the same real-secret shapes + allowlist, so the guardrail is NEVER vacuous.
#
# Usage:
#   secret-scan.sh staged                 # scan the staged diff  (pre-commit)
#   secret-scan.sh range <base> <tip>     # scan commits base..tip (pre-push, explicit)
#   secret-scan.sh push-stdin             # read pre-push ref updates on stdin, scan each range
#
# Exit: 0 = clean, 1 = a secret was found (block), 0 = nothing to scan.
set -u

mode="${1:-staged}"
repo_root="$(git rev-parse --show-toplevel 2>/dev/null)" || exit 0
config="$repo_root/.gitleaks.toml"

# ---- allowlist / placeholder regexes (used by the grep fallback; gitleaks reads .gitleaks.toml) ----
# Lines matching this are IGNORED even if a secret shape appears (known fixtures + placeholders).
ALLOW_RE='whsec_(demo|test|attacker_guess)|sk_live_secret|[Xx]{3,}|<[^>]*>|REDACTED|PLACEHOLDER|[Cc]hange[-_]?[Mm]e|[Ee]xample|[Dd]ummy|[Ss]ample|[Yy]our[-_]|[Ff]ake|\$\{'

# Real-secret shapes (ERE). Kept in lockstep with .gitleaks.toml's rules.
# NOTE: private-key alt uses an OPTIONAL group `(RSA |EC |OPENSSH )?` — NOT `(RSA |EC |OPENSSH |)` —
# because BSD/macOS grep rejects an empty alternation branch ("empty (sub)expression"). Same match set.
SECRET_RE='whsec_[A-Za-z0-9]{16,}|sk_(live|test)_[A-Za-z0-9]{16,}|(pk|rk)_(live|test)_[A-Za-z0-9]{16,}|(AKIA|ASIA)[0-9A-Z]{16}|-----BEGIN (RSA |EC |OPENSSH )?PRIVATE KEY-----|ghp_[A-Za-z0-9]{36}|github_pat_[A-Za-z0-9_]{20,}|xox[baprs]-[A-Za-z0-9-]{10,}'
# Secret-looking assignment (needs the placeholder allowlist to avoid noise).
ASSIGN_RE='(PASSWORD|SECRET|TOKEN|API_?KEY|ADMIN_PASSWORD)[[:space:]]*[:=][[:space:]]*["'"'"']?[A-Za-z0-9+/]{20,}'

block_msg() {
  printf '\n\033[31m╳ secret-scan: BLOCKED — a possible real secret was found.\033[0m\n' >&2
  printf '  A credential shape (stripe/aws/github/slack/private-key/high-entropy) appears above.\n' >&2
  printf '  This backstop stops a secret from being committed/pushed public (see docs/PUBLISHING-SAFETY.md).\n' >&2
  printf '  If it is a genuine offline TEST FIXTURE, add it to the .gitleaks.toml allowlist.\n' >&2
  printf '  To bypass in a true emergency (discouraged): git commit --no-verify / git push --no-verify\n\n' >&2
}

# True iff $1 is a base we can actually scan FROM. Guards the two ways this hook used to explode on a
# live, multi-terminal repo — both reported as mystery errors on an ordinary `git push`:
#
#   * "fatal: '..' is outside repository" — an EMPTY base/tip. `git` feeds no ref lines when there is
#     nothing to push, and pre-push's `printf '%s\n' "$stdin_data"` turns empty stdin into a LONE
#     NEWLINE, so `read` yields four empty vars. Empty does not match the `^0+$` all-zeros sentinel,
#     so the old code sailed past every guard into `git diff "$remote_oid..$local_oid"` = `git diff
#     ".."` — which git parses as a PATHSPEC, not a range. Hence the nonsense message.
#   * "not a valid commit range" — a base the LOCAL clone does not have. `remote_oid` is what the
#     REMOTE holds; on this repo several terminals rebase and force-push the shared branch, so the
#     oid git hands the hook is routinely an object we never fetched. `<unknown>..<tip>` then dies.
#
# In both cases the correct fallback is the new-branch form (`<tip> --not --remotes`): scan what is
# genuinely new locally. Fail OPEN on scanning scope, never fail closed on a bad range — the point is
# to scan the pushed commits, not to block a push because we could not name them.
usable_base() {
  [ -n "${1:-}" ] || return 1
  printf '%s' "$1" | grep -qE '^0+$' && return 1
  git cat-file -e "${1}^{commit}" 2>/dev/null
}

# ---------------------------------------------------------------------------------------------------
# gitleaks path
# ---------------------------------------------------------------------------------------------------
if command -v gitleaks >/dev/null 2>&1; then
  gl() { gitleaks "$@" --no-banner --redact -c "$config" "$repo_root"; }
  case "$mode" in
    staged)
      gl git --staged || { block_msg; exit 1; } ;;
    range)
      base="${2:-}"; tip="${3:-}"
      [ -n "$tip" ] || exit 0
      if usable_base "$base"; then opts="$base..$tip"; else opts="$tip --not --remotes"; fi
      gl git --log-opts="$opts" || { block_msg; exit 1; } ;;
    push-stdin)
      rc=0
      while read -r local_ref local_oid remote_ref remote_oid; do
        # Skip blank/short lines (see usable_base) and branch deletions (all-zero local oid).
        [ -n "${local_oid:-}" ] || continue
        printf '%s' "$local_oid" | grep -qE '^0+$' && continue
        if usable_base "${remote_oid:-}"; then
          opts="$remote_oid..$local_oid"
        else
          opts="$local_oid --not --remotes"
        fi
        gl git --log-opts="$opts" || rc=1
      done
      [ "$rc" -eq 0 ] || { block_msg; exit 1; } ;;
    *)
      echo "secret-scan: unknown mode '$mode'" >&2; exit 0 ;;
  esac
  exit 0
fi

# ---------------------------------------------------------------------------------------------------
# grep fallback (gitleaks not installed) — scans ADDED lines only; applies the same allowlist
# ---------------------------------------------------------------------------------------------------
emit_hits() {
  # $1 = diff text (already added-only+stripped). Print offending lines; return 0 if any hit.
  hits="$(printf '%s\n' "$1" | grep -vE "$ALLOW_RE" | grep -En "$SECRET_RE" || true)"
  assign="$(printf '%s\n' "$1" | grep -vE "$ALLOW_RE" | grep -En "$ASSIGN_RE" || true)"
  found=0
  if [ -n "$hits" ];   then printf '%s\n' "$hits"   >&2; found=1; fi
  if [ -n "$assign" ]; then printf '%s\n' "$assign" >&2; found=1; fi
  return $found  # 0 = no hit
}

added_lines() { grep -E '^\+' | grep -vE '^\+\+\+' | sed 's/^\+//'; }

case "$mode" in
  staged)
    diff_text="$(git diff --cached -U0 --diff-filter=ACM | added_lines)"
    emit_hits "$diff_text" && exit 0 || { block_msg; exit 1; } ;;
  range)
    base="${2:-}"; tip="${3:-}"; [ -n "$tip" ] || exit 0
    if usable_base "$base"; then
      diff_text="$(git diff "$base..$tip" | added_lines)"
    else
      diff_text="$(git log -p "$tip" --not --remotes | added_lines)"
    fi
    emit_hits "$diff_text" && exit 0 || { block_msg; exit 1; } ;;
  push-stdin)
    rc=0
    while read -r local_ref local_oid remote_ref remote_oid; do
      # Skip blank/short lines (see usable_base) and branch deletions.
      [ -n "${local_oid:-}" ] || continue
      printf '%s' "$local_oid" | grep -qE '^0+$' && continue
      if usable_base "${remote_oid:-}"; then
        diff_text="$(git diff "$remote_oid..$local_oid" | added_lines)"
      else
        diff_text="$(git log -p "$local_oid" --not --remotes | added_lines)"
      fi
      emit_hits "$diff_text" || rc=1
    done
    [ "$rc" -eq 0 ] && exit 0 || { block_msg; exit 1; } ;;
  *)
    echo "secret-scan: unknown mode '$mode'" >&2; exit 0 ;;
esac

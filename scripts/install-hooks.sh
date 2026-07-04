#!/usr/bin/env bash
# Install this repo's tracked git hooks into .git/hooks — WITHOUT touching core.hooksPath (git-lfs
# sets it and owns the post-*/pre-push hooks there; we only ADD a pre-commit alongside them).
# Symlinks (not copies) so edits to scripts/git-hooks/* take effect immediately. Idempotent.
# Run once after cloning: `bash scripts/install-hooks.sh`.
set -euo pipefail
repo_root="$(git rev-parse --show-toplevel)"
src="$repo_root/scripts/git-hooks"
dst="$repo_root/.git/hooks"
mkdir -p "$dst"
for hook in "$src"/*; do
  [ -f "$hook" ] || continue
  name="$(basename "$hook")"
  chmod +x "$hook"
  # relative symlink from .git/hooks/<name> → ../../scripts/git-hooks/<name> (moves with the repo)
  ln -sf "../../scripts/git-hooks/$name" "$dst/$name"
  echo "installed hook: .git/hooks/$name -> scripts/git-hooks/$name"
done
echo "done. (git-lfs's hooks left intact; core.hooksPath unchanged)"

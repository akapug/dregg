# Remote setup — pushing the private DreggNet working repo

The DreggNet product is open source (AGPL-3.0) — its clean snapshot is published
publicly. This runbook is about the **private working repo** (`emberian/DreggNet`),
which is kept private because it retains full git history, live-infra config, and
the retained third-party Elide sources (under `docs/engine/oracle/`) that are not
redistributable — not because the product is closed. All commits to date are local
(there is no remote yet); the steps below create the private remote and push.

This is **ember's action to run** — it touches ember's GitHub account and is a
publish step. The steps below are not executed by CI or by an agent.

## Prerequisites

- `gh` CLI authenticated as `emberian` (`gh auth status`).
- The working tree clean and on the branch you intend to publish.
- Compute is owned and in-crate (the `Sandboxed` wasm tier runs on a vendored
  pure-Rust `wasmi` interpreter) — there is **no external compute submodule** to
  clone and no cross-org deploy key or PAT to arrange. CI builds the workspace
  directly.

## 1. Create the private repo

Create it empty (no remote content), private:

```sh
gh repo create emberian/DreggNet --private \
  --description "DreggNet — the metered federated serving substrate" \
  --disable-wiki
```

`gh repo create` without `--source`/`--push` just creates the empty GitHub repo;
it does not add a remote or push. Keep it that way so the push below is explicit.

## 2. Add the remote

```sh
cd ~/dev/DreggNet
git remote add origin git@github.com:emberian/DreggNet.git
git remote -v   # confirm origin → emberian/DreggNet
```

## 3. Push the branches

Publish `dev` (the working branch) and `main`:

```sh
# dev — the active branch.
git push -u origin dev

# main — if it exists locally.
git push -u origin main
```

Push tags too if any exist:

```sh
git push origin --tags
```

## 4. Post-push hygiene

- Set the default branch in the GitHub repo settings (`main` or `dev`, your call).
- Confirm the repo is **Private** (Settings → General → Danger Zone shows it).
- Confirm CI ran: the `CI` workflow triggers on push to `dev`/`main` and on PRs
  (see `.github/workflows/ci.yml`). Compute is in-crate, so there is no submodule
  clone step that could fail for want of a credential.
- Confirm no secrets leaked into history — `.gitignore` excludes `target/`,
  `.env*`, `secrets/`, key material (`*.pem`/`*.key`/`*.p12`), and
  `credentials.json`. The repo is private regardless, but keep credentials out.

## What stays local

This working repo is not published publicly — its history, infra config, and the
retained Elide `docs/engine/oracle/` sources stay private. The DreggNet product
itself is open (AGPL-3.0), published as a clean public snapshot; the moat is the
live network, the multi-operator federation, and the verifiable proofs — not
secret code. Do not add a public mirror of *this* working tree.

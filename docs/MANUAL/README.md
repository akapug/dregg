# The dregg / deos manual — start here

This is the trail guide for a person who is *not* the author, sitting down to
**use deos** or **build on dregg** for the first time. It is a living document:
the stable spine is filled in; the parts that are still settling are marked
**[in flux]** so the manual never lies about what runs today.

The manual is the trail guide. **The map is the territory:** the interactive
[**ATLAS**](../../dregg-atlas/site/index.html) — open it in a browser — is the
crawled, code-grounded map of every surface, the object-capability web, the game
tree, and the protocol. When you want to *explore the whole system*, go there.

## The names (so the rest reads cleanly)

- **robigalia** — the whole project / the stack.
- **dregg** — the kernel: a formally-verified (Lean 4) distributed
  object-capability OS. The Lean executor *is* the function the node runs.
- **deos** — the desktop userlayer you inhabit. *deos runs on dregg runs in
  robigalia.* deos adds **zero new trust**: every window is a capability, every
  interaction is a verified turn.

## The one sentence

> A turn is the exercise of an attenuable, proof-carrying token over owned
> state, leaving a verifiable receipt.

A *capability* is **constructive knowledge**: to hold one is to be able to
exhibit a witness that verifies, never merely to assert. Your boundaries are
theorems, not permissions.

## Two doors

| You are… | Go to |
|---|---|
| Sitting down to **use** deos — click around, author cards, share a world | [USER.md](USER.md) |
| **Building** on dregg — write a card, host a server, embed the kernel | [DEVELOPER.md](DEVELOPER.md) |

## Where this manual sits among the docs

- This manual = the **start-here trail guide** (orientation + first paths).
- [`../../README.md`](../../README.md) = the human-facing tour + the five
  guarantees + the first-five-minutes commands.
- [`../../README-LLMs.md`](../../README-LLMs.md) = the dense machine-facing
  reference.
- [`../../metatheory/CLAIMS.md`](../../metatheory/CLAIMS.md) = exactly what is
  proven, what is assumed, and the honest open seams (build-enforced via
  `Dregg2/Claims.lean`).
- [`../KERNEL.md`](../KERNEL.md) = the substrate design (four substances, the
  verbs, the verified kernel).
- [`HYPERDREGGMEDIA.md`](../deos/HYPERDREGGMEDIA.md) = the charter for the inhabited
  world.
- [`DEOS.md`](../deos/DEOS.md) · [`COCKPIT-UX.md`](../deos/COCKPIT-UX.md) = the desktop brand and
  the cockpit's frame.

> **Honesty note.** This is research software under active development. No
> independent audit has happened. **Do not use it for anything
> security-critical.** The crypto floor it stands on is *assumed*, not
> discharged; the honest open seams are enumerated in
> [`../../metatheory/CLAIMS.md`](../../metatheory/CLAIMS.md) (the honesty
> labels + § OPEN).

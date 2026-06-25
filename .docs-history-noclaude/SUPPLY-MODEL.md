# The dregg supply model — per-asset wells + capability-gated mint/burn

## Why

Two holes hid under "burn": **conservation** (a well-less asset's burn is a
non-conserving `Σδ≠0` destroy) and **authority** (the verified Lean kernel gates burn on
`mintAuthorizedB`/issuer-authority; the Rust kernel lets any holder self-destruct with no
check). They diverge because "burn" conflates two genuinely different operations. The
coherent model separates them, and both holes close as a consequence.

This is the **AssetId := issuer-cell Σδ=0** unification from the dregg3 campaign, made real:
the asset *is* its issuer, supply is conserved against a per-asset well, and the
create/destroy of supply is **capability-gated** — i.e. it lives in dregg's own authority
algebra rather than in special-case kernel arms.

## The model

### Invariant (per asset, always)
**`Σ(all holders) + well = 0`.** The well's balance is the negative of circulating supply
(negative-capable). Every supply operation preserves this; it is the `Σδ=0` conservation
guarantee taken to the supply layer (not just intra-turn moves).

### The well
Each asset has exactly one **well** cell — a real signed supply account, NOT a "sink." It
is created when the asset is issued (its mint-cap is established) and is resolved
deterministically from the asset (`AssetId := issuer`; the well is the issuer-cell's supply
ledger for that asset). The genesis default-asset well (`node/src/genesis.rs:218`, balance
`−total_issued`) is the existing instance of exactly this — generalized to every asset.

### Supply operations are capability-gated (the unifying move)
Authority over supply is a **capability**, not a hardcoded kernel check — so the model is a
*policy space*, not a fixed semantics:

| op | move | authority | conserves |
|---|---|---|---|
| **Mint** | well → holder (well more negative) | a **mint-cap** over the asset (issuer authority; "a cell cannot coin its own supply" = no mint-cap, no minting) | ✓ |
| **Burn / self-redeem** | holder → well (well toward 0, supply ↓) | the **holder** (reducing your *own* balance needs no issuer auth — it's your value and can only *shrink* supply); optionally an issuer **burn-policy cap** if the asset wants gated destruction | ✓ |
| **Issuer-burn** (destroy others' / well supply) | → well | a burn/supply cap | ✓ |

**Mint and burn are duals with asymmetric authority**: creating value is privileged
(mint-cap); destroying *your own* value is permissionless-by-default. Lean's
`mintAuthorizedB`-on-burn was over-strict — it gated the holder's own redemption on issuer
authority, conflating the two.

### How it subsumes both worlds (and extends)
- **Lean's issuer-move burn** = the asset whose policy grants the burn-cap only to the issuer.
- **Rust's holder self-burn** = self-redemption, permissionless in this model.
- **Extension**: per-asset policy via caps — the issuer can make burns cap-gated or
  permissionless, grant/revoke mint-caps, delegate issuance. All in the existing capability
  layer.

### The "no issuer concept" gap dissolves
Rust today has no `Effect::Mint`; value enters implicitly (genesis / `BridgeMint` /
`CreateCell`-at-balance-0) — which is the deeper hole *under* the burn one ("where does
supply come from?" is unauthored). In this model **the issuer of an asset is whoever holds
its mint-cap** (origin: genesis or asset-creation), and supply enters *only* through a
first-class cap-gated **Mint**. The opaque-`token_id` problem goes away: the asset's
authority *is* its mint-cap lineage.

## Decisions (ratified)
- **Self-burn default: permissionless self-redeem**, with an optional per-asset issuer
  burn-policy cap. Supports both holder-redeem and issuer-controlled destruction.
- **Mint is a first-class `Effect::Mint`, cap-gated.** Implicit value-entry
  (CreateCell-at-0 for non-genesis) is retired in favor of authored minting.

## Alignment (BOTH kernels move — the goal is the best system, not freezing Lean)

### Lean (`metatheory/Dregg2/Exec/IssuerMove.lean`, `Handlers/StateSupply.lean`)
Split the single `issuerBurnK` gate: **mint** = mint-cap-gated (`mintAuthorizedB`), **self-
redeem** = holder-permissioned (the holder is the src, reducing their own balance to the
well). Keep `issuerBurnK_preserves_exact` conservation; refine only the authority predicate.
`BridgeMint` becomes an instance of cap-gated Mint (resolving the §4 faithfulness note).

### Rust (`turn/src/executor/`)
- Per-asset well: generalize `issuer_well_for` + well registration so every asset resolves a
  real signed well (created at issuance).
- `apply_burn`: route the debit into a well credit (conserving); keep self-burn
  permissionless; gate non-self / issuer-burn on the burn/supply cap.
- New `Effect::Mint`: well → holder, gated on a mint-cap; this is VK-affecting (a new effect
  descriptor) — staged behind the Lean descriptor + the circuit AIR, deploy ember-gated.
- Retire implicit value-entry for non-genesis CreateCell.

When both kernels implement this, the `Burn` (and `Mint`) entries on the Rust↔Lean
divergence allowlist are **deleted**, not re-characterized — the kernels genuinely agree.

## Staged build (each stage green + conservation-checked)
1. **Per-asset well + conserving self-burn** (Rust). Generalize the well; `apply_burn`
   credits the well; self-burn stays permissionless. Closes the **conservation** hole now.
   Differential/parity stay green; the well is a real `−supply` account. *No VK change.*
2. **`Effect::Mint` (cap-gated), Rust + Lean spec + circuit descriptor.** First-class mint;
   the issuer = mint-cap holder. *VK-affecting — Lean descriptor + AIR; deploy ember-gated.*
3. **Lean authority split** + retire implicit value-entry; delete the `Burn`/`Mint`
   allowlist entries; the rejection-parity corpus asserts agreement.
4. **Per-asset burn-policy cap** (the optional issuer-gated-destruction extension).

## Gates
Per-asset `Σholders + well = 0` (a conservation property test); cap-authority (mint needs a
mint-cap, rejection-parity verified); byte-identity for the v8/v9 commitment where a stage
doesn't change committed bytes; the VK-affecting stages gated behind the Lean descriptor +
AIR + ember deploy approval.

## What "done" looks like
Supply has exactly one authored entry (cap-gated Mint) and one authored exit (Burn/redeem),
both conserving against a per-asset well, both gated by capabilities the issuer controls —
so "who can coin / destroy this asset" is answered by the cap graph, not a kernel special
case, and the Rust and Lean kernels implement the *same* model with no burn/mint divergence.

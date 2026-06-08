# The Authorization Model — COMPLETE

The dregg2 authorization model is internalized end-to-end: a **token gates the
EXECUTOR ADMISSION**, every caveat tier and operator is **executed** (not
narrated), and no out-of-band authorization gate remains on a production path.
This is the l4v / INTERNALIZE-THE-GUARANTEES bar: "things being out-of-band is
us failing to develop a protocol that internalizes its guarantees." Each
guarantee below is proven **non-vacuous** — a forged / over-authorized
credential is REJECTED and a valid one is ADMITTED, on the SAME live path.

Build/test evidence is at the end. The whole model builds green
(`lake build` 991 jobs, `#assert_axioms` clean — only `{propext,
Classical.choice, Quot.sound}`, no `sorryAx`) and the Rust crates + auth tests
pass.

---

## 1. The shape of the gate

Authorization is one indivisible per-node decision fired IN FRONT of the
unchanged effect executor:

```
execFullAGated s na a = if gateOK na s then execFullA s a else none
gateOK na s = credentialValidG na          -- WHO  (§8 portal)
           && capAuthorityG na             -- WHAT (verified: granted ≤ held)
           && caveatsDischarged na s        -- CAVEATS (tiered, state-reading + macaroon HMAC)
           && revocationGate na s           -- NOT-REVOKED (kernel-state registry)
```

`Dregg2/Exec/FullForestAuth.lean:485` (`gateOK`),
`:514` (`execFullAGated`). The gate is a CONJUNCTION — **fail-closed on ANY
leg**; a single false leg ⇒ `none` ⇒ whole-forest rollback. No-TOCTOU is
automatic: `gateOK na s` reads exactly the `s` `execFullA` then commits against
(`gatedNode_check_eq_use`, `FullForestAuth.lean:584`).

The gate only NARROWS admission. On the commit path the gated run is
byte-identical to the ungated run of `eraseG f`
(`execFullForestG_erases`, `FullForestAuth.lean:846`), so conservation
(`execFullForestG_conserves_per_asset`, `:885`) and Granovetter
no-amplification (`execFullForestG_no_amplify`, `:898`) survive as one-line
corollaries — the launder teeth are intact.

---

## 2. The 10-variant `Authorization` (the WHO leg)

`FullForestAuth.lean:102` — the full dregg1 `Authorization` sum, single
per-node field, routed through ONE `AuthPortal` seam (`:85`):

| # | variant | leg | how it is decided |
|---|---|---|---|
| 1 | `signature` | crypto portal | `CryptoKernel.verify stmt sig` |
| 2 | `proof` | crypto portal | vk-bound ZK proof |
| 3 | `breadstuff` | Lean c-list | pure ledger read (WHAT leg gates) |
| 4 | `bearer` | crypto portal | SignedDelegation / StarkDelegation |
| 5 | `unchecked` | §8 anchor | **fail-closed** at a credentialed node (`portalVerify .unchecked = false`, `:151`) |
| 6 | `capTpDelivered` | portal + Lean | two sigs ∧ `granted ≤ held` (the dregg1 gap, modeled CORRECT) |
| 7 | `custom` | crypto portal | registry witnessed-predicate |
| 8 | `oneOf` | Lean structural | 1-of-N selector, 3 structural rules, recurses |
| 9 | `stealth` | crypto portal | curve25519 point relation + one-time sig |
| 10 | `token` | portal + Lean | biscuit/macaroon sig + caveat meet |

The portal's per-arm reduction is `portalVerify` (`:145`). Its `soundness` is a
Prop CARRIER (the §8 floor, the circuit's obligation) — **never proved sound in
Lean**, honestly named (`AuthPortal.soundness`, `:90`). The crypto hypotheses
(`CryptoKernel.collisionHard`, `MacKernel.unforgeable`) are assumptions, and
each is witnessed FALSE for a collapsing kernel so it is load-bearing, not
`True`.

**Non-vacuity (same live path):** `portalVerify goodSig = true`,
`portalVerify forgedSig = false`, `.unchecked = false`, OneOf with an Unchecked
slot = false (`FullForestAuth.lean:191-197`).

---

## 3. Every caveat tier + operator is EXECUTED

`GatedCaveat` (`FullForestAuth.lean:232`) carries a `DriftTier` tag, a
within-cell `check`, and a `.coordinated` cross-cell `cross` discharge.
`GatedCaveat.holds` (`:253`) dispatches per tier. The macaroon HMAC chain is the
fourth operator, gated by `chainGateG` (`:451`). All four are now witnessed
NON-VACUOUSLY on the SAME live `execFullForestG` entry in
`Dregg2/Exec/GatedForestCfg.lean`:

### A1 — tier WHAT (cap-authority `granted ≤ held`), load-bearing at the wire
`capModeOfEdge` (`GatedForestCfg.lean:134`) routes a delegation edge's
`keep`/`parentCap` into `.capTpDelivered` over the REAL `ExecAuth = Finset Auth`
lattice. A non-amplifying edge ADMITS; an amplifying one (`keep ⊄ parent`) makes
`capAuthorityG = false` ⇒ rollback.
- `capOkForestG_what_admits` (`:324`) — admits
- `capAmplifyForestG_what_rejects` (`:331`) — rejects
- `capAmplifyForestG_rolls_back` (`:345`) — `execFullForestG = none`

### A2 — the AGENT-FACING `Authorization::Token` path, BOTH legs
`mkAuthToken` (`:417`) sets the WHO to `.token` and the WHAT to the REAL
`AuthMode.token` windowed biscuit (`agentToken`, `:400`) — NOT the
`.unchecked` admit-by-construction. The token gates the executor on BOTH legs,
witnessed each direction:
- `tokenOkForestG_commits` (`:517`) — valid in-scope token COMMITS
- `tokenForgedForestG_rolls_back` (`:528`) — forged signature ⇒ rollback (WHO leg)
- `tokenOverAttenForestG_rolls_back` (`:542`) — over-attenuated ⇒ rollback (WHAT leg)

The two negatives are ORTHOGONAL (different gate legs), so neither is laundered
by the other. This is the executable face of "the token gates the executor, not
the narration."

### A3 — the TIER-3 COORDINATED caveat, WELDED into the production gate
`GatedCaveat.cross` welds `CoordinatedCaveat.dischargeCoordinated` /
`CrossCaveat.jointApplyCaveated` inline: on a single machine the companion cell
lives in the SAME `RecChainedState`, read on the SAME snapshot the node commits
against (no TOCTOU). The dead `.coordinated => false` branch is gone — replaced
by the proved atomic-snapshot equalizer.
- `coordOkForestG_commits` (`:669`) — satisfied covenant COMMITS
- `coordViolatedForestG_rolls_back` (`:693`) — violated covenant ⇒ rollback
- `coordCaveatNoView_fails` (`:642`) — `cross = none` ⇒ fail-closed (the dregg1 posture, recovered exactly)

### A4 — the MACAROON CAVEAT-CHAIN operator, EXECUTED (HMAC tail-binding)
`mkAuthChain` (`:763`) carries a REAL macaroon chain in `NodeAuth.chain`. The
`chainGateG` leg = `c.verify && c.admits` = `verifiedChainGate`, so caveat
REMOVAL is caught (`CaveatChain.removal_breaks_tail`) and the meet is enforced.
- `chainOkForestG_commits` (`:808`) — genuine in-window chain COMMITS
- `chainForgedForestG_rolls_back` (`:824`) — a dropped-caveat forgery breaks the HMAC tail ⇒ rollback

The macaroon kernel here is the honest reference kernel whose `unforgeable`
carrier is PROVED (`honest_unforgeable`) and provably FALSE for the collapsing
kernel (`collapse_not_unforgeable`) — load-bearing, not a `True` no-op.

### Revocation (kernel-state registry, fail-closed)
`revocationGate` (`FullForestAuth.lean:476`) reads the COMMITTED
`s.kernel.revoked` (adversary-uncontrollable), NOT the wire-supplied `rev`.
`gateOK_revoked_fails` (`:496`) proves a revoked credential cannot pass no matter
how valid its signature or how discharged its caveats.

### Biscuit Datalog attenuation + macaroon caveat-chaining (the algebra)
`Dregg2/Authority/Caveat.lean`: `Token.attenuate` = appending a caveat = the ONE
narrowing rule; `attenuate_narrows` (`:84`) proves `granted ≤ held` over the
caveat facts/rules (an attenuated token admits only what the parent already
admitted). `attenuate_subset` (`:92`) is the set form. The biscuit/macaroon split
IS the vat boundary (`macaroon_not_crossvat`, `:112`). `Dregg2/Authority/
CaveatChain.lean` is the macaroon HMAC chain modeled exactly as Rust computes the
tail: `append_narrows` (`:230`), `removal_breaks_tail` (`:324`), and
`chain_unforgeable` (`:402`) consuming `MacKernel.unforgeable`. The Rust biscuit
Datalog backend (`token/src/datalog_verify.rs`, `dregg_caveats.rs`) implements the
same subset/meet semantics (set-valued caveats: the request's values must be a
subset; `dregg_caveats.rs:72`).

---

## 4. Per-node attestation — credential-blindness ELIMINATED

`gatedActionInvG` (`FullForestAuth.lean:918`) ANDs the three auth conjuncts onto
the unchanged per-asset/chain/kind invariant. Every committed node of a gated
forest attests it at every nesting depth:
- `execFullAGated_attests` (`:931`) — per node
- `execFullForestG_each_attests` (`:995`) — whole tree
- `execFullForestG_unauthorized_fails` (`:949`) — fail-closed at the root on ANY leg

---

## 5. The agent-facing surfaces route through the EXECUTOR (no out-of-band gate)

### SDK `SubAgent` — `sdk/src/runtime.rs`
`SubAgent::execute_method` (`:968`) builds the worker's biscuit as
`Authorization::Token` (`cap_authorization`, `:937`) and calls
`executor.execute(&turn, &mut ledger)` (`:1036`). An over-scope call is rejected
by the executor's `verify_token_authorization`, NOT an out-of-band `cap.verify()`
(`:962-966`). The memory note "SubAgent::execute submits Authorization::Unchecked
+ checks caps OUT-OF-BAND" describes a PRIOR state, now eliminated (commit
`4e9d744c3` "Internalize the object-capability gate").
- `can_authorize` (`:899`) still exists but is a read-only DIAGNOSTIC predicate;
  it gates NO state mutation (the executor's token path is the admission).

### Node MCP — `node/src/mcp.rs`
The per-tool capability gate `enforce_tool_cap` (`:1532`) fires BEFORE
`dispatch_tool` (`handle_tools_call`, `:6844`). It parses the presented
`Authorization::Token` (`parse_presented_cap`, `:1504`), maps the tool to its
required `(action, resource)` scope (`tool_required_scope`, `:1376` — fail-closed:
an unmapped tool requires `admin`), and admits/rejects via the EXECUTOR's
`verify_token_for_scope` (`:1575`) — the SAME verification used to admit a turn.
A non-covering token (wrong issuer/target, un-granted verb) is REJECTED; under
`mcp_cap_enforce`, a missing token is also rejected.

Adversarial tests (`node/src/mcp.rs`, `mcp::tests`):
- `mcp_in_scope_cap_admitted_by_executor` — admits
- `mcp_overscope_cap_rejected_by_executor` — rejects (read token, admin tool)
- `mcp_missing_cap_rejected_under_enforcement` — rejects
- `mcp_wrong_issuer_cap_rejected` — rejects

---

## 6. The out-of-band audit — every gate internalized, or the precise residual

A grep of `node/src/`, `sdk/src/`, `app-framework/src/` for `cap.verify()`,
`Authorization::Unchecked`, and admit-by-construction surfaces:

| site | verdict |
|---|---|
| `node/src/mcp.rs:137,165` (`build_forest_with_effects` / `build_signed_forest`) | `build_signed_forest` REPLACES the placeholder with a real `Authorization::Signature` before submit (`:176`). `build_forest_with_effects` is for the agent's OWN cell (`agent_cell_id` derived from the cipherclerk), submitted only AFTER `enforce_tool_cap` required a covering Token. |
| `node/src/mcp.rs:1833,5546` | inner `authorization` field for the agent acting on its OWN no-auth cell. The executor admits `Unchecked` ONLY under `AuthRequired::None` (the cell's own policy, `authorize.rs:691`); for every other `AuthRequired` it is DENIED (`authorize.rs:832`). Gated by `enforce_tool_cap` upstream. |
| `node/src/mcp.rs:1780` (`tool_authorize` `verify_token`) | read-only QUERY tool returning an `authorized` bool; gates NO mutation. The tool itself is `enforce_tool_cap`-gated (scope `write`). |
| `node/src/api.rs:6604,6835` | inside `#[cfg(test)] fn make_test_forest` — test helper, not a production path. |
| `node/src/ws.rs:491`, `node/src/api.rs:1768` | the WS/HTTP `authorize` QUERY endpoints (token introspection); report-only, gate no mutation. (Owned by node-infra; not edited here.) |
| `sdk/src/runtime.rs:454` | `AgentRuntime::execute` builds the agent's OWN-cell action; the runtime's own turn is signed/admitted by the executor on submit. |
| `sdk/src/cipherclerk.rs:*`, `committed_turn.rs:233` | OWN-cell actions; the cipherclerk signs the turn (`build_signed_forest` analog). The audit notes there (`SDK-DREGGSCRIPT-AUDIT.md §9`) flag and GUARD against any regression to `Unchecked` on a non-owned target. |
| `app-framework/src/authorizer.rs`, `escrow.rs` | the framework REPLACED its historical `Unchecked` placeholders with `authorizer.authorize(ctx)?` (`authorizer.rs:70`); `Unchecked` is intentionally NOT used as a placeholder (`escrow.rs:123`). |

**Residual (precise):** there is ONE deliberate residual, the
`mcp_cap_enforce` back-compat flag (`mcp.rs:1527`). When it is OFF, a MISSING
`_cap` token passes `enforce_tool_cap` (a PRESENTED-but-non-covering token is
ALWAYS rejected). This is a deployment toggle for back-compat, not a bypass:
(a) a presented token is always verified by the executor; (b) the tool body is
still separately gated by the global cipherclerk unlock; (c) with
`mcp_cap_enforce` ON (the hardened posture), a missing token is rejected
fail-closed. There is no surface where a PRESENTED over-authorized or forged
credential is admitted out-of-band.

---

## 7. Build + test evidence

- `lake build Dregg2.Exec.FullForestAuth Dregg2.Exec.GatedForestCfg
  Dregg2.Authority.Caveat` → **Build completed successfully (991 jobs)**.
- `GatedForestCfg.lean`: 31 `#assert_axioms` (incl. the 8 new A4 macaroon-chain
  keystones) replay clean — kernel axioms only, NO `sorryAx`, NO `native_decide`,
  NO `:= True`.
- `cargo build -p dregg-token -p dregg-node` → exit 0.
- `cargo test -p dregg-node --bin dregg-node mcp::tests` → the MCP cap-gate
  adversarial suite passes (in-scope admit / over-scope reject / missing reject /
  wrong-issuer reject).
- `cargo test -p dregg-token` → token (biscuit/macaroon/datalog) suite passes.

**Bottom line:** the token gates the EXECUTOR ADMISSION. All four caveat
operators (within-cell tiers, cap-authority `granted ≤ held`, coordinated
cross-cell, macaroon HMAC chain) are executed end-to-end on the live gate, each
with a non-vacuity witness (admitted true AND rejected false on the same path).
No out-of-band authorization gate remains on a production path; the single
residual is a named, fail-closed-when-on back-compat toggle, not a bypass.

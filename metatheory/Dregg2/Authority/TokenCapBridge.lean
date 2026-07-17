/-
# Dregg2.Authority.TokenCapBridge — the token-caveat ⟷ cell-program (cap-crown) arrow.
## offline biscuit/macaroon verify ⟺ the in-circuit `checkSubset` proof, as ONE predicate.

`.docs-history-noclaude/AUTHORIZATION-MODEL.md` diagnoses the deepest open seam: the agent token layer (biscuit /
macaroon — the `Authority.Caveat` `Token.admits` caveat-set and the `Authority.Biscuit` signed
delegation chain) and the in-circuit cap-crown (#103 — the c-list `granted ⊆ held` the circuit
witnesses, realized as the `Circuit.Argus` `RecStmt.checkSubset` CELL-PROGRAM, `Stmt.lean §L′`,
welded at `Effects/Attenuate.lean`) are "two informal stories welded by `&&`, not one proven arrow."

`Authority.CaveatCapBridge` closed ONE face of that seam: the macaroon HMAC chain GATE (`chainGateG`)
⇒ the kernel cap GATE (`capAuthorityG`), gate-to-gate on `ExecAuth`. It never touches the
CELL-PROGRAM the circuit interprets (`RecStmt`/`interp`/`checkSubset`). This module closes the DEEPER
face — the one the lead flagged with `tokenCaveat_authorizes_iff_cellProgram_admits` /
`caveatSet_refines_capCrown`: that a token's CAVEAT-SET authorization and the CELL-PROGRAM the circuit
witnesses are **literally one predicate** over `ExecAuth = Finset Auth`, so

  > offline token-verify (the agent layer's `Token.admits` / the biscuit's `WellFormed` narrowing)
  > ⟺ the in-circuit `checkSubset granted held` proof (`interp (capCrownStmt …) k |>.isSome`)

— both decide the SAME `granted ⊆ held`, not two agreeing scalars.

## The arrow, in four legs (all four → one `granted ⊆ held` over `Finset Auth`)

  * **§2 the ISO (the keystone).** `tokenCaveat_authorizes_iff_cellProgram_admits` — a token bearing
    exactly the rights-narrowing caveat `capCaveat granted held` admits a request IFF the cell-program
    `capCrownStmt granted held` (= `RecStmt.checkSubset (const granted) (const held)`, the very gate
    `Effects/Attenuate.lean` welds into the circuit) admits. Both unfold to `decide (granted ⊆ held)`.
    The token caveat IS the cell-program, as one Boolean.
  * **§3 the macaroon CHAIN refinement.** `caveatSet_refines_capCrown` — a WHOLE caveat-set
    (a macaroon chain of kept-rights masks) confers `caveatChainAuthority held keeps`, which the
    cell-program `capCrownStmt (chain-authority) held` ALWAYS admits (it is `≤ held`, reusing
    `CaveatCapBridge.caveatChainAuthority_le_held`). The macaroon narrowing refines the circuit gate.
  * **§4 the biscuit OFFLINE-VERIFY leg.** `biscuitVerify_implies_capCrown_admits` — a well-formed
    biscuit (the OFFLINE public-key chain, `Authority.Biscuit.WellFormed`) has leaf rights ⊆ root
    rights (`biscuit_narrows`), so the cell-program `capCrownStmt leaf.authority root.authority`
    admits. This is the named ask verbatim: **offline biscuit-verify ⟹ in-circuit proof.**
  * **§5 the honest NAMED-CRYPTO gap.** The legs above are the STRUCTURAL arrow — unconditional,
    `#assert_clean`. The full "a FORGED token cannot make the circuit admit a non-narrowing" needs the
    token's signature unforgeability (biscuit ed25519 EUF-CMA, the `Authority.Biscuit.SigChecker`
    carrier) / the macaroon HMAC EUF-CMA (`CaveatChain.MacKernel.unforgeable`). We NAME them as
    hypotheses and state the conditional `forged_token_cannot_forge_capCrown` that consumes the biscuit
    `WellFormed` (which the unforgeability portal guarantees no adversary can fabricate for an
    amplifying chain) — we do NOT launder the crypto into a Lean law.

REUSES `Authority.Caveat` (`Token`/`Caveat`/`admits`), `Authority.BiscuitGraph`
(`WellFormed`/`biscuit_narrows`), `Authority.CaveatCapBridge` (`caveatChainAuthority` + its `≤ held`
refinement), and `Circuit.Argus.Stmt` (`RecStmt.checkSubset`/`interp`/`interp_checkSubset`). EDITS
none. ONE namespace. The FIRST module to import BOTH the token caveat layer AND the cell-program /
circuit layer — making them, at last, one object.

Pure, computable, `#guard`-able; `#assert_clean` (axiom set ⊆ {propext, Classical.choice, Quot.sound};
the named crypto carriers in §5 are explicit HYPOTHESES, never axioms).
-/
import Dregg2.Authority.Caveat
import Dregg2.Authority.BiscuitGraph
import Dregg2.Authority.CaveatCapBridge
import Dregg2.Circuit.Argus.Stmt

namespace Dregg2.Authority.TokenCapBridge

open Dregg2.Authority
open Dregg2.Exec (ExecAuth RecordKernelState)
open Dregg2.Circuit.Argus (RecStmt interp interp_checkSubset checkSubset_admits_iff)

/-! ## §1 — The shared rights predicate, expressed BOTH as a token caveat AND as a cell-program.

The cap-crown's non-amplification atom is `granted ⊆ held` over `ExecAuth = Finset Auth`
(`Exec/Caps.lean`, `confRights`). We render it TWICE — once as an agent-layer token caveat
(`capCaveat`, a `Authority.Caveat.opaque` check), once as the circuit's cell-program
(`capCrownStmt`, a `RecStmt.checkSubset` — the EXACT gate `Effects/Attenuate.lean` welds in-band) —
and §2 proves the two renderings are the SAME Boolean. -/

/-- **`RightsCtx`** — the request context a rights-bearing caveat reads: the `granted` (asked) and
`held` (parent) rights of the capability-bearing verb being authorized. This is the agent-layer view
of the kernel's `(granted, held) : ExecAuth` pair (`.docs-history-noclaude/AUTHORIZATION-MODEL.md §4.1`, the
"narrowed-authority spine"). A macaroon/biscuit caveat evaluates against exactly this. -/
structure RightsCtx where
  /-- the rights the request asks to exercise / install (the kernel `granted`). -/
  granted : ExecAuth
  /-- the rights the parent capability holds (the kernel `held`). -/
  held    : ExecAuth
-- (no `deriving Repr`: `ExecAuth = Finset Auth`'s `Repr` is an UNSAFE declaration, so deriving it
-- would force `RightsCtx` into the compiler and crash codegen; the `#guard` witnesses compare Bools,
-- never `Repr`, so none is needed.)

/-- **`capCaveat`** — the rights-narrowing token caveat (the `CapabilityCaveat` `Authority.Caveat`'s
docstring names): a `Caveat.opaque` whose check is the genuine non-amplification decision
`decide (ctx.granted ⊆ ctx.held)` over `ExecAuth = Finset Auth`. This is the agent-layer (biscuit
fact / macaroon 1st-party caveat) rendering of `granted ⊆ held` — fail-closed, decidable. -/
def capCaveat : Caveat RightsCtx Unit :=
  .opaque (fun ctx => decide (ctx.granted ≤ ctx.held))

/-- **`capToken granted held`** — a token bearing exactly one `capCaveat` (a capability-bearing
verb's credential). Kind is `macaroon` (cell-scoped); the kind does not enter the rights decision.
This is the minimal token whose authorization IS the cap-crown gate. -/
def capToken : Token RightsCtx Unit := { kind := .macaroon, caveats := [capCaveat] }

/-- **`capCrownStmt granted held`** — the cell-program the circuit witnesses for non-amplification:
`RecStmt.checkSubset (const granted) (const held)` — the EXACT primitive `Effects/Attenuate.lean`
welds in-band (`attenuateStmt = seq (checkSubset (granted.rights) (held.rights)) (setCaps …)`,
`Stmt.lean §L′`). A pure domain-restrictor: commits (`some k`) iff `granted ⊆ held` over the genuine
`Finset Auth` order, mutates nothing. The cap-crown predicate, as a runnable IR term. -/
def capCrownStmt (granted held : ExecAuth) : RecStmt :=
  RecStmt.checkSubset (fun _ => granted) (fun _ => held)

/-- The request context a `RightsCtx` caveat reads for the `(granted, held)` verb. -/
def mkCtx (granted held : ExecAuth) : RightsCtx := { granted := granted, held := held }

/-- No discharges — the cap caveat is a 1st-party (local) check, never a third-party caveat. -/
def noD : Discharges Unit := fun _ => false

/-! ## §2 — THE KEYSTONE ISO: the token caveat IS the cell-program (one Boolean over `Finset Auth`).

Both renderings decide `granted ⊆ held`. We prove each side equals `decide (granted ≤ held)` and
then chain them: the token's offline `admits` and the cell-program's in-circuit `isSome` are THE SAME
proposition — not two agreeing scalars, the LITERAL one predicate the lead asked for. -/

/-- **`capToken_admits_iff`** — the agent-layer side: the cap token admits the `(granted, held)`
request IFF `granted ⊆ held`. `Token.admits` is the conjunction of the single `capCaveat` check,
which is `decide (granted ≤ held)`. -/
theorem capToken_admits_iff (granted held : ExecAuth) :
    (capToken).admits (mkCtx granted held) noD = true ↔ granted ≤ held := by
  unfold capToken capCaveat Token.admits mkCtx
  simp only [List.all_cons, List.all_nil, Bool.and_true, Caveat.ok, decide_eq_true_eq]

/-- **`capCrownStmt_admits_iff`** — the circuit side: the cell-program `capCrownStmt granted held`
admits (its `interp` is `some`, the in-circuit `checkSubset` gate fires) IFF `granted ⊆ held`. Directly
the §L′ keystone `checkSubset_admits_iff` on the constant read-outs. -/
theorem capCrownStmt_admits_iff (granted held : ExecAuth) (k : RecordKernelState) :
    (interp (capCrownStmt granted held) k).isSome = true ↔ granted ≤ held := by
  unfold capCrownStmt
  exact checkSubset_admits_iff (fun _ => granted) (fun _ => held) k

/-- **`tokenCaveat_authorizes_iff_cellProgram_admits` — THE ARROW (the keystone the lead named).**

A token bearing the rights-narrowing caveat AUTHORIZES the `(granted, held)` request (offline
`Token.admits`, the agent/biscuit/macaroon layer) IF AND ONLY IF the cell-program the CIRCUIT
witnesses (`capCrownStmt granted held` = `RecStmt.checkSubset …`, the `Effects/Attenuate.lean` gate)
ADMITS (`interp |>.isSome`). They are not two agreeing facts welded by `&&` — they are the SAME
proposition `granted ⊆ held` over `ExecAuth = Finset Auth`, reached from both ends. This is offline
token-verify ⟺ in-circuit proof, as ONE predicate. -/
theorem tokenCaveat_authorizes_iff_cellProgram_admits
    (granted held : ExecAuth) (k : RecordKernelState) :
    (capToken).admits (mkCtx granted held) noD = true
      ↔ (interp (capCrownStmt granted held) k).isSome = true := by
  rw [capToken_admits_iff, capCrownStmt_admits_iff]

/-- **`tokenCaveat_authorizes_eq_cellProgram_admits`** — the Bool-EQUALITY face of the same arrow:
the two decisions are EQUAL as Booleans (the offline token gate and the in-circuit cell-program gate
return the SAME bit on every `(granted, held)`). The strongest "one predicate" statement: not merely
inter-derivable, definitionally one value. -/
theorem tokenCaveat_authorizes_eq_cellProgram_admits
    (granted held : ExecAuth) (k : RecordKernelState) :
    (capToken).admits (mkCtx granted held) noD = (interp (capCrownStmt granted held) k).isSome := by
  rw [Bool.eq_iff_iff]
  exact tokenCaveat_authorizes_iff_cellProgram_admits granted held k

/-! ## §3 — `caveatSet_refines_capCrown`: a whole macaroon CHAIN refines the cell-program.

§2 binds ONE caveat. A real macaroon is a CHAIN of kept-rights masks; its cumulative authority is
`CaveatCapBridge.caveatChainAuthority held keeps` (the parent met against every mask), proven `≤ held`
there (`caveatChainAuthority_le_held`). So the cell-program at the chain authority ALWAYS admits — the
WHOLE caveat-set's narrowing refines the circuit's `checkSubset`. This lifts the §2 single-caveat iso
to the full chain the lead asked about, REUSING the already-proven refinement (no re-derivation). -/

/-- **`caveatSet_refines_capCrown` (the chain refinement).** For ANY macaroon chain of kept-rights
masks `keeps` over a parent `held`, the cell-program `capCrownStmt (caveatChainAuthority held keeps)
held` — the circuit's `checkSubset` at the chain's CONFERRED authority — ADMITS. Because the chain
authority is `≤ held` (`CaveatCapBridge.caveatChainAuthority_le_held`, the macaroon `append_narrows`
on the rights lattice), the in-circuit non-amplification gate fires: a macaroon, however attenuated,
yields an in-circuit-admissible cap-crown. The caveat-SET narrowing REFINES the cell-program. -/
theorem caveatSet_refines_capCrown (held : ExecAuth) (keeps : List ExecAuth)
    (k : RecordKernelState) :
    (interp (capCrownStmt (CaveatCapBridge.caveatChainAuthority held keeps) held) k).isSome = true := by
  rw [capCrownStmt_admits_iff]
  exact CaveatCapBridge.caveatChainAuthority_le_held held keeps

/-- **`caveatChainToken_admits_capCrown`** — the agent-layer companion: the token bearing the
rights-narrowing caveat at the CHAIN authority also admits offline. Together with
`caveatSet_refines_capCrown` (the circuit side), the macaroon chain's offline `admits` and the
cell-program's in-circuit `isSome` agree for the whole chain — §2's iso, lifted to the chain. -/
theorem caveatChainToken_admits_capCrown (held : ExecAuth) (keeps : List ExecAuth) :
    (capToken).admits (mkCtx (CaveatCapBridge.caveatChainAuthority held keeps) held) noD = true := by
  rw [capToken_admits_iff]
  exact CaveatCapBridge.caveatChainAuthority_le_held held keeps

/-! ## §4 — the BISCUIT OFFLINE-VERIFY leg: a well-formed biscuit ⟹ the cell-program admits.

The named ask names BOTH carriers: "offline biscuit-verify ⟺ in-circuit proof". §2/§3 covered the
macaroon caveat-set; here is the biscuit (public-key, OFFLINE) leg. `Authority.Biscuit.WellFormed`
is the offline-verifiable signed delegation chain; `biscuit_narrows` proves its leaf rights ⊆ root
rights. So the cell-program at `(leaf.authority, root.authority)` admits: OFFLINE biscuit verification
implies the IN-CIRCUIT cell-program admits the same narrowing. The two carriers, one predicate. -/

/-- **`biscuitVerify_implies_capCrown_admits` — offline biscuit-verify ⟹ in-circuit proof.**

Given a WELL-FORMED biscuit (the offline public-key delegation chain `Authority.Biscuit.WellFormed`,
verified WITHOUT contacting the issuer) with leaf block `leaf` and root block `root`, the cell-program
the CIRCUIT witnesses — `capCrownStmt leaf.authority root.authority` — ADMITS. The biscuit's own
narrowing law (`biscuit_narrows`: leaf rights ⊆ root rights) is exactly the cell-program's admission
condition. So a credential that verifies OFFLINE at the agent layer yields an IN-CIRCUIT-admissible
cap-crown for the SAME rights narrowing: offline biscuit-verify ⟺ in-circuit `checkSubset`, the named
ask, on the biscuit carrier. (Signature unforgeability — that the `WellFormed` chain could not have
been forged — is the §5 named hypothesis, NOT consumed here: this is the structural narrowing leg.) -/
theorem biscuitVerify_implies_capCrown_admits
    {sigOk : Biscuit.SigChecker} {rk : Biscuit.PubKey} {blocks : List Biscuit.Block}
    (wf : Biscuit.WellFormed sigOk rk blocks)
    {leaf root : Biscuit.Block}
    (hh : blocks.head? = some leaf) (hl : blocks.getLast? = some root)
    (k : RecordKernelState) :
    (interp (capCrownStmt leaf.authority root.authority) k).isSome = true := by
  rw [capCrownStmt_admits_iff]
  -- `biscuit_narrows` gives `leaf.authority ⊆ root.authority`; `Finset.le_iff_subset` is `≤`.
  rw [Finset.le_iff_subset]
  exact Biscuit.biscuit_narrows wf hh hl

/-! ## §5 — the HONEST named-crypto gap (do NOT launder vacuity).

The legs above are the STRUCTURAL arrow: a token whose caveats / blocks NARROW yields an
in-circuit-admissible cap-crown, UNCONDITIONALLY (`#assert_clean`). What they do NOT close on their
own is the ADVERSARIAL direction: "a FORGED token cannot make the circuit admit a NON-narrowing." That
needs the token's signature/MAC unforgeability — and we NAME it, never assume it as a Lean law.

  * **biscuit** — the §8 `Authority.Biscuit.SigChecker` carrier: no adversary lacking the parent's
    secret can produce a block that verifies. `Authority.Biscuit` already proves the STRUCTURAL teeth
    (`amplifying_block_rejected`, `forged_block_rejected`): an amplifying or forged block makes the
    chain ILL-FORMED. So `WellFormed` is exactly the predicate the unforgeability portal certifies an
    adversary CANNOT fabricate for an amplifying chain.
  * **macaroon** — `CaveatChain.MacKernel.unforgeable` (the HMAC EUF-CMA carrier already in the tree):
    a verifying chain's tail is a GENUINE MAC (`CaveatChain.chain_unforgeable`), so its caveat list —
    hence its conferred authority — is bound, unforgeable.

We state the biscuit adversarial bound as a theorem that CONSUMES `WellFormed` (which is what the
signature portal guarantees of any chain an adversary could present). The HMAC face is cited from
`CaveatChain.chain_unforgeable`, not re-proved. -/

/-- **`forged_token_cannot_forge_capCrown` (the adversarial bound, biscuit carrier).** An adversary
cannot present a biscuit that VERIFIES (`WellFormed`, the offline signature check) yet whose leaf
block AMPLIFIES past the root (claims a right the root never held) — because an amplifying chain is
ILL-FORMED (`Authority.Biscuit.amplifying_block_rejected`, the structural tooth), so it cannot verify
in the first place. Stated contrapositively: a verifying biscuit's leaf NEVER amplifies, hence the
cell-program ADMITS the genuine narrowing and REFUSES nothing forgeable.

The crypto content — that the adversary cannot make `sigOk` accept a fabricated block, so `WellFormed`
is the adversary's ONLY admissible presentation — lives in the `sigOk` EUF-CMA carrier (§8, the named
`Biscuit.SigChecker` unforgeability), NOT here. This theorem is the STRUCTURAL half: GIVEN a verifying
chain (which unforgeability says is all the adversary can offer), the cap-crown narrowing holds. The
two-block amplifying-leaf case is the load-bearing one (`b :: prev :: rest`); we discharge it from the
structural teeth. -/
theorem forged_token_cannot_forge_capCrown
    (sigOk : Biscuit.SigChecker) (rk : Biscuit.PubKey)
    (b prev : Biscuit.Block) (rest : List Biscuit.Block)
    (hamp : ¬ Biscuit.attenuates b prev) :
    ¬ Biscuit.WellFormed sigOk rk (b :: prev :: rest) :=
  Biscuit.amplifying_block_rejected sigOk rk hamp

/-- **`capCrown_admits_genuine_biscuit_narrowing`** — the positive companion of the bound: on a
VERIFYING two-block-or-more biscuit, the leaf attenuates the previous block (`attenuates b prev`, the
`WellFormed` edge invariant), so the cell-program at `(b.authority, prev.authority)` admits. The
adversary's only admissible chains (the verifying ones — the unforgeability portal forbids the rest)
are EXACTLY those the cap-crown admits. No forgeable narrowing slips past the circuit. -/
theorem capCrown_admits_genuine_biscuit_narrowing
    (sigOk : Biscuit.SigChecker) (rk : Biscuit.PubKey)
    (b prev : Biscuit.Block) (rest : List Biscuit.Block)
    (wf : Biscuit.WellFormed sigOk rk (b :: prev :: rest))
    (k : RecordKernelState) :
    (interp (capCrownStmt b.authority prev.authority) k).isSome = true := by
  rw [capCrownStmt_admits_iff, Finset.le_iff_subset]
  -- `WellFormed (b :: prev :: rest)` unfolds to `sigOk … ∧ attenuates b prev ∧ WellFormed …`.
  exact wf.2.1

/-! ## §6 — NON-VACUITY: both polarities, on the SAME objects, BOTH gates.

The arrow is worthless if either gate admitted everything. We exhibit, on concrete `ExecAuth` pairs:
a genuine narrowing `{read} ⊆ {read,write}` ADMITS at BOTH the token gate AND the cell-program; a
strict superset `{read,write} ⊄ {read}` REFUSES at BOTH; and — the partial-order tooth the cardinality
shadow could never make — an INCOMPARABLE pair `{read}` vs `{write}` REFUSES at BOTH. The iso §2 holds
across all three (the two gates agree bit-for-bit), and the biscuit/chain legs fire on a concrete chain. -/

/-- A minimal kernel state for the cell-program non-vacuity witnesses (the `checkSubset` read-outs are
constant in `k`, so only existence matters; `RecordKernelState`'s other fields default). -/
def kNV : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 0)], caps := fun _ => [] }

/-- A genuine narrowing: `{read}` ⊆ `{read, write}`. -/
def grantedR : ExecAuth := {Auth.read}
def heldRW   : ExecAuth := {Auth.read, Auth.write}
/-- An over-broad ask: `{read, write}` ⊄ `{read}` (strict superset). -/
def grantedRW : ExecAuth := {Auth.read, Auth.write}
def heldR     : ExecAuth := {Auth.read}
/-- An INCOMPARABLE pair: `{write}` vs `{read}` (neither ⊆ the other). -/
def grantedW : ExecAuth := {Auth.write}

-- The token gate and the cell-program gate AGREE, three-way, on the SAME pairs:
-- ADMIT a genuine subset …
#guard ((capToken).admits (mkCtx grantedR heldRW) noD)                       -- true  (token)
#guard ((interp (capCrownStmt grantedR heldRW) kNV).isSome)                  -- true  (cell-program)
-- … REFUSE a strict superset …
#guard ((capToken).admits (mkCtx grantedRW heldR) noD) == false              -- false (token)
#guard ((interp (capCrownStmt grantedRW heldR) kNV).isSome) == false         -- false (cell-program)
-- … REFUSE an incomparable pair (the partial-order tooth) …
#guard ((capToken).admits (mkCtx grantedW heldR) noD) == false               -- false (token)
#guard ((interp (capCrownStmt grantedW heldR) kNV).isSome) == false          -- false (cell-program)

/-- **NON-VACUITY (positive — both gates ADMIT a genuine narrowing, AND agree).** A `{read} ⊆
{read,write}` narrowing is admitted by the token caveat AND by the cell-program, and the §2 iso holds:
the two bits are equal. -/
theorem nv_admits_and_agrees :
    (capToken).admits (mkCtx grantedR heldRW) noD = true
    ∧ (interp (capCrownStmt grantedR heldRW) kNV).isSome = true
    ∧ (capToken).admits (mkCtx grantedR heldRW) noD
        = (interp (capCrownStmt grantedR heldRW) kNV).isSome := by
  refine ⟨by decide, by decide, ?_⟩
  exact tokenCaveat_authorizes_eq_cellProgram_admits grantedR heldRW kNV

/-- **NON-VACUITY (negative tooth — both gates REFUSE an INCOMPARABLE pair, AND agree).** The
load-bearing partial-order case the cardinality shadow could never make: `{write}` against a parent
holding only `{read}` (equal cardinality, NEITHER a subset) is REFUSED by the token caveat AND by the
cell-program, and the two bits agree. The arrow's conclusion is a REAL constraint, refused identically
at both ends — not a vacuous always-admit. -/
theorem nv_refuses_incomparable_and_agrees :
    (capToken).admits (mkCtx grantedW heldR) noD = false
    ∧ (interp (capCrownStmt grantedW heldR) kNV).isSome = false
    ∧ (capToken).admits (mkCtx grantedW heldR) noD
        = (interp (capCrownStmt grantedW heldR) kNV).isSome := by
  refine ⟨by decide, by decide, ?_⟩
  exact tokenCaveat_authorizes_eq_cellProgram_admits grantedW heldR kNV

/-- A concrete well-formed biscuit (reused from `Authority.Biscuit`): leaf `{read}` ← mid `{read,
write}` ← root `{read,write,grant}`, signed + narrowing at every step. -/
def demoBiscuit : List Biscuit.Block := Biscuit.goodBiscuit

/-- **NON-VACUITY (the biscuit OFFLINE-VERIFY leg fires concretely).** The well-formed `goodBiscuit`'s
leaf rights `{read}` ⊆ root rights `{read,write,grant}`, so the cell-program admits: offline biscuit
verification yields an in-circuit-admissible cap-crown, witnessed on a real signed chain (not
abstractly). -/
theorem nv_biscuit_offline_verify_admits_capCrown (k : RecordKernelState) :
    (interp (capCrownStmt Biscuit.leafBlock.authority Biscuit.rootBlock.authority) k).isSome = true :=
  biscuitVerify_implies_capCrown_admits Biscuit.goodBiscuit_wellFormed (by rfl) (by rfl) k

/-- **NON-VACUITY (the macaroon CHAIN refinement fires concretely).** A two-mask chain over
`{read,write}` confers `{read}` (= `caveatChainAuthority {read,write} [{read,write}, {read}]`), which
the cell-program admits — `caveatSet_refines_capCrown` on a concrete chain. -/
theorem nv_chain_refines_capCrown (k : RecordKernelState) :
    (interp (capCrownStmt
      (CaveatCapBridge.caveatChainAuthority heldRW [heldRW, grantedR]) heldRW) k).isSome = true :=
  caveatSet_refines_capCrown heldRW [heldRW, grantedR] k

#assert_clean capToken_admits_iff
#assert_clean capCrownStmt_admits_iff
#assert_clean tokenCaveat_authorizes_iff_cellProgram_admits
#assert_clean tokenCaveat_authorizes_eq_cellProgram_admits
#assert_clean caveatSet_refines_capCrown
#assert_clean caveatChainToken_admits_capCrown
#assert_clean biscuitVerify_implies_capCrown_admits
#assert_clean forged_token_cannot_forge_capCrown
#assert_clean capCrown_admits_genuine_biscuit_narrowing
#assert_clean nv_admits_and_agrees
#assert_clean nv_refuses_incomparable_and_agrees
#assert_clean nv_biscuit_offline_verify_admits_capCrown
#assert_clean nv_chain_refines_capCrown

end Dregg2.Authority.TokenCapBridge

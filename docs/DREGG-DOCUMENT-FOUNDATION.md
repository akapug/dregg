# DREGG DOCUMENT — the foundation

*The soundness foundation for the dregg document, written after reading the code and the proofs
adversarially. It supersedes the flinching `DREGG-DOCUMENT-DESIGN.md`. §1 holds the **whole** core
as the guiding star; §2 scopes the **foundation** we swarm first; §3 is the honest ledger of what is
proven / tested / assumed today, because every design decision below rests on it.*

**Register:** a design document. §1 is the guiding star; §3 is the as-built ledger. Foundation
pieces F1–F3 are built (§2 marks each); F4's export cutover is the remaining named seam, ember-gated.

---

## 0. The one paragraph

A dregg document is a **graph of cells** (composition), each cell an **umem** whose committed root
is its boundary, rendered by a **recursive fold through the viewer's membrane** as a tree of
**`<dregg-*>` custom elements** (shadow root = membrane boundary = cell boundary). The soundness
core — cross-cell atom identity, the commitment, merge, the quote/embed verifier — is **proven
Lean**; the F4 target is to `@[export]` it so it runs **native and in the browser tab** as **one**
implementation with no Rust shadow to drift (the wasm-Lean path is proven viable; §4 — the cutover
itself is the remaining named seam). The already-proven merge algebra rides on top. The document is
not a new subsystem — it is the composition algebra given a real carrier and a real hash, with the
web as its backend.

---

## 1. The holistic core (the guiding star — hold it while building the foundation)

Five facts, each read out of the code, that together *are* the design:

**1.1 Composition binds boundaries, not bytes.** A `UVal::UmemRef` is 32 bytes — a child umem's
root. `open_through_umem_ref` reads through it as two independent applications of the *proven*
boundary keystone. So a child cell can be a codebase, a world, a federation ledger — **the parent's
commitment does not grow by one byte**, and a light client composes the two checks. *"Bind the
boundary, not the bytes, and largeness rides for free."*

**1.2 Composition factors collaboration.** Layout graph and each child graph are **disjoint**
(`CellId`/`AtomId` spaces don't overlap) → merge is a **product of pushouts**; a child-content edit
can **never** conflict with a layout edit (tested: `layout_edit_and_child_edit_do_not_conflict`).
The *only* new cross-boundary conflict is a `Pin::At` divergence (two authors pin one embed to
different receipts) — a single-valued field clash, reusing existing machinery. **Collaboration
scales by factoring into cells, not by a cleverer merge.** This is why we do *not* need a global
CRDT co-typing subsystem before authoring real documents; same-region co-typing is a narrow case,
deliberately left empirical by the DDL design.

**1.3 The universal surface shape.** `ViewNode::host(cellId)`, `Op::Embed{ChildRef, Pin}`, and
`<dregg-embed src="dregg://…">` are **one idea at three layers** — a node/atom/element that IS a
cell, resolved through the membrane. The existence proof is in-tree: `scene_to_composed` maps every
desktop window to an `Op::Embed`, folded through `content_composed`, with per-viewer darkening
(`an_out_of_cap_window_darkens_in_the_composed_desktop`). **The desktop is a composed document.** So
composition is not a document feature; it is the shape of every dregg surface. The web mapping is an
*instance of a proven algebra*, not an analogy:
| composition algebra | web | proof status |
|---|---|---|
| a cell | a custom element | — |
| `Op::Embed{ChildRef, Pin}` | a nested `<dregg-*>` | prototype |
| membrane meet `held ∧ lineage` | shadow boundary + the element's cap projection | **built + tested** |
| `Darkened` (citation kept, `text=""`, no forge path) | element renders only its provenance | **built + tested** |
| rendering confers no authority | a `<dregg-*>` is a *surface* | **PROVEN** (`surfaceConfersExactly`) |
| `Pin::Live` vs `Pin::At(receipt)` | a live element vs a frozen quote | — |

**1.4 Two references, one committed indirection.** `ChildRef = Cell(CellId, Pin)` (fixed identity,
survives key rotation) `| Name(DreggUri, Pin)` (re-bindable role — "the hero figure", "the current
clause"; `Unbound` first-class). The `Name` commitment binds `namespace ‖ name ‖ pin ‖ role ‖
provenance` — **the indirection itself**, so a light client follows the same name. Re-bindable
references that stay verifiable. (`COLL_EMBEDS` leaf: built — `dregg-doc/src/substrate.rs` binds
each embed's pointer, pin, role, and provenance into the parent commitment; `NamespaceResolver`
lives in `composition.rs`.)

**1.5 Structure is cells; content is atoms.** Because a section IS a cell and a figure IS a cell,
`Block`/`Media`/`Code` are **embedded cells**, not atom-content variants. Within one cell, the
patch document holds atoms (`Text` runs + a DOM-shaped `Element{tag, attrs, children}`, already
landed) with marks as a *separate Peritext overlay*. So the model is two levels:
- **across cells** — composition: product-of-pushouts, cap-frustum, membrane, darkening. *Maps to
  nested custom elements; shadow root = cell boundary.*
- **within a cell** — the patch document. *Maps to the DOM subtree inside one shadow root; `AtomId`
  = the DOM node key the reconciler diffs against.*

**Hold all five while swarming the foundation.** They are the invariants each foundation piece must
not violate; they are not themselves the first build.

---

## 2. The foundation (what we swarm FIRST)

The foundation is the **soundness core** that makes composition *type* and *not forge*. Everything
rich (marks, vocabularies, the editor, live transclusion push) is downstream and **deliberately
deferred** — the DDL design says to let it emerge from authoring real documents on a small sound
core, so the rich work rests on discharged guarantees rather than assumptions.

The audit found every document defect is one mistake — **the Lean is a shadow of the Rust, so the
proof is about a model, not the thing.** The foundation kills the shadow-gap; F4 finishes the job
by construction, carrying the core to Lean `@[export]`s over canonical bytes (batched — the FFI is
not per-node; §4). Four pieces:

**F1 — The composed carrier + product-of-pushouts. BUILT.** `DocMerge.lean` proves `merge_is_lub`/
`isPushout` over a SINGLE `DocGraph` (`AtomId := Nat` local to one graph). A composed document is a
**family of DocGraphs indexed by CellId** — a parent layout graph + a `CellId → DocGraph` map of
children, each independently owned. `DocMergeComposed.lean` defines `ComposedDoc` + `mergeComposed`
(componentwise `merge`, matching `composition.rs::merge_composed`) and LIFTS the single-cell
theorems to the product — the merge laws componentwise (`mergeComposed_comm`/`assoc`/`idem` via
`childJoin`), the universal property (`mergeComposed_is_lub`), the pushout in the composed thin
category, and **the boundary lemma** (`boundary_layout_child_disjoint`): a child-content edit and a
layout edit can never conflict, because their carriers are DISJOINT components (§1.2 made a
theorem). NOTE: the cross-cell identity here is the family INDEX
(`CellId`); `AtomId` stays LOCAL per cell. A *global* `(CellId, AtomId)` id is a DOWNSTREAM
refinement needed only for atom-RANGE transclusion (quoting specific atoms inside another cell),
not for whole-cell composition.

**F2 — Real-hash commitment binding the pointer AND the alternatives. BUILT** (in Rust, with the
soundness in Lean; the Lean-`@[export]` one-implementation form is F4's cutover). The production
document commitment is `substrate_commit` (`dregg-doc/src/substrate.rs`) — the real sorted-Poseidon2
heap root over the projected cell heap — binding: the atom's type+content+provenance (typed
`canonical_bytes`); for an embed, the `ChildRef` pointer under the `COLL_EMBEDS` leaf; **and for a
conflict, BOTH live alternatives + their provenance** — that last is **conflict-as-state
soundness**: without it, a light client can be shown a two-branch conflict hiding a *forged*
alternative (the seven-forgery-bugs shape, in the document layer), and the substrate anti-forge
tests exercise exactly that against the real root. `DocSubstrateSound.lean` proves the two
soundness properties on the faithful WIDE 8-felt root (`mapRoot8_injective`,
`opensToMerkle8_functional` — riding `MapMerkleRoot`, not the superseded flat sponge), under the
named arity-16 chip collision-resistance hypothesis. `DefaultHasher` survives only for local id
derivation (`AtomId`/`PatchId` seeds), never the commitment.

**F3 — The anchored quote/embed verifier. BUILT.** The include path routes through the
committee-anchored cryptographic gate: `TranscludedField::include()` threads the resolver's held
committee into `include_anchored`, which gates every quote on
`AttestedResource::verify_anchored(committee)` — signature verification against the client's
trusted keys, NOT a structural quorum count (`starbridge-web-surface/src/transclusion.rs`).
FAIL-CLOSED: an empty committee accepts nothing; a root fabricated under untrusted keys is refused
(`ProvenanceUnverified`); a non-finalized read is refused (`NotFinalized`). The Lean mirror is
`Dregg2.Deos.AnchoredQuote`: `anchored_quote_unforgeable` discharges the anti-forge to the crypto
floor — signature unforgeability (EUF-CMA) + hash collision-resistance, both actually used in the
proof. The former hole (structural-count-only `verify()` on the include path) is closed by
construction, not by remembering to call the right function.

**F4 — The module-layering + the doc differential retirement. NAMED SEAM (not built; the cutover
is ember-gated).** Structure the core as the wasm discipline demands (§4): `DocCore` (Init-only,
`UInt64`/BabyBear, `@[export]`) + `DocProofs` (imports `DocCore` + Mathlib, proves F1–F3, **off the
wasm import path**). Wire the Rust `dregg-doc` + the `<dregg-doc>` wasm to call the exported core.
This is the piece that makes `<dregg-doc>`'s in-tab executor *the proven core*, retiring the shadow.
Until it lands, the Rust `dregg-doc` is the executor and the Lean modules are its proven model —
differential-tested, not identical-by-construction.

**Honest carriers (named, at the floor — same as the circuits):** Poseidon2 collision-resistance,
signature unforgeability. Which committee to trust is a *policy*. `Pin::Live` vs coordination-
freedom is a *semantics decision* (a live cross-cell read is provably not i-confluent), not a proof
gap — proposed default: `Pin::Live` for render, `Pin::At(receipt)` snapshot for anything entering a
commitment. **Not assumed; a call to make.**

---

## 3. The as-built ledger (why the foundation is shaped this way)

**PROVEN in Lean (`#assert_axioms`-clean):** merge comm/assoc/idem/total, `merge_is_lub`,
`merge_isPushout` — **over `AtomVal := Status`**, which `DocMerge.lean` argues faithful to what the
code merges (content diverges at the commitment layer, not the merge algebra). The composed lift
(`DocMergeComposed.lean`: `mergeComposed_is_lub`, the composed pushout, the boundary lemma), the
patch-commutation laws (`DocPatch.lean`: independent additive ops commute, each op
inclusion-monotone, apply=merge-with-a-singleton), and the FULL labelled patch category `P`
(`PatchCategory.lean`: morphisms are `Op`-sequences, a genuine `CategoryTheory.Category` — the
former named residual, closed). Conflict-as-first-class-state (`merge_has_conflict`), two-regime
`prose_iconfluent`/`field_not_iconfluent`, stitch=pushout, settlement soundness (non-tautological
via `deployedSettle`), non-amplification (`reshareN_attenuates`, `surfaceConfersExactly`,
`transclusion_no_amplify`), document-commitment soundness on the faithful wide 8-felt root
(`DocSubstrateSound.lean`, under the named chip-CR hypothesis).

**PROVEN but weaker than its name:** `Transclusion.lean` is `def Transclusion := ImportedEq`; its
keystones are renamings. Its anti-forge (`transclusion_forge_refused`) rests on `stateAt : Receipt →
Value` being an **abstract total function** — a receipt determines a value *by model construction*.
It refuses "different value for the same cited receipt"; it says **nothing** about fabricating a
receipt. The non-forgeable quote is proven elsewhere: `AnchoredQuote.lean`'s
`anchored_quote_unforgeable` discharges to signature unforgeability + collision resistance, both
actually invoked (F3's Lean leg).

**TESTED-in-Rust only, single-instance:** the merge "laws" in `tests.rs` are examples over a fixed
3-graph fixture (the ∀-proof lives in Lean); per-viewer darkening (real + specific). The `commit`
anti-forge tests ride the REAL sorted-Poseidon2 root under `--features substrate`.

**Named seams / holes:** receipt-id ↔ patch-id (uncrossed); `AtomId` single-graph (the
`(cell,atom)` global id, a downstream refinement for atom-range transclusion); `Embed`/`Transclude`
absent from the core atom sum (embeds live in the composition layer's `Op::Embed`, not
`AtomContent`); the F4 export cutover (the Rust executor vs proven-Lean-core seam); the leptos
reactive (push) transclusion.

**What composition makes load-bearing:** cross-cell identity (F1); cross-cell commitment binding
(F2); the crypto that a self-authored cell could ignore but a *peer-verified quote* cannot (F2/F3).
**Composition is precisely the thing that makes these guarantees matter** — which is why the
foundation is the soundness core, not a document IR.

---

## 4. How the core reaches the tab (the wasm-Lean discipline — proven viable)

`@[export]` Lean runs in wasm32; verified live under Node: a real Poseidon2 content-root fold (the
`Storage/Deployed` idiom, `@[extern]` fast Rust primitive at the leaf) ran at **677 KB** vs ~40 MB
as-written — ~60×. So the doc-core lives in the tab as the *proven* core, not a Rust shadow.

**The load-bearing discipline (subtle — it is NOT the linker):** Prop bodies erase (Mathlib *lemmas*
generate no code), but **module *initialization* is not erased** — importing a module runs its
`initialize_*` at boot and keeps the object; the reachability-GC chases those edges and cannot prune
below the transitive import closure. **Minimality is an import-graph property.** So:
- **`DocCore`**: `@[export]` fns in an **Init-only** module (`UInt64`/BabyBear/Init `List`/`String`;
  avoid `ℤ`/Mathlib). Verify: `grep -o 'initialize_[A-Za-z0-9_]*' Mod.c | sort -u` shows only `Init`
  + the module.
- **`DocProofs`**: imports `DocCore` + Mathlib, proves F1–F3 — **never on the wasm import path.** The
  proofs stay exactly as strong (they discharge to the `Poseidon2SpongeCR` floor); they just don't
  ship. *Proofs off the wasm import path.*
- **FFI shape**: batched over canonical bytes (`commit.rs::canonical_bytes` is the encoding), not a
  `lean_object*` object-graph crawl. GMP is a red herring (`USE_GMP:OFF`, fixed-width core).
- Mandatory flags: `-DLEAN_EMSCRIPTEN -fwasm-exceptions`. Recipe reproducible; native path links
  `libdregg_lean.a` as today. **Measure the per-edit FFI cost before committing to per-edit calls;**
  the storage-commit shape is proven, a per-keystroke merge is a different shape.

*(The in-browser Lean **elaborator** — authoring new Lean in-tab — hits a `MULTI_THREAD` wasm-ld
wall. Different goal; does NOT gate running the doc-core.)*

---

## 5. Build order (the swarm)

Foundation-first; each piece verifiable against the existing tested laws; nothing discards the
banked soundness.

1. **F1 — the composed carrier in Lean** (`DocMergeComposed.lean`) + the lifted
   `merge_is_lub`/pushout theorems. **Done.**
2. **F2 — the real-hash commitment** (`substrate_commit`, sorted-Poseidon2) binding pointer +
   conflict alternatives, with `DocSubstrateSound.lean` on the wide root. **Done** (Rust production
   path + Lean soundness; the Lean-export form rides F4).
3. **F3 — the anchored verifier on the `include()` path** (`include_anchored` +
   `AnchoredQuote.lean`). **Done.**
4. **F4a — the `DocCore`/`DocProofs` module split** + a minimal `@[export]` `atom_id`/`commit`
   compiling to wasm at the 677 KB floor (prove the discipline on the real core, not a probe).
   **Open.**
5. **F4b — wire `dregg-doc` (native) + `<dregg-doc>` (wasm) to the exported core.** Retire the
   shadow. **Open; the cutover is ember-gated.**
6. **Then** the rich layer — marks, vocabularies, the editor, live-embed push — *emergent from
   authoring real documents on the sound foundation.* A follow-on spec, deliberately not now.

**Guiding-star check for every agent:** does this piece keep §1.1–1.5 true? (boundary-not-bytes;
composition-factors-merge; the universal surface shape; committed indirection; structure-is-cells.)

---

*The foundation stands: a composed carrier with lifted laws, a real hash binding pointer and
alternatives, and a closed committee-anchored verifier. What remains is F4 — putting the proven
core itself in the tab. Then the document gets to become rich, on ground we have actually checked.*

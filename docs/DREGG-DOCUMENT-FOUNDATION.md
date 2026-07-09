# DREGG DOCUMENT — the foundation

*The soundness foundation for the dregg document, written after reading the code and the proofs
adversarially. It supersedes the flinching `DREGG-DOCUMENT-DESIGN.md`. §1 holds the **whole** core
as the guiding star; §2 scopes the **foundation** we swarm first; §3 is the honest ledger of what is
proven / tested / assumed today, because every design decision below rests on it.*

**Register:** a design document. §3 marks as-built state; everything else is target. The gap is the
program.

---

## 0. The one paragraph

A dregg document is a **graph of cells** (composition), each cell an **umem** whose committed root
is its boundary, rendered by a **recursive fold through the viewer's membrane** as a tree of
**`<dregg-*>` custom elements** (shadow root = membrane boundary = cell boundary). The soundness
core — cross-cell atom identity, the commitment, merge, the quote/embed verifier — is **proven
Lean, `@[export]`ed**, and it runs **native and in the browser tab** (the wasm-Lean path is closed;
§4). There is **one** implementation and it is the proven one; no Rust shadow to drift. The already-
proven merge algebra rides on top. The document is not a new subsystem — it is the composition
algebra given a real carrier and a real hash, with the web as its backend.

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
references that stay verifiable. (`COLL_EMBEDS` leaf: designed, unbuilt — a foundation deliverable.)

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

The foundation is the **soundness core in Lean, exported**, that makes composition *type* and *not
forge*. Everything rich (marks, vocabularies, the editor, live transclusion push) is downstream and
**deliberately deferred** — the DDL design says to let it emerge from authoring real documents on a
small sound core, and the audit says the rich work currently sits on undischarged assumptions.

The audit found every document defect is one mistake — **the Lean is a shadow of the Rust, so the
proof is about a model, not the thing.** The foundation kills the shadow-gap by construction. Four
pieces, each a Lean `@[export]` over canonical bytes (batched — the FFI is not per-node; §4):

**F1 — The composed carrier + product-of-pushouts.** `DocMerge.lean` proves `merge_is_lub`/
`isPushout` over a SINGLE `DocGraph` (`AtomId := Nat` local to one graph). A composed document is a
**family of DocGraphs indexed by CellId** — a parent layout graph + a `CellId → DocGraph` map of
children, each independently owned (matching `composition.rs::merge_composed`). Define `ComposedDoc`
+ `mergeComposed` (componentwise `merge`) in Lean and LIFT the single-cell theorems to the product:
`mergeComposed_is_lub`, `mergeComposed_isPushout` (product of per-cell pushouts is a pushout), and
**the boundary lemma** — a child-content edit and a layout edit can never conflict, because their
carriers are DISJOINT components (§1.2 made a theorem). The algebra is content-agnostic (Lane 2 proved
nothing strains), so this is a lift, not a new merge. NOTE (corrected from an earlier draft): the
cross-cell identity here is the family INDEX (`CellId`); `AtomId` stays LOCAL per cell. A *global*
`(CellId, AtomId)` id is a DOWNSTREAM refinement needed only for atom-RANGE transclusion (quoting
specific atoms inside another cell), not for whole-cell composition.

**F2 — Real-hash commitment binding the pointer AND the alternatives.** `commit` today rides a
non-cryptographic `DefaultHasher` outside `--features substrate`. Write `commit` in Lean over
**Poseidon2** (via `@[extern "dregg_poseidon2_2to1"]` — the fast Rust primitive at the leaf,
`Storage/Deployed.lean`'s idiom), binding: the atom's type+content+provenance; for an embed, the
`ChildRef` pointer (`COLL_EMBEDS`); **and for a conflict, BOTH live alternatives + their provenance**
— that last is **conflict-as-state soundness**: without it, a light client can be shown a two-branch
conflict hiding a *forged* alternative (the seven-forgery-bugs shape, in the document layer). Export
`commit`. `HInj` discharges from Poseidon2-CR, not sitting un-invoked.

**F3 — The anchored quote/embed verifier.** `TranscludedField::include()` calls `AttestedResource::
verify()` — content-hash + receipt-stream + a **structural quorum count**, NOT signature
verification; the real gate `verify_anchored(committee)` exists and is **never called** ("cannot
tell a fabricated root by a committee it does not trust"). This is a **live hole** on the path whose
whole job is verifying a peer's bytes. Write the anchored verifier in Lean (signature + committee),
export it, and put it **on the `include()` path**. The hole closes by construction, not by
remembering to call the right function.

**F4 — The module-layering + the doc differential retirement.** Structure the core as the wasm
discipline demands (§4): `DocCore` (Init-only, `UInt64`/BabyBear, `@[export]`) + `DocProofs`
(imports `DocCore` + Mathlib, proves F1–F3, **off the wasm import path**). Wire the Rust `dregg-doc`
+ the `<dregg-doc>` wasm to call the exported core. This is the piece that makes `<dregg-doc>`'s
in-tab executor *the proven core*, retiring the shadow.

**Honest carriers (named, at the floor — same as the circuits):** Poseidon2 collision-resistance,
signature unforgeability. Which committee to trust is a *policy*. `Pin::Live` vs coordination-
freedom is a *semantics decision* (a live cross-cell read is provably not i-confluent), not a proof
gap — proposed default: `Pin::Live` for render, `Pin::At(receipt)` snapshot for anything entering a
commitment. **Not assumed; a call to make.**

---

## 3. The as-built ledger (why the foundation is shaped this way)

**PROVEN in Lean (`#assert_axioms`-clean):** merge comm/assoc/idem/total, `merge_is_lub`,
`merge_isPushout` — but **in the thin/preorder category over `AtomVal := Status` (liveness bits
only)**; the full labelled patch category `P` is a named residual. Conflict-as-first-class-state
(`merge_has_conflict`), two-regime `prose_iconfluent`/`field_not_iconfluent`, stitch=pushout,
settlement soundness (non-tautological via `deployedSettle`), non-amplification
(`reshareN_attenuates`, `surfaceConfersExactly`, `transclusion_no_amplify`).

**PROVEN but weaker than its name:** `Transclusion.lean` is `def Transclusion := ImportedEq`; its
keystones are renamings. The anti-forge (`transclusion_forge_refused`) rests on `stateAt : Receipt →
Value` being an **abstract total function** — a receipt determines a value *by model construction*.
It refuses "different value for the same cited receipt"; it says **nothing** about fabricating a
receipt. `HInj`/`HFresh` (collision-resistance) exist and are **not invoked** by any transclusion
keystone. **The non-forgeable quote is not proven.** (F2/F3 close this.)

**TESTED-in-Rust only, single-instance, under a TOY hash:** the merge "laws" in `tests.rs` are
examples over a fixed 3-graph fixture (∀-proof lives in Lean); `commit` anti-forge tests ride
`DefaultHasher`; per-viewer darkening (real + specific). **Live hole:** `include()` does structural
quorum, not `verify_anchored`.

**Named seams / holes:** receipt-id ↔ patch-id (uncrossed); `DefaultHasher` outside `--features
substrate`; `AtomId` single-graph (the `(cell,atom)` HOLE); `Embed`/`Transclude` absent from the
core atom sum; the `COLL_EMBEDS` leaf + substrate `NamespaceResolver` (designed, unbuilt); the full
patch category `P`; the leptos reactive (push) transclusion.

**What composition newly makes load-bearing:** cross-cell identity (F1); cross-cell commitment
binding (F2); the crypto that a self-authored cell could ignore but a *peer-verified quote* cannot
(F2/F3). **Composition is precisely the thing that makes the un-discharged assumptions matter** —
which is why the foundation is the soundness core, not a document IR.

---

## 4. How the core reaches the tab (the wasm-Lean discipline — PROVEN this session)

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

1. **F1 — cross-cell `AtomId` in Lean** + re-prove `merge_is_lub`/`isPushout` over the composed
   carrier. (Unblocks the type-level existence of a composed document.)
2. **F4a — the `DocCore`/`DocProofs` module split** + a minimal `@[export]` `atom_id`/`commit`
   compiling to wasm at the 677 KB floor (prove the discipline on the real core, not a probe).
3. **F2 — `commit` in Lean over Poseidon2**, binding pointer + conflict alternatives (conflict-as-
   state soundness). Retire the `DefaultHasher`.
4. **F3 — the anchored verifier in Lean, on the `include()` path.** Close the live hole.
5. **F4b — wire `dregg-doc` (native) + `<dregg-doc>` (wasm) to the exported core.** Retire the shadow.
6. **Then** the rich layer — marks, vocabularies, the editor, live-embed push — *emergent from
   authoring real documents on the sound foundation.* A follow-on spec, deliberately not now.

**Guiding-star check for every agent:** does this piece keep §1.1–1.5 true? (boundary-not-bytes;
composition-factors-merge; the universal surface shape; committed indirection; structure-is-cells.)

---

*The soundness is done for a single cell over liveness bits. The foundation gives it a real carrier,
a real hash, and a closed verifier — and puts the proven core in the tab. Then, and only then, the
document gets to become rich, on ground we have actually checked.*

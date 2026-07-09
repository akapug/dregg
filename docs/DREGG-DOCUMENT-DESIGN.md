# DREGG DOCUMENT — the design

*The document language and its rendered IR, designed to the ambition: verifiable rich text **and**
code, authenticated **live** transclusion at fragment identity, conflict as first-class renderable
state, real-time collaboration **and** reviewed landing, AI-authorable-and-checkable hypermedia.*

**This is a design document, not an as-built description.** §7 states precisely what is banked
today and what is to be engineered. The distance between them is the program, not a caveat.

---

## 0. The thesis

A dregg document is **a typed graph of provenance-carrying atoms**, edited under **two explicitly
separated regimes**, rendered through **a document IR with stable node identity**, and quotable
**at atom identity with a live, authenticated reference.**

Every existing system has some of this. None has all of it, because none has a verified substrate
underneath — and *that* is the part we already own.

---

## 1. The two regimes (the organizing insight)

Collaborative editing has two fundamentally different modes, and conflating them is why every
existing tool is bad at one of them:

| | **CO-TYPING** (live) | **LANDING** (reviewed) |
|---|---|---|
| the question | "we are typing in the same paragraph right now" | "this change is proposed against that document" |
| correct behavior | concurrent same-region edits **interleave** | a change **lands or conflicts**, visibly |
| the math | a CRDT sequence (RGA / Fugue) | patch algebra, merge = categorical **pushout** |
| identity | per-character/element, causally ordered | per-atom, content-addressed, tombstoned |
| what a conflict is | *impossible by construction* (interleave) | **first-class carried state** with authored resolutions |
| the artifact | a live shared buffer | a **proven patch**, receipted |

Google Docs has co-typing and no real landing. Git/Pijul have landing and no co-typing. **dregg has
both, separated by an explicit `Regime`, sharing one atom identity and one verification story.** You
co-type inside a region; you *land* a change across a boundary; the same document carries both, and
the receipt chain proves what happened either way.

This separation is the design's spine. The CRDT layer sits **under** the atoms; the patch algebra
sits **over** them.

## 2. The typed atom (the one concentrated re-foundation)

Today `Atom.content: String` — a flat sequence of opaque strings. That single field is the root
cause of every rich-media gap. It becomes a typed sum (the shape `composition.rs` already rehearses):

```
AtomContent =
  | Text(Run)                       -- a text run, the CRDT-sequenced leaf
  | Block(kind, children)           -- section, para, list, item, table, cell, quote
  | Code(lang, tokens)              -- code as structure, not "text lines"
  | Media(ref)                      -- image, canvas, embed by content-addr
  | Embed(ChildRef)                 -- a nested document
  | Transclude(AtomRange, prov)     -- an authenticated live quote (§5)
```

Threaded through `content` / `walk_atoms` / `diff` / `merge` / `commit` / `render`. Bounded, and it
unlocks structure, marks, code, and media at once.

**Marks are NOT baked into content.** Inline formatting is a **non-destructive mergeable range
overlay** (Peritext / Automerge-marks): `Mark{range: AtomRange, kind: Bold|Link(uri)|Code|…}`, merged
independently of the text it spans. This is the only sound way to get bold/link/code-span that
survives concurrent edits — bake a mark into bytes and every concurrent edit re-mints and destroys it.

**Structure is a block+inline tree** (ProseMirror/Notion shape) so reparenting a list item, splitting
a paragraph, or merging table cells is a *structural* merge, not a line-antichain accident.

**Identity survives editing.** Today `Alive|Dead` is too coarse: an in-line edit re-mints the atom, so
blame churns and two authors editing *different halves of the same line* spuriously conflict. Adopt
Pijul's **byte-interval atoms + a richer status lattice** (zombie / pseudo-edge) so **split, join,
and true move preserve atom identity** — the prerequisite for real blame, real moves, and
non-spurious conflicts.

## 3. Conflict as first-class, all the way up

This is already real in the core (`resolutions_for` yields *authored patches* that provably collapse
the conflict; a clean doc yields an empty menu; both polarities tested). The design extends it:

- **Nested conflicts** and **conflicts inside structure** (two authors restructure the same list).
- The resolution menu carries the **base column** (what it forked from), not just the two branches.
- More gestures than keep/order: *interleave, take-both-as-siblings, promote-to-conflict-block*.
- **Authoring must not stop at a fork.** Today `Doc::text()` halts at the first conflict, silently
  dropping the document's entire tail. A document with an unresolved conflict must remain fully
  readable, editable, and quotable *past* it. Conflict is a **local** state, not a wall.
- **`Conflict` is an IR node** (§4), not CSS positional trickery.

## 4. The Document IR (a sibling to `ViewNode`, not a stretch of it)

`ViewNode` is a genuinely good **control-panel / reflective-inspector IR** — `u64` binds, `{turn,i64}`
affordances, positional nodes. It stays exactly that. Documents get their own IR, because three of
ViewNode's load-bearing assumptions are structurally wrong here (scalar values, identity-free nodes,
string-leaf text) and cannot be patched away.

```
DocNode =
  | Atom{ id, provenance, content, marks }      -- stable id: the atom's own identity
  | Block{ id, kind, children }
  | Conflict{ id, base, alternatives: [Branch{ author, atoms }] }
  | Transclude{ id, src: AtomRange, provenance, trust_tier, resolved }
  | Code{ id, lang, tokens, provenance }
  | Media{ id, ref, provenance }
```

Three properties `ViewNode` cannot have, and this must:

1. **Stable node identity.** Nodes are keyed by atom id → the renderer applies **patches
   incrementally** through a **keyed reconciler**, preserving focus, selection, scroll, and IME.
   (Today's renderer is `innerHTML =` or a regex hack — the reason an editor is impossible.)
2. **Provenance and trust are IR-native.** Every node carries who authored it in which proven turn;
   every `Transclude` carries its resolved provenance **and its trust tier**. Honest trust labeling
   stops being a boundary concern and becomes a *property of the node*.
3. **Conflict is a node.** It renders as itself — both live alternatives, with their authors — and
   its resolution gestures are affordances.

**The affordance model must grow with it.** `{turn: String, arg: i64}` cannot express "insert this
text here" or "apply this mark to that range." The document IR requires **string-valued binds** and
**typed, structured turn arguments**. This is the same lack that makes forms, search boxes, and
editors inexpressible today — it is a substrate fix, not a document nicety.

## 5. Transclusion at atom identity, and actually live

What exists is excellent *verification* — a real Xanadu EDL where each quoted span resolves through
content→commitment→receipt→receipt-stream-root→quorum, with byte-range granularity, unbreakable
links (amend the source, the quote re-resolves and cites the new receipt), per-viewer darkening
through the Membrane (provenance kept, bytes withheld, never forged), and tampering refused. Keep
all of it.

Two changes make it the thing the ambition names:

**(a) Address atoms, not bytes.** Today the byte-span document (`deos-web-cells`) and the atom/patch
document (`dregg-doc`) are **disjoint crates with no shared model**, so a quote cites the *source
cell's whole receipt* — the fragment's own lineage does not travel. Unify them: a `Transcluded` span
addresses an **`AtomRange` of a patch-document by id**. Then:
- the quote carries the **fragment's atom-level provenance** (who authored *these* atoms, in which turn),
- it updates **structurally** when the source is edited (not "bytes 11..20 moved"),
- it can quote *across a conflict* and show that it is quoting a contested region,
- and it composes: a transcluded atom is still an atom.

**(b) Live means push.** Today `resolve()` is pull; `LiveDomSnapshot` is a snapshot. Add a **reactive
liveness layer**: subscribe to a source atom-range; on the source's finalization, **invalidate and
re-resolve**, re-verifying the chain. A live transclusion is then a *standing verified subscription*,
and the DOM element re-renders when its source truly changes.

This is Nelson's transclusion with **forces**: authentic, fragment-identified, live, and
provenance-carrying — quotable across documents, cells, and federations.

## 6. Verifiability, closed all the way down

The commitment already binds provenance in its preimage, with a tested anti-forge tooth (mutate an
alternative's author → the commitment changes, even with byte-identical rendered text). Under
`--features substrate` it's sorted-Poseidon2 over the real cell heap, and a patch drives a cap-gated
turn leaving a receipt. Finish it:

- **Cross-check receipt-id ↔ patch-id.** Today it is a *named seam*: two witnesses that don't yet
  refer to each other. **A patch IS its turn** — bind them so a stranger verifying the receipt has
  verified *that patch*, and the document's history and the ledger are one object.
- **One real hash.** The standalone `commit`/`AtomId::derive`/`Patch::id` use a non-cryptographic
  `DefaultHasher`. The substrate path already has Poseidon2. There should not be a "toy identity"
  mode that a document could accidentally be authored under.
- **Author is an identity, not a `u64`.** Bind it to the cell/capability identity so "who wrote this
  atom" is a claim a stranger can check, not a label.
- **AI authorship gets a schema.** With a typed document, a proposed patch is validated against the
  document's *shape* — not merely "it is a well-formed patch." An AI's edit is checkable in kind, not
  just in form.

## 7. What is banked, what is to build

**Banked (do not rebuild):** the patch algebra (atoms, tombstones, order-edges, additive union
merge) with its laws *tested as equalities* including `branch_then_stitch_is_the_pushout`;
conflict-as-first-class with authored `resolutions_for` (both polarities tested); blame; three-way
diff3; the commitment + anti-forge tooth; the entire transclusion **verification** chain; per-viewer
darkening; forge-refused.

**Bounded refactor:** the typed atom (§2) threaded through the core. `composition.rs` is the dress
rehearsal — it already names `AtomContent::{Text,Embed}` "the production shape."

**Net-new subsystems (the real distance, and worth it):**
1. **Mergeable marks** (Peritext-style range overlays).
2. **The CRDT co-typing regime** (RGA/Fugue under the atoms) + the explicit `Regime` split (§1).
3. **The Document IR + keyed reconciler** (§4) — and with it, string binds + structured turn args.
4. **Reactive liveness** for transclusion (§5b) + unifying the two document worlds onto atom identity (§5a).

**Seams to close:** receipt↔patch correspondence; one real hash; author-as-identity; authoring past a
conflict.

## 8. Build order

1. **Typed atom** (§2) — everything hangs on it. Land `AtomContent` in the core; thread it through
   diff/merge/commit/render; keep every existing law green.
2. **Document IR + keyed reconciler** (§4) — stable ids, incremental patch application, provenance +
   trust IR-native, `Conflict` as a node. This is what makes an editor *possible*.
3. **String binds + structured turn args** — the substrate fix the IR needs (and forms/search need).
4. **Marks** (Peritext overlays) + **block/inline structure**.
5. **Interval atoms + status lattice** — split/join/move preserving identity; kill spurious
   same-line conflicts.
6. **Unify transclusion onto atom identity** (`deos-web-cells` depends on `dregg-doc`) + **reactive
   liveness**.
7. **CRDT co-typing regime** + the `Regime` classifier.
8. **Close the seams** (receipt↔patch, real hash, author identity, authoring past a conflict).

Each step is verifiable against the existing tested laws; none of them requires discarding the
soundness already banked.

---

*The soundness is done. What remains is to give it a document worth being sound about.*

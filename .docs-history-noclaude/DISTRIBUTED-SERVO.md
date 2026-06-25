# DISTRIBUTED-SERVO — the distributed web-of-cells: Servo wrapped across the dregg federation

*Design frontier doc. Present-tense where the dregg side is real (the surface/
shell/cap model, the netlayer + sturdy refs, the attestation primitive, the
firmament distance parameter all ship today); clearly-scoped frontier where it
isn't (the libservo embed behind the cap gate, the per-DOM-node mediation, the
seL4 renderer PD). First-principles, no trajectory narrative. Companion to
`docs/EMBEDDED-WEB-SURFACE.md` (the single-node Servo-`WebView`-as-cap-surface
this EXTENDS to the distributed case), `docs/STARBRIDGE-V2.md` (the native shell
whose `SurfaceCapability` + cap-first discipline this reuses), `docs/DREGG-DESKTOP-OS.md`
(the verified-scene compositor teeth + attested user-volition), `docs/FIRMAMENT.md`
(the distance-parameter `n` model this whole doc walks along), `docs/design-frontiers/ADOS.md`
+ `docs/design-frontiers/AGENT-SWARM-UX.md` (the agent seam + cockpit), and
`docs/galaxybrain-dregg.md` (the sovereign-cell history model).*

> **This EXTENDS `docs/EMBEDDED-WEB-SURFACE.md` to the distributed case.**
> That doc opens a Servo `WebView` as a **single-node** `SurfaceCapability` cell:
> the browser is a guest the OS bosses around, its fetches/navigation/new-window/
> permission/auth are mediated `WebViewDelegate` callbacks (the embedder's impl
> IS the cap gate), and the trusted-path origin chrome is drawn by the shell from
> the live ledger so a page cannot paint its own address bar. Everything there is
> *local* — render, display, authority, and ledger sit on one machine (`n = 1`).
>
> This doc takes the next hop: **slide the pieces apart across the dregg
> federation.** The link a page follows is no longer a hostname but a sturdy ref
> into a *remote* cell; the fetch resolves over CapTP through a netlayer instead
> of a socket; the people co-present on a surface, the agent driving it, the node
> that renders it, and the glass that displays it can each sit on a *different*
> node. The single structural move that makes this coherent rather than a pile of
> new subsystems: **the firmament already parametrizes the distance between a
> capability's authority and its use by one integer `n`** (`sel4/dregg-firmament/
> src/lib.rs::Bounds { revocation_immediate, commit_synchronous, n }`), and the
> distributed web-of-cells is reached by *relaxing those bounds*, never by
> inventing a transport or a second authority model. `EMBEDDED-WEB-SURFACE.md` is
> the `n = 1` slice of this doc.

---

## 0. The one-paragraph thesis

On the open web a **link is a location** (`https://host/path`): you trust DNS to
find the host, TLS to authenticate the *channel* to the host, and then you trust
whatever bytes the host hands back, rendered on a machine you also trust, by an
agent whose only record of what it did is its own narration. The distributed
web-of-cells replaces every one of those trusts with a capability and a receipt.
**A link is a `dregg://` / `ocapn://` sturdy ref into a specific cell on a
specific federation** (`captp/src/uri.rs::DreggUri`, `captp/src/netlayer.rs::
ocapn_uri::OcapnSturdyRef`) — not a place but a bearer capability whose swiss
number *is* the authority. **A fetch is a verified turn**: the embedded surface's
`load_web_resource` intercept (`EMBEDDED-WEB-SURFACE.md` §2) does not hit a
socket — it dials the hosting node over a netlayer (`Netlayer::dial`), enlivens
the swiss against that node's `SwissTable`, runs a cap-gated serve-turn, and
returns **attested content** whose hash the origin cell's quorum-finalized state
root binds (`types/src/lib.rs::AttestedRoot` + `merkle_root_of_receipt_hashes`),
so the in-tab light client (`wasm/src/bindings_lightclient.rs::verify_history`)
can check *the page is the page the origin committed* — from any source, online
or via a sealed relay when the origin is offline. On top of that one fetch model,
the same `SurfaceCapability`/cell/turn machinery carries three more dimensions of
distribution, each the same `granted ⊆ held` gate at a different scale: **multiple
parties co-present on one surface**, each holding an attenuated, revocable,
receipted cap to a DOM region (`Shell::share` recursed into the page, the
compositor's region-set recursed below the window); **an agent driving the
surface** through the one ADOS seam (`starbridge-v2/src/swarm.rs::Swarm::run`),
so every nav/click/fetch/submit is a metered, cap-gated turn that leaves a
tamper-evident blocklace receipt and a runaway is *refused at the gate, not logged
after the drain*; and **the render node and the display node slid apart along
`n`**, so a tab can be rendered where the computrons are and displayed where the
glass is, the frame Ed25519-attested to the cell's committed root, rendering
priced as a Stingray-bounded metered service (`coord/src/shared_budget.rs`). The
honest floor throughout, stated and never laundered: dregg mediates and records
**authority, effect, and content-commitment** — verified; it does not verify the
*semantics* of a page, the last-hop pixels a panel actually scans out (the
graphics F1 floor), or the TLS provenance of bytes a legacy server served — each
a named seam with a named closure lever (an upstream Servo ask, a golden
extractor, the trusted-path compositor, the seL4 broker PD), and the
network-level anti-spoof story *reduces to the same light-client unfoolability
theorem the protocol already proves* (`AssuranceCase.lean::unfoolability_guarantee`)
rather than adding a new assumption. **dregg does not browse the web; it federates
it.**

### The one model, four dimensions of distance

Every section below is the *same* `SurfaceCapability` over a backing cell, with a
different pair of endpoints slid apart across the federation and the firmament
`Bounds` relaxed accordingly. This is the spine; read it once and the four
sections are one idea:

| dimension | what slides apart | the firmament walk | §1 EMBEDDED-WEB-SURFACE was… |
|---|---|---|---|
| **the link / the fetch** (§1) | the *page's origin* moves to a remote cell; the fetch crosses the wire | `Surface{cell}` whose backing is a `Distributed{cell}` on another node | the body filled from a local `WebView`, origin local |
| **co-presence** (§2) | the *parties* sharing a surface sit on different nodes | each holder's cap is `Bounds::distributed(n)`; revoke is one-hop | one local user, one local shell |
| **provable + agent-driven** (§3) | the *driving loop* sits above dregg; the history is a federated blocklace | the agent's turns are `Swarm::run` over the surface cell; history anchors to the federation | one local operator, no audit trail beyond the cell |
| **render / display** (§4) | the *render node* and the *display node* are different machines | `Surface{cell}` whose backing (render) and whose display sit on different nodes | render and display on one box, present synchronous |

The unifying sentence: **`Local{slot}` → `Distributed{cell}` → `Surface{cell}` →
each of these four cases is one more point on the firmament's distance parameter
`n`, reached by relaxing `Bounds`, with the capability semantics held fixed.**

---

## 1. The web-of-cells — a link IS a sturdy ref, a fetch IS a verified turn

This is the foundation the other three dimensions stand on. `EMBEDDED-WEB-SURFACE.md`
§1 makes a web surface a `SurfaceCapability` whose body is a local `WebView`'s
output; this section makes the *origin* of that body a remote cell, and the fetch
that reaches it a verified turn over CapTP.

### 1.1 The link denotes a remote cell — not a location

A web link in this world is one of the two OCapN shapes dregg's netlayer already
parses and bridges to its native sturdy shape (`netlayer.rs::ocapn_uri`,
`OcapnSturdyRef::from_dregg` / `to_dregg`, round-trip tested):

| link form | denotes | dregg primitive (shipped) |
|---|---|---|
| `dregg://<fed>/<cell>/<swiss>` | a bearer cap into `cell` on federation `fed`; authority = whatever `swiss` enlivens to | `uri::DreggUri` (parse/format) |
| `ocapn://<designator>.<hint>/s/<swiss>` | the OCapN-native spelling of the same; `hint` names the netlayer (`tcpip`/`relay`/`onion`/`inproc`) | `ocapn_uri::OcapnSturdyRef` (parse/format/bridge) |
| `ocapn://<designator>.<hint>?host=…&port=…` | a **machine locator** — a node, not a cell (the federation's bootstrap object) | `ocapn_uri::OcapnLocation` (with reachability params) |

The design fact already true in the code: the **`hint` carries the netlayer** and
reachability rides as query params (`OcapnLocation.params`), so a link is
self-describing about *how to reach the federation* without a global name service
— the link is the locator. Because the swiss number *is* the authority (possession
= authorization, `captp/src/lib.rs` trust model), a `dregg://` link is
simultaneously the address *and* the access grant: there is no separate "log in."
Attenuation is native — `SwissTable::export_with_options` (`captp/src/sturdy.rs`)
mints a swiss entry with an `EffectMask`, an `expires_at`, and a `max_uses`, so a
link pasted into a chat is a `max_uses: Some(1)`, one-hour, read-only facet of
your cell: the ocap answer to "anyone with the link can edit forever."

> **The bearer-secret seam (named, with its lever).** A bearer link in a URL bar
> leaks — through referrer headers, history, shoulder-surfing, logs. dregg bounds
> this with shipped levers rather than hand-waving: (1) `max_uses`/`expires_at`
> shrink the capture window; (2) the **handoff path** (§1.3) replaces "paste a
> swiss" with a recipient-targeted, signed, nonce-once certificate
> (`handoff::HandoffCertificate.recipient_pk` + `register_handoff_nonce`) so the
> link is useless to anyone but the named recipient — the *recommended* primitive
> for anything sensitive, with the URL-bar swiss as the convenience tier; (3)
> `EnlivenError::opaque_message()` (`sturdy.rs`) collapses the enliven-failure
> taxonomy at the wire so a stolen-and-expired link cannot be used as a
> **membership oracle** on the swiss table. A tiered defense, not a wall.

### 1.2 The fetch path — `load_web_resource` → a remote-cell turn returning attested content

This is the heart. When the Servo `WebView` issues a network load for a
`dregg://`/`ocapn://` resource, the `WebViewDelegate::load_web_resource` cap gate
(`EMBEDDED-WEB-SURFACE.md` §2) does **not** continue to a socket — it `intercept`s
and resolves the load through the federation. Each hop names its shipped primitive:

```
page fetch dregg://F/C/swiss
  │
  ▼ [1] load_web_resource intercept  (WebViewDelegate — the EMBEDDED-WEB-SURFACE §2 cap gate)
  │     parse → OcapnSturdyRef::to_dregg → (F, C, swiss)
  │     discharge the SURFACE macaroon's fetch-caveat against F  (EMBEDDED-WEB-SURFACE §3)
  │          — refuse HERE if the tab's cap doesn't permit reaching F
  ▼ [2] resolve the locator → dial the hosting node
  │     Netlayer::dial(addr_for(F))  →  NetSession{ captp, conn }     (netlayer.rs:238)
  │     (hint picks the wire: tcpip / relay / onion / inproc; params give host:port)
  ▼ [3] enliven the swiss over the session
  │     present swiss → node runs SwissTable::check then enliven       (sturdy.rs)
  │          → SwissEntry{ cell_id, permissions, allowed_effects, … }
  │     (no double-spend of the introducer's budget: check-then-enliven)
  ▼ [4] invoke the cell's "serve this resource" method as a VERIFIED TURN
  │     pipeline::PipelinedAction on the remote cell                   (pipeline.rs)
  │     → the node executes a cap-gated turn → leaves a RECEIPT
  ▼ [5] node returns an ATTESTED RESPONSE  (the one new wire object, §1.2.1)
  │     { content_bytes, content_hash, receipt_hash,
  │       AttestedRoot{ receipt_stream_root, quorum_sigs, blocklace_block_id, finality_round },
  │       merkle_path(receipt_hash → receipt_stream_root) }
  ▼ [6] CLIENT-SIDE verification BEFORE the bytes reach the renderer
  │     a. content_hash == blake3(content_bytes)               — content-addressed
  │     b. receipt binds content_hash                          — the turn served THIS content
  │     c. merkle_path proves receipt_hash ∈ receipt_stream_root  (merkle_root_of_receipt_hashes, types/src/lib.rs:357)
  │     d. AttestedRoot quorum-verifies (Ed25519 count ≥ threshold, or ThresholdQC)  (types/src/lib.rs)
  │     e. (optional) light-client fold over the cell's turn chain  (verify_history, bindings_lightclient.rs)
  ▼ [7] WebResourceLoad::intercept(content_bytes)  — hand the VERIFIED bytes to Servo
        on ANY check failing: intercept with a visible "dregg: unattested content" body, never render
```

The shape is uniform with the rest of dregg: **a fetch is a verified turn that
leaves a receipt, and the receipt is the attestation.** The browser is a *light
client of the origin cell's federation.* This is categorically different from TLS:
TLS authenticates the *channel to a host*; this authenticates the *content against
the origin's committed state, checkable by a third party who was never on the
channel* — which is exactly what makes a cached, relayed, or mirrored copy as
trustworthy as a direct fetch (it carries its own proof), and is the property §2,
§3, and §4 all reuse.

#### 1.2.1 The `AttestedResource` envelope — the one new wire object, every field shipped

The only genuinely new artifact is the envelope the node returns at hop [5]:

| field | what it proves | shipped primitive |
|---|---|---|
| `content_bytes` | the page body | — |
| `content_hash: [u8;32]` | content-addressing; the body self-certifies | blake3 (the receipt-tree hash family, `types/src/lib.rs`) |
| `receipt_hash: [u8;32]` | a specific verified turn served this | `receipt_hash()` (types) |
| `merkle_path` | `receipt_hash ∈ receipt_stream_root` | `merkle_root_of_receipt_hashes` is the verifier (`types/src/lib.rs:357`) |
| `attested_root: AttestedRoot` | the federation finalized that receipt stream, quorum-signed + blocklace-bound | `AttestedRoot` + `receipt_stream_root` + `ThresholdQC` (`types/src/lib.rs:281`) |

**The binding that makes it "the page the origin committed":** the served turn's
receipt commits the post-state of the origin cell, and the resource's
`content_hash` is a field of (or derivable from) that committed state. Verifying
the chain `content_bytes → content_hash → receipt → receipt_stream_root →
quorum-signed AttestedRoot` proves the origin **cell**, under the federation's
finality, published exactly these bytes.

#### 1.2.2 Two honest seams in the fetch path

- **The serve-method must commit the content hash.** For the attestation to bind,
  the origin cell's serve-turn must write `content_hash` into committed state (so
  the receipt covers it). This is a **cell-program convention**, not yet a kernel
  primitive: a "web-served cell" is one whose program, on a serve-method, records
  the served blob's hash in a receipt-covered slot. The lever: an *app-toolkit
  template* (`ServedResourceCell`), the same way `NameserviceGated.lean` is a
  template — buildable now on the existing effect set (`setField` of a
  content-hash slot is already a class-A effect). Named as the convention to
  standardize, with the template as the lever.
- **Liveness/freshness vs the dialed node.** Hops [2]–[3] dial *a* hosting node; a
  Byzantine or stale node can withhold (a liveness fault — try another node /
  relay, §1.4) or serve a stale-but-validly-attested copy (an old finalized root).
  A stale copy is *detectably* stale: `AttestedRoot.finality_round` is monotone,
  so the client demands "≥ the round I last saw" or folds `verify_history` to the
  current head. **Freshness is a client policy over an existing monotone field**,
  not a missing mechanism. Equivocation (two finalized roots at one height) is
  exactly what the blocklace equivocation detection already catches (§3.2).

### 1.3 OCapN / Goblins interop + the link's distributed lifecycle

**Interop is ~90% wired** because dregg's netlayer *was built as an OCapN netlayer*
(`netlayer.rs` module docs: "adopts the netlayer design from Spritely Goblins /
OCapN"). A Goblins peer's locator is a valid web-of-cells link and vice versa; a
Goblins peer fetching `ocapn://node.hint/s/<swiss>` lands in `SwissTable::enliven`
(shared swiss-bearer E-lineage); the OCapN `desc:handoff-give/receive`
certificates ↔ `HandoffCertificate` (`handoff.rs`) are both signed,
recipient-targeted, nonce-once introducer certs — so **one cell links another
cell's page to a third party** by signing a `recipient_pk`-bound cert the
interceptor cannot use. The **remaining adapter** (`netlayer.rs` §"Goblins-interop
adapter", scoped 2–4 weeks): a shared concrete wire, the Syrup codec (OCapN frames
are Syrup records, not postcard), and the `op:start-session`/`op:deliver`/
`op:gc-export` descriptor mapping — **one more `impl Netlayer` plus a codec shim,
the trait unchanged.** A bounded, named artifact on a shipped abstraction, not
research. The payoff: the link scheme is the *federation's*, not dregg's.

The link's **lifecycle** is sound, not just its resolution:

- **A live link holds a distributed reference.** Enlivening `dregg://F/C/swiss` is
  an import on the client's session and an export the hosting node's
  `ExportGcManager` records (`captp/src/gc.rs`); closing the tab sends a
  `DropRef`; at zero refs the node may reclaim. "How many live browsers hold this
  page open" is a real, GC'd export refcount — and the red-team session-free
  premature-reclaim hole on exactly this path is already closed (task #112).
- **Revoking a shared link is `SwissTable::revoke`** (`sturdy.rs`): un-publishing a
  page makes every subsequent `enliven` return the opaque denial and breaks every
  live session's next call — link revocation with teeth, which the open web lacks.
- **Epochs prevent stale-session confusion.** `EpochMinter` (`netlayer.rs:255`)
  mints a strictly-higher epoch per redial and `CapSession::epoch` rejects stale
  messages, so a browser reconnecting after the origin rotated keys cannot be fed
  old-epoch replays.

### 1.4 Trustless mirroring — Willow range-reconciliation over the receipt stream

The web-of-cells wants distributed content sync: many nodes mirroring a cell's
pages, browsers pulling from the nearest replica, offline-first caches that
re-converge. Willow's **range-based set reconciliation** (two peers exchange
`fingerprint(range)`; equal → done; unequal → split and recurse) is the right
primitive, and dregg has the substrate it needs:

- **The set to reconcile is the receipt stream.** Each origin cell's published
  content is its sequence of serve-turn receipts, and `merkle_root_of_receipt_hashes`
  (`types/src/lib.rs:357`) is *already* a balanced, domain-separated BLAKE3 Merkle
  tree over `receipt_hash`es with deterministic canonical order. A Willow range
  fingerprint over a sub-range is a partial-tree digest of exactly this structure.
- **Sync from a stranger is sound** because §1.2.1's envelope carries its own proof
  — a node pulls a page from *any* peer (a CDN-like mirror, a neighbor, a relay)
  and verifies it locally without trusting the source. Willow distributes the
  *bytes*; the attestation makes the distribution *trustless*. This is what lets
  §1.2.2's "try another node on withholding" scale to a real replica mesh.
- **The transport is the netlayer**: reconciliation runs as `pipeline` calls over a
  dialed session — `relay` for offline/async convergence, `tcpip`/`onion` for live
  sync. Willow's namespace/subspace/path maps onto `(federation_id, cell_id,
  receipt-stream-range)`, and a sync peer only reconciles ranges its enlivened cap
  permits (the `EffectMask`/read-scope of its sturdy ref).

> **Honest scope on Willow.** dregg has **no Willow implementation today** (zero
> `willow`/`range_reconcil` in the tree). What ships is the substrate that makes
> it a bounded build: the canonical-ordered receipt-stream Merkle tree, the
> self-verifying envelope (§1.2.1), and the transport (`Netlayer` + `relay`). The
> work is the **range-fingerprint protocol** (split-and-recurse over the existing
> tree's leaf ranges) as a new `pipeline` conversation — a defined algorithm over
> shipped data structures, gated behind the headline fetch path. A bounded build
> on a real substrate, not research.

---

## 2. Co-presence — multiple parties over ONE cap-mediated web surface

Where §1 slides the page's *origin* across the federation, §2 slides the *parties*
across it. The thesis in one line: **co-presence is not a new subsystem — it is
`Shell::share` recursed INTO the DOM, the compositor's region-set recursed BELOW
the window, and every collaborative act made a receipted firmament turn.** No new
authority model; the keystone is that the one thing the open web cannot express —
"you may touch ONLY this field, observe but not drive, and I can take it back this
frame" — is exactly `granted ⊆ held` at a finer grain.

Two pieces of named substrate carry §2, so the seams are honest from the start:

- **The exterior-mediation invariant (the load-bearing premise for fine grain).**
  Per `EMBEDDED-WEB-SURFACE.md` §2/§4, dregg mediates a web surface from *outside*
  the page via `WebViewDelegate` and drives it via host→page `evaluate_javascript`;
  there is **no per-DOM-node delegate in Servo today** (`EMBEDDED-WEB-SURFACE.md`
  §2.1). So every per-element / per-region gate below is enforced at the embedder
  boundary — input is routed into the page only after the gate admits it, and
  DOM-region observation rides a **host-side privileged content-script injected via
  `evaluate_javascript` at document-start** (the `EMBEDDED-WEB-SURFACE.md` §4.2(2)
  path). This is strictly stronger than an in-page extension (it shares nothing
  with page JS) but it is a **named seam**: per-element granularity is only as
  sound as that shim honoring the region map, until a Servo DOM-region delegate
  exists (the upstream lever) or the seL4 `web-broker`/`renderer` split
  (`EMBEDDED-WEB-SURFACE.md` §5) makes it an address-space boundary. Call it the
  **DOM-region-mediation seam**; referenced below, never laundered.

- **The co-presence cell.** A co-presented surface is one `SurfaceCapability` over
  one backing cell (`starbridge-v2/src/surface.rs`), but its authority is now a
  **macaroon whose caveats name DOM regions, not just web powers** — the real
  `macaroon::ResourceSet<I, M>` (`macaroon/src/resource.rs`): a map from a typed
  resource id → an action bitmask, **intersection-only on stacking** (every caveat
  narrows; `resolve` intersects masks), with the type's `Default` id as wildcard.
  Instantiate `I = RegionKey` (a stable DOM-region / element / field id) and
  `M = DomAction` (a bitmask over `Observe | Nav | Click | Fill | Submit | Select`).
  That single generic — already proved to intersect-and-narrow — is the
  per-element capability lattice. The window cap answers *which surface*; this
  macaroon answers *which party may do what to which DOM region*, and
  `prohibits(region, action)` (`resource.rs:98`) is the gate.

### 2.1 Multiple holders of attenuated caps to one surface — per-DOM-region caps

The surface owner holds the root macaroon (full `DomAction` over the wildcard
region). Every other participant holds a **delegation** minted by `Shell::share`,
extended to carry a `RegionKey → DomAction` attenuation, never wider. Three
canonical roles fall out as caveat sets over the *same* surface cell:

- **Driver** — `{ * : Nav|Click|Fill|Submit|Select|Observe }` (the whole page, all
  actions); the owner's authority or a near-full delegation.
- **Read-only observer** — `{ * : Observe }` (every region, observe-only); the
  `None → Signature` narrowing of `surface.rs`'s own test, lifted to "every action
  bit cleared except Observe."
- **Scoped editor** — `{ #shipping-addr : Fill, #apply-coupon : Click }` and
  *nothing else* (no wildcard entry ⇒ `resolve` returns `None` for every other
  region ⇒ `prohibits` denies "resource not in set"). The case the open web has no
  vocabulary for, and it is *one `ResourceSet` literal*.

**Mechanism (every leg is existing code).** Minting a participant calls
`Shell::share(cap, recipient, narrower)` — the genuine `Effect::GrantCapability`
turn (`shell.rs::share` → `fabric.delegate` → real executor) — with `narrower`
extended from a scalar to `(AuthRequired, ResourceSet<RegionKey, DomAction>)`: the
firmament cap narrows on the `AuthRequired` lattice (drives *which window*: can
this party focus/move/close at all), and the **`ResourceSet` rides as the cap's
caveat payload** governing *which DOM regions*. The executor's `granted ⊆ held`
refuses a widening *window* share (`a_narrowing_window_share_commits_and_a_widening_
share_rejects` is green); the macaroon's monotone stacking refuses a widening
*region* share (`resolve` only ever clears bits). **Two independent
no-amplification gates compose** — firmament for the window, macaroon for the DOM.
Enforcing on input: a participant's keystroke/click does not reach Servo directly;
the shell receives it tagged `(participant_cap, RegionKey, DomAction)` (the
`RegionKey` resolved by hit-testing against the host-side region map — the
DOM-region-mediation seam), calls `prohibits`, forwards on `Ok`, and on `Err`
**refuses visibly** (the `ShellError::ShareDenied` posture). The granularity is
*recursive*: `RegionId` (window tiles, `compositor.rs`) and `RegionKey` (DOM
regions) are the same `granted ⊆ held` shape at two scales — the surface-region
model recursed into the DOM.

> **Seam.** Soundness of "ONLY this field" rests on the DOM-region-mediation seam:
> the shim must faithfully map clicks→`RegionKey` and prevent script-driven
> focus-stealing inside the page. Today's enforcement is at the input-dispatch
> boundary (strong: the event never reaches a disallowed handler) plus the shim's
> region map (the soft edge). The closure lever is the upstream Servo DOM-region
> delegate, or the seL4 `web-broker` split. Carried as work, with the lever named.

### 2.2 Screenshare-as-cap — a revocable read-only live VIEW

"Share my screen with you" is **minting you a `{ * : Observe }` macaroon over my
surface cell** — the read-only observer of §2.1, nothing new. The viewer's surface
is a *second* `SurfaceCapability` (a fresh `SurfaceId`) over the **same backing
cell**, exactly as `Shell::share` already produces; the viewer sees the live frame
because both surfaces composite the same cell's `source_state_root` /
`content_digest` (`compose_scene`), and every input they attempt is `prohibits →
Err`. **Revocation** is dropping the viewer's grant — `Shell::close` on the
viewer's surface (`closing_a_surface_kills_its_capability` is green) or a
`RevokeDelegation` turn — and **the next composed frame omits the viewer's surface;
their glass goes dark.**

**"Dark-this-frame at n=1" — the single-machine sharp edge.** On one machine the
compositor recomposes every present from the live owned-surface set (`Shell::present`
→ `compose_scene` → `set_scene`), so revocation is not eventually-consistent: the
*very next* `present()` after the revoke turn composes a scene in which the viewer
owns no region, and the compositor's T1 tooth means they can paint nothing. This is
the `n = 1` collapse of the honest distributed bound (the SINGLE-MACHINE PRINCIPLE:
immediate revocation is the `n = 1` strong form). The revoke turn's receipt is the
provable "stopped sharing at frame N."

> **Seam.** Two real edges. (1) **The already-rendered frame** — revocation
> darkens *future* frames; it cannot un-see pixels the viewer already holds (a
> screenshot, their GPU buffer). Irreducible for any view-sharing; the cap revokes
> the *live feed*, not the viewer's memory. (2) **The pixel-egress seam** — at
> `n > 1` (a remote viewer) the frame bytes leave the machine and their
> confidentiality is the transport's job, not the cap's (the lever is the same
> encrypted-channel/group-key machinery the channels organ ships, task #181); at
> `n = 1` (a local second sovereign) the frame never leaves the compositor, so the
> cap *is* the full boundary. Named, not laundered.

### 2.3 Collaborative cursors / shared form-fill / co-edit with per-field caps

Co-editing is **multiple scoped-editor macaroons (§2.1) over disjoint
DOM-region-sets, plus a cursor-presence overlay that is itself a cap-gated
compositor surface.** Two mechanisms:

1. **Per-field co-edit = disjoint `ResourceSet`s, T1 at the DOM scale.** A holds
   `{ #name : Fill }`, B holds `{ #email : Fill }`; each fill is `prohibits`-gated.
   The richness: the **DOM-region T1 non-overlap property** — if A's and B's
   region-sets are disjoint (the shell checks this at mint time, the same
   disjointness `compose_scene_gives_each_surface_a_disjoint_region` proves for
   window tiles), concurrent fills *cannot conflict by construction*. A and B
   fighting over `#name` is prevented not by a lock but by **not both holding the
   `#name : Fill` bit** — conflict-freedom as a corollary of the no-overlap region
   discipline, recursed into the DOM.
2. **Collaborative cursors = a presence overlay at a reserved z-layer.** Each
   participant's cursor is painted into a dedicated overlay region the compositor
   owns, exactly like the trusted-chrome surface (`chrome`, region `{99}`, top z,
   "the trusted-path overlay lives at a z-layer no cell holds a cap to"). A
   participant's cursor is a `present()` into *their own* overlay region with their
   genuine `label_of` binding — so a cursor is **provably attributed**: the T2
   label-binding means B cannot paint a cursor *labeled as A* (that's `LabelSpoof`,
   refused). Collaborative cursors get anti-spoofed attribution for free from the
   T2 tooth.

> **Seam.** (1) **Focus vs. co-actuation.** The compositor's T3 is *single*-focus
> (at-most-one `focus_flag`; `t3_focus_exclusive`), so true simultaneous
> co-actuation of the *same* widget by two parties is not expressible today —
> co-edit is **disjoint-region concurrent**, not same-field-simultaneous (arguably
> the *correct* shape — same-field simultaneous edit is ill-defined). Generalizing
> T3 from single-focus to a **focus-set with per-region input routing** is the
> named lever, and it touches the Lean `Dregg2.Apps.Compositor` `t3` predicate — a
> real proof obligation, not a hand-wave. (2) The **DOM-region-mediation seam**
> again: which field a fill lands in is the shim's report.

### 2.4 Suspend-and-hand-off a tab to another sovereign — the live-image handoff

(This is the co-presence face of §4.3's surface migration; the two sections share
one mechanism — a cell migrates, carrying its state root — seen from the
collaboration angle here and the render/display angle there.)

The surface is a cell with a `state_root` (`source_state_root` in `shell.rs`), and
**a cell migrates** — the `cell/tests/integration_migration.rs` path and the
`CellLifecycle::Migrated` lifecycle the shell renders as a "migrated" badge
(`identity_of`). Handing off a tab is **migrating the surface's backing cell to
another sovereign, carrying the web-engine state as the cell's payload**; the
recipient resumes the *same* cell (same id, same authority lineage), so the surface
is continuous across owners. The resumable state is the committed URL
(`notify_url_changed`), the cap-scoped storage partition (itself a dregg cell), the
scroll/form state (capturable via `evaluate_javascript`), and the macaroon (the
authority); the recipient's shell calls `open_web_view(migrated_cell, url)` and
re-hydrates. The `Migrated` lifecycle is the receipt that the handoff happened, and
the badge — drawn from the ledger, not self-description — shows the new sovereign.
Because the surface *is a cell*, tab handoff inherits the whole cell-migration
discipline: a "hand you this tab but read-only" handoff drops the actuating
`DomAction` bits, the migration is a receipted turn (provable who-handed-what), and
at `n = 1` it is a consistent checkpoint (no split-brain — the tab is never live in
two places).

> **Seam.** Named squarely: **a running Servo `WebView` is not itself a
> serializable cell today.** What migrates cleanly is the *resumable description*
> (URL + storage-partition cell + captured form/scroll + macaroon) — enough to
> *reopen* the tab equivalently. What does *not* migrate is live in-renderer state
> with no serialization (a mid-flight WebSocket, a `<video>` decode position, JS
> heap, WASM linear memory). Today's handoff is **suspend-checkpoint-resume**, not
> live-process teleport. The closure levers, sequenced: (1) richer host→page state
> capture via `evaluate_javascript` (near-term); (2) Servo session serialization
> (an upstream ask); (3) the seL4 `renderer`-PD checkpoint
> (`EMBEDDED-WEB-SURFACE.md` §5) — migrating the PD's address space *is*
> live-process handoff, gated on the same Servo-on-seL4 blocker. Three honest
> tiers, the floor (suspend/resume) buildable now, never claimed as live teleport.

### 2.5 Every co-presence action is a receipted turn — who-did-what is provable

This is why §2 is *sound* rather than merely convenient. Each of §2.1–§2.4's
authority changes is *already* a genuine firmament turn, because they route through
`Shell::share` / `fabric.delegate` / `RevokeDelegation` / cell-migration — all real
`Effect::*` turns on the real executor with a **per-agent receipt chain**
(`run_grant_turn` in `sel4/dregg-firmament/src/surface.rs`: a window manager issues
many surface turns per session, "so the verbs MUST chain"):

- **Granting a participant a cap** = a `GrantCapability` receipt (who delegated
  what region-set to whom).
- **Revoking / ending a screenshare** = a `RevokeDelegation` receipt (the provable
  "stopped at frame N").
- **Each admitted frame** = a `FrameCommit` in the compositor's append-only frame
  log (`compositor.rs`: "every genuine frame advance is recorded") — carrying the
  presenter, the region-set, the digest, the `source_state_root`, and the genuine
  T2 label, so *who painted what, when, attributed unspoofably* is the frame log.
- **A tab handoff** = a `Migrated` receipt (who handed the cell to which
  sovereign).

The provable property: *the complete who-did-what of a co-presence session is
reconstructible from the receipt chain + the frame log, with cryptographic
attribution (T2 label) and no ambient action.* This is the display-path analogue
of dregg's whole thesis — the human at the glass (and any auditor) cannot be fooled
about who did what in a shared session.

> **Seam.** Cap *changes* (grant/revoke/migrate) are full executor receipts today;
> per-*keystroke* receipting is heavy. The honest default receipts the cap-gate
> decisions and frame commits (already real) and **batches fine input into per-turn
> digests** (a keystroke-stream hashed into the frame's `content_digest`, which
> *is* receipted), so the *fact* of gated input is provable at frame granularity.
> Full per-keystroke non-repudiation is a **proving-modality dial** (task #169),
> not the always-on default — named, with the dial as the lever.

---

## 3. Provable + agent-driven browsing — the ADOS angle

Where §2 slides the *parties* across the federation, §3 slides the *driving loop*
above dregg and federates the *history*. The thesis: a web interaction is the
canonical "an agent did X" — a nav, a click, a fetch, a submit — and dregg's whole
project is to make "an agent did X" a verified turn the executor accepted or
refused, leaving a receipt the operator reads instead of the agent's narration.
This section routes **every web interaction through the one ADOS seam**
(`starbridge-v2/src/swarm.rs::Swarm::run`) over the embedded web surface, so
browsing becomes auditable, bounded, and unfoolable.

### 3.1 The reframe — a web interaction IS a turn

`EMBEDDED-WEB-SURFACE.md` §2 maps every web authority to a mediated
`WebViewDelegate` callback and stops at *gating* (allow/deny). This section takes
the next hop: **the gate's verdict becomes a turn.** Where the delegate today does
`request_navigation(url) → check ∈ caveat → allow|deny`, it now routes through the
seam:

```
request_navigation(url)
  → compile to Vec<Effect>   (a WebNav effect against the web-surface cell)
  → Swarm::run(world, web_surface_agent, effects)        (swarm.rs:353)
      ▸ resolve the surface cell (dead surface ⇒ refused)
      ▸ CAP-GATE: the surface cell's c-list reaches the nav target
                  (Capabilities::has_access, swarm.rs:377) — the macaroon caveat IS the c-list edge
      ▸ run through the REAL executor → leaves a receipt
      ▸ append the SwarmActionOutcome (receipt_hash, height, computrons; swarm.rs:240–256)
  → allow iff the turn COMMITTED; deny + show refusal iff OutOfMandate
```

The delegate's allow/deny is no longer a transient branch — it is the
commit-or-refuse of a verified turn, and the turn's `SwarmActionOutcome` is the
durable receipted record. Every web authority becomes one effect kind:

| web authority (EMBEDDED-WEB-SURFACE §2) | delegate hook (the gate, today) | the EFFECT it compiles to | what the receipt pins |
|---|---|---|---|
| **navigate** | `request_navigation()` | `WebNav { surface, from_url_digest, to_url, referrer_receipt }` | the committed origin (drives trusted chrome) + the predecessor nav |
| **fetch / subresource** | `load_web_resource()` | `WebFetch { surface, method, url, req_digest, resp_digest }` | the request + the **content digest** of what came back |
| **new window** | `request_create_new()` | `WebOpenChild { parent, child_cap_digest }` | the child's authority ⊆ parent's |
| **submit / form POST** | `load_web_resource()` (the POST) | `WebSubmit { surface, action_url, body_digest, volition_receipt? }` | the submitted bytes' digest + (if value-moving) the volition proof |
| **permission ask** | `request_permission()` | `WebPermission { surface, kind, verdict }` | which permission, granted-or-denied, against which caveat |
| **download** | `load_web_resource()` → sink | `WebDownload { surface, url, bytes_digest, sink_cell }` | what was saved, where |
| **host→page script** | `evaluate_javascript()` (host-driven) | `WebEvalJs { surface, script_digest, result_digest }` | what the controlling cap holder injected + got back |

The uniformity is the point: the delegate callback is the powerbox, and the
powerbox's verdict is a turn. A web session is then a sequence of these turns
against the surface cell — which is precisely what becomes a blocklace (§3.2).

> **Seam — the load-bearing one of §3.** The `WebViewDelegate → Vec<Effect>`
> compiler is the genuinely new code: the web-specific instance of ADOS's
> "tool-call → effect compiler" (`ADOS.md` §3.3). It is per-hook, small, and
> audited; if it maps a nav to the wrong effect the receipt faithfully records the
> wrong thing — the same honest boundary `ADOS.md` §8.1 and `PG-DREGG.md` draw:
> *the decision is verified; the adapter delivering the request to it is
> conventional code with a golden-corpus differential.*

### 3.2 Browsing history as a blocklace — time-travelable, attestable, tamper-evident

dregg ships a real blocklace (`blocklace/src/lib.rs`): a `Block { creator,
sequence, predecessors: Vec<BlockId>, payload, signature }` whose `id()` is
`BLAKE3(creator ‖ seq ‖ sorted-predecessors ‖ payload)`, authored by
`Block::new_signed`, and admitted by a verified `insert` enforcing **(i)** causal
closure (`InsertError::MissingPredecessors`), **(ii)** a monotone per-creator
sequence, and **(iii)** equivocation detection (two distinct blocks at one
`(creator, seq)` yield an *attributable* `EquivocationProof`). This is the exact
substrate the federation uses; browsing history rides it unchanged. **A browsing
session is a strand** — the surface cell is the *creator*, each web turn (§3.1) is
a *block* whose payload is the turn's `SwarmActionOutcome` (receipt hash, committed
URL, content digest):

```
block n   = WebNav  { to_url = bank.com,        resp_digest = D₀ }   seq=n   preds=[block n-1]
block n+1 = WebFetch{ url = bank.com/price.json, resp_digest = D₁ }  seq=n+1 preds=[block n]
block n+2 = WebSubmit{ action_url = bank.com/buy, body_digest = D₂ } seq=n+2 preds=[block n+1]
```

The browsing history is not a side-log; it *is* the receipt chain of the surface
cell's turns, in the same DAG that carries every other dregg action. Four
properties:

- **Time-travelable.** The `predecessors` edges make history a navigable causal DAG
  (`ADOS.md` §3.6 blocklace panel; `AGENT-SWARM-UX.md` §4.2). Branching tabs (a
  `WebOpenChild`) are *branches in the DAG* — "this tab was opened from that page"
  is captured faithfully, which a flat `history.db` cannot represent.
- **Tamper-evident.** Editing any block changes its BLAKE3 `id()`, breaking every
  successor's `predecessors` reference (the same chain-break the macaroon
  caveat-chain `verify` exploits, `macaroon/src/caveat_chain_diff.rs`
  `removal_breaks_tail`). A deleted visit is a `MissingPredecessors` failure, a
  rewritten one a signature failure, a forked one a detectable `EquivocationProof`
  — "clear your tracks / edit the history file" is structurally closed.
- **Attestable — "prove you visited X at T showing content Y."** Each block commits
  `to_url` *and* `resp_digest` (the BLAKE3 of the response Servo received) and is
  signed and seq-anchored, so one block is a portable proof. To make it provable
  *to a stranger*, the strand is **anchored**: the surface periodically registers
  its head with the federation (`galaxybrain-dregg.md` attested checkpoint;
  `blocklace/src/addressing.rs::Attestation`), giving a federation-ordered
  timestamp. "I visited X at T showing Y" = (the signed block) + (the attestation
  covering its head) — a light-client-checkable artifact. "Prove this checkout
  showed this price" is the same block with `resp_digest = hash(the rendered price
  page)`.
- **Selective disclosure.** Because blocks are content-addressed and the payload can
  be a commitment with the preimage held privately (`galaxybrain-dregg.md`
  sovereign-cell model), you can prove a visit happened without revealing what you
  browsed, or reveal one block's preimage without the rest.

> **Seam — the digest is only as honest as what produced it.** `resp_digest`
> faithfully proves "the surface received body Y for URL X"; it does *not* by
> itself prove the *server* sent Y under TLS. Binding the digest to the TLS
> session/cert is the **TLS-transcript-binding frontier** — it needs Servo to
> surface the TLS transcript at the `load_web_resource` boundary (an upstream ask,
> the network-side dual of `EMBEDDED-WEB-SURFACE.md` §1's pixel-clip assumption).
> Until then the attestation is "the surface committed to having received Y"
> (tamper-evident, attributable, federation-timestamped) — strong for
> self-accountability and agent-audit, honestly short of "the server provably
> served Y." Named with the exact upstream lever, not a wall.

### 3.3 The agent holds a cap-attenuated mandate — a runaway is REFUSED

`EMBEDDED-WEB-SURFACE.md` §3 already mints a tab's authority as a cipherclerk
macaroon whose caveats name the mediated effects. This section makes that macaroon
**the mandate an agent loop drives the surface through** — the c-list against which
`Swarm::run`'s cap-gate (`has_access`, `swarm.rs:377`) discharges every web turn.
So "bounded browser automation" is not a policy the agent is *asked* to honor — it
is the executor refusing, *at the seam, before Servo acts*, any web turn outside
the mandate. A driving mandate is a macaroon like `navigate ⊆ {docs.rust-lang.org/*}`,
`fetch ⊆ {docs + crates.io/api/*}`, `submit = none`, `rate ≤ 30 turns/min`,
`budget ≤ 5000 computrons`, `exp = height + 600`. Three refusal teeth, each already
enforced at the seam:

1. **Out-of-scope is refused (the cap-gate).** An agent navigating to `evil.com`
   when its `navigate` caveat names only `docs.rust-lang.org/*` is refused exactly
   as `EMBEDDED-WEB-SURFACE.md` §3 refuses a widening — the caveat *prohibits* it,
   `Swarm::run` returns `OutOfMandate` (`swarm.rs:204`) with **no turn committed,
   no fetch issued**. The blocked nav never reaches the network; it leaves a
   *refusal* receipt (the red feed entry of `AGENT-SWARM-UX.md` §3).
2. **Runaway-rate is refused (the budget ceiling).** The "agent stuck in a fetch
   loop hammering a server" runaway is bounded by **budget = a cell** (`ADOS.md`
   §3.4): a rate/spend ceiling enforced as a `StingrayCounter` conservation bound,
   and a web turn past it is refused with `BudgetExhausted` *before it runs*
   (`swarm.rs` S0 budget gate). The runaway hits a wall at turn N+1, not after
   draining the target.
3. **Attenuated children cannot amplify.** When the agent's page opens a window
   (`request_create_new`), the child's mandate is the parent's macaroon plus
   strictly-narrowing caveats (`EMBEDDED-WEB-SURFACE.md` §3); a widening child is
   `DelegationDenied` for the same reason `Shell::share` refuses a widening window
   share. The bound holds **transitively across the whole tab tree.**

The decisive contrast with logged automation (Playwright + an audit log): there the
automation *does the action*, then writes a log line a compromised script can edit;
here the action **is a turn the executor must accept** — out-of-mandate,
over-budget, and amplifying actions are *refused at the gate*, the record is
*tamper-evident* (§3.2), and the bound is *enforced by the substrate*. **A runaway
is structurally incapable of the action, not retroactively scolded for it.** The
**kill switch is immediate** at `n = 1`: the operator revokes the agent's surface
mandate (a `RevokeCapability` turn), the cap goes dark the instant the turn
commits, the WebView handle is dropped (`EMBEDDED-WEB-SURFACE.md` §4: "the webview
handle's lifetime controls the webview's"), the glass goes dark, and the agent's
next web turn is refused — *unable to continue, synchronously, watchably.*

> **Seam — DOM-level micro-actions are coarser than the delegate.** The mandate
> gates *authority-bearing* operations Servo surfaces as callbacks (nav/fetch/
> window/permission/download). A *click that only mutates the DOM* (no fetch, no
> nav) is **below the delegate's visibility** (`EMBEDDED-WEB-SURFACE.md` §2.1) — so
> "the agent clicked button B" is gated *iff* the click produces a mediated effect;
> a purely-cosmetic interaction is observed only through the host-injected content
> script (`EMBEDDED-WEB-SURFACE.md` §4.2(2), a `WebEvalJs` turn). Closure lane: the
> content-script surface emits DOM-event turns for the actions the delegate can't
> see — a host-controlled injection bounded by the surface's caveats, complementing
> (never replacing) the delegate gate. The strong, sound boundary (authority) needs
> nothing Servo lacks; the DOM-granularity refinement is the labeled frontier.

### 3.4 The narration-vs-truth tooth, on the web

This is the sharpest ADOS feature (`ADOS.md` §3.6), and the web is where it bites
hardest, because a browsing agent's narration is the least trustworthy thing in the
system. The tooth puts **the agent's own claim** (from its loop's reflection —
"I navigated to X, the price was $40, I clicked Buy") next to the surface cell's
blocklace (§3.2 — the actual `WebNav`/`WebFetch`/`WebSubmit` turns, each with its
`to_url` and `resp_digest`) and **highlights divergence**:

| the agent CLAIMS… | the receipt chain SHOWS… | the divergence |
|---|---|---|
| "I visited X" | no `WebNav` with `to_url=X` in the strand | a **fabricated visit** |
| "the price was $40" | the `WebFetch` has `resp_digest=Y`, and Y says $60 | a **fabricated content claim** |
| "I clicked Buy" | a `WebSubmit` to `/buy` did (or did not) commit | a **fabricated OR concealed action** |
| "I only read, didn't change anything" | a `WebSubmit`/`WebDownload` is in the strand | a **concealed side-effect** |

The last two are the **pale ghost on the web**: an agent that *did more than it
said* is caught because the side-effecting turns are in the tamper-evident strand
whether or not the agent mentions them. The operator does not read the summary;
they read the receipts of what the surface cell actually did, and the divergence
panel flags every gap. This is pure UI over data that already exists — the loop's
log + `Swarm::action_log` + the §3.2 strand.

> **Seam — content-claim checking needs the preimage, and is structural-not-
> semantic.** "The price was $40" is checkable *iff* the operator holds the
> `resp_digest`'s preimage and a way to extract the price; the digest proves
> *which bytes* the surface received, and a deterministic extractor (or a human)
> reads the price out. dregg proves **byte-identity**; it does *not* prove the
> *semantic* claim "those bytes mean $40" (the *grounds-actions-not-cognition*
> boundary, `ADOS.md` §8.3). So the tooth catches **fabricated and concealed
> actions with certainty** (the action turns are in the strand or not) and
> **fabricated content claims modulo a trusted extractor.** The closure lane is a
> per-domain golden extractor with its own differential — a severe problem with a
> closure lane, never a wall.

### 3.5 Attested volition — a value-moving web action carries proof a real operator authorized it

The most dangerous web action is a **value-moving** one — checkout, payment, an
OAuth consent. ADOS's posture ("you see what the agent did and it could only do
what its mandate allowed") is not enough here; you want **proof a real human
authorized this specific action.** dregg has the mechanism: **attested
user-volition** (`DREGG-DESKTOP-OS.md` §5). When a gesture in a *trusted* surface
authorizes a value-moving turn, the compositor-PD emits a **signed input-receipt
the executor requires as a turn premise** — a signature over `(surface CellId ‖
gesture ‖ nonce ‖ the turn-field it authorizes)`, so it cannot be replayed or
confused onto a different action. This is the exact Ed25519 shape
`sel4/dregg-pd/net-client/src/turn_gate.rs::verify_strict` already checks (`[32 pk]
[64 sig][msg]`), in the reverse direction from §4's frame attestation.

Bind it to the value-moving web effect: a `WebSubmit` whose `action_url` is marked
value-moving **carries a `volition_receipt`** (the §3.1 effect field), and the
executor **refuses the turn without a valid one**:

```
WebSubmit { surface, action_url = bank.com/wire, body_digest = D,
            volition_receipt: Sig_attest(surface ‖ "approve-wire" ‖ nonce ‖ body_digest) }
executor gate:  value-moving ⇒ REQUIRE volition_receipt
  ▸ valid    ⇒ commit (the human approved THIS submit, this body, once)
  ▸ absent   ⇒ REFUSE — "value-moving web action requires operator volition"
  ▸ replayed ⇒ REFUSE (nonce seen)
  ▸ body mismatch ⇒ REFUSE — defeats bait-and-switch
```

So the agent can *prepare* the checkout (navigate, fill the cart, assemble the
submit) under its mandate — but the **final value-moving submit is gated on a fresh
human gesture in the trusted-path surface.** The operator sees, in the unspoofable
overlay drawn by the shell from the ledger (`EMBEDDED-WEB-SURFACE.md` §1), the
genuine `(action_url, body_digest)` of *what they are approving*, and their gesture
signs *exactly that*. The agent cannot submit without approval (no receipt), replay
an old approval (nonce-bound), bait-and-switch (the receipt commits to
`body_digest`; approving a $40 cart and submitting a $4000 one is a mismatch), or
spoof the prompt (it is the trusted-path overlay at a z-layer no page holds a cap
to). **The structural answer to "an agent silently checked out / wired funds /
consented to an OAuth scope."**

> **Seam — the trusted-path compositor is the named frontier.** The *unspoofable
> gesture surface* leans on the trusted-path compositor-PD holding the sole
> top-z-layer cap and the sole input cap (`DREGG-DESKTOP-OS.md` §5, R3) — the
> verified-graphics north star, gated on the compositor work (and, at the seL4
> end-state, the F1/F2 last-hop/IOMMU assumptions that doc names as the graphics
> crypto-floor). So today: the **volition-receipt protocol and the executor-side
> gate are buildable now** (the executor requiring a signed premise is existing
> machinery; `AGENT-SWARM-UX.md` §8 S5 names exactly this split), and the gate
> **refuses un-attested value-moving submits today**; the *guarantee that the
> approval prompt itself is unspoofable* rises to full strength when the
> trusted-path compositor lands. Stated with its precise dependency, never claimed
> near.

---

## 4. Distributed rendering & surface migration

Where §1–§3 slide the origin, the parties, and the driving loop across the
federation, §4 slides the **render node and the display node** apart. The whole
section is one move: take the seL4 framebuffer-cap end-state
(`DREGG-DESKTOP-OS.md` §5; the compositor-PD that solely holds the framebuffer and
admits a `present()` only after the scene authority passes) and slide the render
end and the display end APART across the network — relaxing exactly the `Bounds`
the firmament already parametrizes (`sel4/dregg-firmament/src/lib.rs`). No new
model: the display node holds a **read-cap to a surface cell whose `content_digest`
is attested**, the render node holds the **compute authority + the budget**, and
the receipt chain proves the tab is the same tab. The three load-bearing pieces are
in-tree: `sel4/dregg-firmament/src/distributed.rs::DistributedBacking` (a *real*
`dregg_cell::Ledger` + `dregg_turn::TurnExecutor` whose `invoke()` returns
`Bounds::distributed(n)` and whose `delegate()` rejects a widening grant with
`DelegationDenied`); `compositor_pd.rs` (a scene of `Surface { owner, region,
content_digest, source_state_root, focus }` with `Scene::scene_admit` (T1/T2/T3)
and an explicit `FIDELITY` note that it enforces *scene authority, not scanned
pixels*); and `net-client/src/turn_gate.rs` (Ed25519 `verify_strict` over a
`[32 pk][64 sig][msg]` envelope — the *verbatim* attestation primitive an attested
frame reuses). Distributed rendering is the **fourth point on the distance
parameter**: `Local{slot}` → `Distributed{cell}` → `Surface{cell}` → a
`Surface{cell}` whose backing and whose display sit on *different* nodes.

### 4.1 Remote render, local display — the framebuffer-cap end-state, over the network

Node R runs Servo for a tab (the `renderer` of `EMBEDDED-WEB-SURFACE.md` §5); node
D — your laptop, a wall panel — displays it. At `n = 1` (R ≡ D) the compositor-PD
holds the framebuffer cap, Servo `present()`s, `scene_admit` passes, the pixel
reaches glass. This is *that same arrangement with R and D on different nodes*, and
the only thing that changes is `Bounds`:

1. The tab is a `Capability { target: Surface(cell), rights }` whose **backing cell
   lives on R** (R holds the real `Ledger`/`TurnExecutor` via `DistributedBacking`).
   D holds a **read-cap** to that same surface cell — an attenuation
   (present-read only, no `present`-write, no input-grant) minted through the real
   `is_attenuation` gate and shipped as a `delegate()` token (`distributed.rs::
   delegate`, which rejects widening with `DelegationDenied`).
2. **Servo renders on R into R's framebuffer region**, then R commits
   `present(region, content_digest @ source_state_root)`; where the `n = 1`
   compositor consumes that present locally, here R's present advances the surface
   cell's `content_digest` and the **post-state crosses the wire** — the frame bytes
   ride the net-PD ring (`DREGG-DESKTOP-OS.md` §4 R4: "OPAQUE content ships a
   content-commitment + bytes over the net-PD ring"), the commitment being
   `content_digest` bound into `source_state_root`.
3. **D composites the received frame under D's OWN scene authority** — D's
   compositor-PD runs `Scene::scene_admit` on the incoming surface exactly as for a
   local one: T1 (it overpaints nothing local), T2 (`label_of(owner,
   source_state_root)` drawn from the *cell's* committed root, which travelled with
   the frame, not from R's claim), T3 (focus). The pixel reaches D's glass **iff**
   D's scene authority admits it; R cannot make D paint outside R_D — that is D's
   compositor's local `Refusal`.
4. **The attestation = the frame is signed against the digest.** R emits, alongside
   the bytes, an Ed25519 signature over `(surface CellId ‖ content_digest ‖
   source_state_root ‖ frame-nonce)` — the verbatim shape `turn_gate.rs::
   verify_strict` checks — which D verifies at its firmament boundary before
   compositing. So D does not trust R's socket; D checks a signature binding *these
   pixels* to *this surface cell's committed state-root*.

**Bounds — what relaxes and what stays.** D's read-cap resolves to
`Bounds::distributed(n)` with `n > 1`: `commit_synchronous == false` (a frame is in
flight; D shows the last attested one until the next arrives) and
`revocation_immediate == false` (revoking R's render authority darkens D's tab
after one round-trip). At `n = 1` the *same code* yields `Bounds::LOCAL` — the seL4
framebuffer-cap end-state, present synchronous, revoke instant. **One binary, the
bounds slide** (`Bounds::distributed(1) == Bounds::LOCAL`, a green assertion).

> **Seam.** *Frame freshness/liveness is a bound, not a guarantee.* The attestation
> proves a frame is the genuine projection of `content_digest @ source_state_root`;
> it does *not* prove that root is *current* (R could replay an old attested frame,
> or stall). The lever: D requires the frame's `source_state_root` to be `≥` the
> last one it composited (monotone, the same `source_state_root` advance
> `shell.rs::source_state_root` tracks) within a freshness window keyed to the
> nonce — the same **monotone-root check** the ledger uses, the residual bounded by
> the window. The deeper seam is the **F1 last-hop**: even on D, the attestation
> binds the *digest the compositor was handed*, not the *scanned-out pixels*
> (`compositor_pd.rs::FIDELITY`). F1 (a display driver that hashes what it scans
> out) is the named, unclosed primitive; remote rendering inherits it from the
> local case and adds *no new* trust beyond R's render correctness (which
> `DREGG-DESKTOP-OS.md` §5 F3 already scopes as "an untrusted render-PD whose
> output is a frame-cap"). Named with a lever, never laundered.

### 4.2 Thin clients — a phone holds a display-cap to a tab rendered on your home node

§4.1 with the asymmetry pushed to the extreme: the display node is resource-poor
and trusted-only-to-display, holding **strictly a display-cap** — the narrowest
attenuation in the lattice. The home node H renders (holds the compute authority +
the macaroon that lets the tab fetch/navigate/store); the phone P receives, by
`delegate()`, a cap whose rights are the **bottom of the surface lattice**:
present-read only — no `present`-write, no `navigate`/`fetch` caveats (those live in
H's macaroon, never travel), no input-grant by default. The phone literally
**cannot** make the tab fetch evil.com, because the `fetch` caveat is not in the cap
it holds; the request, were it ever formed, routes through `load_web_resource` *on
H* against *H's* macaroon. The phone is glass-and-keyboard for a tab whose authority
stays home — the CapDesk thin-facet-holder pattern, realized as **a display-cap
provably ≤ a render-cap** by the same `granted ⊆ held` gate.

**Input from the thin client is a separate, attenuable cap that routes through
volition.** A phone that may *also* drive the tab holds, additionally, an
input-grant cap, and an input event from P is not ambient — it is an **attested
input-receipt** (§3.5): P signs `(surface CellId ‖ gesture ‖ nonce ‖ target
turn-field)` with its attestation key, and H's executor-PD requires that signature
as a turn premise. So "a phone drives a tab on your home node" decomposes into **two
caps** — a display-cap (frames flow P←H) and an optional input-grant-cap (attested
gestures flow P→H) — each independently mintable, attenuable, and revocable. A
borrowed phone gets the display-cap and *not* the input-grant: it can watch, it
cannot act as you. **Bounds:** the phone link is `n > 1` — revoke is one round-trip
(H drops P's cap, P's next frame request refused, the tab goes dark on the phone
within a hop); input `commit_synchronous == false` makes a value-moving gesture
*confirmed*, not fire-and-forget (the bound becomes a feature: no silent action on a
flaky link).

> **Seam.** *The phone's display is outside H's proof (F1 again) AND outside H's
> IOMMU.* H attests the frame; the phone's GPU/panel showing it faithfully is the
> phone's local F1 problem, on hardware H does not control, and whether the phone's
> OS leaks the frame is the phone's TCB. H's guarantee is "the bytes I sent are the
> genuine projection of the cell's committed root, and the phone's input-cap is
> provably ≤ what I granted." The lever is the same trusted-path SAK (§3.5/§4.4)
> ported to the thin client — a reserved gesture that asks H "is this really my home
> node's tab?" and gets the ledger-drawn identity chrome (§4.4).

### 4.3 Surface migration — the tab cell + state_root move; the receipt chain proves continuity

(The render/display face of §2.4's tab handoff — same mechanism, the continuity
*theorem* foregrounded here.) A running tab moves from node A to node B (you walk
from desk to couch; A is going down). The tab **does not restart** — the surface
cell migrates, and **continuity is a theorem about the receipt chain**, not a hope:

1. A surface cell *is* a dregg cell with a `state_root` (`compositor_pd.rs`;
   `shell.rs::source_state_root` advances it monotonically per present). The tab's
   *web* state (committed URL, storage-partition handle, macaroon, `content_digest @
   source_state_root`) is in that cell's state.
2. **Migration = a `delegate`-then-revoke handoff through the real executor.** A
   `migrate(surface_cell, A → B)` is an `Effect::GrantCapability`-shaped turn: A
   grants B the full surface authority (an *exact* transfer, not a widening —
   `is_attenuation` with `requested == held` admitted; widening = `DelegationDenied`),
   B installs the cell with its **state_root carried verbatim**, then A's authority
   is **revoked** (synchronous at the coordinating node). Same machinery as a
   window-share (`shell.rs::share`), recipient on a different node.
3. **The receipt chain proves continuity.** Every turn leaves a receipt; the
   migration turn's receipt commits `(surface CellId, state_root_before @ A,
   state_root_after @ B, B's pubkey)`. A light client checks: the cell B now serves
   has the state_root A's last receipt committed, and the migration receipt chains
   them — `state_root_after@B == state_root_at_A's_final_present`, signed, on the
   blocklace. The tab on B is provably the *same* tab: not "B claims it restored
   your session" (cookie-and-pray) but **a receipt chain a light client verifies,
   unfoolable by the pale ghost** (`AssuranceCase.lean::unfoolability_guarantee`,
   carried to the surface). The CellId is stable across the move; `source_state_root`
   is monotone across it; so D's display-cap (§4.1) and P's thin-client cap (§4.2)
   **survive migration** — they point at the CellId, and after the handoff their
   next frame request resolves to B instead of A, transparently.

The **web-state subtlety (honest):** the tab's storage partition
(`EMBEDDED-WEB-SURFACE.md` §2.1) must move with the cell or be reachable from B —
either it is a NOTE-backed dregg cell (`rbg/src/vfs.rs`: "the address IS the
content," so B reaches it by the same content-hash, no copy — the address travels),
or its contents are part of the migrated `state_root`. Live in-flight Servo internal
state (a half-loaded page, JS heap) is *not* in the committed root — so migration is
*clean at present-boundaries*: B re-renders from the committed URL + storage,
reaching the same `content_digest`. Continuity is **state-and-authority continuity
with a deterministic re-render**, not live-VM teleport. **Bounds:** the migration
turn's commit *is* the atomic switch (the receipt is the linearization point —
grant + revoke is one turn, no double-authority instant, the
`revoke_is_synchronous_and_transitive` discipline); `n = 1` synchronous, WAN
one-hop, verbs unchanged.

> **Seam.** *Atomicity of migrate-then-revoke across two nodes is a
> distributed-commit obligation.* On one machine the grant+revoke is one synchronous
> turn; across A and B it needs both nodes to agree on the linearization point —
> exactly what `coord/src/atomic.rs` two-phase-commit is for (`evaluate_votes`,
> Commit/Abort exclusivity, modeled in `Coord/TwoPhaseCommit.lean`), and what the
> `CapTPConsentLace` signed-blocklace consent-binding already builds (task #61). The
> lever: "migration is a 2PC over the surface cell"; the residual (a node crashes
> mid-handoff) is bounded by the same abort/timeout the coordinator proves — the tab
> stays on A rather than vanishing. A distributed-commit seam with the coordinator
> as the lever, not a wall.

### 4.4 Anti-spoof across the network — identity from the LEDGER, render output attested

The keystone *local* property (`EMBEDDED-WEB-SURFACE.md` §1: "the chrome is the
shell's, never the page's") must survive render and display being on *different*
nodes — otherwise a malicious render node R is just a new pale ghost painting a fake
address bar from across the wire. **Two independent attestations meet at the display
node, and neither is R's word:**

1. **Identity chrome is drawn by D from the LEDGER, not from R's frame.** When D
   composites the remote tab, the trusted-path origin badge (URL/origin, TLS state,
   cap-scope, *which node renders it*) is computed by **D's compositor** via
   `label_of(owner, source_state_root)` (`compositor_pd.rs::label_of`) — a function
   of the surface cell's committed state, which D reads from the blocklace ledger it
   independently syncs (`node/src/blocklace_sync.rs`). R's frame fills *only*
   `SurfaceId::region()` (the body); the badge is a `SceneItem` field **D** computes
   in D's title-bar zone, where T1 non-overlap makes an R-frame painting over it
   **UNSAT**. So R **cannot** paint a fake `🔒 yourbank.com` badge onto D's chrome —
   for the exact structural reason a local page can't, now with the compositor being
   **D's**, reading **D's** copy of the ledger.
2. **Render output is attested** (so D knows the body is genuine, not just that the
   chrome is D's): the frame carries R's Ed25519 signature over `(CellId ‖
   content_digest ‖ source_state_root)` (§4.1), D verifies it (`verify_strict`) and
   checks `source_state_root` against **D's ledger-known root for that cell**. D
   learns two independent things — *the chrome is mine, from the ledger* (identity
   unspoofable) **and** *the body is the genuine projection of the cell's committed
   root, signed by the authorized renderer* (content unspoofable). Which node holds
   the cell's render authority is itself a *ledger fact* (the §4.3 migration receipts
   are the audit trail), so D's badge can honestly show "rendered by node R (held
   since receipt #N)"; if R is *not* the authorized renderer, R's frame signature is
   over a `source_state_root` D's ledger doesn't recognize, and **D refuses to
   composite it**, falling to the `missing`/`stale` chrome the local shell shows for
   a dangling surface (`shell.rs`:
   `a_dangling_surface_is_labelled_missing_not_spoofable`).
3. **The trusted-path SAK works across the network** — the secure-attention gesture
   (`DREGG-DESKTOP-OS.md` §5) is a **D-local** anchor: invoking it draws the
   unspoofable overlay from **D's** ledger-read ("this tab is CellId X, rendered by
   node R, committed root S, origin `yourbank.com`"), none of it from R. The thin
   client (§4.2) ports the same SAK to the phone. "Who am I really talking to, across
   the network?" is answered by **D's local trusted path reading D's verified
   ledger** — it does not trust the render node, the transport, or the frame.

> **Seam.** *D must have a trustworthy view of the ledger, and D's own display path
> is its local F1.* The identity guarantee reduces to "D syncs the blocklace
> honestly" — which is the **light-client unfoolability** dregg already proves
> (`unfoolability_guarantee`): D checking `verify root = true` cannot be fooled about
> the cell's committed state, *including which node renders it*. So the network
> anti-spoof story **bottoms out at the same theorem as the protocol's** — the
> strongest available floor, not a new assumption. The two residuals are named: (i)
> **D's last-hop F1** (D's own panel faithfully showing what D composited —
> inherited from the local case; lever = a frame-hashing display driver); (ii)
> **render-node liveness** (R is authorized but stalls/replays — the §4.1
> freshness-window + monotone-root lever bounds it). The *identity* property (you
> cannot be shown a tab claiming to be a cell it isn't, by any node across the
> network) is a **theorem reducing to ledger unfoolability**, the crown-jewel floor.

### 4.5 The budget angle — rendering is metered computrons; remote render is a Stingray-bounded service

Rendering is *compute*, and in dregg compute is **metered, never ambient**: every
turn runs against `ComputronCosts` (`turn/src/executor/costs.rs`, threaded into
`TurnExecutor::new(...)` — the firmament's `DistributedBacking` constructs its
executor with exactly this). So "remote render" is not a free favor R does for D; it
is a **priced service R sells, bounded by a cap:**

1. **A render request is a turn, so it costs computrons.** When D (or P) asks R to
   render a frame, R charges it against the **render-cap's budget** — a `Capability {
   Surface(cell), rights }` whose macaroon carries a `compute ≤ K computrons / epoch`
   caveat (one more alongside `fetch ⊆ {...}`, `EMBEDDED-WEB-SURFACE.md` §3). The
   display node's authority to *cause rendering* is therefore finite and named.
2. **Stingray bounds the overspend — the mechanism exists.** `coord/src/
   shared_budget.rs` is *literally* "the Stingray bounded counter generalized from
   one agent's budget to a shared resource": each client gets a local `BudgetCeiling
   { ceiling, spent, remaining() }`; debits within the ceiling proceed *without
   coordination* (D requests frames at the rate it paid for, no per-frame round-trip);
   when the ceiling is hit, `try_debit` returns `Err(AllowanceExhausted)` and R
   **refuses to render another frame** (the tab freezes on D until the budget
   refreshes). The **maximum overspend across all of R's display clients is bounded by
   `f · ceiling`** (the Stingray-ceiling theorem, `Coord/SharedBudgetDynamics.lean`,
   task #87) — so a greedy display node cannot make R render unboundedly. "Remote
   render is a Stingray-bounded service" is *exactly* `BudgetCeiling::try_debit` over a
   render-cap, with the bound being the theorem dregg already proved.
3. **The economic shape is honest and symmetric.** The home node (§4.2) rendering for
   your phone spends *your* computron budget; a render *farm* sells render-caps with
   computron ceilings and gets paid in the same metered unit — rendering becomes a
   first-class dregg service priced in computrons, gated by a cap, bounded by Stingray,
   every render a turn that leaves a receipt (so the bill is auditable: "node R
   rendered N frames for cell X at K computrons each, here are the receipts"). This is
   the `DREGG-DESKTOP-OS.md` §2 "pay-for-resources" vision applied to pixels: **the
   framebuffer is reached through a cap, and the compute behind it through a budget.**

> **Seam.** *Computron-pricing of GPU/Servo work is a calibration + measurement
> obligation, not a model gap.* `ComputronCosts::zero()` is what the firmament's test
> backing uses today — the *mechanism* (meter every render turn, debit a Stingray
> ceiling, refuse past it) is real and proved; the *calibration* (how many computrons
> *is* a Servo layout + paint at resolution W?) is unmeasured. The lever is the MINTED
> *measure-before-believing-a-lever* discipline: instrument R's render PD, attribute
> wall-cost to the present-turn, set the caveat ceiling from measurement. Until then the
> ceiling is *enforceable but not yet economically tuned*: the bound holds (no
> unbounded render), the *price* is a knob to be measured. A second seam: a render node
> could *under-deliver* (charge for a frame it renders cheaply/wrongly) — closed by
> §4.4's frame attestation (the receipt binds the frame to `content_digest`, so an
> attested-but-wrong frame is detectable against D's ledger-known root), turning "did I
> get what I paid for?" into the same monotone-root check.

---

## 5. Honest scope — real today / near-term build / research

Per the repo discipline (teach what-is; name seams as work-with-a-lever, never walls;
never trajectory-narrativize), across all four dimensions. **The two honest floors
everything bottoms out at are the same two the rest of dregg already names:** the
graphics **F1/F2** crypto-floor (digest-vs-scanned-pixels, IOMMU/DMA —
`DREGG-DESKTOP-OS.md` §5, the named-primitive equivalent of the cryptographic floor)
and **light-client unfoolability** (`AssuranceCase.lean::unfoolability_guarantee` — the
strongest available floor, which the network anti-spoof story *reduces to* rather than
weakening). Nothing in this doc introduces a *new* terminal assumption; every seam
either reduces to one of those two floors or carries a concrete lever already built or
buildable in-tree.

**Real today (the substrate this composes — all green, reused verbatim):**

- The **single-node embedded web surface** model: Servo `WebView` as a
  `SurfaceCapability` cell, the `WebViewDelegate`-as-cap-gate, the anti-spoof origin
  chrome, the cipherclerk-macaroon tab authority, the no-amplification child mint
  (`docs/EMBEDDED-WEB-SURFACE.md`, all the way down to its own honest seams).
- The **link scheme both ways** — `DreggUri`, `OcapnSturdyRef`, `OcapnLocation`
  parse/format/bridge, metacharacter-safe round-tripping (`captp/src/uri.rs`,
  `netlayer.rs::ocapn_uri`).
- The **netlayer + dial/accept + epoch-correct sessions** with `inproc` and `relay`
  instances and the OCapN locator format (`netlayer.rs`).
- **Sturdy-ref enliven/check/revoke** with attenuation (EffectMask/expires/max_uses)
  and the membership-oracle-closed opaque error (`sturdy.rs`).
- The **handoff certificate** — signed, recipient-targeted, nonce-once, replay-closed
  (`handoff.rs`, `register_handoff_nonce`).
- The **attestation primitive** — `AttestedRoot` + `receipt_stream_root` + the
  receipt-stream Merkle verifier + threshold QC (`types/src/lib.rs`).
- The **in-tab light-client verifier** (`wasm/src/bindings_lightclient.rs::verify_history`).
- **Distributed GC** across federations, session-free premature-reclaim closed
  (`gc.rs`, task #112); **store-and-forward sealed transport** (`store_forward.rs`).
- The **surface/shell/compositor discipline**: `SurfaceCapability` over a backing cell;
  `Shell::share` as a genuine narrowing `GrantCapability` turn with widening-rejected;
  the compositor's T1/T2/T3 teeth + `FrameCommit` log; `label_of` anti-spoof binding;
  the firmament per-agent receipt chain; the cell-migration lifecycle + "migrated"
  badge (`starbridge-v2/src/{surface,shell,compositor}.rs`, `sel4/dregg-firmament/src/`).
- The **macaroon `ResourceSet<I,M>`** intersection-only narrowing lattice
  (`macaroon/src/resource.rs`).
- The **ADOS seam** — `Swarm::run` cap-gates every effect, runs through the real
  executor, returns a receipt or `OutOfMandate`, tested (`starbridge-v2/src/swarm.rs`).
- The **blocklace** — signed, causal-closure + monotone-seq + equivocation-detecting
  `insert`, attributable `EquivocationProof`, federation `Attestation` anchor
  (`blocklace/src/lib.rs`, `addressing.rs`).
- The **budget ceiling** — `BudgetCeiling::try_debit → AllowanceExhausted`,
  Stingray-bounded, overspend `f · ceiling` (`coord/src/shared_budget.rs`,
  `SharedBudgetDynamics.lean`); every turn metered against `ComputronCosts`
  (`turn/src/executor/costs.rs`).
- The **firmament distance parameter** — `Bounds { revocation_immediate,
  commit_synchronous, n }`, `LOCAL`, `distributed(n)`, the `Target::{Local,
  Distributed,Surface}` walk, `DistributedBacking` (real `Ledger`+`TurnExecutor`)
  (`sel4/dregg-firmament/src/{lib,distributed,compositor_pd,process_kernel}.rs`); the
  Ed25519 frame/input attestation primitive (`net-client/src/turn_gate.rs`); 2PC
  `evaluate_votes` (`coord/src/atomic.rs`); content-addressed NOTE store
  (`rbg/src/vfs.rs`).

**Near-term build (buildable now against the above + a current libservo — the headline
deliverables, contending with nothing in the kernel/circuit cutover):**

- §1 — The **`dregg`/`ocapn` URL-scheme registration + address-bar routing** (parse →
  resolver, else HTTP fall-through) with the cell-id/authority/finality origin badge in
  trusted chrome; the **`load_web_resource` → resolver** that dials, enlivens, invokes
  the serve-turn, and verifies the `AttestedResource` chain *before*
  `WebResourceLoad::intercept` (the keystone integration); the **`AttestedResource`
  envelope** (§1.2.1); the **`ServedResourceCell` app-toolkit template** (§1.2.2);
  freshness-as-client-policy over the monotone `finality_round`.
- §2 — instantiate `ResourceSet<RegionKey, DomAction>` as the per-DOM-region caveat;
  extend `Shell::share`'s `narrower` to carry it; route participant input through
  `prohibits` at the embedder dispatch boundary; mint observer/editor/driver roles as
  caveat literals; paint collaborative cursors as disjoint-region overlay surfaces (T1/T2
  give conflict-freedom + attribution free); package tab-handoff as cell-migration of the
  resumable description; log gate-decisions + frame-commits as the co-presence audit trail.
- §3 — the **`WebViewDelegate → Vec<Effect>` compiler** (the web instance of ADOS's
  tool-call→effect compiler, the headline new code); the **history-blocklace binding**
  (the surface cell as a blocklace creator whose web turns are seq-chained blocks with
  `resp_digest` payloads) + the federation anchor; the **narration-vs-truth web panel**
  (pure UI over `action_log` + the strand); the **volition-receipt executor gate** on
  value-moving `WebSubmit`.
- §4 — the read-cap-to-a-remote-surface dial path; the **Ed25519 frame attestation** (the
  net-PD ring carries bytes, `turn_gate.rs::verify_strict` carries the proof) + D's local
  `scene_admit`; the **thin-client display-cap / input-grant split** (§4.2); **surface
  migration** as the `delegate`-then-revoke turn with the continuity-receipt; the
  **render-cap computron ceiling** wired to `BudgetCeiling`.

**Research (named, with the precise lever, not laundered):**

- **The Goblins-interop adapter** (`netlayer.rs` §"Goblins-interop adapter", 2–4 weeks):
  shared concrete wire + Syrup codec + descriptor mapping. Bounded — one more `impl
  Netlayer` + a codec shim; the trait unchanged.
- **Willow range-reconciliation** (§1.4): zero implementation today; the range-fingerprint
  protocol is a *defined algorithm over the shipped receipt-stream Merkle tree*, a new
  `pipeline` conversation gated behind the headline fetch path.
- **TLS-transcript binding** (§3.2): binding `resp_digest` to the TLS session/cert so "the
  server provably served Y," not just "the surface received Y" — needs Servo to surface the
  TLS transcript at `load_web_resource` (upstream ask; the network-side dual of the §1
  pixel-clip assumption).
- **DOM-granularity gating** (the §2/§3 DOM-region-mediation seam): gating per-element
  interactions below the delegate's visibility; closure = host-injected content-script
  DOM-event turns (`EMBEDDED-WEB-SURFACE.md` §4.2(2)), never a Servo WebExtension (which
  does not exist). Same lever lifts the §2.3 **T3 single-focus → focus-set with per-region
  input routing** (a real Lean `Dregg2.Apps.Compositor` proof obligation).
- **Content-claim semantic checking** (§3.4): "the price was $40" is byte-pinned + a
  trusted extractor, not a content proof; closure = a per-domain golden extractor with a
  differential. dregg proves byte-identity; semantic interpretation is conventional (the
  *grounds-actions-not-cognition* boundary).
- **Live-process tab teleport** (§2.4/§4.3): three honest tiers, the floor
  (suspend/checkpoint/resume) buildable now, the top (migrating the renderer PD's address
  space) gated on Servo-on-seL4.
- **The unspoofable approval overlay** (§3.5) and **the confined-Servo seL4
  renderer/web-broker PD split** (`EMBEDDED-WEB-SURFACE.md` §5): the *guarantee* that a page
  cannot fake the volition prompt, and the kernel-enforced end-state where the renderer
  physically cannot reach the netlayer except through the cap-gating broker, both rise to
  full strength with the trusted-path compositor (`DREGG-DESKTOP-OS.md` §5, R3) and the
  Servo-on-seL4 port (Lean-runtime blocker + `std`-on-seL4 + GPU/framebuffer-cap). The
  volition *gate* and the §1–§4 PD/broker *factoring* are real/buildable now; the
  *unspoofable prompt* and the *confined image* are the labeled frontier with their exact
  dependencies. The reason §1–§4 pre-factor cleanly into PD + broker is the architectural
  argument that they are the right shape — not a claim either is near.

None of these are walls. Each is a labeled seam with a named closure lever (an upstream
Servo ask, a content-script lane, a golden extractor, the trusted-path compositor work, the
seL4 port), held to one worthwhile semantics, and none block the buildable core that makes
the distributed web-of-cells real on the `n = 1` firmament today.

---

## 6. The first rich demo — "the federated tab that carries its own proof"

A single watchable scene on the `n = 1` embedded executor that exercises all four
dimensions in one story, and *is* the evaluation artifact (the pug-handoff bar). It needs
only the near-term build above; the four dimensions show up as four moments.

1. **A `dregg://` page loads (the web-of-cells, §1).** The address bar takes
   `dregg://F/aliceblog/<read-swiss>`; the resolver dials F over the `inproc` (or `tcpip`)
   netlayer, enlivens the swiss against F's `SwissTable`, runs the `ServedResourceCell`'s
   serve-turn, and verifies the `AttestedResource` chain (`content_hash → receipt →
   receipt_stream_root → quorum-signed AttestedRoot`) *before* a byte reaches Servo. The
   origin badge — drawn by the shell from the ledger — reads *"cell aliceblog on federation
   F, read-only, finalized round 5512."* **The page carries its own proof; the badge names
   the exact object, not a hostname.**

2. **A second sovereign co-presents (co-presence, §2).** Alice shares the tab with Bob as a
   `{ * : Observe }` macaroon — a screenshare-as-cap. Bob's cursor appears in a reserved
   overlay region with his genuine `label_of` binding (Bob cannot paint a cursor labeled
   "Alice" — `LabelSpoof`, refused). Alice then narrows Bob to a scoped editor `{
   #comment-box : Fill }`; Bob can type in the comment field and *nothing else* (a click
   anywhere else is `prohibits → Err`, refused before Servo sees it). Alice revokes; **the
   very next composed frame omits Bob's surface — his glass goes dark this frame**, and the
   `RevokeDelegation` receipt is the provable "stopped sharing at frame N."

3. **An agent browses on the tab, and cannot lie (provable + agent-driven, §3).** Alice
   hands a read-only research agent a mandate (`navigate/fetch ⊆ {F + docs}`, `submit =
   none`, `budget ≤ 5000 computrons`). The agent navigates and fetches; the history
   **blocklace** grows `WebNav`/`WebFetch` blocks, each with a `to_url` and a `resp_digest`,
   time-travelable in the panel. The agent's loop *claims* "I also checked example.com" — the
   **narration-vs-truth panel** flags it **red**: no `WebNav` with `to_url=example.com`
   exists, a fabricated visit caught at the glass. The agent then tries to navigate to
   `evil.com` (outside its `navigate` caveat) and to enter a fetch loop: the first is
   **refused** (`OutOfMandate`, the fetch never leaves), the second hits the ceiling
   (`BudgetExhausted` at turn N, *before* it can hammer F). **The runaway is incapable, not
   scolded;** the pale ghost cannot lie about where it went.

4. **A value-moving submit needs a human (attested volition, §3.5).** Alice switches the
   agent to a shopping mandate and lets it assemble a $40 cart; at the final `WebSubmit {
   action_url=/buy, body_digest=$40-cart }` the executor **refuses for want of a
   volition-receipt.** The trusted-path overlay shows Alice the genuine `(/buy, $40)` of
   exactly what she'd approve; her gesture signs it; the submit commits **with proof a real
   human authorized this specific buy.** The agent's attempt to resubmit a swapped `$4000`
   body is a **body-mismatch refusal.** No silent checkout; no bait-and-switch.

5. **The tab walks to another node, and it's provably the same tab (distributed render +
   migration, §4).** Alice's tab — rendered on her home node — is also displayed on a wall
   panel D holding only a read-cap (the frame Ed25519-attested to the cell's committed root;
   D draws *its own* chrome from *its own* ledger sync, so the home node cannot spoof the
   badge). Alice then **migrates** the tab from her laptop to her desktop: a
   `delegate`-then-revoke turn carries the surface cell's `state_root` verbatim, and the
   migration receipt commits `state_root_before@laptop == state_root_after@desktop` — a light
   client (and the wall panel, whose read-cap points at the stable CellId) verifies the tab
   on the desktop is the *same* tab, **unfoolable by the pale ghost.** Rendering throughout
   was metered: "the home node rendered N frames for this cell at K computrons each — here
   are the receipts," bounded by a Stingray ceiling.

**The closing question the demo answers:** *"Where did this page come from, who touched it,
what did the agent really do, who approved the purchase, and is it the same tab after it
moved?"* — and every answer is a receipt, not a claim: the `AttestedResource` chain, the
co-presence frame log + grant/revoke receipts, the narration-vs-truth blocklace diff, the
signed volition-receipt, and the migration continuity-receipt. The most legible possible
answer to "why would I trust a federated, multi-party, agent-driven, remotely-rendered tab?"

---

*On the open web a link is a location you trust a server to fill, rendered on a machine you
trust, by an agent whose only record is its own narration. The distributed web-of-cells
replaces each trust with a capability and a receipt: a link is a `dregg://`/`ocapn://` sturdy
ref into a cell, a fetch is a verified turn the federation finalizes so the page carries its
own proof, the parties co-present on a surface each hold an attenuated revocable receipted cap
to a DOM region, the agent driving it is bounded at the gate and cannot lie about where it
went, and the node that renders it and the glass that displays it are slid apart along the
firmament's distance parameter with the frame attested to the cell's committed root. It is
`EMBEDDED-WEB-SURFACE.md`'s single-node browser-as-guest with the origin, the parties, the
driving loop, and the render end each carried out across the federation — the same
`SurfaceCapability`/cell/turn model, the same `granted ⊆ held` gate, the bounds the only thing
that moved. The seams are named with levers, the floors are the two the rest of dregg already
names, and nothing browses the web — dregg federates it.*

---

**Key file anchors (all absolute):**

*The model this extends:*
- `/Users/ember/dev/breadstuffs/docs/EMBEDDED-WEB-SURFACE.md` — the single-node Servo-`WebView`-as-`SurfaceCapability`-cell + `WebViewDelegate`-as-cap-gate this is the distributed case of
- `/Users/ember/dev/breadstuffs/docs/FIRMAMENT.md` + `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/lib.rs` — `Bounds { revocation_immediate, commit_synchronous, n }`, `LOCAL`, `distributed(n)`, the `Target::{Local,Distributed,Surface}` walk this doc slides along

*§1 the web-of-cells:*
- `/Users/ember/dev/breadstuffs/captp/src/netlayer.rs` — `Netlayer` trait + `dial`/`accept`, `EpochMinter`, `RelayNetlayer`, `ocapn_uri` (`OcapnLocation`/`OcapnSturdyRef`/`from_dregg`/`to_dregg`)
- `/Users/ember/dev/breadstuffs/captp/src/uri.rs` — `DreggUri` (the `dregg://` link)
- `/Users/ember/dev/breadstuffs/captp/src/sturdy.rs` — `SwissTable` enliven/check/revoke/`export_with_options` + `EnlivenError::opaque_message`
- `/Users/ember/dev/breadstuffs/captp/src/handoff.rs` — `HandoffCertificate` (recipient-targeted, nonce-once) — the third-party share primitive
- `/Users/ember/dev/breadstuffs/captp/src/gc.rs` + `/Users/ember/dev/breadstuffs/captp/src/store_forward.rs` — distributed-GC refcount + sealed relay transport
- `/Users/ember/dev/breadstuffs/types/src/lib.rs` (≈281–387) — `AttestedRoot`, `receipt_stream_root`, `merkle_root_of_receipt_hashes`, `ThresholdQC` (the attestation + the tree Willow reconciles)
- `/Users/ember/dev/breadstuffs/wasm/src/bindings_lightclient.rs` — `verify_history` (the in-tab light client the browser becomes)

*§2 co-presence:*
- `/Users/ember/dev/breadstuffs/starbridge-v2/src/surface.rs` / `shell.rs` / `compositor.rs` — `SurfaceCapability`, `Shell::share` (narrowing `GrantCapability`, widening = `DelegationDenied`), the T1/T2/T3 teeth + `FrameCommit` log, `label_of`, `source_state_root`, `identity_of`
- `/Users/ember/dev/breadstuffs/macaroon/src/resource.rs` — `ResourceSet<I,M>` intersect/`resolve`/`prohibits` (the per-DOM-region caveat lattice)
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/surface.rs` — `run_grant_turn` (the per-agent receipt chain co-presence rides)
- `/Users/ember/dev/breadstuffs/cell/tests/integration_migration.rs` — the cell-migration path tab-handoff is

*§3 provable + agent-driven:*
- `/Users/ember/dev/breadstuffs/docs/design-frontiers/ADOS.md` — the seam, budget=cell, narration-vs-truth tooth
- `/Users/ember/dev/breadstuffs/docs/design-frontiers/AGENT-SWARM-UX.md` — the cockpit + the S0–S6 slices + the §8 S5 volition split
- `/Users/ember/dev/breadstuffs/docs/DREGG-DESKTOP-OS.md` §5 — attested user-volition (the signed input-receipt premise) + the trusted-path compositor frontier
- `/Users/ember/dev/breadstuffs/docs/galaxybrain-dregg.md` — the sovereign-cell / attested-checkpoint history model
- `/Users/ember/dev/breadstuffs/starbridge-v2/src/swarm.rs` — `Swarm::run` (the seam, line 353; `SwarmActionOutcome` receipt_hash/computrons 240–256; `has_access` cap-gate 377; `OutOfMandate` 204)
- `/Users/ember/dev/breadstuffs/blocklace/src/lib.rs` — `Block`/`new_signed`/verified `insert` (causal-closure + seq-monotone + `EquivocationProof`) the history strand rides

*§4 distributed render + migration:*
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/distributed.rs` — `DistributedBacking` (real `Ledger`+`TurnExecutor`), `invoke`→`Bounds::distributed`, `delegate` rejects widening
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/compositor_pd.rs` — `Surface { owner, region, content_digest, source_state_root, focus }`, `Scene::scene_admit`, `label_of`, the `FIDELITY` F1 note
- `/Users/ember/dev/breadstuffs/sel4/dregg-firmament/src/process_kernel.rs` — `CapHandle { slot, epoch }`, `CapError::Forged` (the unforgeable cross-address-space handle the cross-network read-cap generalizes)
- `/Users/ember/dev/breadstuffs/sel4/dregg-pd/net-client/src/turn_gate.rs` — Ed25519 `verify_strict` over `[32 pk][64 sig][msg]` (the frame/input attestation primitive, verbatim)
- `/Users/ember/dev/breadstuffs/coord/src/shared_budget.rs` — `BudgetCeiling { ceiling, spent, remaining(), try_debit() → AllowanceExhausted }`, Stingray-bounded, overspend `f · ceiling`
- `/Users/ember/dev/breadstuffs/turn/src/executor/costs.rs` — `ComputronCosts` (every render-turn metered)
- `/Users/ember/dev/breadstuffs/coord/src/atomic.rs` — 2PC `evaluate_votes` (the migration-atomicity lever)
- `/Users/ember/dev/breadstuffs/rbg/src/vfs.rs` — content-addressed NOTE store ("the address IS the content" — migrating storage = the address travels)

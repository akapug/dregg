# deos-matrix

The protocol foundation of the **native deos Matrix client**.

This crate stands on the official **[matrix-rust-sdk]** (`matrix-sdk 0.18`) — the
pure-Rust SDK that provides the Matrix protocol (sync, room state, ruma events),
end-to-end encryption (vodozemac), login flows, and media. It is the same
foundation Element X, Fractal, and iamb build on. We do **not** re-implement the
protocol. Our value-add is the **gpui UI** (the `deos-chat` demo, below) and the
**deos confinement integration** — culminating in the **rehydratable membrane**
seam (`docs/deos/MEMBRANE-MERGE-SEAM.md`): a chat message can carry a
frustum-culled, cap-bounded fork of the deos world that recipients rehydrate,
drive real turns on, and stitch back.

[matrix-rust-sdk]: https://github.com/matrix-org/matrix-rust-sdk

## The deos-chat gpui UI (built, behind the `gui` feature)

A polished, **dregg-pilled** Matrix client — the chat IS the dregg world, not a
silo that happens to render inside deos.

- `ChatView` (`src/chat.rs`) — the kickass UI:
  - **Room-list sidebar**: encryption/DM glyphs, unread pills, topics, member
    counts, the logged-in user.
  - **Sender-grouped timeline**: day separators, avatar chips on a stable
    per-sender hue, **per-sender person-trust badges** ("verify the person, not
    the device"), **reactions** (aggregate pills, "mine" highlighted), **replies**
    (quoted-preview context), and **edit/redaction STATES** (an edited message
    shows "(edited)"; a redacted one shows a tombstone — never a destructive
    deletion).
  - **The STAR feature — membrane-bearing messages**: a message can embed a
    rehydratable cap-bounded fork of the deos world, rendered as a card with a
    **"▶ rehydrate & drive"** affordance (and a fail-closed "newer membrane" state).
  - **Composer**: `gpui_component::input::Input`/`InputState`, nheko keymap
    (**Enter sends, Shift-Enter newlines**, **↑ edits your last message**), a
    "⬡ attach membrane" action, and a **send-receipt** status line ("turn N ·
    cell:… · root …").
  - **Presence**: typing + read-receipt indicators (ephemeral view-state).
- `ChatSource` + `MockSource` (`src/source.rs`) — the synchronous data seam the UI
  renders against. `MatrixHandle` is a real `ChatSource` (live backend);
  `MockSource::seeded()` is a recorded sync so the UI is **real and exercisable
  offline** (no homeserver) — seeded with reactions, a reply, an edit, a
  redaction, and a real (mock) membrane-bearing message. The composer actually
  appends and the room cell's turn-count advances.
- `deos-chat` (`src/bin/chat.rs`) — the windowed demo (`cargo run --features gui
  --bin deos-chat`), or `--headless` for the CI-runnable data-path proof.
- `ChatSurface` (`src/cockpit_surface.rs`, feature `cockpit-surface`) — mounts the
  chat as a dock `CockpitSurface` in starbridge-v2 (forwarder ready-to-drop at
  `starbridge-v2/src/dock/chat_surface.rs`).

## The dregg-pilling — the chat IS the dregg world (`docs/deos/APPS-AS-CELLS.md` §3)

- **ROOM = a CELL** (`src/cell.rs::RoomCell`) — a room's durable core (membership,
  post-cap, history) is a `Cell`; its messages are the cell's *turn history*. The
  UI header shows the room cell id + turn-count.
- **IDENTITY = a CELL** (`src/cell.rs::IdentityCell`) — a Matrix user ties to a
  `CellId`; device keys are caps the identity cell holds. Person-trust
  (`Verified`/`Unverified`/`Changed`) is the identity *cell's* verdict, surfaced as
  a per-sender badge (a CHANGED identity shows loudly).
- **SEND = a TURN** (`src/cell.rs::SendReceipt`) — every send conceptually commits
  a turn against the room cell, leaving a verifiable receipt (sketch offline,
  byte-identical `TurnReceipt` on the deos side).
- **A MESSAGE CARRIES A MEMBRANE** (`src/membrane.rs`) — `MembraneEnvelope` rides
  in the `TimelineMessage` model; `MembraneHost` is the comms-PD trait (mint /
  rehydrate / drive / stitch). `MockMembraneHost` is an offline impl so the whole
  round-trip — **mint → serialize → rehydrate (fail-closed on root substitution &
  future version) → drive turns → stitch back** — is exercised in tests with NO
  deos executor. The design grounds in `docs/deos/MEMBRANE-MERGE-SEAM.md`.

## What is here today — the LIVE path (proven against a real homeserver)

- `MatrixClient` (`src/client.rs`) — the protocol surface a heavy Matrix user
  needs to be comfortable on **his own custom homeserver**:
  - **Custom-homeserver login**: a URL **or** a bare server-name (`.well-known`
    discovery), **password**, **access-token**, and **SSO/OIDC** (`login_sso`
    opens the homeserver's login page via the local-HTTP redirect flow;
    `sso_login_url` for clients that drive the browser themselves), all with a
    device display-name, session persistence, and restore.
  - **E2E a nheko user trusts**: device verification via `VerificationFlow`
    (`src/verification.rs` — request → SAS-emoji compare → confirm, the
    cross-signing "verify the person, not the device" flow), key **backup** status
    (`backup_enabled`), **recovery** (`enable_recovery` → a recovery key;
    `recover` on a new device), and **live person-trust** read from the crypto
    store's cross-signing state (`person_trust`).
  - **The features a heavy user expects**: **spaces** (room hierarchy,
    `spaces()`), **media** (send `send_attachment`, fetch `fetch_media` — into the
    existing image/attachment path), **room directory + search** + **join by
    id/alias** (`search_public_rooms`, `join`), **invites** (`invited_rooms`,
    `accept_invite`, `reject_invite`, `invite_user`), **power levels** + basic room
    settings (`power_levels`, `set_power_level`), and **threads** (folded in via
    `thread_root` extraction off the timeline).
  - Plus the core: encrypted `sync_once`/`sync_forever`, `joined_rooms()`,
    `recent_timeline()`, `send_text()`, `send_membrane()`, and **`send_object()`**
    — the generalized dregg-object send.
- `StoredSession` (`src/session.rs`) — JSON persistence of the SDK session +
  store location/passphrase; `restore()` rebuilds an authenticated client with no
  password.
- `MatrixWorker`/`MatrixHandle` (`src/worker.rs`) — the **sync→async bridge**
  (the iamb `worker.rs` shape). `MatrixHandle` is a **fully-implemented**
  `ChatSource` (login/sync/rooms/timeline/`send`/`send_membrane`/`whoami`), so the
  SAME `ChatView` runs over a live server or the mock — one impl swap.
- `deos-matrix-cli` (`src/bin/cli.rs`) — a headless harness: `login`,
  `login-token`, `rooms`, `timeline`, `send`, `send-membrane`, `send-object`,
  `spaces`, `directory`, `join`, `invites`, `accept-invite`, `power`,
  `encryption`, `whoami`.

```
deos-matrix-cli login --homeserver matrix.org --user @me:matrix.org   # bare name → .well-known
deos-matrix-cli rooms
deos-matrix-cli timeline --room '!abc:matrix.org' --limit 30
deos-matrix-cli send --room '!abc:matrix.org' --body 'hello'
deos-matrix-cli send-membrane --room '!abc:matrix.org'                # the deos-pilling, live
deos-matrix-cli send-object  --room '!abc:matrix.org' --kind transclusion   # any dregg object
deos-matrix-cli spaces                                                # the room hierarchy
deos-matrix-cli directory --query 'rust'                             # public room search
deos-matrix-cli join --room '#matrix:matrix.org'                     # join by alias
deos-matrix-cli invites                                              # pending invites
deos-matrix-cli encryption                                           # device id + key-backup health
```

### The membrane-over-real-Matrix wire shape

A membrane is **additive over plain Matrix**: it rides as a namespaced custom
field inside a normal `m.room.message`, so a non-deos client shows the human
fallback while a deos client extracts the typed envelope.

```json
{
  "msgtype": "m.text",
  "body": "[deos membrane · 4 cells · root e35bbee9 · cut@h100]",
  "software.ember.deos.membrane": { "version": 1, "frustum_root": …,
    "sturdyref": "dregg://fork/e35bbee9", "snapshot": …, "cut": …, "cursor": … }
}
```

### dregg semantic objects over Matrix (the generalized membrane)

The membrane was one object riding in a Matrix message. `src/object.rs`
generalizes that into a **`kind`-tagged envelope** that carries ANY dregg semantic
object, so a Matrix room becomes a dregg **object-exchange channel**. Every object
rides under one key (`software.ember.deos.object`) inside a normal
`m.room.message` with a human `body` fallback:

```json
{
  "msgtype": "m.text",
  "body": "[deos transclusion · e35bbee9.BALANCE_SUM = 0]",   // non-deos clients read this
  "software.ember.deos.object": {
    "version": 1,
    "kind": "transclusion",                                   // the tag selecting the payload
    "payload": { "source_cell": …, "field": "BALANCE_SUM", "value": "0", "bound_root": … }
  }
}
```

The kinds — each a *citation* the recipient materializes against its OWN authority,
each rendered specially in the timeline (`object_card` in `src/chat.rs`):

| `kind` | carries | rendered as |
|--------|---------|-------------|
| `membrane` | the rehydratable cap-bounded world-fork | the "rehydrate & drive" card (the star feature) |
| `cell` | a cell reference (id + label + kind) | an "open cell" action |
| `capability` | a shareable sturdyref + attenuated lineage | "accept into your powerbox" |
| `transclusion` | a provenanced quote of a cell field (value + bound root) | the live quoted value, "re-resolve live" |
| `affordance` | a named cap-gated action on a cell | a fireable button (gated on the required cap) |
| `receipt` | a turn-receipt digest (pre/post root + index) | the receipt summary, "verify" |

**Fail-closed forward-compat (the load-bearing tooth):** an object whose envelope
`version` is newer than this build, OR whose `kind` this build does not know, is
treated as **absent** — the message renders its text fallback and the rich object
is never half-acted-on. A deos client never guesses at a future object, never fires
an affordance it cannot fully understand. Every kind's mint → wire → extract →
render-shape round-trip is unit-tested (`object::tests::every_kind_round_trips…`)
and proven over a real server (`tests/live_homeserver.rs`).

### Proving the live path

The full live path is exercised by `tests/live_homeserver.rs` (**creds-gated**: a
no-op without `DEOS_MATRIX_TEST_{HS,USER,PASS}`, so `cargo test` is green in CI
without network). Point it at a throwaway homeserver (a single-container conduit
works — see the test's module docs) and it runs **build → login → restore → sync
→ list rooms → send (text + membrane + dregg-object×2) → read back → extract the
typed envelopes** against a real server. A second creds-gated test
(`live_servername_discovery_login`, gated on `DEOS_MATRIX_TEST_SERVERNAME`) proves
the **bare-server-name `.well-known` discovery** login path. The wire shapes are
also unit-proven offline (`client::tests::membrane_survives_the_room_message_wire_shape`,
`object::tests::every_kind_round_trips_through_the_wire`), so the send/receive
halves are verified agreeing on the format with or without a server.

**What is live vs mock-tested vs gated.** Custom-homeserver login (URL/server-name/
password/token/SSO), spaces, media, directory/join, invites, power levels, and
backup/recovery call the **real** SDK and are exercised live (creds-gated). The
**dregg-object** send/extract is proven both offline (the mock `ChatSource`
round-trips every kind) and live. **Device verification** (`VerificationFlow`)
needs a second device/user on a live encrypted session, so its handshake is
live-gated; what is unit-tested is the renderable **state-machine projection**
(`SasProgress`/`VerificationPhase` — the SAS-emoji comparison shape the UI drives).

## The standalone-workspace + async boundary (load-bearing)

The `Cargo.toml` opens with an empty `[workspace]` table, making this crate its
**own workspace root** — NOT a member of the repo-root workspace. This is the
same pattern as `servo-render/`. The reason: `matrix-rust-sdk` drags a heavy
tokio-async dependency tree (reqwest/hyper, vodozemac, rusqlite, ruma, hundreds
of transitive crates). Keeping it out of the repo-root workspace keeps the lean
dregg/Lean lanes and their shared `./target` untouched. `cd deos-matrix && cargo
build` builds into THIS crate's local target only.

**The async question, stated plainly:** `matrix-rust-sdk` is tokio-async; dregg's
embedded executor is **sync**. So the Matrix client is — and stays — a separate
crate/app that owns its own tokio runtime, exactly like `servo-render` owns its
own render path. The bridge to the deos/dregg side is a narrow request/response
channel (`src/worker.rs`), NOT a shared runtime.

## In the browser — wasm32 (`gpui_web`-rendered chat in a tab)

The `gpui` `ChatView` already renders on `gpui_web`, and `matrix-rust-sdk`
compiles to wasm. This crate builds to **`wasm32-unknown-unknown`** so the chat
data path runs in a browser tab.

**What runs on wasm32 today (built + tested):**

- The whole **data path** — `RoomSummary`/`TimelineMessage`/`MessageKind`, the
  `membrane`/`object`/`cell` wire types, `ChatSource`, and the offline
  **`MockSource`** (rooms, timeline, send, the membrane round-trip, send-as-turn).
  `cargo build --lib --target wasm32-unknown-unknown` is green, and
  `src/source.rs::wasm_tests::mock_chatsource_runs_on_wasm` runs the full
  `MockSource`-backed `ChatSource` under `wasm-pack test` (real wasm32 execution).
  So the chat UI has live data in a tab **with no server**.
- `MatrixClient::build`/`login_password`/`login_access_token`/`restore`/`sync`
  **compile** on wasm32, backed by the browser **IndexedDB** store
  (`indexeddb_store`) that replaces native SQLite, with reqwest-over-rustls and a
  `wasm-bindgen-futures` async model.

**The wasm async model (the worker question, on wasm).** The native sync→async
bridge — `MatrixWorker` (an OS thread + a multi-thread tokio runtime) and the
blocking `MatrixHandle` (`oneshot::blocking_recv`) — **cannot exist on
single-threaded wasm**: no OS threads, and you may not block the browser event
loop. So `worker.rs` is `cfg(not(target_family = "wasm"))`. On wasm the UI awaits
`MatrixClient`'s async methods directly on `wasm-bindgen-futures::spawn_local`
(the browser event loop is the runtime). Per-target deps make this clean: native
keeps `tokio` `rt-multi-thread` + `matrix-sdk` default (`sqlite` + `sso-login`);
wasm uses `tokio` `sync`+`macros` only and `matrix-sdk`
`default-features = false` + `e2e-encryption` + `indexeddb` + `js` (see
`Cargo.toml`'s `[target.…]` tables). `.cargo/config.toml` sets the
`getrandom_backend="wasm_js"` rustflag the transitive getrandom-0.3 needs.

**The live-in-browser-sync gap (honest).** The data path + mock **run** on wasm;
a live `login`→`sync` against a real homeserver **compiles** but is not yet
exercised end-to-end in a browser. What remains to wire:

1. **CORS** — a browser `fetch` to the homeserver requires the homeserver to send
   permissive CORS headers on `/_matrix/*` (Synapse/Conduit do for the
   client-server API, but a custom deployment must be checked). This is a
   homeserver-config matter, not a code change here.
2. **The wasm async driver** — replace the `MatrixHandle` call sites the UI uses
   with `spawn_local`-driven `MatrixClient` awaits (the data the UI reads is
   identical; only the bridge differs).
3. **Sliding-sync / sync loop on the event loop** — `sync_forever` is a native
   loop; in the browser it becomes a `spawn_local` task feeding the UI.
4. **SSO** — `login_sso` (the local-HTTP redirect catcher) is native-only; the
   browser path is the in-tab OAuth/OIDC redirect via `sso_login_url` (which
   compiles on wasm), still to be driven.

So: **the `ChatSource` + `MockSource` run on wasm32 (proven); live in-browser
sync is the next wire** (CORS check + the `spawn_local` driver over the
already-compiling `MatrixClient`).

## The deos integration design (real-now vs roadmap)

A Matrix client in deos is not merely "an app that talks to Matrix":

| Seam | Design | Status |
|------|--------|--------|
| **Identity-cell binding** | The user's Matrix identity (`@user:server` + device id) ties to a deos identity cell (`starbridge-apps/identity`). The access token + device keys are sealed to that cell rather than a plaintext `session.json`. | **Roadmap.** Today `StoredSession` is plaintext JSON (the headless stand-in). The seam is the `session` module's persistence trait, to be redirected at the identity cell. |
| **Device-keys-as-caps** | Matrix E2E device keys (cross-signing master/self/user-signing) are modeled as deos caps: holding the cap = the authority to act as that device / verify others. | **Roadmap.** The SDK already owns the keys in its crypto store; the cap-wrapping is a deos-side projection, not an SDK change. |
| **Confined comms-PD** | The whole client runs as a sandboxed firmament process-domain (`sel4/dregg-firmament/src/process_kernel.rs`): MMU-separated address space, no ambient network, talks to the rest of deos only over the worker channel. | **Roadmap** (the PD model exists and boots; this crate is not yet hosted in one). The `worker.rs` bridge is the PD's single seam, built today. |
| **Network as a net-cap** | The PD reaches the homeserver only through a granted network capability (`net/`), not ambient sockets. | **Roadmap.** Requires routing the SDK's reqwest transport through the net-cap; an HTTP-client injection point. |
| **Rooms as dockable surfaces** | Each room is a dockable surface in the deos WM/dock (the firmament `surface.rs` / compositor model). | **Roadmap** (UI phase). `RoomSummary`/timeline are the data the surface renders. |
| **Hermes as a room inhabitant** | Hermes (an agent) can sit in a room as a cap-bounded inhabitant — it sends/receives like any member but only with the caps it holds. | **Roadmap.** Falls out once the client core + cap model exist; Hermes just drives the worker handle under its caps. |

The honest split: **the protocol foundation is real now**; every deos seam above
is a projection over this crate (identity persistence, cap wrapping, PD hosting,
net-cap transport, dockable surfaces) — design landed, wiring is the next phases.

## Parity roadmap

1. **P0 — foundation (this crate):** homeserver config (URL + server-name
   discovery), password / access-token / SSO login, encrypted sync, room list,
   recent timeline, **send (text + membrane + dregg-object)**, session
   persistence/restore. ✅ builds, ✅ unit-tested, ✅ **proven live**.
2. **P1 — read/write timeline:** ✅ send is live; edits/reactions/replies are
   modeled (the mock seeds them; the SDK-UI `Timeline` would fold them in for
   *received* events), **threads** aggregated via `thread_root`. Read
   receipts/typing are live-source view-state.
3. **P2 — encryption UX:** ✅ device verification (`VerificationFlow` — SAS emoji +
   cross-signing; handshake live-gated, projection unit-tested), ✅ key backup +
   recovery, ✅ encrypted media (send/fetch attachment), ✅ live person-trust.
4. **P3 — discovery + login breadth:** ✅ SSO/OIDC login, ✅ spaces tree, ✅ room
   directory/search/join, ✅ invites (accept/reject/invite), ✅ power levels.
5. **P4 — media + notifications:** ✅ image/file/audio/video send + fetch; push/
   notification config is the remaining piece.
6. **P5 — gpui UI:** ✅ room-list pane, timeline view (membrane + every dregg-object
   kind rendered), composer — on the vendored `gpui-component` widgets; the
   verification-flow UI panel and rooms-as-dockable-surfaces are the next UI
   pieces.
7. **P6 — deos confinement:** host in the comms-PD, identity-cell session,
   device-keys-as-caps, net-cap transport, Hermes inhabitant. (Roadmap.)

## Dependency-weight honesty

`matrix-rust-sdk` is a large dependency: reqwest/hyper (HTTP), vodozemac (Olm/
Megolm E2E), rusqlite (bundled SQLite for state + crypto stores), the full ruma
event/api crate family, and their transitive trees. First clean build is on the
order of hundreds of crates and minutes of compile time. That cost is exactly why
this crate is an isolated workspace. It buys a production, audited Matrix
protocol + encryption implementation — not something to re-derive.

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

- `MatrixClient` (`src/client.rs`) — configure a homeserver + SQLite store (URL
  **or** bare server-name with `.well-known` discovery), **password login** and
  **access-token / SSO login** with session persistence, session restore,
  encrypted `sync_once`/`sync_forever`, `joined_rooms()`, `recent_timeline()`,
  **`send_text()`**, and **`send_membrane()`** — the membrane rides as a custom
  field inside an ordinary `m.room.message`. The receive side extracts it back
  into a typed `MembraneEnvelope` (fail-closed on a future wire version).
- `StoredSession` (`src/session.rs`) — JSON persistence of the SDK session +
  store location/passphrase; `restore()` rebuilds an authenticated client with no
  password.
- `MatrixWorker`/`MatrixHandle` (`src/worker.rs`) — the **sync→async bridge**
  (the iamb `worker.rs` shape). `MatrixHandle` is a **fully-implemented**
  `ChatSource` (login/sync/rooms/timeline/`send`/`send_membrane`/`whoami`), so the
  SAME `ChatView` runs over a live server or the mock — one impl swap.
- `deos-matrix-cli` (`src/bin/cli.rs`) — a headless harness: `login`,
  `login-token`, `rooms`, `timeline`, `send`, `send-membrane`, `whoami`.

```
deos-matrix-cli login --homeserver https://matrix.org --user @me:matrix.org
deos-matrix-cli rooms
deos-matrix-cli timeline --room '!abc:matrix.org' --limit 30
deos-matrix-cli send --room '!abc:matrix.org' --body 'hello'
deos-matrix-cli send-membrane --room '!abc:matrix.org'   # the deos-pilling, live
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

### Proving the live path

The full live path is exercised by `tests/live_homeserver.rs` (**creds-gated**: a
no-op without `DEOS_MATRIX_TEST_{HS,USER,PASS}`, so `cargo test` is green in CI
without network). Point it at a throwaway homeserver (a single-container conduit
works — see the test's module docs) and it runs **build → login → restore → sync
→ list rooms → send (text + membrane) → read back → extract the typed envelope**
against a real server. The wire shape itself is also unit-proven offline
(`client::tests::membrane_survives_the_room_message_wire_shape`), so the
send/receive halves are verified agreeing on the format with or without a server.

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
   discovery), password **and** access-token login, encrypted sync, room list,
   recent timeline, **send (text + membrane)**, session persistence/restore.
   ✅ builds, ✅ unit-tested, ✅ **proven live** (`tests/live_homeserver.rs`).
2. **P1 — read/write timeline:** adopt `matrix-sdk-ui`'s `Timeline` (edits,
   reactions, replies, threads folded in for *received* events — send is live);
   read receipts/typing over the live source.
3. **P2 — encryption UX:** device verification (SAS emoji + cross-signing),
   key backup, recovery; encrypted media.
4. **P3 — discovery + login breadth:** SSO/OIDC login, spaces tree, room
   directory/join, invites.
5. **P4 — media + notifications:** image/file/voice send+receive, thumbnails,
   push/notification client.
6. **P5 — gpui UI:** room-list pane, timeline view, composer, verification flow —
   on the vendored `gpui-component` widgets, rooms as dockable surfaces.
7. **P6 — deos confinement:** host in the comms-PD, identity-cell session,
   device-keys-as-caps, net-cap transport, Hermes inhabitant.

## Dependency-weight honesty

`matrix-rust-sdk` is a large dependency: reqwest/hyper (HTTP), vodozemac (Olm/
Megolm E2E), rusqlite (bundled SQLite for state + crypto stores), the full ruma
event/api crate family, and their transitive trees. First clean build is on the
order of hundreds of crates and minutes of compile time. That cost is exactly why
this crate is an isolated workspace. It buys a production, audited Matrix
protocol + encryption implementation — not something to re-derive.

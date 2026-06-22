# deos-matrix

The protocol foundation of the **native deos Matrix client**.

This crate stands on the official **[matrix-rust-sdk]** (`matrix-sdk 0.18`) — the
pure-Rust SDK that provides the Matrix protocol (sync, room state, ruma events),
end-to-end encryption (vodozemac), login flows, and media. It is the same
foundation Element X, Fractal, and iamb build on. We do **not** re-implement the
protocol. Our value-add is the **gpui UI** (deferred to the `gpui-component`
vendoring) and the **deos confinement integration** (below).

[matrix-rust-sdk]: https://github.com/matrix-org/matrix-rust-sdk

## What is here today (the headless foundation, proven to build)

- `MatrixClient` (`src/client.rs`) — configure a homeserver + SQLite store,
  password login with session persistence, session restore, encrypted
  `sync_once`/`sync_forever`, `joined_rooms()`, `recent_timeline()`.
- `StoredSession` (`src/session.rs`) — JSON persistence of the SDK session +
  store location/passphrase.
- `MatrixWorker`/`MatrixHandle` (`src/worker.rs`) — the **sync→async bridge**
  (the iamb `worker.rs` shape): a synchronous caller sends a typed request and
  blocks on a oneshot reply; the worker owns the tokio runtime. This is the seam
  the confined comms-PD will cross.
- `deos-matrix-cli` (`src/bin/cli.rs`) — a headless harness: `login`, `rooms`,
  `timeline`, `whoami`. No UI required to exercise the protocol path.

```
deos-matrix-cli login --homeserver https://matrix.org --user @me:matrix.org
deos-matrix-cli rooms
deos-matrix-cli timeline --room '!abc:matrix.org' --limit 30
```

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

1. **P0 — foundation (this crate):** homeserver config, password login,
   encrypted sync, room list, recent timeline. ✅ builds.
2. **P1 — read/write timeline:** adopt `matrix-sdk-ui`'s `Timeline` (edits,
   reactions, replies, threads folded in); send messages; read receipts/typing.
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

# The self-hosting loop — develop dregg INSIDE deos

deos hosts its own development: a running `dregg-node`, the cockpit attached to
it, a firmament-backed editor whose saves are verified ledger turns, and a real
terminal running `cargo`/`git` over a live PTY — all inside the deos image.

This document records the RUN that demonstrates both real halves in one cockpit
view AND the FULL single loop — edit a real source file in the firmament editor,
save it (a verified ledger turn), and have the terminal's `rustc`/`cargo` compile
THAT VERY EDIT — closed by the FirmamentFs↔disk dual-write.

## The two real halves

* **(a) Editor — firmament over the LIVE World.** The editor pane
  ([`dock::editor_surface::EditorPane::firmament_over`]) edits a sovereign
  *cell*, not a disk file. A save sets the buffer and calls the editor's real
  `save`, which commits a cap-gated `SetField` turn through the verified
  executor, leaving a genuine `TurnReceipt`. The save count on the status line is
  the live on-ledger receipt count — the same ledger the cockpit's cell inspector
  reads.

* **(b) Terminal — a live alacritty PTY.** The terminal pane
  ([`dock::terminal_surface::TerminalPane::spawn`]) runs a real child process on a
  real PTY. The default bake runs `cargo --version`; its genuine stdout lands in
  the cell grid.

The view that mounts both is `starbridge_v2::self_hosting::SelfHostingView`.

## Reproduce (headless bake, RUNS + ASSERTS + screenshots)

```sh
cd starbridge-v2
cargo build --features native-full --bin starbridge-v2
./target/debug/starbridge-v2 --render-self-hosting self-hosting-loop --render-size 1600x1000
# optional: --self-hosting-cmd git --version    (run a different real command)
```

The bake is self-checking — it FAILS (non-zero exit) unless BOTH hold:

* the editor save grew the live `TurnReceipt` count (a real verified turn), and
* the terminal command's genuine output reached the grid (a real PTY child).

A passing run prints both proofs and writes `self-hosting-loop.png`. The captured
frame (`starbridge-v2/self-hosting-loop.png`, 3200×2000) shows the editor pane
(status line: `saved main.rs (… bytes) — N saves · on-ledger FirmamentFs
(cell=file, save=receipted turn)`) beside the terminal pane (the real
`cargo …-nightly (…)` banner), under the live image header (height · cells ·
receipts).

A representative run:

```
OK headless SELF-HOSTING render -> self-hosting-loop.png (3200x2000, logical 1600x1000)
  PROOF (a) editor: save fired a real turn — receipts 5 -> 6 on-ledger …
  PROOF (b) terminal: live alacritty PTY ran `cargo --version` INSIDE deos —
            grid shows: "cargo 1.98.0-nightly (…)"
```

## The FULL single loop — the FirmamentFs↔disk dual-write

The two halves above each touch a different store: the editor saves to CELLS
(ledger turns) while `cargo`/`rustc` read DISK. The **FirmamentFs↔disk
dual-write** closes that gap into one loop.

`FirmamentFs` gains an OPTIONAL disk-mirror root (off by default —
`enable_disk_mirror(root)`). When set, every `save` — AFTER the verified turn
commits (the cell update is the durable, receipted **source of truth**) — ALSO
writes the decoded new content to `<root>/<path>`, a **derived read-mirror** the
legacy disk-reading toolchain compiles from. Enabling the mirror also backfills
every already-seeded file to disk, so the toolchain sees the genesis content from
the first command. A mirror write error surfaces (fail-loud): the disk can never
silently desync from the ledger. With the root unset, behavior is exactly
cell-only (no disk writes at all) — the existing firmament tests and the original
`--render-self-hosting` bake are unchanged.

The cell is always the source of truth; the disk file is a read-mirror the
toolchain compiles. The save remains a single cap-gated `SetField` turn leaving a
`TurnReceipt` — the dual-write rides on top of the committed turn, it does not
replace or weaken it.

### Reproduce the FULL loop

```sh
cd starbridge-v2
cargo build --features native-full --bin starbridge-v2
./target/debug/starbridge-v2 --render-self-hosting-full self-hosting-loop-full
```

This bake wires the firmament editor's saves to a temp mirror dir and points a
live interactive `sh` PTY at that same dir, then drives the FULL loop and asserts
THREE hard proofs (it FAILS non-zero unless all hold):

1. **receipt** — the editor save grew the live `TurnReceipt` count (the edit is a
   real verified turn on the live ledger);
2. **disk-mirror** — the on-disk mirror file (`<dir>/main.rs`) now holds the `v2`
   edit (the cell's new content was dual-written to disk);
3. **terminal-sees-it** — the live `sh` PTY runs `rustc main.rs -o prog && ./prog`
   over the mirrored file and the compiled program's stdout (`v2`) reaches the
   grid (the toolchain compiled THAT VERY EDIT).

A representative run:

```
OK headless SELF-HOSTING-FULL render -> self-hosting-loop-full.png (3200x2000, logical 1600x1000)
  THE FULL SINGLE LOOP RAN: editor edit → receipted turn → disk mirror → terminal toolchain saw it.
  PROOF (receipt): save fired a real cap-gated SetField turn — receipts 5 -> 6 on-ledger.
  PROOF (disk-mirror): the cell's v2 content was dual-written to disk at <dir>/main.rs …
  PROOF (terminal-sees-it): the live sh PTY ran `rustc main.rs && ./prog` over the mirrored file — ./prog printed: v2.
```

The captured frame (`starbridge-v2/self-hosting-loop-full.png`) shows the terminal
pane with `./prog` printing `v2` followed by `cat main.rs` showing the v2 source,
under the live image header reading `6 receipts · on-ledger` — the editor's
receipted save compiled by the terminal's real toolchain, in one image.

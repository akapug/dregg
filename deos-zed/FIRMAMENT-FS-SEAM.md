# The FirmamentFs seam

deos-zed is a real code editor that edits real files inside deos. Its single
load-bearing design decision is that **the editor never touches a filesystem
directly** — every file operation goes through one trait, `Fs`
(`src/fs.rs`). Today that trait is backed by `RealFs` (`std::fs`). Tomorrow it is
backed by `FirmamentFs`, where a file is a sovereign cell and a save is a
receipted dregg turn. That transition is a **one-impl change**: no editor, no
file-tree, no UI code moves.

This document specifies that seam.

## The trait

```rust
pub trait Fs: Send + Sync + 'static {
    fn load(&self, path: &Path) -> Result<String>;
    fn save(&self, path: &Path, content: &str) -> Result<()>;
    fn read_dir(&self, path: &Path) -> Result<Vec<DirEntry>>;
    fn metadata(&self, path: &Path) -> Result<Metadata>;
    fn backend_label(&self) -> &'static str;
}
```

It mirrors the subset of Zed's `fs::Fs` that an editor actually exercises:
`load` on open, `save` on save, `read_dir` + `metadata` for the file tree. It is
kept small and synchronous on purpose — the editor already runs file I/O off a
background spawn, and a synchronous trait is far simpler to satisfy with a
`FirmamentFs` whose `save` is a turn.

The editor holds an `Arc<dyn Fs>` and depends on nothing else. `backend_label()`
is surfaced in the editor's status line, so which backing store is in use is
**visible to the user** — the firmament swap is observable, not silent.

## RealFs (today)

`std::fs`, with a write-to-temp-then-rename `save` so a crash mid-write can never
truncate the user's file. This is the default and it works now: the demo seeds a
real file, the editor opens + edits + saves it, and the bytes on disk change
(verified independently of the seam — see `cargo run --bin demo -- --verify`).

## FirmamentFs (the next step)

A file becomes a **cell**; a save becomes a **receipted turn**. The mapping:

| `Fs` method     | firmament realization |
|-----------------|-----------------------|
| `load(path)`    | resolve `path` → a read cap through the directory namespace; read the cell's content substance. A read is authority-checked but does not mutate state, so it needs no turn. |
| `save(path, c)` | a dregg **turn**: exercise a write cap over the file-cell, replacing its content; the turn leaves a verifiable **receipt**. "Save" becomes an attestable event, not an opaque syscall. |
| `read_dir(p)`   | `DirectoryCell::list()` — the capability-scoped listing (`rbg/src/directory.rs`). Holding the directory cap *is* the authority to enumerate it. |
| `metadata(p)`   | `DirectoryCell::get(name)` → resolve to a sturdy ref + cell kind. |

### The path → cap namespace

A path like `/proj/src/main.rs` resolves component-by-component through
`DirectoryCell`s (`rbg/src/directory.rs`):

- Each `DirectoryCell` maps names → `(cap, version)` via `get(name)`, mutates via
  an atomic CAS `swap(name, version, cap)`, and lists via `list()`.
- Directories contain directories (recursive scoping), so a path walk is a chain
  of `get` calls ending at a leaf **file-cell**, whose content substance is the
  editable text.
- The **root `DirectoryCell` cap is the editor's mount point**. The editor can
  only see and edit what that cap reaches — which is exactly the firmament
  confinement story: one cap across distance
  (`sel4/dregg-firmament/`), the n=1 collapse of local-seL4-cap ↔ distributed
  dregg-cap ↔ surface.

### What `save` actually is

`save` is the one mutating operation, so it is the one that becomes a turn:

1. Build a turn that spends a write cap on the file-cell and binds the new
   content as the cell's next content substance (Σδ=0 over the content-cell: the
   old content note is nullified, the new one created).
2. Submit through the executor; obtain the **receipt** — the proof-carrying
   token that this exact edit happened under this exact authority.
3. The receipt is the editor's "saved" acknowledgement, and it is independently
   verifiable: a light client can confirm the file now holds this content
   **without trusting the editor**.

This is the whole point of the seam. It upgrades "the editor wrote a file" from
an unwitnessed side effect into a **witnessed, attenuable, receipted turn**.

## Why FirmamentFs is a stub today

`src/fs/firmament.rs` implements the trait but every method returns a clear
"needs a live executor handle + mounted root `DirectoryCell` cap from the host
deos image" error. Those handles come from the host (starbridge-v2's `World`),
not from deos-zed standalone — deos-zed deliberately has no dependency on the
executor crates so it stays buildable and demoable on its own. The constructor
takes those handles as opaque parameters precisely so the seam is *shaped*: when
the host wires the real `DirectoryCap` + `ExecutorHandle`, the four method bodies
in `firmament.rs` are filled against the live executor and **that file is the
only thing that changes**.

## How the host wires it

In starbridge-v2, the cockpit holds a live `World` with the embedded executor
and a mounted root directory. To make the editor firmament-backed:

1. Construct a `FirmamentFs::new(root_cap, executor)` (signature lands when the
   host types are threaded in) and box it as `Arc<dyn Fs>`.
2. Hand that `Arc<dyn Fs>` to `EditorPane::new(...)`
   (`starbridge-v2/src/dock/editor_surface.rs`) instead of `RealFs::arc()`.

Nothing in the editor or the file tree changes. The editor that was editing disk
files is now editing cells, with receipted saves, because the only thing that
ever spoke to a filesystem was the `Fs` trait.

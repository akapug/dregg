# microkit-patch — the one-function tool change that lets the 5-PD assembly BOOT

The stock Microkit tool maps every PD program-image segment with 4 KiB pages
(`tool/microkit/src/capdl/builder.rs`: `let page_size = PageSize::Small;`). For
the `executor` PD — whose embedded verified Lean closure is ~300 MiB of ELF — that
is ~83,000 individual frame caps, and the on-device CapDL initialiser exhausts the
kernel's `ROOT_CNODE_SIZE_BITS` (panics `OutOfSlots`) before any PD runs.

`0001-2mib-elf-image-pages.patch` changes `add_elf_to_spec` to map each image
segment with the LARGEST page (2 MiB `PageSize::Large`) its alignment + remaining
span permits, falling back to 4 KiB for the unaligned prefix/tail. The executor
PD's segments are already 2 MiB-aligned (its `.cargo/config.toml` links with
`-z max-page-size=0x200000`), so the ~300-MiB image collapses to ~170 Large frames
+ small tails — 2,322 total objects, a 91 MiB initial task. Small-page PD images
are unchanged (no aligned 2 MiB run exists → every step takes the Small branch).

The tool and the on-device `initialiser.elf` share an rkyv spec schema, so the
tool MUST be built from the same source as the SDK's bundled initialiser. The SDK
(`microkit-sdk-2.2.0`) ships the initialiser from the **microkit `2.2.0` tag**
(`seL4/rust-sel4` rev `cf43f5d`). `microkit-2.2.0-patched` is this patch applied
to that exact tag and built — schema-compatible with the SDK initialiser. (A build
from a later `2.2.0-dev` commit pins `au-ts/rust-sel4 33cb1325`, whose spec the
2.2.0 initialiser cannot read → it panics `ArchivedOption::unwrap()` on None at
`init_logging` before any output.)

## Install / reproduce

```sh
# Install the patched tool over the SDK binary (back up the original first):
cp $HOME/sel4-sdk/microkit-sdk-2.2.0/bin/microkit{,.orig}
cp microkit-2.2.0-patched $HOME/sel4-sdk/microkit-sdk-2.2.0/bin/microkit

# Build + boot the real 5-PD assembly (the verified turn runs status:2 ok:1):
cd ../../..          # -> sel4/
make run-assembly-real
```

To rebuild the tool from source instead of using the prebuilt binary:

```sh
git -C <microkit-checkout> worktree add /tmp/microkit-2.2.0 2.2.0
cd /tmp/microkit-2.2.0 && git apply <this-dir>/0001-2mib-elf-image-pages.patch
cd tool/microkit && cargo build --release
# -> /tmp/microkit-2.2.0/target/release/microkit
```

## Upstreamable

This is a general improvement (it benefits any PD with a large, page-aligned
image and is a no-op otherwise), not a dregg-specific hack — a candidate for an
upstream Microkit PR (map image segments with the largest aligned page).

`assembly-boot-evidence.log` is the verbatim serial of the clean 5-PD boot.

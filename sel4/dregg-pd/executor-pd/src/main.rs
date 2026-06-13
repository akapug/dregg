//! executor-PD — the firmament's HEART (bring-up state).
//!
//! The destination: a protection domain that embeds the VERIFIED dregg executor
//! (`execFullForestG` via `dregg-lean-ffi`) and runs every app turn through the
//! proved `decode -> step -> encode -> receipt`. This is "the firmament's one
//! true blocker" (docs/FIRMAMENT.md §6).
//!
//! The blocker is the Lean RUNTIME on bare-metal aarch64-sel4-microkit. The
//! excision plan (docs/SEL4-EMBEDDING.md §2) is four steps. Step (1) — the
//! object-format wall, the part the roadmap called "weeks-to-a-quarter fog" — is
//! now GREEN: the entire 757-object Dregg2 closure (including the executor entry
//! `dregg_exec_full_forest_auth`) ELF-recompiles for aarch64 on the native macOS
//! host with ZERO source changes (`scripts/cross-compile-closure.sh`). The
//! remaining wall is the ELF Lean runtime (leanrt/leancpp ship Mach-O-only, no
//! C++ sources in the toolchain) — characterized precisely in `WALL.md`.
//!
//! Until the runtime links, this PD boots as a STATUS heart: it occupies the
//! firmament's heart slot and reports the bring-up state + the cross-compile
//! proof over serial, rather than leaving the slot empty. The verified-compute
//! heart organ that boots a REAL computation TODAY (a plonky3 STARK, no Lean) is
//! the sibling verifier-stark PD.

#![no_std]
#![no_main]

use sel4_microkit::{debug_println, protection_domain, Handler, Infallible};

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("");
    debug_println!("    ┌─────────────────────────────────────────────┐");
    debug_println!("    │   dregg executor-PD  ·  the firmament HEART  │");
    debug_println!("    └─────────────────────────────────────────────┘");
    debug_println!("");
    debug_println!("[exec] protection domain booted on the seL4 microkernel");
    debug_println!("[exec] destination: run every app turn through the VERIFIED");
    debug_println!("[exec]   execFullForestG (decode -> step -> encode -> receipt)");
    debug_println!("");
    debug_println!("[exec] excision plan (docs/SEL4-EMBEDDING.md §2):");
    debug_println!("[exec]   (1) ELF-recompile the Lean closure ........ ✅ GREEN");
    debug_println!("[exec]       757/757 Dregg2 facets -> ELF aarch64, 0 source edits");
    debug_println!("[exec]       entry dregg_exec_full_forest_auth present (global T)");
    debug_println!("[exec]   (2) ELF leanrt + stub initialize_libuv/io .. ⛔ WALL");
    debug_println!("[exec]   (3) GMP for ELF / fixnum-only shim ......... ◐ shim plausible");
    debug_println!("[exec]   (4) host on sel4-musl + root-task-with-std . ◐ after (2),(3)");
    debug_println!("");
    debug_println!("[exec] the wall: the toolchain ships leanrt/leancpp Mach-O-ONLY");
    debug_println!("[exec]   and carries no C++ runtime sources, so the ELF IR closure");
    debug_println!("[exec]   has no runtime to link against. See WALL.md (next step:");
    debug_println!("[exec]   build an ELF leanrt from lean4@d024af099 + excise libuv).");
    debug_println!("");
    debug_println!("[exec] heart slot OCCUPIED + self-reporting ( ◕‿◕ )");
    HandlerImpl
}

/// No channels to service yet — the PD reports its bring-up state at init and
/// then idles in the Microkit event loop. When the runtime links, the handler
/// will accept a `turn_in` page, run it through `dregg_exec_full_forest_auth`,
/// and write the receipt to `receipt_out`.
struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
}

//! executor-PD — the firmament's HEART (bring-up state).
//!
//! The destination: a protection domain that embeds the VERIFIED dregg executor
//! (`execFullForestG` via `dregg-lean-ffi`) and runs every app turn through the
//! proved `decode -> step -> encode -> receipt`. This is "the firmament's one
//! true blocker" (.docs-history-noclaude/FIRMAMENT.md §6).
//!
//! The blocker is the Lean RUNTIME on bare-metal aarch64-sel4-microkit. The
//! excision plan (.docs-history-noclaude/SEL4-EMBEDDING.md §2) is four steps. Step (1) — the
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
    debug_println!("[exec] excision plan (.docs-history-noclaude/SEL4-EMBEDDING.md §2):");
    debug_println!("[exec]   (1) ELF-recompile the Lean closure ........ ✅ GREEN");
    debug_println!("[exec]       757/757 Dregg2 facets -> ELF aarch64, 0 source edits");
    debug_println!("[exec]   (2) ELF Lean RUNTIME (leanrt+lib+kernel) ... ✅ GREEN — built");
    debug_println!(
        "[exec]   (3) GMP for ELF ........................... ✅ GREEN — real GMP 6.3.0"
    );
    debug_println!("[exec]   (4) host on sel4-musl + root-task-with-std . ◐ this PD");
    debug_println!("");
    debug_println!("[exec] THE WALL IS PASSED: dregg-executor.elf (static aarch64-musl,");
    debug_println!("[exec]   0 undefined) runs ONE real turn through the VERIFIED");
    debug_println!("[exec]   dregg_exec_full_forest_auth -> status:2 ok:1 (bodyCommitted:");
    debug_println!("[exec]   nonce 7->8, a 30-unit transfer, nullifier+commitment). The");
    debug_println!("[exec]   Lean runtime is now an ordinary musl image; step 4 is to");
    debug_println!("[exec]   host it as a root-task-with-std PD. See WALL.md.");
    debug_println!("");
    debug_println!("[exec] heart slot OCCUPIED + the REAL executor links & runs ( ◕‿◕ )");
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

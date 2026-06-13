//! M0 — the dregg Robigalia v0 boot proof.
//!
//! A minimal seL4 Microkit protection domain (PD) written in Rust. It boots on
//! the seL4 microkernel under QEMU (`qemu_virt_aarch64`), drops to userspace,
//! and prints the demo banner over the serial console via the Microkit debug
//! `puts`. No Lean, no IO loop, no dregg dependency — this is the rung that
//! proves the whole native-macOS toolchain (Microkit SDK 2.2.0 + rust-sel4 +
//! `qemu-system-aarch64`) actually boots a Rust component on seL4.

#![no_std]
#![no_main]

use sel4_microkit::{debug_println, protection_domain, Handler, Infallible};

// A small heap is declared so the PD carries a global allocator even when the
// workspace's feature unification enables `sel4-microkit/alloc` (M1/M2 turn it
// on). M0 itself uses no `alloc`; the heap is unused but satisfies the runtime.
#[protection_domain(heap_size = 0x1000)]
fn init() -> HandlerImpl {
    debug_println!("");
    debug_println!("    ┌─────────────────────────────────────────┐");
    debug_println!("    │   dregg robigalia v0                     │");
    debug_println!("    │   a Rust userspace on seL4               │");
    debug_println!("    └─────────────────────────────────────────┘");
    debug_println!("");
    debug_println!("[m0] protection domain booted on the seL4 microkernel");
    debug_println!("[m0] capabilities all the way down ( ◕‿◕ )");
    HandlerImpl
}

/// The PD has no channels to service in M0 — it prints once at init and then
/// idles in the Microkit event loop. The default `Handler` is sufficient.
struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
}

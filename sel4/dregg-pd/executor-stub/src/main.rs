//! The executor-PD SEAT in the 5-PD firmament assembly (`sel4/dregg.system`).
//!
//! This is a minimal placeholder PD holding the firmament HEART seat until the
//! verified Lean executor (`execFullForestG`, `metatheory/`) can cross-compile
//! for `aarch64-sel4-microkit` (THE blocker — the Lean-runtime bottom-half ELF
//! recompile + libuv excision + musl host, .docs-history-noclaude/SEL4-EMBEDDING.md §2 /
//! .docs-history-noclaude/FIRMAMENT.md §6). It does NOT run verified compute; the verifier-stark
//! PD is the bankable verified-compute heart organ in this assembly.
//!
//! What it DOES do, faithfully, is occupy the executor's exact place in the cap
//! partition (.docs-history-noclaude/FIRMAMENT.md §2): it maps the `turn_in` (R) and `commit_out`
//! (RW) shared regions the real executor will use — and NOTHING else (no device
//! cap, no NIC cap) — touches them to prove the caps are live, and prints the
//! partition over serial. The assembly therefore BOOTS as a real multi-PD image
//! with the executor seat held + wired.

#![no_std]
#![no_main]

use sel4_microkit::{debug_println, memory_region_symbol, protection_domain, Handler, Infallible};

// The shared regions this PD's cap partition grants it (mirrors dregg.system):
//   turn_in    — R : the de-enveloped, signature-checked turn from ingress.
//   commit_out — RW: the commit-log entry handed to persist.
// memory_region_symbol resolves the setvar'd vaddr the Microkit loader patched.
fn turn_in() -> *const u8 {
    memory_region_symbol!(turn_in_vaddr: *mut [u8], n = 0x100000).as_ptr() as *const u8
}
fn commit_out() -> *mut u8 {
    memory_region_symbol!(commit_out_vaddr: *mut [u8], n = 0x400000).as_ptr() as *mut u8
}

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("[executor] dregg executor-PD SEAT booted — the firmament heart seat");
    debug_println!("[executor]   cap partition: turn_in (R), commit_out (RW); NO device/NIC cap");

    // Prove the mapped regions are live: read the first byte of turn_in (R) and
    // write a sentinel into commit_out (RW). seL4 would fault this PD if it did
    // not hold these caps — so reaching the next line IS the cap partition,
    // enforced.
    let staged = unsafe { core::ptr::read_volatile(turn_in()) };
    unsafe { core::ptr::write_volatile(commit_out(), 0xE0) }; // 'E' for executor seat
    let echo = unsafe { core::ptr::read_volatile(commit_out() as *const u8) };
    debug_println!(
        "[executor]   turn_in[0]={:#04x} read OK; commit_out[0]<-{:#04x} write OK",
        staged,
        echo
    );

    debug_println!(
        "[executor]   verified turn path (execFullForestG) is BLOCKED on the Lean ELF port (§2);"
    );
    debug_println!("[executor]   the verifier-stark PD is the bankable verified-compute heart organ this image ships.");
    debug_println!("[executor]   awaiting ingress→executor signal (channel id 1) …");
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;

    // ingress signals "a signature-checked turn is staged in turn_in" on
    // channel id 1; the real executor would decode→step→encode and signal
    // persist on id 2. The seat acknowledges the edge so the channel is live.
    fn notified(&mut self, channels: sel4_microkit::ChannelSet) -> Result<(), Self::Error> {
        for channel in channels.iter() {
            debug_println!(
                "[executor]   notified on channel {} (turn staged)",
                channel.index()
            );
        }
        Ok(())
    }
}

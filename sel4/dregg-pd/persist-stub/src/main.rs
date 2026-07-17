//! The persist-PD SEAT in the 5-PD firmament assembly (`sel4/dregg.system`).
//!
//! The real persist-PD is the SOLE holder of the storage-device cap, backing
//! `redb` over a raw block cap with the snapshot⊕overlay + root tooth
//! (`persist/src/snapshot.rs`, .docs-history-noclaude/SEL4-EMBEDDING.md §3, .docs-history-noclaude/FIRMAMENT.md §2).
//! That block-cap backend is the §3 ecosystem work; until it lands this seat
//! holds the persist place in the cap partition so the assembly BOOTS as a real
//! multi-PD image.
//!
//! Cap partition (.docs-history-noclaude/FIRMAMENT.md §2): it maps `commit_out` (R) — the
//! executor→persist commit-log handoff — and NOTHING else (no block-device cap
//! YET; the device cap will land HERE and only here). It touches the region to
//! prove the cap is live and services the executor→persist notification channel.

#![no_std]
#![no_main]

use sel4_microkit::{debug_println, memory_region_symbol, protection_domain, Handler, Infallible};

// The only shared region the persist seat's cap partition grants: commit_out (R).
fn commit_out() -> *const u8 {
    memory_region_symbol!(commit_out_vaddr: *mut [u8], n = 0x400000).as_ptr() as *const u8
}

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("[persist] dregg persist-PD SEAT booted — the durable-store seat");
    debug_println!("[persist]   cap partition: commit_out (R); the storage-device cap will land HERE (sole holder)");

    // Prove the commit_out cap is live: read the byte the executor seat wrote
    // (0xE0). seL4 faults this PD if it lacks the cap — reaching the print IS
    // the partition enforced.
    let committed = unsafe { core::ptr::read_volatile(commit_out()) };
    debug_println!(
        "[persist]   commit_out[0]={:#04x} read OK (executor seat's sentinel)",
        committed
    );

    debug_println!(
        "[persist]   redb-over-block-cap + snapshot⊕overlay root tooth is the §3 block-cap port;"
    );
    debug_println!("[persist]   no other PD can ever touch the disk — the partition makes durable state unforgeable.");
    debug_println!("[persist]   awaiting executor→persist commit signal (channel id 1) …");
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;

    // The executor signals "a commit-log entry is ready in commit_out" on this
    // PD's channel id 1; the real persist-PD writes the redb transaction before
    // the turn returns (the n=1 synchronous-commit property, FIRMAMENT §3).
    fn notified(&mut self, channels: sel4_microkit::ChannelSet) -> Result<(), Self::Error> {
        for channel in channels.iter() {
            debug_println!(
                "[persist]   notified on channel {} (commit ready)",
                channel.index()
            );
        }
        Ok(())
    }
}

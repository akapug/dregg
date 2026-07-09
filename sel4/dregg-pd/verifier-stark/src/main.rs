//! verifier-stark — a firmament verifier PD (seL4 protection domain).
//!
//! Capability partition (the firmament's verifier trust boundary): this PD is
//! pure compute over bytes. It holds NO prover authority over dregg state, NO
//! storage cap, NO NIC cap — the seL4-enforced form of "a verifier runs with
//! no callback into a prover" (verifier/src/lib.rs).
//!
//! The vendored on-boot STARK selftest demo has been removed; this PD now boots
//! and observes the one-way executor→verifier edge.

#![no_std]
#![no_main]

extern crate alloc;

use sel4_microkit::{debug_println, protection_domain, Channel, ChannelSet, Handler, Infallible};

// The executor→verifier edge (dregg.system: executor id 3 → verifier id 1). It is
// ONE-WAY ("a bundle is staged / verdict ready"): the verifier NEVER calls out to
// a prover — this edge IS the no-prover-callback property (FIRMAMENT §2).
const EXECUTOR_TO_VERIFIER: Channel = Channel::new(1);

#[protection_domain(heap_size = 0x100000)]
fn init() -> HandlerImpl {
    debug_println!("[stark] dregg verifier-stark PD booted");
    // vendored STARK selftest demo removed — nothing to run on boot.
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;

    // The executor signals (one-way) that a turn committed and a bundle is staged.
    // Acknowledge it; the default Handler::notified panics on any notification,
    // which would fault this PD when the executor's verdict-ready edge fires.
    fn notified(&mut self, channels: ChannelSet) -> Result<(), Self::Error> {
        for channel in channels.iter() {
            if channel == EXECUTOR_TO_VERIFIER {
                debug_println!(
                    "[stark] executor→verifier signal (ch {}) — bundle staged / verdict-ready edge observed",
                    channel.index()
                );
            } else {
                debug_println!("[stark] notified on channel {}", channel.index());
            }
        }
        Ok(())
    }
}

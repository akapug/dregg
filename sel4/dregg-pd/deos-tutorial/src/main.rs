//! THE deos ONBOARDING — a polished, multi-screen, INTERACTIVE tutorial that
//! boots in a QEMU window on seL4. The newcomer presses SPACE / UP / DOWN to
//! walk a six-screen arc teaching deos from first principles (a capability is
//! constructive knowledge; your boundaries are theorems), rendering REAL deos
//! data shapes. "Like loading AOL as a 7-year-old, except in the Good Cyberpunk
//! Timeline, plus smalltalk-tier." (docs/desktop-os-research/GRAPHICAL-SEL4-BOOT.md.)
//!
//! ## What this PD is
//!
//! It GROWS the compositor-fb PD's bytes->glass mechanism (fw_cfg + ramfb
//! scanout) into a real UX. The PD:
//!   1. is the SOLE holder of QEMU's fw_cfg engine MMIO cap + a 4 MiB DMA
//!      framebuffer region (`fb.rs`) -- it draws an 800x600 frame QEMU scans out;
//!   2. is the SOLE holder of a virtio-keyboard-device's virtio-mmio region + DMA
//!      region + IRQ (`keyboard.rs`) -- the SAME device-cap discipline the
//!      net-driver PD (sel4/dregg-pd/net) uses for virtio-net, here for HUMAN
//!      input. A keypress raises the IRQ -> the PD's `notified()` runs -> the
//!      screen advances and the framebuffer repaints, live;
//!   3. renders six polished screens (`screens.rs`) with a COMPLETE 8x8 font
//!      (`font.rs`) -- every printable ASCII glyph, real g/j/p/q/y descenders.
//!
//! The cap partition IS the boundary: this PD holds the display + keyboard caps
//! and NOTHING else (no NIC, no other PD's memory). seL4 faults any stray access.
//!
//! ## Fidelity (honestly labeled)
//!
//! The pixels are real (genuine ramfb scanout of a framebuffer this PD solely
//! holds), the keyboard is a real (emulated) virtio device this PD solely holds,
//! and the navigation is real. The deos DATA shown (a cell's four substances, an
//! affordance's cap-gate, a dregg:// reference) is a FAITHFUL PREVIEW with real
//! shapes -- the LIVE in-VM executor running real turns behind these surfaces is
//! the named frontier (Rung 3, GRAPHICAL-SEL4-BOOT.md §4 / SEL4-EMBEDDING.md §2),
//! beyond this onboarding.

#![no_std]
#![no_main]

extern crate alloc;

use sel4_microkit::{debug_println, protection_domain, Channel, ChannelSet, Handler, Infallible};

mod fb;
mod font;
mod keyboard;
mod screens;

use fb::Canvas;
use keyboard::{Keyboard, Nav};

/// The keyboard IRQ channel (matches `<irq id="0">` in deos-tutorial.system).
const KBD: Channel = Channel::new(0);

/// The running tutorial: which screen is showing, plus the optional keyboard.
struct Tutorial {
    screen: usize,
    kbd: Option<Keyboard>,
}

impl Tutorial {
    /// Repaint the current screen into the framebuffer (which QEMU scans out).
    fn paint(&self) {
        let mut canvas = unsafe { Canvas::map() };
        screens::draw(&mut canvas, self.screen);
    }

    fn apply(&mut self, nav: Nav) {
        let before = self.screen;
        match nav {
            Nav::Next => {
                self.screen = (self.screen + 1) % screens::N_SCREENS;
            }
            Nav::Prev => {
                self.screen = (self.screen + screens::N_SCREENS - 1) % screens::N_SCREENS;
            }
            Nav::None => {}
        }
        if self.screen != before {
            debug_println!(
                "[deos-tutorial]   -> screen {}/{}",
                self.screen + 1,
                screens::N_SCREENS
            );
            self.paint();
        }
    }
}

impl Handler for Tutorial {
    type Error = Infallible;

    /// A keyboard IRQ: drain the events, fold to a Nav, advance + repaint, then
    /// re-arm the IRQ so the next keypress notifies us again.
    fn notified(&mut self, _channels: ChannelSet) -> Result<(), Self::Error> {
        if let Some(dev) = self.kbd.as_mut() {
            let nav = keyboard::drain(dev);
            self.apply(nav);
        }
        // Re-arm: acknowledge the kernel-level IRQ so it can fire again.
        let _ = KBD.irq_ack();
        Ok(())
    }
}

#[protection_domain(heap_size = 0x40000)]
fn init() -> Tutorial {
    debug_println!("");
    debug_println!("    +-----------------------------------------------+");
    debug_println!("    |   deos . robigalia v0  --  THE ONBOARDING     |");
    debug_println!("    |   deos-tutorial PD : ramfb + virtio-keyboard  |");
    debug_println!("    +-----------------------------------------------+");
    debug_println!("[deos-tutorial] booted -- SOLE holder of the fw_cfg display cap + the");
    debug_println!("[deos-tutorial] virtio-keyboard cap (the interactive graphical edge).");

    let mut tut = Tutorial { screen: 0, kbd: None };

    // (A) DRAW the welcome screen FIRST, so the bytes are present the instant
    // ramfb starts scanning out.
    tut.paint();
    debug_println!(
        "[deos-tutorial]   painted screen 1/{} ({}x{} XRGB8888)",
        screens::N_SCREENS,
        fb::WIDTH,
        fb::HEIGHT
    );

    // (B) configure ramfb so QEMU scans out this PD's framebuffer.
    if !fb::configure_ramfb() {
        debug_println!("[deos-tutorial]   (boot with `make run-tutorial`; the window needs -device ramfb)");
        return tut;
    }

    // (C) bring up the keyboard. Real input is the headline; if the slot is empty
    // (the image booted without -device virtio-keyboard-device), the tutorial
    // still shows screen 1 and names virtio-input as the immediate next rung.
    tut.kbd = keyboard::init();
    if tut.kbd.is_some() {
        // Ack the first IRQ so subsequent keypresses schedule notified().
        let _ = KBD.irq_ack();
        debug_println!("[deos-tutorial]   INTERACTIVE: SPACE/UP/DOWN navigate the six screens.");
    } else {
        debug_println!("[deos-tutorial]   NON-INTERACTIVE this boot (no keyboard device).");
        debug_println!("[deos-tutorial]   next rung: wire -device virtio-keyboard-device on mmio slot 30.");
    }

    debug_println!("[deos-tutorial]   deos is on glass, and it listens. ( o_o )");
    tut
}

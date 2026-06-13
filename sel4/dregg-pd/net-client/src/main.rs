//
// net-client — the firmament's network edge, CLIENT half (docs/FIRMAMENT.md §3,
// §6; docs/SEL4-EMBEDDING.md §4).
//
// This PD turns "the NIC is up" into "a turn arrives over TCP". It runs a
// smoltcp Interface over the shared ring buffers it shares with the driver PD
// (../net/), acquires an IPv4 address by DHCP, listens on TCP port 5555, and on
// each received frame applies the SignedTurn admission gate: an envelope is
//
//     [ 32-byte Ed25519 public key ][ 64-byte signature ][ message bytes ]
//
// and the PD Ed25519-verifies (`verify_strict`, the strict/cofactorless check
// dalek recommends) the signature over the message under the embedded key
// BEFORE the turn would ever cross the firmament boundary into the executor.
// Bad signatures are REFUSED at the edge — the seL4-enforced form of "the
// ingress PD de-envelopes + Ed25519-checks a SignedTurn before handing it to
// the executor; signature-bad turns never reach the verified core". A plain
// (non-envelope) line is echoed, so a bare `nc`/`ping` smoke test also passes.
//
// The Ed25519 path is ed25519-dalek 2 (no_std) — the SAME crate major the dregg
// SDK signs `SignedTurn` with (sdk/src/cipherclerk.rs) — so the check here is
// the deployed verification, not a parallel one.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;

use smoltcp::iface::{Config, Interface, SocketSet};
use smoltcp::socket::dhcpv4;
use smoltcp::socket::tcp;
use smoltcp::time::Instant;
use smoltcp::wire::{EthernetAddress, HardwareAddress, IpCidr};

use sel4_abstract_allocator::WithAlignmentBound;
use sel4_abstract_allocator::basic::BasicAllocator;
use sel4_driver_interfaces::net::GetNetDeviceMeta;
use sel4_microkit::{
    Channel, ChannelSet, Handler, Infallible, debug_println, memory_region_symbol,
    protection_domain,
};
use sel4_microkit_driver_adapters::net::client::Client as NetClient;
use sel4_shared_memory::SharedMemoryRef;
use sel4_shared_ring_buffer::RingBuffers;
use sel4_shared_ring_buffer_smoltcp::DeviceImpl;

mod config;
mod turn_gate;

use config::channels;

type NetDevice = DeviceImpl<WithAlignmentBound<BasicAllocator>>;

const RX_BUFFER_SIZE: usize = 4096;
const TX_BUFFER_SIZE: usize = 4096;

/// The on-device edge state: the smoltcp device, interface, socket set, and the
/// synthetic monotonic clock. smoltcp wants a strictly non-decreasing `Instant`;
/// with no timer PD wired here we advance a millisecond counter on every crank,
/// which is sufficient to drive DHCP retransmit + TCP state without a real RTC.
struct EdgeHandler {
    device: NetDevice,
    iface: Interface,
    sockets: SocketSet<'static>,
    dhcp_handle: smoltcp::iface::SocketHandle,
    tcp_handle: smoltcp::iface::SocketHandle,
    millis: i64,
    have_addr: bool,
    cranks: u32,
}

impl EdgeHandler {
    fn now(&self) -> Instant {
        Instant::from_millis(self.millis)
    }

    /// One crank: advance the clock, drain RX/TX through smoltcp, handle the
    /// DHCP lease, then service the TCP echo + SignedTurn admission listener.
    fn crank(&mut self) {
        self.millis += 10;
        self.cranks = self.cranks.wrapping_add(1);
        let ts = self.now();

        let _ = self.iface.poll(ts, &mut self.device, &mut self.sockets);

        // A sparse heartbeat: the first few cranks witness the device TX/RX
        // readiness (the edge is live and shuttling frames), without flooding
        // the serial.
        if self.cranks <= 3 {
            debug_println!(
                "[net-client] crank #{} dev.can_tx={} dev.can_rx={}",
                self.cranks,
                self.device.can_transmit(),
                self.device.can_receive()
            );
        }

        // DHCP: pick up a newly-acquired (or lost) lease and reflect it onto the
        // interface's address + default route.
        let event = self
            .sockets
            .get_mut::<dhcpv4::Socket>(self.dhcp_handle)
            .poll();
        if let Some(ev) = event {
            match ev {
                dhcpv4::Event::Configured(cfg) => {
                    debug_println!(
                        "[net-client] DHCP bound: ip={} router={:?} — the edge has an address",
                        cfg.address,
                        cfg.router
                    );
                    self.iface.update_ip_addrs(|addrs| {
                        addrs.clear();
                        let _ = addrs.push(IpCidr::Ipv4(cfg.address));
                    });
                    if let Some(router) = cfg.router {
                        let _ = self.iface.routes_mut().add_default_ipv4_route(router);
                    } else {
                        self.iface.routes_mut().remove_default_ipv4_route();
                    }
                    self.have_addr = true;
                }
                dhcpv4::Event::Deconfigured => {
                    debug_println!("[net-client] DHCP lease lost");
                    self.iface.update_ip_addrs(|addrs| addrs.clear());
                    self.iface.routes_mut().remove_default_ipv4_route();
                    self.have_addr = false;
                }
            }
        }

        self.service_tcp();

        // Re-poll so any bytes we queued onto the TCP socket egress promptly.
        let _ = self.iface.poll(self.now(), &mut self.device, &mut self.sockets);

        // Self-sustaining poll while we still need a DHCP lease: kick the driver
        // so it flushes our just-queued TX (the DISCOVER/REQUEST) and notifies
        // us back on the OFFER/ACK — each round-trip advances DHCP one step.
        // With no timer PD this is how the handshake makes progress; once bound,
        // we fall back to cranking purely on driver RX notifications.
        if !self.have_addr {
            channels::DRIVER.notify();
        }
    }

    /// The TCP echo + SignedTurn admission gate. (Re-)listens on port 5555,
    /// and on a received chunk either Ed25519-checks a SignedTurn envelope
    /// (the firmament-boundary gate) or echoes a plain line (the smoke test).
    fn service_tcp(&mut self) {
        let socket = self.sockets.get_mut::<tcp::Socket>(self.tcp_handle);

        if !socket.is_open() {
            if let Err(e) = socket.listen(config::ECHO_PORT) {
                debug_println!("[net-client] tcp listen error: {:?}", e);
            } else {
                debug_println!(
                    "[net-client] TCP listening on :{} — a turn can now arrive over TCP",
                    config::ECHO_PORT
                );
            }
        }

        if socket.can_recv() {
            // Pull up to one MTU-ish chunk and decide what it is.
            let mut buf = [0u8; 1600];
            let n = socket.recv_slice(&mut buf).unwrap_or(0);
            if n > 0 {
                let reply = turn_gate::handle_chunk(&buf[..n]);
                if socket.can_send() {
                    let _ = socket.send_slice(&reply);
                }
            }
        }
    }
}

impl Handler for EdgeHandler {
    type Error = Infallible;

    fn notified(&mut self, _channels: ChannelSet) -> Result<(), Self::Error> {
        // Any notification (a frame from the driver) cranks the stack. While we
        // still need a DHCP lease, spin a bounded number of cranks within this
        // dispatch: each inner crank pokes the higher-priority driver to drain
        // the shared RX ring, so the DHCP OFFER/ACK is picked up without a timer
        // PD. The spin is bounded so a notification can never wedge the PD.
        // One crank per dispatch, then RETURN to Recv. Busy-spinning here would
        // starve the driver's RX delivery: the driver places the OFFER/ACK into
        // the shared rx_used ring from ITS notified() handler, which only runs
        // when we yield. So we crank once (consuming whatever RX is ready,
        // queuing the next DHCP step + poking the driver) and go back to Recv;
        // the driver's next RX notification drives the following crank.
        self.crank();
        Ok(())
    }
}

#[protection_domain(heap_size = 2 * 1024 * 1024)]
fn init() -> EdgeHandler {
    debug_println!("[net-client] init — the smoltcp edge PD is up");

    // The MAC comes from the driver over a protected (PPC) call — the driver is
    // the sole holder of the NIC cap; we learn our hardware address from it.
    let mut net_meta = NetClient::new(channels::DRIVER);
    let mac = net_meta
        .get_mac_address()
        .expect("driver returned a MAC address");
    let mac_address = EthernetAddress(mac.0);
    debug_println!("[net-client] MAC from driver: {:02x?}", mac.0);

    let notify_driver: fn() = || channels::DRIVER.notify();

    // The smoltcp phy::Device over the shared ring buffers (the `Provide` role
    // to the driver's `Use` role) + a bounce-buffer allocator over the shared
    // client DMA region.
    let dma_region = unsafe {
        SharedMemoryRef::<'static, _>::new(memory_region_symbol!(
            virtio_net_client_dma_vaddr: *mut [u8],
            n = config::VIRTIO_NET_CLIENT_DMA_SIZE
        ))
    };
    let bounce_buffer_allocator =
        WithAlignmentBound::new(BasicAllocator::new(dma_region.as_ptr().len()), 1);

    let rx_ring = RingBuffers::from_ptrs_using_default_initialization_strategy_for_role(
        unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_rx_free: *mut _)) },
        unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_rx_used: *mut _)) },
        notify_driver,
    );
    let tx_ring = RingBuffers::from_ptrs_using_default_initialization_strategy_for_role(
        unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_tx_free: *mut _)) },
        unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_tx_used: *mut _)) },
        notify_driver,
    );

    let caps = {
        let mut c = smoltcp::phy::DeviceCapabilities::default();
        c.medium = smoltcp::phy::Medium::Ethernet;
        c.max_transmission_unit = 1500;
        c
    };

    let mut device = DeviceImpl::new(
        Default::default(),
        dma_region,
        bounce_buffer_allocator,
        rx_ring,
        tx_ring,
        16,
        2048,
        caps,
    )
    .expect("smoltcp DeviceImpl over the shared rings");

    // The interface, seeded with our MAC. No static IP — DHCP fills it in.
    let mut iface_config = Config::new(HardwareAddress::Ethernet(mac_address));
    iface_config.random_seed = 0x6472_6567_6731; // "dregg1" — deterministic, houyhnhnm
    let iface = Interface::new(iface_config, &mut device, Instant::from_millis(0));

    // Sockets: one DHCPv4 client, one TCP listener with its rx/tx buffers.
    let mut sockets = SocketSet::new(vec![]);
    let dhcp_handle = sockets.add(dhcpv4::Socket::new());

    let tcp_socket = {
        let rx = tcp::SocketBuffer::new(vec![0u8; RX_BUFFER_SIZE]);
        let tx = tcp::SocketBuffer::new(vec![0u8; TX_BUFFER_SIZE]);
        tcp::Socket::new(rx, tx)
    };
    let tcp_handle = sockets.add(tcp_socket);

    debug_println!(
        "[net-client] DHCP + TCP sockets armed; cranking on driver notifications (port {})",
        config::ECHO_PORT
    );

    let mut handler = EdgeHandler {
        device,
        iface,
        sockets,
        dhcp_handle,
        tcp_handle,
        millis: 0,
        have_addr: false,
        cranks: 0,
    };

    // One crank at init: queue the first DHCP DISCOVER and (via the !have_addr
    // branch in crank) poke the driver to flush it. Then RETURN — a Microkit PD
    // must leave init() and block on Recv for the driver's RX notification (the
    // OFFER) to schedule its notified() handler. We must NOT busy-loop DHCP here:
    // the driver can only deliver RX once we are blocked receiving.
    handler.crank();

    handler
}

// Silence the unused-on-this-path warning while keeping the field as a readable
// liveness witness for future ingress wiring.
#[allow(dead_code)]
fn _assert_channel_is_used(_c: Channel) {}

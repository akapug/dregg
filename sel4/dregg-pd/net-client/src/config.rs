//
// net-client config — channel ids + shared-region sizes, mirroring the driver's
// half (../net/src/config.rs) and the net-full.system assembly.
//

pub mod channels {
    use sel4_microkit::Channel;

    /// The driver PD. In net-full.system this client's `id=0` end binds to the
    /// driver's `id=1` end (the driver's CLIENT channel). Notifications both
    /// ways crank the ring buffers; the protected (PPC) direction fetches the
    /// MAC via sel4-microkit-simple-ipc.
    pub const DRIVER: Channel = Channel::new(0);
}

/// The shared DMA region the driver copies RX frames into / TX frames out of.
/// Must match the driver's VIRTIO_NET_CLIENT_DMA_SIZE.
pub const VIRTIO_NET_CLIENT_DMA_SIZE: usize = 0x200_000;

/// The TCP port the echo + SignedTurn-admission listener binds. Reached from the
/// host via `-netdev user,hostfwd=tcp::5555-:5555`.
pub const ECHO_PORT: u16 = 5555;

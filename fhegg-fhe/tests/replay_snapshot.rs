//! Restart-safe replay-set framing teeth.
//!
//! The snapshot is a canonical corruption/context detector. Rollback resistance
//! is deliberately left to the caller's transactional or monotonic storage.

use fhegg_fhe::attestation::{ReplayGuard, ReplaySnapshotError, SnapshotReplayGuard};
use sha2::{Digest, Sha256};

fn refresh_checksum(wire: &mut [u8]) {
    let body_end = wire.len() - 32;
    let domain = b"fhegg/replay-snapshot/v1";
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    hasher.update((body_end as u64).to_be_bytes());
    hasher.update(&wire[..body_end]);
    let checksum: [u8; 32] = hasher.finalize().into();
    wire[body_end..].copy_from_slice(&checksum);
}

#[test]
fn replay_snapshot_roundtrips_and_preserves_refusal_after_restart() {
    let context = [0x51; 32];
    let first = [0x11; 32];
    let second = [0x22; 32];
    let mut guard = SnapshotReplayGuard::new(context);
    assert!(guard.check_and_record(second));
    assert!(guard.check_and_record(first));
    assert!(!guard.check_and_record(first));
    assert_eq!(guard.revision(), 2);
    assert_eq!(guard.len(), 2);

    let wire = guard.to_wire_bytes();
    let mut restored = SnapshotReplayGuard::from_wire_bytes(context, &wire).unwrap();
    assert_eq!(restored, guard);
    assert_eq!(restored.to_wire_bytes(), wire, "canonical sorted snapshot");
    assert_eq!(restored.snapshot_digest(), guard.snapshot_digest());
    assert!(!restored.check_and_record(first), "replay survives restart");
    assert!(restored.check_and_record([0x33; 32]));
    assert_eq!(restored.revision(), 3);
}

#[test]
fn replay_snapshot_refuses_context_corruption_truncation_and_noncanonical_order() {
    let context = [0x61; 32];
    let mut guard = SnapshotReplayGuard::new(context);
    assert!(guard.check_and_record([0x10; 32]));
    assert!(guard.check_and_record([0x20; 32]));
    let wire = guard.to_wire_bytes();

    assert_eq!(
        SnapshotReplayGuard::from_wire_bytes([0x62; 32], &wire),
        Err(ReplaySnapshotError::ContextMismatch)
    );
    for end in 0..wire.len() {
        assert!(SnapshotReplayGuard::from_wire_bytes(context, &wire[..end]).is_err());
    }

    let mut corrupt = wire.clone();
    corrupt[60] ^= 1;
    assert_eq!(
        SnapshotReplayGuard::from_wire_bytes(context, &corrupt),
        Err(ReplaySnapshotError::ChecksumMismatch)
    );

    // Even an attacker who recomputes the public corruption checksum cannot
    // make a noncanonical/duplicate set parse.
    let mut reversed = wire;
    let first = reversed[56..88].to_vec();
    let second = reversed[88..120].to_vec();
    reversed[56..88].copy_from_slice(&second);
    reversed[88..120].copy_from_slice(&first);
    refresh_checksum(&mut reversed);
    assert_eq!(
        SnapshotReplayGuard::from_wire_bytes(context, &reversed),
        Err(ReplaySnapshotError::NonCanonicalOrder)
    );
}

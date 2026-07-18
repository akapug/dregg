//! The GPU-RESIDENT pipeline — upload once, compute resident, download once (the performance north star).
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §3. OWNED by the `gpu_arena` lane. Wraps
//! `bfv_gpu`. This is the fix for the transfer-bound one-shot "loss": data stays on-device across the
//! pipeline so the fold becomes free and the transfer amortizes over the whole computation.
#![allow(dead_code, unused_variables)]

use crate::bfv_lean::LeanCiphertext;

/// A wgpu device + a resident ciphertext buffer pool.
pub struct Arena;
/// An on-device ciphertext-set — NEVER downloaded until `download` is called.
pub struct ResidentHandle;

/// None if there is no wgpu adapter (headless).
pub fn arena() -> Option<Arena> {
    todo!("gpu_arena lane: wgpu device + resident pool")
}
impl Arena {
    /// The ONE upload transfer.
    pub fn upload(&self, cts: &[LeanCiphertext]) -> ResidentHandle {
        todo!("gpu_arena lane: upload to a resident buffer")
    }
    /// Fold WITHOUT download — the fold is now free (data already resident).
    pub fn fold_resident(&self, h: &ResidentHandle) -> ResidentHandle {
        todo!("gpu_arena lane: on-device fold, no readback")
    }
    /// The ONE readback.
    pub fn download(&self, h: &ResidentHandle) -> Vec<LeanCiphertext> {
        todo!("gpu_arena lane: readback")
    }
}

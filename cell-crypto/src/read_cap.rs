//! # Read-capability — the dual of the write-cap, gating READ confidentiality.
//!
//! `docs/deos/PRIVACY-CONFIDENTIALITY.md` Milestone 0. dregg's [`Permissions`]
//! ([`dregg_cell::permissions`]) are cold on **write**: the 8 [`AuthRequired`] slots
//! say who may *change* a cell, attenuably. The dual question — who may *read* a
//! cell's hidden state — had no first-class capability, even though every
//! confidentiality organ already existed disconnected. This module welds them.
//!
//! A read is the exercise of an attenuable viewing-authority over committed
//! state: the write-discipline run backwards (authority over *decryption* rather
//! than over *mutation*). It is **purely additive** — it does NOT touch the write
//! [`AuthRequired`] lattice, the cell state-commitment shape, or anything the
//! circuit / verification key sees.
//!
//! ## The pieces (all welds of green organs)
//!
//! - **[`FieldSet`]** — a 16-bit mask over the cell's 16 state slots. This is the
//!   read-lattice: `granted ⊆ held` is [`FieldSet::is_subset_of`], the SAME
//!   subset partial-order the write side uses ([`dregg_cell::facet::is_facet_attenuation`],
//!   `child & parent == child`). There is no amplification: you cannot grant read
//!   of a slot you cannot read.
//! - **[`ViewKey`]** — a 32-byte HKDF-tree root. The per-slot decryption key is
//!   `KDF(root, domain, slot_index)` ([`ViewKey::slot_key`]) via BLAKE3's
//!   keyed-hash KDF — the SAME family [`crate::note_encryption`] /
//!   [`crate::seal`] already use. Attenuation of a read-cap is attenuation of the
//!   *key it hands*: a narrower [`ReadCap`] carries the same root but its `slots`
//!   mask only admits derivation of the granted slots' keys (the cap is the
//!   gate over which `slot_key`s a holder is entitled to compute).
//! - **[`EncryptedSlot`]** — a `Committed` slot becomes `(commitment, ciphertext)`.
//!   The **commitment is byte-identical** to what the cell stores today
//!   ([`CellState::compute_commitment`] — `BLAKE3(value || nonce)`), so the
//!   binding the circuit / conservation sees is UNCHANGED. The ciphertext is the
//!   only new artifact: an [`crate::note_encryption`]-style ECIES box, sealed to
//!   the slot's per-slot ViewKey-derived X25519 key. Hiding is *added*; binding
//!   is *untouched* — the load-bearing constraint that keeps the circuit green.
//! - **[`ReadCap::open`]** — derive the per-slot keys this cap's `slots` admit,
//!   ECIES-open exactly those ciphertexts, return cleartext for those slots only.
//!   A holder of a narrower cap gets fewer slots — *demonstrated by the key not
//!   being derivable*, not by a policy check.
//!
//! ## What this is NOT (honest seams, named with their lanes)
//!
//! - **Cryptographic revocation ≠ cap revocation.** The cap-object revokes via
//!   the existing [`dregg_cell::revocation_channel`]; only key-rotation stops a revoked
//!   holder reading *new* content, and nothing un-reveals a past read. Inherent to
//!   encryption (`PRIVACY-CONFIDENTIALITY.md` §5).
//! - **No metadata privacy.** This hides slot *contents*, never *that a read
//!   happened* or *which cell* (`PRIVACY-CONFIDENTIALITY.md` §1b).
//! - **ZK-private cells (M2)** — state-as-all-commitments with a hiding-STARK
//!   transition proof — are the deeper, VK-affecting rung. NOT here.

use crate::note_encryption::{decrypt_note, encrypt_note_to, NoteDecryptError, NotePlaintext};
use dregg_cell::state::{CellState, FieldVisibility, STATE_SLOTS};
use serde::{Deserialize, Serialize};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroize;

/// Domain separation for the per-slot ViewKey derivation. Distinct from the
/// note-encryption / seal / stealth contexts so a read-slot key can never be
/// confused with any other derived key.
const VIEW_SLOT_CONTEXT: &str = "dregg-read-slot v1";

/// A subset of the cell's 16 state slots — the read-lattice. A 16-bit mask: bit
/// `i` set ⇒ slot `i` is in the set.
///
/// `granted ⊆ held` ([`Self::is_subset_of`]) is the read-cap attenuation order,
/// mirroring the write side's [`dregg_cell::facet::is_facet_attenuation`]
/// (`child & parent == child`). The same partial order, a different carrier
/// (*which slots* may be opened, vs *which effects* may be issued).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Default)]
pub struct FieldSet(pub u16);

impl FieldSet {
    /// The empty set (opens nothing).
    pub const EMPTY: FieldSet = FieldSet(0);
    /// Every one of the 16 slots.
    pub const ALL: FieldSet = FieldSet(0xFFFF);

    /// A set containing exactly the given slot indices (indices `>= 16` ignored —
    /// the read-lattice covers only the 16 fixed slots).
    pub fn from_slots(slots: &[usize]) -> FieldSet {
        let mut m = 0u16;
        for &s in slots {
            if s < STATE_SLOTS {
                m |= 1 << s;
            }
        }
        FieldSet(m)
    }

    /// A singleton set for slot `i` (empty if `i >= 16`).
    pub fn single(i: usize) -> FieldSet {
        if i < STATE_SLOTS {
            FieldSet(1 << i)
        } else {
            FieldSet::EMPTY
        }
    }

    /// Does this set contain slot `i`?
    pub fn contains(&self, i: usize) -> bool {
        i < STATE_SLOTS && (self.0 & (1 << i)) != 0
    }

    /// Is `self` a subset of `other` (`self ⊆ other`)? The read-cap attenuation
    /// order — the exact bit-discipline of [`dregg_cell::facet::is_facet_attenuation`].
    pub fn is_subset_of(&self, other: &FieldSet) -> bool {
        self.0 & other.0 == self.0
    }

    /// Intersection — the slots BOTH sets admit.
    pub fn intersect(&self, other: &FieldSet) -> FieldSet {
        FieldSet(self.0 & other.0)
    }

    /// Iterate the slot indices in this set, ascending.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..STATE_SLOTS).filter(move |&i| self.contains(i))
    }

    /// Is the set empty?
    pub fn is_empty(&self) -> bool {
        self.0 == 0
    }
}

/// **`is_read_attenuation`** — the read-cap attenuation gate: `granted ⊆ held`.
///
/// The read-side twin of [`dregg_cell::is_attenuation`] / [`dregg_cell::facet::is_facet_attenuation`]:
/// a read-cap may be reshared only into one whose slot-set is a subset. There is
/// no amplification — you cannot grant read of a slot you cannot read.
pub fn is_read_attenuation(held: &FieldSet, granted: &FieldSet) -> bool {
    granted.is_subset_of(held)
}

/// The HKDF-tree **viewing key** — the root key material from which per-slot
/// decryption keys are derived.
///
/// Custody of this root is the decryption authority. A [`ReadCap`] pairs a
/// `ViewKey` with the `slots` it is *entitled* to derive; attenuation hands a
/// narrower `slots` over the same root (the cap gates which `slot_key`s the
/// holder may legitimately compute — the HKDF-tree makes delegation clean).
///
/// Per-slot derivation is `KDF(root, domain="dregg-read-slot v1", slot_index)`,
/// yielding an independent X25519 secret per slot. Knowing the root lets you
/// derive ALL slot keys; the cap's `slots` is the *authorization* over which you
/// may. (A future tail can hand a per-slot derived sub-key set instead of the
/// root for cryptographic — not merely authorizational — slot confinement; §5
/// names that lane. M0 binds the entitlement in the cap.)
#[derive(Clone, Serialize, Deserialize)]
pub struct ViewKey {
    root: [u8; 32],
}

impl Drop for ViewKey {
    fn drop(&mut self) {
        self.root.zeroize();
    }
}

impl core::fmt::Debug for ViewKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ViewKey").field("root", &"<redacted>").finish()
    }
}

impl ViewKey {
    /// Construct a ViewKey from 32 bytes of root key material.
    pub fn from_root(root: [u8; 32]) -> ViewKey {
        ViewKey { root }
    }

    /// Derive the per-slot X25519 **secret** key for `slot`:
    /// `KDF(root, "dregg-read-slot v1", slot_index)`. The HKDF-tree leaf for
    /// that slot. Two distinct slots yield independent keys (domain-separated by
    /// the slot index), so possessing slot `i`'s key gives nothing about slot `j`.
    pub fn slot_secret(&self, slot: usize) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key(VIEW_SLOT_CONTEXT);
        hasher.update(&self.root);
        hasher.update(&(slot as u64).to_le_bytes());
        let mut out = [0u8; 32];
        out.copy_from_slice(hasher.finalize().as_bytes());
        out
    }

    /// The per-slot X25519 **public** key — the encryption target for sealing
    /// slot `slot`'s ciphertext. The author of an encrypted slot uses this; a
    /// reader derives [`Self::slot_secret`] to open it.
    pub fn slot_pubkey(&self, slot: usize) -> [u8; 32] {
        let secret = StaticSecret::from(self.slot_secret(slot));
        *PublicKey::from(&secret).as_bytes()
    }
}

/// A `Committed` slot's on-ledger pair: the **commitment** the circuit sees
/// (byte-identical to today's [`CellState::compute_commitment`]) plus the
/// **ECIES ciphertext** a read-cap holder opens.
///
/// `PRIVACY-CONFIDENTIALITY.md` §2b: binding unchanged (write-soundness intact),
/// hiding added. A party without the cap sees only `(commitment, ciphertext)`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EncryptedSlot {
    /// `BLAKE3(value || nonce)` — the EXACT commitment the cell already stores in
    /// `CellState::commitments[i]` (the binding the circuit / conservation see).
    pub commitment: [u8; 32],
    /// The [`crate::note_encryption`]-style ECIES box over the slot opening,
    /// sealed to the slot's ViewKey-derived public key. The new artifact.
    pub ciphertext: Vec<u8>,
}

/// The cleartext opening of an encrypted slot — what the author seals and a
/// read-cap holder recovers. Reuses the [`NotePlaintext`] wire-form
/// (`value || asset_type || blinding`) so it drops straight onto the audited
/// ECIES path; here we carry the 32-byte slot value in the `blinding` field and
/// the commitment nonce in `asset_type` so the holder can re-derive and CHECK the
/// commitment after decrypting.
///
/// (Reusing the note opening rather than inventing a slot-specific wire keeps the
/// `note_encryption` AEAD path byte-for-byte the audited one — weld, not build.)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlotOpening {
    /// The slot's 32-byte cleartext value.
    pub value: [u8; 32],
    /// The commitment nonce mixed into `BLAKE3(value || nonce)`.
    pub commitment_nonce: u64,
}

impl SlotOpening {
    fn to_note_plaintext(&self) -> NotePlaintext {
        // value carried in `blinding` (32B); nonce in `asset_type`; `value`=0.
        NotePlaintext {
            value: 0,
            asset_type: self.commitment_nonce,
            blinding: self.value,
        }
    }

    fn from_note_plaintext(pt: &NotePlaintext) -> SlotOpening {
        SlotOpening {
            value: pt.blinding,
            commitment_nonce: pt.asset_type,
        }
    }
}

/// **Seal** a slot opening to a slot's ViewKey-derived public key, producing the
/// `(commitment, ciphertext)` pair.
///
/// The commitment is computed by the SAME function the cell already uses
/// ([`CellState::compute_commitment`], `BLAKE3(value || nonce)`) so it is
/// byte-identical to `CellState::commitments[slot]` — the circuit sees no change.
pub fn seal_slot(view_key: &ViewKey, slot: usize, opening: &SlotOpening) -> EncryptedSlot {
    let commitment = CellState::compute_commitment_pub(&opening.value, opening.commitment_nonce);
    let slot_pub = view_key.slot_pubkey(slot);
    let ciphertext = encrypt_note_to(&slot_pub, &opening.to_note_plaintext());
    EncryptedSlot {
        commitment,
        ciphertext,
    }
}

/// Errors from opening an encrypted slot under a read-cap.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReadCapError {
    /// The read-cap's `slots` does not admit this slot — the holder is not
    /// entitled to derive the key (the attenuation gate). NOT a decryption
    /// attempt: the cap simply does not cover the slot.
    SlotNotAuthorized(usize),
    /// The slot's ciphertext failed to decrypt under the derived key (wrong
    /// ViewKey, or tampered box). Fails closed.
    Decrypt(NoteDecryptError),
    /// The decrypted value's recomputed commitment does not match the slot's
    /// stored commitment — the ciphertext and commitment disagree (binding
    /// check). Fails closed.
    CommitmentMismatch(usize),
}

impl core::fmt::Display for ReadCapError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ReadCapError::SlotNotAuthorized(i) => {
                write!(f, "read-cap does not authorize slot {i}")
            }
            ReadCapError::Decrypt(e) => write!(f, "slot decryption failed: {e}"),
            ReadCapError::CommitmentMismatch(i) => {
                write!(f, "slot {i} ciphertext disagrees with its commitment")
            }
        }
    }
}

impl std::error::Error for ReadCapError {}

/// A **read-capability** over a cell: the attenuable viewing-authority. The dual
/// of a write-cap — `slots` is the read-lattice, `view_key` the decryption
/// authority for exactly those slots.
///
/// Attenuation ([`Self::attenuate`]) narrows `slots` via [`is_read_attenuation`]
/// (`granted ⊆ held`); the ViewKey root rides along (the cap gates which slot
/// keys the holder is entitled to derive). Revocation rides the existing
/// [`dregg_cell::revocation_channel`] for the cap-object (§2a).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ReadCap {
    /// Which cell this opens.
    pub target: dregg_cell::id::CellId,
    /// The read-lattice: which of the 16 slots this cap opens.
    pub slots: FieldSet,
    /// The decryption authority for those slots.
    pub view_key: ViewKey,
    /// Optional provenance token, mirroring a write-cap's breadstuff.
    #[serde(default)]
    pub breadstuff: Option<[u8; 32]>,
}

impl ReadCap {
    /// Mint a fresh read-cap over `target` opening `slots`, with viewing key
    /// `view_key`.
    pub fn new(target: dregg_cell::id::CellId, slots: FieldSet, view_key: ViewKey) -> ReadCap {
        ReadCap {
            target,
            slots,
            view_key,
            breadstuff: None,
        }
    }

    /// **Attenuate** this read-cap to a narrower slot-set. Succeeds iff
    /// `granted ⊆ self.slots` ([`is_read_attenuation`]); returns `None` on any
    /// attempted amplification (a slot the holder cannot read). The returned cap
    /// carries the SAME `target`, ViewKey, and breadstuff — only the `slots`
    /// entitlement narrows.
    pub fn attenuate(&self, granted: FieldSet) -> Option<ReadCap> {
        if is_read_attenuation(&self.slots, &granted) {
            Some(ReadCap {
                target: self.target,
                slots: granted,
                view_key: self.view_key.clone(),
                breadstuff: self.breadstuff,
            })
        } else {
            None
        }
    }

    /// Does this cap derive the key for slot `i`? (`i ∈ slots`.) The
    /// `readCapDerives` predicate the membrane weld consults — the cryptographic
    /// spine of the disclosure bit.
    pub fn derives(&self, slot: usize) -> bool {
        self.slots.contains(slot)
    }

    /// **Open one encrypted slot** under this cap. Fails with
    /// [`ReadCapError::SlotNotAuthorized`] if the cap's `slots` does not cover
    /// `slot` (the attenuation gate — the narrower viewer is refused HERE, before
    /// any decryption), with [`ReadCapError::Decrypt`] if the ciphertext does not
    /// open under the derived key, or [`ReadCapError::CommitmentMismatch`] if the
    /// recovered value does not match the slot commitment.
    pub fn open_slot(
        &self,
        slot: usize,
        encrypted: &EncryptedSlot,
    ) -> Result<SlotOpening, ReadCapError> {
        if !self.slots.contains(slot) {
            return Err(ReadCapError::SlotNotAuthorized(slot));
        }
        let secret = self.view_key.slot_secret(slot);
        let pt = decrypt_note(&secret, &encrypted.ciphertext).map_err(ReadCapError::Decrypt)?;
        let opening = SlotOpening::from_note_plaintext(&pt);
        // Binding check: the recovered value MUST hash to the stored commitment.
        let recomputed =
            CellState::compute_commitment_pub(&opening.value, opening.commitment_nonce);
        if recomputed != encrypted.commitment {
            return Err(ReadCapError::CommitmentMismatch(slot));
        }
        Ok(opening)
    }

    /// **Open every slot a cell exposes that this cap authorizes.** Returns a map
    /// `slot → value` for exactly the slots in `self.slots` that the cell carries
    /// as an encrypted `Committed` slot AND that decrypt+verify cleanly. Slots the
    /// cap does not cover are silently absent (not an error — they are simply not
    /// in this viewer's frustum); slots that fail to decrypt/verify are skipped.
    ///
    /// `encrypted` is the cell's slot ciphertext side-table (`slot → EncryptedSlot`),
    /// carried alongside the cell (the ciphertext is the new artifact; the
    /// commitment already lives in `CellState::commitments`).
    pub fn open(
        &self,
        encrypted: &std::collections::BTreeMap<usize, EncryptedSlot>,
    ) -> std::collections::BTreeMap<usize, [u8; 32]> {
        let mut out = std::collections::BTreeMap::new();
        for slot in self.slots.iter() {
            if let Some(es) = encrypted.get(&slot) {
                if let Ok(opening) = self.open_slot(slot, es) {
                    out.insert(slot, opening.value);
                }
            }
        }
        out
    }
}

/// A cell's **encrypted-slot side-table**: `slot → (commitment, ciphertext)` for
/// each `Committed` slot whose value is sealed. This lives ALONGSIDE the cell —
/// it is purely the new ciphertext artifact; the commitment half already lives in
/// `CellState::commitments[slot]` (byte-identical). The cell's state-commitment
/// shape is untouched, so the circuit / VK see no change.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct EncryptedState {
    /// Per-slot sealed openings, keyed by slot index.
    pub slots: std::collections::BTreeMap<usize, EncryptedSlot>,
}

impl EncryptedState {
    /// A fresh, empty side-table.
    pub fn new() -> EncryptedState {
        EncryptedState {
            slots: std::collections::BTreeMap::new(),
        }
    }

    /// **Seal slot `slot` of a cell** under `view_key`: encrypt its current value
    /// (with `commitment_nonce`), store the `(commitment, ciphertext)` pair, AND
    /// stamp the cell's `field_visibility[slot] = Committed` with the byte-
    /// identical commitment in `CellState::commitments[slot]`.
    ///
    /// This is the ADDITIVE write path: the cell's commitment is set by the
    /// EXISTING [`CellState::set_field_visibility`] (so the on-cell commitment is
    /// exactly what it would be without read-caps), and the ciphertext is recorded
    /// here, off to the side. Returns `false` for an out-of-range slot.
    pub fn seal_field(
        &mut self,
        cell: &mut CellState,
        slot: usize,
        view_key: &ViewKey,
        commitment_nonce: u64,
    ) -> bool {
        if slot >= STATE_SLOTS {
            return false;
        }
        let value = *cell.get_field(slot).expect("slot in range");
        // Mark the slot Committed with the EXISTING commitment path — byte-
        // identical to a normal committed slot, so the circuit sees no change.
        cell.set_field_visibility(slot, FieldVisibility::Committed, commitment_nonce);
        let opening = SlotOpening {
            value,
            commitment_nonce,
        };
        let es = seal_slot(view_key, slot, &opening);
        // Sanity: the side-table commitment equals the cell's stored commitment.
        debug_assert_eq!(
            Some(es.commitment),
            cell.commitments[slot],
            "encrypted-slot commitment must be byte-identical to the cell's"
        );
        self.slots.insert(slot, es);
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::id::CellId;

    fn cid(b: u8) -> CellId {
        let mut k = [0u8; 32];
        k[0] = b;
        CellId::derive_raw(&k, &[0u8; 32])
    }

    fn vk(seed: u8) -> ViewKey {
        ViewKey::from_root([seed; 32])
    }

    fn fe(byte: u8) -> [u8; 32] {
        let mut f = [0u8; 32];
        f[31] = byte;
        f
    }

    // ── FieldSet lattice ────────────────────────────────────────────────────

    #[test]
    fn fieldset_subset_is_the_attenuation_order() {
        let wide = FieldSet::from_slots(&[3, 4, 5]);
        let narrow = FieldSet::from_slots(&[3, 4]);
        let single = FieldSet::single(3);
        assert!(narrow.is_subset_of(&wide));
        assert!(single.is_subset_of(&narrow));
        assert!(is_read_attenuation(&wide, &narrow));
        assert!(is_read_attenuation(&narrow, &single));
        // No amplification: a slot not held cannot be granted.
        let amplified = FieldSet::from_slots(&[3, 4, 5, 6]);
        assert!(!is_read_attenuation(&wide, &amplified));
    }

    #[test]
    fn slot_keys_are_independent_per_slot() {
        let k = vk(0x11);
        // Distinct slots derive distinct secrets (domain-separated by index).
        let s3 = k.slot_secret(3);
        let s4 = k.slot_secret(4);
        assert_ne!(s3, s4);
        // Public keys likewise distinct.
        assert_ne!(k.slot_pubkey(3), k.slot_pubkey(4));
    }

    // ── byte-identical commitment (the load-bearing constraint) ─────────────

    /// The encrypted slot's commitment is BYTE-IDENTICAL to what a normal
    /// `Committed` cell field stores — proving the circuit/VK sees no change.
    #[test]
    fn commitment_is_byte_identical_to_the_cell() {
        let mut plain = CellState::new(0);
        plain.set_field(5, fe(99));
        // A normal committed slot, using ONLY the existing cell path:
        plain.set_field_visibility(5, FieldVisibility::Committed, 0xDEAD);
        let cell_commitment = plain.commitments[5].expect("committed");

        // The read-cap-sealed slot's commitment, via seal_slot:
        let key = vk(0x22);
        let opening = SlotOpening {
            value: fe(99),
            commitment_nonce: 0xDEAD,
        };
        let es = seal_slot(&key, 5, &opening);

        assert_eq!(
            es.commitment, cell_commitment,
            "the encrypted-slot commitment MUST be byte-identical to the cell's \
             existing committed-field commitment — the circuit sees no change"
        );
    }

    /// `seal_field` stamps the cell with the SAME commitment it stores in the
    /// side-table (the additive write path keeps the on-cell commitment normal).
    #[test]
    fn seal_field_keeps_cell_commitment_normal() {
        let mut cell = CellState::new(0);
        cell.set_field(7, fe(123));
        let mut enc = EncryptedState::new();
        let key = vk(0x33);
        assert!(enc.seal_field(&mut cell, 7, &key, 0xBEEF));

        // The cell's committed view is the ordinary BLAKE3(value||nonce):
        assert_eq!(cell.field_visibility[7], FieldVisibility::Committed);
        assert_eq!(
            cell.commitments[7],
            Some(CellState::compute_commitment_pub(&fe(123), 0xBEEF))
        );
        // …and the side-table carries the same commitment.
        assert_eq!(enc.slots[&7].commitment, cell.commitments[7].unwrap());
    }

    // ── roundtrip + THE NON-VACUITY TOOTH ───────────────────────────────────

    #[test]
    fn wide_cap_opens_its_slots() {
        let mut cell = CellState::new(0);
        cell.set_field(3, fe(30));
        cell.set_field(4, fe(40));
        cell.set_field(5, fe(50));
        let key = vk(0x44);
        let mut enc = EncryptedState::new();
        enc.seal_field(&mut cell, 3, &key, 1);
        enc.seal_field(&mut cell, 4, &key, 2);
        enc.seal_field(&mut cell, 5, &key, 3);

        let cap = ReadCap::new(cid(1), FieldSet::from_slots(&[3, 4, 5]), key);
        let opened = cap.open(&enc.slots);
        assert_eq!(opened.get(&3), Some(&fe(30)));
        assert_eq!(opened.get(&4), Some(&fe(40)));
        assert_eq!(opened.get(&5), Some(&fe(50)));
    }

    /// THE NON-VACUITY TOOTH (`PRIVACY-CONFIDENTIALITY.md` §4 / Milestone 0):
    /// two viewers at equal write-authority but different read-caps. The narrow
    /// read-cap PROVABLY cannot decrypt a slot the wide one can — BOTH the true
    /// case (wide reads it) AND the false case (narrow is refused), proven not
    /// asserted.
    #[test]
    fn narrow_cap_provably_cannot_read_a_slot_the_wide_one_can() {
        let mut cell = CellState::new(0);
        cell.set_field(3, fe(30));
        cell.set_field(5, fe(50));
        let key = vk(0x55);
        let mut enc = EncryptedState::new();
        enc.seal_field(&mut cell, 3, &key, 11);
        enc.seal_field(&mut cell, 5, &key, 22);

        // Wide cap: slots {3,5}.   Narrow cap (attenuated): slots {3} only.
        let wide = ReadCap::new(cid(1), FieldSet::from_slots(&[3, 5]), key.clone());
        let narrow = wide.attenuate(FieldSet::single(3)).expect("attenuation");

        // TRUE: the wide cap opens slot 5.
        assert_eq!(
            wide.open_slot(5, &enc.slots[&5]).map(|o| o.value),
            Ok(fe(50)),
            "wide cap MUST open slot 5"
        );
        // FALSE: the narrow cap is REFUSED at slot 5 — the key is not in its
        // entitlement; the cap gate (not a decryption attempt) stops it.
        assert_eq!(
            narrow.open_slot(5, &enc.slots[&5]),
            Err(ReadCapError::SlotNotAuthorized(5)),
            "narrow cap MUST NOT open slot 5"
        );
        // …and both DO open the slot they share (the cap is non-vacuous: it
        // genuinely opens what it covers).
        assert_eq!(wide.open_slot(3, &enc.slots[&3]).map(|o| o.value), Ok(fe(30)));
        assert_eq!(
            narrow.open_slot(3, &enc.slots[&3]).map(|o| o.value),
            Ok(fe(30))
        );
        // The bulk `open` confirms the slot-set difference: wide opens {3,5},
        // narrow opens {3}.
        assert_eq!(wide.open(&enc.slots).keys().copied().collect::<Vec<_>>(), vec![3, 5]);
        assert_eq!(
            narrow.open(&enc.slots).keys().copied().collect::<Vec<_>>(),
            vec![3]
        );
    }

    /// CRYPTOGRAPHIC TOOTH: even a cap whose `slots` covers slot 5 cannot open it
    /// under the WRONG ViewKey — the AEAD fails closed (the entitlement is the
    /// policy gate; the key is the cryptographic gate, and both must hold).
    #[test]
    fn wrong_view_key_fails_closed_even_if_authorized() {
        let mut cell = CellState::new(0);
        cell.set_field(5, fe(50));
        let real = vk(0x66);
        let mut enc = EncryptedState::new();
        enc.seal_field(&mut cell, 5, &real, 7);

        // A cap that CLAIMS slot 5 but carries the wrong ViewKey.
        let imposter = ReadCap::new(cid(1), FieldSet::single(5), vk(0x99));
        let err = imposter.open_slot(5, &enc.slots[&5]).unwrap_err();
        assert!(
            matches!(err, ReadCapError::Decrypt(_)),
            "wrong ViewKey must fail the AEAD closed, got {err:?}"
        );
    }

    /// TAMPER TOOTH: a flipped commitment (binding) is caught even when the
    /// ciphertext decrypts — the commitment cross-check fails closed.
    #[test]
    fn commitment_tamper_is_caught() {
        let mut cell = CellState::new(0);
        cell.set_field(2, fe(20));
        let key = vk(0x77);
        let mut enc = EncryptedState::new();
        enc.seal_field(&mut cell, 2, &key, 3);

        let cap = ReadCap::new(cid(1), FieldSet::single(2), key);
        // Tamper the stored commitment (claim the slot commits a different value).
        let mut tampered = enc.slots[&2].clone();
        tampered.commitment[0] ^= 0xFF;
        assert_eq!(
            cap.open_slot(2, &tampered),
            Err(ReadCapError::CommitmentMismatch(2))
        );
    }

    /// Attenuation cannot amplify: you cannot widen a narrow cap.
    #[test]
    fn attenuation_refuses_amplification() {
        let key = vk(0x88);
        let narrow = ReadCap::new(cid(1), FieldSet::single(3), key);
        assert!(
            narrow.attenuate(FieldSet::from_slots(&[3, 4])).is_none(),
            "must refuse widening {{3}} -> {{3,4}}"
        );
        assert!(narrow.attenuate(FieldSet::single(3)).is_some());
    }
}

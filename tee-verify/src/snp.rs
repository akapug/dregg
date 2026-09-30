//! AMD SEV-SNP attestation-report verifier — the SNP sibling of [`crate::NitroVerifier`].
//!
//! Parses the fixed-layout **1184-byte** `ATTESTATION_REPORT` (AMD SEV-SNP ABI, Table
//! 22), extracts the code identity + bound commitment, and verifies the report is
//! genuine:
//!
//! 1. **Parse** (fully real): every field is read from its fixed byte offset —
//!    `VERSION`, `SIGNATURE_ALGO`, `CURRENT_TCB`/`REPORTED_TCB`, `REPORT_DATA` (0x50,
//!    64 bytes), `MEASUREMENT` (0x90, 48 bytes), `HOST_DATA`, `CHIP_ID`, and the
//!    ECDSA-P384 signature (0x2A0, stored as two little-endian 72-byte components).
//! 2. **Body signature** (fully real): the first `0x2A0` bytes (everything preceding
//!    the signature) are verified as ECDSA-P384 / SHA-384 against the chip's **VCEK**
//!    public key — exactly the scheme [`crate::verify_cose_sig`] uses for Nitro's
//!    ES384, via `p384`.
//! 3. **Cert chain** (anchored to the real AMD roots): VCEK ← ASK ← pinned **ARK**,
//!    structured like [`crate::verify_cert_chain`]. The VCEK certificate rides appended to
//!    the report bytes (`report(1184) ‖ vcek_der`); ASK + ARK are the **real AMD roots**
//!    embedded from the AMD KDS per product (Milan/Genoa/Turin) — see [`snp_chain`] for the
//!    pinned roots + provenance. AMD's ARK/ASK sign RSA-4096-PSS, verified via the `rsa`
//!    crate (the algorithm `x509-parser` lacks).
//!
//! 4. **Corroboration** (F1): the VCEK certificate's AMD extensions name the TCB it was
//!    issued at and the chip it belongs to; the report's `REPORTED_TCB` and `CHIP_ID`
//!    must equal them, and the TCB floor is applied to the certificate's value.
//! 5. **Launch policy** (F2): an [`SnpPolicy`] gates the guest `POLICY` (DEBUG and
//!    MIGRATE_MA refused by default, reserved bits enforced), the `VMPL`, and `GUEST_SVN`.
//! 6. **Revocation** (F3): operator-supplied AMD CRLs, verified under the pinned ARK/ASK.
//!
//! Every refusal is a named [`SnpError`] variant.
//!
//! **Fail-closed.** A [`SnpVerifier`] built with [`SnpVerifier::new`] carries no pinned
//! AMD roots and rejects *every* report (`Err`) before it would extract claims. Build the
//! anchored verifier with [`SnpVerifier::new_with_amd_roots`] (real embedded AMD roots per
//! product) — or [`SnpVerifier::with_pinned_roots`] / [`SnpVerifier::with_pinned_roots_pem`]
//! for operator-supplied roots. With the roots pinned, the verifier ACCEPTS a genuine AMD
//! `VCEK ← ASK ← ARK` chain and fail-closes on a forged / wrong-product / tampered chain.
//!
//! **Grade.** This is ATTESTED grade: the AMD hardware-vendor root chain is real + pinned,
//! and the report PARSING + field extraction + body-signature verify are real crypto. The
//! remaining piece to verify a *live* report is a genuine SEV-SNP `ATTESTATION_REPORT` +
//! its per-chip VCEK captured from EPYC-SNP hardware (the report-body fixture) — the ROOT
//! trust is now real, not a seam.

use dregg_cell::tee_attest::{TcbStatus, TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims};
use p384::ecdsa::signature::Verifier;
use p384::ecdsa::{Signature, VerifyingKey};
use sha2::{Digest, Sha256};

/// The `dregg-cell`-free cert-chain trust core: the pinned real AMD roots (ARK/ASK per
/// product), the RSA-PSS link primitive, and `VCEK ← ASK ← ARK` chain verify. Split out so
/// it builds + tests standalone even when a sibling workspace crate is red. Re-exported so
/// the historical `snp::SnpTrust` / `snp::verify_snp_cert_chain` / `snp::verify_rsa_pss_sha384`
/// paths keep resolving.
///
/// Kept as the top-level `src/snp_chain.rs` file (so it "builds + tests standalone"), which is
/// why the child-module path is spelled explicitly rather than the default `src/snp/snp_chain.rs`.
#[path = "snp_chain.rs"]
pub mod snp_chain;
pub use snp_chain::{
    amd_kds_cert_chain_url, amd_kds_crl_url, verify_cert_link, verify_rsa_pss_sha384,
    verify_snp_cert_chain, SnpChainError, SnpProduct, SnpTrust, TcbVersion, VcekEndorsement,
    HW_ID_LEN,
};

/// Total size of a SEV-SNP `ATTESTATION_REPORT` (`0x4A0`).
pub const REPORT_LEN: usize = 1184;

// Field offsets into the report (AMD SEV-SNP ABI Table 22).
const OFF_VERSION: usize = 0x000; // u32
const OFF_GUEST_SVN: usize = 0x004; // u32
const OFF_POLICY: usize = 0x008; // u64
const OFF_VMPL: usize = 0x030; // u32
const OFF_SIGNATURE_ALGO: usize = 0x034; // u32
const OFF_CURRENT_TCB: usize = 0x038; // TCB_VERSION (u64 LE)
const OFF_KEY_INFO: usize = 0x048; // u32: AUTHOR_KEY_EN[0], MASK_CHIP_KEY[1], SIGNING_KEY[4:2]
const OFF_REPORT_DATA: usize = 0x050; // 64 bytes
const OFF_MEASUREMENT: usize = 0x090; // 48 bytes
const OFF_HOST_DATA: usize = 0x0C0; // 32 bytes
const OFF_REPORTED_TCB: usize = 0x180; // TCB_VERSION (u64 LE)
const OFF_CHIP_ID: usize = 0x1A0; // 64 bytes
const OFF_SIGNATURE: usize = 0x2A0; // 512-byte SIGNATURE block; also == length of the signed body

const REPORT_DATA_LEN: usize = 64;
const MEASUREMENT_LEN: usize = 48;
const HOST_DATA_LEN: usize = 32;
const CHIP_ID_LEN: usize = HW_ID_LEN;

/// Each ECDSA component (R, S) occupies a fixed 72-byte little-endian field.
const SIG_COMPONENT_LEN: usize = 72;
/// P-384 scalars are 48 bytes; the upper 24 bytes of each 72-byte field are zero.
const P384_SCALAR_LEN: usize = 48;

/// `SIGNATURE_ALGO` value for ECDSA-P384 with SHA-384 (the only algo AMD emits today).
const SIG_ALGO_ECDSA_P384_SHA384: u32 = 1;

/// `GUEST_POLICY` bits (SEV-SNP ABI spec, guest policy table; read against virtee `sev`
/// 8.0.0 `GuestPolicy`). Bits 7:0 ABI_MINOR and 15:8 ABI_MAJOR are version fields.
pub mod policy_bits {
    /// Host SMT usage allowed.
    pub const SMT: u64 = 1 << 16;
    /// Reserved, MUST be one — a report with it clear is not a well-formed policy.
    pub const RESERVED_MBO: u64 = 1 << 17;
    /// A migration agent may be associated with the guest (and can export its memory).
    pub const MIGRATE_MA: u64 = 1 << 18;
    /// Debugging allowed: the host may decrypt guest memory via SNP_DBG_DECRYPT.
    pub const DEBUG: u64 = 1 << 19;
    /// Guest may only be activated on one socket.
    pub const SINGLE_SOCKET: u64 = 1 << 20;
    /// CXL may be populated with devices or memory.
    pub const CXL_ALLOW: u64 = 1 << 21;
    /// AES-256-XTS required for memory encryption.
    pub const MEM_AES_256_XTS: u64 = 1 << 22;
    /// RAPL must be disabled.
    pub const RAPL_DIS: u64 = 1 << 23;
    /// Ciphertext hiding must be enabled.
    pub const CIPHERTEXT_HIDING: u64 = 1 << 24;
    /// Page swap/move commands disabled.
    pub const PAGE_SWAP_DISABLE: u64 = 1 << 25;
    /// Every bit this verifier knows the meaning of (0..=25). Bits 63:26 are MBZ; a set
    /// one is a policy this verifier cannot evaluate, so it refuses.
    pub const KNOWN: u64 = (1 << 26) - 1;
}

/// `KEY_INFO.SIGNING_KEY` value meaning "signed by the VCEK" (1 = VLEK, 7 = unsigned).
const SIGNING_KEY_VCEK: u32 = 0;

/// A parsed SEV-SNP attestation report. All fields are read from fixed offsets; the raw
/// bytes are retained so the signed body and signature can be recovered exactly. The TCB
/// fields are decoded under the product's layout (see [`TcbVersion`]).
#[derive(Debug, Clone)]
pub struct SnpReport {
    pub version: u32,
    pub guest_svn: u32,
    pub policy: u64,
    pub vmpl: u32,
    pub sig_algo: u32,
    pub key_info: u32,
    pub current_tcb: TcbVersion,
    pub reported_tcb: TcbVersion,
    pub report_data: [u8; REPORT_DATA_LEN],
    pub measurement: [u8; MEASUREMENT_LEN],
    pub host_data: [u8; HOST_DATA_LEN],
    pub chip_id: [u8; CHIP_ID_LEN],
    /// The full 1184-byte report (source of `signed_body` + `signature`).
    raw: Vec<u8>,
}

fn rd_u32(b: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]])
}

fn rd_u64(b: &[u8], off: usize) -> u64 {
    let mut a = [0u8; 8];
    a.copy_from_slice(&b[off..off + 8]);
    u64::from_le_bytes(a)
}

impl SnpReport {
    /// Parse exactly the 1184-byte `ATTESTATION_REPORT` for `product`. Real: every field
    /// comes from its fixed offset; the only rejections are a wrong length or an unknown
    /// VERSION.
    pub fn parse(bytes: &[u8], product: SnpProduct) -> Result<SnpReport, String> {
        if bytes.len() != REPORT_LEN {
            return Err(format!(
                "SNP report must be {REPORT_LEN} bytes, got {}",
                bytes.len()
            ));
        }
        let version = rd_u32(bytes, OFF_VERSION);
        if version != 2 && version != 3 {
            return Err(format!(
                "unsupported SNP report VERSION {version} (want 2 or 3)"
            ));
        }

        let mut report_data = [0u8; REPORT_DATA_LEN];
        report_data.copy_from_slice(&bytes[OFF_REPORT_DATA..OFF_REPORT_DATA + REPORT_DATA_LEN]);
        let mut measurement = [0u8; MEASUREMENT_LEN];
        measurement.copy_from_slice(&bytes[OFF_MEASUREMENT..OFF_MEASUREMENT + MEASUREMENT_LEN]);
        let mut host_data = [0u8; HOST_DATA_LEN];
        host_data.copy_from_slice(&bytes[OFF_HOST_DATA..OFF_HOST_DATA + HOST_DATA_LEN]);
        let mut chip_id = [0u8; CHIP_ID_LEN];
        chip_id.copy_from_slice(&bytes[OFF_CHIP_ID..OFF_CHIP_ID + CHIP_ID_LEN]);

        let mut cur = [0u8; 8];
        cur.copy_from_slice(&bytes[OFF_CURRENT_TCB..OFF_CURRENT_TCB + 8]);
        let mut rep = [0u8; 8];
        rep.copy_from_slice(&bytes[OFF_REPORTED_TCB..OFF_REPORTED_TCB + 8]);

        Ok(SnpReport {
            version,
            guest_svn: rd_u32(bytes, OFF_GUEST_SVN),
            policy: rd_u64(bytes, OFF_POLICY),
            vmpl: rd_u32(bytes, OFF_VMPL),
            sig_algo: rd_u32(bytes, OFF_SIGNATURE_ALGO),
            key_info: rd_u32(bytes, OFF_KEY_INFO),
            current_tcb: TcbVersion::from_report_bytes(cur, product),
            reported_tcb: TcbVersion::from_report_bytes(rep, product),
            report_data,
            measurement,
            host_data,
            chip_id,
            raw: bytes.to_vec(),
        })
    }

    /// The bytes covered by the signature: everything before the 0x2A0 signature block.
    pub fn signed_body(&self) -> &[u8] {
        &self.raw[..OFF_SIGNATURE]
    }

    /// The code identity for the predicate: `SHA-256(MEASUREMENT)` (48 → 32 bytes).
    pub fn folded_measurement(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(self.measurement);
        h.finalize().into()
    }

    /// The bound commitment: the first 32 bytes of the 64-byte `REPORT_DATA`.
    pub fn report_data_32(&self) -> [u8; 32] {
        let mut r = [0u8; 32];
        r.copy_from_slice(&self.report_data[..32]);
        r
    }

    /// `KEY_INFO.SIGNING_KEY` (bits 4:2): 0 = VCEK, 1 = VLEK, 7 = none.
    pub fn signing_key(&self) -> u32 {
        (self.key_info >> 2) & 0b111
    }

    /// Decode the P-384 signature from AMD's two little-endian 72-byte components into a
    /// `p384` `Signature` (big-endian R‖S). Rejects a report whose components carry a
    /// value wider than a P-384 scalar (the upper 24 bytes of each field must be zero).
    pub fn signature(&self) -> Result<Signature, String> {
        let r_field = &self.raw[OFF_SIGNATURE..OFF_SIGNATURE + SIG_COMPONENT_LEN];
        let s_field =
            &self.raw[OFF_SIGNATURE + SIG_COMPONENT_LEN..OFF_SIGNATURE + 2 * SIG_COMPONENT_LEN];
        for (name, field) in [("R", r_field), ("S", s_field)] {
            if field[P384_SCALAR_LEN..].iter().any(|&b| b != 0) {
                return Err(format!(
                    "SNP signature {name} component exceeds a P-384 scalar (non-zero high bytes)"
                ));
            }
        }
        // AMD stores each component little-endian; p384 wants big-endian R‖S.
        let mut be = [0u8; 2 * P384_SCALAR_LEN];
        for i in 0..P384_SCALAR_LEN {
            be[i] = r_field[P384_SCALAR_LEN - 1 - i];
            be[P384_SCALAR_LEN + i] = s_field[P384_SCALAR_LEN - 1 - i];
        }
        Signature::from_slice(&be).map_err(|e| format!("SNP signature decode: {e}"))
    }
}

/// Verify the report-body ECDSA-P384/SHA-384 signature with the chip's VCEK public key.
/// Real crypto — this is the binding between the VCEK identity and the report contents.
pub fn verify_snp_signature(report: &SnpReport, vcek_vk: &VerifyingKey) -> Result<(), String> {
    if report.sig_algo != SIG_ALGO_ECDSA_P384_SHA384 {
        return Err(format!(
            "unsupported SNP SIGNATURE_ALGO {} (want {SIG_ALGO_ECDSA_P384_SHA384} = ECDSA-P384/SHA-384)",
            report.sig_algo
        ));
    }
    let sig = report.signature()?;
    vcek_vk
        .verify(report.signed_body(), &sig)
        .map_err(|e| format!("SNP report signature verify FAILED: {e}"))
}

/// What a verifier requires of a report beyond a genuine signature: the launch policy the
/// guest ran under, the privilege level the report was requested from, the guest's own
/// SVN, and the platform TCB floor.
///
/// Built only through [`SnpPolicy::new`], which names the two floors. Every other field
/// starts at its strict value and can only be relaxed by a named call:
///
/// - **debug guests refused.** `DEBUG` lets the host decrypt guest memory, so a debug
///   guest's measurement says nothing about what ran. No constructor accepts one;
///   [`SnpPolicy::accept_debug_guests_insecure`] exists for lab rigs and says so.
/// - **migration agents refused.** `MIGRATE_MA` lets a migration agent export the guest.
/// - **VMPL 0 only.** A report requested from a less-privileged VMPL speaks for software
///   the VMPL-0 layer can override; [`SnpPolicy::allow_vmpls`] widens it for SVSM setups.
/// - **reserved policy bits.** Bit 17 must be one; bits 63:26 must be zero.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SnpPolicy {
    /// Platform TCB floor, compared against the TCB the VCEK certificate endorses.
    pub min_tcb: TcbVersion,
    /// Minimum `GUEST_SVN` (the guest author's own security version).
    pub min_guest_svn: u32,
    /// Bitmask over VMPL 0..=3 of the levels a report may come from.
    allowed_vmpls: u8,
    allow_debug: bool,
    allow_migration_agent: bool,
    /// Policy bits the guest MUST have set (e.g. [`policy_bits::SINGLE_SOCKET`]).
    required_policy_bits: u64,
}

impl SnpPolicy {
    /// The strict policy with the two floors named: debug and migration-agent guests
    /// refused, VMPL 0 only, no additional required policy bits.
    pub fn new(min_tcb: TcbVersion, min_guest_svn: u32) -> SnpPolicy {
        SnpPolicy {
            min_tcb,
            min_guest_svn,
            allowed_vmpls: 0b0001,
            allow_debug: false,
            allow_migration_agent: false,
            required_policy_bits: 0,
        }
    }

    /// Replace the accepted VMPL set. Levels above 3 do not exist and are refused here.
    pub fn allow_vmpls(mut self, vmpls: &[u32]) -> Result<SnpPolicy, String> {
        let mut m = 0u8;
        for &v in vmpls {
            if v > 3 {
                return Err(format!("VMPL {v} does not exist (0..=3)"));
            }
            m |= 1 << v;
        }
        if m == 0 {
            return Err("an empty VMPL set accepts nothing; name at least one".into());
        }
        self.allowed_vmpls = m;
        Ok(self)
    }

    /// Require these guest-policy bits to be set (only bits this verifier knows).
    pub fn require_policy_bits(mut self, bits: u64) -> Result<SnpPolicy, String> {
        if bits & !policy_bits::KNOWN != 0 {
            return Err(format!("unknown guest-policy bits {bits:#x}"));
        }
        self.required_policy_bits |= bits;
        Ok(self)
    }

    /// Accept guests whose policy allows a migration agent.
    pub fn allow_migration_agent(mut self) -> SnpPolicy {
        self.allow_migration_agent = true;
        self
    }

    /// Accept DEBUG guests. The host can read such a guest's memory; use only on a lab
    /// rig where that is the point.
    pub fn accept_debug_guests_insecure(mut self) -> SnpPolicy {
        self.allow_debug = true;
        self
    }

    /// Whether `vmpl` is in the accepted set.
    pub fn vmpl_allowed(&self, vmpl: u32) -> bool {
        vmpl <= 3 && self.allowed_vmpls & (1 << vmpl) != 0
    }
}

/// Why [`SnpVerifier`] refused a report. One variant per gate, so a caller or a test can
/// tell exactly which one fired; the trait entry point renders it with `Display`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SnpError {
    WrongKind(TeeQuoteKind),
    TooShort(usize),
    Parse(String),
    /// No pinned AMD roots: this verifier accepts nothing.
    NoPinnedRoots,
    Chain(SnpChainError),
    Signature(String),
    /// `KEY_INFO.SIGNING_KEY` is not the VCEK (VLEK-signed or unsigned reports need a
    /// different certificate than the one this path verifies).
    SigningKeyNotVcek {
        signing_key: u32,
    },
    /// F1: the report's `REPORTED_TCB` differs from the TCB the VCEK certificate was
    /// issued for. The report field is the key-holder's claim; the certificate is AMD's.
    ReportedTcbNotCorroborated {
        report: TcbVersion,
        vcek: TcbVersion,
    },
    /// F1: the report's `CHIP_ID` differs from the VCEK certificate's hwID (or is masked
    /// to zero, which no VCEK names).
    ChipIdNotCorroborated,
    /// F2: guest-policy bit 17 (reserved, must be one) is clear.
    PolicyReservedBitClear {
        policy: u64,
    },
    /// F2: guest-policy bits 63:26 (reserved, must be zero) are set.
    PolicyUnknownBitsSet {
        policy: u64,
    },
    /// F2: the guest was launched with DEBUG allowed.
    DebugGuest {
        policy: u64,
    },
    /// F2: the guest was launched with a migration agent allowed.
    MigrationAgentAllowed {
        policy: u64,
    },
    /// F2: a guest-policy bit the verifier requires is clear.
    RequiredPolicyBitsMissing {
        policy: u64,
        required: u64,
    },
    /// F2: the report was requested from a VMPL outside the accepted set.
    VmplNotAllowed {
        vmpl: u32,
    },
    /// F2: `GUEST_SVN` is below the configured minimum.
    GuestSvnBelowMinimum {
        guest_svn: u32,
        min: u32,
    },
}

impl std::fmt::Display for SnpError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnpError::WrongKind(k) => write!(f, "SnpVerifier handles SevSnp only, got {k:?}"),
            SnpError::TooShort(n) => write!(
                f,
                "SNP proof too short: {n} bytes (need >= {REPORT_LEN} report [+ VCEK DER])"
            ),
            SnpError::Parse(e) => write!(f, "{e}"),
            SnpError::NoPinnedRoots => write!(
                f,
                "SNP verifier fail-closed: no pinned AMD roots (ARK/ASK) installed — call with_pinned_roots"
            ),
            SnpError::Chain(e) => write!(f, "{e}"),
            SnpError::Signature(e) => write!(f, "{e}"),
            SnpError::SigningKeyNotVcek { signing_key } => write!(
                f,
                "SNP report SIGNING_KEY is {signing_key}, not the VCEK (0); refused"
            ),
            SnpError::ReportedTcbNotCorroborated { report, vcek } => write!(
                f,
                "SNP REPORTED_TCB {report:?} is not the TCB the VCEK certifies {vcek:?}; refused"
            ),
            SnpError::ChipIdNotCorroborated => {
                write!(f, "SNP CHIP_ID does not match the VCEK hwID; refused")
            }
            SnpError::PolicyReservedBitClear { policy } => write!(
                f,
                "SNP guest policy {policy:#x} has reserved bit 17 clear; refused"
            ),
            SnpError::PolicyUnknownBitsSet { policy } => write!(
                f,
                "SNP guest policy {policy:#x} sets bits this verifier cannot evaluate; refused"
            ),
            SnpError::DebugGuest { policy } => write!(
                f,
                "SNP guest policy {policy:#x} allows DEBUG (host can decrypt guest memory); refused"
            ),
            SnpError::MigrationAgentAllowed { policy } => write!(
                f,
                "SNP guest policy {policy:#x} allows a migration agent; refused"
            ),
            SnpError::RequiredPolicyBitsMissing { policy, required } => write!(
                f,
                "SNP guest policy {policy:#x} lacks required bits {required:#x}; refused"
            ),
            SnpError::VmplNotAllowed { vmpl } => {
                write!(f, "SNP report from VMPL {vmpl} is outside the accepted set; refused")
            }
            SnpError::GuestSvnBelowMinimum { guest_svn, min } => write!(
                f,
                "SNP GUEST_SVN {guest_svn} is below the minimum {min}; refused"
            ),
        }
    }
}

impl std::error::Error for SnpError {}

/// Verifier for AMD SEV-SNP attestation reports. Fail-closed unless pinned AMD roots
/// (ARK/ASK) are installed. The presented report bytes are `report(1184) ‖ vcek_der`.
///
/// **Every accepting constructor takes an [`SnpPolicy`]**, and an `SnpPolicy` exists only
/// with its TCB and guest-SVN floors named. So there is no accepting verifier without a
/// floor, and none that accepts a debug guest unless someone wrote
/// `accept_debug_guests_insecure`.
///
/// What the verifier binds, in order: the VCEK chains to the pinned ARK (and no configured
/// CRL revokes it); the report body is signed by that VCEK, as `KEY_INFO` says; the
/// report's `REPORTED_TCB` and `CHIP_ID` equal what the VCEK certificate endorses (so a
/// key extracted from an old-TCB chip cannot claim a new TCB); the guest policy, VMPL and
/// guest SVN meet the policy. Any failure is an `Err`. Then the floor is applied to the
/// **certificate's** TCB: below it yields `TcbStatus::BelowPolicy`, which the
/// [`crate::attested_data`] weld and `cell`'s `tee_attest.rs` gate refuse.
pub struct SnpVerifier {
    /// Pinned AMD roots. `None` = fail-closed (reject every report).
    trust: Option<SnpTrust>,
    /// The policy every accepting constructor names. `None` exactly when `trust` is.
    policy: Option<SnpPolicy>,
}

/// A report that passed every gate, with the values it was judged on.
#[derive(Debug, Clone)]
pub struct SnpVerified {
    pub report: SnpReport,
    pub vcek: VcekEndorsement,
    pub claims: TeeReportClaims,
}

impl SnpVerifier {
    /// A fail-closed verifier: with no pinned AMD roots it rejects every report before
    /// any policy decision, so it carries no policy.
    pub fn new() -> SnpVerifier {
        SnpVerifier {
            trust: None,
            policy: None,
        }
    }

    /// Anchor to an explicit [`SnpTrust`] (roots, product, CRLs) under `policy`.
    pub fn with_trust(trust: SnpTrust, policy: SnpPolicy) -> SnpVerifier {
        SnpVerifier {
            trust: Some(trust),
            policy: Some(policy),
        }
    }

    /// Install the pinned AMD roots (self-signed ARK DER + ASK DER) for `product`.
    pub fn with_pinned_roots(
        ark_der: Vec<u8>,
        ask_der: Vec<u8>,
        product: SnpProduct,
        policy: SnpPolicy,
    ) -> SnpVerifier {
        SnpVerifier::with_trust(
            SnpTrust {
                ark_der,
                ask_der,
                product,
                crls: Vec::new(),
            },
            policy,
        )
    }

    /// Install the pinned AMD roots from **PEM** (operator-friendly). See
    /// [`SnpTrust::from_pem`] and [`amd_kds_cert_chain_url`] for the real cert source.
    /// Still fail-closed — a malformed PEM is an `Err`, never a silent accept.
    pub fn with_pinned_roots_pem(
        ark_pem: &str,
        ask_pem: &str,
        product: SnpProduct,
        policy: SnpPolicy,
    ) -> Result<SnpVerifier, String> {
        Ok(SnpVerifier::with_trust(
            SnpTrust::from_pem(ark_pem, ask_pem, product)?,
            policy,
        ))
    }

    /// Anchor to the **real AMD roots** for a SEV-SNP product line — the ARK/ASK embedded
    /// from the AMD KDS (provenance in [`snp_chain`]) — under `policy`. This is the
    /// production anchor.
    pub fn new_with_amd_roots(
        product: SnpProduct,
        policy: SnpPolicy,
    ) -> Result<SnpVerifier, String> {
        Ok(SnpVerifier::with_trust(
            SnpTrust::for_product(product)?,
            policy,
        ))
    }

    /// Add an operator-supplied DER CRL to the pinned trust (see [`SnpTrust::with_crl`]).
    /// On a fail-closed verifier (no roots) there is nothing to add it to; it still
    /// refuses everything.
    pub fn with_crl(mut self, crl_der: Vec<u8>) -> SnpVerifier {
        self.trust = self.trust.map(|t| t.with_crl(crl_der));
        self
    }

    /// Verify `report(1184) ‖ vcek_der`, returning the named refusal on failure.
    pub fn verify(&self, report_bytes: &[u8]) -> Result<SnpVerified, SnpError> {
        if report_bytes.len() < REPORT_LEN {
            return Err(SnpError::TooShort(report_bytes.len()));
        }
        // Fail closed BEFORE anything else if no pinned roots are installed.
        let (trust, policy) = match (&self.trust, &self.policy) {
            (Some(t), Some(p)) => (t, p),
            _ => return Err(SnpError::NoPinnedRoots),
        };
        let report = SnpReport::parse(&report_bytes[..REPORT_LEN], trust.product)
            .map_err(SnpError::Parse)?;
        let vcek_der = &report_bytes[REPORT_LEN..];

        let vcek = verify_snp_cert_chain(vcek_der, trust).map_err(SnpError::Chain)?;
        verify_snp_signature(&report, &vcek.key).map_err(SnpError::Signature)?;
        if report.signing_key() != SIGNING_KEY_VCEK {
            return Err(SnpError::SigningKeyNotVcek {
                signing_key: report.signing_key(),
            });
        }

        // F1: the report's TCB and chip id are the key-holder's claims; the certificate
        // is AMD's statement of which chip at which TCB this key belongs to.
        if report.reported_tcb != vcek.tcb {
            return Err(SnpError::ReportedTcbNotCorroborated {
                report: report.reported_tcb,
                vcek: vcek.tcb,
            });
        }
        if report.chip_id != vcek.hw_id || report.chip_id.iter().all(|&b| b == 0) {
            return Err(SnpError::ChipIdNotCorroborated);
        }

        // F2: the launch policy, privilege level and guest SVN.
        let p = report.policy;
        if p & policy_bits::RESERVED_MBO == 0 {
            return Err(SnpError::PolicyReservedBitClear { policy: p });
        }
        if p & !policy_bits::KNOWN != 0 {
            return Err(SnpError::PolicyUnknownBitsSet { policy: p });
        }
        if p & policy_bits::DEBUG != 0 && !policy.allow_debug {
            return Err(SnpError::DebugGuest { policy: p });
        }
        if p & policy_bits::MIGRATE_MA != 0 && !policy.allow_migration_agent {
            return Err(SnpError::MigrationAgentAllowed { policy: p });
        }
        if p & policy.required_policy_bits != policy.required_policy_bits {
            return Err(SnpError::RequiredPolicyBitsMissing {
                policy: p,
                required: policy.required_policy_bits,
            });
        }
        if !policy.vmpl_allowed(report.vmpl) {
            return Err(SnpError::VmplNotAllowed { vmpl: report.vmpl });
        }
        if report.guest_svn < policy.min_guest_svn {
            return Err(SnpError::GuestSvnBelowMinimum {
                guest_svn: report.guest_svn,
                min: policy.min_guest_svn,
            });
        }

        // The floor, on the CERTIFICATE's TCB (equal to REPORTED_TCB, checked above). SNP
        // genuinely has a TCB rung, so this is `MetPolicy`/`BelowPolicy` and never
        // `NoPolicyOnPlatform` — that arm is Nitro's.
        let claims = TeeReportClaims {
            measurement: report.folded_measurement(),
            report_data: report.report_data_32(),
            tcb: if vcek.tcb.meets(&policy.min_tcb) {
                TcbStatus::MetPolicy
            } else {
                TcbStatus::BelowPolicy
            },
        };
        Ok(SnpVerified {
            report,
            vcek,
            claims,
        })
    }
}

impl Default for SnpVerifier {
    fn default() -> Self {
        Self::new()
    }
}

impl TeeAttestationVerifier for SnpVerifier {
    fn verify_report(
        &self,
        kind: TeeQuoteKind,
        report_bytes: &[u8],
    ) -> Result<TeeReportClaims, String> {
        if kind != TeeQuoteKind::SevSnp {
            return Err(SnpError::WrongKind(kind).to_string());
        }
        self.verify(report_bytes)
            .map(|v| v.claims)
            .map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p384::ecdsa::signature::Signer;
    use p384::ecdsa::SigningKey;

    const HONEST_TCB: TcbVersion = TcbVersion {
        fmc: 0,
        bootloader: 3,
        tee: 1,
        snp: 8,
        microcode: 72,
    };
    const HONEST_TURIN_TCB: TcbVersion = TcbVersion {
        fmc: 2,
        bootloader: 3,
        tee: 1,
        snp: 8,
        microcode: 72,
    };
    const HONEST_POLICY: u64 = policy_bits::RESERVED_MBO | policy_bits::SMT;
    const HONEST_GUEST_SVN: u32 = 7;

    fn honest_chip_id() -> [u8; CHIP_ID_LEN] {
        let mut c = [0u8; CHIP_ID_LEN];
        for (i, b) in c.iter_mut().enumerate() {
            *b = 0x11u8.wrapping_add(i as u8);
        }
        c
    }

    /// The fields of a synthetic report, each mutable independently so a forgery changes
    /// exactly one thing relative to the honest report.
    #[derive(Clone)]
    struct Fields {
        version: u32,
        guest_svn: u32,
        policy: u64,
        vmpl: u32,
        sig_algo: u32,
        key_info: u32,
        reported_tcb: TcbVersion,
        chip_id: [u8; CHIP_ID_LEN],
    }

    fn honest_fields(product: SnpProduct) -> Fields {
        Fields {
            version: if product == SnpProduct::Turin { 3 } else { 2 },
            guest_svn: HONEST_GUEST_SVN,
            policy: HONEST_POLICY,
            vmpl: 0,
            sig_algo: SIG_ALGO_ECDSA_P384_SHA384,
            key_info: 0,
            reported_tcb: if product.has_fmc() {
                HONEST_TURIN_TCB
            } else {
                HONEST_TCB
            },
            chip_id: honest_chip_id(),
        }
    }

    /// Lay out an (unsigned) report from `f` under `product`'s TCB layout.
    fn layout(f: &Fields, product: SnpProduct) -> Vec<u8> {
        let mut r = vec![0u8; REPORT_LEN];
        r[OFF_VERSION..OFF_VERSION + 4].copy_from_slice(&f.version.to_le_bytes());
        r[OFF_GUEST_SVN..OFF_GUEST_SVN + 4].copy_from_slice(&f.guest_svn.to_le_bytes());
        r[OFF_POLICY..OFF_POLICY + 8].copy_from_slice(&f.policy.to_le_bytes());
        r[OFF_VMPL..OFF_VMPL + 4].copy_from_slice(&f.vmpl.to_le_bytes());
        r[OFF_SIGNATURE_ALGO..OFF_SIGNATURE_ALGO + 4].copy_from_slice(&f.sig_algo.to_le_bytes());
        r[OFF_KEY_INFO..OFF_KEY_INFO + 4].copy_from_slice(&f.key_info.to_le_bytes());
        let tcb = f.reported_tcb.to_report_bytes(product);
        r[OFF_CURRENT_TCB..OFF_CURRENT_TCB + 8].copy_from_slice(&tcb);
        r[OFF_REPORTED_TCB..OFF_REPORTED_TCB + 8].copy_from_slice(&tcb);
        for i in 0..REPORT_DATA_LEN {
            r[OFF_REPORT_DATA + i] = i as u8;
        }
        for i in 0..MEASUREMENT_LEN {
            r[OFF_MEASUREMENT + i] = 0xA0;
        }
        r[OFF_CHIP_ID..OFF_CHIP_ID + CHIP_ID_LEN].copy_from_slice(&f.chip_id);
        r
    }

    /// A well-formed Milan-layout synthetic report (unsigned).
    fn synthetic_report() -> Vec<u8> {
        layout(&honest_fields(SnpProduct::Milan), SnpProduct::Milan)
    }

    /// Place a p384 signature into the report's AMD little-endian R/S component fields.
    fn embed_signature(report: &mut [u8], sig: &Signature) {
        let be = sig.to_bytes(); // 96 bytes big-endian R‖S
        for i in 0..P384_SCALAR_LEN {
            report[OFF_SIGNATURE + i] = be[P384_SCALAR_LEN - 1 - i]; // R little-endian
            report[OFF_SIGNATURE + SIG_COMPONENT_LEN + i] = be[2 * P384_SCALAR_LEN - 1 - i];
            // S LE
        }
    }

    fn sign_report(bytes: &mut [u8], signer: &SigningKey) {
        let sig: Signature = signer.sign(&bytes[..OFF_SIGNATURE]);
        embed_signature(bytes, &sig);
    }

    #[test]
    fn parse_and_field_extraction() {
        let bytes = synthetic_report();
        let rep = SnpReport::parse(&bytes, SnpProduct::Milan).expect("parse");
        assert_eq!(rep.version, 2);
        assert_eq!(rep.sig_algo, SIG_ALGO_ECDSA_P384_SHA384);
        assert_eq!(rep.guest_svn, 7);
        assert_eq!(rep.policy, HONEST_POLICY);
        assert_eq!(rep.vmpl, 0);
        assert_eq!(rep.signing_key(), 0);
        assert_eq!(rep.chip_id, honest_chip_id());
        assert_eq!(rep.reported_tcb, HONEST_TCB);
        let rd = rep.report_data_32();
        assert_eq!(rd[0], 0x00);
        assert_eq!(rd[31], 0x1F);
        let mut h = Sha256::new();
        h.update([0xA0u8; MEASUREMENT_LEN]);
        let expect: [u8; 32] = h.finalize().into();
        assert_eq!(rep.folded_measurement(), expect);
        // The same bytes read under Turin's layout give a different TCB.
        let tu = SnpReport::parse(&bytes, SnpProduct::Turin).unwrap();
        assert_ne!(tu.reported_tcb, rep.reported_tcb);
    }

    #[test]
    fn wrong_length_and_version_rejected() {
        assert!(SnpReport::parse(&[0u8; 100], SnpProduct::Milan).is_err());
        let mut bytes = synthetic_report();
        bytes[OFF_VERSION] = 9; // unknown version
        assert!(SnpReport::parse(&bytes, SnpProduct::Milan).is_err());
    }

    #[test]
    fn body_signature_roundtrips_with_real_p384() {
        let sk = SigningKey::from_slice(&[7u8; 48]).expect("signing key");
        let vk = *sk.verifying_key();
        let mut bytes = synthetic_report();
        sign_report(&mut bytes, &sk);
        let rep = SnpReport::parse(&bytes, SnpProduct::Milan).unwrap();
        verify_snp_signature(&rep, &vk).expect("valid signature");
        let mut tampered = bytes.clone();
        tampered[OFF_MEASUREMENT] ^= 0xFF;
        let rep2 = SnpReport::parse(&tampered, SnpProduct::Milan).unwrap();
        assert!(verify_snp_signature(&rep2, &vk).is_err());
    }

    #[test]
    fn wrong_sig_algo_rejected() {
        let sk = SigningKey::from_slice(&[9u8; 48]).unwrap();
        let vk = *sk.verifying_key();
        let mut bytes = synthetic_report();
        bytes[OFF_SIGNATURE_ALGO] = 2; // not ECDSA-P384/SHA-384
        let rep = SnpReport::parse(&bytes, SnpProduct::Milan).unwrap();
        assert!(verify_snp_signature(&rep, &vk).is_err());
    }

    #[test]
    fn fail_closed_without_pinned_roots() {
        let bytes = synthetic_report();
        let v = SnpVerifier::new();
        assert_eq!(v.verify(&bytes).unwrap_err(), SnpError::NoPinnedRoots);
        let err = v
            .verify_report(TeeQuoteKind::SevSnp, &bytes)
            .expect_err("must fail closed");
        assert!(err.contains("fail-closed"), "unexpected error: {err}");
    }

    #[test]
    fn wrong_kind_rejected() {
        let bytes = synthetic_report();
        let v = SnpVerifier::new();
        assert!(v.verify_report(TeeQuoteKind::AwsNitro, &bytes).is_err());
    }

    #[test]
    fn too_short_rejected() {
        let v = SnpVerifier::new();
        assert_eq!(v.verify(&[0u8; 100]).unwrap_err(), SnpError::TooShort(100));
    }

    #[test]
    fn missing_vcek_fails_chain_seam() {
        let bytes = synthetic_report();
        let v = SnpVerifier::with_pinned_roots(
            vec![0u8; 4],
            vec![0u8; 4],
            SnpProduct::Milan,
            SnpPolicy::new(TcbVersion::default(), 0),
        );
        assert_eq!(
            v.verify(&bytes).unwrap_err(),
            SnpError::Chain(SnpChainError::NoVcek)
        );
    }

    // --- Self-signed test PKI: ARK -> ASK -> VCEK, all ECDSA-P384/SHA-384 ---
    //
    // Proves the cert-chain + body-signature + corroboration logic end-to-end with NO AMD
    // network fetch: a three-level P-384 PKI whose VCEK carries the AMD extensions, a
    // synthetic report signed with the VCEK private key, and the full pipeline. Real AMD
    // ARK/ASK sign RSA-4096 PSS; that link primitive and the real AMD CRLs are exercised in
    // `snp_chain::tests`.
    //
    // The forgeries below model the F1 attacker: someone holding a GENUINE VCEK private
    // key (e.g. extracted from a chip at a vulnerable TCB). Every forged report is signed
    // with that key, so the signature and the chain verify; each test changes one field
    // relative to the honest report, asserts the bytes differ, and asserts the named gate
    // refuses.
    use p384::pkcs8::DecodePrivateKey;
    use p384::SecretKey;
    use rcgen::{
        date_time_ymd, BasicConstraints, CertificateParams, CertificateRevocationListParams,
        CustomExtension, DnType, IsCa, Issuer, KeyIdMethod, KeyPair, KeyUsagePurpose,
        RevokedCertParams, SerialNumber, PKCS_ECDSA_P384_SHA384,
    };

    const ASK_SERIAL: u64 = 0x0A51;
    const VCEK_SERIAL: u64 = 0x0FCE;

    struct TestPki {
        product: SnpProduct,
        ark_der: Vec<u8>,
        ask_der: Vec<u8>,
        vcek_der: Vec<u8>,
        ark_pem: String,
        ask_pem: String,
        vcek_signer: SigningKey,
        ark_key: KeyPair,
        ark_params: CertificateParams,
        ask_key: KeyPair,
        ask_params: CertificateParams,
    }

    fn gen_key() -> KeyPair {
        KeyPair::generate_for(&PKCS_ECDSA_P384_SHA384).expect("p384 keygen")
    }

    fn ca_params(cn: &str, serial: Option<u64>) -> CertificateParams {
        let mut p = CertificateParams::new(Vec::<String>::new()).expect("params");
        p.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
        p.key_usages = vec![KeyUsagePurpose::KeyCertSign, KeyUsagePurpose::CrlSign];
        p.distinguished_name.push(DnType::CommonName, cn);
        p.serial_number = serial.map(SerialNumber::from);
        p
    }

    fn signer_from(kp: &KeyPair) -> SigningKey {
        let secret = SecretKey::from_pkcs8_der(&kp.serialize_der()).expect("pkcs8 -> p384");
        SigningKey::from(secret)
    }

    /// OID string -> the arc vector rcgen wants.
    fn arcs(oid: &str) -> Vec<u64> {
        oid.split('.').map(|a| a.parse().unwrap()).collect()
    }

    fn spl_der(v: u8) -> Vec<u8> {
        if v < 0x80 {
            vec![0x02, 0x01, v]
        } else {
            vec![0x02, 0x02, 0x00, v]
        }
    }

    /// What the test VCEK certificate endorses. `omit` drops one extension by OID.
    struct VcekExt {
        tcb: TcbVersion,
        hw_id: [u8; CHIP_ID_LEN],
        omit: Option<&'static str>,
    }

    fn vcek_extensions(e: &VcekExt, product: SnpProduct) -> Vec<CustomExtension> {
        let mut hw = vec![0x04, 0x40];
        hw.extend_from_slice(&e.hw_id);
        let mut all = vec![
            (snp_chain::OID_VCEK_BL_SPL, spl_der(e.tcb.bootloader)),
            (snp_chain::OID_VCEK_TEE_SPL, spl_der(e.tcb.tee)),
            (snp_chain::OID_VCEK_SNP_SPL, spl_der(e.tcb.snp)),
            (snp_chain::OID_VCEK_UCODE_SPL, spl_der(e.tcb.microcode)),
            (snp_chain::OID_VCEK_HW_ID, hw),
        ];
        if product.has_fmc() {
            all.push((snp_chain::OID_VCEK_FMC_SPL, spl_der(e.tcb.fmc)));
        }
        all.into_iter()
            .filter(|(o, _)| Some(*o) != e.omit)
            .map(|(o, c)| CustomExtension::from_oid_content(&arcs(o), c))
            .collect()
    }

    fn build_pki_with(product: SnpProduct, ext: VcekExt) -> TestPki {
        let ark_key = gen_key();
        let ark_params = ca_params("ARK-test", None);
        let ark_cert = ark_params.self_signed(&ark_key).expect("ARK self-sign");

        let ask_key = gen_key();
        let ask_params = ca_params("ASK-test", Some(ASK_SERIAL));
        let ask_cert = ask_params
            .signed_by(&ask_key, &Issuer::from_params(&ark_params, &ark_key))
            .expect("ASK<-ARK");

        let vcek_key = gen_key();
        let mut vcek_params = CertificateParams::new(Vec::<String>::new()).expect("params");
        vcek_params
            .distinguished_name
            .push(DnType::CommonName, "VCEK-test");
        vcek_params.serial_number = Some(SerialNumber::from(VCEK_SERIAL));
        vcek_params.custom_extensions = vcek_extensions(&ext, product);
        let vcek_cert = vcek_params
            .signed_by(&vcek_key, &Issuer::from_params(&ask_params, &ask_key))
            .expect("VCEK<-ASK");

        TestPki {
            product,
            ark_der: ark_cert.der().to_vec(),
            ask_der: ask_cert.der().to_vec(),
            vcek_der: vcek_cert.der().to_vec(),
            ark_pem: ark_cert.pem(),
            ask_pem: ask_cert.pem(),
            vcek_signer: signer_from(&vcek_key),
            ark_key,
            ark_params,
            ask_key,
            ask_params,
        }
    }

    /// The honest PKI: a VCEK endorsing exactly the honest report's TCB and chip id.
    fn build_pki_for(product: SnpProduct) -> TestPki {
        build_pki_with(
            product,
            VcekExt {
                tcb: honest_fields(product).reported_tcb,
                hw_id: honest_chip_id(),
                omit: None,
            },
        )
    }

    fn build_pki() -> TestPki {
        build_pki_for(SnpProduct::Milan)
    }

    fn trust_of(pki: &TestPki) -> SnpTrust {
        SnpTrust {
            ark_der: pki.ark_der.clone(),
            ask_der: pki.ask_der.clone(),
            product: pki.product,
            crls: Vec::new(),
        }
    }

    fn honest_policy(pki: &TestPki) -> SnpPolicy {
        SnpPolicy::new(honest_fields(pki.product).reported_tcb, HONEST_GUEST_SVN)
    }

    /// `report(1184) ‖ vcek_der`, the report laid out from `f` and signed by the VCEK key.
    fn proof_for(pki: &TestPki, f: &Fields) -> Vec<u8> {
        let mut bytes = layout(f, pki.product);
        sign_report(&mut bytes, &pki.vcek_signer);
        bytes.extend_from_slice(&pki.vcek_der);
        bytes
    }

    /// Build the honest proof and a forgery that changes `f` via `mutate`; assert the
    /// forgery's bytes differ from the honest ones and that the honest one passes the same
    /// verifier; return the forgery's verdict.
    fn forge(
        pki: &TestPki,
        v: &SnpVerifier,
        mutate: impl FnOnce(&mut Fields),
    ) -> Result<SnpVerified, SnpError> {
        let honest = honest_fields(pki.product);
        let honest_proof = proof_for(pki, &honest);
        v.verify(&honest_proof)
            .expect("the honest report passes this verifier");
        let mut forged = honest.clone();
        mutate(&mut forged);
        let forged_proof = proof_for(pki, &forged);
        assert_ne!(
            forged_proof[..OFF_SIGNATURE],
            honest_proof[..OFF_SIGNATURE],
            "the forgery must differ from the honest report"
        );
        v.verify(&forged_proof)
    }

    fn verifier(pki: &TestPki, policy: SnpPolicy) -> SnpVerifier {
        SnpVerifier::with_trust(trust_of(pki), policy)
    }

    #[test]
    fn self_signed_pki_chain_verifies_and_returns_the_endorsement() {
        let pki = build_pki();
        let e = verify_snp_cert_chain(&pki.vcek_der, &trust_of(&pki)).expect("valid chain");
        assert_eq!(&e.key, pki.vcek_signer.verifying_key());
        assert_eq!(e.tcb, HONEST_TCB);
        assert_eq!(e.hw_id, honest_chip_id());
    }

    /// The one honest report that still passes, through the trait entry point.
    #[test]
    fn honest_report_passes_every_gate() {
        let pki = build_pki();
        let proof = proof_for(&pki, &honest_fields(SnpProduct::Milan));
        let v = verifier(&pki, honest_policy(&pki));
        let claims = v
            .verify_report(TeeQuoteKind::SevSnp, &proof)
            .expect("full pipeline accepts");
        assert_eq!(claims.report_data[0], 0x00);
        assert_eq!(claims.report_data[31], 0x1F);
        assert_eq!(claims.tcb, TcbStatus::MetPolicy, "at-floor TCB is trusted");
    }

    #[test]
    fn honest_turin_report_passes_under_turin_layout() {
        let pki = build_pki_for(SnpProduct::Turin);
        let proof = proof_for(&pki, &honest_fields(SnpProduct::Turin));
        let got = verifier(&pki, honest_policy(&pki))
            .verify(&proof)
            .expect("Turin accepts");
        assert_eq!(got.vcek.tcb, HONEST_TURIN_TCB);
        assert_eq!(got.claims.tcb, TcbStatus::MetPolicy);
    }

    #[test]
    fn with_pinned_roots_pem_accepts_full_chain() {
        let pki = build_pki();
        let proof = proof_for(&pki, &honest_fields(SnpProduct::Milan));
        let v = SnpVerifier::with_pinned_roots_pem(
            &pki.ark_pem,
            &pki.ask_pem,
            SnpProduct::Milan,
            honest_policy(&pki),
        )
        .expect("PEM roots load");
        v.verify(&proof).expect("pipeline via PEM roots accepts");
    }

    // ---- F2: guest policy, VMPL, guest SVN ----

    #[test]
    fn forged_debug_guest_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.policy |= policy_bits::DEBUG).unwrap_err();
        assert_eq!(
            err,
            SnpError::DebugGuest {
                policy: HONEST_POLICY | policy_bits::DEBUG
            }
        );
        // Only the explicitly-named insecure knob admits it.
        let lab = verifier(&pki, honest_policy(&pki).accept_debug_guests_insecure());
        forge(&pki, &lab, |f| f.policy |= policy_bits::DEBUG).expect("lab rig accepts debug");
    }

    #[test]
    fn forged_migration_agent_guest_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.policy |= policy_bits::MIGRATE_MA).unwrap_err();
        assert!(
            matches!(err, SnpError::MigrationAgentAllowed { .. }),
            "{err}"
        );
    }

    #[test]
    fn forged_policy_with_reserved_bit_clear_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.policy &= !policy_bits::RESERVED_MBO).unwrap_err();
        assert!(
            matches!(err, SnpError::PolicyReservedBitClear { .. }),
            "{err}"
        );
    }

    #[test]
    fn forged_policy_with_unknown_bits_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.policy |= 1 << 40).unwrap_err();
        assert!(
            matches!(err, SnpError::PolicyUnknownBitsSet { .. }),
            "{err}"
        );
    }

    #[test]
    fn forged_policy_missing_a_required_bit_is_refused() {
        let pki = build_pki();
        let policy = honest_policy(&pki)
            .require_policy_bits(policy_bits::SMT)
            .unwrap();
        let v = verifier(&pki, policy);
        let err = forge(&pki, &v, |f| f.policy &= !policy_bits::SMT).unwrap_err();
        assert!(
            matches!(err, SnpError::RequiredPolicyBitsMissing { required, .. } if required == policy_bits::SMT),
            "{err}"
        );
        assert!(honest_policy(&pki).require_policy_bits(1 << 40).is_err());
    }

    #[test]
    fn forged_vmpl_outside_policy_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.vmpl = 1).unwrap_err();
        assert_eq!(err, SnpError::VmplNotAllowed { vmpl: 1 });
        let err = forge(&pki, &v, |f| f.vmpl = 7).unwrap_err();
        assert_eq!(err, SnpError::VmplNotAllowed { vmpl: 7 });
        // Widening the set is explicit, and VMPLs that do not exist cannot be named.
        let svsm = verifier(&pki, honest_policy(&pki).allow_vmpls(&[0, 1]).unwrap());
        forge(&pki, &svsm, |f| f.vmpl = 1).expect("VMPL 1 accepted once named");
        assert!(honest_policy(&pki).allow_vmpls(&[4]).is_err());
        assert!(honest_policy(&pki).allow_vmpls(&[]).is_err());
    }

    #[test]
    fn forged_guest_svn_below_minimum_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.guest_svn = HONEST_GUEST_SVN - 1).unwrap_err();
        assert_eq!(
            err,
            SnpError::GuestSvnBelowMinimum {
                guest_svn: HONEST_GUEST_SVN - 1,
                min: HONEST_GUEST_SVN
            }
        );
    }

    // ---- F1: the report's TCB and chip id must be what the VCEK certifies ----

    /// The F1 attack: a key extracted at an old TCB, claiming a patched one. The cert says
    /// microcode 72; the report claims 80 (above any floor). Before this lane that report
    /// was `MetPolicy`.
    #[test]
    fn forged_reported_tcb_above_the_certified_tcb_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let claimed = TcbVersion {
            microcode: 80,
            ..HONEST_TCB
        };
        let err = forge(&pki, &v, |f| f.reported_tcb = claimed).unwrap_err();
        assert_eq!(
            err,
            SnpError::ReportedTcbNotCorroborated {
                report: claimed,
                vcek: HONEST_TCB
            }
        );
        // Every component is bound, not just microcode.
        for t in [
            TcbVersion {
                bootloader: 4,
                ..HONEST_TCB
            },
            TcbVersion {
                tee: 2,
                ..HONEST_TCB
            },
            TcbVersion {
                snp: 9,
                ..HONEST_TCB
            },
            TcbVersion {
                microcode: 71,
                ..HONEST_TCB
            },
        ] {
            assert!(matches!(
                forge(&pki, &v, |f| f.reported_tcb = t).unwrap_err(),
                SnpError::ReportedTcbNotCorroborated { .. }
            ));
        }
    }

    #[test]
    fn forged_turin_fmc_is_refused() {
        let pki = build_pki_for(SnpProduct::Turin);
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.reported_tcb.fmc = 3).unwrap_err();
        assert!(
            matches!(err, SnpError::ReportedTcbNotCorroborated { .. }),
            "{err}"
        );
    }

    #[test]
    fn forged_chip_id_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.chip_id[0] ^= 0x01).unwrap_err();
        assert_eq!(err, SnpError::ChipIdNotCorroborated);
    }

    /// A masked (all-zero) CHIP_ID is refused even under a VCEK whose hwID is all zeros.
    #[test]
    fn masked_chip_id_is_refused() {
        let pki = build_pki_with(
            SnpProduct::Milan,
            VcekExt {
                tcb: HONEST_TCB,
                hw_id: [0u8; CHIP_ID_LEN],
                omit: None,
            },
        );
        let mut f = honest_fields(SnpProduct::Milan);
        f.chip_id = [0u8; CHIP_ID_LEN];
        let proof = proof_for(&pki, &f);
        assert_ne!(
            proof[..OFF_SIGNATURE],
            proof_for(&build_pki(), &honest_fields(SnpProduct::Milan))[..OFF_SIGNATURE]
        );
        let err = verifier(&pki, honest_policy(&pki))
            .verify(&proof)
            .unwrap_err();
        assert_eq!(err, SnpError::ChipIdNotCorroborated);
    }

    /// A VCEK missing any AMD extension corroborates nothing and is refused, by name.
    #[test]
    fn vcek_missing_an_amd_extension_is_refused() {
        for (product, oid, name) in [
            (SnpProduct::Milan, snp_chain::OID_VCEK_BL_SPL, "blSPL"),
            (SnpProduct::Milan, snp_chain::OID_VCEK_TEE_SPL, "teeSPL"),
            (SnpProduct::Milan, snp_chain::OID_VCEK_SNP_SPL, "snpSPL"),
            (SnpProduct::Milan, snp_chain::OID_VCEK_UCODE_SPL, "ucodeSPL"),
            (SnpProduct::Milan, snp_chain::OID_VCEK_HW_ID, "hwID"),
            (SnpProduct::Turin, snp_chain::OID_VCEK_FMC_SPL, "fmcSPL"),
        ] {
            let pki = build_pki_with(
                product,
                VcekExt {
                    tcb: honest_fields(product).reported_tcb,
                    hw_id: honest_chip_id(),
                    omit: Some(oid),
                },
            );
            let proof = proof_for(&pki, &honest_fields(product));
            let err = verifier(&pki, honest_policy(&pki))
                .verify(&proof)
                .unwrap_err();
            assert_eq!(
                err,
                SnpError::Chain(SnpChainError::VcekExtensionMissing { name }),
                "{product:?} without {name}"
            );
        }
    }

    #[test]
    fn forged_vlek_signing_key_is_refused() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let err = forge(&pki, &v, |f| f.key_info = 1 << 2).unwrap_err();
        assert_eq!(err, SnpError::SigningKeyNotVcek { signing_key: 1 });
    }

    /// A report whose bytes change WITHOUT a re-signature is refused at the signature.
    #[test]
    fn unsigned_tamper_is_refused_at_the_signature() {
        let pki = build_pki();
        let v = verifier(&pki, honest_policy(&pki));
        let mut proof = proof_for(&pki, &honest_fields(SnpProduct::Milan));
        v.verify(&proof).expect("honest");
        proof[OFF_POLICY + 2] |= 0x08; // DEBUG, not re-signed
        assert!(matches!(
            v.verify(&proof).unwrap_err(),
            SnpError::Signature(_)
        ));
    }

    /// FALSIFIER for TEE-audit F1 (floor): a GENUINE down-level chip — its VCEK certifies
    /// the low TCB and its report says the same — yields `BelowPolicy`; at/above is trusted.
    #[test]
    fn down_level_certified_tcb_is_below_policy_at_or_above_is_trusted() {
        let floor = HONEST_TCB;
        for (tcb, want) in [
            (
                TcbVersion {
                    microcode: 71,
                    ..HONEST_TCB
                },
                TcbStatus::BelowPolicy,
            ),
            (
                TcbVersion {
                    bootloader: 2,
                    ..HONEST_TCB
                },
                TcbStatus::BelowPolicy,
            ),
            (HONEST_TCB, TcbStatus::MetPolicy),
            (
                TcbVersion {
                    fmc: 0,
                    bootloader: 4,
                    tee: 2,
                    snp: 9,
                    microcode: 80,
                },
                TcbStatus::MetPolicy,
            ),
        ] {
            let pki = build_pki_with(
                SnpProduct::Milan,
                VcekExt {
                    tcb,
                    hw_id: honest_chip_id(),
                    omit: None,
                },
            );
            let mut f = honest_fields(SnpProduct::Milan);
            f.reported_tcb = tcb;
            let got = verifier(&pki, SnpPolicy::new(floor, HONEST_GUEST_SVN))
                .verify(&proof_for(&pki, &f))
                .expect("a genuine chip at any TCB verifies");
            assert_eq!(got.claims.tcb, want, "{tcb:?}");
        }
    }

    // ---- F3: revocation ----

    fn crl_signed_by(
        issuer_params: &CertificateParams,
        issuer_key: &KeyPair,
        revoked: &[u64],
        next_update_year: i32,
    ) -> Vec<u8> {
        let params = CertificateRevocationListParams {
            this_update: date_time_ymd(2020, 1, 1),
            next_update: date_time_ymd(next_update_year, 1, 1),
            crl_number: SerialNumber::from(1u64),
            issuing_distribution_point: None,
            revoked_certs: revoked
                .iter()
                .map(|&s| RevokedCertParams {
                    serial_number: SerialNumber::from(s),
                    revocation_time: date_time_ymd(2021, 1, 1),
                    reason_code: None,
                    invalidity_date: None,
                })
                .collect(),
            key_identifier_method: KeyIdMethod::Sha256,
        };
        params
            .signed_by(&Issuer::from_params(issuer_params, issuer_key))
            .expect("CRL sign")
            .der()
            .to_vec()
    }

    fn verify_with_crl(pki: &TestPki, crl: Vec<u8>) -> Result<SnpVerified, SnpError> {
        let proof = proof_for(pki, &honest_fields(pki.product));
        verifier(pki, honest_policy(pki))
            .with_crl(crl)
            .verify(&proof)
    }

    #[test]
    fn crl_that_revokes_nothing_relevant_passes() {
        let pki = build_pki();
        verify_with_crl(
            &pki,
            crl_signed_by(&pki.ark_params, &pki.ark_key, &[0x9999], 2100),
        )
        .expect("ARK CRL not listing the ASK");
        verify_with_crl(
            &pki,
            crl_signed_by(&pki.ask_params, &pki.ask_key, &[0x9999], 2100),
        )
        .expect("ASK CRL not listing the VCEK");
    }

    #[test]
    fn revoked_vcek_is_refused() {
        let pki = build_pki();
        let err = verify_with_crl(
            &pki,
            crl_signed_by(&pki.ask_params, &pki.ask_key, &[VCEK_SERIAL], 2100),
        )
        .unwrap_err();
        assert_eq!(
            err,
            SnpError::Chain(SnpChainError::Revoked { cert: "VCEK" })
        );
    }

    #[test]
    fn revoked_ask_is_refused() {
        let pki = build_pki();
        let err = verify_with_crl(
            &pki,
            crl_signed_by(&pki.ark_params, &pki.ark_key, &[ASK_SERIAL], 2100),
        )
        .unwrap_err();
        assert_eq!(err, SnpError::Chain(SnpChainError::Revoked { cert: "ASK" }));
    }

    #[test]
    fn stale_crl_is_refused() {
        let pki = build_pki();
        let err = verify_with_crl(
            &pki,
            crl_signed_by(&pki.ark_params, &pki.ark_key, &[], 2021),
        )
        .unwrap_err();
        assert!(
            matches!(err, SnpError::Chain(SnpChainError::CrlNotCurrent(_))),
            "{err}"
        );
    }

    /// A CRL under the right issuer NAME but the wrong KEY does not verify; a CRL from a
    /// stranger is refused as an unknown issuer. Neither is silently ignored.
    #[test]
    fn crl_from_wrong_key_or_stranger_is_refused() {
        let pki = build_pki();
        let impostor = gen_key();
        let err = verify_with_crl(&pki, crl_signed_by(&pki.ark_params, &impostor, &[], 2100))
            .unwrap_err();
        assert!(
            matches!(err, SnpError::Chain(SnpChainError::CrlSignature(_))),
            "{err}"
        );
        let stranger = ca_params("Stranger-CA", None);
        let err =
            verify_with_crl(&pki, crl_signed_by(&stranger, &impostor, &[], 2100)).unwrap_err();
        assert_eq!(err, SnpError::Chain(SnpChainError::CrlIssuerUnknown));
    }

    #[test]
    fn from_pem_roundtrips_der_and_verifies() {
        let pki = build_pki();
        let trust =
            SnpTrust::from_pem(&pki.ark_pem, &pki.ask_pem, SnpProduct::Milan).expect("from_pem");
        assert_eq!(trust.ark_der, pki.ark_der);
        assert_eq!(trust.ask_der, pki.ask_der);
        let e = verify_snp_cert_chain(&pki.vcek_der, &trust).expect("chain via PEM roots");
        assert_eq!(&e.key, pki.vcek_signer.verifying_key());
    }

    #[test]
    fn from_pem_rejects_non_certificate_label() {
        assert!(SnpTrust::from_pem("not a pem", "also not", SnpProduct::Milan).is_err());
    }

    #[test]
    fn wrong_ark_rejects_chain() {
        let pki = build_pki();
        let other = build_pki();
        let mut trust = trust_of(&pki);
        trust.ark_der = other.ark_der;
        assert!(matches!(
            verify_snp_cert_chain(&pki.vcek_der, &trust).unwrap_err(),
            SnpChainError::LinkSignature { .. }
        ));
    }

    #[test]
    fn tampered_vcek_rejects_chain() {
        let pki = build_pki();
        let mut bad = pki.vcek_der.clone();
        let n = bad.len();
        bad[n - 1] ^= 0xFF; // corrupt the VCEK signature tail
        assert!(verify_snp_cert_chain(&bad, &trust_of(&pki)).is_err());
    }

    /// Anchoring to the real embedded AMD roots: the roots load and the chain seam rejects
    /// an absent VCEK (fail-closed).
    #[test]
    fn new_with_amd_roots_anchors_real_chain() {
        for product in [SnpProduct::Milan, SnpProduct::Genoa, SnpProduct::Turin] {
            let v =
                SnpVerifier::new_with_amd_roots(product, SnpPolicy::new(TcbVersion::default(), 0))
                    .expect("real AMD roots load");
            let bytes = synthetic_report();
            assert_eq!(
                v.verify(&bytes).unwrap_err(),
                SnpError::Chain(SnpChainError::NoVcek)
            );
        }
    }
}

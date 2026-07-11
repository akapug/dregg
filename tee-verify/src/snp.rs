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
//! 3. **Cert chain** (behind the pinned-roots seam): VCEK ← ASK ← pinned **ARK**,
//!    structured like [`crate::verify_cert_chain`] with `x509-parser`'s `verify`
//!    feature. The VCEK certificate rides appended to the report bytes
//!    (`report(1184) ‖ vcek_der`); ASK + ARK are the operator-pinned AMD roots.
//!
//! **Fail-closed.** A [`SnpVerifier`] built with [`SnpVerifier::new`] carries no pinned
//! AMD roots and rejects *every* report (`Err`) before it would extract claims —
//! parsing and body-signature code are real, but no trust decision is made without the
//! pinned ARK/ASK. Install the real chain with [`SnpVerifier::with_pinned_roots`]. This
//! is the honest first cut: the report PARSING + field extraction + body-signature
//! verify are real; the chain-to-AMD-root is a clearly-marked seam that fails closed,
//! never silently accepts.

use dregg_cell::tee_attest::{TeeAttestationVerifier, TeeQuoteKind, TeeReportClaims};
use p384::ecdsa::signature::Verifier;
use p384::ecdsa::{Signature, VerifyingKey};
use sha2::{Digest, Sha256};
use x509_parser::prelude::*;

/// Total size of a SEV-SNP `ATTESTATION_REPORT` (`0x4A0`).
pub const REPORT_LEN: usize = 1184;

// Field offsets into the report (AMD SEV-SNP ABI Table 22).
const OFF_VERSION: usize = 0x000; // u32
const OFF_GUEST_SVN: usize = 0x004; // u32
const OFF_POLICY: usize = 0x008; // u64
const OFF_VMPL: usize = 0x030; // u32
const OFF_SIGNATURE_ALGO: usize = 0x034; // u32
const OFF_CURRENT_TCB: usize = 0x038; // TCB_VERSION (u64 LE)
const OFF_REPORT_DATA: usize = 0x050; // 64 bytes
const OFF_MEASUREMENT: usize = 0x090; // 48 bytes
const OFF_HOST_DATA: usize = 0x0C0; // 32 bytes
const OFF_REPORTED_TCB: usize = 0x180; // TCB_VERSION (u64 LE)
const OFF_CHIP_ID: usize = 0x1A0; // 64 bytes
const OFF_SIGNATURE: usize = 0x2A0; // 512-byte SIGNATURE block; also == length of the signed body

const REPORT_DATA_LEN: usize = 64;
const MEASUREMENT_LEN: usize = 48;
const HOST_DATA_LEN: usize = 32;
const CHIP_ID_LEN: usize = 64;

/// Each ECDSA component (R, S) occupies a fixed 72-byte little-endian field.
const SIG_COMPONENT_LEN: usize = 72;
/// P-384 scalars are 48 bytes; the upper 24 bytes of each 72-byte field are zero.
const P384_SCALAR_LEN: usize = 48;

/// `SIGNATURE_ALGO` value for ECDSA-P384 with SHA-384 (the only algo AMD emits today).
const SIG_ALGO_ECDSA_P384_SHA384: u32 = 1;

/// A parsed AMD SEV-SNP `TCB_VERSION` (8 bytes: bootloader, tee, [reserved×4], snp,
/// microcode). Compared component-wise against a pinned minimum for `tcb_ok`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TcbVersion {
    pub bootloader: u8,
    pub tee: u8,
    pub snp: u8,
    pub microcode: u8,
}

impl TcbVersion {
    fn from_le_bytes(b: [u8; 8]) -> TcbVersion {
        TcbVersion {
            bootloader: b[0],
            tee: b[1],
            // b[2..6] reserved
            snp: b[6],
            microcode: b[7],
        }
    }

    /// Every component is at least the pinned minimum (a down-level rung fails).
    pub fn meets(&self, min: &TcbVersion) -> bool {
        self.bootloader >= min.bootloader
            && self.tee >= min.tee
            && self.snp >= min.snp
            && self.microcode >= min.microcode
    }
}

/// A parsed SEV-SNP attestation report. All fields are read from fixed offsets; the raw
/// bytes are retained so the signed body and signature can be recovered exactly.
#[derive(Debug, Clone)]
pub struct SnpReport {
    pub version: u32,
    pub guest_svn: u32,
    pub policy: u64,
    pub vmpl: u32,
    pub sig_algo: u32,
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
    /// Parse exactly the 1184-byte `ATTESTATION_REPORT`. Real: every field comes from
    /// its fixed offset; the only rejections are a wrong length or an unknown VERSION.
    pub fn parse(bytes: &[u8]) -> Result<SnpReport, String> {
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
            current_tcb: TcbVersion::from_le_bytes(cur),
            reported_tcb: TcbVersion::from_le_bytes(rep),
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

/// The operator-pinned AMD roots. `ark_der` is the self-signed AMD Root Key; `ask_der`
/// is the AMD SEV Signing Key (intermediate, signed by ARK). These are chip-family
/// constants fetched once from the AMD KDS and pinned — the per-chip VCEK is presented
/// alongside each report.
#[derive(Debug, Clone)]
pub struct SnpTrust {
    pub ark_der: Vec<u8>,
    pub ask_der: Vec<u8>,
}

/// Verify VCEK ← ASK ← pinned-ARK and return the VCEK's P-384 public key.
///
/// Structured like [`crate::verify_cert_chain`]: each link's signature is checked
/// against its issuer's key and every cert's validity window is checked at wall-clock
/// now (SNP reports carry no timestamp of their own). NOTE: AMD's ARK/ASK sign with
/// RSA-4096 **PSS**; whether `x509-parser`'s `verify` feature accepts a given AMD root
/// determines whether a real chain verifies — either way this path only ever fails
/// *closed* (an unsupported signature is an `Err`, never a silent accept).
pub fn verify_snp_cert_chain(vcek_der: &[u8], trust: &SnpTrust) -> Result<VerifyingKey, String> {
    if vcek_der.is_empty() {
        return Err("no VCEK certificate appended to the SNP report bytes".into());
    }
    let (_, ark) =
        X509Certificate::from_der(&trust.ark_der).map_err(|e| format!("pinned ARK parse: {e}"))?;
    let (_, ask) =
        X509Certificate::from_der(&trust.ask_der).map_err(|e| format!("pinned ASK parse: {e}"))?;
    let (_, vcek) = X509Certificate::from_der(vcek_der).map_err(|e| format!("VCEK parse: {e}"))?;

    let now = ASN1Time::now();
    for (name, cert) in [("ARK", &ark), ("ASK", &ask), ("VCEK", &vcek)] {
        if !cert.validity().is_valid_at(now) {
            return Err(format!("{name} certificate is not valid now"));
        }
    }

    // ARK is self-signed (the trust anchor); ASK is signed by ARK; VCEK by ASK.
    ark.verify_signature(Some(ark.public_key()))
        .map_err(|e| format!("ARK self-signature: {e:?}"))?;
    ask.verify_signature(Some(ark.public_key()))
        .map_err(|e| format!("ASK←ARK signature: {e:?}"))?;
    vcek.verify_signature(Some(ask.public_key()))
        .map_err(|e| format!("VCEK←ASK signature: {e:?}"))?;

    let point = vcek.public_key().subject_public_key.data.as_ref();
    VerifyingKey::from_sec1_bytes(point).map_err(|e| format!("VCEK P-384 key: {e}"))
}

/// Verifier for AMD SEV-SNP attestation reports. Fail-closed unless pinned AMD roots
/// (ARK/ASK) are installed. The presented report bytes are `report(1184) ‖ vcek_der`.
pub struct SnpVerifier {
    /// Pinned AMD roots. `None` = fail-closed (reject every report).
    trust: Option<SnpTrust>,
    /// Minimum acceptable `REPORTED_TCB`; a report below it yields `tcb_ok = false`.
    min_tcb: TcbVersion,
}

impl SnpVerifier {
    /// A fail-closed verifier: parses + would body-verify, but with no pinned AMD roots
    /// it rejects every report (no trust decision without ARK/ASK).
    pub fn new() -> SnpVerifier {
        SnpVerifier {
            trust: None,
            min_tcb: TcbVersion::default(),
        }
    }

    /// Install the pinned AMD roots (self-signed ARK DER + ASK DER) — the real chain.
    pub fn with_pinned_roots(ark_der: Vec<u8>, ask_der: Vec<u8>) -> SnpVerifier {
        SnpVerifier {
            trust: Some(SnpTrust { ark_der, ask_der }),
            min_tcb: TcbVersion::default(),
        }
    }

    /// Pin a minimum `REPORTED_TCB`; reports below it get `tcb_ok = false`.
    pub fn with_min_tcb(mut self, min_tcb: TcbVersion) -> SnpVerifier {
        self.min_tcb = min_tcb;
        self
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
            return Err(format!("SnpVerifier handles SevSnp only, got {kind:?}"));
        }
        if report_bytes.len() < REPORT_LEN {
            return Err(format!(
                "SNP proof too short: {} bytes (need >= {REPORT_LEN} report [+ VCEK DER])",
                report_bytes.len()
            ));
        }
        let report = SnpReport::parse(&report_bytes[..REPORT_LEN])?;
        let vcek_der = &report_bytes[REPORT_LEN..];

        // Fail closed BEFORE extracting claims if no pinned roots are installed.
        let trust = self.trust.as_ref().ok_or(
            "SNP verifier fail-closed: no pinned AMD roots (ARK/ASK) installed — call with_pinned_roots",
        )?;

        let vcek_vk = verify_snp_cert_chain(vcek_der, trust)?;
        verify_snp_signature(&report, &vcek_vk)?;

        Ok(TeeReportClaims {
            measurement: report.folded_measurement(),
            report_data: report.report_data_32(),
            tcb_ok: report.reported_tcb.meets(&self.min_tcb),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use p384::ecdsa::signature::Signer;
    use p384::ecdsa::SigningKey;

    /// A well-formed synthetic report (fixed layout) with fillable field regions.
    fn synthetic_report() -> Vec<u8> {
        let mut r = vec![0u8; REPORT_LEN];
        // VERSION = 2
        r[OFF_VERSION] = 2;
        // SIGNATURE_ALGO = 1 (ECDSA-P384/SHA-384)
        r[OFF_SIGNATURE_ALGO] = 1;
        // GUEST_SVN = 7
        r[OFF_GUEST_SVN] = 7;
        // CURRENT_TCB / REPORTED_TCB: bootloader=3, tee=1, snp=8, microcode=72
        for off in [OFF_CURRENT_TCB, OFF_REPORTED_TCB] {
            r[off] = 3; // bootloader
            r[off + 1] = 1; // tee
            r[off + 6] = 8; // snp
            r[off + 7] = 72; // microcode
        }
        // REPORT_DATA: 0x00,0x01,...,0x3F
        for i in 0..REPORT_DATA_LEN {
            r[OFF_REPORT_DATA + i] = i as u8;
        }
        // MEASUREMENT: 0xA0 repeated
        for i in 0..MEASUREMENT_LEN {
            r[OFF_MEASUREMENT + i] = 0xA0;
        }
        r
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

    #[test]
    fn parse_and_field_extraction() {
        let bytes = synthetic_report();
        let rep = SnpReport::parse(&bytes).expect("parse");
        assert_eq!(rep.version, 2);
        assert_eq!(rep.sig_algo, SIG_ALGO_ECDSA_P384_SHA384);
        assert_eq!(rep.guest_svn, 7);
        assert_eq!(
            rep.reported_tcb,
            TcbVersion {
                bootloader: 3,
                tee: 1,
                snp: 8,
                microcode: 72
            }
        );
        // report_data first 32 bytes = 0x00..0x1F
        let rd = rep.report_data_32();
        assert_eq!(rd[0], 0x00);
        assert_eq!(rd[31], 0x1F);
        // folded measurement = SHA-256 of the 48 measurement bytes
        let mut h = Sha256::new();
        h.update([0xA0u8; MEASUREMENT_LEN]);
        let expect: [u8; 32] = h.finalize().into();
        assert_eq!(rep.folded_measurement(), expect);
    }

    #[test]
    fn wrong_length_and_version_rejected() {
        assert!(SnpReport::parse(&[0u8; 100]).is_err());
        let mut bytes = synthetic_report();
        bytes[OFF_VERSION] = 9; // unknown version
        assert!(SnpReport::parse(&bytes).is_err());
    }

    #[test]
    fn body_signature_roundtrips_with_real_p384() {
        let sk = SigningKey::from_slice(&[7u8; 48]).expect("signing key");
        let vk = *sk.verifying_key();
        let mut bytes = synthetic_report();
        let rep = SnpReport::parse(&bytes).unwrap();
        let sig: Signature = sk.sign(rep.signed_body());
        embed_signature(&mut bytes, &sig);
        let rep = SnpReport::parse(&bytes).unwrap();
        // Genuine signature verifies.
        verify_snp_signature(&rep, &vk).expect("valid signature");
        // Tamper one body byte → verification fails.
        let mut tampered = bytes.clone();
        tampered[OFF_MEASUREMENT] ^= 0xFF;
        let rep2 = SnpReport::parse(&tampered).unwrap();
        assert!(verify_snp_signature(&rep2, &vk).is_err());
    }

    #[test]
    fn wrong_sig_algo_rejected() {
        let sk = SigningKey::from_slice(&[9u8; 48]).unwrap();
        let vk = *sk.verifying_key();
        let mut bytes = synthetic_report();
        bytes[OFF_SIGNATURE_ALGO] = 2; // not ECDSA-P384/SHA-384
        let rep = SnpReport::parse(&bytes).unwrap();
        assert!(verify_snp_signature(&rep, &vk).is_err());
    }

    #[test]
    fn fail_closed_without_pinned_roots() {
        let bytes = synthetic_report();
        let v = SnpVerifier::new();
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
        assert!(v.verify_report(TeeQuoteKind::SevSnp, &[0u8; 100]).is_err());
    }

    #[test]
    fn missing_vcek_fails_chain_seam() {
        // With pinned roots but no appended VCEK, the chain seam rejects (fail-closed).
        let bytes = synthetic_report();
        let v = SnpVerifier::with_pinned_roots(vec![0u8; 4], vec![0u8; 4]);
        let err = v
            .verify_report(TeeQuoteKind::SevSnp, &bytes)
            .expect_err("no VCEK");
        assert!(
            err.contains("VCEK") || err.contains("ARK"),
            "unexpected: {err}"
        );
    }
}

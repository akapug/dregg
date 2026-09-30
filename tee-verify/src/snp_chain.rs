//! AMD SEV-SNP certificate-chain trust — the `dregg_cell`-free core of the SNP
//! verifier ([`crate::snp::SnpVerifier`]).
//!
//! This module holds everything needed to anchor a SEV-SNP report to the **real AMD
//! root chain** — the pinned roots, the RSA-PSS link primitive, and the
//! `VCEK ← ASK ← ARK` chain verify — with no dependency on `dregg-cell` (hence none on
//! `dregg-circuit`). That separation lets the chain logic be built and tested standalone
//! (see `tee-verify/tests/`-adjacent standalone harness) even when a sibling crate in the
//! workspace is red.
//!
//! ## Pinned roots (provenance)
//!
//! The [`SnpProduct`] roots embedded below are the AMD **Key Distribution Service (KDS)**
//! `cert_chain` responses, fetched verbatim on **2026-07-13** from
//! `https://kdsintf.amd.com/vcek/v1/<Product>/cert_chain`. Each file is the KDS response
//! byte-for-byte: two PEM `CERTIFICATE` blocks, **ASK first** (the SEV signing key,
//! `CN=SEV-<Product>`) then **ARK** (the self-signed root, `CN=ARK-<Product>`). Both are
//! RSA-4096 signed with RSASSA-PSS / MGF1-SHA-384. Independently checked at pin time with
//! OpenSSL: each ARK is self-signed (`openssl verify` OK) and each ASK verifies under its
//! ARK. ARK SHA-256 fingerprints (the trust anchors):
//!
//! - Milan ARK: `69D063B45344D26A2E94E1F4210DE49EF555308287D4C174445C95639A540BCD`
//! - Genoa ARK: `4C6598D19C18719C5DFD4A7D335F674E5BFE1D8F800CEA2CF270C10D103DB2F1`
//! - Turin ARK: `1F084161A44BB6D93778A904877D4819CAFA5D05EF4193B2DED9DD9C73DD3F6A`
//!
//! These are chip-family constants (they change only when AMD rotates a product root),
//! so pinning them is exactly analogous to how [`crate`] pins the AWS Nitro root G1.

use p384::ecdsa::VerifyingKey;
use x509_parser::prelude::*;

/// The `id-RSASSA-PSS` signature-algorithm OID (`1.2.840.113549.1.1.10`) — how AMD's ARK
/// and ASK sign (RSA-4096, MGF1-SHA-384, salt 48). `x509-parser`'s `verify_signature`
/// supports only PKCS#1 v1.5 / ECDSA / Ed25519 (see its `verify.rs`), so a chain link
/// signed with this OID is routed to [`verify_rsa_pss_sha384`] instead.
const RSASSA_PSS_OID: &str = "1.2.840.113549.1.1.10";

/// Verify an **RSASSA-PSS / SHA-384** signature (the AMD ARK/ASK certificate-link
/// algorithm) with the `rsa` crate — the maintained impl `x509-parser` lacks. `issuer_spki`
/// is the issuer's `SubjectPublicKeyInfo.subjectPublicKey` bytes (a DER `RSAPublicKey`,
/// PKCS#1); `message` is the signed TBS DER; `signature` is the raw signature. Uses the
/// SHA-384 salt length (48 = digest output size, which `VerifyingKey::new` selects) — the
/// AMD ARK/ASK PSS parameter.
pub fn verify_rsa_pss_sha384(
    issuer_spki: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), String> {
    use rsa::pkcs1::DecodeRsaPublicKey;
    use rsa::pss::{Signature as PssSignature, VerifyingKey};
    use rsa::signature::Verifier;
    use sha2::Sha384;

    let pk = rsa::RsaPublicKey::from_pkcs1_der(issuer_spki)
        .map_err(|e| format!("issuer RSA public key (PKCS#1) decode: {e}"))?;
    let vk = VerifyingKey::<Sha384>::new(pk);
    let sig =
        PssSignature::try_from(signature).map_err(|e| format!("PSS signature decode: {e}"))?;
    vk.verify(message, &sig)
        .map_err(|e| format!("RSA-PSS-SHA384 signature verify FAILED: {e}"))
}

/// Verify one certificate-chain link: `child`'s signature under `issuer`'s public key,
/// dispatching on `child`'s signature algorithm. AMD's `id-RSASSA-PSS` ARK/ASK links go to
/// [`verify_rsa_pss_sha384`] (the `rsa` crate); everything else (the ECDSA-P384 VCEK link,
/// and the ECDSA self-PKI used in tests) goes through `x509-parser`'s `verify_signature`.
/// Either arm fails **closed** — an unsupported algorithm or a bad signature is an `Err`.
pub fn verify_cert_link(
    child: &X509Certificate<'_>,
    issuer: &X509Certificate<'_>,
) -> Result<(), String> {
    if child.signature_algorithm.algorithm.to_id_string() == RSASSA_PSS_OID {
        verify_rsa_pss_sha384(
            issuer.public_key().subject_public_key.data.as_ref(),
            child.tbs_certificate.as_ref(),
            child.signature_value.data.as_ref(),
        )
    } else {
        child
            .verify_signature(Some(issuer.public_key()))
            .map_err(|e| format!("chain link signature: {e:?}"))
    }
}

/// A parsed AMD SEV-SNP `TCB_VERSION`: the four security patch levels every product
/// carries, plus Turin's `FMC` level (always 0 on Milan/Genoa, which have no FMC).
///
/// The 8-byte wire layout differs by product (SEV-SNP ABI spec, `TCB_VERSION`; read
/// against virtee `sev` 8.0.0 `firmware/host/types/snp.rs`):
///
/// | byte | Milan / Genoa | Turin      |
/// |------|---------------|------------|
/// | 0    | BOOT_LOADER   | FMC        |
/// | 1    | TEE           | BOOT_LOADER|
/// | 2    | reserved      | TEE        |
/// | 3    | reserved      | SNP        |
/// | 4–5  | reserved      | reserved   |
/// | 6    | SNP           | reserved   |
/// | 7    | MICROCODE     | MICROCODE  |
///
/// so it is only ever decoded against a known [`SnpProduct`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TcbVersion {
    pub fmc: u8,
    pub bootloader: u8,
    pub tee: u8,
    pub snp: u8,
    pub microcode: u8,
}

impl TcbVersion {
    /// Decode a report's 8-byte little-endian `TCB_VERSION` under `product`'s layout.
    pub fn from_report_bytes(b: [u8; 8], product: SnpProduct) -> TcbVersion {
        match product {
            SnpProduct::Milan | SnpProduct::Genoa => TcbVersion {
                fmc: 0,
                bootloader: b[0],
                tee: b[1],
                snp: b[6],
                microcode: b[7],
            },
            SnpProduct::Turin => TcbVersion {
                fmc: b[0],
                bootloader: b[1],
                tee: b[2],
                snp: b[3],
                microcode: b[7],
            },
        }
    }

    /// Encode under `product`'s layout (reserved bytes zero). The inverse of
    /// [`TcbVersion::from_report_bytes`] on every value that product can represent.
    pub fn to_report_bytes(&self, product: SnpProduct) -> [u8; 8] {
        let mut b = [0u8; 8];
        match product {
            SnpProduct::Milan | SnpProduct::Genoa => {
                b[0] = self.bootloader;
                b[1] = self.tee;
                b[6] = self.snp;
                b[7] = self.microcode;
            }
            SnpProduct::Turin => {
                b[0] = self.fmc;
                b[1] = self.bootloader;
                b[2] = self.tee;
                b[3] = self.snp;
                b[7] = self.microcode;
            }
        }
        b
    }

    /// Every component is at least the pinned minimum (a down-level rung fails).
    pub fn meets(&self, min: &TcbVersion) -> bool {
        self.fmc >= min.fmc
            && self.bootloader >= min.bootloader
            && self.tee >= min.tee
            && self.snp >= min.snp
            && self.microcode >= min.microcode
    }
}

// VCEK X.509 extensions, under AMD's private-enterprise arc 1.3.6.1.4.1.3704. Source: AMD
// "Versioned Chip Endorsement Key (VCEK) Certificate and KDS Interface Specification"
// (pub. 57230), the VCEK extensions table; the OID values and the value encodings below
// were read against virtee `snpguest` 0.10.0 `src/verify.rs` (`SnpOid`, `check_cert_bytes`)
// rather than recalled. Each SPL is a DER INTEGER; hwID is a DER OCTET STRING of 64 bytes
// (also on Turin), and very old VCEKs carry the 64 raw bytes without the OCTET STRING
// wrapper.
/// `blSPL` — the BOOT_LOADER security patch level the VCEK was derived at.
pub const OID_VCEK_BL_SPL: &str = "1.3.6.1.4.1.3704.1.3.1";
/// `teeSPL` — the TEE (PSP OS) security patch level.
pub const OID_VCEK_TEE_SPL: &str = "1.3.6.1.4.1.3704.1.3.2";
/// `snpSPL` — the SNP firmware security patch level.
pub const OID_VCEK_SNP_SPL: &str = "1.3.6.1.4.1.3704.1.3.3";
/// `ucodeSPL` — the microcode security patch level.
pub const OID_VCEK_UCODE_SPL: &str = "1.3.6.1.4.1.3704.1.3.8";
/// `fmcSPL` — Turin's FMC security patch level (absent on Milan/Genoa).
pub const OID_VCEK_FMC_SPL: &str = "1.3.6.1.4.1.3704.1.3.9";
/// `hwID` — the 64-byte chip identifier; equals the report's `CHIP_ID` for the chip
/// whose VCEK this is.
pub const OID_VCEK_HW_ID: &str = "1.3.6.1.4.1.3704.1.4";

/// Length of the `hwID` extension value and of the report's `CHIP_ID`.
pub const HW_ID_LEN: usize = 64;

/// Why the VCEK ← ASK ← ARK trust path refused. Every variant is a refusal; each names a
/// distinct gate so a caller (and a test) can tell which one fired.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SnpChainError {
    /// No VCEK DER followed the 1184-byte report.
    NoVcek,
    /// A certificate or CRL did not parse.
    Parse { what: &'static str, detail: String },
    /// A certificate is outside its validity window at wall-clock now.
    NotValidNow { cert: &'static str },
    /// A chain link's signature did not verify.
    LinkSignature { link: &'static str, detail: String },
    /// The VCEK's subject key is not a P-384 point.
    VcekKey(String),
    /// A required AMD VCEK extension is absent — the certificate does not say which TCB
    /// or chip it endorses, so it corroborates nothing (F1).
    VcekExtensionMissing { name: &'static str },
    /// An AMD VCEK extension occurs more than once.
    VcekExtensionDuplicate { name: &'static str },
    /// An AMD VCEK extension value is not the encoding the AMD spec gives it.
    VcekExtensionMalformed { name: &'static str, detail: String },
    /// A configured CRL is issued by neither the pinned ARK nor the pinned ASK.
    CrlIssuerUnknown,
    /// A configured CRL's signature does not verify under its issuer (F3).
    CrlSignature(String),
    /// A configured CRL is not current: `thisUpdate` in the future, or `nextUpdate`
    /// absent or past. A stale revocation list cannot vouch that nothing was revoked since.
    CrlNotCurrent(String),
    /// A certificate on the path appears on a configured, verified, current CRL (F3).
    Revoked { cert: &'static str },
}

impl std::fmt::Display for SnpChainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SnpChainError::NoVcek => {
                write!(f, "no VCEK certificate appended to the SNP report bytes")
            }
            SnpChainError::Parse { what, detail } => write!(f, "{what} parse: {detail}"),
            SnpChainError::NotValidNow { cert } => {
                write!(f, "{cert} certificate is not valid now")
            }
            SnpChainError::LinkSignature { link, detail } => {
                write!(f, "{link} signature: {detail}")
            }
            SnpChainError::VcekKey(e) => write!(f, "VCEK P-384 key: {e}"),
            SnpChainError::VcekExtensionMissing { name } => {
                write!(f, "VCEK certificate lacks the AMD {name} extension")
            }
            SnpChainError::VcekExtensionDuplicate { name } => {
                write!(f, "VCEK certificate carries the AMD {name} extension twice")
            }
            SnpChainError::VcekExtensionMalformed { name, detail } => {
                write!(f, "VCEK AMD {name} extension malformed: {detail}")
            }
            SnpChainError::CrlIssuerUnknown => {
                write!(
                    f,
                    "SNP CRL issuer is neither the pinned ARK nor the pinned ASK"
                )
            }
            SnpChainError::CrlSignature(e) => write!(f, "SNP CRL signature: {e}"),
            SnpChainError::CrlNotCurrent(e) => write!(f, "SNP CRL not current: {e}"),
            SnpChainError::Revoked { cert } => {
                write!(f, "{cert} certificate is REVOKED by a configured AMD CRL")
            }
        }
    }
}

impl std::error::Error for SnpChainError {}

/// The operator-pinned AMD roots for ONE product line, plus any revocation lists the
/// operator supplies. `ark_der` is the self-signed AMD Root Key; `ask_der` is the AMD SEV
/// Signing Key (intermediate, signed by ARK). These are chip-family constants fetched once
/// from the AMD KDS and pinned — the per-chip VCEK is presented alongside each report.
///
/// `product` is part of the trust, not a hint: it fixes how a report's `TCB_VERSION` bytes
/// decode (Turin moved the fields) and which VCEK extensions must be present.
///
/// `crls` are DER X.509 CRLs (AMD KDS serves the ARK-issued one at
/// `https://kdsintf.amd.com/vcek/v1/<Product>/crl`; see [`amd_kds_crl_url`]). Nothing here
/// fetches: the operator supplies them. When any is configured, every one must be issued by
/// the pinned ARK or ASK, verify under it, and be current, or the chain refuses; the ASK
/// is refused if an ARK-issued CRL lists its serial, and the VCEK if an ASK-issued one does.
#[derive(Debug, Clone)]
pub struct SnpTrust {
    pub ark_der: Vec<u8>,
    pub ask_der: Vec<u8>,
    pub product: SnpProduct,
    pub crls: Vec<Vec<u8>>,
}

/// Decode a single PEM `CERTIFICATE` block to its DER bytes. Only the first block is
/// read; a non-`CERTIFICATE` label is an error (fail-closed on malformed input).
fn pem_cert_to_der(pem: &str, what: &str) -> Result<Vec<u8>, String> {
    let (_, block) = x509_parser::pem::parse_x509_pem(pem.as_bytes())
        .map_err(|e| format!("{what} PEM parse: {e}"))?;
    if block.label != "CERTIFICATE" {
        return Err(format!(
            "{what} PEM label is {:?}, expected CERTIFICATE",
            block.label
        ));
    }
    Ok(block.contents)
}

/// The AMD **Key Distribution Service (KDS)** endpoint that serves the ASK+ARK PEM chain
/// for a SEV product line (`"Milan"`, `"Genoa"`, …). A GET returns the ASK (SEV
/// intermediate) followed by the self-signed ARK (SEV root), both PEM `CERTIFICATE`
/// blocks. Fetch this once per chip family, split the two blocks, and pin them via
/// [`SnpTrust::from_kds_cert_chain`]. The matching per-chip **VCEK** is fetched from
/// `https://kdsintf.amd.com/vcek/v1/{product}/{hwid}?blSPL=..&teeSPL=..&snpSPL=..&ucodeSPL=..`
/// and rides appended to each report (`report(1184) ‖ vcek_der`). No fetch happens here —
/// this only names the source URL so an operator (or a fetch tool outside the TCB) can
/// retrieve the roots and install them.
pub fn amd_kds_cert_chain_url(product: &str) -> String {
    format!("https://kdsintf.amd.com/vcek/v1/{product}/cert_chain")
}

/// The AMD KDS endpoint serving the ARK-issued DER CRL for a product line. No fetch
/// happens here; install the bytes with [`SnpTrust::with_crl`].
pub fn amd_kds_crl_url(product: &str) -> String {
    format!("https://kdsintf.amd.com/vcek/v1/{product}/crl")
}

/// A pinned AMD SEV-SNP product line. Each variant carries the KDS `cert_chain` embedded
/// below (fetched 2026-07-13 — see the module docs for provenance + fingerprints).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SnpProduct {
    /// 3rd-gen EPYC (Zen 3).
    Milan,
    /// 4th-gen EPYC (Zen 4).
    Genoa,
    /// 5th-gen EPYC (Zen 5).
    Turin,
}

/// AMD KDS `cert_chain` PEM (ASK then ARK), fetched verbatim 2026-07-13 from
/// `https://kdsintf.amd.com/vcek/v1/Milan/cert_chain`.
const AMD_MILAN_CERT_CHAIN_PEM: &str = include_str!("amd_milan_cert_chain.pem");
/// AMD KDS `cert_chain` PEM (ASK then ARK), fetched verbatim 2026-07-13 from
/// `https://kdsintf.amd.com/vcek/v1/Genoa/cert_chain`.
const AMD_GENOA_CERT_CHAIN_PEM: &str = include_str!("amd_genoa_cert_chain.pem");
/// AMD KDS `cert_chain` PEM (ASK then ARK), fetched verbatim 2026-07-13 from
/// `https://kdsintf.amd.com/vcek/v1/Turin/cert_chain`.
const AMD_TURIN_CERT_CHAIN_PEM: &str = include_str!("amd_turin_cert_chain.pem");

impl SnpProduct {
    /// The product name as AMD KDS spells it in URLs.
    pub fn name(self) -> &'static str {
        match self {
            SnpProduct::Milan => "Milan",
            SnpProduct::Genoa => "Genoa",
            SnpProduct::Turin => "Turin",
        }
    }

    /// The embedded KDS `cert_chain` PEM (ASK then ARK) for this product.
    pub fn cert_chain_pem(self) -> &'static str {
        match self {
            SnpProduct::Milan => AMD_MILAN_CERT_CHAIN_PEM,
            SnpProduct::Genoa => AMD_GENOA_CERT_CHAIN_PEM,
            SnpProduct::Turin => AMD_TURIN_CERT_CHAIN_PEM,
        }
    }

    /// The KDS `cert_chain` URL this product's roots were pinned from.
    pub fn cert_chain_url(self) -> String {
        amd_kds_cert_chain_url(self.name())
    }

    /// Whether this product's TCB carries an FMC level (and its VCEK an `fmcSPL`).
    pub fn has_fmc(self) -> bool {
        matches!(self, SnpProduct::Turin)
    }
}

impl SnpTrust {
    /// Build pinned roots from operator-provided PEM: the self-signed AMD **ARK** (SEV
    /// root) and the **ASK** (SEV intermediate) for `product`. Each argument must contain a
    /// single PEM `CERTIFICATE` block; the DER is extracted and stored for chain
    /// verification.
    ///
    /// The real certificates come from the AMD KDS — see [`amd_kds_cert_chain_url`]. The
    /// `cert_chain` endpoint returns ASK then ARK; split the two blocks and pass the ARK
    /// block as `ark_pem` and the ASK block as `ask_pem`. Prefer
    /// [`SnpTrust::from_kds_cert_chain`] to avoid splitting by hand.
    pub fn from_pem(ark_pem: &str, ask_pem: &str, product: SnpProduct) -> Result<SnpTrust, String> {
        Ok(SnpTrust {
            ark_der: pem_cert_to_der(ark_pem, "ARK")?,
            ask_der: pem_cert_to_der(ask_pem, "ASK")?,
            product,
            crls: Vec::new(),
        })
    }

    /// Build pinned roots from a KDS `cert_chain` response verbatim — the two-block PEM
    /// **ASK then ARK** (the order AMD's `/vcek/v1/<Product>/cert_chain` returns). Exactly
    /// two `CERTIFICATE` blocks are required; the first is the ASK, the second the ARK.
    /// Fail-closed: a wrong block count or a non-`CERTIFICATE` label is an `Err`.
    pub fn from_kds_cert_chain(chain_pem: &str, product: SnpProduct) -> Result<SnpTrust, String> {
        let mut ders: Vec<Vec<u8>> = Vec::new();
        for block in x509_parser::pem::Pem::iter_from_buffer(chain_pem.as_bytes()) {
            let block = block.map_err(|e| format!("KDS cert_chain PEM parse: {e}"))?;
            if block.label != "CERTIFICATE" {
                return Err(format!(
                    "KDS cert_chain block label is {:?}, expected CERTIFICATE",
                    block.label
                ));
            }
            ders.push(block.contents);
        }
        if ders.len() != 2 {
            return Err(format!(
                "KDS cert_chain must hold exactly 2 certs (ASK then ARK), got {}",
                ders.len()
            ));
        }
        let ark_der = ders.pop().expect("len==2"); // second block = ARK (self-signed root)
        let ask_der = ders.pop().expect("len==2"); // first block  = ASK (SEV intermediate)
        Ok(SnpTrust {
            ark_der,
            ask_der,
            product,
            crls: Vec::new(),
        })
    }

    /// The pinned AMD roots for a SEV-SNP product line — the real ARK/ASK embedded from
    /// the AMD KDS (see the module docs for provenance). This is the anchored trust the
    /// verifier is built with in production.
    pub fn for_product(product: SnpProduct) -> Result<SnpTrust, String> {
        SnpTrust::from_kds_cert_chain(product.cert_chain_pem(), product)
    }

    /// Add an operator-supplied DER CRL (e.g. the KDS response at [`amd_kds_crl_url`]).
    /// Once any CRL is configured, the chain verify refuses unless every configured CRL
    /// is issued by the pinned ARK/ASK, verifies, and is current.
    pub fn with_crl(mut self, crl_der: Vec<u8>) -> SnpTrust {
        self.crls.push(crl_der);
        self
    }
}

/// What a verified VCEK certificate endorses: its P-384 key, and — from the AMD
/// extensions — the TCB it was derived at and the chip it belongs to. A report signed by
/// this key is only as trustworthy as these values; the report's own `REPORTED_TCB` and
/// `CHIP_ID` are claims the key-holder chose, so the caller must require they equal these.
#[derive(Debug, Clone)]
pub struct VcekEndorsement {
    pub key: VerifyingKey,
    pub tcb: TcbVersion,
    pub hw_id: [u8; HW_ID_LEN],
}

/// Read one DER TLV with a single-byte tag: `(tag, contents, rest)`. Definite lengths only
/// (DER), minimal long-form lengths up to 4 bytes.
fn der_tlv(i: &[u8]) -> Result<(u8, &[u8], &[u8]), String> {
    if i.len() < 2 {
        return Err("truncated DER header".into());
    }
    let tag = i[0];
    let (len, hdr) = match i[1] {
        n if n < 0x80 => (n as usize, 2usize),
        0x80 => return Err("indefinite length is not DER".into()),
        n => {
            let k = (n & 0x7f) as usize;
            if k > 4 || i.len() < 2 + k {
                return Err("bad DER long-form length".into());
            }
            let mut len = 0usize;
            for &b in &i[2..2 + k] {
                len = (len << 8) | b as usize;
            }
            if len < 0x80 || i[2] == 0 {
                return Err("non-minimal DER length".into());
            }
            (len, 2 + k)
        }
    };
    let end = hdr.checked_add(len).ok_or("DER length overflow")?;
    if i.len() < end {
        return Err("DER contents truncated".into());
    }
    Ok((tag, &i[hdr..end], &i[end..]))
}

/// Decode an SPL extension value: exactly one DER INTEGER, non-negative, minimal, ≤ 255.
fn decode_spl(name: &'static str, v: &[u8]) -> Result<u8, SnpChainError> {
    let bad = |detail: String| SnpChainError::VcekExtensionMalformed { name, detail };
    let (tag, c, rest) = der_tlv(v).map_err(bad)?;
    if tag != 0x02 || !rest.is_empty() {
        return Err(bad(format!("expected a lone DER INTEGER, tag {tag:#04x}")));
    }
    match c {
        [x] if *x < 0x80 => Ok(*x),
        [0x00, x] if *x >= 0x80 => Ok(*x),
        _ => Err(bad(format!(
            "INTEGER is not a minimal 0..=255 value: {c:02x?}"
        ))),
    }
}

/// Decode the hwID value: a DER OCTET STRING of 64 bytes, or (legacy VCEKs) the 64 raw
/// bytes. The two are told apart by total length (66 vs 64), never by guessing at a tag.
fn decode_hw_id(v: &[u8]) -> Result<[u8; HW_ID_LEN], SnpChainError> {
    let name = "hwID";
    let bad = |detail: String| SnpChainError::VcekExtensionMalformed { name, detail };
    let raw: &[u8] = if v.len() == HW_ID_LEN {
        v
    } else {
        let (tag, c, rest) = der_tlv(v).map_err(bad)?;
        if tag != 0x04 || !rest.is_empty() {
            return Err(bad(format!("expected a lone OCTET STRING, tag {tag:#04x}")));
        }
        c
    };
    raw.try_into()
        .map_err(|_| bad(format!("hwID is {} bytes, want {HW_ID_LEN}", raw.len())))
}

/// Parse the AMD extensions off a VCEK certificate. Every extension the product defines is
/// REQUIRED: a VCEK that does not name its TCB and chip corroborates nothing, so absence
/// refuses (the reference tool `snpguest` skips a missing extension; this does not).
fn vcek_extensions(
    vcek: &X509Certificate<'_>,
    product: SnpProduct,
) -> Result<(TcbVersion, [u8; HW_ID_LEN]), SnpChainError> {
    let wanted: &[(&'static str, &'static str)] = &[
        ("blSPL", OID_VCEK_BL_SPL),
        ("teeSPL", OID_VCEK_TEE_SPL),
        ("snpSPL", OID_VCEK_SNP_SPL),
        ("ucodeSPL", OID_VCEK_UCODE_SPL),
        ("fmcSPL", OID_VCEK_FMC_SPL),
        ("hwID", OID_VCEK_HW_ID),
    ];
    let mut found: [Option<&[u8]>; 6] = [None; 6];
    for ext in vcek.extensions() {
        let oid = ext.oid.to_id_string();
        if let Some(k) = wanted.iter().position(|(_, o)| *o == oid) {
            if found[k].is_some() {
                return Err(SnpChainError::VcekExtensionDuplicate { name: wanted[k].0 });
            }
            found[k] = Some(ext.value);
        }
    }
    let get = |k: usize| found[k].ok_or(SnpChainError::VcekExtensionMissing { name: wanted[k].0 });
    let tcb = TcbVersion {
        bootloader: decode_spl("blSPL", get(0)?)?,
        tee: decode_spl("teeSPL", get(1)?)?,
        snp: decode_spl("snpSPL", get(2)?)?,
        microcode: decode_spl("ucodeSPL", get(3)?)?,
        fmc: if product.has_fmc() {
            decode_spl("fmcSPL", get(4)?)?
        } else {
            0
        },
    };
    Ok((tcb, decode_hw_id(get(5)?)?))
}

/// The signed-TBS bytes of a DER `CertificateList` (its first inner element). x509-parser
/// keeps them `pub(crate)`, and the RSA-PSS arm needs them.
fn crl_tbs_der(crl_der: &[u8]) -> Result<&[u8], String> {
    let (tag, outer, _) = der_tlv(crl_der)?;
    if tag != 0x30 {
        return Err("CRL is not a SEQUENCE".into());
    }
    let (tag, _, rest) = der_tlv(outer)?;
    if tag != 0x30 {
        return Err("CRL tbsCertList is not a SEQUENCE".into());
    }
    Ok(&outer[..outer.len() - rest.len()])
}

/// Verify one configured CRL against the pinned ARK/ASK and refuse if it revokes the ASK
/// (ARK-issued CRL) or the VCEK (ASK-issued CRL).
fn check_crl(
    crl_der: &[u8],
    ark: &X509Certificate<'_>,
    ask: &X509Certificate<'_>,
    vcek: &X509Certificate<'_>,
    now: ASN1Time,
) -> Result<(), SnpChainError> {
    let (_, crl) =
        CertificateRevocationList::from_der(crl_der).map_err(|e| SnpChainError::Parse {
            what: "SNP CRL",
            detail: e.to_string(),
        })?;
    let (issuer, subject, subject_name): (
        &X509Certificate<'_>,
        &X509Certificate<'_>,
        &'static str,
    ) = if crl.issuer() == ark.subject() {
        (ark, ask, "ASK")
    } else if crl.issuer() == ask.subject() {
        (ask, vcek, "VCEK")
    } else {
        return Err(SnpChainError::CrlIssuerUnknown);
    };

    if crl.signature_algorithm.algorithm.to_id_string() == RSASSA_PSS_OID {
        let tbs = crl_tbs_der(crl_der).map_err(SnpChainError::CrlSignature)?;
        verify_rsa_pss_sha384(
            issuer.public_key().subject_public_key.data.as_ref(),
            tbs,
            crl.signature_value.data.as_ref(),
        )
        .map_err(SnpChainError::CrlSignature)?;
    } else {
        crl.verify_signature(issuer.public_key())
            .map_err(|e| SnpChainError::CrlSignature(format!("{e:?}")))?;
    }

    if crl.last_update() > now {
        return Err(SnpChainError::CrlNotCurrent(
            "thisUpdate is in the future".into(),
        ));
    }
    match crl.next_update() {
        None => return Err(SnpChainError::CrlNotCurrent("no nextUpdate".into())),
        Some(n) if n < now => {
            return Err(SnpChainError::CrlNotCurrent(format!(
                "nextUpdate {n} has passed"
            )))
        }
        Some(_) => {}
    }

    let serial = subject.serial.clone();
    if crl
        .iter_revoked_certificates()
        .any(|r| r.user_certificate == serial)
    {
        return Err(SnpChainError::Revoked { cert: subject_name });
    }
    Ok(())
}

/// Verify VCEK ← ASK ← pinned-ARK, apply any configured CRLs, and return what the VCEK
/// endorses: its P-384 key plus the TCB and chip id from its AMD extensions.
///
/// Structured like [`crate::verify_cert_chain`]: each link's signature is checked
/// against its issuer's key (via [`verify_cert_link`]) and every cert's validity window is
/// checked at wall-clock now (SNP reports carry no timestamp of their own). AMD's ARK/ASK
/// sign RSA-4096 **PSS** — `x509-parser` cannot verify PSS, so [`verify_cert_link`] routes
/// those links to [`verify_rsa_pss_sha384`] (the `rsa` crate); the ECDSA-P384 VCEK link
/// stays on `x509-parser`. Either way this path fails **closed** (an unsupported signature
/// or a bad one is an `Err`, never a silent accept).
pub fn verify_snp_cert_chain(
    vcek_der: &[u8],
    trust: &SnpTrust,
) -> Result<VcekEndorsement, SnpChainError> {
    if vcek_der.is_empty() {
        return Err(SnpChainError::NoVcek);
    }
    let parse = |what: &'static str, der| {
        X509Certificate::from_der(der)
            .map(|(_, c)| c)
            .map_err(|e| SnpChainError::Parse {
                what,
                detail: e.to_string(),
            })
    };
    let ark = parse("pinned ARK", &trust.ark_der)?;
    let ask = parse("pinned ASK", &trust.ask_der)?;
    let vcek = parse("VCEK", vcek_der)?;

    let now = ASN1Time::now();
    for (name, cert) in [("ARK", &ark), ("ASK", &ask), ("VCEK", &vcek)] {
        if !cert.validity().is_valid_at(now) {
            return Err(SnpChainError::NotValidNow { cert: name });
        }
    }

    // ARK is self-signed (the trust anchor); ASK is signed by ARK; VCEK by ASK. Each link
    // dispatches by signature algorithm (RSA-PSS for the real AMD ARK/ASK, ECDSA otherwise).
    let link = |link: &'static str, r: Result<(), String>| {
        r.map_err(|detail| SnpChainError::LinkSignature { link, detail })
    };
    link("ARK self", verify_cert_link(&ark, &ark))?;
    link("ASK←ARK", verify_cert_link(&ask, &ark))?;
    link("VCEK←ASK", verify_cert_link(&vcek, &ask))?;

    for crl in &trust.crls {
        check_crl(crl, &ark, &ask, &vcek, now)?;
    }

    let (tcb, hw_id) = vcek_extensions(&vcek, trust.product)?;
    let point = vcek.public_key().subject_public_key.data.as_ref();
    let key =
        VerifyingKey::from_sec1_bytes(point).map_err(|e| SnpChainError::VcekKey(e.to_string()))?;
    Ok(VcekEndorsement { key, tcb, hw_id })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The three pinned product roots load, hold exactly ASK+ARK, and each ARK is
    /// self-signed under the **real AMD RSA-PSS-SHA384 link** (`verify_cert_link` routing
    /// `id-RSASSA-PSS` to the `rsa` crate). The ASK verifies under its ARK. This exercises
    /// the real AMD root crypto with NO hardware and NO network at test time — the roots
    /// are embedded.
    #[test]
    fn real_amd_roots_load_and_self_verify() {
        for product in [SnpProduct::Milan, SnpProduct::Genoa, SnpProduct::Turin] {
            let trust = SnpTrust::for_product(product)
                .unwrap_or_else(|e| panic!("{product:?} roots load: {e}"));

            let (_, ark) = X509Certificate::from_der(&trust.ark_der).expect("ARK parse");
            let (_, ask) = X509Certificate::from_der(&trust.ask_der).expect("ASK parse");

            // ARK is self-signed with RSA-PSS-SHA384 (real AMD root crypto).
            verify_cert_link(&ark, &ark)
                .unwrap_or_else(|e| panic!("{product:?} ARK self-signature: {e}"));
            // ASK ← ARK, again the real RSA-PSS-SHA384 link.
            verify_cert_link(&ask, &ark).unwrap_or_else(|e| panic!("{product:?} ASK←ARK: {e}"));

            // The subjects are what AMD names them: ARK-<Product> (self) and SEV-<Product>.
            let ark_cn: Vec<_> = ark.subject().iter_common_name().collect();
            let ask_cn: Vec<_> = ask.subject().iter_common_name().collect();
            assert!(
                ark_cn[0].as_str().unwrap().starts_with("ARK-"),
                "{product:?} ARK CN = {:?}",
                ark_cn[0].as_str()
            );
            assert!(
                ask_cn[0].as_str().unwrap().starts_with("SEV-"),
                "{product:?} ASK CN = {:?}",
                ask_cn[0].as_str()
            );
            // ARK is its own issuer (self-signed root).
            assert_eq!(
                ark.issuer(),
                ark.subject(),
                "{product:?} ARK not self-issued"
            );
            // ASK is issued by the ARK.
            assert_eq!(ask.issuer(), ark.subject(), "{product:?} ASK issuer != ARK");
        }
    }

    /// A **forged / wrong ARK** rejects: swap in a different product's ARK and the real
    /// ASK no longer chains (the RSA-PSS-SHA384 link fails closed). Cross every pair.
    #[test]
    fn wrong_product_ark_rejects_real_ask() {
        let products = [SnpProduct::Milan, SnpProduct::Genoa, SnpProduct::Turin];
        for &p in &products {
            let real = SnpTrust::for_product(p).expect("roots");
            let (_, real_ask) = X509Certificate::from_der(&real.ask_der).expect("ASK parse");
            for &q in &products {
                if p == q {
                    continue;
                }
                let other = SnpTrust::for_product(q).expect("roots");
                let (_, wrong_ark) =
                    X509Certificate::from_der(&other.ark_der).expect("wrong ARK parse");
                assert!(
                    verify_cert_link(&real_ask, &wrong_ark).is_err(),
                    "{p:?} ASK must NOT verify under {q:?} ARK"
                );
            }
        }
    }

    /// A **tampered ARK** rejects: flip a byte in the DER and it no longer parses/verifies
    /// as a self-signed root.
    #[test]
    fn tampered_ark_rejects() {
        let trust = SnpTrust::for_product(SnpProduct::Milan).expect("roots");
        // Corrupt a byte deep in the ARK TBS (not the PEM framing).
        let mut bad = trust.ark_der.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 0xFF;
        match X509Certificate::from_der(&bad) {
            Ok((_, ark)) => assert!(
                verify_cert_link(&ark, &ark).is_err(),
                "tampered ARK must not self-verify"
            ),
            Err(_) => { /* corruption broke DER parse — also fail-closed */ }
        }
    }

    /// A **tampered ASK** rejects under the genuine ARK (the RSA-PSS-SHA384 link catches
    /// the flipped TBS byte).
    #[test]
    fn tampered_ask_rejects_under_real_ark() {
        let trust = SnpTrust::for_product(SnpProduct::Genoa).expect("roots");
        let (_, ark) = X509Certificate::from_der(&trust.ark_der).expect("ARK");
        let mut bad = trust.ask_der.clone();
        let mid = bad.len() / 2;
        bad[mid] ^= 0xFF;
        match X509Certificate::from_der(&bad) {
            Ok((_, ask)) => assert!(
                verify_cert_link(&ask, &ark).is_err(),
                "tampered ASK must not verify under real ARK"
            ),
            Err(_) => {}
        }
    }

    /// `from_kds_cert_chain` requires exactly two CERTIFICATE blocks and pins ARK=second,
    /// ASK=first (KDS order). Round-trips against the embedded Milan chain.
    #[test]
    fn kds_cert_chain_splits_ask_then_ark() {
        let trust = SnpTrust::from_kds_cert_chain(AMD_MILAN_CERT_CHAIN_PEM, SnpProduct::Milan)
            .expect("split");
        let (_, ark) = X509Certificate::from_der(&trust.ark_der).expect("ARK");
        let (_, ask) = X509Certificate::from_der(&trust.ask_der).expect("ASK");
        assert!(ark
            .subject()
            .iter_common_name()
            .next()
            .unwrap()
            .as_str()
            .unwrap()
            .starts_with("ARK-"));
        assert!(ask
            .subject()
            .iter_common_name()
            .next()
            .unwrap()
            .as_str()
            .unwrap()
            .starts_with("SEV-"));
        // A single-block PEM is rejected (fail-closed on wrong count).
        assert!(SnpTrust::from_kds_cert_chain(
            "-----BEGIN CERTIFICATE-----\nMIIB\n-----END CERTIFICATE-----\n",
            SnpProduct::Milan
        )
        .is_err());
    }

    /// `verify_snp_cert_chain` still fail-closes on an empty VCEK even with real pinned
    /// roots (the VCEK is per-chip and rides the report; without it no chain completes).
    #[test]
    fn real_roots_reject_empty_vcek() {
        let trust = SnpTrust::for_product(SnpProduct::Turin).expect("roots");
        assert!(verify_snp_cert_chain(&[], &trust).is_err());
    }

    /// The RSA-PSS-SHA384 link primitive — a genuine PSS-SHA384 signature over a stand-in
    /// TBS verifies; a tampered message, signature, or wrong issuer key is refused. This is
    /// the exact algorithm AMD's ARK/ASK sign with (`x509-parser` cannot do PSS). AMD uses
    /// RSA-4096; the test uses 2048 for keygen speed — identical code path.
    #[test]
    fn rsa_pss_sha384_link_primitive_roundtrips_and_rejects_tamper() {
        use rsa::pkcs1::EncodeRsaPublicKey;
        use rsa::pss::{Signature as PssSignature, SigningKey};
        use rsa::signature::{RandomizedSigner, SignatureEncoding};
        use rsa::RsaPrivateKey;
        use sha2::Sha384;

        let mut rng = rand::thread_rng();
        let sk = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen");
        let spki = sk
            .to_public_key()
            .to_pkcs1_der()
            .expect("pkcs1 der")
            .as_bytes()
            .to_vec();

        let signing = SigningKey::<Sha384>::new(sk);
        let msg = b"a stand-in for a certificate TBS DER (AMD ARK/ASK PSS-SHA384)";
        let sig: PssSignature = signing.sign_with_rng(&mut rng, msg);
        let sig_bytes = sig.to_bytes();

        verify_rsa_pss_sha384(&spki, msg, &sig_bytes).expect("valid PSS link");

        let mut bad_msg = msg.to_vec();
        bad_msg[0] ^= 0xFF;
        assert!(verify_rsa_pss_sha384(&spki, &bad_msg, &sig_bytes).is_err());

        let mut bad_sig = sig_bytes.to_vec();
        let n = bad_sig.len();
        bad_sig[n - 1] ^= 0xFF;
        assert!(verify_rsa_pss_sha384(&spki, msg, &bad_sig).is_err());

        let other = RsaPrivateKey::new(&mut rng, 2048).expect("rsa keygen 2");
        let other_spki = other
            .to_public_key()
            .to_pkcs1_der()
            .unwrap()
            .as_bytes()
            .to_vec();
        assert!(verify_rsa_pss_sha384(&other_spki, msg, &sig_bytes).is_err());
    }

    #[test]
    fn amd_kds_url_names_the_real_source() {
        assert_eq!(
            amd_kds_cert_chain_url("Milan"),
            "https://kdsintf.amd.com/vcek/v1/Milan/cert_chain"
        );
        assert_eq!(
            SnpProduct::Genoa.cert_chain_url(),
            "https://kdsintf.amd.com/vcek/v1/Genoa/cert_chain"
        );
    }

    // Real AMD KDS CRLs, fetched verbatim 2026-09-30 from
    // `https://kdsintf.amd.com/vcek/v1/<Product>/crl` (DER, ARK-issued, RSASSA-PSS/SHA-384).
    // SHA-256: Milan dd68e9e3…d5e6a525, Genoa f242adeb…8ba0cc16, Turin 0699382a…5d4f604b.
    // thisUpdate 2026-09-22, nextUpdate 2026-11-09. The Genoa CRL revokes serial 0x020001
    // (a retired Genoa ASK); the pinned Genoa ASK is 0x020002.
    const AMD_MILAN_CRL_DER: &[u8] = include_bytes!("amd_milan_crl.der");
    const AMD_GENOA_CRL_DER: &[u8] = include_bytes!("amd_genoa_crl.der");
    const AMD_TURIN_CRL_DER: &[u8] = include_bytes!("amd_turin_crl.der");

    /// The real AMD CRLs verify under the real ARKs through the RSA-PSS arm, and none of
    /// them revokes the pinned ASK. The freshness window is deliberately NOT asserted here
    /// (it lapses 2026-11-09); this pins the signature path and the issuer match, which is
    /// what a PSS-only CRL could get wrong.
    #[test]
    fn real_amd_crls_verify_under_real_arks_and_do_not_revoke_pinned_asks() {
        for (product, der) in [
            (SnpProduct::Milan, AMD_MILAN_CRL_DER),
            (SnpProduct::Genoa, AMD_GENOA_CRL_DER),
            (SnpProduct::Turin, AMD_TURIN_CRL_DER),
        ] {
            let trust = SnpTrust::for_product(product).expect("roots");
            let (_, ark) = X509Certificate::from_der(&trust.ark_der).unwrap();
            let (_, ask) = X509Certificate::from_der(&trust.ask_der).unwrap();
            let (_, crl) = CertificateRevocationList::from_der(der).expect("CRL parse");
            assert_eq!(crl.issuer(), ark.subject(), "{product:?} CRL is ARK-issued");
            assert_eq!(
                crl.signature_algorithm.algorithm.to_id_string(),
                RSASSA_PSS_OID
            );
            verify_rsa_pss_sha384(
                ark.public_key().subject_public_key.data.as_ref(),
                crl_tbs_der(der).unwrap(),
                crl.signature_value.data.as_ref(),
            )
            .unwrap_or_else(|e| panic!("{product:?} CRL signature: {e}"));
            assert!(!crl
                .iter_revoked_certificates()
                .any(|r| r.user_certificate == ask.serial));
            // A CRL from another product's ARK does not verify here (wrong key).
            let other = if product == SnpProduct::Milan {
                AMD_GENOA_CRL_DER
            } else {
                AMD_MILAN_CRL_DER
            };
            let (_, ocrl) = CertificateRevocationList::from_der(other).unwrap();
            assert!(verify_rsa_pss_sha384(
                ark.public_key().subject_public_key.data.as_ref(),
                crl_tbs_der(other).unwrap(),
                ocrl.signature_value.data.as_ref(),
            )
            .is_err());
        }
        // The Genoa CRL genuinely lists a revoked ASK serial (0x020001).
        let (_, g) = CertificateRevocationList::from_der(AMD_GENOA_CRL_DER).unwrap();
        let revoked: Vec<_> = g
            .iter_revoked_certificates()
            .map(|r| r.raw_serial().to_vec())
            .collect();
        assert_eq!(revoked, vec![vec![0x02, 0x00, 0x01]]);
    }

    /// A CRL whose TBS byte is flipped no longer verifies under the real ARK.
    #[test]
    fn tampered_real_crl_refuses() {
        let trust = SnpTrust::for_product(SnpProduct::Genoa).expect("roots");
        let (_, ark) = X509Certificate::from_der(&trust.ark_der).unwrap();
        let mut bad = AMD_GENOA_CRL_DER.to_vec();
        let tbs_len = crl_tbs_der(&bad).unwrap().len();
        // Flip a byte inside the TBS (after the outer header, well inside the TBS).
        bad[tbs_len / 2] ^= 0x01;
        assert_ne!(bad.as_slice(), AMD_GENOA_CRL_DER);
        let ok = match CertificateRevocationList::from_der(&bad) {
            Ok((_, crl)) => crl_tbs_der(&bad)
                .map(|tbs| {
                    verify_rsa_pss_sha384(
                        ark.public_key().subject_public_key.data.as_ref(),
                        tbs,
                        crl.signature_value.data.as_ref(),
                    )
                    .is_ok()
                })
                .unwrap_or(false),
            Err(_) => false,
        };
        assert!(!ok, "a tampered CRL must not verify");
    }

    #[test]
    fn spl_and_hwid_decoding_is_strict() {
        assert_eq!(decode_spl("blSPL", &[0x02, 0x01, 0x07]), Ok(7));
        assert_eq!(decode_spl("blSPL", &[0x02, 0x02, 0x00, 0xC8]), Ok(200));
        // Non-minimal, negative, wrong tag, trailing bytes, too wide: all refused.
        for bad in [
            &[0x02, 0x02, 0x00, 0x07][..],
            &[0x02, 0x01, 0x80][..],
            &[0x04, 0x01, 0x07][..],
            &[0x02, 0x01, 0x07, 0x00][..],
            &[0x02, 0x02, 0x01, 0x00][..],
            &[][..],
        ] {
            assert!(
                matches!(
                    decode_spl("blSPL", bad),
                    Err(SnpChainError::VcekExtensionMalformed { name: "blSPL", .. })
                ),
                "{bad:02x?}"
            );
        }
        let id = [0x5Au8; HW_ID_LEN];
        let mut wrapped = vec![0x04, 0x40];
        wrapped.extend_from_slice(&id);
        assert_eq!(decode_hw_id(&wrapped), Ok(id));
        assert_eq!(decode_hw_id(&id), Ok(id)); // legacy raw form
        assert!(decode_hw_id(&wrapped[..40]).is_err());
        let mut short = vec![0x04, 0x08];
        short.extend_from_slice(&id[..8]);
        assert!(decode_hw_id(&short).is_err(), "an 8-byte hwID is refused");
    }

    /// Turin moved the TCB fields; the two layouts round-trip and differ on the same bytes.
    #[test]
    fn tcb_layout_is_per_product() {
        let b = [1u8, 2, 3, 4, 0, 0, 5, 6];
        let mg = TcbVersion::from_report_bytes(b, SnpProduct::Genoa);
        let tu = TcbVersion::from_report_bytes(b, SnpProduct::Turin);
        assert_eq!(
            mg,
            TcbVersion {
                fmc: 0,
                bootloader: 1,
                tee: 2,
                snp: 5,
                microcode: 6
            }
        );
        assert_eq!(
            tu,
            TcbVersion {
                fmc: 1,
                bootloader: 2,
                tee: 3,
                snp: 4,
                microcode: 6
            }
        );
        for p in [SnpProduct::Milan, SnpProduct::Genoa, SnpProduct::Turin] {
            let t = TcbVersion {
                fmc: if p.has_fmc() { 9 } else { 0 },
                bootloader: 1,
                tee: 2,
                snp: 3,
                microcode: 4,
            };
            assert_eq!(TcbVersion::from_report_bytes(t.to_report_bytes(p), p), t);
        }
    }
}

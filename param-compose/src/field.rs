//! Signed-integer <-> BabyBear helpers.
//!
//! The reference composition (`crate::reference`) evaluates in exact `i128` and maps the
//! result through [`fb`]; the AIR evaluates in the field. Since [`fb`] is a ring
//! homomorphism on the range `i128` values reach here, the two agree exactly — that is
//! what lets the reference be a faithful oracle for the AIR's witness.

use dregg_circuit::field::{BABYBEAR_P, BabyBear};

/// Canonical `BabyBear` of a signed integer (`-1` maps to `p-1`).
pub fn fb(x: i128) -> BabyBear {
    let p = BABYBEAR_P as i128;
    BabyBear::new((((x % p) + p) % p) as u32)
}

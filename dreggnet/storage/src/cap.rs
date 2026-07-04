//! `cap` — the capability authorizing a bucket operation.
//!
//! Mirrors the hosting [`PublishCap`]: a holder of a `storage-bucket/<name>` cap
//! may operate (create / put / get / list / delete on) the bucket named `<name>`,
//! and *only* that bucket. The cap binds both the holder and the bucket name — so
//! it cannot be exercised against a different bucket, the operation's
//! cap-attenuation. On a dregg node this is a cap token whose caveats bind the
//! authorized bucket; here it is the in-process stand-in the
//! [`BucketRegistry`](crate::BucketRegistry) gates on.
//!
//! [`PublishCap`]: ../../dreggnet_webapp/hosting/struct.PublishCap.html

use serde::{Deserialize, Serialize};

/// The cap-token prefix a storage capability carries: `storage-bucket/<name>`.
pub const STORAGE_CAP_PREFIX: &str = "storage-bucket/";

/// A capability authorizing operations on one bucket. Bound to the holder and the
/// bucket name (`storage-bucket/<name>`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StorageCap {
    /// The cap holder (becomes the bucket's `owner` on create).
    pub holder: String,
    /// The cap token: `storage-bucket/<name>`.
    pub cap: String,
}

impl StorageCap {
    /// A storage cap for `holder` over the bucket named `name`
    /// (`storage-bucket/<name>`).
    pub fn for_bucket(holder: impl Into<String>, name: &str) -> StorageCap {
        StorageCap {
            holder: holder.into(),
            cap: format!("{STORAGE_CAP_PREFIX}{name}"),
        }
    }

    /// The bucket name this cap authorizes, if it is a well-formed
    /// `storage-bucket/<name>` token (a non-empty name).
    pub fn bucket(&self) -> Option<&str> {
        self.cap
            .strip_prefix(STORAGE_CAP_PREFIX)
            .filter(|n| !n.is_empty())
    }

    /// Whether this cap authorizes operating the bucket `name`.
    pub fn authorizes(&self, name: &str) -> bool {
        self.bucket() == Some(name)
    }
}

/// Whether `name` is a usable bucket name: non-empty, ≤63 chars, `[a-z0-9-]`, not
/// starting/ending with `-`. A bucket name doubles as a clean namespace label (it
/// can address a `<name>.store.example.com`-style endpoint), so it follows the
/// same DNS-label discipline a site name does.
pub fn is_valid_bucket_name(name: &str) -> bool {
    if name.is_empty() || name.len() > 63 {
        return false;
    }
    if name.starts_with('-') || name.ends_with('-') {
        return false;
    }
    name.bytes()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_binds_holder_and_bucket() {
        let c = StorageCap::for_bucket("agent:ember", "reports");
        assert_eq!(c.cap, "storage-bucket/reports");
        assert_eq!(c.bucket(), Some("reports"));
        assert!(c.authorizes("reports"));
        assert!(!c.authorizes("images"));
    }

    #[test]
    fn bucket_name_validation() {
        assert!(is_valid_bucket_name("reports"));
        assert!(is_valid_bucket_name("my-bucket-2"));
        assert!(!is_valid_bucket_name(""));
        assert!(!is_valid_bucket_name("-x"));
        assert!(!is_valid_bucket_name("x-"));
        assert!(!is_valid_bucket_name("Has.Dot"));
        assert!(!is_valid_bucket_name("has space"));
    }
}

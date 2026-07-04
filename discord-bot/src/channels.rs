//! Semi-private per-user DreggNet Cloud channels.
//!
//! A user claims their own Discord channel ([`commands::channel`]). The channel
//! is visibility-gated to the user + the admin (ember): `@everyone` is denied
//! `VIEW_CHANNEL`, while the owner and the admin are allowed to view + post. The
//! channel is recorded in the bot DB bound to the user's dregg cell, and becomes
//! the surface from which the user drives their own confined Hermes
//! ([`crate::hermes_channel`]).
//!
//! ## The "semi-private" posture (best-effort; admin sees all)
//!
//! This is Discord-permission privacy, not cryptographic privacy: it keeps the
//! channel out of `@everyone`'s view, but the guild owner, anyone with
//! `MANAGE_CHANNELS`/`ADMINISTRATOR`, and — by design — the pinned admin can read
//! it. The admin's read access is explicit (an allow overwrite) AND total (the
//! admin webportal monitors every channel's DB-recorded activity and internal
//! state). "Semi-private" names exactly this: private from peers, transparent to
//! the operator.
//!
//! The permission *plan* ([`plan_private_overwrites`]) is a pure function so the
//! gating logic is unit-tested offline; the live Discord `create_channel` call is
//! the only part that needs a token (gated in [`commands::channel`]).

use serenity::all::{PermissionOverwrite, PermissionOverwriteType, Permissions, RoleId, UserId};

/// The permission set a participant (owner / admin) needs to use the channel.
fn participant_allow() -> Permissions {
    Permissions::VIEW_CHANNEL | Permissions::SEND_MESSAGES | Permissions::READ_MESSAGE_HISTORY
}

/// Build the permission overwrites for a semi-private per-user channel.
///
/// * `@everyone` (the role whose id equals the guild id) is DENIED `VIEW_CHANNEL`
///   — the channel does not appear for peers.
/// * the `owner` is ALLOWED to view, post, and read history — it is their surface.
/// * the `admin` (if pinned) is ALLOWED the same — the operator sees all.
///
/// Pure: no Discord client needed, so the gating is unit-testable.
pub fn plan_private_overwrites(
    everyone_role: RoleId,
    owner: UserId,
    admin: Option<UserId>,
) -> Vec<PermissionOverwrite> {
    let mut overwrites = vec![
        // Deny the whole guild.
        PermissionOverwrite {
            allow: Permissions::empty(),
            deny: Permissions::VIEW_CHANNEL,
            kind: PermissionOverwriteType::Role(everyone_role),
        },
        // Allow the owner.
        PermissionOverwrite {
            allow: participant_allow(),
            deny: Permissions::empty(),
            kind: PermissionOverwriteType::Member(owner),
        },
    ];

    // Allow the admin — but never emit a duplicate overwrite if the admin IS the
    // owner (e.g. ember claiming their own channel).
    if let Some(admin) = admin {
        if admin != owner {
            overwrites.push(PermissionOverwrite {
                allow: participant_allow(),
                deny: Permissions::empty(),
                kind: PermissionOverwriteType::Member(admin),
            });
        }
    }

    overwrites
}

/// The channel name for a user's semi-private channel (Discord lowercases +
/// dash-normalizes channel names; we do it ourselves so the stored name matches).
pub fn channel_name_for(discord_id: u64) -> String {
    format!("dregg-{discord_id}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_overwrites_deny_everyone_allow_owner_and_admin() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        let admin = UserId::new(200);

        let ovr = plan_private_overwrites(everyone, owner, Some(admin));
        assert_eq!(ovr.len(), 3, "everyone-deny + owner-allow + admin-allow");

        // @everyone is denied VIEW_CHANNEL and allowed nothing.
        let everyone_ovr = ovr
            .iter()
            .find(|o| matches!(o.kind, PermissionOverwriteType::Role(r) if r == everyone))
            .expect("an everyone overwrite");
        assert!(everyone_ovr.deny.contains(Permissions::VIEW_CHANNEL));
        assert!(everyone_ovr.allow.is_empty());

        // Owner + admin can both view.
        for who in [owner, admin] {
            let m = ovr
                .iter()
                .find(|o| matches!(o.kind, PermissionOverwriteType::Member(u) if u == who))
                .expect("a member overwrite");
            assert!(m.allow.contains(Permissions::VIEW_CHANNEL));
            assert!(m.allow.contains(Permissions::SEND_MESSAGES));
        }
    }

    #[test]
    fn admin_equal_to_owner_is_not_duplicated() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        // ember claims their own channel: admin == owner.
        let ovr = plan_private_overwrites(everyone, owner, Some(owner));
        assert_eq!(ovr.len(), 2, "no duplicate owner/admin overwrite");
    }

    #[test]
    fn no_admin_pinned_still_gates_to_owner() {
        let everyone = RoleId::new(1);
        let owner = UserId::new(100);
        let ovr = plan_private_overwrites(everyone, owner, None);
        assert_eq!(ovr.len(), 2);
    }

    #[test]
    fn channel_name_is_stable() {
        assert_eq!(channel_name_for(42), "dregg-42");
    }
}

//! End-to-end teams/orgs proof: an org with owner+admin+member+viewer; a member
//! creates an org-owned resource; a viewer is refused a write (role-cap teeth);
//! an admin manages members but cannot delete the org; ownership transfers; a
//! non-member cannot see the org's resources (org-scoping teeth); and the role IS
//! a cap attenuation (a role-cap cannot amplify beyond its grant).

use dreggnet_org::cap::authorize;
use dreggnet_org::resource::scope_for_member;
use dreggnet_org::{OrgAuthority, OrgError, Permission, ResourceKind, Role};

/// A seated member: their subject + the role-cap the org minted them.
type Seat = (String, dreggnet_webauth::cred::Credential);

/// Build an org with the four core roles seated, returning the authority plus the
/// (subject, role-cap) of each member. Owner founds; owner invites the rest; each
/// accepts (which mints their role-cap).
fn org_with_team() -> (OrgAuthority, Seat, Seat, Seat, Seat) {
    let owner = "dregg:owner00000000".to_string();
    let admin = "dregg:admin00000000".to_string();
    let member = "dregg:member0000000".to_string();
    let viewer = "dregg:viewer0000000".to_string();

    let mut a = OrgAuthority::found_with_seed([7u8; 32], "Acme Team", owner.clone());
    let owner_cap = a.owner_cap();

    // Owner invites the three others; each accepts and gets their role-cap.
    let inv_admin = a
        .invite(&owner_cap, &owner, admin.clone(), Role::Admin, 100)
        .unwrap();
    let admin_cap = a.accept_invite(&inv_admin, &admin).unwrap();

    let inv_member = a
        .invite(&owner_cap, &owner, member.clone(), Role::Member, 100)
        .unwrap();
    let member_cap = a.accept_invite(&inv_member, &member).unwrap();

    let inv_viewer = a
        .invite(&owner_cap, &owner, viewer.clone(), Role::Viewer, 100)
        .unwrap();
    let viewer_cap = a.accept_invite(&inv_viewer, &viewer).unwrap();

    (
        a,
        (owner, owner_cap),
        (admin, admin_cap),
        (member, member_cap),
        (viewer, viewer_cap),
    )
}

#[test]
fn the_full_org_lifecycle() {
    let (mut a, (owner, owner_cap), (admin, admin_cap), (member, member_cap), (viewer, viewer_cap)) =
        org_with_team();
    let now = 200;

    // --- the team is seated with the four roles ---
    assert_eq!(a.org().members.len(), 4);
    assert_eq!(a.org().role_of(&owner), Some(Role::Owner));
    assert_eq!(a.org().role_of(&admin), Some(Role::Admin));
    assert_eq!(a.org().role_of(&member), Some(Role::Member));
    assert_eq!(a.org().role_of(&viewer), Some(Role::Viewer));

    // --- a member creates a resource → it is ORG-owned ---
    let site = a
        .create_resource(
            &member_cap,
            &member,
            ResourceKind::Site,
            "site_1",
            "Landing",
            now,
        )
        .expect("member may create");
    assert_eq!(
        site.owner(),
        a.org().id,
        "the resource is owned by the org, not the member"
    );
    assert_eq!(
        site.created_by, member,
        "provenance records the acting member"
    );

    // --- a VIEWER is refused a write (role-cap teeth) ---
    let viewer_write = authorize(
        &viewer_cap,
        &a.public(),
        a.id(),
        Permission::ResourceWrite,
        now,
    );
    assert!(viewer_write.is_err(), "a viewer must not be able to write");
    // and the viewer cannot create a resource at all.
    let viewer_create = a.create_resource(&viewer_cap, &viewer, ResourceKind::Site, "x", "x", now);
    assert!(matches!(viewer_create, Err(OrgError::NotAuthorized { .. })));
    // the viewer CAN read (its one permission).
    assert!(
        authorize(
            &viewer_cap,
            &a.public(),
            a.id(),
            Permission::ResourceRead,
            now
        )
        .is_ok()
    );

    // --- an ADMIN manages members but CANNOT delete the org ---
    let newcomer = "dregg:newcomer00000".to_string();
    let inv = a
        .invite(&admin_cap, &admin, newcomer.clone(), Role::Member, now)
        .expect("admin may invite");
    let _newcomer_cap = a.accept_invite(&inv, &newcomer).unwrap();
    assert!(
        a.org().is_member(&newcomer),
        "admin successfully added a member"
    );
    // but admin's cap is refused org:delete...
    assert!(authorize(&admin_cap, &a.public(), a.id(), Permission::OrgDelete, now).is_err());
    // ...and a non-member (a new fresh authority object isn't needed): demonstrate
    // the admin literally cannot delete the org through the typed action either by
    // checking the perm — the delete_org consumes the authority, so check the perm.
    assert!(!Role::Admin.grants(Permission::OrgDelete));

    // --- a member (non-admin) CANNOT manage members ---
    let denied = a.invite(
        &member_cap,
        &member,
        "dregg:nope000000000",
        Role::Member,
        now,
    );
    assert!(
        matches!(denied, Err(OrgError::NotAuthorized { .. })),
        "a member cannot invite"
    );

    // --- ownership TRANSFERS (owner-only) ---
    // an admin cannot transfer ownership...
    let admin_xfer = a.transfer_ownership(&admin_cap, &admin, &admin, now);
    assert!(matches!(admin_xfer, Err(OrgError::NotAuthorized { .. })));
    // ...the owner transfers to the admin.
    let new_owner_cap = a
        .transfer_ownership(&owner_cap, &owner, &admin, now)
        .expect("owner may transfer");
    assert_eq!(a.org().owner, admin, "ownership moved to the admin");
    assert_eq!(a.org().role_of(&admin), Some(Role::Owner));
    assert_eq!(
        a.org().role_of(&owner),
        Some(Role::Admin),
        "old owner demoted to admin"
    );
    // the new owner's cap can now delete the org.
    assert!(
        authorize(
            &new_owner_cap,
            &a.public(),
            a.id(),
            Permission::OrgDelete,
            now
        )
        .is_ok()
    );

    // --- the OLD owner's cap is still just an owner-cap; it has not lost reach as
    //     a credential, but the org now treats them as admin. The new owner can
    //     delete; the typed delete_org succeeds for the new owner. ---
    assert!(
        a.delete_org(&new_owner_cap, now).is_ok(),
        "the new owner deletes the org"
    );
}

#[test]
fn org_scoping_a_non_member_sees_nothing() {
    let (mut a, (_owner, _oc), (_admin, _ac), (member, member_cap), _viewer) = org_with_team();
    let now = 300;

    let r1 = a
        .create_resource(&member_cap, &member, ResourceKind::Site, "s1", "S1", now)
        .unwrap();
    let r2 = a
        .create_resource(&member_cap, &member, ResourceKind::Bucket, "b1", "B1", now)
        .unwrap();
    let resources = vec![r1, r2];

    // a member sees the team's resources.
    let seen = scope_for_member(&resources, a.org(), &member);
    assert_eq!(seen.len(), 2, "a member sees the org's resources");

    // a NON-member sees nothing — the org-scoping read tooth.
    let stranger = "dregg:stranger00000";
    let seen = scope_for_member(&resources, a.org(), stranger);
    assert!(
        seen.is_empty(),
        "a non-member sees none of the org's resources"
    );
    assert!(!resources[0].visible_to(a.org(), stranger));
    assert!(resources[0].visible_to(a.org(), &member));
}

#[test]
fn cross_org_cap_cannot_reach_another_org() {
    // Two independent orgs. A member-cap from org A must not act on org B.
    let mut a = OrgAuthority::found_with_seed([1u8; 32], "Org A", "dregg:ownerA0000000");
    let b = OrgAuthority::found_with_seed([2u8; 32], "Org B", "dregg:ownerB0000000");
    let owner_a = "dregg:ownerA0000000".to_string();
    let oa_cap = a.owner_cap();

    let member_a = "dregg:memberA000000".to_string();
    let inv = a
        .invite(&oa_cap, &owner_a, member_a.clone(), Role::Member, 100)
        .unwrap();
    let cap_a = a.accept_invite(&inv, &member_a).unwrap();

    // cap_a writes in org A...
    assert!(authorize(&cap_a, &a.public(), a.id(), Permission::ResourceWrite, 100).is_ok());
    // ...but is refused against org B (different root key AND different org id).
    assert!(authorize(&cap_a, &b.public(), b.id(), Permission::ResourceWrite, 100).is_err());
}

#[test]
fn accept_invite_cannot_be_redeemed_by_a_stranger() {
    let mut a = OrgAuthority::found_with_seed([9u8; 32], "Org", "dregg:owner000000000");
    let owner = "dregg:owner000000000".to_string();
    let oc = a.owner_cap();

    let invitee = "dregg:invitee000000".to_string();
    let inv = a
        .invite(&oc, &owner, invitee.clone(), Role::Member, 100)
        .unwrap();

    // a stranger cannot redeem someone else's invite.
    let attacker = "dregg:attacker00000";
    assert!(matches!(
        a.accept_invite(&inv, attacker),
        Err(OrgError::InviteMismatch)
    ));
    assert!(!a.org().is_member(attacker));

    // the rightful invitee can.
    assert!(a.accept_invite(&inv, &invitee).is_ok());
    assert!(a.org().is_member(&invitee));
}

#[test]
fn remove_member_and_owner_is_unremovable() {
    let (mut a, (owner, owner_cap), (_admin, _ac), (member, _mc), _viewer) = org_with_team();
    let now = 400;

    // owner removes the member.
    assert!(a.remove_member(&owner_cap, &owner, &member, now).is_ok());
    assert!(!a.org().is_member(&member));

    // the owner cannot be removed (must transfer first).
    assert!(matches!(
        a.remove_member(&owner_cap, &owner, &owner, now),
        Err(OrgError::CannotRemoveOwner)
    ));
}

#[test]
fn membership_audit_trail_is_recorded_in_order() {
    let (a, ..) = org_with_team();
    let events = &a.org().events;
    // founded + 3×(invited, accepted) = 7 events, strictly ordered.
    assert_eq!(events.len(), 7);
    for (i, e) in events.iter().enumerate() {
        assert_eq!(e.seq, i as u64, "events carry a monotone seq");
    }
    assert_eq!(events[0].action, dreggnet_org::MembershipAction::Founded);
}

//! `dreggnet-org` — **teams / organizations (IAM)** for DreggNet.
//!
//! The cloud-readiness gap (`docs/CLOUD-PROVIDER-READINESS.md`): DreggNet
//! identity is **single-wallet only** — a `dga1_` cap-account is the whole
//! subject, and the console scopes "my stuff" by `owner == subject`. Real clouds
//! have **organizations** with **members** and **roles** (AWS Organizations / IAM,
//! GCP projects + IAM, a Vercel/Cloudflare team). This crate adds that — and the
//! elegant part is that it adds **no new authorization primitive**. DreggNet's
//! capability-attenuation lattice (the webauth `dga1_` caveat-chain, whose
//! `attenuate` provably only ever *narrows* authority) **already is** the role
//! mechanism. This crate just makes it legible as orgs + roles.
//!
//! ## How the cap lattice becomes orgs + roles
//!
//! * An [`Org`] is **its own dregg cell** — it has its own minting authority
//!   ([`OrgAuthority`] holds the [`RootKey`](dreggnet_webauth::cred::RootKey)) and
//!   a stable id `org:<16hex>`. The org **owns** resources ([`OrgResource`]):
//!   a resource created in an org context is owned by the *org*, not the acting
//!   member.
//! * **Members** are `dga1_` cap-accounts (subjects) added to the org; each holds
//!   a [`Role`] (`owner` / `admin` / `member` / `billing` / `viewer`).
//! * A role maps to a set of [`Permission`]s, which compiles to an **attenuated
//!   capability** over the org-owner's authority ([`cap::mint_role_cap`]): the
//!   owner grant (`AnyOf(all perms)`, pinned to this org) is `attenuate`d to the
//!   role's perms. So **"admin" = a cap attenuated to manage-but-not-delete-org**;
//!   **"viewer" = a read-only attenuation.** A member acts on org resources by
//!   presenting their role-cap, verified ([`cap::authorize`]) against the org root
//!   key + a context binding `org` (the **scoping** tooth) and `perm` (the
//!   **role-gating** tooth). A viewer-cap simply does not satisfy a `resource:write`
//!   context — the write is *refused*, and by the no-amplify property it cannot be
//!   forged wider (proven in [`cap`]). **The role IS an attenuation of the
//!   lattice — that is the whole design.**
//! * **Invites + membership** ([`OrgAuthority`]): invite a cap-account to a role,
//!   accept (the org mints the member's role-cap), remove, change-role, and
//!   transfer ownership — each a recorded [`MembershipEvent`] turn.
//!
//! ## Named seams (call sites this crate is ready to wire into, NOT yet wired)
//!
//! These are deliberately out of scope here (green-gated, swarm-safe: a disjoint
//! new crate) and named for the integrator:
//!
//! * **console org-switcher** — `dreggnet-console` today renders one subject's
//!   "my stuff" ([`scope`](../dreggnet_console/fn.scope.html) by `owner == subject`).
//!   The seam: a switcher that flips the active context between *personal* and
//!   *each org the subject is a member of*, rendering the org's resources via
//!   [`resource::scope_for_member`] (the org-level twin of console's `scope`) and
//!   showing the member's [`Role`]. The console's `Owned` model lifts directly:
//!   an org-owned resource is visible iff the subject is a member of the owner org.
//! * **webauth org-context** — `dreggnet-webauth`'s forward-auth echoes the verified
//!   subject as `X-Dregg-Subject`. The seam: when a request acts in an org context,
//!   the edge resolves the presented credential as a **role-cap** ([`cap::authorize`]
//!   against the org root key) and echoes `X-Dregg-Org` + `X-Dregg-Role` alongside
//!   the subject, so upstream surfaces (gateway/webapp/control/storage) scope to the
//!   *org* and gate on the *role* exactly as they scope to a subject today. The
//!   per-account guard standing (`guard::governance`) extends per-org the same way.
//! * **receipt chain** — [`MembershipEvent`]s are an in-record typed audit trail;
//!   wiring them into the product-wide `dreggnet-receipt` prev-hash-chained signed
//!   stream (as `guard::governance` does) makes the membership history third-party
//!   `verify_chain`-able.

pub mod cap;
pub mod org;
pub mod resource;
pub mod role;

pub use org::{Invite, Membership, MembershipAction, MembershipEvent, Org, OrgAuthority, OrgError};
pub use resource::{OrgResource, ResourceKind, scope_for_member};
pub use role::{ORG_KEY, PERM_KEY, Permission, Role};

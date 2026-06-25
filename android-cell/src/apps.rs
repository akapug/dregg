//! **The installed-app registry — the install↔launch↔intent (and content) bridge.** The
//! state that makes the [`crate::appfactory`] birth, the [`crate::intentgate`] resolution,
//! and the [`crate::contentgate`] resolution one coherent loop: an app is *installed* (minted
//! as an android-cell from its manifest descriptor), it is *launched* on a runtime, and a
//! live app's outbound intents / `content://` accesses resolve over the **cap-reachable
//! neighborhood of installed apps** — NOT a device-wide `PackageManager`/`ContentResolver`.
//!
//! # The loop, closed
//!
//! `GRAPHIDEOS.md §1` makes installing an app a cap-gated birth and an intent a turn over a
//! cap you hold. Those two are the same fact seen twice: an installed app is reachable as a
//! handler/provider **iff** (a) its manifest *declared* the `<intent-filter>` / `<provider>`
//! AND (b) the resolving cell *holds a cap* to it. The [`InstalledApps`] registry is where
//! both halves meet:
//!
//! - [`InstalledApps::install`] records `(cell, manifest, launch)` and returns the
//!   [`FactoryDescriptor`] the appfactory mints from the manifest — the install IS the
//!   cap-gated birth (the descriptor's `allowed_cap_templates` are EXACTLY the manifest's
//!   declared permissions) AND the registry entry, in one act.
//! - [`InstalledApps::resolver_for`] builds an [`IntentResolver`] for a *launching* cell over
//!   only the installed apps it was granted a cap to (`granted`). Each published
//!   `<intent-filter>` becomes an [`IntentHandler`] named to the publishing app's cell.
//! - [`InstalledApps::content_resolver_for`] does the same for `content://` providers,
//!   building a [`ContentResolver`] over the cap-reachable apps' published authorities.
//!
//! So an app the launching cell holds no cap to is, by construction, NOT a candidate — the
//! no-ambient-`startActivity` / no-ambient-`ContentResolver` property, sourced from the real
//! installed-app set rather than a hand-built handler list.

use std::collections::BTreeSet;

use dregg_cell::FactoryDescriptor;
use dregg_firmament::CellId;

use crate::appfactory::AndroidManifest;
use crate::contentgate::{ContentProvider, ContentResolver, ProviderGrant};
use crate::intentgate::{IntentHandler, IntentResolver};
use crate::runtime::AppLaunch;

/// One installed app — the android-cell minted from a manifest, plus how to launch it.
#[derive(Clone, Debug)]
pub struct InstalledApp {
    /// The android-cell this app was minted as (the handler/provider identity another cell
    /// resolves to).
    pub cell: CellId,
    /// The manifest the cell was born from — the source of its published `<intent-filter>`s
    /// and `<provider>` authorities (and, via the appfactory, its cap-set).
    pub manifest: AndroidManifest,
    /// How the runtime launches this app's program (`am start` component or package).
    pub launch: AppLaunch,
}

/// **The installed-app registry.** The set of android-cells the device has minted, the unit
/// the launch + intent + content loops range over. Holds NO ambient authority — a resolver
/// it builds is always *restricted to a caller-supplied `granted` neighborhood*, so the
/// registry being device-wide does not make resolution device-wide.
#[derive(Default)]
pub struct InstalledApps {
    apps: Vec<InstalledApp>,
}

impl InstalledApps {
    pub fn new() -> Self {
        InstalledApps { apps: Vec::new() }
    }

    /// **INSTALL = THE CAP-GATED BIRTH + THE REGISTRY ENTRY.** Mint `manifest`'s
    /// [`FactoryDescriptor`] (the appfactory birth — its `allowed_cap_templates` are exactly
    /// the manifest's declared permissions) and register the app under `cell` with how to
    /// `launch` it. Returns the descriptor so the install's conferred authority is the same
    /// auditable, content-addressed artifact the appfactory produces.
    pub fn install(
        &mut self,
        cell: CellId,
        manifest: AndroidManifest,
        launch: AppLaunch,
        factory_vk: [u8; 32],
    ) -> FactoryDescriptor {
        let descriptor = manifest.to_factory_descriptor(factory_vk);
        self.apps.push(InstalledApp {
            cell,
            manifest,
            launch,
        });
        descriptor
    }

    /// The installed apps (the device's minted android-cells).
    pub fn apps(&self) -> &[InstalledApp] {
        &self.apps
    }

    /// The installed app minted as `cell`, if any.
    pub fn get(&self, cell: CellId) -> Option<&InstalledApp> {
        self.apps.iter().find(|a| a.cell == cell)
    }

    /// **Build the [`IntentResolver`] for `launching_cell`** over only the installed apps it
    /// holds a cap to (`granted`). Each published `<intent-filter>` becomes an
    /// [`IntentHandler`] named to the publishing app's cell + package label — so an app is a
    /// candidate handler iff its manifest declared the filter AND `launching_cell` holds a cap
    /// to it. This is the install↔intent loop, sourced from the real installed-app set.
    pub fn resolver_for(
        &self,
        launching_cell: CellId,
        granted: &BTreeSet<CellId>,
    ) -> IntentResolver {
        let handlers = self
            .apps
            .iter()
            .filter(|a| granted.contains(&a.cell))
            .flat_map(|a| {
                let cell = a.cell;
                let label = a.manifest.package.clone();
                a.manifest
                    .intent_filters
                    .iter()
                    .cloned()
                    .map(move |filter| IntentHandler::new(cell, label.clone(), filter))
            })
            .collect::<Vec<_>>();
        IntentResolver::new(handlers, Some(launching_cell))
    }

    /// **Build the [`ContentResolver`] for `launching_cell`** over only the installed apps it
    /// holds a cap to (`granted`). Each published `<provider>` authority becomes a
    /// [`ContentProvider`] named to the publishing app's cell. `grant` is the access the
    /// launching cell was handed over those providers (the cap attenuation — a strictly
    /// narrower per-provider grant is the powerbox hand-over). The install↔content loop.
    pub fn content_resolver_for(
        &self,
        launching_cell: CellId,
        granted: &BTreeSet<CellId>,
        grant: ProviderGrant,
    ) -> ContentResolver {
        let providers = self
            .apps
            .iter()
            .filter(|a| granted.contains(&a.cell))
            .flat_map(|a| {
                let cell = a.cell;
                let label = a.manifest.package.clone();
                a.manifest
                    .content_authorities
                    .iter()
                    .cloned()
                    .map(move |authority| {
                        ContentProvider::new(cell, authority, label.clone(), grant)
                    })
            })
            .collect::<Vec<_>>();
        ContentResolver::new(providers, Some(launching_cell))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::appfactory::AndroidPermission;
    use crate::contentgate::{ContentAccess, ContentUri};
    use crate::intentgate::{AndroidIntent, IntentFilter};
    use dregg_firmament::cell_seed;
    use starbridge_web_surface::{AuthRequired, SurfaceCapability};

    fn maps() -> (CellId, AndroidManifest) {
        (
            cell_seed(0x51),
            AndroidManifest::new(
                "com.example.maps",
                [
                    AndroidPermission::Internet,
                    AndroidPermission::AccessFineLocation,
                ],
            )
            .with_intent_filters([IntentFilter::new(["android.intent.action.VIEW"], ["geo"])]),
        )
    }
    fn browser() -> (CellId, AndroidManifest) {
        (
            cell_seed(0x52),
            AndroidManifest::new("com.example.browser", [AndroidPermission::Internet])
                .with_intent_filters([IntentFilter::new(
                    ["android.intent.action.VIEW"],
                    ["http", "https"],
                )]),
        )
    }
    fn contacts() -> (CellId, AndroidManifest) {
        (
            cell_seed(0x53),
            AndroidManifest::new("com.android.contacts", [AndroidPermission::ReadContacts])
                .with_content_authorities(["com.android.contacts"]),
        )
    }

    fn registry() -> InstalledApps {
        let mut apps = InstalledApps::new();
        for (cell, manifest) in [maps(), browser(), contacts()] {
            apps.install(cell, manifest, AppLaunch::Package("pkg".into()), [0x11; 32]);
        }
        apps
    }

    /// Install returns the appfactory descriptor (the cap-gated birth) AND registers the app.
    #[test]
    fn install_is_the_birth_plus_the_registry_entry() {
        let mut apps = InstalledApps::new();
        let (cell, manifest) = maps();
        let desc = apps.install(
            cell,
            manifest,
            AppLaunch::Package("com.example.maps".into()),
            [0x11; 32],
        );
        // Two declared permissions ⟹ exactly two cap templates (the appfactory property).
        assert_eq!(desc.allowed_cap_templates.len(), 2);
        // And the app is now installed.
        assert!(apps.get(cell).is_some());
        assert_eq!(apps.apps().len(), 1);
    }

    /// **THE LOAD-BEARING TEST: the resolver a launching cell gets ranges ONLY over the
    /// installed apps it holds a cap to — an app it was never granted is not a candidate.**
    #[test]
    fn resolver_ranges_only_over_the_granted_neighborhood() {
        let apps = registry();
        let me = cell_seed(9);
        let (maps_cell, _) = maps();
        let (browser_cell, _) = browser();

        // Granted maps only.
        let granted: BTreeSet<CellId> = [maps_cell].into_iter().collect();
        let resolver = apps.resolver_for(me, &granted);
        let surface = SurfaceCapability::root(me, AuthRequired::Either);

        // A geo VIEW resolves to maps (granted + its manifest published the geo filter).
        let geo = AndroidIntent::view("android.intent.action.VIEW", "geo:0,0?q=cafe");
        assert!(resolver.resolve(&surface, &geo).decision.resolved());

        // An https VIEW reaches NOTHING — the browser is installed but NOT granted, so it
        // is not in this cell's neighborhood (no ambient device-wide resolution).
        let web = AndroidIntent::view("android.intent.action.VIEW", "https://example.com");
        assert!(
            resolver
                .resolve(&surface, &web)
                .decision
                .refused_no_handler(),
            "the browser is installed but ungranted — not a candidate"
        );

        // Granting the browser too brings it into the neighborhood.
        let granted2: BTreeSet<CellId> = [maps_cell, browser_cell].into_iter().collect();
        let resolver2 = apps.resolver_for(me, &granted2);
        assert!(resolver2.resolve(&surface, &web).decision.resolved());
    }

    /// **THE FULL LOOP, no device: install → launch → fire intent → route to a cap-reachable
    /// handler on the runtime.** Exercises `launch_installed_app` welding the resolver to the
    /// `CapturedFrameRuntime` as the intent sink (via the `&mut S` impl), proving the launched
    /// app's outbound intent reaches ONLY a granted handler's `am start`.
    #[test]
    fn launch_then_dispatch_routes_to_a_granted_handler_on_the_runtime() {
        use crate::intentgate::AndroidIntentGate;
        use crate::runtime::{CapturedFrameRuntime, launch_installed_app};

        let apps = registry();
        let me = cell_seed(9);
        let (maps_cell, _) = maps();
        let (browser_cell, _) = browser();
        let granted: BTreeSet<CellId> = [maps_cell, browser_cell].into_iter().collect();

        let mut rt = CapturedFrameRuntime::from_screencap_raw(Vec::new());
        // Launch the maps app as `me`; the resolver is built over `me`'s cap-reachable apps.
        let resolver = launch_installed_app(&mut rt, &apps, maps_cell, &granted)
            .expect("the installed maps app launches + yields a resolver");

        // Weld the resolver to the runtime as the intent sink; dispatch a geo VIEW.
        let surface = SurfaceCapability::root(me, AuthRequired::Either);
        {
            let mut gate = AndroidIntentGate::new(resolver, &mut rt);
            let geo = AndroidIntent::view("android.intent.action.VIEW", "geo:0,0?q=cafe");
            let r = gate.dispatch(&surface, geo);
            assert!(r.decision.resolved(), "the geo VIEW resolves");

            // A SEND/mailto reaches nothing — no granted handler published that filter.
            let mail = AndroidIntent::view("android.intent.action.SEND", "mailto:x@y.z");
            assert!(gate.dispatch(&surface, mail).decision.refused_no_handler());
        }

        // Only the resolved geo VIEW reached the runtime's `am start` (recorded by the sink).
        assert_eq!(
            rt.intents_dispatched.len(),
            1,
            "only the resolved intent dispatched"
        );
        assert_eq!(
            rt.intents_dispatched[0].1, maps_cell,
            "routed to the maps handler cell"
        );
    }

    /// Launching a cell that was never installed is an error (not a silent empty resolver).
    #[test]
    fn launch_unknown_app_errors() {
        use crate::runtime::{CapturedFrameRuntime, launch_installed_app};
        let apps = registry();
        let mut rt = CapturedFrameRuntime::from_screencap_raw(Vec::new());
        let granted: BTreeSet<CellId> = BTreeSet::new();
        let err = launch_installed_app(&mut rt, &apps, cell_seed(0xFE), &granted);
        assert!(matches!(
            err,
            Err(crate::runtime::RuntimeError::AppNotInstalled { .. })
        ));
    }

    /// The install↔content loop: a granted provider-app's published authority is a
    /// cap-reachable [`ContentProvider`]; an ungranted one is not.
    #[test]
    fn content_resolver_ranges_only_over_the_granted_neighborhood() {
        let apps = registry();
        let me = cell_seed(9);
        let (contacts_cell, _) = contacts();

        // Ungranted: the contacts provider is unreachable.
        let none: BTreeSet<CellId> = BTreeSet::new();
        let r0 = apps.content_resolver_for(me, &none, ProviderGrant::ReadOnly);
        let uri = ContentUri::parse("content://com.android.contacts/people").unwrap();
        assert!(
            r0.resolve(&uri, ContentAccess::Read)
                .decision
                .refused_no_provider()
        );

        // Granted (read): a read is granted, but a write is refused by the read-only grant.
        let granted: BTreeSet<CellId> = [contacts_cell].into_iter().collect();
        let r1 = apps.content_resolver_for(me, &granted, ProviderGrant::ReadOnly);
        assert!(r1.resolve(&uri, ContentAccess::Read).decision.granted());
        assert!(
            r1.resolve(&uri, ContentAccess::Write)
                .decision
                .refused_read_only(),
            "a read-only grant does not amplify to a write"
        );
    }
}

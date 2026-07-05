//! The umem superpowers a JSON-lines append-log can NEVER give, proven at the control
//! plane's two record stores — the persistent-server [`ServerStore`] and the
//! [`MeshNodeRegistry`] (the #2 re-dregg move, `docs/REGISTRIES-AS-UMEM.md`):
//!
//! - **umem round-trip** — a `put`/`register` commits to a real Poseidon2 boundary root;
//!   a restart reconstructs the fleet / mesh FROM the committed heap, exactly-once.
//! - **fork** — branch the whole fleet record-set / mesh registry; the copies diverge.
//! - **time-travel** — restore an earlier committed root ("the fleet as of yesterday").
//!
//! Both stores were from-scratch durable logs (the `dreggnet-store` myopia); they are
//! now real umem cells, and these are the teeth a flat append-log could never grow.

use std::net::Ipv4Addr;

use dreggnet_control::{
    MachineId, MeshNode, MeshNodeRegistry, ServerRecord, ServerState, ServerStore,
};

fn temp(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let n = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-umem-ctrl-{tag}-{n}.snap"));
    p
}
fn cleanup(path: &std::path::Path) {
    std::fs::remove_file(path).ok();
    let mut h = path.as_os_str().to_os_string();
    h.push(".history");
    std::fs::remove_dir_all(std::path::PathBuf::from(h)).ok();
}

fn server(id: &str, state: ServerState) -> ServerRecord {
    ServerRecord {
        id: id.to_string(),
        app: "app".to_string(),
        name: format!("name-{id}"),
        state,
        lessee: "agent:ember".to_string(),
        cap_grade: "sandboxed".to_string(),
        asset: "DREGG".to_string(),
        budget_units: 1_000,
        per_period_units: 10,
        size: "small".to_string(),
        region: "local".to_string(),
        periods_metered: 0,
        machine_id: None,
        last_metered_at: None,
        cell_id: String::new(),
        checkpoint_root: None,
    }
}

fn node(id: &str, addr: &str) -> MeshNode {
    MeshNode::new(
        MachineId(id.to_string()),
        "cHVia2V5LXBsYWNlaG9sZGVyLXgyNTUxOS0zMmJ5dGVzIQ==",
        "203.0.113.1:51820",
        addr.parse::<Ipv4Addr>().unwrap(),
    )
}

// ----------------------------------------------------------------------------
// ServerStore (the persistent-server fleet record-set).
// ----------------------------------------------------------------------------

/// Round-trip: put servers → commit to a umem boundary root → "restart" → reconstructed
/// FROM the committed heap, exactly-once.
#[test]
fn server_store_umem_round_trip() {
    let path = temp("srv-round-trip");
    let root_after;
    {
        let store = ServerStore::open(&path).unwrap();
        store.put(&server("srv_a", ServerState::Running)).unwrap();
        store.put(&server("srv_b", ServerState::Running)).unwrap();
        root_after = store.umem_root();
        assert_eq!(root_after.len(), 64);
        assert_eq!(store.len(), 2);
    }
    let reopened = ServerStore::open(&path).unwrap();
    assert_eq!(reopened.len(), 2);
    assert_eq!(reopened.get("srv_a").unwrap().lessee, "agent:ember");
    assert_eq!(
        reopened.umem_root(),
        root_after,
        "the committed root is reproduced"
    );
    cleanup(&path);
}

/// Fork the whole fleet record-set: two divergent copies from one committed root.
#[test]
fn server_store_fork_diverges() {
    let base = temp("srv-fork-base");
    let forked = temp("srv-fork-copy");
    let store = ServerStore::open(&base).unwrap();
    store.put(&server("srv_a", ServerState::Running)).unwrap();
    store.put(&server("srv_b", ServerState::Running)).unwrap();
    let root0 = store.umem_root();

    let fork = store.fork(&forked).unwrap();
    assert_eq!(
        fork.umem_root(),
        root0,
        "the fork starts at the parent's root"
    );
    assert_eq!(fork.len(), 2);

    fork.put(&server("srv_c", ServerState::Running)).unwrap();
    store.put(&server("srv_d", ServerState::Running)).unwrap();
    assert!(fork.get("srv_c").is_some() && fork.get("srv_d").is_none());
    assert!(store.get("srv_d").is_some() && store.get("srv_c").is_none());
    assert_ne!(fork.umem_root(), store.umem_root(), "the copies diverged");
    cleanup(&base);
    cleanup(&forked);
}

/// Time-travel: restore an earlier committed root, durably across a restart.
#[test]
fn server_store_time_travel() {
    let path = temp("srv-time-travel");
    let root_v1;
    {
        let store = ServerStore::open(&path).unwrap();
        store.put(&server("srv_a", ServerState::Running)).unwrap();
        root_v1 = store.checkpoint(); // "yesterday": only srv_a
        store.put(&server("srv_b", ServerState::Running)).unwrap();
        assert_eq!(store.len(), 2);

        store.restore(&root_v1).unwrap();
        assert_eq!(store.len(), 1);
        assert!(store.get("srv_a").is_some() && store.get("srv_b").is_none());
        assert_eq!(store.umem_root(), root_v1);
    }
    let reopened = ServerStore::open(&path).unwrap();
    assert_eq!(reopened.len(), 1);
    assert!(reopened.get("srv_a").is_some() && reopened.get("srv_b").is_none());
    assert_eq!(reopened.umem_root(), root_v1);
    cleanup(&path);
}

// ----------------------------------------------------------------------------
// MeshNodeRegistry (the machine -> mesh-identity map).
// ----------------------------------------------------------------------------

/// Round-trip: register nodes → commit to a umem boundary root → "restart" →
/// reconstructed FROM the committed heap, reachable again.
#[test]
fn mesh_registry_umem_round_trip() {
    let path = temp("mesh-round-trip");
    let root_after;
    {
        let reg = MeshNodeRegistry::with_durable_store(&path).unwrap();
        reg.register(node("i-1", "100.64.0.1")).unwrap();
        reg.register(node("i-2", "100.64.0.2")).unwrap();
        root_after = reg.umem_root().unwrap();
        assert_eq!(root_after.len(), 64);
    }
    let reopened = MeshNodeRegistry::with_durable_store(&path).unwrap();
    assert!(reopened.get(&MachineId("i-1".to_string())).is_some());
    assert!(reopened.get(&MachineId("i-2".to_string())).is_some());
    assert_eq!(reopened.umem_root().unwrap(), root_after);
    cleanup(&path);
}

/// Fork the whole mesh registry: two divergent copies from one committed root.
#[test]
fn mesh_registry_fork_diverges() {
    let base = temp("mesh-fork-base");
    let forked = temp("mesh-fork-copy");
    let reg = MeshNodeRegistry::with_durable_store(&base).unwrap();
    reg.register(node("i-1", "100.64.0.1")).unwrap();
    let root0 = reg.umem_root().unwrap();

    let fork = reg
        .fork_registry(&forked)
        .expect("durable forks")
        .expect("fork ok");
    assert_eq!(fork.umem_root().unwrap(), root0);

    fork.register(node("i-2", "100.64.0.2")).unwrap();
    reg.register(node("i-3", "100.64.0.3")).unwrap();
    assert!(fork.get(&MachineId("i-2".to_string())).is_some());
    assert!(fork.get(&MachineId("i-3".to_string())).is_none());
    assert!(reg.get(&MachineId("i-3".to_string())).is_some());
    assert!(reg.get(&MachineId("i-2".to_string())).is_none());
    assert_ne!(fork.umem_root().unwrap(), reg.umem_root().unwrap());
    cleanup(&base);
    cleanup(&forked);
}

/// Time-travel: restore the mesh registry to an earlier committed root, durably.
#[test]
fn mesh_registry_time_travel() {
    let path = temp("mesh-time-travel");
    let root_v1;
    {
        let reg = MeshNodeRegistry::with_durable_store(&path).unwrap();
        reg.register(node("i-1", "100.64.0.1")).unwrap();
        root_v1 = reg.checkpoint_registry().unwrap();
        reg.register(node("i-2", "100.64.0.2")).unwrap();

        reg.restore_registry(&root_v1).unwrap();
        assert!(reg.get(&MachineId("i-1".to_string())).is_some());
        assert!(reg.get(&MachineId("i-2".to_string())).is_none());
        assert_eq!(reg.umem_root().unwrap(), root_v1);
    }
    let reopened = MeshNodeRegistry::with_durable_store(&path).unwrap();
    assert!(reopened.get(&MachineId("i-1".to_string())).is_some());
    assert!(reopened.get(&MachineId("i-2".to_string())).is_none());
    assert_eq!(reopened.umem_root().unwrap(), root_v1);
    cleanup(&path);
}

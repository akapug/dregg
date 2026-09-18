//! Process-global Lean initialization cannot be reset between scenarios.
//! Each parent test executes itself alone in a fresh subprocess, including under libtest.
#![cfg(feature = "lean-lib")]

use dregg_lean_ffi::{
    deleg_admit, lean_initialization_status, lean_runtime_init_status, DelegGrant, LeanRuntimeMode,
};
use std::process::Command;
use std::sync::{Arc, Barrier};

#[cfg(lean_lib_present)]
extern "C" {
    fn dregg_ffi_test_foreign_thread(single_threaded: i32) -> i32;
}

fn foreign_thread(single_threaded: bool) -> i32 {
    #[cfg(lean_lib_present)]
    unsafe {
        dregg_ffi_test_foreign_thread(i32::from(single_threaded))
    }
    #[cfg(not(lean_lib_present))]
    {
        let _ = single_threaded;
        panic!("lifecycle probe requires the real Lean archive")
    }
}

fn isolated(name: &str, body: impl FnOnce()) {
    const CHILD: &str = "DREGG_INIT_LIFECYCLE_CHILD";
    if std::env::var(CHILD).as_deref() == Ok(name) {
        assert_eq!(lean_initialization_status(), Default::default());
        body();
        return;
    }
    let result = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", name, "--nocapture", "--test-threads=1"])
        .env(CHILD, name)
        .status()
        .expect("start isolated Lean initialization scenario");
    assert!(result.success(), "isolated {name} failed: {result}");
}

fn admitted() {
    assert_eq!(
        deleg_admit(
            DelegGrant {
                tool_id: 7,
                rate_limit: 10,
                deadline: 99
            },
            99,
            7,
            9,
            10
        ),
        Ok(true)
    );
}

fn check_real_verdicts() {
    let grant = DelegGrant {
        tool_id: 7,
        rate_limit: 10,
        deadline: 99,
    };
    admitted();
    for (now, tool, old, new) in [
        (99, 8, 9, 10),              // scope
        (100, 7, 9, 10),             // deadline
        (99, 7, 8, 10),              // step
        (99, 7, -1, 0),              // sane prior count
        (99, 7, 10, 11),             // rate
        (99, 7, i64::MAX, i64::MIN), // no host integer wraparound
    ] {
        assert_eq!(deleg_admit(grant, now, tool, old, new), Ok(false));
    }
    assert_eq!(
        deleg_admit(
            DelegGrant {
                tool_id: i64::MIN,
                rate_limit: i64::MAX,
                deadline: i64::MAX,
            },
            i64::MIN,
            i64::MIN,
            i64::MAX - 1,
            i64::MAX
        ),
        Ok(true)
    );
}

#[test]
fn delegated_admission_initializes_only_its_real_lean_module() {
    isolated(
        "delegated_admission_initializes_only_its_real_lean_module",
        || {
            check_real_verdicts();
            let threads: Vec<_> = (0..8)
                .map(|_| std::thread::spawn(check_real_verdicts))
                .collect();
            for thread in threads {
                thread.join().unwrap();
            }
            let status = lean_initialization_status();
            assert_eq!(status.runtime_mode, Some(LeanRuntimeMode::Default));
            assert!(status.delegated_admission_ready);
            assert_eq!(status.default_full, None);
            assert_eq!(status.single_threaded_full, None);
            assert_eq!(status.failure, None);
            assert_eq!(lean_runtime_init_status(), None);

            // Strict codec behavior through the same actual generated export. The
            // public verdict calls above have initialized this exact module first.
            #[cfg(dregg_deleg_admit_present)]
            {
                use std::ffi::CString;
                use std::os::raw::c_char;
                extern "C" {
                    fn dregg_deleg_admit_str(
                        input: *const c_char,
                        out: *mut c_char,
                        cap: usize,
                    ) -> usize;
                }
                let malformed = CString::new("7 10 malformed").unwrap();
                let mut out = [17u8; 32];
                let size = unsafe {
                    dregg_deleg_admit_str(malformed.as_ptr(), out.as_mut_ptr().cast(), out.len())
                };
                assert_eq!(size, 0, "malformed wire must produce no verdict");
                assert_eq!(out[0], 0);
            }
            #[cfg(not(dregg_deleg_admit_present))]
            panic!("lifecycle probe requires the real DelegAdmit initializer/export pair");
        },
    );
}

#[test]
fn lean_init_lifecycle_heavy_narrow_then_concurrent_full() {
    isolated(
        "lean_init_lifecycle_heavy_narrow_then_concurrent_full",
        || {
            admitted();
            assert_eq!(lean_runtime_init_status(), None);
            let start = Arc::new(Barrier::new(5));
            let native = {
                let start = Arc::clone(&start);
                std::thread::spawn(move || {
                    start.wait();
                    foreign_thread(false)
                })
            };
            let readers: Vec<_> = (0..4)
                .map(|_| {
                    let start = Arc::clone(&start);
                    std::thread::spawn(move || {
                        start.wait();
                        check_real_verdicts();
                    })
                })
                .collect();
            assert_eq!(
                native.join().unwrap(),
                0,
                "native ABI init + real kernel call"
            );
            for reader in readers {
                reader.join().unwrap();
            }
            assert_eq!(lean_runtime_init_status(), Some(Ok(())));
            assert_eq!(dregg_lean_ffi::dregg_ffi_init(), 0);
            assert_eq!(
                dregg_lean_ffi::dregg_ffi_init_st(),
                1,
                "mixed mode must refuse"
            );
            assert_eq!(
                foreign_thread(false),
                0,
                "a later foreign host thread attaches safely"
            );
            admitted();
            assert_eq!(lean_initialization_status().failure, None);
        },
    );
}

#[test]
fn lean_init_lifecycle_heavy_foreign_full_first_then_narrow() {
    isolated(
        "lean_init_lifecycle_heavy_foreign_full_first_then_narrow",
        || {
            // The runtime-starting native thread exits before this Rust thread enters.
            // It must neither attach its allocator twice nor finalize the original runtime.
            assert_eq!(foreign_thread(false), 0);
            check_real_verdicts();
            assert!(lean_initialization_status().delegated_admission_ready);
            assert_eq!(lean_runtime_init_status(), Some(Ok(())));
            assert_eq!(foreign_thread(false), 0);
        },
    );
}

#[test]
fn lean_init_lifecycle_heavy_st_owner_and_mode_exclusion() {
    isolated(
        "lean_init_lifecycle_heavy_st_owner_and_mode_exclusion",
        || {
            assert!(dregg_lean_ffi::init_single_threaded());
            check_real_verdicts();
            let status = lean_initialization_status();
            assert_eq!(status.runtime_mode, Some(LeanRuntimeMode::SingleThreaded));
            assert_eq!(status.single_threaded_full, Some(Ok(())));
            assert_eq!(status.default_full, None);
            assert_eq!(
                foreign_thread(true),
                1,
                "foreign host cannot take ST ownership"
            );
            assert_eq!(
                foreign_thread(false),
                1,
                "foreign host cannot switch runtime mode"
            );
            assert!(!dregg_lean_ffi::lean_available());
            assert_eq!(
                lean_initialization_status(),
                status,
                "refusal must not mutate readiness"
            );
            admitted();
        },
    );
}

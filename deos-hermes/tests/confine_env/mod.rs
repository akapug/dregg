//! Which confinement branch THIS host can take, probed independently of the
//! sandbox under test, so a confinement test asserts the branch the host decides
//! and says out loud which one it took.
//!
//! * macOS: Seatbelt (`sandbox_init`) is always present → `Confinable`.
//! * Linux: the jail's first layer is `unshare(USER|NET|NS|PID)`. A kernel that
//!   forbids unprivileged user namespaces refuses it (`EPERM`/`ENOSPC`), and then
//!   the launch MUST be refused with the typed `Namespaces` error. (Ubuntu's
//!   `apparmor_restrict_unprivileged_userns = 1` still allows the `unshare`; it
//!   only refuses a uid map, which the jail does not write.)

#![allow(dead_code)]

/// The branch a confinement test must assert on this host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConfineEnv {
    /// Every layer is available: the PD launches and every tooth must hold.
    Confinable,
    /// The namespace layer is unavailable (the reason is the errno): the launch
    /// must be REFUSED with the typed `Namespaces` error, and no PD may run.
    NoNamespaces(String),
}

/// Probe in a throwaway forked child (the unshare is irreversible).
pub fn probe() -> ConfineEnv {
    #[cfg(target_os = "linux")]
    {
        let flags =
            libc::CLONE_NEWUSER | libc::CLONE_NEWNET | libc::CLONE_NEWNS | libc::CLONE_NEWPID;
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0, "fork for the env probe");
        if pid == 0 {
            let rc = unsafe { libc::unshare(flags) };
            let errno = if rc == 0 {
                0
            } else {
                std::io::Error::last_os_error()
                    .raw_os_error()
                    .unwrap_or(255)
            };
            unsafe { libc::_exit(errno.clamp(0, 255)) };
        }
        let mut status: libc::c_int = 0;
        let rc = unsafe { libc::waitpid(pid, &mut status, 0) };
        assert_eq!(rc, pid, "reap the env probe");
        assert!(libc::WIFEXITED(status), "env probe exited normally");
        match libc::WEXITSTATUS(status) {
            0 => ConfineEnv::Confinable,
            e => ConfineEnv::NoNamespaces(std::io::Error::from_raw_os_error(e).to_string()),
        }
    }
    #[cfg(not(target_os = "linux"))]
    {
        ConfineEnv::Confinable
    }
}

/// Probe, and print the branch (a green run always says which branch it took).
pub fn probe_and_announce(test: &str) -> ConfineEnv {
    let env = probe();
    eprintln!("[confine-env] {test}: {env:?}");
    env
}

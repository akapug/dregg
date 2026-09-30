//! The environment a deos terminal hands its shell.
//!
//! A terminal child gets a MINIMAL environment built from a named allowlist,
//! never the host process's whole environment. The cockpit process that hosts a
//! terminal routinely holds provider keys (`ANTHROPIC_API_KEY`, `HERMES_API_KEY`,
//! read from env by `deos-hermes`), session tokens and launcher secrets; every one
//! of them used to reach the shell and anything it ran.
//!
//! Two callers build a child from this:
//!
//! - the native view ([`crate::model::Terminal::spawn`]), whose `env` argument is
//!   the child's COMPLETE environment — the model strips everything inherited that
//!   is not in the map (see `model.rs`);
//! - the PTY-over-WebSocket server ([`crate::pty_server`]), which calls
//!   `CommandBuilder::env_clear` and then applies this map.
//!
//! The allowlist is [`BASE_VARS`] plus [`EXTRA_VARS`], plus any names an operator
//! lists in `DEOS_TERMINAL_ENV_ALLOW` (comma-separated). An operator who wants a
//! secret in their terminal has to name it.

use std::collections::HashMap;

/// The variables every shell gets when the host has them.
pub const BASE_VARS: &[&str] = &["PATH", "HOME", "TERM", "LANG"];

/// Identity, locale and scratch-space variables that carry no credential.
pub const EXTRA_VARS: &[&str] = &[
    "USER", "LOGNAME", "SHELL", "TMPDIR", "LC_ALL", "LC_CTYPE", "TZ",
];

/// The operator's explicit additions to the allowlist (comma-separated names).
pub const ENV_ALLOW_VAR: &str = "DEOS_TERMINAL_ENV_ALLOW";

/// `TERM` when the host process has none (a GUI-launched cockpit usually has no
/// controlling terminal, so no `TERM`); the grid is an xterm-compatible emulator.
pub const DEFAULT_TERM: &str = "xterm-256color";

/// The minimal shell environment, read from this process's environment.
pub fn minimal_shell_env() -> HashMap<String, String> {
    let extra = std::env::var(ENV_ALLOW_VAR).unwrap_or_default();
    minimal_shell_env_from(
        |name| std::env::var(name).ok(),
        extra.split(',').map(str::trim).filter(|s| !s.is_empty()),
    )
}

/// The minimal shell environment over an arbitrary lookup (the testable core).
/// `operator_allow` are extra names to carry through if present.
pub fn minimal_shell_env_from<'a>(
    lookup: impl Fn(&str) -> Option<String>,
    operator_allow: impl IntoIterator<Item = &'a str>,
) -> HashMap<String, String> {
    let mut env = HashMap::new();
    let names = BASE_VARS
        .iter()
        .chain(EXTRA_VARS.iter())
        .copied()
        .chain(operator_allow);
    for name in names {
        if name.is_empty() || name.contains('=') {
            continue;
        }
        if let Some(value) = lookup(name) {
            env.insert(name.to_string(), value);
        }
    }
    env.entry("TERM".to_string())
        .or_insert_with(|| DEFAULT_TERM.to_string());
    env
}

#[cfg(test)]
mod tests {
    use super::*;

    fn host(vars: &[(&str, &str)]) -> impl Fn(&str) -> Option<String> {
        let map: HashMap<String, String> = vars
            .iter()
            .map(|(k, v)| (k.to_string(), v.to_string()))
            .collect();
        move |name| map.get(name).cloned()
    }

    #[test]
    fn only_allowlisted_names_cross() {
        let lookup = host(&[
            ("PATH", "/usr/bin:/bin"),
            ("HOME", "/home/op"),
            ("LANG", "C.UTF-8"),
            ("USER", "op"),
            ("ANTHROPIC_API_KEY", "sk-ant-secret"),
            ("HERMES_API_KEY", "hk-secret"),
            ("DEOS_TERMINAL_TOKEN", "launcher-token"),
            ("AWS_SECRET_ACCESS_KEY", "aws"),
        ]);
        let env = minimal_shell_env_from(lookup, []);
        let mut keys: Vec<&str> = env.keys().map(String::as_str).collect();
        keys.sort_unstable();
        assert_eq!(keys, ["HOME", "LANG", "PATH", "TERM", "USER"]);
        assert_eq!(
            env["TERM"], DEFAULT_TERM,
            "TERM defaults when the host has none"
        );
        for (_, v) in &env {
            assert!(!v.contains("secret") && !v.contains("token") && v != "aws");
        }
    }

    #[test]
    fn host_term_wins_and_operator_names_are_honoured() {
        let lookup = host(&[
            ("TERM", "screen"),
            ("PATH", "/bin"),
            ("MY_TOOL_HOME", "/opt/tool"),
            ("NOT_ASKED", "x"),
        ]);
        let env = minimal_shell_env_from(lookup, ["MY_TOOL_HOME", "", "A=B"]);
        assert_eq!(env["TERM"], "screen");
        assert_eq!(env["MY_TOOL_HOME"], "/opt/tool");
        assert!(!env.contains_key("NOT_ASKED"));
        assert!(!env.contains_key("A=B"));
    }
}

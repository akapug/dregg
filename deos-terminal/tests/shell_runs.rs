//! Headless proof that the terminal MODEL runs a real shell over a real PTY.
//!
//! No GUI: spawn `$SHELL`, write a command, poll the grid until the command's
//! output appears. This is the "a real shell works" verification minus the gpui
//! window (the `deos-terminal-demo` bin is the windowed version of the same).

use std::collections::HashMap;
use std::time::{Duration, Instant};

use deos_terminal::model::{TermSize, Terminal};

/// Flatten the visible grid into a string so we can assert on shell output.
fn screen_text(term: &Terminal) -> String {
    let content = term.content();
    let cols = content.columns.max(1);
    let rows = content.screen_lines.max(1);
    let mut grid = vec![vec![' '; cols]; rows];
    for cell in &content.cells {
        let row = cell.line + content.display_offset as i32;
        if row >= 0 && (row as usize) < rows && cell.column < cols {
            grid[row as usize][cell.column] = cell.c;
        }
    }
    grid.into_iter()
        .map(|r| r.into_iter().collect::<String>())
        .collect::<Vec<_>>()
        .join("\n")
}

fn wait_for<F: Fn(&Terminal) -> bool>(term: &Terminal, timeout: Duration, pred: F) -> bool {
    let start = Instant::now();
    while start.elapsed() < timeout {
        if pred(term) {
            return true;
        }
        std::thread::sleep(Duration::from_millis(25));
    }
    pred(term)
}

#[test]
fn real_shell_echoes_a_marker() {
    // Use a plain POSIX shell with no rc files for a deterministic, fast prompt.
    let shell = ("/bin/sh".to_string(), vec!["-i".to_string()]);
    let mut env = HashMap::new();
    // Keep the prompt trivial and predictable.
    env.insert("PS1".to_string(), "$ ".to_string());
    env.insert("ENV".to_string(), String::new());

    let term = Terminal::spawn(
        Some(shell),
        std::env::current_dir().ok(),
        env,
        TermSize::new(80, 24),
    )
    .expect("spawn shell");

    // Let the shell come up.
    assert!(
        wait_for(&term, Duration::from_secs(5), |t| t.generation() > 0),
        "the shell never produced any output (no PTY activity)"
    );

    // Run a command whose output is a unique marker.
    let marker = "DEOS_TERMINAL_OK_4242";
    term.write_str(&format!("echo {marker}\n"));

    let saw_marker = wait_for(&term, Duration::from_secs(8), |t| {
        // The marker appears twice (the typed echo + the command output); assert
        // it shows up at least as the command's output line.
        screen_text(t).matches(marker).count() >= 1
    });

    let screen = screen_text(&term);
    assert!(
        saw_marker,
        "shell did not echo the marker. Visible screen was:\n{screen}"
    );
}

#[test]
fn pty_resizes_without_panicking() {
    let term_result = Terminal::spawn(
        Some(("/bin/sh".to_string(), vec![])),
        std::env::current_dir().ok(),
        HashMap::new(),
        TermSize::new(80, 24),
    );
    let mut term = term_result.expect("spawn shell");
    term.resize(TermSize::new(120, 40), 8, 16);
    let content = term.content();
    assert_eq!(content.columns, 120);
    assert_eq!(content.screen_lines, 40);
}

/// D10: the child environment is exactly the map handed to `Terminal::spawn` —
/// a variable this process holds does not reach the shell unless named. The
/// positive half (a named variable does arrive) keeps the probe honest: if the
/// shell never expanded anything, both halves could not pass together.
#[test]
fn host_environment_does_not_reach_the_shell() {
    // A secret-shaped variable in THIS process's environment.
    std::env::set_var("DEOS_D10_HOST_SECRET", "leaked-host-secret");

    let shell = ("/bin/sh".to_string(), vec!["-i".to_string()]);
    let mut env = HashMap::new();
    env.insert("PS1".to_string(), "$ ".to_string());
    env.insert("ENV".to_string(), String::new());
    env.insert("DEOS_D10_NAMED".to_string(), "named-ok".to_string());

    let term = Terminal::spawn(
        Some(shell),
        std::env::current_dir().ok(),
        env,
        TermSize::new(120, 24),
    )
    .expect("spawn shell");
    assert!(
        wait_for(&term, Duration::from_secs(5), |t| t.generation() > 0),
        "the shell never produced any output"
    );

    // `[S:<secret-or-absent>]` and `[N:<named>]` land as the command's output.
    term.write_str("echo \"[S:${DEOS_D10_HOST_SECRET:-absent}]\" \"[N:${DEOS_D10_NAMED:-absent}]\"\n");
    let done = wait_for(&term, Duration::from_secs(8), |t| {
        screen_text(t).contains("[N:named-ok]")
    });
    let screen = screen_text(&term);
    assert!(done, "the probe command never ran. Screen:\n{screen}");
    assert!(
        screen.contains("[S:absent]"),
        "the host variable reached the shell. Screen:\n{screen}"
    );
    assert!(
        !screen.contains("[S:leaked-host-secret]"),
        "the host secret reached the shell. Screen:\n{screen}"
    );
}

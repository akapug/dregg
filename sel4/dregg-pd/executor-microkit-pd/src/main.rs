//! executor-microkit-pd — the firmament keystone (WALL step 4, ASSEMBLED): the
//! `executor` SEAT of the 5-PD assembly (`sel4/dregg.system`), made REAL.
//!
//! This is a Microkit protection domain that EMBEDS the VERIFIED dregg executor
//! (`dregg_exec_full_forest_auth` = `execFullForestG` + admission, proved in
//! `metatheory/`) and runs a real turn THROUGH the PD's channels:
//!
//!     net/ingress --(ch 1)--> [executor PD] --(ch 2)--> persist
//!                  turn in       VERIFIED turn       receipt in
//!                  turn_in (R)   decode→step→encode  commit_out (RW)
//!
//! It folds the proven hosting from the sibling `../executor-rootserver/` (the
//! musl + libuv-excised Lean-ELF runtime that BOOTS one verified turn under seL4)
//! into a Microkit *PD* seat. The two differ only in the entry shim:
//!
//!   * The root task uses `declare_root_task!` + `sel4-root-task-with-std`.
//!   * This PD uses `#[protection_domain]` + a Microkit `Handler`.
//!
//! BUT both share `sel4-runtime-common`'s `global_init()`, which runs the C++
//! static initializers (`.preinit_array` then `.init_array`) before the entry —
//! the Microkit entry opts in via `declare_rust_entrypoint! { global_init if
//! true }`. So the `.preinit_array` syscall-handler install (ahead of the Lean
//! C++ ctors that allocate at init) + the in-PD Linux-syscall handler that
//! services the runtime's malloc/write/... work IDENTICALLY here. The handler +
//! heaps below are ported verbatim from the root task; only the entry/event-loop
//! shape is Microkit's.
//!
//! Cap partition (.docs-history-noclaude/FIRMAMENT.md §2): `turn_in` (R), `commit_out` (RW), and
//! NOTHING else — no device cap, no NIC cap. seL4 faults this PD if it touches a
//! cap it does not hold, so the VERIFIED turn reading turn_in and writing
//! commit_out IS the partition, enforced.

#![no_std]
#![no_main]
#![allow(unreachable_patterns)]

use core::alloc::{GlobalAlloc, Layout};
use core::ffi::{c_char, c_int, c_long};
use core::ptr;

use one_shot_mutex::sync::RawOneShotMutex;

use sel4_dlmalloc::{StaticDlmalloc, StaticHeap};
use sel4_linux_syscall_types::{ENOMEM, ENOSYS, MAP_ANONYMOUS, SEEK_CUR};
use sel4_microkit::{
    debug_print, debug_println, memory_region_symbol, protection_domain, Channel, ChannelSet,
    Handler, Infallible,
};
use sel4_musl::{
    set_syscall_handler, ParseSyscallError, Syscall, SyscallReturnValue, VaListAsSyscallArgs,
};

// ── The shared regions this PD's cap partition grants (mirrors dregg.system) ──
//   turn_in    — R : the de-enveloped, signature-checked turn from ingress.
//   commit_out — RW: the commit-log entry (the receipt) handed to persist.
const TURN_IN_SIZE: usize = 0x100000; // 1 MiB  (dregg.system <memory_region turn_in>)
const COMMIT_OUT_SIZE: usize = 0x400000; // 4 MiB (dregg.system <memory_region commit_out>)

fn turn_in() -> *const u8 {
    memory_region_symbol!(turn_in_vaddr: *mut [u8], n = TURN_IN_SIZE).as_ptr() as *const u8
}
fn commit_out() -> *mut u8 {
    memory_region_symbol!(commit_out_vaddr: *mut [u8], n = COMMIT_OUT_SIZE).as_ptr() as *mut u8
}

// ── The channels (mirrors dregg.system <channel> ends for `executor`) ─────────
const NET_TO_EXECUTOR: Channel = Channel::new(1); // net/ingress signals "turn staged"
const EXECUTOR_TO_PERSIST: Channel = Channel::new(2); // signal "commit ready"
const EXECUTOR_TO_VERIFIER: Channel = Channel::new(3); // one-way "bundle staged" (FIRMAMENT §2)

// ── The C driver (scripts/driver-microkit.c): init once + run one turn ────────
unsafe extern "C" {
    fn dregg_executor_init() -> c_int;
    fn dregg_executor_run_turn(
        in_ptr: *const u8,
        in_len: usize,
        out_ptr: *mut u8,
        out_cap: usize,
    ) -> c_long;
    fn dregg_executor_demo_wire(len: *mut usize) -> *const u8;
}

// ── THE ORDERING FIX (../executor-rootserver, WALL-roottask.md §__sysinfo-null) ─
// The seL4 musl libc routes every syscall through the `__sysinfo` function
// pointer, NULL until `set_syscall_handler` populates it. `global_init()` runs
// the C++ `.init_array` constructors (Lean static initializers — some allocate:
// malloc → mmap → `br __sysinfo`(=0) → fault at address 0) BEFORE the PD entry.
// `sel4_ctors_dtors::run_ctors` executes `.preinit_array` BEFORE `.init_array`,
// so a `.preinit_array` entry installs the handler ahead of every C++ ctor. This
// is identical to the root task — the Microkit entry runs the same global_init.
unsafe extern "C" fn install_syscall_handler_preinit() {
    unsafe {
        set_syscall_handler(handle_syscall);
    }
}

#[used]
#[unsafe(link_section = ".preinit_array")]
static PREINIT_INSTALL_SYSCALL_HANDLER: unsafe extern "C" fn() = install_syscall_handler_preinit;

#[protection_domain(heap_size = 0x10000)]
fn init() -> HandlerImpl {
    debug_println!("");
    debug_println!(
        "[executor] dregg executor-PD — the firmament HEART, embedding the VERIFIED executor"
    );
    debug_println!("[executor]   cap partition: turn_in (R), commit_out (RW); NO device/NIC cap");
    debug_println!("[executor]   (the .preinit_array hook installed the sel4-musl syscall handler");
    debug_println!("[executor]    ahead of the Lean C++ ctors that global_init() already ran)");

    // Prove the mapped regions are live (seL4 would have faulted this PD already
    // if it lacked these caps — the C++ ctors + the read/write below all touch
    // PD memory + the regions).
    let staged0 = unsafe { core::ptr::read_volatile(turn_in()) };
    debug_println!("[executor]   turn_in[0]={:#04x} (region live)", staged0);

    // Bring up the embedded Lean runtime ONCE (module init for the COMPILED
    // closure). The C++ ctors already ran in global_init(); this is the Lean
    // module-init chain rooted at Dregg2.Exec.FFI.
    debug_println!("[executor]   initializing embedded Lean runtime …");
    let rc = unsafe { dregg_executor_init() };
    if rc != 0 {
        debug_println!("[executor]   FATAL: Lean runtime init returned rc={rc}");
        // Fall through to the handler anyway so the PD doesn't fault the whole
        // assembly; turns will report the init failure.
    } else {
        debug_println!("[executor]   embedded Lean runtime UP — execFullForestG ready ( ◕‿◕ )");
    }

    // SELF-STAGE the verified demo turn so the assembly demonstrates a REAL turn
    // flowing through THIS PD even before the net edge writes one. The cap
    // partition maps turn_in READ-ONLY for the executor (the net/ingress edge is
    // the writer; seL4 faults any write the executor attempts — verified live:
    // a write to turn_in's vaddr takes a level-3 permission fault). So the boot
    // demo runs the verified turn from the COMPILED-IN wire (the PD's own
    // readable text, `dregg_executor_demo_wire`) straight into the verified
    // executor, writing only to commit_out (RW) and signalling persist + the
    // verifier — exactly the channel control-flow the LIVE path drives, minus the
    // read of the (here read-only, net-filled) turn_in. This is the assembled-PD
    // analogue of the rootserver's compiled-in wire.
    if rc == 0 {
        debug_println!(
            "[executor]   >>> running the verified DEMO turn (in-PD wire) through the PD"
        );
        run_demo_turn();
    }

    debug_println!("[executor]   awaiting ingress→executor signal (channel id 1) for live turns …");
    HandlerImpl { turns: 0 }
}

/// Run the compiled-in verified demo wire (`dregg_executor_demo_wire`, the same
/// `wideDemoInput` the host-musl + rootserver run banked → status:2 ok:1) through
/// the VERIFIED executor, write the receipt to `commit_out` (RW), and signal
/// persist + the verifier. This is the BOOT self-demo: it does NOT touch the
/// read-only turn_in (which the net edge fills for live turns). Returns the
/// receipt length, or a negative code.
fn run_demo_turn() -> c_long {
    let mut len: usize = 0;
    let wire = unsafe { dregg_executor_demo_wire(&mut len) };
    if wire.is_null() || len == 0 {
        debug_println!("[executor]   (no demo wire compiled in — len={len})");
        return -3;
    }
    debug_println!("[executor]   demo wire: {len} bytes (in-PD text, turn_in untouched)");
    run_turn_through_executor(wire, len)
}

/// Read the framed turn from the READ-ONLY `turn_in` region (4-byte LE length
/// prefix + wire) the net/ingress edge staged, and run it through the verified
/// executor. This is the LIVE path: turn_in is mapped R for the executor, so
/// reading it is within the cap partition.
fn run_turn_from_turn_in() -> c_long {
    let src = turn_in();
    let len = unsafe {
        let b0 = core::ptr::read_volatile(src.add(0)) as u32;
        let b1 = core::ptr::read_volatile(src.add(1)) as u32;
        let b2 = core::ptr::read_volatile(src.add(2)) as u32;
        let b3 = core::ptr::read_volatile(src.add(3)) as u32;
        (b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)) as usize
    };
    if len == 0 || len + 4 > TURN_IN_SIZE {
        debug_println!("[executor]   turn_in framing empty/oversize (len={len}); nothing to run");
        return -2;
    }
    let in_ptr = unsafe { src.add(4) };
    run_turn_through_executor(in_ptr, len)
}

/// The shared turn path: run `in_ptr[0..in_len]` through the VERIFIED executor,
/// write the receipt to `commit_out` (RW), surface status/ok, and signal persist
/// (channel id 2) + the verifier (channel id 3) — the assembly's real
/// control-flow edges (dregg.system <channel>s). The input may come from the
/// in-PD demo wire (boot) or the read-only turn_in (live); the WRITE is always to
/// commit_out, the one region the executor holds RW.
fn run_turn_through_executor(in_ptr: *const u8, in_len: usize) -> c_long {
    let out_ptr = commit_out();

    let n = unsafe { dregg_executor_run_turn(in_ptr, in_len, out_ptr, COMMIT_OUT_SIZE) };
    if n < 0 {
        debug_println!("[executor]   run_turn returned {n} (overflow/error)");
        return n;
    }

    // The receipt is now in commit_out. Echo a short prefix over serial so the
    // boot log shows the real turn flowed through the PD, then surface the
    // status/ok the verified executor produced.
    debug_println!("[executor]   receipt written to commit_out ({n} bytes):");
    print_commit_out(n as usize);
    report_status_ok(n as usize);

    debug_println!("[executor]   signalling persist (ch 2) + verifier (ch 3)");
    EXECUTOR_TO_PERSIST.notify();
    EXECUTOR_TO_VERIFIER.notify();
    n
}

/// Print the receipt bytes in `commit_out[0..n]` over the debug serial.
fn print_commit_out(n: usize) {
    let p = commit_out() as *const u8;
    debug_print!("---RECEIPT-BEGIN---\n");
    for i in 0..n {
        let c = unsafe { core::ptr::read_volatile(p.add(i)) };
        debug_print!("{}", c as char);
    }
    debug_print!("\n---RECEIPT-END---\n");
}

/// Scan the receipt for the verified `"status":N,"ok":M` tail and print a crisp
/// one-liner — the load-bearing evidence the turn ACCEPTED (status:2 ok:1).
fn report_status_ok(n: usize) {
    let p = commit_out() as *const u8;
    let mut status: Option<u8> = None;
    let mut ok: Option<u8> = None;
    // Tiny forward scan for the substrings `status":` and `ok":` (the JSON tail).
    let read = |i: usize| -> u8 { unsafe { core::ptr::read_volatile(p.add(i)) } };
    let matches = |i: usize, pat: &[u8]| -> bool {
        if i + pat.len() > n {
            return false;
        }
        for (k, &c) in pat.iter().enumerate() {
            if read(i + k) != c {
                return false;
            }
        }
        true
    };
    let digit_after = |mut i: usize| -> Option<u8> {
        // skip to the next ASCII digit, parse one digit (status/ok are 0..9)
        while i < n {
            let c = read(i);
            if c.is_ascii_digit() {
                return Some(c - b'0');
            }
            if c == b',' || c == b'}' {
                break;
            }
            i += 1;
        }
        None
    };
    let mut i = 0;
    while i < n {
        if status.is_none() && matches(i, b"status\":") {
            status = digit_after(i + 8);
        }
        if ok.is_none() && matches(i, b"ok\":") {
            ok = digit_after(i + 4);
        }
        if status.is_some() && ok.is_some() {
            break;
        }
        i += 1;
    }
    match (status, ok) {
        (Some(s), Some(o)) => {
            debug_println!("[executor]   ==> VERIFIED turn through the PD: status:{s} ok:{o}");
            if s == 2 && o == 1 {
                debug_println!("[executor]   ==> bodyCommitted — the executor PD ran a REAL accepted turn ( ◕‿◕ )");
            }
        }
        _ => debug_println!("[executor]   ==> turn ran (receipt {n} bytes; status/ok not parsed)"),
    }
}

struct HandlerImpl {
    turns: u64,
}

impl Handler for HandlerImpl {
    type Error = Infallible;

    // net/ingress signals "a signature-checked turn is staged in turn_in" on
    // channel id 1. The PD runs it through the VERIFIED executor and signals
    // persist (id 2) + verifier (id 3). This is the LIVE turn path — each
    // ingress notification drives one real verified turn through the PD.
    fn notified(&mut self, channels: ChannelSet) -> Result<(), Self::Error> {
        for channel in channels.iter() {
            if channel == NET_TO_EXECUTOR {
                self.turns += 1;
                debug_println!(
                    "[executor]   ingress signal (ch {}) — running LIVE turn #{}",
                    channel.index(),
                    self.turns
                );
                run_turn_from_turn_in();
            } else {
                debug_println!("[executor]   notified on channel {}", channel.index());
            }
        }
        Ok(())
    }
}

// ════════════════════════════════════════════════════════════════════════════
// The in-PD Linux-syscall handler — ported verbatim from ../executor-rootserver/
// src/main.rs. It services the surface the embedded Lean runtime exercises on the
// pure executor turn: heap (Brk + anonymous Mmap), stdout/stderr (Write/Writev),
// and the no-op identity calls. Any unexpected syscall is reported (a precise
// next wall to characterize) rather than silently faked. The verified turn is
// pure + single-threaded + deterministic, so the faithful answers are no-op
// success / zero-fill.
// ════════════════════════════════════════════════════════════════════════════

// ENOENT (no such file/directory) — not re-exported by sel4-linux-syscall-types.
const ENOENT: SyscallReturnValue = 2;
const EBADF: SyscallReturnValue = 9;
// The sentinel fd `openat("/dev/urandom")` returns; `read` zero-fills it. The
// Lean runtime seeds its hash from /dev/urandom at init.
const URANDOM_FD: SyscallReturnValue = 1000;

fn path_is(path_ptr: *const u8, want: &[u8]) -> bool {
    if path_ptr.is_null() {
        return false;
    }
    for (i, &w) in want.iter().enumerate() {
        let c = unsafe { *path_ptr.add(i) };
        if c != w {
            return false;
        }
    }
    unsafe { *path_ptr.add(want.len()) == 0 }
}

fn handle_syscall(
    syscall: Result<Syscall, ParseSyscallError<VaListAsSyscallArgs>>,
) -> SyscallReturnValue {
    match syscall {
        Ok(syscall) => handle_known_syscall(syscall),
        Err(ParseSyscallError::UnrecognizedSyscallNumber { sysnum, args }) => {
            handle_by_number(sysnum, args)
        }
        Err(err) => {
            debug_println!("[executor]   UNPARSED SYSCALL (a precise wall): {err:?}");
            -ENOSYS
        }
    }
}

mod nr {
    use sel4_linux_syscall_types::SyscallNumber;
    pub const IOCTL: SyscallNumber = 29;
    pub const FUTEX: SyscallNumber = 98;
    pub const SET_ROBUST_LIST: SyscallNumber = 99;
    pub const NANOSLEEP: SyscallNumber = 101;
    pub const CLOCK_GETTIME: SyscallNumber = 113;
    pub const SCHED_GETAFFINITY: SyscallNumber = 123;
    pub const SIGALTSTACK: SyscallNumber = 132;
    pub const RT_SIGACTION: SyscallNumber = 134;
    pub const RT_SIGPROCMASK: SyscallNumber = 135;
    pub const SET_TID_ADDRESS: SyscallNumber = 96;
    pub const MPROTECT: SyscallNumber = 226;
    pub const MADVISE: SyscallNumber = 233;
    pub const PRLIMIT64: SyscallNumber = 261;
    pub const GETRANDOM: SyscallNumber = 278;
    pub const TGKILL: SyscallNumber = 131;
    pub const EXIT_GROUP: SyscallNumber = 94;
    pub const RSEQ: SyscallNumber = 293;
    pub const MEMBARRIER: SyscallNumber = 283;
    pub const OPENAT: SyscallNumber = 56;
    pub const CLOSE: SyscallNumber = 57;
    pub const READ: SyscallNumber = 63;
    pub const FCNTL: SyscallNumber = 25;
    pub const FSTAT: SyscallNumber = 80;
    pub const NEWFSTATAT: SyscallNumber = 79;
    pub const READLINKAT: SyscallNumber = 78;
    pub const FACCESSAT: SyscallNumber = 48;
    pub const STATX: SyscallNumber = 291;
    pub const PPOLL: SyscallNumber = 73;
    pub const GETPID: SyscallNumber = 172;
    pub const GETTID: SyscallNumber = 178;
    pub const GETRUSAGE: SyscallNumber = 165;
    pub const SYSINFO: SyscallNumber = 179;
    pub const SCHED_YIELD: SyscallNumber = 124;
}

fn handle_by_number(
    sysnum: sel4_linux_syscall_types::SyscallNumber,
    mut args: VaListAsSyscallArgs,
) -> SyscallReturnValue {
    use sel4_linux_syscall_types::SyscallArgs;
    match sysnum {
        nr::SET_TID_ADDRESS
        | nr::SET_ROBUST_LIST
        | nr::RT_SIGACTION
        | nr::RT_SIGPROCMASK
        | nr::SIGALTSTACK
        | nr::IOCTL
        | nr::MPROTECT
        | nr::MADVISE
        | nr::PRLIMIT64
        | nr::SCHED_GETAFFINITY
        | nr::RSEQ
        | nr::MEMBARRIER
        | nr::TGKILL
        | nr::NANOSLEEP => 0,
        nr::FUTEX => 0,
        nr::GETPID | nr::GETTID => 1,
        nr::SCHED_YIELD | nr::PPOLL | nr::GETRUSAGE | nr::SYSINFO => 0,
        nr::OPENAT => {
            let _dirfd: usize = args.next_arg().unwrap_or(0);
            let path_ptr: *const u8 = args.next_arg::<usize>().unwrap_or(0) as *const u8;
            if path_is(path_ptr, b"/dev/urandom") || path_is(path_ptr, b"/dev/random") {
                URANDOM_FD
            } else {
                -ENOENT
            }
        }
        nr::FACCESSAT | nr::READLINKAT | nr::STATX | nr::NEWFSTATAT => -ENOENT,
        nr::CLOSE | nr::FCNTL => 0,
        nr::READ => {
            let fd: SyscallReturnValue =
                args.next_arg::<usize>().unwrap_or(0) as SyscallReturnValue;
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let count: usize = args.next_arg().unwrap_or(0);
            if fd == URANDOM_FD && !buf.is_null() {
                for i in 0..count {
                    unsafe { buf.add(i).write(0) };
                }
                count as SyscallReturnValue
            } else {
                0
            }
        }
        nr::FSTAT => -EBADF,
        nr::CLOCK_GETTIME => {
            let _clockid: usize = args.next_arg().unwrap_or(0);
            let ts: *mut u64 = args.next_arg::<usize>().unwrap_or(0) as *mut u64;
            if !ts.is_null() {
                unsafe {
                    ts.write(0);
                    ts.add(1).write(0);
                }
            }
            0
        }
        nr::GETRANDOM => {
            let buf: *mut u8 = args.next_arg::<usize>().unwrap_or(0) as *mut u8;
            let len: usize = args.next_arg().unwrap_or(0);
            if !buf.is_null() {
                for i in 0..len {
                    unsafe { buf.add(i).write(0) };
                }
            }
            len as SyscallReturnValue
        }
        nr::EXIT_GROUP => {
            debug_println!("[executor]   (libc exit_group during/after the turn — parking)");
            sel4::init_thread::suspend_self()
        }
        other => {
            debug_println!("[executor]   UNHANDLED SYSCALL number {other} (a precise wall)");
            -ENOSYS
        }
    }
}

fn handle_known_syscall(syscall: Syscall) -> SyscallReturnValue {
    use Syscall::*;
    match syscall {
        Getuid | Geteuid | Getgid | Getegid => 0,
        Brk { addr } => {
            let bounds = BRK_HEAP.bounds();
            (if addr.is_null() {
                bounds.start()
            } else if (bounds.start()..bounds.end()).contains(&addr.cast()) {
                addr.cast()
            } else {
                ptr::null()
            }) as SyscallReturnValue
        }
        Mmap {
            addr: _,
            len,
            prot: _,
            flag,
            fd: _,
            offset: _,
        } => {
            if flag & MAP_ANONYMOUS != 0 {
                (unsafe { MMAP_DLMALLOC.alloc(Layout::from_size_align(len, 4096).unwrap()) })
                    as SyscallReturnValue
            } else {
                -ENOMEM
            }
        }
        Lseek { fd, offset, whence } => {
            assert!(whence == SEEK_CUR);
            assert!(offset == 0);
            assert!((0..=2).contains(&fd));
            0
        }
        Write { fd, buf, count } => {
            assert!(fd == 1 || fd == 2);
            for i in 0..(count as isize) {
                let c: c_char = unsafe { *buf.offset(i) };
                debug_print!("{}", c as u8 as char);
            }
            count as SyscallReturnValue
        }
        Writev { fd, iov, iovcnt } => {
            assert!(fd == 1 || fd == 2);
            let mut ret: isize = 0;
            for i in 0..(iovcnt as isize) {
                let iov = unsafe { &*iov.offset(i) };
                for j in 0..(iov.iov_len as isize) {
                    let c: u8 = unsafe { *(iov.iov_base as *const u8).offset(j) };
                    debug_print!("{}", c as char);
                    ret += 1;
                }
            }
            ret as SyscallReturnValue
        }
        other => {
            debug_println!("[executor]   UNHANDLED SYSCALL (a precise wall): {other:?}");
            -ENOSYS
        }
    }
}

// The brk heap and the mmap pool — the Lean runtime + one transfer turn fit in a
// few MiB (the host-musl run's RSS is modest). These are static PD memory (BSS
// in the PD's own frames), so they directly inflate the initial-task footprint
// the seL4 loader must place; sized to the turn's real need (48 MiB GC arena),
// not generously, to keep the embedded image small.
static BRK_HEAP: StaticHeap<{ 4 * 1024 * 1024 }> = StaticHeap::new();

const MMAP_HEAP_SIZE: usize = 48 * 1024 * 1024;
static MMAP_HEAP: StaticHeap<MMAP_HEAP_SIZE> = StaticHeap::new();
static MMAP_DLMALLOC: StaticDlmalloc<RawOneShotMutex> = StaticDlmalloc::new(MMAP_HEAP.bounds());

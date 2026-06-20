//! Real seL4 thread bring-up for the render-PD — servicing the musl `__clone`
//! by materializing a second seL4 TCB.
//!
//! ## Why this module exists (the measured wall)
//!
//! lavapipe's `lvp_queue_init` UNCONDITIONALLY calls `vk_queue_enable_submit_thread`
//! → `thrd_create` → `pthread_create` → the seL4-musl `__clone`. The seL4/musllibc
//! fork's `__clone` for the `aarch64_sel4` ARCH is a STUB that returns `-ENOSYS`
//! (`mov w0, #-38; ret`) WITHOUT issuing any syscall — so it never even reaches the
//! `__sysinfo` syscall handler. That `-ENOSYS` surfaces as `thrd_error` →
//! `vkCreateDevice = VK_ERROR_UNKNOWN` (-13). The render stalls there.
//!
//! The lever (WIRING.md "THE NEXT OS DEMAND"): replace that stub with a real
//! `__clone` that creates a second seL4 thread. We do it the executor-PD-class way —
//! a TCB retyped from one of the root task's untyped caps, SHARING the root task's
//! CSpace + VSpace (a thread, not a process), with a fresh stack and its own IPC
//! buffer frame, scheduled by seL4. Mirrors the upstream
//! `crates/examples/root-task/spawn-thread` precedent, adapted to the
//! `sel4-root-task-with-std` profile and driven from the `__clone` ABI.
//!
//! ## The `__clone` ABI we service
//!
//! musl's `clone(3)` C wrapper walks its varargs and tail-calls the arch asm
//! `__clone(fn, child_stack, flags, arg, ptid, tls, ctid)` (x0..x6):
//!   * x0 `fn`    — `int (*)(void *)`, the thread entry (musl's `start`/`start_c11`).
//!   * x1 `stack` — the TOP of the child stack (musl already reserved + aligned it).
//!   * x2 `flags` — CLONE_VM|CLONE_FS|... (we share VM/CSpace unconditionally).
//!   * x3 `arg`   — the single `void *` handed to `fn` (the `pthread`/`thrd` self).
//!   * x4 `ptid`  — parent-tid futex slot (set-tid; we just zero it, single PD).
//!   * x5 `tls`   — the new thread's TPIDR_EL0 value (musl's `TP_ADJ(self)`). MUST
//!                  be installed or `__pthread_self` (reads tpidr_el0) is wrong.
//!   * x6 `ctid`  — child-tid futex slot.
//!
//! Our `__clone` (Rust `dregg_clone`, called from musl-compat.c) materializes a TCB
//! whose registers are `pc=trampoline`, `sp=stack`, `x0=fn`, `x1=arg`,
//! `tpidr_el0=tls`, resumes it, and returns a positive synthetic tid. The
//! trampoline installs the child's own IPC buffer (so its later seL4 invocations
//! work) and its self-TCB cap (so `exit` can suspend IT, not the main thread), then
//! tail-calls `fn(arg)`. When the thread runs `__pthread_exit` it issues `exit`
//! (syscall 93) through `__sysinfo`; the handler (main.rs) suspends the calling TCB.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicUsize, Ordering};

use sel4::{
    CNodeCapData, CapTypeForObjectOfFixedSize, FrameObjectType, UserContext, cap, cap_type,
    init_thread,
};

/// GRANULE (4 KiB) — the IPC-buffer frame size.
const GRANULE: usize = FrameObjectType::GRANULE.bytes();

/// The maximum number of secondary threads we can materialize. lavapipe's headless
/// single-frame render spawns exactly one (the Vulkan submit thread); a handful of
/// headroom costs only static frames + CSpace slots.
const MAX_THREADS: usize = 8;

// ───────────────────────── the object allocator ─────────────────────────────
//
// Captured from BootInfo in `main` (the same shape as the spawn-thread example):
// the largest non-device untyped (to retype TCBs from) + the empty CSpace slot
// range (to place the new caps). The render-PD's CSpace is the init thread's
// (ROOT_CNODE_SIZE_BITS=19 — ample slots), shared with the new threads.

struct ThreadSpawner {
    /// The untyped we retype TCBs out of.
    untyped: cap::Untyped,
    /// The next free CSpace slot index in the init-thread CNode.
    next_slot: AtomicUsize,
    /// One-past-the-last free slot.
    last_slot: usize,
    /// How many secondary threads have been spawned (index into the static pools).
    spawned: AtomicUsize,
}

// SAFETY: the spawner is only mutated through atomics; the cap handles are Copy
// plain words. Single-core PD, accessed under the syscall-handler serialization.
unsafe impl Sync for ThreadSpawner {}

/// The process-wide spawner, installed by `init` before the lavapipe driver runs.
/// `None` until `init`; `dregg_clone` errors (-ENOSYS) if it is somehow reached
/// first (it cannot be: `init` runs in `main` before `dregg_render_pd_run`).
static SPAWNER: SpawnerCell = SpawnerCell(UnsafeCell::new(None));

struct SpawnerCell(UnsafeCell<Option<ThreadSpawner>>);
unsafe impl Sync for SpawnerCell {}

// ───────────────────────── the per-thread static frames ─────────────────────
//
// Each secondary thread needs (a) a stack and (b) an IPC-buffer frame whose cap we
// resolve from the user-image frames (it lives in this image, so the kernel already
// has a Granule cap for it). We pre-reserve MAX_THREADS of each as page-aligned
// statics in the image. The stack musl passes (`child_stack`) is the thread's real
// stack; this in-image stack is a fallback the trampoline does not need (musl owns
// the stack), but the IPC-buffer frame MUST be a real mapped page in the image.

#[repr(C, align(4096))]
struct Granule([u8; GRANULE]);

/// IPC-buffer frames for the secondary threads (in the user image → caps resolvable
/// via `bootinfo.user_image_frames()`).
static mut IPC_FRAMES: [Granule; MAX_THREADS] = {
    const Z: Granule = Granule([0u8; GRANULE]);
    [Z; MAX_THREADS]
};

/// Each spawned thread's own TCB cap, so the `exit` syscall handler can suspend the
/// CALLING thread (not the main thread). Indexed by the synthetic tid-1.
static THREAD_TCBS: [AtomicUsize; MAX_THREADS] =
    [const { AtomicUsize::new(0) }; MAX_THREADS];

/// Each spawned thread's IPC-buffer vaddr (for the trampoline's `set_ipc_buffer`).
static THREAD_IPC_PTRS: [AtomicUsize; MAX_THREADS] =
    [const { AtomicUsize::new(0) }; MAX_THREADS];

/// Each spawned thread's TLS pointer (TPIDR_EL0 value). We identify the CALLING
/// thread at `exit` time by reading TPIDR_EL0 and matching it here — avoiding a
/// `#[thread_local]` (which would depend on std's per-thread TLS init for threads
/// std does not know about). The main thread's TPIDR_EL0 matches none of these, so
/// it falls through to the whole-PD park.
static THREAD_TLS_PTRS: [AtomicUsize; MAX_THREADS] =
    [const { AtomicUsize::new(0) }; MAX_THREADS];

// ───────────────────────── init (called from main) ──────────────────────────

unsafe extern "C" {
    /// Set `__libc.can_do_threads = __libc.threaded = 1` (musl-compat.c). musl's
    /// `__pthread_create` returns -ENOSYS until this flag is set; the seL4 std
    /// runtime never runs the musl startup that would set it.
    fn dregg_enable_musl_threads();
}

/// Capture the untyped + empty-slot range from BootInfo so `dregg_clone` can
/// materialize TCBs. Call ONCE in `main`, before driving lavapipe.
pub fn init(bootinfo: &'static sel4::BootInfo) {
    // Ungate musl threads so pthread_create reaches our TCB-backed __clone.
    unsafe { dregg_enable_musl_threads() };

    let untyped = find_largest_kernel_untyped(bootinfo);
    let empty = bootinfo.empty().range();
    let spawner = ThreadSpawner {
        untyped,
        next_slot: AtomicUsize::new(empty.start),
        last_slot: empty.end,
        spawned: AtomicUsize::new(0),
    };
    unsafe {
        *SPAWNER.0.get() = Some(spawner);
        *BOOTINFO_PTR.0.get() = Some(bootinfo as *const sel4::BootInfo);
    }
}

fn find_largest_kernel_untyped(bootinfo: &sel4::BootInfo) -> cap::Untyped {
    let (ut_ix, _desc) = bootinfo
        .untyped_list()
        .iter()
        .enumerate()
        .filter(|(_i, desc)| !desc.is_device())
        .max_by_key(|(_i, desc)| desc.size_bits())
        .unwrap();
    bootinfo.untyped().index(ut_ix).cap()
}

fn spawner() -> Option<&'static ThreadSpawner> {
    unsafe { (*SPAWNER.0.get()).as_ref() }
}

fn alloc_slot(s: &ThreadSpawner) -> Option<usize> {
    let ix = s.next_slot.fetch_add(1, Ordering::AcqRel);
    if ix >= s.last_slot { None } else { Some(ix) }
}

/// Resolve the user-image Granule cap that maps `addr` (which must lie within this
/// root task's loaded image — true for our static `IPC_FRAMES`).
fn user_image_frame(bootinfo: &sel4::BootInfo, addr: usize) -> init_thread::Slot<cap_type::Granule> {
    unsafe extern "C" {
        static __executable_start: usize;
    }
    let image_base = core::ptr::addr_of!(__executable_start) as usize;
    bootinfo
        .user_image_frames()
        .index(addr / GRANULE - image_base / GRANULE)
}

// ───────────────────────── the __clone service ──────────────────────────────

/// The render-PD `__clone`, called from `musl-compat.c`'s `__clone` shim (which
/// overrides the seL4 musl stub via `--whole-archive` link precedence). Returns a
/// positive synthetic tid on success, or a negative errno on failure (matching the
/// musl asm `__clone` contract: the C `clone` wrapper passes our return to
/// `__syscall_ret`).
///
/// SAFETY: called with the musl `__clone` register ABI; `fn_`/`stack`/`arg` are the
/// thread entry, child stack top, and the entry's single argument.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn dregg_clone(
    fn_: usize,
    stack: usize,
    _flags: usize,
    arg: usize,
    _ptid: usize,
    tls: usize,
    _ctid: usize,
) -> isize {
    let Some(s) = spawner() else {
        sel4::debug_println!("[render-pd] dregg_clone: spawner not initialized");
        return -38; // -ENOSYS: init never ran (cannot happen via the real path)
    };

    let idx = s.spawned.fetch_add(1, Ordering::AcqRel);
    if idx >= MAX_THREADS {
        sel4::debug_println!("[render-pd] __clone: thread pool exhausted ({MAX_THREADS})");
        return -11; // -EAGAIN
    }

    // The BootInfo is reachable via the init-thread machinery; we re-derive the
    // user-image frame cap for this thread's IPC buffer from the captured bootinfo
    // pointer stashed at init. We pass the bootinfo down through a static.
    let bootinfo = unsafe { (*BOOTINFO_PTR.0.get()).expect("thread::init not called") };
    let bootinfo: &sel4::BootInfo = unsafe { &*bootinfo };

    // (1) Retype a TCB from the untyped into a fresh CSpace slot.
    let Some(tcb_slot) = alloc_slot(s) else {
        sel4::debug_println!("[render-pd] __clone: out of CSpace slots");
        return -11;
    };
    if s.untyped
        .untyped_retype(
            &<cap_type::Tcb as CapTypeForObjectOfFixedSize>::object_blueprint(),
            &init_thread::slot::CNODE.cap().absolute_cptr_for_self(),
            tcb_slot,
            1,
        )
        .is_err()
    {
        sel4::debug_println!("[render-pd] __clone: TCB retype failed");
        return -12; // -ENOMEM
    }
    let tcb: cap::Tcb = init_thread::Slot::from_index(tcb_slot).downcast::<cap_type::Tcb>().cap();

    // (2) This thread's IPC-buffer frame (a static in the image → cap from bootinfo).
    let ipc_vaddr = core::ptr::addr_of!(IPC_FRAMES[idx]) as usize;
    let ipc_frame = user_image_frame(bootinfo, ipc_vaddr).cap();

    // (3) Configure the TCB: SHARE the init thread's CSpace + VSpace (a thread of
    //     this PD, not a new address space), with this thread's IPC buffer. No
    //     fault endpoint (a fault → the kernel suspends the thread; we read it on
    //     the serial via the kernel's fault message — acceptable for bring-up).
    if tcb
        .tcb_configure(
            init_thread::slot::NULL.cptr(),
            init_thread::slot::CNODE.cap(),
            CNodeCapData::new(0, 0),
            init_thread::slot::VSPACE.cap(),
            ipc_vaddr as sel4::Word,
            ipc_frame,
        )
        .is_err()
    {
        sel4::debug_println!("[render-pd] __clone: tcb_configure failed");
        return -12;
    }

    // (4) Record this thread's self-TCB cap + IPC vaddr + tls so the trampoline and
    //     the exit handler can find them. Synthetic tid = idx + 2 (main = 1).
    let tid = idx + 2;
    THREAD_TCBS[idx].store(tcb.cptr().bits() as usize, Ordering::Release);
    THREAD_IPC_PTRS[idx].store(ipc_vaddr, Ordering::Release);
    THREAD_TLS_PTRS[idx].store(tls, Ordering::Release);

    // (5) Registers: pc=trampoline, sp=stack, x0=fn, x1=arg, x2=idx, tpidr_el0=tls.
    let mut ctx = UserContext::default();
    *ctx.pc_mut() = thread_trampoline as *const () as usize as sel4::Word;
    *ctx.sp_mut() = (stack as sel4::Word) & !0xf; // 16-byte align (AAPCS64)
    *ctx.gpr_mut(0) = fn_ as sel4::Word;
    *ctx.gpr_mut(1) = arg as sel4::Word;
    *ctx.gpr_mut(2) = idx as sel4::Word;
    *ctx.gpr_mut(3) = tid as sel4::Word;
    ctx.inner_mut().tpidr_el0 = tls as sel4::Word;

    // (6) Priority: BELOW the init/main thread. On this single-core, non-MCS,
    //     priority-preemptive config a same-priority second thread would round-robin
    //     with main and (with our no-op futex) busy-spin the lavapipe submit loop,
    //     racing main's heap allocations during the synchronous JIT. A lower
    //     priority makes the submit thread run ONLY when main blocks (which, for the
    //     synchronous headless single-frame render, is at teardown) — no race, and
    //     the submit thread still exists so vkCreateDevice succeeds.
    let _ = tcb.tcb_set_priority(init_thread::slot::TCB.cap(), 100);

    // (7) Write all registers AND resume.
    if tcb.tcb_write_all_registers(true, &mut ctx).is_err() {
        sel4::debug_println!("[render-pd] __clone: write_registers/resume failed");
        return -12;
    }

    sel4::debug_println!(
        "[render-pd] __clone -> seL4 TCB #{tid} live (fn={fn_:#x} stack={stack:#x} tls={tls:#x})"
    );
    tid as isize
}

/// The new thread starts here (NOT directly at musl's `fn`): install this thread's
/// IPC buffer, then tail-call `fn(arg)`. x0=fn, x1=arg, x2=idx, x3=tid (set by
/// `dregg_clone`).
unsafe extern "C" fn thread_trampoline(fn_: usize, arg: usize, idx: usize, _tid: usize) -> ! {
    // (a) Install this thread's IPC buffer so its later seL4 invocations (e.g. the
    //     `exit`-driven self-suspend) have a buffer. The frame is mapped at the
    //     vaddr we configured the TCB with. The IPC-buffer state is thread-local
    //     (keyed by this thread's TPIDR_EL0, set in the registers), so this only
    //     affects THIS thread.
    let ipc_ptr = THREAD_IPC_PTRS[idx].load(Ordering::Acquire) as *mut sel4::IpcBuffer;
    unsafe {
        sel4::set_ipc_buffer(&mut *ipc_ptr);
    }

    // (b) Tail-call the musl thread entry. It runs the queue submit loop and, on
    //     thread teardown, issues `exit` (syscall 93) which the handler routes to
    //     `suspend_current_thread`.
    let entry: extern "C" fn(usize) -> ! = unsafe { core::mem::transmute(fn_) };
    entry(arg)
}

/// Read this thread's TPIDR_EL0 (its TLS pointer) — the per-thread identity we use
/// to find which secondary thread is calling `exit`.
#[inline]
fn read_tpidr_el0() -> usize {
    let v: usize;
    unsafe {
        core::arch::asm!("mrs {}, tpidr_el0", out(reg) v, options(nomem, nostack, preserves_flags));
    }
    v
}

/// Called by the `exit` (syscall 93) handler: suspend the CALLING seL4 thread. We
/// identify it by matching TPIDR_EL0 against the recorded secondary-thread TLS
/// pointers. The main thread (its TLS matches none) falls through to parking the
/// whole PD (its `exit` is the process exit).
pub fn suspend_current_thread() -> ! {
    let tp = read_tpidr_el0();
    let n = MAX_THREADS;
    for idx in 0..n {
        let tls = THREAD_TLS_PTRS[idx].load(Ordering::Acquire);
        if tls != 0 && tls == tp {
            let bits = THREAD_TCBS[idx].load(Ordering::Acquire);
            if bits != 0 {
                // Reconstruct the self-TCB cap and suspend it. After suspend the
                // thread never runs again; the static frames are not reclaimed,
                // correct for a submit thread that only tears down at PD shutdown.
                let tcb: cap::Tcb =
                    sel4::CPtr::from_bits(bits as sel4::Word).cast::<cap_type::Tcb>();
                let _ = tcb.tcb_suspend();
            }
            break;
        }
    }
    // main thread or a missing cap: park.
    init_thread::suspend_self()
}

// ───────────────────────── bootinfo stash ───────────────────────────────────
//
// `dregg_clone` is reached from C (no bootinfo arg), so stash the bootinfo pointer
// at init for the IPC-frame cap resolution.

static BOOTINFO_PTR: BootInfoCell = BootInfoCell(UnsafeCell::new(None));
struct BootInfoCell(UnsafeCell<Option<*const sel4::BootInfo>>);
unsafe impl Sync for BootInfoCell {}

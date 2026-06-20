// musl-compat.c — the handful of libc symbols the lean seL4/musllibc fork
// (`aarch64_sel4` ARCH) lacks but Mesa + LLVM reference at link time. Each is a
// faithful, minimal definition; none changes the render path's behaviour.
//
// Provided here (not patched into the musl) so the render-PD link is reproducible
// against the stock seL4 musl substrate executor-rootserver provisions.
//
//   * secure_getenv     — a GNU extension Mesa's env helpers reach for. With no
//                         setuid/setgid in a single seL4 PD, it is exactly getenv.
//   * qsort_r           — the reentrant qsort variant (NIR/util sort). The seL4
//                         musl ships qsort but not qsort_r; implement it on top
//                         of qsort via a thread-local trampoline (single-threaded
//                         PD ⇒ a plain static is safe).
//   * c23_timespec_get  — the C23-named timespec_get the newer libstdc++/Mesa
//                         reference; forward to the deterministic clock (the PD's
//                         clock_gettime is zeroed — time is not load-bearing for
//                         the offscreen render).
//   * __syscall_cp_asm / __cp_begin / __cp_end / __cp_cancel — musl's pthread
//                         cancellation-point machinery. The `aarch64_sel4` ARCH
//                         omits the defining asm, yet `pthread_cancel.o` (pulled
//                         transitively) references them. With LP_NUM_THREADS=0
//                         lavapipe spawns NO threads and cancels nothing, so the
//                         cancellation path is dead: __syscall_cp_asm forwards to
//                         the plain syscall, and the __cp_* markers are no-ops.

#include <stddef.h>

// ── getenv (THE single-thread lever) ─────────────────────────────────────────
// This minimal seL4 root task has a NULL `__environ`, so the libc getenv returns
// NULL for everything and `std::env::set_var` faults touching `environ` before
// main. We define getenv HERE (whole-archived ⇒ chosen over the libc's
// `getenv.o`, which lld then never pulls): a tiny in-image env table. It pins
// LP_NUM_THREADS=0 (single-threaded llvmpipe: no thrd_create, no rasterizer pool
// — the fix for `vkCreateDevice = VK_ERROR_UNKNOWN` on this single-core PD) and
// the software-driver selectors. Any other key → NULL (unset), the headless
// default. No `environ` is touched.
static int str_eq(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return *a == *b;
}
char *getenv(const char *name) {
    if (!name) return NULL;
    static char zero[]      = "0";
    static char llvmpipe[]  = "llvmpipe";
    static char one[]       = "1";
    if (str_eq(name, "LP_NUM_THREADS"))       return zero;
    if (str_eq(name, "GALLIUM_DRIVER"))       return llvmpipe;
    if (str_eq(name, "LIBGL_ALWAYS_SOFTWARE")) return one;
    return NULL;
}

// ── secure_getenv ────────────────────────────────────────────────────────────
char *secure_getenv(const char *name) {
    return getenv(name);
}

// ── qsort_r ──────────────────────────────────────────────────────────────────
extern void qsort(void *base, size_t nmemb, size_t size,
                  int (*compar)(const void *, const void *));

// Single-threaded PD: a static carries the user comparator + context across the
// plain-qsort call. (No reentrancy hazard — the PD's rasterizer is single-threaded
// with LP_NUM_THREADS=0.)
static int (*g_qsort_r_cmp)(const void *, const void *, void *);
static void *g_qsort_r_ctx;

static int qsort_r_trampoline(const void *a, const void *b) {
    return g_qsort_r_cmp(a, b, g_qsort_r_ctx);
}

void qsort_r(void *base, size_t nmemb, size_t size,
             int (*compar)(const void *, const void *, void *), void *arg) {
    g_qsort_r_cmp = compar;
    g_qsort_r_ctx = arg;
    qsort(base, nmemb, size, qsort_r_trampoline);
}

// ── c23_timespec_get ─────────────────────────────────────────────────────────
// The C23-named entry the newer toolchain emits; forward to the libc timespec_get
// the seL4 musl provides (which reads the PD's zeroed clock — deterministic).
struct timespec; // opaque; the libc timespec_get takes (struct timespec*, int)
extern int timespec_get(struct timespec *ts, int base);
int c23_timespec_get(struct timespec *ts, int base) {
    return timespec_get(ts, base);
}

// ── pthread cancellation-point machinery (dead with LP_NUM_THREADS=0) ─────────
// The musl ABI: long __syscall_cp_asm(volatile int *cancel, long n, long a..f).
// With no cancellation, it is the plain syscall. __syscall is the seL4 musl's
// C-level syscall (routes via __sysinfo, NOT a direct svc).
extern long __syscall(long n, ...);

long __syscall_cp_asm(volatile int *cancel, long n,
                      long a, long b, long c, long d, long e, long f) {
    (void)cancel;
    return __syscall(n, a, b, c, d, e, f);
}

// The __cp_begin/__cp_end/__cp_cancel markers are address labels musl's
// cancellation asm compares the trap PC against. With the forwarding
// __syscall_cp_asm above (which never traps a cancellable point), they are never
// consulted; define them as distinct addresses so the references resolve.
__attribute__((used)) void __cp_begin(void) {}
__attribute__((used)) void __cp_end(void) {}
__attribute__((used)) void __cp_cancel(void) {}

// ── getrandom ────────────────────────────────────────────────────────────────
// The libc wrapper the leaner seL4 musl omits. Issue the raw syscall (#278 on
// aarch64); the PD's syscall handler zero-fills deterministically — fine, the
// offscreen render's randomness is not load-bearing.
#ifndef SYS_getrandom
#define SYS_getrandom 278
#endif
long getrandom(void *buf, size_t buflen, unsigned int flags) {
    return __syscall(SYS_getrandom, (long)buf, (long)buflen, (long)flags);
}

// ── memfd_create ─────────────────────────────────────────────────────────────
// Mesa's shader-cache / scratch paths reach for an anonymous memory fd. The PD
// has no filesystem, so report ENOSYS (-1, errno=38) — Mesa falls back to an
// ordinary anonymous mmap (which our handler serves), the headless-correct path.
extern int *__errno_location(void);
int memfd_create(const char *name, unsigned int flags) {
    (void)name; (void)flags;
    *__errno_location() = 38; // ENOSYS
    return -1;
}

// ── reallocarray ─────────────────────────────────────────────────────────────
// realloc(ptr, nmemb*size) with multiplication-overflow protection (the BSD/glibc
// extension util/ code uses). The seL4 musl ships realloc but not this wrapper.
extern void *realloc(void *ptr, size_t size);
void *reallocarray(void *ptr, size_t nmemb, size_t size) {
    if (size != 0 && nmemb > (size_t)-1 / size) {
        *__errno_location() = 12; // ENOMEM
        return NULL;
    }
    return realloc(ptr, nmemb * size);
}

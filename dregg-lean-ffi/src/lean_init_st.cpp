/* lean_init_st.cpp — the SINGLE-THREADED, IO-thread-free Lean runtime init.
 *
 * THE EMBEDDABLE-LEAN-RUNTIME path (.docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md). The default
 * `dregg_ffi_init` enters lib.rs's shared coordinator, whose default prefix calls
 * `lean_initialize_runtime_module()`, which
 * runs the full init chain INCLUDING `initialize_libuv()`. On a multi-thread Lean
 * build that call spawns the **libuv event-loop thread** (libuv.cpp:
 * `lthread([]{ event_loop_run_loop(&global_ev); })`) — measured as a +1 OS thread
 * at init. A postgres backend is strictly single-threaded
 * (`pg-dregg/docs/PG-DREGG-TIER-D-SPIKE.md` §4.2), so that background thread is a
 * blocker for hosting the executor IN the backend.
 *
 * The fix is the HOST analogue of the seL4 executor-PD's libuv excision
 * (`sel4/dregg-pd/executor-pd/scripts/build-leanrt-elf.sh`, which patches
 * `init_module.cpp` to drop `initialize_libuv()`): here we simply DO NOT call
 * `lean_initialize_runtime_module()` at all. Instead we call the eight individual
 * `lean::initialize_*` initializers directly (each is an exported, linkable symbol
 * in its own `libleanrt.a` member), in the SAME order `init_module.cpp` uses, but
 * OMITTING `initialize_libuv()`. Because we never reference
 * `lean_initialize_runtime_module`, the linker never pulls `init_module.cpp.o`,
 * which is the only thing that references `initialize_libuv` / `libuv.cpp.o` — so
 * the event-loop thread is never even linked in.
 *
 * SOUNDNESS: the pure executor turn (`dregg_exec_full_forest_auth` =
 * `execFullForestG` + admission) performs NO socket/file/timer IO (it is a
 * deterministic fold over the wire). It needs the IO-MONAD CORE (`initialize_io`,
 * which is libuv-free — heartbeats, the mono clock, `lean_io_mark_end_initialization`)
 * but NONE of the libuv event loop. The verified closure references no libuv symbol
 * (confirmed by `nm`), and the executor never calls `lean_init_task_manager`, so the
 * task manager stays `nullptr` and `Task.spawn` runs inline (object.cpp:
 * `lean_task_spawn_core`: `if (!g_task_manager) return lean_task_pure(apply_1(...))`).
 * The result is a runtime that, in this process, spawns ZERO threads of its own.
 *
 * This file is compiled by build.rs (alongside lean_init.c) only when the linked
 * archive is present. Runtime and module phases are private helpers; the public
 * default/ST init ABI shares one mode-owning coordinator in lib.rs.
 */
#include <lean/lean.h>
#include "lean_init_internal.h"
#include <time.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>

/* SHARED-vs-STATIC linkage (DREGG_LEAN_SHARED, set by build.rs in
 * `DREGG_LEAN_LINK=shared` mode — the cdylib path, e.g. the pgrx extension):
 *
 *   * STATIC (the host probe + the standalone node): `libleanrt.a` is linked, so the
 *     eight individual `lean::initialize_*` C++ symbols are available. We call them
 *     directly and OMIT `initialize_libuv` → the libuv event-loop thread is never even
 *     linked (the true libuv-thread-free init, measured 2→2→2 by the embeddable probe).
 *
 *   * SHARED (the cdylib): `libleanshared` HIDES the individual `lean::initialize_*`
 *     symbols (and the runtime internals they use — mpz/utf8/heartbeat/…), exporting
 *     only the C-ABI `lean_initialize_runtime_module`. Supplying the hidden internals
 *     from a static `libleanrt.a` copy creates a SPLIT-BRAIN runtime (two copies of the
 *     runtime's global state) that SIGSEGVs in-process. So under shared linkage the ST
 *     init MUST route through the single exported `lean_initialize_runtime_module`
 *     (ONE runtime copy) — which DOES start the libuv thread. The shared-mode
 *     `dregg_ffi_init_st` is therefore single-RUNTIME but NOT libuv-thread-free; the
 *     libuv-free property is a STATIC-link property (.docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md §5).
 */
#ifndef DREGG_LEAN_SHARED
namespace lean {
/* The eight libuv-free initializers from init_module.cpp's chain (each defined in
 * its own runtime object: alloc/debug/object/io/thread/mutex/process/stack_overflow).
 * `initialize_libuv` is deliberately NOT declared or called. */
void initialize_alloc();
void initialize_debug();
void initialize_object();
void initialize_io();
void initialize_thread();
void initialize_mutex();
void initialize_process();
void initialize_stack_overflow();
}
#else
extern "C" {
/* The exported C-ABI full runtime init (libleanshared exports this; it runs the whole
 * init chain INCLUDING initialize_libuv). Used ONLY in shared mode — see the header. */
void lean_initialize_runtime_module(void);
}
#endif

/* The existing ST module set. It is deliberately tracked separately from the
 * default module list; ST success does not assert every default export is ready.
 * Each generated initializer is `extern "C"`
 * with C linkage (Lean's `@[export]` / `initialize_*` symbols are C-ABI). */
extern "C" {
lean_object *initialize_Dregg2_Dregg2_Exec_FFI(uint8_t builtin);
#ifdef DREGG_FINALIZE_GATE
lean_object *initialize_Dregg2_Dregg2_Distributed_FinalityGate(uint8_t builtin);
#endif
#ifdef DREGG_STRAND_ADMIT
lean_object *initialize_Dregg2_Dregg2_Distributed_StrandAdmission(uint8_t builtin);
#endif
#ifdef DREGG_ROUND_ADVANCE
lean_object *initialize_Dregg2_Dregg2_Distributed_RoundAdvanceGate(uint8_t builtin);
#endif
#ifdef DREGG_ACK_ADMIT
lean_object *initialize_Dregg2_Dregg2_Distributed_AckBeforeAdmit(uint8_t builtin);
#endif
#ifdef DREGG_DISTRIBUTED_EXPORTS
lean_object *initialize_Dregg2_Dregg2_Exec_DistributedExports(uint8_t builtin);
#endif
#ifdef DREGG_POA_SIGNAL_JUDGE
/* The PoA evaluator reads initialized Emit globals. Keep the single-threaded path at exact parity
 * with `dregg_ffi_init`; availability still confers no authority on caller-authored state. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkJudge(uint8_t builtin);
#endif
#ifdef DREGG_POA_NETWORK_GENESIS
/* Exact parity with the default initializer for the Lean-owned zero-head ceremony. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkGenesis(uint8_t builtin);
#endif
#ifdef DREGG_POA_RECORDS_PROJECT
/* Exact parity for the Records read model; it reaches the same evaluator globals. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_RecordsRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_SIGNAL_SLOT_DERIVE
/* ⚑ 2026-08-06 — THIS ENTRY WAS MISSING while `lean_init.c` had carried it since the derivation
 * landed, so the two initializer sites were ONE ENTRY OUT OF SYNC. On the single-threaded path the
 * module's initializer never ran, and a Lean module whose initializer never runs answers with an
 * uninitialized closure the first time it is called — on the scored-run PREPARATION path, i.e. a
 * silent refusal of every scored run rather than a loud one. Both sites are one edit now. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_SlotDeriveRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_STATION_DAILY_READ
/* Exact parity for the station daily read; it reaches the same evaluator globals. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_StationDailyRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_CRATE_OPEN
/* Exact parity for the station crate-open WRITE. Landed in the same edit as `lean_init.c`'s. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_StationCrateOpenRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_SIGNAL_FEEDBACK
/* ⚑ 2026-08-07 — THIS ENTRY WAS MISSING while `lean_init.c` had carried it since the mid-run
 * feedback oracle landed, so the two initializer sites were ONE ENTRY OUT OF SYNC for the SECOND
 * time (the first was `SlotDeriveRuntime`, noted below). The failure mode is identical and it is
 * silent: on the single-threaded path the module's initializer never runs, the export answers with
 * an uninitialized closure, and every mid-run LOCKED/DRIFT query refuses without saying why. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_SignalFeedbackRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_DARK_BAZAAR_JUDGE
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_DarkBazaarJudge(uint8_t builtin);
#endif
#ifdef DREGG_POA_GALLEY_DAILY_JUDGE
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_GalleyMaintenanceDailyRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_NIGHT_WATCH_CAMPAIGN_JUDGE
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_NightWatchCampaignWire(uint8_t builtin);
#endif
#if defined(DREGG_POA_CREW_FIELD_STEP) || defined(DREGG_POA_CREW_FIELD_SEAT_PREIMAGE)
/* Parity for the crew step surface. The `_str` bridge and the byte ceiling live only in
 * lean_init.c — that asymmetry is correct; INITIALIZER parity is what must hold, and this
 * file records two cases where it did not and every scored run silently refused. */
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_CrewFieldMissionAdmission(uint8_t builtin);
#endif
#if defined(DREGG_POA_EVENT_BATCH_RUNTIME_PLAN) || \
    defined(DREGG_POA_EVENT_BATCH_RUNTIME_INITIAL_HEADS_DIGEST)
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_EventBatchRuntime(uint8_t builtin);
#endif
#if defined(DREGG_POA_WORLD_ACTIVATION_JUDGE) || defined(DREGG_POA_WORLD_ACTIVATION_AUTHORIZES)
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_WorldActivation(uint8_t builtin);
#endif
#ifdef DREGG_POA_ACTIVATED_CONTENT_AUTHORIZE
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_ActivatedContentRuntime(uint8_t builtin);
#endif
#ifdef DREGG_POA_BAZAAR_RUNTIME
lean_object *initialize_Dregg2_Dregg2_Games_PathOfAngels_BazaarGameRuntime(uint8_t builtin);
#endif
}

/* The ST runtime prefix for the executor-in-a-constrained-host
 * path. STATIC linkage: libuv-thread-free (the eight initializers, no libuv). SHARED
 * linkage (the cdylib): single-runtime via the exported `lean_initialize_runtime_module`
 * (which starts the libuv thread — see the header note + .docs-history-noclaude/EMBEDDABLE-LEAN-RUNTIME.md §5).
 *
 * This is only the runtime prefix. The shared Rust coordinator owns mode
 * selection, idempotency, thread attachment, and sticky module failures. */
extern "C" void dregg_ffi_start_runtime_st(void) {
#ifndef DREGG_LEAN_SHARED
    /* STATIC: the libuv-free prefix of lean_initialize_runtime_module(), in order. */
    lean::initialize_alloc();
    lean::initialize_debug();
    lean::initialize_object();
    lean::initialize_io();      /* IO-MONAD CORE — libuv-free; the executor needs it */
    lean::initialize_thread();  /* thread-local reset fns only; spawns nothing */
    lean::initialize_mutex();
    lean::initialize_process();
    lean::initialize_stack_overflow();
    /* initialize_libuv() — DELIBERATELY OMITTED (the event-loop thread). */
#else
    /* SHARED: the single exported runtime init (one runtime copy; starts libuv). */
    lean_initialize_runtime_module();
#endif
}

/* Keep the existing ST module set; full default availability is not inferred from
 * ST success. Only the owning host thread may enter this mode. */
extern "C" int dregg_ffi_init_st_modules(void) {
    lean_object *res = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_FFI);
    if (!lean_io_result_is_ok(res)) {
        lean_io_result_show_error(res);
        lean_dec_ref(res);
        return 1;
    }
    lean_dec_ref(res);
#ifdef DREGG_FINALIZE_GATE
    {
        lean_object *gres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_FinalityGate);
        if (!lean_io_result_is_ok(gres)) { lean_io_result_show_error(gres); lean_dec_ref(gres); return 1; }
        lean_dec_ref(gres);
    }
#endif
#ifdef DREGG_STRAND_ADMIT
    {
        lean_object *ares = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_StrandAdmission);
        if (!lean_io_result_is_ok(ares)) { lean_io_result_show_error(ares); lean_dec_ref(ares); return 1; }
        lean_dec_ref(ares);
    }
#endif
#ifdef DREGG_ROUND_ADVANCE
    {
        lean_object *rres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_RoundAdvanceGate);
        if (!lean_io_result_is_ok(rres)) { lean_io_result_show_error(rres); lean_dec_ref(rres); return 1; }
        lean_dec_ref(rres);
    }
#endif
#ifdef DREGG_ACK_ADMIT
    {
        lean_object *kres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Distributed_AckBeforeAdmit);
        if (!lean_io_result_is_ok(kres)) { lean_io_result_show_error(kres); lean_dec_ref(kres); return 1; }
        lean_dec_ref(kres);
    }
#endif
#ifdef DREGG_DISTRIBUTED_EXPORTS
    {
        lean_object *dres = DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Exec_DistributedExports);
        if (!lean_io_result_is_ok(dres)) { lean_io_result_show_error(dres); lean_dec_ref(dres); return 1; }
        lean_dec_ref(dres);
    }
#endif
#ifdef DREGG_POA_SIGNAL_JUDGE
    {
        lean_object *poares =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkJudge);
        if (!lean_io_result_is_ok(poares)) {
            lean_io_result_show_error(poares);
            lean_dec_ref(poares);
            return 1;
        }
        lean_dec_ref(poares);
    }
#endif
#ifdef DREGG_POA_RECORDS_PROJECT
    {
        lean_object *poarecres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_RecordsRuntime);
        if (!lean_io_result_is_ok(poarecres)) {
            lean_io_result_show_error(poarecres);
            lean_dec_ref(poarecres);
            return 1;
        }
        lean_dec_ref(poarecres);
    }
#endif
#ifdef DREGG_POA_SIGNAL_SLOT_DERIVE
    {
        lean_object *slotderiveres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_SlotDeriveRuntime);
        if (!lean_io_result_is_ok(slotderiveres)) {
            lean_io_result_show_error(slotderiveres);
            lean_dec_ref(slotderiveres);
            return 1;
        }
        lean_dec_ref(slotderiveres);
    }
#endif
#ifdef DREGG_POA_STATION_DAILY_READ
    {
        lean_object *poastationres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_StationDailyRuntime);
        if (!lean_io_result_is_ok(poastationres)) {
            lean_io_result_show_error(poastationres);
            lean_dec_ref(poastationres);
            return 1;
        }
        lean_dec_ref(poastationres);
    }
#endif
#ifdef DREGG_POA_CRATE_OPEN
    {
        lean_object *poacrateres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_StationCrateOpenRuntime);
        if (!lean_io_result_is_ok(poacrateres)) {
            lean_io_result_show_error(poacrateres);
            lean_dec_ref(poacrateres);
            return 1;
        }
        lean_dec_ref(poacrateres);
    }
#endif
#ifdef DREGG_POA_SIGNAL_FEEDBACK
    {
        lean_object *feedbackres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_SignalFeedbackRuntime);
        if (!lean_io_result_is_ok(feedbackres)) {
            lean_io_result_show_error(feedbackres);
            lean_dec_ref(feedbackres);
            return 1;
        }
        lean_dec_ref(feedbackres);
    }
#endif
#ifdef DREGG_POA_NETWORK_GENESIS
    {
        lean_object *poagenres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_NetworkGenesis);
        if (!lean_io_result_is_ok(poagenres)) {
            lean_io_result_show_error(poagenres);
            lean_dec_ref(poagenres);
            return 1;
        }
        lean_dec_ref(poagenres);
    }
#endif
#ifdef DREGG_POA_DARK_BAZAAR_JUDGE
    {
        lean_object *bazaarres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_DarkBazaarJudge);
        if (!lean_io_result_is_ok(bazaarres)) {
            lean_io_result_show_error(bazaarres);
            lean_dec_ref(bazaarres);
            return 1;
        }
        lean_dec_ref(bazaarres);
    }
#endif
#ifdef DREGG_POA_GALLEY_DAILY_JUDGE
    {
        lean_object *galleyres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_GalleyMaintenanceDailyRuntime);
        if (!lean_io_result_is_ok(galleyres)) {
            lean_io_result_show_error(galleyres);
            lean_dec_ref(galleyres);
            return 1;
        }
        lean_dec_ref(galleyres);
    }
#endif
#ifdef DREGG_POA_NIGHT_WATCH_CAMPAIGN_JUDGE
    {
        lean_object *nightwatchres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_NightWatchCampaignWire);
        if (!lean_io_result_is_ok(nightwatchres)) {
            lean_io_result_show_error(nightwatchres);
            lean_dec_ref(nightwatchres);
            return 1;
        }
        lean_dec_ref(nightwatchres);
    }
#endif
#if defined(DREGG_POA_CREW_FIELD_STEP) || defined(DREGG_POA_CREW_FIELD_SEAT_PREIMAGE)
    {
        lean_object *crewfieldres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_CrewFieldMissionAdmission);
        if (!lean_io_result_is_ok(crewfieldres)) {
            lean_io_result_show_error(crewfieldres);
            lean_dec_ref(crewfieldres);
            return 1;
        }
        lean_dec_ref(crewfieldres);
    }
#endif
#if defined(DREGG_POA_EVENT_BATCH_RUNTIME_PLAN) || \
    defined(DREGG_POA_EVENT_BATCH_RUNTIME_INITIAL_HEADS_DIGEST)
    {
        lean_object *batchres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_EventBatchRuntime);
        if (!lean_io_result_is_ok(batchres)) {
            lean_io_result_show_error(batchres);
            lean_dec_ref(batchres);
            return 1;
        }
        lean_dec_ref(batchres);
    }
#endif
#if defined(DREGG_POA_WORLD_ACTIVATION_JUDGE) || defined(DREGG_POA_WORLD_ACTIVATION_AUTHORIZES)
    {
        lean_object *worldactivationres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_WorldActivation);
        if (!lean_io_result_is_ok(worldactivationres)) {
            lean_io_result_show_error(worldactivationres);
            lean_dec_ref(worldactivationres);
            return 1;
        }
        lean_dec_ref(worldactivationres);
    }
#endif
#ifdef DREGG_POA_ACTIVATED_CONTENT_AUTHORIZE
    {
        lean_object *activatedcontentres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_ActivatedContentRuntime);
        if (!lean_io_result_is_ok(activatedcontentres)) {
            lean_io_result_show_error(activatedcontentres);
            lean_dec_ref(activatedcontentres);
            return 1;
        }
        lean_dec_ref(activatedcontentres);
    }
#endif
#ifdef DREGG_POA_BAZAAR_RUNTIME
    {
        lean_object *bazaarpersistres =
            DREGG_INIT_MODULE(initialize_Dregg2_Dregg2_Games_PathOfAngels_BazaarGameRuntime);
        if (!lean_io_result_is_ok(bazaarpersistres)) {
            lean_io_result_show_error(bazaarpersistres);
            lean_dec_ref(bazaarpersistres);
            return 1;
        }
        lean_dec_ref(bazaarpersistres);
    }
#endif
    return 0;
}

/* Called only while the shared lifecycle lock is held. Generated module guards
 * are plain booleans and become true before dependencies finish; errors are
 * retained by Rust and are never retried. The name is a static string literal.
 * Timings are inclusive of the module's still-uninitialized import closure. */
static const char *dregg_failed_module = nullptr;

extern "C" const char *dregg_ffi_last_failed_module(void) {
    return dregg_failed_module;
}

extern "C" lean_object *dregg_ffi_run_module_init(
    const char *name, dregg_module_initializer init) {
    const char *profile_env = std::getenv("DREGG_LEAN_INIT_PROFILE");
    const bool profile = profile_env != nullptr && std::strcmp(profile_env, "1") == 0;
    struct timespec begin = {};
    const bool have_begin = profile && clock_gettime(CLOCK_MONOTONIC, &begin) == 0;
    if (profile) {
        std::fprintf(stderr, "[dregg lean init] module=%s begin\n", name);
        std::fflush(stderr);
    }
    lean_object *result = init(1);
    const bool ok = lean_io_result_is_ok(result);
    if (!ok && dregg_failed_module == nullptr) dregg_failed_module = name;
    if (profile) {
        struct timespec end = {};
        const bool have_end = clock_gettime(CLOCK_MONOTONIC, &end) == 0;
        if (have_begin && have_end) {
            const double milliseconds =
                (static_cast<double>(end.tv_sec) - static_cast<double>(begin.tv_sec)) * 1000.0 +
                (static_cast<double>(end.tv_nsec) - static_cast<double>(begin.tv_nsec)) / 1000000.0;
            std::fprintf(stderr, "[dregg lean init] module=%s elapsed_ms=%.3f result=%s\n",
                         name, milliseconds, ok ? "ok" : "error");
        } else {
            std::fprintf(stderr, "[dregg lean init] module=%s elapsed_ms=unavailable result=%s\n",
                         name, ok ? "ok" : "error");
        }
        std::fflush(stderr);
    }
    return result;
}

/* Built only with the lean-lib harness feature. Exercise a host thread created
 * outside Rust: the public init ABI must attach it before a real Lean call. */
#include <cstdint>
#include <cstdlib>
#include <pthread.h>

extern "C" int dregg_ffi_init(void);
extern "C" int dregg_ffi_init_st(void);
extern "C" std::uint64_t dregg_kernel_transfer_total(
    std::uint64_t a, std::uint64_t b, std::uint64_t amount);

struct native_init_request {
    int single_threaded;
    int result;
};

static void *run_native_init(void *opaque) {
    auto &request = *static_cast<native_init_request *>(opaque);
    const auto init = request.single_threaded ? dregg_ffi_init_st : dregg_ffi_init;
    request.result = init();
    if (request.result != 0) return nullptr;
    // Reentry must not reattach the same allocator or restart the runtime.
    request.result = init();
    if (request.result == 0 && dregg_kernel_transfer_total(100, 5, 30) != 105)
        request.result = -2;
    return nullptr;
}

extern "C" int dregg_ffi_test_foreign_thread(int single_threaded) {
    // Use the platform thread ABI. The Lean archive selects its C++ runtime;
    // std::thread from the host compiler can otherwise require a different ABI.
    native_init_request request{single_threaded, -1};
    pthread_t host;
    if (pthread_create(&host, nullptr, run_native_init, &request) != 0) return -3;
    // Owned secondary attachment finalizes at thread exit; the runtime owner does not.
    // A failed join cannot return while the worker may still hold &request.
    if (pthread_join(host, nullptr) != 0) std::abort();
    return request.result;
}

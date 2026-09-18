/* Built only with the lean-lib harness feature. Exercise a host thread created
 * outside Rust: the public init ABI must attach it before a real Lean call. */
#include <cstdint>
#include <thread>

extern "C" int dregg_ffi_init(void);
extern "C" int dregg_ffi_init_st(void);
extern "C" std::uint64_t dregg_kernel_transfer_total(
    std::uint64_t a, std::uint64_t b, std::uint64_t amount);

extern "C" int dregg_ffi_test_foreign_thread(int single_threaded) {
    int result = -1;
    std::thread host([&]() {
        const auto init = single_threaded ? dregg_ffi_init_st : dregg_ffi_init;
        result = init();
        if (result != 0) return;
        // Reentry must not reattach the same allocator or restart the runtime.
        result = init();
        if (result == 0 && dregg_kernel_transfer_total(100, 5, 30) != 105) result = -2;
    });
    host.join(); // Owned secondary attachment finalizes here; the runtime owner does not.
    return result;
}

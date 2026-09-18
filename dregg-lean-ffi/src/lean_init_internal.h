/* Private helpers for the Rust-owned process initialization lifecycle.
 * These helpers are not independently safe entrypoints: the shared coordinator
 * owns the runtime mode, thread attachment, module lock, and sticky failures. */
#pragma once
#include <lean/lean.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef lean_object *(*dregg_module_initializer)(uint8_t);
lean_object *dregg_ffi_run_module_init(const char *name, dregg_module_initializer init);
const char *dregg_ffi_last_failed_module(void);

#ifdef __cplusplus
}
#endif

#define DREGG_INIT_MODULE(name) dregg_ffi_run_module_init(#name, name)

# Kimi (Moonshot) live-brain demo — auth probe + fail-closed witness

> The brain is now **provider-agnostic** — point it at any OpenAI-compatible
> endpoint (a local proxy, ollama, vLLM, OpenRouter, …) with `--brain openai`
> `--llm-base` `--llm-model`. See [BRING-YOUR-OWN-LLM.md](BRING-YOUR-OWN-LLM.md).
> Kimi/Moonshot below is just one such endpoint (the historical default).

Status of the BYO key at `~/.kimikey` against the live Moonshot API, and the
sound behaviour of the brain ([`exec/src/openai_compat.rs`](../exec/src/openai_compat.rs),
`OpenAICompatBrain` / `KimiBrain`) when the key is rejected.

Date: 2026-06-30. Probed with the fresh key ember placed in `~/.kimikey`
(replacing the previously-rejected one).

## The key (redacted)

- Length: 72 chars, single trailing `\n` (trimmed by `ProviderKey::from_file`).
- Shape: `sk-kimi-…` (8-char `sk-kimi-` prefix + 64 payload chars), only
  `[A-Za-z0-9-]`. No BOM / hidden bytes / encoding corruption — the file loads
  and trims cleanly.
- The secret itself is never reproduced here (or in any receipt, report, log, or
  request body — see the confinement teeth below).

## Live auth probe — STILL REJECTED

Direct OpenAI-compatible calls with the key in the `Authorization: Bearer`
header, both Moonshot regions, both `/models` and `/chat/completions`:

| Endpoint                                   | Route               | Result                                              |
|--------------------------------------------|---------------------|-----------------------------------------------------|
| `https://api.moonshot.ai/v1` (global)      | `GET /models`       | HTTP 401 `{"error":{"message":"Invalid Authentication","type":"invalid_authentication_error"}}` |
| `https://api.moonshot.ai/v1` (global)      | `POST /chat/completions` (`kimi-k2-0711-preview`) | HTTP 401 `Invalid Authentication` |
| `https://api.moonshot.cn/v1` (mainland)    | `GET /models`       | HTTP 401 `Invalid Authentication`                   |
| `https://api.moonshot.cn/v1` (mainland)    | `POST /chat/completions` | HTTP 401 `Invalid Authentication`              |

The fresh key authenticates **no better** than the prior one — same
`Invalid Authentication` on every endpoint/route. The failure is at the
credential, not transport: the request reaches Moonshot and is refused.

### What a valid key needs

The `sk-kimi-` prefix is **not** the Moonshot Open Platform key shape (those are
`sk-` + ~48 chars and are what `api.moonshot.{ai,cn}/v1` authenticate). A key
that works here must be a Moonshot **Open Platform** API key — minted at
platform.moonshot.ai → API Keys, on an account with billing/credit enabled — and
must return HTTP 200 on `GET /v1/models`. The current `sk-kimi-…` credential
appears to belong to a different Kimi product/console (or is not provisioned on
the Open Platform that these endpoints serve); it is not recognized by either
region.

## The brain fail-closes soundly (live test, real wire)

`exec/src/kimi.rs::kimi_live_brain_reasons_over_a_real_call` (`--ignored`,
`--features kimi-live`) ran a **real** `LiveKimiCaller` POST with this key:

```
$ cargo test -p dreggnet-exec --features kimi-live --lib kimi:: -- --ignored --nocapture
running 1 test
live Kimi call did not complete (key rejected / unreachable); brain fail-closed
test kimi::tests::kimi_live_brain_reasons_over_a_real_call ... ok
```

The brain did exactly what confinement requires when the provider refuses:

- **No fabricated action.** A provider error finishes the turn (`next_action`
  returns `None`); the model never invents a tool-call.
- **An empty, sound, re-witnessable chain.** `admitted == 0`,
  `consumed <= budget`, and `verify_agent_run(&report)` re-witnesses the
  (empty) receipt chain. Fail-closed is still *proven*, not merely quiet.

This is the documented state when `~/.kimikey` is not a valid Moonshot key.

## Green gate (no regression)

- The 6 recorded-transport kimi tests pass deterministically:
  `kimi_drives_a_cap_gated_metered_receipted_task`,
  `an_out_of_bundle_tool_kimi_tries_is_refused_then_adapts` (out-of-bundle tool
  refused, then the model adapts off the fed-back verdict),
  `a_runaway_kimi_is_bounded_by_the_budget` (degenerate model bounded at the
  budget ceiling), `the_byo_key_never_leaks`,
  `a_forged_verdict_in_a_kimi_run_breaks_the_receipt`,
  `key_loads_from_a_file_trimmed`.
- `cargo test -p dreggnet-exec --lib` → `83 passed; 0 failed` (exit 0).
  (A flaky SIGABRT was observed once at *process teardown* after the
  `test result: ok` line — a cpython/wasmtime static-teardown race, unrelated to
  the kimi work; reruns of the full lib and every focused subset exit 0.)

## Key confinement — verified, no leak

Across the probe and the live run the secret was scanned out of every surface
the agent's reach can observe:

- Not in any request body the brain sent (`RecordedKimiCaller::key_leak_in_body`
  stays `false`; the live path puts the key only in the `Authorization` header).
- Not in the serialized run report, any receipt, or the run log.
- `ProviderKey`'s `Debug` is redacted (`<redacted>`), so a stray `{:?}` cannot
  leak it.
- This document reproduces only the prefix shape, never the secret.

## To re-run once a valid Open-Platform key is in place

```
# put a valid Moonshot Open Platform key (sk-…) in ~/.kimikey, then:
cargo test -p dreggnet-exec --features kimi-live --lib kimi:: -- --ignored --nocapture
# expect: "live Kimi loop: admitted=… consumed=… receipts=…" and admitted >= 1.
```

The same loop also drives `dregg-cloud agent deploy --brain kimi`.

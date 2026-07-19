"""Round-trips for the 2026-07-17 surface additions: tokens/presentations,
the light-client verify, and the `.reveal()` / `.on()` turn verbs.

No live node: authorization presentations are fully local (the STARK prove
for selective/private mode runs in-process, ~200-500ms), the light-client
tests exercise the fail-closed path (a POSITIVE verify needs a real
whole-chain aggregate envelope, which only the Rust recursion prover mints —
named gap, covered Rust-side in lightclient's own tests), and the builder
verbs sign offline with pinned federation_id + nonce.
"""

import pytest

import dregg

FED = "00" * 32
ROOT_KEY = "11" * 32


@pytest.fixture(autouse=True)
def temp_dregg_home(tmp_path, monkeypatch):
    monkeypatch.setenv("DREGG_HOME", str(tmp_path / "dregg-home"))
    monkeypatch.delenv("DREGG_PROFILE", raising=False)
    monkeypatch.delenv("DREGG_API_TOKEN", raising=False)


# ─── tokens & presentations ───


def test_mint_and_attenuate_token():
    ident = dregg.Identity.create("minter")
    token = ident.mint_token(ROOT_KEY, "dns")
    assert token.service == "dns"
    assert token.encoded.startswith("em2_")

    narrowed = ident.attenuate(token, services=[("dns", "r")])
    assert narrowed.service == "dns"
    assert narrowed.encoded != token.encoded  # narrowing minted a new token

    # Narrowing only: an EMPTY attenuation is refused by the core.
    with pytest.raises(dregg.DreggRefused):
        ident.attenuate(token)


def test_trusted_presentation_on_a_root_token():
    """Trusted mode is the ROOT-KEY HOLDER's mode (local Datalog + HMAC
    verify with the stored root key). A root token authorizes; the
    presentation round-trips through its wire bytes."""
    ident = dregg.Identity.create("presenter")
    token = ident.mint_token(ROOT_KEY, "dns")

    ok = ident.authorize(token, mode="trusted", service="dns", action="read")
    assert ok.kind == "trusted"
    assert ok.conclusion is True

    data = bytes(ok.to_bytes())
    again = dregg.Presentation.from_bytes(data)
    assert again.kind == "trusted"
    assert again.conclusion is True


def test_trusted_mode_refuses_attenuated_tokens_fail_closed():
    """THE CORE'S REAL CONTRACT (verified from cipherclerk source, not
    guessed): `attenuate` deliberately does NOT carry the root forging key
    into the child (security: an attenuated token cannot mint or re-verify
    the HMAC chain), so TRUSTED mode on an attenuated token is a refusal —
    not a Deny, not a silent pass. The attenuated token's presentation path
    is the ZK path (which needs federation membership — see below)."""
    ident = dregg.Identity.create("attenuator")
    token = ident.mint_token(ROOT_KEY, "dns")
    narrowed = ident.attenuate(token, services=[("dns", "r")])
    with pytest.raises(dregg.DreggRefused, match="signature verification failed"):
        ident.authorize(narrowed, mode="trusted", service="dns", action="read")


def test_selective_and_private_refuse_without_federation_membership():
    """NAMED PRODUCTION CONTRACT: the selective/private STARK prove path
    requires a federation-membership Merkle path on the token. A locally
    minted root token has none, and the production (non-`test-utils`) build
    has no synthetic-path fallback — so the refusal is loud and names the
    real cause. The POSITIVE selective path from Python needs the
    delegate/receive bindings (a membership-proof-bearing token) — a named
    gap, not bound yet; the Rust side covers it under bridge `test-utils`."""
    ident = dregg.Identity.create("selective")
    token = ident.mint_token(ROOT_KEY, "dns")
    for mode in ("selective", "private"):
        with pytest.raises(dregg.DreggRefused, match="federation"):
            ident.authorize(token, mode=mode, reveal=[0], service="dns", action="read")


def test_presentation_from_bytes_fails_closed():
    with pytest.raises(dregg.DreggRefused):
        dregg.Presentation.from_bytes(b"\xff" * 40)


def test_verify_disclosure_presentation_fails_closed_on_wrong_kind():
    """A TRUSTED presentation carries no commitment to check; the verify must
    return False (the Rust fail-closed contract), never True-by-default."""
    ident = dregg.Identity.create("wrongkind")
    token = ident.mint_token(ROOT_KEY, "dns")
    trusted = ident.authorize(token, mode="trusted", service="dns", action="read")
    assert dregg.verify_disclosure_presentation(trusted) is False


# ─── light-client verify (fail-closed legs; positive path is Rust-side) ───


def test_lightclient_verify_refuses_garbage_and_empty():
    from dregg import lightclient

    with pytest.raises(dregg.DreggRefused):
        lightclient.verify_history(b"", "22" * 32)
    with pytest.raises(dregg.DreggRefused):
        lightclient.verify_history(b"not an envelope at all", "22" * 32)


def test_lightclient_verify_validates_vk_argument():
    from dregg import lightclient

    with pytest.raises(ValueError):
        lightclient.verify_history(b"whatever", "zz")  # not hex / not 32 bytes


# ─── the new builder verbs, offline (pinned federation + nonce) ───


def test_reveal_witness_rides_under_the_signature():
    ident = dregg.Identity.create("revealer")
    secret = b"\xed" * 32
    t = (
        ident.turn("http://unused.invalid", federation_id=FED)
        .write_u64(1, 7)
        .reveal(secret)
        .nonce(0)
        .sign()
    )
    base = (
        dregg.Identity.from_profile("revealer")
        .turn("http://unused.invalid", federation_id=FED)
        .write_u64(1, 7)
        .nonce(0)
        .sign()
    )
    # The witness is UNDER the signature: same effects, different wire bytes
    # AND different signed hash. (The Rust drift-killer proves the blob opens
    # a real PreimageGate through the executor; this pins the py plumbing.)
    assert bytes(t.to_bytes()) != bytes(base.to_bytes())
    assert t.turn_hash != base.turn_hash


def test_on_target_retargets_the_action():
    ident = dregg.Identity.create("onner")
    target = "ab" * 32
    t = (
        ident.turn("http://unused.invalid", federation_id=FED)
        .on(target)
        .write_u64(0, 7)
        .nonce(0)
        .sign()
    )
    # The clerk's faithful explain names the TARGET cell, not the agent cell.
    assert target in t.explain().lower()

    # Ordering is fail-closed: .on() after staging verbs is refused (the
    # staged effects were built against the previous acting cell).
    with pytest.raises(dregg.DreggRefused):
        (
            dregg.Identity.from_profile("onner")
            .turn("http://unused.invalid", federation_id=FED)
            .write_u64(0, 7)
            .on(target)
        )

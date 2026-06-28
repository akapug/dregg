"""The service-economy surface: pay / invoke_service / lease.

These run against a REAL in-process `dregg.ServiceRuntime` — the verified
kernel executor, not a mock — so the assertions are the Python twins of the
Rust facade's tests in `sdk/src/service_economy.rs`: `pay` desugars to one
conserving Transfer and conserves value end-to-end, `invoke_service` routes the
method (and refuses an unknown one) and prepends the canonical pay leg, and the
lease's open/fund/run advances the durable checkpoint and the executor refuses a
run past the capacity ceiling.
"""

import pytest

import dregg


@pytest.fixture(scope="session", autouse=True)
def _warm_executor():
    """Absorb the first (cold) in-process executor turn before the timing-
    sensitive lease assertions. The executor verifies the worker's biscuit
    credential under biscuit's `RunLimits` (which includes a wall-clock
    `max_time`); the very first Datalog evaluation after a fresh build/import is
    slow enough on a cold machine to trip it, so we run one throwaway lease
    cycle here to warm the code paths."""
    rt = dregg.ServiceRuntime()
    funder = rt.spawn()
    lease = rt.lease(1)
    lease.fund(funder, 1_000)
    lease.run()


def test_pay_desugars_to_one_conserving_transfer_and_conserves_value():
    rt = dregg.ServiceRuntime()
    recipient = rt.spawn()

    payer = rt.cell_id
    pre_payer = rt.balance(payer)
    pre_recip = rt.balance(recipient.cell_id)

    receipt = rt.pay(recipient.cell_id, 1_000)
    assert len(receipt.turn_hash) == 64

    post_payer = rt.balance(payer)
    post_recip = rt.balance(recipient.cell_id)

    # The recipient is credited EXACTLY the transferred amount; the payer is
    # debited at least that much (plus the turn fee). The only value sink beyond
    # the conserved transfer is the payer's fee (Σδ=0 on the asset).
    assert post_recip - pre_recip == 1_000
    payer_loss = pre_payer - post_payer
    assert payer_loss >= 1_000
    total_decrease = (pre_payer + pre_recip) - (post_payer + post_recip)
    assert total_decrease == payer_loss - 1_000


def test_invoke_service_routes_method_and_refuses_unknown():
    rt = dregg.ServiceRuntime()
    svc = rt.install_service_cell(["render"])

    action = rt.invoke_service(svc, "render")
    assert action["target"] == svc
    assert action["method"] == dregg.method_symbol("render")
    # No pay leg, no work: the desugar carries no effects.
    assert action["effects"] == []

    with pytest.raises(dregg.DreggRefused):
        rt.invoke_service(svc, "undeclared")


def test_invoke_service_prepends_canonical_pay_leg():
    rt = dregg.ServiceRuntime()
    svc = rt.install_service_cell(["render"])
    asset = rt.native_asset

    action = rt.invoke_service(svc, "render", pay=(svc, 250, asset))

    # Effect 0 is the canonical pay Transfer (caller -> provider).
    assert len(action["effects"]) == 1
    leg = action["effects"][0]
    assert leg["kind"] == "transfer"
    assert leg["from"] == rt.cell_id
    assert leg["to"] == svc
    assert leg["amount"] == 250


def test_lease_open_fund_run_advances_checkpoint():
    rt = dregg.ServiceRuntime()
    funder = rt.spawn()
    lease = rt.lease(2)
    assert lease.step == 0
    assert lease.remaining == 2

    pre = rt.balance(lease.lease_cell)
    lease.fund(funder, 5_000)
    assert rt.balance(lease.lease_cell) - pre == 5_000

    s1 = lease.run()
    assert len(s1.turn_hash) == 64
    assert lease.step == 1
    assert lease.remaining == 1

    lease.run()
    assert lease.step == 2
    assert lease.remaining == 0


def test_lease_run_past_ceiling_is_refused_by_the_executor():
    rt = dregg.ServiceRuntime()
    lease = rt.lease(1)

    lease.run()
    assert lease.step == 1

    # The FieldLte meter binds the ceiling into the committed transition: the
    # run that would exceed max_steps is rejected by the executor itself.
    with pytest.raises(dregg.DreggRefused):
        lease.run()
    # The refused run did not advance the durable checkpoint.
    assert lease.step == 1

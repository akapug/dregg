"""THE DREGG ATLAS crawler — walk the reachable state-space of the live verified
image and dump it as data the site-builder renders.

Produces (under dregg-atlas/data/):
  protocol.json   — the AuthRequired lattice, effects, refusal taxonomy
  cells.json      — every cell at genesis, with its 7 faces + affordances + halo
  gametree.json   — the reachable state-space: nodes = world-states (keyed by
                    post-state digest), edges = turns (committed vs refused, with
                    reasons). The game tree.

State identity = the post-state hash a committed turn returns (the Merkle root of
the ledger after the turn). The empty path is "genesis". Because the per-cell
nonce ratchets monotonically (touch = IncrementNonce), the state-space is
infinite; we bound by depth + node/edge caps and LOG every bound so a truncation
is never mistaken for completeness.
"""
import json
import os
import sys

from mcp_client import Mcp

DATA = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
os.makedirs(DATA, exist_ok=True)

MAX_DEPTH = int(os.environ.get("ATLAS_DEPTH", "4"))
MAX_NODES = int(os.environ.get("ATLAS_NODES", "600"))
MAX_EDGES = int(os.environ.get("ATLAS_EDGES", "4000"))


def survey_snapshot(m):
    s = m.call("survey")
    return {
        "cell_count": s["cell_count"],
        "cells": [
            {"short": c["short"], "kind": c["kind"], "balance": c.get("balance"),
             "cap_edges": c["cap_edges"], "title": c["title"]}
            for c in s["cells"]
        ],
    }


TRANSFER_AMOUNT = int(os.environ.get("ATLAS_XFER", "1000"))


def all_moves(m):
    """The candidate move set from a state: every self-affordance on every cell
    (authorized or not), PLUS a representative cross-cell transfer between every
    ordered pair (value flow + conservation). Raw-effect moves carry kind='effect'."""
    cells = m.call("survey")["cells"]
    moves = []
    for c in cells:
        aff = m.call("affordances", cell=c["id"])
        for msg in aff["messages"]:
            moves.append({
                "kind": "affordance", "cell_id": c["id"], "cell": c["short"],
                "message": msg["name"], "effect": msg["effect"],
                "required": msg["required"], "authorized": msg["authorized"],
            })
    # cross-cell transfers — the value-flow verb the self-affordance surface lacks
    for a in cells:
        for b in cells:
            if a["id"] == b["id"]:
                continue
            moves.append({
                "kind": "effect", "effect_kind": "transfer",
                "cell_id": a["id"], "cell": a["short"], "to": b["id"], "to_short": b["short"],
                "message": f"transfer {TRANSFER_AMOUNT}→{b['short']}",
                "effect": "Transfer", "required": "Signature", "authorized": True,
            })
    return moves


def fire_move(m, mv):
    """Fire a candidate move (affordance or raw effect) and return the MCP result."""
    if mv.get("kind") == "effect" and mv.get("effect_kind") == "transfer":
        return m.call("effect", kind="transfer", **{"from": mv["cell_id"]}, to=mv["to"], amount=TRANSFER_AMOUNT)
    return m.call("act", cell=mv["cell_id"], message=mv["message"])


def reconstruct(m, path):
    """Set the world to the state after `path` (a list of (cell_id, message))."""
    m.call("rewind", to=0)
    digest = "genesis"
    for (cell_id, msg) in path:
        res = m.call("act", cell=cell_id, message=msg)
        if res["outcome"] == "committed":
            digest = res["receipt"]["post_state"]
    return digest


def crawl_gametree(m):
    """DFS over the reachable state-space using cheap snapshot/restore for
    backtracking (instant, vs the 3s reboot a rewind costs). State identity is
    the post-state Merkle root a committed turn returns."""
    nodes = {}   # digest -> {depth, snapshot}
    edges = []   # {from, to, cell, message, effect, required, authorized, outcome, ...}
    seen = set()
    bounds = {"depth_capped": 0, "node_cap_hit": False, "edge_cap_hit": False}

    def dfs(depth, parent_dig):
        if bounds["edge_cap_hit"] or bounds["node_cap_hit"]:
            return
        snap = m.call("snapshot")["id"]
        try:
            moves = all_moves(m)
            for mv in moves:
                if len(edges) >= MAX_EDGES:
                    bounds["edge_cap_hit"] = True
                    break
                m.call("restore", id=snap)  # back to this node's state (instant)
                res = fire_move(m, mv)
                edge = {
                    "from": parent_dig, "cell": mv["cell"], "message": mv["message"],
                    "effect": mv["effect"], "required": mv["required"],
                    "authorized": mv["authorized"], "outcome": res["outcome"],
                    "verb": mv.get("kind", "affordance"),
                }
                if res["outcome"] == "committed":
                    child = res["receipt"]["post_state"]
                    edge["to"] = child
                    edge["computrons"] = res["receipt"]["computrons"]
                    if child not in seen:
                        seen.add(child)
                        if len(nodes) >= MAX_NODES:
                            bounds["node_cap_hit"] = True
                        else:
                            nodes[child] = {"depth": depth + 1, "snapshot": survey_snapshot(m), "digest": child}
                            edges.append(edge)
                            if depth + 1 < MAX_DEPTH:
                                dfs(depth + 1, child)  # we are AT `child` now
                            else:
                                bounds["depth_capped"] += 1
                            continue
                    else:
                        edge["to_existing"] = True
                else:
                    edge["to"] = parent_dig  # refused → self-loop with a reason
                    edge["by_executor"] = res.get("by_executor")
                    edge["reason"] = res.get("reason", "")
                edges.append(edge)
        finally:
            m.call("forget", id=snap)

    m.call("rewind", to=0)  # clean genesis
    gdig = "genesis"
    nodes[gdig] = {"depth": 0, "snapshot": survey_snapshot(m), "digest": gdig}
    seen.add(gdig)
    dfs(0, gdig)

    return {
        "meta": {
            "max_depth": MAX_DEPTH, "max_nodes": MAX_NODES, "max_edges": MAX_EDGES,
            "node_count": len(nodes), "edge_count": len(edges),
            "committed_edges": sum(1 for e in edges if e["outcome"] == "committed"),
            "refused_edges": sum(1 for e in edges if e["outcome"] == "refused"),
            "bounds_hit": bounds,
            "note": "state digest = post-state Merkle root; refused edges are self-loops with a reason",
        },
        "nodes": list(nodes.values()),
        "edges": edges,
    }


def crawl_cells(m):
    m.call("rewind", to=0)
    exp = m.call("export", out=os.path.join(DATA, "_export_raw.json"))
    # the export tool wrote the full dump; re-read it for the cell faces
    with open(os.path.join(DATA, "_export_raw.json")) as f:
        return json.load(f)


# ---------------------------------------------------------------------------
# THE HYPERMAP — the cross-linked hypermedia backbone the site links over.
#
# Every object in the image becomes a typed node with a STABLE id, and every
# relation a typed edge, so the site can cross-link anything to anything:
#   cell:<short>           — a sovereign cell
#   face:<short>/<kind>    — one of a cell's presentation faces
#   affordance:<short>/<m> — a message the cell understands
#   effect:<Name>          — a protocol effect (the verb a message lifts to)
#   ocap-edge:<a>→<b>      — a capability grant in the ledger
# edges: presents (cell→face) · understands (cell→affordance) · lifts_to
# (affordance→effect) · grants (cell→ocap-edge→cell) · requires (affordance→
# auth-tier). If the MCP server exposes a first-class `map` tool (the sibling
# lane), we PREFER it (it is the authoritative cross-linked graph) and merge.
# ---------------------------------------------------------------------------

def crawl_hypermap(m, cells_dump):
    m.call("rewind", to=0)
    nodes, edges = {}, []
    seen_edge = set()

    def add_node(nid, ntype, **attrs):
        if nid not in nodes:
            nodes[nid] = {"id": nid, "type": ntype, **attrs}
        return nid

    def add_edge(a, b, etype, **attrs):
        key = (a, b, etype)
        if key in seen_edge:
            return
        seen_edge.add(key)
        edges.append({"from": a, "to": b, "type": etype, **attrs})

    # protocol-level effect nodes (the shared verb vocabulary)
    proto = m.call("protocol")
    for eff in proto.get("effects_seen", []):
        add_node("effect:" + eff, "effect", name=eff)

    cells = cells_dump.get("cells", [])
    for c in cells:
        short = c.get("short") or c.get("id", "")[:8]
        cnode = add_node("cell:" + short, "cell", short=short, kind=c.get("kind"),
                         title=c.get("title"), id=c.get("id"))
        # faces
        for face in c.get("faces", []):
            fid = f"face:{short}/{face.get('kind')}"
            add_node(fid, "face", cell=short, kind=face.get("kind"), label=face.get("label"))
            add_edge(cnode, fid, "presents")
        # affordances → effects, auth tiers
        for a in c.get("affordances", []):
            aid = f"affordance:{short}/{a.get('name')}"
            add_node(aid, "affordance", cell=short, message=a.get("name"),
                     effect=a.get("effect"), required=a.get("required"),
                     authorized=a.get("authorized"))
            add_edge(cnode, aid, "understands")
            eff = a.get("effect")
            if eff:
                add_node("effect:" + eff, "effect", name=eff)
                add_edge(aid, "effect:" + eff, "lifts_to")
            tier = a.get("required")
            if tier:
                tid = add_node("auth:" + tier, "auth-tier", tier=tier)
                add_edge(aid, tid, "requires")

    # ocap edges from the live graph (the capability web)
    try:
        og = m.call("graph", kind="ocap", format="json")
        for e in og.get("edges", []):
            a = e.get("from") or e.get("holder")
            b = e.get("to") or e.get("target")
            if not (a and b):
                continue
            a_s, b_s = str(a)[:8], str(b)[:8]
            ca, cb = "cell:" + a_s, "cell:" + b_s
            add_node(ca, "cell", short=a_s)
            add_node(cb, "cell", short=b_s)
            oid = f"ocap-edge:{a_s}->{b_s}"
            add_node(oid, "ocap-edge", holder=a_s, target=b_s,
                     rights=e.get("rights"), slot=e.get("slot"),
                     delegated=e.get("delegated"), faceted=e.get("faceted"))
            add_edge(ca, oid, "grants")
            add_edge(oid, cb, "to")
    except Exception as ex:
        print(f"  (ocap graph unavailable: {ex})", file=sys.stderr)

    out = {
        "meta": {
            "node_count": len(nodes), "edge_count": len(edges),
            "node_types": _count_by(nodes.values(), "type"),
            "edge_types": _count_by(edges, "type"),
            "source": "synthesized from survey/inspect/affordances/graph/protocol",
            "note": "every object is a stable-id typed node; every relation a typed edge "
                    "— the hypermedia backbone the site cross-links over.",
        },
        "nodes": list(nodes.values()),
        "edges": edges,
    }

    # PREFER a first-class `map` tool if the server exposes one (sibling lane).
    try:
        if "map" in m.tools():
            native = m.call("map")
            out["native_map"] = native
            out["meta"]["native_map"] = True
            out["meta"]["note"] += " · merged with the MCP `map` tool's authoritative graph."
    except Exception as ex:
        print(f"  (map tool probe failed: {ex})", file=sys.stderr)

    return out


def _count_by(items, key):
    out = {}
    for it in items:
        k = it.get(key) if isinstance(it, dict) else None
        out[k] = out.get(k, 0) + 1
    return out


def main():
    m = Mcp()
    try:
        print("crawling protocol…", file=sys.stderr)
        proto = m.call("protocol")
        json.dump(proto, open(os.path.join(DATA, "protocol.json"), "w"), indent=2)

        print("crawling cells (faces/affordances/halo via export)…", file=sys.stderr)
        cells = crawl_cells(m)
        # stamp each cell + face + affordance with its stable hypermap node id so
        # cells.json cross-links into the same id-space the site links over.
        for c in cells.get("cells", []):
            short = c.get("short") or c.get("id", "")[:8]
            c["node_id"] = "cell:" + short
            for face in c.get("faces", []):
                face["node_id"] = f"face:{short}/{face.get('kind')}"
            for a in c.get("affordances", []):
                a["node_id"] = f"affordance:{short}/{a.get('name')}"
        json.dump(cells, open(os.path.join(DATA, "cells.json"), "w"), indent=2)

        print("building the hypermap (cross-linked backbone)…", file=sys.stderr)
        hm = crawl_hypermap(m, cells)
        json.dump(hm, open(os.path.join(DATA, "hypermap.json"), "w"), indent=2)
        print(f"  hypermap: {hm['meta']['node_count']} nodes / {hm['meta']['edge_count']} edges "
              f"(types: {hm['meta']['node_types']})", file=sys.stderr)

        print(f"crawling game tree (depth={MAX_DEPTH})…", file=sys.stderr)
        gt = crawl_gametree(m)
        json.dump(gt, open(os.path.join(DATA, "gametree.json"), "w"), indent=2)
        print(f"  game tree: {gt['meta']['node_count']} states, {gt['meta']['edge_count']} transitions "
              f"({gt['meta']['committed_edges']} committed, {gt['meta']['refused_edges']} refused)", file=sys.stderr)
        print(f"  bounds hit: {gt['meta']['bounds_hit']}", file=sys.stderr)
    finally:
        m.close()

    # The components pillar is grepped off the source tree (no MCP needed) — emit
    # it here so `crawl.py` produces the full data set in one pass.
    try:
        import components
        components.build()
    except Exception as ex:
        print(f"  (components emit skipped: {ex})", file=sys.stderr)


if __name__ == "__main__":
    main()

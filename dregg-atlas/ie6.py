"""THE IE6 FLOOR — a pure-HTML-4.01 view of the cockpit for any user-agent back to
the dawn of the web (for timetravelers). No CSS3, no JS, no canvas, no wasm: just
`<table>` layout, `<img>`, and genuine `<map>`/`<area>` image-maps (IE6 can't do
canvas — you navigate by clicking regions of a server-rendered frame). This is the
graceful-degradation floor under the live wasm cockpit: where the browser can't run
the model, it gets pre-rendered frames as clickable images.

Server-less: generates static pages from the cockpit surface screenshots. Run after
shoot.py + build.py:  python3 ie6.py   →  site/ie6/index.html
"""
import json
import os
import html

ROOT = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(ROOT, "data")
SITE = os.path.join(ROOT, "site")
IE6 = os.path.join(SITE, "ie6")

# HTML 4.01 Transitional — the doctype a 1999 browser expects.
HEAD = """<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN" "http://www.w3.org/TR/html4/loose.dtd">
<html><head><meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
<title>{title} - THE DREGG ATLAS (compatibility view)</title></head>
<body bgcolor="#0a0e14" text="#c9d1d9" link="#58a6ff" vlink="#bc8cff" alink="#f0883e">
<font face="monospace" size="2">"""
FOOT = "</font></body></html>"


def esc(s):
    return html.escape(str(s or ""))


def build():
    os.makedirs(IE6, exist_ok=True)
    surfaces = json.load(open(os.path.join(DATA, "surfaces.json")))
    gt = json.load(open(os.path.join(DATA, "gametree.json")))["meta"]

    # --- index.html: a genuine <map> image-map over a banner frame + a table grid ---
    banner = surfaces[0]["file"] if surfaces else None  # the HOME surface
    # The banner is shown at 900px wide; <area> bands divide it into nav targets.
    # (IE6 navigates by clicking regions of a pre-rendered frame — the whole point.)
    areas = (
        '<area shape="rect" coords="0,0,900,200" href="surfaces.html" alt="surfaces" title="the 28 cockpit surfaces">'
        '<area shape="rect" coords="0,200,900,420" href="gametree.html" alt="game tree" title="the protocol state-space">'
        '<area shape="rect" coords="0,420,900,585" href="about.html" alt="about" title="what this is">'
    )
    body = [HEAD.format(title="dregg")]
    body.append('<table width="920" align="center" cellpadding="6"><tr><td>')
    body.append('<h1><font color="#58a6ff">THE DREGG ATLAS</font> '
                '<font color="#8b949e" size="2">- compatibility view (HTML 4.01, no script)</font></h1>')
    body.append('<p>The verified object-capability OS, mapped — rendered as plain images and tables '
                'for any browser back to the dawn of the web. The live interactive atlas needs a modern '
                'browser; this floor does not. <b>Click a band of the frame below to navigate</b> '
                '(a genuine <tt>&lt;map&gt;</tt> image-map — the way you drove a remote screen before canvas existed).</p>')
    if banner:
        body.append(f'<p><img src="../screenshots/{esc(banner)}" width="900" height="585" '
                    f'usemap="#nav" border="1" alt="dregg cockpit"></p>'
                    f'<map name="nav">{areas}</map>')
    body.append('<p><b>Or jump straight in:</b> &nbsp; '
                '<a href="surfaces.html">[ the 28 surfaces ]</a> &nbsp; '
                '<a href="gametree.html">[ the game tree ]</a> &nbsp; '
                '<a href="about.html">[ about ]</a></p>')
    body.append(f'<p><font color="#8b949e">Game tree: {gt.get("node_count","?")} states / '
                f'{gt.get("edge_count","?")} transitions. Surfaces: {len(surfaces)}.</font></p>')
    body.append('</td></tr></table>')
    body.append(FOOT)
    open(os.path.join(IE6, "index.html"), "w").write("\n".join(body))

    # --- surfaces.html: a table grid of all 28 surface thumbnails (each a link) ---
    rows = ['<table width="940" align="center" cellpadding="8" cellspacing="0" border="0">']
    per_row = 3
    for i, s in enumerate(surfaces):
        if i % per_row == 0:
            rows.append("<tr>" if i == 0 else "</tr><tr>")
        rows.append(
            f'<td width="300" valign="top" bgcolor="#161b22">'
            f'<a href="s_{esc(s["tab"])}.html"><img src="../screenshots/{esc(s["file"])}" '
            f'width="290" border="0" alt="{esc(s["tab"])}"></a><br>'
            f'<b><font color="#58a6ff">{esc(s["tab"])}</font></b><br>'
            f'<font size="1" color="#8b949e">{esc((s.get("explainer") or "")[:90])}</font></td>'
        )
    rows.append("</tr></table>")
    page = [HEAD.format(title="surfaces"),
            '<p><a href="index.html">&lt;&lt; atlas</a> / surfaces</p>',
            '<h2><font color="#58a6ff">The 28 cockpit surfaces</font></h2>',
            "\n".join(rows), FOOT]
    open(os.path.join(IE6, "surfaces.html"), "w").write("\n".join(page))

    # --- per-surface pages: full frame + explainer + prev/next/up nav ---
    for i, s in enumerate(surfaces):
        prev = surfaces[i - 1]["tab"] if i > 0 else surfaces[-1]["tab"]
        nxt = surfaces[(i + 1) % len(surfaces)]["tab"]
        page = [HEAD.format(title=s["tab"]),
                f'<p><a href="index.html">&lt;&lt; atlas</a> / <a href="surfaces.html">surfaces</a> / {esc(s["tab"])} '
                f'&nbsp;&nbsp; [<a href="s_{esc(prev)}.html">prev</a>] [<a href="s_{esc(nxt)}.html">next</a>]</p>',
                f'<h2><font color="#58a6ff">{esc(s["tab"])}</font></h2>',
                f'<p><img src="../screenshots/{esc(s["file"])}" width="960" border="1" alt="{esc(s["tab"])}"></p>',
                f'<p>{esc(s.get("explainer"))}</p>',
                FOOT]
        open(os.path.join(IE6, f's_{s["tab"]}.html'), "w").write("\n".join(page))

    # --- gametree.html: the radial frame, as a static image + the numbers ---
    page = [HEAD.format(title="game tree"),
            '<p><a href="index.html">&lt;&lt; atlas</a> / game tree</p>',
            '<h2><font color="#58a6ff">The protocol game tree</font></h2>',
            f'<p>The reachable state-space of the live verified image: '
            f'<b>{gt.get("node_count","?")}</b> world-states, <b>{gt.get("edge_count","?")}</b> turns '
            f'(<font color="#3fb950">{gt.get("committed_edges","?")} committed</font>, '
            f'<font color="#f85149">{gt.get("refused_edges","?")} refused</font>). '
            f'Each state is keyed by its post-state Merkle root; each turn was fired through the verified '
            f'executor. The interactive radial map needs a modern browser; the numbers are the same.</p>',
            '<p><a href="index.html">&lt;&lt; back</a></p>', FOOT]
    open(os.path.join(IE6, "gametree.html"), "w").write("\n".join(page))

    # --- about.html ---
    page = [HEAD.format(title="about"),
            '<p><a href="index.html">&lt;&lt; atlas</a> / about</p>',
            '<h2><font color="#58a6ff">About this compatibility view</font></h2>',
            '<p>THE DREGG ATLAS is a self-built map of dregg, a formally verified distributed '
            'object-capability OS, crawled from the live verified image. The full atlas is an '
            'interactive single-page app (game tree, UI tree, ocap web, protocol). This is its '
            '<b>graceful-degradation floor</b>: pure HTML 4.01, no script, no canvas, no wasm — so any '
            'user-agent, however old, gets the surfaces and the shape. The live cockpit itself degrades '
            'the same way: where a browser cannot run the wasm model, it can still be driven as a '
            'server-rendered frame via image-maps. Welcome, timetraveler.</p>',
            '<p><a href="../index.html">[ the full interactive atlas ]</a></p>', FOOT]
    open(os.path.join(IE6, "about.html"), "w").write("\n".join(page))

    print(f"IE6 floor → {IE6}/index.html ({len(surfaces)} surfaces, pure HTML 4.01)")


if __name__ == "__main__":
    build()

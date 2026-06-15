//! THE SIX-SCREEN ONBOARDING ARC. Each screen is a polished, characterful,
//! retro-futurist frame painted into the framebuffer with REAL deos data shapes
//! (a real cell's four substances, a real affordance's cap∧state gate, a
//! `dregg://` web-of-cells reference). The soul: houyhnhnm computing
//! (orthogonal persistence, "I object to doing things computers can do", the user
//! holds ultimate control) + constructive knowledge ("to hold a capability is to
//! exhibit a witness that verifies — never to assert it").
//!
//! Data shapes are drawn from the live deos crates (read, not invented):
//!   - `Cell` (cell/src/cell.rs): a BLAKE3 content-addressed `id`, an Ed25519
//!     `public_key`, a `CellState` (16 fields + nonce + SIGNED i64 balance), a
//!     `Permissions` table, a `CapabilitySet` c-list, a `CellProgram`, a
//!     `CellMode` (Hosted/Sovereign), a `CellLifecycle` (Live/Sealed/…).
//!   - the four substances: VALUE = `balance: i64`; STATE = `fields[16]` + nonce;
//!     AUTHORITY = permissions ∧ the c-list; EVIDENCE = the verification key /
//!     `proved_state` / commitments.
//!   - the production law (CONSTRUCTIVE-KNOWLEDGE.md §3): gateOK = WHO ∧ WHAT ∧
//!     HOW ∧ not-revoked — a door lights iff the witness verifies AND state permits.

use crate::fb::{rgb, Canvas, HEIGHT, WIDTH};

pub const N_SCREENS: usize = 6;

// ───────────────────────────── the deos palette ─────────────────────────────
// A cyberpunk-retro teal/cyan set: deep ink backdrops, neon teal accents, warm
// amber for "live"/value, soft magenta for the web, muted greys for body text.
const INK_TOP: (u8, u8, u8) = (6, 16, 26);
const INK_BOT: (u8, u8, u8) = (3, 8, 16);
const CARD_HI: (u8, u8, u8) = (18, 34, 46);
const CARD_LO: (u8, u8, u8) = (9, 17, 26);
const TEAL: u32 = rgb(64, 224, 208);
const TEAL_DIM: u32 = rgb(40, 130, 130);
const CYAN: u32 = rgb(120, 230, 240);
const WHITE: u32 = rgb(232, 246, 248);
const GREY: u32 = rgb(150, 178, 188);
const DIM: u32 = rgb(96, 124, 136);
const AMBER: u32 = rgb(255, 196, 92);
const GREEN: u32 = rgb(96, 230, 140);
const RED: u32 = rgb(232, 96, 96);
const MAGENTA: u32 = rgb(212, 130, 230);
const GOLD: u32 = rgb(240, 214, 120);

/// Paint screen `n` (0-based) into the canvas. Every screen clears its own
/// backdrop, so switching is a clean repaint.
pub fn draw(c: &mut Canvas, n: usize) {
    c.vgradient(INK_TOP, INK_BOT);
    starfield(c, n);
    match n {
        0 => screen_welcome(c),
        1 => screen_theorems(c),
        2 => screen_cell(c),
        3 => screen_affordances(c),
        4 => screen_web(c),
        _ => screen_keys(c),
    }
    chrome(c, n);
}

// A faint deterministic "starfield" of dim teal dots — depth without noise. The
// pattern is seeded by the screen index so each screen feels distinct but calm.
fn starfield(c: &mut Canvas, seed: usize) {
    let mut s: u32 = 0x9E37_79B9 ^ (seed as u32).wrapping_mul(0x85EB_CA77).wrapping_add(1);
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 17;
        s ^= s << 5;
        s
    };
    for _ in 0..90 {
        let x = next() % WIDTH;
        let y = next() % (HEIGHT - 70);
        let b = 18 + (next() % 26) as u8;
        c.put(x, y, rgb(b / 2, b, b));
    }
}

// The persistent chrome: a top hairline + title strip, and the bottom status bar
// with the screen counter + the navigation hint. Present on every screen so the
// UX feels like one running program.
fn chrome(c: &mut Canvas, n: usize) {
    // top hairline
    c.rect(0, 0, WIDTH, 2, TEAL_DIM);
    c.text("deos", 24, 16, 2, 1, TEAL);
    c.text("robigalia v0", 24 + 90, 18, 1, 1, DIM);
    // a tiny right-aligned breadcrumb of the arc
    let dots_x = WIDTH - 24 - (N_SCREENS as u32) * 18;
    for i in 0..N_SCREENS {
        let x = dots_x + i as u32 * 18;
        let col = if i == n { TEAL } else { rgb(40, 64, 72) };
        c.rect(x, 20, 11, 4, col);
    }

    // bottom status bar
    let bar_y = HEIGHT - 36;
    c.rect(0, bar_y, WIDTH, 36, rgb(7, 14, 22));
    c.rect(0, bar_y, WIDTH, 2, TEAL_DIM);
    let mut x = 24;
    x = c.text("SPACE", x, bar_y + 11, 1, 1, TEAL);
    x = c.text(" next", x, bar_y + 11, 1, 1, GREY);
    x += 18;
    x = c.text("UP/DOWN", x, bar_y + 11, 1, 1, TEAL);
    let _ = c.text(" back/fwd", x, bar_y + 11, 1, 1, GREY);
    // right: screen counter
    let label = SCREEN_LABEL[n];
    let lw = Canvas::text_w(label, 1, 1);
    c.text(label, WIDTH - 24 - lw, bar_y + 11, 1, 1, DIM);
}

const SCREEN_LABEL: [&str; N_SCREENS] = [
    "1/6  welcome",
    "2/6  theorems",
    "3/6  a cell",
    "4/6  affordances",
    "5/6  web of cells",
    "6/6  the keys",
];

// Helper: a centered card panel with a teal border + a subtle vertical gradient.
fn card(c: &mut Canvas, x: u32, y: u32, w: u32, h: u32) {
    c.vgradient_rect(x, y, w, h, CARD_HI, CARD_LO);
    c.frame(x, y, w, h, 2, TEAL_DIM);
}

// A small "chip"/tag with a filled background and a label.
fn chip(c: &mut Canvas, x: u32, y: u32, text: &str, fg: u32, bg: u32) -> u32 {
    let tw = Canvas::text_w(text, 1, 1);
    let w = tw + 16;
    c.rect(x, y, w, 18, bg);
    c.frame(x, y, w, 18, 1, fg);
    c.text(text, x + 8, y + 5, 1, 1, fg);
    x + w
}

// ───────────────────────────── screen 0: welcome ────────────────────────────
fn screen_welcome(c: &mut Canvas) {
    // A big, confident title. The logotype "deos" oversize, then a tagline.
    let cx = WIDTH / 2;

    // a glowing horizon band behind the title
    c.vgradient_rect(0, 150, WIDTH, 220, (10, 30, 40), (6, 16, 26));

    c.text_center("deos", 0, WIDTH, 150, 11, 2, TEAL);
    // subtle drop accent line under the logotype
    let lw = Canvas::text_w("deos", 11, 2);
    c.rect(cx - lw / 2, 254, lw, 3, TEAL_DIM);

    c.text_center("a computing system you actually hold", 0, WIDTH, 288, 2, 1, WHITE);
    c.text_center("an operating system on seL4, where authority is proof", 0, WIDTH, 322, 1, 2, GREY);

    // three tiny pillars
    let py = 380;
    let third = WIDTH / 3;
    pillar(c, 0 * third, py, "CAPABILITY", "to hold is to prove", TEAL);
    pillar(c, 1 * third, py, "PERSISTENCE", "nothing is ever lost", AMBER);
    pillar(c, 2 * third, py, "SOVEREIGNTY", "the keys are yours", MAGENTA);

    c.text_center("press SPACE to begin the tour", 0, WIDTH, 500, 1, 2, CYAN);
}

fn pillar(c: &mut Canvas, x0: u32, y: u32, title: &str, sub: &str, accent: u32) {
    let w = WIDTH / 3;
    // a little diamond bullet
    let cx = x0 + w / 2;
    diamond(c, cx, y, 6, accent);
    c.text_center(title, x0, w, y + 18, 1, 2, accent);
    c.text_center(sub, x0, w, y + 36, 1, 1, DIM);
}

fn diamond(c: &mut Canvas, cx: u32, cy: u32, r: u32, color: u32) {
    for dy in 0..=r {
        let span = r - dy;
        c.rect(cx - span, cy - dy, 2 * span + 1, 1, color);
        c.rect(cx - span, cy + dy, 2 * span + 1, 1, color);
    }
}

// ─────────────────────── screen 1: boundaries are theorems ───────────────────
fn screen_theorems(c: &mut Canvas) {
    let mx = 64;
    let w = WIDTH - 2 * mx;
    // Big headline at scale 3, track 0 so the long line fits inside 800px.
    c.text("your boundaries are theorems,", mx, 78, 3, 0, WHITE);
    c.text("not permissions", mx, 118, 3, 0, TEAL);

    card(c, mx, 174, w, 150);
    let tx = mx + 28;
    c.text("a capability is constructive knowledge", tx, 196, 2, 0, CYAN);
    c.text("To HOLD a capability is to be able to EXHIBIT a witness", tx, 234, 1, 2, GREY);
    c.text("the kernel accepts -- never merely to assert it, never", tx, 258, 1, 2, GREY);
    c.text("merely to be named in a table. Authority is PRODUCTION", tx, 282, 1, 2, GREY);
    c.text("under non-forgeability. Possession and proof are one act.", tx, 306, 1, 2, GREY);

    // the four facets of the production law, as a row of chips
    let fy = 356;
    c.text("every act passes one fail-closed gate:", mx, fy, 1, 2, DIM);
    let mut x = mx;
    let gy = fy + 26;
    x = chip(c, x, gy, "WHO  witness verifies", GREEN, rgb(10, 28, 20)) + 10;
    x = chip(c, x, gy, "WHAT  granted <= held", TEAL, rgb(8, 24, 28)) + 10;
    let _ = chip(c, x, gy, "HOW  caveats discharge", AMBER, rgb(28, 22, 8));
    let _ = chip(c, mx, gy + 28, "and the edge is not revoked or expired", RED, rgb(28, 12, 12));

    // the punchline, set apart
    c.rect(mx, 452, 6, 56, TEAL);
    c.text("You cannot cross a boundary you cannot prove.", mx + 20, 458, 1, 2, WHITE);
    c.text("So a boundary you hold is a theorem -- it HOLDS, by construction.", mx + 20, 484, 1, 1, GREY);
}

// ─────────────────────── screen 2: a real cell ──────────────────────────────
fn screen_cell(c: &mut Canvas) {
    let mx = 64;
    c.text("this is a cell", mx, 76, 3, 1, WHITE);
    c.text("the knower, the agent, the object -- one unit of deos", mx, 118, 1, 2, GREY);

    // the cell card
    let cw = WIDTH - 2 * mx;
    card(c, mx, 150, cw, 380);
    let tx = mx + 28;

    // header: id + lifecycle/mode chips
    c.text("cell", tx, 172, 2, 1, TEAL);
    let mut hx = tx + Canvas::text_w("cell", 2, 1) + 16;
    hx = chip(c, hx, 174, "LIVE", GREEN, rgb(10, 26, 18)) + 8;
    let _ = chip(c, hx, 174, "SOVEREIGN", MAGENTA, rgb(24, 14, 28));

    // content-addressed id (a real BLAKE3(public_key || token_id) shape)
    c.text("id   blake3(pk||token)", tx, 212, 1, 1, DIM);
    c.text("c0ffee21 9a3b4d77 0badf00d 1337beef ...", tx, 232, 1, 1, CYAN);
    c.text("pk   ed25519", tx, 260, 1, 1, DIM);
    c.text("3f29ab10 77cd5e02 ...                  (32 bytes)", tx, 280, 1, 1, GREY);

    // a divider
    c.rect(tx, 308, cw - 56, 1, rgb(30, 50, 58));
    c.text("the four substances", tx, 318, 1, 2, TEAL);

    // four substance tiles in a 2x2 grid
    let gx = tx;
    let gy = 348;
    let tile_w = (cw - 56 - 24) / 2;
    let tile_h = 78;
    substance(c, gx, gy, tile_w, tile_h, "VALUE", "balance : i64 (signed)", "+ 1_000", AMBER);
    substance(c, gx + tile_w + 24, gy, tile_w, tile_h, "STATE", "fields[16] + nonce", "nonce 0x2a", CYAN);
    substance(c, gx, gy + tile_h + 16, tile_w, tile_h, "AUTHORITY", "permissions ^ c-list", "3 caps held", TEAL);
    substance(
        c,
        gx + tile_w + 24,
        gy + tile_h + 16,
        tile_w,
        tile_h,
        "EVIDENCE",
        "vk + proved_state",
        "proved: true",
        GREEN,
    );
}

fn substance(
    c: &mut Canvas,
    x: u32,
    y: u32,
    w: u32,
    h: u32,
    name: &str,
    schema: &str,
    value: &str,
    accent: u32,
) {
    c.vgradient_rect(x, y, w, h, CARD_LO, (6, 12, 18));
    c.frame(x, y, w, h, 1, accent);
    c.rect(x, y, 4, h, accent); // accent spine
    c.text(name, x + 16, y + 12, 1, 2, accent);
    c.text(schema, x + 16, y + 34, 1, 1, DIM);
    c.text(value, x + 16, y + 54, 1, 1, WHITE);
}

// ─────────────────────── screen 3: affordances (cap ^ state) ─────────────────
fn screen_affordances(c: &mut Canvas) {
    let mx = 64;
    c.text("affordances", mx, 76, 3, 1, WHITE);
    c.text("a door lights iff you hold the cap AND the state permits", mx, 118, 1, 2, GREY);

    // The gate equation, prominent (scale 2, track 0 so the whole conjunction
    // fits inside the card at 800px width).
    card(c, mx, 152, WIDTH - 2 * mx, 92);
    c.text("gateOK = WHO & WHAT & HOW & not-revoked", mx + 28, 176, 2, 0, CYAN);
    c.text("an affordance is offered only when the whole conjunction is true.", mx + 28, 214, 1, 1, DIM);

    // Three affordance "buttons" with their gate state shown honestly.
    let by = 280;
    let bw = (WIDTH - 2 * mx - 2 * 28) / 3;
    affordance(
        c,
        mx,
        by,
        bw,
        "transfer",
        "move 250 value",
        Gate::Lit,
        "cap: spend  state: balance>=250",
    );
    affordance(
        c,
        mx + bw + 28,
        by,
        bw,
        "delegate",
        "grant read to a peer",
        Gate::Lit,
        "cap: grant  granted <= held: ok",
    );
    affordance(
        c,
        mx + 2 * (bw + 28),
        by,
        bw,
        "seal record",
        "freeze this cell",
        Gate::Dark,
        "cap: admin  NOT HELD -- refused",
    );

    // the takeaway
    c.rect(mx, 470, 6, 56, AMBER);
    c.text("A refused affordance writes NO pixel and moves NO value.", mx + 20, 476, 1, 2, WHITE);
    c.text("The dark button is not a locked door -- it is a theorem you cannot prove.", mx + 20, 502, 1, 1, GREY);
}

enum Gate {
    Lit,
    Dark,
}

fn affordance(c: &mut Canvas, x: u32, y: u32, w: u32, title: &str, sub: &str, gate: Gate, why: &str) {
    let h = 150;
    match gate {
        Gate::Lit => {
            c.vgradient_rect(x, y, w, h, (10, 40, 36), (8, 24, 26));
            c.frame(x, y, w, h, 2, GREEN);
            // a lit indicator lamp
            lamp(c, x + w - 26, y + 14, GREEN);
            c.text(title, x + 16, y + 14, 2, 0, WHITE);
            c.text(sub, x + 16, y + 48, 1, 1, GREY);
            c.text("LIT", x + 16, y + h - 60, 1, 2, GREEN);
            wrap2(c, why, x + 16, y + h - 38, w - 32, GREEN);
        }
        Gate::Dark => {
            c.vgradient_rect(x, y, w, h, (20, 12, 12), (10, 7, 7));
            c.frame(x, y, w, h, 2, rgb(120, 56, 56));
            lamp(c, x + w - 26, y + 14, rgb(90, 40, 40));
            c.text(title, x + 16, y + 14, 2, 0, GREY);
            c.text(sub, x + 16, y + 48, 1, 1, DIM);
            c.text("DARK", x + 16, y + h - 60, 1, 2, RED);
            wrap2(c, why, x + 16, y + h - 38, w - 32, rgb(200, 130, 130));
        }
    }
}

// a small round-ish lamp (a filled 3-row plus)
fn lamp(c: &mut Canvas, x: u32, y: u32, color: u32) {
    c.rect(x + 2, y, 8, 12, color);
    c.rect(x, y + 2, 12, 8, color);
}

// crude 2-line wrap for the short "why" caption (keeps within tile width)
fn wrap2(c: &mut Canvas, s: &str, x: u32, y: u32, w: u32, color: u32) {
    let max_chars = (w / 8).max(1) as usize; // 8px per glyph at scale 1
    let b = s.as_bytes();
    if b.len() <= max_chars {
        c.text(s, x, y, 1, 0, color);
        return;
    }
    // split at the last space before max_chars
    let mut split = max_chars.min(b.len());
    while split > 0 && b[split - 1] != b' ' {
        split -= 1;
    }
    if split == 0 {
        split = max_chars;
    }
    let (a, rest) = s.split_at(split);
    c.text(a.trim_end(), x, y, 1, 0, color);
    let rest = rest.trim_start();
    let rest = if rest.len() > max_chars { &rest[..max_chars] } else { rest };
    c.text(rest, x, y + 12, 1, 0, color);
}

// ─────────────────────── screen 4: the web of cells ─────────────────────────
fn screen_web(c: &mut Canvas) {
    let mx = 64;
    c.text("the web of cells", mx, 76, 3, 1, WHITE);
    c.text("cells reference cells -- a partial, local knowledge graph", mx, 118, 1, 2, GREY);

    // a dregg:// reference, like a hyperlink
    card(c, mx, 152, WIDTH - 2 * mx, 72);
    c.text("dregg://", mx + 28, 176, 2, 1, MAGENTA);
    c.text("c0ffee21.../garden/quote", mx + 28 + Canvas::text_w("dregg://", 2, 1), 178, 2, 1, CYAN);
    c.text("an edge you learn of only when someone PRODUCES a witness for it.", mx + 28, 204, 1, 1, DIM);

    // the transcluded quote, set as a real pulled fragment
    let qy = 252;
    card(c, mx, qy, WIDTH - 2 * mx, 150);
    c.rect(mx, qy, 6, 150, MAGENTA);
    c.text("transcluded from dregg://c0ffee21.../garden/quote", mx + 24, qy + 16, 1, 1, DIM);
    c.text("\"I object to doing things", mx + 24, qy + 44, 2, 1, GOLD);
    c.text("that computers can do.\"", mx + 24, qy + 78, 2, 1, GOLD);
    c.text("-- the Sacred Motto of the Guild of Houyhnhnm Programmers", mx + 24, qy + 116, 1, 1, GREY);

    // the graph law: a full-width caption, then a tiny node diagram, then the
    // takeaway line -- all on their own rows so nothing clips the right edge.
    let gy = 426;
    c.text("only connectivity begets connectivity", mx, gy, 1, 2, DIM);
    // node a -> node b -> node c, arrows clearly between the boxes.
    let ny = gy + 26;
    let n1 = node(c, mx + 20, ny, "you", TEAL);
    let n2x = mx + 200;
    edge(c, n1 + 8, ny + 14, n2x - 8, ny + 14, MAGENTA);
    let n2 = node(c, n2x, ny, "garden", GOLD);
    let n3x = mx + 380;
    edge(c, n2 + 8, ny + 14, n3x - 8, ny + 14, MAGENTA);
    let n3 = node(c, n3x, ny, "quote", CYAN);
    c.text("you produce only what you hold", n3 + 28, ny + 9, 1, 0, GREY);
}

/// Draw a node box; returns the x of its right edge (for wiring edges).
fn node(c: &mut Canvas, x: u32, y: u32, label: &str, color: u32) -> u32 {
    let tw = Canvas::text_w(label, 1, 0);
    let w = tw + 20;
    c.vgradient_rect(x, y, w, 28, CARD_HI, CARD_LO);
    c.frame(x, y, w, 28, 2, color);
    c.text(label, x + 10, y + 9, 1, 0, color);
    x + w
}

fn edge(c: &mut Canvas, x0: u32, y: u32, x1: u32, _y1: u32, color: u32) {
    if x1 > x0 {
        c.rect(x0, y, x1 - x0, 2, color);
        // little arrowhead at the destination end
        c.rect(x1 - 6, y - 3, 2, 8, color);
        c.rect(x1 - 4, y - 2, 2, 6, color);
        c.rect(x1 - 2, y - 1, 2, 4, color);
    }
}

// ─────────────────────── screen 5: you hold the keys ────────────────────────
fn screen_keys(c: &mut Canvas) {
    let cx = WIDTH / 2;

    c.vgradient_rect(0, 130, WIDTH, 200, (10, 30, 40), (6, 16, 26));
    c.text_center("you hold the keys", 0, WIDTH, 150, 4, 1, TEAL);
    let lw = Canvas::text_w("you hold the keys", 4, 1);
    c.rect(cx - lw / 2, 198, lw, 3, TEAL_DIM);

    c.text_center("no vendor between you and your computing.", 0, WIDTH, 236, 1, 2, WHITE);
    c.text_center("authority is what you can prove. persistence is the default.", 0, WIDTH, 266, 1, 2, GREY);
    c.text_center("the boundaries are yours, and they hold by construction.", 0, WIDTH, 290, 1, 2, GREY);

    // a key glyph, drawn from rectangles, centered
    draw_key(c, cx - 70, 330, GOLD);

    // recap chips
    let ry = 440;
    let mut x = cx - 250;
    x = chip(c, x, ry, "constructive knowledge", TEAL, rgb(8, 24, 28)) + 12;
    x = chip(c, x, ry, "sovereign cells", MAGENTA, rgb(24, 14, 28)) + 12;
    let _ = chip(c, x, ry, "verified on seL4", GREEN, rgb(10, 26, 18));

    // the call to action, big and inviting
    c.text_center("press SPACE to begin", 0, WIDTH, 496, 2, 2, CYAN);
}

// a stylized key: a ring (hollow square) + a shaft + two teeth
fn draw_key(c: &mut Canvas, x: u32, y: u32, color: u32) {
    // ring
    c.frame(x, y + 6, 44, 44, 6, color);
    c.rect(x + 16, y + 22, 12, 12, color); // ring hole filled (looks like a bow)
    // erase center to make a hole
    c.rect(x + 14, y + 20, 16, 16, rgb(6, 16, 26));
    // shaft
    c.rect(x + 44, y + 22, 96, 12, color);
    // teeth
    c.rect(x + 116, y + 34, 10, 14, color);
    c.rect(x + 132, y + 34, 10, 20, color);
}

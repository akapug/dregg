/**
 * THE ROOM-MAP VISUALIZER — an inline-SVG picture of a dungeon's room graph, shared by the play
 * surface (/vault) and the forge (/forge). No libraries, no CDN — a deterministic, position-
 * independent leveled layout drawn straight into an HTML container.
 *
 * The data is exactly what `GET /game/map` returns: `[{id, name, exits:[{name,to,toName,locked,
 * gateReason}]}]`. Nodes are rooms; a directed arrow per exit; a LOCKED exit is drawn distinctly
 * (dashed + red, its gate reason on hover). The player's CURRENT room is highlighted; rooms the
 * player has VISITED read solid, the rest faded; a room disconnected from the graph is flagged.
 *
 * The layout is a BFS-leveled column grid rooted at a STABLE, position-independent node (the room
 * with the fewest incoming exits, ties by id) so the picture does NOT reshuffle as the player
 * moves — only the highlighting changes. A room unreachable from that root lands in a trailing
 * "disconnected" column, so a stray room is visible at a glance (great authoring feedback).
 */

export interface MapExit { name?: string; to: string; toName?: string; locked: boolean; gateReason?: string | null }
export interface MapRoom { id: string; name: string; exits: MapExit[] }
export interface RoomMapOpts {
  /** The player's current room id (highlighted "you are here"). */
  currentRoomId?: string | null;
  /** Room ids the player has visited/known (solid); everything else reads faded/unexplored. */
  visited?: Set<string> | string[] | null;
  /** When true (the forge, where the author wrote every room), treat ALL rooms as known/solid. */
  allKnown?: boolean;
}

const NODE_W = 128;
const NODE_H = 46;
const COL_GAP = 66;
const ROW_GAP = 20;
const PAD = 28;
const COL_STEP = NODE_W + COL_GAP;
const ROW_STEP = NODE_H + ROW_GAP;

function esc(s: string): string {
  return String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]!));
}

function truncate(s: string, n: number): string {
  return s.length > n ? s.slice(0, n - 1).trimEnd() + "…" : s;
}

/** Clip the ray from a node's center toward (tx,ty) to the node's rectangle border. */
function clip(cx: number, cy: number, tx: number, ty: number): [number, number] {
  const dx = tx - cx, dy = ty - cy;
  const hw = NODE_W / 2 + 3, hh = NODE_H / 2 + 3;
  if (dx === 0 && dy === 0) return [cx, cy];
  const sx = dx === 0 ? Infinity : hw / Math.abs(dx);
  const sy = dy === 0 ? Infinity : hh / Math.abs(dy);
  const s = Math.min(sx, sy);
  return [cx + dx * s, cy + dy * s];
}

/**
 * Render the room graph into `container`. Replaces its contents with a legend + one inline SVG.
 * Safe to call repeatedly (e.g. after every move) — the layout is stable, so only the highlight
 * moves.
 */
export function renderRoomMap(container: HTMLElement, rooms: MapRoom[], opts: RoomMapOpts = {}): void {
  if (!container) return;
  if (!rooms || !rooms.length) {
    container.innerHTML = '<div class="rm-empty">no rooms to map yet.</div>';
    return;
  }

  const byId = new Map<string, MapRoom>();
  for (const r of rooms) byId.set(r.id, r);
  const known = opts.allKnown
    ? new Set(rooms.map((r) => r.id))
    : new Set<string>(Array.isArray(opts.visited) ? opts.visited : opts.visited ? Array.from(opts.visited) : []);
  const current = opts.currentRoomId || null;
  if (current) known.add(current);

  // Undirected adjacency (for LEVEL assignment — an exit connects both ways for layout purposes),
  // restricted to targets that actually exist.
  const adj = new Map<string, Set<string>>();
  const link = (a: string, b: string) => {
    if (!byId.has(a) || !byId.has(b)) return;
    if (!adj.has(a)) adj.set(a, new Set());
    if (!adj.has(b)) adj.set(b, new Set());
    adj.get(a)!.add(b); adj.get(b)!.add(a);
  };
  const incoming = new Map<string, number>();
  for (const r of rooms) incoming.set(r.id, 0);
  for (const r of rooms) {
    for (const e of r.exits) {
      if (byId.has(e.to)) incoming.set(e.to, (incoming.get(e.to) || 0) + 1);
      link(r.id, e.to);
    }
  }

  // A STABLE root: the room with the fewest incoming exits, ties broken by id. Independent of the
  // player's position, so the drawing does not reshuffle when they move.
  const ordered = rooms.map((r) => r.id).sort();
  let root = ordered[0];
  let best = Infinity;
  for (const id of ordered) {
    const inc = incoming.get(id) || 0;
    if (inc < best) { best = inc; root = id; }
  }

  // BFS (undirected) → level per room. Unreached rooms are "disconnected".
  const level = new Map<string, number>();
  const queue: string[] = [root];
  level.set(root, 0);
  let maxLevel = 0;
  while (queue.length) {
    const id = queue.shift()!;
    const l = level.get(id)!;
    maxLevel = Math.max(maxLevel, l);
    for (const nb of adj.get(id) || []) {
      if (!level.has(nb)) { level.set(nb, l + 1); queue.push(nb); }
    }
  }
  const orphanLevel = maxLevel + 1;
  const orphans = new Set<string>();
  for (const id of ordered) {
    if (!level.has(id)) { level.set(id, orphanLevel); orphans.add(id); }
  }
  const usedOrphanLevel = orphans.size > 0;
  const lastLevel = usedOrphanLevel ? orphanLevel : maxLevel;

  // Column grid: group rooms by level, order within a level by id (stable).
  const cols: string[][] = [];
  for (let l = 0; l <= lastLevel; l++) cols.push([]);
  for (const id of ordered) cols[level.get(id)!].push(id);

  const pos = new Map<string, { x: number; y: number }>();
  let maxRows = 0;
  for (let l = 0; l < cols.length; l++) {
    maxRows = Math.max(maxRows, cols[l].length);
    cols[l].forEach((id, row) => {
      pos.set(id, { x: PAD + l * COL_STEP + NODE_W / 2, y: PAD + row * ROW_STEP + NODE_H / 2 });
    });
  }
  const width = PAD * 2 + (cols.length - 1) * COL_STEP + NODE_W;
  const height = PAD * 2 + Math.max(1, maxRows - 1) * ROW_STEP + NODE_H;

  // ── edges ──
  const edgeSvg: string[] = [];
  for (const r of rooms) {
    const a = pos.get(r.id); if (!a) continue;
    for (const e of r.exits) {
      const b = pos.get(e.to); if (!b) continue;
      // Perpendicular offset so an A→B / B→A pair separates onto opposite sides.
      const dx = b.x - a.x, dy = b.y - a.y, len = Math.hypot(dx, dy) || 1;
      const off = 4.5, px = (-dy / len) * off, py = (dx / len) * off;
      const [sx, sy] = clip(a.x + px, a.y + py, b.x + px, b.y + py);
      const [ex, ey] = clip(b.x + px, b.y + py, a.x + px, a.y + py);
      const cls = e.locked ? "rm-edge locked" : "rm-edge";
      const marker = e.locked ? "url(#rm-arrow-locked)" : "url(#rm-arrow)";
      const dirLabel = e.name ? `${e.name} → ${e.toName || e.to}` : (e.toName || e.to);
      const title = e.locked ? `${dirLabel}  — barred: ${e.gateReason || "locked"}` : dirLabel;
      edgeSvg.push(
        `<line class="${cls}" x1="${sx.toFixed(1)}" y1="${sy.toFixed(1)}" x2="${ex.toFixed(1)}" y2="${ey.toFixed(1)}" marker-end="${marker}"><title>${esc(title)}</title></line>`
      );
    }
  }

  // ── nodes ──
  const nodeSvg: string[] = [];
  for (const r of rooms) {
    const p = pos.get(r.id)!;
    const x = p.x - NODE_W / 2, y = p.y - NODE_H / 2;
    const isCurrent = r.id === current;
    const isKnown = known.has(r.id);
    const isOrphan = orphans.has(r.id);
    const cls = ["rm-node"];
    if (isCurrent) cls.push("current");
    else if (isKnown) cls.push("visited");
    else cls.push("unknown");
    if (isOrphan) cls.push("orphan");
    const label = truncate(r.name, 15);
    const you = isCurrent
      ? `<circle class="rm-you-dot" cx="${p.x.toFixed(1)}" cy="${(y - 8).toFixed(1)}" r="4"></circle>` +
        `<text class="rm-you" x="${p.x.toFixed(1)}" y="${(y - 14).toFixed(1)}" text-anchor="middle">you are here</text>`
      : "";
    nodeSvg.push(
      `<g class="${cls.join(" ")}">` +
        you +
        `<rect x="${x.toFixed(1)}" y="${y.toFixed(1)}" width="${NODE_W}" height="${NODE_H}" rx="10"></rect>` +
        `<text class="rm-label" x="${p.x.toFixed(1)}" y="${(p.y + 4).toFixed(1)}" text-anchor="middle">${esc(label)}<title>${esc(r.name)}</title></text>` +
      `</g>`
    );
  }

  const W = Math.ceil(width), H = Math.ceil(height);
  const svg =
    `<svg class="roommap-svg" viewBox="0 0 ${W} ${H}" width="${W}" height="${H}" role="img" ` +
    `aria-label="room map: ${esc(String(rooms.length))} rooms" preserveAspectRatio="xMinYMin meet">` +
    `<defs>` +
      `<marker id="rm-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">` +
        `<path class="rm-ahead" d="M0,0 L10,5 L0,10 z"></path></marker>` +
      `<marker id="rm-arrow-locked" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">` +
        `<path class="rm-ahead locked" d="M0,0 L10,5 L0,10 z"></path></marker>` +
    `</defs>` +
    `<g class="rm-edges">${edgeSvg.join("")}</g>` +
    `<g class="rm-nodes">${nodeSvg.join("")}</g>` +
    `</svg>`;

  const orphanChip = usedOrphanLevel
    ? `<span class="rm-key rm-key-orphan"><span class="rm-swatch"></span>disconnected</span>`
    : "";
  const legend =
    `<div class="rm-legend">` +
      `<span class="rm-key rm-key-current"><span class="rm-swatch"></span>you are here</span>` +
      `<span class="rm-key rm-key-visited"><span class="rm-swatch"></span>visited</span>` +
      `<span class="rm-key rm-key-unknown"><span class="rm-swatch"></span>unexplored</span>` +
      `<span class="rm-key rm-key-locked"><span class="rm-swatch"></span>barred way</span>` +
      orphanChip +
    `</div>`;

  container.innerHTML = legend + `<div class="rm-scroll">${svg}</div>`;
}

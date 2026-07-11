// THE DRIVEN MOBILE PASS — the bar: it fits a phone, shown.
//
// Loads every key page at a 360px-wide viewport (a small phone) in headless Chromium and
// ASSERTS there is no horizontal overflow — document.documentElement.scrollWidth must stay
// within the viewport width (a couple of px of sub-pixel slack). It also checks the shared
// site-nav is present (the one-product chrome) and that the theme toggle + share controls
// meet a 44px tap-target floor. Captures a stitched contact sheet at demo/run/mobile.png
// (the hub in a phone frame) + a per-page report at demo/run/mobile.txt.
//
//   node demo/run-mobile.mjs
//
// The collective-story pages play out of the box; the AI-dungeon pages (/vault, /party,
// /forge, /dungeon) render their full chrome even without the native game service wired,
// so the layout is exercised either way. No CDN assets — the page is fully self-contained.

import assert from "node:assert/strict";
import { mkdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import path from "node:path";
import { makeServer } from "./serve.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const pwRequire = createRequire(path.join(REPO, "extension", "tests", "package.json"));
const { chromium } = pwRequire("playwright");
const OUT = path.join(__dirname, "run");

// A small phone. 360×780 is a common Android logical size; iPhone SE is 375.
const VIEWPORT = { width: 360, height: 780 };
const SLACK = 2; // px of sub-pixel slack allowed before we call it overflow

const PAGES = [
  { route: "/hub", name: "the hub (front door)" },
  { route: "/", name: "The Commons" },
  { route: "/author", name: "Author your own" },
  { route: "/vault", name: "The Sunken Vault" },
  { route: "/party", name: "The Collective Dungeon" },
  { route: "/forge", name: "The Forge" },
  { route: "/dungeon", name: "The Attested Dungeon" },
];

async function measure(page) {
  return page.evaluate(() => {
    const de = document.documentElement;
    const nav = document.querySelector(".site-nav");
    const toggle = document.querySelector("[data-theme-toggle]");
    const share = document.querySelector("[data-share]");
    const box = (el) => { if (!el) return null; const r = el.getBoundingClientRect(); return { w: Math.round(r.width), h: Math.round(r.height) }; };
    return {
      scrollWidth: de.scrollWidth,
      clientWidth: de.clientWidth,
      innerWidth: window.innerWidth,
      hasNav: !!nav,
      brandHref: nav ? (nav.querySelector(".brand") ? nav.querySelector(".brand").getAttribute("href") : null) : null,
      toggle: box(toggle),
      share: box(share),
    };
  });
}

async function main() {
  await mkdir(OUT, { recursive: true });
  const { server, base } = await makeServer(0);
  const browser = await chromium.launch({ headless: true });
  const report = [];
  const failures = [];
  let hubShot = null;
  try {
    for (const p of PAGES) {
      const page = await browser.newPage({ viewport: VIEWPORT, deviceScaleFactor: 2 });
      const consoleErrs = [];
      page.on("pageerror", (e) => consoleErrs.push(String(e)));
      try {
        await page.goto(`${base}${p.route}`, { waitUntil: "load" });
        await page.waitForTimeout(250); // let boot + first render settle
        const m = await measure(page);
        const overflow = m.scrollWidth - m.innerWidth;
        const okOverflow = overflow <= SLACK;
        const okNav = m.hasNav && m.brandHref === "/hub";
        const okToggle = m.toggle && m.toggle.w >= 44 && m.toggle.h >= 44;
        const okShare = m.share && m.share.w >= 44 && m.share.h >= 44;

        report.push(
          `${okOverflow && okNav && okToggle && okShare ? "✓" : "✗"} ${p.route.padEnd(9)} ${p.name}\n` +
          `      overflow: scrollWidth ${m.scrollWidth} vs innerWidth ${m.innerWidth} → ${overflow <= 0 ? "none" : overflow + "px"} ${okOverflow ? "OK" : "OVERFLOW"}\n` +
          `      nav: ${m.hasNav ? "present" : "MISSING"} (home → ${m.brandHref})` +
          `  · theme toggle ${m.toggle ? m.toggle.w + "×" + m.toggle.h : "MISSING"} ${okToggle ? "≥44px" : "TOO SMALL"}` +
          `  · share ${m.share ? m.share.w + "×" + m.share.h : "MISSING"} ${okShare ? "≥44px" : "TOO SMALL"}`
        );

        if (!okOverflow) failures.push(`${p.route}: horizontal overflow of ${overflow}px (scrollWidth ${m.scrollWidth} > innerWidth ${m.innerWidth})`);
        if (!okNav) failures.push(`${p.route}: shared site-nav missing or brand not linked to /hub`);
        if (!okToggle) failures.push(`${p.route}: theme toggle below the 44px tap-target floor`);
        if (!okShare) failures.push(`${p.route}: share control below the 44px tap-target floor`);
        if (consoleErrs.length) report.push(`      (page errors: ${consoleErrs.join(" · ")})`);

        if (p.route === "/hub") hubShot = await page.screenshot({ fullPage: true });
      } finally {
        await page.close();
      }
    }
  } finally {
    await browser.close();
    server.close();
  }

  if (hubShot) await writeFile(path.join(OUT, "mobile.png"), hubShot);

  const header = [
    "THE MOBILE PASS — every key page at 360px wide (a small phone)",
    `driven run · viewport ${VIEWPORT.width}×${VIEWPORT.height} · served at ${base}`,
    "assert: no horizontal overflow (scrollWidth ≤ innerWidth) · shared nav present · 44px tap targets",
    "=".repeat(78),
    "",
  ].join("\n");
  const body = report.join("\n\n");
  const foot = "\n\n" + "=".repeat(78) + "\n" +
    (failures.length ? `RESULT: ${failures.length} problem(s):\n  - ${failures.join("\n  - ")}\n` : "RESULT: every key page fits a 360px phone — no horizontal overflow, shared nav present, tap targets ≥44px.\n");
  const transcript = header + body + foot;
  await writeFile(path.join(OUT, "mobile.txt"), transcript, "utf8");
  console.log("\n" + transcript);
  console.log(`  screenshot → ${path.join(OUT, "mobile.png")}`);
  console.log(`  report     → ${path.join(OUT, "mobile.txt")}\n`);

  assert.equal(failures.length, 0, `mobile pass found ${failures.length} problem(s) — see above`);
  console.log("  ✓ THE MOBILE PASS: every key page fits a 360px phone, one cohesive nav, tap-friendly.\n");
}

main().catch((e) => {
  console.error("\n  ✗ MOBILE PASS FAILED\n");
  console.error(e?.stack || String(e));
  process.exit(1);
});

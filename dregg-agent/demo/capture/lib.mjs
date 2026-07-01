// Shared helpers for the browser-surface capture scripts.
//
// Everything here is presentation glue: a legible caption bar (carrying the beat
// label AND the honesty note, burned into the frame), paced waits, and the
// chromium the cached Playwright provides. No surface behaviour is faked here —
// the pages are the real server-rendered DreggNet surfaces / the real MV3
// extension; this only labels and paces the recording.

import { chromium } from 'playwright-core';

export const VIEW = { width: 1280, height: 800 };

export function exe() {
  return chromium.executablePath();
}

export const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// Inject (once) a fixed caption bar at the bottom of the frame and set its text.
// `title` is the beat; `note` is the honesty label (recorded-locally / what is
// real vs demo). Legible at video size, does not mutate the surface's own DOM
// semantics (pure overlay).
export async function caption(page, title, note) {
  await page.evaluate(({ title, note }) => {
    let bar = document.getElementById('__cap_bar');
    if (!bar) {
      const style = document.createElement('style');
      style.textContent = `
        #__cap_bar{position:fixed;left:0;right:0;bottom:0;z-index:2147483647;
          font-family:ui-monospace,SFMono-Regular,Menlo,monospace;
          background:linear-gradient(0deg,rgba(8,8,18,.97),rgba(8,8,18,.86));
          border-top:2px solid #7b8cff;color:#e8e8f5;padding:10px 20px 12px;
          display:flex;flex-direction:column;gap:2px;pointer-events:none;}
        #__cap_bar .t{font-size:19px;font-weight:700;letter-spacing:.01em;color:#fff;}
        #__cap_bar .t b{color:#a779ff;}
        #__cap_bar .n{font-size:12.5px;color:#9a9ac0;}
        #__cap_bar .n b{color:#46d39a;font-weight:600;}
        #__cap_bar .badge{position:fixed;top:12px;right:16px;z-index:2147483647;
          font-family:ui-monospace,monospace;font-size:11px;color:#0e0e1a;
          background:#ffcf6b;border-radius:6px;padding:3px 9px;font-weight:700;
          box-shadow:0 2px 8px rgba(0,0,0,.4);}
      `;
      document.head.appendChild(style);
      bar = document.createElement('div');
      bar.id = '__cap_bar';
      bar.innerHTML = '<div class="t"></div><div class="n"></div>'
        + '<div class="badge">◉ RECORDED LOCALLY</div>';
      document.body.appendChild(bar);
    }
    bar.querySelector('.t').innerHTML = title;
    bar.querySelector('.n').innerHTML = note || '';
  }, { title, note });
}

// Smooth-scroll an element into view centred, then settle.
export async function reveal(page, selector, ms = 700) {
  await page.evaluate((sel) => {
    const el = document.querySelector(sel);
    if (el) el.scrollIntoView({ behavior: 'smooth', block: 'center' });
  }, selector);
  await sleep(ms);
}

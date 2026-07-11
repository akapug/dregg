// Shared site chrome behavior for the verifiable-fiction pages:
//   • theme toggle (light/dark) with localStorage persistence, applied before paint (no FOUC);
//   • a "copy a shareable link" affordance.
//
// Loaded same-origin (<script src="/theme.js">) so it satisfies a strict `script-src 'self'`
// CSP (the Forge page). No imports, no network, no external assets.
(function () {
  "use strict";
  var KEY = "dregg-theme";

  function saved() {
    try { return localStorage.getItem(KEY); } catch (e) { return null; }
  }
  function prefersDark() {
    try { return window.matchMedia && window.matchMedia("(prefers-color-scheme: dark)").matches; }
    catch (e) { return false; }
  }
  // The theme actually in effect right now (explicit choice, else the OS preference).
  function effective() {
    var s = saved();
    if (s === "light" || s === "dark") return s;
    return prefersDark() ? "dark" : "light";
  }
  // Apply an explicit choice to <html data-theme>; clear it to fall back to the OS.
  function apply(choice) {
    var root = document.documentElement;
    if (choice === "light" || choice === "dark") root.setAttribute("data-theme", choice);
    else root.removeAttribute("data-theme");
  }

  // ── run immediately (this script sits in <head>, before <body> paints) ──
  apply(saved());

  function icon(t) { return t === "dark" ? "🌙" : "☀️"; }

  function refreshToggles() {
    var eff = effective();
    var next = eff === "dark" ? "light" : "dark";
    var toggles = document.querySelectorAll("[data-theme-toggle]");
    for (var i = 0; i < toggles.length; i++) {
      var b = toggles[i];
      b.textContent = icon(eff);
      b.setAttribute("aria-label", "Switch to " + next + " theme");
      b.setAttribute("title", (eff === "dark" ? "Dark" : "Light") + " theme — switch to " + next);
    }
  }

  function toggleTheme() {
    var next = effective() === "dark" ? "light" : "dark";
    try { localStorage.setItem(KEY, next); } catch (e) {}
    apply(next);
    refreshToggles();
  }

  function flash(btn, text, ok) {
    if (btn.__restore) { clearTimeout(btn.__t); }
    else { btn.__restore = btn.innerHTML; }
    btn.classList.toggle("copied", !!ok);
    btn.classList.toggle("share-fail", !ok);
    btn.textContent = text;
    btn.__t = setTimeout(function () {
      btn.innerHTML = btn.__restore;
      btn.__restore = null;
      btn.classList.remove("copied", "share-fail");
    }, 1600);
  }

  function share(btn) {
    var url = (btn.getAttribute("data-share-url") || location.href);
    function ok() { flash(btn, "✓ Link copied", true); }
    function fail() { flash(btn, "⚠ Press ⌘/Ctrl-C", false); }
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(url).then(ok, function () { legacy(url) ? ok() : fail(); });
    } else {
      legacy(url) ? ok() : fail();
    }
  }
  function legacy(url) {
    try {
      var ta = document.createElement("textarea");
      ta.value = url; ta.setAttribute("readonly", "");
      ta.style.position = "absolute"; ta.style.left = "-9999px";
      document.body.appendChild(ta); ta.select();
      var done = document.execCommand("copy");
      document.body.removeChild(ta);
      return done;
    } catch (e) { return false; }
  }

  function wire() {
    var toggles = document.querySelectorAll("[data-theme-toggle]");
    for (var i = 0; i < toggles.length; i++) {
      if (toggles[i].__wired) continue;
      toggles[i].__wired = true;
      toggles[i].addEventListener("click", toggleTheme);
    }
    var shares = document.querySelectorAll("[data-share]");
    for (var j = 0; j < shares.length; j++) {
      if (shares[j].__wired) continue;
      shares[j].__wired = true;
      (function (b) { b.addEventListener("click", function () { share(b); }); })(shares[j]);
    }
    refreshToggles();
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", wire);
  else wire();

  // Keep the toggle icon honest if the OS theme flips while no explicit choice is set.
  try {
    var mq = window.matchMedia("(prefers-color-scheme: dark)");
    var onChange = function () { if (!saved()) refreshToggles(); };
    if (mq.addEventListener) mq.addEventListener("change", onChange);
    else if (mq.addListener) mq.addListener(onChange);
  } catch (e) {}
})();

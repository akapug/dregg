/**
 * The popup — two faces:
 *
 *   1. **Identity** (default): shows the active dregg identity (public cell id),
 *      the front door's "who am I" face.
 *   2. **Approval** (`?pending=<id>`): the anti-blind-signing gate. The
 *      background opens this carrying a pending approval id; the popup fetches
 *      the faithful `explain()` reading + per-effect plain language for EXACTLY
 *      the turn about to be signed, renders it, and the user clicks Approve or
 *      Decline. The verdict is posted back to the background, which submits the
 *      turn ONLY on Approve. Nothing here ever sees key material.
 */

import type { ApprovalView, IdentityView } from "./protocol";

const $ = (id: string): HTMLElement => {
  const el = document.getElementById(id);
  if (!el) throw new Error(`missing element #${id}`);
  return el;
};

function sendMessage<T>(msg: unknown): Promise<T> {
  return new Promise((resolve) => chrome.runtime.sendMessage(msg, (r: T) => resolve(r)));
}

async function renderIdentity(): Promise<void> {
  $("approval").style.display = "none";
  $("identity").style.display = "block";
  const r = await sendMessage<{ ok: boolean; view?: IdentityView; error?: string }>({ type: "dregg:popupIdentity" });
  if (r.ok && r.view) {
    $("cellId").textContent = r.view.cellIdHex;
    $("pubkey").textContent = r.view.publicKeyHex;
    $("label").textContent = r.view.label ?? "dregg identity";
  } else {
    $("cellId").textContent = `error: ${r.error ?? "unavailable"}`;
  }
}

async function renderApproval(pendingId: string): Promise<void> {
  $("identity").style.display = "none";
  $("approval").style.display = "block";

  const r = await sendMessage<{ ok: boolean; view?: ApprovalView; error?: string }>({
    type: "dregg:getPending",
    pendingId,
  });
  if (!r.ok || !r.view) {
    $("approvalTitle").textContent = "Approval expired";
    $("approvalBody").textContent = r.error ?? "no such pending request";
    return;
  }
  const view = r.view;

  $("origin").textContent = view.origin || "(unknown page)";
  $("signer").textContent = view.signerCellIdHex;
  if (view.pageLabel) {
    const labelEl = $("pageLabel");
    labelEl.textContent = `Page says: “${view.pageLabel}” (advisory — verify the effects below)`;
    labelEl.style.display = "block";
  }

  // Per-effect plain language, derived from the SAME signed term.
  const list = $("effects");
  list.innerHTML = "";
  for (const line of view.lines) {
    const li = document.createElement("li");
    li.textContent = line;
    if (line.includes("UNKNOWN EFFECT")) li.className = "unknown";
    list.appendChild(li);
  }

  // The faithful SDK reading (the bytes), available for inspection.
  $("explain").textContent = view.explain;

  if (view.hasUnknown) {
    const warn = $("blindWarning");
    warn.style.display = "block";
    warn.textContent =
      "⚠ This turn contains an effect the wallet could not read. Approving is a blind signature — do not approve unless you trust this page.";
  }

  const finish = async (approved: boolean): Promise<void> => {
    await sendMessage({ type: "dregg:approvalResult", pendingId, approved });
    window.close();
  };
  ($("approveBtn") as HTMLButtonElement).onclick = () => void finish(true);
  ($("declineBtn") as HTMLButtonElement).onclick = () => void finish(false);
  // Closing the window without choosing is treated as a decline by the worker
  // only if it re-asks; to be safe, wire beforeunload to a decline.
  window.addEventListener("beforeunload", () => void sendMessage({ type: "dregg:approvalResult", pendingId, approved: false }));
}

const params = new URLSearchParams(location.search);
const pending = params.get("pending");
if (pending) {
  void renderApproval(pending);
} else {
  void renderIdentity();
}

//! The **JS engine binding** — real SpiderMonkey (`mozjs`) driving deos substance.
//!
//! [`JsRuntime`] wraps a genuine `JSContext`/`Runtime` (the same minimal embedding the
//! `mozjs` `eval`/`callback` examples prove). It installs native Rust functions onto a
//! fresh global; a JS prelude builds the ergonomic `deos.applet({...})` / `app.fire` /
//! `app.get` / `app.view` surface on top of them. The natives bridge into a
//! thread-local [`Applet`] (the embedded verified executor) so:
//!
//!   - `app.fire("inc", n)` → a REAL cap-gated verified turn (a `TurnReceipt`);
//!   - `app.get(slot)` → a witnessed read off the live ledger;
//!   - `app.view.set(k, v)` → a plain in-memory change (NO turn, NO receipt).
//!
//! SpiderMonkey rooting/GC is observed via the `rooted!` macro and `CallArgs`, exactly
//! as the upstream `callback.rs` test does. This is the genuine engine, not a stub.

use std::cell::RefCell;
use std::ffi::CStr;
use std::ptr;
use std::ptr::NonNull;
use std::str;

use mozjs::context::{JSContext as SmContext, RawJSContext};
use mozjs::jsapi::{CallArgs, OnNewGlobalHookOption, Value};
use mozjs::jsval::{Int32Value, StringValue, UndefinedValue};
use mozjs::realm::AutoRealm;
use mozjs::rooted;
use mozjs::rust::wrappers2::{
    EncodeStringToUTF8, JS_DefineFunction, JS_NewGlobalObject, JS_NewStringCopyN,
};
use mozjs::rust::{
    evaluate_script, CompileOptionsWrapper, JSEngine, RealmOptions, Runtime, SIMPLE_GLOBAL_CLASS,
};

use crate::applet::{Applet, FireError};
use crate::attach::AttachedApplet;
use crate::reflect_binding;

/// The substance the native functions drive: EITHER deos-js's own embedded engine
/// ([`Applet`]) or a PROVIDED live World ([`AttachedApplet`] — the attach path). The
/// natives call the SAME surface on both (crawl `ledger()`, fire, read, view-state),
/// so one set of bindings serves both the embedded spike and the live cockpit.
pub enum JsTarget {
    /// deos-js's own fresh embedded engine — a private single-cell world.
    Embedded(Applet),
    /// A provided live World (the cockpit's real ledger, or a fork) — the attach path.
    Attached(AttachedApplet),
}

impl JsTarget {
    /// Read the live ledger the reflective crawl walks (the REAL cells of whichever
    /// world is attached) by running `f` over it — closure-passing so the attach
    /// path can borrow a World held behind an `Rc<RefCell<World>>` for the read's
    /// duration. The crawl natives produce their JSON inside `f`.
    pub fn with_ledger(&self, f: &mut dyn FnMut(&dregg_cell::Ledger)) {
        match self {
            JsTarget::Embedded(a) => f(a.ledger()),
            JsTarget::Attached(a) => a.with_ledger(f),
        }
    }
    /// Fire an affordance — ONE cap-gated verified turn (on the embedded engine, or
    /// the live World). Returns the receipt hash on commit.
    pub fn fire(&mut self, affordance: &str, arg: i64) -> Result<[u8; 32], FireError> {
        match self {
            JsTarget::Embedded(a) => a.fire(affordance, arg).map(|r| r.receipt_hash()),
            JsTarget::Attached(a) => a.fire(affordance, arg),
        }
    }
    /// Witnessed read of one model field as a u64.
    pub fn get_u64(&self, slot: usize) -> u64 {
        match self {
            JsTarget::Embedded(a) => a.get_u64(slot),
            JsTarget::Attached(a) => a.get_u64(slot),
        }
    }
    /// The agent/applet cell (the affordance projection's subject).
    pub fn cell(&self) -> dregg_types::CellId {
        match self {
            JsTarget::Embedded(a) => a.cell(),
            JsTarget::Attached(a) => a.cell(),
        }
    }
    /// The registered affordance specs (name + required authority).
    pub fn affordance_specs(&self) -> Vec<(String, dregg_cell::AuthRequired)> {
        match self {
            JsTarget::Embedded(a) => a.affordance_specs(),
            JsTarget::Attached(a) => a.affordance_specs(),
        }
    }
    /// The committed receipt count (the audit tape length).
    pub fn receipt_count(&self) -> usize {
        match self {
            JsTarget::Embedded(a) => a.receipt_count(),
            JsTarget::Attached(a) => a.receipt_count(),
        }
    }
    /// The committed receipt-hash tape (the rewindable lineage).
    pub fn receipts(&self) -> Vec<[u8; 32]> {
        match self {
            JsTarget::Embedded(a) => a.receipts().to_vec(),
            JsTarget::Attached(a) => a.receipts().to_vec(),
        }
    }
    fn set_view(&mut self, key: &str, value: &str) {
        match self {
            JsTarget::Embedded(a) => a.set_view(key, value),
            JsTarget::Attached(a) => a.set_view(key, value),
        }
    }
    fn get_view(&self, key: &str) -> Option<String> {
        match self {
            JsTarget::Embedded(a) => a.get_view(key).map(|s| s.to_string()),
            JsTarget::Attached(a) => a.get_view(key).map(|s| s.to_string()),
        }
    }
    /// The full committed receipts — the Provenance face's lineage. Empty for the
    /// attach path (the live World owns the full provenance log; the attach tape
    /// carries hashes only).
    fn full_receipts(&self) -> Vec<dregg_turn::turn::TurnReceipt> {
        match self {
            JsTarget::Embedded(a) => a.full_receipts().to_vec(),
            JsTarget::Attached(_) => Vec::new(),
        }
    }
    /// Snapshot the substance for cheap rewind — only the embedded engine supports
    /// it (a fork is the live World's own rewind primitive). `None` for attach.
    fn snapshot(&self) -> Option<(Vec<u8>, usize)> {
        match self {
            JsTarget::Embedded(a) => Some((a.snapshot(), a.receipt_count())),
            JsTarget::Attached(_) => None,
        }
    }
    /// Restore the embedded substance to a snapshot. The attach path cannot rewind
    /// here (the live World rewinds itself).
    fn restore(&mut self, bytes: &[u8], keep: usize) -> Result<(), String> {
        match self {
            JsTarget::Embedded(a) => a.restore(bytes, keep),
            JsTarget::Attached(_) => Err("attach path cannot rewind in-JS".into()),
        }
    }
}

thread_local! {
    /// The substance the native functions drive. ONE target per runtime for the spike
    /// (the polynomial-functor interface of a single sovereign cell, embedded OR live).
    /// A real multi-app surface would key by an integer handle returned from
    /// `deos.applet`.
    static CURRENT_APPLET: RefCell<Option<JsTarget>> = const { RefCell::new(None) };
    /// The last error message a native produced (surfaced to the test).
    static LAST_NATIVE_ERROR: RefCell<Option<String>> = const { RefCell::new(None) };
    /// A scratch string for the UTF-8-encode callback to deposit into.
    static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
    /// Snapshot store for `deos.world.snapshot()`/`.rewind(token)`: token → (bytes,
    /// receipt-count-at-snapshot). A snapshot is the integrity-hashed ledger state.
    static SNAPSHOTS: RefCell<Vec<(Vec<u8>, usize)>> = const { RefCell::new(Vec::new()) };
}

/// Install the embedded applet the native functions drive (deos-js's own engine).
pub fn set_current_applet(applet: Applet) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(JsTarget::Embedded(applet)));
}

/// Install an ATTACHED applet — the runtime bound to a PROVIDED live World (the
/// cockpit's real ledger, or a fork). The crawl + fire then drive that World.
pub fn set_current_attached(applet: AttachedApplet) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(JsTarget::Attached(applet)));
}

/// Install a fully-formed [`JsTarget`] (embedded or attached) directly.
pub fn set_current_target(target: JsTarget) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(target));
}

/// Take the target back out (to inspect its ledger/receipts after a JS run).
pub fn take_current_target() -> Option<JsTarget> {
    CURRENT_APPLET.with(|c| c.borrow_mut().take())
}

/// Take the EMBEDDED applet back out, if the current target is embedded (else `None`).
/// Preserves the existing `take_current_applet()` shape for the embedded callers.
pub fn take_current_applet() -> Option<Applet> {
    match CURRENT_APPLET.with(|c| c.borrow_mut().take()) {
        Some(JsTarget::Embedded(a)) => Some(a),
        other => {
            // Not embedded — put it back so an attached caller can take it.
            if let Some(t) = other {
                CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(t));
            }
            None
        }
    }
}

/// The last native-function error, if any.
pub fn last_native_error() -> Option<String> {
    LAST_NATIVE_ERROR.with(|e| e.borrow().clone())
}

fn record_error(msg: String) {
    LAST_NATIVE_ERROR.with(|e| *e.borrow_mut() = Some(msg));
}

/// The JS prelude — builds `deos.applet`/`app.fire`/`app.get`/`app.view` atop the
/// `__deos_*` natives. `app.view.set/get` route to the EPHEMERAL natives (in-memory;
/// never a turn). `deos.applet(spec)` turns each declared affordance name into a
/// method that fires the corresponding verified turn.
const PRELUDE: &str = r#"
    var deos = {
        applet: function(spec) {
            var handle = {
                fire: function(name, arg) { return __deos_fire(String(name), arg | 0); },
                get: function(slot) { return __deos_get(slot | 0); },
                view: {
                    set: function(k, v) { __deos_view_set(String(k), String(v)); },
                    get: function(k) { return __deos_view_get(String(k)); }
                }
            };
            var names = (spec && spec.affordances) || [];
            for (var i = 0; i < names.length; i++) {
                (function(n) {
                    handle[n] = function(arg) { return handle.fire(n, arg | 0); };
                })(names[i]);
            }
            return handle;
        },
        // ── THE REFLECTIVE CRAWL (slice 2) — JS objects crawl the live image ──────
        // Reflection is a cap-bounded, attested READ (confers no authority), distinct
        // from driving (a turn). Every accessor parses JSON from a `__deos_reflect_*`
        // native that projects the live ledger through `deos-reflect`.
        world: {
            // every cell id on the ledger (the unbounded crawl root)
            cells: function() { return JSON.parse(__deos_world_cells()); },
            cellCount: function() { return this.cells().length; },
            // the capability web (nodes + edges)
            ocap: function() { return JSON.parse(__deos_world_ocap()); },
            // cheap fork-based time-travel: snapshot returns a token; rewind(token)
            // restores the ledger to it (a READ-restore — receipts truncate to match).
            snapshot: function() { return __deos_snapshot() | 0; },
            rewind: function(token) { return __deos_rewind(token | 0) | 0; }
        },
        // fuzzy spotter over every cell's faces → [{cell, score, snippet}], best-first.
        search: function(q) { return JSON.parse(__deos_search(String(q))); },
        // ── THE VIEW LANGUAGE (slice 3) — a serializable element-tree (data, NOT gpui) ─
        // `deos.ui.*` build a view-tree describing gpui-component widgets; a button's
        // onClick is `{turn:"<affordance>", arg:N}` (a real turn when rendered+fired);
        // a `bind(() => expr)` node re-reads its value on demand (fine-grained signal).
        // deos-js stays GPUI-FREE: this produces DATA; a separate renderer draws it.
        ui: (function() {
            function node(kind, props, children) {
                var n = { kind: kind, props: props || {} };
                if (children !== undefined) n.children = children;
                return n;
            }
            return {
                vstack: function() { return node("vstack", {}, Array.prototype.slice.call(arguments)); },
                row:    function() { return node("row", {}, Array.prototype.slice.call(arguments)); },
                text:   function(s) { return node("text", { text: String(s) }); },
                // a bound value node: re-evaluates `fn()` each read (signal binding).
                bind:   function(fn) { var n = node("bind", {}); n.read = fn; return n; },
                // a button whose onClick fires affordance `aff` with `arg` — a real turn.
                button: function(label, aff, arg) {
                    return node("button", { label: String(label), onClick: { turn: String(aff), arg: (arg | 0) } });
                },
                input:  function(viewKey) { return node("input", { bindView: String(viewKey) }); },
                list:   function(items) { return node("list", {}, items || []); },
                table:  function(rows) { return node("table", {}, rows || []); }
            };
        })(),
        // a reflective handle on ONE cell: its substances · faces · affordances · frustum.
        cell: function(id) {
            var cid = String(id);
            return {
                id: cid,
                // the four substances (value/authority/state/evidence) as a field tree
                reflect: function() {
                    var j = __deos_cell(cid);
                    return j === "null" ? null : JSON.parse(j);
                },
                // a quick read of a named substance field's value
                field: function(key) {
                    var r = this.reflect();
                    if (!r) return null;
                    for (var i = 0; i < r.fields.length; i++)
                        if (r.fields[i].key === key) return r.fields[i].value;
                    return null;
                },
                // the moldable faces (RawFields · Graph · DomainVisual · Provenance) —
                // each a distinct obs-projection of the SAME cell.
                present: function() {
                    var j = __deos_present(cid);
                    return j === "null" ? null : JSON.parse(j);
                },
                // the cap-gated message list a holder of `viewer`'s authority may fire.
                // `viewer` is an authority label: "none"/"signature"/"proof"/"either".
                affordances: function(viewer) {
                    return JSON.parse(__deos_affordances(String(viewer || "none")));
                },
                // .as(viewer) → the cap-bounded view: which cells `viewer` may crawl,
                // and a reflect() that yields null for an unobservable target.
                as: function(viewer) {
                    var v = String(viewer);
                    return {
                        frustum: function() { return JSON.parse(__deos_frustum(v)); },
                        canObserve: function(target) {
                            var f = this.frustum();
                            return f.visible.indexOf(String(target)) >= 0;
                        },
                        reflect: function(target) {
                            var j = __deos_frustum_reflect(v, String(target));
                            return j === "null" ? null : JSON.parse(j);
                        }
                    };
                }
            };
        }
    };
"#;

/// A real SpiderMonkey runtime with the `deos` binding available.
pub struct JsRuntime {
    rt: Runtime,
    // The engine handle must stay alive for the runtime's lifetime.
    _engine: JSEngine,
}

impl JsRuntime {
    /// Boot a genuine SpiderMonkey runtime. The `deos` binding + prelude are installed
    /// per-[`Self::eval`] (on a fresh global) so a single test script sees them.
    pub fn new() -> Result<Self, String> {
        let engine = JSEngine::init().map_err(|e| format!("JSEngine::init: {e:?}"))?;
        let rt = Runtime::new(engine.handle());
        Ok(JsRuntime { rt, _engine: engine })
    }

    /// Evaluate a JS program against a fresh global that has the `deos` binding. The
    /// program drives the thread-local applet. Returns the script's result as an i32
    /// if it produced one (else `None`).
    pub fn eval(&mut self, source: &str) -> Result<Option<i32>, String> {
        LAST_NATIVE_ERROR.with(|e| *e.borrow_mut() = None);

        let cx = self.rt.cx();
        let realm_opts = RealmOptions::default();
        unsafe {
            rooted!(&in(cx) let global = JS_NewGlobalObject(
                cx,
                &SIMPLE_GLOBAL_CLASS,
                ptr::null_mut(),
                OnNewGlobalHookOption::FireOnNewGlobalHook,
                &*realm_opts,
            ));

            // ENTER THE REALM before defining the natives / running scripts — the
            // proven upstream pattern (callback.rs). Defining a function on, or
            // converting a string within, a global that is NOT the active realm
            // segfaults. `global_and_reborrow` yields the realm-bound global handle +
            // the realm context to use for everything below.
            let mut realm = AutoRealm::new_from_handle(cx, global.handle());
            let (g, realm_cx) = realm.global_and_reborrow();

            // Install the native bridge functions on the realm's global.
            for (name, f, nargs) in [
                // drive (slice 1)
                (c"__deos_fire", native_fire as RawNative, 2u32),
                (c"__deos_get", native_get as RawNative, 1),
                (c"__deos_view_set", native_view_set as RawNative, 2),
                (c"__deos_view_get", native_view_get as RawNative, 1),
                // crawl (slice 2) — the reflective natives (return JSON strings)
                (c"__deos_world_cells", native_world_cells as RawNative, 0),
                (c"__deos_world_ocap", native_world_ocap as RawNative, 0),
                (c"__deos_cell", native_cell as RawNative, 1),
                (c"__deos_frustum", native_frustum as RawNative, 1),
                (c"__deos_frustum_reflect", native_frustum_reflect as RawNative, 2),
                // fan-out — present faces · affordances · snapshot/rewind · spotter
                (c"__deos_present", native_present as RawNative, 1),
                (c"__deos_affordances", native_affordances as RawNative, 1),
                (c"__deos_snapshot", native_snapshot as RawNative, 0),
                (c"__deos_rewind", native_rewind as RawNative, 1),
                (c"__deos_search", native_search as RawNative, 1),
            ] {
                let defined = JS_DefineFunction(realm_cx, g, name.as_ptr(), Some(f), nargs, 0);
                if defined.is_null() {
                    return Err(format!("JS_DefineFunction failed for {name:?}"));
                }
            }

            // (1) install the prelude on this global; (2) run the user's source.
            eval_on(realm_cx, g, PRELUDE)?;
            let r = eval_on(realm_cx, g, source)?;

            if let Some(err) = last_native_error() {
                return Err(format!("native error during eval: {err}"));
            }
            Ok(r)
        }
    }

    /// THE ATTACH RUN — install an [`AttachedApplet`] (bound to a PROVIDED live World)
    /// as the runtime's target, eval `source` against it, then take the target back
    /// out so the caller can read the committed-fire tape. The crawl + fires inside
    /// `source` drive the ATTACHED World's real cells (a receipt landing on the live
    /// ledger), with the cap tooth mounted under the agent's `held`.
    ///
    /// Returns `(script_result, committed_receipt_hashes, the_target_back)`. The
    /// caller keeps the [`AttachedApplet`] (and through it the `WorldSink`) to inspect
    /// the live ledger after the run.
    pub fn run_attached(
        &mut self,
        applet: AttachedApplet,
        source: &str,
    ) -> Result<AttachRunOutcome, String> {
        set_current_attached(applet);
        let eval = self.eval(source);
        let target = take_current_target();
        let attached = match target {
            Some(JsTarget::Attached(a)) => a,
            _ => return Err("attached target vanished during run".into()),
        };
        match eval {
            Ok(result) => Ok(AttachRunOutcome {
                result,
                receipts: attached.receipts().to_vec(),
                fires_committed: attached.receipt_count(),
                applet: attached,
            }),
            Err(e) => Err(e),
        }
    }
}

/// The outcome of a [`JsRuntime::run_attached`]: what the JS did on the live World.
pub struct AttachRunOutcome {
    /// The script's i32 completion value, if any.
    pub result: Option<i32>,
    /// The receipt hashes the JS committed on the live World, in order.
    pub receipts: Vec<[u8; 32]>,
    /// How many verified turns committed (the audit-tape length).
    pub fires_committed: usize,
    /// The attached applet handed back (its `WorldSink` reads the live ledger).
    pub applet: AttachedApplet,
}

type RawNative = unsafe extern "C" fn(*mut RawJSContext, u32, *mut Value) -> bool;

/// Evaluate `source` against `global`, returning an i32 result if produced. The
/// rooted `rval` receives the script's completion value. `cx` must be the active
/// realm's context.
fn eval_on(
    cx: &mut SmContext,
    global: mozjs::rust::HandleObject,
    source: &str,
) -> Result<Option<i32>, String> {
    rooted!(&in(cx) let mut rval = UndefinedValue());
    let options = CompileOptionsWrapper::new(cx, c"deos.js".to_owned(), 1);
    match evaluate_script(cx, global, source, rval.handle_mut(), options) {
        Ok(()) => {
            let v = rval.get();
            if v.is_int32() {
                Ok(Some(v.to_int32()))
            } else {
                Ok(None)
            }
        }
        Err(()) => Err("evaluate_script returned an error".to_string()),
    }
}

/// Pull a UTF-8 String out of a JS value argument (the raw handle from `CallArgs::get`).
unsafe fn arg_string(cx: &mut SmContext, raw: mozjs::jsapi::HandleValue) -> String {
    let handle = mozjs::rust::Handle::from_raw(raw);
    let js = mozjs::rust::ToString(cx.raw_cx(), handle);
    rooted!(&in(cx) let rooted_str = js);
    unsafe extern "C" fn cb(message: *const core::ffi::c_char) {
        let m = CStr::from_ptr(message);
        let s = str::from_utf8(m.to_bytes()).unwrap_or("").to_string();
        SCRATCH.with(|sc| *sc.borrow_mut() = s);
    }
    EncodeStringToUTF8(cx, rooted_str.handle().into(), cb);
    SCRATCH.with(|sc| sc.borrow().clone())
}

/// Pull an i32 out of a JS value argument (the raw handle from `CallArgs::get`).
unsafe fn arg_i32(raw: mozjs::jsapi::HandleValue) -> i32 {
    let v = mozjs::rust::Handle::from_raw(raw).get();
    if v.is_int32() {
        v.to_int32()
    } else if v.is_double() {
        v.to_double() as i32
    } else {
        0
    }
}

// ── The native bridge functions ───────────────────────────────────────────────────

/// `__deos_fire(name, arg)` — fire an affordance = ONE cap-gated verified turn.
/// Returns the model's value at slot 0 after the turn (for the counter shape), or -1
/// on refusal (the cap tooth) / executor rejection.
unsafe extern "C" fn native_fire(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    if args.argc_ < 1 {
        record_error("__deos_fire requires (name, arg)".into());
        args.rval().set(Int32Value(-1));
        return true;
    }
    let name = arg_string(&mut cx, args.get(0));
    let arg = if args.argc_ >= 2 {
        arg_i32(args.get(1)) as i64
    } else {
        0
    };

    // A cap-gate REFUSAL is an EXPECTED, JS-observable outcome (returns -1 with NO
    // receipt) — NOT a fatal eval error. Only a genuine fault (no applet, or the
    // executor rejecting an AUTHORIZED turn) poisons the eval.
    let outcome = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        match guard.as_mut() {
            Some(target) => match target.fire(&name, arg) {
                Ok(_receipt_hash) => FireOutcome::Committed(target.get_u64(0) as i32),
                Err(crate::applet::FireError::Unauthorized { .. }) => FireOutcome::Refused,
                Err(crate::applet::FireError::UnknownAffordance(n)) => {
                    FireOutcome::Fatal(format!("unknown affordance '{n}'"))
                }
                Err(crate::applet::FireError::Executor(r)) => {
                    FireOutcome::Fatal(format!("executor rejected authorized turn: {r}"))
                }
            },
            None => FireOutcome::Fatal("no applet installed".into()),
        }
    });

    match outcome {
        FireOutcome::Committed(v) => args.rval().set(Int32Value(v)),
        FireOutcome::Refused => args.rval().set(Int32Value(-1)),
        FireOutcome::Fatal(e) => {
            record_error(e);
            args.rval().set(Int32Value(-1));
        }
    }
    true
}

/// The three faces of a fire from JS: committed (a verified turn), refused (the cap
/// gate said no — expected, JS sees -1), or fatal (a real fault that poisons eval).
enum FireOutcome {
    Committed(i32),
    Refused,
    Fatal(String),
}

/// `__deos_get(slot)` — a witnessed read off the live ledger.
unsafe extern "C" fn native_get(_context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let args = CallArgs::from_vp(vp, argc);
    let slot = if args.argc_ >= 1 {
        arg_i32(args.get(0)) as usize
    } else {
        0
    };
    let v = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| a.get_u64(slot) as i32)
            .unwrap_or(-1)
    });
    args.rval().set(Int32Value(v));
    true
}

/// `__deos_view_set(key, value)` — ephemeral view-state. NO turn, NO receipt.
unsafe extern "C" fn native_view_set(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    if args.argc_ < 2 {
        record_error("__deos_view_set requires (key, value)".into());
        args.rval().set(UndefinedValue());
        return true;
    }
    let key = arg_string(&mut cx, args.get(0));
    let val = arg_string(&mut cx, args.get(1));
    CURRENT_APPLET.with(|c| {
        if let Some(a) = c.borrow_mut().as_mut() {
            a.set_view(&key, &val);
        }
    });
    args.rval().set(UndefinedValue());
    true
}

/// `__deos_view_get(key)` — read ephemeral view-state. Returns 1 if present else 0.
unsafe extern "C" fn native_view_get(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let key = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let present = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| a.get_view(&key).is_some())
            .unwrap_or(false)
    });
    args.rval().set(Int32Value(if present { 1 } else { 0 }));
    true
}

// ── THE REFLECTIVE CRAWL natives (slice 2) — each returns a JSON STRING ────────────

/// Set the rval of a native call to a freshly-allocated JS string. Returns false (the
/// native should return false) only on allocation failure.
unsafe fn return_string(cx: &mut SmContext, args: &CallArgs, s: &str) -> bool {
    let js_str = JS_NewStringCopyN(cx, s.as_ptr() as *const core::ffi::c_char, s.len());
    if js_str.is_null() {
        record_error("JS_NewStringCopyN failed".into());
        args.rval().set(UndefinedValue());
        return false;
    }
    args.rval().set(StringValue(&*js_str));
    true
}

/// `__deos_world_cells()` → JSON array of every cell id on the applet's ledger.
unsafe extern "C" fn native_world_cells(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_APPLET.with(|c| {
        let mut out = "[]".to_string();
        if let Some(a) = c.borrow().as_ref() {
            a.with_ledger(&mut |l| out = reflect_binding::world_cells_json(l));
        }
        out
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_world_ocap()` → JSON of the capability web (nodes + edges).
unsafe extern "C" fn native_world_ocap(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_APPLET.with(|c| {
        let mut out = "{\"nodes\":[],\"edges\":[]}".to_string();
        if let Some(a) = c.borrow().as_ref() {
            a.with_ledger(&mut |l| out = reflect_binding::world_ocap_json(l));
        }
        out
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_cell(id)` → JSON of the cell's four substances (or `"null"` if absent).
unsafe extern "C" fn native_cell(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let id_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match reflect_binding::parse_cell_id(&id_hex) {
            Some(id) => {
                let mut out = "null".to_string();
                applet.with_ledger(&mut |l| {
                    out = reflect_binding::cell_json(l, &id).unwrap_or_else(|| "null".to_string())
                });
                out
            }
            None => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_frustum(viewer)` → JSON of the cap-bounded view (which cells viewer crawls).
unsafe extern "C" fn native_frustum(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let viewer_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string(),
        };
        match reflect_binding::parse_cell_id(&viewer_hex) {
            Some(viewer) => {
                let mut out = "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string();
                applet.with_ledger(&mut |l| out = reflect_binding::frustum_json(l, &viewer));
                out
            }
            None => "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_frustum_reflect(viewer, target)` → the cell JSON if `viewer` may observe
/// `target`, else `"null"` (the attested read: an unreachable cell is absent).
unsafe extern "C" fn native_frustum_reflect(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let viewer_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let target_hex = if args.argc_ >= 2 { arg_string(&mut cx, args.get(1)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match (
            reflect_binding::parse_cell_id(&viewer_hex),
            reflect_binding::parse_cell_id(&target_hex),
        ) {
            (Some(viewer), Some(target)) => {
                let mut out = "null".to_string();
                applet.with_ledger(&mut |l| {
                    out = reflect_binding::frustum_reflect_json(l, &viewer, &target)
                });
                out
            }
            _ => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

// ── THE FAN-OUT natives (present · affordances · snapshot/rewind · spotter) ────────

/// `__deos_present(id)` → the moldable faces JSON (RawFields/Graph/DomainVisual/
/// Provenance), or `"null"` if the cell is absent.
unsafe extern "C" fn native_present(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let id_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match reflect_binding::parse_cell_id(&id_hex) {
            Some(id) => {
                let receipts = applet.full_receipts();
                let mut out = "null".to_string();
                applet.with_ledger(&mut |l| {
                    out = reflect_binding::cell_present_json(l, &id, &receipts)
                        .unwrap_or_else(|| "null".to_string())
                });
                out
            }
            None => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_affordances(viewerAuthLabel)` → the cap-gated message list the holder of
/// that authority may fire, as JSON. The label is "none"/"signature"/"proof"/"either".
unsafe extern "C" fn native_affordances(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let label = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { "none".into() };
    let held = parse_auth_label(&label);
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        match guard.as_ref() {
            Some(a) => reflect_binding::cell_affordances_json(&a.cell(), &a.affordance_specs(), &held),
            None => "[]".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_snapshot()` → an integer token denoting the saved ledger state (for rewind).
unsafe extern "C" fn native_snapshot(_context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let args = CallArgs::from_vp(vp, argc);
    let token = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        match guard.as_ref().and_then(|a| a.snapshot()) {
            Some((bytes, count)) => SNAPSHOTS.with(|s| {
                let mut v = s.borrow_mut();
                v.push((bytes, count));
                (v.len() - 1) as i32
            }),
            None => -1,
        }
    });
    args.rval().set(Int32Value(token));
    true
}

/// `__deos_rewind(token)` → restore the ledger to snapshot `token`. Returns 1 on
/// success, -1 on a bad token or restore failure. The audit tape truncates to match —
/// time-travel that leaves no phantom receipts.
unsafe extern "C" fn native_rewind(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let _cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let token = if args.argc_ >= 1 { arg_i32(args.get(0)) } else { -1 };
    let ok = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        let applet = match guard.as_mut() {
            Some(a) => a,
            None => return false,
        };
        let snap = SNAPSHOTS.with(|s| {
            s.borrow().get(token as usize).cloned()
        });
        match snap {
            Some((bytes, count)) => applet.restore(&bytes, count).is_ok(),
            None => false,
        }
    });
    args.rval().set(Int32Value(if ok { 1 } else { -1 }));
    true
}

/// `__deos_search(q)` → the spotter hits JSON (fuzzy over every cell's faces).
unsafe extern "C" fn native_search(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let q = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let mut out = "[]".to_string();
        if let Some(a) = c.borrow().as_ref() {
            a.with_ledger(&mut |l| out = reflect_binding::spotter_json(l, &q));
        }
        out
    });
    return_string(&mut cx, &args, &json)
}

/// Parse an authority label from JS into an `AuthRequired` (the held authority for
/// affordance projection). Unknown → `None` (the broadest — sees everything).
fn parse_auth_label(label: &str) -> dregg_cell::AuthRequired {
    use dregg_cell::AuthRequired;
    match label.to_lowercase().as_str() {
        "signature" | "sig" => AuthRequired::Signature,
        "proof" => AuthRequired::Proof,
        "either" => AuthRequired::Either,
        "impossible" => AuthRequired::Impossible,
        _ => AuthRequired::None,
    }
}

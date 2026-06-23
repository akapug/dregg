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
use mozjs::jsval::{Int32Value, UndefinedValue};
use mozjs::realm::AutoRealm;
use mozjs::rooted;
use mozjs::rust::wrappers2::{EncodeStringToUTF8, JS_DefineFunction, JS_NewGlobalObject};
use mozjs::rust::{
    evaluate_script, CompileOptionsWrapper, JSEngine, RealmOptions, Runtime, SIMPLE_GLOBAL_CLASS,
};

use crate::applet::Applet;

thread_local! {
    /// The applet the native functions drive. ONE applet per runtime for the spike
    /// (the polynomial-functor interface of a single sovereign cell). A real multi-app
    /// surface would key by an integer handle returned from `deos.applet`.
    static CURRENT_APPLET: RefCell<Option<Applet>> = const { RefCell::new(None) };
    /// The last error message a native produced (surfaced to the test).
    static LAST_NATIVE_ERROR: RefCell<Option<String>> = const { RefCell::new(None) };
    /// A scratch string for the UTF-8-encode callback to deposit into.
    static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
}

/// Install the applet the native functions drive.
pub fn set_current_applet(applet: Applet) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(applet));
}

/// Take the applet back out (to inspect its ledger/receipts after a JS run).
pub fn take_current_applet() -> Option<Applet> {
    CURRENT_APPLET.with(|c| c.borrow_mut().take())
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
                (c"__deos_fire", native_fire as RawNative, 2u32),
                (c"__deos_get", native_get as RawNative, 1),
                (c"__deos_view_set", native_view_set as RawNative, 2),
                (c"__deos_view_get", native_view_get as RawNative, 1),
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
            Some(applet) => match applet.fire(&name, arg) {
                Ok(_receipt) => FireOutcome::Committed(applet.get_u64(0) as i32),
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

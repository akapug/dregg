//! The **native deos-js runtime** — a pure-Rust `boa` engine driving cell-attached JS.
//!
//! A fresh [`boa_engine::Context`] has NO host bindings (no fetch/fs/process/clock
//! beyond ECMAScript `Date`). The sandbox boundary IS the absence of ambient
//! functions; [`NativeRuntime`] installs only the cap-bounded host surface a cell's
//! attached JS is allowed to touch. The keystone is `t(turn, arg)` — fire an
//! affordance = commit ONE cap-gated verified turn (the same path a static `{turn,arg}`
//! button runs). See `docs/deos/JS-ON-CELLS.md`.
//!
//! Host state is shared with the native function via a thread-local (the proven
//! deos-js pattern): [`NativeRuntime::run`] installs the [`CellApplet`] into the
//! thread-local for the eval's duration, then takes it back out with its committed
//! receipt tape.

use std::cell::RefCell;

use boa_engine::{js_string, Context, JsNativeError, JsValue, NativeFunction, Source};

use crate::applet::{CellApplet, FireError};

thread_local! {
    /// The applet the installed host functions drive, for the duration of one
    /// [`NativeRuntime::run`]. The native `t` borrows it, fires, and puts it back.
    static CURRENT_APPLET: RefCell<Option<CellApplet>> = const { RefCell::new(None) };
    /// The last cap-tooth / executor refusal a host fn hit (surfaced to the caller even
    /// though the JS sees a thrown error).
    static LAST_FIRE_ERROR: RefCell<Option<FireError>> = const { RefCell::new(None) };
}

/// What a [`NativeRuntime::run`] produced.
pub struct RunOutcome {
    /// The applet handed back, carrying its committed receipt tape + live model.
    pub applet: CellApplet,
    /// The script's completion value coerced to `i32`, if it produced a number.
    pub result: Option<i32>,
    /// The last fire refusal a host fn hit during the run (the cap tooth or the
    /// executor), if any — even though the JS observed a thrown error.
    pub last_fire_error: Option<FireError>,
}

/// The cap-bounded host function `t(turn, arg)` — **fire an affordance**. This is the
/// ONLY authority the cell-JS has: every other host capability (fs/net/clock) is
/// absent. It bridges into [`CellApplet::fire`], so the cell-JS commits the SAME
/// cap-gated verified turn a static `{turn,arg}` button does.
///
/// `t(name)` fires with arg 0; `t(name, n)` fires with the integer arg. Returns the new
/// value of the affordance's slot (a witnessed read off the live ledger). An unknown
/// affordance, a cap-tooth refusal, or an executor rejection throws a JS error AND is
/// recorded in [`LAST_FIRE_ERROR`] for the host.
fn native_fire(
    _this: &JsValue,
    args: &[JsValue],
    ctx: &mut Context,
) -> boa_engine::JsResult<JsValue> {
    let name = match args.first() {
        Some(v) => v.to_string(ctx)?.to_std_string_escaped(),
        None => {
            return Err(JsNativeError::typ()
                .with_message("t(turn, arg): missing affordance name")
                .into())
        }
    };
    let arg: i64 = match args.get(1) {
        Some(v) if !v.is_undefined() => v.to_i32(ctx)? as i64,
        _ => 0,
    };

    // Fire inside the thread-local borrow; on success read back the model scalar (the
    // witnessed value `t` returns). The PoC counter surface writes slot 0.
    let fired: Result<i64, FireError> = CURRENT_APPLET.with(|cell| {
        let mut slot = cell.borrow_mut();
        let applet = slot
            .as_mut()
            .expect("a CellApplet is installed for the duration of run()");
        applet
            .fire(&name, arg)
            .map(|_receipt| applet.get_u64(0) as i64)
    });

    match fired {
        Ok(value) => Ok(JsValue::from(value)),
        Err(e) => {
            LAST_FIRE_ERROR.with(|s| *s.borrow_mut() = Some(e.clone()));
            Err(JsNativeError::typ()
                .with_message(format!("t({name:?}) refused: {e}"))
                .into())
        }
    }
}

/// The native (pure-Rust, no-servo) deos-js runtime. One engine that runs cell-attached
/// JS in the cockpit (gpui) AND the web shell — `boa` compiles to native and wasm with
/// no C toolchain.
pub struct NativeRuntime {
    context: Context,
}

impl Default for NativeRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeRuntime {
    /// Boot a fresh runtime. The `Context` starts with NO host bindings — the sandbox.
    pub fn new() -> Self {
        NativeRuntime {
            context: Context::default(),
        }
    }

    /// **Run cell-attached JS** against `applet`. Installs the cap-bounded host surface
    /// (`t(turn, arg)`) onto a fresh global, evals `source`, then hands the applet back
    /// with its committed receipt tape. The script can do nothing but call the installed
    /// host functions + ECMAScript builtins — no fs/net/clock/ambient authority.
    pub fn run(&mut self, applet: CellApplet, source: &str) -> Result<RunOutcome, String> {
        // Install the cap-bounded host functions onto the global.
        self.context
            .register_global_callable(js_string!("t"), 2, NativeFunction::from_fn_ptr(native_fire))
            .map_err(|e| format!("register t(): {e}"))?;

        CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(applet));
        LAST_FIRE_ERROR.with(|s| *s.borrow_mut() = None);

        let eval = self.context.eval(Source::from_bytes(source));

        let applet = CURRENT_APPLET
            .with(|c| c.borrow_mut().take())
            .ok_or_else(|| "the applet vanished during run".to_string())?;
        let last_fire_error = LAST_FIRE_ERROR.with(|s| s.borrow_mut().take());

        match eval {
            Ok(value) => {
                let result = value.as_number().map(|n| n as i32);
                Ok(RunOutcome {
                    applet,
                    result,
                    last_fire_error,
                })
            }
            Err(e) => Err(format!("JS error: {e}")),
        }
    }
}

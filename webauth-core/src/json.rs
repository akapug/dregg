//! A tiny, dependency-free JSON **object writer** — enough to emit the flat
//! `{key: value}` records this crate returns (`/whoami`, the login response, the
//! challenge, error bodies, the audit line) with correct string escaping, and
//! nothing more.
//!
//! ## Why not `format!`
//!
//! The prior server hand-built every JSON body with `format!` and ad-hoc
//! sanitization (`subject.replace('"', "")` in one place, nothing in another),
//! so a value containing `"`, `\`, a control character, or a newline could break
//! the framing. Auth values are issuer-controlled today, but "trusted today"
//! is exactly the assumption a real service must not bake in. This writer escapes
//! per RFC 8259 (`"`, `\`, `\b`, `\f`, `\n`, `\r`, `\t`, and `\u00xx` for the
//! remaining control bytes) so every string field is safe regardless of source.

/// A flat JSON object being assembled key-by-key. Insertion order is preserved.
#[derive(Debug, Default)]
pub struct JsonObject {
    buf: String,
    started: bool,
}

impl JsonObject {
    pub fn new() -> Self {
        Self {
            buf: String::from("{"),
            started: false,
        }
    }

    fn key(&mut self, key: &str) {
        if self.started {
            self.buf.push(',');
        }
        self.started = true;
        escape_into(&mut self.buf, key);
        self.buf.push(':');
    }

    /// Append a string-valued field (escaped).
    pub fn str(&mut self, key: &str, value: &str) -> &mut Self {
        self.key(key);
        escape_into(&mut self.buf, value);
        self
    }

    /// Append an integer-valued field.
    pub fn int(&mut self, key: &str, value: i64) -> &mut Self {
        self.key(key);
        self.buf.push_str(&value.to_string());
        self
    }

    /// Append a boolean-valued field.
    pub fn bool(&mut self, key: &str, value: bool) -> &mut Self {
        self.key(key);
        self.buf.push_str(if value { "true" } else { "false" });
        self
    }

    /// Append a `null`-valued field.
    pub fn null(&mut self, key: &str) -> &mut Self {
        self.key(key);
        self.buf.push_str("null");
        self
    }

    /// Append a field whose value is already-rendered raw JSON (e.g. a nested
    /// object built by another [`JsonObject`]). The caller owns its validity.
    pub fn raw(&mut self, key: &str, value: &str) -> &mut Self {
        self.key(key);
        self.buf.push_str(value);
        self
    }

    /// Finish the object and return the JSON string.
    pub fn finish(mut self) -> String {
        self.buf.push('}');
        self.buf
    }
}

/// Escape `s` as a quoted JSON string, appending to `out`.
pub fn escape_into(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Escape `s` as a quoted JSON string.
pub fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    escape_into(&mut out, s);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn object_round_trips_flat_fields() {
        let out = {
            let mut o = JsonObject::new();
            o.str("subject", "dregg:abc")
                .int("expires", 42)
                .bool("ok", true)
                .null("cap");
            o.finish()
        };
        assert_eq!(
            out,
            r#"{"subject":"dregg:abc","expires":42,"ok":true,"cap":null}"#
        );
    }

    #[test]
    fn strings_are_escaped() {
        assert_eq!(escape("a\"b"), r#""a\"b""#);
        assert_eq!(escape("a\\b"), r#""a\\b""#);
        assert_eq!(escape("a\nb"), r#""a\nb""#);
        // A raw control byte becomes \u00xx (built without a literal control
        // char in source to keep the file clean).
        let ctrl = char::from(1u8).to_string();
        assert_eq!(escape(&ctrl), "\"\\u0001\"");
    }

    #[test]
    fn injection_cannot_escape_the_value() {
        let mut o = JsonObject::new();
        o.str("subject", "x\",\"admin\":\"true");
        let out = o.finish();
        // The whole hostile string stays inside the subject value.
        assert!(!out.contains(r#""admin":"true""#), "{out}");
        assert!(out.contains(r#""subject":"x\",\"admin\":\"true""#), "{out}");
    }
}

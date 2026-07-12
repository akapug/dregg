//! **The ONE affordance-transport codec** — the single encode/decode for a
//! [`ViewNode::Button`](crate::tree::ViewNode)'s `{turn, arg}` affordance as it rides back to the
//! executor over whatever channel a surface backend uses.
//!
//! Every backend carries the SAME `{turn, arg}` payload on actuation; they differed only in the
//! byte shape of the channel that carries it (Discord's component custom-id, Telegram's
//! `callback_data`, a web `data-turn`/form field). This canonicalizes that shape into one
//! transport-parameterized codec so the four ad-hoc encodings become one function with a
//! [`AffordanceTransport`] argument. The Discord `deosturn:<turn>:<arg>` shape is the general
//! case; Telegram/web are the un-prefixed `<turn>:<arg>` variant of the same codec.
//!
//! Round-trips for every transport: `parse_affordance_id(&affordance_id(turn, arg, t), t) ==
//! Some((turn, arg))`.

/// The channel a surface backend carries an affordance `{turn, arg}` back on. Selects the byte
/// shape of the encoded id; the payload is identical across all of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AffordanceTransport {
    /// A Discord message-component **custom-id** — prefixed `deosturn:<turn>:<arg>` so a bot's
    /// component handler can tell one of ours from any other component id (a non-`deosturn:` id
    /// decodes to `None`, i.e. "not ours, ignore").
    Discord,
    /// A Telegram inline-keyboard button's **`callback_data`** — the un-prefixed `<turn>:<arg>`
    /// (Telegram caps `callback_data` at 64 bytes; the prefix is dead weight there, and the
    /// keyboard is only ever our own). Decoded by splitting on the LAST separator.
    Telegram,
    /// A web control's affordance payload — the un-prefixed `<turn>:<arg>` (the same shape the
    /// `data-turn`/`data-arg` attributes carry as a pair). Identical codec to [`Self::Telegram`].
    Web,
}

/// The Discord custom-id prefix carrying a [`ViewNode::Button`](crate::tree::ViewNode)'s affordance
/// through Discord's component-id channel — the Discord analogue of the web renderer's `data-turn`.
pub const TURN_PREFIX: &str = "deosturn";

/// The `<turn>:<arg>` separator (the un-prefixed transports split on it; Discord uses it too, after
/// its prefix).
const SEP: char = ':';

/// Encode an affordance `{turn, arg}` into the id `transport` carries it on. The inverse of
/// [`parse_affordance_id`] for the same `transport`.
///
/// - [`AffordanceTransport::Discord`] → `deosturn:<turn>:<arg>` (prefixed).
/// - [`AffordanceTransport::Telegram`] / [`AffordanceTransport::Web`] → `<turn>:<arg>` (un-prefixed).
pub fn affordance_id(turn: &str, arg: i64, transport: AffordanceTransport) -> String {
    match transport {
        AffordanceTransport::Discord => format!("{TURN_PREFIX}{SEP}{turn}{SEP}{arg}"),
        AffordanceTransport::Telegram | AffordanceTransport::Web => format!("{turn}{SEP}{arg}"),
    }
}

/// Decode an id minted by [`affordance_id`] for the same `transport` back into `(turn, arg)`.
/// `None` if the id is not one of ours for that transport (Discord: missing/`!= deosturn` prefix)
/// or is malformed (no separator / a non-integer arg) — a press the surface never minted.
///
/// Discord splits after the prefix (`splitn(3, ':')`); the un-prefixed transports split on the
/// LAST separator (`rsplit_once`), so a `turn` may in principle contain earlier separators.
pub fn parse_affordance_id(id: &str, transport: AffordanceTransport) -> Option<(String, i64)> {
    match transport {
        AffordanceTransport::Discord => {
            let mut it = id.splitn(3, SEP);
            if it.next()? != TURN_PREFIX {
                return None;
            }
            let turn = it.next()?.to_string();
            let arg = it.next()?.parse().ok()?;
            Some((turn, arg))
        }
        AffordanceTransport::Telegram | AffordanceTransport::Web => {
            let (turn, arg) = id.rsplit_once(SEP)?;
            Some((turn.to_string(), arg.parse().ok()?))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALL: [AffordanceTransport; 3] = [
        AffordanceTransport::Discord,
        AffordanceTransport::Telegram,
        AffordanceTransport::Web,
    ];

    /// The one codec round-trips `encode → decode` for EVERY transport (the move-#1 property).
    #[test]
    fn round_trips_every_transport() {
        for t in ALL {
            for (turn, arg) in [
                ("inc", 7i64),
                ("choose", 0),
                ("bump", -1),
                ("trade_blows", 999),
            ] {
                let id = affordance_id(turn, arg, t);
                assert_eq!(
                    parse_affordance_id(&id, t),
                    Some((turn.to_string(), arg)),
                    "{t:?} round-trips {turn}/{arg} via {id}"
                );
            }
        }
    }

    /// The Discord transport is prefixed; the un-prefixed transports are not (the shapes the four
    /// old encodings used).
    #[test]
    fn transport_byte_shapes() {
        assert_eq!(
            affordance_id("inc", 7, AffordanceTransport::Discord),
            "deosturn:inc:7"
        );
        assert_eq!(
            affordance_id("inc", 7, AffordanceTransport::Telegram),
            "inc:7"
        );
        assert_eq!(affordance_id("inc", 7, AffordanceTransport::Web), "inc:7");
    }

    /// A Discord id lacking the `deosturn:` prefix is "not ours" → `None` (the bot's component
    /// handler ignores foreign component ids).
    #[test]
    fn discord_rejects_a_foreign_id() {
        assert_eq!(
            parse_affordance_id("deos:abcd:approve", AffordanceTransport::Discord),
            None
        );
        assert_eq!(
            parse_affordance_id("other:thing", AffordanceTransport::Discord),
            None
        );
    }

    /// The un-prefixed transports split on the LAST separator (an arg stays unambiguous even if a
    /// turn contained an earlier one).
    #[test]
    fn unprefixed_splits_on_last_separator() {
        assert_eq!(
            parse_affordance_id("a:b:3", AffordanceTransport::Telegram),
            Some(("a:b".to_string(), 3))
        );
        assert_eq!(parse_affordance_id("noarg", AffordanceTransport::Web), None);
    }
}

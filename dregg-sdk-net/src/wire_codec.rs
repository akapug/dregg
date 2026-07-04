//! No-I/O wire protocol codec over the wire-free [`DreggEngine`].
//!
//! The `DreggEngine` core (executor + ledger + token + proof core) lives in
//! [`dregg_sdk::embed`] and carries no networking deps. This module is its
//! networked face: encode/decode of the dregg wire protocol and the server-side
//! [`WireCodec::process_message`] logic, both built on `dregg-wire`.

use dregg_sdk::embed::DreggEngine;
use dregg_wire::message::WireMessage;
use dregg_wire::server::ProofVerifier;

/// No-I/O wire protocol codec.
///
/// Provides encode/decode for the dregg wire protocol without any transport.
/// The caller handles reading bytes from and writing bytes to their own I/O layer.
pub struct WireCodec;

impl WireCodec {
    /// Decode a wire protocol message from a raw payload (without length prefix).
    ///
    /// The caller is responsible for framing (reading the 4-byte LE length prefix
    /// and providing exactly that many bytes here).
    pub fn decode(payload: &[u8]) -> Result<WireMessage, String> {
        dregg_wire::codec::decode(payload).map_err(|e| e.to_string())
    }

    /// Encode a wire protocol message to bytes (with length prefix).
    ///
    /// Returns a complete frame ready to write to any byte stream.
    pub fn encode(msg: &WireMessage) -> Result<Vec<u8>, String> {
        dregg_wire::codec::encode(msg).map_err(|e| e.to_string())
    }

    /// The framing header size (4 bytes, little-endian u32 payload length).
    pub const HEADER_SIZE: usize = 4;

    /// Parse the length prefix from a 4-byte header.
    ///
    /// Returns the payload size in bytes. The caller should then read exactly
    /// that many bytes and pass them to [`Self::decode`].
    pub fn parse_header(header: &[u8; 4]) -> u32 {
        u32::from_le_bytes(*header)
    }

    /// Process a decoded message against an engine, producing response messages.
    ///
    /// This implements the server-side protocol logic without any I/O:
    /// - `Hello` -> `Welcome`
    /// - `PresentToken` -> `PresentationResult`
    /// - `RequestAttestedRoot` -> `AttestedRoot`
    /// - `Ping` -> `Pong`
    /// - Others -> None
    ///
    /// The caller sends the returned messages back over their transport.
    pub fn process_message(engine: &DreggEngine, msg: WireMessage) -> Vec<WireMessage> {
        match msg {
            WireMessage::Hello {
                protocol_version, ..
            } => {
                if protocol_version != dregg_wire::message::PROTOCOL_VERSION {
                    return vec![WireMessage::Error {
                        code: dregg_wire::message::error_codes::UNSUPPORTED_VERSION,
                        message: format!(
                            "unsupported protocol version {protocol_version}, expected {}",
                            dregg_wire::message::PROTOCOL_VERSION
                        ),
                    }];
                }
                vec![WireMessage::Welcome {
                    federation_root: engine.federation_root(),
                    member_count: 1,
                    node_id: engine.executor().local_federation_id,
                    node_name: "embed".to_string(),
                }]
            }
            WireMessage::PresentToken {
                proof,
                request,
                federation_root,
            } => {
                // Verify root freshness.
                if federation_root != engine.federation_root() {
                    return vec![WireMessage::PresentationResult {
                        accepted: false,
                        reason: Some("stale federation root".into()),
                        request_digest: request.digest(),
                    }];
                }

                // Verify the STARK proof using the wire server's verifier.
                let accepted = dregg_wire::server::StarkVerifier
                    .verify(&proof, &request.action, &request.resource)
                    .unwrap_or(false);

                vec![WireMessage::PresentationResult {
                    accepted,
                    reason: if accepted {
                        None
                    } else {
                        Some("proof verification failed".into())
                    },
                    request_digest: request.digest(),
                }]
            }
            WireMessage::RequestAttestedRoot => {
                vec![WireMessage::AttestedRoot {
                    root: engine.federation_root(),
                    height: engine.executor().block_height,
                    timestamp: engine.executor().current_timestamp,
                    signatures: vec![],
                    threshold_qc: None,
                }]
            }
            WireMessage::Ping { seq, .. } => {
                vec![WireMessage::Pong {
                    seq,
                    timestamp: engine.executor().current_timestamp,
                }]
            }
            // Response messages and unknown -> no reply.
            _ => vec![],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_sdk::embed::EngineConfig;

    #[test]
    fn wire_codec_roundtrip() {
        let msg = WireMessage::Ping {
            seq: 42,
            timestamp: 1234567890,
        };
        let encoded = WireCodec::encode(&msg).unwrap();
        // Skip the 4-byte header.
        let payload = &encoded[WireCodec::HEADER_SIZE..];
        let decoded = WireCodec::decode(payload).unwrap();
        assert_eq!(decoded, msg);
    }

    #[test]
    fn process_hello_message() {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        let hello = WireMessage::Hello {
            node_id: [0xaa; 32],
            node_name: "test-client".into(),
            protocol_version: dregg_wire::message::PROTOCOL_VERSION,
            capabilities: vec![],
        };
        let responses = WireCodec::process_message(&engine, hello);
        assert_eq!(responses.len(), 1);
        match &responses[0] {
            WireMessage::Welcome { node_name, .. } => assert_eq!(node_name, "embed"),
            other => panic!("expected Welcome, got {other:?}"),
        }
    }

    #[test]
    fn process_ping_message() {
        let engine = DreggEngine::new(EngineConfig::for_testing());
        let ping = WireMessage::Ping {
            seq: 7,
            timestamp: 100,
        };
        let responses = WireCodec::process_message(&engine, ping);
        assert_eq!(responses.len(), 1);
        match &responses[0] {
            WireMessage::Pong { seq, .. } => assert_eq!(*seq, 7),
            other => panic!("expected Pong, got {other:?}"),
        }
    }
}

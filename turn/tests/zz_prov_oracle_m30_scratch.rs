// TRANSIENT M30 ground-truth measurement — DELETE after capture. Not committed.
// Deserializes the exact serde-JSON the sdk-ts differential emits into the REAL
// `dregg_turn::Turn` and postcard-encodes it — the ground truth the TS
// `encodeTurn` must match byte-for-byte.
use dregg_turn::Turn;

#[test]
fn zz_prov_oracle_emit() {
    let path = std::env::var("PROV_ORACLE_JSON").expect("set PROV_ORACLE_JSON");
    let json = std::fs::read_to_string(&path).expect("read json");
    let turn: Turn = serde_json::from_str(&json).expect("deserialize Turn");
    let bytes = postcard::to_allocvec(&turn).expect("postcard encode");
    println!("PROV_ORACLE_HEX={}", hex::encode(&bytes));
    println!("PROV_ORACLE_LEN={}", bytes.len());
}

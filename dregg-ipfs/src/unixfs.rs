//! `unixfs` — **chunked content**: a real UnixFS/dag-pb file DAG builder + the
//! verified DAG-walk read.
//!
//! The single-block bridge ([`crate::pin_blob`] / [`crate::fetch_verified`]) is exact
//! but only reaches content that fits in one IPFS block. Larger content is what IPFS
//! *chunks*: raw leaf blocks under a `dag-pb` UnixFS-file root whose CID is a hash over
//! the **link structure**, not the file bytes — so a flat re-hash cannot check it, and
//! the old bridge simply refused it ([`crate::client::IpfsError::NotVerifiableByFlatHash`]).
//! This module closes that hole with two halves that both stay verify-don't-trust:
//!
//! - [`build_file_dag`] / [`pin_file`] — split content into ≤[`DEFAULT_CHUNK_SIZE`]
//!   raw leaves and fold them into a **balanced** UnixFS-file DAG (each parent a
//!   `dag-pb` node linking ≤[`DEFAULT_MAX_LINKS`] children). Every block is
//!   blake3-addressed, so the leaves reuse the exact single-block CID
//!   ([`crate::cid::Cid::raw_blake3`]) and the root is a `dag-pb` blake3 CID.
//! - [`fetch_cat`] — the **verified DAG walk**: fetch the root block, re-hash it
//!   against the root CID, parse its links, and recurse — re-witnessing *every* block
//!   (leaf and interior) against its own CID before using it, then concatenating the
//!   leaves in order. A lying node that flips any byte moves that block's hash and is
//!   refused. The reassembled length is checked against the UnixFS `filesize`.
//!
//! Because [`fetch_cat`] follows links generically (a link to a `dag-pb` child is
//! walked recursively), it reads a multi-level DAG produced by a stock `ipfs add
//! --hash=blake3` too, not only the single-level shape this builder writes. **Honest
//! boundary:** the block-level content-addressing is exact and enforced; *byte-exact
//! parity* with go-ipfs's default chunker boundaries + balanced-layout Tsizes (so this
//! builder's root CID equals a live `ipfs add`'s) is reviewed-go — this builder emits a
//! valid, self-consistent, fully verifiable blake3 UnixFS DAG that [`fetch_cat`]
//! round-trips.

use crate::cid::{CODEC_DAG_PB, CODEC_RAW, Cid};
use crate::client::{IpfsClient, IpfsError};

/// The default leaf chunk size — 256 KiB, the go-ipfs default fixed-size chunker.
pub const DEFAULT_CHUNK_SIZE: usize = 256 * 1024;

/// The default maximum links per `dag-pb` node — the go-ipfs balanced-DAG default
/// (`ipfs.DefaultLinksPerBlock`).
pub const DEFAULT_MAX_LINKS: usize = 174;

/// One content-addressed block of a built DAG: its CID and its exact bytes. Pin these
/// (leaves first) to make the DAG retrievable; the [`root`](FileDag::root) is the CID
/// to commit + fetch.
#[derive(Clone, Debug)]
pub struct Block {
    /// The block's CID (raw leaf, or `dag-pb` interior/root node).
    pub cid: Cid,
    /// The block's exact bytes (a raw leaf's content, or a serialized `PBNode`).
    pub bytes: Vec<u8>,
}

/// A built UnixFS file DAG: the root CID to commit, plus every block to pin.
#[derive(Clone, Debug)]
pub struct FileDag {
    /// The DAG root CID (a raw-leaf CID for content ≤ one chunk, else a `dag-pb` root).
    pub root: Cid,
    /// All blocks (leaves + interior nodes + root), safe to pin in order (children
    /// before parents).
    pub blocks: Vec<Block>,
}

/// Build a UnixFS file DAG over `content` with the default chunk size + fan-out.
pub fn build_file_dag(content: &[u8]) -> FileDag {
    build_file_dag_with(content, DEFAULT_CHUNK_SIZE, DEFAULT_MAX_LINKS)
}

/// Build a UnixFS file DAG with explicit `chunk_size` + `max_links`.
///
/// Content that fits in one chunk becomes a single **raw** leaf (root == that leaf CID
/// == `raw(blake3(content))`, identical to the single-block bridge). Larger content is
/// chunked into raw leaves and folded into a balanced `dag-pb` tree.
pub fn build_file_dag_with(content: &[u8], chunk_size: usize, max_links: usize) -> FileDag {
    assert!(chunk_size > 0 && max_links >= 2, "degenerate DAG params");

    // A single chunk is a bare raw leaf — no dag-pb wrapper (matches raw-leaves add).
    if content.len() <= chunk_size {
        let cid = Cid::raw_blake3(content);
        return FileDag {
            root: cid.clone(),
            blocks: vec![Block {
                cid,
                bytes: content.to_vec(),
            }],
        };
    }

    let mut blocks: Vec<Block> = Vec::new();

    // Level 0: the raw leaves.
    let mut level: Vec<Node> = content
        .chunks(chunk_size)
        .map(|chunk| {
            let cid = Cid::raw_blake3(chunk);
            blocks.push(Block {
                cid: cid.clone(),
                bytes: chunk.to_vec(),
            });
            Node {
                cid,
                filesize: chunk.len() as u64,
                dag_size: chunk.len() as u64,
            }
        })
        .collect();

    // Fold up into balanced dag-pb parents until a single root remains.
    while level.len() > 1 {
        let mut next: Vec<Node> = Vec::with_capacity(level.len().div_ceil(max_links));
        for group in level.chunks(max_links) {
            let (node, bytes) = build_parent(group);
            blocks.push(Block {
                cid: node.cid.clone(),
                bytes,
            });
            next.push(node);
        }
        level = next;
    }

    FileDag {
        root: level.into_iter().next().expect("nonempty").cid,
        blocks,
    }
}

/// Build a UnixFS file DAG over `content` and pin every block to `client`, returning
/// the root CID (to commit in the cell). Children are pinned before parents so the DAG
/// is complete before the root becomes referenceable.
pub fn pin_file<C: IpfsClient>(client: &C, content: &[u8]) -> Result<Cid, IpfsError> {
    let dag = build_file_dag(content);
    for block in &dag.blocks {
        client.put_block(&block.cid, &block.bytes)?;
    }
    Ok(dag.root)
}

/// **The verified DAG-walk read.** Fetch and reassemble the content addressed by
/// `root` from `client`, re-witnessing *every* block against its own CID — no trust in
/// the serving node. Handles a bare raw blob, a single-level DAG, or a multi-level DAG.
///
/// Refuses: a block whose bytes do not hash to its CID
/// ([`IpfsError::CidMismatch`]); a non-blake3 / non-UnixFS CID
/// ([`IpfsError::NotVerifiableByFlatHash`]); a DAG deeper than 64 levels
/// ([`IpfsError::DagTooDeep`], guarding against a cyclic/adversarial DAG); a
/// reassembled length disagreeing with the UnixFS `filesize`.
pub fn fetch_cat<C: IpfsClient>(client: &C, root: &Cid) -> Result<Vec<u8>, IpfsError> {
    let mut out = Vec::new();
    walk(client, root, 0, &mut out)?;
    Ok(out)
}

const MAX_DEPTH: usize = 64;

fn walk<C: IpfsClient>(
    client: &C,
    cid: &Cid,
    depth: usize,
    out: &mut Vec<u8>,
) -> Result<(), IpfsError> {
    if depth > MAX_DEPTH {
        return Err(IpfsError::DagTooDeep {
            max_depth: MAX_DEPTH,
        });
    }
    let block = client.get(cid)?;
    // Every block in a blake3 DAG is re-witnessed against its own CID: the tamper
    // tooth that makes the whole walk trustless.
    if !cid.is_blake3() {
        return Err(IpfsError::NotVerifiableByFlatHash(cid.to_string_cid()));
    }
    let recomputed = *blake3::hash(&block).as_bytes();
    if recomputed.as_slice() != cid.digest.as_slice() {
        return Err(IpfsError::CidMismatch {
            requested: cid.to_string_cid(),
            got: Cid::from_blake3_digest(cid.codec, recomputed).to_string_cid(),
        });
    }

    match cid.codec {
        CODEC_RAW => {
            // A raw leaf: its bytes are file content.
            out.extend_from_slice(&block);
            Ok(())
        }
        CODEC_DAG_PB => {
            let node = parse_pb_node(&block)?;
            let start = out.len();
            for link in &node.links {
                let child = Cid::from_bytes(link)
                    .map_err(|e| IpfsError::BadDagNode(format!("bad link CID: {e}")))?;
                walk(client, &child, depth + 1, out)?;
            }
            // If the node carried a UnixFS filesize, the reassembled span must match —
            // a truncated/padded DAG is refused even if every block self-verifies.
            if let Some(filesize) = node.filesize {
                let got = (out.len() - start) as u64;
                if got != filesize {
                    return Err(IpfsError::BadDagNode(format!(
                        "unixfs filesize {filesize} != reassembled {got}"
                    )));
                }
            }
            Ok(())
        }
        other => Err(IpfsError::NotVerifiableByFlatHash(format!(
            "codec 0x{other:x} is not a UnixFS file DAG"
        ))),
    }
}

// -- the balanced-tree parent builder -----------------------------------------

/// A DAG node summary used while folding levels: its CID, the UnixFS filesize of the
/// subtree it roots, and its cumulative serialized DAG size (for a link's `Tsize`).
struct Node {
    cid: Cid,
    filesize: u64,
    dag_size: u64,
}

/// Build one `dag-pb` UnixFS-file parent over `children`; returns the node summary and
/// the serialized block bytes.
fn build_parent(children: &[Node]) -> (Node, Vec<u8>) {
    let filesize: u64 = children.iter().map(|c| c.filesize).sum();
    let blocksizes: Vec<u64> = children.iter().map(|c| c.filesize).collect();
    let unixfs_data = encode_unixfs_file(filesize, &blocksizes);

    // Canonical dag-pb: Links (field 2) precede Data (field 1).
    let mut node = Vec::new();
    for c in children {
        // Tsize = the cumulative serialized size of the linked subtree.
        let link = encode_pb_link(&c.cid.to_bytes(), c.dag_size);
        pb_field_bytes(&mut node, 2, &link);
    }
    pb_field_bytes(&mut node, 1, &unixfs_data);

    let cid = Cid::from_blake3_digest(CODEC_DAG_PB, *blake3::hash(&node).as_bytes());
    let dag_size = node.len() as u64 + children.iter().map(|c| c.dag_size).sum::<u64>();
    (
        Node {
            cid,
            filesize,
            dag_size,
        },
        node,
    )
}

// -- minimal protobuf (dag-pb + UnixFS) ---------------------------------------

/// UnixFS `DataType::File` (= 2).
const UNIXFS_TYPE_FILE: u64 = 2;

/// Encode the UnixFS `Data` message for a file node: `Type=File`, `filesize`, and the
/// per-child `blocksizes`. (No inline `Data` — the bytes live in the raw leaves.)
fn encode_unixfs_file(filesize: u64, blocksizes: &[u64]) -> Vec<u8> {
    let mut out = Vec::new();
    pb_field_varint(&mut out, 1, UNIXFS_TYPE_FILE); // Type
    pb_field_varint(&mut out, 3, filesize); // filesize
    for &bs in blocksizes {
        pb_field_varint(&mut out, 4, bs); // repeated blocksizes
    }
    out
}

/// Encode a dag-pb `PBLink`: `Hash` (field 1, the child CID bytes) + `Tsize` (field 3).
/// `Name` (field 2) is omitted (empty) for a file DAG.
fn encode_pb_link(hash: &[u8], tsize: u64) -> Vec<u8> {
    let mut out = Vec::new();
    pb_field_bytes(&mut out, 1, hash); // Hash
    pb_field_varint(&mut out, 3, tsize); // Tsize
    out
}

/// A parsed dag-pb node: the ordered child link CIDs (raw bytes) + the UnixFS
/// `filesize` if the `Data` field carried one.
struct PbNode {
    links: Vec<Vec<u8>>,
    filesize: Option<u64>,
}

/// Parse a dag-pb `PBNode`: collect every `Links` (field 2) `Hash`, and read the
/// UnixFS `filesize` from the `Data` (field 1) message.
fn parse_pb_node(bytes: &[u8]) -> Result<PbNode, IpfsError> {
    let mut links = Vec::new();
    let mut filesize = None;
    let mut p = 0usize;
    while p < bytes.len() {
        let (field, wire, val) = pb_read_field(bytes, &mut p)?;
        match (field, wire) {
            // Links (field 2): a length-delimited PBLink submessage.
            (2, 2) => {
                let link = as_bytes(val)?;
                links.push(parse_pb_link(link)?);
            }
            // Data (field 1): the UnixFS Data message.
            (1, 2) => {
                filesize = parse_unixfs_filesize(as_bytes(val)?)?;
            }
            _ => {}
        }
    }
    Ok(PbNode { links, filesize })
}

/// Parse a `PBLink`, returning the `Hash` (field 1) bytes.
fn parse_pb_link(bytes: &[u8]) -> Result<Vec<u8>, IpfsError> {
    let mut p = 0usize;
    let mut hash = None;
    while p < bytes.len() {
        let (field, wire, val) = pb_read_field(bytes, &mut p)?;
        if field == 1 && wire == 2 {
            hash = Some(as_bytes(val)?.to_vec());
        }
    }
    hash.ok_or_else(|| IpfsError::BadDagNode("PBLink had no Hash".into()))
}

/// Read the UnixFS `filesize` (field 3) from a `Data` message, if present.
fn parse_unixfs_filesize(bytes: &[u8]) -> Result<Option<u64>, IpfsError> {
    let mut p = 0usize;
    let mut filesize = None;
    while p < bytes.len() {
        let (field, wire, val) = pb_read_field(bytes, &mut p)?;
        if field == 3 && wire == 0 {
            if let PbVal::Varint(v) = val {
                filesize = Some(v);
            }
        }
    }
    Ok(filesize)
}

// -- protobuf wire primitives -------------------------------------------------

enum PbVal<'a> {
    Varint(u64),
    Bytes(&'a [u8]),
}

fn as_bytes(v: PbVal<'_>) -> Result<&[u8], IpfsError> {
    match v {
        PbVal::Bytes(b) => Ok(b),
        PbVal::Varint(_) => Err(IpfsError::BadDagNode("expected length-delimited".into())),
    }
}

/// Read one protobuf field `(field_number, wire_type, value)`. Supports wire types 0
/// (varint) and 2 (length-delimited); others are a malformed-node error.
fn pb_read_field<'a>(bytes: &'a [u8], p: &mut usize) -> Result<(u64, u64, PbVal<'a>), IpfsError> {
    let key = pb_read_varint(bytes, p)?;
    let field = key >> 3;
    let wire = key & 0x7;
    match wire {
        0 => {
            let v = pb_read_varint(bytes, p)?;
            Ok((field, wire, PbVal::Varint(v)))
        }
        2 => {
            let len = pb_read_varint(bytes, p)? as usize;
            let end = p
                .checked_add(len)
                .filter(|&e| e <= bytes.len())
                .ok_or_else(|| IpfsError::BadDagNode("length-delimited overrun".into()))?;
            let slice = &bytes[*p..end];
            *p = end;
            Ok((field, wire, PbVal::Bytes(slice)))
        }
        other => Err(IpfsError::BadDagNode(format!(
            "unsupported wire type {other}"
        ))),
    }
}

fn pb_read_varint(bytes: &[u8], p: &mut usize) -> Result<u64, IpfsError> {
    let mut result: u64 = 0;
    let mut shift = 0u32;
    loop {
        let b = *bytes
            .get(*p)
            .ok_or_else(|| IpfsError::BadDagNode("truncated varint".into()))?;
        *p += 1;
        if shift >= 64 {
            return Err(IpfsError::BadDagNode("varint overflow".into()));
        }
        result |= ((b & 0x7f) as u64) << shift;
        if b & 0x80 == 0 {
            return Ok(result);
        }
        shift += 7;
    }
}

fn pb_write_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let mut byte = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if v == 0 {
            break;
        }
    }
}

/// Write a varint field: `key = (field << 3) | 0` then the value.
fn pb_field_varint(out: &mut Vec<u8>, field: u64, v: u64) {
    pb_write_varint(out, field << 3);
    pb_write_varint(out, v);
}

/// Write a length-delimited field: `key = (field << 3) | 2`, length, then bytes.
fn pb_field_bytes(out: &mut Vec<u8>, field: u64, data: &[u8]) {
    pb_write_varint(out, (field << 3) | 2);
    pb_write_varint(out, data.len() as u64);
    out.extend_from_slice(data);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::client::MockIpfs;

    #[test]
    fn single_chunk_is_a_bare_raw_leaf() {
        // Content within one chunk builds no dag-pb wrapper: the root IS the raw-blake3
        // single-block CID, identical to the bridge's whole-blob pin.
        let content = b"small enough to be one block";
        let dag = build_file_dag_with(content, 256, DEFAULT_MAX_LINKS);
        assert_eq!(dag.root, Cid::raw_blake3(content));
        assert_eq!(dag.blocks.len(), 1);
        assert!(dag.root.is_raw_blake3());
    }

    #[test]
    fn chunked_file_round_trips_through_the_verified_walk() {
        let node = MockIpfs::new();
        // ~5 chunks of 64 bytes each: forces a dag-pb root over raw leaves.
        let content: Vec<u8> = (0..300u32).map(|i| (i * 7 % 251) as u8).collect();
        let root = {
            let dag = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
            assert!(
                dag.root.is_dag_pb(),
                "multi-chunk content roots at a dag-pb node"
            );
            for b in &dag.blocks {
                node.put_block(&b.cid, &b.bytes).unwrap();
            }
            dag.root
        };
        // The verified walk reassembles the exact bytes.
        assert_eq!(fetch_cat(&node, &root).unwrap(), content);
    }

    #[test]
    fn multi_level_dag_round_trips() {
        let node = MockIpfs::new();
        // 20 leaves with max_links=3 → a 3-level balanced tree.
        let content: Vec<u8> = (0..20u32 * 8).map(|i| i as u8).collect();
        let dag = build_file_dag_with(&content, 8, 3);
        assert!(dag.root.is_dag_pb());
        assert!(
            dag.blocks.len() > 21,
            "interior nodes exist: {}",
            dag.blocks.len()
        );
        for b in &dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        assert_eq!(fetch_cat(&node, &dag.root).unwrap(), content);
    }

    #[test]
    fn pin_file_then_fetch_cat() {
        let node = MockIpfs::new();
        let content: Vec<u8> = (0..1000u32).map(|i| (i % 256) as u8).collect();
        let root = pin_file(&node, &content).unwrap();
        assert_eq!(fetch_cat(&node, &root).unwrap(), content);
    }

    #[test]
    fn a_tampered_leaf_is_refused_by_the_walk() {
        let node = MockIpfs::new();
        let content: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let dag = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
        for b in &dag.blocks {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        // Tamper a raw leaf (the first block is a leaf).
        let leaf = &dag.blocks[0];
        node.tamper(&leaf.cid, b"this is not the committed chunk!");
        let err = fetch_cat(&node, &dag.root).unwrap_err();
        assert!(matches!(err, IpfsError::CidMismatch { .. }), "got {err:?}");
    }

    #[test]
    fn a_missing_block_is_not_found() {
        let node = MockIpfs::new();
        let content: Vec<u8> = (0..300u32).map(|i| i as u8).collect();
        let dag = build_file_dag_with(&content, 64, DEFAULT_MAX_LINKS);
        // Pin everything EXCEPT one leaf.
        for b in dag.blocks.iter().skip(1) {
            node.put_block(&b.cid, &b.bytes).unwrap();
        }
        // Now forget one leaf so it is unavailable during the walk.
        node.forget(&dag.blocks[0].cid);
        assert!(matches!(
            fetch_cat(&node, &dag.root),
            Err(IpfsError::NotFound(_))
        ));
    }

    #[test]
    fn pb_varint_round_trips() {
        for v in [0u64, 1, 127, 128, 300, 262144, u64::MAX] {
            let mut buf = Vec::new();
            pb_write_varint(&mut buf, v);
            let mut p = 0;
            assert_eq!(pb_read_varint(&buf, &mut p).unwrap(), v);
            assert_eq!(p, buf.len());
        }
    }
}

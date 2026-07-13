// Gold-KAT generator: o1js Poseidon.hash (Mina-Poseidon / kimchi params over
// Pasta Fp) for a set of fixed inputs. The Rust probe at
// circuit-prove/sketches/mina-pasta-hash-probe asserts bit-exact equality
// against these outputs (the Pasta analogue of the Poseidon2Bn254 gold KAT in
// circuit-prove/src/dregg_outer_config.rs).
//
// Run: node scripts/poseidon-kat.mjs
import { Field, Poseidon, MerkleTree } from 'o1js';

const P = Field.ORDER; // Pasta Fp modulus
console.log('# o1js', '1.x', 'Field.ORDER =', '0x' + P.toString(16));

const cases = [
  ['empty', []],
  ['zero', [0n]],
  ['one', [1n]],
  ['two', [2n]],
  ['seq012', [0n, 1n, 2n]],
  ['pminus1', [P - 1n]],
  ['pminus1_pair', [P - 1n, P - 1n]],
  ['block_boundary', [1n, 2n, 3n, 4n, 5n]],
  ['compress_LR', [123456789n, 987654321n]], // the 2->1 Merkle compress shape
];

for (const [name, ins] of cases) {
  const h = Poseidon.hash(ins.map((x) => Field(x)));
  console.log(name, '=', '0x' + h.toBigInt().toString(16).padStart(64, '0'));
}

// MMCS-shape cross-check: o1js MerkleTree (nodes = Poseidon.hash([l, r])),
// depth-2 root over leaves [1,2,3,4] — matched by the Rust probe's `compress`.
const tree = new MerkleTree(3);
tree.setLeaf(0n, Field(1));
tree.setLeaf(1n, Field(2));
tree.setLeaf(2n, Field(3));
tree.setLeaf(3n, Field(4));
console.log(
  'merkle_root_1234 =',
  '0x' + tree.getRoot().toBigInt().toString(16).padStart(64, '0')
);

/* crypto-floor.c — the REAL §8 crypto floor for the executor PD.
 *
 * Replaces crypto-stub.c (panic-if-reached, WRONG arity/types) with the eight
 * `@[extern]` crypto portals of `Dregg2/Crypto/PortalFloor.lean`, implemented at
 * the EXACT Lean C ABI the closure expects (read from the emitted facet
 * `metatheory/.lake/build/ir/Dregg2/Crypto/PortalFloor.c`):
 *
 *   uint8_t      dregg_ed25519_verify (lean_object*, lean_object*, lean_object*); // Nat,Nat,Nat -> Bool
 *   uint8_t      dregg_stark_verify   (lean_object*, lean_object*);               // Nat,Nat     -> Bool
 *   lean_object* dregg_pedersen_commit(lean_object*, lean_object*);               // Int,Int     -> Nat
 *   lean_object* dregg_poseidon2_hash (lean_object*, lean_object*);               // Nat,Nat     -> Nat
 *   lean_object* dregg_blake3_hash    (lean_object*);                             // List Nat    -> Nat
 *   lean_object* dregg_nullifier_derive(lean_object*);                            // Nat         -> Nat
 *   uint8_t      dregg_aead_open      (lean_object*, lean_object*, lean_object*); // Nat,Nat,Nat -> Bool
 *   lean_object* dregg_hmac_sha256    (lean_object*, lean_object*);               // Nat,Nat     -> Nat
 *
 * OWNERSHIP. The closure's `___boxed` wrappers pass their owned params straight
 * to these externs with NO surrounding inc/dec — so each extern OWNS its
 * arguments and must `lean_dec` them, and returns a freshly-owned result (the
 * standard Lean owned-`lean_obj_arg` convention). We extract values with the
 * BORROWING `lean_uint64_of_nat`, then `lean_dec` each owned arg.
 *
 * CRYPTO. The hashes are wired to the SAME carried implementations the
 * verifier-stark PD runs on seL4 — the Plonky3-conformant Poseidon2 over BabyBear
 * + BLAKE3 — via the `dreggcf_*` entry points of the `dregg-crypto-floor` Rust
 * staticlib (crypto-floor/, built for aarch64-unknown-linux-musl). So a turn that
 * hashes (Merkle node / commitment / nullifier / transcript) now computes a real,
 * field-correct digest on-device instead of aborting.
 *
 * HONEST SCOPE. Poseidon2 (§4), BLAKE3 (§5), the Poseidon2-derived nullifier (§6),
 * and the BLAKE3-keyed MAC (§8 HMAC analogue) are REAL. The three primitives on a
 * DIFFERENT crypto surface NOT carried in verifier-stark — ed25519/curve25519 (§1),
 * Pedersen/elliptic-curve (§3), ChaCha20-Poly1305 AEAD (§7) — and the STARK verify
 * over an abstract Nat pair (§2) keep an ABI-CORRECT, FAIL-CLOSED floor here: a
 * verify returns 0 (reject, NEVER a spurious accept); a commit returns a
 * deterministic placeholder digest. A hashing turn does not reach them. Each logs
 * the precise named primitive once if reached, so the next wiring step is exact.
 */
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* ---- the real carried crypto (Rust staticlib dregg-crypto-floor) ----------- */
extern uint64_t dreggcf_poseidon2_2to1(uint64_t left, uint64_t right);
extern uint64_t dreggcf_blake3_to_field(const uint8_t *data, size_t len);
extern uint64_t dreggcf_nullifier(uint64_t note);
extern uint64_t dreggcf_keyed_mac(uint64_t key, const uint8_t *msg, size_t msg_len);
extern uint8_t  dreggcf_stark_verify_abstract(uint64_t stmt, uint64_t proof);

/* Report a not-yet-carried primitive exactly once (so a reached floor names the
 * precise next wiring step rather than spamming or silently faking). */
static void floor_note_once(const char *prim) {
    static const char *seen[8];
    static int n = 0;
    for (int i = 0; i < n; i++) if (seen[i] == prim) return;
    if (n < 8) seen[n++] = prim;
    fprintf(stderr, "[exec] crypto floor: %s not carried in verifier-stark "
                    "(fail-closed; the hashing path does not reach it)\n", prim);
}

/* ===========================================================================
 * §4 — Poseidon2 (Nat,Nat -> Nat). REAL.
 * =========================================================================== */
lean_object *dregg_poseidon2_hash(lean_object *a, lean_object *b) {
    uint64_t la = lean_uint64_of_nat(a);   /* borrowing extract */
    uint64_t lb = lean_uint64_of_nat(b);
    lean_dec(a);                           /* we own a, b — release them */
    lean_dec(b);
    uint64_t h = dreggcf_poseidon2_2to1(la, lb);
    return lean_uint64_to_nat(h);          /* fresh owned Nat */
}

/* ===========================================================================
 * §5 — BLAKE3 (List Nat -> Nat). REAL.
 *
 * Walk the cons-list, taking each element's low byte (a `List Nat` of byte/limb
 * values; the canonical transcript form is a byte list), BLAKE3 it, and bridge
 * the digest into the field exactly as the carried STARK does. nil = scalar
 * (boxed 0, tag 0); cons = ctor tag 1, field 0 = head Nat, field 1 = tail.
 * =========================================================================== */
lean_object *dregg_blake3_hash(lean_object *lst) {
    /* First pass: count length (borrowing). */
    size_t len = 0;
    for (lean_object *p = lst; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) len++;

    uint8_t *buf = NULL;
    if (len > 0) {
        buf = (uint8_t *)malloc(len);
        if (!buf) { lean_dec(lst); abort(); }
        size_t i = 0;
        for (lean_object *p = lst; !lean_is_scalar(p); p = lean_ctor_get(p, 1)) {
            lean_object *head = lean_ctor_get(p, 0);          /* borrowed Nat */
            buf[i++] = (uint8_t)(lean_uint64_of_nat(head) & 0xff);
        }
    }
    lean_dec(lst);                                            /* own the list */
    uint64_t h = dreggcf_blake3_to_field(buf, len);
    free(buf);
    return lean_uint64_to_nat(h);
}

/* ===========================================================================
 * §6 — Nullifier (Nat -> Nat). REAL (Poseidon2-derived deterministic tag).
 * =========================================================================== */
lean_object *dregg_nullifier_derive(lean_object *note) {
    uint64_t n = lean_uint64_of_nat(note);
    lean_dec(note);
    return lean_uint64_to_nat(dreggcf_nullifier(n));
}

/* ===========================================================================
 * §8 — HMAC analogue (Nat,Nat -> Nat). REAL (BLAKE3-keyed MAC).
 *
 * The message Nat's little-endian bytes are MAC'd under a key derived from the
 * key Nat. A real keyed PRF/MAC over the carried hash (the assumption is
 * BLAKE3-keyed unforgeability, the standard analogue of HMAC-SHA256's).
 * =========================================================================== */
lean_object *dregg_hmac_sha256(lean_object *key, lean_object *msg) {
    uint64_t k = lean_uint64_of_nat(key);
    uint64_t m = lean_uint64_of_nat(msg);
    lean_dec(key);
    lean_dec(msg);
    uint8_t mbytes[8];
    for (int i = 0; i < 8; i++) mbytes[i] = (uint8_t)((m >> (8 * i)) & 0xff);
    return lean_uint64_to_nat(dreggcf_keyed_mac(k, mbytes, 8));
}

/* ===========================================================================
 * §2 — STARK verify (Nat,Nat -> Bool). FAIL-CLOSED wiring.
 *
 * Two abstract Nats carry no checkable StarkProof; the carried real verifier
 * (stark_core::stark::verify) needs the structured proof bytes, supplied out of
 * band by the executor PD's proof-carrying turn. Until that byte channel is
 * routed here, reject (0) — NEVER accept without a verified proof.
 * =========================================================================== */
uint8_t dregg_stark_verify(lean_object *stmt, lean_object *proof) {
    uint64_t s = lean_uint64_of_nat(stmt);
    uint64_t p = lean_uint64_of_nat(proof);
    lean_dec(stmt);
    lean_dec(proof);
    floor_note_once("stark-verify(abstract-Nat)");
    return dreggcf_stark_verify_abstract(s, p); /* always 0 (sound reject) */
}

/* ===========================================================================
 * §1 — ed25519 verify (Nat,Nat,Nat -> Bool). NOT carried — fail-closed.
 * curve25519 is a different crypto surface than the carried STARK hashes.
 * =========================================================================== */
uint8_t dregg_ed25519_verify(lean_object *pk, lean_object *m, lean_object *s) {
    lean_dec(pk);
    lean_dec(m);
    lean_dec(s);
    floor_note_once("ed25519");
    return 0; /* reject — never a spurious accept */
}

/* ===========================================================================
 * §7 — AEAD open (Nat,Nat,Nat -> Bool). NOT carried — fail-closed.
 * ChaCha20-Poly1305 + X25519 is a different surface than the carried hashes.
 * =========================================================================== */
uint8_t dregg_aead_open(lean_object *key, lean_object *ct, lean_object *aad) {
    lean_dec(key);
    lean_dec(ct);
    lean_dec(aad);
    floor_note_once("aead-open");
    return 0; /* reject — never a spurious authenticate */
}

/* ===========================================================================
 * §3 — Pedersen commit (Int,Int -> Nat). NOT carried — deterministic placeholder.
 * The real Pedersen is an elliptic-curve commitment (not carried in
 * verifier-stark). We return a DETERMINISTIC Poseidon2 digest of the two Int
 * limbs so the function is total + collision-resistant-shaped, but it is NOT a
 * binding curve commitment — labeled, and not reached by a hashing turn. (Int is
 * a Nat-or-negSucc `lean_object*`; we take its low magnitude bits.)
 * =========================================================================== */
lean_object *dregg_pedersen_commit(lean_object *v, lean_object *r) {
    /* Int low bits: lean_uint64_of_nat reads the underlying magnitude object for
     * a nonneg Int (a Nat); for negSucc it reads the wrapped Nat. Either way a
     * deterministic limb — adequate for a labeled placeholder digest. */
    uint64_t lv = lean_is_scalar(v) ? (uint64_t)lean_unbox(v) : lean_uint64_of_nat(v);
    uint64_t lr = lean_is_scalar(r) ? (uint64_t)lean_unbox(r) : lean_uint64_of_nat(r);
    lean_dec(v);
    lean_dec(r);
    floor_note_once("pedersen-commit(curve)");
    return lean_uint64_to_nat(dreggcf_poseidon2_2to1(lv, lr));
}

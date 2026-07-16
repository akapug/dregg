// THE PROTOCOL-SOURCE ORACLE — read the Rust source of truth at test time.
//
// sdk-py cannot mis-encode: it depends on dregg-turn/dregg-cell BY PATH and
// encodes with the same `postcard` the node decodes with. sdk-ts MUST port the
// codec to TypeScript, so it is structurally capable of drifting — and did
// (M30: dropped `CapabilityRef::provenance`; signed `dregg-action-sig-v2`
// against a `v3` executor). The byte differential (`wire.test.mjs`) closes the
// half of that class it can SEE: for the effects TS models, it proves the bytes
// equal the real Rust postcard, because its oracle is the freshly-built
// dregg-wasm — the actual protocol code.
//
// It cannot close the other half. A differential only compares what you think
// to compare. The Rust `Effect` enum has 34 variants; the TS union models 7.
// A 35th variant, or a new field on a modeled one, is INVISIBLE to a byte
// comparison over the 7 fixtures TS happens to build. That is the residual
// drift channel, and it is the one that is silent.
//
// This module is the second oracle, mirroring sdk-py's
// `effect_variants_from_protocol_source`: it PARSES the protocol's own Rust
// source at test time and hands back the vocabulary — variant names, their
// POSITIONAL INDEX (postcard encodes an enum as a varint of its index; the
// protocol's own comment states the law: "a new variant MUST append, never
// insert — the durable postcard codec is index-sensitive"), and field names.
//
// ⚠ WHY IT CANNOT GO STALE: there is no checked-in, generated, or gitignored
// artifact here. The oracle is `../turn/src/action.rs` itself, read on every
// run. Every function below FAILS LOUD — missing file, unreadable, or the enum
// no longer present is a THROW, never a skip and never a cached fallback. A
// differential whose oracle can be absent proves nothing (M30).

import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));

/** Repo-root-relative path to a protocol source file. sdk-ts sits at the root. */
export const protocolFile = (rel) => join(here, "..", "..", rel);

function readProtocol(rel) {
  const path = protocolFile(rel);
  let src;
  try {
    src = readFileSync(path, "utf8");
  } catch (e) {
    throw new Error(
      `PROTOCOL SOURCE MISSING — cannot read ${rel} (${path}): ${e.message}. ` +
        `The vocabulary oracle reads the protocol's Rust source at test time; it has ` +
        `NO cached copy to fall back to, by design. If the protocol moved, this gate ` +
        `must be pointed at its new home — not skipped.`,
    );
  }
  return src;
}

/**
 * Strip Rust comments: line comments (two slashes, incl. doc comments) and
 * block comments, including nested ones. String literals are respected, so a
 * comment marker inside a Rust string literal is not mistaken for a comment.
 */
function stripComments(src) {
  let out = "";
  let i = 0;
  let block = 0;
  while (i < src.length) {
    const two = src.slice(i, i + 2);
    if (block > 0) {
      if (two === "/*") { block++; i += 2; continue; }
      if (two === "*/") { block--; i += 2; continue; }
      i++;
      continue;
    }
    if (two === "/*") { block++; i += 2; continue; }
    if (two === "//") {
      while (i < src.length && src[i] !== "\n") i++;
      continue;
    }
    if (src[i] === '"') {
      out += src[i++];
      while (i < src.length) {
        if (src[i] === "\\") { out += src.slice(i, i + 2); i += 2; continue; }
        out += src[i];
        if (src[i] === '"') { i++; break; }
        i++;
      }
      continue;
    }
    out += src[i++];
  }
  return out;
}

/** Extract the brace-balanced body following `header` (e.g. `pub enum Effect {`). */
function bodyAfter(src, header, what, rel) {
  const at = src.indexOf(header);
  if (at === -1) {
    throw new Error(
      `PROTOCOL VOCABULARY LOST — ${rel} no longer contains \`${header}\`. ` +
        `The ${what} oracle parses that declaration to learn the wire vocabulary. ` +
        `It was renamed, moved, or restructured: this gate is RED until the oracle ` +
        `is pointed at the real declaration. It must not pass by assuming the old shape.`,
    );
  }
  const open = src.indexOf("{", at + header.length - 1);
  let depth = 0;
  for (let k = open; k < src.length; k++) {
    if (src[k] === "{") depth++;
    else if (src[k] === "}") {
      depth--;
      if (depth === 0) return src.slice(open + 1, k);
    }
  }
  throw new Error(`unbalanced braces parsing ${what} in ${rel}`);
}

/** Split on top-level commas, tracking (), [], {}, and <> generics. */
function splitTopLevel(body) {
  const parts = [];
  let depth = 0;
  let angle = 0;
  let cur = "";
  for (let i = 0; i < body.length; i++) {
    const ch = body[i];
    if (ch === "{" || ch === "(" || ch === "[") depth++;
    else if (ch === "}" || ch === ")" || ch === "]") depth--;
    else if (ch === "<") angle++;
    else if (ch === ">" && angle > 0 && body[i - 1] !== "-") angle--;
    if (ch === "," && depth === 0 && angle === 0) {
      parts.push(cur);
      cur = "";
      continue;
    }
    cur += ch;
  }
  if (cur.trim()) parts.push(cur);
  return parts.map((p) => p.trim()).filter(Boolean);
}

/** Drop leading `#[...]` attributes from a variant/field declaration. */
function dropAttrs(decl) {
  let s = decl.trim();
  while (s.startsWith("#")) {
    const open = s.indexOf("[");
    if (open === -1) break;
    let depth = 0;
    let k = open;
    for (; k < s.length; k++) {
      if (s[k] === "[") depth++;
      else if (s[k] === "]") { depth--; if (depth === 0) break; }
    }
    s = s.slice(k + 1).trim();
  }
  return s;
}

/** Field names of a `{ a: T, b: U }` variant/struct body, in declaration order. */
function fieldNames(braceBody) {
  return splitTopLevel(braceBody)
    .map(dropAttrs)
    .map((f) => {
      const m = /^(?:pub(?:\s*\([^)]*\))?\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:/.exec(f);
      return m ? m[1] : null;
    })
    .filter(Boolean);
}

/**
 * Parse a Rust enum into its ordered variants.
 *
 * Returns `[{ name, index, kind: "struct"|"tuple"|"unit", fields }]` where
 * `index` is the POSITIONAL serde/postcard discriminant — the thing the TS
 * codec writes as a varint, and the thing an inserted variant silently shifts.
 */
export function rustEnum(rel, enumName) {
  const src = stripComments(readProtocol(rel));
  const body = bodyAfter(src, `pub enum ${enumName} {`, `\`${enumName}\``, rel);
  const variants = splitTopLevel(body).map(dropAttrs).filter(Boolean);
  const parsed = variants.map((v, index) => {
    const nameMatch = /^([A-Za-z_][A-Za-z0-9_]*)/.exec(v);
    if (!nameMatch) throw new Error(`unparsable ${enumName} variant #${index}: ${v.slice(0, 60)}`);
    const name = nameMatch[1];
    const rest = v.slice(name.length).trim();
    if (rest.startsWith("{")) {
      return { name, index, kind: "struct", fields: fieldNames(rest.slice(1, rest.lastIndexOf("}"))) };
    }
    if (rest.startsWith("(")) {
      return { name, index, kind: "tuple", fields: [] };
    }
    return { name, index, kind: "unit", fields: [] };
  });
  if (parsed.length === 0) {
    throw new Error(`PROTOCOL VOCABULARY EMPTY — parsed zero variants from ${enumName} in ${rel}`);
  }
  return parsed;
}

/** Parse a Rust struct's field names, in declaration order. */
export function rustStruct(rel, structName) {
  const src = stripComments(readProtocol(rel));
  const body = bodyAfter(src, `pub struct ${structName} {`, `\`${structName}\``, rel);
  const fields = fieldNames(body);
  if (fields.length === 0) {
    throw new Error(`PROTOCOL VOCABULARY EMPTY — parsed zero fields from ${structName} in ${rel}`);
  }
  return fields;
}

/**
 * Read the discriminants the TS codec ACTUALLY writes, from the TS source.
 *
 * The bridge map in the vocabulary gate says which Rust variant each TS `kind`
 * claims to be; this says which index TS really encodes. Reading it from source
 * (rather than restating it in the test) is what keeps this gate from becoming
 * a third hand-maintained mirror of the same facts — the exact failure mode it
 * exists to kill. Parses `case "<kind>":` ... `w.varint(<n>)` inside `fnName`.
 */
export function tsDiscriminants(fnName) {
  const path = join(here, "..", "src", "internal", "wire.ts");
  const src = readFileSync(path, "utf8");
  const at = src.indexOf(`function ${fnName}(`);
  if (at === -1) throw new Error(`TS codec function \`${fnName}\` not found in ${path}`);
  const open = src.indexOf("{", at);
  let depth = 0;
  let end = -1;
  for (let k = open; k < src.length; k++) {
    if (src[k] === "{") depth++;
    else if (src[k] === "}") { depth--; if (depth === 0) { end = k; break; } }
  }
  const body = src.slice(open, end);
  const out = new Map();
  const re = /case\s+"([A-Za-z0-9_]+)"\s*:\s*(?:\/\/[^\n]*\n|\s)*?[\s\S]*?w\s*\.\s*varint\(\s*(\d+)\s*\)/g;
  // Walk case-by-case so a later case's varint cannot be attributed to an earlier one.
  const cases = [...body.matchAll(/case\s+"([A-Za-z0-9_]+)"\s*:/g)];
  for (let i = 0; i < cases.length; i++) {
    const start = cases[i].index;
    const stop = i + 1 < cases.length ? cases[i + 1].index : body.length;
    const chunk = body.slice(start, stop);
    const m = /w\s*\.\s*varint\(\s*(\d+)\s*\)/.exec(chunk);
    if (!m) throw new Error(`TS \`${fnName}\` case "${cases[i][1]}" writes no literal varint discriminant`);
    out.set(cases[i][1], Number(m[1]));
  }
  void re;
  if (out.size === 0) throw new Error(`TS \`${fnName}\` yielded no discriminants`);
  return out;
}

/** snake_case a TS camelCase identifier (publicKey → public_key). */
export const snake = (s) => s.replace(/[A-Z]/g, (c) => `_${c.toLowerCase()}`);

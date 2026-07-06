//! **The well-formed leg** — a JSON CFG parse certificate (`producesChain`-shaped).
//!
//! This is the Rust realization of `metatheory/Dregg2/Crypto/Cfg.lean`. The prover emits
//! a **derivation form-chain** — the sentential forms `[initial] ⟶ … ⟶ input`, each
//! consecutive pair a single-rule `Produces` — and the verifier checks each step locally.
//! This is the context-free analogue of a DFA run: nested/balanced structure (arbitrary
//! object/array depth) the regular DFA cascade provably cannot express.
//!
//! The types mirror `Cfg.lean` one-for-one:
//!
//! | this module                    | `Cfg.lean`                                   |
//! |--------------------------------|----------------------------------------------|
//! | [`Symbol`]                     | `Symbol T g.NT` (terminal / nonterminal)     |
//! | [`Rule`]                       | `ContextFreeRule T NT`                       |
//! | [`json_grammar`]               | a `ContextFreeGrammar`                        |
//! | [`ParseCertificate`] (`Vec<Vec<Symbol>>`) | the derivation `chain`             |
//! | [`produces_chain`]             | `producesChain g chain`                       |
//! | [`cfg_accepts`]                | `CfgAccepts g input chain` (head/getLast/producesChain) |
//! | [`verify_cfg_cert`]            | the `CfgVerifierKernel.verify` accepting bit  |
//!
//! Unlike `Cfg.lean`'s hand-written 5-token demo grammar, this is a **real JSON grammar**
//! (objects with members, arrays with elements, strings/numbers/booleans/null) plus a
//! recursive-descent parser that emits the leftmost derivation certificate over any
//! standard JSON body — e.g. an actual Anthropic `POST /v1/messages` response. A
//! well-formed body yields a valid certificate; a malformed body yields NONE.

/// A JSON terminal token class (the grammar's terminal alphabet — `T` in `Cfg.lean`).
/// String/number/boolean/null LEAVES are single terminals; structural punctuation are
/// terminals too. The concrete lexeme bytes are abstracted away (the CFG certifies
/// STRUCTURE — that the token stream nests correctly).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JTok {
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `[`
    LBrack,
    /// `]`
    RBrack,
    /// `:`
    Colon,
    /// `,`
    Comma,
    /// a string literal `"…"`
    Str,
    /// a number literal
    Num,
    /// `true`
    True,
    /// `false`
    False,
    /// `null`
    Null,
}

/// A JSON nonterminal (`g.NT` in `Cfg.lean`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum JNt {
    /// a JSON value (the grammar's initial nonterminal)
    Value,
    /// an object `{ … }`
    Object,
    /// a non-empty comma-separated member list
    Members,
    /// one `"key": value` member
    Member,
    /// an array `[ … ]`
    Array,
    /// a non-empty comma-separated element list
    Elements,
}

/// A grammar symbol — terminal or nonterminal (`Symbol T g.NT`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Symbol {
    /// A terminal token.
    T(JTok),
    /// A nonterminal.
    N(JNt),
}

/// A context-free production `lhs → rhs` (`ContextFreeRule`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    /// The nonterminal being rewritten.
    pub lhs: JNt,
    /// The replacement sentential form.
    pub rhs: Vec<Symbol>,
}

/// The initial nonterminal (`g.initial`).
pub const INITIAL: JNt = JNt::Value;

/// **The JSON grammar** — the production set (`ContextFreeGrammar.rules`):
///
/// ```text
/// Value    → Str | Num | True | False | Null | Object | Array
/// Object   → { } | { Members }
/// Members  → Member | Member , Members
/// Member   → Str : Value
/// Array    → [ ] | [ Elements ]
/// Elements → Value | Value , Elements
/// ```
///
/// Objects and arrays nest through `Value`, so this recognizes arbitrary-depth balanced
/// JSON — the canonical NON-regular property the DFA cascade cannot certify.
pub fn json_grammar() -> Vec<Rule> {
    use JNt::*;
    use JTok::*;
    let t = Symbol::T;
    let n = Symbol::N;
    vec![
        Rule {
            lhs: Value,
            rhs: vec![t(Str)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(Num)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(True)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(False)],
        },
        Rule {
            lhs: Value,
            rhs: vec![t(Null)],
        },
        Rule {
            lhs: Value,
            rhs: vec![n(Object)],
        },
        Rule {
            lhs: Value,
            rhs: vec![n(Array)],
        },
        Rule {
            lhs: Object,
            rhs: vec![t(LBrace), t(RBrace)],
        },
        Rule {
            lhs: Object,
            rhs: vec![t(LBrace), n(Members), t(RBrace)],
        },
        Rule {
            lhs: Members,
            rhs: vec![n(Member)],
        },
        Rule {
            lhs: Members,
            rhs: vec![n(Member), t(Comma), n(Members)],
        },
        Rule {
            lhs: Member,
            rhs: vec![t(Str), t(Colon), n(Value)],
        },
        Rule {
            lhs: Array,
            rhs: vec![t(LBrack), t(RBrack)],
        },
        Rule {
            lhs: Array,
            rhs: vec![t(LBrack), n(Elements), t(RBrack)],
        },
        Rule {
            lhs: Elements,
            rhs: vec![n(Value)],
        },
        Rule {
            lhs: Elements,
            rhs: vec![n(Value), t(Comma), n(Elements)],
        },
    ]
}

/// **The parse certificate** — the derivation form-chain (`chain` in `Cfg.lean`): the
/// list of sentential forms threaded from `[N(initial)]` to the token word. Each
/// consecutive pair is one single-rule `Produces` step, checked locally by
/// [`verify_cfg_cert`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseCertificate {
    /// The sentential forms `[initial] ⟶ … ⟶ input`.
    pub chain: Vec<Vec<Symbol>>,
}

/// Why a JSON body failed to tokenize / parse (so the prover cannot emit a certificate),
/// or why a presented certificate does not certify its body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CfgError {
    /// The body does not lex as JSON at byte offset `at`.
    LexError { at: usize },
    /// The token stream does not parse as a JSON value (unbalanced / trailing tokens).
    ParseError { reason: &'static str },
    /// The certificate chain is empty.
    EmptyChain,
    /// The chain does not start at `[N(initial)]`.
    BadHead,
    /// The chain does not end at the body's token word (`input.map(terminal)`).
    BadTail,
    /// Step `at` of the chain is not a valid single-rule `Produces` rewrite.
    BadStep { at: usize },
}

// ─────────────────────────────────────────────────────────────────────────────
// Tokenizer — bytes → JTok stream (standard JSON lexing).
// ─────────────────────────────────────────────────────────────────────────────

/// Lex a JSON body into its terminal token stream. Fail-closed on any non-JSON byte —
/// a malformed body cannot even be tokenized, so no certificate is emitted for it.
pub fn tokenize(body: &[u8]) -> Result<Vec<JTok>, CfgError> {
    let mut toks = Vec::new();
    let mut i = 0usize;
    let n = body.len();
    while i < n {
        let c = body[i];
        match c {
            b' ' | b'\t' | b'\n' | b'\r' => {
                i += 1;
            }
            b'{' => {
                toks.push(JTok::LBrace);
                i += 1;
            }
            b'}' => {
                toks.push(JTok::RBrace);
                i += 1;
            }
            b'[' => {
                toks.push(JTok::LBrack);
                i += 1;
            }
            b']' => {
                toks.push(JTok::RBrack);
                i += 1;
            }
            b':' => {
                toks.push(JTok::Colon);
                i += 1;
            }
            b',' => {
                toks.push(JTok::Comma);
                i += 1;
            }
            b'"' => {
                i = lex_string(body, i)?;
                toks.push(JTok::Str);
            }
            b't' => {
                i = lex_keyword(body, i, b"true")?;
                toks.push(JTok::True);
            }
            b'f' => {
                i = lex_keyword(body, i, b"false")?;
                toks.push(JTok::False);
            }
            b'n' => {
                i = lex_keyword(body, i, b"null")?;
                toks.push(JTok::Null);
            }
            b'-' | b'0'..=b'9' => {
                i = lex_number(body, i)?;
                toks.push(JTok::Num);
            }
            _ => return Err(CfgError::LexError { at: i }),
        }
    }
    Ok(toks)
}

/// Consume a string starting at the opening quote `body[i] == '"'`; return the index just
/// past the closing quote. Handles the standard JSON escapes.
fn lex_string(body: &[u8], start: usize) -> Result<usize, CfgError> {
    let n = body.len();
    let mut i = start + 1; // past opening quote
    while i < n {
        match body[i] {
            b'"' => return Ok(i + 1),
            b'\\' => {
                let e = *body.get(i + 1).ok_or(CfgError::LexError { at: i })?;
                match e {
                    b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't' => i += 2,
                    b'u' => {
                        // \uXXXX — four hex digits
                        if i + 6 > n {
                            return Err(CfgError::LexError { at: i });
                        }
                        for h in &body[i + 2..i + 6] {
                            if !h.is_ascii_hexdigit() {
                                return Err(CfgError::LexError { at: i });
                            }
                        }
                        i += 6;
                    }
                    _ => return Err(CfgError::LexError { at: i }),
                }
            }
            // control chars must be escaped in strict JSON
            0x00..=0x1F => return Err(CfgError::LexError { at: i }),
            _ => i += 1,
        }
    }
    Err(CfgError::LexError { at: start }) // unterminated string
}

/// Consume the literal `kw` at `body[start..]`; return the index just past it.
fn lex_keyword(body: &[u8], start: usize, kw: &[u8]) -> Result<usize, CfgError> {
    if body.len() >= start + kw.len() && &body[start..start + kw.len()] == kw {
        Ok(start + kw.len())
    } else {
        Err(CfgError::LexError { at: start })
    }
}

/// Consume a JSON number at `body[start..]`; return the index just past it. Grammar:
/// `-? (0 | [1-9][0-9]*) (. [0-9]+)? ([eE] [+-]? [0-9]+)?`.
fn lex_number(body: &[u8], start: usize) -> Result<usize, CfgError> {
    let n = body.len();
    let mut i = start;
    if i < n && body[i] == b'-' {
        i += 1;
    }
    // integer part
    match body.get(i) {
        Some(b'0') => i += 1,
        Some(b'1'..=b'9') => {
            while i < n && body[i].is_ascii_digit() {
                i += 1;
            }
        }
        _ => return Err(CfgError::LexError { at: start }),
    }
    // fraction
    if i < n && body[i] == b'.' {
        i += 1;
        let f0 = i;
        while i < n && body[i].is_ascii_digit() {
            i += 1;
        }
        if i == f0 {
            return Err(CfgError::LexError { at: start });
        }
    }
    // exponent
    if i < n && (body[i] == b'e' || body[i] == b'E') {
        i += 1;
        if i < n && (body[i] == b'+' || body[i] == b'-') {
            i += 1;
        }
        let e0 = i;
        while i < n && body[i].is_ascii_digit() {
            i += 1;
        }
        if i == e0 {
            return Err(CfgError::LexError { at: start });
        }
    }
    Ok(i)
}

// ─────────────────────────────────────────────────────────────────────────────
// Parser — JTok stream → parse tree → leftmost derivation certificate.
// ─────────────────────────────────────────────────────────────────────────────

/// A concrete parse tree. Each [`Tree::Node`] records a nonterminal and its children; the
/// rule it applied is recovered from the children (leaves → terminals, sub-nodes →
/// nonterminals), so the tree witnesses a specific derivation.
#[derive(Clone, Debug)]
enum Tree {
    Leaf(JTok),
    Node(JNt, Vec<Tree>),
}

impl Tree {
    /// The grammar symbol this subtree occupies in its parent's rhs.
    fn symbol(&self) -> Symbol {
        match self {
            Tree::Leaf(t) => Symbol::T(*t),
            Tree::Node(nt, _) => Symbol::N(*nt),
        }
    }
}

/// A recursive-descent parser cursor over the token stream.
struct Parser<'a> {
    toks: &'a [JTok],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<JTok> {
        self.toks.get(self.pos).copied()
    }

    fn bump(&mut self, expected: JTok) -> Result<(), CfgError> {
        if self.peek() == Some(expected) {
            self.pos += 1;
            Ok(())
        } else {
            Err(CfgError::ParseError {
                reason: "unexpected token",
            })
        }
    }

    fn value(&mut self) -> Result<Tree, CfgError> {
        match self.peek() {
            Some(JTok::Str) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::Str)]))
            }
            Some(JTok::Num) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::Num)]))
            }
            Some(JTok::True) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::True)]))
            }
            Some(JTok::False) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::False)]))
            }
            Some(JTok::Null) => {
                self.pos += 1;
                Ok(Tree::Node(JNt::Value, vec![Tree::Leaf(JTok::Null)]))
            }
            Some(JTok::LBrace) => {
                let obj = self.object()?;
                Ok(Tree::Node(JNt::Value, vec![obj]))
            }
            Some(JTok::LBrack) => {
                let arr = self.array()?;
                Ok(Tree::Node(JNt::Value, vec![arr]))
            }
            _ => Err(CfgError::ParseError {
                reason: "expected a value",
            }),
        }
    }

    fn object(&mut self) -> Result<Tree, CfgError> {
        self.bump(JTok::LBrace)?;
        if self.peek() == Some(JTok::RBrace) {
            self.pos += 1;
            return Ok(Tree::Node(
                JNt::Object,
                vec![Tree::Leaf(JTok::LBrace), Tree::Leaf(JTok::RBrace)],
            ));
        }
        let members = self.members()?;
        self.bump(JTok::RBrace)?;
        Ok(Tree::Node(
            JNt::Object,
            vec![Tree::Leaf(JTok::LBrace), members, Tree::Leaf(JTok::RBrace)],
        ))
    }

    fn members(&mut self) -> Result<Tree, CfgError> {
        let member = self.member()?;
        if self.peek() == Some(JTok::Comma) {
            self.pos += 1;
            let rest = self.members()?;
            Ok(Tree::Node(
                JNt::Members,
                vec![member, Tree::Leaf(JTok::Comma), rest],
            ))
        } else {
            Ok(Tree::Node(JNt::Members, vec![member]))
        }
    }

    fn member(&mut self) -> Result<Tree, CfgError> {
        self.bump(JTok::Str)?;
        self.bump(JTok::Colon)?;
        let value = self.value()?;
        Ok(Tree::Node(
            JNt::Member,
            vec![Tree::Leaf(JTok::Str), Tree::Leaf(JTok::Colon), value],
        ))
    }

    fn array(&mut self) -> Result<Tree, CfgError> {
        self.bump(JTok::LBrack)?;
        if self.peek() == Some(JTok::RBrack) {
            self.pos += 1;
            return Ok(Tree::Node(
                JNt::Array,
                vec![Tree::Leaf(JTok::LBrack), Tree::Leaf(JTok::RBrack)],
            ));
        }
        let elements = self.elements()?;
        self.bump(JTok::RBrack)?;
        Ok(Tree::Node(
            JNt::Array,
            vec![Tree::Leaf(JTok::LBrack), elements, Tree::Leaf(JTok::RBrack)],
        ))
    }

    fn elements(&mut self) -> Result<Tree, CfgError> {
        let value = self.value()?;
        if self.peek() == Some(JTok::Comma) {
            self.pos += 1;
            let rest = self.elements()?;
            Ok(Tree::Node(
                JNt::Elements,
                vec![value, Tree::Leaf(JTok::Comma), rest],
            ))
        } else {
            Ok(Tree::Node(JNt::Elements, vec![value]))
        }
    }
}

/// Produce the LEFTMOST derivation chain from a parse tree: repeatedly rewrite the
/// leftmost nonterminal using the rule its subtree records. This is the certificate the
/// prover threads — a valid `producesChain` from `[N(initial)]` to the token word.
fn leftmost_chain(root: &Tree) -> Vec<Vec<Symbol>> {
    use std::collections::VecDeque;
    let root_nt = match root {
        Tree::Node(nt, _) => *nt,
        Tree::Leaf(_) => unreachable!("root of a JSON parse is always a Value nonterminal"),
    };
    let mut form: Vec<Symbol> = vec![Symbol::N(root_nt)];
    // The pending subtrees for the nonterminals of `form`, in left-to-right order.
    let mut queue: VecDeque<&Tree> = VecDeque::new();
    queue.push_back(root);
    let mut chain: Vec<Vec<Symbol>> = vec![form.clone()];

    while let Some(i) = form.iter().position(|s| matches!(s, Symbol::N(_))) {
        // Everything before i is terminal, so the front of the queue is the subtree for
        // the nonterminal at i.
        let node = queue
            .pop_front()
            .expect("a pending subtree per nonterminal");
        let Tree::Node(_nt, children) = node else {
            unreachable!("a nonterminal position always maps to a Node")
        };
        let rhs: Vec<Symbol> = children.iter().map(Tree::symbol).collect();
        // Splice rhs in at position i.
        let mut next = form[..i].to_vec();
        next.extend_from_slice(&rhs);
        next.extend_from_slice(&form[i + 1..]);
        // The rhs's nonterminal children become the new leftmost pending subtrees.
        for child in children.iter().rev() {
            if let Tree::Node(..) = child {
                queue.push_front(child);
            }
        }
        form = next;
        chain.push(form.clone());
    }
    chain
}

/// **PRODUCE a parse certificate** over a JSON body — the well-formed-leg prover.
///
/// Lexes + parses the body as a JSON value and emits the leftmost derivation certificate.
/// A well-formed body yields `Ok(cert)`; a malformed body (lex/parse failure, trailing
/// tokens) yields `Err` — **no certificate exists for a malformed body**.
pub fn prove_cfg_cert(body: &[u8]) -> Result<ParseCertificate, CfgError> {
    let toks = tokenize(body)?;
    let mut parser = Parser {
        toks: &toks,
        pos: 0,
    };
    let tree = parser.value()?;
    if parser.pos != toks.len() {
        return Err(CfgError::ParseError {
            reason: "trailing tokens after the JSON value",
        });
    }
    Ok(ParseCertificate {
        chain: leftmost_chain(&tree),
    })
}

// ─────────────────────────────────────────────────────────────────────────────
// Verifier — the `CfgAccepts` accepting bit (locally-checkable).
// ─────────────────────────────────────────────────────────────────────────────

/// Whether `b` is one single-rule `Produces` rewrite of `a` under `grammar`: there is a
/// rule `lhs → rhs` and a position `i` with `a[i] = N(lhs)` and
/// `b == a[..i] ++ rhs ++ a[i+1..]`. This is `g.Produces a b` — a real production applied
/// at one nonterminal, in any context (matching `Cfg.lean`).
fn produces(grammar: &[Rule], a: &[Symbol], b: &[Symbol]) -> bool {
    for (i, sym) in a.iter().enumerate() {
        let Symbol::N(nt) = sym else { continue };
        for rule in grammar {
            if rule.lhs != *nt {
                continue;
            }
            // b == a[..i] ++ rhs ++ a[i+1..] ?
            let mut rebuilt = Vec::with_capacity(a.len() - 1 + rule.rhs.len());
            rebuilt.extend_from_slice(&a[..i]);
            rebuilt.extend_from_slice(&rule.rhs);
            rebuilt.extend_from_slice(&a[i + 1..]);
            if rebuilt == b {
                return true;
            }
        }
    }
    false
}

/// **`produces_chain`** — every consecutive pair of sentential forms is one valid
/// production step (`producesChain g chain` in `Cfg.lean`). The step at which validity
/// fails is returned as `Err(index)`.
fn produces_chain(grammar: &[Rule], chain: &[Vec<Symbol>]) -> Result<(), usize> {
    for (k, pair) in chain.windows(2).enumerate() {
        if !produces(grammar, &pair[0], &pair[1]) {
            return Err(k);
        }
    }
    Ok(())
}

/// **`cfg_accepts`** — the CFG acceptance predicate (`CfgAccepts g input chain`): the
/// chain is non-empty, STARTS at `[N(initial)]`, ENDS at the input word wrapped as
/// terminals, and every step is a valid production. Locally checkable — exactly what an
/// in-circuit CFG verifier's accepting bit certifies.
pub fn cfg_accepts(
    grammar: &[Rule],
    input: &[JTok],
    cert: &ParseCertificate,
) -> Result<(), CfgError> {
    let chain = &cert.chain;
    let head = chain.first().ok_or(CfgError::EmptyChain)?;
    if head.as_slice() != [Symbol::N(INITIAL)] {
        return Err(CfgError::BadHead);
    }
    let tail = chain.last().ok_or(CfgError::EmptyChain)?;
    let want_tail: Vec<Symbol> = input.iter().map(|t| Symbol::T(*t)).collect();
    if tail != &want_tail {
        return Err(CfgError::BadTail);
    }
    produces_chain(grammar, chain).map_err(|at| CfgError::BadStep { at })?;
    Ok(())
}

/// **VERIFY a parse certificate binds a JSON body** — the well-formed-leg verifier.
///
/// The verifier re-tokenizes `body` ITSELF (so the certificate is checked against the
/// authenticated bytes, not the prover's word), then checks `cfg_accepts` over the
/// [`json_grammar`]. `Ok(())` ⟺ the certificate is a genuine leftmost derivation of the
/// body's token word from the start symbol ⟹ the body lies in the JSON context-free
/// language.
pub fn verify_cfg_cert(cert: &ParseCertificate, body: &[u8]) -> Result<(), CfgError> {
    let toks = tokenize(body)?;
    cfg_accepts(&json_grammar(), &toks, cert)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A representative Anthropic `POST /v1/messages` response body — deeply nested
    /// (object → array of content blocks → object → …) — yields a valid certificate that
    /// the verifier accepts against the re-tokenized body.
    const ANTHROPIC_BODY: &[u8] = br#"{"id":"msg_01ABC","type":"message","role":"assistant","model":"claude-opus-4-8","content":[{"type":"text","text":"hello"}],"stop_reason":"end_turn","stop_sequence":null,"usage":{"input_tokens":12,"output_tokens":3}}"#;

    #[test]
    fn wellformed_anthropic_body_certificate_verifies() {
        let cert = prove_cfg_cert(ANTHROPIC_BODY).expect("well-formed body → certificate");
        verify_cfg_cert(&cert, ANTHROPIC_BODY).expect("the certificate verifies against the body");
        // The chain starts at the start symbol and ends at the token word (non-vacuous).
        assert_eq!(cert.chain.first().unwrap().as_slice(), [Symbol::N(INITIAL)]);
        assert!(cert.chain.len() > 1);
    }

    #[test]
    fn deeply_nested_json_certifies() {
        // Arbitrary-depth nesting — the canonical non-regular property.
        let body = br#"[[[[["deep"]]]]]"#;
        let cert = prove_cfg_cert(body).expect("nested arrays are well-formed");
        verify_cfg_cert(&cert, body).unwrap();
    }

    #[test]
    fn malformed_body_yields_no_certificate() {
        // Unbalanced brace / truncated object — the prover cannot emit a certificate.
        assert!(matches!(
            prove_cfg_cert(br#"{"id":"msg","content":"#),
            Err(_)
        ));
        assert!(matches!(prove_cfg_cert(br#"{"a":1,}"#), Err(_))); // trailing comma
        assert!(matches!(prove_cfg_cert(br#"[1,2"#), Err(_))); // unbalanced array
        assert!(matches!(prove_cfg_cert(br#"nul"#), Err(_))); // bad keyword
        assert!(matches!(prove_cfg_cert(br#"{"k" 1}"#), Err(_))); // missing colon
    }

    #[test]
    fn certificate_for_a_different_body_is_refused() {
        // A certificate proven over one body does NOT certify a different body — the
        // verifier re-tokenizes and the tail mismatches.
        let cert = prove_cfg_cert(br#"{"a":1}"#).unwrap();
        assert!(matches!(
            verify_cfg_cert(&cert, br#"{"a":2,"b":3}"#),
            Err(CfgError::BadTail)
        ));
    }

    #[test]
    fn tampered_step_is_refused() {
        // Corrupt an interior form so a step is no longer a valid single-rule Produces.
        let mut cert = prove_cfg_cert(br#"[null]"#).unwrap();
        let mid = cert.chain.len() / 2;
        cert.chain[mid].insert(0, Symbol::T(JTok::Comma));
        assert!(matches!(
            verify_cfg_cert(&cert, br#"[null]"#),
            Err(CfgError::BadStep { .. }) | Err(CfgError::BadTail)
        ));
    }

    #[test]
    fn empty_chain_and_bad_head_refused() {
        assert_eq!(
            verify_cfg_cert(&ParseCertificate { chain: vec![] }, br#"1"#),
            Err(CfgError::EmptyChain)
        );
        let bad = ParseCertificate {
            chain: vec![vec![Symbol::N(JNt::Object)], vec![Symbol::T(JTok::Num)]],
        };
        assert_eq!(verify_cfg_cert(&bad, br#"1"#), Err(CfgError::BadHead));
    }
}

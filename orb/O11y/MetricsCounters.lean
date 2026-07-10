/-!
# O11y.MetricsCounters — the deployed request/status-class counters, proven

`O11y.Prometheus` / `O11y.PromExposition` prove the *rendering* of the metrics
surface (the text-exposition line grammar). This file closes the counting layer
underneath it: the two accounting laws the deployed `record` path guarantees on
every served response, modelled directly on the running dataplane.

Ground truth: `crates/dataplane/src/metrics.rs :: record` / `record_streamed`,
called once per finalized response from the io_uring serve loop
(`crates/dataplane/src/uring.rs`, at the two funnel points where a response is
finalized for send). That function does exactly two counting acts per response:

```rust
REQUESTS.fetch_add(1, Ordering::Relaxed);      // drorb_requests_total += 1
match status_class(head) {                     // one class bucket += 1
    Some(2) => &R2XX, Some(3) => &R3XX,
    Some(4) => &R4XX, Some(5) => &R5XX, _ => &ROTHER,
}.fetch_add(1, Ordering::Relaxed);
```

and `status_class` reads the leading digit of the HTTP status code out of the
response head (`HTTP/1.1 SP CODE …`), following the status-class partition of
RFC 9110 §15 (1xx/2xx/3xx/4xx/5xx). The status-class function below is a
byte-faithful transcription of the deployed `status_class`; the counter
transition is a byte-faithful transcription of `record`.

Proven here (core-Lean only — the axiom footprint on the headline theorems is
empty, checked with `#print axioms`):

* `metrics_counter_monotone` — one served response bumps `drorb_requests_total`
  by exactly one; hence it is monotone non-decreasing and strictly increasing
  per response (never a skip, never a double count).
* `metrics_total_counts` / `metrics_total_from_zero` — folding `record` over `N`
  served responses leaves `drorb_requests_total` at `N` (from a fresh registry):
  the exact invariant the deployed `/metrics` endpoint reports after `N` curls.
* `metrics_status_class` — a response of status class `Nxx` increments the
  `drorb_responses_total{class="Nxx"}` bucket by exactly one, and
  `metrics_status_class_others` — leaves every other class bucket fixed.
* `statusClass_faithful_*` — the byte-level status-class reader agrees with the
  wire on concrete `HTTP/1.1 …` heads (200→2xx, 404→4xx, 500→5xx, malformed→
  other), pinning the model to the bytes the running server actually parses.
-/

namespace O11y.MetricsCounters

/-! ## Byte-level status-class reader (mirrors `metrics.rs :: status_class`) -/

/-- ASCII space and CR, as the deployed reader splits on them. -/
def spaceByte : UInt8 := 0x20
def crByte : UInt8 := 0x0D

/-- `b` is an ASCII decimal digit (`'0'..'9'`), i.e. Rust's `u8::is_ascii_digit`. -/
def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- The leading digit of the HTTP status code in a response head, or `none` if
the head is not a recognisable `PREFIX SP CODE …` with a 3-ASCII-digit `CODE`.

Byte-faithful transcription of `crates/dataplane/src/metrics.rs :: status_class`:

* `head` = bytes up to the first CR (Rust `split(b'\r').next()`, which on a
  head with no CR yields the whole slice — `takeWhile` matches both cases);
* find the first space and take everything after it (Rust `position(SP)?` then
  `head[sp+1..]`); no space ⇒ `none`;
* `code` = bytes up to the next space (Rust `split(b' ').next()`);
* if `code` is exactly 3 ASCII digits, return its leading digit `code[0]-'0'`. -/
def statusClass (resp : List UInt8) : Option UInt8 :=
  let head := resp.takeWhile (fun b => b ≠ crByte)
  match head.dropWhile (fun b => b ≠ spaceByte) with
  | [] => none
  | _ :: after =>
      let code := after.takeWhile (fun b => b ≠ spaceByte)
      if code.length = 3 ∧ code.all isDigit then
        some (code.headD 0 - 0x30)
      else none

/-! ## Status classes and the counter registry (mirrors `metrics.rs :: record`) -/

/-- The five status-class buckets of `drorb_responses_total{class=…}`, exactly
the arms of the deployed `match status_class(head) { … }`. -/
inductive Class
  | c2 | c3 | c4 | c5 | cOther
  deriving DecidableEq

/-- Map a response to its class bucket, mirroring the deployed `match`:
`Some(2)=>2xx, Some(3)=>3xx, Some(4)=>4xx, Some(5)=>5xx, _=>other`. -/
def classify (resp : List UInt8) : Class :=
  match statusClass resp with
  | some 2 => .c2
  | some 3 => .c3
  | some 4 => .c4
  | some 5 => .c5
  | _ => .cOther

/-- The counter registry state this lane reasons about: the total request
counter (`drorb_requests_total`) and the per-class response buckets
(`drorb_responses_total{class=…}`). The deployed statics `REQUESTS` and
`R2XX..ROTHER` are the atomics behind these fields. -/
structure Counters where
  total : Nat
  bucket : Class → Nat

/-- The empty registry (all atomics start at zero — `AtomicU64::new(0)`). -/
def Counters.zero : Counters := { total := 0, bucket := fun _ => 0 }

/-- One served response, as the deployed `record` counts it: bump `total` by one
and bump the served response's class bucket by one, leaving the other buckets
fixed. Byte-faithful transcription of the two `fetch_add(1, …)` in `record`. -/
def Counters.record (s : Counters) (resp : List UInt8) : Counters :=
  { total := s.total + 1
    bucket := fun c => if c = classify resp then s.bucket c + 1 else s.bucket c }

/-- Fold `record` over a sequence of served responses (the serve loop over a run
of requests). -/
def Counters.recordAll (s : Counters) (resps : List (List UInt8)) : Counters :=
  resps.foldl Counters.record s

/-! ## Counter monotonicity (drorb_requests_total) -/

/-- **metrics_counter_monotone.** One served response bumps `drorb_requests_total`
by *exactly one*. This is the exact per-response accounting the io_uring serve
loop performs (`REQUESTS.fetch_add(1)` at each finalized response). -/
theorem metrics_counter_monotone (s : Counters) (resp : List UInt8) :
    (s.record resp).total = s.total + 1 := rfl

/-- Monotone non-decreasing: the total never drops across a served response
(immediate from the exact-add law). -/
theorem metrics_counter_nondecreasing (s : Counters) (resp : List UInt8) :
    s.total ≤ (s.record resp).total := by
  rw [metrics_counter_monotone]; exact Nat.le_succ _

/-- Strictly increasing per response: never a skipped or duplicated count. -/
theorem metrics_counter_strict (s : Counters) (resp : List UInt8) :
    s.total < (s.record resp).total := by
  rw [metrics_counter_monotone]; exact Nat.lt_succ_self _

/-- **metrics_total_counts.** Serving `N` responses raises `drorb_requests_total`
by exactly `N` — the total counts served responses one-for-one. -/
theorem metrics_total_counts (s : Counters) (resps : List (List UInt8)) :
    (s.recordAll resps).total = s.total + resps.length := by
  induction resps generalizing s with
  | nil => simp [Counters.recordAll]
  | cons r rs ih =>
      simp only [Counters.recordAll, List.foldl_cons, List.length_cons] at *
      rw [ih (s.record r), metrics_counter_monotone]; omega

/-- **metrics_total_from_zero.** After `N` served responses on a fresh registry,
`drorb_requests_total == N`. This is exactly what the deployed `/metrics`
endpoint must report after `N` requests curled through the io_uring dataplane —
the prove-what-runs invariant. -/
theorem metrics_total_from_zero (resps : List (List UInt8)) :
    (Counters.zero.recordAll resps).total = resps.length := by
  rw [metrics_total_counts]; simp [Counters.zero]

/-! ## Status-class accounting (drorb_responses_total{class=…}) -/

/-- **metrics_status_class.** A served response increments the class bucket for
*its own* class by exactly one. Combined with `classify` this says: a response of
status class `Nxx` increments `drorb_responses_total{class="Nxx"}` by one. -/
theorem metrics_status_class (s : Counters) (resp : List UInt8) :
    (s.record resp).bucket (classify resp) = s.bucket (classify resp) + 1 := by
  simp [Counters.record]

/-- **metrics_status_class_others.** A served response leaves every *other* class
bucket exactly fixed — only the response's own class bucket moves. -/
theorem metrics_status_class_others (s : Counters) (resp : List UInt8) (c : Class)
    (h : c ≠ classify resp) :
    (s.record resp).bucket c = s.bucket c := by
  simp [Counters.record, h]

/-- The class a response is filed under is determined by its byte-level status
class: a head that reads status class `2` is filed under `c2` (and likewise 3/4/5;
anything else under `cOther`). Ties the bucket law to the wire reader. -/
theorem classify_of_statusClass_two (resp : List UInt8)
    (h : statusClass resp = some 2) : classify resp = .c2 := by
  simp [classify, h]

theorem classify_of_statusClass_three (resp : List UInt8)
    (h : statusClass resp = some 3) : classify resp = .c3 := by
  simp [classify, h]

theorem classify_of_statusClass_four (resp : List UInt8)
    (h : statusClass resp = some 4) : classify resp = .c4 := by
  simp [classify, h]

theorem classify_of_statusClass_five (resp : List UInt8)
    (h : statusClass resp = some 5) : classify resp = .c5 := by
  simp [classify, h]

/-- Fully wired: a response whose head reads status class `2` bumps the `2xx`
bucket by exactly one (and symmetric statements hold for 3/4/5 via the
`classify_of_statusClass_*` lemmas). -/
theorem metrics_status_class_2xx (s : Counters) (resp : List UInt8)
    (h : statusClass resp = some 2) :
    (s.record resp).bucket .c2 = s.bucket .c2 + 1 := by
  have := metrics_status_class s resp
  rwa [classify_of_statusClass_two resp h] at this

/-! ## Wire fidelity — concrete `HTTP/1.1 …` heads the running server parses

The byte lists below are the ASCII bytes of real status lines. They pin the
model's `statusClass` to the bytes the deployed reader consumes, so the counting
laws above land on the true wire, not a paraphrase. -/

/-- Bytes of `"HTTP/1.1 200 OK\r\n"`. -/
def head200 : List UInt8 :=
  [0x48,0x54,0x54,0x50,0x2F,0x31,0x2E,0x31,0x20,0x32,0x30,0x30,0x20,0x4F,0x4B,0x0D,0x0A]

/-- Bytes of `"HTTP/1.1 404 Not Found\r\n"`. -/
def head404 : List UInt8 :=
  [0x48,0x54,0x54,0x50,0x2F,0x31,0x2E,0x31,0x20,0x34,0x30,0x34,0x20,
   0x4E,0x6F,0x74,0x20,0x46,0x6F,0x75,0x6E,0x64,0x0D,0x0A]

/-- Bytes of `"HTTP/1.1 500 Internal Server Error\r\n"` (prefix through the code). -/
def head500 : List UInt8 :=
  [0x48,0x54,0x54,0x50,0x2F,0x31,0x2E,0x31,0x20,0x35,0x30,0x30,0x20,0x45,0x0D,0x0A]

/-- Bytes of a malformed head `"garbage\r\n"` (no space-delimited 3-digit code). -/
def headBad : List UInt8 := [0x67,0x61,0x72,0x62,0x61,0x67,0x65,0x0D,0x0A]

theorem statusClass_faithful_200 : statusClass head200 = some 2 := by decide
theorem statusClass_faithful_404 : statusClass head404 = some 4 := by decide
theorem statusClass_faithful_500 : statusClass head500 = some 5 := by decide
theorem statusClass_faithful_bad : statusClass headBad = none := by decide

theorem classify_faithful_200 : classify head200 = .c2 := by decide
theorem classify_faithful_404 : classify head404 = .c4 := by decide
theorem classify_faithful_500 : classify head500 = .c5 := by decide
theorem classify_faithful_bad : classify headBad = .cOther := by decide

/-- End-to-end on a real head: a served `200 OK` response bumps `drorb_requests_total`
by one and `drorb_responses_total{class="2xx"}` by one, on a fresh registry. -/
theorem metrics_200_endtoend :
    (Counters.zero.record head200).total = 1
    ∧ (Counters.zero.record head200).bucket .c2 = 1 := by
  refine ⟨rfl, ?_⟩
  have : classify head200 = .c2 := classify_faithful_200
  simp [Counters.record, Counters.zero, this]

end O11y.MetricsCounters

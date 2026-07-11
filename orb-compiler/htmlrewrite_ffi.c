/* FFI driver for htmlrewrite.pnk (the S12 HtmlRewrite tokenizer loop). Linked
 * next to the stock CakeML basis_ffi.c (which provides main()/heap/stack/cml_main).
 * ONE load, ONE report — the single FFI-oracle contract of this image.
 *
 * @load_body(ctrl, 32, inb, 4096) -> ffiload_body(c=ctrl, .., a=inb, ..):
 *   stages the response body from BODY (or stdin if BODY unset) into inb[0..],
 *   and writes its length L at ctrl+0.
 *
 * @report_body(ctrl, 16, out, 4096) -> ffireport_body(c=ctrl, a=out):
 *   c = [L @c+0, O @c+8]; a = the rewritten body. Prints O and out[0..O) verbatim,
 *   plus a byte checksum, so the rewrite can be diffed against the deployed
 *   Reactor.Stage.HtmlRewrite.rewriteBytes ground truth.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef unsigned long long ull;

void ffiload_body(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t L = 0;
  const char *body = getenv("BODY");
  if (body) {
    size_t n = strlen(body);
    if ((long)n > alen) { fprintf(stderr, "body too big\n"); exit(1); }
    memcpy(a, body, n);
    L = (uint64_t)n;
  } else {
    /* no BODY env: read raw bytes from stdin (lets us feed arbitrary bytes incl.
     * embedded NULs that the env cannot carry) */
    ssize_t r = read(0, a, (size_t)alen);
    if (r > 0) L = (uint64_t)r;
  }
  memcpy(c + 0, &L, 8);
}

void ffireport_body(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t L = 0, O = 0;
  memcpy(&L, c + 0, 8);
  memcpy(&O, c + 8, 8);
  uint64_t sum = 0;
  for (uint64_t i = 0; i < O; i++) sum += a[i];
  printf("in_len=%llu out_len=%llu checksum=%llu\n", (ull)L, (ull)O, (ull)sum);
  printf("OUT[");
  fwrite(a, 1, (size_t)O, stdout);
  printf("]\n");
  fflush(stdout);
}

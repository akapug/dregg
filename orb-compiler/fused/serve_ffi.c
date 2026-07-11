/* Fused-serve FFI driver for serve.pnk. Linked next to the stock basis_ffi.c
 * (which provides main(), heap/stack setup, cml_main dispatch). ONE load, ONE
 * report — the single FFI-oracle contract the fused serve shares.
 *
 * @load_serve(ctrl, 32, buf, 4096) -> ffiload_serve(c=ctrl, .., a=buf, ..):
 *   stages a whole request from the environment into the shared control block:
 *     LINE   request-line bytes            -> buf[0..]          (a+0)
 *     ADDR   encoded client-address bytes  -> abuf = buf+4096   (a+4096)
 *            (space/comma-separated decimals, e.g. "4 0 0 0 0 1 0 1 0" = v4 10/8)
 *     MAXAGE HSTS max-age scalar           -> ctrl+16
 *     CODE   redirect Code tag (0..3)      -> ctrl+24
 *   seeds the 159-byte response body source at src = buf+12288 (a+12288), and
 *   seeds the two header templates the threaded Response appends:
 *     HSTS     -> hsts_tmpl = a+12544, its length -> ctrl+112
 *     Location -> loc_tmpl  = a+12800, its length -> ctrl+120
 *   scalars: len@ctrl+0, alen@ctrl+8, maxage@ctrl+16, code@ctrl+24.
 *
 * @report_serve(ctrl+32, 80, out, total) -> ffireport_serve(c=ctrl+32, a=out):
 *   c = the 10-word result vector (mirrored from the threaded Response record);
 *   a = the serialized response (status line + accumulated headers + body) of
 *   `total` bytes. Prints the serve decision AND the serialized Response.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned long long ull;

void ffiload_serve(unsigned char *c, long clen, unsigned char *a, long alen) {
  /* LINE -> buf */
  const char *line = getenv("LINE");
  uint64_t L = 0;
  if (line) {
    size_t n = strlen(line);
    if ((long)n > alen) { fprintf(stderr, "line too big\n"); exit(1); }
    memcpy(a, line, n);
    L = (uint64_t)n;
  }
  /* ADDR -> abuf = a+4096 */
  const char *addr = getenv("ADDR");
  uint64_t AL = 0;
  unsigned char *ab = a + 4096;
  if (addr) {
    const char *p = addr;
    while (*p) {
      while (*p == ' ' || *p == ',') p++;
      if (!*p) break;
      char *e;
      long v = strtol(p, &e, 10);
      if (e == p) break;
      ab[AL++] = (unsigned char)(v & 0xff);
      p = e;
    }
  }
  uint64_t maxage = getenv("MAXAGE") ? strtoull(getenv("MAXAGE"), 0, 10) : 0;
  uint64_t code   = getenv("CODE")   ? strtoull(getenv("CODE"),   0, 10) : 0;
  memcpy(c + 0,  &L,      8);
  memcpy(c + 8,  &AL,     8);
  memcpy(c + 16, &maxage, 8);
  memcpy(c + 24, &code,   8);
  /* seed the 159-byte response body source at src = a+12288 */
  unsigned char *src = a + 12288;
  for (int i = 0; i < 159; i++) src[i] = (unsigned char)(0x20 + (i % 90));
  /* seed the two header templates the threaded Response appends */
  const char *hs = "Strict-Transport-Security: max-age=31536000\r\n";
  unsigned char *ht = a + 12544;
  uint64_t HL = (uint64_t)strlen(hs);
  memcpy(ht, hs, HL);
  const char *ls = "Location: /\r\n";
  unsigned char *lt = a + 12800;
  uint64_t LOCL = (uint64_t)strlen(ls);
  memcpy(lt, ls, LOCL);
  memcpy(c + 112, &HL,   8);   /* hsts_tmpl length  -> ctrl+112 */
  memcpy(c + 120, &LOCL, 8);   /* loc_tmpl  length  -> ctrl+120 */
}

void ffireport_serve(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t r[10];
  memcpy(r, c, 80);
  printf("parse.ok=%llu method_len=%llu target_len=%llu ver_len=%llu\n",
         (ull)r[0], (ull)r[1], (ull)r[2], (ull)r[3]);
  printf("traversal.blocked=%llu ipf.admit=%llu machine.counter=%llu "
         "hsts.effective=%llu final.status=%llu ADMIT=%llu\n",
         (ull)r[4], (ull)r[5], (ull)r[6], (ull)r[7], (ull)r[8], (ull)r[9]);
  /* the serialized Response the threaded record produced: status line +
   * accumulated header block + body, `alen` bytes total. */
  printf("--- serialized response (%ld bytes) ---\n", alen);
  fwrite(a, 1, (size_t)alen, stdout);
  printf("--- end response ---\n");
  uint64_t sum = 0;
  for (long i = 0; i < alen; i++) sum += a[i];
  printf("response.bytes=%ld response_checksum=%llu\n", alen, (ull)sum);
  fflush(stdout);
}

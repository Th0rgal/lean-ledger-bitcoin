/*
 * test_bolos_ffi.c — automated host + ARM Thumb cross-compile C unit tests
 * for the lean-ledger-bitcoin BOLOS FFI shim.
 *
 * Host mode (default):  built with the host C compiler, linked against the
 *   turbo-lean-emitted host freestanding archive
 *   (ffi/bolos/build/host/liblean_ledger_bitcoin.a) and executed; failures
 *   print diagnostics and the process exits non-zero.
 *
 * Freestanding mode (-DLLB_TEST_FREESTANDING): no libc, no stdio — built with
 *   `clang --target=thumbv6m-none-eabi` / `thumbv8m.main-none-eabi` and
 *   `arm-none-eabi-gcc`, linked against the matching emitted archive; every
 *   check increments `g_llb_test_failures` and `main()` returns the count.
 *
 * The mock TCB installs a deterministic reference SHA-256 and record/replay
 * doubles for the BOLOS syscalls, exercising every shim wrapper including
 * the fail-closed paths.
 */
#include "llb_bolos_shim.h"

/* ---- tiny libc-free helpers (both modes) ---- */
static void *fs_memset(void *s, int c, size_t n) {
  unsigned char *p = (unsigned char *)s;
  while (n-- != 0) {
    *p++ = (unsigned char)c;
  }
  return s;
}
static void *fs_memcpy(void *dst, const void *src, size_t n) {
  unsigned char *d = (unsigned char *)dst;
  const unsigned char *s = (const unsigned char *)src;
  while (n-- != 0) {
    *d++ = *s++;
  }
  return dst;
}
static int fs_memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *pa = (const unsigned char *)a;
  const unsigned char *pb = (const unsigned char *)b;
  while (n-- != 0) {
    if (*pa != *pb) {
      return (*pa < *pb) ? -1 : 1;
    }
    pa++;
    pb++;
  }
  return 0;
}

#if defined(LLB_TEST_FREESTANDING)

/* freestanding harness: no libc; the compiler may still emit memset/memcpy
 * for aggregate copies, so provide freestanding definitions. */
volatile int g_llb_test_failures = 0;
#define TEST_CHECK(cond)              \
  do {                                \
    if (!(cond)) {                    \
      g_llb_test_failures++;          \
    }                                 \
  } while (0)
#define TEST_NOTE(msg) ((void)(msg))

void *memset(void *s, int c, size_t n);
void *memcpy(void *dst, const void *src, size_t n);
void *memset(void *s, int c, size_t n) { return fs_memset(s, c, n); }
void *memcpy(void *dst, const void *src, size_t n) { return fs_memcpy(dst, src, n); }

/*
 * ARM EABI runtime helpers the compilers may emit for block moves on
 * thumbv6m / thumbv8m.main even under -ffreestanding. Note the EABI
 * memset/memclr argument order: (dst, size, value).
 */
#if defined(__arm__)
void __aeabi_memcpy(void *d, const void *s, size_t n) { fs_memcpy(d, s, n); }
void __aeabi_memcpy4(void *d, const void *s, size_t n) { fs_memcpy(d, s, n); }
void __aeabi_memcpy8(void *d, const void *s, size_t n) { fs_memcpy(d, s, n); }
void __aeabi_memset(void *d, size_t n, int c) { fs_memset(d, c, n); }
void __aeabi_memset4(void *d, size_t n, int c) { fs_memset(d, c, n); }
void __aeabi_memclr(void *d, size_t n) { fs_memset(d, 0, n); }
void __aeabi_memclr4(void *d, size_t n) { fs_memset(d, 0, n); }
void __aeabi_memclr8(void *d, size_t n) { fs_memset(d, 0, n); }
#endif

#else /* hosted */

#include <stdio.h>

static int g_llb_test_failures = 0;
static int g_llb_check_count = 0;
#define TEST_CHECK(cond)                                                   \
  do {                                                                     \
    g_llb_check_count++;                                                   \
    if (!(cond)) {                                                         \
      g_llb_test_failures++;                                               \
      printf("FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);               \
    }                                                                      \
  } while (0)
#define TEST_NOTE(msg) printf("%s\n", (msg))

#endif

/* ================================================================== */
/* Compact reference SHA-256 (FIPS 180-4) for the mock `cx_hash_sha256` */
/* ================================================================== */

typedef struct {
  uint32_t h[8];
  uint32_t total_len; /* input bytes; 32-bit keeps the freestanding test ARMv6-M
                         clean (no 64-bit libcalls); test inputs are tiny */
  unsigned char buf[64];
  size_t buf_len;
} llb_test_sha256_ctx;

static const uint32_t llb_test_sha256_k[64] = {
  0x428a2f98u, 0x71374491u, 0xb5c0fbcfu, 0xe9b5dba5u, 0x3956c25bu, 0x59f111f1u,
  0x923f82a4u, 0xab1c5ed5u, 0xd807aa98u, 0x12835b01u, 0x243185beu, 0x550c7dc3u,
  0x72be5d74u, 0x80deb1feu, 0x9bdc06a7u, 0xc19bf174u, 0xe49b69c1u, 0xefbe4786u,
  0x0fc19dc6u, 0x240ca1ccu, 0x2de92c6fu, 0x4a7484aau, 0x5cb0a9dcu, 0x76f988dau,
  0x983e5152u, 0xa831c66du, 0xb00327c8u, 0xbf597fc7u, 0xc6e00bf3u, 0xd5a79147u,
  0x06ca6351u, 0x14292967u, 0x27b70a85u, 0x2e1b2138u, 0x4d2c6dfcu, 0x53380d13u,
  0x650a7354u, 0x766a0abbu, 0x81c2c92eu, 0x92722c85u, 0xa2bfe8a1u, 0xa81a664bu,
  0xc24b8b70u, 0xc76c51a3u, 0xd192e819u, 0xd6990624u, 0xf40e3585u, 0x106aa070u,
  0x19a4c116u, 0x1e376c08u, 0x2748774cu, 0x34b0bcb5u, 0x391c0cb3u, 0x4ed8aa4au,
  0x5b9cca4fu, 0x682e6ff3u, 0x748f82eeu, 0x78a5636fu, 0x84c87814u, 0x8cc70208u,
  0x90befffau, 0xa4506cebu, 0xbef9a3f7u, 0xc67178f2u};

#define LLB_TEST_ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static void llb_test_sha256_compress(llb_test_sha256_ctx *ctx, const unsigned char *p) {
  uint32_t w[64];
  size_t i;
  for (i = 0; i < 16; i++) {
    w[i] = ((uint32_t)p[i * 4] << 24) | ((uint32_t)p[i * 4 + 1] << 16) |
           ((uint32_t)p[i * 4 + 2] << 8) | (uint32_t)p[i * 4 + 3];
  }
  for (i = 16; i < 64; i++) {
    uint32_t s0 = LLB_TEST_ROTR(w[i - 15], 7) ^ LLB_TEST_ROTR(w[i - 15], 18) ^ (w[i - 15] >> 3);
    uint32_t s1 = LLB_TEST_ROTR(w[i - 2], 17) ^ LLB_TEST_ROTR(w[i - 2], 19) ^ (w[i - 2] >> 10);
    w[i] = w[i - 16] + s0 + w[i - 7] + s1;
  }
  uint32_t a = ctx->h[0], b = ctx->h[1], c = ctx->h[2], d = ctx->h[3];
  uint32_t e = ctx->h[4], f = ctx->h[5], g = ctx->h[6], h = ctx->h[7];
  for (i = 0; i < 64; i++) {
    uint32_t S1 = LLB_TEST_ROTR(e, 6) ^ LLB_TEST_ROTR(e, 11) ^ LLB_TEST_ROTR(e, 25);
    uint32_t ch = (e & f) ^ (~e & g);
    uint32_t t1 = h + S1 + ch + llb_test_sha256_k[i] + w[i];
    uint32_t S0 = LLB_TEST_ROTR(a, 2) ^ LLB_TEST_ROTR(a, 13) ^ LLB_TEST_ROTR(a, 22);
    uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
    uint32_t t2 = S0 + maj;
    h = g; g = f; f = e; e = d + t1;
    d = c; c = b; b = a; a = t1 + t2;
  }
  ctx->h[0] += a; ctx->h[1] += b; ctx->h[2] += c; ctx->h[3] += d;
  ctx->h[4] += e; ctx->h[5] += f; ctx->h[6] += g; ctx->h[7] += h;
}

static void llb_test_sha256_init(llb_test_sha256_ctx *ctx) {
  static const uint32_t init[8] = {0x6a09e667u, 0xbb67ae85u, 0x3c6ef372u, 0xa54ff53au,
                                    0x510e527fu, 0x9b05688cu, 0x1f83d9abu, 0x5be0cd19u};
  size_t i;
  for (i = 0; i < 8; i++) {
    ctx->h[i] = init[i];
  }
  ctx->total_len = 0;
  ctx->buf_len = 0;
}

static void llb_test_sha256_update(llb_test_sha256_ctx *ctx, const unsigned char *data, size_t len) {
  ctx->total_len += len;
  while (len > 0) {
    size_t take = 64 - ctx->buf_len;
    if (take > len) {
      take = len;
    }
    fs_memcpy(ctx->buf + ctx->buf_len, data, take);
    ctx->buf_len += take;
    data += take;
    len -= take;
    if (ctx->buf_len == 64) {
      llb_test_sha256_compress(ctx, ctx->buf);
      ctx->buf_len = 0;
    }
  }
}

static void llb_test_sha256_final(llb_test_sha256_ctx *ctx, unsigned char out[32]) {
  uint32_t bits = ctx->total_len * 8u;
  unsigned char one = 0x80;
  unsigned char zero = 0;
  unsigned char lenb[8];
  size_t i;
  llb_test_sha256_update(ctx, &one, 1);
  while (ctx->buf_len != 56) {
    llb_test_sha256_update(ctx, &zero, 1);
  }
  /* 64-bit big-endian bit length. `bits` is 32-bit, so the high 4 bytes are
   * zero; written explicitly to avoid `bits >> 32+` undefined behaviour on
   * 32-bit targets (ARMv6-M / RV32). */
  lenb[0] = 0;
  lenb[1] = 0;
  lenb[2] = 0;
  lenb[3] = 0;
  lenb[4] = (unsigned char)(bits >> 24);
  lenb[5] = (unsigned char)(bits >> 16);
  lenb[6] = (unsigned char)(bits >> 8);
  lenb[7] = (unsigned char)bits;
  fs_memcpy(ctx->buf + 56, lenb, 8);
  llb_test_sha256_compress(ctx, ctx->buf);
  ctx->buf_len = 0;
  for (i = 0; i < 8; i++) {
    out[i * 4] = (unsigned char)(ctx->h[i] >> 24);
    out[i * 4 + 1] = (unsigned char)(ctx->h[i] >> 16);
    out[i * 4 + 2] = (unsigned char)(ctx->h[i] >> 8);
    out[i * 4 + 3] = (unsigned char)(ctx->h[i]);
  }
}

static void llb_test_sha256(const unsigned char *data, size_t len, unsigned char out[32]) {
  llb_test_sha256_ctx ctx;
  llb_test_sha256_init(&ctx);
  if (len > 0) {
    llb_test_sha256_update(&ctx, data, len);
  }
  llb_test_sha256_final(&ctx, out);
}

/* ================================================================== */
/* Mock BOLOS TCB                                                      */
/* ================================================================== */

static uint32_t g_mock_last_mode;
static llb_cx_curve_t g_mock_last_curve;
static uint32_t g_mock_last_path_len;
static uint32_t g_mock_last_path[16];
static uint32_t g_mock_last_seed_len;
static uint8_t g_mock_derive_calls;
static uint8_t g_mock_io_calls;
static uint8_t g_mock_last_channel;
static uint16_t g_mock_last_tx_len;
static uint8_t g_mock_rng_calls;
static uint32_t g_mock_rng_state;
static uint8_t g_mock_ui_calls;
static int g_mock_ui_last_accepted;

static llb_cx_err_t mock_derive_bip32_with_seed(uint32_t mode, llb_cx_curve_t curve,
                                                const uint32_t *path, uint32_t path_len,
                                                uint8_t raw_privkey[LLB_BIP32_RAW_PRIVKEY_SIZE],
                                                uint8_t *chain_code,
                                                const uint8_t *seed, uint32_t seed_len) {
  uint32_t i;
  g_mock_last_mode = mode;
  g_mock_last_curve = curve;
  g_mock_last_path_len = path_len;
  g_mock_last_seed_len = seed_len;
  g_mock_derive_calls++;
  for (i = 0; i < path_len && i < 16; i++) {
    g_mock_last_path[i] = path[i];
  }
  /* Deterministic stand-in for the SE BIP32 derivation: the private key is a
   * simple digest of (mode, curve, path, seed) and the chain code of the
   * path; the first 32 bytes of raw_privkey carry the key, the next 32 the
   * SLIP-21 style chain part (only the first 32 are the secp256k1 key). */
  uint32_t seed_i = 0;
  for (i = 0; i < LLB_BIP32_RAW_PRIVKEY_SIZE; i++) {
    uint32_t acc = mode + curve * 31u + (uint32_t)i * 2654435761u;
    uint32_t j;
    for (j = 0; j < path_len && j < 16; j++) {
      acc = acc * 1103515245u + g_mock_last_path[j] + 12345u;
    }
    if (seed != NULL && seed_len > 0) {
      acc ^= (uint32_t)seed[seed_i] * 2654435761u;
      seed_i++;
      if (seed_i >= seed_len) {
        seed_i = 0;
      }
    }
    raw_privkey[i] = (unsigned char)(acc >> 24);
  }
  if (chain_code != NULL) {
    for (i = 0; i < LLB_BIP32_CHAIN_CODE_SIZE; i++) {
      chain_code[i] = (unsigned char)(raw_privkey[i] ^ raw_privkey[i + 32]);
    }
  }
  return LLB_CX_OK;
}

static size_t mock_hash_sha256(const uint8_t *in, size_t len, uint8_t *out, size_t out_len) {
  if (out_len < 32) {
    return 0;
  }
  llb_test_sha256(in, len, out);
  return 32;
}

static llb_cx_err_t mock_ecfp_generate_pair(llb_cx_curve_t curve,
                                            llb_cx_ecfp_public_key_t *pubkey,
                                            llb_cx_ecfp_private_key_t *privkey,
                                            bool keep_private) {
  (void)keep_private;
  if (curve != LLB_CX_CURVE_SECP256K1) {
    return LLB_CX_INTERNAL_ERROR;
  }
  pubkey->curve = curve;
  pubkey->W_len = LLB_ECFP_PUBLIC_KEY_SIZE;
  pubkey->W[0] = 0x04;
  {
    size_t i;
    for (i = 0; i < 32; i++) {
      pubkey->W[1 + i] = privkey->d[i];
      pubkey->W[33 + i] = (unsigned char)~privkey->d[i];
    }
  }
  return LLB_CX_OK;
}

static llb_cx_err_t mock_ecfp_add_point(llb_cx_curve_t curve, uint8_t *r,
                                        const uint8_t *p, const uint8_t *q) {
  (void)curve;
  size_t i;
  for (i = 0; i < LLB_ECFP_PUBLIC_KEY_SIZE; i++) {
    r[i] = (unsigned char)(p[i] ^ q[i]);
  }
  return LLB_CX_OK;
}

static llb_cx_err_t mock_ecfp_scalar_mult(llb_cx_curve_t curve, uint8_t *p,
                                          const uint8_t *k, size_t k_len) {
  (void)curve;
  size_t i;
  size_t ki = 0;
  for (i = 0; i < LLB_ECFP_PUBLIC_KEY_SIZE; i++) {
    p[i] = (unsigned char)(p[i] + k[ki]);
    ki++;
    if (ki >= k_len) {
      ki = 0;
    }
  }
  return LLB_CX_OK;
}

static void mock_rng(uint8_t *buffer, size_t len) {
  g_mock_rng_calls++;
  if (g_mock_rng_state == 0) {
    g_mock_rng_state = 0x12345678u;
  }
  size_t i;
  for (i = 0; i < len; i++) {
    g_mock_rng_state ^= g_mock_rng_state << 13;
    g_mock_rng_state ^= g_mock_rng_state >> 17;
    g_mock_rng_state ^= g_mock_rng_state << 5;
    buffer[i] = (unsigned char)(g_mock_rng_state >> 24);
  }
}

static uint16_t mock_io_exchange(uint8_t channel_and_flags, uint16_t tx_len) {
  g_mock_io_calls++;
  g_mock_last_channel = channel_and_flags;
  g_mock_last_tx_len = tx_len;
  return (uint16_t)(tx_len == 0 ? 42 : 7);
}

static void mock_ui_review(const char *title, const char *body,
                           llb_bolos_ui_choice_cb_t on_choice, void *user_state) {
  (void)title;
  (void)body;
  g_mock_ui_calls++;
  /* auto-accept when user_state points at a non-zero int, reject otherwise */
  int accept = (user_state != NULL && *(int *)user_state != 0);
  g_mock_ui_last_accepted = accept;
  on_choice((bool)accept, user_state);
}

static void install_mock_tcb(void) {
  llb_bolos_tcb_t tcb;
  fs_memset(&tcb, 0, sizeof(tcb));
  tcb.derive_bip32_with_seed = mock_derive_bip32_with_seed;
  tcb.hash_sha256 = mock_hash_sha256;
  tcb.ecfp_generate_pair = mock_ecfp_generate_pair;
  tcb.ecfp_add_point = mock_ecfp_add_point;
  tcb.ecfp_scalar_mult = mock_ecfp_scalar_mult;
  tcb.rng = mock_rng;
  tcb.io_exchange = mock_io_exchange;
  tcb.ui_review = mock_ui_review;
  if (llb_bolos_tcb_set(&tcb) != LLB_BOLOS_OK) {
    TEST_CHECK(0 && "mock TCB install failed");
  }
}

/* ================================================================== */
/* Tests                                                               */
/* ================================================================== */

static int g_ui_choice_seen_accepted = -1;
static int g_ui_choice_seen_state = -1;

static void ui_choice_cb(bool accepted, void *user_state) {
  g_ui_choice_seen_accepted = accepted ? 1 : 0;
  g_ui_choice_seen_state = (user_state != NULL) ? *(int *)user_state : -1;
}

static void test_kernel_version_abi(void) {
  TEST_NOTE("test_kernel_version_abi");
  uint32_t packed = llb_version_packed(); /* freestanding ABI into the archive */
  TEST_CHECK(packed == LLB_VERSION_PACKED_EXPECTED);
  TEST_CHECK((packed >> 16) == LLB_VERSION_MAJOR);
  TEST_CHECK(((packed >> 8) & 0xFFu) == LLB_VERSION_MINOR);
  TEST_CHECK((packed & 0xFFu) == LLB_VERSION_PATCH);
  TEST_CHECK(llb_bolos_check_kernel_version() == LLB_BOLOS_OK);
}

static void test_fail_closed_without_tcb(void) {
  TEST_NOTE("test_fail_closed_without_tcb");
  uint8_t privkey[LLB_BIP32_RAW_PRIVKEY_SIZE];
  uint8_t chain[LLB_BIP32_CHAIN_CODE_SIZE];
  uint8_t digest[LLB_SHA256_SIZE];
  uint8_t point[LLB_ECFP_PUBLIC_KEY_SIZE];
  uint16_t rx = 0;

  TEST_CHECK(llb_bolos_tcb_set(NULL) == LLB_BOLOS_OK);
  TEST_CHECK(llb_bolos_tcb_get() == NULL);
  TEST_CHECK(llb_bolos_derive_bip32(LLB_CX_CURVE_SECP256K1, NULL, 0, privkey, chain) ==
             LLB_CX_INTERNAL_ERROR);
  TEST_CHECK(llb_bolos_sha256((const uint8_t *)"x", 1, digest) == LLB_BOLOS_ERR_TCB);
  TEST_CHECK(llb_bolos_ecfp_generate_pair(LLB_CX_CURVE_SECP256K1, NULL, NULL, false) ==
             LLB_CX_INTERNAL_ERROR);
  TEST_CHECK(llb_bolos_ecfp_add_point(LLB_CX_CURVE_SECP256K1, point, point, point) ==
             LLB_CX_INTERNAL_ERROR);
  TEST_CHECK(llb_bolos_ecfp_scalar_mult(LLB_CX_CURVE_SECP256K1, point, chain, 32) ==
             LLB_CX_INTERNAL_ERROR);
  TEST_CHECK(llb_bolos_rng(digest, sizeof(digest)) == LLB_BOLOS_ERR_TCB);
  TEST_CHECK(llb_bolos_io_exchange(LLB_CHANNEL_APDU | LLB_IO_RETURN_AFTER_TX, 10, &rx) ==
             LLB_BOLOS_ERR_TCB);
  TEST_CHECK(rx == 0);
  TEST_CHECK(llb_bolos_ui_review("t", "b", ui_choice_cb, NULL) == LLB_BOLOS_ERR_TCB);
}

static void test_tcb_table_validation(void) {
  TEST_NOTE("test_tcb_table_validation");
  llb_bolos_tcb_t tcb;
  fs_memset(&tcb, 0, sizeof(tcb));
  /* all-NULL table must be rejected */
  TEST_CHECK(llb_bolos_tcb_set(&tcb) == LLB_BOLOS_ERR_TCB);
  TEST_CHECK(llb_bolos_tcb_get() == NULL);
}

static void test_sha256_vectors(void) {
  TEST_NOTE("test_sha256_vectors");
  static const uint8_t empty_expected[32] = {
      0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
      0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55};
  static const uint8_t abc_expected[32] = {
      0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
      0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad};
  uint8_t out[32];
  int rc = llb_bolos_sha256(NULL, 0, out);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  TEST_CHECK(fs_memcmp(out, empty_expected, 32) == 0);
  rc = llb_bolos_sha256((const uint8_t *)"abc", 3, out);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  TEST_CHECK(fs_memcmp(out, abc_expected, 32) == 0);
  /* 55/56/64-byte inputs exercise the SHA-256 padding boundaries */
  uint8_t buf[64];
  size_t i;
  for (i = 0; i < sizeof(buf); i++) {
    buf[i] = (unsigned char)i;
  }
  rc = llb_bolos_sha256(buf, 55, out);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  rc = llb_bolos_sha256(buf, 56, out);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  rc = llb_bolos_sha256(buf, 64, out);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  /* NULL output is a parameter error, not a TCB crash */
  TEST_CHECK(llb_bolos_sha256(buf, 1, NULL) == LLB_BOLOS_ERR_PARAM);
}

static void test_derive_bip32(void) {
  TEST_NOTE("test_derive_bip32");
  const uint32_t path[3] = {0x80000000u | 84u, 0x80000000u | 0u, 0x80000000u | 0u};
  uint8_t privkey[LLB_BIP32_RAW_PRIVKEY_SIZE];
  uint8_t chain[LLB_BIP32_CHAIN_CODE_SIZE];
  llb_cx_err_t rc = llb_bolos_derive_bip32(LLB_CX_CURVE_SECP256K1, path, 3, privkey, chain);
  TEST_CHECK(rc == LLB_CX_OK);
  TEST_CHECK(g_mock_derive_calls == 1);
  TEST_CHECK(g_mock_last_mode == LLB_HDW_NORMAL);
  TEST_CHECK(g_mock_last_curve == LLB_CX_CURVE_SECP256K1);
  TEST_CHECK(g_mock_last_path_len == 3);
  TEST_CHECK(g_mock_last_path[0] == path[0]);
  TEST_CHECK(g_mock_last_path[2] == path[2]);
  uint8_t non_zero = 0;
  size_t i;
  for (i = 0; i < 32; i++) {
    non_zero |= privkey[i] | chain[i];
  }
  TEST_CHECK(non_zero != 0);

  /* seed variant (SLIP-21 style) */
  const uint8_t seed[4] = {0xde, 0xad, 0xbe, 0xef};
  rc = llb_bolos_derive_bip32_with_seed(LLB_HDW_SLIP21, LLB_CX_CURVE_SECP256K1, path, 1,
                                        privkey, NULL, seed, sizeof(seed));
  TEST_CHECK(rc == LLB_CX_OK);
  TEST_CHECK(g_mock_last_mode == LLB_HDW_SLIP21);
  TEST_CHECK(g_mock_last_seed_len == sizeof(seed));
  TEST_CHECK(g_mock_derive_calls == 2);

  /* NULL key buffer is rejected before reaching the TCB */
  TEST_CHECK(llb_bolos_derive_bip32(LLB_CX_CURVE_SECP256K1, path, 3, NULL, chain) ==
             LLB_CX_INTERNAL_ERROR);
  TEST_CHECK(g_mock_derive_calls == 2);
}

static void test_ecfp(void) {
  TEST_NOTE("test_ecfp");
  llb_cx_ecfp_private_key_t priv;
  llb_cx_ecfp_public_key_t pub;
  priv.curve = LLB_CX_CURVE_SECP256K1;
  priv.d_len = 32;
  size_t i;
  for (i = 0; i < 32; i++) {
    priv.d[i] = (unsigned char)(i + 1);
  }
  llb_cx_err_t rc = llb_bolos_ecfp_generate_pair(LLB_CX_CURVE_SECP256K1, &pub, &priv, true);
  TEST_CHECK(rc == LLB_CX_OK);
  TEST_CHECK(pub.curve == LLB_CX_CURVE_SECP256K1);
  TEST_CHECK(pub.W_len == LLB_ECFP_PUBLIC_KEY_SIZE);
  TEST_CHECK(pub.W[0] == 0x04);
  TEST_CHECK(pub.W[1] == 1 && pub.W[2] == 2);
  TEST_CHECK(pub.W[33] == (unsigned char)~1);

  uint8_t p[LLB_ECFP_PUBLIC_KEY_SIZE];
  uint8_t q[LLB_ECFP_PUBLIC_KEY_SIZE];
  uint8_t r[LLB_ECFP_PUBLIC_KEY_SIZE];
  for (i = 0; i < LLB_ECFP_PUBLIC_KEY_SIZE; i++) {
    p[i] = (unsigned char)i;
    q[i] = (unsigned char)(i * 3);
  }
  rc = llb_bolos_ecfp_add_point(LLB_CX_CURVE_SECP256K1, r, p, q);
  TEST_CHECK(rc == LLB_CX_OK);
  TEST_CHECK(r[0] == (unsigned char)(p[0] ^ q[0]));

  rc = llb_bolos_ecfp_scalar_mult(LLB_CX_CURVE_SECP256K1, p, priv.d, 32);
  TEST_CHECK(rc == LLB_CX_OK);
  /* k_len > 32 must be rejected by the shim before reaching the TCB */
  rc = llb_bolos_ecfp_scalar_mult(LLB_CX_CURVE_SECP256K1, p, priv.d, 33);
  TEST_CHECK(rc == LLB_CX_INTERNAL_ERROR);
}

static void test_rng(void) {
  TEST_NOTE("test_rng");
  uint8_t a[16];
  uint8_t b[16];
  TEST_CHECK(llb_bolos_rng(a, sizeof(a)) == LLB_BOLOS_OK);
  TEST_CHECK(g_mock_rng_calls == 1);
  TEST_CHECK(llb_bolos_rng(b, sizeof(b)) == LLB_BOLOS_OK);
  TEST_CHECK(g_mock_rng_calls == 2);
  /* deterministic xorshift doubles must advance state between calls */
  TEST_CHECK(fs_memcmp(a, b, sizeof(a)) != 0);
  TEST_CHECK(llb_bolos_rng(NULL, 4) == LLB_BOLOS_ERR_PARAM);
}

static void test_io_exchange(void) {
  TEST_NOTE("test_io_exchange");
  uint16_t rx = 0;
  int rc = llb_bolos_io_exchange(LLB_CHANNEL_APDU | LLB_IO_RETURN_AFTER_TX, 128, &rx);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  TEST_CHECK(g_mock_io_calls == 1);
  TEST_CHECK(g_mock_last_channel == (LLB_CHANNEL_APDU | LLB_IO_RETURN_AFTER_TX));
  TEST_CHECK(g_mock_last_tx_len == 128);
  TEST_CHECK(rx == 7);
  rc = llb_bolos_io_exchange(LLB_CHANNEL_APDU, 0, &rx);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  TEST_CHECK(rx == 42);
}

static void test_ui_review(void) {
  TEST_NOTE("test_ui_review");
  int accept = 1;
  g_ui_choice_seen_accepted = -1;
  int rc = llb_bolos_ui_review("Confirm tx", "Send 1 BTC", ui_choice_cb, &accept);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  TEST_CHECK(g_mock_ui_calls == 1);
  TEST_CHECK(g_mock_ui_last_accepted == 1);
  TEST_CHECK(g_ui_choice_seen_accepted == 1);
  TEST_CHECK(g_ui_choice_seen_state == 1);

  accept = 0;
  rc = llb_bolos_ui_review("Confirm tx", "Send 1 BTC", ui_choice_cb, &accept);
  TEST_CHECK(rc == LLB_BOLOS_OK);
  TEST_CHECK(g_mock_ui_last_accepted == 0);
  TEST_CHECK(g_ui_choice_seen_accepted == 0);

  TEST_CHECK(llb_bolos_ui_review(NULL, "b", ui_choice_cb, NULL) == LLB_BOLOS_ERR_PARAM);
}

static void test_wave4_opt_kernels(void) {
  TEST_NOTE("test_wave4_opt_kernels");
  /* O(1)-step Merkle descent state: (size, index) packed as (size << 32) | index.
     The direction is read like the app does: right iff the index changed. */
  uint64_t st = (UINT64_C(7) << 32) | UINT64_C(5);
  st = llb_merkle_advance_state(st); /* mask=4, 5>=4 -> right */
  TEST_CHECK(st == ((UINT64_C(3) << 32) | UINT64_C(1)));
  st = llb_merkle_advance_state(st); /* mask=2, 1<2 -> left */
  TEST_CHECK(st == ((UINT64_C(2) << 32) | UINT64_C(1)));
  st = llb_merkle_advance_state(st); /* mask=1, 1>=1 -> right */
  TEST_CHECK(st == ((UINT64_C(1) << 32) | UINT64_C(0)));
  TEST_CHECK(llb_merkle_advance_state(st) == st); /* leaf: fixed point */

  /* BIP-32 pubkey export prefix safety, Bech32 final constant, wallet name char */
  TEST_CHECK(llb_bip32_pubkey_export_prefix_ok(
      0x80000054u, 0x80000000u, 0x80000000u, 0u, 3u, 0u, 1u) == 1);
  TEST_CHECK(llb_bip32_pubkey_export_prefix_ok(
      0x80000030u, 0x80000000u, 0x80000000u, 0x80000002u, 4u, 0u, 1u) == 1);
  TEST_CHECK(llb_bip32_pubkey_export_prefix_ok(
      0x80000030u, 0x80000000u, 0x80000000u, 0x80000003u, 4u, 0u, 1u) == 0);
  TEST_CHECK(llb_bip32_pubkey_export_prefix_ok(
      0x80454C45u, 0xC2494532u, 0u, 0u, 2u, 0u, 1u) == 1);
  TEST_CHECK(llb_bech32_final_constant(1) == 1u);
  TEST_CHECK(llb_bech32_final_constant(2) == 0x2bc830a3u);
  TEST_CHECK(llb_bech32_final_constant(0) == 0u);
  TEST_CHECK(llb_wallet_name_char_ok((uint8_t)' ', 1) == 0);
  TEST_CHECK(llb_wallet_name_char_ok((uint8_t)' ', 0) == 1);
  TEST_CHECK(llb_wallet_name_char_ok((uint8_t)'A', 1) == 1);
}

static void test_option2_flat_slice_kernels(void) {
  TEST_NOTE("test_option2_flat_slice_kernels");

  /* Checked CompactSize reader */
  uint8_t vi1[1] = {252};
  uint8_t vi3[3] = {0xFD, 0xFD, 0x00};
  uint8_t vi_bad[3] = {0xFD, 0xFC, 0x00};
  uint64_t r1 = llb_read_compact_size_checked(vi1, 1, 1000u);
  TEST_CHECK((r1 >> 32) == 1 && (uint32_t)r1 == 252u);
  uint64_t r3 = llb_read_compact_size_checked(vi3, 3, 1000u);
  TEST_CHECK((r3 >> 32) == 3 && (uint32_t)r3 == 253u);
  TEST_CHECK(llb_read_compact_size_checked(vi_bad, 3, 1000u) == 0);
  TEST_CHECK(llb_read_compact_size_checked(vi3, 3, 252u) == 0);

  /* Division-free ASCII satoshi formatting */
  char amt[32];
  uint32_t alen = llb_format_sats_ascii(UINT64_C(123450000), (const uint8_t *)"BTC", 3, 0,
                                        (uint8_t *)amt, sizeof(amt));
  TEST_CHECK(alen == 10);
  TEST_CHECK(fs_memcmp(amt, "1.2345 BTC", 11) == 0);
  alen = llb_format_sats_ascii(UINT64_C(123450000), (const uint8_t *)"BTC", 3, 1,
                               (uint8_t *)amt, sizeof(amt));
  TEST_CHECK(alen == 14 && fs_memcmp(amt, "1.23450000 BTC", 15) == 0);
  alen = llb_format_sats_ascii(UINT64_C(100000000), NULL, 0, 0, (uint8_t *)amt, sizeof(amt));
  TEST_CHECK(alen == 1 && fs_memcmp(amt, "1", 2) == 0);
  /* The BTC / satoshi split is no longer exported; exercise it through the formatter. */
  alen = llb_format_sats_ascii(UINT64_C(99999999), NULL, 0, 0, (uint8_t *)amt, sizeof(amt));
  TEST_CHECK(alen == 10 && fs_memcmp(amt, "0.99999999", 11) == 0);
  alen = llb_format_sats_ascii(UINT64_C(2100000000000000), NULL, 0, 0, (uint8_t *)amt, sizeof(amt));
  TEST_CHECK(alen == 8 && fs_memcmp(amt, "21000000", 9) == 0);
  alen = llb_format_sats_ascii(UINT64_MAX, NULL, 0, 0, (uint8_t *)amt, sizeof(amt));
  TEST_CHECK(alen == 21 && fs_memcmp(amt, "184467440737.09551615", 22) == 0);

  /* Full-path BIP-32 pubkey export safety */
  const uint32_t ok_path[5] = {0x80000054u, 0x80000000u, 0x80000000u, 0u, 7u};
  const uint32_t bad_tail[5] = {0x80000054u, 0x80000000u, 0x80000000u, 0x80000000u, 7u};
  TEST_CHECK(llb_bip32_check_export_path(ok_path, 5, 0) == 1);
  TEST_CHECK(llb_bip32_check_export_path(bad_tail, 5, 0) == 0);

  /* PSBT locktime accumulator + checked sats + dual UTXO */
  uint64_t lt = llb_psbt_locktime_init();
  lt = llb_psbt_locktime_step(lt, 1, 800000u, 0, 0u);
  TEST_CHECK(lt != 0);
  uint64_t fin = llb_psbt_locktime_finalize(lt, 0u);
  TEST_CHECK((fin >> 32) == 1 && (uint32_t)fin == 800000u);
  TEST_CHECK(llb_psbt_locktime_step(lt, 0, 0u, 1, 500000000u) == 0);

  /* 2 inputs with heights 100 and 250: the larger height wins over the fallback */
  uint64_t lt2 = llb_psbt_locktime_step(llb_psbt_locktime_init(), 1, 100u, 0, 0u);
  lt2 = llb_psbt_locktime_step(lt2, 1, 250u, 0, 0u);
  uint64_t det = llb_psbt_locktime_finalize(lt2, 42u);
  TEST_CHECK((det >> 32) == 1 && (uint32_t)det == 250u);

  TEST_CHECK(llb_checked_add_sats_ok(UINT64_C(2100000000000000), 1u) == 0);
  TEST_CHECK(llb_checked_add_sats_val(100u, 200u) == 300u);

  uint8_t p2tr[34];
  p2tr[0] = 0x51;
  p2tr[1] = 0x20;
  for (size_t i = 0; i < 32; i++) {
    p2tr[2 + i] = (uint8_t)(i + 1);
  }
  TEST_CHECK(llb_check_dual_utxo(500u, p2tr, 34, 500u, p2tr, 34) == 1);
  TEST_CHECK(llb_check_dual_utxo(500u, p2tr, 34, 501u, p2tr, 34) == 0);

  /* Constant-stack sorting */
  uint16_t u16s[4] = {40, 10, 30, 20};
  llb_sort_u16(u16s, 4);
  TEST_CHECK(u16s[0] == 10 && u16s[1] == 20 && u16s[2] == 30 && u16s[3] == 40);
  uint8_t recs[9] = {0x03, 0x00, 0x01, 0x01, 0x09, 0x00, 0x01, 0x02, 0x00};
  llb_sort_fixed_bytes(recs, 3, 3);
  TEST_CHECK(recs[0] == 0x01 && recs[1] == 0x02 && recs[3] == 0x01 && recs[4] == 0x09 &&
             recs[6] == 0x03);

  /* BIP-379 Miniscript postfix typechecker & script helpers */
  TEST_CHECK(llb_miniscript_older_ok(144u) == 1);
  TEST_CHECK(llb_miniscript_older_ok(0u) == 0);
  TEST_CHECK(llb_miniscript_after_ok(800000u) == 1);
  TEST_CHECK(llb_miniscript_after_ok(0u) == 0);
  /* and_v(v:pk(A), older(144)) => [pk_k(0x02), c:(0x12), v:(0x15), older(0x06, 144 LE), and_v(0x20)] */
  uint8_t ms_ops[9] = {0x02, 0x12, 0x15, 0x06, 0x90, 0x00, 0x00, 0x00, 0x20};
  uint8_t ms_scratch[128];
  TEST_CHECK(llb_miniscript_check_postfix(ms_ops, 9, 0, 0x03, ms_scratch) == 1);
}

int main(void) {
  test_kernel_version_abi();
  test_wave4_opt_kernels();
  test_option2_flat_slice_kernels();
  test_fail_closed_without_tcb();
  test_tcb_table_validation();
  install_mock_tcb();
  TEST_CHECK(llb_bolos_tcb_get() != NULL);
  test_sha256_vectors();
  test_derive_bip32();
  test_ecfp();
  test_rng();
  test_io_exchange();
  test_ui_review();
  /* uninstall again: wrappers must fail closed afterwards */
  TEST_CHECK(llb_bolos_tcb_set(NULL) == LLB_BOLOS_OK);
  uint8_t digest[LLB_SHA256_SIZE];
  TEST_CHECK(llb_bolos_sha256(NULL, 0, digest) == LLB_BOLOS_ERR_TCB);

#if !defined(LLB_TEST_FREESTANDING)
  printf("llb bolos ffi tests: %d checks, %d failures\n", g_llb_check_count,
         g_llb_test_failures);
#endif
  return g_llb_test_failures;
}

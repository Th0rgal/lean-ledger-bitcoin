// microbench_bolos.c — Deterministic x86_64 rdtsc + wall-clock microbenchmark
// comparing unmodified LedgerHQ/app-bitcoin (f010982) C hotspots against our
// Lean-integrated freestanding kernel implementations on identical workloads.
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <x86intrin.h>

#include "liblean_ledger_bitcoin.h"

#define MAX_AMOUNT_LENGTH 25
#define BIP44_COIN_TYPE 0U
#define MAX_BIP44_ACCOUNT_RECOMMENDED 100U
#define H 0x80000000UL

static inline uint64_t rdtsc_start(void) {
    unsigned int aux;
    _mm_lfence();
    uint64_t t = __rdtscp(&aux);
    _mm_lfence();
    return t;
}

static inline uint64_t rdtsc_end(void) {
    unsigned int aux;
    uint64_t t = __rdtscp(&aux);
    _mm_lfence();
    return t;
}

static inline uint64_t mono_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC_RAW, &ts);
    return (uint64_t) ts.tv_sec * UINT64_C(1000000000) + (uint64_t) ts.tv_nsec;
}

// ============================================================================
// 1. format_sats_amount: Reference vs Lean
// ============================================================================
static size_t ref_n_digits(uint64_t number) {
    size_t count = 0;
    do {
        count++;
        number /= 10;
    } while (number != 0);
    return count;
}

__attribute__((noinline)) void ref_format_sats_amount(const char *coin_name,
                                                      uint64_t amount,
                                                      char out[static MAX_AMOUNT_LENGTH + 1]) {
    uint64_t integral_part = amount / 100000000;
    uint32_t fractional_part = (uint32_t) (amount % 100000000);

    char fractional_str[9];
    snprintf(fractional_str, 9, "%08u", fractional_part);
    for (int i = 7; i > 0 && fractional_str[i] == '0'; i--) {
        fractional_str[i] = '\0';
    }

    char integral_str[12 + 1];
    size_t integral_part_digit_count = ref_n_digits(integral_part);
    for (unsigned int i = 0; i < integral_part_digit_count; i++) {
        integral_str[integral_part_digit_count - 1 - i] = '0' + (integral_part % 10);
        integral_part /= 10;
    }
    integral_str[integral_part_digit_count] = '\0';

    snprintf(out,
             MAX_AMOUNT_LENGTH + 1,
             "%s%s%s %s",
             integral_str,
             fractional_part ? "." : "",
             fractional_part ? fractional_str : "",
             coin_name);
}

__attribute__((noinline)) void lean_format_sats_amount(const char *coin_name,
                                                       uint64_t amount,
                                                       char out[static MAX_AMOUNT_LENGTH + 1]) {
    size_t ticker_len = strlen(coin_name);
    if (ticker_len > MAX_AMOUNT_LENGTH) {
        ticker_len = MAX_AMOUNT_LENGTH;
    }
    (void) llb_format_sats_ascii(amount,
                                 (const uint8_t *) coin_name,
                                 (uint32_t) ticker_len,
                                 0U,
                                 (uint8_t *) out,
                                 MAX_AMOUNT_LENGTH + 1U);
}

// ============================================================================
// 2. merkle_get_ith_direction: Reference O(log^2 n) vs Lean O(log n)
// ============================================================================
static inline uint8_t ref_ceil_lg(uint32_t x) {
    if (x <= 1) return 0;
    uint8_t r = 0;
    uint32_t v = x - 1;
    while (v > 0) {
        v >>= 1;
        r++;
    }
    return r;
}

__attribute__((noinline)) int ref_merkle_get_ith_direction(size_t size, size_t index, size_t i) {
    if (size <= 1 || index >= size) {
        return -1;
    }
    uint8_t n_directions = 0;
    while (size > 1) {
        uint8_t depth = ref_ceil_lg((uint32_t) size);
        uint32_t mask = 1U << (depth - 1);
        uint8_t is_right_child = (index & mask) != 0 ? 1 : 0;
        if (n_directions == i) {
            return is_right_child;
        }
        ++n_directions;
        if (is_right_child) {
            size -= mask;
            index -= mask;
        } else {
            size = mask;
        }
    }
    return -1;
}

__attribute__((noinline)) int lean_merkle_get_ith_direction(size_t size, size_t index, size_t i) {
    if (size <= 1 || index >= size || size > UINT32_MAX) {
        return -1;
    }
    uint64_t state = (((uint64_t) (uint32_t) size) << 32) | ((uint64_t) (uint32_t) index);
    for (size_t step = 0;; step++) {
        uint64_t next = llb_merkle_advance_state(state);
        if ((uint32_t) (next >> 32) == (uint32_t) (state >> 32)) {
            return -1;
        }
        if (step == i) {
            return ((uint32_t) next != (uint32_t) state) ? 1 : 0;
        }
        state = next;
    }
}

// ============================================================================
// 2b. Bech32 + SegWit witness program validation (segwit_addr.c)
// ============================================================================
__attribute__((noinline)) int ref_segwit_program_check(int witver, size_t witprog_len, int enc) {
    uint32_t fc = 0;
    if (enc == 1) {
        fc = 1U;
    } else if (enc == 2) {
        fc = 0x2bc830a3U;
    } else {
        return 0;
    }
    if (witver < 0 || witver > 16) return 0;
    if (witver == 0 && witprog_len != 20 && witprog_len != 32) return 0;
    if (witprog_len < 2 || witprog_len > 40) return 0;
    if (witver == 0 && enc != 1) return 0;
    if (witver > 0 && enc != 2) return 0;
    return (int) (fc & 0xffU) + 1;
}

__attribute__((noinline)) int lean_segwit_program_check(int witver, size_t witprog_len, int enc) {
    if ((unsigned int) witver > 16U || witprog_len > 40U) return 0;
    uint32_t fc = llb_bech32_final_constant((uint8_t) enc);
    if (fc == 0U) return 0;
    if (!llb_segwit_program_valid((uint8_t) witver, (uint8_t) witprog_len)) return 0;
    if ((witver == 0) != (enc == 1)) return 0;
    return (int) (fc & 0xffU) + 1;
}

// ============================================================================
// 3. BIP32 pubkey export safety check: Reference vs Lean
// ============================================================================
__attribute__((noinline)) bool ref_is_path_safe_for_pubkey_export(const uint32_t bip32_path[],
                                                                  size_t bip32_path_len) {
    if (bip32_path_len == 2 && bip32_path[0] == (4541509 ^ H) &&
        bip32_path[1] == (1112098098 ^ H)) {
        return true;
    }
    if (bip32_path_len < 3) return false;
    uint32_t purpose = bip32_path[0] & 0x7FFFFFFF;
    size_t hardened_der_len;
    switch (purpose) {
        case 44:
        case 49:
        case 84:
        case 86:
        case 87:
        case 45:
            hardened_der_len = 3;
            break;
        case 48:
            hardened_der_len = 4;
            break;
        default:
            return false;
    }
    if (bip32_path_len < hardened_der_len) return false;
    for (unsigned int i = 0; i < hardened_der_len; i++) {
        if (bip32_path[i] < 0x80000000) return false;
    }
    for (unsigned int i = hardened_der_len; i < bip32_path_len; i++) {
        if (bip32_path[i] >= 0x80000000) return false;
    }
    uint32_t coin_type = bip32_path[1] & 0x7FFFFFFF;
    if (coin_type != BIP44_COIN_TYPE) return false;
    uint32_t account = bip32_path[2] & 0x7FFFFFFF;
    if (account > MAX_BIP44_ACCOUNT_RECOMMENDED) return false;
    if (purpose == 48) {
        uint32_t script_type = bip32_path[3] & 0x7FFFFFFF;
        if (script_type != 1 && script_type != 2) return false;
    }
    return true;
}

__attribute__((noinline)) bool lean_is_path_safe_for_pubkey_export(const uint32_t bip32_path[],
                                                                   size_t bip32_path_len) {
    if (bip32_path_len > 255U) {
        return false;
    }
    return llb_bip32_check_export_path(bip32_path, (uint8_t) bip32_path_len, BIP44_COIN_TYPE) != 0U;
}

// ============================================================================
// 4. MuSig2 KeySort (BIP-327): Reference libc qsort vs Lean constant-stack sort
// ============================================================================
typedef uint8_t plain_pk_t[33];

static int cmp_plain_pk(const void *a, const void *b) {
    return memcmp(a, b, sizeof(plain_pk_t));
}

__attribute__((noinline)) void ref_musig_keysort(plain_pk_t keys[], size_t n_keys) {
    qsort(keys, n_keys, sizeof(plain_pk_t), cmp_plain_pk);
}

__attribute__((noinline)) void lean_musig_keysort(plain_pk_t keys[], size_t n_keys) {
    llb_sort_fixed_bytes((uint8_t *) keys, (uint32_t) n_keys, sizeof(plain_pk_t));
}

int main(void) {
    const int ROUNDS = 21;
    volatile uint64_t sink = 0;

    // --- 1) format_sats_amount ---
    const uint64_t amounts[8] = {
        0ULL,
        1ULL,
        546ULL,
        12345678ULL,
        100000000ULL,
        2100000000000000ULL,
        99999999999999999ULL,
        UINT64_MAX,
    };
    // Differential check first
    for (int i = 0; i < 8; i++) {
        char b1[32], b2[32];
        ref_format_sats_amount("BTC", amounts[i], b1);
        lean_format_sats_amount("BTC", amounts[i], b2);
        if (strcmp(b1, b2) != 0) {
            fprintf(stderr, "MISMATCH format_sats_amount: %s vs %s\n", b1, b2);
            return 1;
        }
    }

    uint64_t ref_sats_cyc = UINT64_MAX, lean_sats_cyc = UINT64_MAX;
    uint64_t ref_sats_ns = UINT64_MAX, lean_sats_ns = UINT64_MAX;
    const int SATS_ITERS = 25000;
    for (int r = 0; r < ROUNDS; r++) {
        char buf[32];
        uint64_t n0 = mono_ns();
        uint64_t c0 = rdtsc_start();
        for (int it = 0; it < SATS_ITERS; it++) {
            for (int k = 0; k < 8; k++) {
                ref_format_sats_amount("BTC", amounts[k] ^ (uint64_t) (it & 7), buf);
                sink += (uint8_t) buf[0];
            }
        }
        uint64_t c1 = rdtsc_end();
        uint64_t n1 = mono_ns();
        if (c1 - c0 < ref_sats_cyc) ref_sats_cyc = c1 - c0;
        if (n1 - n0 < ref_sats_ns) ref_sats_ns = n1 - n0;

        n0 = mono_ns();
        c0 = rdtsc_start();
        for (int it = 0; it < SATS_ITERS; it++) {
            for (int k = 0; k < 8; k++) {
                lean_format_sats_amount("BTC", amounts[k] ^ (uint64_t) (it & 7), buf);
                sink += (uint8_t) buf[0];
            }
        }
        c1 = rdtsc_end();
        n1 = mono_ns();
        if (c1 - c0 < lean_sats_cyc) lean_sats_cyc = c1 - c0;
        if (n1 - n0 < lean_sats_ns) lean_sats_ns = n1 - n0;
    }

    // --- 2) merkle_get_ith_direction (full 256-leaf tree proof traversal) ---
    for (size_t sz = 2; sz <= 260; sz += 17) {
        for (size_t idx = 0; idx < sz; idx += 5) {
            for (size_t d = 0; d < 10; d++) {
                int r1 = ref_merkle_get_ith_direction(sz, idx, d);
                int r2 = lean_merkle_get_ith_direction(sz, idx, d);
                if (r1 != r2) {
                    fprintf(stderr, "MISMATCH merkle(%zu,%zu,%zu): %d vs %d\n", sz, idx, d, r1, r2);
                    return 1;
                }
            }
        }
    }

    uint64_t ref_mrk_cyc = UINT64_MAX, lean_mrk_cyc = UINT64_MAX;
    uint64_t ref_mrk_ns = UINT64_MAX, lean_mrk_ns = UINT64_MAX;
    const int MRK_ITERS = 200;
    volatile size_t dyn_sz = 256;
    for (int r = 0; r < ROUNDS; r++) {
        size_t sz = dyn_sz;
        uint64_t acc = 0;
        uint64_t n0 = mono_ns();
        uint64_t c0 = rdtsc_start();
        for (int it = 0; it < MRK_ITERS; it++) {
            for (size_t idx = 0; idx < sz; idx++) {
                for (size_t step = 0; step < 8; step++) {
                    acc += (uint64_t) (ref_merkle_get_ith_direction(sz, idx, step) + 2);
                }
            }
        }
        uint64_t c1 = rdtsc_end();
        uint64_t n1 = mono_ns();
        sink += acc;
        if (c1 - c0 < ref_mrk_cyc) ref_mrk_cyc = c1 - c0;
        if (n1 - n0 < ref_mrk_ns) ref_mrk_ns = n1 - n0;

        acc = 0;
        n0 = mono_ns();
        c0 = rdtsc_start();
        for (int it = 0; it < MRK_ITERS; it++) {
            for (size_t idx = 0; idx < sz; idx++) {
                for (size_t step = 0; step < 8; step++) {
                    acc += (uint64_t) (lean_merkle_get_ith_direction(sz, idx, step) + 2);
                }
            }
        }
        c1 = rdtsc_end();
        n1 = mono_ns();
        sink += acc;
        if (c1 - c0 < lean_mrk_cyc) lean_mrk_cyc = c1 - c0;
        if (n1 - n0 < lean_mrk_ns) lean_mrk_ns = n1 - n0;
    }

    // --- 3) BIP32 pubkey export safety check ---
    const uint32_t paths[8][6] = {
        {44U | H, 0U | H, 0U | H, 0, 0, 0},
        {84U | H, 0U | H, 5U | H, 0, 12, 0},
        {86U | H, 0U | H, 99U | H, 1, 7, 0},
        {48U | H, 0U | H, 0U | H, 2U | H, 0, 3},
        {4541509U | H, 1112098098U | H, 0, 0, 0, 0},
        {84U | H, 1U | H, 0U | H, 0, 0, 0},
        {48U | H, 0U | H, 0U | H, 3U | H, 0, 0},
        {44U | H, 0U | H, 200U | H, 0, 0, 0},
    };
    const size_t path_lens[8] = {3, 5, 5, 6, 2, 3, 4, 3};
    for (int i = 0; i < 8; i++) {
        bool b1 = ref_is_path_safe_for_pubkey_export(paths[i], path_lens[i]);
        bool b2 = lean_is_path_safe_for_pubkey_export(paths[i], path_lens[i]);
        if (b1 != b2) {
            fprintf(stderr, "MISMATCH bip32(%d): %d vs %d\n", i, b1, b2);
            return 1;
        }
    }

    uint64_t ref_bip_cyc = UINT64_MAX, lean_bip_cyc = UINT64_MAX;
    uint64_t ref_bip_ns = UINT64_MAX, lean_bip_ns = UINT64_MAX;
    const int BIP_ITERS = 100000;
    volatile int dyn_mask = 7;
    for (int r = 0; r < ROUNDS; r++) {
        int mask = dyn_mask;
        uint64_t acc = 0;
        uint64_t n0 = mono_ns();
        uint64_t c0 = rdtsc_start();
        for (int it = 0; it < BIP_ITERS; it++) {
            for (int k = 0; k < 8; k++) {
                int idx = (k ^ it) & mask;
                acc += ref_is_path_safe_for_pubkey_export(paths[idx], path_lens[idx]);
            }
        }
        uint64_t c1 = rdtsc_end();
        uint64_t n1 = mono_ns();
        sink += acc;
        if (c1 - c0 < ref_bip_cyc) ref_bip_cyc = c1 - c0;
        if (n1 - n0 < ref_bip_ns) ref_bip_ns = n1 - n0;

        acc = 0;
        n0 = mono_ns();
        c0 = rdtsc_start();
        for (int it = 0; it < BIP_ITERS; it++) {
            for (int k = 0; k < 8; k++) {
                int idx = (k ^ it) & mask;
                acc += lean_is_path_safe_for_pubkey_export(paths[idx], path_lens[idx]);
            }
        }
        c1 = rdtsc_end();
        n1 = mono_ns();
        sink += acc;
        if (c1 - c0 < lean_bip_cyc) lean_bip_cyc = c1 - c0;
        if (n1 - n0 < lean_bip_ns) lean_bip_ns = n1 - n0;
    }

    // --- 4) MuSig2 KeySort (5 compressed pubkeys) ---
    const plain_pk_t init_pks[5] = {
        {0x03, 0xf1, 0x10},
        {0x02, 0x99, 0xaa},
        {0x03, 0x12, 0x34},
        {0x02, 0x01, 0xff},
        {0x02, 0x99, 0x05},
    };
    {
        plain_pk_t a[5], b[5];
        memcpy(a, init_pks, sizeof(init_pks));
        memcpy(b, init_pks, sizeof(init_pks));
        ref_musig_keysort(a, 5);
        lean_musig_keysort(b, 5);
        if (memcmp(a, b, sizeof(a)) != 0) {
            fprintf(stderr, "MISMATCH musig_keysort\n");
            return 1;
        }
    }

    uint64_t ref_ms_cyc = UINT64_MAX, lean_ms_cyc = UINT64_MAX;
    uint64_t ref_ms_ns = UINT64_MAX, lean_ms_ns = UINT64_MAX;
    const int MS_ITERS = 200000;
    for (int r = 0; r < ROUNDS; r++) {
        plain_pk_t work[5];
        uint64_t n0 = mono_ns();
        uint64_t c0 = rdtsc_start();
        for (int it = 0; it < MS_ITERS; it++) {
            memcpy(work, init_pks, sizeof(init_pks));
            work[0][2] ^= (uint8_t) it;
            ref_musig_keysort(work, 5);
            sink += work[0][1];
        }
        uint64_t c1 = rdtsc_end();
        uint64_t n1 = mono_ns();
        if (c1 - c0 < ref_ms_cyc) ref_ms_cyc = c1 - c0;
        if (n1 - n0 < ref_ms_ns) ref_ms_ns = n1 - n0;

        n0 = mono_ns();
        c0 = rdtsc_start();
        for (int it = 0; it < MS_ITERS; it++) {
            memcpy(work, init_pks, sizeof(init_pks));
            work[0][2] ^= (uint8_t) it;
            lean_musig_keysort(work, 5);
            sink += work[0][1];
        }
        c1 = rdtsc_end();
        n1 = mono_ns();
        if (c1 - c0 < lean_ms_cyc) lean_ms_cyc = c1 - c0;
        if (n1 - n0 < lean_ms_ns) lean_ms_ns = n1 - n0;
    }

    // --- 5) Bech32 + SegWit witness program validation ---
    for (int v = -1; v <= 17; v++) {
        for (size_t wl = 0; wl <= 42; wl++) {
            for (int enc = 0; enc <= 3; enc++) {
                int r1 = ref_segwit_program_check(v, wl, enc);
                int r2 = lean_segwit_program_check(v, wl, enc);
                if (r1 != r2) {
                    fprintf(stderr, "MISMATCH segwit(%d,%zu,%d): %d vs %d\n", v, wl, enc, r1, r2);
                    return 1;
                }
            }
        }
    }

    uint64_t ref_sw_cyc = UINT64_MAX, lean_sw_cyc = UINT64_MAX;
    uint64_t ref_sw_ns = UINT64_MAX, lean_sw_ns = UINT64_MAX;
    const int SW_ITERS = 100000;
    const int sw_vers[8] = {0, 0, 1, 16, 0, 2, -1, 17};
    const size_t sw_lens[8] = {20, 32, 32, 40, 24, 2, 20, 32};
    const int sw_encs[8] = {1, 1, 2, 2, 1, 2, 1, 2};
    for (int r = 0; r < ROUNDS; r++) {
        int mask = dyn_mask;
        uint64_t acc = 0;
        uint64_t n0 = mono_ns();
        uint64_t c0 = rdtsc_start();
        for (int it = 0; it < SW_ITERS; it++) {
            for (int k = 0; k < 8; k++) {
                int idx = (k ^ it) & mask;
                acc += (uint64_t) ref_segwit_program_check(sw_vers[idx], sw_lens[idx], sw_encs[idx]);
            }
        }
        uint64_t c1 = rdtsc_end();
        uint64_t n1 = mono_ns();
        sink += acc;
        if (c1 - c0 < ref_sw_cyc) ref_sw_cyc = c1 - c0;
        if (n1 - n0 < ref_sw_ns) ref_sw_ns = n1 - n0;

        acc = 0;
        n0 = mono_ns();
        c0 = rdtsc_start();
        for (int it = 0; it < SW_ITERS; it++) {
            for (int k = 0; k < 8; k++) {
                int idx = (k ^ it) & mask;
                acc += (uint64_t) lean_segwit_program_check(sw_vers[idx], sw_lens[idx], sw_encs[idx]);
            }
        }
        c1 = rdtsc_end();
        n1 = mono_ns();
        sink += acc;
        if (c1 - c0 < lean_sw_cyc) lean_sw_cyc = c1 - c0;
        if (n1 - n0 < lean_sw_ns) lean_sw_ns = n1 - n0;
    }

    uint64_t total_ref_cyc = ref_sats_cyc + ref_mrk_cyc + ref_bip_cyc + ref_ms_cyc + ref_sw_cyc;
    uint64_t total_lean_cyc = lean_sats_cyc + lean_mrk_cyc + lean_bip_cyc + lean_ms_cyc + lean_sw_cyc;

    printf("{\n");
    printf("  \"sink\": %" PRIu64 ",\n", (uint64_t) sink);
    printf("  \"format_sats_amount\": {\"ops\": %d, \"ref_cycles\": %" PRIu64 ", \"lean_cycles\": %" PRIu64 ", \"ref_ns\": %" PRIu64 ", \"lean_ns\": %" PRIu64 ", \"speedup_cycles\": %.3f},\n",
           SATS_ITERS * 8, ref_sats_cyc, lean_sats_cyc, ref_sats_ns, lean_sats_ns, (double) ref_sats_cyc / (double) lean_sats_cyc);
    printf("  \"merkle_get_ith_direction_256\": {\"ops\": %d, \"ref_cycles\": %" PRIu64 ", \"lean_cycles\": %" PRIu64 ", \"ref_ns\": %" PRIu64 ", \"lean_ns\": %" PRIu64 ", \"speedup_cycles\": %.3f},\n",
           MRK_ITERS * 256 * 8, ref_mrk_cyc, lean_mrk_cyc, ref_mrk_ns, lean_mrk_ns, (double) ref_mrk_cyc / (double) lean_mrk_cyc);
    printf("  \"bip32_pubkey_export_check\": {\"ops\": %d, \"ref_cycles\": %" PRIu64 ", \"lean_cycles\": %" PRIu64 ", \"ref_ns\": %" PRIu64 ", \"lean_ns\": %" PRIu64 ", \"speedup_cycles\": %.3f},\n",
           BIP_ITERS * 8, ref_bip_cyc, lean_bip_cyc, ref_bip_ns, lean_bip_ns, (double) ref_bip_cyc / (double) lean_bip_cyc);
    printf("  \"musig2_keysort_5pks\": {\"ops\": %d, \"ref_cycles\": %" PRIu64 ", \"lean_cycles\": %" PRIu64 ", \"ref_ns\": %" PRIu64 ", \"lean_ns\": %" PRIu64 ", \"speedup_cycles\": %.3f},\n",
           MS_ITERS, ref_ms_cyc, lean_ms_cyc, ref_ms_ns, lean_ms_ns, (double) ref_ms_cyc / (double) lean_ms_cyc);
    printf("  \"segwit_program_check\": {\"ops\": %d, \"ref_cycles\": %" PRIu64 ", \"lean_cycles\": %" PRIu64 ", \"ref_ns\": %" PRIu64 ", \"lean_ns\": %" PRIu64 ", \"speedup_cycles\": %.3f},\n",
           SW_ITERS * 8, ref_sw_cyc, lean_sw_cyc, ref_sw_ns, lean_sw_ns, (double) ref_sw_cyc / (double) lean_sw_cyc);
    printf("  \"aggregate_hotspot_suite\": {\"ref_cycles\": %" PRIu64 ", \"lean_cycles\": %" PRIu64 ", \"speedup_cycles\": %.3f}\n",
           total_ref_cyc, total_lean_cyc, (double) total_ref_cyc / (double) total_lean_cyc);
    printf("}\n");
    return 0;
}

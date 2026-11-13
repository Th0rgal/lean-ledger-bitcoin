#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern uint32_t llb_format_sats_ascii(uint64_t, const uint8_t *, uint32_t,
                                      uint8_t, uint8_t *, uint32_t);

static uint64_t cases;

static void check(uint64_t amount, uint8_t pad, uint32_t ticker_len) {
    uint8_t ticker[256], expected[512], storage[544], before[544];
    for (size_t i = 0; i < sizeof(ticker); ++i) ticker[i] = (uint8_t)i;
    memset(expected, 0, sizeof(expected));
    int n = snprintf((char *)expected, sizeof(expected), "%" PRIu64,
                     amount / UINT64_C(100000000));
    if (n < 0 || (size_t)n >= sizeof(expected)) abort();
    uint32_t total = (uint32_t)n;
    uint32_t frac = (uint32_t)(amount % UINT64_C(100000000));
    if (pad || frac) {
        char digits[9];
        int written = snprintf(digits, sizeof(digits), "%08" PRIu32, frac);
        if (written != 8) abort();
        size_t len = 8;
        if (!pad) while (len && digits[len - 1] == '0') --len;
        expected[total++] = '.';
        memcpy(expected + total, digits, len);
        total += (uint32_t)len;
    }
    if (ticker_len && ticker_len <= 256) {
        expected[total++] = ' ';
        memcpy(expected + total, ticker, ticker_len);
        total += ticker_len;
    }
    expected[total] = 0;
    uint32_t caps[] = {0, 1, total - 1, total, total + 1, total + 2, UINT32_MAX};
    for (size_t c = 0; c < sizeof(caps) / sizeof(caps[0]); ++c) {
        memset(storage, 0xa5, sizeof(storage));
        memcpy(before, storage, sizeof(storage));
        const uint8_t *input = ticker_len == 0 || ticker_len > 256 ? NULL : ticker;
        uint32_t got = llb_format_sats_ascii(amount, input, ticker_len, pad,
                                            storage + 16, caps[c]);
        int success = ticker_len <= 256 && caps[c] > total;
        if (success) memcpy(before + 16, expected, total + 1);
        if (got != (success ? total : 0) || memcmp(storage, before, sizeof(storage))) {
            fprintf(stderr, "amount=%" PRIu64 " pad=%u ticker=%" PRIu32
                    " cap=%" PRIu32 " got=%" PRIu32 " expected=%" PRIu32 "\n",
                    amount, (unsigned)pad, ticker_len, caps[c], got, success ? total : 0);
            exit(1);
        }
        ++cases;
    }
}

int main(void) {
    uint64_t amounts[] = {0, 1, 9, 10, 99, 100, 99999999, 100000000,
        100000001, 123450000, 9999999999999999ULL, 10000000000000000ULL,
        10000000000000001ULL, 2100000000000000ULL, UINT64_MAX};
    uint32_t tickers[] = {0, 1, 3, 255, 256, 257, UINT32_MAX};
    for (size_t a = 0; a < sizeof(amounts) / sizeof(amounts[0]); ++a)
        for (unsigned p = 0; p < 256; ++p)
            for (size_t t = 0; t < sizeof(tickers) / sizeof(tickers[0]); ++t)
                check(amounts[a], (uint8_t)p, tickers[t]);
    uint64_t state = UINT64_C(0xe42fdc4fce5640b8);
    for (unsigned i = 0; i < 1024; ++i) {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        for (size_t t = 0; t < sizeof(tickers) / sizeof(tickers[0]); ++t) {
            check(state, 0, tickers[t]);
            check(state, 255, tickers[t]);
        }
    }
    printf("%" PRIu64 " formatter oracle/canary cases passed\n", cases);
    return 0;
}

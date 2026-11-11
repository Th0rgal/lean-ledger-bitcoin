/*
 * llb_bolos_shim.h — Thin BOLOS (Nano X / Nano S+ / Stax / Flex / Apex P) C99
 * hardware-syscall shim for lean-ledger-bitcoin.
 *
 * The shim wraps the BOLOS Trusted Computing Base (TCB) boundary — the
 * `os_derive_bip32_*` seed-derivation syscalls, the `cx_hash_*` / `cx_ecfp_*` /
 * `cx_rng_*` cryptochip calls, the APDU `io_exchange` transport and the
 * `nbgl_*` / `ux_*` UI callbacks — behind a plain C99 function-pointer table
 * (`llb_bolos_tcb_t`) that can be consumed next to the freestanding C99 header
 * emitted by turbo-lean (`liblean_ledger_bitcoin.h`).
 *
 * The shim itself is freestanding C99: it only uses <stdint.h>, <stddef.h>
 * and <stdbool.h>, so it builds for the host unit tests, for
 * `clang --target=thumbv6m-none-eabi` / `thumbv8m.main-none-eabi` and for
 * `arm-none-eabi-gcc` BOLOS firmware builds.
 *
 * On-device integrators implement `llb_bolos_tcb_t` by forwarding to the
 * Ledger SDK (ox_ec.h / os_seed.h / io.h / nbgl_usecase.h) and install it with
 * `llb_bolos_tcb_set()`. Every `llb_bolos_*` wrapper fails closed
 * (LLB_BOLOS_ERR_TCB) while no TCB is installed.
 */
#ifndef LLB_BOLOS_SHIM_H
#define LLB_BOLOS_SHIM_H

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/*
 * The turbo-lean emitted freestanding kernel header. Pass
 * `-I<ffi/bolos/build/<target>>` (and optionally override with
 * `-DLLB_FREESTANDING_HEADER='"..."'` when the header lives elsewhere).
 */
#ifndef LLB_FREESTANDING_HEADER
#define LLB_FREESTANDING_HEADER "liblean_ledger_bitcoin.h"
#endif
#include LLB_FREESTANDING_HEADER

#ifdef __cplusplus
extern "C" {
#endif

/* ------------------------------------------------------------------ */
/* Packed version contract (must match BitcoinLedger/FreestandingKernels.lean) */
/* ------------------------------------------------------------------ */

/* (major << 16) | (minor << 8) | patch — major=2, minor=4, patch=1 */
#define LLB_VERSION_PACKED_EXPECTED UINT32_C(0x00020401)
#define LLB_VERSION_MAJOR UINT32_C(2)
#define LLB_VERSION_MINOR UINT32_C(4)
#define LLB_VERSION_PATCH UINT32_C(1)

/* ------------------------------------------------------------------ */
/* BOLOS SDK constants mirrored (ox_ec.h, os_seed.h, os_io_legacy.h)   */
/* ------------------------------------------------------------------ */

typedef uint32_t llb_cx_err_t; /* BOLOS cx_err_t is uint32_t */
#define LLB_CX_OK UINT32_C(0x00000000)
#define LLB_CX_INTERNAL_ERROR UINT32_C(0xFFFFFF97)

typedef uint32_t llb_cx_curve_t;
#define LLB_CX_CURVE_SECP256K1 UINT32_C(0x21) /* == CX_CURVE_256K1 */

/* BIP32/SLIP21 seed derivation modes (os_seed.h). */
#define LLB_HDW_NORMAL UINT32_C(0)
#define LLB_HDW_SLIP21 UINT32_C(2)

/* APDU io_exchange channels and flags (os_io_legacy.h). */
#define LLB_CHANNEL_APDU 0x00
#define LLB_IO_ASYNCH_REPLY 0x10
#define LLB_IO_RETURN_AFTER_TX 0x20

/* Sizes (bytes) of the 256-bit ECFP key material (ox_ec.h). */
#define LLB_ECFP_PRIVATE_KEY_SIZE 32u
#define LLB_ECFP_PUBLIC_KEY_SIZE 65u
#define LLB_BIP32_RAW_PRIVKEY_SIZE 64u /* os_derive_bip32_* raw_privkey[static 64] */
#define LLB_BIP32_CHAIN_CODE_SIZE 32u
#define LLB_SHA256_SIZE 32u

/* BOLOS cx_ecfp_256_public_key_s: { cx_curve_t curve; size_t W_len;
 * uint8_t W[65]; } and cx_ecfp_256_private_key_s:
 * { cx_curve_t curve; size_t d_len; uint8_t d[32]; }. */
typedef struct llb_cx_ecfp_public_key {
  llb_cx_curve_t curve;
  size_t W_len;
  uint8_t W[LLB_ECFP_PUBLIC_KEY_SIZE];
} llb_cx_ecfp_public_key_t;

typedef struct llb_cx_ecfp_private_key {
  llb_cx_curve_t curve;
  size_t d_len;
  uint8_t d[LLB_ECFP_PRIVATE_KEY_SIZE];
} llb_cx_ecfp_private_key_t;

/* ------------------------------------------------------------------ */
/* UI callbacks                                                        */
/* ------------------------------------------------------------------ */

/*
 * Target-agnostic UI choice callback covering both the Nano `ux_*` flow
 * validation callbacks (`UX_CALLBACK_VALIDATE?`) and the large-screen
 * `nbgl_choiceCallback_t` (Stax / Flex / Apex P: `void (*)(bool confirm)`).
 * `user_state` is passed through from the review request, untouched.
 */
typedef void (*llb_bolos_ui_choice_cb_t)(bool accepted, void *user_state);

/* ------------------------------------------------------------------ */
/* The BOLOS TCB function-pointer table                                */
/* ------------------------------------------------------------------ */

/*
 * One clean seam over the whole BOLOS hardware/OS surface used by the
 * lean-ledger-bitcoin kernels. Field order matches the Ledger SDK function
 * signatures documented inline; all pointers are non-NULL when installed
 * (llb_bolos_tcb_set rejects a partially filled table).
 */
typedef struct llb_bolos_tcb {
  /* os_derive_bip32_with_seed_no_throw(mode, curve, path, path_len,
   *     raw_privkey[64], chain_code, seed, seed_len) -> cx_err_t */
  llb_cx_err_t (*derive_bip32_with_seed)(uint32_t derivation_mode,
                                         llb_cx_curve_t curve,
                                         const uint32_t *path,
                                         uint32_t path_len,
                                         uint8_t raw_privkey[LLB_BIP32_RAW_PRIVKEY_SIZE],
                                         uint8_t *chain_code,
                                         const uint8_t *seed,
                                         uint32_t seed_len);

  /* cx_hash_sha256(in, len, out, out_len) -> out_len */
  size_t (*hash_sha256)(const uint8_t *in, size_t len, uint8_t *out, size_t out_len);

  /* cx_ecfp_generate_pair_no_throw(curve, pubkey, privkey, keepprivate) */
  llb_cx_err_t (*ecfp_generate_pair)(llb_cx_curve_t curve,
                                     llb_cx_ecfp_public_key_t *pubkey,
                                     llb_cx_ecfp_private_key_t *privkey,
                                     bool keep_private);

  /* cx_ecfp_add_point_no_throw(curve, R, P, Q) */
  llb_cx_err_t (*ecfp_add_point)(llb_cx_curve_t curve, uint8_t *r,
                                 const uint8_t *p, const uint8_t *q);

  /* cx_ecfp_scalar_mult_no_throw(curve, P, k, k_len) */
  llb_cx_err_t (*ecfp_scalar_mult)(llb_cx_curve_t curve, uint8_t *p,
                                   const uint8_t *k, size_t k_len);

  /* cx_rng_no_throw(buffer, len) — fills `len` bytes of TRNG output. */
  void (*rng)(uint8_t *buffer, size_t len);

  /* io_exchange(channel_and_flags, tx_len) -> rx_len */
  uint16_t (*io_exchange)(uint8_t channel_and_flags, uint16_t tx_len);

  /*
   * UI review entry point, unifying:
   *   - Nano (X / S+): `ux_flow_init`-driven paginated review flows
   *     (ux_flow_step / UX_CALLBACK macros), and
   *   - Stax / Flex / Apex P: `nbgl_useCaseReview` /
   *     `nbgl_useCaseReviewStreaming*` with a `nbgl_choiceCallback_t`.
   * `on_choice` is invoked exactly once when the user accepts or rejects;
   * `user_state` is passed through.
   */
  void (*ui_review)(const char *title, const char *body,
                    llb_bolos_ui_choice_cb_t on_choice, void *user_state);
} llb_bolos_tcb_t;

/* ------------------------------------------------------------------ */
/* Shim error codes                                                    */
/* ------------------------------------------------------------------ */

#define LLB_BOLOS_OK 0
#define LLB_BOLOS_ERR_TCB (-1)   /* no (or partial) TCB installed */
#define LLB_BOLOS_ERR_PARAM (-2) /* NULL/oversized argument */

/* ------------------------------------------------------------------ */
/* TCB installation / query                                           */
/* ------------------------------------------------------------------ */

/*
 * Install (or, with NULL, uninstall) the BOLOS TCB vtable. The table is
 * copied into shim-owned storage, so it may live on the stack of the caller.
 * Returns LLB_BOLOS_ERR_TCB if a NULL field is present in a non-NULL table.
 */
int llb_bolos_tcb_set(const llb_bolos_tcb_t *tcb);

/* Currently installed TCB, or NULL when none is installed (fail-closed). */
const llb_bolos_tcb_t *llb_bolos_tcb_get(void);

/* ------------------------------------------------------------------ */
/* Thin wrappers (all fail closed while no TCB is installed)           */
/* ------------------------------------------------------------------ */

/* os_derive_bip32_no_throw(curve, path, path_len, raw_privkey, chain_code). */
llb_cx_err_t llb_bolos_derive_bip32(llb_cx_curve_t curve, const uint32_t *path,
                                    uint32_t path_len,
                                    uint8_t raw_privkey[LLB_BIP32_RAW_PRIVKEY_SIZE],
                                    uint8_t *chain_code);

/* os_derive_bip32_with_seed_no_throw(...) — SLIP-21 style derivations. */
llb_cx_err_t llb_bolos_derive_bip32_with_seed(uint32_t derivation_mode,
                                              llb_cx_curve_t curve,
                                              const uint32_t *path,
                                              uint32_t path_len,
                                              uint8_t raw_privkey[LLB_BIP32_RAW_PRIVKEY_SIZE],
                                              uint8_t *chain_code,
                                              const uint8_t *seed, uint32_t seed_len);

/* cx_hash_sha256: writes exactly 32 bytes to `out` on success. */
int llb_bolos_sha256(const uint8_t *in, size_t len, uint8_t out[LLB_SHA256_SIZE]);

/* cx_ecfp_generate_pair_no_throw. */
llb_cx_err_t llb_bolos_ecfp_generate_pair(llb_cx_curve_t curve,
                                          llb_cx_ecfp_public_key_t *pubkey,
                                          llb_cx_ecfp_private_key_t *privkey,
                                          bool keep_private);

/* cx_ecfp_add_point_no_throw — 65-byte uncompressed SEC1 points. */
llb_cx_err_t llb_bolos_ecfp_add_point(llb_cx_curve_t curve, uint8_t *r,
                                      const uint8_t *p, const uint8_t *q);

/* cx_ecfp_scalar_mult_no_throw — k_len must be <= 32. */
llb_cx_err_t llb_bolos_ecfp_scalar_mult(llb_cx_curve_t curve, uint8_t *p,
                                        const uint8_t *k, size_t k_len);

/* cx_rng_no_throw(buffer, len). */
int llb_bolos_rng(uint8_t *buffer, size_t len);

/* io_exchange(channel_and_flags, tx_len): `rx_len` receives the APDU rx
 * length. Returns LLB_BOLOS_ERR_TCB if no TCB is installed. */
int llb_bolos_io_exchange(uint8_t channel_and_flags, uint16_t tx_len,
                          uint16_t *rx_len);

/* UI review request; see llb_bolos_tcb_t.ui_review. */
int llb_bolos_ui_review(const char *title, const char *body,
                        llb_bolos_ui_choice_cb_t on_choice, void *user_state);

/*
 * Kernel version gate: verifies that the linked turbo-lean-emitted
 * freestanding kernel archive matches the packed version this FFI shim was
 * written against ((2 << 16) | (4 << 8) | 1 == 0x00020401).
 * Returns LLB_BOLOS_OK on match, LLB_BOLOS_ERR_TCB-style negative otherwise.
 */
int llb_bolos_check_kernel_version(void);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* LLB_BOLOS_SHIM_H */

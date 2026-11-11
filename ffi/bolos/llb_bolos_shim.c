/*
 * llb_bolos_shim.c — implementation of the BOLOS TCB shim
 * (see llb_bolos_shim.h). Freestanding C99, no libc.
 */
#include "llb_bolos_shim.h"

static llb_bolos_tcb_t llb_bolos_tcb_storage;
static int llb_bolos_tcb_installed = 0;

int llb_bolos_tcb_set(const llb_bolos_tcb_t *tcb) {
  if (tcb == NULL) {
    llb_bolos_tcb_installed = 0;
    return LLB_BOLOS_OK;
  }
  /* Fail closed on a partially filled table: a NULL function pointer would
   * otherwise crash on dispatch on the device. */
  if (tcb->derive_bip32_with_seed == NULL || tcb->hash_sha256 == NULL ||
      tcb->ecfp_generate_pair == NULL || tcb->ecfp_add_point == NULL ||
      tcb->ecfp_scalar_mult == NULL || tcb->rng == NULL ||
      tcb->io_exchange == NULL || tcb->ui_review == NULL) {
    return LLB_BOLOS_ERR_TCB;
  }
  llb_bolos_tcb_storage = *tcb;
  llb_bolos_tcb_installed = 1;
  return LLB_BOLOS_OK;
}

const llb_bolos_tcb_t *llb_bolos_tcb_get(void) {
  if (!llb_bolos_tcb_installed) {
    return NULL;
  }
  return &llb_bolos_tcb_storage;
}

llb_cx_err_t llb_bolos_derive_bip32(llb_cx_curve_t curve, const uint32_t *path,
                                    uint32_t path_len,
                                    uint8_t raw_privkey[LLB_BIP32_RAW_PRIVKEY_SIZE],
                                    uint8_t *chain_code) {
  return llb_bolos_derive_bip32_with_seed(LLB_HDW_NORMAL, curve, path, path_len,
                                          raw_privkey, chain_code, NULL, 0);
}

llb_cx_err_t llb_bolos_derive_bip32_with_seed(uint32_t derivation_mode,
                                              llb_cx_curve_t curve,
                                              const uint32_t *path,
                                              uint32_t path_len,
                                              uint8_t raw_privkey[LLB_BIP32_RAW_PRIVKEY_SIZE],
                                              uint8_t *chain_code,
                                              const uint8_t *seed, uint32_t seed_len) {
  if (raw_privkey == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  if (path_len != 0 && path == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  return tcb->derive_bip32_with_seed(derivation_mode, curve, path, path_len,
                                     raw_privkey, chain_code, seed, seed_len);
}

int llb_bolos_sha256(const uint8_t *in, size_t len, uint8_t out[LLB_SHA256_SIZE]) {
  if (out == NULL) {
    return LLB_BOLOS_ERR_PARAM;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_BOLOS_ERR_TCB;
  }
  if (len != 0 && in == NULL) {
    return LLB_BOLOS_ERR_PARAM;
  }
  size_t written = tcb->hash_sha256(in, len, out, LLB_SHA256_SIZE);
  return (written == LLB_SHA256_SIZE) ? LLB_BOLOS_OK : LLB_BOLOS_ERR_TCB;
}

llb_cx_err_t llb_bolos_ecfp_generate_pair(llb_cx_curve_t curve,
                                          llb_cx_ecfp_public_key_t *pubkey,
                                          llb_cx_ecfp_private_key_t *privkey,
                                          bool keep_private) {
  if (pubkey == NULL || privkey == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  return tcb->ecfp_generate_pair(curve, pubkey, privkey, keep_private);
}

llb_cx_err_t llb_bolos_ecfp_add_point(llb_cx_curve_t curve, uint8_t *r,
                                      const uint8_t *p, const uint8_t *q) {
  if (r == NULL || p == NULL || q == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  return tcb->ecfp_add_point(curve, r, p, q);
}

llb_cx_err_t llb_bolos_ecfp_scalar_mult(llb_cx_curve_t curve, uint8_t *p,
                                        const uint8_t *k, size_t k_len) {
  if (p == NULL || k == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  if (k_len > 32) {
    return LLB_CX_INTERNAL_ERROR;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_CX_INTERNAL_ERROR;
  }
  return tcb->ecfp_scalar_mult(curve, p, k, k_len);
}

int llb_bolos_rng(uint8_t *buffer, size_t len) {
  if (buffer == NULL) {
    return LLB_BOLOS_ERR_PARAM;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_BOLOS_ERR_TCB;
  }
  tcb->rng(buffer, len);
  return LLB_BOLOS_OK;
}

int llb_bolos_io_exchange(uint8_t channel_and_flags, uint16_t tx_len,
                          uint16_t *rx_len) {
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_BOLOS_ERR_TCB;
  }
  uint16_t rx = tcb->io_exchange(channel_and_flags, tx_len);
  if (rx_len != NULL) {
    *rx_len = rx;
  }
  return LLB_BOLOS_OK;
}

int llb_bolos_ui_review(const char *title, const char *body,
                        llb_bolos_ui_choice_cb_t on_choice, void *user_state) {
  if (title == NULL || body == NULL || on_choice == NULL) {
    return LLB_BOLOS_ERR_PARAM;
  }
  const llb_bolos_tcb_t *tcb = llb_bolos_tcb_get();
  if (tcb == NULL) {
    return LLB_BOLOS_ERR_TCB;
  }
  tcb->ui_review(title, body, on_choice, user_state);
  return LLB_BOLOS_OK;
}

int llb_bolos_check_kernel_version(void) {
  /* Freestanding ABI call straight into the turbo-lean-emitted archive. */
  uint32_t packed = llb_version_packed();
  if (packed != LLB_VERSION_PACKED_EXPECTED) {
    return LLB_BOLOS_ERR_TCB;
  }
  return LLB_BOLOS_OK;
}

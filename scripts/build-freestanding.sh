#!/usr/bin/env bash
# build-freestanding.sh — Reproducible freestanding C99 emission for lean-ledger-bitcoin.
#
# Invokes the turbo-lean `lean-native emit-freestanding-c-lib` emitter on the
# freestanding kernel module (default: BitcoinLedger/FreestandingKernels.lean)
# for all three 32-bit ILP32 Ledger targets:
#
#   thumbv6m      (thumbv6m-none-eabi)        BOLOS — Nano X (Secure Element FW layout)
#   thumbv8m.main (thumbv8m.main-none-eabi)   BOLOS — Nano S+ / Stax / Flex / Apex P
#   riscv32imac   (riscv32imac-unknown-none-elf) Vanadium V-App (RISC-V RV32IMAC)
#
# plus a host (x86_64) freestanding emission used by the `ffi/bolos` and
# `ffi/vanadium` host-side unit tests (`make -C ffi/bolos test`,
# `cargo test --manifest-path ffi/vanadium/Cargo.toml`).
#
# For every target the script verifies, failing closed:
#   * .ll / .h / .o / .a / .su artifacts all exist;
#   * the freestanding C99 header only includes <stdint.h>/<stddef.h>/<stdbool.h>;
#   * the archive has 0 undefined symbols (`llvm-nm`) and 0 malloc/lean_alloc_*/lean_*
#     heap/runtime symbols (mirroring the emitter's own fail-closed audit);
#   * worst-case kernel stack frame budget: every .su frame is < LLB_STACK_BUDGET
#     bytes (default 1024), well within the 12 KB Nano X main stack.
#
# Environment overrides:
#   LEAN_NATIVE       path to the lean-native driver
#                     (default: hub cache turbo-lean/lean/.lake/build/bin/lean-native)
#   LLB_KERNEL        kernel .lean module (default: BitcoinLedger/FreestandingKernels.lean)
#   LLB_STACK_BUDGET  per-kernel-function worst-case frame budget in bytes (default: 1024)
#   CLANG / LLVM_NM   tool overrides

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

HUB="${LEDGER_HUB:-/var/lib/orb-node/work/caches/ledger-hub}"
LEAN_NATIVE="${LEAN_NATIVE:-${HUB}/turbo-lean/lean/.lake/build/bin/lean-native}"
LLB_KERNEL="${LLB_KERNEL:-BitcoinLedger/FreestandingKernels.lean}"
LLB_STACK_BUDGET="${LLB_STACK_BUDGET:-1024}"
CLANG="${CLANG:-clang}"
LLVM_NM="${LLVM_NM:-$(command -v llvm-nm || command -v nm)}"
LIB_NAME="liblean_ledger_bitcoin"

# Stack-usage budget for the 12 KB Nano X main stack: keep every single kernel
# frame strictly below 1 KiB so that even deep BOLOS call chains stay safe.
if ! [[ "${LLB_STACK_BUDGET}" =~ ^[0-9]+$ ]] || [ "${LLB_STACK_BUDGET}" -le 0 ]; then
  echo "build-freestanding.sh: invalid LLB_STACK_BUDGET='${LLB_STACK_BUDGET}'" >&2
  exit 2
fi

die() {
  echo "build-freestanding.sh: ERROR: $*" >&2
  exit 1
}

log() {
  printf '[build-freestanding] %s\n' "$*"
}

[ -x "${LEAN_NATIVE}" ] || die "lean-native driver not found/executable at '${LEAN_NATIVE}' (set LEAN_NATIVE)"
[ -f "${REPO_ROOT}/${LLB_KERNEL}" ] || die "kernel module '${REPO_ROOT}/${LLB_KERNEL}' not found (set LLB_KERNEL)"
command -v "${CLANG}" >/dev/null 2>&1 || die "clang not found at '${CLANG}' (set CLANG)"
command -v "${LLVM_NM}" >/dev/null 2>&1 || die "nm not found at '${LLVM_NM}' (set LLVM_NM)"

# target-tag|out-dir
TARGETS=(
  "thumbv6m|${REPO_ROOT}/ffi/bolos/build/thumbv6m"
  "thumbv8m.main|${REPO_ROOT}/ffi/bolos/build/thumbv8m.main"
  "riscv32imac|${REPO_ROOT}/ffi/vanadium/build/riscv32imac"
  # Host freestanding emission: links into the host-side C (ffi/bolos) and Rust
  # (ffi/vanadium) unit tests of the FFI shims.
  "x86_64|${REPO_ROOT}/ffi/bolos/build/host"
  "x86_64|${REPO_ROOT}/ffi/vanadium/build/host"
)

emit_target() {
  local tag="$1" out_dir="$2"
  mkdir -p "${out_dir}"
  local archive="${out_dir}/${LIB_NAME}.a"

  log "emitting ${tag} -> ${out_dir}"
  (cd "${REPO_ROOT}" && "${LEAN_NATIVE}" emit-freestanding-c-lib \
    --input "${LLB_KERNEL}" \
    --target "${tag}" \
    --clang-bin "${CLANG}" \
    -o "${archive}" \
    --json)
}

verify_target() {
  local tag="$1" out_dir="$2"
  local stem="${out_dir}/${LIB_NAME}"
  local artifact

  for artifact in "${stem}.ll" "${stem}.h" "${stem}.o" "${stem}.a" "${stem}.su"; do
    [ -s "${artifact}" ] || die "[${tag}] missing or empty artifact: ${artifact}"
  done
  log "[${tag}] artifacts ok: .ll .h .o .a .su"

  # 1) Freestanding C99 header discipline: only the three freestanding includes.
  local bad_include
  bad_include="$(grep -E '^[[:space:]]*#[[:space:]]*include' "${stem}.h" \
    | grep -v -E '<(stdint|stddef|stdbool)\.h>' || true)"
  if [ -n "${bad_include}" ]; then
    die "[${tag}] freestanding C99 header contains non-freestanding include(s): ${bad_include}"
  fi
  log "[${tag}] header ok: <stdint.h>/<stddef.h>/<stdbool.h> only"

  # 2) Symbol audit on the archive: 0 undefined, 0 heap/runtime symbols.
  local nm_out
  nm_out="$("${LLVM_NM}" "${stem}.a")"
  local undef
  undef="$(printf '%s\n' "${nm_out}" | awk '$1 == "U" || $2 == "U"' || true)"
  if [ -n "${undef}" ]; then
    die "[${tag}] archive has undefined symbols: ${undef}"
  fi
  local forbidden
  forbidden="$(printf '%s\n' "${nm_out}" \
    | grep -E 'malloc|free|lean_alloc_|lean_inc|lean_dec|lean_mark_mt|lean_native_ensure_exclusive|lean_native_box_u64' \
    || true)"
  if [ -n "${forbidden}" ]; then
    die "[${tag}] archive references forbidden heap/runtime symbols: ${forbidden}"
  fi
  log "[${tag}] symbols ok: undefined=0, malloc/lean_alloc_*=0"

  # 3) Stack-usage budget: every kernel function frame < LLB_STACK_BUDGET bytes.
  local worst frame fn
  worst=0
  while IFS=$'\t' read -r fn frame _type; do
    [ -n "${fn}" ] || continue
    if ! [[ "${frame}" =~ ^[0-9]+$ ]]; then
      die "[${tag}] unparseable .su line for '${fn}': frame='${frame}'"
    fi
    if [ "${frame}" -ge "${LLB_STACK_BUDGET}" ]; then
      die "[${tag}] stack frame budget exceeded for '${fn}': ${frame} >= ${LLB_STACK_BUDGET} bytes"
    fi
    if [ "${frame}" -gt "${worst}" ]; then
      worst="${frame}"
    fi
  done < "${stem}.su"
  log "[${tag}] stack budget ok: worst frame ${worst} bytes < ${LLB_STACK_BUDGET} (12 KB Nano X stack)"
}

main() {
  log "lean-native driver: ${LEAN_NATIVE}"
  log "kernel module:      ${LLB_KERNEL}"
  log "stack budget:       < ${LLB_STACK_BUDGET} bytes per kernel function"
  log ""

  local entry tag out_dir
  for entry in "${TARGETS[@]}"; do
    tag="${entry%%|*}"
    out_dir="${entry#*|}"
    emit_target "${tag}" "${out_dir}"
    verify_target "${tag}" "${out_dir}"
    log ""
  done

  log "SUCCESS: freestanding C99 bundles verified for thumbv6m, thumbv8m.main,"
  log "riscv32imac (+ host test emissions) with 0 undefined symbols, 0 heap/runtime"
  log "symbols and worst-case stack frames within the ${LLB_STACK_BUDGET}-byte budget."
}

main "$@"

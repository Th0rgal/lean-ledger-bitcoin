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
if [ -z "${LEAN_NATIVE:-}" ]; then
  if [ -x "${REPO_ROOT}/../turbo-lean/lean/.lake/build/bin/lean-native" ]; then
    LEAN_NATIVE="${REPO_ROOT}/../turbo-lean/lean/.lake/build/bin/lean-native"
  else
    LEAN_NATIVE="${HUB}/turbo-lean/lean/.lake/build/bin/lean-native"
  fi
fi
find_llvm_tool() {
  local name="$1"
  local cand
  if command -v "${name}" >/dev/null 2>&1; then
    command -v "${name}"
    return 0
  fi
  for cand in \
    "/usr/lib/llvm-21/bin/${name}" \
    "/usr/lib/llvm-20/bin/${name}" \
    "/usr/lib/llvm-19/bin/${name}" \
    "/usr/lib/llvm-18/bin/${name}" \
    "${HUB}/dev-tools-rootfs/usr/lib/llvm-21/bin/${name}"; do
    if [ -x "${cand}" ]; then
      printf '%s\n' "${cand}"
      return 0
    fi
  done
  return 1
}

LLB_KERNEL="${LLB_KERNEL:-BitcoinLedger/FreestandingKernels.lean}"
LLB_STACK_BUDGET="${LLB_STACK_BUDGET:-1024}"
CLANG="${CLANG:-$(find_llvm_tool clang || echo clang)}"
LLVM_NM="${LLVM_NM:-$(find_llvm_tool llvm-nm || command -v nm || echo llvm-nm)}"
LLVM_AR="${LLVM_AR:-$(find_llvm_tool llvm-ar || command -v ar || echo llvm-ar)}"
LLVM_OPT="${LLVM_OPT:-$(find_llvm_tool opt || echo opt)}"
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

[ -f "${REPO_ROOT}/${LLB_KERNEL}" ] || die "kernel module '${REPO_ROOT}/${LLB_KERNEL}' not found (set LLB_KERNEL)"
command -v "${CLANG}" >/dev/null 2>&1 || [ -x "${CLANG}" ] || die "clang not found at '${CLANG}' (set CLANG)"
command -v "${LLVM_NM}" >/dev/null 2>&1 || [ -x "${LLVM_NM}" ] || die "nm not found at '${LLVM_NM}' (set LLVM_NM)"
command -v "${LLVM_AR}" >/dev/null 2>&1 || [ -x "${LLVM_AR}" ] || die "ar not found at '${LLVM_AR}' (set LLVM_AR)"

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
  [ -x "${LEAN_NATIVE}" ] || die "lean-native not executable at '${LEAN_NATIVE}' (C fallback removed)"
  (cd "${REPO_ROOT}" && "${LEAN_NATIVE}" emit-freestanding-c-lib \
    --input "${LLB_KERNEL}" \
    --target "${tag}" \
    --clang-bin "${CLANG}" \
    -o "${archive}" \
    --json) || die "[${tag}] lean-native emit-freestanding-c-lib failed"
}

emit_bolos_lto_bundle() {
  local lto_dir="${REPO_ROOT}/ffi/bolos/build/lto"
  local opt_bin="${LLVM_OPT}"
  command -v "${opt_bin}" >/dev/null 2>&1 || [ -x "${opt_bin}" ] || die "LLVM opt binary not found at '${opt_bin}'"

  mkdir -p "${lto_dir}"
  cp "${REPO_ROOT}/ffi/bolos/build/thumbv8m.main/${LIB_NAME}.h" "${lto_dir}/${LIB_NAME}_ilp32.h"
  cp "${REPO_ROOT}/ffi/bolos/build/host/${LIB_NAME}.h" "${lto_dir}/${LIB_NAME}_lp64.h"
  cat > "${lto_dir}/${LIB_NAME}.h" <<'EOF'
#pragma once
#if defined(__LP64__) || defined(_LP64)
#include "liblean_ledger_bitcoin_lp64.h"
#else
#include "liblean_ledger_bitcoin_ilp32.h"
#endif
EOF

  local tag src_ll dst_ll
  for tag in thumbv6m thumbv8m.main host; do
    src_ll="${REPO_ROOT}/ffi/bolos/build/${tag}/${LIB_NAME}.ll"
    dst_ll="${lto_dir}/${LIB_NAME}_${tag}.ll"
    python3 - "${src_ll}" "${dst_ll}.pre.ll" "${tag}" <<'PY'
import re, sys

src, dst, tag = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(src).read()

INLINE_SCALARS = {
    "llb_bip32_bolos_depth_ok",
    "llb_bip32_is_hardened",
    "llb_bip32_unharden",
    "llb_valid_amount",
    "llb_checked_add_sats_ok",
    "llb_checked_add_sats_val",
    "llb_sighash_type_valid",
    "llb_taproot_sighash_valid",
    "llb_bech32_final_constant",
    "llb_segwit_program_valid",
    "llb_witness_opcode_to_version",
    "llb_wallet_name_char_ok",
    "llb_merkle_advance_state",
    "llb_miniscript_older_ok",
    "llb_miniscript_after_ok",
    "llb_miniscript_andor_branches_valid",
}

out = []
for line in text.splitlines():
    if line.startswith("!llvm.ident") or line.startswith("!0 = !{!\"lean-native"):
        continue
    m = re.match(r'^define\s+(?:(?:dso_local|internal|hidden)\s+)*(.*?)\s+@([^\(\s]+)\((.*)$', line)
    if m:
        ret_ty, fn, rest = m.groups()
        if fn.startswith("llb_"):
            extra = " alwaysinline" if (fn in INLINE_SCALARS or tag == "host") else ""
            opt_attr = "" if tag == "host" else " optsize"
            line = f"define hidden {ret_ty} @{fn}({rest}"
            if line.endswith("{"):
                line = line[:-1] + f"{opt_attr}{extra} {{"
        else:
            line = f"define internal {ret_ty} @{fn}({rest}"
    elif line.startswith("attributes #"):
        line = re.sub(r'\s*"(?:target-cpu|target-features|tune-cpu|frame-pointer|stack-protector-buffer-size)"="[^"]*"', '', line)
        line = line.replace(" minsize ", " ")
        if tag == "host":
            line = line.replace(" optsize ", " ")
    out.append(line)

open(dst, "w").write("\n".join(out) + "\n")
PY
    if [ "${tag}" = "host" ]; then
      "${opt_bin}" -S -passes='default<O2>' "${dst_ll}.pre.ll" -o "${dst_ll}"
    else
      "${opt_bin}" -S -passes='default<Oz>' "${dst_ll}.pre.ll" -o "${dst_ll}"
    fi
    python3 - "${dst_ll}" "${tag}" <<'PY2'
import re, sys
p, tag = sys.argv[1], sys.argv[2]
s = open(p).read()
def clean_attr(l: str) -> str:
    if l.startswith("attributes #"):
        l = re.sub(r'\s*"(?:target-cpu|target-features|tune-cpu|frame-pointer|stack-protector-buffer-size)"="[^"]*"', '', l)
    l = l.replace(" minsize ", " ")
    if tag == "host":
        l = l.replace(" optsize ", " ")
    return l
open(p, "w").write("\n".join(
    clean_attr(l)
    for l in s.splitlines()
    if not l.startswith("!llvm.ident") and not l.startswith("!0 = !{!\"lean-native")
) + "\n")
PY2
    rm -f "${dst_ll}.pre.ll"
    [ -s "${dst_ll}" ] || die "failed to emit BOLOS LTO IR: ${dst_ll}"
  done
  log "[bolos-lto] staged LTO bitcode IR + dual ILP32/LP64 headers -> ${lto_dir}"
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
    | grep -E 'malloc|free|memcpy|memmove|memset|memcmp|__aeabi_|__udiv|__umod|lean_alloc_|lean_inc|lean_dec|lean_mark_mt|lean_native_ensure_exclusive|lean_native_box_u64' \
    || true)"
  if [ -n "${forbidden}" ]; then
    die "[${tag}] archive references forbidden heap/runtime/libgcc symbols: ${forbidden}"
  fi
  local sym_count
  sym_count="$(printf '%s\n' "${nm_out}" | awk '$2 == "T" && $3 ~ /^llb_/ { print $3 }' | sort -u | wc -l | tr -d ' ')"
  if [ "${sym_count}" -lt 45 ]; then
    die "[${tag}] archive exports ${sym_count} llb_* symbols (expected >= 45)"
  fi
  log "[${tag}] symbols ok: exported=${sym_count}, undefined=0, forbidden=0"

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

  emit_bolos_lto_bundle

  log "SUCCESS: freestanding C99 bundles verified for thumbv6m, thumbv8m.main,"
  log "riscv32imac (+ host test emissions) with 0 undefined symbols, 0 heap/runtime"
  log "symbols and worst-case stack frames within the ${LLB_STACK_BUDGET}-byte budget."
}

main "$@"

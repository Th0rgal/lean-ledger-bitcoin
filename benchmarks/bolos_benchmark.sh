#!/usr/bin/env bash
# bolos_benchmark.sh — Reproducible end-to-end storage, RAM, stack, CPU cycle,
# ARM Thumb instruction-count, host PSBT suite, and live Speculos APDU latency
# benchmark comparing unmodified LedgerHQ/app-bitcoin (f010982d3050e02813cd7129bebd68cf2d1f2099)
# against our Lean-backed BOLOS Bitcoin app (`lean-ledger-bitcoin`).
#
# Usage:
#   ./benchmarks/bolos_benchmark.sh [--skip-rebuild]
#
# Outputs:
#   benchmarks/bolos_results.json
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
W4_ROOT="${W4_ROOT:-/var/lib/orb-node/work/w4-bolos}"
HUB="${HUB:-/var/lib/orb-node/work/caches/ledger-hub}"

if [ -f "${HUB}/env.sh" ]; then
  # shellcheck disable=SC1090
  source "${HUB}/env.sh"
fi
export PATH="${W4_ROOT}/bitcoin-core/bitcoin-32.1/bin:${HUB}/tool-shims:${HUB}/venv-bolos/bin:${HUB}/dev-tools-rootfs/usr/lib/llvm-21/bin:${HUB}/sysroot/usr/bin:${PATH}"
export LD_LIBRARY_PATH="${HUB}/llvm21-libs:${LD_LIBRARY_PATH:-}"
export PYTHONPATH="${W4_ROOT}/py-extra:${PYTHONPATH:-}"

REF_APP="${REF_APP:-${W4_ROOT}/app-bitcoin-ref}"
LEAN_APP="${LEAN_APP:-${W4_ROOT}/app-bitcoin-lean}"
REF_ART="${REF_ART:-${W4_ROOT}/ref-artifacts}"
LEAN_ART="${LEAN_ART:-${W4_ROOT}/lean-artifacts}"
OUT_JSON="${REPO_ROOT}/benchmarks/bolos_results.json"

NSP_SDK="${HUB}/dev-tools-rootfs/opt/nanosplus-secure-sdk"
NX_SDK="${HUB}/dev-tools-rootfs/opt/nanox-secure-sdk"

SKIP_REBUILD=0
HOTSPOTS_ONLY=0
for arg in "$@"; do
  case "${arg}" in
    --skip-rebuild) SKIP_REBUILD=1 ;;
    --hotspots-only) HOTSPOTS_ONLY=1; SKIP_REBUILD=1 ;;
  esac
done

CLANG_BIN=""
for c in clang-21 /usr/lib/llvm-18/bin/clang clang; do
  if command -v "${c}" >/dev/null 2>&1; then
    CLANG_BIN="$(command -v "${c}")"
    break
  elif [ -x "${c}" ]; then
    CLANG_BIN="${c}"
    break
  fi
done
if [ -z "${CLANG_BIN}" ]; then
  echo "[bolos-bench] ERROR: clang not found" >&2
  exit 1
fi

build_app_variant() {
  local app_dir="$1" out_dir="$2" sdk="$3" coin="$4" extra="$5"
  mkdir -p "${out_dir}"
  rm -rf "${app_dir}/build" "${app_dir}/bin" "${app_dir}/debug"
  BOLOS_SDK="${sdk}" make -C "${app_dir}" -j"$(nproc)" COIN="${coin}" DEBUG=0 ${extra} >/dev/null 2>&1
  cp "${app_dir}/bin/app.elf" "${out_dir}/app.elf"
  cp "${app_dir}/bin/app.apdu" "${out_dir}/app.apdu"
  cp "${app_dir}/debug/app.map" "${out_dir}/app.map"
  cp "${app_dir}/debug/app.asm" "${out_dir}/app.asm"
}

if [ "${HOTSPOTS_ONLY}" -eq 1 ]; then
  :
elif [ "${SKIP_REBUILD}" -eq 0 ]; then
  echo "[bolos-bench] 1/5 Emitting freestanding Lean LTO bundle..."
  "${REPO_ROOT}/scripts/build-freestanding.sh" >/dev/null
  cp "${REPO_ROOT}/ffi/bolos/build/lto/"* "${LEAN_APP}/src/lean_kernels/"

  echo "[bolos-bench] 2/5 Building unmodified Reference & Lean BOLOS firmware variants..."
  build_app_variant "${REF_APP}"  "${REF_ART}/nanosp-mainnet"            "${NSP_SDK}" "bitcoin"         ""
  build_app_variant "${REF_APP}"  "${REF_ART}/nanox-mainnet"             "${NX_SDK}"  "bitcoin"         ""
  build_app_variant "${REF_APP}"  "${REF_ART}/nanosp-testnet"            "${NSP_SDK}" "bitcoin_testnet" ""
  build_app_variant "${REF_APP}"  "${REF_ART}/nanox-testnet"             "${NX_SDK}"  "bitcoin_testnet" ""
  build_app_variant "${REF_APP}"  "${REF_ART}/nanosp-testnet-perf"       "${NSP_SDK}" "bitcoin_testnet" "AUTOAPPROVE_FOR_PERF_TESTS=1"
  build_app_variant "${REF_APP}"  "${REF_ART}/nanox-testnet-perf"        "${NX_SDK}"  "bitcoin_testnet" "AUTOAPPROVE_FOR_PERF_TESTS=1"

  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanosp-mainnet"           "${NSP_SDK}" "bitcoin"         ""
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanosp-mainnet-sameflags" "${NSP_SDK}" "bitcoin"         "LLB_KEEP_UPSTREAM_DEFINES=1"
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanox-mainnet"            "${NX_SDK}"  "bitcoin"         ""
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanox-mainnet-sameflags"  "${NX_SDK}"  "bitcoin"         "LLB_KEEP_UPSTREAM_DEFINES=1"
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanosp-testnet"           "${NSP_SDK}" "bitcoin_testnet" ""
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanox-testnet"            "${NX_SDK}"  "bitcoin_testnet" ""
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanosp-testnet-perf"      "${NSP_SDK}" "bitcoin_testnet" "AUTOAPPROVE_FOR_PERF_TESTS=1"
  build_app_variant "${LEAN_APP}" "${LEAN_ART}/nanox-testnet-perf"       "${NX_SDK}"  "bitcoin_testnet" "AUTOAPPROVE_FOR_PERF_TESTS=1"
else
  echo "[bolos-bench] 1-2/5 Reusing prebuilt Reference & Lean firmware artifacts (--skip-rebuild)..."
fi

echo "[bolos-bench] 3/5 Running x86_64 LTO rdtscp hotspot microbenchmarks..."
HOTSPOT_BIN="/tmp/w4_bench_bolos_hotspots_$$"
"${CLANG_BIN}" -O2 -flto -march=x86-64 -Wno-override-module \
  -I"${REPO_ROOT}/ffi/bolos/build/lto" \
  "${REPO_ROOT}/ffi/bolos/bench_bolos_hotspots.c" \
  "${REPO_ROOT}/ffi/bolos/build/lto/liblean_ledger_bitcoin_host.ll" \
  -o "${HOTSPOT_BIN}"
HOTSPOT_JSON="$(taskset -c 0 "${HOTSPOT_BIN}")"
rm -f "${HOTSPOT_BIN}"

if [ "${HOTSPOTS_ONLY}" -eq 1 ]; then
  printf '%s\n' "${HOTSPOT_JSON}"
  exit 0
fi

echo "[bolos-bench] 4/5 Collecting storage, RAM, stack, ARM instruction counts & host C suite timings..."
echo "[bolos-bench] 5/5 Measuring interleaved Speculos APDU wall-clock latencies on Nano S+ & Nano X..."

export REPO_ROOT REF_APP LEAN_APP REF_ART LEAN_ART OUT_JSON HOTSPOT_JSON
python3 - << 'PY'
import hashlib, hmac, json, os, re, statistics, subprocess, sys, time

REPO_ROOT = os.environ["REPO_ROOT"]
REF_APP = os.environ["REF_APP"]
LEAN_APP = os.environ["LEAN_APP"]
REF_ART = os.environ["REF_ART"]
LEAN_ART = os.environ["LEAN_ART"]
OUT_JSON = os.environ["OUT_JSON"]
HOTSPOT_DATA = json.loads(os.environ["HOTSPOT_JSON"])

sys.path.insert(0, LEAN_APP)
sys.path.insert(0, os.path.join(LEAN_APP, "bitcoin_client"))

# ---------------------------------------------------------------------------
# 1. Storage, RAM, & Static Stack Call-Graph Analyzer
# ---------------------------------------------------------------------------
def analyze_asm(asm_path: str):
    funcs = {}
    cur = None
    total_insns = 0
    for line in open(asm_path):
        m = re.match(r"^[0-9a-f]+\s+<([^>]+)>:\s*$", line)
        if m:
            cur = m.group(1)
            funcs[cur] = {"push": 0, "sub_sp": 0, "calls": set(), "tail": set(), "insns": 0}
            continue
        if cur is None:
            continue
        parts = line.split("\t")
        if len(parts) < 3:
            continue
        mnem = parts[1].strip()
        if mnem.startswith("."):
            continue
        funcs[cur]["insns"] += 1
        total_insns += 1
        ops = parts[2].split("@")[0].strip()
        if mnem.startswith("push") and funcs[cur]["push"] == 0:
            rm = re.search(r"\{([^}]+)\}", ops)
            if rm:
                regs = []
                for item in rm.group(1).split(","):
                    item = item.strip()
                    if "-" in item:
                        a, b = item.split("-")
                        ra = int(re.sub(r"\D", "", a))
                        rb = int(re.sub(r"\D", "", b))
                        regs.extend(range(ra, rb + 1))
                    else:
                        regs.append(item)
                funcs[cur]["push"] = 4 * len(regs)
        elif mnem in ("sub", "sub.w", "subs") and ops.startswith("sp,"):
            im = re.search(r"#0x([0-9a-fA-F]+)|#(\d+)", ops)
            if im:
                val = int(im.group(1), 16) if im.group(1) else int(im.group(2))
                if val > funcs[cur]["sub_sp"]:
                    funcs[cur]["sub_sp"] = val
        elif mnem in ("bl", "blx"):
            tm = re.search(r"<([^+>]+)>", parts[2])
            if tm:
                funcs[cur]["calls"].add(tm.group(1))
        elif mnem in ("b.w", "b"):
            tm = re.search(r"<([^+>]+)>", parts[2])
            if tm and tm.group(1) != cur:
                funcs[cur]["tail"].add(tm.group(1))

    frames = {f: d["push"] + d["sub_sp"] for f, d in funcs.items()}
    memo = {}
    visiting = set()

    def max_stack(fn):
        if fn not in funcs:
            return (0, [fn])
        if fn in memo:
            return memo[fn]
        if fn in visiting:
            return (frames[fn], [fn + " (RECURSIVE)"])
        visiting.add(fn)
        best_sub = 0
        best_path = []
        for cal in sorted(funcs[fn]["calls"]):
            s, p = max_stack(cal)
            if s > best_sub:
                best_sub, best_path = s, p
        for cal in sorted(funcs[fn]["tail"]):
            s, p = max_stack(cal)
            if s - frames[fn] > best_sub:
                best_sub, best_path = s - frames[fn], p
        visiting.remove(fn)
        res = (frames[fn] + best_sub, [fn] + best_path)
        memo[fn] = res
        return res

    worst_bytes = 0
    worst_root = ""
    worst_path = []
    for f in sorted(funcs):
        s, p = max_stack(f)
        if s > worst_bytes:
            worst_bytes, worst_root, worst_path = s, f, p

    key_handlers = {}
    for h in [
        "main",
        "handler_sign_psbt",
        "handler_register_wallet",
        "handler_get_wallet_address",
        "handler_get_extended_pubkey",
        "handler_sign_message",
        "format_sats_amount",
        "merkle_get_ith_direction",
    ]:
        if h in funcs:
            key_handlers[h] = {
                "max_stack_bytes": max_stack(h)[0],
                "own_frame_bytes": frames[h],
                "arm_thumb_insns": funcs[h]["insns"],
            }

    return {
        "worst_case_stack_bytes": worst_bytes,
        "worst_case_root": worst_root,
        "worst_case_call_chain_depth": len(worst_path),
        "total_arm_thumb_insns": total_insns,
        "has_recursive_qsort": "qsort" in funcs,
        "handlers": key_handlers,
    }


def parse_map_input_sections(map_path: str):
    code = rodata = data = bss = 0
    for line in open(map_path):
        m = re.match(r"^\s*[0-9a-f]+\s+[0-9a-f]+\s+([0-9a-f]+)\s+\d+\s+(.+)$", line)
        if not m:
            continue
        sz = int(m.group(1), 16)
        rest = m.group(2).strip()
        mc = re.search(r":\(([^)]+)\)$", rest)
        if not mc:
            continue
        sec = mc.group(1)
        if sec.startswith((".text", ".boot", ".ARM.exidx")):
            code += sz
        elif sec.startswith((".rodata", ".nvm_data")):
            rodata += sz
        elif sec.startswith(".data"):
            data += sz
        elif sec.startswith((".bss", "COMMON")):
            bss += sz
    return {"input_code": code, "input_rodata": rodata, "input_data": data, "input_bss": bss}


def collect_elf_metrics(art_dir: str):
    elf_path = os.path.join(art_dir, "app.elf")
    apdu_path = os.path.join(art_dir, "app.apdu")
    map_path = os.path.join(art_dir, "app.map")
    asm_path = os.path.join(art_dir, "app.asm")

    nm_out = subprocess.check_output(["llvm-nm", "--radix=d", elf_path], text=True)
    syms = {}
    for line in nm_out.splitlines():
        parts = line.split()
        if len(parts) >= 3:
            syms[parts[-1]] = int(parts[0])

    ph_out = subprocess.check_output(["llvm-readelf", "-l", elf_path], text=True)
    loads = [int(m.group(1), 16) for m in re.finditer(r"LOAD\s+\S+\s+\S+\s+\S+\s+(0x[0-9a-fA-F]+)", ph_out)]
    size_b = subprocess.check_output(["llvm-size", "-B", elf_path], text=True).splitlines()[1].split()

    tmp_strip = f"/tmp/w4_strip_{os.getpid()}.elf"
    subprocess.check_call(["arm-none-eabi-strip", "-o", tmp_strip, elf_path])
    stripped_sz = os.path.getsize(tmp_strip)
    os.remove(tmp_strip)

    mp = parse_map_input_sections(map_path)
    st = analyze_asm(asm_path)

    return {
        "load_flash_bytes": sum(loads),
        "text_code_bytes": syms["_ecode"] - syms["_text"],
        "rodata_bytes": syms["_etext"] - syms["_ecode"],
        "map_input_code_bytes": mp["input_code"],
        "map_input_rodata_bytes": mp["input_rodata"],
        "data_bytes": int(size_b[1]),
        "bss_ram_bytes": syms["_ebss"] - syms["_bss"],
        "total_static_ram_bytes": int(size_b[1]) + (syms["_ebss"] - syms["_bss"]),
        "elf_unstripped_bytes": os.path.getsize(elf_path),
        "elf_stripped_bytes": stripped_sz,
        "apdu_bytes": os.path.getsize(apdu_path),
        "has_qsort": "qsort" in syms,
        "has_udivmoddi4": ("__aeabi_uldivmod" in syms) or ("__udivmoddi4" in syms),
        "stack_and_insns": st,
    }

storage_ram_stack = {
    "nanosp_mainnet": {
        "reference": collect_elf_metrics(os.path.join(REF_ART, "nanosp-mainnet")),
        "lean_opt": collect_elf_metrics(os.path.join(LEAN_ART, "nanosp-mainnet")),
        "lean_sameflags": collect_elf_metrics(os.path.join(LEAN_ART, "nanosp-mainnet-sameflags")),
    },
    "nanox_mainnet": {
        "reference": collect_elf_metrics(os.path.join(REF_ART, "nanox-mainnet")),
        "lean_opt": collect_elf_metrics(os.path.join(LEAN_ART, "nanox-mainnet")),
        "lean_sameflags": collect_elf_metrics(os.path.join(LEAN_ART, "nanox-mainnet-sameflags")),
    },
    "nanosp_testnet": {
        "reference": collect_elf_metrics(os.path.join(REF_ART, "nanosp-testnet")),
        "lean_opt": collect_elf_metrics(os.path.join(LEAN_ART, "nanosp-testnet")),
    },
    "nanox_testnet": {
        "reference": collect_elf_metrics(os.path.join(REF_ART, "nanox-testnet")),
        "lean_opt": collect_elf_metrics(os.path.join(LEAN_ART, "nanox-testnet")),
    },
}

# ---------------------------------------------------------------------------
# 2. Full Host C Unit-Test Workload Latency (Interleaved, Pinned Core 0)
# ---------------------------------------------------------------------------
UNIT_BINS = [
    "test_display_utils",
    "test_get_merkle_leaf_index",
    "test_musig",
    "test_wallet",
    "test_register_wallet",
    "test_get_wallet_address",
    "test_get_extended_pubkey",
    "test_psbt_fields",
]

host_unit_suites = {}
ref_ut_dir = os.path.join(REF_ART, "unit-tests-build")
lean_ut_dir = os.path.join(LEAN_ART, "unit-tests-build")
if os.path.isdir(ref_ut_dir) and os.path.isdir(lean_ut_dir):
    for b in UNIT_BINS:
        rb = os.path.join(ref_ut_dir, b)
        lb = os.path.join(lean_ut_dir, b)
        if not (os.path.exists(rb) and os.path.exists(lb)):
            continue
        r_times, l_times = [], []
        # Warmup
        subprocess.check_call(["taskset", "-c", "0", rb], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        subprocess.check_call(["taskset", "-c", "0", lb], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for rnd in range(15):
            if rnd % 2 == 0:
                t0 = time.perf_counter_ns()
                subprocess.check_call(["taskset", "-c", "0", rb], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                r_times.append((time.perf_counter_ns() - t0) / 1e6)
                t0 = time.perf_counter_ns()
                subprocess.check_call(["taskset", "-c", "0", lb], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                l_times.append((time.perf_counter_ns() - t0) / 1e6)
            else:
                t0 = time.perf_counter_ns()
                subprocess.check_call(["taskset", "-c", "0", lb], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                l_times.append((time.perf_counter_ns() - t0) / 1e6)
                t0 = time.perf_counter_ns()
                subprocess.check_call(["taskset", "-c", "0", rb], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                r_times.append((time.perf_counter_ns() - t0) / 1e6)
        rm = round(min(r_times), 3)
        lm = round(min(l_times), 3)
        rmed = round(statistics.median(r_times), 3)
        lmed = round(statistics.median(l_times), 3)
        host_unit_suites[b] = {
            "ref_min_ms": rm,
            "lean_min_ms": lm,
            "ref_median_ms": rmed,
            "lean_median_ms": lmed,
            "speedup_median": round(rmed / lmed, 3) if lmed > 0 else 1.0,
        }

# ---------------------------------------------------------------------------
# 3. Live Speculos APDU Wall-Clock Latency (Interleaved Reference vs Lean)
# ---------------------------------------------------------------------------
from speculos.client import SpeculosClient
from ledger_bitcoin import createClient, Chain, WalletPolicy
from test_utils import SpeculosGlobals, txmaker

PERF_SEED = txmaker.SPECULOS_SEED

def make_perf_workloads():
    wp_tr = WalletPolicy(
        name="",
        descriptor_template="tr(@0/**)",
        keys_info=["[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"],
    )
    wp_wsh_3of5 = WalletPolicy(
        name="Cold storage",
        descriptor_template="wsh(sortedmulti(3,@0/**,@1/**,@2/**,@3/**,@4/**))",
        keys_info=[
            "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK",
            "tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
            "tpubDF4kujkh5dAhC1pFgBToZybXdvJFXXGX4BWdDxWqP7EUpG8gxkfMQeDjGPDnTr9e4NrkFmDM1ocav3Jz6x79CRZbxGr9dzFokJLuvDDnyRh",
            "tpubDD3ULTdBbyuMMMs8BCsJKgZgEnZjjbsbtV6ig3xtkQnaSc1gu9kNhmDDEW49HoLzDNA4y2TMqRzj4BugrrtcpXkjoHSoMVhJwfZLUFmv6yn",
            "tpubDDyh1VAY2sHfGHE59muC5PWa3tosSTm62sNTDSmZUsx9TbyBdoVkZibYZuDoqJ8dJ6v6eYZz6SE1d6sDv45NgJFB1oqCLGzyiQBGyjexc7V",
        ],
    )

    in_amts_3 = [10000 + 10000 * i for i in range(3)]
    out_amts_2 = [sum(in_amts_3) // 2 - i for i in range(2)]
    psbt_tr_3in = txmaker.createPsbt(wp_tr, in_amts_3, out_amts_2, [False, True])

    out_amts_wsh = [sum(in_amts_3) // 3 - i for i in range(3)]
    psbt_wsh_3in = txmaker.createPsbt(wp_wsh_3of5, in_amts_3, out_amts_wsh, [False, True, False])

    return {
        "wp_tr": wp_tr,
        "wp_wsh_3of5": wp_wsh_3of5,
        "psbt_tr_3in": psbt_tr_3in,
        "psbt_wsh_3in": psbt_wsh_3in,
    }

WORKLOADS = make_perf_workloads()

def benchmark_speculos_pair(model: str, ref_elf: str, lean_elf: str, base_port: int):
    os.environ["SPECULOS_APPNAME"] = "Bitcoin Test:2.5.1"

    ops_spec = [
        ("GET_VERSION", 13, 10.0),
        ("GET_MASTER_FINGERPRINT", 11, 1.0),
        ("GET_EXTENDED_PUBKEY", 9, 1.0),
        ("GET_WALLET_ADDRESS", 7, 1.0),
        ("REGISTER_WALLET", 5, 1.0),
        ("SIGN_PSBT_TR_3IN", 4, 1.0),
        ("SIGN_PSBT_WSH3OF5_3IN", 3, 1.0),
    ]

    def run_pass(elf_path: str, api_port: int):
        url = f"http://127.0.0.1:{api_port}"
        comm = SpeculosClient(
            elf_path,
            ["--model", model, "--seed", PERF_SEED, "--display", "headless", "--api-port", str(api_port), "--apdu-port", "0"],
            api_url=url,
        )
        comm.start()
        try:
            c = createClient(comm, chain=Chain.TEST, debug=False)
            _, hmac_3of5 = c.register_wallet(WORKLOADS["wp_wsh_3of5"])
            call_map = {
                "GET_VERSION": lambda: [comm.apdu_exchange(0xB0, 0x01, b"", p1=0, p2=0) for _ in range(10)],
                "GET_MASTER_FINGERPRINT": lambda: c.get_master_fingerprint(),
                "GET_EXTENDED_PUBKEY": lambda: c.get_extended_pubkey("m/48'/1'/0'/2'", False),
                "GET_WALLET_ADDRESS": lambda: c.get_wallet_address(WORKLOADS["wp_tr"], None, 0, 7, False),
                "REGISTER_WALLET": lambda: c.register_wallet(WORKLOADS["wp_wsh_3of5"]),
                "SIGN_PSBT_TR_3IN": lambda: c.sign_psbt(WORKLOADS["psbt_tr_3in"], WORKLOADS["wp_tr"], None),
                "SIGN_PSBT_WSH3OF5_3IN": lambda: c.sign_psbt(WORKLOADS["psbt_wsh_3in"], WORKLOADS["wp_wsh_3of5"], hmac_3of5),
            }
            samples = {}
            for op_name, rounds, div_factor in ops_spec:
                fn = call_map[op_name]
                fn()
                arr = []
                for _ in range(rounds):
                    t0 = time.perf_counter_ns()
                    fn()
                    arr.append(((time.perf_counter_ns() - t0) / 1e6) / div_factor)
                samples[op_name] = arr
            return samples
        finally:
            comm.stop()

    # ABBA symmetric counterbalanced passes (Ref -> Lean -> Lean -> Ref) so only 1 QEMU
    # process runs at any instant while canceling linear/step host CPU frequency drift.
    r1 = run_pass(ref_elf, base_port)
    l1 = run_pass(lean_elf, base_port + 1)
    l2 = run_pass(lean_elf, base_port + 2)
    r2 = run_pass(ref_elf, base_port + 3)

    res = {}
    for op_name, rounds_half, _ in ops_spec:
        r_ms = r1[op_name] + r2[op_name]
        l_ms = l1[op_name] + l2[op_name]
        rmed = round(statistics.median(r_ms), 3)
        lmed = round(statistics.median(l_ms), 3)
        rmin = round(min(r_ms), 3)
        lmin = round(min(l_ms), 3)
        res[op_name] = {
            "rounds": len(r_ms),
            "ref_min_ms": rmin,
            "lean_min_ms": lmin,
            "delta_min_ms": round(lmin - rmin, 3),
            "speedup_min": round(rmin / lmin, 4) if lmin > 0 else 1.0,
            "ref_median_ms": rmed,
            "lean_median_ms": lmed,
            "delta_median_ms": round(lmed - rmed, 3),
            "speedup_median": round(rmed / lmed, 4) if lmed > 0 else 1.0,
        }
        print(f"  [{model}] {op_name:24s}: min Ref={rmin:8.3f} ms vs Lean={lmin:8.3f} ms ({res[op_name]['speedup_min']:.3f}x) | med Ref={rmed:8.3f} ms vs Lean={lmed:8.3f} ms ({res[op_name]['speedup_median']:.3f}x)")
    return res

speculos_apdu_latency = {
    "nanosp": benchmark_speculos_pair(
        "nanosp",
        os.path.join(REF_ART, "nanosp-testnet-perf", "app.elf"),
        os.path.join(LEAN_ART, "nanosp-testnet-perf", "app.elf"),
        5260,
    ),
    "nanox": benchmark_speculos_pair(
        "nanox",
        os.path.join(REF_ART, "nanox-testnet-perf", "app.elf"),
        os.path.join(LEAN_ART, "nanox-testnet-perf", "app.elf"),
        5270,
    ),
}

out_payload = {
    "metadata": {
        "upstream_repo": "LedgerHQ/app-bitcoin",
        "upstream_commit": "f010982d3050e02813cd7129bebd68cf2d1f2099",
        "turbo_lean_branch": "feat/freestanding-flat-ptr-loops",
        "turbo_lean_commit": "b9524d8059476935730c16afab0e18501ff80b49",
        "measurement_host": {
            "environment": os.environ.get("BENCHMARK_HOST_CLASS", "unspecified"),
            "same_host_reference_and_lean": True,
        },
        "targets": {
            "nanosp": "thumbv8m.main-none-eabi (cortex-m35p+nodsp, API_LEVEL 27)",
            "nanox": "thumbv6m-none-eabi (cortex-m3, API_LEVEL 22)",
        },
        "compiler": "Debian clang 21.1.8 + ld.lld 21.1.8 + arm-none-eabi-gcc sysroot",
    },
    "storage_ram_stack": storage_ram_stack,
    "x86_64_rdtscp_hotspots": HOTSPOT_DATA,
    "host_unit_test_workloads": host_unit_suites,
    "speculos_apdu_latency_ms": speculos_apdu_latency,
}

os.makedirs(os.path.dirname(OUT_JSON), exist_ok=True)
with open(OUT_JSON, "w") as f:
    json.dump(out_payload, f, indent=2)
print(f"[bolos-bench] Wrote {OUT_JSON}")
PY

#!/usr/bin/env bash
# benchmarks/vanadium_benchmark.sh
#
# Reproducible end-to-end storage, RAM/stack, RV32IMAC VM instruction/page-fault,
# Speculos Flex wall-clock latency, and host microbenchmark suite comparing:
#   1. Unmodified upstream `LedgerHQ/vanadium` (`ace8e96982408959dea9e7fbc59ee36e8c54e645`)
#      `apps/bitcoin/app` (`vnd-bitcoin` RV32IMAC V-App)
#   2. Our Lean-integrated & optimized `vnd-bitcoin` (`ffi/vanadium` +
#      `ffi/vanadium/patches/vanadium-bitcoin-lean-opt.patch`, enforcing `VND-BUG-001..009`)
#   3. Same-profile `vnd-bitcoin` (upstream Cargo/linker/64 KiB heap profile + our Lean
#      code/dependency optimizations, isolating pure source-level wins from profile wins).
#
# Usage:
#   bash benchmarks/vanadium_benchmark.sh
#
# Environment overrides:
#   LEDGER_HUB     (default: /var/lib/orb-node/work/caches/ledger-hub)
#   VANADIUM_REF   (default: /var/lib/orb-node/work/w4-vanadium/vanadium-ref)
#   VANADIUM_LEAN  (default: /var/lib/orb-node/work/w4-vanadium/vanadium-lean)
#   VM_METRICS_BIN (default: /var/lib/orb-node/work/w4-vanadium/vm-metrics/app-vanadium-metrics)
#   E2E_RUNS       (default: 5)
#
# Per-APDU counter trace (optional; replaces steps 3, 5 and 6):
#   TRACE_OUT_DIR  if set (to a directory that has no elfs/ yet), runs only the sign_transaction
#                  workload for the three variants, samples the VM counters after every APDU
#                  exchange, then exits. Needs VM_METRICS_BIN to be a VM built with the "metrics"
#                  feature *and* benchmarks/vanadium_vm_live_metrics.patch applied (upstream only
#                  serves GetMetrics after the V-App has exited). Raw runs, frozen ELFs and
#                  Speculos screenshots are written there; benchmarks/vanadium_trace.py
#                  assembles them into benchmarks/vanadium_trace.json.
#   TRACE_RUNS     measured runs per variant, interleaved in mirrored cycles (default: 3)

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEDGER_HUB="${LEDGER_HUB:-/var/lib/orb-node/work/caches/ledger-hub}"
VANADIUM_REF="${VANADIUM_REF:-/var/lib/orb-node/work/w4-vanadium/vanadium-ref}"
VANADIUM_LEAN="${VANADIUM_LEAN:-/var/lib/orb-node/work/w4-vanadium/vanadium-lean}"
VM_METRICS_BIN="${VM_METRICS_BIN:-/var/lib/orb-node/work/w4-vanadium/vm-metrics/app-vanadium-metrics}"
E2E_RUNS="${E2E_RUNS:-5}"
OUT_JSON="${OUT_JSON:-$REPO_ROOT/benchmarks/vanadium_results.json}"

if [[ -f "$LEDGER_HUB/env.sh" ]]; then
  # shellcheck disable=SC1090
  source "$LEDGER_HUB/env.sh"
fi
export PATH="$LEDGER_HUB/venv-bolos/bin:$PATH"
export PKG_CONFIG_PATH="${PKG_CONFIG_PATH:-$LEDGER_HUB/sysroot/usr/lib/x86_64-linux-gnu/pkgconfig}"

WORK_TMP="$(mktemp -d /tmp/vanadium-bench-XXXXXX)"
trap 'rm -rf "$WORK_TMP"' EXIT

echo "[1/6] Emitting & verifying 0-byte stack frame Lean freestanding kernels (ffi/vanadium)..."
LEAN_NATIVE="${LEAN_NATIVE:-$LEDGER_HUB/turbo-lean/lean/.lake/build/bin/lean-native}"
mkdir -p "$REPO_ROOT/ffi/vanadium/build/riscv32imac" "$REPO_ROOT/ffi/vanadium/build/host"

timeout 180s "$LEAN_NATIVE" emit-freestanding-c-lib \
  --input "$REPO_ROOT/BitcoinLedger/FreestandingKernels.lean" \
  --target riscv32imac --clang-bin clang \
  -o "$REPO_ROOT/ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a" --json > "$WORK_TMP/emit_rv32.json"

clang --target=riscv32-unknown-none-elf -march=rv32imac -mabi=ilp32 -Oz \
  -ffunction-sections -fdata-sections -fno-unwind-tables -fno-asynchronous-unwind-tables \
  -c "$REPO_ROOT/ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.ll" \
  -o "$REPO_ROOT/ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.o"
rm -f "$REPO_ROOT/ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a"
llvm-ar rcs "$REPO_ROOT/ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a" \
  "$REPO_ROOT/ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.o"
printf "1" > "$REPO_ROOT/ffi/vanadium/build/riscv32imac/.oz_gc_built"

timeout 180s "$LEAN_NATIVE" emit-freestanding-c-lib \
  --input "$REPO_ROOT/BitcoinLedger/FreestandingKernels.lean" \
  --target x86_64 --clang-bin clang \
  -o "$REPO_ROOT/ffi/vanadium/build/host/liblean_ledger_bitcoin.a" --json > "$WORK_TMP/emit_host.json"

echo "[2/6] Building RV32IMAC ELF variants (Reference, Lean-Optimized, Same-Profile)..."
mkdir -p "$WORK_TMP/elfs/ref_plain/target" \
         "$WORK_TMP/elfs/ref_auto/target" \
         "$WORK_TMP/elfs/lean_plain/target" \
         "$WORK_TMP/elfs/lean_auto/target" \
         "$WORK_TMP/elfs/sameprof_plain/target" \
         "$WORK_TMP/elfs/sameprof_auto/target"
cp "$VANADIUM_REF/apps/bitcoin/app/Cargo.toml" "$WORK_TMP/elfs/ref_plain/Cargo.toml"
cp "$VANADIUM_REF/apps/bitcoin/app/Cargo.toml" "$WORK_TMP/elfs/ref_auto/Cargo.toml"
cp "$VANADIUM_LEAN/apps/bitcoin/app/Cargo.toml" "$WORK_TMP/elfs/lean_plain/Cargo.toml"
cp "$VANADIUM_LEAN/apps/bitcoin/app/Cargo.toml" "$WORK_TMP/elfs/lean_auto/Cargo.toml"
cp "$VANADIUM_REF/apps/bitcoin/app/Cargo.toml" "$WORK_TMP/elfs/sameprof_plain/Cargo.toml"
cp "$VANADIUM_REF/apps/bitcoin/app/Cargo.toml" "$WORK_TMP/elfs/sameprof_auto/Cargo.toml"

# Reference plain + autoapprove
(cd "$VANADIUM_REF/apps/bitcoin/app" && \
  cargo build --release --target riscv32imac-unknown-none-elf --no-default-features --features target_vanadium_ledger --quiet && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/ref_plain/target/ref_plain.elf" && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/ref_plain.elf" && \
  cargo build --release --target riscv32imac-unknown-none-elf --no-default-features --features target_vanadium_ledger,autoapprove --quiet && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/ref_auto/target/ref_auto.elf" && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/ref_auto.elf")

# Lean-optimized plain + autoapprove
(cd "$VANADIUM_LEAN/apps/bitcoin/app" && \
  cargo build --release --target riscv32imac-unknown-none-elf --no-default-features --features target_vanadium_ledger --quiet && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/lean_plain/target/lean_plain.elf" && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/lean_plain.elf" && \
  cargo build --release --target riscv32imac-unknown-none-elf --no-default-features --features target_vanadium_ledger,autoapprove --quiet && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/lean_auto/target/lean_auto.elf" && \
  cp target/riscv32imac-unknown-none-elf/release/vnd-bitcoin "$WORK_TMP/elfs/lean_auto.elf")

# Same-profile Lean plain + autoapprove (upstream linker flags, panic=unwind, strip=none, VAPP_HEAP_SIZE=65536)
SAMEPROF_TARGET="/tmp/w4-sameprof-target"
(cd "$VANADIUM_LEAN/apps/bitcoin/app" && \
  VAPP_HEAP_SIZE=65536 RUSTFLAGS="-Clink-arg=--no-rosegment" \
  cargo build --release --target riscv32imac-unknown-none-elf --target-dir "$SAMEPROF_TARGET" \
    --config 'profile.release.panic="unwind"' --config 'profile.release.strip="none"' \
    --no-default-features --features target_vanadium_ledger --quiet && \
  cp "$SAMEPROF_TARGET/riscv32imac-unknown-none-elf/release/vnd-bitcoin" "$WORK_TMP/elfs/sameprof_plain/target/sameprof_plain.elf" && \
  cp "$SAMEPROF_TARGET/riscv32imac-unknown-none-elf/release/vnd-bitcoin" "$WORK_TMP/elfs/sameprof_plain.elf" && \
  VAPP_HEAP_SIZE=65536 RUSTFLAGS="-Clink-arg=--no-rosegment" \
  cargo build --release --target riscv32imac-unknown-none-elf --target-dir "$SAMEPROF_TARGET" \
    --config 'profile.release.panic="unwind"' --config 'profile.release.strip="none"' \
    --no-default-features --features target_vanadium_ledger,autoapprove --quiet && \
  cp "$SAMEPROF_TARGET/riscv32imac-unknown-none-elf/release/vnd-bitcoin" "$WORK_TMP/elfs/sameprof_auto/target/sameprof_auto.elf" && \
  cp "$SAMEPROF_TARGET/riscv32imac-unknown-none-elf/release/vnd-bitcoin" "$WORK_TMP/elfs/sameprof_auto.elf")

if [[ -z "${TRACE_OUT_DIR:-}" ]]; then
echo "[3/6] Running deterministic host microbenchmarks (llb-vanadium-ffi)..."
HOST_BENCH_JSON="$(cargo run --release --quiet --manifest-path "$REPO_ROOT/ffi/vanadium/Cargo.toml" --example bench_kernels -- 1000000)"
echo "  Host bench: $HOST_BENCH_JSON"
fi

echo "[4/6] Building Speculos Flex E2E benchmark driver..."
mkdir -p "$WORK_TMP/driver/src"
cat > "$WORK_TMP/driver/Cargo.toml" << EOF
[package]
name = "vanadium-e2e-bench"
version = "0.1.0"
edition = "2021"

[dependencies]
vnd-bitcoin-client = { path = "$VANADIUM_LEAN/apps/bitcoin/client" }
common = { package = "vnd-bitcoin-common", path = "$VANADIUM_LEAN/apps/bitcoin/common", default-features = false, features = ["target_native"] }
sdk = { package = "vanadium-client-sdk", path = "$VANADIUM_LEAN/client-sdk" }
bitcoin = { version = "0.32.0", features = ["serde"], default-features = false }
base64 = { version = "0.22.1", default-features = false, features = ["alloc"] }
hex = "0.4.3"
tokio = { version = "1.38.1", features = ["io-util", "macros", "net", "rt", "rt-multi-thread", "sync", "time"] }
async-trait = "0.1.81"
EOF

cat > "$WORK_TMP/driver/src/main.rs" << 'EOF'
use std::net::{IpAddr, Ipv4Addr, SocketAddr, TcpListener};
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

use base64::Engine;
use bitcoin::{
    bip32::{ChildNumber, DerivationPath, Xpriv, Xpub},
    hashes::Hash,
    secp256k1::{ecdsa::Signature, Message, Secp256k1},
    sighash::SighashCache,
    Amount, EcdsaSighashType, NetworkKind, OutPoint, ScriptBuf, Transaction, TxIn, TxOut, Txid,
};
use common::{
    account::SilentPaymentCoordinates,
    bip388::{KeyInformation, WalletPolicy},
    fastpsbt::{PSBT_OUT_SCRIPT, PSBT_OUT_SP_V0_INFO},
    message::KeyTree,
    psbt::{prepare_psbt, PsbtV2},
    script::ToScript,
    silent_payments::{self as sp, Secp256k1 as Curve, Secp256k1Point, Secp256k1Scalar, SilentPaymentCode},
};
use sdk::{
    linewriter::Sink,
    transport::{APDUCommand, StatusWord, Transport, TransportTcp, TransportWrapper},
    vanadium_client::VanadiumAppClient,
};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::time::sleep;
use vnd_bitcoin_client::BitcoinClient;

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

async fn spawn_speculos(vanadium_bin: &str) -> (Child, Arc<TransportTcp>, u16) {
    for _ in 0..10 {
        let apdu_port = free_port();
        let api_port = free_port();
        let mut child = Command::new("speculos")
            .args([
                vanadium_bin,
                "--model", "flex",
                "--display", "headless",
                "--apdu-port", &apdu_port.to_string(),
                "--api-port", &api_port.to_string(),
            ])
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .expect("spawn speculos");

        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), apdu_port);
        for _ in 0..25 {
            if let Ok(Some(_)) = child.try_wait() {
                break;
            }
            if let Ok(tcp) = TransportTcp::new(addr).await {
                return (child, Arc::new(tcp), api_port);
            }
            sleep(Duration::from_millis(150)).await;
        }
        let _ = child.kill();
        let _ = child.wait();
    }
    panic!("Failed to start Speculos");
}

fn parse_wallet_policy(template: &str, keys_info: &[&str]) -> WalletPolicy {
    let keys = keys_info.iter().map(|k| KeyInformation::try_from(*k).unwrap()).collect();
    WalletPolicy::new(template, keys).unwrap()
}

#[derive(Default, Clone)]
struct WorkloadResult {
    wall_ms: f64,
    apdu_exchanges: u64,
    bytes_sent: u64,
    bytes_received: u64,
    instruction_count: Option<u64>,
    page_loads: Option<u32>,
    page_commits: Option<u32>,
    current_heap_bytes: Option<u32>,
    peak_heap_bytes: Option<u32>,
}

async fn query_vm_metrics(tcp: &TransportTcp) -> (u64, u32, u32) {
    let cmd = APDUCommand { cla: 0xE0, ins: 0xF0, p1: 0, p2: 0, data: Vec::new() };
    let (sw, data) = tcp.exchange(&cmd).await.expect("GetMetrics exchange");
    assert_eq!(sw, StatusWord::OK);
    assert_eq!(data.len(), 80);
    (
        u64::from_be_bytes(data[64..72].try_into().unwrap()),
        u32::from_be_bytes(data[72..76].try_into().unwrap()),
        u32::from_be_bytes(data[76..80].try_into().unwrap()),
    )
}

async fn run_workload(
    vanadium_bin: &str,
    vapp_bin: &str,
    name: &str,
    with_metrics: bool,
    query_heap: bool,
) -> WorkloadResult {
    let (mut child, tcp, _api_port) = spawn_speculos(vanadium_bin).await;
    let transport = Arc::new(TransportWrapper::new(tcp.clone()));

    let t0 = Instant::now();
    let vapp_client = VanadiumAppClient::with_vapp(vapp_bin, transport, Box::new(Sink::default()), false)
        .await
        .expect("VanadiumAppClient::with_vapp");
    let mut client = BitcoinClient::new(Box::new(vapp_client));

    if query_heap {
        let _ = client.get_heap_stats(true).await;
    }

    match name {
        "get_fingerprint" => {
            let fpr = client.get_master_fingerprint(KeyTree::Standard).await.unwrap();
            assert_eq!(fpr, 0xf5acc2fd);
        }
        "sign_transaction" => {
            sign_transaction_flow(&mut client, &|_| {}).await;
        }
        "send_to_silent_payment" => {
            let xpub = "tpubDCtKfsNyRhULjZ9XMS4VKKtVcPdVDi8MKUbcSD9MJDyjRu1A2ND5MiipozyyspBT9bg8upEp7a8EAgFxNxXn1d7QkdbL52Ty5jiSLcxPt1P";
            let wallet_policy = parse_wallet_policy("wpkh(@0/**)", &[&format!("[f5acc2fd/84'/1'/0']{xpub}")]);
            let account_name = "My segwit account #0";
            let (_, por) = client.register_account(account_name, &wallet_policy, None, None, false).await.unwrap();
            let (_, code) = SilentPaymentCode::from_address("sp1qqgste7k9hx0qftg6qmwlkqtwuy6cycyavzmzj85c6qdfhjdpdjtdgqjuexzk6murw56suy3e0rd2cgqvycxttddwsvgxe2usfpxumr70xc9pkqwv").unwrap();
            let secp = Secp256k1::new();
            let key = xpub.parse::<Xpub>().unwrap().derive_pub(&secp, &[ChildNumber::from(0), ChildNumber::from(2)]).unwrap().public_key;
            let prevout = TxOut { value: Amount::from_sat(100_000), script_pubkey: wallet_policy.to_script(false, 2).unwrap() };
            let mut tx = Transaction {
                version: bitcoin::transaction::Version::TWO,
                lock_time: bitcoin::absolute::LockTime::ZERO,
                input: vec![TxIn { previous_output: OutPoint { txid: Txid::from_byte_array([1; 32]), vout: 0 }, ..Default::default() }],
                output: vec![TxOut { value: Amount::from_sat(99_000), script_pubkey: ScriptBuf::from_bytes(vec![0x51]) }],
            };
            let mut psbt_v0 = bitcoin::psbt::Psbt::from_unsigned_tx(tx.clone()).unwrap();
            psbt_v0.inputs[0].witness_utxo = Some(prevout.clone());
            psbt_v0.inputs[0].bip32_derivation.insert(key, ("f5acc2fd".parse().unwrap(), "m/84'/1'/0'/0/2".parse().unwrap()));
            let mut psbt = PsbtV2::from_v0(&psbt_v0.serialize()).unwrap();
            psbt.outputs[0].remove(PSBT_OUT_SCRIPT, &[]);
            psbt.outputs[0].insert(PSBT_OUT_SP_V0_INFO, &[], code.to_bytes().to_vec());
            prepare_psbt(&mut psbt, &[(&wallet_policy, &account_name, &por.dangerous_as_bytes())]).unwrap();
            let result = client.sign_psbt(&psbt.serialize()).await.unwrap();
            assert_eq!(result.signatures.len(), 1);
            result.merge_into(&mut psbt).unwrap();
            let share = &result.sp_shares[0];
            let a = Secp256k1Point::from_compressed(&key.serialize()).unwrap();
            let c = Secp256k1Point::from_compressed(&share.share).unwrap();
            assert!(sp::verify_proof(&a, code.scan(), &c, &share.dleq_proof, &Curve::get_generator(), None));
            tx.output[0].script_pubkey = psbt.outputs[0].script().unwrap();
            let sighash = SighashCache::new(&tx).p2wpkh_signature_hash(0, &prevout.script_pubkey, prevout.value, EcdsaSighashType::All).unwrap();
            let (_, der) = result.signatures[0].signature.split_last().unwrap();
            secp.verify_ecdsa(&Message::from_digest(sighash.to_byte_array()), &Signature::from_der(der).unwrap(), &key).unwrap();
        }
        "silent_payment_account" => {
            let account = client.export_silent_payment_scan_key(3).await.unwrap();
            let seed = hex::decode("b11997faff420a331bb4a4ffdc8bdc8ba7c01732a99a30d83dbbebd469666c84b47d09d3f5f472b3b9384ac634beba2a440ba36ec7661144132f35e206873564").unwrap();
            let key = |path: &str| {
                let master = Xpriv::new_master(NetworkKind::Test, &seed).unwrap();
                let path: DerivationPath = path.parse().unwrap();
                let k = master.derive_priv(&Secp256k1::new(), &path).unwrap();
                Secp256k1Scalar::from_be_bytes(&k.private_key.secret_bytes()).unwrap()
            };
            assert_eq!(account.scan_key(), &key("m/352'/1'/3'/1'/0"));
            let name = "Silent payments #3";
            let (_, por) = client.register_account(name, &account, None, None, false).await.unwrap();
            for label in [None, Some(1)] {
                let coords = SilentPaymentCoordinates::Code { label };
                let (address, _) = client.get_address(&account, name, &coords, Some(&por), false, None).await.unwrap();
                assert!(address.starts_with("tsp1"));
            }
            let change = SilentPaymentCoordinates::Code { label: Some(0) };
            assert!(client.get_address(&account, name, &change, Some(&por), false, None).await.is_err());
        }
        other => panic!("Unknown workload: {}", other),
    }

    let (current_heap_bytes, peak_heap_bytes) = if query_heap {
        match client.get_heap_stats(false).await {
            Ok((cur, peak)) => (Some(cur), Some(peak)),
            Err(_) => (None, None),
        }
    } else {
        (None, None)
    };

    let status = client.exit().await.expect("client.exit");
    assert_eq!(status, 0);
    let wall_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let apdu_exchanges = tcp.total_exchanges();
    let bytes_sent = tcp.total_sent();
    let bytes_received = tcp.total_received();
    drop(client);

    let (instruction_count, page_loads, page_commits) = if with_metrics {
        let (i, l, c) = query_vm_metrics(&tcp).await;
        (Some(i), Some(l), Some(c))
    } else {
        (None, None, None)
    };

    let _ = child.kill();
    let _ = child.wait();

    WorkloadResult {
        wall_ms,
        apdu_exchanges,
        bytes_sent,
        bytes_received,
        instruction_count,
        page_loads,
        page_commits,
        current_heap_bytes,
        peak_heap_bytes,
    }
}

// The Taproot `tr(@0/**)` signing flow of the "sign_transaction" workload. `on_phase` is called
// right before the client request that opens each phase.
async fn sign_transaction_flow(client: &mut BitcoinClient, on_phase: &dyn Fn(&'static str)) {
    let psbt_b64 = "cHNidP8BAH0CAAAAAeFoYcDSl0n1LNLt3hDLzE9ZEhBxD2QOXY4UQM6F2W3GAQAAAAD9////Ao00lwAAAAAAIlEgC450hrwwagrvt6fACvBAVULbGs1z7syoJ3HM9f5etg+ghgEAAAAAABYAFBOZuKCYR6A5sDUvWNISwYC6sX93AAAAAAABASvfu5gAAAAAACJRIImQSmNI1/+aRNSduLaoB8Yi6Gg2TFR9pCbzC1piExhqIRbpxpsJXtBLVir8jUFpGTa6Vz629om8I2YAvk+jkm9kEhkA9azC/VYAAIABAACAAAAAgAEAAAADAAAAARcg6cabCV7QS1Yq/I1BaRk2ulc+tvaJvCNmAL5Po5JvZBIAAQUgApCB7OVhaqHLmTGfxIdO/uR/CM66X2AEY2yMQ0CaXwohBwKQgezlYWqhy5kxn8SHTv7kfwjOul9gBGNsjENAml8KGQD1rML9VgAAgAEAAIAAAACAAQAAAAIAAAAAAA==";
    let mut psbt = PsbtV2::from_v0(&base64::engine::general_purpose::STANDARD.decode(psbt_b64).unwrap()).unwrap();
    let wallet_policy = parse_wallet_policy(
        "tr(@0/**)",
        &["[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"],
    );
    let account_name = "My taproot account #0";
    on_phase("account_registration");
    let (_, por) = client.register_account(account_name, &wallet_policy, None, None, false).await.unwrap();
    on_phase("sign_transaction");
    prepare_psbt(&mut psbt, &[(&wallet_policy, &account_name, &por.dangerous_as_bytes())]).unwrap();
    let result = client.sign_psbt(&psbt.serialize()).await.unwrap();
    assert_eq!(result.signatures.len(), 1);
}

// ---- Per-APDU VM counter trace (`--trace`) --------------------------------------------------
//
// Needs a VM built with the "metrics" feature and benchmarks/vanadium_vm_live_metrics.patch:
// upstream only answers GetMetrics once the V-App has exited, whereas the patched VM also
// answers it (with live counters) every time the V-App is interrupted and waiting for the
// client's `Continue`.

struct TraceSample {
    t_ms: f64,
    phase: &'static str,
    vm_state: &'static str,
    instructions: u64,
    page_loads: u32,
    page_commits: u32,
}

// Transport that, after every APDU exchange of the workload, reads the VM counters with one
// extra GetMetrics exchange. The extra exchanges are not counted in `apdu_index`.
struct TracingTransport {
    inner: Arc<TransportTcp>,
    t0: Instant,
    gate: tokio::sync::Mutex<()>,
    phase: std::sync::Mutex<&'static str>,
    samples: std::sync::Mutex<Vec<TraceSample>>,
}

impl TracingTransport {
    fn set_phase(&self, phase: &'static str) {
        *self.phase.lock().unwrap() = phase;
    }
}

#[async_trait::async_trait]
impl Transport for TracingTransport {
    type Error = Box<dyn std::error::Error + Send + Sync>;

    async fn exchange(&self, command: &APDUCommand) -> Result<(StatusWord, Vec<u8>), Self::Error> {
        let _gate = self.gate.lock().await;
        let (sw, data) = self.inner.exchange(command).await?;
        // host-monotonic timestamp of the end of the workload's exchange, before the probe
        let t_ms = self.t0.elapsed().as_secs_f64() * 1000.0;
        let phase = *self.phase.lock().unwrap();

        let probe = APDUCommand { cla: 0xE0, ins: 0xF0, p1: 0, p2: 0, data: Vec::new() };
        let (probe_sw, m) = self.inner.exchange(&probe).await?;
        let sample = if probe_sw == StatusWord::OK && m.len() == 80 {
            let vm_state = if sw == StatusWord::InterruptedExecution { "vapp_interrupted" } else { "vapp_exited" };
            TraceSample {
                t_ms,
                phase,
                vm_state,
                instructions: u64::from_be_bytes(m[64..72].try_into().unwrap()),
                page_loads: u32::from_be_bytes(m[72..76].try_into().unwrap()),
                page_commits: u32::from_be_bytes(m[76..80].try_into().unwrap()),
            }
        } else {
            // No V-App has run yet on this VM instance: there is nothing to count.
            assert_eq!(probe_sw, StatusWord::IncorrectData, "unexpected GetMetrics status");
            assert_ne!(sw, StatusWord::InterruptedExecution, "GetMetrics refused while the V-App is interrupted");
            TraceSample { t_ms, phase, vm_state: "no_vapp", instructions: 0, page_loads: 0, page_commits: 0 }
        };
        self.samples.lock().unwrap().push(sample);
        Ok((sw, data))
    }
}

async fn http_get(port: u16, path: &str) -> Option<Vec<u8>> {
    let mut s = tokio::net::TcpStream::connect(("127.0.0.1", port)).await.ok()?;
    let req = format!("GET {} HTTP/1.0\r\nHost: 127.0.0.1\r\n\r\n", path);
    s.write_all(req.as_bytes()).await.ok()?;
    let mut buf = Vec::new();
    s.read_to_end(&mut buf).await.ok()?;
    if !(buf.starts_with(b"HTTP/1.0 200") || buf.starts_with(b"HTTP/1.1 200")) {
        return None;
    }
    let pos = buf.windows(4).position(|w| w == b"\r\n\r\n")?;
    Some(buf[pos + 4..].to_vec())
}

// Saves the Speculos screen every time it changes, as `f<microseconds since t0>.png`.
async fn record_screen(api_port: u16, t0: Instant, dir: String) {
    let mut last: Vec<u8> = Vec::new();
    loop {
        if let Some(png) = http_get(api_port, "/screenshot").await {
            if !png.is_empty() && png != last {
                let t_us = t0.elapsed().as_micros();
                std::fs::write(format!("{}/f{:010}.png", dir, t_us), &png).unwrap();
                last = png;
            }
        }
        sleep(Duration::from_millis(100)).await;
    }
}

struct TraceRun {
    wall_ms: f64,
    samples: Vec<TraceSample>,
}

async fn run_trace(vanadium_bin: &str, vapp_bin: &str, frames_dir: Option<&str>) -> TraceRun {
    let (mut child, tcp, api_port) = spawn_speculos(vanadium_bin).await;
    let t0 = Instant::now();
    let recorder = frames_dir.map(|dir| {
        std::fs::create_dir_all(dir).unwrap();
        tokio::spawn(record_screen(api_port, t0, dir.to_string()))
    });
    let transport = Arc::new(TracingTransport {
        inner: tcp,
        t0,
        gate: tokio::sync::Mutex::new(()),
        phase: std::sync::Mutex::new("app_start"),
        samples: std::sync::Mutex::new(Vec::new()),
    });
    let dyn_transport: Arc<dyn Transport<Error = Box<dyn std::error::Error + Send + Sync>>> = transport.clone();

    let vapp_client = VanadiumAppClient::with_vapp(vapp_bin, dyn_transport, Box::new(Sink::default()), false)
        .await
        .expect("VanadiumAppClient::with_vapp");
    let mut client = BitcoinClient::new(Box::new(vapp_client));

    let phase_transport = transport.clone();
    sign_transaction_flow(&mut client, &move |phase| phase_transport.set_phase(phase)).await;

    transport.set_phase("exit");
    let status = client.exit().await.expect("client.exit");
    assert_eq!(status, 0);
    let wall_ms = t0.elapsed().as_secs_f64() * 1000.0;
    drop(client);

    if let Some(recorder) = recorder {
        // leave the recorder a little longer to catch the final screen
        sleep(Duration::from_millis(300)).await;
        recorder.abort();
    }
    let _ = child.kill();
    let _ = child.wait();

    let samples = std::mem::take(&mut *transport.samples.lock().unwrap());
    TraceRun { wall_ms, samples }
}

fn trace_run_json(seq: usize, variant: &str, vapp_bin: &str, run: &TraceRun) -> String {
    let mut out = format!(
        "{{\"seq\":{},\"variant\":\"{}\",\"elf\":\"{}\",\"wall_ms\":{:.3},\"apdu_exchanges\":{},\"samples\":[\n",
        seq, variant, vapp_bin, run.wall_ms, run.samples.len()
    );
    for (i, s) in run.samples.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        out.push_str(&format!(
            "{{\"t_ms\":{:.3},\"phase\":\"{}\",\"apdu_index\":{},\"rv32_instructions\":{},\"vm_page_loads\":{},\"vm_page_commits\":{},\"vm_state\":\"{}\"}}",
            s.t_ms, s.phase, i, s.instructions, s.page_loads, s.page_commits, s.vm_state
        ));
    }
    out.push_str("\n]}\n");
    out
}

fn print_stats(wl: &str, times: &mut [f64], last: &WorkloadResult, idx: usize) {
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = times.len();
    let median_ms = times[n / 2];
    let min_ms = times[0];
    let mean_ms = times.iter().sum::<f64>() / (n as f64);
    if idx > 0 { print!(","); }
    print!(
        "\"{}\":{{\"median_ms\":{:.2},\"min_ms\":{:.2},\"mean_ms\":{:.2},\"apdu_exchanges\":{},\"bytes_sent\":{},\"bytes_received\":{}",
        wl, median_ms, min_ms, mean_ms, last.apdu_exchanges, last.bytes_sent, last.bytes_received
    );
    if let (Some(ic), Some(pl), Some(pc)) = (last.instruction_count, last.page_loads, last.page_commits) {
        print!(",\"rv32_instructions\":{},\"page_loads\":{},\"page_commits\":{}", ic, pl, pc);
    }
    if let (Some(ch), Some(ph)) = (last.current_heap_bytes, last.peak_heap_bytes) {
        print!(",\"current_heap_bytes\":{},\"peak_heap_bytes\":{}", ch, ph);
    }
    print!("}}");
}

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    let workloads = ["get_fingerprint", "sign_transaction", "send_to_silent_payment", "silent_payment_account"];

    // Interleaved ABBA comparison mode: `--abba <vm_bin> <ref_vapp> <lean_vapp> <pairs>`
    // Runs warm-up + `pairs` interleaved A-B-B-A cycles (2 * pairs samples per binary) to cancel host drift.
    if args.get(1).map(|s| s.as_str()) == Some("--abba") {
        let vanadium_bin = &args[2];
        let ref_vapp = &args[3];
        let lean_vapp = &args[4];
        let pairs: usize = args[5].parse().unwrap();
        let samples = pairs * 2;
        print!("{{\"mode\":\"ABBA\",\"pairs\":{},\"samples_per_variant\":{},\"reference\":{{\"runs\":{},\"workloads\":{{", pairs, samples, samples);
        let mut ref_all: Vec<(Vec<f64>, WorkloadResult)> = Vec::with_capacity(workloads.len());
        let mut lean_all: Vec<(Vec<f64>, WorkloadResult)> = Vec::with_capacity(workloads.len());
        for wl in workloads.iter() {
            // Unmeasured warm-up pair (A then B)
            let _ = run_workload(vanadium_bin, ref_vapp, wl, false, false).await;
            let _ = run_workload(vanadium_bin, lean_vapp, wl, false, false).await;

            let mut ref_times = Vec::with_capacity(samples);
            let mut lean_times = Vec::with_capacity(samples);
            let mut ref_last = WorkloadResult::default();
            let mut lean_last = WorkloadResult::default();
            for _ in 0..pairs {
                let ra1 = run_workload(vanadium_bin, ref_vapp, wl, false, false).await;
                let rb1 = run_workload(vanadium_bin, lean_vapp, wl, false, false).await;
                let rb2 = run_workload(vanadium_bin, lean_vapp, wl, false, false).await;
                let ra2 = run_workload(vanadium_bin, ref_vapp, wl, false, false).await;
                ref_times.push(ra1.wall_ms);
                ref_times.push(ra2.wall_ms);
                lean_times.push(rb1.wall_ms);
                lean_times.push(rb2.wall_ms);
                ref_last = ra2;
                lean_last = rb2;
            }
            ref_all.push((ref_times, ref_last));
            lean_all.push((lean_times, lean_last));
        }
        for (idx, wl) in workloads.iter().enumerate() {
            let (ref mut times, ref last) = ref_all[idx];
            print_stats(wl, times, last, idx);
        }
        print!("}}}},\"lean_optimized\":{{\"runs\":{},\"workloads\":{{", samples);
        for (idx, wl) in workloads.iter().enumerate() {
            let (ref mut times, ref last) = lean_all[idx];
            print_stats(wl, times, last, idx);
        }
        println!("}}}}}}");
        return;
    }

    // Per-APDU trace mode: `--trace <metrics_vm_bin> <runs> <out_dir> <variant>=<vapp_elf>...`
    // One unmeasured warm-up run per variant, then `runs` cycles over the variants, every other
    // cycle in reverse order (A B C, C B A, A B C, ...) to cancel host drift.
    if args.get(1).map(|s| s.as_str()) == Some("--trace") {
        let vanadium_bin = &args[2];
        let runs: usize = args[3].parse().unwrap();
        let out_dir = &args[4];
        let variants: Vec<(&str, &str)> = args[5..]
            .iter()
            .map(|a| a.split_once('=').expect("expected <variant>=<vapp_elf>"))
            .collect();
        std::fs::create_dir_all(out_dir).unwrap();
        for (_, vapp_bin) in variants.iter() {
            let _ = run_trace(vanadium_bin, vapp_bin, None).await;
        }
        let mut seq = 0;
        for cycle in 0..runs {
            let mut order = variants.clone();
            if cycle % 2 == 1 {
                order.reverse();
            }
            for (variant, vapp_bin) in order {
                let frames_dir = format!("{}/frames/run-{:02}-{}", out_dir, seq, variant);
                let run = run_trace(vanadium_bin, vapp_bin, Some(&frames_dir)).await;
                let last = run.samples.last().expect("no APDU exchanged");
                eprintln!(
                    "  [trace] run {:02} {:<18} {} APDUs, {} instructions, {} page loads, {} page commits, {:.0} ms",
                    seq, variant, run.samples.len(), last.instructions, last.page_loads, last.page_commits, run.wall_ms
                );
                std::fs::write(
                    format!("{}/run-{:02}-{}.json", out_dir, seq, variant),
                    trace_run_json(seq, variant, vapp_bin, &run),
                )
                .unwrap();
                seq += 1;
            }
        }
        return;
    }

    let vanadium_bin = &args[1];
    let vapp_bin = &args[2];
    let runs: usize = args[3].parse().unwrap();
    let with_metrics = args.iter().any(|a| a == "--metrics");
    let query_heap = args.iter().any(|a| a == "--heap");

    print!("{{\"runs\":{},\"workloads\":{{", runs);
    for (idx, wl) in workloads.iter().enumerate() {
        let mut times = Vec::with_capacity(runs);
        let mut last = WorkloadResult::default();
        for _ in 0..runs {
            let r = run_workload(vanadium_bin, vapp_bin, wl, with_metrics, query_heap).await;
            times.push(r.wall_ms);
            last = r;
        }
        print_stats(wl, &mut times, &last, idx);
    }
    println!("}}}}");
}
EOF

# Reuse cargo cache in /tmp/w4-bench-driver-cache for fast rebuilds
CARGO_TARGET_DIR=/tmp/w4-bench-driver-cache cargo build --release --quiet --manifest-path "$WORK_TMP/driver/Cargo.toml"
DRIVER_BIN="/tmp/w4-bench-driver-cache/release/vanadium-e2e-bench"

VM_RELEASE_BIN="$VANADIUM_REF/vm/target/flex/release/app-vanadium"
REF_VAPP_PATH="$WORK_TMP/elfs/ref_auto/target/ref_auto.elf"
LEAN_VAPP_PATH="$WORK_TMP/elfs/lean_auto/target/lean_auto.elf"
SAMEPROF_VAPP_PATH="$WORK_TMP/elfs/sameprof_auto/target/sameprof_auto.elf"

if [[ -n "${TRACE_OUT_DIR:-}" ]]; then
  TRACE_RUNS="${TRACE_RUNS:-3}"
  if [[ -e "$TRACE_OUT_DIR/elfs" ]]; then
    echo "TRACE_OUT_DIR=$TRACE_OUT_DIR already holds frozen ELFs; use a fresh directory" >&2
    exit 1
  fi
  echo "[trace] Freezing and hashing the V-App ELFs and the metrics VM -> $TRACE_OUT_DIR/elfs ..."
  mkdir -p "$TRACE_OUT_DIR/elfs"
  cp "$REF_VAPP_PATH" "$TRACE_OUT_DIR/elfs/reference.elf"
  cp "$LEAN_VAPP_PATH" "$TRACE_OUT_DIR/elfs/lean_optimized.elf"
  cp "$SAMEPROF_VAPP_PATH" "$TRACE_OUT_DIR/elfs/same_profile_lean.elf"
  cp "$VM_METRICS_BIN" "$TRACE_OUT_DIR/elfs/app-vanadium-live-metrics"
  cp "$WORK_TMP/driver/src/main.rs" "$TRACE_OUT_DIR/driver_main.rs"
  (cd "$TRACE_OUT_DIR/elfs" && sha256sum reference.elf lean_optimized.elf same_profile_lean.elf app-vanadium-live-metrics | tee SHA256SUMS)
  chmod a-w "$TRACE_OUT_DIR"/elfs/*
  echo "[trace] sign_transaction, $TRACE_RUNS runs per variant, VM counters sampled after every APDU exchange..."
  "$DRIVER_BIN" --trace "$TRACE_OUT_DIR/elfs/app-vanadium-live-metrics" "$TRACE_RUNS" "$TRACE_OUT_DIR" \
    "reference=$TRACE_OUT_DIR/elfs/reference.elf" \
    "lean_optimized=$TRACE_OUT_DIR/elfs/lean_optimized.elf" \
    "same_profile_lean=$TRACE_OUT_DIR/elfs/same_profile_lean.elf"
  (cd "$TRACE_OUT_DIR/elfs" && sha256sum --check --quiet SHA256SUMS)
  echo "[trace] Raw runs written to $TRACE_OUT_DIR; assemble with benchmarks/vanadium_trace.py"
  exit 0
fi

echo "[5/6] Running ABBA interleaved Speculos Flex E2E latency ($E2E_RUNS ABBA pairs = $((E2E_RUNS * 2)) samples/variant) + exact RV32 VM & peak_heap_bytes metrics..."
ABBA_LAT_JSON="$("$DRIVER_BIN" --abba "$VM_RELEASE_BIN" "$REF_VAPP_PATH" "$LEAN_VAPP_PATH" "$E2E_RUNS")"
REF_MET_JSON="$("$DRIVER_BIN" "$VM_METRICS_BIN" "$REF_VAPP_PATH" 1 --metrics)"
LEAN_MET_JSON="$("$DRIVER_BIN" "$VM_METRICS_BIN" "$LEAN_VAPP_PATH" 1 --metrics)"
SAMEPROF_MET_JSON="$("$DRIVER_BIN" "$VM_METRICS_BIN" "$SAMEPROF_VAPP_PATH" 1 --metrics)"
LEAN_HEAP_JSON="$("$DRIVER_BIN" "$VM_METRICS_BIN" "$LEAN_VAPP_PATH" 1 --heap)"
SAMEPROF_HEAP_JSON="$("$DRIVER_BIN" "$VM_METRICS_BIN" "$SAMEPROF_VAPP_PATH" 1 --heap)"

echo "[6/6] Assembling complete JSON results -> $OUT_JSON..."
python3 - "$WORK_TMP" "$OUT_JSON" "$HOST_BENCH_JSON" "$ABBA_LAT_JSON" "$REF_MET_JSON" "$LEAN_MET_JSON" "$SAMEPROF_MET_JSON" "$LEAN_HEAP_JSON" "$SAMEPROF_HEAP_JSON" "$REPO_ROOT" << 'PY'
import json, math, os, re, subprocess, sys

work_tmp, out_json, host_json, abba_lat, ref_met, lean_met, sameprof_met, lean_heap, sameprof_heap, repo_root = sys.argv[1:11]

def parse_elf(elf_path, stack_size):
    elf_bytes = os.path.getsize(elf_path)
    ph = subprocess.check_output(["readelf", "-l", elf_path], text=True)
    loads = []
    for line in ph.splitlines():
        m = re.match(r"\s*LOAD\s+0x[0-9a-fA-F]+\s+0x([0-9a-fA-F]+)\s+0x[0-9a-fA-F]+\s+0x([0-9a-fA-F]+)\s+0x([0-9a-fA-F]+)\s+([RWE ]{3})", line)
        if m:
            loads.append({
                "vaddr": int(m.group(1), 16),
                "filesz": int(m.group(2), 16),
                "memsz": int(m.group(3), 16),
                "flags": m.group(4).strip(),
            })
    assert len(loads) == 2, f"Expected exact 2 PT_LOAD segments, got {len(loads)}"
    rx = loads[0]
    rw = loads[1]

    sa = subprocess.check_output(["llvm-size", "-A", elf_path], text=True)
    secs = {}
    for line in sa.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0].startswith("."):
            try:
                secs[parts[0]] = int(parts[1])
            except ValueError:
                pass

    n_code_pages = math.ceil(rx["memsz"] / 256)
    n_data_pages = math.ceil(rw["memsz"] / 256)
    n_stack_pages = math.ceil(stack_size / 256)
    return {
        "elf_file_bytes": elf_bytes,
        "pt_load_segments": len(loads),
        "load_rx_bytes": rx["memsz"],
        "load_rw_ram_bytes": rw["memsz"],
        "load_rw_filesz_bytes": rw["filesz"],
        "stack_bytes": stack_size,
        "total_vapp_ram_bytes": rw["memsz"] + stack_size,
        "text_bytes": secs.get(".text", 0),
        "rodata_bytes": secs.get(".rodata", 0),
        "eh_frame_bytes": secs.get(".eh_frame", 0),
        "data_bytes": secs.get(".data", 0),
        "bss_bytes": secs.get(".bss", 0),
        "n_code_pages_256b": n_code_pages,
        "code_merkle_tree_depth": math.ceil(math.log2(max(1, n_code_pages))),
        "n_data_pages_256b": n_data_pages,
        "n_stack_pages_256b": n_stack_pages,
    }

def merge_e2e(lat_obj, met_obj, heap_obj=None):
    out = {}
    for wl, ldata in lat_obj["workloads"].items():
        mdata = met_obj["workloads"][wl]
        entry = {
            "wall_median_ms": ldata["median_ms"],
            "wall_min_ms": ldata["min_ms"],
            "wall_mean_ms": ldata["mean_ms"],
            "apdu_exchanges": ldata["apdu_exchanges"],
            "apdu_bytes_sent": ldata["bytes_sent"],
            "apdu_bytes_received": ldata["bytes_received"],
            "rv32_instructions": mdata["rv32_instructions"],
            "vm_page_loads": mdata["page_loads"],
            "vm_page_commits": mdata["page_commits"],
        }
        if heap_obj is not None:
            hdata = heap_obj["workloads"].get(wl, {})
            if "peak_heap_bytes" in hdata:
                entry["peak_heap_bytes"] = hdata["peak_heap_bytes"]
                entry["current_heap_bytes"] = hdata["current_heap_bytes"]
        out[wl] = entry
    return out

su_path = os.path.join(repo_root, "ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.su")
su_frames = []
if os.path.exists(su_path):
    with open(su_path) as f:
        for line in f:
            parts = line.strip().split("\t")
            if len(parts) >= 2:
                fn_name = parts[0].split(":")[-1]
                frame_bytes = int(parts[1].split()[0])
                su_frames.append({"symbol": fn_name, "stack_frame_bytes": frame_bytes})

ref_plain = parse_elf(os.path.join(work_tmp, "elfs/ref_plain.elf"), 65536)
ref_auto = parse_elf(os.path.join(work_tmp, "elfs/ref_auto.elf"), 65536)
lean_plain = parse_elf(os.path.join(work_tmp, "elfs/lean_plain.elf"), 32768)
lean_auto = parse_elf(os.path.join(work_tmp, "elfs/lean_auto.elf"), 32768)
same_plain = parse_elf(os.path.join(work_tmp, "elfs/sameprof_plain.elf"), 65536)
same_auto = parse_elf(os.path.join(work_tmp, "elfs/sameprof_auto.elf"), 65536)

abba = json.loads(abba_lat)
ref_e2e = merge_e2e(abba["reference"], json.loads(ref_met))
lean_e2e = merge_e2e(abba["lean_optimized"], json.loads(lean_met), json.loads(lean_heap))
same_e2e = merge_e2e(json.loads(sameprof_met), json.loads(sameprof_met), json.loads(sameprof_heap))

summary_deltas = {
    "plain_production_vapp": {
        "load_rx_delta_bytes": lean_plain["load_rx_bytes"] - ref_plain["load_rx_bytes"],
        "load_rx_delta_pct": round(100.0 * (lean_plain["load_rx_bytes"] - ref_plain["load_rx_bytes"]) / ref_plain["load_rx_bytes"], 2),
        "elf_file_delta_bytes": lean_plain["elf_file_bytes"] - ref_plain["elf_file_bytes"],
        "elf_file_delta_pct": round(100.0 * (lean_plain["elf_file_bytes"] - ref_plain["elf_file_bytes"]) / ref_plain["elf_file_bytes"], 2),
        "load_rw_ram_delta_bytes": lean_plain["load_rw_ram_bytes"] - ref_plain["load_rw_ram_bytes"],
        "load_rw_ram_delta_pct": round(100.0 * (lean_plain["load_rw_ram_bytes"] - ref_plain["load_rw_ram_bytes"]) / ref_plain["load_rw_ram_bytes"], 2),
        "total_vapp_ram_delta_bytes": lean_plain["total_vapp_ram_bytes"] - ref_plain["total_vapp_ram_bytes"],
        "total_vapp_ram_delta_pct": round(100.0 * (lean_plain["total_vapp_ram_bytes"] - ref_plain["total_vapp_ram_bytes"]) / ref_plain["total_vapp_ram_bytes"], 2),
    },
    "autoapprove_e2e_vapp": {
        "load_rx_delta_bytes": lean_auto["load_rx_bytes"] - ref_auto["load_rx_bytes"],
        "load_rx_delta_pct": round(100.0 * (lean_auto["load_rx_bytes"] - ref_auto["load_rx_bytes"]) / ref_auto["load_rx_bytes"], 2),
        "elf_file_delta_bytes": lean_auto["elf_file_bytes"] - ref_auto["elf_file_bytes"],
        "elf_file_delta_pct": round(100.0 * (lean_auto["elf_file_bytes"] - ref_auto["elf_file_bytes"]) / ref_auto["elf_file_bytes"], 2),
        "load_rw_ram_delta_bytes": lean_auto["load_rw_ram_bytes"] - ref_auto["load_rw_ram_bytes"],
        "load_rw_ram_delta_pct": round(100.0 * (lean_auto["load_rw_ram_bytes"] - ref_auto["load_rw_ram_bytes"]) / ref_auto["load_rw_ram_bytes"], 2),
    },
    "same_profile_plain_vapp": {
        "load_rx_delta_bytes": same_plain["load_rx_bytes"] - ref_plain["load_rx_bytes"],
        "load_rx_delta_pct": round(100.0 * (same_plain["load_rx_bytes"] - ref_plain["load_rx_bytes"]) / ref_plain["load_rx_bytes"], 2),
        "elf_file_delta_bytes": same_plain["elf_file_bytes"] - ref_plain["elf_file_bytes"],
        "elf_file_delta_pct": round(100.0 * (same_plain["elf_file_bytes"] - ref_plain["elf_file_bytes"]) / ref_plain["elf_file_bytes"], 2),
    },
    "speculos_flex_e2e_deltas": {
        wl: {
            "wall_median_delta_ms": round(lean_e2e[wl]["wall_median_ms"] - ref_e2e[wl]["wall_median_ms"], 2),
            "wall_median_delta_pct": round(100.0 * (lean_e2e[wl]["wall_median_ms"] - ref_e2e[wl]["wall_median_ms"]) / ref_e2e[wl]["wall_median_ms"], 2),
            "rv32_instructions_delta": lean_e2e[wl]["rv32_instructions"] - ref_e2e[wl]["rv32_instructions"],
            "rv32_instructions_delta_pct": round(100.0 * (lean_e2e[wl]["rv32_instructions"] - ref_e2e[wl]["rv32_instructions"]) / ref_e2e[wl]["rv32_instructions"], 2),
            "vm_page_loads_delta": lean_e2e[wl]["vm_page_loads"] - ref_e2e[wl]["vm_page_loads"],
            "vm_page_loads_delta_pct": round(100.0 * (lean_e2e[wl]["vm_page_loads"] - ref_e2e[wl]["vm_page_loads"]) / ref_e2e[wl]["vm_page_loads"], 2),
            "apdu_exchanges_delta": lean_e2e[wl]["apdu_exchanges"] - ref_e2e[wl]["apdu_exchanges"],
            "apdu_exchanges_delta_pct": round(100.0 * (lean_e2e[wl]["apdu_exchanges"] - ref_e2e[wl]["apdu_exchanges"]) / ref_e2e[wl]["apdu_exchanges"], 2),
            "apdu_bytes_sent_delta": lean_e2e[wl]["apdu_bytes_sent"] - ref_e2e[wl]["apdu_bytes_sent"],
            "apdu_bytes_sent_delta_pct": round(100.0 * (lean_e2e[wl]["apdu_bytes_sent"] - ref_e2e[wl]["apdu_bytes_sent"]) / ref_e2e[wl]["apdu_bytes_sent"], 2),
        }
        for wl in ref_e2e
    },
}

doc = {
    "benchmark_suite": "vanadium-bitcoin-vapp-wave4",
    "measurement_host": {
        "environment": os.environ.get("BENCHMARK_HOST_CLASS", "unspecified"),
        "same_host_reference_and_lean": True,
    },
    "upstream_reference_commit": "ace8e96982408959dea9e7fbc59ee36e8c54e645",
    "target_isa": "riscv32imac-unknown-none-elf",
    "device_model": "Ledger Flex (Speculos --model flex, 480x600 E-Ink)",
    "lean_freestanding_kernels": {
        "version_packed": "0x00020401",
        "exported_symbols": sum(1 for line in subprocess.check_output(["llvm-nm", "--defined-only", "--extern-only", os.path.join(repo_root, "ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a")], text=True).splitlines() if line.split() and line.split()[-1].startswith("llb_")),
        "stack_frame_count": len(su_frames),
        "max_stack_frame_bytes": max((x["stack_frame_bytes"] for x in su_frames), default=0),
        "frames": su_frames,
    },
    "storage_and_ram": {
        "reference_plain": ref_plain,
        "lean_optimized_plain": lean_plain,
        "same_profile_lean_plain": same_plain,
        "reference_autoapprove": ref_auto,
        "lean_optimized_autoapprove": lean_auto,
        "same_profile_lean_autoapprove": same_auto,
    },
    "speculos_flex_e2e": {
        "protocol": "ABBA interleaved (1 unmeasured warm-up pair + N A-B-B-A cycles; identical spawn_task + display_transaction + await_task path across plain and autoapprove)",
        "abba_pairs_per_workload": abba["pairs"],
        "runs_per_workload": abba["samples_per_variant"],
        "reference": ref_e2e,
        "lean_optimized": lean_e2e,
        "same_profile_lean": same_e2e,
    },
    "host_microbenchmarks": json.loads(host_json),
    "summary_deltas": summary_deltas,
}

os.makedirs(os.path.dirname(out_json), exist_ok=True)
with open(out_json, "w") as f:
    json.dump(doc, f, indent=2)
print(f"Wrote {out_json}")
PY

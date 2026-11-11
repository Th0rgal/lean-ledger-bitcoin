//! build.rs — links the turbo-lean-emitted `lean-ledger-bitcoin` freestanding
//! archive into the `llb-vanadium-ffi` crate:
//!
//! * `target_arch = "riscv32"` (Vanadium V-App, `riscv32imac-unknown-none-elf`):
//!   `ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a`
//! * any other (host) target — used by `cargo test` on the development host:
//!   `ffi/vanadium/build/host/liblean_ledger_bitcoin.a`
//!
//! Both archives are produced by `scripts/build-freestanding.sh`; the script
//! fails fast with a pointer to it when they are missing.

use std::env;
use std::path::PathBuf;
use std::process::Command;

const LIB_NAME: &str = "liblean_ledger_bitcoin";
const LINK_NAME: &str = "lean_ledger_bitcoin";

fn try_auto_emit(manifest_dir: &PathBuf, dir: &PathBuf, target: &str) {
    let repo_root = manifest_dir.join("..").join("..");
    let kernel = repo_root.join("BitcoinLedger").join("FreestandingKernels.lean");
    if !kernel.is_file() {
        return;
    }

    let lean_native = env::var("LEAN_NATIVE")
        .ok()
        .map(PathBuf::from)
        .filter(|p| p.is_file())
        .or_else(|| {
            let sibling = repo_root
                .join("..")
                .join("turbo-lean")
                .join("lean")
                .join(".lake")
                .join("build")
                .join("bin")
                .join("lean-native");
            sibling.is_file().then_some(sibling)
        })
        .unwrap_or_else(|| {
            let hub = env::var("LEDGER_HUB")
                .unwrap_or_else(|_| "/var/lib/orb-node/work/caches/ledger-hub".to_string());
            PathBuf::from(hub)
                .join("turbo-lean")
                .join("lean")
                .join(".lake")
                .join("build")
                .join("bin")
                .join("lean-native")
        });
    if !lean_native.is_file() {
        return;
    }

    let _ = std::fs::create_dir_all(dir);
    let emit_tag = if target.starts_with("riscv32") {
        "riscv32imac"
    } else {
        "x86_64"
    };
    let archive = dir.join(format!("{}.a", LIB_NAME));
    let _ = Command::new(&lean_native)
        .current_dir(&repo_root)
        .args([
            "emit-freestanding-c-lib",
            "--input",
            "BitcoinLedger/FreestandingKernels.lean",
            "--target",
            emit_tag,
            "--clang-bin",
            "clang",
            "-o",
            archive.to_str().unwrap(),
            "--json",
        ])
        .status();

    // On RV32IMAC, re-compile the freestanding LLVM IR with `-Oz -ffunction-sections -fdata-sections`
    // so `--gc-sections` / LTO discards unused BOLOS-only kernel symbols while keeping 0-byte frames.
    if target.starts_with("riscv32") {
        let ll = dir.join(format!("{}.ll", LIB_NAME));
        let obj = dir.join(format!("{}.o", LIB_NAME));
        if ll.is_file() {
            let status = Command::new("clang")
                .args([
                    "--target=riscv32-unknown-none-elf",
                    "-march=rv32imac",
                    "-mabi=ilp32",
                    "-Oz",
                    "-ffunction-sections",
                    "-fdata-sections",
                    "-fno-unwind-tables",
                    "-fno-asynchronous-unwind-tables",
                    "-c",
                    ll.to_str().unwrap(),
                    "-o",
                    obj.to_str().unwrap(),
                ])
                .status();
            if matches!(status, Ok(s) if s.success()) {
                let _ = std::fs::remove_file(&archive);
                let ar_bin = if Command::new("llvm-ar").arg("--version").output().is_ok() {
                    "llvm-ar"
                } else {
                    "ar"
                };
                let _ = Command::new(ar_bin)
                    .args(["rcs", archive.to_str().unwrap(), obj.to_str().unwrap()])
                    .status();
            }
        }
    }
}

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let target = env::var("TARGET").unwrap_or_default();

    // The 32-bit ILP32 Vanadium target links the riscv32imac freestanding
    // archive; everything else (host tests) links the host emission.
    let tag = if target.starts_with("riscv32") {
        "riscv32imac"
    } else {
        "host"
    };
    let dir = manifest_dir.join("build").join(tag);
    let archive = dir.join(format!("{}.a", LIB_NAME));

    if !archive.is_file() {
        try_auto_emit(&manifest_dir, &dir, &target);
    } else if target.starts_with("riscv32") {
        // Ensure existing RV32 archive uses -ffunction-sections -fno-unwind-tables if .ll is present
        let ll = dir.join(format!("{}.ll", LIB_NAME));
        let marker = dir.join(".oz_gc_built");
        if ll.is_file() && !marker.is_file() {
            try_auto_emit(&manifest_dir, &dir, &target);
            let _ = std::fs::write(&marker, b"1");
        }
    }

    if !archive.is_file() {
        panic!(
            "llb-vanadium-ffi: missing freestanding archive {} for target '{}'. \
             Run scripts/build-freestanding.sh from the repository root first.",
            archive.display(),
            target
        );
    }

    println!("cargo:rerun-if-changed={}", archive.display());
    println!("cargo:rustc-link-search=native={}", dir.display());
    println!("cargo:rustc-link-lib=static={}", LINK_NAME);
}

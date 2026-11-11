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

const LIB_NAME: &str = "lean_ledger_bitcoin"; // liblean_ledger_bitcoin.a

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
    let archive = dir.join(format!("lib{}.a", LIB_NAME));

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
    println!("cargo:rustc-link-lib=static={}", LIB_NAME);
}

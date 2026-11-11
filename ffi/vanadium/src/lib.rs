//! `llb-vanadium-ffi` — thin Vanadium Rust/C FFI crate for the
//! `lean-ledger-bitcoin` freestanding kernels.
//!
//! The crate links the `turbo-lean`-emitted static archive
//! (`liblean_ledger_bitcoin.a`) via `extern "C"` — the `riscv32imac` emission
//! on `target_arch = "riscv32"` (Vanadium V-App, RV32IMAC ILP32) and the host
//! emission everywhere else (development / `cargo test`) — and exposes safe,
//! `no_std`-compatible wrappers for the Vanadium Bitcoin V-App
//! (`apps/bitcoin/app`) ECALL boundary:
//!
//! * `ecall_derive_hd_node`, `ecall_get_master_fingerprint`
//! * `ecall_sha256` (via `hash_init` / `hash_update` / `hash_final`)
//! * `ecall_secp256k1_*` (`ecfp_add_point`, `ecfp_scalar_mult`, `ecdsa_sign`,
//!   `ecdsa_verify`, `schnorr_sign`, `schnorr_verify`, `get_random_bytes`)
//! * `ecall_xsend` / `ecall_xrecv`
//!
//! On RV32 the raw ECALLs are executed with the Vanadium V-App machine
//! convention (syscall number in `t0`, arguments in `a0..a7`, return value in
//! `a0`, exactly mirroring `LedgerHQ/vanadium` `ecalls/src/ecalls_impl.rs`).
//! On other targets the same surface is expressed as the [`RawEcalls`] trait
//! so host unit tests can drive the safe wrappers against test doubles while
//! the linked Lean kernel archive is checked through [`version_packed`].

#![cfg_attr(not(test), no_std)]
#![allow(clippy::missing_safety_doc)]

use core::fmt;

// ---------------------------------------------------------------------------
// Packed version contract (BitcoinLedger/FreestandingKernels.lean):
// (2 << 16) | (4 << 8) | 1 == 0x00020401
// ---------------------------------------------------------------------------

/// Packed kernel version this FFI crate is written against.
pub const VERSION_PACKED_EXPECTED: u32 = 0x0002_0401;
/// Kernel major version.
pub const VERSION_MAJOR: u32 = 2;
/// Kernel minor version.
pub const VERSION_MINOR: u32 = 4;
/// Kernel patch version.
pub const VERSION_PATCH: u32 = 1;

/// Consensus `MAX_MONEY` (`21_000_000 * 100_000_000 = 2_100_000_000_000_000` satoshis).
pub const MAX_MONEY_SATS: u64 = 2_100_000_000_000_000;

mod sys {
    extern "C" {
        /// turbo-lean-emitted freestanding kernel entries
        /// (`BitcoinLedger.FreestandingKernels.*`).
        pub fn llb_version_packed() -> u32;
        pub fn llb_valid_amount(sats: u64) -> u8;
        pub fn llb_checked_add_sats_ok(a: u64, b: u64) -> u8;
        pub fn llb_checked_add_sats_val(a: u64, b: u64) -> u64;
        pub fn llb_checked_sub_sats_ok(a: u64, b: u64) -> u8;
        pub fn llb_checked_sub_sats_val(a: u64, b: u64) -> u64;
        pub fn llb_varint_encoded_len(n: u64) -> u8;
        pub fn llb_varint_prefix_is_canonical(tag: u8, decoded_val: u64) -> u8;
        pub fn llb_bip32_is_hardened(idx: u32) -> u8;
        pub fn llb_bip32_harden(n: u32) -> u32;
        pub fn llb_bip32_unharden(idx: u32) -> u32;
        pub fn llb_bip32_bolos_depth_ok(depth: u8) -> u8;
        pub fn llb_bip32_vanadium_depth_ok(depth: u8) -> u8;
        pub fn llb_bip32_standard_purpose_ok(purpose_step: u32) -> u8;
        pub fn llb_witness_opcode_to_version(op: u8) -> u8;
        pub fn llb_segwit_program_valid(witver: u8, prog_len: u8) -> u8;
        pub fn llb_bech32_polymod_step(pre: u32, val: u8) -> u32;
        pub fn llb_minimal_push_opcode_ok(op: u8, first_byte: u8, push_len: u32) -> u8;
        pub fn llb_sighash_type_valid(sighash_u32: u32) -> u8;
        pub fn llb_taproot_sighash_valid(sighash_byte: u8) -> u8;
        pub fn llb_merkle_depth_index_ok(tree_size: u32, index: u32, depth: u8) -> u8;
        pub fn llb_bolos_sw_for_error(err_tag: u8) -> u16;
    }
}

/// Calls `llb_version_packed()` in the linked freestanding kernel archive.
///
/// Return value must always equal [`VERSION_PACKED_EXPECTED`]; use
/// [`check_kernel_version`] for the checked form.
pub fn version_packed() -> u32 {
    // SAFETY: pure freestanding function with no preconditions.
    unsafe { sys::llb_version_packed() }
}

/// Consensus satoshi range check (`0 <= sats <= MAX_MONEY`).
pub fn valid_amount(sats: u64) -> bool {
    // SAFETY: pure freestanding scalar function with no preconditions.
    unsafe { sys::llb_valid_amount(sats) != 0 }
}

/// Overflow-free satoshi addition in `[0, MAX_MONEY]`.
pub fn checked_add_sats(a: u64, b: u64) -> Option<u64> {
    // SAFETY: pure freestanding scalar functions with no preconditions.
    unsafe {
        if sys::llb_checked_add_sats_ok(a, b) != 0 {
            Some(sys::llb_checked_add_sats_val(a, b))
        } else {
            None
        }
    }
}

/// Underflow-free satoshi subtraction in `[0, MAX_MONEY]`.
pub fn checked_sub_sats(a: u64, b: u64) -> Option<u64> {
    // SAFETY: pure freestanding scalar functions with no preconditions.
    unsafe {
        if sys::llb_checked_sub_sats_ok(a, b) != 0 {
            Some(sys::llb_checked_sub_sats_val(a, b))
        } else {
            None
        }
    }
}

/// Canonical CompactSize / VarInt encoded byte length (`1`, `3`, `5`, or `9`).
pub fn varint_encoded_len(n: u64) -> u8 {
    unsafe { sys::llb_varint_encoded_len(n) }
}

/// Check whether a CompactSize prefix `tag` and `decoded_val` form a minimal encoding.
pub fn varint_prefix_is_canonical(tag: u8, decoded_val: u64) -> bool {
    unsafe { sys::llb_varint_prefix_is_canonical(tag, decoded_val) != 0 }
}

/// Check whether BIP-32 child index `idx` has the hardened bit (`0x8000_0000`) set.
pub fn bip32_is_hardened(idx: u32) -> bool {
    unsafe { sys::llb_bip32_is_hardened(idx) != 0 }
}

/// Set the BIP-32 hardened bit (`n | 0x8000_0000`).
pub fn bip32_harden(n: u32) -> u32 {
    unsafe { sys::llb_bip32_harden(n) }
}

/// Clear the BIP-32 hardened bit (`idx & 0x7FFF_FFFF`).
pub fn bip32_unharden(idx: u32) -> u32 {
    unsafe { sys::llb_bip32_unharden(idx) }
}

/// BOLOS standard BIP-32 path depth gate (`depth <= 10`).
pub fn bip32_bolos_depth_ok(depth: u8) -> bool {
    unsafe { sys::llb_bip32_bolos_depth_ok(depth) != 0 }
}

/// Vanadium `KeyTree::Standard` BIP-32 path depth gate (`depth <= 16`).
pub fn bip32_vanadium_depth_ok(depth: u8) -> bool {
    unsafe { sys::llb_bip32_vanadium_depth_ok(depth) != 0 }
}

/// Hardened standard 3-step BIP purpose check (`44'`, `49'`, `84'`, `86'`, `87'`, `45'`).
pub fn bip32_standard_purpose_ok(purpose_step: u32) -> bool {
    unsafe { sys::llb_bip32_standard_purpose_ok(purpose_step) != 0 }
}

/// Decode a Bitcoin Script witness-version opcode (`OP_0` -> `Some(0)`, `OP_1..OP_16` -> `Some(1..=16)`).
pub fn witness_opcode_to_version(op: u8) -> Option<u8> {
    let v = unsafe { sys::llb_witness_opcode_to_version(op) };
    if v == 0xFF { None } else { Some(v) }
}

/// Validate SegWit witness version & program length (`v0`: `20|32`, `v1..=16`: `2..=40`).
pub fn segwit_program_valid(witver: u8, prog_len: u8) -> bool {
    unsafe { sys::llb_segwit_program_valid(witver, prog_len) != 0 }
}

/// Single GF(32) generator-polynomial step for Bech32 / Bech32m `polymod`.
pub fn bech32_polymod_step(pre: u32, val: u8) -> u32 {
    unsafe { sys::llb_bech32_polymod_step(pre, val) }
}

/// Validate BIP-62 `MINIMALDATA` canonicality for `(op, first_byte, push_len)`.
pub fn minimal_push_opcode_ok(op: u8, first_byte: u8, push_len: u32) -> bool {
    unsafe { sys::llb_minimal_push_opcode_ok(op, first_byte, push_len) != 0 }
}

/// Validate a 32-bit non-Taproot sighash type (`0x01..=0x03`, `0x81..=0x83`).
pub fn sighash_type_valid(sighash_u32: u32) -> bool {
    unsafe { sys::llb_sighash_type_valid(sighash_u32) != 0 }
}

/// Validate a 1-byte BIP-341 Taproot sighash type (`0x00`, `0x01..=0x03`, `0x81..=0x83`).
pub fn taproot_sighash_valid(sighash_byte: u8) -> bool {
    unsafe { sys::llb_taproot_sighash_valid(sighash_byte) != 0 }
}

/// Validate Merkle inclusion-proof header bounds (`0 < tree_size`, `index < tree_size`, `depth <= 32`).
pub fn merkle_depth_index_ok(tree_size: u32, index: u32, depth: u8) -> bool {
    unsafe { sys::llb_merkle_depth_index_ok(tree_size, index, depth) != 0 }
}

/// Map compact `SpecError` discriminant tag (`0..=18`) to BOLOS 16-bit APDU status word.
pub fn bolos_sw_for_error(err_tag: u8) -> u16 {
    unsafe { sys::llb_bolos_sw_for_error(err_tag) }
}

/// Exercises all 22 freestanding C99 kernel exports from `liblean_ledger_bitcoin.a`
/// in `no_std` environments (e.g. Vanadium RV32IMAC V-App boot / request boundary).
pub fn kernel_self_test() -> bool {
    check_kernel_version().is_ok()
        && valid_amount(MAX_MONEY_SATS)
        && !valid_amount(MAX_MONEY_SATS + 1)
        && checked_add_sats(1_000_000, 2_500_000) == Some(3_500_000)
        && checked_add_sats(MAX_MONEY_SATS, 1).is_none()
        && checked_sub_sats(5_000_000, 1_500_000) == Some(3_500_000)
        && checked_sub_sats(100, 101).is_none()
        && varint_encoded_len(0xFC) == 1
        && varint_encoded_len(0xFD) == 3
        && varint_prefix_is_canonical(0xFD, 0xFD)
        && !varint_prefix_is_canonical(0xFD, 0xFC)
        && bip32_is_hardened(bip32_harden(86))
        && bip32_unharden(bip32_harden(86)) == 86
        && bip32_bolos_depth_ok(10)
        && !bip32_bolos_depth_ok(11)
        && bip32_vanadium_depth_ok(16)
        && !bip32_vanadium_depth_ok(17)
        && bip32_standard_purpose_ok(bip32_harden(86))
        && witness_opcode_to_version(0x51) == Some(1)
        && segwit_program_valid(1, 32)
        && bech32_polymod_step(1, 0) == 0x20
        && minimal_push_opcode_ok(0x01, 0x42, 1)
        && !minimal_push_opcode_ok(0x01, 0x05, 1)
        && sighash_type_valid(0x01)
        && !sighash_type_valid(0x00)
        && taproot_sighash_valid(0x00)
        && merkle_depth_index_ok(8, 3, 3)
        && bolos_sw_for_error(5) == 0x6985
}

/// Unpacked kernel version triple.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Version {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

/// Unpacks a packed version (as returned by [`version_packed`]).
pub fn unpack_version(packed: u32) -> Version {
    Version {
        major: packed >> 16,
        minor: (packed >> 8) & 0xFF,
        patch: packed & 0xFF,
    }
}

/// Verifies the linked kernel archive matches this FFI crate's version
/// contract (`0x00020401`).
pub fn check_kernel_version() -> Result<Version, VersionMismatch> {
    let packed = version_packed();
    if packed == VERSION_PACKED_EXPECTED {
        Ok(unpack_version(packed))
    } else {
        Err(VersionMismatch {
            linked: packed,
            expected: VERSION_PACKED_EXPECTED,
        })
    }
}

/// The linked freestanding kernel archive does not match this crate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VersionMismatch {
    pub linked: u32,
    pub expected: u32,
}

impl fmt::Display for VersionMismatch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "kernel version mismatch: linked 0x{:08x}, expected 0x{:08x}",
            self.linked, self.expected
        )
    }
}

// ---------------------------------------------------------------------------
// ECALL numbers and protocol constants
// (mirrors LedgerHQ/vanadium common/src/ecall_constants.rs @ ace8e96)
// ---------------------------------------------------------------------------

/// Vanadium ECALL syscall numbers.
pub mod ecall_nr {
    pub const XSEND: u32 = 2;
    pub const XRECV: u32 = 3;
    pub const DERIVE_HD_NODE: u32 = 130;
    pub const GET_MASTER_FINGERPRINT: u32 = 131;
    pub const HASH_INIT: u32 = 150;
    pub const HASH_UPDATE: u32 = 151;
    pub const HASH_DIGEST: u32 = 152;
    pub const ECFP_ADD_POINT: u32 = 160;
    pub const ECFP_SCALAR_MULT: u32 = 161;
    pub const GET_RANDOM_BYTES: u32 = 170;
    pub const ECDSA_SIGN: u32 = 180;
    pub const ECDSA_VERIFY: u32 = 181;
    pub const SCHNORR_SIGN: u32 = 182;
    pub const SCHNORR_VERIFY: u32 = 183;
}

/// Curve identifiers (`CurveKind`).
pub mod curve {
    /// secp256k1 (`CurveKind::Secp256k1`).
    pub const SECP256K1: u32 = 0x21;
}

/// Hash algorithm identifiers (`HashId`).
pub mod hash_id {
    pub const RIPEMD160: u32 = 1;
    pub const SHA256: u32 = 3;
    pub const SHA384: u32 = 4;
    pub const SHA512: u32 = 5;
    pub const KECCAK: u32 = 6;
    pub const SHA3: u32 = 7;
}

/// Composite `hash_id` for a `Sha256` ECALL with a 32-byte output
/// (`HashId::ecall_id(32)`: algorithm in bits 23-16, output size in bits 15-0).
pub const fn sha256_ecall_id(output_size: u16) -> u32 {
    ((hash_id::SHA256 as u32) << 16) | (output_size as u32)
}

/// Opaque SHA-256 hash-context size for the hash ECALLs
/// (`CTX_SHA256_SIZE`).
pub const CTX_SHA256_SIZE: usize = 128;

/// Signing modes (`EcdsaSignMode` / `SchnorrSignMode`).
pub mod sign_mode {
    /// Deterministic ECDSA nonce (RFC 6979): `EcdsaSignMode::RFC6979`.
    pub const ECDSA_RFC6979: u32 = 3 << 9;
    /// BIP-340 Schnorr signing: `SchnorrSignMode::BIP340`.
    pub const SCHNORR_BIP340: u32 = 0;
}

/// Size in bytes of a secp256k1 private key.
pub const SECP256K1_PRIVKEY_SIZE: usize = 32;
/// Size in bytes of an uncompressed secp256k1 public key (SEC1 `0x04 || x || y`).
pub const SECP256K1_PUBKEY_SIZE: usize = 65;
/// Size in bytes of an x-only (BIP-340) public key.
pub const SECP256K1_XONLY_PUBKEY_SIZE: usize = 32;
/// Maximum size in bytes of a DER-encoded ECDSA signature.
pub const MAX_DER_SIGNATURE_LEN: usize = 72;
/// Size in bytes of a BIP-340 Schnorr signature.
pub const SCHNORR_SIGNATURE_SIZE: usize = 64;

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Errors surfaced by the safe ECALL wrappers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EcallError {
    /// The ECALL reported failure (status 0 / unexpected status).
    EcallFailed(&'static str),
    /// A slice-based argument had the wrong length.
    InvalidSlice(&'static str),
}

impl fmt::Display for EcallError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EcallError::EcallFailed(what) => write!(f, "ecall failed: {}", what),
            EcallError::InvalidSlice(what) => write!(f, "invalid argument length: {}", what),
        }
    }
}

// ---------------------------------------------------------------------------
// Raw ECALL surface
// ---------------------------------------------------------------------------

/// Raw (pointer-level) mirror of the Vanadium ECALL boundary used by the
/// Bitcoin V-App. On RV32 it is implemented by [`machine::MachineEcalls`]
/// (real `ecall` instructions); host tests provide doubles.
///
/// # Safety
/// Implementations must uphold the pointer/length preconditions of each
/// method, exactly as documented for the corresponding Vanadium ECALL.
pub unsafe trait RawEcalls {
    /// ECALL_DERIVE_HD_NODE: writes 32-byte `privkey` and `chain_code`.
    /// Returns 1 on success, 0 on failure.
    unsafe fn derive_hd_node(
        &mut self,
        curve: u32,
        path: *const u32,
        path_len: usize,
        privkey: *mut u8,
        chain_code: *mut u8,
    ) -> u32;

    /// ECALL_GET_MASTER_FINGERPRINT: writes the master fingerprint.
    /// Returns 1 on success, 0 on failure.
    unsafe fn get_master_fingerprint(&mut self, curve: u32, fingerprint: *mut u32) -> u32;

    /// ECALL_HASH_INIT: initializes the opaque context.
    /// Returns 1 on success, 0 on failure.
    unsafe fn hash_init(&mut self, hash_id: u32, ctx: *mut u8) -> u32;

    /// ECALL_HASH_UPDATE: absorbs `len` bytes.
    /// Returns 1 on success, 0 on failure.
    unsafe fn hash_update(
        &mut self,
        hash_id: u32,
        ctx: *mut u8,
        data: *const u8,
        len: usize,
    ) -> u32;

    /// ECALL_HASH_DIGEST: writes the digest.
    /// Returns 1 on success, 0 on failure.
    unsafe fn hash_final(&mut self, hash_id: u32, ctx: *mut u8, digest: *mut u8) -> u32;

    /// ECALL_ECFP_ADD_POINT: 65-byte uncompressed points.
    /// Returns 1 on success, 0 on failure.
    unsafe fn ecfp_add_point(
        &mut self,
        curve: u32,
        r: *mut u8,
        p: *const u8,
        q: *const u8,
    ) -> u32;

    /// ECALL_ECFP_SCALAR_MULT: 65-byte point, big-endian scalar (`k_len <= 32`).
    /// Returns 1 on success, 0 on failure.
    unsafe fn ecfp_scalar_mult(
        &mut self,
        curve: u32,
        r: *mut u8,
        p: *const u8,
        k: *const u8,
        k_len: usize,
    ) -> u32;

    /// ECALL_GET_RANDOM_BYTES. Returns 1 on success, 0 on failure.
    unsafe fn get_random_bytes(&mut self, buffer: *mut u8, size: usize) -> u32;

    /// ECALL_ECDSA_SIGN: DER signature, low-S, RFC 6979 nonce.
    /// Returns the signature length on success, 0 on failure.
    unsafe fn ecdsa_sign(
        &mut self,
        curve: u32,
        mode: u32,
        hash_id: u32,
        privkey: *const u8,
        msg_hash: *const u8,
        signature: *mut u8,
    ) -> usize;

    /// ECALL_ECDSA_VERIFY: strict BIP-66 DER signature.
    /// Returns 1 if valid, 0 otherwise.
    unsafe fn ecdsa_verify(
        &mut self,
        curve: u32,
        pubkey: *const u8,
        msg_hash: *const u8,
        signature: *const u8,
        signature_len: usize,
    ) -> u32;

    /// ECALL_SCHNORR_SIGN: BIP-340, `entropy` may be null for fresh randomness.
    /// Returns 64 on success, 0 on failure.
    unsafe fn schnorr_sign(
        &mut self,
        curve: u32,
        mode: u32,
        hash_id: u32,
        privkey: *const u8,
        msg: *const u8,
        msg_len: usize,
        signature: *mut u8,
        entropy: *const [u8; 32],
    ) -> usize;

    /// ECALL_SCHNORR_VERIFY: BIP-340 x-only pubkey, 64-byte signature.
    /// Returns 1 if valid, 0 otherwise.
    unsafe fn schnorr_verify(
        &mut self,
        curve: u32,
        mode: u32,
        hash_id: u32,
        pubkey: *const u8,
        msg: *const u8,
        msg_len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> u32;

    /// ECALL_XSEND: sends `size` bytes to the host.
    unsafe fn xsend(&mut self, buffer: *const u8, size: usize);

    /// ECALL_XRECV: receives into `buffer`, returns the received length.
    unsafe fn xrecv(&mut self, buffer: *mut u8, size: usize) -> usize;
}

/// RV32 machine ECALL backend (`target_arch = "riscv32"`).
///
/// Implements the Vanadium V-App machine convention: syscall number in `t0`,
/// integer/pointer arguments in `a0..a7`, return value in `a0`.
#[cfg(target_arch = "riscv32")]
pub mod machine {
    use super::RawEcalls;
    use core::arch::asm;

    /// Raw RV32 ECALL backend (real `ecall` instructions).
    #[derive(Default, Debug, Clone, Copy)]
    pub struct MachineEcalls;

    impl MachineEcalls {
        #[inline(always)]
        unsafe fn ecall2(nr: u32, a0: usize, a1: usize) -> u32 {
            let ret: u32;
            unsafe {
                asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1, lateout("a0") ret)
            }
            ret
        }
        #[inline(always)]
        unsafe fn ecall3(nr: u32, a0: usize, a1: usize, a2: usize) -> u32 {
            let ret: u32;
            unsafe {
                asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1, in("a2") a2, lateout("a0") ret)
            }
            ret
        }
        #[inline(always)]
        unsafe fn ecall4(nr: u32, a0: usize, a1: usize, a2: usize, a3: usize) -> u32 {
            let ret: u32;
            unsafe {
                asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1, in("a2") a2, in("a3") a3,
                     lateout("a0") ret)
            }
            ret
        }
        #[inline(always)]
        unsafe fn ecall5(nr: u32, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize) -> u32 {
            let ret: u32;
            unsafe {
                asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1, in("a2") a2, in("a3") a3,
                     in("a4") a4, lateout("a0") ret)
            }
            ret
        }
        #[inline(always)]
        unsafe fn ecall6(
            nr: u32,
            a0: usize,
            a1: usize,
            a2: usize,
            a3: usize,
            a4: usize,
            a5: usize,
        ) -> u32 {
            let ret: u32;
            unsafe {
                asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1, in("a2") a2, in("a3") a3,
                     in("a4") a4, in("a5") a5, lateout("a0") ret)
            }
            ret
        }
        #[inline(always)]
        unsafe fn ecall8(
            nr: u32,
            a0: usize,
            a1: usize,
            a2: usize,
            a3: usize,
            a4: usize,
            a5: usize,
            a6: usize,
            a7: usize,
        ) -> u32 {
            let ret: u32;
            unsafe {
                asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1, in("a2") a2, in("a3") a3,
                     in("a4") a4, in("a5") a5, in("a6") a6, in("a7") a7, lateout("a0") ret)
            }
            ret
        }
    }

    impl MachineEcalls {
        #[inline(always)]
        unsafe fn ecall2v(nr: u32, a0: usize, a1: usize) {
            unsafe { asm!("ecall", in("t0") nr, in("a0") a0, in("a1") a1) }
        }
    }

    // SAFETY: register-level mirror of LedgerHQ/vanadium
    // ecalls/src/ecalls_impl.rs (syscall number in t0, args in a0..a7,
    // return in a0).
    unsafe impl RawEcalls for MachineEcalls {
        unsafe fn derive_hd_node(
            &mut self,
            curve: u32,
            path: *const u32,
            path_len: usize,
            privkey: *mut u8,
            chain_code: *mut u8,
        ) -> u32 {
            unsafe {
                Self::ecall5(
                    super::ecall_nr::DERIVE_HD_NODE,
                    curve as usize,
                    path as usize,
                    path_len,
                    privkey as usize,
                    chain_code as usize,
                )
            }
        }

        unsafe fn get_master_fingerprint(&mut self, curve: u32, fingerprint: *mut u32) -> u32 {
            unsafe {
                Self::ecall2(
                    super::ecall_nr::GET_MASTER_FINGERPRINT,
                    curve as usize,
                    fingerprint as usize,
                )
            }
        }

        unsafe fn hash_init(&mut self, hash_id: u32, ctx: *mut u8) -> u32 {
            unsafe { Self::ecall2(super::ecall_nr::HASH_INIT, hash_id as usize, ctx as usize) }
        }

        unsafe fn hash_update(
            &mut self,
            hash_id: u32,
            ctx: *mut u8,
            data: *const u8,
            len: usize,
        ) -> u32 {
            unsafe {
                Self::ecall4(
                    super::ecall_nr::HASH_UPDATE,
                    hash_id as usize,
                    ctx as usize,
                    data as usize,
                    len,
                )
            }
        }

        unsafe fn hash_final(&mut self, hash_id: u32, ctx: *mut u8, digest: *mut u8) -> u32 {
            unsafe {
                Self::ecall3(
                    super::ecall_nr::HASH_DIGEST,
                    hash_id as usize,
                    ctx as usize,
                    digest as usize,
                )
            }
        }

        unsafe fn ecfp_add_point(
            &mut self,
            curve: u32,
            r: *mut u8,
            p: *const u8,
            q: *const u8,
        ) -> u32 {
            unsafe {
                Self::ecall4(
                    super::ecall_nr::ECFP_ADD_POINT,
                    curve as usize,
                    r as usize,
                    p as usize,
                    q as usize,
                )
            }
        }

        unsafe fn ecfp_scalar_mult(
            &mut self,
            curve: u32,
            r: *mut u8,
            p: *const u8,
            k: *const u8,
            k_len: usize,
        ) -> u32 {
            unsafe {
                Self::ecall5(
                    super::ecall_nr::ECFP_SCALAR_MULT,
                    curve as usize,
                    r as usize,
                    p as usize,
                    k as usize,
                    k_len,
                )
            }
        }

        unsafe fn get_random_bytes(&mut self, buffer: *mut u8, size: usize) -> u32 {
            unsafe { Self::ecall2(super::ecall_nr::GET_RANDOM_BYTES, buffer as usize, size) }
        }

        unsafe fn ecdsa_sign(
            &mut self,
            curve: u32,
            mode: u32,
            hash_id: u32,
            privkey: *const u8,
            msg_hash: *const u8,
            signature: *mut u8,
        ) -> usize {
            unsafe {
                Self::ecall6(
                    super::ecall_nr::ECDSA_SIGN,
                    curve as usize,
                    mode as usize,
                    hash_id as usize,
                    privkey as usize,
                    msg_hash as usize,
                    signature as usize,
                ) as usize
            }
        }

        unsafe fn ecdsa_verify(
            &mut self,
            curve: u32,
            pubkey: *const u8,
            msg_hash: *const u8,
            signature: *const u8,
            signature_len: usize,
        ) -> u32 {
            unsafe {
                Self::ecall5(
                    super::ecall_nr::ECDSA_VERIFY,
                    curve as usize,
                    pubkey as usize,
                    msg_hash as usize,
                    signature as usize,
                    signature_len,
                )
            }
        }

        unsafe fn schnorr_sign(
            &mut self,
            curve: u32,
            mode: u32,
            hash_id: u32,
            privkey: *const u8,
            msg: *const u8,
            msg_len: usize,
            signature: *mut u8,
            entropy: *const [u8; 32],
        ) -> usize {
            unsafe {
                Self::ecall8(
                    super::ecall_nr::SCHNORR_SIGN,
                    curve as usize,
                    mode as usize,
                    hash_id as usize,
                    privkey as usize,
                    msg as usize,
                    msg_len,
                    signature as usize,
                    entropy as usize,
                ) as usize
            }
        }

        unsafe fn schnorr_verify(
            &mut self,
            curve: u32,
            mode: u32,
            hash_id: u32,
            pubkey: *const u8,
            msg: *const u8,
            msg_len: usize,
            signature: *const u8,
            signature_len: usize,
        ) -> u32 {
            unsafe {
                Self::ecall8(
                    super::ecall_nr::SCHNORR_VERIFY,
                    curve as usize,
                    mode as usize,
                    hash_id as usize,
                    pubkey as usize,
                    msg as usize,
                    msg_len,
                    signature as usize,
                    signature_len,
                )
            }
        }

        unsafe fn xsend(&mut self, buffer: *const u8, size: usize) {
            unsafe { Self::ecall2v(super::ecall_nr::XSEND, buffer as usize, size) }
        }

        unsafe fn xrecv(&mut self, buffer: *mut u8, size: usize) -> usize {
            unsafe { Self::ecall2(super::ecall_nr::XRECV, buffer as usize, size) as usize }
        }
    }
}

// ---------------------------------------------------------------------------
// Safe wrappers
// ---------------------------------------------------------------------------

/// A derived HD node: 32-byte private key and 32-byte chain code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HdNode {
    pub privkey: [u8; SECP256K1_PRIVKEY_SIZE],
    pub chain_code: [u8; SECP256K1_PRIVKEY_SIZE],
}

/// BIP-32 HD node derivation (`ecall_derive_hd_node`, ECALL 130).
pub fn derive_hd_node(
    ec: &mut dyn RawEcalls,
    curve: u32,
    path: &[u32],
) -> Result<HdNode, EcallError> {
    if path.len() > 255 {
        return Err(EcallError::InvalidSlice("bip32 path too long"));
    }
    let mut node = HdNode {
        privkey: [0u8; SECP256K1_PRIVKEY_SIZE],
        chain_code: [0u8; SECP256K1_PRIVKEY_SIZE],
    };
    // SAFETY: `path` is a valid `path_len`-element read; output buffers are
    // correctly sized fixed arrays.
    let status = unsafe {
        ec.derive_hd_node(
            curve,
            path.as_ptr(),
            path.len(),
            node.privkey.as_mut_ptr(),
            node.chain_code.as_mut_ptr(),
        )
    };
    if status != 1 {
        return Err(EcallError::EcallFailed("derive_hd_node"));
    }
    Ok(node)
}

/// Master key fingerprint (`ecall_get_master_fingerprint`, ECALL 131).
pub fn get_master_fingerprint(ec: &mut dyn RawEcalls, curve: u32) -> Result<u32, EcallError> {
    let mut fingerprint: u32 = 0;
    // SAFETY: `fingerprint` is a valid writable u32.
    let status = unsafe { ec.get_master_fingerprint(curve, &mut fingerprint) };
    if status != 1 {
        return Err(EcallError::EcallFailed("get_master_fingerprint"));
    }
    Ok(fingerprint)
}

/// SHA-256 (`ecall_sha256`): safe wrapper over the hash ECALLs
/// (`hash_init` / `hash_update` / `hash_final`) with the composite
/// `Sha256(32)` hash id.
pub fn sha256(ec: &mut dyn RawEcalls, data: &[u8]) -> Result<[u8; 32], EcallError> {
    let hash_id = sha256_ecall_id(32);
    let mut ctx = [0u8; CTX_SHA256_SIZE];
    let mut digest = [0u8; 32];
    // SAFETY: `ctx` is CTX_SHA256_SIZE bytes as required by the hash ECALLs;
    // `data` is a valid slice.
    unsafe {
        if ec.hash_init(hash_id, ctx.as_mut_ptr()) != 1 {
            return Err(EcallError::EcallFailed("hash_init"));
        }
        if !data.is_empty() {
            if ec.hash_update(hash_id, ctx.as_mut_ptr(), data.as_ptr(), data.len()) != 1 {
                return Err(EcallError::EcallFailed("hash_update"));
            }
        }
        if ec.hash_final(hash_id, ctx.as_mut_ptr(), digest.as_mut_ptr()) != 1 {
            return Err(EcallError::EcallFailed("hash_final"));
        }
    }
    Ok(digest)
}

/// secp256k1 point addition (`ecall_secp256k1_add_point`): 65-byte
/// uncompressed SEC1 points, result written as `[u8; 65]`.
pub fn secp256k1_add_point(
    ec: &mut dyn RawEcalls,
    p: &[u8; SECP256K1_PUBKEY_SIZE],
    q: &[u8; SECP256K1_PUBKEY_SIZE],
) -> Result<[u8; SECP256K1_PUBKEY_SIZE], EcallError> {
    let mut r = [0u8; SECP256K1_PUBKEY_SIZE];
    // SAFETY: all pointers reference correctly sized buffers.
    let status =
        unsafe { ec.ecfp_add_point(curve::SECP256K1, r.as_mut_ptr(), p.as_ptr(), q.as_ptr()) };
    if status != 1 {
        return Err(EcallError::EcallFailed("ecfp_add_point"));
    }
    Ok(r)
}

/// secp256k1 scalar multiplication (`ecall_secp256k1_scalar_mult`):
/// 65-byte point times a big-endian scalar (`k_len <= 32`).
pub fn secp256k1_scalar_mult(
    ec: &mut dyn RawEcalls,
    p: &[u8; SECP256K1_PUBKEY_SIZE],
    k: &[u8],
) -> Result<[u8; SECP256K1_PUBKEY_SIZE], EcallError> {
    if k.is_empty() || k.len() > 32 {
        return Err(EcallError::InvalidSlice("scalar length must be in 1..=32"));
    }
    let mut r = [0u8; SECP256K1_PUBKEY_SIZE];
    // SAFETY: all pointers reference correctly sized buffers.
    let status = unsafe {
        ec.ecfp_scalar_mult(curve::SECP256K1, r.as_mut_ptr(), p.as_ptr(), k.as_ptr(), k.len())
    };
    if status != 1 {
        return Err(EcallError::EcallFailed("ecfp_scalar_mult"));
    }
    Ok(r)
}

/// Deterministic ECDSA (RFC 6979) signature over a SHA-256 message hash
/// (`ecall_secp256k1_ecdsa_sign`): returns the DER signature bytes.
pub fn secp256k1_ecdsa_sign(
    ec: &mut dyn RawEcalls,
    privkey: &[u8; SECP256K1_PRIVKEY_SIZE],
    msg_hash: &[u8; 32],
) -> Result<([u8; MAX_DER_SIGNATURE_LEN], usize), EcallError> {
    let mut sig = [0u8; MAX_DER_SIGNATURE_LEN];
    // SAFETY: all pointers reference correctly sized buffers.
    let len = unsafe {
        ec.ecdsa_sign(
            curve::SECP256K1,
            sign_mode::ECDSA_RFC6979,
            hash_id::SHA256,
            privkey.as_ptr(),
            msg_hash.as_ptr(),
            sig.as_mut_ptr(),
        )
    };
    if len == 0 || len > MAX_DER_SIGNATURE_LEN {
        return Err(EcallError::EcallFailed("ecdsa_sign"));
    }
    Ok((sig, len))
}

/// Strict BIP-66 DER ECDSA verification (`ecall_secp256k1_ecdsa_verify`).
pub fn secp256k1_ecdsa_verify(
    ec: &mut dyn RawEcalls,
    pubkey: &[u8; SECP256K1_PUBKEY_SIZE],
    msg_hash: &[u8; 32],
    signature: &[u8],
) -> Result<bool, EcallError> {
    if signature.is_empty() || signature.len() > MAX_DER_SIGNATURE_LEN {
        return Err(EcallError::InvalidSlice("signature length must be in 1..=72"));
    }
    // SAFETY: all pointers reference correctly sized buffers.
    let status = unsafe {
        ec.ecdsa_verify(
            curve::SECP256K1,
            pubkey.as_ptr(),
            msg_hash.as_ptr(),
            signature.as_ptr(),
            signature.len(),
        )
    };
    Ok(status == 1)
}

/// BIP-340 Schnorr signature (`ecall_secp256k1_schnorr_sign`): 64-byte
/// signature; `entropy` supplies the auxiliary randomness or `None` for
/// fresh randomness.
pub fn secp256k1_schnorr_sign(
    ec: &mut dyn RawEcalls,
    privkey: &[u8; SECP256K1_PRIVKEY_SIZE],
    msg: &[u8],
    entropy: Option<&[u8; 32]>,
) -> Result<[u8; SCHNORR_SIGNATURE_SIZE], EcallError> {
    let mut sig = [0u8; SCHNORR_SIGNATURE_SIZE];
    // SAFETY: all pointers reference correctly sized buffers; entropy is
    // either a valid 32-byte array or null.
    let len = unsafe {
        ec.schnorr_sign(
            curve::SECP256K1,
            sign_mode::SCHNORR_BIP340,
            hash_id::SHA256,
            privkey.as_ptr(),
            msg.as_ptr(),
            msg.len(),
            sig.as_mut_ptr(),
            entropy.map_or(core::ptr::null(), |e| e as *const [u8; 32]),
        )
    };
    if len != SCHNORR_SIGNATURE_SIZE {
        return Err(EcallError::EcallFailed("schnorr_sign"));
    }
    Ok(sig)
}

/// BIP-340 Schnorr verification (`ecall_secp256k1_schnorr_verify`) against a
/// 32-byte x-only public key.
pub fn secp256k1_schnorr_verify(
    ec: &mut dyn RawEcalls,
    xonly_pubkey: &[u8; SECP256K1_XONLY_PUBKEY_SIZE],
    msg: &[u8],
    signature: &[u8; SCHNORR_SIGNATURE_SIZE],
) -> Result<bool, EcallError> {
    // SAFETY: all pointers reference correctly sized buffers.
    let status = unsafe {
        ec.schnorr_verify(
            curve::SECP256K1,
            sign_mode::SCHNORR_BIP340,
            hash_id::SHA256,
            xonly_pubkey.as_ptr(),
            msg.as_ptr(),
            msg.len(),
            signature.as_ptr(),
            signature.len(),
        )
    };
    Ok(status == 1)
}

/// TRNG bytes (`ecall_get_random_bytes`).
pub fn get_random_bytes(ec: &mut dyn RawEcalls, out: &mut [u8]) -> Result<(), EcallError> {
    if out.is_empty() {
        return Err(EcallError::InvalidSlice("empty random buffer"));
    }
    // SAFETY: `out` is a valid `out.len()`-byte writable buffer.
    let status = unsafe { ec.get_random_bytes(out.as_mut_ptr(), out.len()) };
    if status != 1 {
        return Err(EcallError::EcallFailed("get_random_bytes"));
    }
    Ok(())
}

/// Host transport send (`ecall_xsend`): sends `data` to the host.
pub fn xsend(ec: &mut dyn RawEcalls, data: &[u8]) {
    if data.is_empty() {
        return;
    }
    // SAFETY: `data` is a valid `data.len()`-byte readable buffer.
    unsafe { ec.xsend(data.as_ptr(), data.len()) }
}

/// Host transport receive (`ecall_xrecv`): fills `buf`, returning the number
/// of received bytes.
pub fn xrecv(ec: &mut dyn RawEcalls, buf: &mut [u8]) -> usize {
    if buf.is_empty() {
        return 0;
    }
    // SAFETY: `buf` is a valid `buf.len()`-byte writable buffer.
    unsafe { ec.xrecv(buf.as_mut_ptr(), buf.len()) }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ------------------------------------------------------------------
    // 1. Linked kernel archive checks (go through the static library).
    // ------------------------------------------------------------------

    #[test]
    fn kernel_version_packed_matches_contract() {
        assert_eq!(version_packed(), VERSION_PACKED_EXPECTED);
        assert_eq!(version_packed(), 0x0002_0401);
    }

    #[test]
    fn kernel_version_unpacks() {
        let v = unpack_version(version_packed());
        assert_eq!(v.major, 2);
        assert_eq!(v.minor, 4);
        assert_eq!(v.patch, 1);
        assert_eq!(v, Version { major: 2, minor: 4, patch: 1 });
    }

    #[test]
    fn kernel_version_check_ok() {
        let v = check_kernel_version().expect("linked kernel must match 0x00020401");
        assert_eq!(v, Version { major: 2, minor: 4, patch: 1 });
        assert!(kernel_self_test());
    }

    #[test]
    fn kernel_satoshi_arithmetic_guards_overflow() {
        assert!(valid_amount(0));
        assert!(valid_amount(MAX_MONEY_SATS));
        assert!(!valid_amount(MAX_MONEY_SATS + 1));
        assert!(!valid_amount(1u64 << 63)); // VND-BUG-002 i64::MIN cast vector
        assert!(!valid_amount(u64::MAX));
        assert_eq!(checked_add_sats(100_000, 250_000), Some(350_000));
        assert_eq!(checked_add_sats(MAX_MONEY_SATS, 0), Some(MAX_MONEY_SATS));
        assert_eq!(checked_add_sats(MAX_MONEY_SATS, 1), None);
        assert_eq!(checked_add_sats(MAX_MONEY_SATS - 10, 11), None);
        assert_eq!(checked_add_sats(1u64 << 63, 1), None);
        assert_eq!(checked_sub_sats(500_000, 125_000), Some(375_000));
        assert_eq!(checked_sub_sats(100, 101), None);
        assert_eq!(checked_sub_sats(MAX_MONEY_SATS + 1, 1), None);
    }

    #[test]
    fn kernel_varint_and_bip32_guards() {
        assert_eq!(varint_encoded_len(0xFC), 1);
        assert_eq!(varint_encoded_len(0xFD), 3);
        assert_eq!(varint_encoded_len(0xFFFF), 3);
        assert_eq!(varint_encoded_len(0x1_0000), 5);
        assert_eq!(varint_encoded_len(0x1_0000_0000), 9);
        assert!(varint_prefix_is_canonical(0xFC, 0xFC));
        assert!(!varint_prefix_is_canonical(0xFD, 0xFC)); // VND-BUG-009 non-minimal 0xFD
        assert!(varint_prefix_is_canonical(0xFD, 0xFD));
        assert!(!varint_prefix_is_canonical(0xFE, 0xFFFF)); // VND-BUG-009 non-minimal 0xFE
        assert!(!varint_prefix_is_canonical(0xFF, 0xFFFF_FFFF)); // VND-BUG-009 non-minimal 0xFF

        let h84 = bip32_harden(84);
        assert_eq!(h84, 0x8000_0054);
        assert!(bip32_is_hardened(h84));
        assert!(!bip32_is_hardened(84));
        assert_eq!(bip32_unharden(h84), 84);
        assert!(bip32_bolos_depth_ok(10));
        assert!(!bip32_bolos_depth_ok(11));
        assert!(bip32_vanadium_depth_ok(16));
        assert!(!bip32_vanadium_depth_ok(17));
        for p in [44, 45, 49, 84, 86, 87] {
            assert!(bip32_standard_purpose_ok(bip32_harden(p)));
            assert!(!bip32_standard_purpose_ok(p));
        }
        assert!(!bip32_standard_purpose_ok(bip32_harden(352)));
    }

    #[test]
    fn kernel_script_sighash_merkle_and_sw_exports() {
        assert_eq!(witness_opcode_to_version(0x00), Some(0));
        assert_eq!(witness_opcode_to_version(0x51), Some(1));
        assert_eq!(witness_opcode_to_version(0x60), Some(16));
        assert_eq!(witness_opcode_to_version(0x50), None);

        assert!(segwit_program_valid(0, 20));
        assert!(segwit_program_valid(0, 32));
        assert!(!segwit_program_valid(0, 24));
        assert!(segwit_program_valid(1, 32));
        assert!(!segwit_program_valid(17, 32));

        // BIP-173polymod step sanity
        let mut chk = 1u32;
        for b in [3u8, 3, 0, 2, 3] {
            chk = bech32_polymod_step(chk, b);
        }
        assert_ne!(chk, 0);

        assert!(minimal_push_opcode_ok(0x00, 0x00, 0));
        assert!(!minimal_push_opcode_ok(0x01, 0x01, 1)); // must use OP_1
        assert!(minimal_push_opcode_ok(0x51, 0x01, 1));
        assert!(minimal_push_opcode_ok(0x4C, 0xAA, 76));
        assert!(!minimal_push_opcode_ok(0x4C, 0xAA, 75));

        for sh in [0x01u32, 0x02, 0x03, 0x81, 0x82, 0x83] {
            assert!(sighash_type_valid(sh));
            assert!(taproot_sighash_valid(sh as u8));
        }
        assert!(!sighash_type_valid(0x00));
        assert!(taproot_sighash_valid(0x00)); // SIGHASH_DEFAULT
        assert!(!taproot_sighash_valid(0x04));

        assert!(merkle_depth_index_ok(16, 15, 4));
        assert!(!merkle_depth_index_ok(0, 0, 0));
        assert!(!merkle_depth_index_ok(4, 4, 2));
        assert!(!merkle_depth_index_ok(4, 0, 33));

        assert_eq!(bolos_sw_for_error(0), 0x6700);
        assert_eq!(bolos_sw_for_error(5), 0x6985);
        assert_eq!(bolos_sw_for_error(18), 0xB008);
        assert_eq!(bolos_sw_for_error(99), 0xB007);
    }

    // ------------------------------------------------------------------
    // 2. Mock backend + SHA-256 reference for the safe wrappers.
    // ------------------------------------------------------------------

    /// Compact reference SHA-256 (FIPS 180-4) driving the mock hash ECALLs.
    struct Sha256 {
        h: [u32; 8],
        buf: [u8; 64],
        buf_len: usize,
        total: u64,
    }

    impl Sha256 {
        fn new() -> Self {
            Sha256 {
                h: [
                    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
                    0x1f83d9ab, 0x5be0cd19,
                ],
                buf: [0; 64],
                buf_len: 0,
                total: 0,
            }
        }

        fn compress(&mut self, block: &[u8]) {
            const K: [u32; 64] = [
                0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
                0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
                0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
                0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
                0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
                0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
                0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
                0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
                0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
            ];
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([
                    block[4 * i],
                    block[4 * i + 1],
                    block[4 * i + 2],
                    block[4 * i + 3],
                ]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) =
                (self.h[0], self.h[1], self.h[2], self.h[3], self.h[4], self.h[5], self.h[6], self.h[7]);
            for i in 0..64 {
                let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
                let ch = (e & f) ^ (!e & g);
                let t1 = h
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
                let maj = (a & b) ^ (a & c) ^ (b & c);
                let t2 = s0.wrapping_add(maj);
                h = g;
                g = f;
                f = e;
                e = d.wrapping_add(t1);
                d = c;
                c = b;
                b = a;
                a = t1.wrapping_add(t2);
            }
            self.h[0] = self.h[0].wrapping_add(a);
            self.h[1] = self.h[1].wrapping_add(b);
            self.h[2] = self.h[2].wrapping_add(c);
            self.h[3] = self.h[3].wrapping_add(d);
            self.h[4] = self.h[4].wrapping_add(e);
            self.h[5] = self.h[5].wrapping_add(f);
            self.h[6] = self.h[6].wrapping_add(g);
            self.h[7] = self.h[7].wrapping_add(h);
        }

        fn update(&mut self, mut data: &[u8]) {
            self.total = self.total.wrapping_add(data.len() as u64);
            while !data.is_empty() {
                let take = (64 - self.buf_len).min(data.len());
                self.buf[self.buf_len..self.buf_len + take].copy_from_slice(&data[..take]);
                self.buf_len += take;
                data = &data[take..];
                if self.buf_len == 64 {
                    let block = self.buf;
                    self.compress(&block);
                    self.buf_len = 0;
                }
            }
        }

        fn finalize(mut self) -> [u8; 32] {
            let bits = self.total * 8;
            self.update(&[0x80]);
            while self.buf_len != 56 {
                self.update(&[0x00]);
            }
            self.buf[56..64].copy_from_slice(&bits.to_be_bytes());
            let block = self.buf;
            self.compress(&block);
            let mut out = [0u8; 32];
            for i in 0..8 {
                out[4 * i..4 * i + 4].copy_from_slice(&self.h[i].to_be_bytes());
            }
            out
        }
    }

    /// Mock ECALL backend: reference SHA-256 for hashing and deterministic
    /// record/replay doubles for everything else.
    struct MockEcalls {
        hasher: Option<Sha256>,
        active_hash_id: u32,
        derive_calls: usize,
        last_path: Vec<u32>,
        last_curve: u32,
        fingerprint: u32,
        fail_derive: bool,
        sent: Vec<Vec<u8>>,
        recv_queue: Vec<Vec<u8>>,
        xrecv_calls: usize,
        xsend_calls: usize,
    }

    impl MockEcalls {
        fn new() -> Self {
            MockEcalls {
                hasher: None,
                active_hash_id: 0,
                derive_calls: 0,
                last_path: Vec::new(),
                last_curve: 0,
                fingerprint: 0xf5ac_c2fd,
                fail_derive: false,
                sent: Vec::new(),
                recv_queue: vec![vec![0xde, 0xad, 0xbe, 0xef]],
                xrecv_calls: 0,
                xsend_calls: 0,
            }
        }
    }

    // SAFETY: mock honors the documented preconditions.
    unsafe impl RawEcalls for MockEcalls {
        unsafe fn derive_hd_node(
            &mut self,
            curve: u32,
            path: *const u32,
            path_len: usize,
            privkey: *mut u8,
            chain_code: *mut u8,
        ) -> u32 {
            self.derive_calls += 1;
            self.last_curve = curve;
            self.last_path = (0..path_len).map(|i| unsafe { *path.add(i) }).collect();
            if self.fail_derive || curve != curve::SECP256K1 {
                return 0;
            }
            let pk = unsafe { core::slice::from_raw_parts_mut(privkey, 32) };
            for (i, byte) in pk.iter_mut().enumerate() {
                *byte = (i as u8).wrapping_mul(7).wrapping_add(1);
            }
            let cc = unsafe { core::slice::from_raw_parts_mut(chain_code, 32) };
            for (i, byte) in cc.iter_mut().enumerate() {
                *byte = (i as u8).wrapping_mul(13).wrapping_add(3);
            }
            1
        }

        unsafe fn get_master_fingerprint(&mut self, curve: u32, fingerprint: *mut u32) -> u32 {
            if curve != curve::SECP256K1 {
                return 0;
            }
            unsafe { *fingerprint = self.fingerprint };
            1
        }

        unsafe fn hash_init(&mut self, hash_id: u32, _ctx: *mut u8) -> u32 {
            self.active_hash_id = hash_id;
            self.hasher = Some(Sha256::new());
            1
        }

        unsafe fn hash_update(
            &mut self,
            hash_id: u32,
            _ctx: *mut u8,
            data: *const u8,
            len: usize,
        ) -> u32 {
            if hash_id != self.active_hash_id {
                return 0;
            }
            let slice = unsafe { core::slice::from_raw_parts(data, len) };
            self.hasher.as_mut().map(|h| h.update(slice));
            1
        }

        unsafe fn hash_final(&mut self, hash_id: u32, _ctx: *mut u8, digest: *mut u8) -> u32 {
            if hash_id != self.active_hash_id {
                return 0;
            }
            let out = self.hasher.take().map(Sha256::finalize);
            match out {
                Some(d) => {
                    unsafe { core::ptr::copy_nonoverlapping(d.as_ptr(), digest, 32) };
                    1
                }
                None => 0,
            }
        }

        unsafe fn ecfp_add_point(
            &mut self,
            curve: u32,
            r: *mut u8,
            p: *const u8,
            q: *const u8,
        ) -> u32 {
            if curve != curve::SECP256K1 {
                return 0;
            }
            for i in 0..SECP256K1_PUBKEY_SIZE {
                unsafe { *r.add(i) = *p.add(i) ^ *q.add(i) };
            }
            1
        }

        unsafe fn ecfp_scalar_mult(
            &mut self,
            curve: u32,
            r: *mut u8,
            p: *const u8,
            k: *const u8,
            k_len: usize,
        ) -> u32 {
            if curve != curve::SECP256K1 || k_len == 0 || k_len > 32 {
                return 0;
            }
            for i in 0..SECP256K1_PUBKEY_SIZE {
                unsafe { *r.add(i) = (*p.add(i)).wrapping_add(*k.add(i % k_len)) };
            }
            1
        }

        unsafe fn get_random_bytes(&mut self, buffer: *mut u8, size: usize) -> u32 {
            if size == 0 || size > 1024 {
                return 0;
            }
            let mut x: u32 = 0x1234_5678;
            for i in 0..size {
                x ^= x << 13;
                x ^= x >> 17;
                x ^= x << 5;
                unsafe { *buffer.add(i) = (x >> 24) as u8 };
            }
            1
        }

        unsafe fn ecdsa_sign(
            &mut self,
            curve: u32,
            mode: u32,
            _hash_id: u32,
            privkey: *const u8,
            msg_hash: *const u8,
            signature: *mut u8,
        ) -> usize {
            if curve != curve::SECP256K1 || mode != sign_mode::ECDSA_RFC6979 {
                return 0;
            }
            // deterministic stand-in signature derived from key and hash
            let mut len = 0usize;
            unsafe {
                for i in 0..9 {
                    *signature.add(i) = (*privkey.add(i % 32)) ^ (*msg_hash.add(i % 32));
                    len += 1;
                }
            }
            len
        }

        unsafe fn ecdsa_verify(
            &mut self,
            curve: u32,
            pubkey: *const u8,
            msg_hash: *const u8,
            signature: *const u8,
            signature_len: usize,
        ) -> u32 {
            if curve != curve::SECP256K1 {
                return 0;
            }
            let mut ok = true;
            for i in 0..signature_len.min(9) {
                let expect = unsafe { (*pubkey.add(i % 65)) ^ (*msg_hash.add(i % 32)) };
                if unsafe { *signature.add(i) } != expect {
                    ok = false;
                }
            }
            ok as u32
        }

        unsafe fn schnorr_sign(
            &mut self,
            curve: u32,
            mode: u32,
            _hash_id: u32,
            privkey: *const u8,
            msg: *const u8,
            msg_len: usize,
            signature: *mut u8,
            entropy: *const [u8; 32],
        ) -> usize {
            if curve != curve::SECP256K1 || mode != sign_mode::SCHNORR_BIP340 {
                return 0;
            }
            let entropy_ref: &[u8; 32] = if entropy.is_null() {
                &[0u8; 32]
            } else {
                unsafe { &*entropy }
            };
            for i in 0..64 {
                let b = unsafe {
                    (*privkey.add(i % 32))
                        ^ (if i < msg_len { *msg.add(i) } else { entropy_ref[i % 32] })
                };
                unsafe { *signature.add(i) = b };
            }
            64
        }

        unsafe fn schnorr_verify(
            &mut self,
            curve: u32,
            mode: u32,
            _hash_id: u32,
            pubkey: *const u8,
            msg: *const u8,
            msg_len: usize,
            signature: *const u8,
            signature_len: usize,
        ) -> u32 {
            if curve != curve::SECP256K1
                || mode != sign_mode::SCHNORR_BIP340
                || signature_len != 64
            {
                return 0;
            }
            // The mock signs with privkey == pubkey ^ 0xFF, so reproduce it.
            let mut ok = true;
            for i in 0..64 {
                let privkey_byte = unsafe { (*pubkey.add(i % 32)) ^ 0xFF };
                let expect = privkey_byte
                    ^ (if i < msg_len { unsafe { *msg.add(i) } } else { 0u8 });
                if unsafe { *signature.add(i) } != expect {
                    ok = false;
                }
            }
            ok as u32
        }

        unsafe fn xsend(&mut self, buffer: *const u8, size: usize) {
            self.xsend_calls += 1;
            let slice = unsafe { core::slice::from_raw_parts(buffer, size) };
            self.sent.push(slice.to_vec());
        }

        unsafe fn xrecv(&mut self, buffer: *mut u8, size: usize) -> usize {
            self.xrecv_calls += 1;
            match self.recv_queue.first() {
                Some(data) => {
                    let n = data.len().min(size);
                    unsafe { core::ptr::copy_nonoverlapping(data.as_ptr(), buffer, n) };
                    self.recv_queue.remove(0);
                    n
                }
                None => 0,
            }
        }
    }

    // ------------------------------------------------------------------
    // 3. Safe-wrapper tests against the mock backend.
    // ------------------------------------------------------------------

    #[test]
    fn sha256_matches_fips_vectors() {
        let mut ec = MockEcalls::new();
        let empty = sha256(&mut ec, b"").unwrap();
        assert_eq!(
            empty,
            [
                0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99,
                0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95,
                0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
            ]
        );
        let abc = sha256(&mut ec, b"abc").unwrap();
        assert_eq!(
            abc,
            [
                0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d,
                0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10,
                0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
            ]
        );
        // padding boundaries: 55, 56 and 64-byte inputs
        let buf: Vec<u8> = (0u8..64).collect();
        assert!(sha256(&mut ec, &buf[..55]).is_ok());
        assert!(sha256(&mut ec, &buf[..56]).is_ok());
        assert!(sha256(&mut ec, &buf).is_ok());
    }

    #[test]
    fn sha256_ecall_id_composition() {
        assert_eq!(sha256_ecall_id(32), (3 << 16) | 32);
        assert_eq!(sha256_ecall_id(32), 0x3_0020);
    }

    #[test]
    fn derive_hd_node_wrapper() {
        let mut ec = MockEcalls::new();
        let path: Vec<u32> = vec![0x8000_0000 | 84, 0x8000_0000, 0x8000_0000];
        let node = derive_hd_node(&mut ec, curve::SECP256K1, &path).unwrap();
        assert_eq!(ec.derive_calls, 1);
        assert_eq!(ec.last_curve, curve::SECP256K1);
        assert_eq!(ec.last_path, path);
        assert_eq!(node.privkey[0], 1);
        assert_eq!(node.privkey[31], 31 * 7 + 1);
        assert_eq!(node.chain_code[0], 3);
        // empty path (master key)
        let master = derive_hd_node(&mut ec, curve::SECP256K1, &[]).unwrap();
        assert_eq!(master.privkey, node.privkey);
        // failure propagates
        ec.fail_derive = true;
        assert_eq!(
            derive_hd_node(&mut ec, curve::SECP256K1, &path),
            Err(EcallError::EcallFailed("derive_hd_node"))
        );
    }

    #[test]
    fn master_fingerprint_wrapper() {
        let mut ec = MockEcalls::new();
        let fp = get_master_fingerprint(&mut ec, curve::SECP256K1).unwrap();
        assert_eq!(fp, 0xf5ac_c2fd);
        assert_eq!(
            get_master_fingerprint(&mut ec, 0x42),
            Err(EcallError::EcallFailed("get_master_fingerprint"))
        );
    }

    #[test]
    fn secp256k1_point_and_scalar_wrappers() {
        let mut ec = MockEcalls::new();
        let p = [0x04u8; 65];
        let q = [0x21u8; 65];
        let r = secp256k1_add_point(&mut ec, &p, &q).unwrap();
        assert_eq!(r[0], 0x04 ^ 0x21);
        let k = [7u8; 32];
        let m = secp256k1_scalar_mult(&mut ec, &p, &k).unwrap();
        assert_eq!(m[0], 0x04 + 7);
        // scalar length validation happens in the wrapper
        assert_eq!(
            secp256k1_scalar_mult(&mut ec, &p, &[]),
            Err(EcallError::InvalidSlice("scalar length must be in 1..=32"))
        );
        assert_eq!(
            secp256k1_scalar_mult(&mut ec, &p, &[0u8; 33]),
            Err(EcallError::InvalidSlice("scalar length must be in 1..=32"))
        );
    }

    #[test]
    fn ecdsa_sign_verify_roundtrip() {
        let mut ec = MockEcalls::new();
        let privkey = [0x42u8; 32];
        let msg_hash = [0xABu8; 32];
        let (sig, len) = secp256k1_ecdsa_sign(&mut ec, &privkey, &msg_hash).unwrap();
        assert!(len > 0 && len <= 72);
        // mock verification expects pubkey bytes equal to the signing key
        let pubkey = [0x42u8; 65];
        assert!(secp256k1_ecdsa_verify(&mut ec, &pubkey, &msg_hash, &sig[..len]).unwrap());
        // a corrupted signature must fail
        let mut bad = sig;
        bad[0] ^= 0xFF;
        assert!(!secp256k1_ecdsa_verify(&mut ec, &pubkey, &msg_hash, &bad[..len]).unwrap());
    }

    #[test]
    fn schnorr_sign_verify_roundtrip() {
        let mut ec = MockEcalls::new();
        let privkey = [0x42u8; 32];
        let msg = b"vanadium v-app";
        let sig = secp256k1_schnorr_sign(&mut ec, &privkey, msg, None).unwrap();
        assert_eq!(sig.len(), 64);
        // mock: xonly pubkey = privkey ^ 0xFF (see MockEcalls::schnorr_verify)
        let xonly: [u8; 32] = core::array::from_fn(|i| privkey[i] ^ 0xFF);
        assert!(secp256k1_schnorr_verify(&mut ec, &xonly, msg, &sig).unwrap());
        let mut bad = sig;
        bad[63] ^= 1;
        assert!(!secp256k1_schnorr_verify(&mut ec, &xonly, msg, &bad).unwrap());
    }

    #[test]
    fn random_bytes_wrapper() {
        let mut ec = MockEcalls::new();
        let mut buf = [0u8; 16];
        get_random_bytes(&mut ec, &mut buf).unwrap();
        assert_ne!(buf, [0u8; 16]);
        assert_eq!(
            get_random_bytes(&mut ec, &mut []),
            Err(EcallError::InvalidSlice("empty random buffer"))
        );
    }

    #[test]
    fn xsend_xrecv_transport() {
        let mut ec = MockEcalls::new();
        let data = [1u8, 2, 3, 4];
        xsend(&mut ec, &data);
        xsend(&mut ec, &data);
        assert_eq!(ec.xsend_calls, 2);
        assert_eq!(ec.sent, vec![data.to_vec(), data.to_vec()]);
        let mut buf = [0u8; 8];
        let n = xrecv(&mut ec, &mut buf);
        assert_eq!(n, 4);
        assert_eq!(&buf[..n], &[0xde, 0xad, 0xbe, 0xef]);
        assert_eq!(ec.xrecv_calls, 1);
        // exhausted queue returns 0
        assert_eq!(xrecv(&mut ec, &mut buf), 0);
    }

    #[test]
    fn ecall_numbers_match_vanadium() {
        assert_eq!(ecall_nr::XSEND, 2);
        assert_eq!(ecall_nr::XRECV, 3);
        assert_eq!(ecall_nr::DERIVE_HD_NODE, 130);
        assert_eq!(ecall_nr::GET_MASTER_FINGERPRINT, 131);
        assert_eq!(ecall_nr::HASH_INIT, 150);
        assert_eq!(ecall_nr::HASH_UPDATE, 151);
        assert_eq!(ecall_nr::HASH_DIGEST, 152);
        assert_eq!(ecall_nr::ECFP_ADD_POINT, 160);
        assert_eq!(ecall_nr::ECFP_SCALAR_MULT, 161);
        assert_eq!(ecall_nr::GET_RANDOM_BYTES, 170);
        assert_eq!(ecall_nr::ECDSA_SIGN, 180);
        assert_eq!(ecall_nr::ECDSA_VERIFY, 181);
        assert_eq!(ecall_nr::SCHNORR_SIGN, 182);
        assert_eq!(ecall_nr::SCHNORR_VERIFY, 183);
        assert_eq!(curve::SECP256K1, 0x21);
        assert_eq!(hash_id::SHA256, 3);
        assert_eq!(sign_mode::ECDSA_RFC6979, 3 << 9);
        assert_eq!(sign_mode::SCHNORR_BIP340, 0);
        assert_eq!(CTX_SHA256_SIZE, 128);
        assert_eq!(MAX_DER_SIGNATURE_LEN, 72);
        assert_eq!(SCHNORR_SIGNATURE_SIZE, 64);
    }
}

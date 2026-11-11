//! `llb-vanadium-ffi` — thin `no_std` Vanadium Rust/C FFI crate for the
//! `lean-ledger-bitcoin` freestanding kernels (`SPEC_ABI.md`).
//!
//! Links the `turbo-lean`-emitted static archive (`liblean_ledger_bitcoin.a`)
//! via `extern "C"` — the `riscv32imac` emission on `target_arch = "riscv32"`
//! (Vanadium V-App, RV32IMAC ILP32) and the host emission everywhere else
//! (`cargo test` / benchmarks).

#![cfg_attr(not(test), no_std)]
#![allow(clippy::missing_safety_doc)]

use core::fmt;

/// Packed kernel version contract (`(2 << 16) | (4 << 8) | 1 == 0x0002_0401`).
pub const VERSION_PACKED_EXPECTED: u32 = 0x0002_0401;
pub const VERSION_MAJOR: u32 = 2;
pub const VERSION_MINOR: u32 = 4;
pub const VERSION_PATCH: u32 = 1;

/// Consensus `MAX_MONEY` (`21_000_000 * 100_000_000 = 2_100_000_000_000_000` satoshis).
pub const MAX_MONEY_SATS: u64 = 2_100_000_000_000_000;

/// Maximum postfix token buffer length accepted by `miniscript_check_postfix`.
pub const MINISCRIPT_MAX_POSTFIX_OPS: usize = 512;

/// Stack scratch size (64 × 2-byte packed entries) required by `llb_miniscript_check_postfix`.
pub const MINISCRIPT_SCRATCH_BYTES: usize = 128;

mod sys {
    extern "C" {
        // A. Existing 29 scalar freestanding kernel exports (`SPEC_ABI.md` 1..29)
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
        pub fn llb_sats_div_1e8(amount: u64) -> u64;
        pub fn llb_sats_mod_1e8(amount: u64) -> u32;
        pub fn llb_merkle_advance_state(st: u64) -> u64;
        pub fn llb_merkle_state_dir(st: u64) -> u8;
        pub fn llb_bip32_pubkey_export_prefix_ok(
            p0: u32,
            p1: u32,
            p2: u32,
            p3: u32,
            path_len: u8,
            expected_coin_type: u32,
            tail_unhardened: u8,
        ) -> u8;
        pub fn llb_bech32_final_constant(enc: u8) -> u32;
        pub fn llb_wallet_name_char_ok(c: u8, is_edge: u8) -> u8;

        // B & C. Option 2 zero-copy buffer & loop kernels (`SPEC_ABI.md` 30..38)
        pub fn llb_miniscript_older_ok(n: u32) -> u8;
        pub fn llb_miniscript_after_ok(n: u32) -> u8;
        pub fn llb_miniscript_check_postfix(
            ops: *const u8,
            ops_len: u32,
            is_tapscript: u8,
            require_flags: u8,
            scratch: *mut u8,
        ) -> u8;
        pub fn llb_psbt_locktime_init() -> u64;
        pub fn llb_psbt_determine_locktime(
            heights_and_times_le: *const u8,
            num_inputs: u32,
            fallback_locktime: u32,
        ) -> u64;
        pub fn llb_psbt_locktime_step(state: u64, has_h: u8, h: u32, has_t: u8, t: u32) -> u64;
        pub fn llb_psbt_locktime_finalize(state: u64, fallback_locktime: u32) -> u64;
        pub fn llb_bytes_eq(a: *const u8, b: *const u8, len: u32) -> u8;
        pub fn llb_check_dual_utxo(
            wit_amount: u64,
            wit_spk: *const u8,
            wit_spk_len: u32,
            non_wit_amount: u64,
            non_wit_spk: *const u8,
            non_wit_spk_len: u32,
        ) -> u8;
        pub fn llb_sum_amounts_le64(amounts_le: *const u8, count: u32) -> u64;
        pub fn llb_bip32_check_export_path(
            path: *const u32,
            path_len: u8,
            expected_coin_type: u32,
        ) -> u8;
        pub fn llb_read_compact_size_checked(buf: *const u8, buf_len: u32, max_val: u32) -> u64;
        pub fn llb_sort_fixed_bytes(buf: *mut u8, count: u32, stride: u32);
        pub fn llb_sort_u16(arr: *mut u16, count: u32);
        pub fn llb_format_sats_ascii(
            amount: u64,
            ticker: *const u8,
            ticker_len: u32,
            pad_frac8: u8,
            out: *mut u8,
            out_cap: u32,
        ) -> u32;
        pub fn llb_miniscript_andor_branches_valid(
            notif_opcode: u8,
            else_opcode: u8,
            endif_opcode: u8,
        ) -> u8;
    }
}

#[inline]
pub fn version_packed() -> u32 {
    unsafe { sys::llb_version_packed() }
}

#[inline]
pub fn valid_amount(sats: u64) -> bool {
    unsafe { sys::llb_valid_amount(sats) != 0 }
}

#[inline]
pub fn checked_add_sats(a: u64, b: u64) -> Option<u64> {
    unsafe {
        if sys::llb_checked_add_sats_ok(a, b) != 0 {
            Some(sys::llb_checked_add_sats_val(a, b))
        } else {
            None
        }
    }
}

#[inline]
pub fn checked_sub_sats(a: u64, b: u64) -> Option<u64> {
    unsafe {
        if sys::llb_checked_sub_sats_ok(a, b) != 0 {
            Some(sys::llb_checked_sub_sats_val(a, b))
        } else {
            None
        }
    }
}

#[inline]
pub fn varint_encoded_len(n: u64) -> u8 {
    unsafe { sys::llb_varint_encoded_len(n) }
}

#[inline]
pub fn varint_prefix_is_canonical(tag: u8, decoded_val: u64) -> bool {
    unsafe { sys::llb_varint_prefix_is_canonical(tag, decoded_val) != 0 }
}

#[inline]
pub fn bip32_is_hardened(idx: u32) -> bool {
    unsafe { sys::llb_bip32_is_hardened(idx) != 0 }
}

#[inline]
pub fn bip32_harden(n: u32) -> u32 {
    unsafe { sys::llb_bip32_harden(n) }
}

#[inline]
pub fn bip32_unharden(idx: u32) -> u32 {
    unsafe { sys::llb_bip32_unharden(idx) }
}

#[inline]
pub fn bip32_bolos_depth_ok(depth: u8) -> bool {
    unsafe { sys::llb_bip32_bolos_depth_ok(depth) != 0 }
}

#[inline]
pub fn bip32_vanadium_depth_ok(depth: u8) -> bool {
    unsafe { sys::llb_bip32_vanadium_depth_ok(depth) != 0 }
}

#[inline]
pub fn bip32_standard_purpose_ok(purpose_step: u32) -> bool {
    unsafe { sys::llb_bip32_standard_purpose_ok(purpose_step) != 0 }
}

#[inline]
pub fn witness_opcode_to_version(op: u8) -> Option<u8> {
    let v = unsafe { sys::llb_witness_opcode_to_version(op) };
    if v == 0xFF { None } else { Some(v) }
}

#[inline]
pub fn segwit_program_valid(witver: u8, prog_len: u8) -> bool {
    unsafe { sys::llb_segwit_program_valid(witver, prog_len) != 0 }
}

#[inline]
pub fn bech32_polymod_step(pre: u32, val: u8) -> u32 {
    unsafe { sys::llb_bech32_polymod_step(pre, val) }
}

#[inline]
pub fn bech32_final_constant(enc: u8) -> u32 {
    unsafe { sys::llb_bech32_final_constant(enc) }
}

#[inline]
pub fn minimal_push_opcode_ok(op: u8, first_byte: u8, push_len: u32) -> bool {
    unsafe { sys::llb_minimal_push_opcode_ok(op, first_byte, push_len) != 0 }
}

#[inline]
pub fn sighash_type_valid(sighash_u32: u32) -> bool {
    unsafe { sys::llb_sighash_type_valid(sighash_u32) != 0 }
}

#[inline]
pub fn taproot_sighash_valid(sighash_byte: u8) -> bool {
    unsafe { sys::llb_taproot_sighash_valid(sighash_byte) != 0 }
}

#[inline]
pub fn merkle_depth_index_ok(tree_size: u32, index: u32, depth: u8) -> bool {
    unsafe { sys::llb_merkle_depth_index_ok(tree_size, index, depth) != 0 }
}

#[inline]
pub fn merkle_advance_state(st: u64) -> u64 {
    unsafe { sys::llb_merkle_advance_state(st) }
}

#[inline]
pub fn merkle_state_dir(st: u64) -> u8 {
    unsafe { sys::llb_merkle_state_dir(st) }
}

#[inline]
pub fn bolos_sw_for_error(err_tag: u8) -> u16 {
    unsafe { sys::llb_bolos_sw_for_error(err_tag) }
}

#[inline]
pub fn sats_div_1e8(amount: u64) -> u64 {
    unsafe { sys::llb_sats_div_1e8(amount) }
}

#[inline]
pub fn sats_mod_1e8(amount: u64) -> u32 {
    unsafe { sys::llb_sats_mod_1e8(amount) }
}

#[inline]
pub fn wallet_name_char_ok(c: u8, is_edge: bool) -> bool {
    unsafe { sys::llb_wallet_name_char_ok(c, u8::from(is_edge)) != 0 }
}

#[inline]
pub fn bip32_pubkey_export_prefix_ok(
    p0: u32,
    p1: u32,
    p2: u32,
    p3: u32,
    path_len: u8,
    expected_coin_type: u32,
    tail_unhardened: bool,
) -> bool {
    unsafe {
        sys::llb_bip32_pubkey_export_prefix_ok(
            p0,
            p1,
            p2,
            p3,
            path_len,
            expected_coin_type,
            u8::from(tail_unhardened),
        ) != 0
    }
}

// ---------------------------------------------------------------------------
// Option 2 zero-copy buffer & loop safe wrappers (`SPEC_ABI.md` 30..38)
// ---------------------------------------------------------------------------

/// BIP-68 `older(n)` consensus range check (`(n & 0xFFBF_0000) == 0 && (n & 0xFFFF) >= 1`).
#[inline]
pub fn miniscript_older_ok(n: u32) -> bool {
    unsafe { sys::llb_miniscript_older_ok(n) != 0 }
}

/// BIP-65 / BIP-379 `after(n)` consensus range check (`1 <= n < 0x8000_0000`).
#[inline]
pub fn miniscript_after_ok(n: u32) -> bool {
    unsafe { sys::llb_miniscript_after_ok(n) != 0 }
}

/// Canonical `andor` framing check (`OP_NOTIF (0x64)`, `OP_ELSE (0x67)`, `OP_ENDIF (0x68)`).
#[inline]
pub fn miniscript_andor_branches_valid(
    notif_opcode: u8,
    else_opcode: u8,
    endif_opcode: u8,
) -> bool {
    unsafe {
        sys::llb_miniscript_andor_branches_valid(notif_opcode, else_opcode, endif_opcode) != 0
    }
}

/// Full postfix BIP-379 / BIP-388 Miniscript typechecker, non-malleability, and
/// timelock-conflict analyzer using 128 bytes of stack scratch (`0` heap allocations).
#[inline]
pub fn miniscript_check_postfix(
    ops: &[u8],
    is_tapscript: bool,
    require_non_malleable: bool,
    require_sig: bool,
) -> bool {
    if ops.is_empty() || ops.len() > MINISCRIPT_MAX_POSTFIX_OPS {
        return false;
    }
    let mut scratch = [0u8; MINISCRIPT_SCRATCH_BYTES];
    let flags = u8::from(require_non_malleable) | (u8::from(require_sig) << 1);
    unsafe {
        sys::llb_miniscript_check_postfix(
            ops.as_ptr(),
            ops.len() as u32,
            u8::from(is_tapscript),
            flags,
            scratch.as_mut_ptr(),
        ) != 0
    }
}

/// Initial state (`1 << 63`) for streaming BIP-370 PSBTv2 locktime resolution.
#[inline]
pub fn psbt_locktime_init() -> u64 {
    unsafe { sys::llb_psbt_locktime_init() }
}

/// Fold one input's optional `required_height_locktime` and `required_time_locktime`
/// into the streaming BIP-370 locktime state.
#[inline]
pub fn psbt_locktime_step(state: u64, height: Option<u32>, time: Option<u32>) -> u64 {
    let (has_h, h) = match height {
        Some(v) => (1u8, v),
        None => (0u8, 0u32),
    };
    let (has_t, t) = match time {
        Some(v) => (1u8, v),
        None => (0u8, 0u32),
    };
    unsafe { sys::llb_psbt_locktime_step(state, has_h, h, has_t, t) }
}

/// Finalize streaming BIP-370 locktime state against `fallback_locktime`.
#[inline]
pub fn psbt_locktime_finalize(state: u64, fallback_locktime: u32) -> Option<u32> {
    let packed = unsafe { sys::llb_psbt_locktime_finalize(state, fallback_locktime) };
    if (packed >> 32) != 0 {
        Some(packed as u32)
    } else {
        None
    }
}

/// Batch BIP-370 locktime determination over packed 10-byte records
/// `[has_h: u8, h_le: [u8; 4], has_t: u8, t_le: [u8; 4]]`.
#[inline]
pub fn psbt_determine_locktime(records_10b: &[u8], fallback_locktime: u32) -> Option<u32> {
    if records_10b.len() % 10 != 0 || records_10b.len() / 10 > u32::MAX as usize {
        return None;
    }
    let num_inputs = (records_10b.len() / 10) as u32;
    let ptr = if records_10b.is_empty() {
        core::ptr::NonNull::<u8>::dangling().as_ptr()
    } else {
        records_10b.as_ptr()
    };
    let packed = unsafe { sys::llb_psbt_determine_locktime(ptr, num_inputs, fallback_locktime) };
    if (packed >> 32) != 0 {
        Some(packed as u32)
    } else {
        None
    }
}

/// Bounded constant-structure byte slice equality.
#[inline]
pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() || a.len() > u32::MAX as usize {
        return false;
    }
    if a.is_empty() {
        return true;
    }
    unsafe { sys::llb_bytes_eq(a.as_ptr(), b.as_ptr(), a.len() as u32) != 0 }
}

/// Dual-UTXO (`witness_utxo` vs `non_witness_utxo[vout]`) consensus & CVE-2020-14199 check.
#[inline]
pub fn check_dual_utxo(
    wit_amount: u64,
    wit_spk: &[u8],
    non_wit_amount: u64,
    non_wit_spk: &[u8],
) -> bool {
    if wit_spk.len() > u32::MAX as usize || non_wit_spk.len() > u32::MAX as usize {
        return false;
    }
    let wit_ptr = if wit_spk.is_empty() {
        core::ptr::NonNull::<u8>::dangling().as_ptr()
    } else {
        wit_spk.as_ptr()
    };
    let non_wit_ptr = if non_wit_spk.is_empty() {
        core::ptr::NonNull::<u8>::dangling().as_ptr()
    } else {
        non_wit_spk.as_ptr()
    };
    unsafe {
        sys::llb_check_dual_utxo(
            wit_amount,
            wit_ptr,
            wit_spk.len() as u32,
            non_wit_amount,
            non_wit_ptr,
            non_wit_spk.len() as u32,
        ) != 0
    }
}

/// Sum `count` 8-byte little-endian satoshi amounts with per-step `MAX_MONEY` overflow checks.
#[inline]
pub fn sum_amounts_le64(amounts_le: &[u8]) -> Option<u64> {
    if amounts_le.len() % 8 != 0 || amounts_le.len() / 8 > u32::MAX as usize {
        return None;
    }
    let count = (amounts_le.len() / 8) as u32;
    let ptr = if amounts_le.is_empty() {
        core::ptr::NonNull::<u8>::dangling().as_ptr()
    } else {
        amounts_le.as_ptr()
    };
    let res = unsafe { sys::llb_sum_amounts_le64(ptr, count) };
    if (res >> 63) != 0 {
        Some(res & ((1u64 << 63) - 1))
    } else {
        None
    }
}

/// Full buffer standard BIP-32 export path policy check (`VND-07` & BOLOS `is_path_safe_for_pubkey_export`).
#[inline]
pub fn bip32_check_export_path(path: &[u32], expected_coin_type: u32) -> bool {
    if path.len() > u8::MAX as usize {
        return false;
    }
    let ptr = if path.is_empty() {
        core::ptr::NonNull::<u32>::dangling().as_ptr()
    } else {
        path.as_ptr()
    };
    unsafe { sys::llb_bip32_check_export_path(ptr, path.len() as u8, expected_coin_type) != 0 }
}

/// Canonical Bitcoin `CompactSize` reader bounded by `max_val`.
/// Returns `Some((value, consumed_bytes))` on valid canonical input, `None` otherwise.
#[inline]
pub fn read_compact_size_checked(buf: &[u8], max_val: u32) -> Option<(u32, usize)> {
    if buf.is_empty() {
        return None;
    }
    let capped_len = buf.len().min(9) as u32;
    let packed = unsafe { sys::llb_read_compact_size_checked(buf.as_ptr(), capped_len, max_val) };
    let consumed = (packed >> 32) as usize;
    if consumed == 0 {
        None
    } else {
        Some((packed as u32, consumed))
    }
}

/// In-place, 0-recursion lexicographic insertion sort of fixed-stride byte records
/// (e.g. `N = 33` for BIP-67 `sortedmulti` / BIP-327 MuSig2, `N = 32` for `sortedmulti_a`).
#[inline]
pub fn sort_fixed_bytes<const N: usize>(items: &mut [[u8; N]]) {
    if N == 0 || items.len() <= 1 || items.len() > u32::MAX as usize || N > u32::MAX as usize {
        return;
    }
    unsafe {
        sys::llb_sort_fixed_bytes(items.as_mut_ptr().cast::<u8>(), items.len() as u32, N as u32);
    }
}

/// In-place, 0-recursion insertion sort of `u16` indices.
#[inline]
pub fn sort_u16(arr: &mut [u16]) {
    if arr.len() <= 1 || arr.len() > u32::MAX as usize {
        return;
    }
    unsafe {
        sys::llb_sort_u16(arr.as_mut_ptr(), arr.len() as u32);
    }
}

/// Division-free ASCII satoshi formatter (`pad_frac8 == true` -> `"0.01000000 TEST"`,
/// `pad_frac8 == false` -> `"0.01 BTC"`). Returns the written UTF-8 subslice (excluding NUL).
#[inline]
pub fn format_sats_ascii<'a>(
    amount: u64,
    ticker: &str,
    pad_frac8: bool,
    out: &'a mut [u8],
) -> Option<&'a str> {
    if out.is_empty() || ticker.len() > u32::MAX as usize || out.len() > u32::MAX as usize {
        return None;
    }
    let ticker_ptr = if ticker.is_empty() {
        core::ptr::NonNull::<u8>::dangling().as_ptr()
    } else {
        ticker.as_bytes().as_ptr()
    };
    let written = unsafe {
        sys::llb_format_sats_ascii(
            amount,
            ticker_ptr,
            ticker.len() as u32,
            u8::from(pad_frac8),
            out.as_mut_ptr(),
            out.len() as u32,
        )
    } as usize;
    if written == 0 || written > out.len() {
        None
    } else {
        core::str::from_utf8(&out[..written]).ok()
    }
}

/// Exercises scalar and Option 2 buffer freestanding C99 kernel exports from `liblean_ledger_bitcoin.a`.
pub fn kernel_self_test() -> bool {
    let mut pks = [[0x03u8; 33], [0x02u8; 33]];
    sort_fixed_bytes(&mut pks);
    let mut amt_buf = [0u8; 40];
    let formatted_ok = format_sats_ascii(1_000_000, "TEST", true, &mut amt_buf)
        == Some("0.01000000 TEST");
    // Postfix `pk(K)` (`0x04`) must pass non-malleable + sig-required check
    let ms_ok = miniscript_check_postfix(&[0x04], false, true, true)
        && !miniscript_check_postfix(&[0x01], false, true, true);
    let lt_st = psbt_locktime_step(psbt_locktime_init(), Some(850_000), None);
    let lt_ok = psbt_locktime_finalize(lt_st, 0) == Some(850_000);
    let std_path = [
        bip32_harden(84),
        bip32_harden(0),
        bip32_harden(0),
    ];

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
        && read_compact_size_checked(&[0xFD, 0xFD, 0x00], 1000) == Some((0xFD, 3))
        && read_compact_size_checked(&[0xFD, 0xFC, 0x00], 1000).is_none()
        && bip32_is_hardened(bip32_harden(86))
        && bip32_unharden(bip32_harden(86)) == 86
        && bip32_bolos_depth_ok(10)
        && !bip32_bolos_depth_ok(11)
        && bip32_vanadium_depth_ok(16)
        && !bip32_vanadium_depth_ok(17)
        && bip32_standard_purpose_ok(bip32_harden(86))
        && bip32_check_export_path(&std_path, 0)
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
        && miniscript_older_ok(144)
        && !miniscript_older_ok(0)
        && miniscript_after_ok(500_000_000)
        && !miniscript_after_ok(0x8000_0000)
        && miniscript_andor_branches_valid(0x64, 0x67, 0x68)
        && check_dual_utxo(50_000, &[0x00, 0x14, 0xaa], 50_000, &[0x00, 0x14, 0xaa])
        && pks[0][0] == 0x02
        && formatted_ok
        && ms_ok
        && lt_ok
}

/// Unpacked kernel version triple.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Version {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

pub fn unpack_version(packed: u32) -> Version {
    Version {
        major: packed >> 16,
        minor: (packed >> 8) & 0xFF,
        patch: packed & 0xFF,
    }
}

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn linked_kernel_self_test_and_version() {
        assert_eq!(version_packed(), VERSION_PACKED_EXPECTED);
        assert_eq!(
            check_kernel_version(),
            Ok(Version {
                major: VERSION_MAJOR,
                minor: VERSION_MINOR,
                patch: VERSION_PATCH,
            })
        );
        assert!(kernel_self_test());
    }

    #[test]
    fn option2_buffer_wrappers_behave_safely() {
        let mut pks = [[0x03u8; 33], [0x02u8; 33], [0x02u8; 33]];
        pks[1][32] = 0x99;
        pks[2][32] = 0x11;
        sort_fixed_bytes(&mut pks);
        assert_eq!(pks[0][32], 0x11);
        assert_eq!(pks[1][32], 0x99);
        assert_eq!(pks[2][0], 0x03);

        let mut idx = [9u16, 1, 5, 3];
        sort_u16(&mut idx);
        assert_eq!(idx, [1, 3, 5, 9]);

        let mut buf = [0u8; 40];
        assert_eq!(
            format_sats_ascii(123_450_000, "BTC", false, &mut buf),
            Some("1.2345 BTC")
        );
        assert_eq!(
            format_sats_ascii(123_450_000, "TEST", true, &mut buf),
            Some("1.23450000 TEST")
        );

        let mut amounts = [0u8; 16];
        amounts[..8].copy_from_slice(&100_000u64.to_le_bytes());
        amounts[8..].copy_from_slice(&250_000u64.to_le_bytes());
        assert_eq!(sum_amounts_le64(&amounts), Some(350_000));

        assert!(check_dual_utxo(1_000, &[0x51, 0x20], 1_000, &[0x51, 0x20]));
        assert!(!check_dual_utxo(1_000, &[0x51, 0x20], 1_001, &[0x51, 0x20]));
        assert!(!check_dual_utxo(1_000, &[0x51, 0x20], 1_000, &[0x51, 0x21]));
    }
}

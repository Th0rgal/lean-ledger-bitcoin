# Track S1 Discrepancy & Security Notes: Primitives, BIP-32, Script, and Addresses

**Audited Reference Commits**
- **BOLOS (`LedgerHQ/app-bitcoin`)**: `f010982d3050e02813cd7129bebd68cf2d1f2099`
- **Vanadium (`LedgerHQ/vanadium`)**: `ace8e96982408959dea9e7fbc59ee36e8c54e645` (`apps/bitcoin`)
- **Canonical Lean 4 Specs**: `Spec/Basic.lean`, `Spec/Bip32.lean`, `Spec/Script.lean`

---

## 1. Satoshi Amounts, `MAX_MONEY`, and Integer Overflow (`Spec/Basic.lean`)

| Property | BOLOS `app-bitcoin` | Vanadium `apps/bitcoin` | Canonical Spec (`Spec/Basic.lean`) |
|---|---|---|---|
| Per-UTXO / per-output `MAX_MONEY` check (`2_100_000_000_000_000` sat) | **Yes**: `preprocess_inputs.c:251,291` & `preprocess_outputs.c:141` reject `> BITCOIN_TOTAL_SUPPLY` (`0x6A80`) | **Missing**: `fastpsbt.rs:1052,1120` wraps arbitrary `u64` via `Amount::from_sat` with no `MAX_MONEY` check | Enforced (`ValidAmount a := a ≤ MAX_MONEY`) |
| Running input/output sum overflow protection | **Indirect only**: raw C `uint64_t +=` (`preprocess_inputs.c:258,298`, `preprocess_outputs.c:149`). Avoids `2^64` wrap only because `MAX_N_INPUTS_CAN_SIGN = 512` (`512 * 2.1e15 < 2^64`); total `inputs_total_amount > MAX_MONEY` is only checked in BIP-322 (`bip322_validation.c:57`) | **Vulnerable**: `sign_psbt/analyze.rs:435,469` uses unchecked `u64 +=` (panics V-App in checked builds or wraps mod `2^64` in release builds instead of returning `Result::Err`) | `sumAmounts?` checks every summand `≤ MAX_MONEY`, prevents `UInt64` wraparound, and enforces total `≤ MAX_MONEY` |
| Signed `i64` net-balance accumulation | `transaction_display.c:249` casts `(int64_t) internal_inputs_total - (int64_t) change_total` (safe only because each `< 512 * 2.1e15 < 2^63`) | **Critical bug**: `sign_psbt/analyze.rs:434,460` executes `account_spent_amounts[id] += value as i64` and `-= amount as i64` on unvalidated `u64`s (`≥ 2^63` becomes negative!), and `display.rs:153` computes `-*spent_amount as u64` (panics/wraps on `i64::MIN`) | Unsigned checked arithmetic (`addAmounts?`, `subAmounts?`, `sumAmounts?`) |

---

## 2. Bitcoin CompactSize / VarInt Canonicality (`Spec/Basic.lean`)

- **BOLOS (`src/common/parser_ext.c:67-108` & SDK `varint_read`)**: `dbuffer_read_varint` (used throughout `psbt_parse_rawtx.c` for tx input/output/witness counts and script lengths) and SDK `buffer_read_varint` (`unit-tests/test_buffer.c:111-128`) parse `0xFD`/`0xFE`/`0xFF` little-endian integers **without** checking minimal lower bounds (`≥ 0xFD`, `≥ 0x10000`, `≥ 0x100000000`). Non-minimal encodings such as `0xFD 0xFC 0x00` are accepted.
- **Vanadium (`common/src/fastpsbt.rs:231-250` vs `common/src/psbt/mod.rs:23`)**:
  - `psbt/mod.rs` uses `rust-bitcoin` `VarInt::consensus_decode`, which **rejects** non-minimal CompactSize values.
  - `fastpsbt.rs` (`Cursor::read_compact_size`, used on the active `SIGN_PSBT` hot path) reads `u16`/`u32`/`u64` after `0xFD`/`0xFE`/`0xFF` **without** minimal-range checks, accepting `0xFD 0xFC 0x00`.
  - Additionally, `fastpsbt.rs:1046` hardcodes `wutxo[8] <= 0xfc` when parsing `PSBT_IN_WITNESS_UTXO`, rejecting valid witness UTXOs whose `scriptPubKey` length requires a 3-byte CompactSize (`≥ 253` bytes).
- **Canonical Spec**: `isCanonicalVarInt` and `decodeVarIntCanonical?` enforce strict minimal thresholds (`0..0xFC`, `0xFD..0xFFFF`, `0x10000..0xFFFFFFFF`, `0x100000000..2^64-1`), with machine-checked roundtrip, injectivity, and non-minimal rejection theorems.

---

## 3. Network Parameters & Error Mappings (`Spec/Basic.lean`)

- **Network Selection**:
  - **BOLOS (`Makefile:67-104`)**: Compile-time `COIN` (`bitcoin` / `bitcoin_recovery` Mainnet vs `bitcoin_testnet` Testnet); no dedicated `Regtest` (`"bcrt"`) or `Signet` build targets.
  - **Vanadium (`apps/bitcoin`)**: Hardcoded to Testnet (`app/src/constants.rs`: `COIN_TICKER = "TEST"`, `SILENT_PAYMENT_HRP = "tsp"`, `BIP32_TESTNET_PUBKEY_VERSION = 0x043587CF`), with a minor internal inconsistency between `bitcoin::params::Params::TESTNET4` (`common/src/account.rs:78`) and `bitcoin::Network::Testnet` (`app/src/handlers/sign_psbt/display.rs:167`).
- **Error Taxonomy**:
  - **BOLOS (`src/boilerplate/sw.h`, `src/error_codes.h`)**: Coarse 16-bit APDU status words (`0x6700`, `0x6982`, `0x6985`, `0x6A80`, `0x6A82`, `0x6A86`, `0x6A87`, `0x6B00`, `0x6D00`, `0x6E00`, `0xB000..0xB008`, plus continuation `0xE000` and success `0x9000`).
  - **Vanadium (`common/src/errors.rs`)**: 59-variant CBOR `#[n(0..58)]` `Error` enum (`AppError`).
  - `SpecError` provides a deterministic total projection onto both `BolosStatusWord` and `AppError` and proves no `SpecError` maps to `0x9000` (`SW_OK`) or `0xE000`.

---

## 4. BIP-32 Depth Limits & `GET_EXTENDED_PUBKEY` Security Policy (`Spec/Bip32.lean`)

1. **Maximum Path Depth & `u8` Truncation Bug**:
   - **BOLOS (`src/constants.h:111-117`)**: `MAX_BIP388_XPUB_DERIVATION_STEPS = 8`, `MAX_BIP32_PATH_STEPS = 10` (`> 10` rejected with `0x6A80`).
   - **Vanadium (`app/src/bip32.rs:18`, `app/src/handlers/get_extended_pubkey.rs:138,161`)**:
     - `KeyTree::Standard` enforces `MAX_BIP32_PATH_LEN = 16` (`Error::DerivationPathTooLong`).
     - **`KeyTree::Resident` Off-by-One Bug**: `get_extended_pubkey.rs:138` checks `if bip32_path.0.len() > 256` instead of `> 255` (`u8::MAX`), and line 161 casts `let depth = bip32_path.0.len() as u8;`. At `len == 256`, `depth` wraps to `0u8`, emitting a malformed serialized xpub with `depth = 0` and non-zero `parentFingerprint`/`childNumber` (violating BIP-32). `Spec/Bip32.lean` enforces `MAX_BIP32_BYTE_DEPTH = 255`.
2. **Silent Extended Public Key Export Policy — Critical Security Regression in Vanadium**:
   - **BOLOS (`src/handler/get_extended_pubkey.c:36-143`)**: `is_path_safe_for_pubkey_export` allows `display == false` **only** for:
     - `m/{44',49',84',86',87',45'}/coin_type'/account'/...` (`account ≤ 100`, remaining steps unhardened),
     - `m/48'/coin_type'/account'/{1',2'}/...` (`account ≤ 100`, remaining steps unhardened),
     - `m/4541509'/1112098098'` (Electrum encryption exception).
     All other paths (root `m`, unhardened prefixes, too-short prefixes like `m/84'` or `m/84'/0'`, wrong `coin_type'`, `account > 100`, `352'`, hardened suffixes) return `SW_NOT_SUPPORTED (0x6A82)` when `display == false`, and trigger an unusual-path warning + interactive confirmation when `display == true`.
   - **Vanadium (`app/src/handlers/get_extended_pubkey.rs:131-229` & `vm/src/handlers/lib/ecall.rs:440`)**: Performs **zero** path-safety filtering and runs under an unrestricted VM curve manifest. With `display == false`, a host can silently export *any* extended pubkey up to depth 16 (including master `m`, unhardened `m/0`, cross-coin paths, identity keys `m/1229210958'/i`, and BIP-352 xpubs `m/352'/1'/n'/1'/0`), enabling silent cross-account/cross-chain privacy de-anonymization.
3. **Serialization Wire Format**:
   - **BOLOS**: Returns 111–112 ASCII Base58Check characters (`78` bytes + `4`-byte double-SHA256 checksum).
   - **Vanadium**: Returns raw `78`-byte binary `ExtendedPubKey` (+ optional ECDSA identity signature).

---

## 5. Script Classification, `MINIMALDATA`, and Bech32 vs Bech32m (`Spec/Script.lean`)

1. **`OP_RETURN` External Output Failure in Vanadium**:
   - **BOLOS (`src/common/script.c:139-203`)**: `format_opscript_script` accepts standard `OP_RETURN` outputs (`≤ 83` bytes, bare `OP_RETURN` or `1..5` minimal pushes without `OP_PUSHDATA2`/`4`) for user verification.
   - **Vanadium (`app/src/handlers/sign_psbt/display.rs:167`)**: Calls `bitcoin::Address::from_script`, which fails on every `OP_RETURN` script with `Error::AddressFromScriptFailed`, preventing Vanadium from signing any PSBT containing an `OP_RETURN` output.
2. **SegWit `v0` Unknown-Length Two-Stage Check**:
   - BOLOS `get_script_type` (`script.c:107-120`) classifies `OP_0 0x02 <2B>` as `SCRIPT_TYPE_UNKNOWN_SEGWIT` and only rejects it later inside `segwit_addr_encode` (`segwit_addr.c:188`: `witver == 0 && witprog_len != 20 && witprog_len != 32`). `Spec/Script.lean` models both `StandardScript.unknownWitness` and strict `isValidSegwitProgram` / `encodeSegwitAddr?` / `decodeSegwitAddr?` segregation.
3. **BIP-173 / BIP-350 SegWit vs BIP-352 Silent Payments**:
   - SegWit strictly segregates `v0 ↔ Bech32` (`20` or `32` bytes, `≤ 90` chars) from `v1..v16 ↔ Bech32m` (`2..40` bytes, `≤ 90` chars).
   - BIP-352 Silent Payments (`vanadium/apps/bitcoin/common/src/silent_payments/address.rs`) uses **Bech32m** at version `0` (`sp1q...` / `tsp1q...`) with a `66`-byte payload (`116–117` chars, max `1023`). `Spec/Script.lean` separates `encodeBech32Raw?`/`decodeBech32Raw? (maxLen)` from SegWit's `encodeSegwitAddr?`/`decodeSegwitAddr?` so both protocols remain sound and composable.

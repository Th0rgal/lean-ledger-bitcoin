# Vanadium V-App Integration, RV32IMAC Kernel Link & Differential Regression Report

- **Shard**: Wave 3 Shard T2 (`llb-w3-t2-vanadium-vapp`)
- **Repository / Branch**: `Th0rgal/lean-ledger-bitcoin` (`wave3/test-t2-vanadium`)
- **Base Commit (`lean-ledger-bitcoin`)**: `0331e64d0e282424fed3a58fa840a31226426958`
- **Compiler Toolchain (`turbo-lean` `feat/ledger-32bit-llvm`)**: `94f42551de5b1910a8c71cd7981008584dc841d7`
- **Audited & Linked `LedgerHQ/vanadium` Commit**: `ace8e96982408959dea9e7fbc59ee36e8c54e645` (`apps/bitcoin/{common,app,client}`)

---

## 1. Executive Summary

| Verification Layer | Command / Target | Result | Details |
| :--- | :--- | :--- | :--- |
| **Freestanding C99 Codegen & Audit** | `./scripts/build-freestanding.sh` | **5 / 5 targets passed** | `thumbv6m`, `thumbv8m.main`, `riscv32imac`, `x86_64` (BOLOS & Vanadium); `23` exported decls (`22` `llb_*` functions + `MAX_MONEY_U64`), `0` undefined symbols, `0` heap allocs, `0 B` RV32IMAC stack frame |
| **`llb-vanadium-ffi` Host Unit Suite** | `cargo test --manifest-path ffi/vanadium/Cargo.toml` | **16 / 16 passed** | Exercises all `22` freestanding C99 kernel exports + `kernel_self_test()` |
| **`llb-vanadium-ffi` RV32IMAC Cross-Build** | `cargo check` & `cargo build --release --manifest-path ffi/vanadium/Cargo.toml --target riscv32imac-unknown-none-elf` | **Passed (`exit 0`)** | `#![no_std]` crate links `ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a` cleanly |
| **`vnd-bitcoin-common` Official Suite** | `cargo test` (`apps/bitcoin/common`) | **78 / 78 passed** | `74` unit + `1` BIP-352 + `2` BIP-374 + `1` BIP-375 tests |
| **`vnd-bitcoin` V-App Linked Host Suite** | `cargo test` (`apps/bitcoin/app` + `llb-vanadium-ffi`) | **79 / 79 passed** | `78` upstream V-App unit tests + `1` linked Lean C99 kernel verification test |
| **`vnd-bitcoin` RV32IMAC V-App ELFs** | `cargo build --release --target riscv32imac-unknown-none-elf` (`target_vanadium_ledger` & `target_vanadium_ledger,autoapprove`) | **2 / 2 ELFs built** | `ELF32`, `RISC-V`, `RVC, soft-float ABI`, exact **2 `LOAD` segments** (`R E` + `RW`), `llb_*` symbols linked into `vnd-bitcoin` |
| **`vnd-bitcoin-client` + Speculos Flex E2E** | `cargo test` (`apps/bitcoin/client`, unit + `--features speculos-tests,debug`) | **9 / 9 passed** | `5` client/CLI unit tests + `4` full Speculos Flex VM + RV32IMAC `vnd-bitcoin` E2E integration tests (`23.67s`) |
| **Pure Lean Differential & Bug Suite** | `timeout 180s lake env lean Tests/VanadiumDifferential.lean` | **15 / 15 sections passed** | `6` official Vanadium differential vector suites (`A.1`–`A.6`) + **all `9` upstream bug regressions (`VND-BUG-001`..`VND-BUG-009`)** (`11` machine-checked theorems + executable evaluations, `0 sorry`) |

---

## 2. Freestanding C99 Build & `ffi/vanadium` (`llb-vanadium-ffi`) Verification

### 2.1 `./scripts/build-freestanding.sh` Multi-Target Codegen & Stack Audit

Running `./scripts/build-freestanding.sh` compiled `BitcoinLedger.FreestandingKernels` via `turbo-lean` (`lean --freestanding -c`) into standalone C99 (`build/freestanding/BitcoinLedger_FreestandingKernels.c`) and built static archives across all 5 hardware targets:

- **Freestanding Audit (`--freestanding-audit`)**:
  - `schemaVersion`: `1`
  - `decls`: `23` (`22` `@[export llb_*]` functions + `l_BitcoinLedger_FreestandingKernels_MAX__MONEY__U64`)
  - `undefinedSymbols`: `0`
  - `malloc` / `free` / `lean_alloc_*` / `lean_inc` / `lean_dec` references: **`0`**
- **Static Archives & Per-Architecture Stack Usage**:
  - `thumbv6m-none-eabi` (Nano S+ Cortex-M0+): max frame **`32 B`**
  - `thumbv8m.main-none-eabi` (Stax / Flex / Apex P Cortex-M33): max frame **`20 B`**
  - `riscv32imac-unknown-none-elf` (Vanadium V-App VM): max frame **`0 B`** (all `22` functions execute purely in registers with zero stack spill!) -> `ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a`
  - `x86_64-unknown-linux-gnu` (host test archives for `ffi/bolos` and `ffi/vanadium`): max frame **`48 B`** -> `ffi/vanadium/build/host/liblean_ledger_bitcoin.a`
- **`llvm-nm` Symbol Audit (`ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a`)**:
  - Verified all `22` defined text (`T`) symbols (`llb_version_packed`, `llb_valid_amount`, `llb_checked_add_sats_ok`, `llb_checked_add_sats_val`, `llb_checked_sub_sats_ok`, `llb_checked_sub_sats_val`, `llb_varint_encoded_len`, `llb_varint_prefix_is_canonical`, `llb_bip32_is_hardened`, `llb_bip32_harden`, `llb_bip32_unharden`, `llb_bip32_bolos_depth_ok`, `llb_bip32_vanadium_depth_ok`, `llb_bip32_standard_purpose_ok`, `llb_witness_opcode_to_version`, `llb_segwit_program_valid`, `llb_bech32_polymod_step`, `llb_minimal_push_opcode_ok`, `llb_sighash_type_valid`, `llb_taproot_sighash_valid`, `llb_merkle_depth_index_ok`, `llb_bolos_sw_for_error`) plus `T l_BitcoinLedger_FreestandingKernels_MAX__MONEY__U64`, with **`0` undefined (`U`) symbols**.

### 2.2 `ffi/vanadium` (`llb-vanadium-ffi`) Host Tests & RV32IMAC Cross-Compilation

`ffi/vanadium/src/lib.rs` was strengthened to bind all `22` freestanding C99 kernel symbols, expose safe `#![no_std]` Rust wrappers plus `kernel_self_test() -> bool` (suitable for V-App startup self-verification inside RV32IMAC), and test every exported kernel alongside Vanadium ECALL wrappers on host:

```text
$ cargo test --manifest-path ffi/vanadium/Cargo.toml
running 16 tests
test tests::kernel_version_check_ok ... ok
test tests::ecall_numbers_match_vanadium ... ok
test tests::kernel_satoshi_arithmetic_guards_overflow ... ok
test tests::kernel_script_sighash_merkle_and_sw_exports ... ok
test tests::kernel_version_packed_matches_contract ... ok
test tests::ecdsa_sign_verify_roundtrip ... ok
test tests::kernel_varint_and_bip32_guards ... ok
test tests::derive_hd_node_wrapper ... ok
test tests::kernel_version_unpacks ... ok
test tests::master_fingerprint_wrapper ... ok
test tests::random_bytes_wrapper ... ok
test tests::schnorr_sign_verify_roundtrip ... ok
test tests::secp256k1_point_and_scalar_wrappers ... ok
test tests::sha256_ecall_id_composition ... ok
test tests::xsend_xrecv_transport ... ok
test tests::sha256_matches_fips_vectors ... ok

test result: ok. 16 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s
```

Cross-compilation for Vanadium's target triple (`riscv32imac-unknown-none-elf`):

```text
$ cargo check --manifest-path ffi/vanadium/Cargo.toml --target riscv32imac-unknown-none-elf
Finished `dev` profile [unoptimized + debuginfo] target(s)

$ cargo build --release --manifest-path ffi/vanadium/Cargo.toml --target riscv32imac-unknown-none-elf
Finished `release` profile [optimized] target(s)
```

---

## 3. Linking `liblean_ledger_bitcoin.a` into `LedgerHQ/vanadium` (`apps/bitcoin`) & Official Test Suite Results

In an isolated copy of `LedgerHQ/vanadium` (`ace8e96982408959dea9e7fbc59ee36e8c54e645`), `llb-vanadium-ffi` (linking `liblean_ledger_bitcoin.a`) was wired into `apps/bitcoin/app/Cargo.toml` and `apps/bitcoin/app/src/main.rs` (invoking `assert!(llb_vanadium_ffi::kernel_self_test())` during V-App initialization and message dispatch).

### 3.1 Official `LedgerHQ/vanadium` `apps/bitcoin` Test Counts (`166 / 166` Passed)

| Crate / Target | Command | Passed | Failed | Notes |
| :--- | :--- | :---: | :---: | :--- |
| `vnd-bitcoin-common` (lib) | `cargo test --lib` (`apps/bitcoin/common`) | **74** | 0 | `bip388`, `fastpsbt`, `por`, `psbt`, `script`, `taproot` |
| `vnd-bitcoin-common` (BIP-352) | `cargo test --test bip352` | **1** | 0 | Official BIP-352 Silent Payments test vectors |
| `vnd-bitcoin-common` (BIP-374) | `cargo test --test bip374` | **2** | 0 | Official BIP-374 DLEQ generate & verify vectors |
| `vnd-bitcoin-common` (BIP-375) | `cargo test --test bip375` | **1** | 0 | Official BIP-375 PSBT Silent Payments vectors |
| `vnd-bitcoin` (`apps/bitcoin/app`) | `cargo test` (host x86_64 + `liblean_ledger_bitcoin.a`) | **79** | 0 | All `78` upstream V-App handler/PSBT/MuSig2/SP tests + `1` `test_linked_lean_freestanding_kernels` |
| `vnd-bitcoin-client` (unit) | `cargo test --lib --bins` (`apps/bitcoin/client`) | **5** | 0 | `2` library tests + `3` CLI binary tests |
| `vnd-bitcoin-client` (Speculos E2E) | `cargo test --test integration_test --features speculos-tests,debug` | **4** | 0 | Runs RV32IMAC `vnd-bitcoin` inside `vanadium-ledger` on Speculos Flex (`23.67s`) |
| **Total** | | **166** | **0** | **100% pass rate with Lean C99 kernel linked** |

### 3.2 RV32IMAC V-App Binary & Speculos Flex E2E Details

- **RV32IMAC V-App ELF Verification**:
  - Built both `cargo build --release --target riscv32imac-unknown-none-elf --features target_vanadium_ledger` and `--features target_vanadium_ledger,autoapprove` in `apps/bitcoin/app`.
  - `readelf -h -l target/riscv32imac-unknown-none-elf/release/vnd-bitcoin` confirmed:
    - Class / Arch / Flags: `ELF32`, `RISC-V`, `0x1, RVC, soft-float ABI`
    - Entry point: `0x00020a7c`
    - Program Headers: exact **2 `LOAD` segments** required by Vanadium's V-App loader (`LOAD 0x00020000 R E` code/rodata + `LOAD 0x00130000 RW` data/bss).
  - `llvm-nm` confirmed `llb_version_packed`, `llb_valid_amount`, `llb_checked_add_sats_ok`, `llb_checked_add_sats_val`, `llb_checked_sub_sats_ok`, `llb_checked_sub_sats_val`, `llb_varint_prefix_is_canonical`, `llb_bip32_vanadium_depth_ok`, `llb_minimal_push_opcode_ok`, `llb_sighash_type_valid`, `llb_taproot_sighash_valid`, etc. linked directly in the RV32IMAC ELF `.text` segment.
- **Speculos Flex VM + Vanadium VM E2E Tests (`apps/bitcoin/client/tests/integration_test.rs`)**:
  1. `test_get_fingerprint`: Booted `vanadium-ledger` inside Speculos (`--model flex`), loaded RV32IMAC `vnd-bitcoin` (executing `llb_vanadium_ffi::kernel_self_test()` on RV32IMAC startup), and verified master fingerprint `0xf5acc2fd`... `ok`
  2. `test_e2e_sign_transaction`: Registered Taproot (`tr(@0/**)`), WPKH (`wpkh(@0/**)`), and P2PKH (`pkh(@0/**)`) policies, funded via Bitcoin Core / `corepc-node` logic, signed multi-input PSBT on RV32IMAC `vnd-bitcoin`, and verified witness signatures... `ok`
  3. `test_e2e_send_to_silent_payment_address`: Signed BIP-375 PSBT sending to BIP-352 `sp1qq...` address with on-device ECDH share & BIP-374 DLEQ proof verification... `ok`
  4. `test_e2e_silent_payment_account`: Registered BIP-392 `sp(@0)` account, exported `tspscan1...` scan key, derived labeled & unlabeled `tsp1...` addresses, and spent Silent Payment outputs via PSBT... `ok`

---

## 4. Pure Lean Differential & Upstream-Bug Regression Suite (`Tests/VanadiumDifferential.lean`)

Running `timeout 180s lake env lean Tests/VanadiumDifferential.lean` executes pure Lean 4 implementations of SHA-256, HMAC-SHA256, SHA-512, HMAC-SHA512, RIPEMD-160, and affine secp256k1 wired into `BitcoinLedger.*`, testing both official Vanadium vectors (`Part A`) and all 9 cataloged Vanadium upstream bugs (`Part B`):

```text
$ timeout 180s lake env lean Tests/VanadiumDifferential.lean
=== Running Tests/VanadiumDifferential.lean ===
  [PASS] A.1 BIP-32 Master Fingerprint, Standard/Resident tpubs & Path Policy (15 vectors)
  [PASS] A.2 BIP-388 Wallet Policies, PoR HMAC & Taproot/MuSig2/Inheritance Addresses (5 suites)
  [PASS] A.3 BIP-379 Miniscript Combinators & Stacked Wrappers (7 templates)
  [PASS] A.4 PSBTv0->v2 Normalization, UTXO/Fee/Change & BIP-341 TapSighash Vector
  [PASS] A.5 Two-Round BIP-327 MuSig2 Session Lifecycle & BIP-340 Schnorr Aggregation
  [PASS] A.6 BIP-352/374/375/392 Silent Payments & BIP-137/BIP-322 Message Signing
  [PASS] B.1 [VND-BUG-001] Andor(X,Y,Z) Canonical OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF
  [PASS] B.2 [VND-BUG-002] Checked UInt64 Satoshi Sums & MAX_MONEY / 2^63 Sign-Flip Defense
  [PASS] B.3 [VND-BUG-003] CVE-2020-14199 Dual-UTXO Cross-Check (nonWitnessUtxo vs witnessUtxo)
  [PASS] B.4 [VND-BUG-004] BIP-370 Dual-Locktime Input, Zero Height & Fallback Isolation
  [PASS] B.5 [VND-BUG-005] sh(wsh(...)) Registration vs Derivation Consistency
  [PASS] B.6 [VND-BUG-006] BIP-379 Type, Malleability, Sig, Timelock, Resource & Internal-Key Gates
  [PASS] B.7 [VND-BUG-007] BIP-32 KeyTree::Resident depth == 256 u8-Wraparound Rejection
  [PASS] B.8 [VND-BUG-008] MuSig2 Round-2 Self-Pubnonce Tamper Rejection & Session Burn
  [PASS] B.9 [VND-BUG-009] GetVersion No-Panic, OP_RETURN, Canonical VarInt & >=253B WitnessUtxo
=== Summary: 15/15 differential & VND-BUG-001..009 sections passed ===
```

### 4.1 Part A — Official Vanadium Differential Vector Coverage

- **`A.1` (`checkBip32Vectors`)**: Exact match on Speculos master fingerprint `0xf5acc2fd` (`KeyTree::Standard`), test resident fingerprint `0xad85d955` (`KeyTree::Resident`), all `7` `KeyTree::Standard` `tpub` vectors from `get_extended_pubkey.rs:285-293` (`m/44'/1'/0'`, `m/44'/1'/10'`, `m/44'/1'/2'/1/42`, `m/48'/1'/4'/1'/0/7`, `m/49'/1'/1'/1/3`, `m/84'/1'/2'/0/10`, `m/86'/1'/4'/1/12`), `2` account roots (`m/84'/1'/0'`, `m/86'/1'/0'`), both `KeyTree::Resident` vectors (`m/44'/1'/0'`, `m/44'/1'/0'/3`), wire path round-trip, and `vanadiumExpubPolicyConfig` / `vanadiumHardenedExpubPolicyConfig` path classification.
- **`A.2` (`checkWalletPolicyAndTaprootVectors`)**: SLIP-21 `"Proof of Registration"` HMAC-SHA256 registration & `tb1qzdr7s2sr0dwmkwx033r4nujzk86u0cy6fmzfjk` derivation (`account.rs:154-173`, `get_address.rs:186-219`), `tr(musig(@0,@1)/**)` index-3 P2TR `5120c1fdfebed0...` (`script.rs:518-536`), both `Simple inheritance` TapTree policies from `register_account.rs:383-443` (including BIP-341 NUMS `.unspendable` key classification), `pkh(@0/**)` child pubkey `02ee8608...`, and `wsh(sortedmulti(2,@0/**,@1/**))`.
- **`A.3` (`checkMiniscriptCombinators`)**: Registration + P2WSH/P2TR `scriptPubKey` derivation across `7` BIP-379 Miniscript descriptors (`andor`, `or_d`, `t:or_c`, `and_b`, `thresh` with `sln:older`, `and_v` with `v:sha256`, and Tapscript `multi_a`).
- **`A.4` (`checkVanadiumTaprootPsbtVector`)**: Full PSBTv0-to-PSBTv2 normalization, input/change script derivation (`m/86'/1'/0'/1/3` and `m/86'/1'/0'/1/2`), UTXO/change/fee validation (`sumInputs = 10_009_567`, `sumOutputs = 10_009_389`, `fee = 178`), and exact BIP-341 `TapSighash` match (`75c96fb06a12db4cd011d8c95a5995db758a4f2837a22f30f0f579619a4466f3`) from `sign_psbt/tests/basic.rs:95-143`.
- **`A.5` (`checkMusig2EndToEndVector`)**: Full 2-of-2 Taproot-tweaked BIP-327 MuSig2 Round-1 (`executeRound1Pass`) & Round-2 (`executeRound2Pass`) session lifecycle, session replay burn (`lookupActive == none`), partial signature aggregation, and real BIP-340 Schnorr verification (`bip340VerifyBytes`).
- **`A.6` (`checkSilentPaymentsAndMessageSigning`)**: Official BIP-352 mainnet `sp1qq...` Bech32m round-trip, BIP-375 `finalizePsbtSilentPayments` output P2TR derivation + BIP-374 `dleqVerify` verification, BIP-392 `tspscan` export/decode + change-label (`m = 0`) rejection, BIP-137 `bitcoinSignedMessageDigest`, and BIP-322 virtual PSBT authorization + tamper rejection (`.bip322ChallengeTxidMismatch`).

### 4.2 Part B — Upstream Bug Regression Matrix (`VND-BUG-001` .. `VND-BUG-009`)

| Bug ID | Severity | Vanadium Upstream Flaw (`ace8e969`) | `BitcoinLedger.*` Theorem & Executable Regression in `Tests/VanadiumDifferential.lean` | Status |
| :--- | :--- | :--- | :--- | :---: |
| **`VND-BUG-001`** | CRITICAL | `script.rs:367-373` compiled `Andor(X,Y,Z)` as `[X] OP_NOTIF [Y] OP_ELSE [Z] OP_ENDIF` (inverted branches) | `vnd_bug_001_andor_canonical_branch_order` + `checkVndBug001`: proves `.andor x y z` emits canonical `[X] 0x64 [Z] 0x67 [Y] 0x68` and differs strictly from Vanadium's swapped bytes | **PASS** |
| **`VND-BUG-002`** | CRITICAL | `fastpsbt.rs` / `analyze.rs` / `display.rs` allowed `> MAX_MONEY`, unchecked `u64 +=` wraparound, and `2^63 as i64` sign-flip | `vnd_bug_002_freestanding_and_basic_reject_overflow_and_sign_flip` + `checkVndBug002`: proves & evaluates rejection of `2^63` (`i64::MIN`), `u64::MAX` wraparound, `15M + 7M BTC > MAX_MONEY`, and negative fees with `.amountExceedsMaxSupply` / `.negativeFeeOutputsExceedInputs` | **PASS** |
| **`VND-BUG-003`** | HIGH | `analyze.rs:223-243, 304-316` omitted `non_witness_utxo.output[vout] == witness_utxo` cross-check (CVE-2020-14199 class) | `vnd_bug_003_dual_utxo_mismatch_always_rejected` + `checkVndBug003`: proves & evaluates `.dualUtxoMismatch` whenever `witnessUtxo` spoofs either `amount` or `scriptPubKey` alongside a valid `nonWitnessUtxo` | **PASS** |
| **`VND-BUG-004`** | HIGH | `fastpsbt.rs:602-634` rejected valid dual-locktime single inputs, accepted `height == 0`, and let `fallback >= 500M` override height `h` | `vnd_bug_004_bip370_locktime_regressions` + `checkVndBug004`: proves single-input dual locktime succeeds (`800_000`), `height == 0` fails (`.locktimeConflictOrInvalid`), and `fallback = 600_000_000` never overrides input height `850_000` | **PASS** |
| **`VND-BUG-005`** | MEDIUM | `register_account.rs` registered `sh(wsh(...))` PoRs that `script.rs` permanently rejected with `InvalidScriptContext` | `vnd_bug_005_vanadium_profile_rejects_sh_wsh_at_registration` + `checkVndBug005`: proves `vanadiumAppProfile` rejects `sh(wsh(...))` upfront at registration (no stranded PoR), while `canonicalLedgerProfile` & `bolosAppProfile` both register and derive 23-byte P2SH cleanly | **PASS** |
| **`VND-BUG-006`** | MEDIUM | `bip388` / `register_account.rs` omitted BIP-379 `B/V/K/W` types, malleability (`m`), sig (`s`), timelock mix (`k`), BIP-68 bits, ops limit & internal-key check | `vnd_bug_006_miniscript_bip379_sanity_gates` + `checkVndBug006`: proves & evaluates `.invalidMiniscriptType`, `.miniscriptMalleable`, `.miniscriptMissingSignature`, `.miniscriptTimelockMix`, `.invalidTimelockRange`, `.miniscriptResourceLimit`, and `.missingInternalKey` | **PASS** |
| **`VND-BUG-007`** | MEDIUM | `get_extended_pubkey.rs:138, 161` checked `len > 256` instead of `> 255`, wrapping `256 as u8 -> depth = 0` on `KeyTree::Resident` | `vnd_bug_007_depth_256_rejected_without_u8_wraparound`, `vnd_bug_007_derive_and_eval_reject_depth_256` + `checkVndBug007`: proves `depth == 256` is rejected with `.bip32PathTooLong` and wrapped `depth = 0` xpubs with non-zero parentFp/childNum fail deserialization | **PASS** |
| **`VND-BUG-008`** | LOW/MED | `musig_signing.rs:463-485` discarded Round-2 recomputed `_pubnonce` without comparing against `PSBT_IN_MUSIG2_PUB_NONCE` | `vnd_bug_008_corrupted_self_pubnonce_rejected` + `checkVndBug008`: proves & evaluates that tampered `psbtMyPubnonce` returns `.pubnonceMismatch` AND atomically burns the session (`lookupActive == none`) | **PASS** |
| **`VND-BUG-009`** | LOW | `main.rs:26` panicked on `GetVersion`; `display.rs:167` failed on `OP_RETURN`; `fastpsbt.rs` accepted non-minimal VarInts & rejected `>= 253` B witness UTXO scripts | `vnd_bug_009_get_version_total_and_state_preserving`, `vnd_bug_009_non_minimal_compact_size_rejected` + `checkVndBug009`: proves `GetVersion` never panics/mutates state, non-minimal CompactSize prefixes (`0xFD/0xFE/0xFF`) fail, valid `OP_RETURN` succeeds while non-minimal/oversized `OP_RETURN` fails, and `300`-byte witness UTXO `scriptPubKey` succeeds | **PASS** |

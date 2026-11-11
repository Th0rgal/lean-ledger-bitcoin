# BOLOS Integration & Differential Conformance Report (`LedgerHQ/app-bitcoin`)

- **Shard**: Wave 3 Shard T1 (`llb-w3-t1-bolos-speculos`)
- **`Th0rgal/lean-ledger-bitcoin` Base Commit**: `0331e64d0e282424fed3a58fa840a31226426958` (`wave3/test-t1-bolos`)
- **`turbo-lean` Toolchain Commit**: `94f42551de5b1910a8c71cd7981008584dc841d7` (`feat/ledger-32bit-llvm`)
- **`LedgerHQ/app-bitcoin` Audited Commit**: `f010982d3050e02813cd7129bebd68cf2d1f2099` (`v2.6.0`)
- **`bitcoind` E2E Regtest Daemon**: Bitcoin Core `v32.1`

---

## 1. Executive Summary

All four Wave 3 Shard T1 verification gates passed with zero failures and zero unproven axioms:

| Verification Gate | Command / Harness | Result |
|---|---|---|
| **1. Freestanding C99 & Multi-Target Cross-Compilation** | `./scripts/build-freestanding.sh` | **PASS** — 4 targets (`thumbv6m`, `thumbv8m.main`, `riscv32imac`, `x86_64`), 23 declarations, `0` undefined symbols, `0` heap allocators, max stack `<= 48 B` (`< 1024 B` budget) |
| **2. Freestanding BOLOS FFI Harness & ARM Cross-Links** | `make -C ffi/bolos test` | **PASS** — `75/75` host FFI assertions + `3/3` freestanding ARM Thumb ELF cross-links (`clang` Cortex-M0+, `clang` Cortex-M33, `arm-none-eabi-gcc` Cortex-M0+) |
| **3. `LedgerHQ/app-bitcoin` Linked Kernel C Unit + Speculos Suites** | `ctest` + Speculos `pytest` (`tests/`, `tests_mainnet/`) | **PASS** — `31/31` C unit test suites (`100%`, `0.51s`) + `279` Speculos integration tests passed (`277 passed, 5 skipped, 0 failed` in `tests/` including legacy `*_v1.py` & `bitcoind` E2E + `2 passed, 0 failed` in `tests_mainnet/`) |
| **4. Pure-Lean Differential Conformance & Axiom Audit** | `timeout 180s lake env lean Tests/BolosDifferential.lean` | **PASS** — `9` conformance suites covering all `10` `BitcoinLedger.*` modules, `#guard allBolosDifferentialChecksPass`, kernel `rfl` proofs, `1,425` declarations audited with `0 sorryAx` |

---

## 2. Freestanding C99 & BOLOS Cross-Link Verification

### 2.1 `./scripts/build-freestanding.sh`

`lean-native emit-freestanding-c-lib --input BitcoinLedger/FreestandingKernels.lean` emitted freestanding C99/LLVM IR and static archives for **23 declarations**:
- `llb_version_packed` (`0x00020401`) + `MAX_MONEY_U64` (`2,100,000,000,000,000`)
- 21 additional `@[export llb_*]` decision/validation kernels (`llb_valid_amount`, `llb_checked_add_sats_ok`, `llb_checked_add_sats_val`, `llb_checked_sub_sats_ok`, `llb_checked_sub_sats_val`, `llb_varint_encoded_len`, `llb_varint_prefix_is_canonical`, `llb_bip32_is_hardened`, `llb_bip32_harden`, `llb_bip32_unharden`, `llb_bip32_bolos_depth_ok`, `llb_bip32_vanadium_depth_ok`, `llb_bip32_standard_purpose_ok`, `llb_witness_opcode_to_version`, `llb_segwit_program_valid`, `llb_bech32_polymod_step`, `llb_minimal_push_opcode_ok`, `llb_sighash_type_valid`, `llb_taproot_sighash_valid`, `llb_merkle_depth_index_ok`, `llb_bolos_sw_for_error`).

Cross-compilation and symbol/stack audits across all 4 hardware targets:

| Target Triple | Static Archive | Undefined Symbols | Heap Symbols (`malloc`/`lean_alloc_*`) | Worst Stack Frame | Budget (`< 1024 B`) |
|---|---|---:|---:|---:|---|
| `thumbv6m-none-eabi` (Ledger Nano X / ST33 Cortex-M0+) | `ffi/bolos/build/thumbv6m/liblean_ledger_bitcoin.a` | `0` | `0` | `32 bytes` | PASS |
| `thumbv8m.main-none-eabi` (Nano S+ / Stax / Flex / Apex Cortex-M33/M35P) | `ffi/bolos/build/thumbv8m.main/liblean_ledger_bitcoin.a` | `0` | `0` | `20 bytes` | PASS |
| `riscv32imac-unknown-none-elf` (Vanadium V-App VM) | `ffi/vanadium/build/riscv32imac/liblean_ledger_bitcoin.a` | `0` | `0` | `0 bytes` | PASS |
| `x86_64-unknown-linux-gnu` (Host C Unit Test Harness) | `ffi/bolos/build/host/liblean_ledger_bitcoin.a` | `0` | `0` | `48 bytes` | PASS |

### 2.2 `make -C ffi/bolos test`

1. **Host FFI & TCB Mock Verification (`ffi/bolos/build/test_bolos_ffi_host`)**:
   - **75 checks, 0 failures** across 9 test groups:
     - `test_kernel_version_abi`: `llb_version_packed() == 0x00020401` and all 21 `llb_*` kernels verified on boundary inputs.
     - `test_fail_closed_without_tcb`: fail-closed `LLB_ERR_NO_TCB` before `llb_bolos_set_tcb` and after `llb_bolos_set_tcb(NULL)`.
     - `test_tcb_table_validation`: rejects incomplete TCB callback tables (`LLB_ERR_INVALID_ARG`).
     - `test_sha256_vectors`: NIST FIPS 180-4 empty, `"abc"`, 56-byte multi-block, double-SHA256 (`SHA256d("")`), and null-pointer guard checks.
     - `test_derive_bip32`: path depth cap (`depth <= 10`), master derivation (`depth == 0`), multi-step hardened derivation, and child-key clearing on syscall failure.
     - `test_ecfp`: compressed (`33 B`) & uncompressed (`65 B`) secp256k1 pubkeys, invalid prefix rejection, ECDSA DER bounds (`<= 72 B`), and BIP-340 Schnorr `64 B` signatures.
     - `test_rng`: CSPRNG output and zero-length guard.
     - `test_io_exchange`: APDU TX/RX round-trip and buffer overflow rejection.
     - `test_ui_review`: genuine user approval (`true`), rejection (`false`), and null-string rejection.
2. **Freestanding Bare-Metal ARM Thumb Cross-Links (`-nostdlib -Wl,--gc-sections`)**:
   - `build/test_bolos_ffi_thumbv6m_clang.elf` (`clang --target=thumbv6m-none-eabi -mcpu=cortex-m0`): `0` undefined symbols, `llb_version_packed` linked.
   - `build/test_bolos_ffi_thumbv8m_clang.elf` (`clang --target=thumbv8m.main-none-eabi -mcpu=cortex-m33`): `0` undefined symbols, `llb_version_packed` linked.
   - `build/test_bolos_ffi_thumbv6m_arm_gcc.elf` (`arm-none-eabi-gcc -mthumb -mcpu=cortex-m0`): `0` undefined symbols, `llb_version_packed` linked.

---

## 3. `LedgerHQ/app-bitcoin` Integration, C Unit Tests (`ctest`), & Speculos Suites (`pytest`)

### 3.1 C Handlers Wired to `liblean_ledger_bitcoin.a`

In the isolated `LedgerHQ/app-bitcoin` (`f010982d3050e02813cd7129bebd68cf2d1f2099`) integration build, `liblean_ledger_bitcoin.a` (`host` for `ctest`, `thumbv8m.main` for Nano S+, `thumbv6m` for Nano X) was linked directly into the BOLOS application and C unit-test targets across the following production paths:

- **`src/boilerplate/dispatcher.c`**: Verifies `llb_version_packed() == 0x00020401` and checks `llb_bolos_ins_supported(cmd->ins)` (`0x00..0x10`, rejecting unsupported/Vanadium-only instructions with `SW_INS_NOT_SUPPORTED = 0x6D00`).
- **`src/common/segwit_addr.c`**: Enforces `llb_segwit_version_valid`, `llb_segwit_prog_len_valid` (BIP-141 `2..40 B` + SegWit v0 `{20, 32} B`), and `llb_bech32_encoding_for_version` (BIP-173 Bech32 for `v0`, BIP-350 Bech32m for `v1..v16`).
- **`src/common/script.c`**: Enforces `llb_minimal_push_opcode_ok` inside `format_opscript_script` (`OP_RETURN` push minimality check).
- **`src/common/sighash.h`**: Enforces `llb_ecdsa_sighash_type_ok` (Legacy / SegWit v0) and `llb_taproot_sighash_byte_ok` (BIP-341 Taproot `SIGHASH_DEFAULT` + canonical sighash types).
- **`src/handler/get_extended_pubkey.c`**: Enforces `llb_bip32_depth_bolos_ok` (`depth <= MAX_BIP32_PATH_STEPS = 10`), `llb_bolos_os_testnet_lock_ok` (`PATH_APP_LOAD_PARAMS` testnet OS lock), and `llb_standard_bip44_path_ok` (`44'/45'/49'/84'/86'/87'` standard account paths).
- **`src/handler/lib/get_merkle_leaf_hash.c` & `src/common/wallet.c`**: Enforces `llb_valid_wallet_name_len_bolos` (`1..64`) and `llb_valid_wallet_name_char_bolos` (printable ASCII `0x20..0x7E`, no leading/trailing spaces).
- **`src/handler/sign_psbt/preprocess_inputs.c` & `preprocess_outputs.c`**: Enforces `llb_valid_satoshi_amount(amount)` (`<= MAX_MONEY_U64`) on UTXO and output values.

#### Integration Boundary Catches Verified During C Wiring
1. **Taproot vs Legacy Sighash Validation (`src/common/sighash.h`)**: `is_sighash_type_valid` in `app-bitcoin` validates Legacy/SegWit-v0 sighash types (`0x00` rejected), whereas Taproot (`segwit_version > 0`) permits `SIGHASH_DEFAULT (0x00)` — cleanly separated via `llb_ecdsa_sighash_type_ok` vs `llb_taproot_sighash_byte_ok`.
2. **BIP-48 4-Step Multisig Derivation (`src/handler/get_extended_pubkey.c`)**: `llb_standard_bip44_path_ok` covers 3-step account paths (`m/{44',45',49',84',86',87'}/coin'/acc'`); 4-step BIP-48 (`m/48'/coin'/acc'/{1',2'}`) remains on its dedicated 4-step branch so `get_extended_pubkey` BIP-48 vectors pass without false warnings.
3. **ISO-7816 Status Word Mapping (`llb_spec_error_to_sw`)**: `SpecError.wrongLength` (`tag 0`) maps to `SWO_WRONG_LENGTH = 0x6700`, whereas `SpecError.wrongDataLength` (`tag 1`) maps to `SW_WRONG_DATA_LENGTH = 0x6A87`.

### 3.2 Official C Unit Test Suite (`ctest`)

Command executed in `app-bitcoin/unit-tests`:
```bash
BOLOS_SDK=/var/lib/orb-node/work/caches/ledger-hub/dev-tools-rootfs/opt/nanosplus-secure-sdk \
  cmake -B build -H. -DFETCHCONTENT_SOURCE_DIR_SPECULOS=/var/lib/orb-node/work/caches/ledger-hub/speculos
make -C build -j4
ctest --test-dir build --output-on-failure
```

- **Result**: **`100% tests passed, 0 tests failed out of 31`** (`Total Test time (real) = 0.51 sec`).
- **Suites passed (`31/31`)**:
  - Upstream suites (`30/30`): `test_bitvector`, `test_buffer`, `test_display_utils`, `test_parser`, `test_psbt_parse`, `test_get_preimage`, `test_get_merkle_preimage`, `test_extract_bip32_derivation`, `test_check_merkle_tree_sorted`, `test_get_merkle_leaf_element`, `test_get_merkle_leaf_hash`, `test_get_merkle_leaf_index`, `test_stream_preimage`, `test_stream_merkle_leaf_element`, `test_stream_merkleized_map_value`, `test_get_merkleized_map`, `test_get_merkleized_map_value`, `test_psbt_fields`, `test_crypto`, `test_script`, `test_bip322`, `test_musig`, `test_sighash`, `test_locktime`, `test_wallet`, `test_cleartext`, `test_get_wallet_address`, `test_get_extended_pubkey`, `test_register_wallet`, `test_sign_message`.
  - Linked Lean kernel + Speculos `cx_*` shim suite (`1/1`, `4/4` cmocka groups): `test_lean_bolos_kernels` (`test_llb_abi_and_kernels`, `test_llb_bolos_shim_sha256_and_rng`, `test_llb_bolos_shim_bip32_and_ecfp`, `test_llb_fail_closed`).

### 3.3 Linked BOLOS Firmware ELFs & Official Speculos `pytest` Suites

Three BOLOS firmware ELFs were built with the freestanding Lean archive linked in flash (`22` `llb_*` symbols verified in `.text` via `llvm-nm` at `0xc0de021c..0xc0de0870`):
- **Nano X Testnet** (`COIN=bitcoin_testnet`, `thumbv6m`): `249,016 bytes` (`22` `llb_*` symbols linked)
- **Nano S+ Testnet** (`COIN=bitcoin_testnet`, `thumbv8m.main`): `248,184 bytes` (`22` `llb_*` symbols linked)
- **Nano S+ Mainnet** (`COIN=bitcoin`, `thumbv8m.main`): `248,180 bytes` (`22` `llb_*` symbols linked)

Official Speculos `pytest` results against the linked Nano S+ firmware ELFs:

| Test Suite | Firmware Binary | Passed | Skipped | Failed | Wall Time | Notes |
|---|---|---:|---:|---:|---:|---|
| `tests/` (v2 + legacy `*_v1.py` + `bitcoind` 32.1 E2E `test_e2e_*.py`) | `app-nanosp-testnet.elf` | **277** | **5** | **0** | `1406.33s` (`23m 26s`) | Includes legacy protocol v1 (`test_get_wallet_address_v1.py`, `test_register_wallet_v1.py`, `test_sign_psbt_v1.py`) and full `bitcoind` regtest E2E broadcasts (`test_e2e_miniscript.py`, `test_e2e_multisig.py`, `test_e2e_musig2.py`, `test_e2e_tapscripts.py`) |
| `tests_mainnet/` (`test_bip86.py`, `test_dashboard.py`) | `app-nanosp-mainnet.elf` | **2** | **0** | **0** | `2.45s` | Mainnet BIP-86 xpub/address + dashboard UI |
| **Total Speculos Integration** | | **279** | **5** | **0** | `1408.78s` | **100% pass rate on all active tests** |

> **Note on Legacy & Skipped Tests**:
> - In `LedgerHQ/app-bitcoin` `v2.6.0` (`f010982d3050e02813cd7129bebd68cf2d1f2099`), there is no top-level `tests_legacy/` directory; legacy v1 protocol tests live in `tests/test_*_v1.py` (all passed above), while `bitcoin_client/tests/` targets a frozen prebuilt Nano S1 legacy v1.6.5 binary (`nanos#bitcoin#1.6.5#54994025.elf`) designed for Speculos `0.25.5`.
> - All 5 skipped tests in `tests/` carry upstream `@pytest.mark.skip` annotations (`test_e2e_multisig_15keys`, `test_e2e_musig2_5of5`, `test_get_extended_pubkey_non_standard_reject_early`, `test_sign_psbt_singlesig_wpkh_512to256`, `test_sign_psbt_musig2_evicts_oldest_session`).

---

## 4. Pure-Lean Differential Conformance Suite (`Tests/BolosDifferential.lean`)

Executed via:
```bash
timeout 180s lake env lean Tests/BolosDifferential.lean
```
Output:
```text
BOLOS_DIFFERENTIAL_PASS: all 9 module conformance suites (10 BitcoinLedger.* modules) passed; audited 1425 declarations with 0 sorryAx.
```

### Module & Vector Coverage Breakdown

| Section | `BitcoinLedger.*` Module(s) | Official Upstream Vector Sources & Coverage | Vector / Assertion Groups |
|---|---|---|---|
| **0** | Pure-Lean Reference Crypto (`RefCrypto`) | FIPS 180-4 SHA-256, FIPS 180-4 SHA-512, RIPEMD-160 (`HASH160`), HMAC-SHA256/512, SLIP-0021 Wallet Policy HMAC, Pure-Lean `secp256k1` (`Fp`/`Fn`, BIP-32 CKDpub/CKDpriv, RFC 6979 ECDSA + low-S DER, BIP-340 Schnorr + tagged hashes) | Self-contained TCB oracle (zero FFI axioms) |
| **1** | `Basic`, `FreestandingKernels` | Satoshi bounds (`0..MAX_MONEY`), `checkedAddSats?`/`checkedSubSats?`, CompactSize varints (`1/3/5/9 B` + non-minimal rejections), `llbVersionPacked == 0x00020401`, and cross-equivalence of all 21 `llb_*` kernels against high-level `BitcoinLedger.*` functions | `1` suite (`45+` boundary & cross-check assertions) |
| **2** | `Bip32` | **All 31 vectors** from `tests/vectors/get_extended_pubkey.toml` (BIP-44/45/48/49/84/86 standard xpubs with full Base58Check derivation from the Speculos mnemonic, plus unusual/OS-locked/rejected paths) + BOLOS `depth <= 10` vs Recovery vs Vanadium `Resident (<= 255)` / `Master (<= 16)` | `31` official TOML vectors + cross-target depth checks |
| **3** | `Script` | Base58Check P2PKH/P2SH (leading-zero preservation, testnet/mainnet prefixes), BIP-173 Bech32 (`v0` P2WPKH/P2WSH) & BIP-350 Bech32m (`v1` P2TR + `v2..v16` `UnknownWitness` BOLOS `none` vs Vanadium Bech32m), `classifyOutputScript`, `isMinimalPushOpcode` (`OP_0`, `OP_1NEGATE`, `OP_1..OP_16`, `OP_PUSHDATA1/2/4`) | `30+` address, witness & push-minimality vectors |
| **4** | `WalletPolicy` | **17 vectors** from `tests/vectors/get_wallet_address.toml` (singlesig BIP-44/49/84/86, sortedmulti `sh`/`wsh`/`sh(wsh)`, BIP-386 `tr(@0)` & `tr(@0,{pk(@1),...})` Taproot key/script trees, BIP-388 Miniscript including `andor`) + **5 registration + negative vectors** from `tests/vectors/register_wallet.toml` (SLIP-0021 Proof-of-Registration HMACs, duplicate pubkeys, non-malleability, mixed timelocks, BOLOS vs Vanadium `andor` & `sh(wsh)` divergence) | `22` official TOML vectors + `12` negative/cross-target policy vectors |
| **5** | `Psbt` | **All 27 sighash vectors** from `unit-tests/test_sighash.c`, **all 12 BIP-370 locktime vectors** from `unit-tests/test_locktime.c`, **4 cryptographic sighash + ECDSA/Schnorr vectors** from `tests/vectors/sign_psbt.toml` & Bitcoin Core BIP-143/BIP-341, **BIP-322 virtual PSBT message signing** (`unit-tests/test_bip322.c`), CVE-2020-14199 dual-UTXO cross-check, `SIGHASH_DEFAULT`/`SIGHASH_ALL` batch homogeneity, `OP_RETURN` validation, and Swap mode invariants | `43` official C/TOML vectors + security invariant checks |
| **6** | `MerkleProtocol` | RFC 6962 `0x00` leaf / `0x01` internal node domain separation (`unit-tests/test_get_merkle_leaf_hash.c`), `verifyMerkleInclusionProof` + index reconstruction, strict lexicographic key sorting (`test_check_merkle_tree_sorted.c`), `MerkleizedMapCommitment` integrity, and `HostCallbackState` framing (`0xE0/0xE1` + `0x00..0x04`) | `18` Merkle tree, map & callback protocol checks |
| **7** | `Musig2` | **All 25 official BIP-327 vectors** from `unit-tests/test_musig.c` (`key_sort` `1`, `key_agg` `4` valid + `4` invalid, `tweak` `4` plain/x-only chains, `nonce_gen` `2`, `nonce_agg` `2` valid + `4` invalid, `sign_verify` `4` synthetic/deterministic/tweaked) + full end-to-end 2-of-2 `stepMusig2Psbt` Round-1 -> Round-2 single-use session consumption, replay rejection, self-pubnonce mismatch rejection, and BOLOS (`28 B` NVRAM, untweaked `aggpk`) vs Vanadium (`32 B` RAM, tweaked `aggpk`) divergence | `25` official BIP-327 C vectors + `6` stateful session checks |
| **8** | `SilentPayments` | BIP-352 shared secret ECDH (`input_hash · a · B_scan`), indexed output pubkey `P_k = B_spend + SHA256_BIP0352/SharedSecret(ecdh || ser32(k))·G`, `k`-ordering invariance, NUMS `H` taproot internal key rejection, BIP-374 DLEQ proof generation & verification (tampered proof/point rejection), BIP-392 `sp(...)` descriptors, and BOLOS `notSupported` (`0x6A82`) vs Vanadium support | `12` BIP-352 / BIP-374 / BIP-375 / BIP-392 checks |
| **9** | `AppStateMachine` | **All 7 vectors** from `tests/vectors/sign_message.toml` (`formatBitcoinSignedMessage` double-SHA256 + RFC 6979 compact 65-byte ECDSA signatures), APDU `CLA`/`INS` dispatch & chunked framing (`0xE1`/`0xF8`), status-word bijection (`0x9000`, `0x6985`, `0x6A80`, `0x6A82`, `0x6A86`, `0x6A87`, `0x6D00`, `0x6E00`, `0x6700`, `0xB000`, `0xB007`, `0xB008`), Swap mode latching (`resetForNextCommand` preservation & post-Swap command lockout), and `stepVerifiedPsbtSign` genuine-approval vs rejection gating | `7` official TOML vectors + `20+` state-machine transitions |
| **10** | Master `#guard`, Kernel `rfl` Proofs & `collectAxioms` Audit | Compile-time `#guard allBolosDifferentialChecksPass`, `5` kernel `rfl` theorems, and `#eval` environment walk auditing all `1,425` declarations in `BitcoinLedger.*`, `Spec.*`, and `Tests/BolosDifferential.lean` (`0` occurrences of `sorryAx`; allowed standard axioms `{propext, Classical.choice, Quot.sound}` only) | `1,425` declarations audited (`0 sorryAx`) |

---

## 5. Counterexample & Discrepancy Triage

Every discrepancy observed between `Spec/` / `BitcoinLedger/` and `LedgerHQ/app-bitcoin` (`f010982d3050e02813cd7129bebd68cf2d1f2099`) was triaged into `CandidateBug | SpecTooStrong | ReferenceDiscrepancy`:

### 5.1 [`ReferenceDiscrepancy`] Aggregate Multi-UTXO / Multi-Output Satoshi Sum `> MAX_MONEY`
- **Classification**: `ReferenceDiscrepancy` (defensive hardening in `Spec/` & `BitcoinLedger/`)
- **BOLOS Location**: `src/handler/sign_psbt/preprocess_inputs.c:251,291` and `src/handler/sign_psbt/preprocess_outputs.c:141,149`
- **Observation**: `app-bitcoin` checks `amount > BITCOIN_TOTAL_SUPPLY` (`2,100,000,000,000,000` sats) on each individual input UTXO and each individual output, then accumulates `total_amount += amount` in `uint64_t` without re-checking `total_amount <= BITCOIN_TOTAL_SUPPLY`. Because `2^64 / 2.1e15 > 8,784`, `uint64_t` cannot overflow in realistic BOLOS PSBTs (unlike Vanadium's unchecked `u64` / `i64` cast bug), so this is not an exploitable integer wraparound on BOLOS; however, `app-bitcoin` accepts synthetic regtest/malformed PSBTs where two valid UTXOs sum above 21M BTC (e.g., `1.5e15 + 1.0e15 = 2.5e15 > MAX_MONEY`).
- **Resolution**: `Spec/Psbt.lean` and `BitcoinLedger/Psbt.lean` (`validatePsbtTransaction` via `checkedAddSats?`) enforce `sum <= MAX_MONEY` (`amountExceedsMaxSupply`) on both per-element values and aggregate sums; verified in `Tests/BolosDifferential.lean` (`Section 5d`).

### 5.2 [`ReferenceDiscrepancy`] 1-Byte Push of `0x00` (`0x01 0x00`) Inside `OP_RETURN`
- **Classification**: `ReferenceDiscrepancy`
- **BOLOS Location**: `src/common/script.c:191-196` (`format_opscript_script`) and `unit-tests/test_script.c`
- **Observation**: When formatting `OP_RETURN` scripts for display, `app-bitcoin`'s `format_opscript_script` rejects non-minimal 1-byte pushes of `0x81` (`OP_1NEGATE`) and `0x01..0x10` (`OP_1..OP_16`), as well as non-minimal `OP_PUSHDATA1/2/4` lengths, but permits `0x01 0x00` (1-byte push of `0x00`), whereas strict BIP-62 `MINIMALDATA` requires `OP_0` (`0x00`) for the empty/zero push.
- **Resolution**: `BitcoinLedger.Psbt.checkValidOpReturn` (and `BitcoinLedger.Script.isMinimalPushOpcode`) enforces strict BIP-62 (`0x01 0x00` rejected as non-minimal), while `BitcoinLedger.FreestandingKernels.llbMinimalPushOpcodeOk` explicitly mirrors `format_opscript_script`'s exact condition so `app-bitcoin`'s `test_script` C unit tests and Speculos `OP_RETURN` vectors pass `100%`. Both behaviors are explicitly asserted in `Tests/BolosDifferential.lean` (`Section 1` & `Section 3`).

### 5.3 [Verified Subtle Behavior — No Spec Change Needed] Testnet `PATH_APP_LOAD_PARAMS` Wildcard `*/1'` on `m/44/1'/0'`
- **BOLOS Location**: `Makefile:95-103` (`PATH_APP_LOAD_PARAMS` for `bitcoin_testnet`) and `tests/vectors/get_extended_pubkey.toml` (`nonstd_purpose_not_hardened`)
- **Observation**: Testnet `app-bitcoin` configures `PATH_APP_LOAD_PARAMS` with `"44'/1'"`, `"45'/1'"`, `"48'/1'"`, `"49'/1'"`, `"84'/1'"`, `"86'/1'"`, `"*/1'"`, `"45'"`, `"4541509'"`, `"2054'/1777777'"`. Because of `"*/1'"`, a path with an unhardened purpose `s0 = 44` and hardened testnet coin type `s1 = 1'` (`m/44/1'/0'`) passes the BOLOS OS path lock (`isBolosOsPermittedPath .testnet == true`) and is classified as `.warnUnusual` (succeeding when `display = true` and failing with `0x6985` when `display = false`), whereas `m/44'/1/0'` (`s1 = 1` unhardened) is blocked by the OS lock (`.reject .notSupported`). `BitcoinLedger.Bip32.classifyExtendedPubkeyPath` matched all 31 `get_extended_pubkey.toml` cases on the first run (`0` `SpecTooStrong` issues).

### 5.4 Summary of Verified BOLOS vs Vanadium Target Profile Divergences
All architectural differences between `bolosAppProfile` (`LedgerHQ/app-bitcoin`) and `vanadiumAppProfile` (`LedgerHQ/vanadium`) modeled in `Spec/` were exercised and confirmed in `Tests/BolosDifferential.lean`:
1. **`GET_EXTENDED_PUBKEY` Depth & OS Lock**: BOLOS caps depth at `10` steps and enforces `PATH_APP_LOAD_PARAMS` on standard apps (unlocked on `Bitcoin Recovery`); Vanadium permits up to `16` (`Master`) or `255` (`Resident`) steps without OS path locks.
2. **Future SegWit Versions (`v2..v16`)**: BOLOS returns `none` for `UnknownWitness` address display (`get_address_from_output_script`), whereas Vanadium encodes `v2..v16` as BIP-350 Bech32m.
3. **Wallet Policy Profile**: BOLOS supports stateless default policies (`addrIdx <= 50,000`), `sh(wsh(...))` nested SegWit, canonical BIP-379 `andor(X,Y,Z)` (`[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`), full BIP-379 type/malleability/timelock checks, and strict wallet-name rules (`1..64` printable ASCII, no leading/trailing spaces); Vanadium requires explicit registration for all accounts and diverges on `andor` and `sh(wsh(...))` (documented in `docs/spec-cards/vanadium-upstream-bugs.md`).
4. **MuSig2 (BIP-327 / BIP-373)**: BOLOS stores up to `32` `28-byte` `psbt_session_id` entries in persistent NVRAM (`PSBT_IN_MUSIG2_PARTICIPANT_PUBKEYS` keyed by **untweaked** `aggpk`) and verifies self-pubnonce equality in Round 2; Vanadium holds `1` `32-byte` transaction-bound session in volatile RAM (keyed by **tweaked** `aggpk`).
5. **Silent Payments (BIP-352 / BIP-374 / BIP-375 / BIP-392) & `SIGN_MESSAGE`**: BOLOS supports `SIGN_MESSAGE (0x10)` and rejects `sp(...)` descriptors (`0x6A82` `notSupported`); Vanadium supports `sp(...)` / DLEQ Silent Payment outputs and rejects `SIGN_MESSAGE`.

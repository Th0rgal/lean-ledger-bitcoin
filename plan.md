# `lean-ledger-bitcoin` — Maxwell Campaign Plan & Architecture

## 1. Mission & Scope

Rebuild the Ledger Bitcoin hardware wallet application in **pure Lean 4** (`leanprover/lean4:v4.35.0`) with:
1. **Minimal, implementation-independent formal specifications (`Spec/`)** deduced from **both** official Ledger reference implementations:
   - `LedgerHQ/app-bitcoin` (`f010982d3050e02813cd7129bebd68cf2d1f2099`): BOLOS native Secure Element application (`thumbv6m-none-eabi` / Thumbv8m, 12–16 KB RAM/stack budget, `CLA=0xE1` / `0xF8` interactive merkleized APDU protocol, BIP-32/388 wallet policies, PSBTv2, BIP-322, cleartext, MuSig2, Ledger Swap).
   - `LedgerHQ/vanadium` `apps/bitcoin` (`ace8e96982408959dea9e7fbc59ee36e8c54e645`): Vanadium RISC-V V-App (`riscv32imac-unknown-none-elf`, ECALL syscall boundary, FastPSBT/PSBTv2, BIP-388 Miniscript accounts, Taproot, MuSig2 BIP-327, BIP-352/374/375 Silent Payments & DLEQ, Resident/Identity keys).
2. **Pure Lean 4 executable implementation (`BitcoinLedger/`)** refined against `Spec/` via machine-checked theorems in `Proofs/` (`0 sorryAx`, standard Lean axioms `{propext, Quot.sound}` only, zero `native_decide` in `Spec/` and `Proofs/`).
3. **End-to-end verified freestanding 32-bit compilation (`Th0rgal/turbo-lean` branch `feat/ledger-32bit-llvm`)**:
   - Extend `LeanNative` (`TargetArch`, `ArchWidth`, `CAbiEmit`, `LLVMAst`, `LLVMLower`, `LLVM.lean`, `lowerToLLVM_sound`, `LLVMEmitVerify` / `RoundtripProofs`) to 32-bit `ILP32` freestanding targets:
     - `thumbv6m` / `thumbv8mMain` (`thumbv6m-none-eabi` / `thumbv8m.main-none-eabi`, `p:32:32`, AAPCS 8-byte `i64` alignment, static/arena `RcMode.freestanding`, zero `malloc`, zero `libleanrt.a`, bounded stack frame budget for Nano X 12 KB / Nano S+ 16 KB).
     - `riscv32imac` (`riscv32imac-unknown-none-elf`, `e-m:e-p:32:32-i64:64-n32-S128`, ILP32 ABI for Vanadium V-App ELF).
   - Link emitted `.ll` via `clang`/`lld` against thin C/Rust hardware shims (`ffi/bolos/`, `ffi/vanadium/`) that wrap **only** TCB syscalls (`os_derive_bip32_*`, hardware crypto primitives, RNG, APDU `io_*` / Vanadium ECALLs, and `nbgl_*`/`ux_*` UI).
4. **100% Official Test Suite Parity + Controlled Spec Evolution**:
   - Pass **100%** of `LedgerHQ/app-bitcoin` `unit-tests` (32 C suites), `tests/` (Ragger/pytest on Speculos), `tests_mainnet`, and `LedgerHQ/vanadium` `apps/bitcoin` unit + client integration + BIP-352/374/375 vector tests.
   - Discover edge cases and potential bugs across both C and Rust reference apps via differential fuzzing and lean-quickcheck / counterexample triage (`CandidateBug | SpecTooStrong | ReferenceDiscrepancy`); evolve `Spec/` minimally with documented Human Spec Cards (`docs/spec-cards/`) to cover any discovered bug classes.

## 2. Formal Specification Rules (`formal-specs` & Hindsight)

- **Plain Lean 4 only**: `def`, `structure`, `inductive`, `theorem` over standard domain types (`ByteArray`, `Array`, `List`, `BitVec`, `UInt8`, `UInt32`, `UInt64`, `Nat`, `Option`, `Except`).
- **Zero wrapper frameworks**: Never import `Th0rgal/lean-specs` or introduce `SpecM`, `ObsQuotient`, `SpecBlock`, `SubSpec`, or tautological `Impl := Spec` mirrors.
- **Implementation-independent contracts**:
  - Specify **observable input/output relations, invariants, cryptographic commitments, and security rejections** (e.g., canonical BIP-32 paths, change-vs-external script matching, amount sum overflow checks, sighash commitment completeness, merkleized map sorting & proof soundness, MuSig2 session nonce linearity / replay prevention, Swap pre-approved parameter lock).
  - Never mirror C/Rust buffer layouts, cursor offsets, or internal state flags inside `Spec/`, except at the explicit Wire/Transport boundary (`Spec/Transport/BolosApdu.lean` and `Spec/Transport/VanadiumWire.lean`) which bridges wire bytes to canonical domain commands.
  - **Atomic error rollback**: Every mutating command transition returning `.error e` must preserve persistent session/keystore state unchanged (explicitly specifying MuSig2 nonce consumption/invalidation rules on abort).
  - **Read-only purity**: Queries (`getVersion`, `getMasterFingerprint`, `getExtendedPubkey`, `getWalletAddress`) satisfy `s' = s`.

## 3. Repository Layout & Disjoint Ownership Boundaries

- `Spec/` (Frozen during implementation waves; changes require Spec Cards in `docs/spec-cards/`):
  - `Spec/Basic.lean`: Core Bitcoin primitives (amounts/satoshis, hashes, networks, varint/compact-size relation, endianness, error taxonomy).
  - `Spec/Bip32.lean`: BIP-32 paths, hardened/unhardened derivation domain, xpub serialization, master fingerprint, Ledger path policy invariants.
  - `Spec/Script.lean`: Output scripts (P2PKH, P2SH, P2WPKH, P2WSH, P2TR, OP_RETURN), Base58Check, Bech32/Bech32m (BIP-173/350).
  - `Spec/WalletPolicy.lean`: BIP-388 Wallet Policies & Miniscript AST, key placeholders, descriptor templates, Taproot tree descriptors, canonical address derivation.
  - `Spec/Psbt.lean`: Unified PSBTv0/PSBTv2 logical model, input/output completeness invariants, non-witness vs witness UTXO rules, BIP-143 / BIP-341 / legacy sighash digests, fee & overflow safety, BIP-322 message-signing virtual tx, cleartext & Swap invariants.
  - `Spec/Musig2.lean`: BIP-327 MuSig2 key aggregation, session lifecycle, nonce anti-reuse linearity, partial signature generation.
  - `Spec/SilentPayments.lean`: BIP-352 Silent Payments, BIP-374 DLEQ proofs, BIP-375 PSBT silent payment fields, scan/spend keys.
  - `Spec/MerkleProtocol.lean`: BOLOS interactive merkleized map/tree & client-command commitment model (`GET_PREIMAGE`, `GET_MERKLE_LEAF_*`, `YIELD`) proving host-untrusted soundness against `Spec/Psbt.lean` & `Spec/WalletPolicy.lean`.
  - `Spec/AppStateMachine.lean`: Top-level observable Ledger Bitcoin state machine unifying BOLOS (`CLA=0xE1`/`0xF8` + Swap) and Vanadium V-App commands, UI user-approval oracle, and hardware crypto oracle.
- `BitcoinLedger/`: Zero-allocation / arena-backed freestanding-compatible Lean 4 implementation lowering cleanly through `turbo-lean` (`LeanNative`).
- `Proofs/`: Refinement and soundness theorems (`BitcoinLedger` refines `Spec`, `0 sorryAx`).
- `Tests/`: Property/differential/mutation checks + host harnesses against `app-bitcoin` and `vanadium` vectors.
- `ffi/bolos/`: Thin BOLOS C SDK shim (`os_*`, `cx_*`, `io_*`, `nbgl_*`) + `Makefile` producing Speculos ARM ELF.
- `ffi/vanadium/`: Thin Vanadium Rust/C ECALL shim + linker script producing `riscv32imac-unknown-none-elf` V-App ELF.

## 4. Wave Plan

1. **Wave 1 (Parallel Bootstrapping)**:
   - **Track C1 (`turbo-lean` `feat/ledger-32bit-llvm`)**: Add `thumbv6m`, `thumbv8mMain`, and `riscv32imac` to `TargetArch` + `ArchWidth.bits32` + `LLVMAst`/`LLVMLower`/`LLVM.lean` + soundness & roundtrip proofs + freestanding no-`libleanrt` C-ABI emission & stack-usage gate.
   - **Track H1 (Ledger Harness Golden Builder VM)**: Provision warm Boat VM with Lean 4.35, `turbo-lean`, `arm-none-eabi` / `clang` Thumb + `riscv32imac` toolchains, Speculos + Ragger pytest suite for `LedgerHQ/app-bitcoin`, and Cargo test harness for `LedgerHQ/vanadium/apps/bitcoin`; baseline both official test suites green and snapshot.
   - **Track S1–S4 (Unified Specification Deduction from Both Apps)**:
     - `S1`: `Spec/Basic.lean`, `Spec/Bip32.lean`, `Spec/Script.lean` (deduced from `app-bitcoin/src/{crypto,common/script,common/segwit_addr,handler/get_*}` + `vanadium/apps/bitcoin/{app/src/bip32,common/src/script}`).
     - `S2`: `Spec/WalletPolicy.lean` (BIP-388 & Miniscript & Taproot policy trees from `app-bitcoin/src/common/wallet.c` + `handler/lib/policy.c` + `vanadium/apps/bitcoin/common/src/{account,taproot,message/bip388_codec}`).
     - `S3`: `Spec/Psbt.lean`, `Spec/MerkleProtocol.lean` (PSBTv0/v2, sighashes, BIP-322, cleartext, Swap, and BOLOS merkleized streaming soundness from `app-bitcoin/src/handler/sign_psbt/*`, `handler/lib/*`, `swap/*` + `vanadium/apps/bitcoin/common/src/{fastpsbt,psbt/*}`).
     - `S4`: `Spec/Musig2.lean`, `Spec/SilentPayments.lean`, `Spec/AppStateMachine.lean` (BIP-327 MuSig2, BIP-352/374/375 Silent Payments, Identity/PoR, and unified command/UI/crypto oracle state machine).
2. **Wave 1.5 (Adversarial Spec Audit & Freeze)**:
   - Dual-family quorum review (Gemini Carbon 4 + Ethereum Foundation `glm-5.3`) + mutation/vacuity audit (`turbo-lean audit-spec`, `#print axioms`). Freeze `Spec/` + write `docs/spec-cards/000-initial-unified-spec.md`.
3. **Wave 2 (Pure Lean 4 Implementation + Freestanding Kernels)**:
   - Disjoint shards implementing `BitcoinLedger/*` and `Proofs/*` against frozen `Spec/`, compiled via `turbo-lean` 32-bit freestanding LLVM backend.
4. **Wave 3 (BOLOS & Vanadium Shim Integration + Official Test Suites)**:
   - Link `BitcoinLedger` 32-bit LLVM archive into BOLOS (`app-bitcoin` replacement ELF) and Vanadium (`vnd-bitcoin` V-App ELF).
   - Run 100% of `unit-tests`, Speculos Ragger `tests/`, `tests_mainnet`, and Vanadium `apps/bitcoin` tests.
5. **Wave 4 (Differential Fuzzing, Bug Discovery, Controlled Spec Evolution & Bytecode Optimization)**:
   - Differential fuzzing (Lean vs C `app-bitcoin` vs Rust `vanadium/apps/bitcoin`); triage discrepancies, document discovered bugs / Spec Cards, optimize ARM Thumb & RV32IMAC code size / stack / cycle counts under verified preservation.

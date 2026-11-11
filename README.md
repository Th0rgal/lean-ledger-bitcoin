# `lean-ledger-bitcoin`

Formally verified Ledger Bitcoin hardware wallet application in **pure Lean 4** (`leanprover/lean4:v4.35.0`), targeting both:
- **Ledger BOLOS** (`LedgerHQ/app-bitcoin` `f010982` parity — 32-bit ARM `thumbv6m-none-eabi` Nano X & `thumbv8m.main-none-eabi` Nano S+ on Speculos)
- **Ledger Vanadium** (`LedgerHQ/vanadium` `ace8e969` `apps/bitcoin` V-App parity — 32-bit RISC-V `riscv32imac-unknown-none-elf` on Speculos Ledger Flex)

Compiled to freestanding 32-bit native code without `libleanrt.a` or dynamic heap allocation via [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean).

## Architecture & Formal Verification (`0 sorryAx`, `0 Classical.choice`)

1. **Minimal User-Facing Specification (`Spec/`, `801` LOC across 4 files)**:
   - [`Spec.lean`](Spec.lean) (`147` LOC): Top-level end-to-end PSBT execution contract (`Spec.validEndToEndPsbtExecution`, `Spec.master_psbt_execution_security`) and non-vacuity witnesses.
   - [`Spec/KeyPolicy.lean`](Spec/KeyPolicy.lean) (`250` LOC): BIP-32 path isolation, extended-pubkey silent-export policy, and BIP-388 wallet policy authorization.
   - [`Spec/TransactionSafety.lean`](Spec/TransactionSafety.lean) (`232` LOC): `MAX_SATOSHIS` (`21,000,000 BTC`) conservation, dual-UTXO CVE-2020-14199 anti-spoofing, BIP-370 locktime consistency, and Ledger Swap lockdown.
   - [`Spec/SessionSecurity.lean`](Spec/SessionSecurity.lean) (`172` LOC): Multi-step APDU/V-App session atomicity, universal user-consent gate, BIP-327 MuSig2 nonce anti-replay, and BIP-375 Silent Payment output verification.
   - Design rationale: [`docs/spec-cards/001-minimal-user-facing-spec.md`](docs/spec-cards/001-minimal-user-facing-spec.md).
2. **Protocol Mechanization (`InternalSpec/`, `20,435` LOC across 10 modules)**:
   - Complete wire-format and consensus mechanization of BIP-32/39, BIP-143/340/341/342, BIP-174/370 PSBTv0/v2, BIP-379/388 Wallet Policies & Miniscript, BIP-327 MuSig2, BIP-352/374/375/392 Silent Payments, Merkleized host-memory protocol, and Ledger BOLOS/Vanadium state machines.
3. **Executable Implementation & Freestanding Kernels (`BitcoinLedger/`, `Proofs/`)**:
   - Constructive refinement proofs in [`Proofs/UserSpecRefinement.lean`](Proofs/UserSpecRefinement.lean) (`973` LOC) and [`Proofs/FreestandingKernels.lean`](Proofs/FreestandingKernels.lean) (`1,466` LOC) audited by [`Tests/AxiomAudit.lean`](Tests/AxiomAudit.lean) (`253` `Spec.*`, `6,564` `InternalSpec.*`, `937` `Proofs.*` declarations depending exclusively on `{propext, Quot.sound}`).

## Benchmarks vs Unmodified Upstream Ledger Apps

- **BOLOS (`LedgerHQ/app-bitcoin` `f010982`)**: [`docs/benchmarks/bolos-vs-reference.md`](docs/benchmarks/bolos-vs-reference.md) (`benchmarks/bolos_benchmark.sh`, `ffi/bolos/patches/app-bitcoin-lean-opt.patch`) — strictly smaller flash (`-1,536 B` Nano S+, `-1,280 B` Nano X; `-1,024 B` / `-512 B` even under identical upstream `DEFINES`), lower `.bss` static RAM (`-144 B`), zero recursion (`qsort` & `__aeabi_uldivmod` eliminated), `-635` / `-510` fewer ARM Thumb instructions, `1.641x` faster hotspot cycles (`6.566x` satoshi formatting), and faster Speculos APDU latencies.
- **Vanadium (`LedgerHQ/vanadium` `ace8e969`)**: [`docs/benchmarks/vanadium-vs-reference.md`](docs/benchmarks/vanadium-vs-reference.md) (`benchmarks/vanadium_benchmark.sh`, `ffi/vanadium/patches/vanadium-bitcoin-lean-opt.patch`) — strictly smaller RV32IMAC `LOAD R E` flash (`-61,658 B` / `-20.15%`, crossing below `1,024` Merkle pages from depth `11` to `10`), `-49.77%` `LOAD RW` RAM, `-50.00%` stack, `39.91x` faster host hot-path kernels, `-22.52%` / `-25.12%` faster Speculos Flex E2E latency, and all 9 formal security fixes (`VND-BUG-001..009`).
- **Live Speculos Simulator Screenshots**: [`docs/screenshots/`](docs/screenshots/) (`bolos-{dashboard,address,register-policy,sign-psbt}.png` on Nano S+ `128x64` + `vanadium-flex-{home,register,sign-tx}.png` on Ledger Flex `480x600`).

See [`plan.md`](plan.md) and [`WORKER.md`](WORKER.md) for architecture, specification rules, and verification gates.

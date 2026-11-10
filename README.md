# `lean-ledger-bitcoin`

Formally verified Ledger Bitcoin hardware wallet application in **pure Lean 4** (`leanprover/lean4:v4.35.0`), targeting both:
- **Ledger BOLOS** (`LedgerHQ/app-bitcoin` parity — 32-bit ARM `thumbv6m-none-eabi` / `thumbv8m.main-none-eabi` on Speculos)
- **Ledger Vanadium** (`LedgerHQ/vanadium` `apps/bitcoin` V-App parity — 32-bit RISC-V `riscv32imac-unknown-none-elf`)

Compiled to freestanding 32-bit native code without `libleanrt.a` or dynamic heap allocation via [`Th0rgal/turbo-lean`](https://github.com/Th0rgal/turbo-lean) (`feat/ledger-32bit-llvm`).

See [`plan.md`](plan.md) and [`WORKER.md`](WORKER.md) for architecture, specification rules, and verification gates.

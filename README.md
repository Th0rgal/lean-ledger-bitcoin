# lean-ledger-bitcoin

A small Lean 4 kernel that is compiled into Ledger's two Bitcoin apps and replaces some of
their security checks:

- the C app on BOLOS (`LedgerHQ/app-bitcoin@f010982d`, Nano S+ and Nano X, ARM Thumb);
- the Rust app on Vanadium (`LedgerHQ/vanadium@ace8e969`, Flex, RV32IMAC).

The apps stay C and Rust. Parsing, cryptography, display and transport are not Lean.

## What to read

| File | What it is |
| --- | --- |
| [`Spec.lean`](Spec.lean) | What the compiled kernel guarantees: 13 statements, each "accepts exactly when" or an equality, written with natural numbers. Statements only. |
| [`BitcoinLedger/FreestandingKernels.lean`](BitcoinLedger/FreestandingKernels.lean) | The kernel: the only Lean code that runs on the device. 31 exported functions, each called by at least one app, no imports. |
| [`Proofs/KernelSpec.lean`](Proofs/KernelSpec.lean) | The proof of every statement of `Spec.lean` (`kernel_meets_spec`), with one accepted and one rejected input for each. |
| [`scripts/check_kernel_spec.py`](scripts/check_kernel_spec.py) | Which exports have a statement, which do not and why. It fails if an export is called by neither app. |

`Spec.lean` currently covers 16 of the 31 exports. The other 15 are listed in
`scripts/check_kernel_spec.py` with the reason. The main gaps:

- **Most buffer functions have no statement yet.** The kernel has an explicit memory model: a
  buffer is a value, a write returns the updated buffer, and every function that writes
  returns the buffer it wrote. `turbo-lean` (branch `feat/freestanding-linear-buffers`)
  compiles that model to loads and stores and refuses a function that does not use its
  mutable buffer linearly; that check is trusted, not proved. The dual-UTXO check and the
  CompactSize reader have a statement. The statements about the Miniscript checker, both
  sorts, the amount formatter and the BIP-32 export path check are not written yet.
- **Statements still phrased against the app model.** The locktime state machine, the
  Merkle direction stepper and a few classifiers are proved equal to definitions in
  `InternalSpec/` (see `Proofs/FreestandingKernels.lean`) and have not been restated here.
- **Trusted, not proved:** `turbo-lean`'s extraction to LLVM IR, clang and lld, and the C
  and Rust call sites. They are checked by differential tests only.

## What is not part of the claim

`InternalSpec/`, the other `BitcoinLedger/*` modules and the other `Proofs/*` files are a
host-side Lean model of the two apps (state machine, PSBT validation, wallet policies) with
its own theorems. It is used as a test oracle (`Tests/BolosDifferential.lean`,
`Tests/VanadiumDifferential.lean`) and as the source of the reference definitions used in
`Proofs/FreestandingKernels.lean`. It does not run on the device, and its theorems say
nothing about the C and Rust code.

## Checks

```bash
python3 scripts/check_kernel_spec.py   # coverage gate
lake build Proofs                      # all proofs
lake build Tests.AxiomAudit            # only propext and Quot.sound are allowed
```

## Integration and measurements

- Patches: [`ffi/bolos/patches/`](ffi/bolos/patches/) and [`ffi/vanadium/patches/`](ffi/vanadium/patches/).
  The BOLOS patch embeds the generated LLVM IR; about 1,150 of its lines are hand-written.
- Kernel build: [`scripts/build-freestanding.sh`](scripts/build-freestanding.sh) (needs clang and `lean-native` from `turbo-lean`, branch `feat/freestanding-linear-buffers`).
- Measurements: the JSON files in [`benchmarks/`](benchmarks/). Files named `*.experimental.json` are marked `experimental_nonvalidated`.
- Upstream findings: [`docs/spec-cards/vanadium-upstream-bugs.md`](docs/spec-cards/vanadium-upstream-bugs.md).

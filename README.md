# lean-ledger-bitcoin

A small Lean 4 kernel that is compiled into Ledger's two Bitcoin apps and replaces some of
their security checks:

- the C app on BOLOS (`LedgerHQ/app-bitcoin@f010982d`, Nano S+ and Nano X, ARM Thumb);
- the Rust app on Vanadium (`LedgerHQ/vanadium@ace8e969`, Flex, RV32IMAC).

The apps stay C and Rust. Parsing, cryptography, display and transport are not Lean.

## What to read

| File | What it is |
| --- | --- |
| [`Spec.lean`](Spec.lean) | What the compiled kernel guarantees: 12 statements, each "accepts exactly when" or an equality, written with natural numbers. Statements only. |
| [`BitcoinLedger/FreestandingKernels.lean`](BitcoinLedger/FreestandingKernels.lean) | The kernel: the only Lean code that runs on the device. 45 exported functions, no imports. |
| [`Proofs/KernelSpec.lean`](Proofs/KernelSpec.lean) | The proof of every statement of `Spec.lean` (`kernel_meets_spec`), with one accepted and one rejected input for each. |
| [`scripts/check_kernel_spec.py`](scripts/check_kernel_spec.py) | Which exports have a statement, which do not and why, and which are called by neither app. |

`Spec.lean` currently covers 17 of the 45 exports. The other 28 are listed in
`scripts/check_kernel_spec.py` with the reason. The main gaps:

- **No memory model.** Functions that read or write a buffer (the Miniscript checker, both
  sorts, the amount formatter, the dual-UTXO check, the CompactSize reader) have no
  statement: in Lean their reads are placeholders and their writes are discarded, and
  `turbo-lean` substitutes real loads and stores when compiling.
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
- Kernel build: [`scripts/build-freestanding.sh`](scripts/build-freestanding.sh) (needs `turbo-lean`'s `lean-native` and clang).
- Measurements: the JSON files in [`benchmarks/`](benchmarks/). Files named `*.experimental.json` are marked `experimental_nonvalidated`.
- Upstream findings: [`docs/spec-cards/vanadium-upstream-bugs.md`](docs/spec-cards/vanadium-upstream-bugs.md).

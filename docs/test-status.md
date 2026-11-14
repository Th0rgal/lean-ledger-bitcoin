# Test status

Fresh run of the official upstream suites against `main`, with both patches applied to the pinned upstreams.

- Date: 2026-11-13T23:36Z to 2026-11-14T01:12Z
- Commit under test: `333406085fec9bc1dc4b04c8e4a4953427d0d1da` (fresh https clone)
- Upstreams: `LedgerHQ/app-bitcoin@f010982d3050e02813cd7129bebd68cf2d1f2099`, `LedgerHQ/vanadium@ace8e96982408959dea9e7fbc59ee36e8c54e645`
- Patches: `ffi/bolos/patches/app-bitcoin-lean-opt.patch` (sha256 `d88e07a1f8ec8600156e9aa00cc6c681e88c9296b16349dd2724807dae9a0541`), `ffi/vanadium/patches/vanadium-bitcoin-lean-opt.patch` (sha256 `ed4a98f79b0f2c7cbfd138844aba2a598f8db0eae87e6c066fd477670a797aeb`)
- VM: one Boat `large` (8 vCPU, 16 GiB, AMD Ryzen 9 9950X), image `orb-snap-health-manager-ledger-hub-warm-v1-eevr`, host `box-node-088efd491a3d7604`
- Tools: clang/LLD 21.1.8, cmake 3.31.3, rustc 1.99.1, turbo-lean `8c3503fa0df7`, Speculos 0.27.4, Ragger 1.48.0, pytest 6.2.5, Bitcoin Core 32.1, Ledger SDK API level 27

"ref" is the unmodified upstream app, "lean" is the same commit with the patch applied. Both are built in the same way on the same VM.

## Result

Everything passes except one upstream test, `test_sign_psbt_singlesig_wpkh_512to256`, which fails in exactly the same way on the unmodified upstream app. Upstream CI never runs that test. With the flags upstream CI uses, the patched app has 0 failures on both devices.

## Builds

| Step | Command | rc |
|---|---|---:|
| Kernel, 4 targets | `bash scripts/build-freestanding.sh` | 0 |
| Kernel C harness | `make -C ffi/bolos test` | 0 |
| Kernel Rust crate | `cargo test --manifest-path ffi/vanadium/Cargo.toml` (2 passed) | 0 |
| BOLOS ref, testnet | `make -j8 COIN=bitcoin_testnet DEBUG=0`, Nano S+ and Nano X | 0 |
| BOLOS lean, testnet | same | 0 |
| BOLOS lean, mainnet | `make -j8 COIN=bitcoin DEBUG=0`, Nano S+ and Nano X | 0 |
| BOLOS lean, perf | `make -j8 COIN=bitcoin_testnet DEBUG=0 AUTOAPPROVE_FOR_PERF_TESTS=1`, Nano S+ and Nano X | 0 |
| Vanadium V-App, plain | `cargo build --release --target riscv32imac-unknown-none-elf --no-default-features --features target_vanadium_ledger` | 0 |
| Vanadium V-App, autoapprove | same with `--features target_vanadium_ledger,autoapprove` | 0 |

`build-freestanding.sh` reports `symbols ok: exported=31, undefined=0, forbidden=0` on thumbv6m, thumbv8m.main, riscv32imac and x86_64, and leaves the checkout clean. The IR shipped inside the BOLOS patch differs from the IR this commit emits only by the `; ModuleID = '<build path>'` line, for both thumb targets.

The two perf ELFs have the same sha256 as the frozen `B-nanosp` / `B-nanox` of `benchmarks/bolos_paired_evidence`.

## BOLOS (`app-bitcoin`)

Ragger commands are run from `tests/`, with `bitcoind` 32.1 on `PATH`. The four `tests/` jobs ran side by side, each in its own network namespace (`unshare -Urn`), because Ragger uses fixed ports.

| Suite | Command | App | Device | Passed | Failed | Skipped | rc | Time |
|---|---|---|---|---:|---:|---:|---:|---:|
| Unit tests | `cmake -B build -H. && make -C build && ctest --test-dir build` in `unit-tests/` | ref | host | 30 | 0 | 0 | 0 | 0.45 s |
| Unit tests | same | lean | host | 31 | 0 | 0 | 0 | 0.42 s |
| `tests/`, all slow tests | `pytest --device <dev> --enable_slow_tests=2` | ref | nanosp | 280 | 1 | 1 | 1 | 2117 s |
| `tests/`, all slow tests | same | ref | nanox | 280 | 1 | 1 | 1 | 2117 s |
| `tests/`, all slow tests | same | lean | nanosp | 280 | 1 | 1 | 1 | 2113 s |
| `tests/`, all slow tests | same | lean | nanox | 280 | 1 | 1 | 1 | 2121 s |
| `tests/`, upstream CI flags | `pytest --device <dev> --enable_slow_tests` | lean | nanosp | 280 | 0 | 2 | 0 | 898 s |
| `tests/`, upstream CI flags | same | lean | nanox | 280 | 0 | 2 | 0 | 895 s |
| `tests_mainnet/` | `pytest --headless --model=<dev> --timeout=300` | lean (mainnet) | nanosp | 2 | 0 | 0 | 0 | 2.2 s |
| `tests_mainnet/` | same | lean (mainnet) | nanox | 2 | 0 | 0 | 0 | 2.2 s |

- 282 tests are collected in `tests/`. The per-test outcomes of the four `--enable_slow_tests=2` runs are identical (compared from the JUnit files).
- The lean unit-test count is 31 because the patch adds `test_lean_bolos_kernels`.
- Skipped everywhere: `test_get_extended_pubkey_non_standard_reject_early` (upstream skips it on Nano devices). At the CI flag level, `test_sign_psbt_singlesig_wpkh_512to256` is skipped too (upstream skips it unless `--enable_slow_tests` is at least 2).
- `tests/` with upstream CI flags was not run on ref.

### `test_sign_psbt_singlesig_wpkh_512to256`

| Command | App | Device | Result | Time |
|---|---|---|---|---:|
| `pytest --device nanosp --enable_slow_tests=2 -k test_sign_psbt_singlesig_wpkh_512to256` | ref | nanosp | 1 failed | 790 s |
| same | ref | nanox | 1 failed | 1090 s |
| same | lean | nanosp | 1 failed | 1098 s |
| same | lean | nanox | 1 failed | 1107 s |

The first row ran alone, the other three side by side.

- First failure, identical in all four: `requests.exceptions.ConnectionError: ('Connection aborted.', RemoteDisconnected('Remote end closed connection without response'))`, raised from `client.sign_psbt` at `tests/test_sign_psbt.py:714`.
- Just before it, Speculos prints `[*] exit called (255)`: the app exits during signing. This happens after the same number of APDUs (43047 sent) on ref and lean, on both devices.
- It is not a test timeout: no `--timeout` is passed, and the failure point does not move when the wall time changes from 790 s to 1107 s.
- The patch changes no file under `tests/`, so both sides run the same test.
- Upstream CI builds with `DEBUG=0` and passes at most `--enable_slow_tests` (level 1), so it never runs this test.

Because the unmodified upstream app fails the same way, this is not caused by the patch or the kernel, and nothing was changed. The reason the upstream app exits was not investigated.

## Vanadium (`apps/bitcoin`)

| Suite | Command | Passed | Failed | Ignored | rc |
|---|---|---:|---:|---:|---:|
| `common` | `cargo test` in `apps/bitcoin/common` | 85 | 0 | 0 | 0 |
| `app` | `cargo test` in `apps/bitcoin/app` | 90 | 0 | 0 | 0 |
| `client`, unit and Speculos integration | `VANADIUM_BINARY=<vm> VAPP_BINARY=<v-app> cargo test --features speculos-tests,debug` in `apps/bitcoin/client` | 9 | 0 | 0 | 0 |

- `common`: 81 unit tests, plus the BIP-352 (1), BIP-374 (2) and BIP-375 (1) vector tests.
- `client`: 5 unit tests and the 4 Speculos tests (`test_get_fingerprint`, `test_e2e_sign_transaction`, `test_e2e_send_to_silent_payment_address`, `test_e2e_silent_payment_account`). These are the features upstream CI uses.
- V-App under test: the autoapprove build above, sha256 `f92d7635181dc576dcdea4d5bbbbdc6b20f52c12914c39e78af3f0e81499eb9b`.
- Vanadium VM: upstream `vanadium@ace8e969` built for Flex with `cargo ledger build flex -- --features blind_registration`, sha256 `2751d0fa37f709d063d1aff18b7c1b7b96d9f2ce3cf1ca4b5de5f1cfc03acd7d`. It was built earlier on the same VM, not rebuilt for this run. The patch changes no file under `vm/`.
- Upstream does not track `Cargo.lock` for these three crates. The lock files came from earlier builds on the same VM.

## Harness notes

Two first attempts failed because of the harness, not the code, and were rerun:

- `tests_mainnet/` was first started with the Ragger `--device` option, which that suite does not accept (pytest usage error, rc 4). The rerun uses the upstream CI command.
- The `client` crate first failed to build because `hidapi` could not find `libudev.pc`. The rerun sets `PKG_CONFIG_PATH` to the toolchain sysroot.

## ELFs under test

| App | Device | Bytes | sha256 |
|---|---|---:|---|
| ref, testnet | nanosp | 247144 | `6a3c677e90ea859fdadbad206b9a7f4da27689a906ae24a0d7c13eacaa8d2d66` |
| ref, testnet | nanox | 247464 | `f52304a6ebf7ce5d3b842edd1a66799b8f2550816e0f0a4c5badf8996a992d3a` |
| lean, testnet | nanosp | 247076 | `f70adbac3c33d7b242e00b3b8e024da9b9408e3841de44321d8d59d57ac6858b` |
| lean, testnet | nanox | 247360 | `f26377ce3fc1ac8fc4c1e45ceb3676aa2b1af9c1793271856d091153a10cc2ff` |
| lean, mainnet | nanosp | 247068 | `fdbae5d93c8be067d6b9a13709a67e3e66891352ab7d5278581e49bdddf42d56` |
| lean, mainnet | nanox | 247352 | `6331d52de899967e017fc8d541c562c83225733fa51e7941ea9138762dfac63b` |
| lean, perf | nanosp | 242308 | `6d4758ca1de76879fa39259c3fd0d4fe3853b36a334b06a7899348fc308618ce` |
| lean, perf | nanox | 242268 | `73e3250e225c654a2d41bc90d6eaa748e40ef866363965bdbadaded80dd17f52` |
| Vanadium V-App, plain | riscv32imac | 266820 | `08b0ec46505ac02c09cda90bb8e96ca3527b893f2936305102a1fe9586a366c9` |
| Vanadium V-App, autoapprove | riscv32imac | 234348 | `f92d7635181dc576dcdea4d5bbbbdc6b20f52c12914c39e78af3f0e81499eb9b` |

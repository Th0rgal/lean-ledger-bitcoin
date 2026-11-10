# Spec Card 000 — Initial Unified Formal Specification (`Spec/`)

- **Spec Card ID**: `SC-000`
- **Status**: Frozen (Wave 1.5 Baseline Freeze)
- **Date**: 2026-11-10
- **Repository**: `Th0rgal/lean-ledger-bitcoin` (`leanprover/lean4:v4.35.0`)
- **Pinned Reference Codebases**:
  - **BOLOS Secure Element App (`LedgerHQ/app-bitcoin`)**: `f010982d3050e02813cd7129bebd68cf2d1f2099`
  - **Vanadium RISC-V V-App (`LedgerHQ/vanadium`, `apps/bitcoin`)**: `ace8e96982408959dea9e7fbc59ee36e8c54e645`
- **Auditors (Dual-Family Wave 1.5 Quorum)**:
  - **Auditor A (`b69768e4-c105-4c8c-a670-72977dd812b7`)**: Gemini Carbon 4 (`antigravity`, `low` effort) — Line-by-line C/Rust cross-reference & test-suite rejection audit
  - **Auditor B (`c0197c71-72df-4975-8fff-8b74c9a2d9e6`)**: EF `glm-5.3` (`opencode`) — Mechanical axiom hygiene (`Lean.collectAxioms`) + 25-input / 7-spec mutation audit
  - **Remediation Workers**: `R1` (`08309456-2838-4664-b7eb-079fe4748ae8`, `Spec/{Basic,Bip32,Script,WalletPolicy}.lean`), `R2a` (`6204cb1e-3b1b-49d2-9f74-c931896c20b2`, `Spec/{MerkleProtocol,Psbt}.lean`), & `R2b` (`3fedb2c8-2e09-4876-aa32-7fe1ce345d3f`, `Spec/{Musig2,SilentPayments,AppStateMachine,Unified}.lean`)

---

## 1. Specification Scope & Architecture

`Spec/` defines the implementation-independent, plain Lean 4 formal specification of the Ledger Bitcoin hardware wallet application across **both** target execution environments (BOLOS ARM Thumb Secure Elements and Vanadium RISC-V V-Apps):

| Module | Domain Responsibility |
| :--- | :--- |
| `Spec/Basic.lean` | Fixed-width byte arrays (`Bytes32`, `SizedBytes`), little/big-endian integer codecs, canonical Bitcoin `CompactSize` / `VarInt`, checked satoshi arithmetic (`MAX_MONEY = 2_100_000_000_000_000`), network parameters, and exact BOLOS (`BolosStatusWord` + `BolosErrorCode`) / Vanadium (`AppError` CBOR `0..58`) error projections. |
| `Spec/Bip32.lean` | BIP-32 path representation, BOLOS OS kernel path lock (`PATH_APP_LOAD_PARAMS`), BOLOS vs Vanadium `GET_EXTENDED_PUBKEY` silent-export whitelists and depth limits (`10` / `16` / `255`), `KeyTree::{Standard, Resident}`, and `CryptoDerivationOracle.Lawful` unhardened `CKDpriv`/`CKDpub` homomorphism. |
| `Spec/Script.lean` | Standard `scriptPubKey` classification (`P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, `P2TR`, `OP_RETURN`, unknown SegWit), minimal `OP_RETURN` push validation, Base58Check, and BIP-173 / BIP-350 / BIP-352 Bech32 & Bech32m codecs (`1 <= hrp.length <= 83`). |
| `Spec/WalletPolicy.lean` | Legacy `V1` and BIP-388 `V2` Wallet Policies, stacked-wrapper BIP-379 Miniscript parser/typechecker/compiler (`B/V/K/W`, `z/o/n/d/u`, `m`, `s`, `k`, BIP-68 `older`, P2WSH & BOLOS resource bounds), BIP-341 TapTree/TapTweak commitments, and `PolicyProfile` target parameterization (`canonicalLedgerProfile`, `bolosAppProfile`, `vanadiumAppProfile`). |
| `Spec/Psbt.lean` | PSBTv0-to-v2 normalization, input/output security validation, dual-UTXO cross-check (`nonWitnessUtxo` vs `witnessUtxo`), internal/external key & script verification, verified change elision (`isChange = true`), fee & high-fee warnings (`full` and `selfTransfer`), `TxDisplayMode.unavailable` on open/mixed sighashes, BIP-143 / BIP-341 / BIP-342 sighashes, BIP-322 message signing, and Ledger Swap mode invariants. |
| `Spec/MerkleProtocol.lean` | BOLOS interactive Merkleized map streaming (`CLA=0xE1`/`0xF8`, `0xE000`, `CCMD_*`), strict lexicographic key-sorting, raw & leaf-prefixed preimage openings, BOLOS depth/key-size bounds, and constructive finite-pool collision-relative soundness (`CollisionFreeOn`). |
| `Spec/Musig2.lean` | BIP-327 KeyAgg, BIP-328 synthetic xpub derivation + TapTweak, deterministic synthetic nonce generation (`"MuSig2 nonce"`), Round-1/Round-2 session store (`capacity = 32` / `28B` prefix on BOLOS, `capacity = 1` / `32B` on Vanadium), re-registration after Round-2 deletion, and ghost `RandRoot` single-use nonce linearity. |
| `Spec/SilentPayments.lean` | BIP-352 Silent Payment addresses (`sp`/`tsp`), BIP-392 scan-key export (`spscan`/`tspscan`), eligible input selection & `BIP0352/Inputs` hash, BIP-374 DLEQ proofs, and BIP-375 PSBT Silent Payment validation (explicit `SIGHASH_ALL`, `spV0Label` verification, BIP-341 NUMS rejection). |
| `Spec/AppStateMachine.lean` | Top-level BOLOS APDU + Vanadium CBOR command state machine, `HardwareOracle` & `UserApprovalOracle` TCB boundary, Swap session termination on failure, read-only purity, atomic error rollback, user-consent gates (including Silent Payment ECDH share emission and Vanadium Round-1), and MuSig2 anti-replay. |
| `Spec/Unified.lean` | Cross-module type bridges (`Network`/`TargetProfile`/`PolicyProfile`, `Bytes32`/`SizedBytes`, `canonicalScriptBech32mCodec`), `HardwareOracle.Lawful`, and end-to-end verified `SIGN_PSBT` composition (`buildVerifiedPsbtSignRequest` / `stepVerifiedPsbtSign`). |

---

## 2. Mechanical Soundness & Axiom Hygiene Contract

Every declaration and theorem under `Spec.*` satisfies:
1. **Plain Lean 4 only**: Zero wrapper DSLs (`SpecM`, `ObsQuotient`, `SpecBlock`, `SubSpec`), zero external spec libraries.
2. **Zero unproved obligations**: `0 sorryAx`.
3. **Zero kernel-bypassing reduction**: `0 Lean.ofReduceBool` and `0 Lean.trustCompiler` (`0 native_decide`).
4. **Strict constructive foundation**: Every `Spec.*` declaration's transitive axiom footprint via `Lean.collectAxioms` is a subset of `{propext, Quot.sound}` (`0 Classical.choice`).
5. **Non-vacuity**: Positive end-to-end execution witnesses (`rfl` / constructive witnesses) accompany negative security rejection theorems across every module, including finite-pool `CollisionFreeOn` witnesses in `Spec/MerkleProtocol.lean`.

---

## 3. Target Parameterization vs Canonical Security Floor

Where BOLOS (`app-bitcoin`) and Vanadium (`apps/bitcoin`) intentionally differ in wire protocol, resource bounds, or feature surface, `Spec/` parameterizes behavior cleanly via `TargetProfile` / `PolicyProfile` / `SigningConfig`:
- **Transport & Framing**: Merkleized streaming APDUs (`CLA=0xE1`/`0xF8`) + Base58Check xpubs + `BolosStatusWord` on BOLOS vs monolithic CBOR `FastPsbt` + 78-byte binary xpubs + `AppError` (`0..58`) on Vanadium.
- **Account & Key Model**: Stateless default BIP-44/49/84/86 policies (`0x00^32` HMAC, `addressIndex <= 50000`), V1/V2 policies, BIP-322, `SIGN_MESSAGE`, and Exchange `SwapLock` on BOLOS vs mandatory Proof-of-Registration, multi-account `VND_ACCOUNT` signing, `KeyTree::Resident`, Identity keys (`IDAUTH`), and BIP-352/374/375/392 Silent Payments on Vanadium.
- **MuSig2**: Transaction-independent `psbt_session_id`, untweaked `aggpk` in `NonceGen`, 32-slot 28-byte-prefix NVRAM store on BOLOS vs tx-bound `psbt_session_id`, post-tweaked `aggpk` in `NonceGen`, 1-slot 32-byte NVRAM store, and multi-internal-key `musig(...)` on Vanadium.

Where side-by-side deduction uncovered **upstream implementation bugs or security regressions** in Vanadium (`andor` branch inversion, `u64`/`i64` amount overflow, `depth = 256` `u8` wraparound, BIP-370 dual/fallback locktime bugs, missing dual-UTXO cross-check, missing Miniscript sanity checks), `Spec/` enforces the **sound BIP/BOLOS security invariant** and documents every upstream discrepancy in [`docs/spec-cards/vanadium-upstream-bugs.md`](./vanadium-upstream-bugs.md).

---

## 4. Post-Freeze Spec Evolution Governance

From this freeze onward, `BitcoinLedger/` implementations and `Proofs/` refinement theorems must target `Spec/` as frozen. Any proposed post-freeze edit to `Spec/` requires:
1. Triage into `CandidateBug` (fix implementation/upstream, keep spec), `SpecTooStrong` (relax spec minimally with official test citation), or `ReferenceDiscrepancy` (factor into target profile parameter while preserving shared core invariants).
2. A numbered Spec Card `docs/spec-cards/NNN-<slug>.md` recording the counterexample, Reference citation, minimalism justification, and dual-family review verdict.
3. Re-verification of `AuditUnifiedSpec.lean` (`0 sorryAx`, `0 native_decide`, `0 Classical.choice`).

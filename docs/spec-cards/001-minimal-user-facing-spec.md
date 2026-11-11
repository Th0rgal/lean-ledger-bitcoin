# Spec Card 001 — Two-Tier Formal Architecture: Minimal User-Facing `Spec/` + Detailed `InternalSpec/`

- **Spec Card ID**: `SC-001`
- **Status**: Active (Wave 4 Architecture Layering)
- **Date**: 2026-11-11
- **Repository**: `Th0rgal/lean-ledger-bitcoin` (`leanprover/lean4:v4.35.0`)
- **Supersedes / Layers Above**: [`SC-000` (`000-initial-unified-spec.md`)](./000-initial-unified-spec.md)
- **Classification**: `SpecRefactoring` (Zero relaxation of security invariants; explicit separation of human-auditable user-facing contracts from byte/wire-level protocol mechanization)

---

## 1. Motivation & Problem Statement

In Waves 1–3 (`SC-000`), the full `20,435`-LOC protocol mechanization lived directly under `Spec/`. While mechanically complete across BIP-32/388/379/174/370/143/341/342/322/327/328/352/374/375/392, BOLOS Merkleized APDU streaming (`CLA=0xE1`/`0xF8`), and Vanadium CBOR `FastPsbt` dispatch, a `20,435`-line specification is too large for a security auditor or Bitcoin developer to read cover-to-cover in one sitting when verifying **what security properties the hardware wallet actually guarantees to the user**.

In Wave 4, we refactor the formal architecture into two clean, constructively connected layers without losing a single line of wire-level mechanization or proof coverage:

1. **`Spec/` (`801` LOC total across 4 files)** — **Minimal, Human-Auditable, Non-Overlapping User-Facing Specification**:
   States every security-critical contract that a Ledger Bitcoin user, wallet integrator, or security reviewer cares about in plain, self-contained Lean 4 (`def`, `structure`, `inductive`, `theorem` — zero wrapper DSLs).
2. **`InternalSpec/` (`20,435` LOC across 10 modules)** — **Complete Protocol & Wire-Level Mechanization**:
   Preserves the entire Wave 1–3 mechanization verbatim (`Basic`, `Bip32`, `Script`, `WalletPolicy`, `Psbt`, `MerkleProtocol`, `Musig2`, `SilentPayments`, `AppStateMachine`, `Unified`).
3. **`Proofs/UserSpecRefinement.lean` (`973` LOC)** — **Constructive End-to-End Refinement Bridge**:
   Proves that the executable `BitcoinLedger/` implementation and `InternalSpec/` protocol state machine satisfy the top-level user-facing `Spec/` contracts without gaps, axioms, or classical choice.

---

## 2. Non-Overlapping Decomposition of `Spec/` (`801` LOC)

Each file in `Spec/` owns an orthogonal security domain with zero duplicate definitions:

| File | LOC | Security Domain & Core Contracts |
| :--- | ---: | :--- |
| `Spec/KeyPolicy.lean` | `250` | **Domain 1 — Key Derivation, Wallet Policy & Identity Isolation**: `Platform` (`.bolos`, `.vanadium`), `KeyTree` (`.standard`, `.resident`), depth ceiling (`MAX_XPUB_DEPTH = 255`, preventing `u8` depth wraparound `VND-BUG-007`), silent vs user-approved xpub export (`canExportExtendedPubkey`), signable policy & Proof-of-Registration authorization (`canUseWalletPolicy`), receive/change derivation branch non-collision, BIP-352 Silent Payment scan-key export (`canExportSilentPaymentScanKey`), and Vanadium identity-key signing (`canSignWithIdentityKey`). |
| `Spec/TransactionSafety.lean` | `232` | **Domain 2 — Value Conservation, Anti-Fee-Sniping, Change Integrity & Swap Lock**: Checked 64-bit satoshi summation bounded by `MAX_MONEY = 2_100_000_000_000_000` (`checkedSatoshiSum?`, preventing `u64`/`i64` overflow `VND-BUG-002`), CVE-2020-14199 dual-UTXO witness/non-witness consistency (`validInputUtxoConsistency`), BIP-370 input/fallback locktime domain compatibility (`validPsbtLocktimeCompatibility`, `VND-BUG-004`), verified internal change elision & conservation (`exactSatoshiSum inputAmounts = externalRecipientSum outputs + verifiedChangeSum outputs + fee`), open-sighash fee hiding (`TxWarningFlags`), and pre-approved Ledger Exchange `SwapLock` enforcement (`satisfiesSwapContract`, standard + cross-chain `OP_RETURN`). |
| `Spec/SessionSecurity.lean` | `172` | **Domain 3 — User Consent, Session Atomicity, MuSig2 Nonce Linearity & Silent Payment Gates**: Explicit `CommandKind` read-only classification (`respectsSessionAtomicity`: successful read-only commands leave persistent state unchanged; failed commands preserve accounts, swap lock, resident seed, and monotonically preserve consumed MuSig2 nonces), secret-material authorization (`authorizedSecretEmission`: no signature, MuSig2 partial sig, or Silent Payment ECDH share is emitted without `UserApproved` or valid BOLOS `SwapLock`), BIP-327 single-use `RandRoot` anti-replay & self-pubnonce integrity (`validMusigRound1Transition`, `validMusigRound2Transition`, `VND-BUG-008`), and BIP-375 Silent Payment output/input gates (`validSilentPaymentPsbtGate`: explicit `SIGHASH_ALL`, `SegWit ≤ v1`, non-NUMS eligible input). |
| `Spec.lean` | `147` | **Top-Level Composition & Master Security Theorem**: Composes Domains 1–3 into `Spec.validEndToEndPsbtExecution` and proves `Spec.master_psbt_execution_security` (simultaneously establishing policy ownership, `MAX_MONEY` satoshi conservation without overflow, CVE-2020-14199 & BIP-370 safety, Swap/UI authorization, and BIP-327 Round-2 nonce burn + replay impossibility) alongside a concrete `rfl` non-vacuity witness (`Spec.nonvacuous_validEndToEndPsbtExecution`). |

---

## 3. Refinement Bridge (`Proofs/UserSpecRefinement.lean`)

`Proofs/UserSpecRefinement.lean` establishes explicit projection functions (`projectPlatform`, `projectKeyTree`, `projectPolicySummary`, `projectCommandKind`, `projectSessionState`) and proves constructive refinement across every domain:

- **`bolos_getExtendedPubkey_refines_userSpec` & `evalGetExtendedPubkey_enforces_userSpec_depth`**: Any `GET_EXTENDED_PUBKEY` accepted by `BitcoinLedger.AppStateMachine.stepAppCommand` / `BitcoinLedger.Bip32.evalGetExtendedPubkey` satisfies `Spec.canExportExtendedPubkey` and `path.length ≤ Spec.MAX_XPUB_DEPTH`.
- **`validateAccountAuth_refines_canUseWalletPolicy`**: Executable account authentication (`BitcoinLedger.AppStateMachine.validateAccountAuth`) implies `Spec.canUseWalletPolicy` across default, zero-PoR, registered HMAC, and Swap modes on both BOLOS and Vanadium.
- **`checkedSumSats?_refines_userSpec` & `validSwapPsbt_standard_refines_userSpec`**: Executable satoshi summation (`BitcoinLedger.checkedSumSats?`) is definitionally/extensionally identical to `Spec.checkedSatoshiSum?` (`≤ MAX_MONEY`), and `BitcoinLedger.AppStateMachine.validSwapPsbt` implies `Spec.satisfiesSwapContract`.
- **`stepAppCommand_refines_sessionAtomicity` & `signPsbt_secret_emission_refines_userSpec`**: Every `BitcoinLedger.AppStateMachine.stepAppCommand` transition satisfies `Spec.respectsSessionAtomicity`, and any `.signPsbt` emitting secret-derived material satisfies `Spec.authorizedSecretEmission`.
- **`consumeRound2_refines_userSpec_nonce_linearity`**: Executable MuSig2 Round-2 session consumption (`BitcoinLedger.Musig2.consumeRound2`) satisfies `Spec.validMusigRound2Transition` (fresh unconsumed `RandRoot`, permanent addition to `consumedMusigRandRoots`, active-slot deletion, and self-pubnonce verification).
- **`analyzePsbtSilentPayments_refines_userSpec_gate`**: Executable BIP-375 Silent Payment analysis (`BitcoinLedger.SilentPayments.analyzePsbtSilentPayments`) enforces `Spec.validSilentPaymentPsbtGate`.
- **`impl_stepVerifiedPsbtSign_satisfies_master_userSpec`**: Concrete end-to-end non-vacuity and refinement theorem executing `BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign` on a Mainnet BIP-84 transaction and proving `Spec.validEndToEndPsbtExecution = true` alongside signature emission.

---

## 4. Mechanical Axiom Audit Verification

Verified via `Tests/AxiomAudit.lean` (`lake build Spec InternalSpec BitcoinLedger Proofs Tests`):
- **Audited declarations**: `253` `Spec.*` (`53` theorems), `6,564` `InternalSpec.*` (`1,653` theorems), and `920` `Proofs.*` (`778` theorems).
- **Forbidden axioms**: `0 sorryAx`, `0 Lean.ofReduceBool`, `0 Lean.trustCompiler`, `0 Classical.choice` — every declaration depends exclusively on `{propext, Quot.sound}`.

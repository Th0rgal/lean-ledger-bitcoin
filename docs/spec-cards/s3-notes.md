# Track S3 Specification Notes — PSBT Signing, Sighashes, BIP-322, Swap & BOLOS Merkle Protocol

- **Campaign**: `lean-ledger-bitcoin` (Wave 1, Track S3)
- **Branch**: `wave1/spec-s3-psbt-merkle` (forked from `9e4ada6`)
- **Owned Files**:
  - `Spec/Psbt.lean` — Canonical PSBTv0/v2 model, input/output security invariants, fee & change rules, Legacy / BIP-143 / BIP-341 / BIP-342 sighash digests, BIP-322 virtual PSBT validation, and Ledger Swap mode checks.
  - `Spec/MerkleProtocol.lean` — BOLOS RFC-6962-variant Merkle trees, Merkleized key-value map commitments, strict lexicographic key-sorting invariant, interactive untrusted-host client commands (`CCMD_*`), and collision-relative Merkleized map soundness proofs.
  - `docs/spec-cards/s3-notes.md` — Reference discrepancies, potential bug candidates, edge cases, and Wave 1.5 integration guide.
- **Reference Codebases Inspected**:
  - `LedgerHQ/app-bitcoin` @ `f010982d3050e02813cd7129bebd68cf2d1f2099` (BOLOS C Secure Element app)
  - `LedgerHQ/vanadium` (`apps/bitcoin`) @ `ace8e96982408959dea9e7fbc59ee36e8c54e645` (Vanadium RISC-V Rust V-App)

---

## 1. Discovered Reference Discrepancies & Potential Bug Candidates (`app-bitcoin` vs `vanadium`)

Systematic comparison of both official Ledger Bitcoin codebases against BIP-143, BIP-174, BIP-322, BIP-341/342, BIP-370, BIP-375, and BIP-388 uncovered **7 substantive behavioral discrepancies**, including **2 candidate protocol/security bugs in Vanadium**:

### Discrepancy 1 (Candidate Bug in Vanadium) — BIP-370 Locktime Determination
- **BOLOS (`app-bitcoin/src/common/locktime.h`, `locktime_determine`)**:
  1. Validates `0 < required_height_locktime < 500_000_000` and `required_time_locktime >= 500_000_000` on every input.
  2. Correctly implements BIP-370 dual-locktime semantics: an input specifying **both** `PSBT_IN_REQUIRED_HEIGHT_LOCKTIME` and `PSBT_IN_REQUIRED_TIME_LOCKTIME` can be satisfied by *either* locktime type; a conflict occurs **if and only if** at least one input specifies *only* height and at least one input specifies *only* time. When both types satisfy all inputs, block height wins as tie-breaker.
  3. Uses `PSBT_GLOBAL_FALLBACK_LOCKTIME` (defaulting to `0`) **only** when no input specifies any required locktime.
- **Vanadium (`vanadium/apps/bitcoin/common/src/fastpsbt.rs:602-634`, `compute_lock_time`)**:
  1. **Bug 1a (Spurious rejection of dual-locktime inputs)**: Tracks global `req_height: Option<u32>` and `req_time: Option<u32>` across all inputs and fails whenever `req_height.is_some() && req_time.is_some()` — falsely rejecting valid BIP-370 PSBTs where a single input declares both locktime fields!
  2. **Bug 1b (Zero height accepted)**: Only checks `if h >= 500_000_000 { return Err(...); }`, failing to reject `required_height_locktime == 0` (violating BIP-370's `> 0` requirement).
  3. **Bug 1c (`fallback_locktime` mixed into `max`)**: Computes `self.global.fallback_locktime.unwrap_or(0).max(h)` instead of ignoring `fallback_locktime` when inputs constrain locktime. Worse, if `fallback_locktime >= 500_000_000` (a UNIX timestamp) while inputs require block height `h < 500_000_000`, `.max(h)` silently switches the transaction's `nLockTime` from block height to UNIX timestamp, violating the input's height lock!
- **Canonical Spec Choice (`Spec/Psbt.lean`, `determineLocktime`)**: Models exact BIP-370 + `app-bitcoin` semantics; proven in `bip370_locktime_conflict_rejected` and `bip370_locktime_ignores_fallback_when_constrained`.

### Discrepancy 2 (Candidate Security Weakness in Vanadium) — Dual-UTXO Cross-Check (`nonWitnessUtxo` + `witnessUtxo`)
- **BOLOS (`app-bitcoin/src/handler/sign_psbt/preprocess_inputs.c:218-246` & `amount_from_psbt.c:31-101`)**:
  - Whenever `PSBT_IN_NON_WITNESS_UTXO` is present (even on SegWit v0 or Taproot v1 inputs), BOLOS computes `doubleSha256` (stripping witness data) to verify `txid == prevout_hash`, extracts `nonWitnessUtxo.vout[prevout_n]`, and when `PSBT_IN_WITNESS_UTXO` is **also** present, enforces that **both** `amount` and `scriptPubKey` of `witnessUtxo` match `nonWitnessUtxo.vout[prevout_n]`.
  - SegWit v0 inputs omitting `nonWitnessUtxo` trigger `warnings.missing_nonwitnessutxo` (CVE-2020-14199 defense).
- **Vanadium (`vanadium/apps/bitcoin/app/src/handlers/sign_psbt/analyze.rs:223-243, 304-316`)**:
  - `validate_input_utxos` checks `non_witness_utxo` txid for Legacy and SegWit v0 (raising `missing_nonwitnessutxo` if absent on SegWit v0), and ignores `non_witness_utxo` completely on Taproot.
  - However, `input_prevout` (`analyze.rs:304-316`) checks `if let Some(witness_utxo) = &input.witness_utxo { return Ok(witness_utxo); }` **without** verifying that `non_witness_utxo.output[vout] == *witness_utxo` when both are supplied! A malformed PSBT containing a valid `non_witness_utxo` (silencing the `missing_nonwitnessutxo` warning!) alongside a lied-about `witness_utxo` amount would have its `non_witness_utxo` pass txid verification while `witness_utxo` is used for fee display and BIP-143 signing.
- **Canonical Spec Choice (`Spec/Psbt.lean`, `extractInputPrevout` & `validateInputUtxo`)**: Enforces BOLOS's strict cross-check (`nwOut == wUtxo`) whenever both UTXO fields are present; proven in `dual_utxo_mismatch_rejected`, `mismatched_non_witness_utxo_txid_rejected`, and `legacy_input_with_witness_utxo_rejected`.

### Discrepancy 3 — Amount Sum `MAX_MONEY` & `u64` Overflow Guard
- **BOLOS (`app-bitcoin/src/handler/sign_psbt/preprocess_inputs.c`, `preprocess_outputs.c`, `process_in_outs.c`)**: Checks `amount <= BITCOIN_TOTAL_SUPPLY` (`21,000,000 * 10^8` sats) on individual inputs/outputs and running sums before `uint64_t` arithmetic.
- **Vanadium (`vanadium/apps/bitcoin/app/src/handlers/sign_psbt/analyze.rs:146, 179`)**: Uses unchecked `u64` addition (`ctx.summary.total_inputs_sats += prevout.value.to_sat()`, `total_outputs_sats += output.amount.to_sat()`) without a `MAX_MONEY` cap.
- **Canonical Spec Choice (`Spec/Psbt.lean`)**: Uses arbitrary-precision `Nat` sums in `Spec` paired with explicit `amount <= MAX_MONEY` and `sum <= MAX_MONEY` checks (`PsbtError.amountExceedsMaxSupply`), guaranteeing 64-bit arithmetic in `BitcoinLedger/` cannot overflow.

### Discrepancy 4 — High-Fee Warning Boundary at `100,000` Satoshis
- **BOLOS (`app-bitcoin/src/ui/display_utils.c` / `transaction_display.c:30`)**: Triggers `high_fee` warning iff `10 * fee >= total_ValidateInputs && total_ValidateInputs > 100_000` (strict `>`).
- **Vanadium (`vanadium/apps/bitcoin/app/src/handlers/sign_psbt/display.rs:133`)**: Triggers `high_fee` warning iff `total_ValidateInputs >= 100_000 && (fee * 100) / total_ValidateInputs >= 10` (inclusive `>=`). Note also integer division `(fee * 100) / total >= 10` is exact-equivalent to `10 * fee >= total` for non-negative integers (`fee * 100 >= 10 * total ⇔ 10 * fee >= total`).
- **Canonical Spec Choice (`Spec/Psbt.lean`, `SigningConfig.highFeeInclusiveAt100k`)**: Explicitly parameterized via `SigningConfig.highFeeInclusiveAt100k : Bool` (`false` for BOLOS parity, `true` for Vanadium parity) while keeping `10 * f >= sumInputs` overflow-free.

### Discrepancy 5 — External Inputs, Multi-Account Signing, and Receive-Branch Output Hiding
- **BOLOS (`app-bitcoin/src/handler/sign_psbt/preprocess_inputs.c`, `preprocess_outputs.c`)**:
  - Signs for a **single** wallet policy per `SIGN_PSBT` APDU.
  - Allows external inputs (belonging to co-signers / other wallets), setting `warnings.external_inputs = true` and requiring ≥ 1 internal input (unless BIP-322 default policy).
  - Silently elides an output as **change** (`isVerifiedChange`) **only** when `is_change == true` (`numSecond`, internal branch), up to `MAX_CHANGE_OUTPUTS = 10`. Outputs to our own wallet policy on the **receive branch** (`is_change == false`, `numFirst`) are **never** hidden and always appear in `DisplayedOutputs`!
- **Vanadium (`vanadium/apps/bitcoin/app/src/handlers/sign_psbt/analyze.rs`)**:
  - Supports multi-account signing in a single PSBT via proprietary `PSBT_GLOBAL_VND_ACCOUNT` (`"ACCOUNT"`) Proof-of-Registration commitments.
  - Rejects external inputs outright (`SignPsbtError::ExternalInputsNotSupported`) unless resolved to a declared `ACCOUNT` or resident identity key.
  - Classifies *both* receive (`is_change = false`) and change (`is_change = true`) outputs of declared accounts as `AnalyzedOutput::Internal` when computing net per-account `Spend from` / `Send to` summaries.
- **Canonical Spec Choice (`Spec/Psbt.lean`)**: Core `isVerifiedChange` enforces the strict single-policy change-branch invariant (`isChange == true`, proven in `unverified_change_never_hidden` and `receive_branch_output_not_verified_change`), with `SigningConfig.allowExternalInputs` gating BOLOS (`true`) vs Vanadium (`false`) external-input policy.

### Discrepancy 6 — Non-Default Sighash Policy & BIP-375 Silent Payment Sighash Restriction
- **BOLOS (`app-bitcoin/src/handler/sign_psbt/sign_input.c` & `preprocess_inputs.c`)**:
  - Legacy inputs: only `SIGHASH_ALL (0x01)` is supported (non-default sighashes rejected even if expert mode is enabled).
  - SegWit v0 & Taproot v1 inputs: `SIGHASH_DEFAULT (0x00)` (Taproot only) and `SIGHASH_ALL (0x01)` are safe; `NONE`, `SINGLE`, and `ANYONECANPAY` combinations are gated behind `SigningConfig.allowNonDefaultSighash` and raise `warnings.nonDefaultSighash`. For `SIGHASH_SINGLE`, BOLOS enforces `inputIndex < outputs.size` (`sign_input.c`).
  - Fee display: when any input uses `ANYONECANPAY` or `NONE`/`SINGLE`, total fee is not closed (`fee = none`, `TxDisplayMode.inputsOnly`).
- **Vanadium (`vanadium/apps/bitcoin/app/src/handlers/sign_psbt/analyze.rs` & `silent_payments.rs`)**:
  - Rejects all sighashes other than `SIGHASH_ALL (0x01)` and (for Taproot when no Silent Payment output is present) `SIGHASH_DEFAULT (0x00)`.
  - Per BIP-375, if any output contains `PSBT_OUT_SP_V0_INFO`, Taproot inputs **must** use explicit `SIGHASH_ALL (0x01)` (`SIGHASH_DEFAULT` `0x00` is rejected with `.silentPaymentForbidsSighashDefault`).
- **Canonical Spec Choice (`Spec/Psbt.lean`)**: Captures the exact union cleanly via `classifySighash`, `SigningConfig.allowNonDefaultSighash`, and the BIP-375 `hasSilentPayments` gate in `validateInputsLoop`.

### Discrepancy 7 — Transport & Feature Surface Partition
- **BOLOS-exclusive features** (modeled in `Spec/Psbt.lean` and `Spec/MerkleProtocol.lean`):
  1. Interactive Merkleized map streaming (`CLA=0xE1` / `0xF8`, `SW_INTERRUPTED_EXECUTION = 0xE000`, `CCMD_YIELD`, `CCMD_GET_PREIMAGE`, `CCMD_GET_MERKLE_LEAF_PROOF`, `CCMD_GET_MERKLE_LEAF_INDEX`, `CCMD_GET_MORE_ELEMENTS`).
  2. Intentional BOLOS deviation from RFC 6962: `MTH([]) = 32 zero bytes` (`zeroBytes32`), whereas RFC 6962 defines `MTH([]) = SHA256("")` (`doc/merkle.md` & `src/common/merkle.c`).
  3. Out-of-bounds index check order in `get_merkle_leaf_index.c:34`: BOLOS rejects `index >= size` **before** checking `!found_flag`, meaning for an empty map (`size == 0`), even `found = 0, index = 0` returns error (`0 >= 0`)! Modeled faithfully in `deviceLookupMerkleMapValue` and proven in `out_of_bounds_index_rejected`.
  4. BIP-322 virtual PSBT message signing (`PSBT_GLOBAL_GENERIC_SIGNED_MESSAGE` in `bip322_validation.c` / `bip322.c`).
  5. Ledger Exchange / Swap silent signing (`swap_checks.c`: `Standard` single-recipient mode and `CrossChain` `OP_RETURN` 20-byte payin-hash mode, strictly forbidding BIP-322, external inputs, non-default sighashes, and multiple change outputs).
  6. Cleartext Miniscript timelock / hashlock satisfaction (`cleartext.h`).
- **Vanadium-exclusive features**:
  1. Monolithic `FastPsbt` wire transport + automatic PSBTv0 (`PSBT_GLOBAL_UNSIGNED_TX`) to PSBTv2 normalization (`fastpsbt.rs`, modeled in `normalizePsbtV0ToV2`).
  2. BIP-352 / BIP-374 / BIP-375 Silent Payments (`PSBT_OUT_SP_V0_INFO`, `PSBT_OUT_SP_V0_LABEL`, `PSBT_IN_SP_ECDH_SHARE`, `PSBT_IN_SP_DLEQ`) — output invariants and BIP-375 sighash restriction modeled in `Spec/Psbt.lean` for S4 integration.
  3. Resident / Identity keys (`m/1227'/...`) and `IDAUTH` Schnorr output authentication (`id_auth.rs`).

---

## 2. Summary of Machine-Checked Theorems (`0 sorryAx`, `0 native_decide`)

### In `Spec/Psbt.lean`:
- `unverified_change_never_hidden`: Any output with `isVerifiedChange policy out = false` is guaranteed to appear in `displayedOutputs`.
- `receive_branch_output_not_verified_change`: Outputs derived on the receive branch (`isChange = false`) are never silently hidden as change.
- `negative_fee_rejected` & `validated_psbt_fee_non_negative`: Closed-commitment PSBTs with `sumInputs < sumOutputs` are unconditionally rejected; any `ValidatedPsbt` with `fee = some f` satisfies `sumOutputs ≤ sumInputs` and `f = sumInputs - sumOutputs`.
- `missing_utxo_rejected`, `mismatched_non_witness_utxo_txid_rejected`, `legacy_input_with_witness_utxo_rejected`, `dual_utxo_mismatch_rejected`: CVE-2020-14199 and mixed-UTXO commitment defenses.
- `swap_rejects_fee_mismatch`, `swap_rejects_amount_mismatch`, `swap_rejects_recipient_mismatch`, `swap_standard_rejects_extra_external_outputs`: Ledger Swap mode locks recipient address, exact external amount, exact fee, and output count before allowing UI bypass.
- `bip370_locktime_conflict_rejected` & `bip370_locktime_ignores_fallback_when_constrained`: Exact BIP-370 locktime semantics.
- `psbt_v0_nonempty_scriptsig_rejected`: BIP-174 unsigned transaction `scriptSig` emptiness enforcement during PSBTv0-to-v2 normalization.
- `bip322_rejected_in_swap_mode` & `bip322_enforces_to_spend_binding`: BIP-322 `to_spend` challenge binding and Swap isolation.
- `non_vacuity_valid_swap_psbt_accepted` & `non_vacuity_valid_bip322_psbt_accepted`: Concrete end-to-end `authorizePsbtSigning` witnesses proven by pure kernel reduction (`rfl`).

### In `Spec/MerkleProtocol.lean`:
- `strictlySorted_pairwise_distinct` & `duplicate_keys_rejected`: Strict lexicographic key ordering (`compare_byte_arrays < 0`) is irreflexive and transitive, forbidding duplicate keys at any distinct leaf indices `i ≠ j`.
- `merkleLeafHash_injective`, `merkleNodeHash_injective`, `merkleLeafHash_ne_nodeHash`: Domain-separated (`0x00` vs `0x01`) collision-relative injectivity (using `Bytes32.size_eq` to rule out 64-byte concatenation ambiguity).
- `verifyMerkleLeafHashProof_unique` & `verifyMerkleElementOpening_unique`: Even against an adversarially chosen `root`, `(root, size, index)` uniquely determines the leaf direction path (`merkleDirections`) and thus binds at most one leaf hash and element preimage under `HashCollisionFree sha256`.
- `buildMerkleAuditPath_complete` & `merkleProof_sound_against_committed_tree`: Completeness and soundness of Merkle openings against `merkleRoot sha256 leaves`.
- `sorted_merkle_map_unique_key_index`, `sorted_merkle_map_lookup_proof_unique`, & `interactive_host_cannot_equivocate_map_value`: Under `HashCollisionFree sha256` and `verifySortedMerkleMapOpenings`, no PSBT key can appear twice and **no two untrusted host oracles can ever prove distinct values `v1 ≠ v2` for the same key `k`**.
- `verified_key_scan_detects_omission`: Proves why BOLOS's key-callback presence flags (`has_witnessUtxo`, `has_sighash_type`, etc.) recorded during `check_merkle_tree_sorted_with_callback` detect host lying-by-omission (`.absentClaimed`).
- `out_of_bounds_index_rejected`: Proves `idx >= map.size` is rejected even when `found = false` (`get_merkle_leaf_index.c:34`).
- `non_vacuity_honest_merkle_map_verified_and_queried`: Concrete 3-leaf unbalanced sorted Merkleized PSBT map witness verified and queried end-to-end (`0 sorryAx`, `0 native_decide`).

---

## 3. Wave 1.5 Coordinator Unification & Integration Guide

To satisfy the Wave 1 parallel independence rule, `Spec/Psbt.lean` and `Spec/MerkleProtocol.lean` do not yet import `Spec/Basic.lean`, `Spec/Bip32.lean`, `Spec/Script.lean`, or `Spec/WalletPolicy.lean`. At Wave 1.5 integration, the coordinator can unify types directly along these clean seams:

| Self-Contained Type / Helper in `Spec/Psbt.lean` | Target Canonical Definition in S1 / S2 / S4 | Unification Action |
|---|---|---|
| `Bytes32`, `zeroBytes32`, `bytesEq`, `bytes32Eq` | `Spec/Basic.lean` (`Bytes32` / `Hash256`) | Alias or replace `Spec.Psbt.Bytes32` with `Spec.Basic.Bytes32`. |
| `MAX_MONEY`, `LOCKTIME_THRESHOLD`, `encodeU16LE`, `encodeU32LE`, `encodeU64LE`, `encodeVarInt` | `Spec/Basic.lean` | Replace local helpers with `Spec.Basic` encoders (identical little-endian & CompactSize semantics). |
| `CryptoOracles` (`sha256`, `hash160`, `formatAddress`) | `Spec/Basic.lean` + `Spec/Script.lean` | Instantiate `formatAddress` with `Spec.Script.formatAddress network` (Base58Check / Bech32 / Bech32m). |
| `KeyOrigin` (`fingerprint : UInt32`, `path : List UInt32`) | `Spec/Bip32.lean` (`KeyOrigin` / `Bip32Path`) | Unify directly with `Spec.Bip32.KeyOrigin`. |
| `mkP2SHScript`, `mkP2WSHScript`, `isP2WPKHScript`, `isP2WSHScript`, `isP2TRScript`, `isValidOpReturnScript`, `computeLegacyScriptCode` | `Spec/Script.lean` | Delegate script recognizers/constructors to `Spec.Script`. |
| `WalletPolicySpec`, `InternalKeyPlaceholder` | `Spec/WalletPolicy.lean` | Provide `WalletPolicy.toWalletPolicySpec (masterFp : UInt32) (policy : WalletPolicy) : WalletPolicySpec` computing `deriveScripts (isChange, addressIndex)` from the BIP-388 descriptor/Miniscript AST. |
| `SilentPaymentOutputInfo` & BIP-375 `hasSilentPayments` sighash gate | `Spec/SilentPayments.lean` (S4) | Feed `ValidatedPsbt` inputs/outputs into S4's BIP-352/374/375 ECDH share & DLEQ generator. |
| `PsbtTx.musig2SessionId`, `InternalKeyPlaceholder.isMusig` | `Spec/Musig2.lean` (S4) | Connect `ValidatedPsbt` and `sighashTaproot` (`TapSighash`) to S4's BIP-327 MuSig2 nonce/partial-sig state machine. |
| `authorizePsbtSigning` & `MerkleizedPsbtCommitment` / `UntrustedHostOracle` | `Spec/AppStateMachine.lean` (S4) | Wire `authorizePsbtSigning` as the canonical domain guard for `SIGN_PSBT` across both BOLOS (via `Spec.MerkleProtocol` openings) and Vanadium (via `FastPsbt` / `normalizePsbtV0ToV2`). |

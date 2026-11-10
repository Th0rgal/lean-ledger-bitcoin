# Upstream Bug & Security Discrepancy Report: `LedgerHQ/vanadium` (`apps/bitcoin`)

- **Audited Vanadium Commit**: `ace8e96982408959dea9e7fbc59ee36e8c54e645` (`LedgerHQ/vanadium`, `apps/bitcoin/{app,client,common}`)
- **Cross-Reference BOLOS Commit**: `f010982d3050e02813cd7129bebd68cf2d1f2099` (`LedgerHQ/app-bitcoin`)
- **Discovered During**: Wave 1 & Wave 1.5 Formal Specification Deduction (`Th0rgal/lean-ledger-bitcoin`)

During formal specification deduction from both official Ledger Bitcoin implementations, side-by-side modeling uncovered **9 concrete bugs and security regressions** in the Vanadium Bitcoin V-App (`apps/bitcoin`) relative to the BIP standards and `LedgerHQ/app-bitcoin`. Each item below records its triage (`CandidateBug`), exact file/line location, impact, and how `Spec/` resolves it.

---

## 1. [CRITICAL — Consensus / Spending Mismatch] `Andor(X, Y, Z)` Compiles Inverted `OP_NOTIF` Branches
- **Location**: `apps/bitcoin/common/src/script.rs:367-373`
- **Bug**: BIP-379 defines `andor(X, Y, Z)` (`(X && Y) || (!X && Z)`) to compile to `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF` (matching `app-bitcoin/src/handler/lib/policy.c:225-238`). Vanadium emits `[X] OP_NOTIF [Y] OP_ELSE [Z] OP_ENDIF`, swapping the true and false branches (`OP_NOTIF` executes its first body when `X == 0`).
- **Impact**: Any BIP-388 wallet policy using `andor(...)` derives a wrong `witnessScript` / TapLeaf Merkle root and enforces the inverted spending condition on-chain compared to Bitcoin Core and Ledger BOLOS.
- **Spec Resolution**: `Spec/WalletPolicy.lean` (`compileMiniscript` `.andor`) enforces canonical BIP-379 `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`.

## 2. [CRITICAL — Amount Overflow & Sign-Flip] Unchecked `u64` Sums and `u64 as i64` Balance Casts
- **Location**: `apps/bitcoin/common/src/fastpsbt.rs:1052,1120`, `apps/bitcoin/app/src/handlers/sign_psbt/analyze.rs:146,179,434-435,460,469`, `display.rs:153`
- **Bug**:
  1. `fastpsbt.rs` accepts arbitrary `u64` satoshi values without checking `<= MAX_MONEY` (`2_100_000_000_000_000`).
  2. `analyze.rs` accumulates input/output sums with unchecked `u64 +=` (panicking in debug or wrapping mod `2^64` in release).
  3. `analyze.rs:434,460` casts `value as i64` into `account_spent_amounts[id]`, turning values `>= 2^63` negative, and `display.rs:153` negates `-*spent_amount as u64` (panicking/wrapping on `i64::MIN`).
- **Impact**: Malformed PSBT UTXO amounts can crash the V-App or corrupt displayed per-account `Spend from` / `Send to` totals and fees via integer wraparound.
- **Spec Resolution**: `Spec/Basic.lean` and `Spec/Psbt.lean` enforce `amount <= MAX_MONEY` on every input, output, and running sum using checked arithmetic.

## 3. [HIGH — CVE-2020-14199 Regression] Missing Dual-UTXO Cross-Check (`non_witness_utxo` vs `witness_utxo`)
- **Location**: `apps/bitcoin/app/src/handlers/sign_psbt/analyze.rs:223-243, 304-316`
- **Bug**: When an input supplies **both** `PSBT_IN_NON_WITNESS_UTXO` and `PSBT_IN_WITNESS_UTXO`, `validate_input_utxos` checks that `non_witness_utxo`'s txid matches `prevout.txid` (silencing the `missing_nonwitnessutxo` warning on SegWit v0), but `input_prevout` (`analyze.rs:305`) returns `input.witness_utxo` directly without verifying `non_witness_utxo.output[vout] == *witness_utxo` (unlike `app-bitcoin/src/handler/sign_psbt/amount_from_psbt.c:31-101`).
- **Impact**: An untrusted host can pair a genuine `non_witness_utxo` with a falsified `witness_utxo` amount to spoof fee display and BIP-143 sighash amounts without triggering `missing_nonwitnessutxo`.
- **Spec Resolution**: `Spec/Psbt.lean` (`extractInputPrevout` / `dual_utxo_mismatch_rejected`) requires exact equality of `amount` and `scriptPubKey` whenever both UTXO fields are present.

## 4. [HIGH — BIP-370 Locktime Violation] Spurious Dual-Locktime Rejection, Zero Height, and Fallback Override
- **Location**: `apps/bitcoin/common/src/fastpsbt.rs:602-634` (`compute_lock_time`)
- **Bug**:
  1. Rejects valid BIP-370 PSBTs where a single input provides both `PSBT_IN_REQUIRED_HEIGHT_LOCKTIME` and `PSBT_IN_REQUIRED_TIME_LOCKTIME` (either satisfies the input).
  2. Fails to reject `required_height_locktime == 0` (BIP-370 requires `> 0`).
  3. Computes `fallback_locktime.unwrap_or(0).max(h)` instead of ignoring `fallback_locktime` when inputs constrain locktime — if `fallback_locktime >= 500_000_000` (UNIX timestamp) and an input requires height `h < 500_000_000`, `.max(h)` silently switches `nLockTime` from block height to timestamp!
- **Spec Resolution**: `Spec/Psbt.lean` (`determineLocktime`) enforces exact BIP-370 + `app-bitcoin` (`locktime.h`) semantics.

## 5. [MEDIUM — BIP-388 Functional Bug] `sh(wsh(...))` Registers Successfully Then Always Fails Derivation
- **Location**: `apps/bitcoin/common/src/script.rs:145-170` vs `apps/bitcoin/app/src/handlers/register_account.rs`
- **Bug**: `register_account` accepts `sh(wsh(...))` policies and issues a valid Proof-of-Registration, but `DescriptorTemplate::Sh` calls `inner.to_script(..., ScriptContext::Sh, ...)` while `DescriptorTemplate::Wsh` rejects `ctx != ScriptContext::None` (`Error::InvalidScriptContext`).
- **Impact**: Every registered `sh(wsh(...))` account permanently fails `GetAddress` and `SignPsbt`.
- **Spec Resolution**: `Spec/WalletPolicy.lean` compiles `sh(wsh(...))` cleanly in `canonicalLedgerProfile` and `bolosAppProfile` while exposing `PolicyProfile.allowShWsh` to document Vanadium's current runtime restriction.

## 6. [MEDIUM — BIP-379 Policy Soundness Gap] Missing Miniscript Type, Malleability, Signature & Timelock Checks
- **Location**: `bip388-0.1.2/src/lib.rs:5` (`// TODO: - add type checks - add malleability checks - add stack limits`), `register_account.rs`
- **Bug**: Vanadium omits BIP-379 `B/V/K/W` typechecking, non-malleability (`m`), unconditional signature requirement (`s`), height/time timelock-mixing (`k`), BIP-68 `older(n)` upper-bit masking, P2WSH resource limits, and `n_internal_keys >= 1` at registration.
- **Spec Resolution**: `Spec/WalletPolicy.lean` enforces full BIP-379 type, malleability, signature, timelock, and BIP-68 sanity invariants.

## 7. [MEDIUM — BIP-32 Serialization Bug] Off-by-One `depth == 256` `u8` Wraparound on `KeyTree::Resident`
- **Location**: `apps/bitcoin/app/src/handlers/get_extended_pubkey.rs:138, 161`
- **Bug**: Checks `if bip32_path.0.len() > 256` instead of `> 255` (`u8::MAX`), then casts `let depth = bip32_path.0.len() as u8;`, wrapping `256` to `depth = 0` with non-zero `parentFingerprint`/`childNumber` (invalid BIP-32 xpub).
- **Spec Resolution**: `Spec/Bip32.lean` caps `KeyTree::Resident` derivation depth at `255` (`MAX_BIP32_BYTE_DEPTH`).

## 8. [LOW/MEDIUM — MuSig2 Robustness] Missing Round-2 Self-Pubnonce Verification
- **Location**: `apps/bitcoin/app/src/handlers/musig_signing.rs:463-485`
- **Bug**: Unlike `app-bitcoin` (`musig_signing.c:514-519`), Vanadium regenerates `_pubnonce` from `rand_root` in Round 2 and discards it without checking `_pubnonce == _my_pubnonce` from `PSBT_IN_MUSIG2_PUB_NONCE`.
- **Spec Resolution**: `Spec/Musig2.lean` supports strict self-pubnonce verification (enabled in canonical and BOLOS profiles, configurable for Vanadium compatibility).

## 9. [LOW — Wire / Parser Quirks] `GetVersion` `todo!()` Panic, `OP_RETURN` Failure, and `wutxo[8] <= 0xfc` Cap
- **Locations**:
  - `apps/bitcoin/app/src/main.rs:26`: `Request::GetVersion` panics the V-App with `todo!()` instead of returning a version or structured `AppError`.
  - `apps/bitcoin/app/src/handlers/sign_psbt/display.rs:167`: `Address::from_script` rejects every `OP_RETURN` output (`Error::AddressFromScriptFailed`).
  - `apps/bitcoin/common/src/fastpsbt.rs:231-250, 1046`: `read_compact_size` omits minimal CompactSize lower-bound checks, and line 1046 hardcodes `wutxo[8] <= 0xfc` (rejecting witness UTXOs with `scriptPubKey.len() >= 253`).

# Track S4 Specification Notes (`Spec/Musig2.lean`, `Spec/SilentPayments.lean`, `Spec/AppStateMachine.lean`)

## 1. Scope & Summary of Owned Specifications

Track S4 specifies the multi-round MuSig2 signing protocol, Silent Payments / DLEQ / PSBT Silent Payment extensions, and the unified top-level Ledger Bitcoin application state machine across both target codebases:

- **BOLOS C app**: `LedgerHQ/app-bitcoin` @ `f010982d3050e02813cd7129bebd68cf2d1f2099`
- **Vanadium Rust V-App**: `LedgerHQ/vanadium` @ `ace8e96982408959dea9e7fbc59ee36e8c54e645`

All three Lean 4 modules (`leanprover/lean4:v4.35.0`) are plain `def` / `structure` / `inductive` / `theorem` specifications with **0 `sorryAx`**, **0 `native_decide`**, and axioms restricted strictly to `{propext, Quot.sound}` (or `{}`).

### 1.1 `Spec/Musig2.lean` — BIP-327 MuSig2 & Nonce Single-Use Linearity
- **BIP-327 Key Aggregation & Tweaking**:
  - `keySort` (insertion-sorted compressed 33-byte SEC1 lexicographic order),
  - `secondUniquePubkey` (BIP-327 `get_second_key` constant-1 optimization),
  - `hashKeys` (`BIP0327/KeyAgg list`) and `keyAggCoeff` (`BIP0327/KeyAgg coefficient`),
  - `keyAgg` (accumulating `a_i * P_i` over `1..1024` participant keys, rejecting infinity),
  - `applyTweak` and `applyTweaks` (plain BIP-328 unhardened derivation tweaks vs x-only BIP-341 Taproot tweaks with odd-Y negation tracking in `KeyAggContext`).
- **BIP-327 Nonce Generation, Aggregation & Partial Signing**:
  - `syntheticRandIJ` (`SHA256("MuSig2 nonce" || rand_root || u32be(i) || u32be(j))` matching both `musig_signing.c:127-143` and `musig_signing.rs:34-49`),
  - `nonceGen` (`BIP0327/aux` XOR masking + `BIP0327/nonce` derivation of `(k_1, k_2)` and 66-byte `R_1 || R_2`),
  - `nonceAgg` (`R_1 = ∑ R_{i,1}`, `R_2 = ∑ R_{i,2}` with BIP-327 infinity fallback to 33 zero bytes),
  - `getSessionValues`, `partialSign` (`s = (k_1 + b * k_2 + e * a * g * g_acc * d) mod n` with even-Y `R` and `Q` adjustments and post-sign `partialSigVerify` self-check), `partialSigAgg`.
- **Session Store & Proved Security Theorems**:
  - `computeBolosPsbtSessionId` and `computeVanadiumPsbtSessionId`,
  - `MusigSessionStore` modeling active `(PsbtSessionId, RandRoot)` slots, optional LRU slot capacity (`32` on BOLOS, `1` on Vanadium), and monotone consumed tombstones (`consumedIds`),
  - `musig_nonce_single_use_linearity`: across any multi-step trace `ops : List MusigOp` (`round1`, `round2`, `evict`), every `PsbtSessionId` produces Round-2 partial signatures **at most once** (`countRound2SuccessFor sid ≤ 1`),
  - Negative security rejection theorems: `executeRound2Pass_rejects_missing_session`, `round2SignTask_rejects_mismatched_self_pubnonce`, `partialSign_rejects_zero_sk`, plus concrete non-vacuity witness `nonvacuous_round1_then_round2_and_replay_rejected`.

### 1.2 `Spec/SilentPayments.lean` — BIP-352 Silent Payments, BIP-374 DLEQ & BIP-375 PSBT SP
- **Address & Scan-Key Encoding**:
  - Bech32m `sp` / `tsp` Silent Payment addresses (`version = 0` with 66-byte `B_scan || B_m`; forward-compatible sender decoding for `version ∈ 1..30` taking the first 66 bytes; hard rejection of `version = 31` per BIP-352),
  - BIP-392 `spscan` / `tspscan` scan-key export encoding (`version = 0`, 65-byte `k_scan (32B) || B_spend (33B)`),
  - Label tweaking `B_m = B_spend + H_label(b_scan || ser_32(m)) * G` and explicit rejection of reserved change label `m = 0` (`deriveAccountSpAddress_rejects_change_label`).
- **Eligible Inputs, `BIP0352/Inputs` Hash & Sender/Receiver ECDH**:
  - Input eligibility classification (`P2PKH`, `P2WPKH`, `P2SH-P2WPKH` with compressed pubkeys, and `P2TR` with BIP-341 `H` NUMS key `50929b74...` exclusion via `SpInputScriptKind`),
  - Lexicographically smallest 36-byte outpoint (`txid_le || vout_le`) selection (`smallestOutpointBytes`) and `BIP0352/Inputs` tagged hash (`computeInputHash`),
  - Sender ECDH share `C = a * B_scan` (`ecdhShare`), shared secret `S = input_hash * C` (`sharedSecret`), `k`-indexed `BIP0352/SharedSecret` output derivation `P_k = B_m + t_k * G` (`outputTweak`, `outputKey`, `assignK`, `assignK_length`), and receiver spending key derivation (`receiverSpendingKey`).
- **BIP-374 DLEQ & BIP-375 PSBT Validation**:
  - `dleqChallenge`, `dleqNonce`, `dleqProve`, `dleqVerify`, and self-verification soundness theorem `dleqProve_implies_dleqVerify`,
  - Full BIP-375 PSBT input/output checks (`analyzePsbtSilentPayments`, `validatePsbtSpOutputs`, `finalizePsbtSilentPayments`): SegWit `v ≥ 2` ban, `SIGHASH_ALL` enforcement, `TX_MODIFIABLE` output-modifiability checks, orphan `PSBT_OUT_SP_V0_LABEL` rejection, per-input vs global ECDH/DLEQ verification,
  - User-consent gate theorem `exportSpScanKey_requires_user_consent` + non-vacuity witness `nonvacuous_finalizePsbtSilentPayments_ok`.

### 1.3 `Spec/AppStateMachine.lean` — Unified BOLOS + Vanadium Command & Session State Machine
- **Unified Command & Wire Surfaces**:
  - BOLOS APDU surface (`CLA = 0xE1` `0x00 GET_EXTENDED_PUBKEY`, `0x02 REGISTER_WALLET`, `0x03 GET_WALLET_ADDRESS`, `0x04 SIGN_PSBT`, `0x05 GET_MASTER_FINGERPRINT`, `0x10 SIGN_MESSAGE`; `CLA = 0xB0`/`0xE1` `0x01 GET_VERSION`; `CLA = 0xF8` `0x01 INS_CONTINUE` unexpected-continue handling; Exchange `SwapLock` standard & cross-chain OP_RETURN validation),
  - Vanadium CBOR `Request` surface (`GetVersion`, `GetMasterFingerprint`, `GetExtendedPubkey`, `RegisterAccount`, `GetAddress`, `SignPsbt`, `ExportSpScanKey`, `RegisterIdentityKey`), including `KeyTree::{Standard, Resident}`, Identity keys (`m/1229210958'`), `IdentitySignature` (`"\x09IDEN/SIGN"`), and cosigner identity PoRs (`"\x0CIDENTITY_KEY"`),
  - Bitcoin `SIGN_MESSAGE` (`"\x18Bitcoin Signed Message:\n" || varint(len) || msg` double-SHA256, 65-byte compact recoverable signature `(base + recId) || r || s`, printable ASCII vs SHA-256 hex UI display rule, `< 2^32` length bound),
  - Parameterized over explicit `HardwareOracle` and `UserApprovalOracle`.
- **Proved Core Security Theorems (`0 sorryAx`)**:
  1. **Read-only purity** (`readOnly_purity`, `getVersion_purity`, `getMasterFingerprint_purity`, `getExtendedPubkey_purity`, `getAddress_purity`): `GetVersion`, `GetMasterFingerprint`, `GetExtendedPubkey`, and `GetAddress` leave `AppPersistentState` (`registeredAccounts`, `musigSessions`, `swapLock`, `residentKeys`) identically equal (`s' = s`).
  2. **Atomic error rollback** (`atomic_error_rollback`): Any command returning `.error (e, s')` leaves `registeredAccounts`, `swapLock`, and `residentKeys` unchanged, and never resurrects a consumed MuSig2 nonce session.
  3. **User consent gate** (`user_consent_gate_signMessage`, `user_consent_gate_signPsbt`): When `UserApprovalOracle` denies consent (`ui.approve = false`), `SignMessage` never succeeds and `SignPsbt` never emits any standard or MuSig2 partial signature unless `s.swapLock = some lock` and `validSwapPsbt` holds.
  4. **MuSig2 Nonce Anti-Replay** (`musig2_nonce_anti_replay`): Across arbitrary multi-step traces `[cmd_1, ..., cmd_k]`, any MuSig2 `PsbtSessionId` produces Round-2 partial signatures in at most one step (`countMusigRound2Steps sid ≤ 1`).

---

## 2. Wave 1 Integration Map (Connecting S1..S4)

To obey the Wave 1 parallel independence rule, `Spec/Musig2.lean`, `Spec/SilentPayments.lean`, and `Spec/AppStateMachine.lean` do not yet import `Spec.Basic`, `Spec.Bip32`, `Spec.Script`, `Spec.WalletPolicy`, `Spec.Psbt`, or `Spec.MerkleProtocol`. At Wave 1 integration, the coordinator can connect them directly via the following clean interfaces:

| Track S4 Interface | Location | Upstream Track & Target Type at Wave 1 Integration |
| --- | --- | --- |
| `SizedBytes n`, `Bytes32`, `CompressedPubKey`, `XOnlyPubKey`, `SchnorrSig` | `Spec/Musig2.lean`, `Spec/SilentPayments.lean` | Alias or coerce to Track S1 `Spec/Basic.lean` fixed-width byte wrappers (`Hash256`, `Bytes32`, `PubKey33`, `XOnlyPubKey32`, `SchnorrSig64`) |
| `MusigCrypto Affine` & `SpCrypto Affine` | `Spec/Musig2.lean`, `Spec/SilentPayments.lean` | Instantiate `Affine` with Track S1's secp256k1 curve point type (`Spec/Secp256k1.lean` / `Spec/Basic.lean`), SHA-256 / BIP-340 tagged hash, and Track S1 `Spec/Bip32.lean` `ckdPubUnhardened` |
| `Bech32mCodec` | `Spec/SilentPayments.lean` | Instantiate with Track S1 `Spec/Script.lean` Bech32m encoder/decoder (`bech32mEncode` / `bech32mDecode`) |
| `SpInputScriptKind` | `Spec/SilentPayments.lean` | Connect via classifier `ScriptPubKey → SpInputScriptKind` from Track S1 `Spec/Script.lean` (`P2PKH`, `P2WPKH`, `P2SH`, `P2TR`, SegWit version extraction) |
| `WalletPolicySpec` | `Spec/AppStateMachine.lean` | Project from Track S2 `Spec/WalletPolicy.lean` (`WalletPolicy`, `walletId` SHA-256 registration ID, `keysInfo` Merkle root, `isDefaultPolicy`) |
| `PsbtSignRequest Affine`, `PsbtSpTx` | `Spec/AppStateMachine.lean`, `Spec/SilentPayments.lean` | Project from Track S3 `Spec/Psbt.lean` + `Spec/Signing.lean` validated PSBT view (input/output totals, change classification, BIP-375 fields, `MusigSignTask` extraction) |
| `BolosApduHeader` / `UnexpectedContinue` | `Spec/AppStateMachine.lean` | Compose with Track S3 `Spec/MerkleProtocol.lean` (`CLA = 0xF8`, `INS = 0x01` host-interactivity yield loop inside multi-round APDU execution) |

---

## 3. Reference Discrepancies & Candidate Bugs (`app-bitcoin` vs `vanadium`)

During side-by-side inspection of `LedgerHQ/app-bitcoin` (`f010982d`) and `LedgerHQ/vanadium` (`ace8e969`), we identified **9 concrete behavioral discrepancies and edge cases**:

1. **[CandidateBug / ReferenceDiscrepancy] Vanadium omits the MuSig2 Round-2 self-pubnonce match check**:
   - **BOLOS (`app-bitcoin/src/handler/sign_psbt/musig_signing.c:514-519`)**: Recomputes `(secnonce, pubnonce)` from `rand_root` in Round 2 and verifies `memcmp(&pubnonce, &my_pubnonce, 66) == 0` against the device's `PSBT_IN_MUSIG2_PUB_NONCE` entry in the PSBT, aborting with `SW_INCORRECT_DATA` on mismatch.
   - **Vanadium (`vanadium/apps/bitcoin/app/src/handlers/musig_signing.rs:463-485`)**: Extracts `_my_pubnonce` solely to confirm Round-2 presence, then calls `musig_nonce_gen(..., &mut _pubnonce)` and **discards `_pubnonce` without comparing it to `_my_pubnonce`**. If a coordinator supplies a stale Round-1 PSBT after a Round-1 retry overwrote the single session slot, Vanadium emits an unaggregatable partial signature instead of rejecting early.
   - **Spec Choice**: `Spec/Musig2.lean` (`round2SignTask`) enforces `recomputedPubnonce == myPubnonce` and proves `round2SignTask_rejects_mismatched_self_pubnonce`.

2. **[ReferenceDiscrepancy] MuSig2 `psbt_session_id` preimage & transaction binding**:
   - **BOLOS (`musig_signing.c:55-75`, `doc/musig.md`)**: Hashes `descriptor_template_sha256 || keys_info_merkle_root || u8(len) || musig2_session_id` (excludes wallet `name`, supports proprietary `PSBT_GLOBAL_MUSIG2_SESSION_ID` up to 32 bytes, and is intentionally **transaction-independent** so Round 1 can run before inputs/outputs are finalized).
   - **Vanadium (`musig_signing.rs:314-319`, `signing.rs:200-201`)**: Hashes `wallet_id || unsigned_tx_id` (commits to wallet `name` via `wallet_id`, binds Round 1 to a fixed unsigned transaction, and ignores `PSBT_GLOBAL_MUSIG2_SESSION_ID`).
   - **Spec Choice**: Both derivations are specified explicitly (`computeBolosPsbtSessionId` and `computeVanadiumPsbtSessionId`).

3. **[ReferenceDiscrepancy] `aggpk` passed to BIP-327 `NonceGen` (`untweaked` vs `tweaked`)**:
   - **BOLOS (`musig_signing.c:230-236`)**: Passes the **untweaked** compressed aggregate pubkey `aggpk_compressed` into `musig_nonce_gen`.
   - **Vanadium (`musig_signing.rs:424-429, 481-485`)**: Passes the **post-tweaked** compressed aggregate pubkey (`tweaked_keyagg_ctx.q().to_encoded_point(true)`) into `musig_nonce_gen`. Both are valid under BIP-327 (since `aggpk` is auxiliary randomness hardening), but they produce distinct deterministic nonces for identical `(rand_root, i, j)` inputs!
   - **Spec Choice**: Parameterized cleanly via `NonceAggPkMode` (`.untweakedBolos` vs `.tweakedVanadium`).

4. **[ReferenceDiscrepancy] MuSig2 session capacity & duplicate internal keys per `musig()`**:
   - **BOLOS (`musig_sessions.h:13`, `register_wallet.c:385`)**: Maintains `MAX_N_MUSIG_SESSIONS = 32` persistent NVRAM slots (`28B id_prefix + 4B LRU + 32B rand_root`) + 1 volatile Round-1 staging slot, and forbids multiple internal keys inside the same `musig(...)` placeholder.
   - **Vanadium (`musig_signing.rs:51-76`, `common/src/policy/musig.rs:89`)**: Stores only **1** 64-byte NVRAM slot (`32B id + 32B rand_root`) and loops over multiple internal keys in a single `musig(...)` expression.

5. **[ReferenceDiscrepancy] `GetExtendedPubkey` silent export path policy & path length limits**:
   - **BOLOS (`get_extended_pubkey.c:36-143`, `constants.h:35`)**: Restricts `path.length ≤ 10` (`MAX_BIP32_PATH_STEPS`) and rejects `display == false` unless `is_path_safe_for_pubkey_export` holds (BIP-44/45/48/49/84/86/87 with `account ≤ 100` or Electrum `m/4541509'/1112098098'`).
   - **Vanadium (`get_extended_pubkey.rs:138-145`)**: Allows `path.length ≤ 256`, supports `KeyTree::{Standard, Resident}` and `identity_index` signatures, and imposes no path whitelist when `display == false`.

6. **[ReferenceDiscrepancy] Default accounts vs mandatory Proof-of-Registration (PoR)**:
   - **BOLOS (`get_wallet_address.c`, `sign_psbt.c`)**: Permits stateless default single-key policies (`wallet_hmac` all-zero, `name == ""`, `address_index ≤ 50000`).
   - **Vanadium (`get_address.rs:86`, `sign_psbt/mod.rs`)**: Rejects empty PoRs with `Error::DefaultAccountsNotSupported`; every account (Wallet Policy or Silent Payment) must be registered first.

7. **[ReferenceDiscrepancy] `GetVersion` handling & APDU instruction classes**:
   - **BOLOS (`constants.h:15-20`, `dispatcher.c:140-143`, `bitcoin_client_rs/src/apdu.rs:19`)**: `GET_VERSION (0x01)` is served by BOLOS SDK (`CLA = 0xB0`) / `CLA = 0xE1`, whereas `CLA = 0xF8, INS = 0x01` is `INS_CONTINUE` (returning `SW_BAD_STATE = 0x6B00` if sent as a top-level command outside an interrupted client-interactivity call).
   - **Vanadium (`app/src/main.rs:26`, `common/src/message/mod.rs:31`)**: Declares `Request::GetVersion` (`#[n(0)]`) in the wire enum, but `handle_req` currently panics with `todo!()`.

8. **[Edge Case] Vanadium `KeyTree::Resident` lazy NVRAM initialization**:
   - **Vanadium (`app/src/resident_key.rs:21-40`)**: `get_or_init_resident_seed` lazily writes 32 CSPRNG bytes to NVRAM slot 0 on the first `KeyTree::Resident` call (`GetMasterFingerprint` or `GetExtendedPubkey`) if uninitialized.
   - **Spec Choice**: `Spec/AppStateMachine.lean` models `residentKeys : Option Bytes32` as provisioned at boot in `AppPersistentState` so read-only purity (`s' = s`) holds strictly on all read-only commands, recording the lazy-init implementation detail here for the Wave 2 refinement bridge.

9. **[Target-Exclusive Features & BIP-375 `k`-Ordering Ambiguity]**:
   - **Vanadium-only**: Silent Payments (`BIP-352`, `BIP-374`, `BIP-375`, `BIP-392` `ExportSpScanKey`), `RegisterIdentityKey`, `IdentitySignature`, and `KeyTree::Resident`. Note also `vanadium/apps/bitcoin/common/src/silent_payments/psbt.rs:22-26`: BIP-375 v0.1.2 prose specifies sorting recipient codes lexicographically per scan key to assign `k`, whereas the official BIP-375 test vectors assign `k` in **PSBT output order** (`assignK` follows the test-vector output order).
   - **BOLOS-only**: `SIGN_MESSAGE (0x10)`, BIP-322 PSBT message signing (`isBip322MessageSigning`), and Ledger Exchange `SwapLock` (`HAVE_SWAP`, standard & cross-chain `OP_RETURN` hash checks).

# Track S2 Spec Card & Integration Notes (`Spec/WalletPolicy.lean`)

**Track**: Wave 1 — `S2` (`wave1/spec-s2-wallet-policy`)
**Owned Specification**: `Spec/WalletPolicy.lean`
**Reference Commits Deduced**:
- `LedgerHQ/app-bitcoin` @ `f010982d3050e02813cd7129bebd68cf2d1f2099` (`doc/wallet.md`, `doc/musig.md`, `src/common/wallet.{h,c}`, `src/handler/lib/policy.{h,c}`, `src/handler/register_wallet.c`, `src/handler/get_wallet_address.c`)
- `LedgerHQ/vanadium` @ `ace8e96982408959dea9e7fbc59ee36e8c54e645` (`apps/bitcoin/common/src/{account.rs,taproot.rs,script.rs,por.rs,message/bip388_codec.rs}`, `apps/bitcoin/app/src/handlers/{register_account.rs,get_address.rs}`, and `bip388-0.1.2`)
- Underlying BIPs: BIP-32, BIP-44/49/84/86, BIP-68/112, BIP-327/328, BIP-340/341/342, BIP-379, BIP-380..386, BIP-388.

---

## 1. Specification Architecture Summary

`Spec/WalletPolicy.lean` specifies the complete, implementation-independent BIP-388 Wallet Policy & Miniscript domain in plain Lean 4 (`0 sorryAx`, `0 native_decide`, `#print axioms` ⊆ `{propext, Quot.sound}`):

1. **BIP-388 Domain Model (`PolicyFormat`, `KeyInformation`, `WalletPolicy`, `PolicyProfile`)**:
   - Models both legacy Ledger `v1` policies (`/**` attached to `KeyInformation` strings, bare `@i` in descriptor templates) and standard BIP-388 `v2` policies (no `/**` on `KeyInformation`, explicit `/**` or `/<M;N>/*` on every key expression).
   - Factors target policy bounds and feature flags cleanly via `PolicyProfile` with three explicit profiles: `canonicalLedgerProfile` (unified BIP-388 + BIP-379 soundness contract), `bolosAppProfile` (`app-bitcoin`), and `vanadiumAppProfile` (`vanadium` `apps/bitcoin`).
   - Enforces wallet name rules (`validWalletName`: `1..=64` printable ASCII `0x20..=0x7E`, no leading/trailing spaces), default stateless single-key accounts (`pkh`, `wpkh`, `sh(wpkh)`, `tr` with BIP-44/49/84/86 origins `m/purpose'/coin_type'/account'` for `account <= 100` and `addressIndex <= 50000`), and registered policy authorization (`DeviceRegistrationOracle` + `REGISTER_WALLET` user confirmation vs 32-byte non-zero HMAC / Proof-of-Registration).
2. **Descriptor & Miniscript AST, Total Parser & BIP-379 Sanity Analyzer**:
   - Top-level templates: `pkh`, `wpkh`, `sh(wpkh)`, `sh(multi)`/`sh(sortedmulti)`, `sh(wsh(...))`, `wsh(sortedmulti)`, `wsh(Miniscript)`, `tr(InternalKey)` (BIP-86), and `tr(InternalKey, TapTree)` (BIP-386) with `musig(@i_0,@i_1,...)` (BIP-328/388) in `v2` Taproot contexts.
   - Exact Ledger Miniscript fragment (`0`, `1`, `pk`, `pkh`, `pk_k`, `pk_h`, `older`, `after`, `sha256`, `hash256`, `ripemd160`, `hash160`, `andor`, `and_v`, `and_b`, `and_n`, `or_b`, `or_c`, `or_d`, `or_i`, `thresh`, `multi`, `multi_a`, and wrappers `a:`, `s:`, `c:`, `d:`, `v:`, `j:`, `n:`, `t:`, `l:`, `u:`).
   - Complete BIP-379 type & sanity system (`B/V/K/W` base types, `z/o/n/d/u` modifiers, `m` non-malleability, `s` top-level signature requirement, `g/h/i/j/k` timelock-mixing conflict detection, BIP-68 safe `older(n)` bitmask `1 <= (n & ~(1<<22)) <= 65535`, and P2WSH resource limits `scriptSize <= 3600`, `ops <= 201`, `stack <= 100`) plus BIP-388 placeholder coverage (`[0, nKeys)` referenced & sequential), `<M;N>` `M != N`, pairwise-disjoint multipaths on repeated `@k`, distinct pubkeys, and `hasOurKey` internal-key signability.
3. **Script Compilation, Taproot Commitments & `deriveWalletScriptPubKey`**:
   - Parameterized over `CryptoPolicyOracle`, specifies exact `scriptPubKey` derivation (`deriveWalletScriptPubKey`, `deriveWalletScriptPubKeyWithProfile`, `deriveAuthorizedWalletScriptPubKey`), including `v:` `OP_*VERIFY` fusion, lexicographic compressed/x-only key sorting for `sortedmulti` / `sortedmulti_a`, and BIP-341 `"TapLeaf"` (`0xC0 || compactSize(len) || script`), lexicographically ordered `"TapBranch"`, and `"TapTweak"` key tweaking, plus canonical BOLOS `walletId` and Vanadium `NAMED_ACCOUNT` PoR commitment preimages.
4. **Machine-Checked Theorems (`12` theorems, `0 sorryAx`, `0 native_decide`)**:
   - **Non-vacuity witnesses**: `nonvacuous_bip84_wpkh`, `nonvacuous_bip86_tr`, `nonvacuous_wsh_sortedmulti`, `nonvacuous_tapscript_tr_tree`.
   - **Security rejection & soundness**: `equal_multipath_keyexpr_rejected`, `equal_multipath_policy_rejected`, `out_of_range_placeholder_coverage_rejected`, `out_of_range_placeholder_policy_rejected`, `multi_tapscript_and_multi_a_wsh_rejected`, `registered_wallet_without_valid_hmac_rejected`, `receive_change_derivation_non_collision`, `registration_requires_our_key`.

---

## 2. Discovered Bugs & Reference Discrepancies (`app-bitcoin` vs `vanadium`)

### CandidateBug #1 (CRITICAL — Consensus / Spending Mismatch): Vanadium `Andor` Inverts `Y` and `Z` Branches
- **BOLOS (`app-bitcoin/src/handler/lib/policy.c:225-238`) & BIP-379**:
  `andor(X, Y, Z)` (semantics `(X && Y) || (!X && Z)`) compiles to:
  `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`
  (when `X` evaluates to `0`, `OP_NOTIF` executes the `Z` branch; when `X` evaluates to `1`, `OP_ELSE` executes the `Y` branch).
- **Vanadium (`apps/bitcoin/common/src/script.rs:367-373`)**:
  ```rust
  DescriptorTemplate::Andor(x, y, z) => Ok(Builder::new()
      .push_Expression(x, ctx)?
      .push_opcode(opcodes::all::OP_NOTIF)
      .push_Expression(y, ctx)?
      .push_opcode(opcodes::all::OP_ELSE)
      .push_Expression(z, ctx)?
      .push_opcode(opcodes::all::OP_ENDIF) ...
  ```
  Vanadium emits `[X] OP_NOTIF [Y] OP_ELSE [Z] OP_ENDIF`, **swapping the true and false branches**! Any wallet policy containing `andor` (though not `and_n(X,Y)` / `or_d(X,Z)` which have dedicated AST nodes in `bip388`) derives a completely different witnessScript / TapLeaf hash and consensus spending condition on Vanadium vs BOLOS / Bitcoin Core.
- **Spec Decision**: `Spec/WalletPolicy.lean` (`compileMiniscript` `.andor`) specifies the canonical BIP-379 / BOLOS compilation `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`.

### CandidateBug #2: Vanadium `sh(wsh(...))` Always Fails Script/Address Derivation
- **Vanadium (`bip388-0.1.2` + `apps/bitcoin/app/src/handlers/register_account.rs` vs `common/src/script.rs:145-170`)**:
  `bip388` parses `sh(wsh(...))` under `ParseContext::WrappedSegwit` and `register_account` successfully registers `sh(wsh(...))` accounts and returns a valid Proof of Registration. However, during script derivation (`DescriptorTemplate::to_script` in `common/src/script.rs`):
  - `DescriptorTemplate::Sh(inner)` checks `if ctx != ScriptContext::None && ctx != ScriptContext::Wsh` and recurses with `inner.to_script(..., ScriptContext::Sh, ...)`.
  - `DescriptorTemplate::Wsh(inner)` checks `if ctx != ScriptContext::None { return Err(Error::InvalidScriptContext); }`.
  Because `Sh` passes `ctx = ScriptContext::Sh` into `Wsh`, `ctx != ScriptContext::None` triggers unconditionally, causing **every `sh(wsh(...))` policy to fail with `Error::InvalidScriptContext`** in `get_address` and PSBT signing.
- **Spec Decision**: `Spec/WalletPolicy.lean` cleanly compiles `sh(wsh(inner))` by computing `witnessScript`, `wshRedeem = mkP2WSH(SHA256(witnessScript))`, and `mkP2SH(HASH160(wshRedeem))`.

### CandidateBug / Security Gap #3: Vanadium `bip388` (`0.1.2`) Omits Miniscript Type, Malleability & Timelock Sanity Checks
- **BOLOS (`wallet.c:get_miniscript_type_and_Limits` + `policy.c`)**: Enforces full BIP-379 `B/V/K/W` + `z/o/n/d/u` typechecking, `m` (non-malleable satisfaction), `s` (unconditional signature requirement), `k` (no height/timestamp timelock mixing on a single satisfaction branch), safe BIP-68 `older(n)` bitmasks (`(n & ~SEQUENCE_LOCKTIME_TYPE_FLAG) == (n & 0xFFFF)` and `>= 1`), and P2WSH script/ops/stack bounds (`3600` bytes, `201` ops, `100` stack elements).
- **Vanadium (`bip388-0.1.2/src/lib.rs:5`)**: Explicitly contains `// TODO: - add type checks - add malleability checks - add stack limits`, accepting ill-typed, malleable, signature-free (e.g., `wsh(1)` or `wsh(older(1))`), or timelock-mixed Miniscript policies, as well as `older(n)` values with consensus-meaningless upper bits set.
- **Spec Decision**: `Spec/WalletPolicy.lean` enforces the complete BIP-379 type, malleability (`m`), signature (`s`), timelock-mixing (`k`), safe BIP-68 `older`, and P2WSH resource invariants across all profiles.

### ReferenceDiscrepancy #4: Wallet Name Validation
- **BOLOS (`register_wallet.c:is_policy_name_acceptable`)**: Enforces `1 <= name.len <= 64`, printable ASCII `0x20..=0x7E`, and no leading or trailing `' '` (`0x20`).
- **Vanadium (`register_account.rs` / `account.rs`)**: Accepts any UTF-8 `String` without length, ASCII, or whitespace trimming checks (framing length via `encode_varint(name.len())` in `AccountCoordinates::id()`).
- **Spec Decision**: Canonical `validWalletName` enforces the strict BOLOS / BIP-388 printable-ASCII `1..=64` non-padded name contract (`Theorem` enforced at registration and PoR authorization).

### ReferenceDiscrepancy #5: Internal-Key (`hasOurKey`) & Signability Checks + Key Classification
- **BOLOS (`register_wallet.c:confirm_and_register_wallet`, `policy.c:check_policy_is_signable`)**:
  - Requires `n_internal_keys >= 1` (`== 1` in `v1`), `<= 1` internal key inside any single `musig(...)` expression, and `<= 8` internal key expressions (`MAX_INTERNAL_KEY_EXPRESSIONS = 8`).
  - Classifies a key as internal iff `origin` is present, `origin.fingerprint == master_fp`, and `derive(origin.path) == ki.xpub`.
- **Vanadium (`register_account.rs` / `account.rs`)**:
  - Does not reject `n_internal_keys == 0` or multiple internal keys in `musig(...)` at registration time.
  - Extends key origins with SLIP-21 `Resident` keys (`master_resident_key_fingerprint`) and optional cosigner identity pubkey labels (`KeyInformation.pubkey_label`).
- **Spec Decision**: `validatePolicyRegistration` enforces `hasOurKey` (`nInternal >= 1`, `== 1` in `v1`), `<= 1` internal key per `musig(...)`, and `<= profile.maxInternalKeyExpressions` (proved in `registration_requires_our_key`). Vanadium's Resident/Identity extensions can be layered onto `DeviceRegistrationOracle` in Track S4 (`Spec/AppStateMachine.lean`).

### ReferenceDiscrepancy #6: Policy Versions (`V1` vs `V2`), Default Stateless Policies & Registration Commitment
- **BOLOS**: Supports both `V1` (`POLICY_SYNTAX_LEDGER_LEGACY`, `version = 1`) and `V2` (`POLICY_SYNTAX_BIP388`, `version = 2`); permits stateless default policies (`name == ""`, `hmac == 0x00^32`, 1 internal key at `m/{44,49,84,86}'/coin_type'/account'` with `account <= 100` and `address_index <= 50000`); commits policies via Merkleized `wallet_header_t` (`walletId`) + SLIP-21 `"LEDGER-Wallet policy"` HMAC-SHA256.
- **Vanadium**: Supports only `V2` BIP-388 strings (`bip388_codec.rs`); rejects empty PoR (`Error::DefaultAccountsNotSupported` in `get_address.rs`); commits via `SHA256(0x0D || "NAMED_ACCOUNT" || varint(name.len) || name || WalletPolicy::encode)` + SLIP-21 `"Proof of Registration"` HMAC-SHA256.
- **Spec Decision**: `PolicyProfile.allowStatelessDefaultPolicies` cleanly toggles stateless default policies (`true` in `canonicalLedgerProfile` and `bolosAppProfile`, `false` in `vanadiumAppProfile`), and Section 5 specifies both commitment preimages (`bolosWalletPolicyHeaderPreimage` and `vanadiumNamedAccountPreimage`).

### ReferenceDiscrepancy #7: `sh(wsh(...))` Fragment Whitelist, `musig` in `sortedmulti_a`, Key Limits & Duplicate Check
| Aspect | BOLOS (`app-bitcoin`) | Vanadium (`apps/bitcoin` + `bip388`) | `PolicyProfile` Parameterization |
| :--- | :--- | :--- | :--- |
| `sh(wsh(...))` inner | Only `multi` / `sortedmulti` (`fragment_whitelist_sh_wsh`) | General `wsh` AST parsed (fails in `script.rs`, see Bug #2) | `allowGeneralMiniscriptInShWsh` (`false` BOLOS, `true` Canonical/Vanadium) |
| `musig(...)` in `sortedmulti_a` | Rejected (`allow_musig = false` in `TOKEN_SORTEDMULTI_A`) | Accepted (`KeyPlaceholder::parse` in Taproot) | `allowMusigInSortedmultiA` (`false` BOLOS, `true` Canonical/Vanadium) |
| Max policy keys | `15` (`MAX_N_KEYS_IN_WALLET_POLICY`, up to `38` with compile flag) | Unbounded `Vec` (`u32` varint) | `maxPolicyKeys` (`15` BOLOS, `38` Canonical, `999` Vanadium) |
| Max `multi` / `sh(multi)` / `multi_a` / `musig` | `16` / `15` / `999` / `5` | `20` / `20` / `999` / unbounded | `maxMultiKeys`, `maxP2shMultiKeys`, `maxMultiAKeys`, `maxMusigKeys` |
| Duplicate key check (`B3`) | Pairwise distinct 33-byte compressed pubkeys | Pairwise distinct 78-byte serialized xpubs | Canonical checks 33-byte compressed pubkeys (strictly stronger than 78-byte xpub equality) |
| `@k` sequential order | Checked as set coverage `{0..nKeys-1}` (`wallet.md` states sequential) | Checked as set coverage `{0..nKeys-1}` (`bip388`) | `requireSequentialPlaceholders` (`true` Canonical, `false` BOLOS/Vanadium) |

---

## 3. Wave 1 Coordinator Integration Map

Per the Wave 1 parallel independence rule, `Spec/WalletPolicy.lean` has **zero imports** and defines minimal local primitives in Section 0 / Section 5. At Wave 1 integration, unify as follows:

| Local Definition in `Spec/WalletPolicy.lean` | Target Unified Module | Integration Action |
| :--- | :--- | :--- |
| `Network`, `encodeU32LE`, `encodeU32BE`, `encodeCompactSize`, `lexByteListLt`, `lexBytesLt`, `insertSortedBytes`, `sortByteArraysLex` | `Spec/Basic.lean` (Track S1) | Alias or replace with `Spec.Basic` primitives |
| `hardenedBit`, `isUnhardened`, `hardened`, `maxOriginSteps`, `KeyOrigin`, `ExtendedPubKey` (`wellFormed`, `xOnlyPubkey`, `serialize78`) | `Spec/Bip32.lean` (Track S1) | Unify `KeyOrigin` & `ExtendedPubKey` with `Spec.Bip32` |
| `OP_*`, `pushScriptU32`, `pushSmallBytes`, `mkP2PKH`, `mkP2SH`, `mkP2WPKH`, `mkP2WSH`, `mkP2TR` | `Spec/Script.lean` (Track S1) | Unify `scriptPubKey` constructors & Bech32/Base58 address wrappers with `Spec.Script` |
| `CryptoPolicyOracle.musigKeyAgg` | `Spec/Musig2.lean` (Track S4) | Instantiate with BIP-327 `KeyAgg` + BIP-328 synthetic chaincode (`868087ca...`) |
| `bolosWalletPolicyHeaderPreimage` | `Spec/MerkleProtocol.lean` (Track S3) | Connect keys/descriptor Merkle roots in `wallet_header_t` (`walletId`) |
| `DeviceRegistrationOracle`, `validatePolicyRegistration`, `authorizePolicyUse`, `deriveAuthorizedWalletScriptPubKey` | `Spec/AppStateMachine.lean` (Track S4) | Plug into `REGISTER_WALLET`, `GET_WALLET_ADDRESS`, and `SIGN_PSBT` change/input verification |

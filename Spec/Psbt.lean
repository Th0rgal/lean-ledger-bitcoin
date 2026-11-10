/-
  Spec/Psbt.lean
  Canonical, implementation-independent formal specification for PSBT signing,
  input/output security invariants, fee & change verification, exact sighash
  digests (Legacy, BIP-143 SegWit v0, BIP-341/342 Taproot), BIP-322 virtual
  transaction validation, and Ledger Swap mode checks.

  Deduced from:
  - LedgerHQ/app-bitcoin (`f010982d3050e02813cd7129bebd68cf2d1f2099`)
  - LedgerHQ/vanadium `apps/bitcoin` (`ace8e96982408959dea9e7fbc59ee36e8c54e645`)
  - BIP-143, BIP-174, BIP-322, BIP-340, BIP-341, BIP-342, BIP-370, BIP-375, BIP-388.
-/

namespace Spec.Psbt

/-! ## 1. Self-Contained Primitive Domain Types & Encoding Helpers -/

/-- Exact 32-byte digest / identifier (`SHA-256`, `txid`, `tapleaf_hash`, etc.). -/
structure Bytes32 where
  bytes : ByteArray
  size_eq : bytes.size = 32
  deriving DecidableEq

instance : Repr Bytes32 where
  reprPrec h _ := repr h.bytes.data

def zeroBytes32 : Bytes32 :=
  { bytes := ByteArray.mk (Array.replicate 32 0)
    size_eq := by simp [ByteArray.size] }

instance : Inhabited Bytes32 := ⟨zeroBytes32⟩

/-- Abstract cryptographic hash suite passed explicitly (never axiomatized). -/
structure CryptoOracles where
  /-- Single SHA-256 digest over arbitrary byte strings. -/
  sha256 : ByteArray → Bytes32
  /-- RIPEMD-160(SHA-256(data)) producing a 20-byte digest. -/
  hash160 : ByteArray → ByteArray
  /-- Address formatter for scriptPubKeys on the active Bitcoin network (`None` if unformattable, e.g. `OP_RETURN`). -/
  formatAddress : ByteArray → Option String

/-- Double SHA-256 (`SHA256(SHA256(x))`). -/
def doubleSha256 (sha256 : ByteArray → Bytes32) (data : ByteArray) : Bytes32 :=
  sha256 (sha256 data).bytes

/-- BIP-340 / BIP-341 / BIP-322 tagged hash: `SHA256(SHA256(tag) || SHA256(tag) || msg)`. -/
def taggedHash (sha256 : ByteArray → Bytes32) (tag : String) (msg : ByteArray) : Bytes32 :=
  let tagHash := (sha256 tag.toUTF8).bytes
  sha256 (tagHash ++ tagHash ++ msg)

/-- Maximum valid Bitcoin amount in satoshis (`21,000,000 * 100,000,000`). -/
def MAX_MONEY : Nat := 2100000000000000

/-- Locktime threshold separating block height (`< 500,000,000`) from UNIX timestamp (`>= 500,000,000`). -/
def LOCKTIME_THRESHOLD : UInt32 := 500000000

/-- Maximum number of silent change outputs permitted in BOLOS (`MAX_CHANGE_OUTPUTS = 10`). -/
def MAX_CHANGE_OUTPUTS : Nat := 10

/-- Maximum confusion score permitted for cleartext signing (`CLEARTEXT_MAX_CONFUSION_SCORE = 100,000`). -/
def MAX_CLEARTEXT_CONFUSION_SCORE : Nat := 100000

/-- Maximum printable ASCII message length displayed directly in BIP-322 (`MAX_PRINTABLE_MESSAGE_LEN = 640`). -/
def MAX_BIP322_PRINTABLE_LEN : Nat := 640

/-- Little-endian 16-bit encoding. -/
def encodeU16LE (v : UInt16) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256)
  ]

/-- Little-endian 32-bit encoding. -/
def encodeU32LE (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256)
  ]

/-- Little-endian 64-bit encoding. -/
def encodeU64LE (v : UInt64) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 4294967296) % 256),
    UInt8.ofNat ((n / 1099511627776) % 256),
    UInt8.ofNat ((n / 281474976710656) % 256),
    UInt8.ofNat ((n / 72057594037927936) % 256)
  ]

/-- Bitcoin CompactSize (`varint`) encoding over `Nat`. -/
def encodeVarInt (n : Nat) : ByteArray :=
  if n < 0xFD then
    ByteArray.mk #[UInt8.ofNat n]
  else if n ≤ 0xFFFF then
    ByteArray.mk #[0xFD] ++ encodeU16LE (UInt16.ofNat n)
  else if n ≤ 0xFFFFFFFF then
    ByteArray.mk #[0xFE] ++ encodeU32LE (UInt32.ofNat n)
  else
    ByteArray.mk #[0xFF] ++ encodeU64LE (UInt64.ofNat n)

/-- Concatenate a list of `ByteArray`s. -/
def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl ByteArray.append ByteArray.empty

/-- Total, transparent byte lookup (`s.data[i]?`). -/
def byteAt? (s : ByteArray) (i : Nat) : Option UInt8 :=
  s.data[i]?

/-- Pure structural byte equality (`a.data.toList == b.data.toList`) that reduces transparently in the Lean kernel. -/
def bytesEq (a b : ByteArray) : Bool :=
  a.data.toList == b.data.toList

/-- Script template check: `OP_HASH160 (0xa9) <20 bytes> OP_EQUAL (0x87)`. -/
def mkP2SHScript (hash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[0xa9, 0x14] ++ hash20 ++ ByteArray.mk #[0x87]

/-- Script template check: `OP_0 (0x00) <20 bytes>`. -/
def isP2WPKHScript (s : ByteArray) : Bool :=
  s.data.size == 22 && byteAt? s 0 == some 0x00 && byteAt? s 1 == some 0x14

/-- Script template check: `OP_0 (0x00) <32 bytes>`. -/
def isP2WSHScript (s : ByteArray) : Bool :=
  s.data.size == 34 && byteAt? s 0 == some 0x00 && byteAt? s 1 == some 0x20

/-- Script template check: `OP_1 (0x51) <32 bytes>`. -/
def isP2TRScript (s : ByteArray) : Bool :=
  s.data.size == 34 && byteAt? s 0 == some 0x51 && byteAt? s 1 == some 0x20

/-- Construct `OP_0 (0x00) <32-byte sha256(witnessScript)>`. -/
def mkP2WSHScript (hash32 : Bytes32) : ByteArray :=
  ByteArray.mk #[0x00, 0x20] ++ hash32.bytes

/-! ## 2. Bitcoin Raw Transactions, Derivation Metadata, and Wallet Policy Interface -/

/-- Spend witness version classification for an input or wallet policy. -/
inductive SpendClass where
  | legacy
  | segwitV0
  | taprootV1
  deriving Repr, DecidableEq, Inhabited

/-- Transaction outpoint (`txid`, `vout`). -/
structure OutPoint where
  txid : Bytes32
  vout : UInt32
  deriving Repr, DecidableEq, Inhabited

/-- Transaction output (`value` in satoshis, `scriptPubKey`). -/
structure TxOut where
  amount : Nat
  scriptPubKey : ByteArray
  deriving DecidableEq, Inhabited

/-- Unsigned/raw transaction input (for `PSBT_GLOBAL_UNSIGNED_TX` and `nonWitnessUtxo`). -/
structure RawTxIn where
  prevout : OutPoint
  scriptSig : ByteArray
  sequence : UInt32
  witness : Array ByteArray := #[]
  deriving DecidableEq, Inhabited

/-- Raw Bitcoin transaction (used in `PSBT_IN_NON_WITNESS_UTXO` and PSBTv0 `UNSIGNED_TX`). -/
structure RawTx where
  version : UInt32
  vin : Array RawTxIn
  vout : Array TxOut
  locktime : UInt32
  deriving DecidableEq, Inhabited

def serializeOutPoint (op : OutPoint) : ByteArray :=
  op.txid.bytes ++ encodeU32LE op.vout

def serializeTxOut (o : TxOut) : ByteArray :=
  encodeU64LE (UInt64.ofNat o.amount) ++ encodeVarInt o.scriptPubKey.size ++ o.scriptPubKey

def serializeRawTxInNoWitness (inp : RawTxIn) : ByteArray :=
  serializeOutPoint inp.prevout ++
  encodeVarInt inp.scriptSig.size ++
  inp.scriptSig ++
  encodeU32LE inp.sequence

/-- Legacy (non-witness) Bitcoin transaction serialization, whose `doubleSha256` defines `txid`. -/
def serializeRawTxNoWitness (tx : RawTx) : ByteArray :=
  encodeU32LE tx.version ++
  encodeVarInt tx.vin.size ++
  concatBytes (tx.vin.toList.map serializeRawTxInNoWitness) ++
  encodeVarInt tx.vout.size ++
  concatBytes (tx.vout.toList.map serializeTxOut) ++
  encodeU32LE tx.locktime

/-- Transaction identifier (`txid`) = `doubleSha256` of non-witness serialization (BIP-141). -/
def computeTxid (sha256 : ByteArray → Bytes32) (tx : RawTx) : Bytes32 :=
  doubleSha256 sha256 (serializeRawTxNoWitness tx)

/-- BIP-32 key origin (`masterFingerprint` + `derivationPath` steps). -/
structure KeyOrigin where
  fingerprint : UInt32
  path : List UInt32
  deriving Repr, DecidableEq, Inhabited

/-- PSBT BIP-32 / Taproot BIP-32 key derivation entry (`pubkey -> (fingerprint, path, leafHashes)`). -/
structure KeyDerivationEntry where
  pubkey : ByteArray
  origin : KeyOrigin
  leafHashes : List Bytes32 := []
  deriving DecidableEq, Inhabited

/-- Internal key placeholder inside a BIP-388 wallet policy (`@i/**` or `musig(...)/**`). -/
structure InternalKeyPlaceholder where
  keyIndex : Nat
  /-- Expected origin fingerprint & prefix path (`[]` for aggregate `musig(...)` root). -/
  expectedOrigin : Option KeyOrigin
  /-- Receive branch child index (typically `0`). -/
  numFirst : UInt32
  /-- Change branch child index (typically `1`). -/
  numSecond : UInt32
  isMusig : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Abstract BIP-388 wallet policy contract (to be unified with `Spec.WalletPolicy` in Wave 1.5). -/
structure WalletPolicySpec where
  /-- Whether this is a standard single-key default policy (requiring no registration HMAC). -/
  isDefault : Bool
  /-- Policy name (must be empty `""` when `isDefault = true`). -/
  name : String
  /-- Spend class of scripts produced by this policy. -/
  spendClass : SpendClass
  /-- Device-owned key placeholders (`st->account.internal_key_expressions`; must be non-empty). -/
  internalPlaceholders : List InternalKeyPlaceholder
  /-- Deterministically derives `(scriptPubKey, optionalRedeemScript, optionalWitnessScript)` at `(isChange, addressIndex)`. -/
  deriveScripts : Bool → UInt32 → Option (ByteArray × Option ByteArray × Option ByteArray)

/-! ## 3. PSBTv2 Logical Model & PSBTv0-to-PSBTv2 Normalization (BIP-174 / BIP-370) -/

/-- BIP-375 Silent Payment output recipient metadata (`PSBT_OUT_SP_V0_INFO` + optional label). -/
structure SilentPaymentOutputInfo where
  scanKey : ByteArray
  spendKey : ByteArray
  label : Option UInt32 := none
  deriving DecidableEq, Inhabited

/-- Logical PSBT input (PSBTv2 representation). -/
structure PsbtInput where
  prevout : OutPoint
  /-- Optional `PSBT_IN_SEQUENCE`; defaults to `0xFFFFFFFF` when absent per BIP-370. -/
  sequence : Option UInt32 := none
  /-- `PSBT_IN_REQUIRED_TIME_LOCKTIME` (`0x10`). -/
  requiredTimeLocktime : Option UInt32 := none
  /-- `PSBT_IN_REQUIRED_HEIGHT_LOCKTIME` (`0x11`). -/
  requiredHeightLocktime : Option UInt32 := none
  /-- `PSBT_IN_NON_WITNESS_UTXO` (`0x00`): full previous transaction. -/
  nonWitnessUtxo : Option RawTx := none
  /-- `PSBT_IN_WITNESS_UTXO` (`0x01`): spent output `(amount, scriptPubKey)`. -/
  witnessUtxo : Option TxOut := none
  /-- `PSBT_IN_SIGHASH_TYPE` (`0x03`). -/
  sighashType : Option UInt32 := none
  /-- `PSBT_IN_REDEEM_SCRIPT` (`0x04`). -/
  redeemScript : Option ByteArray := none
  /-- `PSBT_IN_WITNESS_SCRIPT` (`0x05`). -/
  witnessScript : Option ByteArray := none
  /-- `PSBT_IN_BIP32_DERIVATION` (`0x06`) and `PSBT_IN_TAP_BIP32_DERIVATION` (`0x16`). -/
  derivations : List KeyDerivationEntry := []
  /-- `PSBT_IN_TAP_INTERNAL_KEY` (`0x17`). -/
  tapInternalKey : Option ByteArray := none
  /-- `PSBT_IN_TAP_MERKLE_ROOT` (`0x18`). -/
  tapMerkleRoot : Option Bytes32 := none
  /-- Optional cleartext witness stack unlocking elements (`PSBT_LEDGER_IN_UNLOCKING_*`). -/
  cleartextConfusionScore : Nat := 0
  /-- MuSig2 pubnonces present on this input (`PSBT_IN_MUSIG2_PUB_NONCE`). -/
  hasMusig2PubNonces : Bool := false
  /-- Per-input BIP-375 ECDH shares / DLEQ proofs present. -/
  hasInputSpSharesOrProofs : Bool := false
  deriving DecidableEq, Inhabited

/-- Effective `nSequence` of a PSBTv2 input (`0xFFFFFFFF` when `PSBT_IN_SEQUENCE` is absent). -/
def PsbtInput.effectiveSequence (inp : PsbtInput) : UInt32 :=
  inp.sequence.getD 0xFFFFFFFF

/-- Logical PSBT output (PSBTv2 representation). -/
structure PsbtOutput where
  amount : Nat
  /-- `PSBT_OUT_SCRIPT` (`0x03`). Mandatory except for unfinalized BIP-375 silent payment outputs. -/
  scriptPubKey : Option ByteArray
  /-- `PSBT_OUT_REDEEM_SCRIPT` (`0x00`). -/
  redeemScript : Option ByteArray := none
  /-- `PSBT_OUT_WITNESS_SCRIPT` (`0x01`). -/
  witnessScript : Option ByteArray := none
  /-- `PSBT_OUT_BIP32_DERIVATION` (`0x02`) and `PSBT_OUT_TAP_BIP32_DERIVATION` (`0x07`). -/
  derivations : List KeyDerivationEntry := []
  /-- `PSBT_OUT_TAP_INTERNAL_KEY` (`0x05`). -/
  tapInternalKey : Option ByteArray := none
  /-- `PSBT_OUT_SP_V0_INFO` (`0x09`) / `PSBT_OUT_SP_V0_LABEL` (`0x0a`). -/
  silentPayment : Option SilentPaymentOutputInfo := none
  deriving DecidableEq, Inhabited

/-- Logical PSBTv2 transaction (`Spec/Psbt.lean` canonical model). -/
structure PsbtTx where
  txVersion : UInt32
  fallbackLocktime : Option UInt32 := none
  txModifiableFlags : Option UInt8 := none
  inputs : Array PsbtInput
  outputs : Array PsbtOutput
  /-- `PSBT_GLOBAL_GENERIC_SIGNED_MESSAGE` (`0x09` in BOLOS BIP-322 PSBT extension). -/
  bip322Message : Option ByteArray := none
  /-- Proprietary `PSBT_GLOBAL_MUSIG2_SESSION_ID` if present. -/
  musig2SessionId : Option Bytes32 := none
  deriving DecidableEq, Inhabited

/-- Raw PSBTv0 input before BIP-370 normalization. -/
structure PsbtV0Input where
  nonWitnessUtxo : Option RawTx := none
  witnessUtxo : Option TxOut := none
  sighashType : Option UInt32 := none
  redeemScript : Option ByteArray := none
  witnessScript : Option ByteArray := none
  derivations : List KeyDerivationEntry := []
  tapInternalKey : Option ByteArray := none
  tapMerkleRoot : Option Bytes32 := none
  requiredTimeLocktime : Option UInt32 := none
  requiredHeightLocktime : Option UInt32 := none
  /-- Any v2-only input field (`PREVIOUS_TXID`, `OUTPUT_INDEX`, `SEQUENCE`) present in a v0 map is invalid! -/
  hasV2ExclusiveFields : Bool := false
  deriving DecidableEq, Inhabited

/-- Raw PSBTv0 output before BIP-370 normalization. -/
structure PsbtV0Output where
  redeemScript : Option ByteArray := none
  witnessScript : Option ByteArray := none
  derivations : List KeyDerivationEntry := []
  tapInternalKey : Option ByteArray := none
  /-- Any v2-only output field (`AMOUNT`, `SCRIPT`) present in a v0 map is invalid! -/
  hasV2ExclusiveFields : Bool := false
  deriving DecidableEq, Inhabited

/-- Raw PSBTv0 container (`PSBT_GLOBAL_VERSION` absent or `0`, with mandatory `UNSIGNED_TX`). -/
structure PsbtV0 where
  version : Option UInt32 := none
  unsignedTx : RawTx
  /-- True if `UNSIGNED_TX` was serialized with SegWit witness marker (forbidden by BIP-174). -/
  unsignedTxHasWitness : Bool := false
  /-- True if any PSBTv2-exclusive global field (`TX_VERSION`, `FALLBACK_LOCKTIME`, `INPUT_COUNT`, `OUTPUT_COUNT`, `TX_MODIFIABLE`) is present. -/
  hasV2ExclusiveGlobals : Bool := false
  inputs : Array PsbtV0Input
  outputs : Array PsbtV0Output
  bip322Message : Option ByteArray := none
  musig2SessionId : Option Bytes32 := none
  deriving DecidableEq, Inhabited

/-- Canonical PSBT validation and signing rejection taxonomy. -/
inductive PsbtError where
  | invalidPsbtVersion
  | psbtV0HasWitnessInUnsignedTx
  | psbtV0NonEmptyScriptSig
  | psbtV0ForbiddenV2Fields
  | psbtV0InputOutputCountMismatch
  | emptyInputsOrOutputs
  | invalidWalletPolicy
  | noInternalInputs
  | externalInputsNotAllowed
  | locktimeConflictOrInvalid
  | missingUtxo
  | legacyHasWitnessUtxo
  | nonWitnessUtxoTxidMismatch
  | prevoutIndexOutOfBounds
  | dualUtxoMismatch
  | redeemScriptMismatch
  | missingOrMismatchedWitnessScript
  | unsupportedSighashType
  | nonDefaultSighashDisallowed
  | sighashSingleIndexOutOfBounds
  | missingOutputScript
  | amountExceedsMaxSupply
  | negativeFeeOutputsExceedInputs
  | tooManyChangeOutputs
  | invalidOpReturnScript
  | cleartextConfusionScoreExceeded
  | bip322ForbiddenInSwap
  | bip322InvalidStructure
  | bip322ChallengeTxidMismatch
  | bip322InvalidSequence
  | swapPolicyOrWarningViolation
  | swapOutputCountMismatch
  | swapInvalidCrossChainPayin
  | swapFeeMismatch
  | swapAmountMismatch
  | swapDestinationMismatch
  deriving Repr, DecidableEq, Inhabited

/-- Normalize a BIP-174 PSBTv0 into a canonical BIP-370 `PsbtTx` (PSBTv2), enforcing all BIP-174/370 invariants
    (`vanadium/apps/bitcoin/common/src/psbt/v2.rs`). -/
def normalizePsbtV0ToV2 (v0 : PsbtV0) : Except PsbtError PsbtTx :=
  let versionOk : Bool := match v0.version with
    | some ver => ver == 0
    | none => true
  if !versionOk then
    .error .invalidPsbtVersion
  else if v0.unsignedTxHasWitness then
    .error .psbtV0HasWitnessInUnsignedTx
  else if v0.hasV2ExclusiveGlobals then
    .error .psbtV0ForbiddenV2Fields
  else if v0.unsignedTx.vin.toList.any (fun txin => txin.scriptSig.size != 0 || txin.witness.size != 0) then
    .error .psbtV0NonEmptyScriptSig
  else if hInSz : v0.inputs.size = v0.unsignedTx.vin.size then
    if hOutSz : v0.outputs.size = v0.unsignedTx.vout.size then
      if v0.inputs.toList.any (·.hasV2ExclusiveFields) || v0.outputs.toList.any (·.hasV2ExclusiveFields) then
        .error .psbtV0ForbiddenV2Fields
      else
        let v2Inputs := Array.ofFn (n := v0.inputs.size) fun ⟨i, hi⟩ =>
          let rawIn := v0.unsignedTx.vin[i]'(hInSz ▸ hi)
          let mIn := v0.inputs[i]'hi
          { prevout := rawIn.prevout
            sequence := some rawIn.sequence
            requiredTimeLocktime := mIn.requiredTimeLocktime
            requiredHeightLocktime := mIn.requiredHeightLocktime
            nonWitnessUtxo := mIn.nonWitnessUtxo
            witnessUtxo := mIn.witnessUtxo
            sighashType := mIn.sighashType
            redeemScript := mIn.redeemScript
            witnessScript := mIn.witnessScript
            derivations := mIn.derivations
            tapInternalKey := mIn.tapInternalKey
            tapMerkleRoot := mIn.tapMerkleRoot }
        let v2Outputs := Array.ofFn (n := v0.outputs.size) fun ⟨i, hi⟩ =>
          let rawOut := v0.unsignedTx.vout[i]'(hOutSz ▸ hi)
          let mOut := v0.outputs[i]'hi
          { amount := rawOut.amount
            scriptPubKey := some rawOut.scriptPubKey
            redeemScript := mOut.redeemScript
            witnessScript := mOut.witnessScript
            derivations := mOut.derivations
            tapInternalKey := mOut.tapInternalKey }
        .ok {
          txVersion := v0.unsignedTx.version
          fallbackLocktime := some v0.unsignedTx.locktime
          txModifiableFlags := none
          inputs := v2Inputs
          outputs := v2Outputs
          bip322Message := v0.bip322Message
          musig2SessionId := v0.musig2SessionId
        }
    else
      .error .psbtV0InputOutputCountMismatch
  else
    .error .psbtV0InputOutputCountMismatch

/-! ## 4. BIP-370 Locktime Determination (`app-bitcoin/src/common/locktime.h`) -/

/-- Validate optional per-input required height (`0 < h < 500_000_000`) and time (`t >= 500_000_000`). -/
def validateInputLocktimeFields (inp : PsbtInput) : Bool :=
  let heightOk := match inp.requiredHeightLocktime with
    | none => true
    | some h => decide (0 < h.toNat ∧ h.toNat < LOCKTIME_THRESHOLD.toNat)
  let timeOk := match inp.requiredTimeLocktime with
    | none => true
    | some t => decide (LOCKTIME_THRESHOLD.toNat ≤ t.toNat)
  heightOk && timeOk

/-- Exact BIP-370 locktime determination (`locktime_determine` in `app-bitcoin/src/common/locktime.h`):
    - Every input's `requiredHeightLocktime` (if present) must be in `[1, 499_999_999]`.
    - Every input's `requiredTimeLocktime` (if present) must be `>= 500_000_000`.
    - An input declaring BOTH height and time accepts EITHER type; a conflict occurs iff at least
      one input requires ONLY height and at least one input requires ONLY time.
    - When both types satisfy all inputs and at least one constraint exists, height wins as tie-breaker.
    - `fallbackLocktime` (default `0`) is used ONLY when NO input specifies any required locktime! -/
def determineLocktime (fallbackLocktime : Option UInt32) (inputs : List PsbtInput) :
    Except PsbtError UInt32 :=
  if !(inputs.all validateInputLocktimeFields) then
    .error .locktimeConflictOrInvalid
  else
    let hasHeightOnly := inputs.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone)
    let hasTimeOnly   := inputs.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone)
    if hasHeightOnly && hasTimeOnly then
      .error .locktimeConflictOrInvalid
    else
      let maxHeight := inputs.foldl (fun acc i =>
        match i.requiredHeightLocktime with
        | some h => if acc < h.toNat then h.toNat else acc
        | none   => acc) 0
      let maxTime := inputs.foldl (fun acc i =>
        match i.requiredTimeLocktime with
        | some t => if acc < t.toNat then t.toNat else acc
        | none   => acc) 0
      let anyHeight := inputs.any (fun i => i.requiredHeightLocktime.isSome)
      let anyTime   := inputs.any (fun i => i.requiredTimeLocktime.isSome)
      if !anyHeight && !anyTime then
        .ok (fallbackLocktime.getD 0)
      else if !hasTimeOnly && anyHeight then
        .ok (UInt32.ofNat maxHeight)
      else
        .ok (UInt32.ofNat maxTime)

/-! ## 5. Sighash Policy Classification (`app-bitcoin/src/common/sighash.h`) -/

def SIGHASH_DEFAULT      : UInt8 := 0x00
def SIGHASH_ALL          : UInt8 := 0x01
def SIGHASH_NONE         : UInt8 := 0x02
def SIGHASH_SINGLE       : UInt8 := 0x03
def SIGHASH_ANYONECANPAY : UInt8 := 0x80

inductive SighashSafety where
  | safe
  | nonSafe
  | unsupported
  deriving Repr, DecidableEq, Inhabited

/-- Classify a raw `PSBT_IN_SIGHASH_TYPE` `UInt32` for a given `SpendClass`
    (`sighash_classify` in `app-bitcoin/src/common/sighash.h`):
    - Rejects high bits (`raw > 0xFF`).
    - `0x00` (`SIGHASH_DEFAULT`) is `.safe` ONLY for Taproot (`taprootV1`), `.unsupported` otherwise.
    - `0x01` (`SIGHASH_ALL`) is `.safe` for all spend classes.
    - `{0x02, 0x03, 0x81, 0x82, 0x83}` are `.nonSafe` for SegWit v0 & Taproot v1, and `.unsupported` for Legacy. -/
def classifySighash (sc : SpendClass) (rawOpt : Option UInt32) : SighashSafety × UInt8 :=
  match rawOpt with
  | none =>
      match sc with
      | .taprootV1 => (.safe, SIGHASH_DEFAULT)
      | .legacy | .segwitV0 => (.safe, SIGHASH_ALL)
  | some raw =>
      if raw.toNat > 0xFF then
        (.unsupported, 0)
      else
        let b := UInt8.ofNat raw.toNat
        if b == SIGHASH_DEFAULT then
          match sc with
          | .taprootV1 => (.safe, b)
          | _ => (.unsupported, b)
        else if b == SIGHASH_ALL then
          (.safe, b)
        else if b == SIGHASH_NONE || b == SIGHASH_SINGLE ||
                b == (SIGHASH_ANYONECANPAY ||| SIGHASH_ALL) ||
                b == (SIGHASH_ANYONECANPAY ||| SIGHASH_NONE) ||
                b == (SIGHASH_ANYONECANPAY ||| SIGHASH_SINGLE) then
          match sc with
          | .legacy => (.unsupported, b)
          | .segwitV0 | .taprootV1 => (.nonSafe, b)
        else
          (.unsupported, b)

/-- Whether a sighash byte leaves the input set open (`ANYONECANPAY`). -/
def sighashOpensInputs (b : UInt8) : Bool :=
  (b &&& SIGHASH_ANYONECANPAY) != 0

/-- Whether a sighash byte fails to commit to ALL outputs (`NONE` or `SINGLE`). -/
def sighashOpensOutputs (b : UInt8) : Bool :=
  let base := b &&& 0x1f
  base == SIGHASH_NONE || base == SIGHASH_SINGLE

/-- Whether a sighash byte has `SIGHASH_SINGLE` base type (`0x03`). -/
def sighashIsSingle (b : UInt8) : Bool :=
  (b &&& 0x1f) == SIGHASH_SINGLE

/-! ## 6. Input UTXO Security Invariants & CVE-2020-14199 Defenses -/

/-- Validated UTXO prevout extracted for an input, plus whether a SegWit v0 `nonWitnessUtxo` was omitted. -/
structure ValidatedInputUtxo where
  prevoutTxOut : TxOut
  spendClass : SpendClass
  missingNonWitnessUtxoWarning : Bool
  deriving DecidableEq, Inhabited

/-- Determine the spend class of a prevout `scriptPubKey` (unwrapping P2SH `redeemScript` if present). -/
def detectInputSpendClass (scriptPubKey : ByteArray) (redeemScript : Option ByteArray) : SpendClass :=
  let inner := redeemScript.getD scriptPubKey
  if isP2WPKHScript inner || isP2WSHScript inner then
    .segwitV0
  else if redeemScript.isNone && isP2TRScript scriptPubKey then
    .taprootV1
  else
    .legacy

/-- Core UTXO commitment check (`preprocess_inputs.c`, `amount_from_psbt.c`, `sign_input.c`, and `vanadium`):
    1. Legacy inputs (`witnessUtxo = none`, or legacy script):
       - MUST provide `nonWitnessUtxo` whose `computeTxid == prevout.txid` and `prevout.vout < vout.size`.
       - MUST NOT provide `witnessUtxo` (prevents signing legacy tx while trusting unverified witnessUtxo).
       - Prevout `(amount, scriptPubKey)` is extracted directly from `nonWitnessUtxo.vout[prevout.vout]`.
    2. SegWit v0 & Taproot v1 inputs:
       - MUST provide `witnessUtxo`.
       - If `nonWitnessUtxo` is ALSO provided, `computeTxid == prevout.txid` AND
         `nonWitnessUtxo.vout[prevout.vout] == witnessUtxo` (both `amount` and `scriptPubKey` MUST match!).
       - SegWit v0 without `nonWitnessUtxo` raises `missingNonWitnessUtxoWarning` (CVE-2020-14199 defense).
    3. Amount bound: `prevout.amount <= MAX_MONEY`.
    4. Wrapped script commitments:
       - If `redeemScript` is present: `mkP2SHScript (hash160 rs) == prevout.scriptPubKey`.
       - If spending P2WSH (native or P2SH-wrapped): `witnessScript` MUST be present and
         `mkP2WSHScript (sha256 ws) == activeScript`. -/
def extractInputPrevout (sha256 : ByteArray → Bytes32) (inp : PsbtInput) :
    Except PsbtError (TxOut × Bool) :=
  match inp.nonWitnessUtxo, inp.witnessUtxo with
  | none, none =>
      .error .missingUtxo
  | some rawTx, none =>
      if computeTxid sha256 rawTx != inp.prevout.txid then
        .error .nonWitnessUtxoTxidMismatch
      else
        let idx := inp.prevout.vout.toNat
        if h : idx < rawTx.vout.size then
          .ok (rawTx.vout[idx]'h, true)
        else
          .error .prevoutIndexOutOfBounds
  | none, some wUtxo =>
      .ok (wUtxo, false)
  | some rawTx, some wUtxo =>
      if computeTxid sha256 rawTx != inp.prevout.txid then
        .error .nonWitnessUtxoTxidMismatch
      else
        let idx := inp.prevout.vout.toNat
        if h : idx < rawTx.vout.size then
          let nwOut := rawTx.vout[idx]'h
          if nwOut != wUtxo then
            .error .dualUtxoMismatch
          else
            .ok (wUtxo, true)
        else
          .error .prevoutIndexOutOfBounds

def validateInputUtxo
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (exemptMissingNonWitnessWarning : Bool := false) : Except PsbtError ValidatedInputUtxo :=
  match extractInputPrevout crypto.sha256 inp with
  | .error e => .error e
  | .ok (txOut, hasNonWitness) =>
      let redeemOk : Bool := match inp.redeemScript with
        | some rs => mkP2SHScript (crypto.hash160 rs) == txOut.scriptPubKey
        | none => true
      if !redeemOk then
        .error .redeemScriptMismatch
      else
        let sc := detectInputSpendClass txOut.scriptPubKey inp.redeemScript
        if sc == .legacy && inp.witnessUtxo.isSome then
          .error .legacyHasWitnessUtxo
        else if sc == .legacy && !hasNonWitness then
          .error .missingUtxo
        else if sc != .legacy && inp.witnessUtxo.isNone then
          .error .missingUtxo
        else
          let activeScript := inp.redeemScript.getD txOut.scriptPubKey
          let witnessOk : Bool :=
            if isP2WSHScript activeScript then
              match inp.witnessScript with
              | none => false
              | some ws => mkP2WSHScript (crypto.sha256 ws) == activeScript
            else
              true
          if !witnessOk then
            .error .missingOrMismatchedWitnessScript
          else if txOut.amount > MAX_MONEY then
            .error .amountExceedsMaxSupply
          else
            let warnMissingNw := (sc == .segwitV0) && (!hasNonWitness) && (!exemptMissingNonWitnessWarning)
            .ok {
              prevoutTxOut := txOut
              spendClass := sc
              missingNonWitnessUtxoWarning := warnMissingNw
            }

/-! ## 7. Wallet Policy Derivation Matching: Internal Inputs & Verified Change Outputs -/

/-- Check whether a key derivation entry matches an `InternalKeyPlaceholder` at `(isChange, addressIndex)`. -/
def derivationMatchesPlaceholder
    (ph : InternalKeyPlaceholder)
    (entry : KeyDerivationEntry) : Option (Bool × UInt32) :=
  let branchStep? : Option (UInt32 × UInt32) :=
    match ph.expectedOrigin with
    | none =>
        if ph.isMusig && entry.origin.fingerprint == 0 then
          match entry.origin.path with
          | [c, idx] => some (c, idx)
          | _ => none
        else
          none
    | some orig =>
        if entry.origin.fingerprint == orig.fingerprint &&
           entry.origin.path.take orig.path.length == orig.path &&
           entry.origin.path.length == orig.path.length + 2 then
          match entry.origin.path.drop orig.path.length with
          | [c, idx] => some (c, idx)
          | _ => none
        else
          none
  match branchStep? with
  | none => none
  | some (c, addrIdx) =>
      if ph.numFirst == ph.numSecond then
        none
      else if c == ph.numFirst then
        some (false, addrIdx)
      else if c == ph.numSecond then
        some (true, addrIdx)
      else
        none

/-- Find matching `(isChange, addressIndex)` coordinates against any internal placeholder of `policy`. -/
def findMatchingCoordinates
    (policy : WalletPolicySpec)
    (derivations : List KeyDerivationEntry) : Option (Bool × UInt32) :=
  derivations.findSome? fun entry =>
    policy.internalPlaceholders.findSome? fun ph =>
      derivationMatchesPlaceholder ph entry

/-- An input is **internal** (`isInternalInput`) iff:
    1. Its PSBT derivation metadata matches an internal key placeholder of `policy` at `(isChange, addressIndex)`, AND
    2. `policy.deriveScripts isChange addressIndex` yields a `scriptPubKey` (and optional `redeemScript`/`witnessScript`)
       matching the input's verified UTXO `scriptPubKey`!
    (`process_in_outs.c:is_in_out_internal` & `compare_wallet_script_at_path.c`). -/
def matchInternalInput
    (policy : WalletPolicySpec)
    (inp : PsbtInput)
    (utxo : TxOut) : Option (Bool × UInt32) :=
  match findMatchingCoordinates policy inp.derivations with
  | none => none
  | some (isChange, addrIdx) =>
      match policy.deriveScripts isChange addrIdx with
      | none => none
      | some (expectedSpk, expectedRedeem, expectedWitness) =>
          let spkOk := bytesEq expectedSpk utxo.scriptPubKey
          let redeemOk := match expectedRedeem, inp.redeemScript with
            | none, none => true
            | some er, some ir => bytesEq er ir
            | _, _ => false
          let witnessOk := match expectedWitness, inp.witnessScript with
            | none, none => true
            | some ew, some iw => bytesEq ew iw
            | _, _ => false
          if spkOk && redeemOk && witnessOk then
            some (isChange, addrIdx)
          else
            none

def isInternalInput (policy : WalletPolicySpec) (inp : PsbtInput) (utxo : TxOut) : Bool :=
  (matchInternalInput policy inp utxo).isSome

/-- **CRITICAL CHANGE ELIMINATION INVARIANT** (`process_in_outs.c:114` & `preprocess_outputs.c`):
    An output is silently accepted as **verified change** (`isVerifiedChange`) IFF:
    1. It is NOT an unfinalized silent payment output (`out.scriptPubKey = some spk`),
    2. Its PSBT key derivation metadata matches an internal key placeholder of the **SAME** `policy`
       being spent, on the **internal (`change`, `isChange = true`)** branch (`numSecond`),
    3. `policy.deriveScripts true addressIndex` matches `out.scriptPubKey` (and any `redeemScript` /
       `witnessScript` present on the output) byte-for-byte!
    Outputs on the receive branch (`isChange = false`) or lacking valid key derivation metadata return `false`
    and MUST be shown to the user in `DisplayedOutputs`! -/
def isVerifiedChange (policy : WalletPolicySpec) (out : PsbtOutput) : Bool :=
  if out.silentPayment.isSome then
    false
  else
    match out.scriptPubKey with
    | none => false
    | some spk =>
        match findMatchingCoordinates policy out.derivations with
        | some (true, addrIdx) =>
            match policy.deriveScripts true addrIdx with
            | none => false
            | some (expectedSpk, expectedRedeem, expectedWitness) =>
                let spkOk := bytesEq expectedSpk spk
                let redeemOk := match out.redeemScript, expectedRedeem with
                  | none, _ => true
                  | some r, some er => bytesEq er r
                  | some _, none => false
                let witnessOk := match out.witnessScript, expectedWitness with
                  | none, _ => true
                  | some w, some ew => bytesEq ew w
                  | some _, none => false
                spkOk && redeemOk && witnessOk
        | _ => false

/-! ## 8. OP_RETURN Standardness, Warnings, Display Modes & Fee Safety -/

/-- Validate minimal push instructions inside an `OP_RETURN` (`0x6a`) output script
    (`format_opscript_script` in `app-bitcoin/src/common/script.c`):
    - Total script length `1 <= len <= 83`, byte 0 is `0x6a` (`OP_RETURN`).
    - Bare `OP_RETURN` (length 1) is valid (`0` pushes).
    - Otherwise `1..5` minimal data push opcodes (`OP_0`, `1..75` direct bytes, `OP_PUSHDATA1` with `76..80` bytes,
      `OP_1NEGATE`, `OP_1..OP_16`; `OP_PUSHDATA2`/`OP_PUSHDATA4` and non-push opcodes are rejected). -/
def verifyOpReturnPushes (s : ByteArray) : Nat → Nat → Nat → Bool
  | 0, pos, nPushes => pos == s.size && nPushes ≤ 5
  | fuel + 1, pos, nPushes =>
      if pos >= s.size then
        pos == s.size && nPushes ≤ 5
      else if nPushes >= 5 then
        false
      else
        match byteAt? s pos with
        | none => false
        | some opByte =>
            let op := opByte.toNat
            if op == 0x00 || op == 0x4f || (0x51 ≤ op && op ≤ 0x60) then
              verifyOpReturnPushes s fuel (pos + 1) (nPushes + 1)
            else if 1 ≤ op && op ≤ 75 then
              if pos + 1 + op ≤ s.size then
                verifyOpReturnPushes s fuel (pos + 1 + op) (nPushes + 1)
              else
                false
            else if op == 0x4c then
              match byteAt? s (pos + 1) with
              | none => false
              | some lenByte =>
                  let dataLen := lenByte.toNat
                  if dataLen > 75 && pos + 2 + dataLen ≤ s.size then
                    verifyOpReturnPushes s fuel (pos + 2 + dataLen) (nPushes + 1)
                  else
                    false
            else
              false

def isValidOpReturnScript (s : ByteArray) : Bool :=
  decide (1 ≤ s.size ∧ s.size ≤ 83) &&
  byteAt? s 0 == some 0x6a &&
  verifyOpReturnPushes s s.size 1 0

def isOpReturnScript (s : ByteArray) : Bool :=
  byteAt? s 0 == some 0x6a

/-- Transaction display mode (`tx_display_mode_t` in `app-bitcoin/src/ui/display.h`). -/
inductive TxDisplayMode where
  /-- Standard full review: recipient outputs + exact network fee. -/
  | full
  /-- Net-value-only review when inputs/outputs are open (`NONE`/`SINGLE`/`ANYONECANPAY`) or external input value is unverified. -/
  | netOnly
  /-- Self-transfer review when all outputs are verified change (`displayedOutputs` is empty). -/
  | selfTransfer
  deriving Repr, DecidableEq, Inhabited

/-- Security warnings surfaced to the interactive user approval screen (`tx_warnings_t`). -/
structure TxWarnings where
  missingNonWitnessUtxo : Bool := false
  nonDefaultSighash : Bool := false
  sighashMixed : Bool := false
  externalInputs : Bool := false
  highFee : Bool := false
  nonStandardLocktime : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Configuration parameters governing policy gates during `SIGN_PSBT`. -/
structure SigningConfig where
  /-- Device setting allowing non-default sighash types (`SIGHASH_NONE`, `SIGHASH_SINGLE`, `ANYONECANPAY`). -/
  allowNonDefaultSighash : Bool := false
  /-- Whether external (non-wallet) inputs are permitted (`true` on BOLOS, `false` on Vanadium). -/
  allowExternalInputs : Bool := true
  /-- High-fee threshold inclusivity (`false` = BOLOS `sumInputs > 100_000`; `true` = Vanadium `sumInputs >= 100_000`). -/
  highFeeInclusiveAt100k : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Validated transaction summary produced prior to user review and cryptographic signing. -/
structure ValidatedPsbt where
  locktime : UInt32
  validatedInputs : Array (ValidatedInputUtxo × Bool × UInt8)
  /-- Indices and outputs that MUST be displayed to the user (`!isVerifiedChange`). -/
  displayedOutputs : List (Nat × PsbtOutput)
  /-- Indices and outputs verified as internal change (`isVerifiedChange`). -/
  changeOutputs : List (Nat × PsbtOutput)
  sumInputs : Nat
  sumInternalInputs : Nat
  sumOutputs : Nat
  sumChangeOutputs : Nat
  /-- Network fee (`some (sumInputs - sumOutputs)` when sighashes close inputs & outputs; `none` when open). -/
  fee : Option Nat
  displayMode : TxDisplayMode
  warnings : TxWarnings
  deriving DecidableEq

/-- Validate wallet policy basic invariants: non-empty internal key expressions, and unnamed if default. -/
def validatePolicyHeader (policy : WalletPolicySpec) : Except PsbtError Unit :=
  if policy.internalPlaceholders.isEmpty then
    .error .invalidWalletPolicy
  else if policy.isDefault && policy.name != "" then
    .error .invalidWalletPolicy
  else
    .ok ()

/-- Validate a single output's script / silent-payment / OP_RETURN / network-address invariants. -/
def validateSingleOutputScript (crypto : CryptoOracles) (out : PsbtOutput) : Except PsbtError Unit :=
  match out.scriptPubKey, out.silentPayment with
  | none, none => .error .missingOutputScript
  | some spk, _ =>
      if isOpReturnScript spk then
        if isValidOpReturnScript spk then .ok () else .error .invalidOpReturnScript
      else
        if (crypto.formatAddress spk).isSome then .ok () else .error .missingOutputScript
  | none, some _ => .ok ()

/-- Classify and validate all outputs, enforcing `MAX_MONEY`, `OP_RETURN` formatting, presence of scripts,
    and `MAX_CHANGE_OUTPUTS` (`preprocess_outputs.c` & `process_in_outs.c`). -/
def classifyAndValidateOutputsLoop
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (idx : Nat)
    (rem : List PsbtOutput)
    (dispAcc : List (Nat × PsbtOutput))
    (chgAcc : List (Nat × PsbtOutput))
    (sumOut : Nat)
    (sumChg : Nat) :
    Except PsbtError (List (Nat × PsbtOutput) × List (Nat × PsbtOutput) × Nat × Nat) :=
  match rem with
  | [] =>
      if chgAcc.length > MAX_CHANGE_OUTPUTS then
        .error .tooManyChangeOutputs
      else
        .ok (dispAcc.reverse, chgAcc.reverse, sumOut, sumChg)
  | out :: rest =>
      if out.amount > MAX_MONEY then
        .error .amountExceedsMaxSupply
      else if sumOut + out.amount > MAX_MONEY then
        .error .amountExceedsMaxSupply
      else
        match validateSingleOutputScript crypto out with
        | .error e => .error e
        | .ok () =>
            if isVerifiedChange policy out then
              classifyAndValidateOutputsLoop crypto policy (idx + 1) rest dispAcc ((idx, out) :: chgAcc)
                (sumOut + out.amount) (sumChg + out.amount)
            else
              classifyAndValidateOutputsLoop crypto policy (idx + 1) rest ((idx, out) :: dispAcc) chgAcc
                (sumOut + out.amount) sumChg

def classifyAndValidateOutputs
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (outputs : List PsbtOutput) :
    Except PsbtError (List (Nat × PsbtOutput) × List (Nat × PsbtOutput) × Nat × Nat) :=
  classifyAndValidateOutputsLoop crypto policy 0 outputs [] [] 0 0

/-- Accumulator state while validating PSBT inputs in index order. -/
structure InputScanAcc where
  valInputs : Array (ValidatedInputUtxo × Bool × UInt8) := #[]
  sumIn : Nat := 0
  sumInternalIn : Nat := 0
  nInternal : Nat := 0
  nExternal : Nat := 0
  anyTaprootInternal : Bool := false
  anyExternalMissingNw : Bool := false
  warnMissingNw : Bool := false
  warnNonDefaultSighash : Bool := false
  sighashInputsOpen : Bool := false
  sighashOutputsOpen : Bool := false
  firstSighash : Option UInt8 := none
  sighashMixed : Bool := false
  deriving DecidableEq

/-- Validate all PSBT inputs recursively without opaque `Id.run` / `forIn` wrappers, keeping kernel reduction transparent. -/
def validateInputsLoop
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (isBip322 : Bool)
    (nOutputs : Nat)
    (idx : Nat)
    (rem : List PsbtInput)
    (acc : InputScanAcc) : Except PsbtError InputScanAcc :=
  match rem with
  | [] =>
      if acc.nInternal == 0 then
        .error .noInternalInputs
      else
        .ok acc
  | inp :: rest =>
      if inp.cleartextConfusionScore > MAX_CLEARTEXT_CONFUSION_SCORE then
        .error .cleartextConfusionScoreExceeded
      else
        match validateInputUtxo crypto inp (isBip322 && idx == 0) with
        | .error e => .error e
        | .ok utxoInfo =>
            let newSumIn := acc.sumIn + utxoInfo.prevoutTxOut.amount
            if newSumIn > MAX_MONEY then
              .error .amountExceedsMaxSupply
            else if isInternalInput policy inp utxoInfo.prevoutTxOut then
              if utxoInfo.spendClass != policy.spendClass then
                .error .invalidWalletPolicy
              else
                let (safety, shByte) := classifySighash policy.spendClass inp.sighashType
                match safety with
                | .unsupported => .error .unsupportedSighashType
                | .nonSafe =>
                    if !cfg.allowNonDefaultSighash then
                      .error .nonDefaultSighashDisallowed
                    else if sighashIsSingle shByte && idx >= nOutputs then
                      .error .sighashSingleIndexOutOfBounds
                    else
                      let normSh := if shByte == SIGHASH_DEFAULT then SIGHASH_ALL else shByte
                      let (nextFirst, nextMixed) := match acc.firstSighash with
                        | none => (some normSh, acc.sighashMixed)
                        | some prev => (some prev, acc.sighashMixed || (prev != normSh))
                      validateInputsLoop crypto cfg policy isBip322 nOutputs (idx + 1) rest {
                        valInputs := acc.valInputs.push (utxoInfo, true, shByte)
                        sumIn := newSumIn
                        sumInternalIn := acc.sumInternalIn + utxoInfo.prevoutTxOut.amount
                        nInternal := acc.nInternal + 1
                        nExternal := acc.nExternal
                        anyTaprootInternal := acc.anyTaprootInternal || (utxoInfo.spendClass == .taprootV1)
                        anyExternalMissingNw := acc.anyExternalMissingNw
                        warnMissingNw := acc.warnMissingNw || utxoInfo.missingNonWitnessUtxoWarning
                        warnNonDefaultSighash := true
                        sighashInputsOpen := acc.sighashInputsOpen || sighashOpensInputs shByte
                        sighashOutputsOpen := acc.sighashOutputsOpen || sighashOpensOutputs shByte
                        firstSighash := nextFirst
                        sighashMixed := nextMixed
                      }
                | .safe =>
                    if sighashIsSingle shByte && idx >= nOutputs then
                      .error .sighashSingleIndexOutOfBounds
                    else
                      let normSh := if shByte == SIGHASH_DEFAULT then SIGHASH_ALL else shByte
                      let (nextFirst, nextMixed) := match acc.firstSighash with
                        | none => (some normSh, acc.sighashMixed)
                        | some prev => (some prev, acc.sighashMixed || (prev != normSh))
                      validateInputsLoop crypto cfg policy isBip322 nOutputs (idx + 1) rest {
                        valInputs := acc.valInputs.push (utxoInfo, true, shByte)
                        sumIn := newSumIn
                        sumInternalIn := acc.sumInternalIn + utxoInfo.prevoutTxOut.amount
                        nInternal := acc.nInternal + 1
                        nExternal := acc.nExternal
                        anyTaprootInternal := acc.anyTaprootInternal || (utxoInfo.spendClass == .taprootV1)
                        anyExternalMissingNw := acc.anyExternalMissingNw
                        warnMissingNw := acc.warnMissingNw || utxoInfo.missingNonWitnessUtxoWarning
                        warnNonDefaultSighash := acc.warnNonDefaultSighash
                        sighashInputsOpen := acc.sighashInputsOpen || sighashOpensInputs shByte
                        sighashOutputsOpen := acc.sighashOutputsOpen || sighashOpensOutputs shByte
                        firstSighash := nextFirst
                        sighashMixed := nextMixed
                      }
            else
              if !cfg.allowExternalInputs then
                .error .externalInputsNotAllowed
              else
                validateInputsLoop crypto cfg policy isBip322 nOutputs (idx + 1) rest {
                  valInputs := acc.valInputs.push (utxoInfo, false, SIGHASH_ALL)
                  sumIn := newSumIn
                  sumInternalIn := acc.sumInternalIn
                  nInternal := acc.nInternal
                  nExternal := acc.nExternal + 1
                  anyTaprootInternal := acc.anyTaprootInternal
                  anyExternalMissingNw := acc.anyExternalMissingNw || inp.nonWitnessUtxo.isNone
                  warnMissingNw := acc.warnMissingNw
                  warnNonDefaultSighash := acc.warnNonDefaultSighash
                  sighashInputsOpen := acc.sighashInputsOpen
                  sighashOutputsOpen := acc.sighashOutputsOpen
                  firstSighash := acc.firstSighash
                  sighashMixed := acc.sighashMixed
                }

/-- Compute closed-transaction fee (`sumInputs >= sumOutputs` enforced strictly when inputs & outputs are closed). -/
def computeClosedFee (inputsOpen outputsOpen : Bool) (sumIn sumOut : Nat) : Except PsbtError (Option Nat) :=
  if !inputsOpen && !outputsOpen then
    if sumIn < sumOut then
      .error .negativeFeeOutputsExceedInputs
    else
      .ok (some (sumIn - sumOut))
  else
    .ok none

/-- Complete canonical PSBT pre-signing validation (`init_global_state` + `preprocess_inputs` +
    `preprocess_outputs` + `process_in_outs` + `transaction_display`). -/
def validatePsbt
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx) : Except PsbtError ValidatedPsbt :=
  match validatePolicyHeader policy with
  | .error e => .error e
  | .ok () =>
      if psbt.inputs.isEmpty || psbt.outputs.isEmpty then
        .error .emptyInputsOrOutputs
      else
        match determineLocktime psbt.fallbackLocktime psbt.inputs.toList with
        | .error e => .error e
        | .ok locktime =>
            match validateInputsLoop crypto cfg policy psbt.bip322Message.isSome psbt.outputs.size 0 psbt.inputs.toList {} with
            | .error e => .error e
            | .ok inAcc =>
                match classifyAndValidateOutputs crypto policy psbt.outputs.toList with
                | .error e => .error e
                | .ok (displayedOuts, changeOuts, sumOut, sumChg) =>
                    match computeClosedFee inAcc.sighashInputsOpen inAcc.sighashOutputsOpen inAcc.sumIn sumOut with
                    | .error e => .error e
                    | .ok fee? =>
                        let externalAmountUnverified :=
                          inAcc.anyExternalMissingNw && !(inAcc.anyTaprootInternal && !inAcc.sighashInputsOpen)
                        let mode : TxDisplayMode :=
                          if inAcc.sighashInputsOpen || inAcc.sighashOutputsOpen || externalAmountUnverified then
                            .netOnly
                          else if displayedOuts.isEmpty then
                            .selfTransfer
                          else
                            .full
                        let aboveSupplyFloor :=
                          if cfg.highFeeInclusiveAt100k then decide (inAcc.sumIn ≥ 100000) else decide (inAcc.sumIn > 100000)
                        let highFeeWarn : Bool :=
                          match mode, fee? with
                          | .full, some f => decide (10 * f ≥ inAcc.sumIn) && aboveSupplyFloor
                          | _, _ => false
                        .ok {
                          locktime := locktime
                          validatedInputs := inAcc.valInputs
                          displayedOutputs := displayedOuts
                          changeOutputs := changeOuts
                          sumInputs := inAcc.sumIn
                          sumInternalInputs := inAcc.sumInternalIn
                          sumOutputs := sumOut
                          sumChangeOutputs := sumChg
                          fee := fee?
                          displayMode := mode
                          warnings := {
                            missingNonWitnessUtxo := inAcc.warnMissingNw
                            nonDefaultSighash := inAcc.warnNonDefaultSighash
                            sighashMixed := inAcc.sighashMixed
                            externalInputs := decide (inAcc.nExternal > 0)
                            highFee := highFeeWarn
                            nonStandardLocktime := decide (locktime.toNat > 0)
                          }
                        }

/-! ## 9. Exact Sighash Digest Specifications (`txhashes.c`, BIP-143, BIP-341, BIP-342) -/

/-- Precomputed transaction-wide SHA-256 digests (`tx_hashes_t` in `txhashes.c`).
    Note: `shaPrevouts`, `shaSequences`, and `shaOutputs` are **single** SHA-256 digests
    (matching BIP-341 directly; BIP-143 applies a second `sha256` on top). -/
structure TxHashes where
  shaPrevouts : Bytes32
  shaAmounts : Bytes32
  shaScriptPubkeys : Bytes32
  shaSequences : Bytes32
  shaOutputs : Bytes32
  deriving DecidableEq

/-- Compute transaction-wide digests over all inputs and finalized outputs (`compute_tx_hashes`). -/
def computeTxHashes
    (sha256 : ByteArray → Bytes32)
    (inputs : List (PsbtInput × TxOut))
    (outputs : List TxOut) : TxHashes :=
  let prevoutsBytes := concatBytes (inputs.map fun (inp, _) => serializeOutPoint inp.prevout)
  let amountsBytes := concatBytes (inputs.map fun (_, utxo) => encodeU64LE (UInt64.ofNat utxo.amount))
  let spkBytes := concatBytes (inputs.map fun (_, utxo) =>
    encodeVarInt utxo.scriptPubKey.size ++ utxo.scriptPubKey)
  let seqBytes := concatBytes (inputs.map fun (inp, _) => encodeU32LE inp.effectiveSequence)
  let outBytes := concatBytes (outputs.map serializeTxOut)
  { shaPrevouts := sha256 prevoutsBytes
    shaAmounts := sha256 amountsBytes
    shaScriptPubkeys := sha256 spkBytes
    shaSequences := sha256 seqBytes
    shaOutputs := sha256 outBytes }

/-- Exact Legacy Sighash (`compute_sighash_legacy` in `txhashes.c`):
    `doubleSha256` of the transaction with `scriptCode` (`redeemScript` if P2SH, else `prevout.scriptPubKey`)
    placed in `vin[inputIndex]` and empty scripts `0x00` in all other inputs, followed by `locktime (4LE)`
    and `sighashByte (4LE)`. -/
def sighashLegacy
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (inputs : Array PsbtInput)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (scriptCode : ByteArray)
    (sighashByte : UInt8) : Bytes32 :=
  let serializedInputs := concatBytes <| (List.range inputs.size).map fun i =>
    if h : i < inputs.size then
      let inp := inputs[i]'h
      let sc :=
        if i == inputIndex then
          encodeVarInt scriptCode.size ++ scriptCode
        else
          ByteArray.mk #[0x00]
      serializeOutPoint inp.prevout ++ sc ++ encodeU32LE inp.effectiveSequence
    else
      ByteArray.empty
  let serializedOutputs := concatBytes (outputs.toList.map serializeTxOut)
  let preimage :=
    encodeU32LE txVersion ++
    encodeVarInt inputs.size ++
    serializedInputs ++
    encodeVarInt outputs.size ++
    serializedOutputs ++
    encodeU32LE locktime ++
    encodeU32LE (UInt32.ofNat sighashByte.toNat)
  doubleSha256 sha256 preimage

/-- Construct BIP-143 `scriptCode` (including length prefix) for SegWit v0 (`txhashes.c:472-514`):
    - For P2WPKH (`0x00 0x14 <20-byte pubkeyHash>`): `0x19 0x76 0xa9 0x14 <20B> 0x88 0xac`.
    - For P2WSH (`0x00 0x20 <32-byte sha256>`): `varint(witnessScript.size) || witnessScript`. -/
def segwitV0ScriptCode (activeScript : ByteArray) (witnessScript : Option ByteArray) : Option ByteArray :=
  if isP2WPKHScript activeScript then
    let pkHash20 := activeScript.extract 2 22
    some (ByteArray.mk #[0x19, 0x76, 0xa9, 0x14] ++ pkHash20 ++ ByteArray.mk #[0x88, 0xac])
  else if isP2WSHScript activeScript then
    match witnessScript with
    | some ws => some (encodeVarInt ws.size ++ ws)
    | none => none
  else
    none

/-- Exact BIP-143 SegWit v0 Sighash (`compute_sighash_segwitv0` in `txhashes.c:408-576`). -/
def sighashSegwitV0
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (hashes : TxHashes)
    (inp : PsbtInput)
    (utxoAmount : Nat)
    (scriptCodeWithLen : ByteArray)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (sighashByte : UInt8) : Bytes32 :=
  let anyoneCanPay := sighashOpensInputs sighashByte
  let base := sighashByte &&& 0x1f
  let hashPrevouts : Bytes32 :=
    if !anyoneCanPay then sha256 hashes.shaPrevouts.bytes else zeroBytes32
  let hashSequence : Bytes32 :=
    if !anyoneCanPay && base != SIGHASH_SINGLE && base != SIGHASH_NONE then
      sha256 hashes.shaSequences.bytes
    else
      zeroBytes32
  let hashOutputs : Bytes32 :=
    if base != SIGHASH_SINGLE && base != SIGHASH_NONE then
      sha256 hashes.shaOutputs.bytes
    else if base == SIGHASH_SINGLE then
      if h : inputIndex < outputs.size then
        doubleSha256 sha256 (serializeTxOut (outputs[inputIndex]'h))
      else
        zeroBytes32
    else
      zeroBytes32
  let preimage :=
    encodeU32LE txVersion ++
    hashPrevouts.bytes ++
    hashSequence.bytes ++
    serializeOutPoint inp.prevout ++
    scriptCodeWithLen ++
    encodeU64LE (UInt64.ofNat utxoAmount) ++
    encodeU32LE inp.effectiveSequence ++
    hashOutputs.bytes ++
    encodeU32LE locktime ++
    encodeU32LE (UInt32.ofNat sighashByte.toNat)
  doubleSha256 sha256 preimage

/-- Exact BIP-341 / BIP-342 Taproot v1 Sighash (`compute_sighash_segwitv1` in `txhashes.c:578-698`).
    Covers both key-path (`tapleafHash = none`, `ext_flag = 0`) and script-path (`tapleafHash = some h`,
    `ext_flag = 1`, `key_version = 0x00`, `codesep_pos = 0xFFFFFFFF`), with annex absent (`annex_present = 0`). -/
def sighashTaproot
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (hashes : TxHashes)
    (inp : PsbtInput)
    (utxo : TxOut)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (tapleafHash : Option Bytes32)
    (sighashByte : UInt8) : Bytes32 :=
  let anyoneCanPay := (sighashByte &&& 0x80) == SIGHASH_ANYONECANPAY
  let base := sighashByte &&& 0x03
  let extFlag : UInt8 := if tapleafHash.isSome then 1 else 0
  let spendType : UInt8 := extFlag * 2
  let commonPrefix :=
    ByteArray.mk #[0x00, sighashByte] ++
    encodeU32LE txVersion ++
    encodeU32LE locktime
  let txInCommits :=
    if !anyoneCanPay then
      hashes.shaPrevouts.bytes ++
      hashes.shaAmounts.bytes ++
      hashes.shaScriptPubkeys.bytes ++
      hashes.shaSequences.bytes
    else
      ByteArray.empty
  let txOutCommits :=
    if base != SIGHASH_NONE && base != SIGHASH_SINGLE then
      hashes.shaOutputs.bytes
    else
      ByteArray.empty
  let perInputData :=
    if anyoneCanPay then
      serializeOutPoint inp.prevout ++
      encodeU64LE (UInt64.ofNat utxo.amount) ++
      encodeVarInt utxo.scriptPubKey.size ++
      utxo.scriptPubKey ++
      encodeU32LE inp.effectiveSequence
    else
      encodeU32LE (UInt32.ofNat inputIndex)
  let singleOutCommit :=
    if base == SIGHASH_SINGLE then
      if h : inputIndex < outputs.size then
        (sha256 (serializeTxOut (outputs[inputIndex]'h))).bytes
      else
        ByteArray.empty
    else
      ByteArray.empty
  let tapscriptExt :=
    match tapleafHash with
    | none => ByteArray.empty
    | some lh => lh.bytes ++ ByteArray.mk #[0x00] ++ encodeU32LE 0xFFFFFFFF
  let msg :=
    commonPrefix ++
    txInCommits ++
    txOutCommits ++
    ByteArray.mk #[spendType] ++
    perInputData ++
    singleOutCommit ++
    tapscriptExt
  taggedHash sha256 "TapSighash" msg

/-- Canonical signature sighash suffix rule (`sign_input.c:115, 225-228` & `signing.rs`):
    - ECDSA signatures ALWAYS append `sighashByte`.
    - BIP-340 Schnorr signatures omit the byte for `SIGHASH_DEFAULT` (`0x00` -> 64 bytes)
      and append `sighashByte` iff `sighashByte != 0x00` (65 bytes). -/
def appendSighashSuffix (isSchnorr : Bool) (rawSig : ByteArray) (sighashByte : UInt8) : ByteArray :=
  if isSchnorr && sighashByte == SIGHASH_DEFAULT then
    rawSig
  else
    rawSig ++ ByteArray.mk #[sighashByte]

/-! ## 10. BIP-322 Virtual Transaction Validation (`bip322_validation.c` & `bip322.c`) -/

/-- BIP-322 `to_spend` virtual transaction (`bip322_compute_to_spend_txid` in `src/common/bip322.c`):
    - `nVersion = 0`, `nLockTime = 0`
    - 1 input: `prevout = 00..00:0xFFFFFFFF`, `scriptSig = OP_0 (0x00) PUSH32 (0x20) <taggedHash("BIP0322-signed-message", message)>`, `nSequence = 0`
    - 1 output: `amount = 0`, `scriptPubKey = messageChallengeScript`. -/
def bip322ToSpendTx (sha256 : ByteArray → Bytes32) (message : ByteArray) (challengeScript : ByteArray) : RawTx :=
  let msgHash := taggedHash sha256 "BIP0322-signed-message" message
  let scriptSig := ByteArray.mk #[0x00, 0x20] ++ msgHash.bytes
  { version := 0
    vin := #[{
      prevout := { txid := zeroBytes32, vout := 0xFFFFFFFF }
      scriptSig := scriptSig
      sequence := 0
    }]
    vout := #[{
      amount := 0
      scriptPubKey := challengeScript
    }]
    locktime := 0 }

def bip322ToSpendTxid (sha256 : ByteArray → Bytes32) (message : ByteArray) (challengeScript : ByteArray) : Bytes32 :=
  computeTxid sha256 (bip322ToSpendTx sha256 message challengeScript)

/-- Check whether a BIP-322 message is directly displayable as printable ASCII (`0x20..0x7E` or `0x0A`, `len <= 640`). -/
def isBip322MessagePrintable (msg : ByteArray) : Bool :=
  decide (msg.size ≤ MAX_BIP322_PRINTABLE_LEN) &&
  msg.toList.all (fun b => (0x20 ≤ b.toNat && b.toNat ≤ 0x7E) || b == 0x0A)

/-- Proof-of-funds `nSequence` check for BIP-322 inputs `i > 0`: relative timelock (BIP-68) must be disabled. -/
def bip322ProofOfFundsSequenceValid (inp : PsbtInput) : Bool :=
  let seq := inp.effectiveSequence
  seq == 0 || (seq &&& (0x80000000 : UInt32)) != 0

/-- Exact BIP-322 `to_sign` PSBT validation (`validate_bip322_psbt` in `bip322_validation.c`):
    1. Forbidden in Swap mode (`!inSwapMode`).
    2. `txVersion == 0 || txVersion == 2`, and `locktime == 0`.
    3. Exactly 1 output (`outputs.size == 1`), `amount == 0`, `scriptPubKey == #[0x6a]` (1-byte `OP_RETURN`), `changeOutputs.isEmpty`.
    4. Zero external inputs (`!warnings.externalInputs`), and all inputs use default/ALL sighash (`!warnings.nonDefaultSighash`).
    5. Input 0 (`message_challenge`):
       - `PSBT_IN_SEQUENCE` MUST be explicitly present and equal to `0` (`sequence == some 0`),
       - `prevout.vout == 0`,
       - `utxo.amount == 0`,
       - `prevout.txid == bip322ToSpendTxid sha256 message utxo0.scriptPubKey`.
    6. Proof-of-funds inputs (`i > 0`): `bip322ProofOfFundsSequenceValid` holds. -/
def validateBip322Psbt
    (sha256 : ByteArray → Bytes32)
    (inSwapMode : Bool)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (message : ByteArray) : Except PsbtError Unit :=
  if inSwapMode then
    .error .bip322ForbiddenInSwap
  else if psbt.txVersion != 0 && psbt.txVersion != 2 then
    .error .bip322InvalidStructure
  else if validated.locktime != 0 then
    .error .bip322InvalidStructure
  else if psbt.outputs.size != 1 || !validated.changeOutputs.isEmpty then
    .error .bip322InvalidStructure
  else if hOut : 0 < psbt.outputs.size then
    let out0 := psbt.outputs[0]'hOut
    if out0.amount != 0 || out0.scriptPubKey != some (ByteArray.mk #[0x6a]) then
      .error .bip322InvalidStructure
    else if validated.warnings.externalInputs || validated.warnings.nonDefaultSighash then
      .error .bip322InvalidStructure
    else if hIn : 0 < psbt.inputs.size ∧ 0 < validated.validatedInputs.size then
      let inp0 := psbt.inputs[0]'hIn.1
      let (utxo0, _, _) := validated.validatedInputs[0]'hIn.2
      if inp0.sequence != some 0 then
        .error .bip322InvalidSequence
      else if inp0.prevout.vout != 0 || utxo0.prevoutTxOut.amount != 0 then
        .error .bip322InvalidStructure
      else if inp0.prevout.txid != bip322ToSpendTxid sha256 message utxo0.prevoutTxOut.scriptPubKey then
        .error .bip322ChallengeTxidMismatch
      else if !(psbt.inputs.toList.drop 1).all bip322ProofOfFundsSequenceValid then
        .error .bip322InvalidSequence
      else
        .ok ()
    else
      .error .bip322InvalidStructure
  else
    .error .bip322InvalidStructure

/-! ## 11. Ledger Swap Mode Contract (`swap_checks.c` & `handle_swap_sign_transaction.c`) -/

/-- Pre-approved Exchange Swap mode (`swap_mode_t` in `swap_globals.h`). -/
inductive SwapMode where
  /-- Standard swap (`extra_id[0] == 0`): 1 external recipient output. -/
  | standard
  /-- Cross-chain swap (`extra_id[0] == 2`): external output 0 is `0`-sat `OP_RETURN <payinData>` with `sha256(payinData) == expectedPayinHash`, and external output 1 is recipient. -/
  | crossChain (expectedPayinHash : Bytes32)
  deriving DecidableEq

/-- Pre-approved swap parameters locked in Exchange app before handing control to Bitcoin app (`G_swap_state`). -/
structure SwapParams where
  mode : SwapMode
  /-- Exact amount in satoshis sent to `destinationAddress`. -/
  amount : Nat
  /-- Exact transaction fee in satoshis. -/
  fees : Nat
  /-- Pre-approved destination address string (without `bitcoin:` URI prefix). -/
  destinationAddress : String
  deriving DecidableEq

/-- Extract the single pushed payload from a cross-chain swap `OP_RETURN` script
    (`extract_op_return_data` in `app-bitcoin/src/handler/sign_psbt/swap_checks.c:21-52`):
    - Byte 0 == `0x6a` (`OP_RETURN`).
    - Either direct push `op ∈ [2, 75]` with `s.size == 2 + op`,
      or `OP_PUSHDATA1` (`0x4c`) with `s.size == 3 + s[2]`. -/
def extractSwapOpReturnData (s : ByteArray) : Option ByteArray :=
  if byteAt? s 0 != some 0x6a then
    none
  else
    match byteAt? s 1 with
    | none => none
    | some pushByte =>
        let pushOp := pushByte.toNat
        if 2 ≤ pushOp && pushOp ≤ 75 then
          if s.size == 2 + pushOp then
            some (s.extract 2 s.size)
          else
            none
        else if pushOp == 0x4c then
          match byteAt? s 2 with
          | none => none
          | some lenByte =>
              let len := lenByte.toNat
              if s.size == 3 + len then
                some (s.extract 3 s.size)
              else
                none
        else
          none

/-- Resolve and validate the recipient output for Swap mode according to `SwapMode`. -/
def extractSwapDestOutput
    (crypto : CryptoOracles)
    (mode : SwapMode)
    (displayedOutputs : List (Nat × PsbtOutput)) : Except PsbtError PsbtOutput :=
  match mode with
  | .standard =>
      match displayedOutputs with
      | [(_, dOut)] => .ok dOut
      | _ => .error .swapOutputCountMismatch
  | .crossChain expectedHash =>
      match displayedOutputs with
      | [(_, opOut), (_, dOut)] =>
          if opOut.amount != 0 then
            .error .swapInvalidCrossChainPayin
          else
            match opOut.scriptPubKey with
            | none => .error .swapInvalidCrossChainPayin
            | some spk =>
                match extractSwapOpReturnData spk with
                | none => .error .swapInvalidCrossChainPayin
                | some payinData =>
                    if crypto.sha256 payinData != expectedHash then
                      .error .swapInvalidCrossChainPayin
                    else
                      .ok dOut
      | _ => .error .swapOutputCountMismatch

/-- Exact Ledger Swap Mode Validation (`check_swap_invariants` in `swap_checks.c`):
    UI approval may be bypassed in Swap mode ONLY when ALL of the following hold:
    1. Not BIP-322 message signing (`psbt.bip322Message.isNone`).
    2. Wallet policy is default (`policy.isDefault == true`).
    3. Zero external inputs (`!validated.warnings.externalInputs`).
    4. No missing `nonWitnessUtxo` warning (`!validated.warnings.missingNonWitnessUtxo`) and no non-default sighash (`!validated.warnings.nonDefaultSighash`).
    5. External outputs (`validated.displayedOutputs`) match `swap.mode` via `extractSwapDestOutput`.
    6. Exact fee match: `validated.fee == some swap.fees`.
    7. Exact spent amount match: `(validated.sumOutputs - validated.sumChangeOutputs) == swap.amount` AND `destOut.amount == swap.amount`.
    8. Exact destination address match: `destOut.scriptPubKey = some destSpk`, `destOut.silentPayment.isNone`,
       and `crypto.formatAddress destSpk == some swap.destinationAddress`. -/
def validateSwapPsbt
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams) : Except PsbtError Unit :=
  if psbt.bip322Message.isSome then
    .error .bip322ForbiddenInSwap
  else if !policy.isDefault ||
          validated.warnings.externalInputs ||
          validated.warnings.missingNonWitnessUtxo ||
          validated.warnings.nonDefaultSighash then
    .error .swapPolicyOrWarningViolation
  else
    match extractSwapDestOutput crypto swap.mode validated.displayedOutputs with
    | .error e => .error e
    | .ok destOut =>
        match validated.fee with
        | none => .error .swapFeeMismatch
        | some actualFee =>
            if actualFee != swap.fees then
              .error .swapFeeMismatch
            else if (validated.sumOutputs - validated.sumChangeOutputs) != swap.amount ||
                    destOut.amount != swap.amount then
              .error .swapAmountMismatch
            else if destOut.silentPayment.isSome then
              .error .swapDestinationMismatch
            else
              match destOut.scriptPubKey with
              | none => .error .swapDestinationMismatch
              | some destSpk =>
                  if crypto.formatAddress destSpk != some swap.destinationAddress then
                    .error .swapDestinationMismatch
                  else
                    .ok ()

/-- Top-level PSBT authorization contract combining general validation, BIP-322 validation (when present),
    and Swap parameter lock validation (when `swapParams = some swap`). -/
def authorizePsbtSigning
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (swapParams : Option SwapParams) : Except PsbtError ValidatedPsbt :=
  match validatePsbt crypto cfg policy psbt with
  | .error e => .error e
  | .ok validated =>
      let bip322Check : Except PsbtError Unit :=
        match psbt.bip322Message with
        | some msg => validateBip322Psbt crypto.sha256 swapParams.isSome psbt validated msg
        | none => .ok ()
      match bip322Check with
      | .error e => .error e
      | .ok () =>
          match swapParams with
          | none => .ok validated
          | some swap =>
              match validateSwapPsbt crypto policy psbt validated swap with
              | .error e => .error e
              | .ok () => .ok validated

/-! ## 12. Security Rejection, Completeness & Non-Vacuity Theorems (`0 sorryAx`) -/

/-- Helper lemma: every output classified by `classifyAndValidateOutputsLoop` with `isVerifiedChange policy out = false`
    is preserved in `displayedOutputs`. -/
private theorem classifyOutputsLoop_preserves_unverified
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (idx : Nat)
    (rem : List PsbtOutput)
    (dispAcc chgAcc : List (Nat × PsbtOutput))
    (sumOut sumChg : Nat)
    (dispRes chgRes : List (Nat × PsbtOutput))
    (sumOutRes sumChgRes : Nat)
    (hOk : classifyAndValidateOutputsLoop crypto policy idx rem dispAcc chgAcc sumOut sumChg =
           .ok (dispRes, chgRes, sumOutRes, sumChgRes)) :
    (∀ p ∈ dispAcc, p ∈ dispRes) ∧
    (∀ k out, rem[k]? = some out → isVerifiedChange policy out = false → (idx + k, out) ∈ dispRes) := by
  induction rem generalizing idx dispAcc chgAcc sumOut sumChg with
  | nil =>
      simp only [classifyAndValidateOutputsLoop] at hOk
      split at hOk
      · contradiction
      · injection hOk with hTuple
        cases hTuple
        constructor
        · intro p hp
          exact List.mem_reverse.mpr hp
        · intro k out hk
          simp at hk
  | cons hd tl ih =>
      simp only [classifyAndValidateOutputsLoop] at hOk
      split at hOk
      · contradiction
      · split at hOk
        · contradiction
        · cases hScript : validateSingleOutputScript crypto hd with
          | error e =>
              rw [hScript] at hOk
              contradiction
          | ok u =>
              cases u
              rw [hScript] at hOk
              simp only at hOk
              by_cases hChg : isVerifiedChange policy hd = true
              · simp only [hChg, ↓reduceIte] at hOk
                obtain ⟨ihAcc, ihRem⟩ := ih (idx + 1) dispAcc ((idx, hd) :: chgAcc) (sumOut + hd.amount) (sumChg + hd.amount) hOk
                refine ⟨ihAcc, ?_⟩
                intro k out hk hNotChg
                cases k with
                | zero =>
                    simp at hk
                    subst hk
                    rw [hChg] at hNotChg
                    contradiction
                | succ k' =>
                    simp at hk
                    have hMem := ihRem k' out hk hNotChg
                    have hEqIdx : idx + 1 + k' = idx + (k' + 1) := by omega
                    rw [hEqIdx] at hMem
                    exact hMem
              · have hFalse : isVerifiedChange policy hd = false := Bool.eq_false_iff.mpr hChg
                simp only [hFalse, Bool.false_eq_true, ↓reduceIte] at hOk
                obtain ⟨ihAcc, ihRem⟩ := ih (idx + 1) ((idx, hd) :: dispAcc) chgAcc (sumOut + hd.amount) sumChg hOk
                constructor
                · intro p hp
                  exact ihAcc p (List.mem_cons_of_mem _ hp)
                · intro k out hk hNotChg
                  cases k with
                  | zero =>
                      simp at hk
                      subst hk
                      have hHead : (idx, hd) ∈ (idx, hd) :: dispAcc := List.Mem.head _
                      have hMem := ihAcc (idx, hd) hHead
                      simpa using hMem
                  | succ k' =>
                      simp at hk
                      have hMem := ihRem k' out hk hNotChg
                      have hEqIdx : idx + 1 + k' = idx + (k' + 1) := by omega
                      rw [hEqIdx] at hMem
                      exact hMem

/-- **THEOREM 1 (Unverified Change Never Hidden)**:
    Whenever output classification succeeds, EVERY output `out` at index `k` for which
    `isVerifiedChange policy out = false` (including external addresses, receive-branch addresses,
    silent payment outputs, or outputs with missing/matched derivation paths) MUST appear in `displayedOutputs`. -/
theorem unverified_change_never_hidden
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (outputs : List PsbtOutput)
    (dispOuts chgOuts : List (Nat × PsbtOutput))
    (sumOut sumChg : Nat)
    (hOk : classifyAndValidateOutputs crypto policy outputs = .ok (dispOuts, chgOuts, sumOut, sumChg))
    (k : Nat) (out : PsbtOutput)
    (hGet : outputs[k]? = some out)
    (hUnverified : isVerifiedChange policy out = false) :
    (k, out) ∈ dispOuts := by
  unfold classifyAndValidateOutputs at hOk
  obtain ⟨_, hRem⟩ := classifyOutputsLoop_preserves_unverified crypto policy 0 outputs [] [] 0 0 dispOuts chgOuts sumOut sumChg hOk
  have hMem := hRem k out hGet hUnverified
  simpa using hMem

/-- **THEOREM 2 (Receive-Branch Output Never Hidden as Change)**:
    Even if an output's derivation metadata belongs to our own wallet policy, if it derives on the
    receive branch (`isChange = false`, `numFirst`) rather than the internal change branch (`numSecond`),
    `isVerifiedChange` is strictly `false`. -/
theorem receive_branch_output_not_verified_change
    (policy : WalletPolicySpec)
    (out : PsbtOutput)
    (addrIdx : UInt32)
    (hCoords : findMatchingCoordinates policy out.derivations = some (false, addrIdx)) :
    isVerifiedChange policy out = false := by
  unfold isVerifiedChange
  split
  · rfl
  · cases out.scriptPubKey with
    | none => rfl
    | some spk => simp [hCoords]

/-- **THEOREM 3a (Negative Fee Rejection)**:
    When input and output commitments are closed (`!inputsOpen && !outputsOpen`), any transaction
    with `sumInputs < sumOutputs` is strictly rejected with `.negativeFeeOutputsExceedInputs`. -/
theorem negative_fee_rejected
    (sumIn sumOut : Nat)
    (hLt : sumIn < sumOut) :
    computeClosedFee false false sumIn sumOut = .error .negativeFeeOutputsExceedInputs := by
  simp [computeClosedFee, hLt]

/-- **THEOREM 3b (Validated PSBT Fee Safety & Overflow-Free Subtraction)**:
    Whenever `validatePsbt` succeeds with `v.fee = some f`, `v.sumOutputs <= v.sumInputs` holds
    strictly and `f = v.sumInputs - v.sumOutputs`. -/
theorem validated_psbt_fee_non_negative
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (v : ValidatedPsbt)
    (f : Nat)
    (hValid : validatePsbt crypto cfg policy psbt = .ok v)
    (hFee : v.fee = some f) :
    v.sumOutputs ≤ v.sumInputs ∧ f = v.sumInputs - v.sumOutputs := by
  unfold validatePsbt at hValid
  cases hPol : validatePolicyHeader policy with
  | error e => rw [hPol] at hValid; contradiction
  | ok u =>
      cases u
      rw [hPol] at hValid
      simp only at hValid
      split at hValid
      · contradiction
      · cases hLt : determineLocktime psbt.fallbackLocktime psbt.inputs.toList with
        | error e => rw [hLt] at hValid; contradiction
        | ok lt =>
            rw [hLt] at hValid
            simp only at hValid
            cases hIn : validateInputsLoop crypto cfg policy psbt.bip322Message.isSome psbt.outputs.size 0 psbt.inputs.toList {} with
            | error e => rw [hIn] at hValid; contradiction
            | ok inAcc =>
                rw [hIn] at hValid
                simp only at hValid
                cases hOut : classifyAndValidateOutputs crypto policy psbt.outputs.toList with
                | error e => rw [hOut] at hValid; contradiction
                | ok outTuple =>
                    rcases outTuple with ⟨dispOuts, chgOuts, sumOut, sumChg⟩
                    rw [hOut] at hValid
                    simp only at hValid
                    cases hCF : computeClosedFee inAcc.sighashInputsOpen inAcc.sighashOutputsOpen inAcc.sumIn sumOut with
                    | error e => rw [hCF] at hValid; contradiction
                    | ok feeOpt =>
                        rw [hCF] at hValid
                        simp only at hValid
                        injection hValid with hV
                        subst hV
                        simp only at hFee
                        subst hFee
                        unfold computeClosedFee at hCF
                        split at hCF
                        · split at hCF
                          · contradiction
                          · injection hCF with hSome
                            injection hSome with hEqF
                            dsimp only
                            omega
                        · cases hCF

/-- Helper for lawful `!=` (`bne`) reflection. -/
private theorem bne_eq_true_of_ne {α : Type} [DecidableEq α] {a b : α} (h : a ≠ b) : (a != b) = true := by
  simp [bne, h]

/-- **THEOREM 4a (CVE-2020-14199 / Missing UTXO Rejection)**:
    An input lacking both `nonWitnessUtxo` and `witnessUtxo` is unconditionally rejected. -/
theorem missing_utxo_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (exempt : Bool)
    (hNoNw : inp.nonWitnessUtxo = none)
    (hNoW : inp.witnessUtxo = none) :
    validateInputUtxo crypto inp exempt = .error .missingUtxo := by
  unfold validateInputUtxo extractInputPrevout
  rw [hNoNw, hNoW]

/-- **THEOREM 4b (Legacy Input With Mismatched `nonWitnessUtxo` Txid Rejected)**:
    Any input providing a `nonWitnessUtxo` whose `doubleSha256` txid differs from `prevout.txid`
    is unconditionally rejected with `.nonWitnessUtxoTxidMismatch`. -/
theorem mismatched_non_witness_utxo_txid_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (rawTx : RawTx)
    (exempt : Bool)
    (hNw : inp.nonWitnessUtxo = some rawTx)
    (hMismatch : computeTxid crypto.sha256 rawTx ≠ inp.prevout.txid) :
    validateInputUtxo crypto inp exempt = .error .nonWitnessUtxoTxidMismatch := by
  unfold validateInputUtxo extractInputPrevout
  have hNe : (computeTxid crypto.sha256 rawTx != inp.prevout.txid) = true := bne_eq_true_of_ne hMismatch
  cases hW : inp.witnessUtxo <;> simp [hNw, hNe]

/-- **THEOREM 4c (Legacy Input Providing `witnessUtxo` Rejected)**:
    A legacy input (`detectInputSpendClass == .legacy`) that supplies `witnessUtxo` (attempting to
    bypass full-tx verification) is rejected with `.legacyHasWitnessUtxo`. -/
theorem legacy_input_with_witness_utxo_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (wUtxo : TxOut)
    (exempt : Bool)
    (hNoNw : inp.nonWitnessUtxo = none)
    (hW : inp.witnessUtxo = some wUtxo)
    (hNoRedeem : inp.redeemScript = none)
    (hLegacy : detectInputSpendClass wUtxo.scriptPubKey none = .legacy) :
    validateInputUtxo crypto inp exempt = .error .legacyHasWitnessUtxo := by
  unfold validateInputUtxo extractInputPrevout
  simp [hNoNw, hW, hNoRedeem, hLegacy]

/-- **THEOREM 4d (Dual-UTXO Cross-Check Defense)**:
    When an input provides BOTH `nonWitnessUtxo` and `witnessUtxo`, if `nonWitnessUtxo.vout[vout]`
    disagrees with `witnessUtxo` (in either `amount` or `scriptPubKey`), validation rejects with
    `.dualUtxoMismatch`. -/
theorem dual_utxo_mismatch_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (rawTx : RawTx)
    (wUtxo : TxOut)
    (exempt : Bool)
    (hNw : inp.nonWitnessUtxo = some rawTx)
    (hW : inp.witnessUtxo = some wUtxo)
    (hTxid : computeTxid crypto.sha256 rawTx = inp.prevout.txid)
    (hBounds : inp.prevout.vout.toNat < rawTx.vout.size)
    (hDiff : rawTx.vout[inp.prevout.vout.toNat]'hBounds ≠ wUtxo) :
    validateInputUtxo crypto inp exempt = .error .dualUtxoMismatch := by
  unfold validateInputUtxo extractInputPrevout
  have hTxEq : (computeTxid crypto.sha256 rawTx != inp.prevout.txid) = false := by
    simp [bne, hTxid]
  have hOutNe : (rawTx.vout[inp.prevout.vout.toNat]'hBounds != wUtxo) = true :=
    bne_eq_true_of_ne hDiff
  simp [hNw, hW, hTxEq, hBounds, hOutNe]

/-- **THEOREM 5a (Swap Mode Rejects Fee Mismatch)**:
    `validateSwapPsbt` rejects any transaction whose fee differs from `swap.fees` (or whose fee is open/`none`). -/
theorem swap_rejects_fee_mismatch
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (hFeeMismatch : validated.fee ≠ some swap.fees) :
    ∀ u, validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  intro u hOk
  unfold validateSwapPsbt at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · cases hDest : extractSwapDestOutput crypto swap.mode validated.displayedOutputs with
      | error e => rw [hDest] at hOk; contradiction
      | ok destOut =>
          rw [hDest] at hOk
          simp only at hOk
          cases hFee : validated.fee with
          | none => rw [hFee] at hOk; contradiction
          | some actualFee =>
              rw [hFee] at hOk
              simp only at hOk
              by_cases hEq : actualFee = swap.fees
              · subst hEq
                exact hFeeMismatch hFee
              · have hNe : (actualFee != swap.fees) = true := bne_eq_true_of_ne hEq
                rw [hNe] at hOk
                contradiction

/-- **THEOREM 5b (Swap Mode Rejects Amount Mismatch)**:
    `validateSwapPsbt` rejects any transaction whose external spent amount (`sumOutputs - sumChangeOutputs`)
    differs from `swap.amount`. -/
theorem swap_rejects_amount_mismatch
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (hAmtMismatch : validated.sumOutputs - validated.sumChangeOutputs ≠ swap.amount) :
    ∀ u, validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  intro u hOk
  unfold validateSwapPsbt at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · cases hDest : extractSwapDestOutput crypto swap.mode validated.displayedOutputs with
      | error e => rw [hDest] at hOk; contradiction
      | ok destOut =>
          rw [hDest] at hOk
          simp only at hOk
          cases hFee : validated.fee with
          | none => rw [hFee] at hOk; contradiction
          | some actualFee =>
              rw [hFee] at hOk
              simp only at hOk
              split at hOk
              · contradiction
              · have hNe : ((validated.sumOutputs - validated.sumChangeOutputs) != swap.amount) = true :=
                  bne_eq_true_of_ne hAmtMismatch
                simp only [hNe, Bool.true_or, ↓reduceIte] at hOk
                contradiction

/-- **THEOREM 5c (Swap Mode Rejects Recipient Address Mismatch)**:
    In standard Swap mode, if the displayed external output's formatted address differs from
    `swap.destinationAddress`, `validateSwapPsbt` strictly fails. -/
theorem swap_rejects_recipient_mismatch
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (idx : Nat) (destOut : PsbtOutput)
    (hStd : swap.mode = .standard)
    (hOuts : validated.displayedOutputs = [(idx, destOut)])
    (hAddrMismatch : ∀ spk, destOut.scriptPubKey = some spk → crypto.formatAddress spk ≠ some swap.destinationAddress) :
    ∀ u, validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  intro u hOk
  unfold validateSwapPsbt at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · have hDest : extractSwapDestOutput crypto swap.mode validated.displayedOutputs = .ok destOut := by
        simp [extractSwapDestOutput, hStd, hOuts]
      rw [hDest] at hOk
      simp only at hOk
      cases hFee : validated.fee with
      | none => rw [hFee] at hOk; contradiction
      | some actualFee =>
          rw [hFee] at hOk
          simp only at hOk
          split at hOk
          · contradiction
          · split at hOk
            · contradiction
            · split at hOk
              · contradiction
              · cases hSpk : destOut.scriptPubKey with
                | none => rw [hSpk] at hOk; contradiction
                | some destSpk =>
                    rw [hSpk] at hOk
                    simp only at hOk
                    have hMis := hAddrMismatch destSpk hSpk
                    cases hFmt : crypto.formatAddress destSpk with
                    | none =>
                        rw [hFmt] at hOk
                        contradiction
                    | some addrStr =>
                        rw [hFmt] at hOk hMis
                        have hStrNe : addrStr ≠ swap.destinationAddress := fun hEq => hMis (congrArg some hEq)
                        have hBne : (some addrStr != some swap.destinationAddress) = true := by
                          simp [bne, hStrNe]
                        rw [hBne] at hOk
                        contradiction

/-- **THEOREM 5d (Swap Mode Rejects Extra External Outputs)**:
    In standard Swap mode, if `displayedOutputs` has length `!= 1` (e.g., an attacker injects a
    second external output or an unverified fake-change output), `validateSwapPsbt` fails. -/
theorem swap_standard_rejects_extra_external_outputs
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (hStd : swap.mode = .standard)
    (hLen : validated.displayedOutputs.length ≠ 1) :
    ∀ u, validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  intro u hOk
  have hExtErr : extractSwapDestOutput crypto swap.mode validated.displayedOutputs = .error .swapOutputCountMismatch := by
    rw [hStd]
    unfold extractSwapDestOutput
    cases hD : validated.displayedOutputs with
    | nil => rfl
    | cons x xs =>
        cases xs with
        | nil =>
            rw [hD] at hLen
            simp at hLen
        | cons y ys => rfl
  unfold validateSwapPsbt at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · rw [hExtErr] at hOk
      contradiction

/-- **THEOREM 6 (BIP-370 Locktime Rejects Conflicts & Ignores Fallback When Any Input Constrains Locktime)**: -/
theorem bip370_locktime_conflict_rejected
    (fallback : Option UInt32)
    (inHeightOnly inTimeOnly : PsbtInput)
    (hValid1 : validateInputLocktimeFields inHeightOnly = true)
    (hValid2 : validateInputLocktimeFields inTimeOnly = true)
    (hH : inHeightOnly.requiredHeightLocktime = some 100 ∧ inHeightOnly.requiredTimeLocktime = none)
    (hT : inTimeOnly.requiredTimeLocktime = some 600000000 ∧ inTimeOnly.requiredHeightLocktime = none) :
    determineLocktime fallback [inHeightOnly, inTimeOnly] = .error .locktimeConflictOrInvalid := by
  unfold determineLocktime
  simp [hValid1, hValid2, hH.1, hH.2, hT.1, hT.2]

theorem bip370_locktime_ignores_fallback_when_constrained
    (fb1 fb2 : Option UInt32)
    (inp : PsbtInput)
    (hReq : inp.requiredHeightLocktime = some 800000)
    (hNoTime : inp.requiredTimeLocktime = none) :
    determineLocktime fb1 [inp] = .ok 800000 ∧
    determineLocktime fb1 [inp] = determineLocktime fb2 [inp] := by
  have hVal : validateInputLocktimeFields inp = true := by
    simp [validateInputLocktimeFields, hReq, hNoTime, LOCKTIME_THRESHOLD]
  simp [determineLocktime, hVal, hReq, hNoTime]

/-- **THEOREM 7 (PSBTv0-to-PSBTv2 Normalization Rejects Non-Empty `scriptSig`)**: -/
theorem psbt_v0_nonempty_scriptsig_rejected
    (v0 : PsbtV0)
    (hVer : v0.version = none)
    (hNoWit : v0.unsignedTxHasWitness = false)
    (hNoV2 : v0.hasV2ExclusiveGlobals = false)
    (txin : RawTxIn)
    (hVin : v0.unsignedTx.vin = #[txin])
    (hNonEmpty : txin.scriptSig.size ≠ 0) :
    normalizePsbtV0ToV2 v0 = .error .psbtV0NonEmptyScriptSig := by
  unfold normalizePsbtV0ToV2
  have hSigNe : (txin.scriptSig.size != 0) = true := bne_eq_true_of_ne hNonEmpty
  simp [hVer, hNoWit, hNoV2, hVin, hSigNe]

/-- **THEOREM 8 (Non-Vacuity Witness: Valid Standard Taproot Swap PSBT Succeeds End-to-End)**:
    Proves that `authorizePsbtSigning` (covering `validatePsbt` + `validateSwapPsbt`) is non-vacuous
    and accepts a concrete valid transaction with verified change and recipient output. -/
theorem non_vacuity_valid_swap_psbt_accepted :
    ∃ (crypto : CryptoOracles) (policy : WalletPolicySpec) (psbt : PsbtTx) (swap : SwapParams) (res : ValidatedPsbt),
      authorizePsbtSigning crypto {} policy psbt (some swap) = .ok res ∧
      res.fee = some 1 ∧
      res.displayedOutputs.length = 1 ∧
      res.changeOutputs.length = 1 := by
  let dummyHash : ByteArray → Bytes32 := fun _ => zeroBytes32
  let inSpk    := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x11)
  let chgSpk   := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x22)
  let destSpk  := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x33)
  let crypto : CryptoOracles := {
    sha256 := dummyHash
    hash160 := fun _ => ByteArray.mk (Array.replicate 20 0)
    formatAddress := fun spk =>
      if byteAt? spk 2 == some 0x33 then some "bc1pdest"
      else if byteAt? spk 2 == some 0x22 then some "bc1pchg"
      else if byteAt? spk 2 == some 0x11 then some "bc1pin"
      else none
  }
  let orig : KeyOrigin := { fingerprint := 1, path := [86] }
  let policy : WalletPolicySpec := {
    isDefault := true
    name := ""
    spendClass := .taprootV1
    internalPlaceholders := [{
      keyIndex := 0
      expectedOrigin := some orig
      numFirst := 0
      numSecond := 1
      isMusig := false
    }]
    deriveScripts := fun isChg addrIdx =>
      if !isChg && addrIdx == 0 then some (inSpk, none, none)
      else if isChg && addrIdx == 1 then some (chgSpk, none, none)
      else none
  }
  let inp0 : PsbtInput := {
    prevout := { txid := zeroBytes32, vout := 0 }
    witnessUtxo := some { amount := 50, scriptPubKey := inSpk }
    derivations := [{
      pubkey := ByteArray.mk #[0x02]
      origin := { fingerprint := 1, path := [86, 0, 0] }
    }]
  }
  let outDest : PsbtOutput := {
    amount := 30
    scriptPubKey := some destSpk
  }
  let outChg : PsbtOutput := {
    amount := 19
    scriptPubKey := some chgSpk
    derivations := [{
      pubkey := ByteArray.mk #[0x03]
      origin := { fingerprint := 1, path := [86, 1, 1] }
    }]
  }
  let psbt : PsbtTx := {
    txVersion := 2
    fallbackLocktime := some 0
    inputs := #[inp0]
    outputs := #[outDest, outChg]
  }
  let swap : SwapParams := {
    mode := .standard
    amount := 30
    fees := 1
    destinationAddress := "bc1pdest"
  }
  let expectedValidated : ValidatedPsbt := {
    locktime := 0
    validatedInputs := #[({ prevoutTxOut := { amount := 50, scriptPubKey := inSpk }, spendClass := .taprootV1, missingNonWitnessUtxoWarning := false }, true, SIGHASH_DEFAULT)]
    displayedOutputs := [(0, outDest)]
    changeOutputs := [(1, outChg)]
    sumInputs := 50
    sumInternalInputs := 50
    sumOutputs := 49
    sumChangeOutputs := 19
    fee := some 1
    displayMode := .full
    warnings := {}
  }
  exact ⟨crypto, policy, psbt, swap, expectedValidated, rfl, rfl, rfl, rfl⟩

/-- **THEOREM 9a (BIP-322 Forbidden in Swap Mode)**:
    Any BIP-322 message-signing PSBT (`inSwapMode = true`) is unconditionally rejected with `.bip322ForbiddenInSwap`. -/
theorem bip322_rejected_in_swap_mode
    (sha256 : ByteArray → Bytes32)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (msg : ByteArray) :
    validateBip322Psbt sha256 true psbt validated msg = .error .bip322ForbiddenInSwap := by
  rfl

/-- **THEOREM 9b (BIP-322 Challenge `to_spend` Binding)**:
    In `validateBip322Psbt`, whenever validation succeeds, input 0's `prevout.txid` MUST equal
    `bip322ToSpendTxid sha256 msg utxo0.prevoutTxOut.scriptPubKey`, `inp0.sequence == some 0`,
    and `validated.locktime == 0`. -/
theorem bip322_enforces_to_spend_binding
    (sha256 : ByteArray → Bytes32)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (msg : ByteArray)
    (hOk : validateBip322Psbt sha256 false psbt validated msg = .ok ()) :
    validated.locktime = 0 ∧
    psbt.outputs.size = 1 ∧
    validated.changeOutputs = [] ∧
    ∃ (hIn0 : 0 < psbt.inputs.size) (hVal0 : 0 < validated.validatedInputs.size),
      (psbt.inputs[0]'hIn0).sequence = some 0 ∧
      (psbt.inputs[0]'hIn0).prevout.txid =
        bip322ToSpendTxid sha256 msg (validated.validatedInputs[0]'hVal0).1.prevoutTxOut.scriptPubKey := by
  unfold validateBip322Psbt at hOk
  simp only [ ↓reduceIte, Bool.false_eq_true] at hOk
  split at hOk
  · contradiction
  · split at hOk
    · contradiction
    · rename_i hVer hLock
      have hLockEq : validated.locktime = 0 := by
        cases hEq : decide (validated.locktime = 0)
        · simp [bne, BEq.beq, hEq] at hLock
        · exact of_decide_eq_true hEq
      split at hOk
      · contradiction
      · rename_i hOutCnt
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
                   not_or, Decidable.not_not] at hOutCnt
        split at hOk
        · rename_i hOut0
          split at hOk
          · contradiction
          · split at hOk
            · contradiction
            · split at hOk
              · rename_i hIn0
                rcases hIn0 with ⟨hI0, hV0⟩
                split at hOk
                · contradiction
                · rename_i hSeq0
                  have hSeqEq : (psbt.inputs[0]'hI0).sequence = some 0 := by
                    cases hS : (psbt.inputs[0]'hI0).sequence with
                    | none =>
                        rw [hS] at hSeq0
                        simp at hSeq0
                    | some sVal =>
                        rw [hS] at hSeq0
                        have hsEq : sVal = 0 :=
                          Decidable.byContradiction (fun hNe => by simp [bne, hNe] at hSeq0)
                        subst hsEq
                        rfl
                  split at hOk
                  · contradiction
                  · split at hOk
                    · contradiction
                    · rename_i hTxid0
                      have hTxidEq : (psbt.inputs[0]'hI0).prevout.txid =
                          bip322ToSpendTxid sha256 msg (validated.validatedInputs[0]'hV0).1.prevoutTxOut.scriptPubKey :=
                        Decidable.byContradiction (fun hNe => hTxid0 (bne_eq_true_of_ne hNe))
                      exact ⟨hLockEq, hOutCnt.1, hOutCnt.2, hI0, hV0, hSeqEq, hTxidEq⟩
              · contradiction
        · contradiction

/-- **THEOREM 10 (Non-Vacuity Witness: Valid BIP-322 Message-Signing PSBT Succeeds End-to-End)**: -/
theorem non_vacuity_valid_bip322_psbt_accepted :
    ∃ (crypto : CryptoOracles) (policy : WalletPolicySpec) (psbt : PsbtTx) (res : ValidatedPsbt),
      psbt.bip322Message = some ("Hello Ledger".toUTF8) ∧
      authorizePsbtSigning crypto {} policy psbt none = .ok res := by
  let dummyHash : ByteArray → Bytes32 := fun _ => zeroBytes32
  let inSpk := ByteArray.mk (#[0x51, 0x20] ++ Array.replicate 32 0x11)
  let crypto : CryptoOracles := {
    sha256 := dummyHash
    hash160 := fun _ => ByteArray.mk (Array.replicate 20 0)
    formatAddress := fun _ => some "bc1ptest"
  }
  let orig : KeyOrigin := { fingerprint := 1, path := [86] }
  let policy : WalletPolicySpec := {
    isDefault := true
    name := ""
    spendClass := .taprootV1
    internalPlaceholders := [{
      keyIndex := 0
      expectedOrigin := some orig
      numFirst := 0
      numSecond := 1
      isMusig := false
    }]
    deriveScripts := fun isChg addrIdx =>
      if !isChg && addrIdx == 0 then some (inSpk, none, none) else none
  }
  let msg := "Hello Ledger".toUTF8
  let inp0 : PsbtInput := {
    prevout := { txid := zeroBytes32, vout := 0 }
    sequence := some 0
    witnessUtxo := some { amount := 0, scriptPubKey := inSpk }
    derivations := [{
      pubkey := ByteArray.mk #[0x02]
      origin := { fingerprint := 1, path := [86, 0, 0] }
    }]
  }
  let out0 : PsbtOutput := {
    amount := 0
    scriptPubKey := some (ByteArray.mk #[0x6a])
  }
  let psbt : PsbtTx := {
    txVersion := 0
    fallbackLocktime := some 0
    inputs := #[inp0]
    outputs := #[out0]
    bip322Message := some msg
  }
  let expectedValidated : ValidatedPsbt := {
    locktime := 0
    validatedInputs := #[({ prevoutTxOut := { amount := 0, scriptPubKey := inSpk }, spendClass := .taprootV1, missingNonWitnessUtxoWarning := false }, true, SIGHASH_DEFAULT)]
    displayedOutputs := [(0, out0)]
    changeOutputs := []
    sumInputs := 0
    sumInternalInputs := 0
    sumOutputs := 0
    sumChangeOutputs := 0
    fee := some 0
    displayMode := .full
    warnings := {}
  }
  exact ⟨crypto, policy, psbt, expectedValidated, rfl, rfl⟩

end Spec.Psbt

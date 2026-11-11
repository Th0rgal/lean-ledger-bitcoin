import InternalSpec

namespace BitcoinLedger.Basic

/-!
# `BitcoinLedger.Basic` — Executable Foundational Bitcoin & Ledger Primitives

Pure, constructive, overflow-safe Lean 4 implementation refining `InternalSpec.Basic`:
1. Fixed-width `UInt64` satoshi arithmetic (`SATS_PER_BTC`, `MAX_MONEY`, `isValidAmount`,
   `checkedAddSats?`, `checkedSubSats?`, `checkedSumSats?`) avoiding unbounded runtime `Nat`
   addition/wraparound via subtraction-bounded `UInt64` checks (`b ≤ MAX_MONEY - a`).
2. Fixed-width byte-slice validators (`isBytesN`, `isBytes4`, `isBytes20`, `isBytes32`,
   `isBytes33`, `isBytes64`, `isBytes65`) and constructive byte-array equality (`eqBytes`).
3. Bitwise shift/mask little-endian & big-endian integer codecs (`encodeU16LE`, `decodeU16LE?`,
   `encodeU32LE`, `decodeU32LE?`, `encodeU64LE`, `decodeU64LE?`, `encodeU32BE`, `decodeU32BE?`).
4. Canonical Bitcoin CompactSize / VarInt byte-length calculator, encoder, and decoders
   (`varIntByteLen`, `encodeVarInt`, `decodeVarIntCanonical?`, `decodeVarIntCanonicalPrefix?`).
5. Bitcoin network parameters (`Mainnet`, `Testnet`, `Regtest`, `Signet`).
6. Deterministic Ledger error mappings (`SpecError` ↔ BOLOS status word `UInt16`,
   `BolosErrorCode`, and Vanadium `AppError` CBOR code).
-/

/-! ### Constructive `BEq` Instances (`0 Classical.choice`) -/
local instance (priority := high) : BEq UInt8 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt16 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt32 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt64 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : LawfulBEq UInt8 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt16 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt32 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt64 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-! ## 1. Satoshi Amounts & Fixed-Width Overflow-Safe `UInt64` Arithmetic -/

/-- Number of satoshis per BTC (`100_000_000`). -/
def SATS_PER_BTC : UInt64 := 100_000_000

/-- Consensus maximum Bitcoin supply in satoshis (`21_000_000 * 100_000_000 = 2_100_000_000_000_000`). -/
def MAX_MONEY : UInt64 := 2_100_000_000_000_000

/-- Fixed-width `UInt64` check for whether `a` is a consensus-valid satoshi amount (`a ≤ MAX_MONEY`). -/
def isValidAmount (a : UInt64) : Bool :=
  decide (a ≤ MAX_MONEY)

/-- Overflow-safe fixed-width `UInt64` addition of two satoshi amounts.
    Checks `a ≤ MAX_MONEY` and `b ≤ MAX_MONEY - a` in `UInt64` hardware registers without
    allocating unbounded `Nat` bignums or risking `2^64` wraparound. -/
def checkedAddSats? (a b : UInt64) : Option UInt64 :=
  if decide (a ≤ MAX_MONEY) && decide (b ≤ MAX_MONEY - a) then
    some (a + b)
  else
    none

/-- Overflow-safe fixed-width `UInt64` subtraction of satoshi amounts (`total - part`),
    enforcing `total ≤ MAX_MONEY` and `part ≤ total`. -/
def checkedSubSats? (total part : UInt64) : Option UInt64 :=
  if decide (total ≤ MAX_MONEY) && decide (part ≤ total) then
    some (total - part)
  else
    none

/-- Tail-recursive `UInt64` accumulator helper for `checkedSumSats?`. -/
def checkedSumSatsLoop (acc : UInt64) : List UInt64 → Option UInt64
  | [] => some acc
  | x :: xs =>
      match checkedAddSats? acc x with
      | none => none
      | some acc' => checkedSumSatsLoop acc' xs

/-- Overflow-safe tail-recursive `UInt64` summation over a list of satoshi amounts. -/
def checkedSumSats? (xs : List UInt64) : Option UInt64 :=
  checkedSumSatsLoop 0 xs

/-- Overflow-safe summation over an `Array UInt64` of satoshi amounts. -/
def checkedSumSatsArray? (xs : Array UInt64) : Option UInt64 :=
  checkedSumSats? xs.toList

/-! ## 2. Fixed-Width Byte-Slice Validators & Constructive Byte Equality -/

/-- Pure structural byte-list equality (`0 Classical.choice`, avoids `@[extern] ByteArray.beq`). -/
def eqByteList : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && eqByteList xs ys
  | _, _ => false

/-- Pure structural `ByteArray` equality (`0 Classical.choice`). -/
def eqBytes (a b : ByteArray) : Bool :=
  eqByteList a.data.toList b.data.toList

/-- Executable validator checking whether `bs` has exact byte length `n`. -/
def isBytesN (n : Nat) (bs : ByteArray) : Bool :=
  decide (bs.size = n)

/-- 4-byte slice validator (BIP-32 fingerprint, version magic, Base58Check checksum). -/
def isBytes4 (bs : ByteArray) : Bool := isBytesN 4 bs

/-- 20-byte slice validator (`HASH160` for P2PKH, P2SH, P2WPKH). -/
def isBytes20 (bs : ByteArray) : Bool := isBytesN 20 bs

/-- 32-byte slice validator (`SHA256`, txid, chain code, Taproot x-only key, P2WSH). -/
def isBytes32 (bs : ByteArray) : Bool := isBytesN 32 bs

/-- 33-byte slice validator (SEC1 compressed secp256k1 public key). -/
def isBytes33 (bs : ByteArray) : Bool := isBytesN 33 bs

/-- 64-byte slice validator (BIP-340 Schnorr signature or compact ECDSA `(r, s)`). -/
def isBytes64 (bs : ByteArray) : Bool := isBytesN 64 bs

/-- 65-byte slice validator (SEC1 uncompressed secp256k1 public key). -/
def isBytes65 (bs : ByteArray) : Bool := isBytesN 65 bs

/-! ## 3. Little-Endian & Big-Endian Fixed-Width Integer Codecs -/

/-- 2-byte little-endian encoder for `UInt16` using fixed-width shifts. -/
def encodeU16LE (v : UInt16) : ByteArray :=
  ByteArray.mk #[
    v.toUInt8,
    (v >>> 8).toUInt8
  ]

/-- 2-byte little-endian decoder for `UInt16` (requires exact length 2). -/
def decodeU16LE? (bs : ByteArray) : Option UInt16 :=
  match bs.data.toList with
  | [b0, b1] =>
      some (b0.toUInt16 ||| (b1.toUInt16 <<< 8))
  | _ => none

/-- 4-byte little-endian encoder for `UInt32` using fixed-width shifts. -/
def encodeU32LE (v : UInt32) : ByteArray :=
  ByteArray.mk #[
    v.toUInt8,
    (v >>> 8).toUInt8,
    (v >>> 16).toUInt8,
    (v >>> 24).toUInt8
  ]

/-- 4-byte little-endian decoder for `UInt32` (requires exact length 4). -/
def decodeU32LE? (bs : ByteArray) : Option UInt32 :=
  match bs.data.toList with
  | [b0, b1, b2, b3] =>
      some (
        b0.toUInt32 |||
        (b1.toUInt32 <<< 8) |||
        (b2.toUInt32 <<< 16) |||
        (b3.toUInt32 <<< 24)
      )
  | _ => none

/-- 8-byte little-endian encoder for `UInt64` using fixed-width shifts. -/
def encodeU64LE (v : UInt64) : ByteArray :=
  ByteArray.mk #[
    v.toUInt8,
    (v >>> 8).toUInt8,
    (v >>> 16).toUInt8,
    (v >>> 24).toUInt8,
    (v >>> 32).toUInt8,
    (v >>> 40).toUInt8,
    (v >>> 48).toUInt8,
    (v >>> 56).toUInt8
  ]

/-- 8-byte little-endian decoder for `UInt64` (requires exact length 8). -/
def decodeU64LE? (bs : ByteArray) : Option UInt64 :=
  match bs.data.toList with
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
      some (
        b0.toUInt64 |||
        (b1.toUInt64 <<< 8) |||
        (b2.toUInt64 <<< 16) |||
        (b3.toUInt64 <<< 24) |||
        (b4.toUInt64 <<< 32) |||
        (b5.toUInt64 <<< 40) |||
        (b6.toUInt64 <<< 48) |||
        (b7.toUInt64 <<< 56)
      )
  | _ => none

/-- 4-byte big-endian encoder for `UInt32` (BIP-32 paths, fingerprints, xpub versions). -/
def encodeU32BE (v : UInt32) : ByteArray :=
  ByteArray.mk #[
    (v >>> 24).toUInt8,
    (v >>> 16).toUInt8,
    (v >>> 8).toUInt8,
    v.toUInt8
  ]

/-- 4-byte big-endian decoder for `UInt32` (requires exact length 4). -/
def decodeU32BE? (bs : ByteArray) : Option UInt32 :=
  match bs.data.toList with
  | [b0, b1, b2, b3] =>
      some (
        (b0.toUInt32 <<< 24) |||
        (b1.toUInt32 <<< 16) |||
        (b2.toUInt32 <<< 8) |||
        b3.toUInt32
      )
  | _ => none

/-! ## 4. Canonical Bitcoin CompactSize / VarInt Codec -/

/-- Exact encoded byte length (`1`, `3`, `5`, or `9`) of canonical CompactSize for `n : UInt64`. -/
def varIntByteLen (n : UInt64) : Nat :=
  if decide (n ≤ 0xFC) then 1
  else if decide (n ≤ 0xFFFF) then 3
  else if decide (n ≤ 0xFFFFFFFF) then 5
  else 9

/-- Canonical Bitcoin CompactSize / VarInt encoder using fixed-width `UInt64` shifts. -/
def encodeVarInt (n : UInt64) : ByteArray :=
  if decide (n ≤ 0xFC) then
    ByteArray.mk #[n.toUInt8]
  else if decide (n ≤ 0xFFFF) then
    ByteArray.mk #[
      0xFD,
      n.toUInt8,
      (n >>> 8).toUInt8
    ]
  else if decide (n ≤ 0xFFFFFFFF) then
    ByteArray.mk #[
      0xFE,
      n.toUInt8,
      (n >>> 8).toUInt8,
      (n >>> 16).toUInt8,
      (n >>> 24).toUInt8
    ]
  else
    ByteArray.mk #[
      0xFF,
      n.toUInt8,
      (n >>> 8).toUInt8,
      (n >>> 16).toUInt8,
      (n >>> 24).toUInt8,
      (n >>> 32).toUInt8,
      (n >>> 40).toUInt8,
      (n >>> 48).toUInt8,
      (n >>> 56).toUInt8
    ]

/-- Canonical Bitcoin CompactSize / VarInt decoder over an exact byte slice.
    Rejects truncated inputs, trailing bytes, and non-minimal encodings
    (`0xFD` `< 0xFD`, `0xFE` `< 0x10000`, `0xFF` `< 0x100000000`). -/
def decodeVarIntCanonical? (bs : ByteArray) : Option UInt64 :=
  match bs.data.toList with
  | [b0] =>
      if decide (b0 ≤ 0xFC) then
        some b0.toUInt64
      else
        none
  | [tag, b0, b1] =>
      if decide (tag = 0xFD) then
        let val : UInt64 := b0.toUInt64 ||| (b1.toUInt64 <<< 8)
        if decide (0xFD ≤ val) then
          some val
        else
          none
      else
        none
  | [tag, b0, b1, b2, b3] =>
      if decide (tag = 0xFE) then
        let val : UInt64 :=
          b0.toUInt64 |||
          (b1.toUInt64 <<< 8) |||
          (b2.toUInt64 <<< 16) |||
          (b3.toUInt64 <<< 24)
        if decide (0x10000 ≤ val) then
          some val
        else
          none
      else
        none
  | [tag, b0, b1, b2, b3, b4, b5, b6, b7] =>
      if decide (tag = 0xFF) then
        let val : UInt64 :=
          b0.toUInt64 |||
          (b1.toUInt64 <<< 8) |||
          (b2.toUInt64 <<< 16) |||
          (b3.toUInt64 <<< 24) |||
          (b4.toUInt64 <<< 32) |||
          (b5.toUInt64 <<< 40) |||
          (b6.toUInt64 <<< 48) |||
          (b7.toUInt64 <<< 56)
        if decide (0x100000000 ≤ val) then
          some val
        else
          none
      else
        none
  | _ => none

/-- Streaming canonical CompactSize / VarInt prefix decoder returning `(value, remainingBytes)`. -/
def decodeVarIntCanonicalPrefix? (bs : ByteArray) : Option (UInt64 × ByteArray) :=
  match bs.data.toList with
  | [] => none
  | tag :: _ =>
      let needed : Nat :=
        if decide (tag ≤ 0xFC) then 1
        else if decide (tag = 0xFD) then 3
        else if decide (tag = 0xFE) then 5
        else 9
      if decide (bs.size < needed) then
        none
      else
        let head := bs.extract 0 needed
        let tail := bs.extract needed bs.size
        match decodeVarIntCanonical? head with
        | some v => some (v, tail)
        | none => none

/-! ## 5. Bitcoin Network Parameters -/

abbrev Network := InternalSpec.Network
abbrev NetworkParams := InternalSpec.NetworkParams

def Mainnet : Network := .mainnet
def Testnet : Network := .testnet
def Regtest : Network := .regtest
def Signet  : Network := .signet

def XPUB_VERSION_MAINNET : UInt32 := 0x0488B21E
def XPUB_VERSION_TESTNET : UInt32 := 0x043587CF

/-- Retrieve consensus and address/key-encoding parameters for a `Network`. -/
def networkParams : Network → NetworkParams
  | .mainnet =>
      { p2pkhVersion := 0x00
        p2shVersion := 0x05
        bech32Hrp := "bc"
        silentPaymentHrp := "sp"
        xpubVersion := XPUB_VERSION_MAINNET
        bip44CoinType := 0
        bip44CoinTypeHardened := 0x80000000 }
  | .testnet =>
      { p2pkhVersion := 0x6F
        p2shVersion := 0xC4
        bech32Hrp := "tb"
        silentPaymentHrp := "tsp"
        xpubVersion := XPUB_VERSION_TESTNET
        bip44CoinType := 1
        bip44CoinTypeHardened := 0x80000001 }
  | .regtest =>
      { p2pkhVersion := 0x6F
        p2shVersion := 0xC4
        bech32Hrp := "bcrt"
        silentPaymentHrp := "tsp"
        xpubVersion := XPUB_VERSION_TESTNET
        bip44CoinType := 1
        bip44CoinTypeHardened := 0x80000001 }
  | .signet =>
      { p2pkhVersion := 0x6F
        p2shVersion := 0xC4
        bech32Hrp := "tb"
        silentPaymentHrp := "tsp"
        xpubVersion := XPUB_VERSION_TESTNET
        bip44CoinType := 1
        bip44CoinTypeHardened := 0x80000001 }

/-! ## 6. Canonical Ledger Error Mappings (`SpecError` ↔ BOLOS `SW` & Vanadium `AppError`) -/

abbrev BolosStatusWord := InternalSpec.BolosStatusWord
abbrev BolosErrorDomain := InternalSpec.BolosErrorDomain
abbrev BolosErrorCode := InternalSpec.BolosErrorCode
abbrev BolosErrorResponse := InternalSpec.BolosErrorResponse
abbrev AppError := InternalSpec.AppError
abbrev SpecError := InternalSpec.SpecError

/-- Encode a `BolosStatusWord` into its 16-bit ISO-7816 / Ledger APDU status word. -/
def bolosStatusWordToU16 : BolosStatusWord → UInt16
  | .swWrongLength                => 0x6700
  | .swSecurityStatusNotSatisfied => 0x6982
  | .swDeny                       => 0x6985
  | .swIncorrectData              => 0x6A80
  | .swNotSupported               => 0x6A82
  | .swWrongP1P2                  => 0x6A86
  | .swWrongDataLength            => 0x6A87
  | .swFailSwap                   => 0x6B00
  | .swInsNotSupported            => 0x6D00
  | .swClaNotSupported            => 0x6E00
  | .swWrongResponseLength        => 0xB000
  | .swDisplayBip32PathFail       => 0xB001
  | .swDisplayAddressFail         => 0xB002
  | .swDisplayAmountFail          => 0xB003
  | .swWrongTxLength              => 0xB004
  | .swTxParsingFail              => 0xB005
  | .swTxHashFail                 => 0xB006
  | .swBadState                   => 0xB007
  | .swSignatureFail              => 0xB008
  | .swInterruptedExecution       => 0xE000
  | .swOk                         => 0x9000

/-- Decode a 16-bit APDU status word into `BolosStatusWord`. -/
def bolosStatusWordFromU16? : UInt16 → Option BolosStatusWord
  | 0x6700 => some .swWrongLength
  | 0x6982 => some .swSecurityStatusNotSatisfied
  | 0x6985 => some .swDeny
  | 0x6A80 => some .swIncorrectData
  | 0x6A82 => some .swNotSupported
  | 0x6A86 => some .swWrongP1P2
  | 0x6A87 => some .swWrongDataLength
  | 0x6B00 => some .swFailSwap
  | 0x6D00 => some .swInsNotSupported
  | 0x6E00 => some .swClaNotSupported
  | 0xB000 => some .swWrongResponseLength
  | 0xB001 => some .swDisplayBip32PathFail
  | 0xB002 => some .swDisplayAddressFail
  | 0xB003 => some .swDisplayAmountFail
  | 0xB004 => some .swWrongTxLength
  | 0xB005 => some .swTxParsingFail
  | 0xB006 => some .swTxHashFail
  | 0xB007 => some .swBadState
  | 0xB008 => some .swSignatureFail
  | 0xE000 => some .swInterruptedExecution
  | 0x9000 => some .swOk
  | _      => none

/-- Encode Vanadium `AppError` into its CBOR `#[n(0..58)]` discriminant as `UInt8`. -/
def appErrorToCborU8 : AppError → UInt8
  | .invalidRequest                    => 0
  | .invalidParameter                  => 1
  | .invalidWalletPolicy               => 2
  | .defaultAccountsNotSupported       => 3
  | .invalidProofOfRegistrationLength  => 4
  | .invalidProofOfRegistration        => 5
  | .invalidAccountId                  => 6
  | .invalidKeyIndex                   => 7
  | .invalidScriptContext              => 8
  | .tooManyKeys                       => 9
  | .invalidMultisigQuorum             => 10
  | .unsupportedWalletPolicy           => 11
  | .derivationPathTooLong             => 12
  | .keyDerivationFailed               => 13
  | .hardenedDerivationNotSupported    => 14
  | .invalidKey                        => 15
  | .errorComputingSighash             => 16
  | .signingFailed                     => 17
  | .failedToDeserializePsbt           => 18
  | .failedToGetAccounts               => 19
  | .externalInputsNotSupported        => 20
  | .witnessUtxoNotAllowedForLegacy    => 21
  | .invalidNonWitnessUtxo             => 22
  | .nonWitnessUtxoMismatch            => 23
  | .nonWitnessUtxoRequired            => 24
  | .witnessUtxoRequiredForSegwit      => 25
  | .invalidWitnessUtxo                => 26
  | .redeemScriptMismatchWitness       => 27
  | .witnessScriptRequiredForP2WSH     => 28
  | .witnessScriptMismatchWitness      => 29
  | .redeemScriptMismatch              => 30
  | .missingPreviousOutputIndex        => 31
  | .missingInputUtxo                  => 32
  | .inputScriptMismatch               => 33
  | .outputScriptMissing               => 34
  | .outputAmountMissing               => 35
  | .outputScriptMismatch              => 36
  | .inputsLessThanOutputs             => 37
  | .failedUnsignedTransaction         => 38
  | .addressFromScriptFailed           => 39
  | .invalidIdentitySignature          => 40
  | .identityMessageFieldTooLong       => 41
  | .unexpectedTaprootPolicy           => 42
  | .unexpectedSegwitVersion           => 43
  | .storageError                      => 44
  | .userRejected                      => 45
  | .missingMusigSession               => 46
  | .missingMusigPubnonce              => 47
  | .unsupportedSilentPayment          => 48
  | .unsupportedSighashType            => 49
  | .invalidSilentPayment              => 50
  | .silentPaymentInputNotHeld         => 51
  | .silentPaymentNoEligibleInputs     => 52
  | .silentPaymentSegwitVersion        => 53
  | .silentPaymentSighashType          => 54
  | .silentPaymentShareMismatch        => 55
  | .silentPaymentOutputScriptMismatch => 56
  | .silentPaymentAccountKeyMismatch   => 57
  | .silentPaymentChangeLabel          => 58

/-- Decode a Vanadium CBOR `UInt8` discriminant (`0..58`) into `AppError`. -/
def appErrorFromCborU8? : UInt8 → Option AppError
  | 0  => some .invalidRequest
  | 1  => some .invalidParameter
  | 2  => some .invalidWalletPolicy
  | 3  => some .defaultAccountsNotSupported
  | 4  => some .invalidProofOfRegistrationLength
  | 5  => some .invalidProofOfRegistration
  | 6  => some .invalidAccountId
  | 7  => some .invalidKeyIndex
  | 8  => some .invalidScriptContext
  | 9  => some .tooManyKeys
  | 10 => some .invalidMultisigQuorum
  | 11 => some .unsupportedWalletPolicy
  | 12 => some .derivationPathTooLong
  | 13 => some .keyDerivationFailed
  | 14 => some .hardenedDerivationNotSupported
  | 15 => some .invalidKey
  | 16 => some .errorComputingSighash
  | 17 => some .signingFailed
  | 18 => some .failedToDeserializePsbt
  | 19 => some .failedToGetAccounts
  | 20 => some .externalInputsNotSupported
  | 21 => some .witnessUtxoNotAllowedForLegacy
  | 22 => some .invalidNonWitnessUtxo
  | 23 => some .nonWitnessUtxoMismatch
  | 24 => some .nonWitnessUtxoRequired
  | 25 => some .witnessUtxoRequiredForSegwit
  | 26 => some .invalidWitnessUtxo
  | 27 => some .redeemScriptMismatchWitness
  | 28 => some .witnessScriptRequiredForP2WSH
  | 29 => some .witnessScriptMismatchWitness
  | 30 => some .redeemScriptMismatch
  | 31 => some .missingPreviousOutputIndex
  | 32 => some .missingInputUtxo
  | 33 => some .inputScriptMismatch
  | 34 => some .outputScriptMissing
  | 35 => some .outputAmountMissing
  | 36 => some .outputScriptMismatch
  | 37 => some .inputsLessThanOutputs
  | 38 => some .failedUnsignedTransaction
  | 39 => some .addressFromScriptFailed
  | 40 => some .invalidIdentitySignature
  | 41 => some .identityMessageFieldTooLong
  | 42 => some .unexpectedTaprootPolicy
  | 43 => some .unexpectedSegwitVersion
  | 44 => some .storageError
  | 45 => some .userRejected
  | 46 => some .missingMusigSession
  | 47 => some .missingMusigPubnonce
  | 48 => some .unsupportedSilentPayment
  | 49 => some .unsupportedSighashType
  | 50 => some .invalidSilentPayment
  | 51 => some .silentPaymentInputNotHeld
  | 52 => some .silentPaymentNoEligibleInputs
  | 53 => some .silentPaymentSegwitVersion
  | 54 => some .silentPaymentSighashType
  | 55 => some .silentPaymentShareMismatch
  | 56 => some .silentPaymentOutputScriptMismatch
  | 57 => some .silentPaymentAccountKeyMismatch
  | 58 => some .silentPaymentChangeLabel
  | _  => none

/-- Deterministic mapping from `SpecError` to `BolosStatusWord`. -/
def specErrorToBolosSw : SpecError → BolosStatusWord
  | .wrongLength                => .swWrongLength
  | .wrongDataLength            => .swWrongDataLength
  | .unsupportedInstruction     => .swInsNotSupported
  | .unsupportedClass           => .swClaNotSupported
  | .wrongP1P2                  => .swWrongP1P2
  | .userRejected               => .swDeny
  | .securityStatusNotSatisfied => .swSecurityStatusNotSatisfied
  | .swapValidationFailed       => .swFailSwap
  | .invalidData                => .swIncorrectData
  | .bip32PathTooLong           => .swIncorrectData
  | .unsupportedBip32Path       => .swNotSupported
  | .notSupported               => .swNotSupported
  | .invalidAmount              => .swIncorrectData
  | .invalidScriptOrAddress     => .swIncorrectData
  | .invalidWalletPolicy        => .swIncorrectData
  | .invalidPsbt                => .swIncorrectData
  | .badState                   => .swBadState
  | .wrongResponseLength        => .swWrongResponseLength
  | .cryptoOrSignatureFailed    => .swSignatureFail

/-- Deterministic mapping from `SpecError` to BOLOS 16-bit APDU status word (`UInt16`). -/
def specErrorToBolosU16 (err : SpecError) : UInt16 :=
  bolosStatusWordToU16 (specErrorToBolosSw err)

/-- Deterministic mapping from `SpecError` to Vanadium `AppError`. -/
def specErrorToVanadiumError : SpecError → AppError
  | .wrongLength                => .invalidRequest
  | .wrongDataLength            => .invalidRequest
  | .unsupportedInstruction     => .invalidRequest
  | .unsupportedClass           => .invalidRequest
  | .wrongP1P2                  => .invalidParameter
  | .userRejected               => .userRejected
  | .securityStatusNotSatisfied => .invalidProofOfRegistration
  | .swapValidationFailed       => .invalidRequest
  | .invalidData                => .invalidParameter
  | .bip32PathTooLong           => .derivationPathTooLong
  | .unsupportedBip32Path       => .keyDerivationFailed
  | .notSupported               => .unsupportedWalletPolicy
  | .invalidAmount              => .inputsLessThanOutputs
  | .invalidScriptOrAddress     => .addressFromScriptFailed
  | .invalidWalletPolicy        => .invalidWalletPolicy
  | .invalidPsbt                => .failedToDeserializePsbt
  | .badState                   => .missingMusigSession
  | .wrongResponseLength        => .invalidRequest
  | .cryptoOrSignatureFailed    => .signingFailed

/-- Deterministic compact 1-byte discriminant (`0..18`) for `SpecError` (used across FFI boundaries). -/
def specErrorToTag : SpecError → UInt8
  | .wrongLength                => 0
  | .wrongDataLength            => 1
  | .unsupportedInstruction     => 2
  | .unsupportedClass           => 3
  | .wrongP1P2                  => 4
  | .userRejected               => 5
  | .securityStatusNotSatisfied => 6
  | .swapValidationFailed       => 7
  | .invalidData                => 8
  | .bip32PathTooLong           => 9
  | .unsupportedBip32Path       => 10
  | .notSupported               => 11
  | .invalidAmount              => 12
  | .invalidScriptOrAddress     => 13
  | .invalidWalletPolicy        => 14
  | .invalidPsbt                => 15
  | .badState                   => 16
  | .wrongResponseLength        => 17
  | .cryptoOrSignatureFailed    => 18

/-- Partial inverse of `specErrorToTag` (`0..18`). -/
def specErrorFromTag? : UInt8 → Option SpecError
  | 0  => some .wrongLength
  | 1  => some .wrongDataLength
  | 2  => some .unsupportedInstruction
  | 3  => some .unsupportedClass
  | 4  => some .wrongP1P2
  | 5  => some .userRejected
  | 6  => some .securityStatusNotSatisfied
  | 7  => some .swapValidationFailed
  | 8  => some .invalidData
  | 9  => some .bip32PathTooLong
  | 10 => some .unsupportedBip32Path
  | 11 => some .notSupported
  | 12 => some .invalidAmount
  | 13 => some .invalidScriptOrAddress
  | 14 => some .invalidWalletPolicy
  | 15 => some .invalidPsbt
  | 16 => some .badState
  | 17 => some .wrongResponseLength
  | 18 => some .cryptoOrSignatureFailed
  | _  => none

end BitcoinLedger.Basic

import InternalSpec
import BitcoinLedger.Musig2
import BitcoinLedger.SilentPayments

/-!
# `BitcoinLedger.AppStateMachine` — Executable Top-Level Command Dispatcher & Verified `SIGN_PSBT`

Pure Lean 4 executable implementation of:
1. BOLOS APDU command classification (`CLA = 0xE1`, `0xB0`, `0xF8`, protocol version check,
   and Swap-mode command filtering) and Vanadium CBOR `Request` tag decoding.
2. Bitcoin `SIGN_MESSAGE` (`"\x18Bitcoin Signed Message:\n"`, printable ASCII vs SHA-256 display,
   double-SHA256 digest, and 65-byte compact recoverable ECDSA formatting).
3. `GET_EXTENDED_PUBKEY` path safety policy (`isPathSafeForPubkeyExport`), Vanadium `IDEN`
   identity key paths & Schnorr signatures, Proof-of-Registration HMAC validation, and
   Ledger Exchange `SwapLock` validation & terminal `swapAborted` latching on failure.
4. Unified top-level command state machine (`stepAppCommand`, `runAppTrace`) delegating MuSig2
   Round-1/Round-2 directly to `BitcoinLedger.Musig2` and Silent Payments directly to
   `BitcoinLedger.SilentPayments`.
5. End-to-end verified `SIGN_PSBT` & BIP-322 message-signing composition
   (`verifyPsbtMerkleBundle`, `buildVerifiedPsbtSignRequest`, `stepVerifiedPsbtSign`,
   `verifyPsbtSignMessage`).

Written constructively (`0 Classical.choice`) for freestanding 32-bit compilation and exact
refinement proofs in `Proofs.AppStateMachine`.
-/

namespace BitcoinLedger.AppStateMachine

open InternalSpec.Musig2 (
  CompressedPubKey SchnorrSig PsbtSessionId RandRoot
  MusigSignTask MusigRound1Output MusigRound2TaskInput MusigRound2Output
  MusigError NonceAggPkMode MusigSessionStore
)
open InternalSpec.SilentPayments (
  SpError SpAddressHrp SpScanHrp Bech32mCodec
  SilentPaymentAccount SilentPaymentCoordinates PsbtSpTx
  SilentPaymentShareOut SilentPaymentOutputScriptOut
)
open InternalSpec.AppStateMachine (
  TargetProfile AppVersion BolosApduHeader BolosWireCommand VanadiumRequestTag
  CompactSigHeaderBase MessageDisplayForm KeyTree
  IdentitySignature RegisteredIdentityEntry
  WalletPolicySpec AccountSpec AddressCoordinates
  SwapMode SwapLock ExternalOutputView
  StandardInputSigRequest StandardInputSignature PsbtMusigPlan PsbtSignRequest
  AppCommand AppResponse AppError AppPersistentState
  UserPrompt UserApprovalOracle HardwareOracle AppTraceOutcome
)
open InternalSpec.Unified (
  PsbtMerkleOpeningBundle VerifiedPsbtSignError
)

/-! ## 1. Wire Constants, Target Profiles & Byte Helpers -/

def bolosClaDefault : UInt8 := 0xB0
def bolosClaApp : UInt8 := 0xE1
def bolosClaFramework : UInt8 := 0xF8

def bolosInsGetExtendedPubkey : UInt8 := 0x00
def bolosInsGetVersion : UInt8 := 0x01
def bolosInsContinue : UInt8 := 0x01
def bolosInsRegisterWallet : UInt8 := 0x02
def bolosInsGetWalletAddress : UInt8 := 0x03
def bolosInsSignPsbt : UInt8 := 0x04
def bolosInsGetMasterFingerprint : UInt8 := 0x05
def bolosInsSignMessage : UInt8 := 0x10

def bolosCurrentProtocolVersion : UInt8 := 1

def bolosMaxBip32PathSteps : Nat := 10
def vanadiumStandardMaxBip32PathSteps : Nat := 16
def vanadiumMaxBip32PathSteps : Nat := 256

def maxBip44AccountRecommended : UInt32 := 100
def maxDefaultAddressIndex : UInt32 := 50000
def maxDisplayableMessageLength : Nat := 640
def maxSignMessageLength : Nat := 0x100000000

def hardenedFlag : UInt32 := 0x80000000
def electrumPathStep0 : UInt32 := 4541509 ||| hardenedFlag
def electrumPathStep1 : UInt32 := 1112098098 ||| hardenedFlag
def identityRootPathComponent : UInt32 := 1229210958 ||| hardenedFlag

def targetAppVersion : AppVersion :=
  { major := 2, minor := 6, patch := 0 }

/-- Extract `coinType` from `TargetProfile`. -/
def profileCoinType : TargetProfile → UInt32
  | .bolos ct => ct
  | .vanadium ct => ct

/-- Maximum BIP-32 path steps for `TargetProfile`. -/
def profileMaxPathSteps : TargetProfile → Nat
  | .bolos _ => bolosMaxBip32PathSteps
  | .vanadium _ => vanadiumMaxBip32PathSteps

/-- MuSig2 nonce `aggpk` mode for `TargetProfile`. -/
def profileMusigAggPkMode : TargetProfile → NonceAggPkMode
  | .bolos _ => .untweakedBolos
  | .vanadium _ => .tweakedVanadium

/-- BIP-392 `spscan`/`tspscan` HRP for `TargetProfile`. -/
def profileSpScanHrp (p : TargetProfile) : SpScanHrp :=
  if decide (profileCoinType p = 0) then .spscan else .tspscan

/-- Initialize target-faithful `MusigSessionStore` (`capacity=32`/`28B` on BOLOS, `capacity=1`/`32B` on Vanadium). -/
def emptyMusigStoreForProfile : TargetProfile → MusigSessionStore
  | .bolos _ => BitcoinLedger.Musig2.bolosDefaultStore
  | .vanadium _ => BitcoinLedger.Musig2.vanadiumDefaultStore

/-- Initialize empty `AppPersistentState` for `TargetProfile`. -/
def emptyStateForProfile (p : TargetProfile) : AppPersistentState :=
  { musigSessions := emptyMusigStoreForProfile p }

/-- Pure `ByteArray` concatenation. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

/-- Concatenate a list of `ByteArray`s. -/
def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl appendBytes (ByteArray.mk #[])

/-- Pure universal list check (`0 Classical.choice`). -/
def appListAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && appListAll p xs

/-- Pure list membership check (`0 Classical.choice`). -/
def appListMem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || appListMem x ys

/-- Pure existential list check (`0 Classical.choice`). -/
def appListAny {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => p x || appListAny p xs

/-- Encode 16-bit unsigned integer in little-endian. -/
def encodeU16LE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF)
  ]

/-- Encode 32-bit unsigned integer in little-endian. -/
def encodeU32LEBytes (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 24) &&& 0xFF)
  ]

/-- Encode 64-bit unsigned integer in little-endian. -/
def encodeU64LEBytes (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 24) &&& 0xFF),
    UInt8.ofNat ((n >>> 32) &&& 0xFF),
    UInt8.ofNat ((n >>> 40) &&& 0xFF),
    UInt8.ofNat ((n >>> 48) &&& 0xFF),
    UInt8.ofNat ((n >>> 56) &&& 0xFF)
  ]

/-- Bitcoin CompactSize (`varint`) encoding. -/
def encodeVarint (n : Nat) : ByteArray :=
  if decide (n < 0xFD) then
    ByteArray.mk #[UInt8.ofNat n]
  else if decide (n ≤ 0xFFFF) then
    appendBytes (ByteArray.mk #[0xFD]) (encodeU16LE n)
  else if decide (n ≤ 0xFFFFFFFF) then
    appendBytes (ByteArray.mk #[0xFE]) (encodeU32LEBytes n)
  else
    appendBytes (ByteArray.mk #[0xFF]) (encodeU64LEBytes n)

/-! ## 2. Bitcoin `SIGN_MESSAGE` Helpers (`sign_message.c` & BIP-137) -/

def bitcoinSignedMessageMagic : ByteArray :=
  ByteArray.mk #[
    0x18,
    0x42, 0x69, 0x74, 0x63, 0x6F, 0x69, 0x6E, 0x20,
    0x53, 0x69, 0x67, 0x6E, 0x65, 0x64, 0x20,
    0x4D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x3A,
    0x0A
  ]

/-- Printable ASCII check (`msg.size ≤ 640` and every byte in `0x20..0x7E` or `0x0A`). -/
def isPrintableAsciiMessage (msg : ByteArray) : Bool :=
  decide (msg.size ≤ maxDisplayableMessageLength) &&
  appListAll (fun b => (decide ((0x20 : UInt8) ≤ b) && decide (b ≤ (0x7E : UInt8))) || decide (b = 0x0A)) msg.data.toList

/-- Bitcoin Signed Message preimage: `magic || varint(msg.size) || msg`. -/
def bitcoinSignedMessagePreimage (msg : ByteArray) : ByteArray :=
  concatBytes [bitcoinSignedMessageMagic, encodeVarint msg.size, msg]

/-- Double-SHA256 Bitcoin Signed Message digest. -/
def bitcoinSignedMessageDigest (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (msg : ByteArray) : InternalSpec.Musig2.Bytes32 :=
  let first := sha256 (bitcoinSignedMessagePreimage msg)
  sha256 first.bytes

/-- Base header byte for BIP-137 compact recoverable signatures. -/
def compactHeaderBaseByte : CompactSigHeaderBase → UInt8
  | .uncompressedP2pkh => 27
  | .compressedP2pkh => 31
  | .p2shP2wpkh => 35
  | .p2wpkh => 39

/-- Construct a 65-byte BIP-137 compact recoverable signature. -/
def formatCompactRecoverableSig (headerBase : CompactSigHeaderBase) (recId : UInt8)
    (r s : InternalSpec.Musig2.Bytes32) : Option InternalSpec.SilentPayments.Bytes65 :=
  if decide (recId > 3) then
    none
  else
    let hdr : InternalSpec.SilentPayments.SizedBytes 1 :=
      ⟨ByteArray.mk #[compactHeaderBaseByte headerBase + recId], rfl⟩
    let r32 : InternalSpec.SilentPayments.Bytes32 := ⟨r.bytes, r.size_eq⟩
    let s32 : InternalSpec.SilentPayments.Bytes32 := ⟨s.bytes, s.size_eq⟩
    some (BitcoinLedger.SilentPayments.appendSized hdr
      (BitcoinLedger.SilentPayments.appendSized r32 s32))

/-- BOLOS `sign_message.c:186` 65-byte compact signature (`31 + (recId & 1)`). -/
def formatBolosSignMessageSig (recId : UInt8)
    (r s : InternalSpec.Musig2.Bytes32) : Option InternalSpec.SilentPayments.Bytes65 :=
  if decide (recId > 3) then
    none
  else
    let parity : UInt8 := recId &&& 1
    let hdr : InternalSpec.SilentPayments.SizedBytes 1 :=
      ⟨ByteArray.mk #[31 + parity], rfl⟩
    let r32 : InternalSpec.SilentPayments.Bytes32 := ⟨r.bytes, r.size_eq⟩
    let s32 : InternalSpec.SilentPayments.Bytes32 := ⟨s.bytes, s.size_eq⟩
    some (BitcoinLedger.SilentPayments.appendSized hdr
      (BitcoinLedger.SilentPayments.appendSized r32 s32))

/-! ## 3. `GET_EXTENDED_PUBKEY` Path Policy, Vanadium Identity Keys & Swap Validation -/

/-- BOLOS `is_path_safe_for_pubkey_export`. -/
def isPathSafeForPubkeyExport (coinType : UInt32) (path : List UInt32) : Bool :=
  match path with
  | [p0, p1] => decide (p0 = electrumPathStep0) && decide (p1 = electrumPathStep1)
  | p0 :: p1 :: p2 :: rest =>
    let purpose := p0 &&& 0x7FFFFFFF
    let hardenedLenOpt : Option Nat :=
      if decide (purpose = 44) || decide (purpose = 49) || decide (purpose = 84) ||
         decide (purpose = 86) || decide (purpose = 87) || decide (purpose = 45) then
        some 3
      else if decide (purpose = 48) then
        some 4
      else
        none
    match hardenedLenOpt with
    | none => false
    | some hLen =>
      if decide (path.length < hLen) then
        false
      else
        let prefixHardened := appListAll (fun step => decide (step ≥ hardenedFlag)) (path.take hLen)
        let suffixUnhardened := appListAll (fun step => decide (step < hardenedFlag)) (path.drop hLen)
        let ctMatch := decide ((p1 &&& 0x7FFFFFFF) = coinType)
        let accOk := decide ((p2 &&& 0x7FFFFFFF) ≤ maxBip44AccountRecommended)
        let bip48Ok :=
          if decide (purpose = 48) then
            match rest with
            | p3 :: _ =>
              let st := p3 &&& 0x7FFFFFFF
              decide (st = 1) || decide (st = 2)
            | [] => false
          else
            true
        prefixHardened && suffixUnhardened && ctMatch && accOk && bip48Ok
  | _ => false

/-- Vanadium `is_identity_path` (`m/1229210958'` or `m/1229210958'/i`). -/
def classifyIdentityPath : List UInt32 → Option (Option UInt32)
  | [root] => if decide (root = identityRootPathComponent) then some none else none
  | [root, idx] => if decide (root = identityRootPathComponent) then some (some idx) else none
  | _ => none

/-- Check compressed SEC1 prefix (`0x02` or `0x03`). -/
def isValidCompressedSec1Prefix (pk : CompressedPubKey) : Bool :=
  match pk.bytes.data.toList with
  | b0 :: _ => decide (b0 = 0x02) || decide (b0 = 0x03)
  | [] => false

def identityKeyMagic : ByteArray :=
  ByteArray.mk #[0x0C, 0x49, 0x44, 0x45, 0x4E, 0x54, 0x49, 0x54, 0x59, 0x5F, 0x4B, 0x45, 0x59]

def identitySignMagic : ByteArray :=
  ByteArray.mk #[0x09, 0x49, 0x44, 0x45, 0x4E, 0x2F, 0x53, 0x49, 0x47, 0x4E]

def identityMsgTypeXpub : ByteArray := ByteArray.mk #[0x58, 0x50, 0x55, 0x42]
def identityMsgTypeOutput : ByteArray := ByteArray.mk #[0x4F, 0x55, 0x54, 0x50, 0x55, 0x54]

/-- Vanadium `build_identity_message(msg_type, object)`. -/
def buildIdentityMessage (msgType object : ByteArray) : Option ByteArray :=
  if decide (msgType.size > 255) || decide (object.size > 255) then
    none
  else
    some (concatBytes [
      identitySignMagic,
      ByteArray.mk #[UInt8.ofNat msgType.size],
      msgType,
      ByteArray.mk #[UInt8.ofNat object.size],
      object
    ])

/-- Vanadium `IdentityKey::get_id(name)`. -/
def computeIdentityRegistrationId (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (name : String) (pubkey : CompressedPubKey) : Option InternalSpec.Musig2.Bytes32 :=
  let nameBytes := name.toUTF8
  if decide (nameBytes.size = 0) || decide (nameBytes.size > 255) then
    none
  else
    some (sha256 (concatBytes [
      identityKeyMagic,
      ByteArray.mk #[UInt8.ofNat nameBytes.size],
      nameBytes,
      pubkey.bytes
    ]))

/-- Check cross-chain Swap first external output (`OP_RETURN <single_push>` with `SHA256 == expectedPayinHash`). -/
def validCrossChainOpReturn (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (out : ExternalOutputView) (expectedPayinHash : InternalSpec.Musig2.Bytes32) : Bool :=
  if decide (out.amount ≠ 0) then
    false
  else
    match out.script.data.toList with
    | 0x6A :: secondByte :: rest =>
      if decide ((2 : UInt8) ≤ secondByte) && decide (secondByte ≤ (75 : UInt8)) then
        let dataLen := secondByte.toNat
        if decide (out.script.size ≠ 2 + dataLen) then
          false
        else
          let payload := ByteArray.mk rest.toArray
          decide (sha256 payload = expectedPayinHash)
      else if decide (secondByte = 0x4C) then
        match rest with
        | lenByte :: payloadList =>
          let dataLen := lenByte.toNat
          if decide (out.script.size < 4) || decide (out.script.size ≠ 3 + dataLen) then
            false
          else
            let payload := ByteArray.mk payloadList.toArray
            decide (sha256 payload = expectedPayinHash)
        | [] => false
      else
        false
    | _ => false

/-- Check whether `porOpt` denotes a default BOLOS wallet (`none` or 32 zero bytes). -/
def isDefaultPor (porOpt : Option InternalSpec.Musig2.Bytes32) : Bool :=
  match porOpt with
  | none => true
  | some por => BitcoinLedger.Musig2.isAllZeros por

/-- Validate all BOLOS `execute_swap_checks` + `sign_psbt.c:55` invariants for `SwapLock`. -/
def validSwapPsbt {Affine : Type} (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (lock : SwapLock) (req : PsbtSignRequest Affine) : Bool :=
  let isDefaultWallet :=
    match req.account with
    | .walletPolicy wp => wp.isDefaultPolicy && isDefaultPor req.por
    | .silentPayment _ _ _ => false
  if !isDefaultWallet then
    false
  else if req.isBip322MessageSigning then
    false
  else if decide (req.nExternalInputs > 0) then
    false
  else if req.missingNonWitnessUtxo || req.nonDefaultSighash || req.sighashInputsOpen || req.sighashOutputsOpen then
    false
  else if decide (req.inputsTotalAmount < req.outputsTotalAmount) then
    false
  else if decide (req.outputsTotalAmount < req.changeOutputsTotalAmount) then
    false
  else
    let fee : UInt64 := req.inputsTotalAmount - req.outputsTotalAmount
    let spent : UInt64 := req.outputsTotalAmount - req.changeOutputsTotalAmount
    if decide (fee ≠ lock.fees) || decide (spent ≠ lock.amount) then
      false
    else
      match lock.mode with
      | .invalidMode => false
      | .standard =>
        match req.externalOutputs with
        | [destOut] => decide (destOut.formattedAddress = some lock.destinationAddress)
        | _ => false
      | .crossChain expectedPayinHash =>
        match req.externalOutputs with
        | [opRetOut, destOut] =>
          validCrossChainOpReturn sha256 opRetOut expectedPayinHash &&
          decide (destOut.formattedAddress = some lock.destinationAddress)
        | _ => false

/-! ## 4. BOLOS APDU & Vanadium CBOR Command Classification & Auth Helpers -/

/-- Classify a top-level BOLOS APDU header (`main.c`, `dispatcher.c`), including Swap-mode
    whitelist filtering and `p2 <= CURRENT_PROTOCOL_VERSION` (with arbitrary `p1` on `CLA=0xE1`). -/
def classifyBolosApdu (inSwapMode : Bool) (hdr : BolosApduHeader) : BolosWireCommand :=
  if inSwapMode then
    if decide (hdr.cla ≠ bolosClaApp) then
      .claNotSupported
    else if decide (hdr.p2 > bolosCurrentProtocolVersion) then
      .wrongP1P2
    else if decide (hdr.ins = bolosInsGetExtendedPubkey) then
      .getExtendedPubkey
    else if decide (hdr.ins = bolosInsGetWalletAddress) then
      .getWalletAddress
    else if decide (hdr.ins = bolosInsSignPsbt) then
      .signPsbt
    else if decide (hdr.ins = bolosInsGetMasterFingerprint) then
      .getMasterFingerprint
    else
      .insNotSupported
  else if decide (hdr.cla = bolosClaDefault) && decide (hdr.ins = bolosInsGetVersion) then
    if decide (hdr.p1 = 0) && decide (hdr.p2 = 0) then .getVersion else .wrongP1P2
  else if decide (hdr.p2 > bolosCurrentProtocolVersion) then
    .wrongP1P2
  else if decide (hdr.cla = bolosClaFramework) && decide (hdr.ins = bolosInsContinue) then
    .unexpectedContinue
  else if decide (hdr.cla = bolosClaApp) then
    if decide (hdr.ins = bolosInsGetExtendedPubkey) then .getExtendedPubkey
    else if decide (hdr.ins = bolosInsRegisterWallet) then .registerWallet
    else if decide (hdr.ins = bolosInsGetWalletAddress) then .getWalletAddress
    else if decide (hdr.ins = bolosInsSignPsbt) then .signPsbt
    else if decide (hdr.ins = bolosInsGetMasterFingerprint) then .getMasterFingerprint
    else if decide (hdr.ins = bolosInsSignMessage) then .signMessage
    else .insNotSupported
  else
    .claNotSupported

/-- Decode Vanadium CBOR `Request` variant tag (`0..8`, `common/src/message/mod.rs:139-233`). -/
def decodeVanadiumRequestTag : Nat → Option VanadiumRequestTag
  | 0 => some .getVersion
  | 1 => some .exit
  | 2 => some .getMasterFingerprint
  | 3 => some .getExtendedPubkey
  | 4 => some .registerAccount
  | 5 => some .getAddress
  | 6 => some .signPsbt
  | 7 => some .registerIdentityKey
  | 8 => some .exportSilentPaymentScanKey
  | _ => none

/-- Predicate identifying read-only query commands. -/
def isCommandReadOnly {Affine : Type} : AppCommand Affine → Bool
  | .getVersion => true
  | .getMasterFingerprint _ => true
  | .getExtendedPubkey _ _ _ _ => true
  | .getAddress _ _ _ _ _ => true
  | _ => false

/-- Check whether `cmd` is permitted while `SwapLock` is active on BOLOS (`main.c:157-159`). -/
def isAllowedInSwap {Affine : Type} : AppCommand Affine → Bool
  | .getMasterFingerprint .standard => true
  | .getExtendedPubkey .standard _ _ none => true
  | .getAddress _ _ _ _ none => true
  | .signPsbt _ => true
  | _ => false

/-- Effective MuSig2 Round-2 self-pubnonce check flag (`true` on BOLOS, configurable on Vanadium). -/
def checkSelfPubnonce {Affine : Type} (hw : HardwareOracle Affine) : TargetProfile → Bool
  | .bolos _ => true
  | .vanadium _ => hw.vanadiumCheckSelfPubnonce

/-- Validate Proof-of-Registration (or default-policy rules on BOLOS vs Vanadium). -/
def validateAccountAuth {Affine : Type} (profile : TargetProfile) (hw : HardwareOracle Affine)
    (inSwapMode : Bool) (account : AccountSpec Affine) (porOpt : Option InternalSpec.Musig2.Bytes32) :
    Except AppError Unit :=
  match account with
  | .walletPolicy wp =>
    if !wp.isSignable then
      .error .incorrectData
    else
      match porOpt with
      | none =>
        match profile with
        | .vanadium _ => .error .notSupported
        | .bolos _ =>
          if wp.isDefaultPolicy && wp.name.isEmpty then
            .ok ()
          else
            .error .incorrectData
      | some por =>
        if BitcoinLedger.Musig2.isAllZeros por then
          match profile with
          | .vanadium _ =>
            if decide (hw.computePorHmac wp.walletId = por) then .ok () else .error .signatureFail
          | .bolos _ =>
            if wp.isDefaultPolicy && wp.name.isEmpty then .ok () else .error .incorrectData
        else if inSwapMode then
          .error .failSwap
        else if decide (hw.computePorHmac wp.walletId = por) then
          .ok ()
        else
          .error .signatureFail
  | .silentPayment _ spAcc accId =>
    match profile with
    | .bolos _ => .error .notSupported
    | .vanadium _ =>
      if inSwapMode then
        .error .failSwap
      else
        match porOpt with
        | none => .error .notSupported
        | some por =>
          if decide (hw.computePorHmac accId = por) && decide (spAcc.accountIndex < hardenedFlag) then
            .ok ()
          else
            .error .signatureFail

/-- Compute optional Vanadium `IdentitySignature` over `(msgType, object)` using `identityIndex`. -/
def maybeSignIdentityObject {Affine : Type} (profile : TargetProfile) (hw : HardwareOracle Affine)
    (identityIndex : Option UInt32) (msgType object : ByteArray) :
    Except AppError (Option IdentitySignature) :=
  match identityIndex with
  | none => .ok none
  | some idx =>
    match profile with
    | .bolos _ => .error .notSupported
    | .vanadium _ =>
      if decide (idx ≥ hardenedFlag) then
        .error .incorrectData
      else
        match buildIdentityMessage msgType object with
        | none => .error .incorrectData
        | some msg =>
          match hw.signWithIdentityKey idx msg with
          | some sig => .ok (some sig)
          | none => .error .badState

/-- Pure recursive verification of registered cosigner identity PoR entries (`0 Classical.choice`). -/
def verifyIdentityEntriesLoop {Affine : Type} (hw : HardwareOracle Affine) :
    List RegisteredIdentityEntry → Except AppError Unit
  | [] => .ok ()
  | entry :: rest =>
    if !isValidCompressedSec1Prefix entry.pubkey then
      .error .signatureFail
    else
      match computeIdentityRegistrationId hw.musigCrypto.sha256 entry.name entry.pubkey with
      | none => .error .signatureFail
      | some regId =>
        if decide (hw.computePorHmac regId ≠ entry.por) then
          .error .signatureFail
        else
          verifyIdentityEntriesLoop hw rest

/-- Pure recursive verification of optional per-key xpub Schnorr signatures (`0 Classical.choice`). -/
def verifyKeySigsLoop {Affine : Type} (hw : HardwareOracle Affine) :
    List (ByteArray × Option IdentitySignature) → Except AppError Unit
  | [] => .ok ()
  | (keyPayload, sigOpt) :: rest =>
    match sigOpt with
    | none => verifyKeySigsLoop hw rest
    | some sig =>
      if !isValidCompressedSec1Prefix sig.identityPubkey then
        .error .signatureFail
      else
        match buildIdentityMessage identityMsgTypeXpub keyPayload with
        | none => .error .incorrectData
        | some msg =>
          if !hw.verifySchnorr sig.identityPubkey msg sig.signature then
            .error .signatureFail
          else
            verifyKeySigsLoop hw rest

/-- Verify registered cosigner identity PoRs and optional per-key xpub signatures in `RegisterAccount`. -/
def verifyRegisteredIdentityAuth {Affine : Type} (hw : HardwareOracle Affine)
    (entries : List RegisteredIdentityEntry)
    (keyInfos : List ByteArray)
    (keySigs : List (Option IdentitySignature)) : Except AppError Unit :=
  match verifyIdentityEntriesLoop hw entries with
  | .error e => .error e
  | .ok () => verifyKeySigsLoop hw (keyInfos.zip keySigs)

/-! ## 5. Unified Command Step Function (`stepAppCommand`) & Multi-Step Traces -/

/-- Check whether BOLOS open-sighash underfunded inputs are permitted. -/
def allowUnderfundedInputs {Affine : Type} (profile : TargetProfile) (inSwap : Bool)
    (psbt : PsbtSignRequest Affine) : Bool :=
  match profile with
  | .bolos _ => !inSwap && (psbt.sighashInputsOpen || psbt.sighashOutputsOpen)
  | .vanadium _ => false

/-- Check whether MuSig2 Round-1-only requires explicit user approval (`C-06`). -/
def round1NeedsApproval (profile : TargetProfile) (spShares : List SilentPaymentShareOut) : Bool :=
  (match profile with | .vanadium _ => true | .bolos _ => false) || !spShares.isEmpty

/-- Authorize PSBT signing via pre-approved `SwapLock` OR interactive user approval. -/
def authorizePsbtStep {Affine : Type} (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (swapLock : Option SwapLock) (ui : UserApprovalOracle Affine)
    (psbt : PsbtSignRequest Affine) : Except AppError Bool :=
  match swapLock with
  | some lock =>
    if validSwapPsbt sha256 lock psbt then .ok true
    else .error .failSwap
  | none =>
    if ui.approve (.confirmSignPsbt psbt) then .ok false
    else .error .userRejected

/-- Compute BIP-375 Silent Payment ECDH shares & output scripts via `BitcoinLedger.SilentPayments`. -/
def computePsbtSpOutputs {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine)
    (spTxOpt : Option (PsbtSpTx Affine)) :
    Except AppError (List SilentPaymentShareOut × List SilentPaymentOutputScriptOut) :=
  match spTxOpt with
  | none => .ok ([], [])
  | some spTx =>
    match profile with
    | .bolos _ => .error .notSupported
    | .vanadium _ =>
      match BitcoinLedger.SilentPayments.finalizePsbtSilentPayments hw.spCrypto spTx hw.freshDleqAuxRand with
      | .error spErr => .error (.silentPaymentError spErr)
      | .ok pair => .ok pair

/-- Pure recursive loop signing standard PSBT inputs. -/
def signStandardInputs {Affine : Type} (hw : HardwareOracle Affine) :
    List StandardInputSigRequest → Except AppError (List StandardInputSignature)
  | [] => .ok []
  | req :: rest =>
    match hw.signPsbtInput req with
    | none => .error .badState
    | some (sigBytes, pk) =>
      match signStandardInputs hw rest with
      | .error e => .error e
      | .ok tail =>
        .ok ({
          inputIndex := req.inputIndex
          signature := sigBytes
          pubkey := pk
          leafHash := req.leafHash
        } :: tail)

/-- Latch `swapAborted := true` whenever `.failSwap` occurs while `s.swapLock.isSome = true`. -/
def abortSwapIfFailed (e : AppError) (s : AppPersistentState) : AppError × AppPersistentState :=
  if s.swapLock.isSome && decide (e = .failSwap) then
    (e, { s with swapAborted := true })
  else
    (e, s)

/-- Execute one top-level `AppCommand`, returning `.error (err, postState)` or `.ok (resp, postState)`. -/
def stepAppCommand {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine)
    (s : AppPersistentState) :
    Except (AppError × AppPersistentState) (AppResponse × AppPersistentState) :=
  if s.swapLock.isSome && s.swapAborted then
    .error (.failSwap, s)
  else if s.swapLock.isSome && !isAllowedInSwap cmd then
    .error (.insNotSupported, s)
  else
    match cmd with
    | .unexpectedContinue =>
      .error (.badState, s)

    | .getVersion =>
      match profile with
      | .bolos _ => .ok (.version targetAppVersion, s)
      | .vanadium _ => .error (.notSupported, s)

    | .getMasterFingerprint tree =>
      match profile, tree with
      | .bolos _, .resident => .error (.notSupported, s)
      | _, _ =>
        match hw.masterFingerprint tree s.residentKeys with
        | some fpr => .ok (.masterFingerprint fpr, s)
        | none => .error (.keyDerivationFailed, s)

    | .getExtendedPubkey tree display path identityIndex =>
      if decide (path.length > profileMaxPathSteps profile) then
        .error (.derivationPathTooLong, s)
      else
        match profile, tree with
        | .bolos _, .resident => .error (.notSupported, s)
        | _, _ =>
          let vanadiumStandardTooLong : Bool :=
            match profile, tree with
            | .vanadium _, .standard => decide (path.length > vanadiumStandardMaxBip32PathSteps)
            | _, _ => false
          if identityIndex.isSome && decide (tree ≠ .standard) then
            .error (.incorrectData, s)
          else if vanadiumStandardTooLong then
            .error (.derivationPathTooLong, s)
          else
            let bolosUnsafeBlocked :=
              match profile with
              | .bolos ct => !isPathSafeForPubkeyExport ct path && !display
              | .vanadium _ => false
            if bolosUnsafeBlocked then
              .error (.notSupported, s)
            else
              match hw.deriveExtendedPubkey tree s.residentKeys path with
              | none => .error (.keyDerivationFailed, s)
              | some (xpub, _pk) =>
                let prompt : UserPrompt Affine :=
                  match profile, tree, classifyIdentityPath path with
                  | .vanadium _, .standard, some idKind => .confirmIdentityPubkey idKind xpub
                  | _, _, _ => .confirmExtendedPubkey tree path xpub
                if display && !ui.approve prompt then
                  .error (.userRejected, s)
                else
                  match maybeSignIdentityObject profile hw identityIndex identityMsgTypeXpub xpub with
                  | .error e => .error (e, s)
                  | .ok idSig => .ok (.extendedPubkey xpub idSig, s)

    | .getAddress display account porOpt coordinates identityIndex =>
      match validateAccountAuth profile hw s.swapLock.isSome account porOpt with
      | .error e => .error (abortSwapIfFailed e s)
      | .ok () =>
        match account, coordinates with
        | .walletPolicy wp, .walletPolicy isChange addrIdx =>
          if decide (addrIdx ≥ hardenedFlag) then
            .error (.incorrectData, s)
          else if isDefaultPor porOpt && decide (addrIdx > maxDefaultAddressIndex) then
            .error (.incorrectData, s)
          else
            match hw.deriveWalletPolicyOutput wp isChange addrIdx with
            | none => .error (.badState, s)
            | some (addr, scriptBytes) =>
              match maybeSignIdentityObject profile hw identityIndex identityMsgTypeOutput scriptBytes with
              | .error e => .error (e, s)
              | .ok idSig =>
                if display && !ui.approve (.confirmAddress account coordinates addr) then
                  .error (.userRejected, s)
                else
                  .ok (.address addr idSig, s)
        | .silentPayment _ spAcc _, .silentPayment spCoords =>
          if identityIndex.isSome then
            .error (.incorrectData, s)
          else
            let spHrp : SpAddressHrp := if decide (profileCoinType profile = 0) then .sp else .tsp
            match BitcoinLedger.SilentPayments.deriveAccountSpAddress hw.spCrypto hw.bech32m spHrp spAcc spCoords with
            | .error spErr => .error (.silentPaymentError spErr, s)
            | .ok addr =>
              if display && !ui.approve (.confirmAddress account coordinates addr) then
                .error (.userRejected, s)
              else
                .ok (.address addr none, s)
        | _, _ =>
          .error (.incorrectData, s)

    | .registerAccount account regIdentities keySigs showCleartext =>
      match account with
      | .walletPolicy wp =>
        if wp.name.isEmpty || decide (wp.name.utf8ByteSize > 64) || decide (wp.nInternalKeys < 1) || !wp.isSignable then
          .error (.incorrectData, s)
        else if decide (wp.version = 1) && decide (wp.nInternalKeys ≠ 1) then
          .error (.incorrectData, s)
        else
          let authCheck : Except AppError Unit :=
            match profile with
            | .bolos _ =>
              if !regIdentities.isEmpty || !keySigs.isEmpty then .error .notSupported else .ok ()
            | .vanadium _ =>
              verifyRegisteredIdentityAuth hw regIdentities wp.keysInfoPayloads keySigs
          match authCheck with
          | .error e => .error (e, s)
          | .ok () =>
            if !ui.approve (.confirmRegisterAccount account showCleartext) then
              .error (.userRejected, s)
            else
              let hmac := hw.computePorHmac wp.walletId
              let entry := (wp.walletId, hmac)
              let reg' := if appListMem entry s.registeredAccounts then s.registeredAccounts else entry :: s.registeredAccounts
              .ok (.accountRegistered wp.walletId hmac, { s with registeredAccounts := reg' })
      | .silentPayment name spAcc accId =>
        match profile with
        | .bolos _ => .error (.notSupported, s)
        | .vanadium _ =>
          if name.isEmpty || decide (name.utf8ByteSize > 64) || !regIdentities.isEmpty || !keySigs.isEmpty then
            .error (.incorrectData, s)
          else
            match hw.deriveSpAccount spAcc.accountIndex with
            | .error spErr => .error (.silentPaymentError spErr, s)
            | .ok derivedAcc =>
              if decide (derivedAcc ≠ spAcc) then
                .error (.incorrectData, s)
              else
                let spHrp : SpAddressHrp := if decide (profileCoinType profile = 0) then .sp else .tsp
                match BitcoinLedger.SilentPayments.deriveAccountSpAddress hw.spCrypto hw.bech32m spHrp spAcc (.code none) with
                | .error spErr => .error (.silentPaymentError spErr, s)
                | .ok _addr =>
                  if !ui.approve (.confirmRegisterAccount account showCleartext) then
                    .error (.userRejected, s)
                  else
                    let hmac := hw.computePorHmac accId
                    let entry := (accId, hmac)
                    let reg' := if appListMem entry s.registeredAccounts then s.registeredAccounts else entry :: s.registeredAccounts
                    .ok (.accountRegistered accId hmac, { s with registeredAccounts := reg' })

    | .registerIdentityKey name pubkey =>
      match profile with
      | .bolos _ => .error (.notSupported, s)
      | .vanadium _ =>
        if !isValidCompressedSec1Prefix pubkey then
          .error (.incorrectData, s)
        else
          match computeIdentityRegistrationId hw.musigCrypto.sha256 name pubkey with
          | none => .error (.incorrectData, s)
          | some keyId =>
            if !ui.approve (.confirmRegisterIdentityKey name pubkey) then
              .error (.userRejected, s)
            else
              let hmac := hw.computePorHmac keyId
              .ok (.identityKeyRegistered keyId hmac, s)

    | .exportSpScanKey _callerHrp accountIndex =>
      match profile with
      | .bolos _ => .error (.notSupported, s)
      | .vanadium _ =>
        let approved := ui.approve (.confirmExportSpScanKey accountIndex)
        match BitcoinLedger.SilentPayments.exportSpScanKey hw.spCrypto hw.bech32m
                (profileSpScanHrp profile) hw.deriveSpAccount accountIndex approved with
        | .error .userRejected => .error (.userRejected, s)
        | .error spErr => .error (.silentPaymentError spErr, s)
        | .ok encoded => .ok (.spScanKeyExported encoded, s)

    | .signMessage path message _headerBase =>
      match profile with
      | .vanadium _ => .error (.notSupported, s)
      | .bolos _ =>
        if decide (path.length > bolosMaxBip32PathSteps) then
          .error (.wrongDataLength, s)
        else if decide (message.size ≥ maxSignMessageLength) then
          .error (.incorrectData, s)
        else
          let dispForm : MessageDisplayForm :=
            if isPrintableAsciiMessage message then
              .cleartextAscii message
            else
              .sha256Digest (hw.musigCrypto.sha256 message)
          if !ui.approve (.confirmSignMessage path dispForm) then
            .error (.userRejected, s)
          else
            let bsmDigest := bitcoinSignedMessageDigest hw.musigCrypto.sha256 message
            match hw.signRecoverableEcdsa path bsmDigest with
            | none => .error (.badState, s)
            | some (recId, r, sScalar) =>
              match formatBolosSignMessageSig recId r sScalar with
              | none => .error (.badState, s)
              | some compact65 => .ok (.messageSigned compact65, s)

    | .signPsbt psbt =>
      if s.swapLock.isSome && psbt.isBip322MessageSigning then
        .error (.notSupported, s)
      else
        match validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
        | .error e => .error (abortSwapIfFailed e s)
        | .ok () =>
          if (!allowUnderfundedInputs profile s.swapLock.isSome psbt &&
              decide (psbt.inputsTotalAmount < psbt.outputsTotalAmount)) ||
             decide (psbt.outputsTotalAmount < psbt.changeOutputsTotalAmount) then
            .error (.incorrectData, s)
          else
            match computePsbtSpOutputs profile hw psbt.silentPaymentTx with
            | .error e => .error (e, s)
            | .ok (spShares, spScripts) =>
              match psbt.musigPlan with
              | .round1Only sid r1Tasks =>
                if !psbt.standardSignTasks.isEmpty || s.swapLock.isSome then
                  .error (.incorrectData, s)
                else if round1NeedsApproval profile spShares && !ui.approve (.confirmSignPsbt psbt) then
                  .error (.userRejected, s)
                else
                  match BitcoinLedger.Musig2.executeRound1Pass hw.musigCrypto (profileMusigAggPkMode profile)
                          s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                  | .error (mErr, ms') =>
                    .error (.musigError mErr, { s with musigSessions := ms' })
                  | .ok (pubnonces, msCommitted) =>
                    .ok (.psbtSigned [] pubnonces [] spShares spScripts false,
                         { s with musigSessions := msCommitted })

              | .none =>
                match authorizePsbtStep hw.musigCrypto.sha256 s.swapLock ui psbt with
                | .error e => .error (abortSwapIfFailed e s)
                | .ok isSwap =>
                  match signStandardInputs hw psbt.standardSignTasks with
                  | .error e => .error (e, s)
                  | .ok stdSigs =>
                    let nextSwap := if isSwap then none else s.swapLock
                    .ok (.psbtSigned stdSigs [] [] spShares spScripts isSwap,
                         { s with swapLock := nextSwap })

              | .round1AndStandard sid r1Tasks =>
                match authorizePsbtStep hw.musigCrypto.sha256 s.swapLock ui psbt with
                | .error e => .error (abortSwapIfFailed e s)
                | .ok isSwap =>
                  match signStandardInputs hw psbt.standardSignTasks with
                  | .error e => .error (e, s)
                  | .ok stdSigs =>
                    match BitcoinLedger.Musig2.executeRound1Pass hw.musigCrypto (profileMusigAggPkMode profile)
                            s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                    | .error (mErr, ms') =>
                      .error (.musigError mErr, { s with musigSessions := ms' })
                    | .ok (pubnonces, msCommitted) =>
                      let nextSwap := if isSwap then none else s.swapLock
                      .ok (.psbtSigned stdSigs pubnonces [] spShares spScripts isSwap,
                           { s with musigSessions := msCommitted, swapLock := nextSwap })

              | .round2 sid r2Inputs =>
                if (BitcoinLedger.Musig2.lookupActive s.musigSessions sid).isNone then
                  .error (.musigError .missingSession, s)
                else
                  match authorizePsbtStep hw.musigCrypto.sha256 s.swapLock ui psbt with
                  | .error e => .error (abortSwapIfFailed e s)
                  | .ok isSwap =>
                    match BitcoinLedger.Musig2.executeRound2Pass hw.musigCrypto (profileMusigAggPkMode profile)
                            s.musigSessions sid r2Inputs (checkSelfPubnonce hw profile) with
                    | .error (mErr, msConsumed) =>
                      .error (.musigError mErr, { s with musigSessions := msConsumed })
                    | .ok (partialSigs, msConsumed) =>
                      match signStandardInputs hw psbt.standardSignTasks with
                      | .error e =>
                        .error (e, { s with musigSessions := msConsumed })
                      | .ok stdSigs =>
                        let nextSwap := if isSwap then none else s.swapLock
                        .ok (.psbtSigned stdSigs [] partialSigs spShares spScripts isSwap,
                             { s with musigSessions := msConsumed, swapLock := nextSwap })

/-- Extract the post-state from `stepAppCommand` regardless of `.ok` or `.error`. -/
def extractPostState :
    Except (AppError × AppPersistentState) (AppResponse × AppPersistentState) → AppPersistentState
  | .ok (_, s') => s'
  | .error (_, s') => s'

/-- Single-step post-state projection. -/
def stepPostState {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s : AppPersistentState) : AppPersistentState :=
  extractPostState (stepAppCommand profile hw ui cmd s)

/-- Execute a multi-step command trace `[cmd_1, ..., cmd_k]` from initial state `s`. -/
def runAppTrace {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine) :
    List (AppCommand Affine) → AppPersistentState → List (AppTraceOutcome Affine) × AppPersistentState
  | [], s => ([], s)
  | cmd :: rest, s =>
    match stepAppCommand profile hw ui cmd s with
    | .ok (resp, s') =>
      let (tail, sFinal) := runAppTrace profile hw ui rest s'
      (.ok cmd resp :: tail, sFinal)
    | .error (err, s') =>
      let (tail, sFinal) := runAppTrace profile hw ui rest s'
      (.error cmd err :: tail, sFinal)

/-- Check whether `stepAppCommand` succeeded in MuSig2 Round 2 using `rr`. -/
def stepUsedMusigRandRoot {Affine : Type} [DecidableEq Affine]
    (cmd : AppCommand Affine)
    (res : Except (AppError × AppPersistentState) (AppResponse × AppPersistentState))
    (s : AppPersistentState) (rr : RandRoot) : Bool :=
  match cmd, res with
  | .signPsbt psbt, .ok (.psbtSigned _ _ _ _ _ _, _) =>
    match psbt.musigPlan with
    | .round2 sid _ => decide (BitcoinLedger.Musig2.lookupActive s.musigSessions sid = some rr)
    | _ => false
  | _, _ => false

/-- Count how many steps in `cmds` emit Round-2 partial signatures using `rr`. -/
def countMusigRound2StepsForRandRoot {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (rr : RandRoot) : List (AppCommand Affine) → AppPersistentState → Nat
  | [], _ => 0
  | cmd :: rest, s =>
    let usedHere := stepUsedMusigRandRoot cmd (stepAppCommand profile hw ui cmd s) s rr
    let s' := stepPostState profile hw ui cmd s
    (if usedHere then 1 else 0) + countMusigRound2StepsForRandRoot profile hw ui rr rest s'

/-- Predicate expressing that `resp` emits secret-key-derived cryptographic material
    (compact message signature, standard PSBT signature, MuSig2 partial signature, or SP ECDH share). -/
def responseEmitsSecretDerivedMaterial : AppResponse → Bool
  | .messageSigned _ => true
  | .psbtSigned stdSigs _ musigPartialSigs spShares _ _ =>
    !stdSigs.isEmpty || !musigPartialSigs.isEmpty || !spShares.isEmpty
  | _ => false

/-! ## 6. End-to-End Verified `SIGN_PSBT` & BIP-322 `verifyPsbtSignMessage` Composition -/

/-- Canonical `PolicyProfile` corresponding to a `TargetProfile`. -/
def policyProfileOfTarget : TargetProfile → InternalSpec.WalletPolicy.PolicyProfile
  | .bolos ct =>
      InternalSpec.WalletPolicy.bolosAppProfile (if decide (ct = 0) then .mainnet else .testnet)
  | .vanadium ct =>
      InternalSpec.WalletPolicy.vanadiumAppProfile (if decide (ct = 0) then .mainnet else .testnet)

/-- Exact isomorphism `InternalSpec.Psbt.Bytes32` ↔ `InternalSpec.Musig2.Bytes32`. -/
def psbtBytes32ToMusig (h : InternalSpec.Psbt.Bytes32) : InternalSpec.Musig2.Bytes32 :=
  ⟨h.bytes, h.size_eq⟩

def musigBytes32ToPsbt (h : InternalSpec.Musig2.Bytes32) : InternalSpec.Psbt.Bytes32 :=
  ⟨h.bytes, h.size_eq⟩

/-- Construct `InternalSpec.Psbt.CryptoOracles` from `TargetProfile`, `InternalSpec.Network`, `HardwareOracle`, and `hash160`. -/
def mkPsbtCryptoOracles
    {Affine : Type}
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (hash160 : ByteArray → ByteArray) : InternalSpec.Psbt.CryptoOracles where
  sha256 bs := musigBytes32ToPsbt (hw.musigCrypto.sha256 bs)
  hash160 := hash160
  formatAddress spk :=
    let addrTarget : InternalSpec.AddressTarget :=
      match profile with
      | .bolos _ => .bolos
      | .vanadium _ => .vanadium
    let dblSha256 : ByteArray → ByteArray := fun b =>
      (hw.musigCrypto.sha256 (hw.musigCrypto.sha256 b).bytes).bytes
    InternalSpec.scriptToAddress? addrTarget dblSha256 net spk

/-- Canonical `InternalSpec.Psbt.SigningConfig` for a `TargetProfile`. -/
def signingConfigOfTarget
    (profile : TargetProfile)
    (allowNonDefaultSighash : Bool := false) : InternalSpec.Psbt.SigningConfig :=
  match profile with
  | .bolos _ =>
      { allowNonDefaultSighash := allowNonDefaultSighash
        allowExternalInputs := true
        highFeeInclusiveAt100k := false }
  | .vanadium _ =>
      { allowNonDefaultSighash := allowNonDefaultSighash
        allowExternalInputs := false
        highFeeInclusiveAt100k := true }

/-- Bridge `SwapLock` into `InternalSpec.Psbt.SwapParams` (`none` if `.invalidMode`). -/
def appSwapLockToPsbtSwapParams (lock : SwapLock) : Option InternalSpec.Psbt.SwapParams :=
  match lock.mode with
  | .standard =>
      some {
        mode := .standard
        amount := lock.amount.toNat
        fees := lock.fees.toNat
        destinationAddress := lock.destinationAddress
      }
  | .crossChain payinHash =>
      some {
        mode := .crossChain (musigBytes32ToPsbt payinHash)
        amount := lock.amount.toNat
        fees := lock.fees.toNat
        destinationAddress := lock.destinationAddress
      }
  | .invalidMode => none

/-- Verify all Merkle map commitments and sorted-key openings in a `PsbtMerkleOpeningBundle`
    against the PSBT's exact input and output counts (`0 Classical.choice`). -/
def verifyPsbtMerkleBundle
    (sha256 : ByteArray → InternalSpec.Psbt.Bytes32)
    (nInputs nOutputs : Nat)
    (bundle : PsbtMerkleOpeningBundle) : Bool :=
  decide (bundle.inputMaps.length = nInputs) &&
  decide (bundle.outputMaps.length = nOutputs) &&
  InternalSpec.MerkleProtocol.verifySortedMerkleMapOpenings sha256 bundle.globalMap bundle.globalKeyOpenings &&
  appListAll (fun (m, ops) =>
    InternalSpec.MerkleProtocol.verifySortedMerkleMapOpenings sha256 m ops) bundle.inputMaps &&
  appListAll (fun (m, ops) =>
    InternalSpec.MerkleProtocol.verifySortedMerkleMapOpenings sha256 m ops) bundle.outputMaps

/-- Convert `InternalSpec.WalletPolicy.KeyOrigin` to `InternalSpec.Psbt.KeyOrigin`. -/
def policyOriginToPsbt (orig : InternalSpec.WalletPolicy.KeyOrigin) : InternalSpec.Psbt.KeyOrigin :=
  { fingerprint := orig.fingerprint
    path := orig.path }

/-- Spend class (`legacy`, `segwitV0`, `taprootV1`) determined by a BIP-388 `DescriptorTemplate`. -/
def descriptorSpendClass : InternalSpec.WalletPolicy.DescriptorTemplate → InternalSpec.Psbt.SpendClass
  | .pkh _ => .legacy
  | .sh (.multi _ _) => .legacy
  | .sh (.sortedmulti _ _) => .legacy
  | .sh (.wpkh _) => .segwitV0
  | .sh (.wsh _) => .segwitV0
  | .wpkh _ => .segwitV0
  | .wsh _ => .segwitV0
  | .tr _ _ => .taprootV1

/-- Classify a `KeyInformation` entry against `DeviceRegistrationOracle`, supporting originless internal root xpubs. -/
def classifyKeyInfoUnified
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (net : InternalSpec.WalletPolicy.Network)
    (ki : InternalSpec.WalletPolicy.KeyInformation) : InternalSpec.WalletPolicy.PolicyKeyRole :=
  let baseRole := InternalSpec.WalletPolicy.classifyKeyInfo dev net ki
  match baseRole, ki.origin with
  | .external, none =>
      if decide (ki.xpub.depth = 0) then
        match dev.deriveAtOrigin net [] with
        | some rootXpub =>
            if decide (rootXpub = ki.xpub) then .internal else .external
        | none => .external
      else
        .external
  | role, _ => role

/-- Extract internal (device-owned) key placeholders from a `InternalSpec.WalletPolicy.WalletPolicy`. -/
def extractInternalPlaceholders
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (net : InternalSpec.WalletPolicy.Network)
    (policy : InternalSpec.WalletPolicy.WalletPolicy) : List InternalSpec.Psbt.InternalKeyPlaceholder :=
  let roles := policy.keys.map (classifyKeyInfoUnified dev net)
  let exprs := InternalSpec.WalletPolicy.collectTemplateKeyExprs policy.template
  exprs.flatMap fun ke =>
    if decide (InternalSpec.WalletPolicy.countInternalInKeyExpr roles ke = 0) then
      []
    else
      let (numFirst, numSecond) := ke.deriv.toPair
      let resolvedOrigin (ki : InternalSpec.WalletPolicy.KeyInformation) : InternalSpec.Psbt.KeyOrigin :=
        match ki.origin with
        | some orig => policyOriginToPsbt orig
        | none => { fingerprint := dev.masterFingerprint, path := [] }
      match ke with
      | .single idx _ =>
          match InternalSpec.WalletPolicy.listNthOpt policy.keys idx with
          | some ki =>
              [{
                keyIndex := idx
                expectedOrigin := some (resolvedOrigin ki)
                numFirst := numFirst
                numSecond := numSecond
                isMusig := false
              }]
          | none => []
      | .musig idxs _ =>
          let syntheticAgg : InternalSpec.Psbt.InternalKeyPlaceholder := {
            keyIndex := idxs.headD 0
            expectedOrigin := none
            numFirst := numFirst
            numSecond := numSecond
            isMusig := true
          }
          let participantPlaceholders : List InternalSpec.Psbt.InternalKeyPlaceholder :=
            idxs.filterMap fun idx =>
              if decide (InternalSpec.WalletPolicy.listNthOpt roles idx = some .internal) then
                match InternalSpec.WalletPolicy.listNthOpt policy.keys idx with
                | some ki =>
                    some {
                      keyIndex := idx
                      expectedOrigin := some (resolvedOrigin ki)
                      numFirst := numFirst
                      numSecond := numSecond
                      isMusig := true
                    }
                | none => none
              else
                none
          syntheticAgg :: participantPlaceholders

/-- Derive `(scriptPubKey, optionalRedeemScript, optionalWitnessScript)` for a `WalletPolicy`. -/
def derivePolicyAllScripts
    (profile : InternalSpec.WalletPolicy.PolicyProfile)
    (ora : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (isChange : Bool)
    (addressIndex : UInt32) : Option (ByteArray × Option ByteArray × Option ByteArray) :=
  match InternalSpec.WalletPolicy.deriveWalletScriptPubKeyWithProfile profile ora policy isChange addressIndex with
  | .error _ => none
  | .ok spk =>
      let net := profile.network
      match policy.template with
      | .pkh _ | .wpkh _ | .tr _ _ =>
          some (spk, none, none)
      | .wsh inner =>
          match InternalSpec.WalletPolicy.compileWshWitnessScript ora net policy.keys isChange addressIndex inner with
          | .ok ws => some (spk, none, some ws)
          | .error _ => none
      | .sh (.wpkh ke) =>
          match InternalSpec.WalletPolicy.deriveKeyExprCompressedPubkey ora net policy.keys isChange addressIndex ke with
          | .ok cpk =>
              let rs := InternalSpec.WalletPolicy.mkP2WPKH (ora.hash160 cpk)
              some (spk, some rs, none)
          | .error _ => none
      | .sh (.multi k kes) =>
          match InternalSpec.WalletPolicy.compileMultiScript ora net policy.keys isChange addressIndex false false k kes with
          | .ok rs => some (spk, some rs, none)
          | .error _ => none
      | .sh (.sortedmulti k kes) =>
          match InternalSpec.WalletPolicy.compileMultiScript ora net policy.keys isChange addressIndex true false k kes with
          | .ok rs => some (spk, some rs, none)
          | .error _ => none
      | .sh (.wsh inner) =>
          match InternalSpec.WalletPolicy.compileWshWitnessScript ora net policy.keys isChange addressIndex inner with
          | .ok ws =>
              let rs := InternalSpec.WalletPolicy.mkP2WSH (ora.sha256 ws)
              some (spk, some rs, some ws)
          | .error _ => none

/-- Project `InternalSpec.WalletPolicy.WalletPolicy` into `InternalSpec.Psbt.WalletPolicySpec`. -/
def toPsbtWalletPolicySpec
    (profile : InternalSpec.WalletPolicy.PolicyProfile)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (ora : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (policy : InternalSpec.WalletPolicy.WalletPolicy) : InternalSpec.Psbt.WalletPolicySpec :=
  { isDefault :=
      profile.allowStatelessDefaultPolicies &&
      InternalSpec.WalletPolicy.isDefaultStatelessPolicy dev profile.network policy
    name := policy.name
    spendClass := descriptorSpendClass policy.template
    internalPlaceholders := extractInternalPlaceholders dev profile.network policy
    deriveScripts := derivePolicyAllScripts profile ora policy }

/-- Project `InternalSpec.WalletPolicy.WalletPolicy` into `WalletPolicySpec`. -/
def toAppWalletPolicySpec
    (profile : InternalSpec.WalletPolicy.PolicyProfile)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (policy : InternalSpec.WalletPolicy.WalletPolicy) : WalletPolicySpec :=
  let roles := policy.keys.map (classifyKeyInfoUnified dev profile.network)
  let nInternal := (roles.filter (fun r => decide (r = .internal))).length
  let wfOk := (InternalSpec.WalletPolicy.checkPolicyWellFormed profile policy).isOk
  let signableOk := (InternalSpec.WalletPolicy.checkRegisteredSignability profile dev policy).isOk
  { name := policy.name
    version := policy.format.wireTag
    descriptorTemplate := descriptorTemplate
    nKeys := policy.keys.length
    nInternalKeys := nInternal
    isDefaultPolicy :=
      wfOk &&
      profile.allowStatelessDefaultPolicies &&
      InternalSpec.WalletPolicy.isDefaultStatelessPolicy dev profile.network policy
    isSignable := wfOk && signableOk
    walletId := walletId
    keysInfoPayloads := keysInfoPayloads }

/-- Build a verified `PsbtSignRequest` from a concrete `WalletPolicy` and `PsbtTx` by executing:
    1. BIP-388 policy well-formedness (`checkPolicyWellFormed`),
    2. BOLOS Merkleized map sorted-key opening verification (`verifyPsbtMerkleBundle`),
    3. Full `InternalSpec.Psbt.authorizePsbtSigning` (UTXO commitments, sighashes, fee/change elimination, BIP-322, and Swap checks). -/
def buildVerifiedPsbtSignRequest
    {Affine : Type}
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (allowNonDefaultSighash : Bool)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (swapLockOpt : Option SwapLock)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (silentPaymentTx : Option (PsbtSpTx Affine)) :
    Except VerifiedPsbtSignError (InternalSpec.Psbt.ValidatedPsbt × PsbtSignRequest Affine) :=
  let polProf := policyProfileOfTarget profile
  match InternalSpec.WalletPolicy.checkPolicyWellFormed polProf policy with
  | .error pErr => .error (.invalidPolicy pErr)
  | .ok () =>
      let psbtCrypto := mkPsbtCryptoOracles profile net hw hash160
      let merkleOk : Bool :=
        match merkleOpt with
        | none => true
        | some bundle =>
            verifyPsbtMerkleBundle psbtCrypto.sha256 psbt.inputs.size psbt.outputs.size bundle
      if !merkleOk then
        .error .merkleVerificationFailed
      else
        let swapParamsRes : Except VerifiedPsbtSignError (Option InternalSpec.Psbt.SwapParams) :=
          match swapLockOpt with
          | none => .ok none
          | some lock =>
              match appSwapLockToPsbtSwapParams lock with
              | some sp => .ok (some sp)
              | none => .error .invalidSwapLockMode
        match swapParamsRes with
        | .error e => .error e
        | .ok swapParamsOpt =>
            let psbtPolicy := toPsbtWalletPolicySpec polProf dev policyOra policy
            let cfg := signingConfigOfTarget profile allowNonDefaultSighash
            match InternalSpec.Psbt.authorizePsbtSigning psbtCrypto cfg psbtPolicy psbt swapParamsOpt with
            | .error psbtErr => .error (.psbtRejected psbtErr)
            | .ok validated =>
                let appPolicy := toAppWalletPolicySpec polProf dev descriptorTemplate walletId keysInfoPayloads policy
                let nExt := (validated.validatedInputs.toList.filter (fun (_, isInt, _) => !isInt)).length
                let inOpen := appListAny (fun (_, isInt, sh) =>
                  isInt && InternalSpec.Psbt.sighashOpensInputs sh) validated.validatedInputs.toList
                let outOpen := appListAny (fun (_, isInt, sh) =>
                  isInt && InternalSpec.Psbt.sighashOpensOutputs sh) validated.validatedInputs.toList
                let extViews : List ExternalOutputView :=
                  validated.displayedOutputs.map fun (_, out) =>
                    let spk := out.scriptPubKey.getD ByteArray.empty
                    { amount := UInt64.ofNat out.amount
                      script := spk
                      formattedAddress := psbtCrypto.formatAddress spk }
                let req : PsbtSignRequest Affine := {
                  account := .walletPolicy appPolicy
                  por := por
                  isBip322MessageSigning := psbt.bip322Message.isSome
                  inputsTotalAmount := UInt64.ofNat validated.sumInputs
                  outputsTotalAmount := UInt64.ofNat validated.sumOutputs
                  changeOutputsTotalAmount := UInt64.ofNat validated.sumChangeOutputs
                  nExternalInputs := nExt
                  missingNonWitnessUtxo := validated.warnings.missingNonWitnessUtxo
                  nonDefaultSighash := validated.warnings.nonDefaultSighash
                  sighashInputsOpen := inOpen
                  sighashOutputsOpen := outOpen
                  externalOutputs := extViews
                  standardSignTasks := standardSignTasks
                  musigPlan := musigPlan
                  silentPaymentTx := silentPaymentTx
                }
                .ok (validated, req)

/-- Execute a fully verified end-to-end `SIGN_PSBT` step via `BitcoinLedger.AppStateMachine.stepAppCommand`. -/
def stepVerifiedPsbtSign
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (allowNonDefaultSighash : Bool)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (silentPaymentTx : Option (PsbtSpTx Affine))
    (s : AppPersistentState) :
    Except (VerifiedPsbtSignError × AppPersistentState)
           (InternalSpec.Psbt.ValidatedPsbt × AppResponse × AppPersistentState) :=
  match buildVerifiedPsbtSignRequest profile net hw dev policyOra hash160 allowNonDefaultSighash
          descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt s.swapLock
          standardSignTasks musigPlan silentPaymentTx with
  | .error vErr =>
      let abortSwap : Bool :=
        s.swapLock.isSome &&
        match vErr with
        | .invalidSwapLockMode
        | .psbtRejected .swapPolicyOrWarningViolation
        | .psbtRejected .swapOutputCountMismatch
        | .psbtRejected .swapInvalidCrossChainPayin
        | .psbtRejected .swapFeeMismatch
        | .psbtRejected .swapAmountMismatch
        | .psbtRejected .swapDestinationMismatch => true
        | _ => false
      let s' := if abortSwap then { s with swapAborted := true } else s
      .error (vErr, s')
  | .ok (validated, req) =>
      match stepAppCommand profile hw ui (.signPsbt req) s with
      | .error (appErr, s') => .error (.appRejected appErr, s')
      | .ok (resp, s') => .ok (validated, resp, s')

/-- End-to-end verified BIP-322 message-signing via `SIGN_PSBT` (`verifyPsbtSignMessage`):
    1. Rejects immediately if `s.swapLock.isSome` (`.psbtRejected .bip322ForbiddenInSwap`).
    2. Requires `psbt.bip322Message` to be explicitly present and byte-for-byte equal to `message`
       (`.psbtRejected .bip322InvalidStructure`).
    3. Executes `stepVerifiedPsbtSign` (which verifies `WalletPolicy`, Merkle openings, UTXO commitments,
       `validateBip322Psbt` challenge `to_spend` txid `bip322ToSpendTxid` + proof-of-funds `nSequence`,
       and user-consent-gated `stepAppCommand`). -/
def verifyPsbtSignMessage
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (message : ByteArray)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (s : AppPersistentState) :
    Except (VerifiedPsbtSignError × AppPersistentState)
           (InternalSpec.Psbt.ValidatedPsbt × AppResponse × AppPersistentState) :=
  if s.swapLock.isSome then
    .error (.psbtRejected .bip322ForbiddenInSwap, s)
  else if !decide (psbt.bip322Message = some message) then
    .error (.psbtRejected .bip322InvalidStructure, s)
  else
    stepVerifiedPsbtSign profile net hw ui dev policyOra hash160 false
      descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
      standardSignTasks musigPlan none s

end BitcoinLedger.AppStateMachine

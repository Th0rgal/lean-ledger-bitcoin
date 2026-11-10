/-
  Spec/AppStateMachine.lean

  Unified top-level command & session state machine for the Ledger Bitcoin
  application across both reference targets:
    - LedgerHQ/app-bitcoin (BOLOS native C app: `src/main.c`, `src/commands.h`,
      `src/boilerplate/dispatcher.c`, `src/handler/*`, `src/swap/*`)
    - LedgerHQ/vanadium (`apps/bitcoin/common/src/message/mod.rs`,
      `apps/bitcoin/common/src/{identity,por}.rs`, `apps/bitcoin/app/src/{main,resident_key,sp_keys}.rs`,
      `apps/bitcoin/app/src/handlers/*`)
-/
import Spec.Musig2
import Spec.SilentPayments

namespace Spec.AppStateMachine

open Spec.Musig2
open Spec.SilentPayments

/-! ## 1. Wire Constants, Target Profiles & Byte Helpers -/

/-- BOLOS APDU instruction classes (`src/constants.h`, `bitcoin_client_rs/src/apdu.rs`). -/
def bolosClaDefault : UInt8 := 0xB0
def bolosClaApp : UInt8 := 0xE1
def bolosClaFramework : UInt8 := 0xF8

/-- BOLOS `CLA = 0xE1` / `0xB0` / `0xF8` instruction codes. -/
def bolosInsGetExtendedPubkey : UInt8 := 0x00
def bolosInsGetVersion : UInt8 := 0x01
def bolosInsContinue : UInt8 := 0x01
def bolosInsRegisterWallet : UInt8 := 0x02
def bolosInsGetWalletAddress : UInt8 := 0x03
def bolosInsSignPsbt : UInt8 := 0x04
def bolosInsGetMasterFingerprint : UInt8 := 0x05
def bolosInsSignMessage : UInt8 := 0x10

/-- BOLOS APDU protocol version (`CURRENT_PROTOCOL_VERSION = 1`). -/
def bolosCurrentProtocolVersion : UInt8 := 1

/-- BOLOS maximum BIP-32 path length (`MAX_BIP32_PATH_STEPS = 10`), vs Vanadium's `MAX_BIP32_PATH_LEN = 16`
    on `KeyTree::Standard` (`bip32.rs:19`) and `256` wire ceiling on `KeyTree::Resident` (`get_extended_pubkey.rs:138`). -/
def bolosMaxBip32PathSteps : Nat := 10
def vanadiumStandardMaxBip32PathSteps : Nat := 16
def vanadiumMaxBip32PathSteps : Nat := 256

/-- Recommended maximum BIP-44 account index for silent pubkey export (`MAX_BIP44_ACCOUNT_RECOMMENDED = 100`). -/
def maxBip44AccountRecommended : UInt32 := 100

/-- Recommended maximum default-wallet address index (`MAX_BIP44_ADDRESS_INDEX_RECOMMENDED = 50000`). -/
def maxDefaultAddressIndex : UInt32 := 50000

/-- Maximum cleartext-displayable Bitcoin Signed Message length on BOLOS (`MAX_DISPLAYBLE_MESSAGE_LENGTH = 640`). -/
def maxDisplayableMessageLength : Nat := 640

/-- Exclusive upper bound on Bitcoin Signed Message byte length (`2^32`). -/
def maxSignMessageLength : Nat := 0x100000000

/-- Hardened child flag (`0x80000000`). -/
def hardenedFlag : UInt32 := 0x80000000

/-- Electrum legacy encryption path `m/4541509'/1112098098'` whitelisted on BOLOS. -/
def electrumPathStep0 : UInt32 := 4541509 ||| hardenedFlag
def electrumPathStep1 : UInt32 := 1112098098 ||| hardenedFlag

/-- Vanadium Identity Key hardened root path component `1229210958'` (`"IDEN"`). -/
def identityRootPathComponent : UInt32 := 1229210958 ||| hardenedFlag

/-- Execution target profile controlling BOLOS-specific vs Vanadium-specific rules. -/
inductive TargetProfile where
  | bolos (coinType : UInt32)
  | vanadium (coinType : UInt32)
  deriving Repr, DecidableEq

def TargetProfile.coinType : TargetProfile → UInt32
  | .bolos ct => ct
  | .vanadium ct => ct

def TargetProfile.maxPathSteps : TargetProfile → Nat
  | .bolos _ => bolosMaxBip32PathSteps
  | .vanadium _ => vanadiumMaxBip32PathSteps

def TargetProfile.musigAggPkMode : TargetProfile → NonceAggPkMode
  | .bolos _ => .untweakedBolos
  | .vanadium _ => .tweakedVanadium

/-- Application semantic version (`2.4.1`). -/
structure AppVersion where
  major : UInt8
  minor : UInt8
  patch : UInt8
  deriving Repr, DecidableEq, Inhabited

def targetAppVersion : AppVersion :=
  { major := 2, minor := 4, patch := 1 }

/-- Pure kernel-reducible `ByteArray` concatenation. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl appendBytes (ByteArray.mk #[])

/-- Encode a 16-bit unsigned integer in little-endian (for Bitcoin CompactSize varints). -/
def encodeU16LE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF)
  ]

/-- Encode a 32-bit unsigned integer in little-endian (for Bitcoin CompactSize varints). -/
def encodeU32LEBytes (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (n &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 24) &&& 0xFF)
  ]

/-- Encode a 64-bit unsigned integer in little-endian (for Bitcoin CompactSize varints). -/
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

/-- Bitcoin CompactSize (`varint`) encoding (`0..252` 1B, `0xFD` + u16LE, `0xFE` + u32LE, `0xFF` + u64LE). -/
def encodeVarint (n : Nat) : ByteArray :=
  if n < 0xFD then
    ByteArray.mk #[UInt8.ofNat n]
  else if n ≤ 0xFFFF then
    appendBytes (ByteArray.mk #[0xFD]) (encodeU16LE n)
  else if n ≤ 0xFFFFFFFF then
    appendBytes (ByteArray.mk #[0xFE]) (encodeU32LEBytes n)
  else
    appendBytes (ByteArray.mk #[0xFF]) (encodeU64LEBytes n)

/-! ## 2. Bitcoin `SIGN_MESSAGE` Specification (`sign_message.c` & BIP-137) -/

/-- Exact 25-byte `"\x18Bitcoin Signed Message:\n"` magic prefix (`sign_message.c:35-37`). -/
def bitcoinSignedMessageMagic : ByteArray :=
  ByteArray.mk #[
    0x18,
    0x42, 0x69, 0x74, 0x63, 0x6F, 0x69, 0x6E, 0x20, -- "Bitcoin "
    0x53, 0x69, 0x67, 0x6E, 0x65, 0x64, 0x20,       -- "Signed "
    0x4D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65, 0x3A, -- "Message:"
    0x0A                                             -- "\n"
  ]

theorem bitcoinSignedMessageMagic_size : bitcoinSignedMessageMagic.size = 25 := by
  rfl

/-- Printable ASCII check from `sign_message.c:78-115`:
    Returns `true` iff `msg.size ≤ 640` and every byte is printable ASCII (`0x20..0x7E`) or LF (`0x0A`).
    When `false`, the device UI displays the uppercase hex `SHA256(msg)` instead of raw bytes. -/
def isPrintableAsciiMessage (msg : ByteArray) : Bool :=
  msg.size ≤ maxDisplayableMessageLength &&
  listAll (fun b => (0x20 ≤ b && b ≤ 0x7E) || decide (b = 0x0A)) msg.data.toList

/-- Format mode shown on the hardware screen when confirming `SIGN_MESSAGE`. -/
inductive MessageDisplayForm where
  | cleartextAscii (raw : ByteArray)
  | sha256Digest (digest : Spec.Musig2.Bytes32)
  deriving DecidableEq

/-- Preimage hashed under double-SHA256 for Bitcoin `SIGN_MESSAGE`:
    `"\x18Bitcoin Signed Message:\n" || varint(msg.size) || msg`. -/
def bitcoinSignedMessagePreimage (msg : ByteArray) : ByteArray :=
  concatBytes [bitcoinSignedMessageMagic, encodeVarint msg.size, msg]

/-- Double-SHA256 Bitcoin Signed Message digest (`SHA256(SHA256(magic || varint(len) || msg))`). -/
def bitcoinSignedMessageDigest (sha256 : ByteArray → Spec.Musig2.Bytes32)
    (msg : ByteArray) : Spec.Musig2.Bytes32 :=
  let first := sha256 (bitcoinSignedMessagePreimage msg)
  sha256 first.bytes

/-- Address / header flag convention for 65-byte compact recoverable signatures (BIP-137 / BOLOS):
    - `.compressedP2pkh` (`31 + recId`, BOLOS `sign_message.c:186` `27 + 4 + parity`)
    - `.uncompressedP2pkh` (`27 + recId`)
    - `.p2shP2wpkh` (`35 + recId`)
    - `.p2wpkh` (`39 + recId`) -/
inductive CompactSigHeaderBase where
  | uncompressedP2pkh
  | compressedP2pkh
  | p2shP2wpkh
  | p2wpkh
  deriving Repr, DecidableEq

def CompactSigHeaderBase.baseByte : CompactSigHeaderBase → UInt8
  | .uncompressedP2pkh => 27
  | .compressedP2pkh => 31
  | .p2shP2wpkh => 35
  | .p2wpkh => 39

/-- Construct the 65-byte Bitcoin compact recoverable signature `(base + recId) || r (32B) || s (32B)`
    for `recId ∈ {0, 1, 2, 3}` (BOLOS emits `base = 31`, `recId = parity ∈ {0, 1}`). -/
def formatCompactRecoverableSig (headerBase : CompactSigHeaderBase) (recId : UInt8)
    (r s : Spec.Musig2.Bytes32) : Option Spec.SilentPayments.Bytes65 :=
  if recId > 3 then
    none
  else
    let hdr : Spec.SilentPayments.SizedBytes 1 :=
      ⟨ByteArray.mk #[headerBase.baseByte + recId], rfl⟩
    let r32 : Spec.SilentPayments.Bytes32 := ⟨r.bytes, r.size_eq⟩
    let s32 : Spec.SilentPayments.Bytes32 := ⟨s.bytes, s.size_eq⟩
    some (Spec.SilentPayments.SizedBytes.append hdr (Spec.SilentPayments.SizedBytes.append r32 s32))

/-! ## 3. `GetExtendedPubkey` Path Policy & Vanadium Identity Keys -/

/-- BOLOS `is_path_safe_for_pubkey_export` (`get_extended_pubkey.c:36-110`):
    Whitelists Electrum `m/4541509'/1112098098'` and standard BIP-44/45/48/49/84/86/87 paths
    with matching `coinType`, `account ≤ 100`, BIP-48 `script_type ∈ {1', 2'}`, and unhardened suffix. -/
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
      if path.length < hLen then
        false
      else
        let prefixHardened := listAll (fun step => step >= hardenedFlag) (path.take hLen)
        let suffixUnhardened := listAll (fun step => step < hardenedFlag) (path.drop hLen)
        let ctMatch := decide ((p1 &&& 0x7FFFFFFF) = coinType)
        let accOk := (p2 &&& 0x7FFFFFFF) ≤ maxBip44AccountRecommended
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

/-- Vanadium `is_identity_path` (`identity.rs:38-44`):
    - `some none` for root identity key `m/1229210958'`
    - `some (some i)` for `i`-th identity key `m/1229210958'/i`
    - `none` otherwise. -/
def classifyIdentityPath : List UInt32 → Option (Option UInt32)
  | [root] => if decide (root = identityRootPathComponent) then some none else none
  | [root, idx] => if decide (root = identityRootPathComponent) then some (some idx) else none
  | _ => none

/-- Vanadium `IdentityKey::new` validation: first byte of 33-byte SEC1 pubkey must be `0x02` or `0x03`. -/
def isValidCompressedSec1Prefix (pk : CompressedPubKey) : Bool :=
  match pk.bytes.data.toList with
  | b0 :: _ => decide (b0 = 0x02) || decide (b0 = 0x03)
  | [] => false

/-- Exact 13-byte `"\x0CIDENTITY_KEY"` magic prefix (`identity.rs:46`). -/
def identityKeyMagic : ByteArray :=
  ByteArray.mk #[0x0C, 0x49, 0x44, 0x45, 0x4E, 0x54, 0x49, 0x54, 0x59, 0x5F, 0x4B, 0x45, 0x59]

/-- Exact 10-byte `"\x09IDEN/SIGN"` magic prefix (`identity.rs:11`). -/
def identitySignMagic : ByteArray :=
  ByteArray.mk #[0x09, 0x49, 0x44, 0x45, 0x4E, 0x2F, 0x53, 0x49, 0x47, 0x4E]

def identityMsgTypeXpub : ByteArray := ByteArray.mk #[0x58, 0x50, 0x55, 0x42] -- "XPUB"
def identityMsgTypeOutput : ByteArray := ByteArray.mk #[0x4F, 0x55, 0x54, 0x50, 0x55, 0x54] -- "OUTPUT"

/-- Vanadium `build_identity_message(msg_type, object)`:
    `"\x09IDEN/SIGN" || u8(msg_type.size) || msg_type || u8(object.size) || object`,
    rejecting either field if its byte length exceeds `255`. -/
def buildIdentityMessage (msgType object : ByteArray) : Option ByteArray :=
  if msgType.size > 255 || object.size > 255 then
    none
  else
    some (concatBytes [
      identitySignMagic,
      ByteArray.mk #[UInt8.ofNat msgType.size],
      msgType,
      ByteArray.mk #[UInt8.ofNat object.size],
      object
    ])

/-- Vanadium `IdentityKey::get_id(name)`:
    `SHA256("\x0CIDENTITY_KEY" || u8(name.utf8ByteSize) || name.toUTF8 || pubkey)`. -/
def computeIdentityRegistrationId (sha256 : ByteArray → Spec.Musig2.Bytes32)
    (name : String) (pubkey : CompressedPubKey) : Option Spec.Musig2.Bytes32 :=
  let nameBytes := name.toUTF8
  if nameBytes.size == 0 || nameBytes.size > 255 then
    none
  else
    some (sha256 (concatBytes [
      identityKeyMagic,
      ByteArray.mk #[UInt8.ofNat nameBytes.size],
      nameBytes,
      pubkey.bytes
    ]))

/-- Schnorr signature authenticating an xpub or output script under an identity key (`message/mod.rs:116`). -/
structure IdentitySignature where
  identityPubkey : CompressedPubKey
  signature : SchnorrSig
  deriving Repr, DecidableEq

/-- Registered cosigner identity key + Proof of Registration supplied during `RegisterAccount`. -/
structure RegisteredIdentityEntry where
  pubkey : CompressedPubKey
  name : String
  por : Spec.Musig2.Bytes32
  deriving Repr, DecidableEq

/-! ## 4. Unified Account, PSBT & Swap Domain Types -/

/-- BIP-32 derivation tree selector (`KeyTree::Standard` vs Vanadium `KeyTree::Resident`). -/
inductive KeyTree where
  | standard
  | resident
  deriving Repr, DecidableEq

/-- Abstract Wallet Policy summary (connecting cleanly to Track S2 `Spec/WalletPolicy.lean` at Wave 1). -/
structure WalletPolicySpec where
  name : String
  version : UInt8
  descriptorTemplate : String
  nKeys : Nat
  nInternalKeys : Nat
  isDefaultPolicy : Bool
  isSignable : Bool
  walletId : Spec.Musig2.Bytes32
  keysInfoPayloads : List ByteArray
  deriving DecidableEq

/-- Unified Account (`WalletPolicy` on both targets, `SilentPayment` on Vanadium). -/
inductive AccountSpec (Affine : Type) where
  | walletPolicy (policy : WalletPolicySpec)
  | silentPayment (name : String) (spAccount : SilentPaymentAccount Affine) (accountId : Spec.Musig2.Bytes32)
  deriving DecidableEq

/-- Coordinates for `GetAddress`. -/
inductive AddressCoordinates where
  | walletPolicy (isChange : Bool) (addressIndex : UInt32)
  | silentPayment (coords : SilentPaymentCoordinates)
  deriving Repr, DecidableEq

/-- Ledger Swap protocol mode (`swap_globals.h` & `handle_swap_sign_transaction.c:71-90`). -/
inductive SwapMode where
  | standard
  | crossChain (payinHash : Spec.Musig2.Bytes32)
  | invalidMode
  deriving Repr, DecidableEq

/-- Active pre-approved Ledger Exchange `SwapLock` (`G_called_from_swap` + `G_swap_state`). -/
structure SwapLock where
  amount : UInt64
  fees : UInt64
  destinationAddress : String
  mode : SwapMode
  deriving Repr, DecidableEq

/-- External output view used by `execute_swap_checks` (`swap_checks.c`). -/
structure ExternalOutputView where
  amount : UInt64
  script : ByteArray
  formattedAddress : Option String
  deriving DecidableEq

/-- Check cross-chain Swap first external output (`OP_RETURN <single_push>` with value `0` and
    `SHA256(pushed_data) == expectedPayinHash`, matching `swap_checks.c:115-168`). -/
def validCrossChainOpReturn (sha256 : ByteArray → Spec.Musig2.Bytes32)
    (out : ExternalOutputView) (expectedPayinHash : Spec.Musig2.Bytes32) : Bool :=
  if decide (out.amount ≠ 0) then
    false
  else
    let bs := out.script.data.toList
    match bs with
    | 0x6A :: secondByte :: rest =>
      if 2 ≤ secondByte && secondByte ≤ 75 then
        let dataLen := secondByte.toNat
        if out.script.size != 2 + dataLen then
          false
        else
          let payload := ByteArray.mk rest.toArray
          sha256 payload == expectedPayinHash
      else if decide (secondByte = 0x4C) then -- OP_PUSHDATA1
        match rest with
        | lenByte :: payloadList =>
          let dataLen := lenByte.toNat
          if out.script.size < 4 || out.script.size != 3 + dataLen then
            false
          else
            let payload := ByteArray.mk payloadList.toArray
            sha256 payload == expectedPayinHash
        | [] => false
      else
        false
    | _ => false

/-- Standard non-MuSig signature produced for a PSBT input (`PartialSignature`). -/
structure StandardInputSigRequest where
  inputIndex : UInt32
  derivationPath : List UInt32
  sighash : Spec.Musig2.Bytes32
  isSchnorr : Bool
  leafHash : Option Spec.Musig2.Bytes32
  deriving Repr, DecidableEq

structure StandardInputSignature where
  inputIndex : UInt32
  signature : ByteArray
  pubkey : CompressedPubKey
  leafHash : Option Spec.Musig2.Bytes32
  deriving DecidableEq

/-- MuSig2 phase behavior within a `SIGN_PSBT` request (`sign_psbt.c:99-140`, `musig_signing.rs`). -/
inductive PsbtMusigPlan where
  | none
  | round1Only (sid : PsbtSessionId) (tasks : List MusigSignTask)
  | round1AndStandard (sid : PsbtSessionId) (tasks : List MusigSignTask)
  | round2 (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
  deriving Repr, DecidableEq

/-- Logical PSBT signing request combining account authentication, Swap metadata, BIP-322 flag,
    standard input signatures, MuSig2 Round-1/Round-2 plan, and BIP-375 Silent Payments. -/
structure PsbtSignRequest (Affine : Type) where
  account : AccountSpec Affine
  por : Option Spec.Musig2.Bytes32
  isBip322MessageSigning : Bool
  inputsTotalAmount : UInt64
  outputsTotalAmount : UInt64
  changeOutputsTotalAmount : UInt64
  nExternalInputs : Nat
  missingNonWitnessUtxo : Bool
  nonDefaultSighash : Bool
  externalOutputs : List ExternalOutputView
  standardSignTasks : List StandardInputSigRequest
  musigPlan : PsbtMusigPlan
  silentPaymentTx : Option PsbtSpTx
  deriving DecidableEq

/-- Validate all BOLOS `execute_swap_checks` + `sign_psbt.c:55` invariants for bypassing interactive UI
    under a pre-approved `SwapLock`. -/
def validSwapPsbt {Affine : Type} (sha256 : ByteArray → Spec.Musig2.Bytes32)
    (lock : SwapLock) (req : PsbtSignRequest Affine) : Bool :=
  let isDefaultWallet :=
    match req.account with
    | .walletPolicy wp => wp.isDefaultPolicy && req.por.isNone
    | .silentPayment _ _ _ => false
  if !isDefaultWallet then
    false
  else if req.isBip322MessageSigning then
    false
  else if req.nExternalInputs > 0 then
    false
  else if req.missingNonWitnessUtxo || req.nonDefaultSighash then
    false
  else if req.inputsTotalAmount < req.outputsTotalAmount then
    false
  else if req.outputsTotalAmount < req.changeOutputsTotalAmount then
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
        | [destOut] => destOut.formattedAddress == some lock.destinationAddress
        | _ => false
      | .crossChain expectedPayinHash =>
        match req.externalOutputs with
        | [opRetOut, destOut] =>
          validCrossChainOpReturn sha256 opRetOut expectedPayinHash &&
          destOut.formattedAddress == some lock.destinationAddress
        | _ => false

/-! ## 5. BOLOS APDU & Vanadium CBOR Command Surfaces -/

/-- Raw BOLOS APDU frame (`CLA`, `INS`, `P1`, `P2`, `Lc = data.size`). -/
structure BolosApduHeader where
  cla : UInt8
  ins : UInt8
  p1 : UInt8
  p2 : UInt8
  deriving Repr, DecidableEq

/-- Decoded BOLOS APDU command classification (`main.c`, `dispatcher.c`, `bitcoin_client_rs/src/apdu.rs`). -/
inductive BolosWireCommand where
  | getVersion
  | getMasterFingerprint
  | getExtendedPubkey
  | registerWallet
  | getWalletAddress
  | signPsbt
  | signMessage
  | unexpectedContinue
  | wrongP1P2
  | claNotSupported
  | insNotSupported
  deriving Repr, DecidableEq

/-- Classify a top-level BOLOS APDU header, including Swap-mode command filtering (`main.c:152-165`)
    and `dispatcher.c:135-165` (`p2 <= CURRENT_PROTOCOL_VERSION`, unexpected `0xF8/0x01`). -/
def classifyBolosApdu (inSwapMode : Bool) (hdr : BolosApduHeader) : BolosWireCommand :=
  if inSwapMode then
    if decide (hdr.cla ≠ bolosClaApp) then
      .claNotSupported
    else if hdr.p2 > bolosCurrentProtocolVersion then
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
  else if hdr.p2 > bolosCurrentProtocolVersion then
    .wrongP1P2
  else if decide (hdr.cla = bolosClaFramework) && decide (hdr.ins = bolosInsContinue) then
    .unexpectedContinue
  else if decide (hdr.cla = bolosClaApp) then
    if decide (hdr.ins = bolosInsGetExtendedPubkey) then .getExtendedPubkey
    else if decide (hdr.ins = bolosInsGetVersion) then .getVersion
    else if decide (hdr.ins = bolosInsRegisterWallet) then .registerWallet
    else if decide (hdr.ins = bolosInsGetWalletAddress) then .getWalletAddress
    else if decide (hdr.ins = bolosInsSignPsbt) then .signPsbt
    else if decide (hdr.ins = bolosInsGetMasterFingerprint) then .getMasterFingerprint
    else if decide (hdr.ins = bolosInsSignMessage) then .signMessage
    else .insNotSupported
  else
    .claNotSupported

/-- Vanadium CBOR `Request` variant indices (`common/src/message/mod.rs:139-233`). -/
inductive VanadiumRequestTag where
  | getVersion                  -- #[n(0)]
  | exit                        -- #[n(1)]
  | getMasterFingerprint        -- #[n(2)]
  | getExtendedPubkey           -- #[n(3)]
  | registerAccount             -- #[n(4)]
  | getAddress                  -- #[n(5)]
  | signPsbt                    -- #[n(6)]
  | registerIdentityKey         -- #[n(7)]
  | exportSilentPaymentScanKey  -- #[n(8)]
  deriving Repr, DecidableEq

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

/-- Unified top-level command sum across BOLOS (`CLA=0xE1`/`0xB0`/`0xF8` + Swap) and Vanadium (`Request`). -/
inductive AppCommand (Affine : Type) where
  | getVersion
  | getMasterFingerprint (tree : KeyTree)
  | getExtendedPubkey
      (tree : KeyTree)
      (display : Bool)
      (path : List UInt32)
      (identityIndex : Option UInt32)
  | registerAccount
      (account : AccountSpec Affine)
      (registeredIdentities : List RegisteredIdentityEntry)
      (keySignatures : List (Option IdentitySignature))
      (showCleartext : Bool)
  | getAddress
      (display : Bool)
      (account : AccountSpec Affine)
      (por : Option Spec.Musig2.Bytes32)
      (coordinates : AddressCoordinates)
      (identityIndex : Option UInt32)
  | signMessage
      (path : List UInt32)
      (message : ByteArray)
      (headerBase : CompactSigHeaderBase)
  | signPsbt
      (psbt : PsbtSignRequest Affine)
  | exportSpScanKey
      (hrp : SpScanHrp)
      (accountIndex : UInt32)
  | registerIdentityKey
      (name : String)
      (pubkey : CompressedPubKey)
  | unexpectedContinue
  deriving DecidableEq

/-- Predicate identifying read-only query commands. -/
def AppCommand.isReadOnly {Affine : Type} : AppCommand Affine → Bool
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

/-- Unified application response type. -/
inductive AppResponse where
  | version (v : AppVersion)
  | masterFingerprint (fpr : UInt32)
  | extendedPubkey (xpub : ByteArray) (identitySig : Option IdentitySignature)
  | accountRegistered (accountId : Spec.Musig2.Bytes32) (hmac : Spec.Musig2.Bytes32)
  | address (addr : String) (identitySig : Option IdentitySignature)
  | messageSigned (compactSig : Spec.SilentPayments.Bytes65)
  | psbtSigned
      (signatures : List StandardInputSignature)
      (musigPubnonces : List MusigRound1Output)
      (musigPartialSigs : List MusigRound2Output)
      (spShares : List SilentPaymentShareOut)
      (spOutputScripts : List SilentPaymentOutputScriptOut)
      (swapCompleted : Bool)
  | spScanKeyExported (encodedKey : String)
  | identityKeyRegistered (keyId : Spec.Musig2.Bytes32) (hmac : Spec.Musig2.Bytes32)
  deriving DecidableEq

/-- Unified error codes mapping cleanly to BOLOS status words (`sw.h`) and Vanadium `common::errors::Error`. -/
inductive AppError where
  | userRejected                        -- SW_DENY (0x6985) / Error::UserRejected
  | incorrectData                       -- SW_INCORRECT_DATA (0x6A80) / InvalidParameter / InvalidRequest
  | notSupported                        -- SW_NOT_SUPPORTED (0x6A82) / DefaultAccountsNotSupported
  | wrongP1P2                           -- SW_WRONG_P1P2 (0x6A86)
  | insNotSupported                     -- SW_INS_NOT_SUPPORTED (0x6D00)
  | claNotSupported                     -- SW_CLA_NOT_SUPPORTED (0x6E00)
  | failSwap                            -- SW_FAIL_SWAP (0x6B00)
  | badState                            -- SW_BAD_STATE (0xB007)
  | signatureFail                       -- SW_SIGNATURE_FAIL (0xB008) / InvalidProofOfRegistration / InvalidIdentitySignature
  | derivationPathTooLong               -- SW_INCORRECT_DATA / Error::DerivationPathTooLong
  | keyDerivationFailed                 -- Error::KeyDerivationFailed
  | musigError (err : MusigError)
  | silentPaymentError (err : SpError)
  deriving Repr, DecidableEq

/-! ## 6. Persistent State, `HardwareOracle` & `UserApprovalOracle` -/

/-- Persistent application state across commands (`AppPersistentState`):
    - `registeredAccounts`: logical registry of device-registered `(accountId, hmac)` pairs
    - `musigSessions`: persistent BIP-327 MuSig2 session store (tracking active `randRoot`s & consumed IDs)
    - `swapLock`: optional pre-approved BOLOS Exchange `SwapLock`
    - `residentKeys`: optional 32-byte Vanadium resident seed (`KeyTree::Resident`) -/
structure AppPersistentState where
  registeredAccounts : List (Spec.Musig2.Bytes32 × Spec.Musig2.Bytes32) := []
  musigSessions : MusigSessionStore := {}
  swapLock : Option SwapLock := none
  residentKeys : Option Spec.Musig2.Bytes32 := none
  deriving Repr, DecidableEq

instance : Inhabited AppPersistentState :=
  ⟨{}⟩

/-- Explicit user-confirmation prompts presented on the Secure Screen. -/
inductive UserPrompt (Affine : Type) where
  | confirmExtendedPubkey (tree : KeyTree) (path : List UInt32) (xpub : ByteArray)
  | confirmIdentityPubkey (index : Option UInt32) (xpub : ByteArray)
  | confirmAddress (account : AccountSpec Affine) (coordinates : AddressCoordinates) (addr : String)
  | confirmRegisterAccount (account : AccountSpec Affine) (showCleartext : Bool)
  | confirmRegisterIdentityKey (name : String) (pubkey : CompressedPubKey)
  | confirmSignMessage (path : List UInt32) (displayForm : MessageDisplayForm)
  | confirmSignPsbt (psbt : PsbtSignRequest Affine)
  | confirmExportSpScanKey (accountIndex : UInt32)
  deriving DecidableEq

/-- Explicit `UserApprovalOracle`: returns `true` iff the physical user inspects and approves `prompt`. -/
structure UserApprovalOracle (Affine : Type) where
  approve : UserPrompt Affine → Bool

/-- Explicit `HardwareOracle`: encapsulates Secure Element / V-App cryptographic & RNG primitives. -/
structure HardwareOracle (Affine : Type) where
  musigCrypto : MusigCrypto Affine
  spCrypto : SpCrypto Affine
  bech32m : Bech32mCodec
  /-- Master key fingerprint for `KeyTree::Standard`, or derived from `residentSeed` for `KeyTree::Resident`. -/
  masterFingerprint : KeyTree → Option Spec.Musig2.Bytes32 → Option UInt32
  /-- Derive serialized 78-byte BIP-32 extended pubkey & compressed key at `path`. -/
  deriveExtendedPubkey : KeyTree → Option Spec.Musig2.Bytes32 → List UInt32 → Option (ByteArray × CompressedPubKey)
  /-- Derive `m/"Proof of Registration"` SLIP-21 HMAC-SHA256 tag over a 32-byte `registrationId`. -/
  computePorHmac : Spec.Musig2.Bytes32 → Spec.Musig2.Bytes32
  /-- Sign a 32-byte digest with recoverable ECDSA at `path`, returning `(recId ∈ 0..3, r, s)`. -/
  signRecoverableEcdsa : List UInt32 → Spec.Musig2.Bytes32 → Option (UInt8 × Spec.Musig2.Bytes32 × Spec.Musig2.Bytes32)
  /-- Sign a 32-byte sighash for a standard PSBT input (`DER || sighashByte` or 64/65B Schnorr). -/
  signPsbtInput : StandardInputSigRequest → Option (ByteArray × CompressedPubKey)
  /-- Produce a Vanadium BIP-340 identity signature over `build_identity_message(msgType, obj)` at `m/1229210958'/i`. -/
  signWithIdentityKey : UInt32 → ByteArray → Option IdentitySignature
  /-- Verify a BIP-340 Schnorr signature over `msg` against compressed `pubkey`. -/
  verifySchnorr : CompressedPubKey → ByteArray → SchnorrSig → Bool
  /-- Derive the device's `SilentPaymentAccount` for `accountIndex < 2^31`. -/
  deriveSpAccount : UInt32 → Except SpError (SilentPaymentAccount Affine)
  /-- Derive address string and raw `scriptPubKey` for a `WalletPolicySpec` at `(isChange, addressIndex)`. -/
  deriveWalletPolicyOutput : WalletPolicySpec → Bool → UInt32 → Option (String × ByteArray)
  /-- Fresh 32-byte CSPRNG draw for MuSig2 Round-1 `randRoot`. -/
  freshMusigRandRoot : RandRoot
  /-- Fresh 32-byte CSPRNG draw for BIP-374 DLEQ proof generation. -/
  freshDleqAuxRand : Spec.SilentPayments.Bytes32

/-! ## 7. Helper Validation Routines -/

/-- Validate Proof-of-Registration (or default-policy rules on BOLOS vs Vanadium). -/
def validateAccountAuth {Affine : Type} (profile : TargetProfile) (hw : HardwareOracle Affine)
    (inSwapMode : Bool) (account : AccountSpec Affine) (porOpt : Option Spec.Musig2.Bytes32) :
    Except AppError Unit :=
  match account with
  | .walletPolicy wp =>
    if !wp.isSignable then
      .error .incorrectData
    else
      match porOpt with
      | none =>
        match profile with
        | .vanadium _ => .error .notSupported -- Error::DefaultAccountsNotSupported
        | .bolos _ =>
          if wp.isDefaultPolicy && wp.name.isEmpty then
            .ok ()
          else
            .error .incorrectData
      | some por =>
        if por.isAllZeros then
          match profile with
          | .vanadium _ =>
            if hw.computePorHmac wp.walletId == por then .ok () else .error .signatureFail
          | .bolos _ =>
            if wp.isDefaultPolicy && wp.name.isEmpty then .ok () else .error .incorrectData
        else if inSwapMode then
          .error .failSwap
        else if hw.computePorHmac wp.walletId == por then
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
          if hw.computePorHmac accId == por && spAcc.accountIndex < bip32HardenedBit then
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
      if idx >= hardenedFlag then
        .error .incorrectData
      else
        match buildIdentityMessage msgType object with
        | none => .error .incorrectData
        | some msg =>
          match hw.signWithIdentityKey idx msg with
          | some sig => .ok (some sig)
          | none => .error .badState

/-- Verify registered cosigner identity PoRs and optional per-key xpub signatures in `RegisterAccount`. -/
def verifyRegisteredIdentityAuth {Affine : Type} (hw : HardwareOracle Affine)
    (entries : List RegisteredIdentityEntry)
    (keyInfos : List ByteArray)
    (keySigs : List (Option IdentitySignature)) : Except AppError Unit := do
  let validPubkeys ← entries.mapM (fun entry => do
    if !isValidCompressedSec1Prefix entry.pubkey then
      .error .signatureFail
    let regId ← match computeIdentityRegistrationId hw.musigCrypto.sha256 entry.name entry.pubkey with
      | some id => .ok id
      | none => .error .signatureFail
    if hw.computePorHmac regId != entry.por then
      .error .signatureFail
    .ok entry.pubkey)
  for (keyPayload, sigOpt) in keyInfos.zip keySigs do
    match sigOpt with
    | none => pure ()
    | some sig =>
      if !listMem sig.identityPubkey validPubkeys then
        .error .signatureFail
      let msg ← match buildIdentityMessage identityMsgTypeXpub keyPayload with
        | some m => .ok m
        | none => .error .incorrectData
      if !hw.verifySchnorr sig.identityPubkey msg sig.signature then
        .error .signatureFail

/-! ## 8. Unified Command Step Function (`stepAppCommand`) -/

/-- Sign all standard (non-MuSig2) PSBT inputs via `hw.signPsbtInput`, failing atomically with
    `.badState` if any input signature fails. -/
def signStandardInputs {Affine : Type} (hw : HardwareOracle Affine)
    (tasks : List StandardInputSigRequest) : Except AppError (List StandardInputSignature) :=
  tasks.mapM (fun req =>
    match hw.signPsbtInput req with
    | some (sigBytes, pk) =>
      Except.ok {
        inputIndex := req.inputIndex
        signature := sigBytes
        pubkey := pk
        leafHash := req.leafHash
      }
    | none => Except.error AppError.badState)

/-- Execute one top-level `AppCommand`, returning either `.error (err, postState)` or `.ok (resp, postState)`.
    Making `postState` explicit on both `.ok` and `.error` captures both atomic rollback of persistent
    accounts/swap/resident keys AND irreversible MuSig2 Round-2 nonce consumption even if a downstream
    signing check aborts mid-pass! -/
def stepAppCommand {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine)
    (s : AppPersistentState) :
    Except (AppError × AppPersistentState) (AppResponse × AppPersistentState) :=
  -- Swap-mode top-level command whitelist (`main.c:152-165`)
  if s.swapLock.isSome && !isAllowedInSwap cmd then
    .error (.insNotSupported, s)
  else
    match cmd with
    | .unexpectedContinue =>
      .error (.badState, s)

    | .getVersion =>
      .ok (.version targetAppVersion, s)

    | .getMasterFingerprint tree =>
      match profile, tree with
      | .bolos _, .resident => .error (.notSupported, s)
      | _, _ =>
        match hw.masterFingerprint tree s.residentKeys with
        | some fpr => .ok (.masterFingerprint fpr, s)
        | none => .error (.keyDerivationFailed, s)

    | .getExtendedPubkey tree display path identityIndex =>
      if path.length > profile.maxPathSteps then
        .error (.derivationPathTooLong, s)
      else
        match profile, tree with
        | .bolos _, .resident => .error (.notSupported, s)
        | _, _ =>
          let vanadiumStandardTooLong : Bool :=
            match profile, tree with
            | .vanadium _, .standard => decide (path.length > vanadiumStandardMaxBip32PathSteps)
            | _, _ => false
          if identityIndex.isSome && tree != .standard then
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
      | .error e => .error (e, s)
      | .ok () =>
        match account, coordinates with
        | .walletPolicy wp, .walletPolicy isChange addrIdx =>
          if addrIdx >= hardenedFlag then
            .error (.incorrectData, s)
          else if porOpt.isNone && addrIdx > maxDefaultAddressIndex then
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
            let spHrp : SpAddressHrp := if decide (profile.coinType = 0) then .sp else .tsp
            match deriveAccountSpAddress hw.spCrypto hw.bech32m spHrp spAcc spCoords with
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
        if wp.name.isEmpty || wp.name.utf8ByteSize > 64 || wp.nInternalKeys < 1 || !wp.isSignable then
          .error (.incorrectData, s)
        else if decide (wp.version = 1) && wp.nInternalKeys != 1 then
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
              let reg' := if listMem entry s.registeredAccounts then s.registeredAccounts else entry :: s.registeredAccounts
              .ok (.accountRegistered wp.walletId hmac, { s with registeredAccounts := reg' })
      | .silentPayment name spAcc accId =>
        match profile with
        | .bolos _ => .error (.notSupported, s)
        | .vanadium _ =>
          if name.isEmpty || name.utf8ByteSize > 64 || !regIdentities.isEmpty || !keySigs.isEmpty then
            .error (.incorrectData, s)
          else
            match hw.deriveSpAccount spAcc.accountIndex with
            | .error spErr => .error (.silentPaymentError spErr, s)
            | .ok derivedAcc =>
              if decide (derivedAcc ≠ spAcc) then
                .error (.incorrectData, s)
              else
                let spHrp : SpAddressHrp := if decide (profile.coinType = 0) then .sp else .tsp
                match deriveAccountSpAddress hw.spCrypto hw.bech32m spHrp spAcc (.code none) with
                | .error spErr => .error (.silentPaymentError spErr, s)
                | .ok _addr =>
                  if !ui.approve (.confirmRegisterAccount account showCleartext) then
                    .error (.userRejected, s)
                  else
                    let hmac := hw.computePorHmac accId
                    let entry := (accId, hmac)
                    let reg' := if listMem entry s.registeredAccounts then s.registeredAccounts else entry :: s.registeredAccounts
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

    | .exportSpScanKey hrp accountIndex =>
      match profile with
      | .bolos _ => .error (.notSupported, s)
      | .vanadium _ =>
        let approved := ui.approve (.confirmExportSpScanKey accountIndex)
        match exportSpScanKey hw.spCrypto hw.bech32m hrp hw.deriveSpAccount accountIndex approved with
        | .error .userRejected => .error (.userRejected, s)
        | .error spErr => .error (.silentPaymentError spErr, s)
        | .ok encoded => .ok (.spScanKeyExported encoded, s)

    | .signMessage path message headerBase =>
      match profile with
      | .vanadium _ => .error (.notSupported, s)
      | .bolos _ =>
        if path.length > bolosMaxBip32PathSteps || message.size >= maxSignMessageLength then
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
              match formatCompactRecoverableSig headerBase recId r sScalar with
              | none => .error (.badState, s)
              | some compact65 => .ok (.messageSigned compact65, s)

    | .signPsbt psbt =>
      match validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
      | .error e => .error (e, s)
      | .ok () =>
        if psbt.inputsTotalAmount < psbt.outputsTotalAmount ||
           psbt.outputsTotalAmount < psbt.changeOutputsTotalAmount then
          .error (.incorrectData, s)
        else
          -- BIP-375 Silent Payment analysis & output/DLEQ computation (Vanadium)
          let spResult : Except AppError (List SilentPaymentShareOut × List SilentPaymentOutputScriptOut) :=
            match psbt.silentPaymentTx with
            | none => .ok ([], [])
            | some spTx =>
              match profile with
              | .bolos _ => .error .notSupported
              | .vanadium _ =>
                match finalizePsbtSilentPayments hw.spCrypto spTx hw.freshDleqAuxRand with
                | .error spErr => .error (.silentPaymentError spErr)
                | .ok pair => .ok pair
          match spResult with
          | .error e => .error (e, s)
          | .ok (spShares, spScripts) =>
            match psbt.musigPlan with
            | .round1Only sid r1Tasks =>
              -- Pure MuSig2 Round 1: emits ONLY public nonces (zero signatures!) and commits session
              if !psbt.standardSignTasks.isEmpty || s.swapLock.isSome then
                .error (.incorrectData, s)
              else
                match executeRound1Pass hw.musigCrypto profile.musigAggPkMode
                        s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                | .error (mErr, ms') =>
                  -- On Round-1 error, do NOT commit changes to persistent state (except any consumed tombstones, which are unchanged)
                  .error (.musigError mErr, { s with musigSessions := ms' })
                | .ok (pubnonces, msCommitted) =>
                  .ok (.psbtSigned [] pubnonces [] spShares spScripts false,
                       { s with musigSessions := msCommitted })

            | .none =>
              -- Standard (non-MuSig) PSBT signing: requires SwapLock match OR explicit user consent!
              let authorized : Except AppError Bool :=
                match s.swapLock with
                | some lock =>
                  if validSwapPsbt hw.musigCrypto.sha256 lock psbt then .ok true
                  else .error .failSwap
                | none =>
                  if ui.approve (.confirmSignPsbt psbt) then .ok false
                  else .error .userRejected
              match authorized with
              | .error e => .error (e, s)
              | .ok isSwap =>
                match signStandardInputs hw psbt.standardSignTasks with
                | .error e => .error (e, s)
                | .ok stdSigs =>
                  let nextSwap := if isSwap then none else s.swapLock
                  .ok (.psbtSigned stdSigs [] [] spShares spScripts isSwap,
                       { s with swapLock := nextSwap })

            | .round1AndStandard sid r1Tasks =>
              -- Hybrid PSBT (Round 1 MuSig2 pubnonces + standard signatures): requires Swap/UI approval
              let authorized : Except AppError Bool :=
                match s.swapLock with
                | some lock =>
                  if validSwapPsbt hw.musigCrypto.sha256 lock psbt then .ok true
                  else .error .failSwap
                | none =>
                  if ui.approve (.confirmSignPsbt psbt) then .ok false
                  else .error .userRejected
              match authorized with
              | .error e => .error (e, s)
              | .ok isSwap =>
                match signStandardInputs hw psbt.standardSignTasks with
                | .error e => .error (e, s)
                | .ok stdSigs =>
                  match executeRound1Pass hw.musigCrypto profile.musigAggPkMode
                          s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                  | .error (mErr, ms') =>
                    .error (.musigError mErr, { s with musigSessions := ms' })
                  | .ok (pubnonces, msCommitted) =>
                    let nextSwap := if isSwap then none else s.swapLock
                    .ok (.psbtSigned stdSigs pubnonces [] spShares spScripts isSwap,
                         { s with musigSessions := msCommitted, swapLock := nextSwap })

            | .round2 sid r2Inputs =>
              -- MuSig2 Round 2: verify session is unconsumed & active, gate on Swap/UI consent,
              -- then atomically consume the nonce session and produce partial signatures!
              if s.musigSessions.lookupActive sid |>.isNone then
                let errCode : MusigError :=
                  if s.musigSessions.isConsumed sid then .sessionAlreadyConsumed else .missingSession
                .error (.musigError errCode, s)
              else
                let authorized : Except AppError Bool :=
                  match s.swapLock with
                  | some lock =>
                    if validSwapPsbt hw.musigCrypto.sha256 lock psbt then .ok true
                    else .error .failSwap
                  | none =>
                    if ui.approve (.confirmSignPsbt psbt) then .ok false
                    else .error .userRejected
                match authorized with
                | .error e => .error (e, s)
                | .ok isSwap =>
                  -- Consume MuSig2 session BEFORE/DURING Round-2 signing so even if standard signing
                  -- or partial signing fails mid-way, the secret nonce session is irreversibly consumed!
                  match executeRound2Pass hw.musigCrypto profile.musigAggPkMode
                          s.musigSessions sid r2Inputs with
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

/-! ## 9. Multi-Step Trace Execution -/

/-- Outcome of a single command in a multi-step trace. -/
inductive AppTraceOutcome (Affine : Type) where
  | ok (cmd : AppCommand Affine) (resp : AppResponse)
  | error (cmd : AppCommand Affine) (err : AppError)
  deriving DecidableEq

/-- Helper to extract the post-state from an `Except (AppError × AppPersistentState) (AppResponse × AppPersistentState)`
    value without exposing an outer `match` to `split`. -/
def extractPostState :
    Except (AppError × AppPersistentState) (AppResponse × AppPersistentState) → AppPersistentState
  | .ok (_, s') => s'
  | .error (_, s') => s'

@[simp] theorem extractPostState_ok (r : AppResponse) (s' : AppPersistentState) :
    extractPostState (.ok (r, s')) = s' := rfl

@[simp] theorem extractPostState_error (e : AppError) (s' : AppPersistentState) :
    extractPostState (.error (e, s')) = s' := rfl

/-- Extract the post-state from `stepAppCommand` regardless of success or error. -/
def stepPostState {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s : AppPersistentState) : AppPersistentState :=
  extractPostState (stepAppCommand profile hw ui cmd s)

/-- Execute an arbitrary multi-step trace `[cmd_1, ..., cmd_k]` from initial state `s`. -/
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

/-- Whether a trace step successfully emitted Round-2 partial signatures for MuSig2 session `sid`. -/
def outcomeProducedMusigRound2For {Affine : Type} (sid : PsbtSessionId) : AppTraceOutcome Affine → Bool
  | .ok (.signPsbt psbt) (.psbtSigned _ _ _ _ _ _) =>
    match psbt.musigPlan with
    | .round2 sid' _ => sid' == sid
    | _ => false
  | _ => false

/-- Count how many steps in a multi-step trace successfully produced Round-2 signatures for `sid`. -/
def countMusigRound2Steps {Affine : Type} (sid : PsbtSessionId) : List (AppTraceOutcome Affine) → Nat
  | [] => 0
  | ev :: rest =>
    (if outcomeProducedMusigRound2For sid ev then 1 else 0) + countMusigRound2Steps sid rest

/-! ## 10. Core Security Theorems (`0 sorryAx`, `0 native_decide`) -/

/-- Helper lemma: when `cmd.isReadOnly = true`, `stepAppCommand` leaves `s` identically unchanged
    on BOTH `.ok` and `.error` outcomes. -/
theorem readOnly_step_postState_eq {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s : AppPersistentState)
    (hRO : cmd.isReadOnly = true) :
    stepPostState profile hw ui cmd s = s := by
  unfold stepPostState stepAppCommand
  by_cases hSwap : (s.swapLock.isSome && !isAllowedInSwap cmd) = true
  · simp [hSwap]
  · simp only [hSwap, Bool.false_eq_true, ↓reduceIte]
    cases cmd with
    | getVersion => rfl
    | getMasterFingerprint tree =>
      cases profile <;> cases tree <;> simp
      all_goals (cases hw.masterFingerprint _ s.residentKeys <;> rfl)
    | getExtendedPubkey tree display path identityIndex =>
      by_cases hLen : path.length > profile.maxPathSteps
      · simp [hLen]
      · simp only [hLen, ↓reduceIte]
        cases profile with
        | bolos ct =>
          cases tree with
          | resident => rfl
          | standard =>
            have hTreeFalse : (KeyTree.standard != KeyTree.standard) = false := rfl
            simp only [hTreeFalse, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            split
            · rfl
            · cases hw.deriveExtendedPubkey .standard s.residentKeys path with
              | none => rfl
              | some pair =>
                rcases pair with ⟨xpub, _pk⟩
                simp only
                split
                · rfl
                · cases maybeSignIdentityObject (.bolos ct) hw identityIndex identityMsgTypeXpub xpub <;> rfl
        | vanadium ct =>
          cases tree with
          | resident =>
            have hTreeTrue : (KeyTree.resident != KeyTree.standard) = true := rfl
            simp only [hTreeTrue, Bool.and_true]
            by_cases hId : identityIndex.isSome = true
            · simp [hId]
            · simp only [hId, Bool.false_eq_true, ↓reduceIte]
              cases hw.deriveExtendedPubkey .resident s.residentKeys path with
              | none => rfl
              | some pair =>
                rcases pair with ⟨xpub, _pk⟩
                simp only
                split
                · rfl
                · cases maybeSignIdentityObject (.vanadium ct) hw identityIndex identityMsgTypeXpub xpub <;> rfl
          | standard =>
            have hTreeFalse : (KeyTree.standard != KeyTree.standard) = false := rfl
            simp only [hTreeFalse, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            by_cases hStdLen : path.length > vanadiumStandardMaxBip32PathSteps
            · simp [hStdLen]
            · simp only [hStdLen, decide_false, Bool.false_eq_true, ↓reduceIte]
              cases hw.deriveExtendedPubkey .standard s.residentKeys path with
              | none => rfl
              | some pair =>
                rcases pair with ⟨xpub, _pk⟩
                simp only
                cases classifyIdentityPath path <;> (
                  simp only
                  split
                  · rfl
                  · cases maybeSignIdentityObject (.vanadium ct) hw identityIndex identityMsgTypeXpub xpub <;> rfl)
    | getAddress display account porOpt coordinates identityIndex =>
      simp only
      cases validateAccountAuth profile hw s.swapLock.isSome account porOpt with
      | error e => rfl
      | ok _ =>
        cases account with
        | walletPolicy wp =>
          cases coordinates with
          | silentPayment _ => rfl
          | walletPolicy isChange addrIdx =>
            simp only
            split
            · rfl
            · split
              · rfl
              · cases hw.deriveWalletPolicyOutput wp isChange addrIdx with
                | none => rfl
                | some pair =>
                  rcases pair with ⟨addr, scriptBytes⟩
                  simp only
                  cases maybeSignIdentityObject profile hw identityIndex identityMsgTypeOutput scriptBytes with
                  | error _ => rfl
                  | ok _ =>
                    simp only
                    split <;> rfl
        | silentPayment name spAcc accId =>
          cases coordinates with
          | walletPolicy _ _ => rfl
          | silentPayment spCoords =>
            simp only
            split
            · rfl
            · cases deriveAccountSpAddress hw.spCrypto hw.bech32m (if decide (profile.coinType = 0) then .sp else .tsp) spAcc spCoords with
              | error _ => rfl
              | ok _ =>
                simp only
                split <;> rfl
    | registerAccount _ _ _ _ => simp [AppCommand.isReadOnly] at hRO
    | signMessage _ _ _ => simp [AppCommand.isReadOnly] at hRO
    | signPsbt _ => simp [AppCommand.isReadOnly] at hRO
    | exportSpScanKey _ _ => simp [AppCommand.isReadOnly] at hRO
    | registerIdentityKey _ _ => simp [AppCommand.isReadOnly] at hRO
    | unexpectedContinue => simp [AppCommand.isReadOnly] at hRO

/-- **Theorem 1 — Read-Only Purity**:
    `GetVersion`, `GetMasterFingerprint`, `GetExtendedPubkey`, and `GetAddress` leave
    `AppPersistentState` (`registeredAccounts`, `musigSessions`, `swapLock`, `residentKeys`)
    identically equal (`s' = s`) on success AND on error. -/
theorem readOnly_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s s' : AppPersistentState)
    (hRO : cmd.isReadOnly = true) :
    ((∃ resp, stepAppCommand profile hw ui cmd s = .ok (resp, s')) ∨
     (∃ err, stepAppCommand profile hw ui cmd s = .error (err, s'))) →
    s' = s := by
  intro hOut
  have hPost := readOnly_step_postState_eq profile hw ui cmd s hRO
  unfold stepPostState at hPost
  rcases hOut with ⟨resp, hOk⟩ | ⟨err, hErr⟩
  · rw [hOk] at hPost
    exact hPost
  · rw [hErr] at hPost
    exact hPost

/-- Explicit corollaries of `readOnly_purity` for each of the four read-only commands. -/
theorem getVersion_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (s s' : AppPersistentState) (resp : AppResponse)
    (h : stepAppCommand profile hw ui .getVersion s = .ok (resp, s')) : s' = s :=
  readOnly_purity profile hw ui .getVersion s s' rfl (Or.inl ⟨resp, h⟩)

theorem getMasterFingerprint_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (tree : KeyTree) (s s' : AppPersistentState) (resp : AppResponse)
    (h : stepAppCommand profile hw ui (.getMasterFingerprint tree) s = .ok (resp, s')) : s' = s :=
  readOnly_purity profile hw ui (.getMasterFingerprint tree) s s' rfl (Or.inl ⟨resp, h⟩)

theorem getExtendedPubkey_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (tree : KeyTree) (display : Bool) (path : List UInt32) (idIdx : Option UInt32)
    (s s' : AppPersistentState) (resp : AppResponse)
    (h : stepAppCommand profile hw ui (.getExtendedPubkey tree display path idIdx) s = .ok (resp, s')) : s' = s :=
  readOnly_purity profile hw ui (.getExtendedPubkey tree display path idIdx) s s' rfl (Or.inl ⟨resp, h⟩)

theorem getAddress_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (display : Bool) (acc : AccountSpec Affine) (por : Option Spec.Musig2.Bytes32)
    (coords : AddressCoordinates) (idIdx : Option UInt32)
    (s s' : AppPersistentState) (resp : AppResponse)
    (h : stepAppCommand profile hw ui (.getAddress display acc por coords idIdx) s = .ok (resp, s')) : s' = s :=
  readOnly_purity profile hw ui (.getAddress display acc por coords idIdx) s s' rfl (Or.inl ⟨resp, h⟩)

/-- **Monotonicity of Consumed MuSig2 Sessions Across Every Command**:
    No command execution (whether `.ok` or `.error`) ever resurrects a consumed MuSig2 session ID. -/
theorem stepAppCommand_preserves_consumed {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s : AppPersistentState) (target : PsbtSessionId)
    (hCons : s.musigSessions.isConsumed target = true) :
    (stepPostState profile hw ui cmd s).musigSessions.isConsumed target = true := by
  by_cases hRO : cmd.isReadOnly = true
  · rw [readOnly_step_postState_eq profile hw ui cmd s hRO]
    exact hCons
  · unfold stepPostState stepAppCommand
    by_cases hSwap : (s.swapLock.isSome && !isAllowedInSwap cmd) = true
    · simp [hSwap, hCons]
    · simp only [hSwap, Bool.false_eq_true, ↓reduceIte]
      cases cmd with
      | getVersion | getMasterFingerprint _ | getExtendedPubkey _ _ _ _ | getAddress _ _ _ _ _ =>
        simp [AppCommand.isReadOnly] at hRO
      | unexpectedContinue => exact hCons
      | registerIdentityKey name pubkey =>
        cases profile with
        | bolos _ => exact hCons
        | vanadium _ =>
          simp only
          split
          · exact hCons
          · cases computeIdentityRegistrationId hw.musigCrypto.sha256 name pubkey with
            | none => exact hCons
            | some _ => simp only; split <;> exact hCons
      | exportSpScanKey hrp accIdx =>
        cases profile with
        | bolos _ => exact hCons
        | vanadium _ =>
          simp only
          cases exportSpScanKey hw.spCrypto hw.bech32m hrp hw.deriveSpAccount accIdx (ui.approve (.confirmExportSpScanKey accIdx)) with
          | error e => cases e <;> exact hCons
          | ok _ => exact hCons
      | signMessage path msg hdrBase =>
        cases profile with
        | vanadium _ => exact hCons
        | bolos _ =>
          simp only
          split
          · exact hCons
          · by_cases hApp : (!ui.approve (.confirmSignMessage path
              (if isPrintableAsciiMessage msg then .cleartextAscii msg else .sha256Digest (hw.musigCrypto.sha256 msg)))) = true
            · simp [hApp, hCons]
            · simp only [hApp, Bool.false_eq_true, ↓reduceIte]
              cases hw.signRecoverableEcdsa path (bitcoinSignedMessageDigest hw.musigCrypto.sha256 msg) with
              | none => exact hCons
              | some triple =>
                rcases triple with ⟨recId, r, sScalar⟩
                simp only
                cases formatCompactRecoverableSig hdrBase recId r sScalar <;> exact hCons
      | registerAccount account regIds keySigs showCt =>
        cases account with
        | walletPolicy wp =>
          simp only
          split
          · exact hCons
          · split
            · exact hCons
            · split
              · exact hCons
              · split <;> exact hCons
        | silentPayment name spAcc accId =>
          cases profile with
          | bolos _ => exact hCons
          | vanadium ct =>
            simp only
            split
            · exact hCons
            · cases hw.deriveSpAccount spAcc.accountIndex with
              | error _ => exact hCons
              | ok derivedAcc =>
                simp only
                split
                · exact hCons
                · cases deriveAccountSpAddress hw.spCrypto hw.bech32m (if decide ((TargetProfile.vanadium ct).coinType = 0) then .sp else .tsp) spAcc (.code none) with
                  | error _ => exact hCons
                  | ok _ =>
                    simp only
                    split <;> exact hCons
      | signPsbt psbt =>
        simp only
        cases validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
        | error _ => exact hCons
        | ok _ =>
          simp only
          split
          · exact hCons
          · split
            · exact hCons
            · cases hPlan : psbt.musigPlan with
              | round1Only sid r1Tasks =>
                simp only
                split
                · exact hCons
                · have hR1 := executeRound1Pass_preserves_consumed hw.musigCrypto profile.musigAggPkMode
                    s.musigSessions sid target hw.freshMusigRandRoot r1Tasks hCons
                  cases hEx : executeRound1Pass hw.musigCrypto profile.musigAggPkMode
                      s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                  | error p =>
                    rcases p with ⟨mErr, ms'⟩
                    rw [hEx] at hR1
                    exact hR1
                  | ok p =>
                    rcases p with ⟨pubnonces, msCommitted⟩
                    rw [hEx] at hR1
                    exact hR1
              | none =>
                simp only
                split
                · exact hCons
                · cases signStandardInputs hw psbt.standardSignTasks <;> exact hCons
              | round1AndStandard sid r1Tasks =>
                simp only
                split
                · exact hCons
                · cases signStandardInputs hw psbt.standardSignTasks with
                  | error _ => exact hCons
                  | ok _ =>
                    have hR1 := executeRound1Pass_preserves_consumed hw.musigCrypto profile.musigAggPkMode
                      s.musigSessions sid target hw.freshMusigRandRoot r1Tasks hCons
                    cases hEx : executeRound1Pass hw.musigCrypto profile.musigAggPkMode
                        s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                    | error p =>
                      rcases p with ⟨mErr, ms'⟩
                      rw [hEx] at hR1
                      exact hR1
                    | ok p =>
                      rcases p with ⟨pubnonces, msCommitted⟩
                      rw [hEx] at hR1
                      exact hR1
              | round2 sid r2Inputs =>
                simp only
                split
                · exact hCons
                · split
                  · exact hCons
                  · have hR2 := executeRound2Pass_preserves_consumed hw.musigCrypto profile.musigAggPkMode
                      s.musigSessions sid target r2Inputs hCons
                    cases hEx : executeRound2Pass hw.musigCrypto profile.musigAggPkMode
                        s.musigSessions sid r2Inputs with
                    | error p =>
                      rcases p with ⟨mErr, msConsumed⟩
                      rw [hEx] at hR2
                      exact hR2
                    | ok p =>
                      rcases p with ⟨partialSigs, msConsumed⟩
                      rw [hEx] at hR2
                      cases signStandardInputs hw psbt.standardSignTasks <;> exact hR2

/-- **Theorem 2 — Atomic Error Rollback**:
    Any command returning `.error (e, s')` leaves `registeredAccounts`, `swapLock`, and
    `residentKeys` identically unchanged (`s'.registeredAccounts = s.registeredAccounts`,
    `s'.swapLock = s.swapLock`, `s'.residentKeys = s.residentKeys`), AND never resurrects
    a consumed MuSig2 nonce session. -/
theorem atomic_error_rollback {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s s' : AppPersistentState) (e : AppError)
    (hErr : stepAppCommand profile hw ui cmd s = .error (e, s')) :
    s'.registeredAccounts = s.registeredAccounts ∧
    s'.swapLock = s.swapLock ∧
    s'.residentKeys = s.residentKeys ∧
    (∀ sid, s.musigSessions.isConsumed sid = true → s'.musigSessions.isConsumed sid = true) := by
  have hConsMono : ∀ sid, s.musigSessions.isConsumed sid = true → s'.musigSessions.isConsumed sid = true := by
    intro sid hC
    have hPost := stepAppCommand_preserves_consumed profile hw ui cmd s sid hC
    unfold stepPostState at hPost
    rw [hErr, extractPostState_error] at hPost
    exact hPost
  have hFields :
      s'.registeredAccounts = s.registeredAccounts ∧
      s'.swapLock = s.swapLock ∧
      s'.residentKeys = s.residentKeys := by
    by_cases hRO : cmd.isReadOnly = true
    · have hEq := readOnly_purity profile hw ui cmd s s' hRO (Or.inr ⟨e, hErr⟩)
      rw [hEq]
      exact ⟨rfl, rfl, rfl⟩
    · unfold stepAppCommand at hErr
      by_cases hSwap : (s.swapLock.isSome && !isAllowedInSwap cmd) = true
      · simp [hSwap] at hErr
        rcases hErr with ⟨_, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · simp only [hSwap, Bool.false_eq_true, ↓reduceIte] at hErr
        cases cmd with
        | getVersion | getMasterFingerprint _ | getExtendedPubkey _ _ _ _ | getAddress _ _ _ _ _ =>
          simp [AppCommand.isReadOnly] at hRO
        | unexpectedContinue =>
          injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
        | registerIdentityKey name pubkey =>
          cases profile with
          | bolos _ =>
            injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
          | vanadium _ =>
            simp only at hErr
            split at hErr
            · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
            · cases hId : computeIdentityRegistrationId hw.musigCrypto.sha256 name pubkey <;> simp [hId] at hErr
              · rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
              · split at hErr
                · rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
                · contradiction
        | exportSpScanKey hrp accIdx =>
          cases profile with
          | bolos _ =>
            injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
          | vanadium _ =>
            simp only at hErr
            cases hExp : exportSpScanKey hw.spCrypto hw.bech32m hrp hw.deriveSpAccount accIdx (ui.approve (.confirmExportSpScanKey accIdx)) with
            | ok _ => simp [hExp] at hErr
            | error spErr =>
              cases spErr <;> (simp [hExp] at hErr; rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩)
        | signMessage path msg hdrBase =>
          cases profile with
          | vanadium _ =>
            injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
          | bolos _ =>
            simp only at hErr
            split at hErr
            · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
            · by_cases hApp : (!ui.approve (.confirmSignMessage path
                (if isPrintableAsciiMessage msg then .cleartextAscii msg else .sha256Digest (hw.musigCrypto.sha256 msg)))) = true
              · simp [hApp] at hErr; rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
              · simp only [hApp, Bool.false_eq_true, ↓reduceIte] at hErr
                cases hSig : hw.signRecoverableEcdsa path (bitcoinSignedMessageDigest hw.musigCrypto.sha256 msg) with
                | none => simp [hSig] at hErr; rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
                | some triple =>
                  rcases triple with ⟨recId, r, sScalar⟩
                  simp only [hSig] at hErr
                  cases hFmt : formatCompactRecoverableSig hdrBase recId r sScalar with
                  | none => simp [hFmt] at hErr; rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
                  | some _ => simp [hFmt] at hErr
        | registerAccount account regIds keySigs showCt =>
          cases account with
          | walletPolicy wp =>
            simp only at hErr
            split at hErr
            · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
            · split at hErr
              · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
              · split at hErr
                · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                · split at hErr
                  · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                  · simp at hErr
          | silentPayment name spAcc accId =>
            cases profile with
            | bolos _ =>
              injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
            | vanadium ct =>
              simp only at hErr
              split at hErr
              · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
              · cases hDer : hw.deriveSpAccount spAcc.accountIndex with
                | error _ => simp [hDer] at hErr; rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
                | ok derivedAcc =>
                  simp only [hDer] at hErr
                  split at hErr
                  · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                  · cases hAddr : deriveAccountSpAddress hw.spCrypto hw.bech32m (if decide ((TargetProfile.vanadium ct).coinType = 0) then .sp else .tsp) spAcc (.code none) with
                    | error _ =>
                      rw [hAddr] at hErr
                      injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                    | ok _ =>
                      rw [hAddr] at hErr
                      simp only at hErr
                      split at hErr
                      · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                      · simp at hErr
        | signPsbt psbt =>
          cases hVal : validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
          | error _ => simp [hVal] at hErr; rcases hErr with ⟨_, rfl⟩; exact ⟨rfl, rfl, rfl⟩
          | ok _ =>
            simp only [hVal] at hErr
            split at hErr
            · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
            · split at hErr
              · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
              · cases hPlan : psbt.musigPlan <;> simp only [hPlan] at hErr
                · -- none
                  split at hErr
                  · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                  · split at hErr
                    · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                    · simp at hErr
                · -- round1Only
                  split at hErr
                  · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                  · split at hErr
                    · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                    · simp at hErr
                · -- round1AndStandard
                  split at hErr
                  · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                  · split at hErr
                    · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                    · split at hErr
                      · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                      · simp at hErr
                · -- round2
                  split at hErr
                  · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                  · split at hErr
                    · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                    · split at hErr
                      · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                      · split at hErr
                        · injection hErr with hPair; cases hPair; exact ⟨rfl, rfl, rfl⟩
                        · simp at hErr
  exact ⟨hFields.1, hFields.2.1, hFields.2.2, hConsMono⟩

/-- Predicate expressing that a `AppResponse` carries at least one cryptographic signature
    from `SignMessage` or `SignPsbt`. -/
def responseEmitsSignature : AppResponse → Bool
  | .messageSigned _ => true
  | .psbtSigned stdSigs _ musigPartialSigs _ _ _ =>
    !stdSigs.isEmpty || !musigPartialSigs.isEmpty
  | _ => false

/-- **Theorem 3 — User Consent Gate**:
    When `UserApprovalOracle` returns `false` (`ui.approve p = false`),
    - `SignMessage` NEVER succeeds;
    - `SignPsbt` NEVER emits any standard or MuSig2 partial signature unless `s.swapLock = some lock`
      and `validSwapPsbt hw.musigCrypto.sha256 lock psbt = true`. -/
theorem user_consent_gate_signMessage {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (path : List UInt32) (msg : ByteArray) (hdrBase : CompactSigHeaderBase)
    (s s' : AppPersistentState) (resp : AppResponse)
    (hDeny : ∀ p, ui.approve p = false) :
    stepAppCommand profile hw ui (.signMessage path msg hdrBase) s ≠ .ok (resp, s') := by
  intro hOk
  unfold stepAppCommand at hOk
  by_cases hSwap : (s.swapLock.isSome && !isAllowedInSwap (@AppCommand.signMessage Affine path msg hdrBase)) = true
  · simp [hSwap] at hOk
  · simp only [hSwap, Bool.false_eq_true, ↓reduceIte] at hOk
    cases profile with
    | vanadium _ => simp at hOk
    | bolos _ =>
      simp only [hDeny] at hOk
      split at hOk <;> simp at hOk

theorem user_consent_gate_signPsbt {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (psbt : PsbtSignRequest Affine) (s s' : AppPersistentState) (resp : AppResponse)
    (hDeny : ∀ p, ui.approve p = false)
    (hOk : stepAppCommand profile hw ui (.signPsbt psbt) s = .ok (resp, s'))
    (hSig : responseEmitsSignature resp = true) :
    ∃ lock : SwapLock, s.swapLock = some lock ∧ validSwapPsbt hw.musigCrypto.sha256 lock psbt = true := by
  unfold stepAppCommand at hOk
  by_cases hSwapGate : (s.swapLock.isSome && !isAllowedInSwap (.signPsbt psbt)) = true
  · simp [hSwapGate] at hOk
  · simp only [hSwapGate, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hVal : validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
    | error _ => simp [hVal] at hOk
    | ok _ =>
      simp only [hVal] at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · cases hPlan : psbt.musigPlan <;> simp only [hPlan] at hOk
          · -- .none
            cases hLock : s.swapLock with
            | none =>
              simp [hLock, hDeny] at hOk
            | some lock =>
              simp only [hLock] at hOk
              cases hValid : validSwapPsbt hw.musigCrypto.sha256 lock psbt
              · simp [hValid] at hOk
              · exact ⟨lock, rfl, hValid⟩
          · -- .round1Only: emits `stdSigs = []` and `musigPartialSigs = []`, contradicting `hSig`!
            split at hOk
            · simp at hOk
            · split at hOk
              · simp at hOk
              · injection hOk with hPair
                cases hPair
                simp [responseEmitsSignature] at hSig
          · -- .round1AndStandard
            cases hLock : s.swapLock with
            | none =>
              simp [hLock, hDeny] at hOk
            | some lock =>
              simp only [hLock] at hOk
              cases hValid : validSwapPsbt hw.musigCrypto.sha256 lock psbt
              · simp [hValid] at hOk
              · exact ⟨lock, rfl, hValid⟩
          · -- .round2
            split at hOk
            · simp at hOk
            · cases hLock : s.swapLock with
              | none =>
                simp [hLock, hDeny] at hOk
              | some lock =>
                simp only [hLock] at hOk
                cases hValid : validSwapPsbt hw.musigCrypto.sha256 lock psbt
                · simp [hValid] at hOk
                · exact ⟨lock, rfl, hValid⟩

/-- Lemma: if `stepAppCommand` succeeds on `.signPsbt psbt` with `psbt.musigPlan = .round2 sid inputs`,
    then `sid` was NOT consumed in `s` and IS consumed in `s'`. -/
theorem stepAppCommand_musigRound2_ok_consumes {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (psbt : PsbtSignRequest Affine) (sid : PsbtSessionId) (r2Inputs : List MusigRound2TaskInput)
    (s s' : AppPersistentState) (resp : AppResponse)
    (hPlan : psbt.musigPlan = .round2 sid r2Inputs)
    (hOk : stepAppCommand profile hw ui (.signPsbt psbt) s = .ok (resp, s')) :
    s.musigSessions.isConsumed sid = false ∧
    s'.musigSessions.isConsumed sid = true ∧
    (∃ a b c d e f, resp = .psbtSigned a b c d e f) := by
  unfold stepAppCommand at hOk
  by_cases hSwapGate : (s.swapLock.isSome && !isAllowedInSwap (.signPsbt psbt)) = true
  · simp [hSwapGate] at hOk
  · simp only [hSwapGate, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hVal : validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
    | error _ => simp [hVal] at hOk
    | ok _ =>
      simp only [hVal] at hOk
      split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · simp only [hPlan] at hOk
          split at hOk
          · simp at hOk
          · split at hOk
            · simp at hOk
            · cases hEx : executeRound2Pass hw.musigCrypto profile.musigAggPkMode s.musigSessions sid r2Inputs with
              | error p => simp [hEx] at hOk
              | ok p =>
                rcases p with ⟨partialSigs, msConsumed⟩
                rw [hEx] at hOk
                simp only at hOk
                cases hStd : signStandardInputs hw psbt.standardSignTasks with
                | error _ => simp [hStd] at hOk
                | ok stdSigs =>
                  rw [hStd] at hOk
                  injection hOk with hPair
                  cases hPair
                  have ⟨hNotCons, hNowCons⟩ := executeRound2Pass_ok_consumes hw.musigCrypto profile.musigAggPkMode
                    s.musigSessions msConsumed sid r2Inputs partialSigs hEx
                  exact ⟨hNotCons, hNowCons, ⟨_, _, _, _, _, _, rfl⟩⟩

/-- Once `sid` is consumed in `s.musigSessions`, no subsequent multi-step trace `cmds` can ever
    emit Round-2 partial signatures for `sid`. -/
theorem countMusigRound2Steps_zero_of_consumed {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (sid : PsbtSessionId) :
    ∀ (cmds : List (AppCommand Affine)) (s : AppPersistentState),
      s.musigSessions.isConsumed sid = true →
      countMusigRound2Steps sid (runAppTrace profile hw ui cmds s).1 = 0
  | [], _, _ => rfl
  | cmd :: rest, s, hCons => by
    unfold runAppTrace
    have hPres := stepAppCommand_preserves_consumed profile hw ui cmd s sid hCons
    unfold stepPostState at hPres
    cases hStep : stepAppCommand profile hw ui cmd s with
    | error pair =>
      rcases pair with ⟨err, s'⟩
      rw [hStep] at hPres
      have ih := countMusigRound2Steps_zero_of_consumed profile hw ui sid rest s' hPres
      simp [countMusigRound2Steps, outcomeProducedMusigRound2For, ih]
    | ok pair =>
      rcases pair with ⟨resp, s'⟩
      rw [hStep] at hPres
      have ih := countMusigRound2Steps_zero_of_consumed profile hw ui sid rest s' hPres
      have hHeadFalse : outcomeProducedMusigRound2For sid (.ok cmd resp) = false := by
        cases cmd with
        | signPsbt psbt =>
          cases resp with
          | psbtSigned a b c d e f =>
            cases hPlan : psbt.musigPlan with
            | round2 sid' r2Inputs =>
              simp only [outcomeProducedMusigRound2For, hPlan]
              by_cases hEq : sid' = sid
              · subst hEq
                have ⟨hNotC, _, _⟩ := stepAppCommand_musigRound2_ok_consumes profile hw ui
                  psbt sid' r2Inputs s s' (.psbtSigned a b c d e f) hPlan hStep
                rw [hCons] at hNotC
                contradiction
              · exact beq_false_of_ne hEq
            | none => simp [outcomeProducedMusigRound2For, hPlan]
            | round1Only _ _ => simp [outcomeProducedMusigRound2For, hPlan]
            | round1AndStandard _ _ => simp [outcomeProducedMusigRound2For, hPlan]
          | _ => rfl
        | _ => rfl
      simp [countMusigRound2Steps, hHeadFalse, ih]

/-- **Theorem 4 — MuSig2 Nonce Anti-Replay Across Arbitrary Multi-Step Traces**:
    For ANY target profile, hardware oracle, user oracle, initial `AppPersistentState`, and
    arbitrary command sequence `cmds = [cmd_1, ..., cmd_k]`, a MuSig2 session ID `sid` produces
    Round-2 partial signatures in **at most one** command step (`countMusigRound2Steps sid ≤ 1`). -/
theorem musig2_nonce_anti_replay {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (sid : PsbtSessionId) :
    ∀ (cmds : List (AppCommand Affine)) (s : AppPersistentState),
      countMusigRound2Steps sid (runAppTrace profile hw ui cmds s).1 ≤ 1
  | [], _ => by simp [runAppTrace, countMusigRound2Steps]
  | cmd :: rest, s => by
    unfold runAppTrace
    cases hStep : stepAppCommand profile hw ui cmd s with
    | error pair =>
      rcases pair with ⟨err, s'⟩
      simp [countMusigRound2Steps, outcomeProducedMusigRound2For,
        musig2_nonce_anti_replay profile hw ui sid rest s']
    | ok pair =>
      rcases pair with ⟨resp, s'⟩
      by_cases hProd : outcomeProducedMusigRound2For sid (.ok cmd resp) = true
      · -- Head step produced Round-2 partial signatures for `sid` => `sid` is now consumed in `s'`!
        have hNowCons : s'.musigSessions.isConsumed sid = true := by
          cases cmd with
          | signPsbt psbt =>
            cases resp with
            | psbtSigned a b c d e f =>
              cases hPlan : psbt.musigPlan with
              | round2 sid' r2Inputs =>
                simp [outcomeProducedMusigRound2For, hPlan] at hProd
                subst hProd
                exact (stepAppCommand_musigRound2_ok_consumes profile hw ui
                  psbt sid' r2Inputs s s' (.psbtSigned a b c d e f) hPlan hStep).2.1
              | none => simp [outcomeProducedMusigRound2For, hPlan] at hProd
              | round1Only _ _ => simp [outcomeProducedMusigRound2For, hPlan] at hProd
              | round1AndStandard _ _ => simp [outcomeProducedMusigRound2For, hPlan] at hProd
            | _ => simp [outcomeProducedMusigRound2For] at hProd
          | _ => simp [outcomeProducedMusigRound2For] at hProd
        have hZero := countMusigRound2Steps_zero_of_consumed profile hw ui sid rest s' hNowCons
        simp [countMusigRound2Steps, hProd, hZero]
      · simp only [Bool.not_eq_true] at hProd
        simp [countMusigRound2Steps, hProd, musig2_nonce_anti_replay profile hw ui sid rest s']

/-! ## 11. Concrete Non-Vacuity Witnesses -/

def toyHardwareOracle : HardwareOracle Unit :=
  { musigCrypto := nonVacuousToyCrypto
    spCrypto := nonVacuousSpCrypto
    bech32m := nonVacuousBech32m
    masterFingerprint := fun _ _ => some 0xF5ACC2FD
    deriveExtendedPubkey := fun _ _ _ => some (ByteArray.mk #[0xAA], toyCompressedPk)
    computePorHmac := fun id => id
    signRecoverableEcdsa := fun _ _ => some (1, oneByte32, threeByte32)
    signPsbtInput := fun _ => some (ByteArray.mk #[0x44], toyCompressedPk)
    signWithIdentityKey := fun _ _ => some {
      identityPubkey := toyCompressedPk
      signature := SizedBytes.append oneByte32 threeByte32
    }
    verifySchnorr := fun _ _ _ => true
    deriveSpAccount := fun idx => .ok { accountIndex := idx, scanKey := 1, spendKey := () }
    deriveWalletPolicyOutput := fun _ _ _ => some ("bc1qtestaddress", ByteArray.mk #[0x00, 0x14])
    freshMusigRandRoot := rrByte32
    freshDleqAuxRand := spFiveByte32 }

/-- **Non-Vacuity Witness 1**: `SIGN_MESSAGE` succeeds on BOLOS when `UserApprovalOracle` approves,
    returning a 65-byte compact recoverable signature with header `32` (`31 + parity 1`). -/
theorem nonvacuous_bolos_signMessage_ok :
    ∃ (resp : AppResponse) (s' : AppPersistentState),
      stepAppCommand (.bolos 0) toyHardwareOracle ⟨fun _ => true⟩
        (.signMessage [84 ||| hardenedFlag, 0 ||| hardenedFlag, 0 ||| hardenedFlag, 0, 0]
          (ByteArray.mk #[0x48, 0x69]) .compressedP2pkh) {} = .ok (resp, s') ∧
      responseEmitsSignature resp = true := by
  let hdr : Spec.SilentPayments.SizedBytes 1 := ⟨ByteArray.mk #[32], rfl⟩
  let r32 : Spec.SilentPayments.Bytes32 := ⟨oneByte32.bytes, oneByte32.size_eq⟩
  let s32 : Spec.SilentPayments.Bytes32 := ⟨threeByte32.bytes, threeByte32.size_eq⟩
  let expectedSig := Spec.SilentPayments.SizedBytes.append hdr (Spec.SilentPayments.SizedBytes.append r32 s32)
  refine ⟨.messageSigned expectedSig, {}, ?_, rfl⟩
  have hPathOk : ¬(bolosMaxBip32PathSteps < 5) := by decide
  have hSizeOk : ¬(maxSignMessageLength ≤ (ByteArray.mk #[0x48, 0x69]).size) := by decide
  simp [stepAppCommand, toyHardwareOracle, formatCompactRecoverableSig, CompactSigHeaderBase.baseByte,
    hPathOk, hSizeOk, expectedSig, hdr, r32, s32]

/-- **Non-Vacuity Witness 2**: Pre-locked BOLOS Swap `SignPsbt` succeeds WITHOUT user approval
    (`ui.approve = fun _ => false`) when the PSBT matches `SwapLock`, and clears `swapLock` (`swapCompleted = true`). -/
theorem nonvacuous_swap_signPsbt_without_ui_consent :
    ∃ (lock : SwapLock) (psbt : PsbtSignRequest Unit) (resp : AppResponse) (s' : AppPersistentState),
      stepAppCommand (.bolos 0) toyHardwareOracle ⟨fun _ => false⟩
        (.signPsbt psbt) { swapLock := some lock } = .ok (resp, s') ∧
      responseEmitsSignature resp = true ∧
      s'.swapLock = none := by
  let lock : SwapLock := {
    amount := 90000
    fees := 1000
    destinationAddress := "bc1qswapdest"
    mode := .standard
  }
  let defaultWp : WalletPolicySpec := {
    name := ""
    version := 2
    descriptorTemplate := "wpkh(@0/**)"
    nKeys := 1
    nInternalKeys := 1
    isDefaultPolicy := true
    isSignable := true
    walletId := oneByte32
    keysInfoPayloads := []
  }
  let stdTask : StandardInputSigRequest := {
    inputIndex := 0
    derivationPath := [84 ||| hardenedFlag, 0 ||| hardenedFlag, 0 ||| hardenedFlag, 0, 0]
    sighash := sighashByte32
    isSchnorr := false
    leafHash := none
  }
  let psbt : PsbtSignRequest Unit := {
    account := .walletPolicy defaultWp
    por := none
    isBip322MessageSigning := false
    inputsTotalAmount := 100000
    outputsTotalAmount := 99000
    changeOutputsTotalAmount := 9000
    nExternalInputs := 0
    missingNonWitnessUtxo := false
    nonDefaultSighash := false
    externalOutputs := [{ amount := 90000, script := ByteArray.mk #[0x00, 0x14], formattedAddress := some "bc1qswapdest" }]
    standardSignTasks := [stdTask]
    musigPlan := .none
    silentPaymentTx := none
  }
  let sigOut : StandardInputSignature := {
    inputIndex := 0
    signature := ByteArray.mk #[0x44]
    pubkey := toyCompressedPk
    leafHash := none
  }
  refine ⟨lock, psbt, .psbtSigned [sigOut] [] [] [] [] true, { swapLock := none }, ?_, rfl, rfl⟩
  have hEmpty : "".isEmpty = true := by decide
  have hSwapOk : validSwapPsbt toyHardwareOracle.musigCrypto.sha256 lock psbt = true := by decide
  have hAuthOk : validateAccountAuth (.bolos 0) toyHardwareOracle true (.walletPolicy defaultWp) none = .ok () := by
    simp [validateAccountAuth, defaultWp, hEmpty]
  have hStdOk : signStandardInputs toyHardwareOracle [stdTask] = .ok [sigOut] := rfl
  have hAmt1 : ¬(psbt.inputsTotalAmount < psbt.outputsTotalAmount) := by decide
  have hAmt2 : ¬(psbt.outputsTotalAmount < psbt.changeOutputsTotalAmount) := by decide
  unfold stepAppCommand
  simp [isAllowedInSwap, psbt, hAuthOk, hAmt1, hAmt2, hSwapOk, hStdOk]

/-- **Non-Vacuity Witness 3**: Multi-step trace executing MuSig2 Round 1, a read-only `GetVersion`,
    MuSig2 Round 2, and a Round-2 replay attempt produces `.ok` for steps 1..3 and rejects step 4
    with `.musigError .sessionAlreadyConsumed`, with `countMusigRound2Steps sid = 1`. -/
theorem nonvacuous_multistep_musig_trace :
    ∃ (sid : PsbtSessionId) (hw : HardwareOracle Unit)
      (cmd1 cmd3 : AppCommand Unit) (r1Resp r2Resp : AppResponse),
      let cmds := [cmd1, .getVersion, cmd3, cmd3]
      let (outcomes, sFinal) := runAppTrace (.bolos 0) hw ⟨fun _ => true⟩ cmds {}
      outcomes.length = 4 ∧
      countMusigRound2Steps sid outcomes = 1 ∧
      sFinal.musigSessions.isConsumed sid = true ∧
      outcomes = [
        .ok cmd1 r1Resp,
        .ok .getVersion (.version targetAppVersion),
        .ok cmd3 r2Resp,
        .error cmd3 (.musigError .sessionAlreadyConsumed)
      ] := by
  rcases nonvacuous_round1_then_round2_and_replay_rejected with
    ⟨sid, rr, t1, t2, r1Out, s1, r2Out, s2, hR1, _hLen1, hR2, _hLen2, _hReplay⟩
  let hwTrace : HardwareOracle Unit := { toyHardwareOracle with freshMusigRandRoot := rr }
  let defaultWp : WalletPolicySpec := {
    name := ""
    version := 2
    descriptorTemplate := "tr(musig(@0,@1)/**)"
    nKeys := 2
    nInternalKeys := 1
    isDefaultPolicy := true
    isSignable := true
    walletId := oneByte32
    keysInfoPayloads := []
  }
  let psbtR1 : PsbtSignRequest Unit := {
    account := .walletPolicy defaultWp
    por := none
    isBip322MessageSigning := false
    inputsTotalAmount := 50000
    outputsTotalAmount := 49000
    changeOutputsTotalAmount := 0
    nExternalInputs := 0
    missingNonWitnessUtxo := false
    nonDefaultSighash := false
    externalOutputs := []
    standardSignTasks := []
    musigPlan := .round1Only sid [t1]
    silentPaymentTx := none
  }
  let psbtR2 : PsbtSignRequest Unit := {
    psbtR1 with musigPlan := .round2 sid [t2]
  }
  let cmd1 : AppCommand Unit := .signPsbt psbtR1
  let cmd3 : AppCommand Unit := .signPsbt psbtR2
  have hEmpty : "".isEmpty = true := by decide
  have hAuth : ∀ b, validateAccountAuth (.bolos 0) hwTrace b (.walletPolicy defaultWp) none = .ok () := by
    intro b
    simp [validateAccountAuth, defaultWp, hEmpty]
  have hAmt1 : ¬((50000 : UInt64) < (49000 : UInt64)) := by decide
  have hAmt2 : ¬((49000 : UInt64) < (0 : UInt64)) := by decide
  have hS1Active : (s1.lookupActive sid).isNone = false := by
    by_cases hNone : (s1.lookupActive sid).isNone = true
    · have hEqNone : s1.lookupActive sid = none := Option.isNone_iff_eq_none.mp hNone
      have hConsumeFail : ∃ err, s1.consumeRound2 sid = .error err := by
        unfold MusigSessionStore.lookupActive at hEqNone
        unfold MusigSessionStore.consumeRound2
        split at hEqNone
        · rename_i hC
          simp [hC]
        · rename_i hNotC
          simp only [hNotC, Bool.false_eq_true, ↓reduceIte]
          cases hFind : s1.activeEntries.find? (fun p => p.1 == sid) with
          | none => exact ⟨.missingSession, rfl⟩
          | some pair => simp [hFind] at hEqNone
      rcases hConsumeFail with ⟨err, hCE⟩
      unfold executeRound2Pass at hR2
      rw [hCE] at hR2
      contradiction
    · simp only [Bool.not_eq_true] at hNone
      exact hNone
  have hS2Cons : s2.isConsumed sid = true :=
    (executeRound2Pass_ok_consumes nonVacuousToyCrypto .untweakedBolos s1 s2 sid [t2] r2Out hR2).2
  have hS2None : (s2.lookupActive sid).isNone = true := by
    unfold MusigSessionStore.lookupActive
    simp [hS2Cons]
  have hAuthF : validateAccountAuth (.bolos 0) hwTrace false (.walletPolicy defaultWp) none = .ok () := hAuth false
  have hStep1 : stepAppCommand (.bolos 0) hwTrace ⟨fun _ => true⟩ cmd1 {} =
      .ok (.psbtSigned [] r1Out [] [] [] false, { musigSessions := s1 }) := by
    unfold stepAppCommand
    simp only [cmd1, psbtR1, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hAuthF]
    simp [hAmt1, hAmt2, TargetProfile.musigAggPkMode, hwTrace, toyHardwareOracle, hR1]
  have hStep2 : stepAppCommand (.bolos 0) hwTrace ⟨fun _ => true⟩ .getVersion { musigSessions := s1 } =
      .ok (.version targetAppVersion, { musigSessions := s1 }) := rfl
  have hStep3 : stepAppCommand (.bolos 0) hwTrace ⟨fun _ => true⟩ cmd3 { musigSessions := s1 } =
      .ok (.psbtSigned [] [] r2Out [] [] false, { musigSessions := s2 }) := by
    unfold stepAppCommand
    simp only [cmd3, psbtR2, psbtR1, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hAuthF]
    simp [hAmt1, hAmt2, hS1Active, TargetProfile.musigAggPkMode,
      hwTrace, toyHardwareOracle, hR2, signStandardInputs]
    rfl
  have hStep4 : stepAppCommand (.bolos 0) hwTrace ⟨fun _ => true⟩ cmd3 { musigSessions := s2 } =
      .error (.musigError .sessionAlreadyConsumed, { musigSessions := s2 }) := by
    unfold stepAppCommand
    simp only [cmd3, psbtR2, psbtR1, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [hAuthF]
    simp [hAmt1, hAmt2, hS2None, hS2Cons]
  refine ⟨sid, hwTrace, cmd1, cmd3, .psbtSigned [] r1Out [] [] [] false, .psbtSigned [] [] r2Out [] [] false, ?_⟩
  simp [runAppTrace, hStep1, hStep2, hStep3, hStep4, countMusigRound2Steps,
    outcomeProducedMusigRound2For, cmd1, cmd3, psbtR1, psbtR2, hS2Cons]

end Spec.AppStateMachine

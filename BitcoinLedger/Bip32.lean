import InternalSpec
import BitcoinLedger.Basic

namespace BitcoinLedger.Bip32

/-!
# `BitcoinLedger.Bip32` — Executable BIP-32 Derivation, Wire Codecs & Export Policy

Executable implementation refining `InternalSpec.Bip32`:
1. Bitwise hardened/unhardened index operations (`HARDENED_BIT = 0x80000000`, `isHardened`, `harden`, `unharden`)
   and BOLOS / BIP-388 / Vanadium / BIP-32 depth gates (`MAX_BIP32_PATH_STEPS = 10`,
   `MAX_BIP388_XPUB_DERIVATION_STEPS = 8`, `MAX_BIP32_PATH_LEN = 16`, `MAX_BIP32_BYTE_DEPTH = 255`)
2. Executable serialized BIP-32 path wire parser & serializer (`[len : UInt8] || u32be[0] || ...`)
3. 78-byte `ExtendedPubKey` (`xpub`/`tpub`) binary serializer & parser plus Base58Check framing
4. Executable `ExtendedPubKey` public child (`CKDpub`) and seed derivation over `InternalSpec.CryptoDerivationOracle`
5. Ledger `GET_EXTENDED_PUBKEY` security policy classifier (standard BIP-44/49/84/86/87/48/45/352 & Electrum
   hardened prefixes allowed silently vs unusual-path UI warning vs rejected unhardened/over-depth/OS-locked paths)
-/

open BitcoinLedger.Basic

-- Constructive `BEq` instances avoiding `Std.PreorderPackage.toBEq` (`Classical.choice`).
local instance (priority := 2000) : BEq UInt8 := ⟨fun a b => decide (a = b)⟩
local instance (priority := 2000) : BEq UInt32 := ⟨fun a b => decide (a = b)⟩

/-! ## 1. BIP-32 Indices, Bitwise Hardening, and Depth Gates -/

/-- A BIP-32 derivation path from master `m` (`#[]` = root `m`). -/
abbrev Bip32Path := InternalSpec.Bip32Path

/-- Bitmask marking a hardened BIP-32 child index (`2^31 = 0x80000000`). -/
def HARDENED_BIT : UInt32 := 0x80000000

/-- Bitmask selecting the low 31 bits of a BIP-32 child index (`0x7FFFFFFF`). -/
def UNHARDENED_MASK : UInt32 := 0x7FFFFFFF

/-- BOLOS maximum BIP-388 wallet-policy xpub derivation steps (`8`). -/
def MAX_BIP388_XPUB_DERIVATION_STEPS : Nat := 8

/-- BOLOS maximum BIP-32 derivation steps (`app-bitcoin/src/constants.h`: `10`). -/
def MAX_BIP32_PATH_STEPS : Nat := 10

/-- Vanadium maximum BIP-32 derivation steps on `KeyTree::Standard` (`16`). -/
def MAX_BIP32_PATH_LEN : Nat := 16

/-- BIP-32 serialized `depth : UInt8` protocol ceiling (`255`). -/
def MAX_BIP32_BYTE_DEPTH : Nat := 255

/-- Recommended upper bound on hardened BIP-44 account index (`100`). -/
def MAX_BIP44_ACCOUNT_RECOMMENDED : UInt32 := 100

/-- Executable bitwise check for whether a BIP-32 child index is hardened (`(idx &&& 0x80000000) != 0`). -/
@[inline] def isHardened (idx : UInt32) : Bool :=
  !decide ((idx &&& HARDENED_BIT) = 0)

/-- Construct a hardened BIP-32 child index using bitwise OR (`n ||| 0x80000000`). -/
@[inline] def harden (n : UInt32) : UInt32 :=
  n ||| HARDENED_BIT

/-- Strip the hardened bit using bitwise AND (`idx &&& 0x7FFFFFFF`). -/
@[inline] def unharden (idx : UInt32) : UInt32 :=
  idx &&& UNHARDENED_MASK

/-- Check BOLOS BIP-388 wallet-policy xpub path depth (`path.size ≤ 8`). -/
@[inline] def checkBip388Depth (path : Bip32Path) : Bool :=
  decide (path.size ≤ MAX_BIP388_XPUB_DERIVATION_STEPS)

/-- Check BOLOS standard BIP-32 path depth (`path.size ≤ 10`). -/
@[inline] def checkBolosDepth (path : Bip32Path) : Bool :=
  decide (path.size ≤ MAX_BIP32_PATH_STEPS)

/-- Check Vanadium `KeyTree.standard` BIP-32 path depth (`path.size ≤ 16`). -/
@[inline] def checkVanadiumDepth (path : Bip32Path) : Bool :=
  decide (path.size ≤ MAX_BIP32_PATH_LEN)

/-- Check BIP-32 1-byte protocol depth ceiling (`path.size ≤ 255`). -/
@[inline] def checkByteDepth (path : Bip32Path) : Bool :=
  decide (path.size ≤ MAX_BIP32_BYTE_DEPTH)

/-! ## 2. Wire BIP-32 Path Serializer & Parser (`[len : UInt8] || u32be*`) -/

def encodePathStepsAux : List UInt32 → ByteArray → ByteArray
  | [], acc => acc
  | step :: rest, acc => encodePathStepsAux rest (acc ++ encodeU32BE step)

/-- Serialize a `Bip32Path` in Ledger APDU wire format (`[depth : UInt8] || step_0_be32 || ...`),
    rejecting paths with `path.size > 255`. -/
def serializeBip32Path? (path : Bip32Path) : Option ByteArray :=
  if decide (path.size > MAX_BIP32_BYTE_DEPTH) then
    none
  else
    let header := ByteArray.mk #[UInt8.ofNat path.size]
    some (encodePathStepsAux path.toList header)

def parsePathStepsAux : Nat → List UInt8 → Array UInt32 → Option Bip32Path
  | 0, [], acc => some acc
  | 0, _ :: _, _ => none
  | count + 1, b0 :: b1 :: b2 :: b3 :: rest, acc =>
      let step :=
        (b0.toUInt32 <<< 24) |||
        (b1.toUInt32 <<< 16) |||
        (b2.toUInt32 <<< 8)  |||
        b3.toUInt32
      parsePathStepsAux count rest (acc.push step)
  | _ + 1, _, _ => none

/-- Parse an exact Ledger wire-encoded BIP-32 path (`[len : UInt8] || 4*len big-endian bytes`),
    rejecting truncated or trailing-byte buffers. -/
def parseBip32Path? (bs : ByteArray) : Option Bip32Path :=
  match bs.data.toList with
  | [] => none
  | lenByte :: rest =>
      let count := lenByte.toNat
      if decide (rest.length ≠ 4 * count) then
        none
      else
        parsePathStepsAux count rest #[]

/-- Parse a wire-encoded BIP-32 path enforcing a maximum step bound `maxSteps`
    (e.g. `MAX_BIP32_PATH_STEPS = 10` on BOLOS or `MAX_BIP32_PATH_LEN = 16` on Vanadium). -/
def parseBip32PathBounded? (maxSteps : Nat) (bs : ByteArray) : Option Bip32Path :=
  match parseBip32Path? bs with
  | none => none
  | some path =>
      if decide (path.size ≤ maxSteps) then some path else none

/-! ## 3. 78-Byte `ExtendedPubKey` Binary & Base58Check Codecs -/

abbrev KeyTree := InternalSpec.KeyTree
abbrev ExtendedPubKey := InternalSpec.ExtendedPubKey

/-- All-zero 4-byte parent fingerprint required by BIP-32 for depth-0 master keys. -/
def zeroFingerprint4 : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0]

/-- Executable check for a valid 33-byte SEC1 compressed secp256k1 public key (`0x02` or `0x03` prefix). -/
def isValidCompressedPubKey (bs : ByteArray) : Bool :=
  isBytes33 bs &&
    match bs.data.toList with
    | pfx :: _ => decide (pfx = 0x02 ∨ pfx = 0x03)
    | [] => false

/-- Executable check for `InternalSpec.ExtendedPubKey.WellFormed`. -/
def isWellFormedExtendedPubKey (xpub : ExtendedPubKey) : Bool :=
  isBytes4 xpub.parentFingerprint &&
  isBytes32 xpub.chainCode &&
  isValidCompressedPubKey xpub.pubkey &&
  (if decide (xpub.depth = 0) then
     eqBytes xpub.parentFingerprint zeroFingerprint4 && decide (xpub.childNumber = 0)
   else
     true)

/-- Serialize an `ExtendedPubKey` to its 78-byte binary BIP-32 representation:
    `version[4] || depth[1] || parentFingerprint[4] || childNumber[4] || chainCode[32] || pubkey[33]`. -/
def serializeExtendedPubKey (xpub : ExtendedPubKey) : ByteArray :=
  encodeU32BE xpub.version ++
  ByteArray.mk #[xpub.depth] ++
  xpub.parentFingerprint ++
  encodeU32BE xpub.childNumber ++
  xpub.chainCode ++
  xpub.pubkey

def sliceListBytes (l : List UInt8) (offset len : Nat) : ByteArray :=
  ByteArray.mk ((l.drop offset).take len).toArray

/-- Parse and validate a 78-byte serialized BIP-32 `ExtendedPubKey`, enforcing field widths,
    SEC1 compressed pubkey prefix (`0x02`/`0x03`), and BIP-32 depth-0 root constraints. -/
def deserializeExtendedPubKey? (bs : ByteArray) : Option ExtendedPubKey :=
  if decide (bs.size ≠ 78) then
    none
  else
    let bytes := bs.data.toList
    let verBytes := sliceListBytes bytes 0 4
    let depthByte := (sliceListBytes bytes 4 1).data.toList.headD 0
    let parentFp := sliceListBytes bytes 5 4
    let childBytes := sliceListBytes bytes 9 4
    let chainCode := sliceListBytes bytes 13 32
    let pubkey := sliceListBytes bytes 45 33
    match decodeU32BE? verBytes, decodeU32BE? childBytes with
    | some version, some childNumber =>
        if !isValidCompressedPubKey pubkey then
          none
        else if decide (depthByte = 0) && (!eqBytes parentFp zeroFingerprint4 || !decide (childNumber = 0)) then
          none
        else
          some {
            version
            depth := depthByte
            parentFingerprint := parentFp
            childNumber
            chainCode
            pubkey
          }
    | _, _ => none

/-! ## 4. Base58Check Framing for 78-Byte `ExtendedPubKey` (`xpub` / `tpub`) -/

/-- Encode a well-formed `ExtendedPubKey` into its BOLOS Base58Check `xpub`/`tpub` string
    (78 serialized bytes + 4-byte `doubleSha256` checksum = 82 Base58-encoded bytes). -/
def encodeExtendedPubKeyBase58Check?
    (doubleSha256 : ByteArray → ByteArray)
    (xpub : ExtendedPubKey) : Option String :=
  if !isWellFormedExtendedPubKey xpub then
    none
  else
    let body := serializeExtendedPubKey xpub
    let digest := doubleSha256 body
    if decide (digest.size < 4) then
      none
    else
      let checksum4 := ByteArray.mk (digest.data.toList.take 4).toArray
      InternalSpec.encodeBase58? (body ++ checksum4)

/-- Decode and verify a Base58Check `xpub`/`tpub` string into a validated `ExtendedPubKey`,
    checking the 4-byte `doubleSha256` checksum and all 78-byte BIP-32 structural invariants. -/
def decodeExtendedPubKeyBase58Check?
    (doubleSha256 : ByteArray → ByteArray)
    (encoded : String) : Option ExtendedPubKey :=
  match InternalSpec.decodeBase58? encoded with
  | none => none
  | some raw =>
      if decide (raw.size < 4) then
        none
      else
        let bodyLen := raw.size - 4
        let body := ByteArray.mk (raw.data.toList.take bodyLen).toArray
        let givenChecksum := ByteArray.mk (raw.data.toList.drop bodyLen).toArray
        let digest := doubleSha256 body
        if decide (digest.size < 4) then
          none
        else
          let expectedChecksum := ByteArray.mk (digest.data.toList.take 4).toArray
          if eqBytes givenChecksum expectedChecksum then
            deserializeExtendedPubKey? body
          else
            none

/-! ## 5. Executable HD Key Derivation (`CKDpub` & Seed Derivation) -/

abbrev CryptoDerivationOracle := InternalSpec.CryptoDerivationOracle

/-- Public child derivation on an `ExtendedPubKey` (`CKDpub`), rejecting hardened child indices
    and saturated depth (`depth == 255`). -/
def deriveChildExtendedPubKey?
    (oracle : CryptoDerivationOracle)
    (parent : ExtendedPubKey)
    (childIdx : UInt32) : Option ExtendedPubKey :=
  if isHardened childIdx || decide (parent.depth = 255) then
    none
  else
    match oracle.deriveChildPub parent.pubkey parent.chainCode childIdx with
    | none => none
    | some (childPub, childChainCode) =>
        let parentFp := (oracle.hash160 parent.pubkey).extract 0 4
        some {
          version := parent.version
          depth := parent.depth + 1
          parentFingerprint := parentFp
          childNumber := childIdx
          chainCode := childChainCode
          pubkey := childPub
        }

/-- Query the 4-byte master fingerprint for `tree`, validating `isBytes4`. -/
def deriveMasterFingerprint? (oracle : CryptoDerivationOracle) (tree : KeyTree) : Option ByteArray :=
  match oracle.masterFingerprint tree with
  | some fp => if isBytes4 fp then some fp else none
  | none => none

/-- Derive the full `ExtendedPubKey` at `path` for `net` and `tree` using `oracle`. -/
def deriveExtendedPubKeyWithOracle
    (oracle : CryptoDerivationOracle)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path) : Option ExtendedPubKey :=
  if decide (path.size > MAX_BIP32_BYTE_DEPTH) then
    none
  else
    match oracle.deriveNode tree path with
    | none => none
    | some (pubkey, chainCode) =>
        if decide (path.size = 0) then
          some {
            version := (networkParams net).xpubVersion
            depth := 0
            parentFingerprint := zeroFingerprint4
            childNumber := 0
            chainCode
            pubkey
          }
        else if decide (path.size = 1) then
          let childNumber := path[0]?.getD 0
          match deriveMasterFingerprint? oracle tree with
          | none => none
          | some masterFp =>
              some {
                version := (networkParams net).xpubVersion
                depth := 1
                parentFingerprint := masterFp
                childNumber
                chainCode
                pubkey
              }
        else
          let parentPath := path.pop
          let childNumber := path[path.size - 1]?.getD 0
          match oracle.deriveNode tree parentPath with
          | none => none
          | some (parentPub, _) =>
              let h := oracle.hash160 parentPub
              if decide (h.size < 4) then
                none
              else
                some {
                  version := (networkParams net).xpubVersion
                  depth := UInt8.ofNat path.size
                  parentFingerprint := h.extract 0 4
                  childNumber
                  chainCode
                  pubkey
                }

abbrev deriveExtendedPubKey? := deriveExtendedPubKeyWithOracle

/-! ## 6. Ledger `GET_EXTENDED_PUBKEY` Security Policy Classifier -/

def BIP45_PURPOSE : UInt32 := 45
def ELECTRUM_ENCRYPTION_PURPOSE : UInt32 := 4541509
def ELECTRUM_ENCRYPTION_SUBPATH : UInt32 := 1112098098
def LEDGER_IDENTITY_PURPOSE : UInt32 := 1229210958

/-- Executable BOLOS OS kernel `PATH_APP_LOAD_PARAMS` path lock (`app-bitcoin/Makefile:95-103`). -/
def isBolosOsPermittedPath (net : Network) (path : Bip32Path) : Bool :=
  match path.toList with
  | [] => false
  | [s0] =>
      decide (s0 = harden ELECTRUM_ENCRYPTION_PURPOSE) ||
      decide (s0 = harden BIP45_PURPOSE)
  | s0 :: s1 :: _ =>
      decide (s0 = harden ELECTRUM_ENCRYPTION_PURPOSE) ||
      decide (s0 = harden BIP45_PURPOSE) ||
      decide (s1 = harden (networkParams net).bip44CoinType)

/-- Check whether every element of `steps` is hardened. -/
def allHardened (steps : List UInt32) : Bool :=
  steps.all isHardened

/-- Check whether every element of `steps` is unhardened. -/
def allUnhardened (steps : List UInt32) : Bool :=
  steps.all (fun idx => !isHardened idx)

/-- Standard 3-hardened-step BIP purposes (`44'`, `49'`, `84'`, `86'`, `87'`, `45'`). -/
def isStandard3StepPurpose (purpose : UInt32) : Bool :=
  decide (purpose = 44) || decide (purpose = 49) || decide (purpose = 84) ||
  decide (purpose = 86) || decide (purpose = 87) || decide (purpose = 45)

/-- Executable BOLOS `is_path_safe_for_pubkey_export` predicate (`get_extended_pubkey.c`). -/
def isBolosSafePubkeyExportPath (net : Network) (path : Bip32Path) : Bool :=
  match path.toList with
  | [s0, s1] =>
      decide (s0 = harden ELECTRUM_ENCRYPTION_PURPOSE) &&
      decide (s1 = harden ELECTRUM_ENCRYPTION_SUBPATH)
  | s0 :: s1 :: s2 :: rest =>
      if !(isHardened s0 && isHardened s1 && isHardened s2) then
        false
      else
        let purpose := unharden s0
        let coinType := unharden s1
        let account := unharden s2
        if !decide (coinType = (networkParams net).bip44CoinType) ||
           decide (MAX_BIP44_ACCOUNT_RECOMMENDED < account) then
          false
        else if isStandard3StepPurpose purpose then
          allUnhardened rest
        else if decide (purpose = 48) then
          match rest with
          | [] => false
          | s3 :: tail =>
              isHardened s3 &&
              (decide (unharden s3 = 1) || decide (unharden s3 = 2)) &&
              allUnhardened tail
        else
          false
  | _ => false

/-- Executable BIP-352 Silent Payment key derivation prefix predicate (`m/352'/coin'/account'/{0',1'}/...`). -/
def isStandardBip352Path (net : Network) (path : Bip32Path) : Bool :=
  match path.toList with
  | s0 :: s1 :: s2 :: s3 :: tail =>
      isHardened s0 && isHardened s1 && isHardened s2 && isHardened s3 &&
      decide (unharden s0 = 352) &&
      decide (unharden s1 = (networkParams net).bip44CoinType) &&
      decide (unharden s2 ≤ MAX_BIP44_ACCOUNT_RECOMMENDED) &&
      (decide (unharden s3 = 0) || decide (unharden s3 = 1)) &&
      allUnhardened tail
  | _ => false

abbrev ExpubPolicyConfig := InternalSpec.ExpubPolicyConfig
abbrev ExpubPolicyDecision := InternalSpec.ExpubPolicyDecision

def bolosExpubPolicyConfig : ExpubPolicyConfig := InternalSpec.bolosExpubPolicyConfig
def bolosRecoveryExpubPolicyConfig : ExpubPolicyConfig := InternalSpec.bolosRecoveryExpubPolicyConfig
def vanadiumExpubPolicyConfig : ExpubPolicyConfig := InternalSpec.vanadiumExpubPolicyConfig
def vanadiumHardenedExpubPolicyConfig : ExpubPolicyConfig := InternalSpec.vanadiumHardenedExpubPolicyConfig

/-- Executable `GET_EXTENDED_PUBKEY` path classifier on `KeyTree`. -/
def classifyExpubPathWithTree
    (cfg : ExpubPolicyConfig)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path) : ExpubPolicyDecision :=
  let maxDepth? : Option Nat :=
    match tree with
    | .standard => some cfg.maxSteps
    | .resident => cfg.maxResidentSteps?
  match maxDepth? with
  | none => .reject .notSupported
  | some maxD =>
      if decide (path.size > maxD) || decide (path.size > MAX_BIP32_BYTE_DEPTH) then
        .reject .bip32PathTooLong
      else if cfg.enforceBolosOsPathLock && !isBolosOsPermittedPath net path then
        .reject .notSupported
      else if !cfg.requireSafeWhitelistForSilent then
        .allowSilent
      else if isBolosSafePubkeyExportPath net path ||
              (cfg.allowBip352Silent && isStandardBip352Path net path) then
        .allowSilent
      else if cfg.strictRejectUnusual then
        .reject .unsupportedBip32Path
      else
        .warnUnusual

/-- Executable `GET_EXTENDED_PUBKEY` path classifier on the `.standard` key tree. -/
def classifyExpubPath (cfg : ExpubPolicyConfig) (net : Network) (path : Bip32Path) : ExpubPolicyDecision :=
  classifyExpubPathWithTree cfg net .standard path

/-- Executable authorization gate for `GET_EXTENDED_PUBKEY`. -/
def authorizeExtendedPubKeyExport
    (cfg : ExpubPolicyConfig)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path)
    (display : Bool)
    (userApproved : Bool) : Except SpecError Unit :=
  match classifyExpubPathWithTree cfg net tree path with
  | .reject err => .error err
  | .warnUnusual =>
      if !display then
        .error .unsupportedBip32Path
      else if !userApproved then
        .error .userRejected
      else
        .ok ()
  | .allowSilent =>
      if display && !userApproved then
        .error .userRejected
      else
        .ok ()

/-- Complete executable `GET_EXTENDED_PUBKEY` handler over `CryptoDerivationOracle`. -/
def evalGetExtendedPubkey
    (oracle : CryptoDerivationOracle)
    (cfg : ExpubPolicyConfig)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path)
    (display : Bool)
    (userApproved : Bool) : Except SpecError ExtendedPubKey := do
  authorizeExtendedPubKeyExport cfg net tree path display userApproved
  match deriveExtendedPubKeyWithOracle oracle net tree path with
  | some xpub => .ok xpub
  | none => .error .cryptoOrSignatureFailed

end BitcoinLedger.Bip32

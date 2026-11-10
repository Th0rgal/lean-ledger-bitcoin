import Spec.Basic

namespace Spec

/-!
# `Spec.Bip32` — BIP-32 Hierarchical Deterministic Derivation & Export Policy

Implementation-independent plain Lean 4 specifications for:
1. `Bip32Path` (`Array UInt32`), hardened index predicate (`idx ≥ 0x80000000`), and depth limits
   (`MAX_BIP32_PATH_STEPS = 10` in BOLOS vs `MAX_BIP32_PATH_LEN = 16` in Vanadium vs `255` BIP-32 byte ceiling)
2. Master fingerprint (`Bytes4`), key trees (`standard` vs `resident`), and `ExtendedPubKey` (78-byte serialized xpub/tpub)
3. Abstract `CryptoDerivationOracle` (secp256k1 HD node derivation, `CKDpub`, `HASH160`, double-SHA256)
4. Ledger `GET_EXTENDED_PUBKEY` security policy (standard BIP-44/49/84/86/87/48/45/352 & Electrum hardened prefixes
   allowed silently vs unusual-path UI warning/approval vs rejected over-depth/invalid paths)
-/

/-! ## 1. BIP-32 Indices, Hardening, and Depth Limits -/

/-- A BIP-32 derivation path from master `m` (`#[]` = root `m`). -/
abbrev Bip32Path := Array UInt32

/-- Bitmask marking a hardened BIP-32 child index (`2^31 = 0x80000000`). -/
def HARDENED_BIT : UInt32 := 0x80000000

/-- BOLOS maximum BIP-388 wallet-policy xpub derivation steps (`app-bitcoin/src/constants.h`). -/
def MAX_BIP388_XPUB_DERIVATION_STEPS : Nat := 8

/-- BOLOS maximum BIP-32 derivation steps (`app-bitcoin/src/constants.h`: `MAX_BIP32_PATH_STEPS = 10`). -/
def MAX_BIP32_PATH_STEPS : Nat := 10

/-- Vanadium maximum BIP-32 derivation steps on `KeyTree::Standard` (`MAX_BIP32_PATH_LEN = 16`). -/
def MAX_BIP32_PATH_LEN : Nat := 16

/-- BIP-32 serialized `depth : UInt8` protocol ceiling (`255`). -/
def MAX_BIP32_BYTE_DEPTH : Nat := 255

/-- Recommended upper bound on hardened BIP-44 account index (`app-bitcoin/src/constants.h`: `100`). -/
def MAX_BIP44_ACCOUNT_RECOMMENDED : UInt32 := 100

/-- Proposition that a BIP-32 child index is hardened (`idx ≥ 0x80000000`). -/
def Hardened (idx : UInt32) : Prop :=
  0x80000000 ≤ idx.toNat

/-- Proposition that a BIP-32 child index is unhardened (`idx < 0x80000000`). -/
def Unhardened (idx : UInt32) : Prop :=
  idx.toNat < 0x80000000

/-- Boolean check for whether a BIP-32 child index is hardened (`idx ≥ 0x80000000`). -/
def isHardened (idx : UInt32) : Bool :=
  decide (0x80000000 ≤ idx.toNat)

/-- Construct a hardened BIP-32 child index from its low 31-bit index (`0x80000000 + (n mod 2^31)`). -/
def harden (n : UInt32) : UInt32 :=
  UInt32.ofNat (0x80000000 + (n.toNat % 0x80000000))

/-- Strip the hardened bit (`idx mod 2^31`), returning the unhardened child number in `0..2^31 - 1`. -/
def unharden (idx : UInt32) : UInt32 :=
  UInt32.ofNat (idx.toNat % 0x80000000)

theorem isHardened_iff (idx : UInt32) : isHardened idx = true ↔ Hardened idx := by
  simp [isHardened, Hardened]

theorem isHardened_false_iff (idx : UInt32) : isHardened idx = false ↔ Unhardened idx := by
  unfold isHardened Unhardened
  cases h : decide (0x80000000 ≤ idx.toNat) <;> simp_all

theorem isHardened_harden (n : UInt32) : isHardened (harden n) = true := by
  rw [isHardened_iff]
  unfold Hardened harden
  rw [UInt32.toNat_ofNat']
  omega

theorem unharden_lt (idx : UInt32) : (unharden idx).toNat < 0x80000000 := by
  unfold unharden
  rw [UInt32.toNat_ofNat']
  omega

theorem unharden_harden {n : UInt32} (h : n.toNat < 0x80000000) :
    unharden (harden n) = n := by
  apply UInt32.toNat_inj.mp
  unfold unharden harden
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']
  omega

theorem harden_unharden {idx : UInt32} (h : isHardened idx = true) :
    harden (unharden idx) = idx := by
  rw [isHardened_iff] at h
  unfold Hardened at h
  have hlt := idx.toNat_lt
  apply UInt32.toNat_inj.mp
  unfold harden unharden
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']
  omega

/-! ## 2. Master Fingerprint, Key Trees, and 78-Byte `ExtendedPubKey` -/

/-- Key tree selector (Vanadium supports both `standard` BIP-39 seed tree and `resident` device-bound tree;
    BOLOS derives on `standard`). -/
inductive KeyTree where
  | standard
  | resident
  deriving Repr, DecidableEq, Inhabited

/-- 4-byte BIP-32 master key fingerprint predicate (`RIPEMD160(SHA256(masterCompressedPubkey))[0..4)`). -/
abbrev MasterFingerprint (bs : ByteArray) : Prop := Bytes4 bs

/-- All-zero 4-byte parent fingerprint required by BIP-32 for depth-0 master keys. -/
def zeroFingerprint4 : ByteArray :=
  ByteArray.mk #[0, 0, 0, 0]

theorem zeroFingerprint4_isBytes4 : Bytes4 zeroFingerprint4 := rfl

/-- Boolean check for a valid 33-byte SEC1 compressed secp256k1 public key (`0x02` or `0x03` prefix). -/
def isValidCompressedPubKey (bs : ByteArray) : Bool :=
  decide (bs.size = 33) &&
    match bs.data.toList with
    | pfx :: _ => decide (pfx = 0x02 ∨ pfx = 0x03)
    | [] => false

/-- Propositional specification of a valid 33-byte SEC1 compressed public key. -/
def ValidCompressedPubKey (bs : ByteArray) : Prop :=
  isValidCompressedPubKey bs = true

/-- BIP-32 extended public key (`xpub` / `tpub`), serialized on the wire as 78 big-endian bytes:
    `version[4] || depth[1] || parentFingerprint[4] || childNumber[4] || chainCode[32] || pubkey[33]`. -/
structure ExtendedPubKey where
  version : UInt32
  depth : UInt8
  parentFingerprint : ByteArray
  childNumber : UInt32
  chainCode : ByteArray
  pubkey : ByteArray
  deriving DecidableEq, Inhabited

/-- Structural and BIP-32 root invariants for an `ExtendedPubKey`. -/
def ExtendedPubKey.WellFormed (xpub : ExtendedPubKey) : Prop :=
  Bytes4 xpub.parentFingerprint ∧
  Bytes32 xpub.chainCode ∧
  ValidCompressedPubKey xpub.pubkey ∧
  (xpub.depth = 0 → xpub.parentFingerprint = zeroFingerprint4 ∧ xpub.childNumber = 0)

/-- Serialize an `ExtendedPubKey` to its 78-byte binary BIP-32 representation.
    (Note: Vanadium returns these raw 78 bytes in `Response::ExtendedPubkey`, whereas BOLOS returns
    Base58Check over these 78 bytes.) -/
def ExtendedPubKey.serialize (xpub : ExtendedPubKey) : ByteArray :=
  encodeU32BEBytes xpub.version ++
  ByteArray.mk #[xpub.depth] ++
  xpub.parentFingerprint ++
  encodeU32BEBytes xpub.childNumber ++
  xpub.chainCode ++
  xpub.pubkey

private def sliceBytes (l : List UInt8) (offset len : Nat) : ByteArray :=
  ByteArray.mk ((l.drop offset).take len).toArray

private theorem sliceBytes_head {a b : ByteArray} {n : Nat} (ha : a.size = n) :
    sliceBytes (a ++ b).data.toList 0 n = a := by
  have hl : a.data.toList.length = n := ha
  unfold sliceBytes
  cases a; cases b
  simp [ByteArray.data_append, hl]

private theorem sliceBytes_tail {a b : ByteArray} {k s m : Nat} (ha : a.size = k) :
    sliceBytes (a ++ b).data.toList (k + s) m = sliceBytes b.data.toList s m := by
  unfold sliceBytes
  cases a with
  | mk arrA =>
      cases b with
      | mk arrB =>
          have hl : arrA.toList.length = k := ha
          have hdrop : List.drop (k + s) arrA.toList = [] :=
            List.drop_eq_nil_of_le (by omega)
          simp [ByteArray.data_append, List.drop_append, hl, hdrop]

private theorem sliceBytes_exact {a : ByteArray} {n : Nat} (ha : a.size = n) :
    sliceBytes a.data.toList 0 n = a := by
  unfold sliceBytes
  cases a with
  | mk arr =>
      have hl : arr.toList.length = n := ha
      simp only [List.drop_zero]
      rw [← hl, List.take_length]

/-- Total decoder for a 78-byte serialized BIP-32 `ExtendedPubKey`, enforcing field widths,
    compressed public key prefix (`0x02`/`0x03`), and BIP-32 depth-0 root constraints. -/
def deserializeExtendedPubKey? (bs : ByteArray) : Option ExtendedPubKey :=
  if bs.size ≠ 78 then
    none
  else
    let bytes := bs.data.toList
    let verBytes := sliceBytes bytes 0 4
    let depthByte := (sliceBytes bytes 4 1).data.toList.headD 0
    let parentFp := sliceBytes bytes 5 4
    let childBytes := sliceBytes bytes 9 4
    let chainCode := sliceBytes bytes 13 32
    let pubkey := sliceBytes bytes 45 33
    match decodeU32BE? verBytes, decodeU32BE? childBytes with
    | some version, some childNumber =>
        if !isValidCompressedPubKey pubkey then
          none
        else if depthByte = 0 ∧ (parentFp ≠ zeroFingerprint4 ∨ childNumber ≠ 0) then
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

theorem ExtendedPubKey.serialize_size {xpub : ExtendedPubKey} (hwf : xpub.WellFormed) :
    xpub.serialize.size = 78 := by
  rcases hwf with ⟨hfp, hcc, hpk, _⟩
  unfold Bytes4 BytesN at hfp
  unfold Bytes32 BytesN at hcc
  unfold ValidCompressedPubKey isValidCompressedPubKey at hpk
  have hpkSize : xpub.pubkey.size = 33 := by
    cases h : decide (xpub.pubkey.size = 33)
    · simp [h] at hpk
    · exact of_decide_eq_true h
  have hverSize : (encodeU32BEBytes xpub.version).size = 4 := rfl
  have hdSize : (ByteArray.mk #[xpub.depth]).size = 1 := rfl
  have hchSize : (encodeU32BEBytes xpub.childNumber).size = 4 := rfl
  unfold ExtendedPubKey.serialize
  simp only [ByteArray.size_append, hverSize, hdSize, hfp, hchSize, hcc, hpkSize]

/-- Roundtrip theorem for 78-byte `ExtendedPubKey` serialization & deserialization. -/
theorem deserializeExtendedPubKey?_serialize {xpub : ExtendedPubKey} (hwf : xpub.WellFormed) :
    deserializeExtendedPubKey? xpub.serialize = some xpub := by
  have hsize : xpub.serialize.size = 78 := xpub.serialize_size hwf
  rcases hwf with ⟨hfp, hcc, hpk, hroot⟩
  unfold Bytes4 BytesN at hfp
  unfold Bytes32 BytesN at hcc
  have hpkBool : isValidCompressedPubKey xpub.pubkey = true := hpk
  have hpkSize : xpub.pubkey.size = 33 := by
    unfold isValidCompressedPubKey at hpkBool
    cases h : decide (xpub.pubkey.size = 33)
    · simp [h] at hpkBool
    · exact of_decide_eq_true h
  let bVer := encodeU32BEBytes xpub.version
  let bDep := ByteArray.mk #[xpub.depth]
  let bFp := xpub.parentFingerprint
  let bCh := encodeU32BEBytes xpub.childNumber
  let bCc := xpub.chainCode
  let bPk := xpub.pubkey
  have sVer : bVer.size = 4 := rfl
  have sDep : bDep.size = 1 := rfl
  have sCh : bCh.size = 4 := rfl
  have hser : xpub.serialize = bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk)))) := by
    unfold ExtendedPubKey.serialize
    simp only [bVer, bDep, bFp, bCh, bCc, bPk, ByteArray.append_assoc]
  unfold deserializeExtendedPubKey?
  simp only [hsize, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hser]
  have eVer : sliceBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 0 4 = bVer :=
    sliceBytes_head sVer
  have eDep : sliceBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 4 1 = bDep := by
    rw [show (4 : Nat) = 4 + 0 from rfl, sliceBytes_tail sVer]
    exact sliceBytes_head sDep
  have eFp : sliceBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 5 4 = bFp := by
    rw [show (5 : Nat) = 4 + (1 + 0) from rfl, sliceBytes_tail sVer, sliceBytes_tail sDep]
    exact sliceBytes_head hfp
  have eCh : sliceBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 9 4 = bCh := by
    rw [show (9 : Nat) = 4 + (1 + (4 + 0)) from rfl,
        sliceBytes_tail sVer, sliceBytes_tail sDep, sliceBytes_tail hfp]
    exact sliceBytes_head sCh
  have eCc : sliceBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 13 32 = bCc := by
    rw [show (13 : Nat) = 4 + (1 + (4 + (4 + 0))) from rfl,
        sliceBytes_tail sVer, sliceBytes_tail sDep, sliceBytes_tail hfp, sliceBytes_tail sCh]
    exact sliceBytes_head hcc
  have ePk : sliceBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 45 33 = bPk := by
    rw [show (45 : Nat) = 4 + (1 + (4 + (4 + (32 + 0)))) from rfl,
        sliceBytes_tail sVer, sliceBytes_tail sDep, sliceBytes_tail hfp,
        sliceBytes_tail sCh, sliceBytes_tail hcc]
    exact sliceBytes_exact hpkSize
  rw [eVer, eDep, eFp, eCh, eCc, ePk]
  have dVer : decodeU32BE? bVer = some xpub.version := decodeU32BE?_roundtrip xpub.version
  have dCh : decodeU32BE? bCh = some xpub.childNumber := decodeU32BE?_roundtrip xpub.childNumber
  have hHead : bDep.data.toList.headD 0 = xpub.depth := rfl
  rw [dVer, dCh, hHead]
  simp only [bFp, bCc, bPk, hpkBool, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hd0 : xpub.depth = 0
  · obtain ⟨hfp0, hch0⟩ := hroot hd0
    cases xpub
    simp_all
  · simp [hd0]

/-! ## 3. Abstract Cryptographic Derivation Oracle -/

/-- Pure, axiom-free oracle abstraction for hardware/VM BIP-32 cryptographic primitives
    (secp256k1 HD node derivation, public child derivation `CKDpub`, `HASH160`, and double-SHA256). -/
structure CryptoDerivationOracle where
  /-- Derive `(compressedPubkey33, chainCode32)` at `path` from the given `KeyTree` seed. -/
  deriveNode : KeyTree → Bip32Path → Option (ByteArray × ByteArray)
  /-- BIP-32 public child key derivation `CKDpub(parentPubkey33, parentChainCode32, childIdx)`.
      Must fail (`none`) whenever `childIdx` is hardened (`≥ 0x80000000`). -/
  deriveChildPub : ByteArray → ByteArray → UInt32 → Option (ByteArray × ByteArray)
  /-- `HASH160(x) = RIPEMD160(SHA256(x))` (20 bytes). -/
  hash160 : ByteArray → ByteArray
  /-- `SHA256(SHA256(x))` (32 bytes, first 4 bytes form Base58Check checksums). -/
  doubleSha256 : ByteArray → ByteArray

/-- Well-formedness laws for a `CryptoDerivationOracle` (no global axioms needed). -/
structure CryptoDerivationOracle.Lawful (oracle : CryptoDerivationOracle) : Prop where
  deriveNode_wf :
    ∀ tree path pub cc,
      oracle.deriveNode tree path = some (pub, cc) →
      ValidCompressedPubKey pub ∧ Bytes32 cc
  deriveChildPub_rejects_hardened :
    ∀ pub cc idx,
      isHardened idx = true →
      oracle.deriveChildPub pub cc idx = none
  deriveChildPub_wf :
    ∀ pub cc idx cpub ccc,
      oracle.deriveChildPub pub cc idx = some (cpub, ccc) →
      ValidCompressedPubKey cpub ∧ Bytes32 ccc
  hash160_bytes20 :
    ∀ bs, Bytes20 (oracle.hash160 bs)
  doubleSha256_bytes32 :
    ∀ bs, Bytes32 (oracle.doubleSha256 bs)

/-- Public child derivation on an `ExtendedPubKey` (`CKDpub`), rejecting hardened child indices
    (`idx ≥ 0x80000000`) and saturated depth (`depth == 255`). -/
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

theorem deriveChildExtendedPubKey?_rejects_hardened
    (oracle : CryptoDerivationOracle) (parent : ExtendedPubKey) (childIdx : UInt32)
    (hHard : isHardened childIdx = true) :
    deriveChildExtendedPubKey? oracle parent childIdx = none := by
  simp [deriveChildExtendedPubKey?, hHard]

theorem deriveChildExtendedPubKey?_rejects_max_depth
    (oracle : CryptoDerivationOracle) (parent : ExtendedPubKey) (childIdx : UInt32)
    (hDepth : parent.depth = 255) :
    deriveChildExtendedPubKey? oracle parent childIdx = none := by
  simp [deriveChildExtendedPubKey?, hDepth]

/-- Derive the 4-byte master fingerprint `HASH160(masterPubkey)[0..4)` for `tree`. -/
def deriveMasterFingerprint? (oracle : CryptoDerivationOracle) (tree : KeyTree) : Option ByteArray :=
  match oracle.deriveNode tree #[] with
  | none => none
  | some (masterPub, _) =>
      let h := oracle.hash160 masterPub
      if h.size < 4 then none else some (h.extract 0 4)

/-- Derive the full `ExtendedPubKey` at `path` for `net` and `tree`.
    Explicitly rejects `path.size > 255` (`MAX_BIP32_BYTE_DEPTH`) so `depth : UInt8` can never
    silently wrap around (unlike Vanadium's `KeyTree::Resident` `path.len() > 256` off-by-one bug). -/
def deriveExtendedPubKey?
    (oracle : CryptoDerivationOracle)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path) : Option ExtendedPubKey :=
  if path.size > MAX_BIP32_BYTE_DEPTH then
    none
  else
    match oracle.deriveNode tree path with
    | none => none
    | some (pubkey, chainCode) =>
        if path.size = 0 then
          some {
            version := net.params.xpubVersion
            depth := 0
            parentFingerprint := zeroFingerprint4
            childNumber := 0
            chainCode
            pubkey
          }
        else
          let parentPath := path.extract 0 (path.size - 1)
          let childNumber := path.toList.getLastD 0
          match oracle.deriveNode tree parentPath with
          | none => none
          | some (parentPub, _) =>
              let h := oracle.hash160 parentPub
              if h.size < 4 then
                none
              else
                some {
                  version := net.params.xpubVersion
                  depth := UInt8.ofNat path.size
                  parentFingerprint := h.extract 0 4
                  childNumber
                  chainCode
                  pubkey
                }

/-! ## 4. Ledger `GET_EXTENDED_PUBKEY` Security Policy -/

/-- Electrum legacy encryption pubkey purpose (`4541509'`), permitted silently at exact depth 2
    `m/4541509'/1112098098'` in BOLOS `get_extended_pubkey.c`. -/
def ELECTRUM_ENCRYPTION_PURPOSE : UInt32 := 4541509

/-- Electrum legacy encryption second hardened step (`1112098098'`). -/
def ELECTRUM_ENCRYPTION_SUBPATH : UInt32 := 1112098098

/-- Vanadium identity key purpose (`0x4944454E = 1229210958`, ASCII `"IDEN"`). -/
def LEDGER_IDENTITY_PURPOSE : UInt32 := 1229210958

/-- Check whether every element of `steps` is hardened (`≥ 0x80000000`). -/
def allHardened (steps : List UInt32) : Bool :=
  steps.all isHardened

/-- Check whether every element of `steps` is unhardened (`< 0x80000000`). -/
def allUnhardened (steps : List UInt32) : Bool :=
  steps.all (fun idx => !isHardened idx)

/-- Standard 3-hardened-step BIP purposes (`44'` legacy, `49'` nested SegWit, `84'` native SegWit,
    `86'` Taproot, `87'` descriptor multisig, `45'` legacy multisig). -/
def isStandard3StepPurpose (purpose : UInt32) : Bool :=
  decide (purpose = 44 ∨ purpose = 49 ∨ purpose = 84 ∨ purpose = 86 ∨ purpose = 87 ∨ purpose = 45)

/-- Exact BOLOS `is_path_safe_for_pubkey_export` predicate (`app-bitcoin/src/handler/get_extended_pubkey.c`):
    1. Exact Electrum exception `m/4541509'/1112098098'`
    2. `m/purpose'/coin_type'/account'/...` for `purpose ∈ {44, 49, 84, 86, 87, 45}`, matching `coin_type'`,
       `account ≤ 100`, and only unhardened steps after index 2
    3. `m/48'/coin_type'/account'/script_type'/...` with matching `coin_type'`, `account ≤ 100`,
       `script_type ∈ {1, 2}`, and only unhardened steps after index 3. -/
def isBolosSafePubkeyExportPath (net : Network) (path : Bip32Path) : Bool :=
  match path.toList with
  | [s0, s1] =>
      decide (s0 = harden ELECTRUM_ENCRYPTION_PURPOSE ∧ s1 = harden ELECTRUM_ENCRYPTION_SUBPATH)
  | s0 :: s1 :: s2 :: rest =>
      if !(isHardened s0 && isHardened s1 && isHardened s2) then
        false
      else
        let purpose := unharden s0
        let coinType := unharden s1
        let account := unharden s2
        if coinType ≠ net.params.bip44CoinType ∨ account > MAX_BIP44_ACCOUNT_RECOMMENDED then
          false
        else if isStandard3StepPurpose purpose then
          allUnhardened rest
        else if purpose = 48 then
          match rest with
          | [] => false
          | s3 :: tail =>
              isHardened s3 &&
              decide (unharden s3 = 1 ∨ unharden s3 = 2) &&
              allUnhardened tail
        else
          false
  | _ => false

/-- BIP-352 Silent Payment key derivation prefix `m/352'/coin_type'/account'/branch'` (+ optional unhardened `0`),
    where `branch = 0` is the spend key and `branch = 1` is the scan key (`vanadium/apps/bitcoin/app/src/sp_keys.rs`).
    Note: BOLOS does NOT whitelist `352'` for silent xpub export (and BIP-352 scan private key export always
    requires user confirmation). -/
def isStandardBip352Path (net : Network) (path : Bip32Path) : Bool :=
  match path.toList with
  | s0 :: s1 :: s2 :: s3 :: tail =>
      isHardened s0 && isHardened s1 && isHardened s2 && isHardened s3 &&
      decide (unharden s0 = 352) &&
      decide (unharden s1 = net.params.bip44CoinType) &&
      decide (unharden s2 ≤ MAX_BIP44_ACCOUNT_RECOMMENDED) &&
      decide (unharden s3 = 0 ∨ unharden s3 = 1) &&
      allUnhardened tail
  | _ => false

/-- Tunable platform/policy parameters for `GET_EXTENDED_PUBKEY` path validation. -/
structure ExpubPolicyConfig where
  /-- Maximum allowed path length (`10` on BOLOS, `16` on Vanadium `KeyTree::Standard`). -/
  maxSteps : Nat
  /-- Whether `m/352'/coin_type'/account'/{0',1'}` xpub export is permitted silently without warning. -/
  allowBip352Silent : Bool := false
  /-- If `true`, reject unhardened/too-short/unusual paths even when `display = true`.
      On BOLOS (`Bitcoin` / `Bitcoin Test` / `Bitcoin Recovery`), `false` means `display = true` shows
      an explicit unusual-path warning and requires interactive user confirmation. -/
  strictRejectUnusual : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Canonical BOLOS `GET_EXTENDED_PUBKEY` policy configuration (`maxSteps = 10`, BIP-352 requires display). -/
def bolosExpubPolicyConfig : ExpubPolicyConfig :=
  { maxSteps := MAX_BIP32_PATH_STEPS
    allowBip352Silent := false
    strictRejectUnusual := false }

/-- Hardened Vanadium `GET_EXTENDED_PUBKEY` policy configuration (`maxSteps = 16` + BOLOS path-safety rules). -/
def vanadiumHardenedExpubPolicyConfig : ExpubPolicyConfig :=
  { maxSteps := MAX_BIP32_PATH_LEN
    allowBip352Silent := false
    strictRejectUnusual := false }

/-- Decision outcome of classifying a BIP-32 path for `GET_EXTENDED_PUBKEY`. -/
inductive ExpubPolicyDecision where
  /-- Standard hardened prefix: allowed silently (`display = false`) or with normal UI (`display = true`). -/
  | allowSilent
  /-- Unusual path (e.g. unhardened root/prefix, too-short prefix, non-standard purpose, `account > 100`,
      wrong `coin_type`, or hardened suffix): rejected when `display = false`; requires interactive user
      warning & approval when `display = true`. -/
  | warnUnusual
  /-- Hard policy rejection regardless of `display` / user approval. -/
  | reject (err : SpecError)
  deriving Repr, DecidableEq, Inhabited

/-- Classify a `Bip32Path` under `ExpubPolicyConfig` and `Network`. -/
def classifyExpubPath (cfg : ExpubPolicyConfig) (net : Network) (path : Bip32Path) : ExpubPolicyDecision :=
  if path.size > cfg.maxSteps || path.size > MAX_BIP32_BYTE_DEPTH then
    .reject .bip32PathTooLong
  else if isBolosSafePubkeyExportPath net path ||
          (cfg.allowBip352Silent && isStandardBip352Path net path) then
    .allowSilent
  else if cfg.strictRejectUnusual then
    .reject .unsupportedBip32Path
  else
    .warnUnusual

/-- Complete specification of `GET_EXTENDED_PUBKEY` combining path security policy, interactive UI
    confirmation (`display`, `userApproved`), and cryptographic HD derivation. -/
def evalGetExtendedPubkey
    (oracle : CryptoDerivationOracle)
    (cfg : ExpubPolicyConfig)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path)
    (display : Bool)
    (userApproved : Bool) : Except SpecError ExtendedPubKey :=
  match classifyExpubPath cfg net path with
  | .reject err => .error err
  | .warnUnusual =>
      if !display then
        .error .unsupportedBip32Path
      else if !userApproved then
        .error .userRejected
      else
        match deriveExtendedPubKey? oracle net tree path with
        | some xpub => .ok xpub
        | none => .error .cryptoOrSignatureFailed
  | .allowSilent =>
      if display && !userApproved then
        .error .userRejected
      else
        match deriveExtendedPubKey? oracle net tree path with
        | some xpub => .ok xpub
        | none => .error .cryptoOrSignatureFailed

/-! ## 5. Security & Sanity Theorems (`0 sorryAx`) -/

/-- Security Theorem 1: Silent export (`display = false`) succeeds ONLY on `.allowSilent` paths
    within `cfg.maxSteps` and `≤ 255`. -/
theorem silent_export_requires_allowSilent
    {oracle : CryptoDerivationOracle} {cfg : ExpubPolicyConfig} {net : Network}
    {tree : KeyTree} {path : Bip32Path} {userApproved : Bool} {xpub : ExtendedPubKey}
    (hok : evalGetExtendedPubkey oracle cfg net tree path false userApproved = .ok xpub) :
    classifyExpubPath cfg net path = .allowSilent ∧
    path.size ≤ cfg.maxSteps ∧
    path.size ≤ MAX_BIP32_BYTE_DEPTH := by
  unfold evalGetExtendedPubkey at hok
  cases hdec : classifyExpubPath cfg net path with
  | reject err => simp [hdec] at hok
  | warnUnusual => simp [hdec] at hok
  | allowSilent =>
      refine ⟨rfl, ?_, ?_⟩
      · unfold classifyExpubPath at hdec
        by_cases hgt : path.size > cfg.maxSteps
        · simp [hgt] at hdec
        · omega
      · unfold classifyExpubPath at hdec
        by_cases hgt : path.size > MAX_BIP32_BYTE_DEPTH
        · simp [hgt] at hdec
        · omega

/-- Security Theorem 2: Over-depth paths (`path.size > cfg.maxSteps`) are ALWAYS rejected with
    `SpecError.bip32PathTooLong`, even when `display = true` and `userApproved = true`. -/
theorem over_depth_always_rejected
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : Network)
    (tree : KeyTree) (path : Bip32Path) (display userApproved : Bool)
    (hover : cfg.maxSteps < path.size) :
    evalGetExtendedPubkey oracle cfg net tree path display userApproved = .error .bip32PathTooLong := by
  have hgt : path.size > cfg.maxSteps := hover
  unfold evalGetExtendedPubkey classifyExpubPath
  simp [hgt]

/-- Security Theorem 3: Empty (`m`) and length-1 (`m/x`) paths are too short to be safe for silent export. -/
theorem short_len0_or_len1_not_safe_silent
    (cfg : ExpubPolicyConfig) (net : Network) (path : Bip32Path)
    (hshort : path.size ≤ 1) :
    classifyExpubPath cfg net path ≠ .allowSilent := by
  unfold classifyExpubPath
  split
  · simp
  · split
    · rename_i hsafe
      exfalso
      have hlen : path.toList.length ≤ 1 := hshort
      cases hlist : path.toList with
      | nil =>
          simp [isBolosSafePubkeyExportPath, isStandardBip352Path, hlist] at hsafe
      | cons s0 tail =>
          cases tail with
          | nil =>
              simp [isBolosSafePubkeyExportPath, isStandardBip352Path, hlist] at hsafe
          | cons s1 rest =>
              rw [hlist] at hlen
              simp at hlen
    · split <;> simp

/-- Security Theorem 4: Any path starting with an unhardened index (`isHardened s0 = false`) is never
    safe for silent export and is rejected when `display = false`. -/
theorem unhardened_first_step_rejected_silently
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : Network)
    (tree : KeyTree) (path : Bip32Path) (userApproved : Bool)
    (s0 : UInt32) (rest : List UInt32)
    (hlist : path.toList = s0 :: rest)
    (hunhard : isHardened s0 = false) :
    ∃ err : SpecError,
      evalGetExtendedPubkey oracle cfg net tree path false userApproved = .error err := by
  have hnotBolos : isBolosSafePubkeyExportPath net path = false := by
    unfold isBolosSafePubkeyExportPath
    rw [hlist]
    cases rest with
    | nil => rfl
    | cons s1 r1 =>
        cases r1 with
        | nil =>
            simp only [decide_eq_false_iff_not, not_and]
            intro hs0 _
            rw [hs0, isHardened_harden] at hunhard
            cases hunhard
        | cons s2 r2 =>
            simp [hunhard]
  have hnot352 : isStandardBip352Path net path = false := by
    unfold isStandardBip352Path
    rw [hlist]
    cases rest with
    | nil => rfl
    | cons s1 r1 =>
        cases r1 with
        | nil => rfl
        | cons s2 r2 =>
            cases r2 with
            | nil => rfl
            | cons s3 r3 => simp [hunhard]
  unfold evalGetExtendedPubkey classifyExpubPath
  by_cases hlen : (path.size > cfg.maxSteps || path.size > MAX_BIP32_BYTE_DEPTH) = true
  · simp [hlen]
  · simp only [Bool.not_eq_true] at hlen
    simp only [hlen, hnotBolos, hnot352, Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    cases cfg.strictRejectUnusual <;> simp

/-- Sanity Theorem: Standard BIP-84 Mainnet account `m/84'/0'/0'` is allowed silently on BOLOS,
    whereas exporting it on Testnet (`coin_type = 1'`) is flagged `.warnUnusual`. -/
theorem bolos_bip84_mainnet_vs_testnet_policy :
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 84, harden 0, harden 0] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .testnet #[harden 84, harden 0, harden 0] = .warnUnusual := by
  decide

/-- Sanity Theorem: Standard BIP-48 Native SegWit Multisig `m/48'/0'/0'/2'` is allowed silently,
    whereas invalid script_type `m/48'/0'/0'/3'` is flagged `.warnUnusual`. -/
theorem bolos_bip48_script_type_policy :
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 48, harden 0, harden 0, harden 2] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 48, harden 0, harden 0, harden 3] = .warnUnusual := by
  decide

end Spec

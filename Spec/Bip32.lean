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
    (secp256k1 HD node derivation, OS/V-App master fingerprint syscall, public child derivation
    `CKDpub`, `HASH160`, and double-SHA256). -/
structure CryptoDerivationOracle where
  /-- Derive `(compressedPubkey33, chainCode32)` at `path` from the given `KeyTree` seed.
      Note: Under BOLOS without `HAVE_APPLICATION_FLAG_DERIVE_MASTER`, `deriveNode .standard #[]`
      returns `none` even though `masterFingerprint .standard` succeeds (`crypto_get_master_key_fingerprint`). -/
  deriveNode : KeyTree → Bip32Path → Option (ByteArray × ByteArray)
  /-- Dedicated OS / V-App master key fingerprint query (`crypto_get_master_key_fingerprint` in
      `app-bitcoin/src/crypto.c:327`, `bip32::master_fingerprint` in `vanadium/app/src/bip32.rs:29`). -/
  masterFingerprint : KeyTree → Option ByteArray
  /-- BIP-32 public child key derivation `CKDpub(parentPubkey33, parentChainCode32, childIdx)`.
      Must fail (`none`) whenever `childIdx` is hardened (`≥ 0x80000000`). -/
  deriveChildPub : ByteArray → ByteArray → UInt32 → Option (ByteArray × ByteArray)
  /-- `HASH160(x) = RIPEMD160(SHA256(x))` (20 bytes). -/
  hash160 : ByteArray → ByteArray
  /-- `SHA256(SHA256(x))` (32 bytes, first 4 bytes form Base58Check checksums). -/
  doubleSha256 : ByteArray → ByteArray

/-- Well-formedness and algebraic homomorphism laws for a `CryptoDerivationOracle` (no global axioms needed). -/
structure CryptoDerivationOracle.Lawful (oracle : CryptoDerivationOracle) : Prop where
  deriveNode_wf :
    ∀ tree path pub cc,
      oracle.deriveNode tree path = some (pub, cc) →
      ValidCompressedPubKey pub ∧ Bytes32 cc
  masterFingerprint_bytes4 :
    ∀ tree fp,
      oracle.masterFingerprint tree = some fp →
      Bytes4 fp
  masterFingerprint_agrees_with_root :
    ∀ tree rootPub rootCc,
      oracle.deriveNode tree #[] = some (rootPub, rootCc) →
      oracle.masterFingerprint tree = some ((oracle.hash160 rootPub).extract 0 4)
  deriveChildPub_rejects_hardened :
    ∀ pub cc idx,
      isHardened idx = true →
      oracle.deriveChildPub pub cc idx = none
  deriveChildPub_wf :
    ∀ pub cc idx cpub ccc,
      oracle.deriveChildPub pub cc idx = some (cpub, ccc) →
      ValidCompressedPubKey cpub ∧ Bytes32 ccc
  /-- Unhardened `CKDpriv`/`CKDpub` child-derivation homomorphism (BIP-32):
      for any unhardened child index `idx` and derived parent node `(pub, cc)` at `path`,
      deriving `path.push idx` from the seed agrees with public child derivation `CKDpub(pub, cc, idx)`. -/
  unhardened_child_homomorphism :
    ∀ tree path idx pub cc,
      isHardened idx = false →
      oracle.deriveNode tree path = some (pub, cc) →
      oracle.deriveNode tree (path.push idx) = oracle.deriveChildPub pub cc idx
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

/-- Query the 4-byte master fingerprint for `tree`, validating `Bytes4`. -/
def deriveMasterFingerprint? (oracle : CryptoDerivationOracle) (tree : KeyTree) : Option ByteArray :=
  match oracle.masterFingerprint tree with
  | some fp => if decide (fp.size = 4) then some fp else none
  | none => none

/-- Derive the full `ExtendedPubKey` at `path` for `net` and `tree` using `oracle`.
    - Rejects `path.size > 255` (`MAX_BIP32_BYTE_DEPTH`) so `depth : UInt8` never wraps around
      (avoiding Vanadium's `KeyTree::Resident` `path.len() > 256` off-by-one bug).
    - When `path.size == 1` (e.g. `"m/45'"`), uses `oracle.masterFingerprint tree` for
      `parentFingerprint` (`crypto.c:327-329`, `get_extended_pubkey.rs:165-166`) instead of
      calling `oracle.deriveNode tree #[]`, which fails under BOLOS without `DERIVE_MASTER`. -/
def deriveExtendedPubKeyWithOracle
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
        else if path.size = 1 then
          let childNumber := path[0]?.getD 0
          match deriveMasterFingerprint? oracle tree with
          | none => none
          | some masterFp =>
              some {
                version := net.params.xpubVersion
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

/-- Backwards-compatible alias for `deriveExtendedPubKeyWithOracle`. -/
abbrev deriveExtendedPubKey? := deriveExtendedPubKeyWithOracle

/-- Induced `ExtendedPubKey` homomorphism theorem: for any lawful `oracle`, non-empty `path` with
    `path.size < 255`, and unhardened `childIdx`, deriving `path.push childIdx` from the seed
    yields the exact same `ExtendedPubKey` as applying `CKDpub` (`deriveChildExtendedPubKey?`)
    to the parent `ExtendedPubKey` derived at `path`. -/
theorem deriveExtendedPubKeyWithOracle_push_unhardened
    {oracle : CryptoDerivationOracle}
    (hLaw : oracle.Lawful)
    (net : Network)
    (tree : KeyTree)
    (path : Bip32Path)
    (childIdx : UInt32)
    (parentXpub : ExtendedPubKey)
    (hNonEmpty : 0 < path.size)
    (hDepthLt : path.size < MAX_BIP32_BYTE_DEPTH)
    (hUnhard : isHardened childIdx = false)
    (hParent : deriveExtendedPubKeyWithOracle oracle net tree path = some parentXpub) :
    deriveExtendedPubKeyWithOracle oracle net tree (path.push childIdx) =
      deriveChildExtendedPubKey? oracle parentXpub childIdx := by
  have hPushSize : (path.push childIdx).size = path.size + 1 := Array.size_push ..
  have hPushLe : ¬ ((path.push childIdx).size > MAX_BIP32_BYTE_DEPTH) := by
    rw [hPushSize]; unfold MAX_BIP32_BYTE_DEPTH at *; omega
  have hParentLe : ¬ (path.size > MAX_BIP32_BYTE_DEPTH) := by
    unfold MAX_BIP32_BYTE_DEPTH at *; omega
  have hPushNe0 : (path.push childIdx).size ≠ 0 := by rw [hPushSize]; omega
  have hPushNe1 : (path.push childIdx).size ≠ 1 := by rw [hPushSize]; omega
  unfold deriveExtendedPubKeyWithOracle at hParent
  simp only [hParentLe, ↓reduceIte] at hParent
  cases hNode : oracle.deriveNode tree path with
  | none => simp [hNode] at hParent
  | some pair =>
      rcases pair with ⟨parentPub, parentCc⟩
      simp only [hNode] at hParent
      have hParentFields :
          parentXpub.version = net.params.xpubVersion ∧
          parentXpub.depth = UInt8.ofNat path.size ∧
          parentXpub.chainCode = parentCc ∧
          parentXpub.pubkey = parentPub := by
        have hNe0 : path.size ≠ 0 := by omega
        simp only [hNe0, ↓reduceIte] at hParent
        cases hEq1 : decide (path.size = 1)
        · have hNe1 : path.size ≠ 1 := of_decide_eq_false hEq1
          simp only [hNe1, ↓reduceIte] at hParent
          cases hPNode : oracle.deriveNode tree path.pop with
          | none => rw [hPNode] at hParent; simp at hParent
          | some ppair =>
              rcases ppair with ⟨ppub, pcc⟩
              rw [hPNode] at hParent
              simp only at hParent
              cases hHlt : decide ((oracle.hash160 ppub).size < 4)
              · have hNotLt : ¬ ((oracle.hash160 ppub).size < 4) := of_decide_eq_false hHlt
                simp only [hNotLt, ↓reduceIte, Option.some.injEq] at hParent
                subst hParent
                exact ⟨rfl, rfl, rfl, rfl⟩
              · have hLt : (oracle.hash160 ppub).size < 4 := of_decide_eq_true hHlt
                simp only [hLt, ↓reduceIte] at hParent
                cases hParent
        · have hIs1 : path.size = 1 := of_decide_eq_true hEq1
          simp only [hIs1, ↓reduceIte] at hParent
          cases hFp : deriveMasterFingerprint? oracle tree with
          | none => simp [hFp] at hParent
          | some fp =>
              simp only [hFp, Option.some.injEq] at hParent
              subst hParent
              rw [hIs1]
              exact ⟨rfl, rfl, rfl, rfl⟩
      rcases hParentFields with ⟨hVer, hDep, hCc, hPk⟩
      have hHom := hLaw.unhardened_child_homomorphism tree path childIdx parentPub parentCc hUnhard hNode
      have hExtract : (path.push childIdx).pop = path := Array.pop_push
      have hLast : (path.push childIdx)[(path.push childIdx).size - 1]?.getD 0 = childIdx := by
        rw [hPushSize, Nat.add_sub_cancel]
        have hLt : path.size < (path.push childIdx).size := by rw [hPushSize]; omega
        rw [Array.getElem?_eq_getElem hLt, Array.getElem_push_eq]
        rfl
      have hDepthNe255 : decide (parentXpub.depth = 255) = false := by
        rw [hDep, decide_eq_false_iff_not]
        intro hEq
        have hToNat := congrArg UInt8.toNat hEq
        rw [UInt8.toNat_ofNat'] at hToNat
        unfold MAX_BIP32_BYTE_DEPTH at hDepthLt
        have : path.size % 256 = 255 := hToNat
        omega
      have hHash20 : ¬ ((oracle.hash160 parentPub).size < 4) := by
        have hb20 : (oracle.hash160 parentPub).size = 20 := hLaw.hash160_bytes20 parentPub
        omega
      have hDepthSucc : UInt8.ofNat (path.size + 1) = parentXpub.depth + 1 := by
        rw [hDep]
        apply UInt8.toNat_inj.mp
        change (path.size + 1) % 256 = ((UInt8.ofNat path.size).toNat + 1) % 256
        rw [UInt8.toNat_ofNat']
        unfold MAX_BIP32_BYTE_DEPTH at hDepthLt
        omega
      unfold deriveExtendedPubKeyWithOracle deriveChildExtendedPubKey?
      simp only [hPushLe, hPushNe0, hPushNe1, ↓reduceIte, hHom, hExtract, hLast,
        hUnhard, hDepthNe255, Bool.or_false]
      rw [← hPk, ← hCc]
      cases hChild : oracle.deriveChildPub parentXpub.pubkey parentXpub.chainCode childIdx with
      | none => rfl
      | some cpair =>
          rcases cpair with ⟨childPub, childCc⟩
          rw [hPk, hNode]
          simp only [hHash20, Bool.false_eq_true, ↓reduceIte]
          rw [hPushSize, hDepthSucc, hVer]

/-! ## 4. Ledger `GET_EXTENDED_PUBKEY` Security Policy -/

/-- Unchained Capital / BIP-45 multisig purpose (`45'`), explicitly permitted in BOLOS
    `PATH_APP_LOAD_PARAMS` (`app-bitcoin/Makefile:95-103`). -/
def BIP45_PURPOSE : UInt32 := 45

/-- Electrum legacy encryption pubkey purpose (`4541509'`), permitted in BOLOS
    `PATH_APP_LOAD_PARAMS` and silently at exact depth 2 `m/4541509'/1112098098'`
    in `get_extended_pubkey.c`. -/
def ELECTRUM_ENCRYPTION_PURPOSE : UInt32 := 4541509

/-- Electrum legacy encryption second hardened step (`1112098098'`). -/
def ELECTRUM_ENCRYPTION_SUBPATH : UInt32 := 1112098098

/-- Vanadium identity key purpose (`0x4944454E = 1229210958`, ASCII `"IDEN"`). -/
def LEDGER_IDENTITY_PURPOSE : UInt32 := 1229210958

/-- BOLOS OS kernel `PATH_APP_LOAD_PARAMS` path lock (`app-bitcoin/Makefile:95-103`):
    - Mainnet (`COIN=bitcoin`): `"*/0'" "4541509'" "45'"`
    - Testnet / Regtest / Signet (`COIN=bitcoin_testnet`): `"*/1'" "4541509'" "45'"`
    Without `HAVE_APPLICATION_FLAG_DERIVE_MASTER`, `os_perso_derive_node_with_seed_key`
    rejects empty root path `#[]` (`"m"`) and any path outside these OS prefixes
    (e.g. wrong-coin `"m/44'/2'/333'"`) with `0x4212 -> SW_NOT_SUPPORTED` (`.notSupported`),
    even when `display = true` and the user approves (`test_get_extended_pubkey.py:128-149`). -/
def isBolosOsPermittedPath (net : Network) (path : Bip32Path) : Bool :=
  match path.toList with
  | [] => false
  | [s0] =>
      decide (s0 = harden ELECTRUM_ENCRYPTION_PURPOSE ∨ s0 = harden BIP45_PURPOSE)
  | s0 :: s1 :: _ =>
      decide (s0 = harden ELECTRUM_ENCRYPTION_PURPOSE ∨
              s0 = harden BIP45_PURPOSE ∨
              s1 = harden net.params.bip44CoinType)

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
  /-- Maximum allowed path length on `KeyTree.standard` (`10` on BOLOS, `16` on Vanadium). -/
  maxSteps : Nat
  /-- Maximum allowed path length on `KeyTree.resident` (`none` means resident tree is unsupported;
      `some 255` on Vanadium caps depth at `MAX_BIP32_BYTE_DEPTH` to avoid `UInt8` wraparound). -/
  maxResidentSteps? : Option Nat := none
  /-- Enforce BOLOS OS kernel `PATH_APP_LOAD_PARAMS` lock (`isBolosOsPermittedPath`), rejecting
      disallowed paths (such as `"m"` or wrong `coin_type`) with `.notSupported` even when `display = true`. -/
  enforceBolosOsPathLock : Bool := false
  /-- Require BIP-44/45/48/49/84/86/87/Electrum path whitelisting for silent (`display = false`) export.
      True on BOLOS (`get_extended_pubkey.c`); false on Vanadium (`get_extended_pubkey.rs`). -/
  requireSafeWhitelistForSilent : Bool := true
  /-- Whether `m/352'/coin_type'/account'/{0',1'}` xpub export is permitted silently without warning
      when `requireSafeWhitelistForSilent = true`. -/
  allowBip352Silent : Bool := false
  /-- If `true` (when `requireSafeWhitelistForSilent = true`), reject unusual paths even when `display = true`.
      On BOLOS (`Bitcoin` / `Bitcoin Test`), `false` means `display = true` shows an unusual-path warning
      and requires interactive user confirmation (subject to `enforceBolosOsPathLock`). -/
  strictRejectUnusual : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- Canonical BOLOS `GET_EXTENDED_PUBKEY` policy configuration:
    - `maxSteps = 10`, resident key tree unsupported
    - OS kernel `PATH_APP_LOAD_PARAMS` lock enforced (`enforceBolosOsPathLock = true`)
    - `isBolosSafePubkeyExportPath` required for `display = false`. -/
def bolosExpubPolicyConfig : ExpubPolicyConfig :=
  { maxSteps := MAX_BIP32_PATH_STEPS
    maxResidentSteps? := none
    enforceBolosOsPathLock := true
    requireSafeWhitelistForSilent := true
    allowBip352Silent := false
    strictRejectUnusual := false }

/-- Canonical BOLOS Recovery app (`COIN=bitcoin_recovery`) policy configuration, where all OS paths
    are unlocked in `Makefile` (`enforceBolosOsPathLock = false`). -/
def bolosRecoveryExpubPolicyConfig : ExpubPolicyConfig :=
  { maxSteps := MAX_BIP32_PATH_STEPS
    maxResidentSteps? := none
    enforceBolosOsPathLock := false
    requireSafeWhitelistForSilent := true
    allowBip352Silent := false
    strictRejectUnusual := false }

/-- Vanadium `GET_EXTENDED_PUBKEY` policy configuration (`vanadium/apps/bitcoin/app/src/handlers/get_extended_pubkey.rs`):
    - Allows `display = false` silently without BIP-44/48/84/86 path whitelisting
    - Caps `.standard` tree depth at `16` (`MAX_BIP32_PATH_LEN`) and `.resident` tree depth at `255`
      (`MAX_BIP32_BYTE_DEPTH`), preventing `depth = 256` `UInt8` wraparound. -/
def vanadiumExpubPolicyConfig : ExpubPolicyConfig :=
  { maxSteps := MAX_BIP32_PATH_LEN
    maxResidentSteps? := some MAX_BIP32_BYTE_DEPTH
    enforceBolosOsPathLock := false
    requireSafeWhitelistForSilent := false
    allowBip352Silent := true
    strictRejectUnusual := false }

/-- Hardened Vanadium `GET_EXTENDED_PUBKEY` policy configuration (`maxSteps = 16` + BOLOS silent-export whitelist). -/
def vanadiumHardenedExpubPolicyConfig : ExpubPolicyConfig :=
  { maxSteps := MAX_BIP32_PATH_LEN
    maxResidentSteps? := some MAX_BIP32_BYTE_DEPTH
    enforceBolosOsPathLock := false
    requireSafeWhitelistForSilent := true
    allowBip352Silent := false
    strictRejectUnusual := false }

/-- Decision outcome of classifying a BIP-32 path for `GET_EXTENDED_PUBKEY`. -/
inductive ExpubPolicyDecision where
  /-- Allowed silently (`display = false`) or with normal UI (`display = true`). -/
  | allowSilent
  /-- Unusual path: rejected when `display = false`; requires interactive user warning & approval
      when `display = true` (provided OS kernel path lock allows derivation). -/
  | warnUnusual
  /-- Hard policy rejection regardless of `display` / user approval. -/
  | reject (err : SpecError)
  deriving Repr, DecidableEq, Inhabited

/-- Classify a `Bip32Path` on `KeyTree` under `ExpubPolicyConfig` and `Network`. -/
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
      if path.size > maxD || path.size > MAX_BIP32_BYTE_DEPTH then
        .reject .bip32PathTooLong
      else if cfg.enforceBolosOsPathLock && !isBolosOsPermittedPath net path then
        -- Note: on BOLOS, when `display = false` and path is unusual, `get_extended_pubkey.c`
        -- rejects with `SW_NOT_SUPPORTED` (`0x6A82`), and when `display = true`, OS `os_perso_derive_node`
        -- also fails with `0x4212 -> SW_NOT_SUPPORTED` (`.notSupported`).
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

/-- Classify a `Bip32Path` on the default `.standard` key tree under `ExpubPolicyConfig` and `Network`. -/
def classifyExpubPath (cfg : ExpubPolicyConfig) (net : Network) (path : Bip32Path) : ExpubPolicyDecision :=
  classifyExpubPathWithTree cfg net .standard path

/-- Authorize an extended public key export (`GET_EXTENDED_PUBKEY`) given `cfg`, `net`, `tree`, `path`,
    `display`, and `userApproved`, before invoking cryptographic derivation. -/
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

/-- Complete specification of `GET_EXTENDED_PUBKEY` combining OS/app path authorization, interactive UI
    confirmation (`display`, `userApproved`), and cryptographic HD derivation. -/
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

/-! ## 5. Security & Sanity Theorems (`0 sorryAx`) -/

/-- Security Theorem 1: Silent export (`display = false`) succeeds ONLY on `.allowSilent` paths
    within the tree's configured step bound and `≤ 255`. -/
theorem silent_export_requires_allowSilent
    {oracle : CryptoDerivationOracle} {cfg : ExpubPolicyConfig} {net : Network}
    {tree : KeyTree} {path : Bip32Path} {userApproved : Bool} {xpub : ExtendedPubKey}
    (hok : evalGetExtendedPubkey oracle cfg net tree path false userApproved = .ok xpub) :
    classifyExpubPathWithTree cfg net tree path = .allowSilent ∧
    path.size ≤ MAX_BIP32_BYTE_DEPTH := by
  unfold evalGetExtendedPubkey authorizeExtendedPubKeyExport at hok
  cases hdec : classifyExpubPathWithTree cfg net tree path with
  | reject err => simp [hdec, bind, Except.bind] at hok
  | warnUnusual => simp [hdec, bind, Except.bind] at hok
  | allowSilent =>
      refine ⟨rfl, ?_⟩
      unfold classifyExpubPathWithTree at hdec
      cases tree <;> simp only at hdec
      · by_cases hgt : (path.size > cfg.maxSteps || path.size > MAX_BIP32_BYTE_DEPTH) = true
        · simp [hgt] at hdec
        · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hgt
          omega
      · cases hres : cfg.maxResidentSteps? with
        | none => simp [hres] at hdec
        | some maxR =>
            simp only [hres] at hdec
            by_cases hgt : (path.size > maxR || path.size > MAX_BIP32_BYTE_DEPTH) = true
            · simp [hgt] at hdec
            · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hgt
              omega

/-- Security Theorem 2: Over-depth paths on `.standard` (`path.size > cfg.maxSteps`) are ALWAYS rejected
    with `SpecError.bip32PathTooLong`, even when `display = true` and `userApproved = true`. -/
theorem over_depth_always_rejected
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : Network)
    (path : Bip32Path) (display userApproved : Bool)
    (hover : cfg.maxSteps < path.size) :
    evalGetExtendedPubkey oracle cfg net .standard path display userApproved = .error .bip32PathTooLong := by
  have hgt : path.size > cfg.maxSteps := hover
  unfold evalGetExtendedPubkey authorizeExtendedPubKeyExport classifyExpubPathWithTree
  simp [hgt, bind, Except.bind]

/-- Security Theorem 3: Under whitelist-enforcing policies (`cfg.requireSafeWhitelistForSilent = true`),
    empty (`m`) and length-1 (`m/x`) paths are never `.allowSilent`. -/
theorem short_len0_or_len1_not_safe_silent
    (cfg : ExpubPolicyConfig) (net : Network) (path : Bip32Path)
    (hReq : cfg.requireSafeWhitelistForSilent = true)
    (hshort : path.size ≤ 1) :
    classifyExpubPath cfg net path ≠ .allowSilent := by
  unfold classifyExpubPath classifyExpubPathWithTree
  simp only [hReq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split
  · simp
  · split
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

/-- Security Theorem 4: Under whitelist-enforcing policies (`cfg.requireSafeWhitelistForSilent = true`),
    any path starting with an unhardened index (`isHardened s0 = false`) is rejected when `display = false`. -/
theorem unhardened_first_step_rejected_silently
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : Network)
    (path : Bip32Path) (userApproved : Bool)
    (s0 : UInt32) (rest : List UInt32)
    (hReq : cfg.requireSafeWhitelistForSilent = true)
    (hlist : path.toList = s0 :: rest)
    (hunhard : isHardened s0 = false) :
    ∃ err : SpecError,
      evalGetExtendedPubkey oracle cfg net .standard path false userApproved = .error err := by
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
  unfold evalGetExtendedPubkey authorizeExtendedPubKeyExport classifyExpubPathWithTree
  simp only [hReq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : (path.size > cfg.maxSteps || path.size > MAX_BIP32_BYTE_DEPTH) = true
  · simp [hlen, bind, Except.bind]
  · simp only [Bool.not_eq_true] at hlen
    simp only [hlen, Bool.false_eq_true, ↓reduceIte]
    by_cases hos : (cfg.enforceBolosOsPathLock && !isBolosOsPermittedPath net path) = true
    · simp [hos, bind, Except.bind]
    · simp only [Bool.not_eq_true] at hos
      simp only [hos, hnotBolos, hnot352, Bool.and_false, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      cases cfg.strictRejectUnusual <;> simp [bind, Except.bind]

/-- Concrete witness oracle modeling BOLOS without `HAVE_APPLICATION_FLAG_DERIVE_MASTER`:
    `deriveNode .standard #[] = none` (root derivation forbidden by OS), while
    `masterFingerprint .standard = some #[0xf5, 0xac, 0xc2, 0xfd]` succeeds and `"m/45'"` derives cleanly. -/
def witnessBolosNoMasterOracle : CryptoDerivationOracle where
  deriveNode tree path :=
    if tree == .standard && path.size == 0 then
      none
    else if tree == .standard then
      some (ByteArray.mk (#[0x02] ++ (List.replicate 32 0x11).toArray),
            ByteArray.mk (List.replicate 32 0x22).toArray)
    else
      some (ByteArray.mk (#[0x03] ++ (List.replicate 32 0x33).toArray),
            ByteArray.mk (List.replicate 32 0x44).toArray)
  masterFingerprint _ := some (ByteArray.mk #[0xf5, 0xac, 0xc2, 0xfd])
  deriveChildPub _ _ idx :=
    if isHardened idx then none
    else some (ByteArray.mk (#[0x02] ++ (List.replicate 32 0x11).toArray),
               ByteArray.mk (List.replicate 32 0x22).toArray)
  hash160 _ := ByteArray.mk (List.replicate 20 0xaa).toArray
  doubleSha256 _ := ByteArray.mk (List.replicate 32 0xbb).toArray

/-- Non-vacuous BOLOS Remediation Theorem (C-10):
    1. `"m/45'"` (`#[harden 45]`) succeeds on BOLOS with `display = true, userApproved = true`
       even though `oracle.deriveNode .standard #[] = none` (using `oracle.masterFingerprint` for `parentFingerprint`),
       while being rejected when `display = false`.
    2. Root path `"m"` (`#[]`) is rejected with `.notSupported` on BOLOS even when `display = true` and `userApproved = true`.
    3. Wrong-coin path `"m/44'/2'/333'"` (`#[harden 44, harden 2, harden 333]`) is rejected with `.notSupported`
       on BOLOS (both mainnet and testnet) even when `display = true` and `userApproved = true`. -/
theorem bolos_os_path_lock_and_depth1_derivation :
    witnessBolosNoMasterOracle.deriveNode .standard #[] = none ∧
    (∃ xpub,
      evalGetExtendedPubkey witnessBolosNoMasterOracle bolosExpubPolicyConfig .mainnet .standard
        #[harden 45] true true = .ok xpub ∧
      xpub.depth = 1 ∧
      xpub.parentFingerprint = ByteArray.mk #[0xf5, 0xac, 0xc2, 0xfd]) ∧
    evalGetExtendedPubkey witnessBolosNoMasterOracle bolosExpubPolicyConfig .mainnet .standard
      #[harden 45] false true = .error .unsupportedBip32Path ∧
    evalGetExtendedPubkey witnessBolosNoMasterOracle bolosExpubPolicyConfig .mainnet .standard
      #[] true true = .error .notSupported ∧
    evalGetExtendedPubkey witnessBolosNoMasterOracle bolosExpubPolicyConfig .mainnet .standard
      #[harden 44, harden 2, harden 333] true true = .error .notSupported ∧
    evalGetExtendedPubkey witnessBolosNoMasterOracle bolosExpubPolicyConfig .testnet .standard
      #[harden 44, harden 2, harden 333] true true = .error .notSupported := by
  let xpub45 : ExtendedPubKey := {
    version := Network.mainnet.params.xpubVersion
    depth := 1
    parentFingerprint := ByteArray.mk #[0xf5, 0xac, 0xc2, 0xfd]
    childNumber := harden 45
    chainCode := ByteArray.mk (List.replicate 32 0x22).toArray
    pubkey := ByteArray.mk (#[0x02] ++ (List.replicate 32 0x11).toArray)
  }
  exact ⟨rfl, ⟨xpub45, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩

/-- Non-vacuous Vanadium Silent Export & Depth Cap Theorem (C-10, m-01):
    1. Vanadium allows `display = false` silently without BIP-44/48/84/86 whitelisting (e.g. `"m"`, `"m/45'"`, `"m/0"`).
    2. On `KeyTree.standard`, depth `16` succeeds silently while depth `17` is rejected with `.bip32PathTooLong`.
    3. On `KeyTree.resident`, depth `255` succeeds silently (with `xpub.depth = 255`) while depth `256`
       is rejected with `.bip32PathTooLong` (preventing `UInt8` wraparound to `0`). -/
theorem vanadium_silent_export_and_tree_depth_caps :
    authorizeExtendedPubKeyExport vanadiumExpubPolicyConfig .testnet .standard #[] false false = .ok () ∧
    authorizeExtendedPubKeyExport vanadiumExpubPolicyConfig .testnet .standard #[harden 45] false false = .ok () ∧
    authorizeExtendedPubKeyExport vanadiumExpubPolicyConfig .testnet .standard #[0] false false = .ok () ∧
    authorizeExtendedPubKeyExport vanadiumExpubPolicyConfig .testnet .standard (List.replicate 16 (harden 0)).toArray false false = .ok () ∧
    authorizeExtendedPubKeyExport vanadiumExpubPolicyConfig .testnet .standard (List.replicate 17 (harden 0)).toArray false false = .error .bip32PathTooLong ∧
    (∃ xpub255,
      evalGetExtendedPubkey witnessBolosNoMasterOracle vanadiumExpubPolicyConfig .testnet .resident
        (List.replicate 255 (0 : UInt32)).toArray false false = .ok xpub255 ∧
      xpub255.depth = 255) ∧
    evalGetExtendedPubkey witnessBolosNoMasterOracle vanadiumExpubPolicyConfig .testnet .resident
      (List.replicate 256 (0 : UInt32)).toArray false false = .error .bip32PathTooLong := by
  let p255 : Bip32Path := (List.replicate 255 (0 : UInt32)).toArray
  let p256 : Bip32Path := (List.replicate 256 (0 : UInt32)).toArray
  have hSize255 : p255.size = 255 := by simp [p255]
  have hSize256 : p256.size = 256 := by simp [p256]
  have hLast255 : p255[254]?.getD 0 = 0 := by simp [p255]
  have hAuth255 : authorizeExtendedPubKeyExport vanadiumExpubPolicyConfig .testnet .resident p255 false false = .ok () := by
    unfold authorizeExtendedPubKeyExport classifyExpubPathWithTree vanadiumExpubPolicyConfig MAX_BIP32_BYTE_DEPTH
    simp [hSize255]
  have hDerive255 :
      deriveExtendedPubKeyWithOracle witnessBolosNoMasterOracle .testnet .resident p255 =
        some {
          version := Network.testnet.params.xpubVersion
          depth := 255
          parentFingerprint := ByteArray.mk #[0xaa, 0xaa, 0xaa, 0xaa]
          childNumber := 0
          chainCode := ByteArray.mk (List.replicate 32 0x44).toArray
          pubkey := ByteArray.mk (#[0x03] ++ (List.replicate 32 0x33).toArray)
        } := by
    have hNodeRes : ∀ q : Bip32Path,
        witnessBolosNoMasterOracle.deriveNode .resident q =
          some (ByteArray.mk (#[0x03] ++ (List.replicate 32 0x33).toArray),
                ByteArray.mk (List.replicate 32 0x44).toArray) := fun _ => rfl
    have hHashRes : ∀ pk : ByteArray,
        witnessBolosNoMasterOracle.hash160 pk =
          ByteArray.mk (List.replicate 20 0xaa).toArray := fun _ => rfl
    have hLast255' : p255[p255.size - 1]?.getD 0 = 0 := by rw [hSize255]; exact hLast255
    unfold deriveExtendedPubKeyWithOracle MAX_BIP32_BYTE_DEPTH
    rw [hLast255', hSize255]
    simp [hNodeRes, hHashRes]
    exact ⟨by decide, rfl⟩
  have hEval255 :
      evalGetExtendedPubkey witnessBolosNoMasterOracle vanadiumExpubPolicyConfig .testnet .resident p255 false false =
        .ok {
          version := Network.testnet.params.xpubVersion
          depth := 255
          parentFingerprint := ByteArray.mk #[0xaa, 0xaa, 0xaa, 0xaa]
          childNumber := 0
          chainCode := ByteArray.mk (List.replicate 32 0x44).toArray
          pubkey := ByteArray.mk (#[0x03] ++ (List.replicate 32 0x33).toArray)
        } := by
    unfold evalGetExtendedPubkey
    rw [hAuth255, hDerive255]
    rfl
  have hEval256 :
      evalGetExtendedPubkey witnessBolosNoMasterOracle vanadiumExpubPolicyConfig .testnet .resident p256 false false =
        .error .bip32PathTooLong := by
    unfold evalGetExtendedPubkey authorizeExtendedPubKeyExport classifyExpubPathWithTree vanadiumExpubPolicyConfig MAX_BIP32_BYTE_DEPTH
    simp [hSize256, bind, Except.bind]
  exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨_, hEval255, rfl⟩, hEval256⟩

/-- Sanity Theorem: Standard BIP-84 Mainnet account `m/84'/0'/0'` is allowed silently on BOLOS,
    whereas exporting it on Testnet (`coin_type = 1'`) is rejected by the BOLOS OS coin-type lock
    (`.reject .notSupported`) on regular `Bitcoin Test` and `.warnUnusual` on `Bitcoin Recovery`. -/
theorem bolos_bip84_mainnet_vs_testnet_policy :
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 84, harden 0, harden 0] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .testnet #[harden 84, harden 0, harden 0] = .reject .notSupported ∧
    classifyExpubPath bolosRecoveryExpubPolicyConfig .testnet #[harden 84, harden 0, harden 0] = .warnUnusual := by
  decide

/-- Sanity Theorem: Standard BIP-48 Native SegWit Multisig `m/48'/0'/0'/2'` is allowed silently,
    whereas invalid script_type `m/48'/0'/0'/3'` (same OS coin_type `0'`) is flagged `.warnUnusual`. -/
theorem bolos_bip48_script_type_policy :
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 48, harden 0, harden 0, harden 2] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 48, harden 0, harden 0, harden 3] = .warnUnusual := by
  decide

end Spec

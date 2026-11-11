/-
  Spec/SilentPayments.lean

  Formal specification of BIP-352 Silent Payments, BIP-374 Discrete Logarithm
  Equality (DLEQ) proofs, BIP-375 PSBT Silent Payment fields, and BIP-392
  `spscan` watch-only scan-key export policy deduced from:
    - LedgerHQ/vanadium (`apps/bitcoin/docs/silent_payments.md`,
      `apps/bitcoin/common/src/silent_payments/{mod,account,address,dleq,psbt,receiver,sender,tags}.rs`,
      `apps/bitcoin/common/src/fastpsbt.rs`,
      `apps/bitcoin/app/src/sp_keys.rs`,
      `apps/bitcoin/app/src/handlers/export_sp_scan_key.rs`,
      `apps/bitcoin/app/src/handlers/get_address.rs`,
      `apps/bitcoin/app/src/handlers/sign_psbt/silent_payments.rs`)
-/

namespace InternalSpec.SilentPayments

/-! ## 1. Domain Constants & Fixed-Width Byte Wrappers -/

/-- The secp256k1 group order `n` (`0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`). -/
def secp256k1Order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

theorem secp256k1Order_pos : 0 < secp256k1Order := by
  decide

/-- BIP-352 `K_MAX`: maximum number of silent payment outputs per distinct scan key in one transaction. -/
def spMaxOutputsPerScanKey : Nat := 2323

/-- BIP-32 hardened child bitmask (`2^31 = 0x80000000`). -/
def bip32HardenedBit : UInt32 := 0x80000000

/-- BIP-352 purpose (`352'`). -/
def bip352Purpose : UInt32 := 352 ||| bip32HardenedBit

/-- BIP-375 PSBT global/input/output key-type constants. -/
def psbtGlobalTxModifiable : UInt8 := 0x06
def psbtGlobalSpEcdhShare : UInt8 := 0x07
def psbtGlobalSpDleq : UInt8 := 0x08
def psbtInSpEcdhShare : UInt8 := 0x1D
def psbtInSpDleq : UInt8 := 0x1E
def psbtInSpSpendBip32Derivation : UInt8 := 0x1F
def psbtInSpTweak : UInt8 := 0x20
def psbtOutScript : UInt8 := 0x04
def psbtOutSpV0Info : UInt8 := 0x09
def psbtOutSpV0Label : UInt8 := 0x0A

/-- `SIGHASH_ALL = 0x01`, the sole explicit sighash flag permitted by BIP-375 when SP outputs exist. -/
def sighashAll : UInt32 := 0x01

/-- `SIGHASH_DEFAULT = 0x00`, the implicit BIP-341 Taproot sighash when `PSBT_IN_SIGHASH_TYPE` is absent. -/
def sighashDefault : UInt32 := 0x00

/-- BIP-341 unspendable NUMS x-only internal key `H`
    (`0x50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0`),
    excluded from BIP-352 Silent Payment input eligibility. -/
def bip341NumsXOnlyBytes : List UInt8 :=
  [ 0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54,
    0xb7, 0x8b, 0x4b, 0x60, 0x35, 0xe9, 0x7a, 0x5e,
    0x07, 0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5,
    0x47, 0xbf, 0xee, 0x9a, 0xce, 0x80, 0x3a, 0xc0 ]

theorem bip341NumsXOnlyBytes_length : bip341NumsXOnlyBytes.length = 32 := by
  rfl

/-- Exact-size byte sequence (`ByteArray` of length `n`). -/
structure SizedBytes (n : Nat) where
  bytes : ByteArray
  size_eq : bytes.size = n
  deriving DecidableEq

instance (n : Nat) : Repr (SizedBytes n) where
  reprPrec b p := reprPrec b.bytes.data p

def SizedBytes.zeros (n : Nat) : SizedBytes n :=
  { bytes := ByteArray.mk (Array.replicate n 0)
    size_eq := by simp [ByteArray.size] }

instance (n : Nat) : Inhabited (SizedBytes n) :=
  ⟨SizedBytes.zeros n⟩

def SizedBytes.append {m n : Nat} (a : SizedBytes m) (b : SizedBytes n) : SizedBytes (m + n) :=
  { bytes := ByteArray.mk (a.bytes.data ++ b.bytes.data)
    size_eq := by
      have ha : a.bytes.data.size = m := a.size_eq
      have hb : b.bytes.data.size = n := b.size_eq
      simp [ByteArray.size, ha, hb] }

/-- Pure kernel-reducible concatenation of `ByteArray`s (avoiding `@[extern]` `ByteArray.copySlice`). -/
def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

/-- Concatenate a list of `ByteArray`s purely in the Lean kernel. -/
def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl appendBytes (ByteArray.mk #[])

abbrev Bytes32 := SizedBytes 32
abbrev Bytes33 := SizedBytes 33
abbrev Bytes34 := SizedBytes 34
abbrev Bytes36 := SizedBytes 36
abbrev Bytes64 := SizedBytes 64
abbrev Bytes65 := SizedBytes 65
abbrev Bytes66 := SizedBytes 66

/-- BIP-341 unspendable NUMS x-only internal key `H` as `Bytes32`. -/
def bip341NumsXOnly : Bytes32 :=
  ⟨ByteArray.mk bip341NumsXOnlyBytes.toArray, by
    change bip341NumsXOnlyBytes.toArray.size = 32
    rw [List.size_toArray, bip341NumsXOnlyBytes_length]⟩

/-- Decode a big-endian byte list into a natural number. -/
def natFromBytesBE (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Encode a natural number into `len` big-endian bytes. -/
def natToBytesBEAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, v, acc => natToBytesBEAux k (v / 256) (UInt8.ofNat (v % 256) :: acc)

theorem natToBytesBEAux_length (k v : Nat) (acc : List UInt8) :
    (natToBytesBEAux k v acc).length = k + acc.length := by
  induction k generalizing v acc with
  | zero => simp [natToBytesBEAux]
  | succ k ih =>
    simp [natToBytesBEAux, ih, Nat.add_comm, Nat.add_left_comm]

def scalarToBytes32 (v : Nat) : Bytes32 :=
  let arr := (natToBytesBEAux 32 v []).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    change arr.size = 32
    rw [List.size_toArray, natToBytesBEAux_length]
    rfl
  ⟨ByteArray.mk arr, hlen⟩

def bytes32ToNat (b : Bytes32) : Nat :=
  natFromBytesBE b.bytes.data.toList

/-- Strict scalar parser (`< secp256k1Order`). -/
def parseScalarStrict (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if s < secp256k1Order then some s else none

/-- Non-zero strict scalar parser (`0 < s < secp256k1Order`), matching BIP-352 `hash_to_scalar`. -/
def parseNonZeroScalar (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if 0 < s && s < secp256k1Order then some s else none

/-- Modular reduction modulo `secp256k1Order`. -/
def parseScalarModN (b : Bytes32) : Nat :=
  bytes32ToNat b % secp256k1Order

/-- Encode `UInt32` in big-endian (`ser_32`). -/
def encodeU32BE (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat ((n >>> 24) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat (n &&& 0xFF)
  ]

/-- Encode `UInt32` in little-endian (4 bytes, used in outpoint serialization). -/
def encodeU32LE (v : UInt32) : SizedBytes 4 :=
  let n := v.toNat
  { bytes := ByteArray.mk #[
      UInt8.ofNat (n &&& 0xFF),
      UInt8.ofNat ((n >>> 8) &&& 0xFF),
      UInt8.ofNat ((n >>> 16) &&& 0xFF),
      UInt8.ofNat ((n >>> 24) &&& 0xFF)
    ]
    size_eq := rfl }

/-- Bytewise XOR of two 32-byte arrays (`t = ser_256(a) XOR H_{"BIP0374/aux"}(r)`). -/
def xorBytes32 (a b : Bytes32) : Bytes32 :=
  let arr := (List.zipWith (· ^^^ ·) a.bytes.data.toList b.bytes.data.toList).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    have ha : a.bytes.data.toList.length = 32 := by rw [Array.length_toList]; exact a.size_eq
    have hb : b.bytes.data.toList.length = 32 := by rw [Array.length_toList]; exact b.size_eq
    change arr.size = 32
    rw [List.size_toArray, List.length_zipWith, ha, hb]
    rfl
  ⟨ByteArray.mk arr, hlen⟩

/-! ## 2. Error Taxonomy & Cryptographic Interface -/

/-- Unified error taxonomy for BIP-352, BIP-374, BIP-375, and BIP-392. -/
inductive SpError where
  | invalidKey
  | invalidEncoding
  | invalidHash
  | invalidProofInput
  | invalidParameter
  | noInputs
  | zeroInputSum
  | tooManyRecipients
  | silentPaymentChangeLabel
  | silentPaymentSegwitVersion
  | silentPaymentSighashType
  | silentPaymentNoEligibleInputs
  | silentPaymentInputNotHeld
  | silentPaymentShareMismatch
  | silentPaymentOutputScriptMismatch
  | missingOutputScript
  | invalidSilentPaymentField
  | userRejected
  deriving Repr, DecidableEq

/-- Abstract secp256k1 point (infinity or affine point). -/
inductive SpPoint (Affine : Type) where
  | infinity : SpPoint Affine
  | affine (p : Affine) : SpPoint Affine
  deriving Repr, DecidableEq

/-- Cryptographic curve, tagged-hash, and Bech32m interface for Silent Payments & DLEQ. -/
structure SpCrypto (Affine : Type) where
  generator : Affine
  pointAdd : SpPoint Affine → SpPoint Affine → SpPoint Affine
  pointMul : Nat → SpPoint Affine → SpPoint Affine
  pointNeg : SpPoint Affine → SpPoint Affine
  hasEvenY : Affine → Bool
  xCoord : Affine → Bytes32
  liftX : Bytes32 → Option Affine
  compress : Affine → Bytes33
  decompress : Bytes33 → Option Affine
  taggedHash : String → ByteArray → Bytes32

/-! ## 3. BIP-350 Bech32m Payload Framing, BIP-352 Addresses & BIP-392 `spscan` -/

/-- Network Human-Readable Part for BIP-352 Silent Payment addresses (`sp` mainnet, `tsp` testnets). -/
inductive SpAddressHrp where
  | sp
  | tsp
  deriving Repr, DecidableEq

def SpAddressHrp.asString : SpAddressHrp → String
  | .sp => "sp"
  | .tsp => "tsp"

def SpAddressHrp.fromLowerString : String → Option SpAddressHrp
  | "sp" => some .sp
  | "tsp" => some .tsp
  | _ => none

/-- Network Human-Readable Part for BIP-392 watch-only scan keys (`spscan` mainnet, `tspscan` testnets). -/
inductive SpScanHrp where
  | spscan
  | tspscan
  deriving Repr, DecidableEq

def SpScanHrp.asString : SpScanHrp → String
  | .spscan => "spscan"
  | .tspscan => "tspscan"

def SpScanHrp.fromLowerString : String → Option SpScanHrp
  | "spscan" => some .spscan
  | "tspscan" => some .tspscan
  | _ => none

/-- Pure recursive universal predicate on lists (avoids `Classical.choice` in `List.all`). -/
def spListAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && spListAll p xs

/-- Pure recursive `DecidableEq` membership test on lists (avoids `Classical.choice` in `List.contains`). -/
def spListMem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || spListMem x ys

@[simp] theorem spListMem_nil {α : Type} [DecidableEq α] (x : α) : spListMem x [] = false := rfl
@[simp] theorem spListMem_cons {α : Type} [DecidableEq α] (x y : α) (ys : List α) :
    spListMem x (y :: ys) = (decide (x = y) || spListMem x ys) := rfl

/-- Check BIP-173 / BIP-352 5-bit-to-8-bit trailing bit padding validity:
    Given `fes : List UInt8` (each `< 32`), leftover bits `(fes.length * 5) % 8` must be `< 5`,
    and the low `padding` bits of the final 5-bit element must be zero. -/
def validBech32Padding (fes : List UInt8) : Bool :=
  let allFe32 := spListAll (fun v => v < 32) fes
  let padding := (fes.length * 5) % 8
  if !allFe32 || padding > 4 then
    false
  else
    match fes.getLast? with
    | none => true
    | some lastFe => (lastFe.toNat &&& ((1 <<< padding) - 1)) == 0

/-- Decoded Bech32m frame `(lowercaseHrp, versionFe32, payloadBytes)` after checksum & padding validation. -/
structure Bech32mCodec where
  encodeVersioned : String → UInt8 → ByteArray → Option String
  decodeVersioned : String → Option (String × UInt8 × ByteArray)

/-- BIP-352 `SilentPaymentCode`: scan public key `B_scan` and (possibly labeled) spend public key `B_m`,
    both guaranteed to be non-infinity curve points. -/
structure SilentPaymentCode (Affine : Type) where
  scan : Affine
  spend : Affine
  deriving Repr, DecidableEq

/-- Serialize `SilentPaymentCode` to 66 bytes `ser_P(B_scan) || ser_P(B_m)`. -/
def SilentPaymentCode.toBytes {Affine : Type} (c : SpCrypto Affine)
    (code : SilentPaymentCode Affine) : Bytes66 :=
  SizedBytes.append (c.compress code.scan) (c.compress code.spend)

/-- Deserialize a 66-byte `PSBT_OUT_SP_V0_INFO` / address payload into `SilentPaymentCode`. -/
def SilentPaymentCode.fromBytes {Affine : Type} (c : SpCrypto Affine)
    (raw : Bytes66) : Except SpError (SilentPaymentCode Affine) :=
  let arr1 := (raw.bytes.data.toList.take 33).toArray
  let bScanBytes : Bytes33 := ⟨ByteArray.mk arr1, by
    have h1 : raw.bytes.data.toList.length = 66 := by rw [Array.length_toList]; exact raw.size_eq
    change arr1.size = 33
    rw [List.size_toArray, List.length_take, h1]
    decide⟩
  let arr2 := (raw.bytes.data.toList.drop 33).toArray
  let bSpendBytes : Bytes33 := ⟨ByteArray.mk arr2, by
    have h1 : raw.bytes.data.toList.length = 66 := by rw [Array.length_toList]; exact raw.size_eq
    change arr2.size = 33
    rw [List.size_toArray, List.length_drop, h1]⟩
  match c.decompress bScanBytes, c.decompress bSpendBytes with
  | some scanPt, some spendPt => .ok { scan := scanPt, spend := spendPt }
  | _, _ => .error .invalidEncoding

/-- Encode a version-0 BIP-352 Silent Payment address (`sp1q...` or `tsp1q...`). -/
def encodeSpAddress {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpAddressHrp) (code : SilentPaymentCode Affine) : Except SpError String :=
  match bech.encodeVersioned hrp.asString 0 (code.toBytes c).bytes with
  | some addr => .ok addr
  | none => .error .invalidEncoding

/-- Decode a BIP-352 Silent Payment address:
    - Version `0`: payload must be **exactly** 66 bytes.
    - Versions `1..30`: payload must be **at least** 66 bytes (forward-compatible prefix).
    - Version `31` (or `> 30`): rejected (`invalidEncoding`). -/
def decodeSpAddress {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (addr : String) : Except SpError (SpAddressHrp × SilentPaymentCode Affine) := do
  let (hrpStr, version, payload) ← match bech.decodeVersioned addr with
    | some triple => .ok triple
    | none => .error .invalidEncoding
  let hrp ← match SpAddressHrp.fromLowerString hrpStr with
    | some h => .ok h
    | none => .error .invalidEncoding
  if _hV0 : decide (version = 0) then
    if hEq : payload.size = 66 then
      let code ← SilentPaymentCode.fromBytes c ⟨payload, hEq⟩
      .ok (hrp, code)
    else
      .error .invalidEncoding
  else if _hV30 : decide (version ≤ 30) then
    if hGe : 66 ≤ payload.size then
      let arr := (payload.data.toList.take 66).toArray
      have hLen : (ByteArray.mk arr).size = 66 := by
        have h1 : 66 ≤ payload.data.toList.length := by
          rw [Array.length_toList]; exact hGe
        change arr.size = 66
        rw [List.size_toArray, List.length_take, Nat.min_eq_left h1]
      let code ← SilentPaymentCode.fromBytes c ⟨ByteArray.mk arr, hLen⟩
      .ok (hrp, code)
    else
      .error .invalidEncoding
  else
    .error .invalidEncoding

/-- Encode a BIP-392 watch-only scan key (`spscan1q...` / `tspscan1q...`, version `0`, 65 bytes:
    `ser_256(b_scan) || ser_P(B_spend)`). Rejects `b_scan = 0` or `b_scan >= n`. -/
def encodeSpScanKey {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpScanHrp) (bScan : Nat) (bSpend : Affine) : Except SpError String := do
  if !(0 < bScan && bScan < secp256k1Order) then
    .error .invalidKey
  let payload65 : Bytes65 := SizedBytes.append (scalarToBytes32 bScan) (c.compress bSpend)
  match bech.encodeVersioned hrp.asString 0 payload65.bytes with
  | some s => .ok s
  | none => .error .invalidEncoding

/-- Decode a BIP-392 `spscan` / `tspscan` key (strictly version `0` and 65-byte payload). -/
def decodeSpScanKey {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (encoded : String) : Except SpError (SpScanHrp × Nat × Affine) := do
  let (hrpStr, version, payload) ← match bech.decodeVersioned encoded with
    | some triple => .ok triple
    | none => .error .invalidEncoding
  let hrp ← match SpScanHrp.fromLowerString hrpStr with
    | some h => .ok h
    | none => .error .invalidEncoding
  if hCheck : version = 0 ∧ payload.size = 65 then
    have hSz : payload.size = 65 := hCheck.2
    let arr1 := (payload.data.toList.take 32).toArray
    let scanBytes : Bytes32 := ⟨ByteArray.mk arr1, by
      have h1 : payload.data.toList.length = 65 := by rw [Array.length_toList]; exact hSz
      change arr1.size = 32
      rw [List.size_toArray, List.length_take, h1]
      decide⟩
    let arr2 := (payload.data.toList.drop 32).toArray
    let spendBytes : Bytes33 := ⟨ByteArray.mk arr2, by
      have h1 : payload.data.toList.length = 65 := by rw [Array.length_toList]; exact hSz
      change arr2.size = 33
      rw [List.size_toArray, List.length_drop, h1]⟩
    let bScan ← match parseNonZeroScalar scanBytes with
      | some s => .ok s
      | none => .error .invalidEncoding
    let bSpend ← match c.decompress spendBytes with
      | some p => .ok p
      | none => .error .invalidEncoding
    .ok (hrp, bScan, bSpend)
  else
    .error .invalidEncoding

/-! ## 4. BIP-352 Account Paths, Labels & `ExportSilentPaymentScanKey` Policy -/

/-- BIP-352 derivation path `[352', coin_type', account_index', branch', 0]`
    where `branch = 0` for `b_spend` and `branch = 1` for `b_scan`, requiring `account_index < 2^31`
    and `coin_type < 2^31`. -/
def spKeyDerivationPath (coinType : UInt32) (accountIndex : UInt32) (isScanBranch : Bool) :
    Except SpError (List UInt32) :=
  if accountIndex >= bip32HardenedBit then
    .error .invalidParameter
  else if coinType >= bip32HardenedBit then
    .error .invalidParameter
  else
    let branch : UInt32 := if isScanBranch then 1 else 0
    .ok [
      bip352Purpose,
      coinType ||| bip32HardenedBit,
      accountIndex ||| bip32HardenedBit,
      branch ||| bip32HardenedBit,
      0
    ]

/-- BIP-352 `SilentPaymentAccount`: `(accountIndex < 2^31, 0 < scanKey < n, spendKey : Affine)`. -/
structure SilentPaymentAccount (Affine : Type) where
  accountIndex : UInt32
  scanKey : Nat
  spendKey : Affine
  deriving Repr, DecidableEq

/-- Validate and construct a `SilentPaymentAccount`. -/
def SilentPaymentAccount.mkChecked {Affine : Type}
    (accountIndex : UInt32) (scanKey : Nat) (spendKey : Affine) :
    Except SpError (SilentPaymentAccount Affine) :=
  if accountIndex >= bip32HardenedBit then
    .error .invalidParameter
  else if !(0 < scanKey && scanKey < secp256k1Order) then
    .error .invalidKey
  else
    .ok { accountIndex := accountIndex, scanKey := scanKey, spendKey := spendKey }

/-- BIP-352 `label_tweak(b_scan, m) = H_{"BIP0352/Label"}(ser_256(b_scan) || ser_32(m))`
    validated as a non-zero scalar `< n`. -/
def labelTweak {Affine : Type} (c : SpCrypto Affine) (bScan : Nat) (m : UInt32) :
    Except SpError Nat := do
  let digest := c.taggedHash "BIP0352/Label" (appendBytes (scalarToBytes32 bScan).bytes (encodeU32BE m))
  match parseNonZeroScalar digest with
  | some t => .ok t
  | none => .error .invalidHash

/-- BIP-352 labeled spend public key `B_m = B_spend + label_tweak(b_scan, m) * G`. -/
def labeledSpendKey {Affine : Type} (c : SpCrypto Affine)
    (bSpend : Affine) (bScan : Nat) (m : UInt32) : Except SpError Affine := do
  let t ← labelTweak c bScan m
  match c.pointAdd (.affine bSpend) (c.pointMul t (.affine c.generator)) with
  | .infinity => .error .invalidKey
  | .affine bm => .ok bm

/-- Coordinates inside a `SilentPaymentAccount` (`Code { label }` vs BIP-376 input `Tweak`). -/
inductive SilentPaymentCoordinates where
  | code (label : Option UInt32)
  | tweak (tweakBytes : Bytes32)
  deriving Repr, DecidableEq

/-- Build a 34-byte P2TR `scriptPubKey` (`OP_1 0x20 || x_only_key`). -/
def mkP2trScript (xOnly : Bytes32) : Bytes34 :=
  let prefix2 : SizedBytes 2 := ⟨ByteArray.mk #[0x51, 0x20], rfl⟩
  SizedBytes.append prefix2 xOnly

/-- Derive the external `GetAddress` Silent Payment address for `account` and `coords`:
    - `Tweak` coordinates are rejected (`invalidParameter`: addresses handed out are codes).
    - Label `Some 0` is rejected (`silentPaymentChangeLabel`: label 0 is reserved for change). -/
def deriveAccountSpAddress {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpAddressHrp) (account : SilentPaymentAccount Affine)
    (coords : SilentPaymentCoordinates) : Except SpError String := do
  match coords with
  | .tweak _ => .error .invalidParameter
  | .code (some 0) => .error .silentPaymentChangeLabel
  | .code labelOpt =>
    let bScanPub ← match c.pointMul account.scanKey (.affine c.generator) with
      | .affine p => .ok p
      | .infinity => .error .invalidKey
    let bm ← match labelOpt with
      | none => .ok account.spendKey
      | some m => labeledSpendKey c account.spendKey account.scanKey m
    encodeSpAddress c bech hrp { scan := bScanPub, spend := bm }

/-- Derive the spent P2TR `scriptPubKey` (`0x51 0x20 || x(B_spend + tweak * G)`) for a BIP-376
    received Silent Payment input (`SilentPaymentCoordinates.tweak`). -/
def deriveAccountTweakScript {Affine : Type} (c : SpCrypto Affine)
    (account : SilentPaymentAccount Affine) (tweakBytes : Bytes32) : Except SpError Bytes34 := do
  let t ← match parseScalarStrict tweakBytes with
    | some s => .ok s
    | none => .error .invalidKey
  match c.pointAdd (.affine account.spendKey) (c.pointMul t (.affine c.generator)) with
  | .infinity => .error .invalidKey
  | .affine outPt => .ok (mkP2trScript (c.xCoord outPt))

/-- `ExportSilentPaymentScanKey` policy (`export_sp_scan_key.rs`):
    Requires `accountIndex < 2^31`, valid account derivation, AND explicit `userApproved = true`. -/
def exportSpScanKey {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpScanHrp) (deriveAccount : UInt32 → Except SpError (SilentPaymentAccount Affine))
    (accountIndex : UInt32) (userApproved : Bool) : Except SpError String := do
  if accountIndex >= bip32HardenedBit then
    .error .invalidParameter
  let account ← deriveAccount accountIndex
  if !userApproved then
    .error .userRejected
  encodeSpScanKey c bech hrp account.scanKey account.spendKey

/-! ## 5. Eligible Input Extraction, Outpoint Ordering & Sender Output Generation -/

/-- Transaction outpoint `(txid_le, vout)`. -/
structure OutPoint where
  txid : Bytes32
  vout : UInt32
  deriving Repr, DecidableEq

/-- BIP-352 36-byte outpoint encoding: `txid (32B) || le32(vout) (4B)`. -/
def outpointBytes (op : OutPoint) : Bytes36 :=
  SizedBytes.append op.txid (encodeU32LE op.vout)

/-- Strict lexicographical `<` on byte lists. -/
def listLexLt : List UInt8 → List UInt8 → Bool
  | _, [] => false
  | [], _ :: _ => true
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else listLexLt as bs

/-- Select the lexicographically smallest 36-byte serialized outpoint across **all** transaction
    inputs (eligible or not). Fails with `.noInputs` if `outpoints` is empty. -/
def smallestOutpointBytes : List OutPoint → Except SpError Bytes36
  | [] => .error .noInputs
  | op :: rest =>
    let init := outpointBytes op
    .ok (rest.foldl (fun best cur =>
      let curB := outpointBytes cur
      if listLexLt curB.bytes.data.toList best.bytes.data.toList then curB else best) init)

/-- Input script classification for BIP-352 eligibility. -/
inductive SpInputScriptKind where
  | pkh
  | wpkh
  | shWpkh
  | tr (hasNumsInternalKey : Bool)
  | other
  deriving Repr, DecidableEq

/-- Whether an input script kind is BIP-352 eligible. -/
def SpInputScriptKind.isEligible : SpInputScriptKind → Bool
  | .pkh | .wpkh | .shWpkh => true
  | .tr hasNums => !hasNums
  | .other => false

/-- Normalize an eligible input private key `d` (`0 < d < n`) per BIP-352:
    For Taproot inputs, negate `d` (`n - d`) if `d * G` has odd `y`. -/
def normalizeInputPrivKey {Affine : Type} (c : SpCrypto Affine)
    (d : Nat) (isTaproot : Bool) : Except SpError Nat := do
  if !(0 < d && d < secp256k1Order) then
    .error .invalidKey
  if !isTaproot then
    .ok d
  else
    match c.pointMul d (.affine c.generator) with
    | .infinity => .error .invalidKey
    | .affine p =>
      if c.hasEvenY p then .ok d else .ok (secp256k1Order - d)

/-- BIP-352 `input_hash = H_{"BIP0352/Inputs"}(outpoint_L || ser_P(A))`,
    validated strictly as `0 < input_hash < n`. -/
def computeInputHash {Affine : Type} (c : SpCrypto Affine)
    (outpoints : List OutPoint) (inputKeySum : SpPoint Affine) : Except SpError Nat := do
  let smallest ← smallestOutpointBytes outpoints
  let aAffine ← match inputKeySum with
    | .infinity => .error .zeroInputSum
    | .affine p => .ok p
  let digest := c.taggedHash "BIP0352/Inputs" (appendBytes smallest.bytes (c.compress aAffine).bytes)
  match parseNonZeroScalar digest with
  | some h => .ok h
  | none => .error .invalidHash

/-- Sender ECDH share `C = a * B_scan`. -/
def ecdhShare {Affine : Type} (c : SpCrypto Affine) (a : Nat) (bScan : Affine) : SpPoint Affine :=
  c.pointMul a (.affine bScan)

/-- Sender/receiver ECDH shared secret `S = input_hash * C = (input_hash * a) * B_scan`. -/
def sharedSecret {Affine : Type} (c : SpCrypto Affine)
    (inputHashScalar : Nat) (share : SpPoint Affine) : Except SpError Affine :=
  match c.pointMul inputHashScalar share with
  | .infinity => .error .invalidKey
  | .affine s => .ok s

/-- Per-output tweak `t_k = H_{"BIP0352/SharedSecret"}(ser_P(S) || be32(k))` (`0 < t_k < n`). -/
def outputTweak {Affine : Type} (c : SpCrypto Affine)
    (secret : Affine) (k : UInt32) : Except SpError Nat := do
  let digest := c.taggedHash "BIP0352/SharedSecret" (appendBytes (c.compress secret).bytes (encodeU32BE k))
  match parseNonZeroScalar digest with
  | some tk => .ok tk
  | none => .error .invalidHash

/-- Output public key `P_k = B_m + t_k * G` (must not be infinity). -/
def outputKey {Affine : Type} (c : SpCrypto Affine)
    (secret : Affine) (bSpend : Affine) (k : UInt32) : Except SpError Affine := do
  let tk ← outputTweak c secret k
  match c.pointAdd (.affine bSpend) (c.pointMul tk (.affine c.generator)) with
  | .infinity => .error .invalidKey
  | .affine pk => .ok pk

/-- Helpers updating per-scan-key counter map. -/
def lookupCounter {Affine : Type} [DecidableEq Affine]
    (scan : Affine) : List (Affine × Nat) → Nat
  | [] => 0
  | (s, cnt) :: rest => if s == scan then cnt else lookupCounter scan rest

def incrementCounter {Affine : Type} [DecidableEq Affine]
    (scan : Affine) : List (Affine × Nat) → List (Affine × Nat)
  | [] => [(scan, 1)]
  | (s, cnt) :: rest =>
    if s == scan then (s, cnt + 1) :: rest else (s, cnt) :: incrementCounter scan rest

def assignKLoop {Affine : Type} [DecidableEq Affine] :
    List (SilentPaymentCode Affine) → List (Affine × Nat) → Except SpError (List UInt32)
  | [], _ => .ok []
  | code :: rest, counters => do
    let k := lookupCounter code.scan counters
    if k >= spMaxOutputsPerScanKey then
      .error .tooManyRecipients
    let restKs ← assignKLoop rest (incrementCounter code.scan counters)
    .ok (UInt32.ofNat k :: restKs)

/-- Assign per-scan-key output counter `k ∈ 0 .. K_MAX-1` in recipient output order. -/
def assignK {Affine : Type} [DecidableEq Affine]
    (recipients : List (SilentPaymentCode Affine)) : Except SpError (List UInt32) :=
  assignKLoop recipients []

theorem assignKLoop_length {Affine : Type} [DecidableEq Affine]
    (codes : List (SilentPaymentCode Affine)) (counters : List (Affine × Nat))
    (ks : List UInt32) (h : assignKLoop codes counters = .ok ks) :
    ks.length = codes.length := by
  induction codes generalizing counters ks with
  | nil =>
    simp [assignKLoop] at h
    subst h
    rfl
  | cons code rest ih =>
    unfold assignKLoop at h
    by_cases hGe : lookupCounter code.scan counters ≥ spMaxOutputsPerScanKey
    · simp [hGe, Bind.bind, Except.bind] at h
    · simp only [hGe, ↓reduceIte] at h
      cases hRec : assignKLoop rest (incrementCounter code.scan counters) with
      | error e =>
        simp [hRec, Bind.bind, Except.bind] at h
      | ok restKs =>
        simp [hRec, Bind.bind, Except.bind] at h
        subst h
        simp [ih _ _ hRec]

theorem assignK_length {Affine : Type} [DecidableEq Affine]
    (codes : List (SilentPaymentCode Affine)) (ks : List UInt32)
    (h : assignK codes = .ok ks) :
    ks.length = codes.length :=
  assignKLoop_length codes [] ks h

/-- Receiver spending private key `d = (b_spend + tweak) mod n` (`!= 0`). -/
def receiverSpendingKey (bSpend tweak : Nat) : Except SpError Nat :=
  let d := (bSpend + tweak) % secp256k1Order
  if d == 0 then .error .invalidKey else .ok d

/-! ## 6. BIP-374 Discrete Logarithm Equality (`DLEQProve` & `DLEQVerify`) -/

/-- BIP-374 challenge scalar `e`:
    `H_{"BIP0374/challenge"}(ser_P(A) || ser_P(B) || ser_P(C) || ser_P(G) || ser_P(R_1) || ser_P(R_2) [|| m]) mod n`. -/
def dleqChallenge {Affine : Type} (c : SpCrypto Affine)
    (aPub b cPt g r1 r2 : Affine) (msg : Option Bytes32) : Nat :=
  let base := concatBytes [
    (c.compress aPub).bytes,
    (c.compress b).bytes,
    (c.compress cPt).bytes,
    (c.compress g).bytes,
    (c.compress r1).bytes,
    (c.compress r2).bytes
  ]
  let payload := match msg with
    | none => base
    | some m => appendBytes base m.bytes
  parseScalarModN (c.taggedHash "BIP0374/challenge" payload)

/-- Split a 64-byte DLEQ proof into `(eBytes, sBytes)`. -/
def splitDleqProof (proof : Bytes64) : Bytes32 × Bytes32 :=
  let arr1 := (proof.bytes.data.toList.take 32).toArray
  let eBytes : Bytes32 := ⟨ByteArray.mk arr1, by
    have h1 : proof.bytes.data.toList.length = 64 := by rw [Array.length_toList]; exact proof.size_eq
    change arr1.size = 32
    rw [List.size_toArray, List.length_take, h1]
    decide⟩
  let arr2 := (proof.bytes.data.toList.drop 32).toArray
  let sBytes : Bytes32 := ⟨ByteArray.mk arr2, by
    have h1 : proof.bytes.data.toList.length = 64 := by rw [Array.length_toList]; exact proof.size_eq
    change arr2.size = 32
    rw [List.size_toArray, List.length_drop, h1]⟩
  (eBytes, sBytes)

/-- BIP-374 `DLEQVerify(A, B, C, proof, G, m)`. -/
def dleqVerify {Affine : Type} (c : SpCrypto Affine)
    (aPub b cPt : Affine) (proof : Bytes64) (g : Affine) (msg : Option Bytes32) : Bool :=
  let (eBytes, sBytes) := splitDleqProof proof
  match parseScalarStrict eBytes, parseScalarStrict sBytes with
  | some e, some s =>
    let minusE := (secp256k1Order - (e % secp256k1Order)) % secp256k1Order
    let r1Pt := c.pointAdd (c.pointMul s (.affine g)) (c.pointMul minusE (.affine aPub))
    let r2Pt := c.pointAdd (c.pointMul s (.affine b)) (c.pointMul minusE (.affine cPt))
    match r1Pt, r2Pt with
    | .affine r1, .affine r2 => dleqChallenge c aPub b cPt g r1 r2 msg == e
    | _, _ => false
  | _, _ => false

/-- Compute the BIP-374 deterministic nonce `k` for `(a, aPub, cPt, auxRand, msg)`. -/
def dleqNonce {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (aPub cPt : Affine) (auxRand : Bytes32) (msg : Option Bytes32) : Nat :=
  let auxHash := c.taggedHash "BIP0374/aux" auxRand.bytes
  let t := xorBytes32 (scalarToBytes32 a) auxHash
  let nonceBase := concatBytes [t.bytes, (c.compress aPub).bytes, (c.compress cPt).bytes]
  let noncePayload := match msg with
    | none => nonceBase
    | some m => appendBytes nonceBase m.bytes
  parseScalarModN (c.taggedHash "BIP0374/nonce" noncePayload)

/-- BIP-374 `DLEQProve(a, B, r, G, m)`:
    Generates a 64-byte proof `ser_256(e) || ser_256(s)` that `A = a * G` and `C = a * B`
    share discrete logarithm `a`, and self-verifies via `dleqVerify` before returning. -/
def dleqProve {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (b : Affine) (auxRand : Bytes32) (g : Affine) (msg : Option Bytes32) :
    Except SpError Bytes64 := do
  if !(0 < a && a < secp256k1Order) then
    .error .invalidProofInput
  let aPub ← match c.pointMul a (.affine g) with
    | .affine p => .ok p
    | .infinity => .error .invalidProofInput
  let cPt ← match c.pointMul a (.affine b) with
    | .affine p => .ok p
    | .infinity => .error .invalidProofInput
  let k := dleqNonce c a aPub cPt auxRand msg
  if k == 0 then
    .error .invalidProofInput
  let r1 ← match c.pointMul k (.affine g) with
    | .affine p => .ok p
    | .infinity => .error .invalidProofInput
  let r2 ← match c.pointMul k (.affine b) with
    | .affine p => .ok p
    | .infinity => .error .invalidProofInput
  let e := dleqChallenge c aPub b cPt g r1 r2 msg
  let s := (k + e * a) % secp256k1Order
  let proof : Bytes64 := SizedBytes.append (scalarToBytes32 e) (scalarToBytes32 s)
  if !dleqVerify c aPub b cPt proof g msg then
    .error .invalidProofInput
  .ok proof

/-- **Soundness of `dleqProve` Self-Verification**:
    Every proof returned by `dleqProve` is guaranteed to pass `dleqVerify` on `(a*G, B, a*B)`. -/
theorem dleqProve_implies_dleqVerify {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (b g : Affine) (auxRand : Bytes32) (msg : Option Bytes32) (proof : Bytes64)
    (hProve : dleqProve c a b auxRand g msg = .ok proof) :
    ∃ (aPub cPt : Affine),
      c.pointMul a (.affine g) = .affine aPub ∧
      c.pointMul a (.affine b) = .affine cPt ∧
      dleqVerify c aPub b cPt proof g msg = true := by
  unfold dleqProve at hProve
  by_cases hRange : (!(decide (0 < a) && decide (a < secp256k1Order))) = true
  · simp [hRange, Bind.bind, Except.bind] at hProve
  · simp only [hRange, Bool.false_eq_true, ↓reduceIte] at hProve
    cases hAG : c.pointMul a (.affine g) with
    | infinity => simp [hAG, Bind.bind, Except.bind] at hProve
    | affine aPub =>
      cases hAB : c.pointMul a (.affine b) with
      | infinity => simp [hAG, hAB, Bind.bind, Except.bind] at hProve
      | affine cPt =>
        refine ⟨aPub, cPt, rfl, rfl, ?_⟩
        simp only [hAG, hAB, Bind.bind, Except.bind] at hProve
        by_cases hk : (dleqNonce c a aPub cPt auxRand msg == 0) = true
        · simp [hk] at hProve
        · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hProve
          cases hR1 : c.pointMul (dleqNonce c a aPub cPt auxRand msg) (.affine g) with
          | infinity => simp [hR1] at hProve
          | affine r1 =>
            rw [hR1] at hProve
            cases hR2 : c.pointMul (dleqNonce c a aPub cPt auxRand msg) (.affine b) with
            | infinity => simp [hR2] at hProve
            | affine r2 =>
              rw [hR2] at hProve
              simp only at hProve
              cases hVer : dleqVerify c aPub b cPt
                  (SizedBytes.append (scalarToBytes32 (dleqChallenge c aPub b cPt g r1 r2 msg))
                    (scalarToBytes32 ((dleqNonce c a aPub cPt auxRand msg + dleqChallenge c aPub b cPt g r1 r2 msg * a) % secp256k1Order)))
                  g msg
              · simp [hVer] at hProve
              · simp [hVer] at hProve
                subst hProve
                exact hVer

/-- `dleqProve` rejects `a = 0`. -/
theorem dleqProve_rejects_zero_scalar {Affine : Type} (c : SpCrypto Affine)
    (b g : Affine) (auxRand : Bytes32) (msg : Option Bytes32) :
    dleqProve c 0 b auxRand g msg = .error .invalidProofInput := by
  unfold dleqProve
  simp [Bind.bind, Except.bind]

/-! ## 7. BIP-375 PSBT Silent Payment Validation & Finalization -/

/-- Logical PSBT input view for BIP-375 Silent Payment checks. -/
structure PsbtSpInput where
  outpoint : OutPoint
  prevoutWitnessVersion : Option UInt8
  sighashType : Option UInt32
  hasInputSpEcdhShare : Bool
  hasInputSpDleq : Bool
  scriptKind : SpInputScriptKind
  tapInternalKey : Option Bytes32 := none
  deviceEligiblePrivKey : Option Nat
  deriving Repr, DecidableEq

/-- Whether `inp` spends a Taproot prevout (`witness_v1` or `tr(...)` policy). -/
def PsbtSpInput.isTaproot (inp : PsbtSpInput) : Bool :=
  match inp.prevoutWitnessVersion, inp.scriptKind with
  | some v, _ => decide (v = 1)
  | _, .tr _ => true
  | _, _ => false

/-- Effective consensus sighash type signed by the device for `inp`:
    - Taproot inputs without `PSBT_IN_SIGHASH_TYPE` default to `SIGHASH_DEFAULT (0x00)`
      (`sighash.rs:taproot_sighash_type`), so BIP-375 requires explicit `some 0x01`!
    - Legacy / SegWit-v0 inputs without `PSBT_IN_SIGHASH_TYPE` default to `SIGHASH_ALL (0x01)`. -/
def PsbtSpInput.effectiveSighashType (inp : PsbtSpInput) : UInt32 :=
  match inp.sighashType with
  | some sh => sh
  | none => if inp.isTaproot then sighashDefault else sighashAll

/-- Whether `inp` is BIP-352 eligible, excluding both boolean `hasNumsInternalKey` and literal
    `bip341NumsXOnly` (`0x50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0`). -/
def PsbtSpInput.isEligible (inp : PsbtSpInput) : Bool :=
  let hasLiteralNums := match inp.tapInternalKey with
    | some xk => decide (xk = bip341NumsXOnly)
    | none => false
  inp.scriptKind.isEligible && !hasLiteralNums

/-- Logical PSBT output view for BIP-375 Silent Payment checks (`ByteArray` without derived `Repr`). -/
structure PsbtSpOutput where
  amount : UInt64
  script : Option ByteArray
  spV0Info : Option Bytes66
  spV0Label : Option UInt32
  hasAccountCoordinates : Bool := false
  hasIdAuthProofs : Bool := false
  deriving DecidableEq

/-- Logical PSBT global Silent Payment fields (BIP-375). -/
structure PsbtSpTx (Affine : Type := Unit) where
  txModifiable : Option UInt8
  globalEcdhShares : List (Bytes33 × Bytes33)
  globalDleqProofs : List (Bytes33 × Bytes64)
  inputs : List PsbtSpInput
  outputs : List PsbtSpOutput
  spAccounts : List (SilentPaymentAccount Affine) := []
  deriving DecidableEq

/-- BIP-375 global ECDH share + DLEQ proof returned by `SignPsbt`. -/
structure SilentPaymentShareOut where
  scanKey : Bytes33
  share : Bytes33
  dleqProof : Bytes64
  deriving Repr, DecidableEq

/-- BIP-375 computed P2TR output script returned by `SignPsbt`. -/
structure SilentPaymentOutputScriptOut where
  outputIndex : UInt32
  script : Bytes34
  deriving Repr, DecidableEq

/-- Structural BIP-375 output rules (`fastpsbt.rs` & `sign_psbt/analyze.rs:315-323`). -/
def validatePsbtSpOutputs (outputs : List PsbtSpOutput) (txModifiable : Option UInt8) :
    Except SpError Unit := do
  let modifiable := ((txModifiable.getD 0).toNat &&& 0x03) != 0
  for out in outputs do
    match out.script, out.spV0Info with
    | none, none => .error .missingOutputScript
    | some _, some _ =>
      if modifiable then .error .invalidSilentPaymentField else pure ()
    | _, _ => pure ()
    if out.spV0Label.isSome && out.spV0Info.isNone then
      .error .invalidSilentPaymentField
    if out.spV0Info.isSome && (out.hasAccountCoordinates || out.hasIdAuthProofs) then
      .error .invalidSilentPaymentField

/-- Verify `PSBT_OUT_SP_V0_LABEL` against `labeledSpendKey` when both `spV0Info` and `spV0Label`
    are present on an output (`code.scan = account.scanKey * G` and
    `code.spend = labeledSpendKey account.spendKey account.scanKey m`). -/
def verifyOutputSpLabel {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (accounts : List (SilentPaymentAccount Affine))
    (code : SilentPaymentCode Affine) (labelOpt : Option UInt32) : Except SpError Unit :=
  match labelOpt with
  | none => .ok ()
  | some m =>
    let matchedAcc? := accounts.find? (fun acc =>
      match c.pointMul acc.scanKey (.affine c.generator) with
      | .affine scanPub => decide (scanPub = code.scan)
      | .infinity => false)
    match matchedAcc? with
    | none => .error .invalidSilentPaymentField
    | some acc => do
      let expectedBm ← labeledSpendKey c acc.spendKey acc.scanKey m
      if decide (expectedBm ≠ code.spend) then
        .error .invalidSilentPaymentField
      else
        .ok ()

/-- Extract indexed Silent Payment recipients `(outputIdx, code)` in output order, verifying
    any `spV0Label` against `accounts` via `labeledSpendKey`. -/
def collectSpRecipients {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (accounts : List (SilentPaymentAccount Affine)) :
    Nat → List PsbtSpOutput → Except SpError (List (Nat × SilentPaymentCode Affine))
  | _, [] => .ok []
  | idx, out :: rest => do
    let tail ← collectSpRecipients c accounts (idx + 1) rest
    match out.spV0Info with
    | none => .ok tail
    | some raw66 =>
      let code ← SilentPaymentCode.fromBytes c raw66
      verifyOutputSpLabel c accounts code out.spV0Label
      .ok ((idx, code) :: tail)

/-- Pre-review BIP-375 `analyze` checks (`silent_payments.rs:analyze`). -/
def analyzePsbtSilentPayments {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (psbt : PsbtSpTx Affine) :
    Except SpError (Option (List (Nat × SilentPaymentCode Affine) × List UInt32 × List Nat)) := do
  validatePsbtSpOutputs psbt.outputs psbt.txModifiable
  let indexedCodes ← collectSpRecipients c psbt.spAccounts 0 psbt.outputs
  if indexedCodes.isEmpty then
    return none
  let ks ← assignK (indexedCodes.map Prod.snd)
  let eligibleKeys ← psbt.inputs.foldlM (fun acc inp => do
    match inp.prevoutWitnessVersion with
    | some v => if decide (1 < v) then .error .silentPaymentSegwitVersion else pure ()
    | none => pure ()
    if decide (inp.effectiveSighashType ≠ sighashAll) then
      .error .silentPaymentSighashType
    if inp.hasInputSpEcdhShare || inp.hasInputSpDleq then
      .error .silentPaymentShareMismatch
    if !inp.isEligible then
      .ok acc
    else
      match inp.deviceEligiblePrivKey with
      | none => .error .silentPaymentInputNotHeld
      | some rawPriv =>
        let isTr := match inp.scriptKind with | .tr _ => true | _ => false
        let normPriv ← normalizeInputPrivKey c rawPriv isTr
        .ok (acc ++ [normPriv])) []
  if eligibleKeys.isEmpty then
    .error .silentPaymentNoEligibleInputs
  let recipientScanKeys : List Bytes33 :=
    indexedCodes.map (fun (_, code) => c.compress code.scan)
  for (scanK, _) in psbt.globalEcdhShares do
    if !spListMem scanK recipientScanKeys then
      .error .silentPaymentShareMismatch
  for (scanK, _) in psbt.globalDleqProofs do
    if !spListMem scanK recipientScanKeys then
      .error .silentPaymentShareMismatch
  .ok (some (indexedCodes, ks, eligibleKeys))

/-- Finalize BIP-375 Silent Payment ECDH shares, DLEQ proofs, and P2TR output scripts. -/
def finalizePsbtSilentPayments {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (psbt : PsbtSpTx Affine) (dleqAuxRand : Bytes32) :
    Except SpError (List SilentPaymentShareOut × List SilentPaymentOutputScriptOut) := do
  match ← analyzePsbtSilentPayments c psbt with
  | none => .ok ([], [])
  | some (indexedCodes, ks, eligibleKeys) =>
    let a := eligibleKeys.foldl (fun acc k => (acc + k) % secp256k1Order) 0
    if a == 0 then
      .error .zeroInputSum
    let aPub ← match c.pointMul a (.affine c.generator) with
      | .affine p => .ok p
      | .infinity => .error .zeroInputSum
    let inHash ← computeInputHash c (psbt.inputs.map (·.outpoint)) (.affine aPub)
    let distinctScans : List Affine :=
      indexedCodes.foldl (fun acc (_, code) =>
        if spListMem code.scan acc then acc else acc ++ [code.scan]) []
    let sharePairs ← distinctScans.mapM (fun scanPt => do
      let scanBytes := c.compress scanPt
      let sharePt ← match ecdhShare c a scanPt with
        | .affine p => .ok p
        | .infinity => .error .invalidKey
      let shareBytes := c.compress sharePt
      let existingShare := (psbt.globalEcdhShares.find? (fun p => p.1 == scanBytes)).map Prod.snd
      let existingProof := (psbt.globalDleqProofs.find? (fun p => p.1 == scanBytes)).map Prod.snd
      let proof ← match existingShare, existingProof with
        | none, none => dleqProve c a scanPt dleqAuxRand c.generator none
        | some exShare, some exProof =>
          if exShare == shareBytes && dleqVerify c aPub scanPt sharePt exProof c.generator none then
            .ok exProof
          else
            .error .silentPaymentShareMismatch
        | _, _ => .error .silentPaymentShareMismatch
      .ok (scanPt, sharePt, { scanKey := scanBytes, share := shareBytes, dleqProof := proof : SilentPaymentShareOut }))
    let outScripts ← (indexedCodes.zip ks).mapM (fun ((outIdx, code), k) => do
      let (_, sharePt, _) ← match sharePairs.find? (fun (s, _, _) => s == code.scan) with
        | some entry => .ok entry
        | none => .error .invalidKey
      let secret ← sharedSecret c inHash (.affine sharePt)
      let outPt ← outputKey c secret code.spend k
      let p2tr := mkP2trScript (c.xCoord outPt)
      match psbt.outputs[outIdx]? with
      | none => .error .invalidParameter
      | some psbtOut =>
        match psbtOut.script with
        | some existing =>
          if existing != p2tr.bytes then .error .silentPaymentOutputScriptMismatch
          else .ok { outputIndex := UInt32.ofNat outIdx, script := p2tr }
        | none =>
          .ok { outputIndex := UInt32.ofNat outIdx, script := p2tr })
    .ok (sharePairs.map (fun (_, _, resp) => resp), outScripts)

/-! ## 8. Security Rejection Theorems & Non-Vacuity Witnesses -/

/-- `deriveAccountSpAddress` strictly forbids handing out the reserved change label `m = 0`. -/
theorem deriveAccountSpAddress_rejects_change_label {Affine : Type}
    (c : SpCrypto Affine) (bech : Bech32mCodec) (hrp : SpAddressHrp)
    (account : SilentPaymentAccount Affine) :
    deriveAccountSpAddress c bech hrp account (.code (some 0)) =
      .error .silentPaymentChangeLabel := by
  rfl

/-- `deriveAccountSpAddress` rejects `Tweak` coordinates (input spending coordinates are not addresses). -/
theorem deriveAccountSpAddress_rejects_tweak_coords {Affine : Type}
    (c : SpCrypto Affine) (bech : Bech32mCodec) (hrp : SpAddressHrp)
    (account : SilentPaymentAccount Affine) (tw : Bytes32) :
    deriveAccountSpAddress c bech hrp account (.tweak tw) =
      .error .invalidParameter := by
  rfl

/-- `exportSpScanKey` never exports a scan key when `userApproved = false`. -/
theorem exportSpScanKey_requires_user_consent {Affine : Type}
    (c : SpCrypto Affine) (bech : Bech32mCodec) (hrp : SpScanHrp)
    (deriveAccount : UInt32 → Except SpError (SilentPaymentAccount Affine))
    (accountIndex : UInt32) :
    ∀ s, exportSpScanKey c bech hrp deriveAccount accountIndex false ≠ .ok s := by
  intro s h
  unfold exportSpScanKey at h
  by_cases hIdx : accountIndex >= bip32HardenedBit
  · simp [hIdx, Bind.bind, Except.bind] at h
  · simp only [hIdx, ↓reduceIte] at h
    cases hDer : deriveAccount accountIndex with
    | error e => simp [hDer, Bind.bind, Except.bind] at h
    | ok acc => simp [hDer, Bind.bind, Except.bind] at h

/-- `exportSpScanKey` rejects hardened/out-of-range account indices (`>= 2^31`). -/
theorem exportSpScanKey_rejects_hardened_index {Affine : Type}
    (c : SpCrypto Affine) (bech : Bech32mCodec) (hrp : SpScanHrp)
    (deriveAccount : UInt32 → Except SpError (SilentPaymentAccount Affine))
    (userApproved : Bool) :
    exportSpScanKey c bech hrp deriveAccount 0x80000000 userApproved =
      .error .invalidParameter := by
  rfl

/-- `validatePsbtSpOutputs` rejects an output carrying a pre-computed `script` alongside `spV0Info`
    while `txModifiable` still allows modifying inputs or outputs (`bits 0..1 != 0`). -/
theorem validatePsbtSpOutputs_rejects_modifiable_computed_script
    (raw66 : Bytes66) (scr : ByteArray) :
    validatePsbtSpOutputs
      [{ amount := 1000, script := some scr, spV0Info := some raw66, spV0Label := none }]
      (some 0x01) = .error .invalidSilentPaymentField := by
  rfl

/-- `validatePsbtSpOutputs` rejects an orphan `PSBT_OUT_SP_V0_LABEL` without `PSBT_OUT_SP_V0_INFO`. -/
theorem validatePsbtSpOutputs_rejects_orphan_label (scr : ByteArray) :
    validatePsbtSpOutputs
      [{ amount := 1000, script := some scr, spV0Info := none, spV0Label := some 1 }]
      none = .error .invalidSilentPaymentField := by
  rfl

/-- `validatePsbtSpOutputs` rejects an output combining `spV0Info` with standard wallet-policy
    account coordinates (`sign_psbt/analyze.rs:320`). -/
theorem validatePsbtSpOutputs_rejects_spV0Info_with_account_coords (raw66 : Bytes66) :
    validatePsbtSpOutputs
      [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none,
         hasAccountCoordinates := true }]
      none = .error .invalidSilentPaymentField := by
  rfl

/-- `validatePsbtSpOutputs` rejects an output combining `spV0Info` with external identity-auth
    proofs (`sign_psbt/analyze.rs:320`). -/
theorem validatePsbtSpOutputs_rejects_spV0Info_with_idAuth (raw66 : Bytes66) :
    validatePsbtSpOutputs
      [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none,
         hasIdAuthProofs := true }]
      none = .error .invalidSilentPaymentField := by
  rfl

/-- `analyzePsbtSilentPayments` rejects inputs with SegWit witness version `> 1` (e.g., v2). -/
theorem analyzePsbtSilentPayments_rejects_segwit_v2 {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (code : SilentPaymentCode Affine) (raw66 : Bytes66)
    (hCode : SilentPaymentCode.fromBytes c raw66 = .ok code) (op : OutPoint) :
    analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := [{
        outpoint := op
        prevoutWitnessVersion := some 2
        sighashType := none
        hasInputSpEcdhShare := false
        hasInputSpDleq := false
        scriptKind := .wpkh
        deviceEligiblePrivKey := some 1
      }]
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none }]
    } = .error .silentPaymentSegwitVersion := by
  unfold analyzePsbtSilentPayments validatePsbtSpOutputs
  simp [collectSpRecipients, verifyOutputSpLabel, hCode, assignK, assignKLoop, lookupCounter,
    spMaxOutputsPerScanKey, ForIn.forIn, List.foldlM, Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- `analyzePsbtSilentPayments` rejects explicit `SIGHASH_DEFAULT (0x00)` (BIP-375 allows only `SIGHASH_ALL = 0x01`). -/
theorem analyzePsbtSilentPayments_rejects_non_sighash_all {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (code : SilentPaymentCode Affine) (raw66 : Bytes66)
    (hCode : SilentPaymentCode.fromBytes c raw66 = .ok code) (op : OutPoint) :
    analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := [{
        outpoint := op
        prevoutWitnessVersion := some 1
        sighashType := some 0x00
        hasInputSpEcdhShare := false
        hasInputSpDleq := false
        scriptKind := .tr false
        deviceEligiblePrivKey := some 1
      }]
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none }]
    } = .error .silentPaymentSighashType := by
  unfold analyzePsbtSilentPayments validatePsbtSpOutputs
  simp [collectSpRecipients, verifyOutputSpLabel, PsbtSpInput.effectiveSighashType, hCode,
    sighashAll, assignK, assignKLoop, lookupCounter,
    spMaxOutputsPerScanKey, ForIn.forIn, List.foldlM, Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- `analyzePsbtSilentPayments` rejects Taproot inputs with implicit `sighashType = none`
    (which signs with `SIGHASH_DEFAULT = 0x00`, violating BIP-375's `SIGHASH_ALL` mandate). -/
theorem analyzePsbtSilentPayments_rejects_taproot_implicit_sighash_default {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (code : SilentPaymentCode Affine) (raw66 : Bytes66)
    (hCode : SilentPaymentCode.fromBytes c raw66 = .ok code) (op : OutPoint) :
    analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := [{
        outpoint := op
        prevoutWitnessVersion := some 1
        sighashType := none
        hasInputSpEcdhShare := false
        hasInputSpDleq := false
        scriptKind := .tr false
        deviceEligiblePrivKey := some 1
      }]
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none }]
    } = .error .silentPaymentSighashType := by
  unfold analyzePsbtSilentPayments validatePsbtSpOutputs
  simp [collectSpRecipients, verifyOutputSpLabel, PsbtSpInput.effectiveSighashType,
    PsbtSpInput.isTaproot, sighashDefault, sighashAll, hCode, assignK, assignKLoop, lookupCounter,
    spMaxOutputsPerScanKey, ForIn.forIn, List.foldlM, Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- `analyzePsbtSilentPayments` excludes Taproot inputs whose internal key is the literal
    BIP-341 NUMS x-only point (`bip341NumsXOnly`), failing with `.silentPaymentNoEligibleInputs`
    when no other eligible input exists. -/
theorem analyzePsbtSilentPayments_excludes_literal_bip341_nums {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (code : SilentPaymentCode Affine) (raw66 : Bytes66)
    (hCode : SilentPaymentCode.fromBytes c raw66 = .ok code) (op : OutPoint) :
    analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := [{
        outpoint := op
        prevoutWitnessVersion := some 1
        sighashType := some sighashAll
        hasInputSpEcdhShare := false
        hasInputSpDleq := false
        scriptKind := .tr false
        tapInternalKey := some bip341NumsXOnly
        deviceEligiblePrivKey := some 1
      }]
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none }]
    } = .error .silentPaymentNoEligibleInputs := by
  unfold analyzePsbtSilentPayments validatePsbtSpOutputs
  simp [collectSpRecipients, verifyOutputSpLabel, PsbtSpInput.effectiveSighashType,
    PsbtSpInput.isEligible, SpInputScriptKind.isEligible, sighashAll, hCode, assignK,
    assignKLoop, lookupCounter, spMaxOutputsPerScanKey,
    ForIn.forIn, List.foldlM, Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- `analyzePsbtSilentPayments` rejects an output carrying `spV0Info` + `spV0Label = some m`
    when `code.spend` does not match `labeledSpendKey` for the account owning `code.scan`. -/
theorem analyzePsbtSilentPayments_rejects_mismatched_spV0Label {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (acc : SilentPaymentAccount Affine)
    (code : SilentPaymentCode Affine) (expectedBm : Affine) (raw66 : Bytes66) (m : UInt32)
    (hCode : SilentPaymentCode.fromBytes c raw66 = .ok code)
    (hScan : c.pointMul acc.scanKey (.affine c.generator) = .affine code.scan)
    (hLbl : labeledSpendKey c acc.spendKey acc.scanKey m = .ok expectedBm)
    (hMismatch : expectedBm ≠ code.spend) :
    analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := []
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := some m }]
      spAccounts := [acc]
    } = .error .invalidSilentPaymentField := by
  unfold analyzePsbtSilentPayments validatePsbtSpOutputs
  simp [collectSpRecipients, verifyOutputSpLabel, hCode, hScan, hLbl, hMismatch,
    ForIn.forIn, Pure.pure, Except.pure, Bind.bind, Except.bind]

/-- Concrete toy `SpCrypto Unit` and `Bech32mCodec` for non-vacuity witness proofs. -/
def spOneByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[1]), by simp [ByteArray.size]⟩

def spTwoByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[2]), by simp [ByteArray.size]⟩

def spFiveByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[5]), by simp [ByteArray.size]⟩

def spNineByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[9]), by simp [ByteArray.size]⟩

def spXByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[0x33]), by simp [ByteArray.size]⟩

def toySpCompressedPk : Bytes33 :=
  ⟨ByteArray.mk (#[0x02] ++ Array.replicate 32 0x22), by simp [ByteArray.size]⟩

def nonVacuousSpCrypto : SpCrypto Unit :=
  { generator := ()
    pointAdd := fun p q =>
      match p, q with
      | .infinity, x => x
      | x, .infinity => x
      | .affine _, .affine _ => .affine ()
    pointMul := fun k p =>
      if k % secp256k1Order == 0 then .infinity else p
    pointNeg := fun p => p
    hasEvenY := fun _ => true
    xCoord := fun _ => spXByte32
    liftX := fun _ => some ()
    compress := fun _ => toySpCompressedPk
    decompress := fun _ => some ()
    taggedHash := fun _ _ => spOneByte32 }

def nonVacuousBech32m : Bech32mCodec :=
  { encodeVersioned := fun hrp ver payload =>
      if decide (ver = 0) then some (hrp ++ "1q" ++ toString payload.size) else none
    decodeVersioned := fun _ => none }

theorem sp_bytes32ToNat_one : bytes32ToNat spOneByte32 = 1 := by decide
theorem sp_bytes32ToNat_two : bytes32ToNat spTwoByte32 = 2 := by decide
theorem sp_scalarToBytes32_one : scalarToBytes32 1 = spOneByte32 := by decide
theorem sp_scalarToBytes32_two : scalarToBytes32 2 = spTwoByte32 := by decide

/-- **Non-Vacuity Witness**: There exists a valid BIP-375 PSBT with a Silent Payment output and
    an eligible input (explicit `sighashType := some sighashAll`, verified change `spV0Label`)
    such that `finalizePsbtSilentPayments` succeeds, emitting 1 verified DLEQ ECDH share and
    1 P2TR output script (`0x51 0x20 || x(P_0)`). -/
theorem nonvacuous_finalizePsbtSilentPayments_ok :
    ∃ (psbt : PsbtSpTx Unit) (shares : List SilentPaymentShareOut)
      (scripts : List SilentPaymentOutputScriptOut),
      finalizePsbtSilentPayments nonVacuousSpCrypto psbt spFiveByte32 =
        .ok (shares, scripts) ∧
      shares.length = 1 ∧
      scripts.length = 1 := by
  let code : SilentPaymentCode Unit := { scan := (), spend := () }
  let codeBytes : Bytes66 := code.toBytes nonVacuousSpCrypto
  let acc : SilentPaymentAccount Unit := { accountIndex := 0, scanKey := 1, spendKey := () }
  let inp : PsbtSpInput := {
    outpoint := { txid := spNineByte32, vout := 0 }
    prevoutWitnessVersion := some 1
    sighashType := some sighashAll
    hasInputSpEcdhShare := false
    hasInputSpDleq := false
    scriptKind := .tr false
    deviceEligiblePrivKey := some 1
  }
  let out : PsbtSpOutput := {
    amount := 50000
    script := none
    spV0Info := some codeBytes
    spV0Label := some 0
  }
  let psbt : PsbtSpTx Unit := {
    txModifiable := some 0
    globalEcdhShares := []
    globalDleqProofs := []
    inputs := [inp]
    outputs := [out]
    spAccounts := [acc]
  }
  let proof64 : Bytes64 := SizedBytes.append spOneByte32 spTwoByte32
  let shareOut : SilentPaymentShareOut := {
    scanKey := toySpCompressedPk
    share := toySpCompressedPk
    dleqProof := proof64
  }
  let scriptOut : SilentPaymentOutputScriptOut := {
    outputIndex := 0
    script := mkP2trScript spXByte32
  }
  have hNotLe1 : ¬(secp256k1Order ≤ 1) := by decide
  have hOneMod : parseScalarModN spOneByte32 = 1 := by decide
  have hOneNz : parseNonZeroScalar spOneByte32 = some 1 := by decide
  have hOneStrict : parseScalarStrict spOneByte32 = some 1 := by decide
  have hTwoStrict : parseScalarStrict spTwoByte32 = some 2 := by decide
  have hSplit : splitDleqProof proof64 = (spOneByte32, spTwoByte32) := by
    decide
  have hHash : ∀ tag msg, nonVacuousSpCrypto.taggedHash tag msg = spOneByte32 := fun _ _ => rfl
  have hComp : ∀ p, nonVacuousSpCrypto.compress p = toySpCompressedPk := fun _ => rfl
  have hDecomp : ∀ b, nonVacuousSpCrypto.decompress b = some () := fun _ => rfl
  have hEven : ∀ p, nonVacuousSpCrypto.hasEvenY p = true := fun _ => rfl
  have hXCoord : ∀ p, nonVacuousSpCrypto.xCoord p = spXByte32 := fun _ => rfl
  have hGenEq : nonVacuousSpCrypto.generator = () := rfl
  have hAddAff : nonVacuousSpCrypto.pointAdd (.affine ()) (.affine ()) = .affine () := rfl
  have hMul1 : ∀ p, nonVacuousSpCrypto.pointMul 1 p = p := by
    intro p
    show (if 1 % secp256k1Order == 0 then SpPoint.infinity else p) = p
    have h1 : (1 % secp256k1Order == 0) = false := by decide
    rw [h1]; rfl
  have hMul2 : ∀ p, nonVacuousSpCrypto.pointMul 2 p = p := by
    intro p
    show (if 2 % secp256k1Order == 0 then SpPoint.infinity else p) = p
    have h1 : (2 % secp256k1Order == 0) = false := by decide
    rw [h1]; rfl
  have hMulMinus1 : ∀ p, nonVacuousSpCrypto.pointMul ((secp256k1Order - 1 % secp256k1Order) % secp256k1Order) p = p := by
    intro p
    show (if ((secp256k1Order - 1 % secp256k1Order) % secp256k1Order) % secp256k1Order == 0 then SpPoint.infinity else p) = p
    have h1 : (((secp256k1Order - 1 % secp256k1Order) % secp256k1Order) % secp256k1Order == 0) = false := by decide
    rw [h1]; rfl
  have hOneAddMod : (1 + 1) % secp256k1Order = 2 := by decide
  have hVerify : dleqVerify nonVacuousSpCrypto () () () proof64 () none = true := by
    unfold dleqVerify dleqChallenge
    rw [hSplit]
    simp only [hOneStrict, hTwoStrict, hMul2, hMulMinus1, hAddAff, hHash, hOneMod]
    decide
  have hProve : dleqProve nonVacuousSpCrypto 1 () spFiveByte32 () none = .ok proof64 := by
    unfold dleqProve dleqNonce dleqChallenge
    simp [hNotLe1, hMul1, hHash, hOneMod, hOneAddMod, sp_scalarToBytes32_one,
      sp_scalarToBytes32_two, proof64, hVerify, Bind.bind, Except.bind]
  have hAnalyze : analyzePsbtSilentPayments nonVacuousSpCrypto psbt =
      .ok (some ([(0, code)], [0], [1])) := by
    unfold analyzePsbtSilentPayments validatePsbtSpOutputs normalizeInputPrivKey
    simp [collectSpRecipients, verifyOutputSpLabel, labeledSpendKey, labelTweak,
      SilentPaymentCode.fromBytes, PsbtSpInput.effectiveSighashType, PsbtSpInput.isEligible,
      SpInputScriptKind.isEligible, sighashAll,
      psbt, acc, inp, out, code, hDecomp, hComp, hHash, hOneNz, hAddAff, hMul1, hEven, hNotLe1,
      assignK, assignKLoop, lookupCounter, spMaxOutputsPerScanKey, ForIn.forIn, List.foldlM,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hFin :
      finalizePsbtSilentPayments nonVacuousSpCrypto psbt spFiveByte32 =
        .ok ([shareOut], [scriptOut]) := by
    have hOneModOrd : 1 % secp256k1Order = 1 := by decide
    unfold finalizePsbtSilentPayments computeInputHash smallestOutpointBytes
      ecdhShare sharedSecret outputKey outputTweak
    simp [hAnalyze, psbt, inp, out, code, shareOut, scriptOut,
      hOneModOrd, hMul1, hAddAff, hHash, hComp, hXCoord, hGenEq, hOneNz, hProve,
      List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨psbt, [shareOut], [scriptOut], hFin, rfl, rfl⟩

end InternalSpec.SilentPayments

import InternalSpec

/-!
# `BitcoinLedger.SilentPayments` — Executable BIP-352, BIP-374, BIP-375 & BIP-392 Implementation

Pure Lean 4 executable implementation of:
1. BIP-352 Silent Payment addresses (`sp`/`tsp`), versioned Bech32m framing, and label tweaks.
2. BIP-392 watch-only scan-key export (`spscan`/`tspscan`) with strict user-consent & account-index gates.
3. Eligible input classification (`P2PKH`, `P2WPKH`, `P2SH-P2WPKH`, `P2TR` excluding BIP-341 NUMS `H`),
   lexicographically smallest 36-byte outpoint selection, and `BIP0352/Inputs` input hash.
4. Sender ECDH share `C = a * B_scan`, shared secret `S = input_hash * C`, `k`-indexed
   `BIP0352/SharedSecret` output key `P_k = B_m + t_k * G`, and receiver spending key derivation.
5. BIP-374 DLEQ proof generation (`dleqProve`) and verification (`dleqVerify`).
6. BIP-375 PSBT Silent Payment validation & finalization (explicit `SIGHASH_ALL`, `spV0Label`
   verification, BIP-341 NUMS internal key rejection, `TX_MODIFIABLE` & output exclusion rules).

Written constructively (`0 Classical.choice`) for freestanding 32-bit compilation and exact
refinement proofs in `Proofs.SilentPayments`.
-/

namespace BitcoinLedger.SilentPayments

open InternalSpec.SilentPayments (
  SizedBytes Bytes32 Bytes33 Bytes34 Bytes36 Bytes64 Bytes65 Bytes66
  SpError SpPoint SpCrypto SpAddressHrp SpScanHrp Bech32mCodec
  SilentPaymentCode SilentPaymentAccount SilentPaymentCoordinates
  OutPoint SpInputScriptKind PsbtSpInput PsbtSpOutput PsbtSpTx
  SilentPaymentShareOut SilentPaymentOutputScriptOut
)

/-! ## 1. Constants & Byte Encoding Primitives -/

/-- Secp256k1 group order `n`. -/
def secp256k1Order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- BIP-352 `K_MAX`: max Silent Payment outputs per distinct scan key (`2323`). -/
def spMaxOutputsPerScanKey : Nat := 2323

/-- BIP-32 hardened child bitmask (`0x80000000`). -/
def bip32HardenedBit : UInt32 := 0x80000000

/-- BIP-352 purpose (`352'`). -/
def bip352Purpose : UInt32 := 352 ||| bip32HardenedBit

/-- `SIGHASH_ALL = 0x01`. -/
def sighashAll : UInt32 := 0x01

/-- `SIGHASH_DEFAULT = 0x00`. -/
def sighashDefault : UInt32 := 0x00

/-- BIP-341 unspendable NUMS x-only internal key `H` (`50929b74...`). -/
def bip341NumsXOnly : Bytes32 :=
  ⟨ByteArray.mk #[
      0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54,
      0xb7, 0x8b, 0x4b, 0x60, 0x35, 0xe9, 0x7a, 0x5e,
      0x07, 0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5,
      0x47, 0xbf, 0xee, 0x9a, 0xce, 0x80, 0x3a, 0xc0 ],
    rfl⟩

/-- Pure byte-list equality (`0 Classical.choice`). -/
def byteListEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a = b) && byteListEq as bs
  | _, _ => false

/-- Pure `ByteArray` equality (`0 Classical.choice`). -/
def bytesEq (a b : ByteArray) : Bool :=
  byteListEq a.data.toList b.data.toList

/-- Pure universal list check (`0 Classical.choice`). -/
def spListAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && spListAll p xs

/-- Pure list membership check (`0 Classical.choice`). -/
def spListMem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || spListMem x ys

/-- Pure `ByteArray` concatenation. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

/-- Concatenate a list of `ByteArray`s. -/
def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl appendBytes (ByteArray.mk #[])

/-- Concatenate two `SizedBytes`. -/
def appendSized {m n : Nat} (a : SizedBytes m) (b : SizedBytes n) : SizedBytes (m + n) :=
  { bytes := ByteArray.mk (a.bytes.data ++ b.bytes.data)
    size_eq := by
      have ha : a.bytes.data.size = m := a.size_eq
      have hb : b.bytes.data.size = n := b.size_eq
      simp [ByteArray.size, ha, hb] }

/-- Decode big-endian byte list into `Nat`. -/
def natFromBytesBE (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Tail-recursive big-endian byte encoder. -/
def natToBytesBEAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, v, acc => natToBytesBEAux k (v / 256) (UInt8.ofNat (v % 256) :: acc)

theorem natToBytesBEAux_length (k v : Nat) (acc : List UInt8) :
    (natToBytesBEAux k v acc).length = k + acc.length := by
  induction k generalizing v acc with
  | zero => simp [natToBytesBEAux]
  | succ k ih =>
    simp [natToBytesBEAux, ih, Nat.add_comm, Nat.add_left_comm]

/-- Encode `v : Nat` as 32 big-endian bytes (`ser_256`). -/
def scalarToBytes32 (v : Nat) : Bytes32 :=
  let arr := (natToBytesBEAux 32 v []).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    change arr.size = 32
    rw [List.size_toArray, natToBytesBEAux_length]
    rfl
  ⟨ByteArray.mk arr, hlen⟩

/-- Decode a 32-byte big-endian scalar. -/
def bytes32ToNat (b : Bytes32) : Nat :=
  natFromBytesBE b.bytes.data.toList

/-- Strict scalar parser (`< secp256k1Order`). -/
def parseScalarStrict (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if decide (s < secp256k1Order) then some s else none

/-- Non-zero strict scalar parser (`0 < s < secp256k1Order`). -/
def parseNonZeroScalar (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if decide (0 < s) && decide (s < secp256k1Order) then some s else none

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

/-- Encode `UInt32` in little-endian (4 bytes). -/
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

/-! ## 2. BIP-352 Silent Payment Addresses & BIP-392 `spscan`/`tspscan` -/

/-- Check BIP-173/352 5-bit-to-8-bit trailing bit padding validity. -/
def validBech32Padding (fes : List UInt8) : Bool :=
  let allFe32 := spListAll (fun v => decide (v < 32)) fes
  let padding := (fes.length * 5) % 8
  if !allFe32 || decide (padding > 4) then
    false
  else
    match fes.getLast? with
    | none => true
    | some lastFe => decide ((lastFe.toNat &&& ((1 <<< padding) - 1)) = 0)

/-- Canonical Bech32m codec instantiated directly from `InternalSpec.Script` (`encodeBech32Raw?` / `decodeBech32Raw?`). -/
def canonicalBech32mCodec : Bech32mCodec :=
  InternalSpec.Unified.canonicalScriptBech32mCodec

/-- Serialize `SilentPaymentCode` to 66 bytes `ser_P(B_scan) || ser_P(B_m)`. -/
def serializeSpCode {Affine : Type} (c : SpCrypto Affine)
    (code : SilentPaymentCode Affine) : Bytes66 :=
  appendSized (c.compress code.scan) (c.compress code.spend)

/-- Deserialize a 66-byte `PSBT_OUT_SP_V0_INFO` / address payload into `SilentPaymentCode`. -/
def deserializeSpCode {Affine : Type} (c : SpCrypto Affine)
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

/-- Encode a version-0 BIP-352 Silent Payment address (`sp1q...` / `tsp1q...`). -/
def encodeSpAddress {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpAddressHrp) (code : SilentPaymentCode Affine) : Except SpError String :=
  match bech.encodeVersioned hrp.asString 0 (serializeSpCode c code).bytes with
  | some addr => .ok addr
  | none => .error .invalidEncoding

/-- Decode a BIP-352 Silent Payment address (`v0` exact 66B, `v1..30` prefix ≥ 66B, `v31` rejected). -/
def decodeSpAddress {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (addr : String) : Except SpError (SpAddressHrp × SilentPaymentCode Affine) :=
  match bech.decodeVersioned addr with
  | none => .error .invalidEncoding
  | some (hrpStr, version, payload) =>
    match SpAddressHrp.fromLowerString hrpStr with
    | none => .error .invalidEncoding
    | some hrp =>
      if decide (version = 0) then
        if hEq : payload.size = 66 then
          match deserializeSpCode c ⟨payload, hEq⟩ with
          | .error e => .error e
          | .ok code => .ok (hrp, code)
        else
          .error .invalidEncoding
      else if decide (version ≤ 30) then
        if hGe : 66 ≤ payload.size then
          let arr := (payload.data.toList.take 66).toArray
          have hLen : (ByteArray.mk arr).size = 66 := by
            have h1 : 66 ≤ payload.data.toList.length := by
              rw [Array.length_toList]; exact hGe
            change arr.size = 66
            rw [List.size_toArray, List.length_take, Nat.min_eq_left h1]
          match deserializeSpCode c ⟨ByteArray.mk arr, hLen⟩ with
          | .error e => .error e
          | .ok code => .ok (hrp, code)
        else
          .error .invalidEncoding
      else
        .error .invalidEncoding

/-- Encode a BIP-392 watch-only scan key (`spscan` / `tspscan`, version 0, 65 bytes). -/
def encodeSpScanKey {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpScanHrp) (bScan : Nat) (bSpend : Affine) : Except SpError String :=
  if !(decide (0 < bScan) && decide (bScan < secp256k1Order)) then
    .error .invalidKey
  else
    let payload65 : Bytes65 := appendSized (scalarToBytes32 bScan) (c.compress bSpend)
    match bech.encodeVersioned hrp.asString 0 payload65.bytes with
    | some s => .ok s
    | none => .error .invalidEncoding

/-- Decode a BIP-392 `spscan` / `tspscan` key (strictly version 0 and 65 bytes). -/
def decodeSpScanKey {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (encoded : String) : Except SpError (SpScanHrp × Nat × Affine) :=
  match bech.decodeVersioned encoded with
  | none => .error .invalidEncoding
  | some (hrpStr, version, payload) =>
    match SpScanHrp.fromLowerString hrpStr with
    | none => .error .invalidEncoding
    | some hrp =>
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
        match parseNonZeroScalar scanBytes with
        | none => .error .invalidEncoding
        | some bScan =>
          match c.decompress spendBytes with
          | none => .error .invalidEncoding
          | some bSpend => .ok (hrp, bScan, bSpend)
      else
        .error .invalidEncoding

/-! ## 3. BIP-352 Account Paths, Labels & `exportSpScanKey` Policy -/

/-- BIP-352 derivation path `[352', coin_type', account_index', branch', 0]`. -/
def spKeyDerivationPath (coinType : UInt32) (accountIndex : UInt32) (isScanBranch : Bool) :
    Except SpError (List UInt32) :=
  if decide (accountIndex ≥ bip32HardenedBit) then
    .error .invalidParameter
  else if decide (coinType ≥ bip32HardenedBit) then
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

/-- Validate and construct a `SilentPaymentAccount`. -/
def mkCheckedSpAccount {Affine : Type}
    (accountIndex : UInt32) (scanKey : Nat) (spendKey : Affine) :
    Except SpError (SilentPaymentAccount Affine) :=
  if decide (accountIndex ≥ bip32HardenedBit) then
    .error .invalidParameter
  else if !(decide (0 < scanKey) && decide (scanKey < secp256k1Order)) then
    .error .invalidKey
  else
    .ok { accountIndex := accountIndex, scanKey := scanKey, spendKey := spendKey }

/-- BIP-352 `label_tweak(b_scan, m) = H_{"BIP0352/Label"}(ser_256(b_scan) || ser_32(m))`. -/
def labelTweak {Affine : Type} (c : SpCrypto Affine) (bScan : Nat) (m : UInt32) :
    Except SpError Nat :=
  let digest := c.taggedHash "BIP0352/Label" (appendBytes (scalarToBytes32 bScan).bytes (encodeU32BE m))
  match parseNonZeroScalar digest with
  | some t => .ok t
  | none => .error .invalidHash

/-- BIP-352 labeled spend public key `B_m = B_spend + label_tweak(b_scan, m) * G`. -/
def labeledSpendKey {Affine : Type} (c : SpCrypto Affine)
    (bSpend : Affine) (bScan : Nat) (m : UInt32) : Except SpError Affine :=
  match labelTweak c bScan m with
  | .error e => .error e
  | .ok t =>
    match c.pointAdd (.affine bSpend) (c.pointMul t (.affine c.generator)) with
    | .infinity => .error .invalidKey
    | .affine bm => .ok bm

/-- Build a 34-byte P2TR `scriptPubKey` (`0x51 0x20 || x_only_key`). -/
def mkP2trScript (xOnly : Bytes32) : Bytes34 :=
  let prefix2 : SizedBytes 2 := ⟨ByteArray.mk #[0x51, 0x20], rfl⟩
  appendSized prefix2 xOnly

/-- Derive external `GetAddress` Silent Payment address (`m = 0` change label & `.tweak` rejected). -/
def deriveAccountSpAddress {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpAddressHrp) (account : SilentPaymentAccount Affine)
    (coords : SilentPaymentCoordinates) : Except SpError String :=
  match coords with
  | .tweak _ => .error .invalidParameter
  | .code (some 0) => .error .silentPaymentChangeLabel
  | .code labelOpt =>
    match c.pointMul account.scanKey (.affine c.generator) with
    | .infinity => .error .invalidKey
    | .affine bScanPub =>
      let bmRes : Except SpError Affine :=
        match labelOpt with
        | none => .ok account.spendKey
        | some m => labeledSpendKey c account.spendKey account.scanKey m
      match bmRes with
      | .error e => .error e
      | .ok bm => encodeSpAddress c bech hrp { scan := bScanPub, spend := bm }

/-- Derive spent P2TR `scriptPubKey` for a BIP-376 received Silent Payment input (`coords = .tweak`). -/
def deriveAccountTweakScript {Affine : Type} (c : SpCrypto Affine)
    (account : SilentPaymentAccount Affine) (tweakBytes : Bytes32) : Except SpError Bytes34 :=
  match parseScalarStrict tweakBytes with
  | none => .error .invalidKey
  | some t =>
    match c.pointAdd (.affine account.spendKey) (c.pointMul t (.affine c.generator)) with
    | .infinity => .error .invalidKey
    | .affine outPt => .ok (mkP2trScript (c.xCoord outPt))

/-- BIP-392 `ExportSilentPaymentScanKey` policy (`accountIndex < 2^31` + `userApproved = true`). -/
def exportSpScanKey {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpScanHrp) (deriveAccount : UInt32 → Except SpError (SilentPaymentAccount Affine))
    (accountIndex : UInt32) (userApproved : Bool) : Except SpError String :=
  if decide (accountIndex ≥ bip32HardenedBit) then
    .error .invalidParameter
  else
    match deriveAccount accountIndex with
    | .error e => .error e
    | .ok account =>
      if !userApproved then
        .error .userRejected
      else
        encodeSpScanKey c bech hrp account.scanKey account.spendKey

/-! ## 4. Eligible Input Selection, `BIP0352/Inputs` Hash & Sender/Receiver ECDH -/

/-- Classify a raw `scriptPubKey` (plus optional redeemScript for `P2SH-P2WPKH`) into `SpInputScriptKind`. -/
def classifySpInputScript (scriptPubKey : ByteArray) (redeemScriptOpt : Option ByteArray := none) :
    SpInputScriptKind :=
  match InternalSpec.classifyScript? scriptPubKey with
  | some (.p2pkh _) => .pkh
  | some (.p2wpkh _) => .wpkh
  | some (.p2sh _) =>
    match redeemScriptOpt with
    | some rs =>
      match InternalSpec.classifyScript? rs with
      | some (.p2wpkh _) => .shWpkh
      | _ => .other
    | none => .other
  | some (.p2tr xk) =>
    .tr (bytesEq xk bip341NumsXOnly.bytes)
  | _ => .other

/-- Check whether `inp` spends a Taproot prevout. -/
def isInputTaproot (inp : PsbtSpInput) : Bool :=
  match inp.prevoutWitnessVersion, inp.scriptKind with
  | some v, _ => decide (v = 1)
  | _, .tr _ => true
  | _, _ => false

/-- Effective consensus sighash type signed by the device for `inp`. -/
def effectiveInputSighashType (inp : PsbtSpInput) : UInt32 :=
  match inp.sighashType with
  | some sh => sh
  | none => if isInputTaproot inp then sighashDefault else sighashAll

/-- Check whether `inp` is BIP-352 eligible (excluding BIP-341 NUMS internal key `H`). -/
def isInputEligible (inp : PsbtSpInput) : Bool :=
  let kindOk := match inp.scriptKind with
    | .pkh | .wpkh | .shWpkh => true
    | .tr hasNums => !hasNums
    | .other => false
  let hasLiteralNums := match inp.tapInternalKey with
    | some xk => decide (xk = bip341NumsXOnly)
    | none => false
  kindOk && !hasLiteralNums

/-- BIP-352 36-byte outpoint encoding `txid (32B) || le32(vout) (4B)`. -/
def outpointBytes (op : OutPoint) : Bytes36 :=
  appendSized op.txid (encodeU32LE op.vout)

/-- Strict lexicographical `<` on byte lists. -/
def listLexLt : List UInt8 → List UInt8 → Bool
  | _, [] => false
  | [], _ :: _ => true
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else listLexLt as bs

/-- Select the lexicographically smallest 36-byte serialized outpoint across all tx inputs. -/
def smallestOutpointBytes : List OutPoint → Except SpError Bytes36
  | [] => .error .noInputs
  | op :: rest =>
    let init := outpointBytes op
    .ok (rest.foldl (fun best cur =>
      let curB := outpointBytes cur
      if listLexLt curB.bytes.data.toList best.bytes.data.toList then curB else best) init)

/-- Normalize an eligible input private key `d` (`0 < d < n`; negate if Taproot and `d * G` has odd `y`). -/
def normalizeInputPrivKey {Affine : Type} (c : SpCrypto Affine)
    (d : Nat) (isTaproot : Bool) : Except SpError Nat :=
  if !(decide (0 < d) && decide (d < secp256k1Order)) then
    .error .invalidKey
  else if !isTaproot then
    .ok d
  else
    match c.pointMul d (.affine c.generator) with
    | .infinity => .error .invalidKey
    | .affine p =>
      if c.hasEvenY p then .ok d else .ok (secp256k1Order - d)

/-- BIP-352 `input_hash = H_{"BIP0352/Inputs"}(outpoint_L || ser_P(A))` (`0 < input_hash < n`). -/
def computeInputHash {Affine : Type} (c : SpCrypto Affine)
    (outpoints : List OutPoint) (inputKeySum : SpPoint Affine) : Except SpError Nat :=
  match smallestOutpointBytes outpoints with
  | .error e => .error e
  | .ok smallest =>
    match inputKeySum with
    | .infinity => .error .zeroInputSum
    | .affine aAffine =>
      let digest := c.taggedHash "BIP0352/Inputs" (appendBytes smallest.bytes (c.compress aAffine).bytes)
      match parseNonZeroScalar digest with
      | some h => .ok h
      | none => .error .invalidHash

/-- Sender ECDH share `C = a * B_scan`. -/
def ecdhShare {Affine : Type} (c : SpCrypto Affine) (a : Nat) (bScan : Affine) : SpPoint Affine :=
  c.pointMul a (.affine bScan)

/-- Shared secret `S = input_hash * C`. -/
def sharedSecret {Affine : Type} (c : SpCrypto Affine)
    (inputHashScalar : Nat) (share : SpPoint Affine) : Except SpError Affine :=
  match c.pointMul inputHashScalar share with
  | .infinity => .error .invalidKey
  | .affine s => .ok s

/-- Per-output tweak `t_k = H_{"BIP0352/SharedSecret"}(ser_P(S) || be32(k))` (`0 < t_k < n`). -/
def outputTweak {Affine : Type} (c : SpCrypto Affine)
    (secret : Affine) (k : UInt32) : Except SpError Nat :=
  let digest := c.taggedHash "BIP0352/SharedSecret" (appendBytes (c.compress secret).bytes (encodeU32BE k))
  match parseNonZeroScalar digest with
  | some tk => .ok tk
  | none => .error .invalidHash

/-- Output public key `P_k = B_m + t_k * G`. -/
def outputKey {Affine : Type} (c : SpCrypto Affine)
    (secret : Affine) (bSpend : Affine) (k : UInt32) : Except SpError Affine :=
  match outputTweak c secret k with
  | .error e => .error e
  | .ok tk =>
    match c.pointAdd (.affine bSpend) (c.pointMul tk (.affine c.generator)) with
    | .infinity => .error .invalidKey
    | .affine pk => .ok pk

/-- Lookup per-scan-key counter `k`. -/
def lookupCounter {Affine : Type} [DecidableEq Affine]
    (scan : Affine) : List (Affine × Nat) → Nat
  | [] => 0
  | (s, cnt) :: rest => if decide (s = scan) then cnt else lookupCounter scan rest

/-- Increment per-scan-key counter `k`. -/
def incrementCounter {Affine : Type} [DecidableEq Affine]
    (scan : Affine) : List (Affine × Nat) → List (Affine × Nat)
  | [] => [(scan, 1)]
  | (s, cnt) :: rest =>
    if decide (s = scan) then (s, cnt + 1) :: rest else (s, cnt) :: incrementCounter scan rest

/-- Assign per-scan-key output counter `k ∈ 0 .. K_MAX - 1` loop. -/
def assignKLoop {Affine : Type} [DecidableEq Affine] :
    List (SilentPaymentCode Affine) → List (Affine × Nat) → Except SpError (List UInt32)
  | [], _ => .ok []
  | code :: rest, counters =>
    let k := lookupCounter code.scan counters
    if decide (k ≥ spMaxOutputsPerScanKey) then
      .error .tooManyRecipients
    else
      match assignKLoop rest (incrementCounter code.scan counters) with
      | .error e => .error e
      | .ok restKs => .ok (UInt32.ofNat k :: restKs)

/-- Assign per-scan-key output counter `k ∈ 0 .. K_MAX - 1` in PSBT output order. -/
def assignK {Affine : Type} [DecidableEq Affine]
    (recipients : List (SilentPaymentCode Affine)) : Except SpError (List UInt32) :=
  assignKLoop recipients []

/-- Receiver spending private key `d = (b_spend + tweak) mod n` (`!= 0`). -/
def receiverSpendingKey (bSpend tweak : Nat) : Except SpError Nat :=
  let d := (bSpend + tweak) % secp256k1Order
  if decide (d = 0) then .error .invalidKey else .ok d

/-! ## 5. BIP-374 Discrete Logarithm Equality (`dleqProve` & `dleqVerify`) -/

/-- BIP-374 challenge scalar `e`. -/
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
    | .affine r1, .affine r2 => decide (dleqChallenge c aPub b cPt g r1 r2 msg = e)
    | _, _ => false
  | _, _ => false

/-- BIP-374 deterministic nonce `k`. -/
def dleqNonce {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (aPub cPt : Affine) (auxRand : Bytes32) (msg : Option Bytes32) : Nat :=
  let auxHash := c.taggedHash "BIP0374/aux" auxRand.bytes
  let t := xorBytes32 (scalarToBytes32 a) auxHash
  let nonceBase := concatBytes [t.bytes, (c.compress aPub).bytes, (c.compress cPt).bytes]
  let noncePayload := match msg with
    | none => nonceBase
    | some m => appendBytes nonceBase m.bytes
  parseScalarModN (c.taggedHash "BIP0374/nonce" noncePayload)

/-- BIP-374 `DLEQProve(a, B, r, G, m)` with mandatory post-generation `dleqVerify` self-check. -/
def dleqProve {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (b : Affine) (auxRand : Bytes32) (g : Affine) (msg : Option Bytes32) :
    Except SpError Bytes64 :=
  if !(decide (0 < a) && decide (a < secp256k1Order)) then
    .error .invalidProofInput
  else
    match c.pointMul a (.affine g) with
    | .infinity => .error .invalidProofInput
    | .affine aPub =>
      match c.pointMul a (.affine b) with
      | .infinity => .error .invalidProofInput
      | .affine cPt =>
        let k := dleqNonce c a aPub cPt auxRand msg
        if decide (k = 0) then
          .error .invalidProofInput
        else
          match c.pointMul k (.affine g) with
          | .infinity => .error .invalidProofInput
          | .affine r1 =>
            match c.pointMul k (.affine b) with
            | .infinity => .error .invalidProofInput
            | .affine r2 =>
              let e := dleqChallenge c aPub b cPt g r1 r2 msg
              let s := (k + e * a) % secp256k1Order
              let proof : Bytes64 := appendSized (scalarToBytes32 e) (scalarToBytes32 s)
              if !dleqVerify c aPub b cPt proof g msg then
                .error .invalidProofInput
              else
                .ok proof

/-! ## 6. BIP-375 PSBT Silent Payment Validation & Finalization -/

/-- Validate structural BIP-375 output rules (`TX_MODIFIABLE`, orphan `spV0Label`, account/idAuth exclusion). -/
def validatePsbtSpOutputOne (modifiable : Bool) (out : PsbtSpOutput) : Except SpError Unit :=
  let step1 : Except SpError Unit :=
    match out.script, out.spV0Info with
    | none, none => .error .missingOutputScript
    | some _, some _ =>
      if modifiable then .error .invalidSilentPaymentField else .ok ()
    | _, _ => .ok ()
  match step1 with
  | .error e => .error e
  | .ok () =>
    if out.spV0Label.isSome && out.spV0Info.isNone then
      .error .invalidSilentPaymentField
    else if out.spV0Info.isSome && (out.hasAccountCoordinates || out.hasIdAuthProofs) then
      .error .invalidSilentPaymentField
    else
      .ok ()

/-- Validate all PSBT outputs under BIP-375 rules. -/
def validatePsbtSpOutputsLoop (modifiable : Bool) : List PsbtSpOutput → Except SpError Unit
  | [] => .ok ()
  | out :: rest =>
    match validatePsbtSpOutputOne modifiable out with
    | .error e => .error e
    | .ok () => validatePsbtSpOutputsLoop modifiable rest

def validatePsbtSpOutputs (outputs : List PsbtSpOutput) (txModifiable : Option UInt8) :
    Except SpError Unit :=
  let modifiable := decide (((txModifiable.getD 0).toNat &&& 0x03) ≠ 0)
  validatePsbtSpOutputsLoop modifiable outputs

/-- Find the `SilentPaymentAccount` whose scan key `acc.scanKey * G` equals `scanPt`. -/
def findAccountByScanKey {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (scanPt : Affine) : List (SilentPaymentAccount Affine) → Option (SilentPaymentAccount Affine)
  | [] => none
  | acc :: rest =>
    let matchesScan := match c.pointMul acc.scanKey (.affine c.generator) with
      | .affine pub => decide (pub = scanPt)
      | .infinity => false
    if matchesScan then some acc else findAccountByScanKey c scanPt rest

/-- Verify `PSBT_OUT_SP_V0_LABEL` against `labeledSpendKey` when present. -/
def verifyOutputSpLabel {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (accounts : List (SilentPaymentAccount Affine))
    (code : SilentPaymentCode Affine) (labelOpt : Option UInt32) : Except SpError Unit :=
  match labelOpt with
  | none => .ok ()
  | some m =>
    match findAccountByScanKey c code.scan accounts with
    | none => .error .invalidSilentPaymentField
    | some acc =>
      match labeledSpendKey c acc.spendKey acc.scanKey m with
      | .error e => .error e
      | .ok expectedBm =>
        if decide (expectedBm ≠ code.spend) then
          .error .invalidSilentPaymentField
        else
          .ok ()

/-- Collect indexed Silent Payment recipients `(outputIdx, code)` in output order. -/
def collectSpRecipients {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (accounts : List (SilentPaymentAccount Affine)) :
    Nat → List PsbtSpOutput → Except SpError (List (Nat × SilentPaymentCode Affine))
  | _, [] => .ok []
  | idx, out :: rest =>
    match collectSpRecipients c accounts (idx + 1) rest with
    | .error e => .error e
    | .ok tail =>
      match out.spV0Info with
      | none => .ok tail
      | some raw66 =>
        match deserializeSpCode c raw66 with
        | .error e => .error e
        | .ok code =>
          match verifyOutputSpLabel c accounts code out.spV0Label with
          | .error e => .error e
          | .ok () => .ok ((idx, code) :: tail)

/-- Validate one PSBT input under BIP-375 and append its normalized eligible private key if eligible. -/
def analyzeSpInputStep {Affine : Type} (c : SpCrypto Affine)
    (acc : List Nat) (inp : PsbtSpInput) : Except SpError (List Nat) :=
  let witCheck : Except SpError Unit :=
    match inp.prevoutWitnessVersion with
    | some v => if decide (1 < v) then .error .silentPaymentSegwitVersion else .ok ()
    | none => .ok ()
  match witCheck with
  | .error e => .error e
  | .ok () =>
    if decide (effectiveInputSighashType inp ≠ sighashAll) then
      .error .silentPaymentSighashType
    else if inp.hasInputSpEcdhShare || inp.hasInputSpDleq then
      .error .silentPaymentShareMismatch
    else if !isInputEligible inp then
      .ok acc
    else
      match inp.deviceEligiblePrivKey with
      | none => .error .silentPaymentInputNotHeld
      | some rawPriv =>
        let isTr := match inp.scriptKind with | .tr _ => true | _ => false
        match normalizeInputPrivKey c rawPriv isTr with
        | .error e => .error e
        | .ok normPriv => .ok (acc ++ [normPriv])

/-- Check that every scan key in `pairs` belongs to `recipientScanKeys`. -/
def checkScanKeysInRecipients {β : Type} (recipientScanKeys : List Bytes33) :
    List (Bytes33 × β) → Except SpError Unit
  | [] => .ok ()
  | (scanK, _) :: rest =>
    if !spListMem scanK recipientScanKeys then
      .error .silentPaymentShareMismatch
    else
      checkScanKeysInRecipients recipientScanKeys rest

/-- Pre-review BIP-375 `analyzePsbtSilentPayments`. -/
def analyzePsbtSilentPayments {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (psbt : PsbtSpTx Affine) :
    Except SpError (Option (List (Nat × SilentPaymentCode Affine) × List UInt32 × List Nat)) :=
  match validatePsbtSpOutputs psbt.outputs psbt.txModifiable with
  | .error e => .error e
  | .ok () =>
    match collectSpRecipients c psbt.spAccounts 0 psbt.outputs with
    | .error e => .error e
    | .ok indexedCodes =>
      if indexedCodes.isEmpty then
        .ok none
      else
        match assignK (indexedCodes.map Prod.snd) with
        | .error e => .error e
        | .ok ks =>
          match psbt.inputs.foldlM (analyzeSpInputStep c) [] with
          | .error e => .error e
          | .ok eligibleKeys =>
            if eligibleKeys.isEmpty then
              .error .silentPaymentNoEligibleInputs
            else
              let recipientScanKeys : List Bytes33 :=
                indexedCodes.map (fun (_, code) => c.compress code.scan)
              match checkScanKeysInRecipients recipientScanKeys psbt.globalEcdhShares with
              | .error e => .error e
              | .ok () =>
                match checkScanKeysInRecipients recipientScanKeys psbt.globalDleqProofs with
                | .error e => .error e
                | .ok () => .ok (some (indexedCodes, ks, eligibleKeys))

/-- Pure lookup of a pair by its 33-byte scan key (`0 Classical.choice`). -/
def lookupByScanBytes {β : Type} (scanBytes : Bytes33) : List (Bytes33 × β) → Option β
  | [] => none
  | (k, v) :: rest => if decide (k = scanBytes) then some v else lookupByScanBytes scanBytes rest

/-- Pure lookup of a computed share tuple by its `Affine` scan key (`0 Classical.choice`). -/
def lookupShareTuple {Affine : Type} [DecidableEq Affine] (scanPt : Affine) :
    List (Affine × Affine × SilentPaymentShareOut) → Option (Affine × Affine × SilentPaymentShareOut)
  | [] => none
  | entry :: rest =>
    if decide (entry.1 = scanPt) then some entry else lookupShareTuple scanPt rest

/-- Finalize BIP-375 Silent Payment ECDH shares, DLEQ proofs, and P2TR output scripts. -/
def finalizePsbtSilentPayments {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (psbt : PsbtSpTx Affine) (dleqAuxRand : Bytes32) :
    Except SpError (List SilentPaymentShareOut × List SilentPaymentOutputScriptOut) :=
  match analyzePsbtSilentPayments c psbt with
  | .error e => .error e
  | .ok none => .ok ([], [])
  | .ok (some (indexedCodes, ks, eligibleKeys)) =>
    let a := eligibleKeys.foldl (fun acc k => (acc + k) % secp256k1Order) 0
    if decide (a = 0) then
      .error .zeroInputSum
    else
      match c.pointMul a (.affine c.generator) with
      | .infinity => .error .zeroInputSum
      | .affine aPub =>
        match computeInputHash c (psbt.inputs.map (·.outpoint)) (.affine aPub) with
        | .error e => .error e
        | .ok inHash =>
          let distinctScans : List Affine :=
            indexedCodes.foldl (fun acc (_, code) =>
              if spListMem code.scan acc then acc else acc ++ [code.scan]) []
          let shareRes : Except SpError (List (Affine × Affine × SilentPaymentShareOut)) :=
            distinctScans.mapM (fun scanPt =>
              let scanBytes := c.compress scanPt
              match ecdhShare c a scanPt with
              | .infinity => Except.error .invalidKey
              | .affine sharePt =>
                let shareBytes := c.compress sharePt
                let existingShare := lookupByScanBytes scanBytes psbt.globalEcdhShares
                let existingProof := lookupByScanBytes scanBytes psbt.globalDleqProofs
                let proofRes : Except SpError Bytes64 :=
                  match existingShare, existingProof with
                  | none, none => dleqProve c a scanPt dleqAuxRand c.generator none
                  | some exShare, some exProof =>
                    if decide (exShare = shareBytes) && dleqVerify c aPub scanPt sharePt exProof c.generator none then
                      Except.ok exProof
                    else
                      Except.error .silentPaymentShareMismatch
                  | _, _ => Except.error .silentPaymentShareMismatch
                match proofRes with
                | .error e => Except.error e
                | .ok proof =>
                  Except.ok (scanPt, sharePt, { scanKey := scanBytes, share := shareBytes, dleqProof := proof : SilentPaymentShareOut }))
          match shareRes with
          | .error e => Except.error e
          | .ok sharePairs =>
            let outRes : Except SpError (List SilentPaymentOutputScriptOut) :=
              (indexedCodes.zip ks).mapM (fun ((outIdx, code), k) =>
                match lookupShareTuple code.scan sharePairs with
                | none => Except.error .invalidKey
                | some (_, sharePt, _) =>
                  match sharedSecret c inHash (.affine sharePt) with
                  | .error e => Except.error e
                  | .ok secret =>
                    match outputKey c secret code.spend k with
                    | .error e => Except.error e
                    | .ok outPt =>
                      let p2tr := mkP2trScript (c.xCoord outPt)
                      match psbt.outputs[outIdx]? with
                      | none => Except.error .invalidParameter
                      | some psbtOut =>
                        match psbtOut.script with
                        | some existing =>
                          if !bytesEq existing p2tr.bytes then Except.error .silentPaymentOutputScriptMismatch
                          else Except.ok { outputIndex := UInt32.ofNat outIdx, script := p2tr }
                        | none =>
                          Except.ok { outputIndex := UInt32.ofNat outIdx, script := p2tr })
            match outRes with
            | .error e => Except.error e
            | .ok outScripts =>
              Except.ok (sharePairs.map (fun (_, _, resp) => resp), outScripts)

end BitcoinLedger.SilentPayments

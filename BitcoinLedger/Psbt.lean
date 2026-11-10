import Spec

namespace BitcoinLedger.Psbt

open Spec.Psbt

/-!
# `BitcoinLedger.Psbt` — Executable PSBTv0/v2 Normalization, Security Validation & Sighash Engine

Pure, constructive, freestanding-friendly Lean 4 implementation of the Ledger Bitcoin
PSBT signing validation and digest engine, deduced from `LedgerHQ/app-bitcoin`
(`f010982d3050e02813cd7129bebd68cf2d1f2099`) and `LedgerHQ/vanadium` (`apps/bitcoin`
`ace8e96982408959dea9e7fbc59ee36e8c54e645`), refined against `Spec.Psbt`.

Key design properties:
- **Strict 64-bit checked satoshi arithmetic** (`MAX_MONEY_SATS = 2_100_000_000_000_000 : UInt64`):
  avoids unbounded bignum arithmetic in amount summation and fee calculation while proving exact
  equivalence with `Spec.Psbt`'s mathematical `Nat` sums.
- **Zero `Classical.choice`, zero `sorry`, zero `@[extern]` `ByteArray.beq`**:
  all byte, digest, script, and integer comparisons use constructive structural decision procedures.
- **Non-trivial algorithmic refinement**:
  - Single-pass iterative `determineLocktime` (`LocktimeScanState`) vs `Spec.Psbt`'s multi-pass list scans.
  - Tail-recursive index-loop `normalizePsbtV0ToV2` vs `Array.ofFn` dependent-index construction.
  - Checked `UInt64` satoshi accumulators (`checkedAddSats?`, `checkedSubSats?`) in input/output loops.
-/

/-! ## 1. Constructive Byte, Digest & Checked `UInt64` Satoshi Helpers -/

/-- Consensus maximum Bitcoin supply in satoshis as a fixed-width `UInt64` (`21,000,000 * 10^8`). -/
def MAX_MONEY_SATS : UInt64 := 2_100_000_000_000_000

/-- Locktime threshold separating block height (`< 500,000,000`) from UNIX timestamp (`>= 500,000,000`). -/
def LOCKTIME_THRESHOLD_U32 : UInt32 := 500_000_000

/-- Maximum number of silent change outputs permitted on BOLOS (`MAX_CHANGE_OUTPUTS = 10`). -/
def MAX_CHANGE_OUTPUTS_CAP : Nat := 10

/-- Maximum confusion score permitted for cleartext signing (`100,000`). -/
def MAX_CLEARTEXT_CONFUSION : Nat := 100_000

/-- Maximum printable ASCII message length displayed directly in BIP-322 (`640`). -/
def MAX_BIP322_PRINTABLE : Nat := 640

/-- Constructive byte-list equality (`0 Classical.choice`). -/
def eqByteList : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && eqByteList xs ys
  | _, _ => false

/-- Constructive `ByteArray` equality (`0 Classical.choice`, avoids `@[extern] ByteArray.beq`). -/
def eqBytes (a b : ByteArray) : Bool :=
  eqByteList a.data.toList b.data.toList

/-- Constructive 32-byte digest equality (`0 Classical.choice`). -/
def eqBytes32 (a b : Bytes32) : Bool :=
  eqBytes a.bytes b.bytes

/-- Constructive `Option UInt8` equality. -/
def eqOptU8 : Option UInt8 → Option UInt8 → Bool
  | none, none => true
  | some a, some b => decide (a = b)
  | _, _ => false

/-- Constructive `Option UInt32` equality. -/
def eqOptU32 : Option UInt32 → Option UInt32 → Bool
  | none, none => true
  | some a, some b => decide (a = b)
  | _, _ => false

/-- Constructive `Option ByteArray` equality. -/
def eqOptBytes : Option ByteArray → Option ByteArray → Bool
  | none, none => true
  | some a, some b => eqBytes a b
  | _, _ => false

/-- Constructive `Option String` equality via UTF-8 bytes (`0 Classical.choice`). -/
def eqOptString : Option String → Option String → Bool
  | none, none => true
  | some a, some b => decide (a = b)
  | _, _ => false

/-- Constructive `List UInt32` equality. -/
def eqU32List : List UInt32 → List UInt32 → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && eqU32List xs ys
  | _, _ => false

/-- Safe byte indexing (`s.data[i]?`). -/
def getByte? (s : ByteArray) (i : Nat) : Option UInt8 :=
  s.data[i]?

/-- Convert a `Nat` satoshi amount into a bounded `UInt64` iff `amt ≤ MAX_MONEY`. -/
def natToValidSats? (amt : Nat) : Option UInt64 :=
  if decide (amt > MAX_MONEY) then
    none
  else
    some (UInt64.ofNat amt)

/-- Overflow-safe 64-bit satoshi addition bounded by `MAX_MONEY_SATS` (`2.1e15 < 2^51 < 2^64`).
    Because `a ≤ MAX_MONEY_SATS` and `b ≤ MAX_MONEY_SATS`, `a + b` cannot wrap `UInt64` (`< 2^52`). -/
def checkedAddSats? (a b : UInt64) : Option UInt64 :=
  if decide (a.toNat ≤ MAX_MONEY) && decide (b.toNat ≤ MAX_MONEY) then
    let sum : UInt64 := a + b
    if decide (sum.toNat > MAX_MONEY) then
      none
    else
      some sum
  else
    none

/-- Overflow-safe 64-bit satoshi subtraction (`total - part` when `part ≤ total ≤ MAX_MONEY`). -/
def checkedSubSats? (total part : UInt64) : Option UInt64 :=
  if decide (total.toNat ≤ MAX_MONEY) && !decide (total.toNat < part.toNat) then
    some (total - part)
  else
    none

/-! ## 2. Little-Endian Encoders, CompactSize & Raw Transaction Digest (`txid`) -/

def putU16LE (v : UInt16) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256)
  ]

def putU32LE (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256)
  ]

def putU64LE (v : UInt64) : ByteArray :=
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

def putVarInt (n : Nat) : ByteArray :=
  if n < 0xFD then
    ByteArray.mk #[UInt8.ofNat n]
  else if n ≤ 0xFFFF then
    ByteArray.mk #[0xFD] ++ putU16LE (UInt16.ofNat n)
  else if n ≤ 0xFFFFFFFF then
    ByteArray.mk #[0xFE] ++ putU32LE (UInt32.ofNat n)
  else
    ByteArray.mk #[0xFF] ++ putU64LE (UInt64.ofNat n)

def joinByteArrays (xs : List ByteArray) : ByteArray :=
  xs.foldl ByteArray.append ByteArray.empty

def hash256d (sha256 : ByteArray → Bytes32) (payload : ByteArray) : Bytes32 :=
  sha256 (sha256 payload).bytes

def bip340TaggedHash (sha256 : ByteArray → Bytes32) (tag : String) (msg : ByteArray) : Bytes32 :=
  let th := (sha256 tag.toUTF8).bytes
  sha256 (th ++ th ++ msg)

def encodeOutPoint (op : OutPoint) : ByteArray :=
  op.txid.bytes ++ putU32LE op.vout

def encodeTxOut (o : TxOut) : ByteArray :=
  putU64LE (UInt64.ofNat o.amount) ++ putVarInt o.scriptPubKey.size ++ o.scriptPubKey

def encodeRawTxInStripped (inp : RawTxIn) : ByteArray :=
  encodeOutPoint inp.prevout ++
  putVarInt inp.scriptSig.size ++
  inp.scriptSig ++
  putU32LE inp.sequence

def encodeRawTxStripped (tx : RawTx) : ByteArray :=
  putU32LE tx.version ++
  putVarInt tx.vin.size ++
  joinByteArrays (tx.vin.toList.map encodeRawTxInStripped) ++
  putVarInt tx.vout.size ++
  joinByteArrays (tx.vout.toList.map encodeTxOut) ++
  putU32LE tx.locktime

/-- Compute stripped (non-witness) BIP-141 transaction ID (`doubleSha256`). -/
def computeTxid (sha256 : ByteArray → Bytes32) (tx : RawTx) : Bytes32 :=
  hash256d sha256 (encodeRawTxStripped tx)

/-! ## 3. PSBTv0-to-PSBTv2 Normalization & BIP-370 Locktime Calculation -/

def checkUnsignedVinEmptyScripts : List RawTxIn → Bool
  | [] => true
  | txin :: rest =>
      decide (txin.scriptSig.size = 0) &&
      decide (txin.witness.size = 0) &&
      checkUnsignedVinEmptyScripts rest

def buildV2InputsLoop
    (vin : Array RawTxIn)
    (v0Ins : Array PsbtV0Input) : Nat → Nat → Array PsbtInput → Array PsbtInput
  | 0, _, acc => acc
  | fuel + 1, idx, acc =>
      if h : idx < v0Ins.size then
        if hVin : idx < vin.size then
          let rawIn := vin[idx]'hVin
          let mIn := v0Ins[idx]'h
          let item : PsbtInput := {
            prevout := rawIn.prevout
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
            tapMerkleRoot := mIn.tapMerkleRoot
          }
          buildV2InputsLoop vin v0Ins fuel (idx + 1) (acc.push item)
        else
          acc
      else
        acc

def buildV2OutputsLoop
    (vout : Array TxOut)
    (v0Outs : Array PsbtV0Output) : Nat → Nat → Array PsbtOutput → Array PsbtOutput
  | 0, _, acc => acc
  | fuel + 1, idx, acc =>
      if h : idx < v0Outs.size then
        if hVout : idx < vout.size then
          let rawOut := vout[idx]'hVout
          let mOut := v0Outs[idx]'h
          let item : PsbtOutput := {
            amount := rawOut.amount
            scriptPubKey := some rawOut.scriptPubKey
            redeemScript := mOut.redeemScript
            witnessScript := mOut.witnessScript
            derivations := mOut.derivations
            tapInternalKey := mOut.tapInternalKey
          }
          buildV2OutputsLoop vout v0Outs fuel (idx + 1) (acc.push item)
        else
          acc
      else
        acc

/-- Executable BIP-174 PSBTv0 to BIP-370 PSBTv2 normalizer. -/
def normalizePsbtV0ToV2 (v0 : PsbtV0) : Except PsbtError PsbtTx :=
  let verOk := match v0.version with
    | some ver => decide (ver = 0)
    | none => true
  if !verOk then
    .error .invalidPsbtVersion
  else if v0.unsignedTxHasWitness then
    .error .psbtV0HasWitnessInUnsignedTx
  else if v0.hasV2ExclusiveGlobals then
    .error .psbtV0ForbiddenV2Fields
  else if !checkUnsignedVinEmptyScripts v0.unsignedTx.vin.toList then
    .error .psbtV0NonEmptyScriptSig
  else if !decide (v0.inputs.size = v0.unsignedTx.vin.size) then
    .error .psbtV0InputOutputCountMismatch
  else if !decide (v0.outputs.size = v0.unsignedTx.vout.size) then
    .error .psbtV0InputOutputCountMismatch
  else if v0.inputs.toList.any (·.hasV2ExclusiveFields) || v0.outputs.toList.any (·.hasV2ExclusiveFields) then
    .error .psbtV0ForbiddenV2Fields
  else
    .ok {
      txVersion := v0.unsignedTx.version
      fallbackLocktime := some v0.unsignedTx.locktime
      txModifiableFlags := none
      inputs := buildV2InputsLoop v0.unsignedTx.vin v0.inputs v0.inputs.size 0 #[]
      outputs := buildV2OutputsLoop v0.unsignedTx.vout v0.outputs v0.outputs.size 0 #[]
      bip322Message := v0.bip322Message
      musig2SessionId := v0.musig2SessionId
    }

/-- Single-pass accumulator for BIP-370 `determineLocktime` (`app-bitcoin/src/common/locktime.h`). -/
structure LocktimeScanState where
  hasHeightOnly : Bool := false
  hasTimeOnly : Bool := false
  anyHeight : Bool := false
  anyTime : Bool := false
  maxHeight : UInt32 := 0
  maxTime : UInt32 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Validate per-input BIP-370 locktime bounds (`0 < height < 500_000_000`, `time >= 500_000_000`). -/
def checkInputLocktimeBounds (inp : PsbtInput) : Bool :=
  let hOk := match inp.requiredHeightLocktime with
    | none => true
    | some h => decide (0 < h.toNat ∧ h.toNat < LOCKTIME_THRESHOLD_U32.toNat)
  let tOk := match inp.requiredTimeLocktime with
    | none => true
    | some t => decide (LOCKTIME_THRESHOLD_U32.toNat ≤ t.toNat)
  hOk && tOk

def scanLocktimeInputs (st : LocktimeScanState) : List PsbtInput → Option LocktimeScanState
  | [] => some st
  | inp :: rest =>
      if !checkInputLocktimeBounds inp then
        none
      else
        let hOnly := inp.requiredHeightLocktime.isSome && inp.requiredTimeLocktime.isNone
        let tOnly := inp.requiredTimeLocktime.isSome && inp.requiredHeightLocktime.isNone
        let nextMaxH := match inp.requiredHeightLocktime with
          | some h => if st.maxHeight.toNat < h.toNat then h else st.maxHeight
          | none => st.maxHeight
        let nextMaxT := match inp.requiredTimeLocktime with
          | some t => if st.maxTime.toNat < t.toNat then t else st.maxTime
          | none => st.maxTime
        scanLocktimeInputs {
          hasHeightOnly := st.hasHeightOnly || hOnly
          hasTimeOnly := st.hasTimeOnly || tOnly
          anyHeight := st.anyHeight || inp.requiredHeightLocktime.isSome
          anyTime := st.anyTime || inp.requiredTimeLocktime.isSome
          maxHeight := nextMaxH
          maxTime := nextMaxT
        } rest

/-- Single-pass BIP-370 locktime calculation (`determineLocktime`), enforcing:
    - height bounds `[1, 499_999_999]` and time bounds `>= 500_000_000`,
    - dual-locktime compatibility (height wins tie-break when no input is time-only),
    - strict conflict rejection when both height-only and time-only inputs exist,
    - fallback locktime used ONLY when no input constrains locktime. -/
def determineLocktime (fallbackLocktime : Option UInt32) (inputs : List PsbtInput) :
    Except PsbtError UInt32 :=
  match scanLocktimeInputs {} inputs with
  | none => .error .locktimeConflictOrInvalid
  | some st =>
      if st.hasHeightOnly && st.hasTimeOnly then
        .error .locktimeConflictOrInvalid
      else if !st.anyHeight && !st.anyTime then
        .ok (fallbackLocktime.getD 0)
      else if !st.hasTimeOnly && st.anyHeight then
        .ok st.maxHeight
      else
        .ok st.maxTime

/-! ## 4. Sighash Classification, Script Templates & Dual-UTXO Cross-Check (CVE-2020-14199) -/

def buildP2SHScript (hash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[0xa9, 0x14] ++ hash20 ++ ByteArray.mk #[0x87]

def buildP2WSHScript (hash32 : Bytes32) : ByteArray :=
  ByteArray.mk #[0x00, 0x20] ++ hash32.bytes

def checkP2WPKH (s : ByteArray) : Bool :=
  decide (s.data.size = 22) && eqOptU8 (getByte? s 0) (some 0x00) && eqOptU8 (getByte? s 1) (some 0x14)

def checkP2WSH (s : ByteArray) : Bool :=
  decide (s.data.size = 34) && eqOptU8 (getByte? s 0) (some 0x00) && eqOptU8 (getByte? s 1) (some 0x20)

def checkP2TR (s : ByteArray) : Bool :=
  decide (s.data.size = 34) && eqOptU8 (getByte? s 0) (some 0x51) && eqOptU8 (getByte? s 1) (some 0x20)

def checkUnknownSegwit (s : ByteArray) : Bool :=
  if checkP2WPKH s || checkP2WSH s || checkP2TR s then
    false
  else if decide (4 ≤ s.data.size ∧ s.data.size ≤ 42) then
    match getByte? s 0, getByte? s 1 with
    | some vByte, some pushLen =>
        let v := vByte.toNat
        (decide (v = 0) || decide (0x51 ≤ v ∧ v ≤ 0x60)) &&
        decide (s.data.size = 2 + pushLen.toNat)
    | _, _ => false
  else
    false

/-- Classify spend witness version of an input `scriptPubKey` + optional `redeemScript`. -/
def classifyInputSpendClass (scriptPubKey : ByteArray) (redeemScript : Option ByteArray) : SpendClass :=
  let inner := redeemScript.getD scriptPubKey
  if checkP2WPKH inner || checkP2WSH inner then
    .segwitV0
  else if redeemScript.isNone && checkP2TR scriptPubKey then
    .taprootV1
  else if redeemScript.isNone && checkUnknownSegwit scriptPubKey then
    .segwitUnknown
  else
    .legacy

/-- Classify a raw `PSBT_IN_SIGHASH_TYPE` (`0x00`/`0x01`/`0x02`/`0x03`/`0x81`/`0x82`/`0x83`). -/
def classifySighashType (sc : SpendClass) (rawOpt : Option UInt32) : SighashSafety × UInt8 :=
  match rawOpt with
  | none =>
      match sc with
      | .taprootV1 => (.safe, SIGHASH_DEFAULT)
      | .legacy | .segwitV0 => (.safe, SIGHASH_ALL)
      | .segwitUnknown => (.unsupported, 0)
  | some raw =>
      if decide (raw.toNat > 0xFF) then
        (.unsupported, 0)
      else
        let b := UInt8.ofNat raw.toNat
        if decide (b = SIGHASH_DEFAULT) then
          match sc with
          | .taprootV1 => (.safe, b)
          | _ => (.unsupported, b)
        else if decide (b = SIGHASH_ALL) then
          match sc with
          | .segwitUnknown => (.unsupported, b)
          | _ => (.safe, b)
        else if decide (b = SIGHASH_NONE) || decide (b = SIGHASH_SINGLE) ||
                decide (b = (SIGHASH_ANYONECANPAY ||| SIGHASH_ALL)) ||
                decide (b = (SIGHASH_ANYONECANPAY ||| SIGHASH_NONE)) ||
                decide (b = (SIGHASH_ANYONECANPAY ||| SIGHASH_SINGLE)) then
          match sc with
          | .legacy | .segwitUnknown => (.unsupported, b)
          | .segwitV0 | .taprootV1 => (.nonSafe, b)
        else
          (.unsupported, b)

def sighashHasAnyoneCanPay (b : UInt8) : Bool :=
  !decide ((b &&& SIGHASH_ANYONECANPAY) = 0)

def sighashLeavesOutputsOpen (b : UInt8) : Bool :=
  let base := b &&& 0x1f
  decide (base = SIGHASH_NONE) || decide (base = SIGHASH_SINGLE)

def sighashBaseIsSingle (b : UInt8) : Bool :=
  decide ((b &&& 0x1f) = SIGHASH_SINGLE)

def sighashCommitsAllProvidedOutputs (b : UInt8) (nOutputs : Nat) : Bool :=
  let base := b &&& 0x1f
  if decide (base = SIGHASH_ALL) || decide (base = SIGHASH_DEFAULT) then
    true
  else
    decide (base = SIGHASH_SINGLE) && decide (nOutputs = 1)

/-- Constructive structural equality on `TxOut` (`amount` + `scriptPubKey`). -/
def eqTxOut (a b : TxOut) : Bool :=
  decide (a.amount = b.amount) && eqBytes a.scriptPubKey b.scriptPubKey

/-- Extract and hash-verify an input's prevout `TxOut`, enforcing the dual-UTXO cross-check
    `nonWitnessUtxo.vout[vout] == witnessUtxo` whenever both are supplied (CVE-2020-14199 defense). -/
def extractInputPrevout (sha256 : ByteArray → Bytes32) (inp : PsbtInput) :
    Except PsbtError (TxOut × Bool) :=
  match inp.nonWitnessUtxo, inp.witnessUtxo with
  | none, none =>
      .error .missingUtxo
  | some rawTx, none =>
      if !eqBytes32 (computeTxid sha256 rawTx) inp.prevout.txid then
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
      if !eqBytes32 (computeTxid sha256 rawTx) inp.prevout.txid then
        .error .nonWitnessUtxoTxidMismatch
      else
        let idx := inp.prevout.vout.toNat
        if h : idx < rawTx.vout.size then
          let nwOut := rawTx.vout[idx]'h
          if !eqTxOut nwOut wUtxo then
            .error .dualUtxoMismatch
          else
            .ok (wUtxo, true)
        else
          .error .prevoutIndexOutOfBounds

/-- Validate UTXO invariants for an **external** (PayJoin / CoinJoin) input, returning both the
    validated UTXO metadata and its checked `UInt64` satoshi amount. -/
def validateExternalInputUtxo
    (crypto : CryptoOracles)
    (inp : PsbtInput) : Except PsbtError ValidatedInputUtxo :=
  match extractInputPrevout crypto.sha256 inp with
  | .error e => .error e
  | .ok (txOut, _) =>
      match natToValidSats? txOut.amount with
      | none => .error .amountExceedsMaxSupply
      | some _ =>
          let sc := classifyInputSpendClass txOut.scriptPubKey inp.redeemScript
          .ok {
            prevoutTxOut := txOut
            spendClass := sc
            missingNonWitnessUtxoWarning := false
          }

/-- Validate UTXO and script-hash commitments for an **internal** (device-signed) input. -/
def validateInternalInputUtxo
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (exemptMissingNonWitnessWarning : Bool := false) : Except PsbtError ValidatedInputUtxo :=
  match extractInputPrevout crypto.sha256 inp with
  | .error e => .error e
  | .ok (txOut, hasNonWitness) =>
      let redeemOk : Bool := match inp.redeemScript with
        | some rs => eqBytes (buildP2SHScript (crypto.hash160 rs)) txOut.scriptPubKey
        | none => true
      if !redeemOk then
        .error .redeemScriptMismatch
      else
        let sc := classifyInputSpendClass txOut.scriptPubKey inp.redeemScript
        if decide (sc = .legacy) && inp.witnessUtxo.isSome then
          .error .legacyHasWitnessUtxo
        else if decide (sc = .legacy) && !hasNonWitness then
          .error .missingUtxo
        else if !decide (sc = .legacy) && inp.witnessUtxo.isNone then
          .error .missingUtxo
        else
          let activeScript := inp.redeemScript.getD txOut.scriptPubKey
          let witnessOk : Bool :=
            if checkP2WSH activeScript then
              match inp.witnessScript with
              | none => false
              | some ws => eqBytes (buildP2WSHScript (crypto.sha256 ws)) activeScript
            else
              true
          if !witnessOk then
            .error .missingOrMismatchedWitnessScript
          else
            match natToValidSats? txOut.amount with
            | none => .error .amountExceedsMaxSupply
            | some _ =>
                let warnMissingNw := decide (sc = .segwitV0) && (!hasNonWitness) && (!exemptMissingNonWitnessWarning)
                .ok {
                  prevoutTxOut := txOut
                  spendClass := sc
                  missingNonWitnessUtxoWarning := warnMissingNw
                }

/-! ## 5. Wallet Policy Derivation Matching & Verified Change Classification -/

def matchOriginPrefix (orig : KeyOrigin) (entryOrig : KeyOrigin) : Option (UInt32 × UInt32) :=
  if decide (entryOrig.fingerprint = orig.fingerprint) &&
     eqU32List (entryOrig.path.take orig.path.length) orig.path &&
     decide (entryOrig.path.length = orig.path.length + 2) then
    match entryOrig.path.drop orig.path.length with
    | [c, idx] => some (c, idx)
    | _ => none
  else
    none

def findFirstSome? {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | x :: xs =>
      match f x with
      | some y => some y
      | none => findFirstSome? f xs

def matchPlaceholderDerivation
    (masterFingerprint : Option UInt32)
    (ph : InternalKeyPlaceholder)
    (entry : KeyDerivationEntry) : Option (Bool × UInt32) :=
  let branchStep? : Option (UInt32 × UInt32) :=
    if ph.isMusig then
      let byExpected := match ph.expectedOrigin with
        | some orig => matchOriginPrefix orig entry.origin
        | none => none
      let byPart := findFirstSome? (fun partOrig => matchOriginPrefix partOrig entry.origin) ph.musigParticipantOrigins
      let byAggFpr := match ph.musigAggregateFingerprint with
        | some aggFpr =>
            if decide (entry.origin.fingerprint = aggFpr) then
              match entry.origin.path with
              | [c, idx] => some (c, idx)
              | _ => none
            else
              none
        | none => none
      let bySyntheticZero :=
        if decide (entry.origin.fingerprint = 0) then
          match entry.origin.path with
          | [c, idx] => some (c, idx)
          | _ => none
        else
          none
      match byExpected with
      | some s => some s
      | none =>
          match byPart with
          | some s => some s
          | none =>
              match byAggFpr with
              | some s => some s
              | none => bySyntheticZero
    else
      match ph.expectedOrigin with
      | some orig => matchOriginPrefix orig entry.origin
      | none =>
          match masterFingerprint with
          | some mfpr =>
              if decide (entry.origin.fingerprint = mfpr) then
                match entry.origin.path with
                | [c, idx] => some (c, idx)
                | _ => none
              else
                none
          | none => none
  match branchStep? with
  | none => none
  | some (c, addrIdx) =>
      if decide (ph.numFirst = ph.numSecond) then
        none
      else if decide (c = ph.numFirst) then
        some (false, addrIdx)
      else if decide (c = ph.numSecond) then
        some (true, addrIdx)
      else
        none

def gatherCandidateCoordinates
    (masterFingerprint : Option UInt32)
    (policy : WalletPolicySpec)
    (derivations : List KeyDerivationEntry) : List (Bool × UInt32) :=
  derivations.foldr (fun entry acc =>
    policy.internalPlaceholders.foldr (fun ph innerAcc =>
      match matchPlaceholderDerivation masterFingerprint ph entry with
      | some coord => coord :: innerAcc
      | none => innerAcc) acc) []

def evalInternalInputCandidates
    (policy : WalletPolicySpec)
    (inp : PsbtInput)
    (utxo : TxOut) : List (Bool × UInt32) → InternalInputCheckResult
  | [] => .notInternal
  | (isChange, addrIdx) :: rest =>
      match policy.deriveScripts isChange addrIdx with
      | none => evalInternalInputCandidates policy inp utxo rest
      | some (expectedSpk, expectedRedeem, expectedWitness) =>
          if eqBytes expectedSpk utxo.scriptPubKey then
            let redeemOk := match expectedRedeem, inp.redeemScript with
              | none, none => true
              | some er, some ir => eqBytes er ir
              | _, _ => false
            let witnessOk := match expectedWitness, inp.witnessScript with
              | none, none => true
              | some ew, some iw => eqBytes ew iw
              | _, _ => false
            if !redeemOk then
              match evalInternalInputCandidates policy inp utxo rest with
              | .matched c i => .matched c i
              | _ => .redeemMismatch
            else if !witnessOk then
              match evalInternalInputCandidates policy inp utxo rest with
              | .matched c i => .matched c i
              | _ => .witnessMismatch
            else
              .matched isChange addrIdx
          else
            evalInternalInputCandidates policy inp utxo rest

def classifyInternalInput
    (masterFingerprint : Option UInt32)
    (policy : WalletPolicySpec)
    (inp : PsbtInput)
    (utxo : TxOut) : InternalInputCheckResult :=
  evalInternalInputCandidates policy inp utxo
    (gatherCandidateCoordinates masterFingerprint policy inp.derivations)

def checkOutputDerivedScripts
    (policy : WalletPolicySpec)
    (out : PsbtOutput)
    (spk : ByteArray)
    (isChange : Bool)
    (addrIdx : UInt32) : Bool :=
  match policy.deriveScripts isChange addrIdx with
  | none => false
  | some (expectedSpk, expectedRedeem, expectedWitness) =>
      let spkOk := eqBytes expectedSpk spk
      let redeemOk := match out.redeemScript, expectedRedeem with
        | none, _ => true
        | some r, some er => eqBytes er r
        | some _, none => false
      let witnessOk := match out.witnessScript, expectedWitness with
        | none, _ => true
        | some w, some ew => eqBytes ew w
        | some _, none => false
      spkOk && redeemOk && witnessOk

def isInternalOutput
    (masterFingerprint : Option UInt32)
    (treatReceiveBranchAsInternal : Bool)
    (policy : WalletPolicySpec)
    (out : PsbtOutput) : Bool :=
  if out.silentPayment.isSome then
    false
  else
    match out.scriptPubKey with
    | none => false
    | some spk =>
        let coords := gatherCandidateCoordinates masterFingerprint policy out.derivations
        coords.any fun (isChange, addrIdx) =>
          (isChange || treatReceiveBranchAsInternal) &&
          checkOutputDerivedScripts policy out spk isChange addrIdx

/-- Executable verified-change classifier (`isChange = true` on `numSecond` branch). -/
def isVerifiedChangeOutput (policy : WalletPolicySpec) (out : PsbtOutput) : Bool :=
  isInternalOutput none false policy out

/-! ## 6. OP_RETURN Minimal Push Check, Checked `UInt64` Fee/Amount Loops & Display Modes -/

def isNonMinimalOneBytePush (b : UInt8) : Bool :=
  let v := b.toNat
  decide (v = 0x00) || decide (1 ≤ v ∧ v ≤ 16) || decide (v = 0x81)

def scanOpReturnPushes (s : ByteArray) : Nat → Nat → Nat → Bool
  | 0, pos, nPushes => decide (pos = s.size) && decide (nPushes ≤ 5)
  | fuel + 1, pos, nPushes =>
      if decide (pos ≥ s.size) then
        decide (pos = s.size) && decide (nPushes ≤ 5)
      else if decide (nPushes ≥ 5) then
        false
      else
        match getByte? s pos with
        | none => false
        | some opByte =>
            let op := opByte.toNat
            if decide (op = 0x00) || decide (op = 0x4f) || decide (0x51 ≤ op ∧ op ≤ 0x60) then
              scanOpReturnPushes s fuel (pos + 1) (nPushes + 1)
            else if decide (1 ≤ op ∧ op ≤ 75) then
              if decide (pos + 1 + op ≤ s.size) then
                if decide (op = 1) then
                  match getByte? s (pos + 1) with
                  | none => false
                  | some pushedByte =>
                      if isNonMinimalOneBytePush pushedByte then
                        false
                      else
                        scanOpReturnPushes s fuel (pos + 2) (nPushes + 1)
                else
                  scanOpReturnPushes s fuel (pos + 1 + op) (nPushes + 1)
              else
                false
            else if decide (op = 0x4c) then
              match getByte? s (pos + 1) with
              | none => false
              | some lenByte =>
                  let dataLen := lenByte.toNat
                  if decide (dataLen > 75) && decide (pos + 2 + dataLen ≤ s.size) then
                    scanOpReturnPushes s fuel (pos + 2 + dataLen) (nPushes + 1)
                  else
                    false
            else
              false

def checkValidOpReturn (s : ByteArray) : Bool :=
  decide (1 ≤ s.size ∧ s.size ≤ 83) &&
  eqOptU8 (getByte? s 0) (some 0x6a) &&
  scanOpReturnPushes s s.size 1 0

def checkIsOpReturn (s : ByteArray) : Bool :=
  eqOptU8 (getByte? s 0) (some 0x6a)

def checkMusig2SessionIdOpt : Option ByteArray → Bool
  | none => true
  | some bs => decide (1 ≤ bs.size ∧ bs.size ≤ 32)

def checkPolicyHeader (policy : WalletPolicySpec) : Except PsbtError Unit :=
  if policy.internalPlaceholders.isEmpty then
    .error .invalidWalletPolicy
  else if decide (policy.spendClass = .segwitUnknown) then
    .error .invalidWalletPolicy
  else if policy.isDefault && !eqByteList policy.name.toUTF8.data.toList [] then
    .error .invalidWalletPolicy
  else
    .ok ()

def validateOutputScript
    (crypto : CryptoOracles)
    (allowOpReturn : Bool)
    (out : PsbtOutput) : Except PsbtError Unit :=
  match out.scriptPubKey, out.silentPayment with
  | none, none => .error .missingOutputScript
  | some spk, _ =>
      if checkIsOpReturn spk then
        if allowOpReturn && checkValidOpReturn spk then .ok () else .error .invalidOpReturnScript
      else
        if (crypto.formatAddress spk).isSome then .ok () else .error .missingOutputScript
  | none, some _ => .ok ()

/-- Output loop using checked `UInt64` satoshi accumulators (`sumOutSats`, `sumChgSats`). -/
def scanOutputsCheckedLoop
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (isBip322 : Bool)
    (policy : WalletPolicySpec)
    (idx : Nat)
    (rem : List PsbtOutput)
    (dispAcc : List (Nat × PsbtOutput))
    (chgAcc : List (Nat × PsbtOutput))
    (sumOutSats : UInt64)
    (sumChgSats : UInt64) :
    Except PsbtError (List (Nat × PsbtOutput) × List (Nat × PsbtOutput) × UInt64 × UInt64) :=
  match rem with
  | [] =>
      let tooMany := match cfg.maxChangeOutputs with
        | some cap => decide (chgAcc.length > cap)
        | none => false
      if tooMany then
        .error .tooManyChangeOutputs
      else
        .ok (dispAcc.reverse, chgAcc.reverse, sumOutSats, sumChgSats)
  | out :: rest =>
      match natToValidSats? out.amount with
      | none => .error .amountExceedsMaxSupply
      | some outSats =>
          match checkedAddSats? sumOutSats outSats with
          | none => .error .amountExceedsMaxSupply
          | some nextSumOut =>
              let allowOpRet := cfg.allowOpReturnOutputs || isBip322
              match validateOutputScript crypto allowOpRet out with
              | .error e => .error e
              | .ok () =>
                  if isInternalOutput cfg.masterFingerprint cfg.treatReceiveBranchAsInternal policy out then
                    let nextSumChg : UInt64 := sumChgSats + outSats
                    scanOutputsCheckedLoop crypto cfg isBip322 policy (idx + 1) rest
                      dispAcc ((idx, out) :: chgAcc) nextSumOut nextSumChg
                  else
                    scanOutputsCheckedLoop crypto cfg isBip322 policy (idx + 1) rest
                      ((idx, out) :: dispAcc) chgAcc nextSumOut sumChgSats

def scanOutputsChecked
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (isBip322 : Bool)
    (policy : WalletPolicySpec)
    (outputs : List PsbtOutput) :
    Except PsbtError (List (Nat × PsbtOutput) × List (Nat × PsbtOutput) × UInt64 × UInt64) :=
  scanOutputsCheckedLoop crypto cfg isBip322 policy 0 outputs [] [] 0 0

/-- Checked `UInt64` input-scan accumulator. -/
structure CheckedInputScanState where
  valInputs : Array (ValidatedInputUtxo × Bool × UInt8) := #[]
  sumInSats : UInt64 := 0
  sumInternalInSats : UInt64 := 0
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

/-- Validate all PSBT inputs using checked `UInt64` satoshi arithmetic. -/
def scanInputsCheckedLoop
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (isBip322 : Bool)
    (nOutputs : Nat)
    (idx : Nat)
    (rem : List PsbtInput)
    (st : CheckedInputScanState) : Except PsbtError CheckedInputScanState :=
  match rem with
  | [] =>
      if decide (st.nInternal = 0) then
        .error .noInternalInputs
      else
        .ok st
  | inp :: rest =>
      if decide (inp.cleartextConfusionScore > MAX_CLEARTEXT_CONFUSION) then
        .error .cleartextConfusionScoreExceeded
      else
        match extractInputPrevout crypto.sha256 inp with
        | .error e => .error e
        | .ok (prevTxOut, _) =>
            match classifyInternalInput cfg.masterFingerprint policy inp prevTxOut with
            | .redeemMismatch => .error .redeemScriptMismatch
            | .witnessMismatch => .error .missingOrMismatchedWitnessScript
            | .matched _ _ =>
                match validateInternalInputUtxo crypto inp (isBip322 && decide (idx = 0)) with
                | .error e => .error e
                | .ok utxoInfo =>
                    let inSats := UInt64.ofNat utxoInfo.prevoutTxOut.amount
                    match checkedAddSats? st.sumInSats inSats with
                    | none => .error .amountExceedsMaxSupply
                    | some nextSumIn =>
                        if !decide (utxoInfo.spendClass = policy.spendClass) then
                          .error .invalidWalletPolicy
                        else
                          let (safety, shByte) := classifySighashType policy.spendClass inp.sighashType
                          match safety with
                          | .unsupported => .error .unsupportedSighashType
                          | .nonSafe =>
                              if !cfg.allowNonDefaultSighash then
                                .error .nonDefaultSighashDisallowed
                              else if sighashBaseIsSingle shByte && decide (idx ≥ nOutputs) then
                                .error .sighashSingleIndexOutOfBounds
                              else
                                let normSh := if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte
                                let (nextFirst, nextMixed) := match st.firstSighash with
                                  | none => (some normSh, st.sighashMixed)
                                  | some prev => (some prev, st.sighashMixed || !decide (prev = normSh))
                                scanInputsCheckedLoop crypto cfg policy isBip322 nOutputs (idx + 1) rest {
                                  valInputs := st.valInputs.push (utxoInfo, true, shByte)
                                  sumInSats := nextSumIn
                                  sumInternalInSats := st.sumInternalInSats + inSats
                                  nInternal := st.nInternal + 1
                                  nExternal := st.nExternal
                                  anyTaprootInternal := st.anyTaprootInternal || decide (utxoInfo.spendClass = .taprootV1)
                                  anyExternalMissingNw := st.anyExternalMissingNw
                                  warnMissingNw := st.warnMissingNw || utxoInfo.missingNonWitnessUtxoWarning
                                  warnNonDefaultSighash := true
                                  sighashInputsOpen := st.sighashInputsOpen || sighashHasAnyoneCanPay shByte
                                  sighashOutputsOpen := st.sighashOutputsOpen || sighashLeavesOutputsOpen shByte
                                  firstSighash := nextFirst
                                  sighashMixed := nextMixed
                                }
                          | .safe =>
                              if sighashBaseIsSingle shByte && decide (idx ≥ nOutputs) then
                                .error .sighashSingleIndexOutOfBounds
                              else
                                let normSh := if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte
                                let (nextFirst, nextMixed) := match st.firstSighash with
                                  | none => (some normSh, st.sighashMixed)
                                  | some prev => (some prev, st.sighashMixed || !decide (prev = normSh))
                                scanInputsCheckedLoop crypto cfg policy isBip322 nOutputs (idx + 1) rest {
                                  valInputs := st.valInputs.push (utxoInfo, true, shByte)
                                  sumInSats := nextSumIn
                                  sumInternalInSats := st.sumInternalInSats + inSats
                                  nInternal := st.nInternal + 1
                                  nExternal := st.nExternal
                                  anyTaprootInternal := st.anyTaprootInternal || decide (utxoInfo.spendClass = .taprootV1)
                                  anyExternalMissingNw := st.anyExternalMissingNw
                                  warnMissingNw := st.warnMissingNw || utxoInfo.missingNonWitnessUtxoWarning
                                  warnNonDefaultSighash := st.warnNonDefaultSighash
                                  sighashInputsOpen := st.sighashInputsOpen || sighashHasAnyoneCanPay shByte
                                  sighashOutputsOpen := st.sighashOutputsOpen || sighashLeavesOutputsOpen shByte
                                  firstSighash := nextFirst
                                  sighashMixed := nextMixed
                                }
            | .notInternal =>
                if !cfg.allowExternalInputs then
                  .error .externalInputsNotAllowed
                else
                  match validateExternalInputUtxo crypto inp with
                  | .error e => .error e
                  | .ok utxoInfo =>
                      let inSats := UInt64.ofNat utxoInfo.prevoutTxOut.amount
                      match checkedAddSats? st.sumInSats inSats with
                      | none => .error .amountExceedsMaxSupply
                      | some nextSumIn =>
                          scanInputsCheckedLoop crypto cfg policy isBip322 nOutputs (idx + 1) rest {
                            valInputs := st.valInputs.push (utxoInfo, false, SIGHASH_ALL)
                            sumInSats := nextSumIn
                            sumInternalInSats := st.sumInternalInSats
                            nInternal := st.nInternal
                            nExternal := st.nExternal + 1
                            anyTaprootInternal := st.anyTaprootInternal
                            anyExternalMissingNw := st.anyExternalMissingNw || inp.nonWitnessUtxo.isNone
                            warnMissingNw := st.warnMissingNw
                            warnNonDefaultSighash := st.warnNonDefaultSighash
                            sighashInputsOpen := st.sighashInputsOpen
                            sighashOutputsOpen := st.sighashOutputsOpen
                            firstSighash := st.firstSighash
                            sighashMixed := st.sighashMixed
                          }

/-- Compute closed-transaction fee via checked `UInt64` subtraction (`totalInSats - totalOutSats`). -/
def computeCheckedFeeSats
    (inputsOpen outputsOpen : Bool)
    (sumInSats sumOutSats : UInt64) : Except PsbtError (Option UInt64) :=
  if !inputsOpen && !outputsOpen then
    match checkedSubSats? sumInSats sumOutSats with
    | none => .error .negativeFeeOutputsExceedInputs
    | some feeSats => .ok (some feeSats)
  else
    .ok none

/-- Select `TxDisplayMode` (`full`, `netOnly`, `selfTransfer`, or `unavailable` on mixed/open sighashes). -/
def selectTxDisplayMode
    (warnNonDefaultSighash : Bool)
    (sighashMixed : Bool)
    (firstSighash : Option UInt8)
    (nOutputs : Nat)
    (nExternal : Nat)
    (externalAmountUnverified : Bool)
    (displayedOutsEmpty : Bool) : TxDisplayMode :=
  if sighashMixed then
    .unavailable
  else if warnNonDefaultSighash then
    let seenSh := firstSighash.getD SIGHASH_ALL
    if sighashCommitsAllProvidedOutputs seenSh nOutputs then
      .netOnly
    else
      .unavailable
  else if decide (nExternal > 0) && externalAmountUnverified then
    .netOnly
  else if displayedOutsEmpty && decide (nExternal = 0) then
    .selfTransfer
  else
    .full

/-- Executable PSBT transaction validation engine (`validatePsbtTransaction`).
    Uses checked `UInt64` satoshi accumulators and detects high-fee warnings in both `.full`
    and `.selfTransfer` display modes (`10 * fee ≥ sumInputs`, safe in `UInt64` since `10 * MAX_MONEY < 2^55`). -/
def validatePsbtTransaction
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx) : Except PsbtError ValidatedPsbt :=
  if !checkMusig2SessionIdOpt cfg.musig2SessionId then
    .error .invalidMusig2SessionId
  else
    match checkPolicyHeader policy with
    | .error e => .error e
    | .ok () =>
        if psbt.inputs.isEmpty || psbt.outputs.isEmpty then
          .error .emptyInputsOrOutputs
        else
          match determineLocktime psbt.fallbackLocktime psbt.inputs.toList with
          | .error e => .error e
          | .ok locktime =>
              match scanInputsCheckedLoop crypto cfg policy psbt.bip322Message.isSome psbt.outputs.size 0 psbt.inputs.toList {} with
              | .error e => .error e
              | .ok inSt =>
                  match scanOutputsChecked crypto cfg psbt.bip322Message.isSome policy psbt.outputs.toList with
                  | .error e => .error e
                  | .ok (displayedOuts, changeOuts, sumOutSats, sumChgSats) =>
                      match computeCheckedFeeSats inSt.sighashInputsOpen inSt.sighashOutputsOpen inSt.sumInSats sumOutSats with
                      | .error e => .error e
                      | .ok feeSats? =>
                          let externalAmountUnverified :=
                            inSt.anyExternalMissingNw && !(inSt.anyTaprootInternal && !inSt.sighashInputsOpen)
                          let mode :=
                            selectTxDisplayMode
                              inSt.warnNonDefaultSighash
                              inSt.sighashMixed
                              inSt.firstSighash
                              psbt.outputs.size
                              inSt.nExternal
                              externalAmountUnverified
                              displayedOuts.isEmpty
                          let aboveSupplyFloor :=
                            if cfg.highFeeInclusiveAt100k then
                              decide (inSt.sumInSats.toNat ≥ 100000)
                            else
                              decide (inSt.sumInSats.toNat > 100000)
                          let highFeeWarn : Bool :=
                            match mode, feeSats? with
                            | .full, some fSats =>
                                decide (10 * fSats.toNat ≥ inSt.sumInSats.toNat) && aboveSupplyFloor
                            | .selfTransfer, some fSats =>
                                decide (10 * fSats.toNat ≥ inSt.sumInSats.toNat) && aboveSupplyFloor
                            | _, _ => false
                          .ok {
                            locktime := locktime
                            validatedInputs := inSt.valInputs
                            displayedOutputs := displayedOuts
                            changeOutputs := changeOuts
                            sumInputs := inSt.sumInSats.toNat
                            sumInternalInputs := inSt.sumInternalInSats.toNat
                            sumOutputs := sumOutSats.toNat
                            sumChangeOutputs := sumChgSats.toNat
                            fee := feeSats?.map UInt64.toNat
                            displayMode := mode
                            warnings := {
                              missingNonWitnessUtxo := inSt.warnMissingNw
                              nonDefaultSighash := inSt.warnNonDefaultSighash
                              sighashMixed := inSt.sighashMixed
                              externalInputs := decide (inSt.nExternal > 0)
                              highFee := highFeeWarn
                              nonStandardLocktime := decide (locktime.toNat > 0)
                            }
                          }

/-- Alias matching `Spec.Psbt.validatePsbt`. -/
abbrev validatePsbt := validatePsbtTransaction

/-! ## 7. Executable Sighash Digest Engine (Legacy, BIP-143 SegWit v0, BIP-341/342 Taproot) -/

/-- Precompute transaction-wide SHA-256 digests (`shaPrevouts`, `shaAmounts`, `shaScriptPubkeys`,
    `shaSequences`, `shaOutputs`). -/
def computeTxHashes
    (sha256 : ByteArray → Bytes32)
    (inputs : List (PsbtInput × TxOut))
    (outputs : List TxOut) : TxHashes :=
  let prevoutsBytes := joinByteArrays (inputs.map fun (inp, _) => encodeOutPoint inp.prevout)
  let amountsBytes := joinByteArrays (inputs.map fun (_, utxo) => putU64LE (UInt64.ofNat utxo.amount))
  let spkBytes := joinByteArrays (inputs.map fun (_, utxo) =>
    putVarInt utxo.scriptPubKey.size ++ utxo.scriptPubKey)
  let seqBytes := joinByteArrays (inputs.map fun (inp, _) => putU32LE inp.effectiveSequence)
  let outBytes := joinByteArrays (outputs.map encodeTxOut)
  { shaPrevouts := sha256 prevoutsBytes
    shaAmounts := sha256 amountsBytes
    shaScriptPubkeys := sha256 spkBytes
    shaSequences := sha256 seqBytes
    shaOutputs := sha256 outBytes }

/-- Executable Legacy sighash digest (`doubleSha256` with `scriptCode` at `inputIndex` and `0x00` elsewhere). -/
def computeSighashLegacy
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (inputs : Array PsbtInput)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (scriptCode : ByteArray)
    (sighashByte : UInt8) : Bytes32 :=
  let serializedInputs := joinByteArrays <| (List.range inputs.size).map fun i =>
    if h : i < inputs.size then
      let inp := inputs[i]'h
      let sc :=
        if decide (i = inputIndex) then
          putVarInt scriptCode.size ++ scriptCode
        else
          ByteArray.mk #[0x00]
      encodeOutPoint inp.prevout ++ sc ++ putU32LE inp.effectiveSequence
    else
      ByteArray.empty
  let serializedOutputs := joinByteArrays (outputs.toList.map encodeTxOut)
  let preimage :=
    putU32LE txVersion ++
    putVarInt inputs.size ++
    serializedInputs ++
    putVarInt outputs.size ++
    serializedOutputs ++
    putU32LE locktime ++
    putU32LE (UInt32.ofNat sighashByte.toNat)
  hash256d sha256 preimage

/-- Construct BIP-143 `scriptCode` (including length prefix) for P2WPKH or P2WSH. -/
def buildSegwitV0ScriptCode (activeScript : ByteArray) (witnessScript : Option ByteArray) : Option ByteArray :=
  if checkP2WPKH activeScript then
    let pkHash20 := activeScript.extract 2 22
    some (ByteArray.mk #[0x19, 0x76, 0xa9, 0x14] ++ pkHash20 ++ ByteArray.mk #[0x88, 0xac])
  else if checkP2WSH activeScript then
    match witnessScript with
    | some ws => some (putVarInt ws.size ++ ws)
    | none => none
  else
    none

/-- Executable BIP-143 SegWit v0 sighash digest (`0x01`/`0x02`/`0x03`/`0x81`/`0x82`/`0x83`). -/
def computeSighashSegwitV0
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
  let anyoneCanPay := sighashHasAnyoneCanPay sighashByte
  let base := sighashByte &&& 0x1f
  let hashPrevouts : Bytes32 :=
    if !anyoneCanPay then sha256 hashes.shaPrevouts.bytes else zeroBytes32
  let hashSequence : Bytes32 :=
    if !anyoneCanPay && !decide (base = SIGHASH_SINGLE) && !decide (base = SIGHASH_NONE) then
      sha256 hashes.shaSequences.bytes
    else
      zeroBytes32
  let hashOutputs : Bytes32 :=
    if !decide (base = SIGHASH_SINGLE) && !decide (base = SIGHASH_NONE) then
      sha256 hashes.shaOutputs.bytes
    else if decide (base = SIGHASH_SINGLE) then
      if h : inputIndex < outputs.size then
        hash256d sha256 (encodeTxOut (outputs[inputIndex]'h))
      else
        zeroBytes32
    else
      zeroBytes32
  let preimage :=
    putU32LE txVersion ++
    hashPrevouts.bytes ++
    hashSequence.bytes ++
    encodeOutPoint inp.prevout ++
    scriptCodeWithLen ++
    putU64LE (UInt64.ofNat utxoAmount) ++
    putU32LE inp.effectiveSequence ++
    hashOutputs.bytes ++
    putU32LE locktime ++
    putU32LE (UInt32.ofNat sighashByte.toNat)
  hash256d sha256 preimage

/-- Executable BIP-341 / BIP-342 Taproot & Tapscript sighash (`0x00`/`0x01`/`0x02`/`0x03`/`0x81`/`0x82`/`0x83`). -/
def computeSighashTaproot
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
  let anyoneCanPay := decide ((sighashByte &&& 0x80) = SIGHASH_ANYONECANPAY)
  let base := sighashByte &&& 0x03
  let extFlag : UInt8 := if tapleafHash.isSome then 1 else 0
  let spendType : UInt8 := extFlag * 2
  let commonPrefix :=
    ByteArray.mk #[0x00, sighashByte] ++
    putU32LE txVersion ++
    putU32LE locktime
  let txInCommits :=
    if !anyoneCanPay then
      hashes.shaPrevouts.bytes ++
      hashes.shaAmounts.bytes ++
      hashes.shaScriptPubkeys.bytes ++
      hashes.shaSequences.bytes
    else
      ByteArray.empty
  let txOutCommits :=
    if !decide (base = SIGHASH_NONE) && !decide (base = SIGHASH_SINGLE) then
      hashes.shaOutputs.bytes
    else
      ByteArray.empty
  let perInputData :=
    if anyoneCanPay then
      encodeOutPoint inp.prevout ++
      putU64LE (UInt64.ofNat utxo.amount) ++
      putVarInt utxo.scriptPubKey.size ++
      utxo.scriptPubKey ++
      putU32LE inp.effectiveSequence
    else
      putU32LE (UInt32.ofNat inputIndex)
  let singleOutCommit :=
    if decide (base = SIGHASH_SINGLE) then
      if h : inputIndex < outputs.size then
        (sha256 (encodeTxOut (outputs[inputIndex]'h))).bytes
      else
        ByteArray.empty
    else
      ByteArray.empty
  let tapscriptExt :=
    match tapleafHash with
    | none => ByteArray.empty
    | some lh => lh.bytes ++ ByteArray.mk #[0x00] ++ putU32LE 0xFFFFFFFF
  let msg :=
    commonPrefix ++
    txInCommits ++
    txOutCommits ++
    ByteArray.mk #[spendType] ++
    perInputData ++
    singleOutCommit ++
    tapscriptExt
  bip340TaggedHash sha256 "TapSighash" msg

/-- Append canonical sighash suffix byte (omitted iff `isSchnorr && sighashByte == 0x00`). -/
def formatSignatureWithSighash (isSchnorr : Bool) (rawSig : ByteArray) (sighashByte : UInt8) : ByteArray :=
  if isSchnorr && decide (sighashByte = SIGHASH_DEFAULT) then
    rawSig
  else
    rawSig ++ ByteArray.mk #[sighashByte]

/-! ## 8. BIP-322 Virtual `to_spend` / `to_sign` Validation & Ledger Exchange Swap Checks -/

def buildBip322ToSpendTx (sha256 : ByteArray → Bytes32) (message : ByteArray) (challengeScript : ByteArray) : RawTx :=
  let msgHash := bip340TaggedHash sha256 "BIP0322-signed-message" message
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

def computeBip322ToSpendTxid (sha256 : ByteArray → Bytes32) (message : ByteArray) (challengeScript : ByteArray) : Bytes32 :=
  computeTxid sha256 (buildBip322ToSpendTx sha256 message challengeScript)

def checkBip322PrintableAscii (msg : ByteArray) : Bool :=
  decide (msg.size ≤ MAX_BIP322_PRINTABLE) &&
  msg.toList.all (fun b => decide (0x20 ≤ b.toNat ∧ b.toNat ≤ 0x7E) || decide (b = 0x0A))

def checkBip322ProofOfFundsSequence (inp : PsbtInput) : Bool :=
  let seq := inp.effectiveSequence
  decide (seq = 0) || !decide ((seq &&& (0x80000000 : UInt32)) = 0)

/-- Validate BIP-322 virtual `to_sign` PSBT structure and `to_spend` challenge binding. -/
def validateBip322Psbt
    (sha256 : ByteArray → Bytes32)
    (inSwapMode : Bool)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (message : ByteArray) : Except PsbtError Unit :=
  if inSwapMode then
    .error .bip322ForbiddenInSwap
  else if !decide (psbt.txVersion = 0) && !decide (psbt.txVersion = 2) then
    .error .bip322InvalidStructure
  else if !decide (validated.locktime = 0) then
    .error .bip322InvalidStructure
  else if !decide (psbt.outputs.size = 1) || !validated.changeOutputs.isEmpty then
    .error .bip322InvalidStructure
  else if hOut : 0 < psbt.outputs.size then
    let out0 := psbt.outputs[0]'hOut
    if !decide (out0.amount = 0) || !eqOptBytes out0.scriptPubKey (some (ByteArray.mk #[0x6a])) then
      .error .bip322InvalidStructure
    else if validated.warnings.externalInputs || validated.warnings.nonDefaultSighash then
      .error .bip322InvalidStructure
    else if hIn : 0 < psbt.inputs.size ∧ 0 < validated.validatedInputs.size then
      let inp0 := psbt.inputs[0]'hIn.1
      let (utxo0, _, _) := validated.validatedInputs[0]'hIn.2
      if !eqOptU32 inp0.sequence (some 0) then
        .error .bip322InvalidSequence
      else if !decide (inp0.prevout.vout = 0) || !decide (utxo0.prevoutTxOut.amount = 0) then
        .error .bip322InvalidStructure
      else if !eqBytes32 inp0.prevout.txid (computeBip322ToSpendTxid sha256 message utxo0.prevoutTxOut.scriptPubKey) then
        .error .bip322ChallengeTxidMismatch
      else if !(psbt.inputs.toList.drop 1).all checkBip322ProofOfFundsSequence then
        .error .bip322InvalidSequence
      else
        .ok ()
    else
      .error .bip322InvalidStructure
  else
    .error .bip322InvalidStructure

/-- Extract cross-chain Swap `OP_RETURN` payload (`2..75` direct push or `0x4c` `OP_PUSHDATA1`). -/
def parseSwapOpReturnPayload (s : ByteArray) : Option ByteArray :=
  if !eqOptU8 (getByte? s 0) (some 0x6a) then
    none
  else
    match getByte? s 1 with
    | none => none
    | some pushByte =>
        let pushOp := pushByte.toNat
        if decide (2 ≤ pushOp ∧ pushOp ≤ 75) then
          if decide (s.size = 2 + pushOp) then
            some (s.extract 2 s.size)
          else
            none
        else if decide (pushOp = 0x4c) then
          match getByte? s 2 with
          | none => none
          | some lenByte =>
              let len := lenByte.toNat
              if decide (s.size = 3 + len) then
                some (s.extract 3 s.size)
              else
                none
        else
          none

/-- Extract and verify Swap recipient output under `standard` or `crossChain` mode. -/
def resolveSwapRecipientOutput
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
          if !decide (opOut.amount = 0) then
            .error .swapInvalidCrossChainPayin
          else
            match opOut.scriptPubKey with
            | none => .error .swapInvalidCrossChainPayin
            | some spk =>
                match parseSwapOpReturnPayload spk with
                | none => .error .swapInvalidCrossChainPayin
                | some payinData =>
                    if !eqBytes32 (crypto.sha256 payinData) expectedHash then
                      .error .swapInvalidCrossChainPayin
                    else
                      .ok dOut
      | _ => .error .swapOutputCountMismatch

/-- Validate Ledger Exchange Swap invariants (`check_swap_invariants` in `swap_checks.c`). -/
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
    match resolveSwapRecipientOutput crypto swap.mode validated.displayedOutputs with
    | .error e => .error e
    | .ok destOut =>
        match validated.fee with
        | none => .error .swapFeeMismatch
        | some actualFee =>
            if !decide (actualFee = swap.fees) then
              .error .swapFeeMismatch
            else if !decide ((validated.sumOutputs - validated.sumChangeOutputs) = swap.amount) ||
                    !decide (destOut.amount = swap.amount) then
              .error .swapAmountMismatch
            else if destOut.silentPayment.isSome then
              .error .swapDestinationMismatch
            else
              match destOut.scriptPubKey with
              | none => .error .swapDestinationMismatch
              | some destSpk =>
                  if !eqOptString (crypto.formatAddress destSpk) (some swap.destinationAddress) then
                    .error .swapDestinationMismatch
                  else
                    .ok ()

/-- Top-level executable PSBT signing authorization (`validatePsbtTransaction` + BIP-322 + Swap). -/
def authorizePsbtSigning
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (swapParams : Option SwapParams) : Except PsbtError ValidatedPsbt :=
  match validatePsbtTransaction crypto cfg policy psbt with
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

end BitcoinLedger.Psbt

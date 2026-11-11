import Spec
import BitcoinLedger.Basic

namespace BitcoinLedger.Script

/-!
# `BitcoinLedger.Script` — Executable Script Classifier, `MINIMALDATA`, Base58Check & Bech32/Bech32m

Executable implementation refining `Spec.Script`:
1. Standard Bitcoin script constructors & classifier (`P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, `P2TR`,
   `OpReturn`, and forward-compatible `UnknownWitness` `v0..v16` programs)
2. `MINIMALDATA` pushdata encoder/decoder and standard `OP_RETURN` canonicality validator
   (`MAX_STANDARD_OP_RETURN_LEN = 83`, `MAX_STANDARD_OP_RETURN_PUSHES = 5`)
3. Constructive Base58 & Base58Check codec
4. BIP-173 / BIP-350 Bech32 / Bech32m polymod, strict zero-padded 8↔5 bit conversion,
   SegWit address encoder/decoder (`v0 ↔ Bech32` 20/32B; `v1..v16 ↔ Bech32m` 2..40B),
   and target-aware `standardScriptToAddress?` / `scriptToAddress?`
-/

open BitcoinLedger.Basic

-- Constructive `BEq` instances avoiding `Std.PreorderPackage.toBEq` (`Classical.choice`).
local instance (priority := 2000) : BEq UInt8 := ⟨fun a b => decide (a = b)⟩
local instance (priority := 2000) : BEq UInt16 := ⟨fun a b => decide (a = b)⟩
local instance (priority := 2000) : BEq UInt32 := ⟨fun a b => decide (a = b)⟩

/-! ## 1. Opcodes, Witness Version Codec & Standard Output Scripts -/

def OP_0 : UInt8 := 0x00
def OP_PUSHDATA1 : UInt8 := 0x4C
def OP_PUSHDATA2 : UInt8 := 0x4D
def OP_PUSHDATA4 : UInt8 := 0x4E
def OP_1NEGATE : UInt8 := 0x4F
def OP_RESERVED : UInt8 := 0x50
def OP_1 : UInt8 := 0x51
def OP_16 : UInt8 := 0x60
def OP_RETURN : UInt8 := 0x6A
def OP_DUP : UInt8 := 0x76
def OP_EQUAL : UInt8 := 0x87
def OP_EQUALVERIFY : UInt8 := 0x88
def OP_HASH160 : UInt8 := 0xA9
def OP_CHECKSIG : UInt8 := 0xAC

def MAX_STANDARD_OP_RETURN_LEN : Nat := 83
def MAX_STANDARD_OP_RETURN_PUSHES : Nat := 5

/-- Map a SegWit witness version `0..16` to its `scriptPubKey` opcode (`0x00` for `0`, `0x50 + v` for `1..16`). -/
@[inline] def encodeWitnessVersionOpcode? (ver : UInt8) : Option UInt8 :=
  if decide (ver = 0) then
    some OP_0
  else if decide (ver ≤ 16) then
    some (0x50 + ver)
  else
    none

/-- Decode a `scriptPubKey` witness version opcode (`OP_0` -> `0`, `OP_1..OP_16` -> `1..16`). -/
@[inline] def decodeWitnessVersionOpcode? (op : UInt8) : Option UInt8 :=
  if decide (op = OP_0) then
    some 0
  else if decide (OP_1 ≤ op) && decide (op ≤ OP_16) then
    some (op - 0x50)
  else
    none

/-- Construct a 25-byte `P2PKH` scriptPubKey (`OP_DUP OP_HASH160 0x14 <hash20> OP_EQUALVERIFY OP_CHECKSIG`). -/
def mkP2PKH (pubKeyHash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_DUP, OP_HASH160, 0x14] ++ pubKeyHash20 ++ ByteArray.mk #[OP_EQUALVERIFY, OP_CHECKSIG]

/-- Construct a 23-byte `P2SH` scriptPubKey (`OP_HASH160 0x14 <hash20> OP_EQUAL`). -/
def mkP2SH (scriptHash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_HASH160, 0x14] ++ scriptHash20 ++ ByteArray.mk #[OP_EQUAL]

/-- Construct a 22-byte `P2WPKH` (SegWit v0) scriptPubKey (`OP_0 0x14 <hash20>`). -/
def mkP2WPKH (pubKeyHash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_0, 0x14] ++ pubKeyHash20

/-- Construct a 34-byte `P2WSH` (SegWit v0) scriptPubKey (`OP_0 0x20 <hash32>`). -/
def mkP2WSH (witnessScriptHash32 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_0, 0x20] ++ witnessScriptHash32

/-- Construct a 34-byte `P2TR` (SegWit v1 Taproot) scriptPubKey (`OP_1 0x20 <key32>`). -/
def mkP2TR (outputKeyXOnly32 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_1, 0x20] ++ outputKeyXOnly32

/-! ## 2. `MINIMALDATA` Pushdata Codec & `OP_RETURN` Canonicality Validator -/

/-- Minimal push-opcode script size for a non-negative `CScriptNum` integer `n`. -/
def minimalScriptNumPushSize (n : UInt32) : Nat :=
  if decide (n ≤ 16) then 1
  else if decide (n < 0x80) then 2
  else if decide (n < 0x8000) then 3
  else if decide (n < 0x800000) then 4
  else if decide (n < 0x80000000) then 5
  else 6

/-- Canonical `MINIMALDATA` push encoder (`none` only if `payload.size > 0xFFFFFFFF`). -/
def encodeMinimalPush? (payload : ByteArray) : Option ByteArray :=
  match payload.data.toList with
  | [] => some (ByteArray.mk #[OP_0])
  | [b] =>
      if decide (1 ≤ b.toNat) && decide (b.toNat ≤ 16) then
        some (ByteArray.mk #[UInt8.ofNat (0x50 + b.toNat)])
      else if decide (b = 0x81) then
        some (ByteArray.mk #[OP_1NEGATE])
      else
        some (ByteArray.mk #[0x01, b])
  | _ =>
      let len := payload.size
      if decide (len ≤ 75) then
        some (ByteArray.mk #[UInt8.ofNat len] ++ payload)
      else if decide (len ≤ 255) then
        some (ByteArray.mk #[OP_PUSHDATA1, UInt8.ofNat len] ++ payload)
      else if decide (len ≤ 65535) then
        some (ByteArray.mk #[OP_PUSHDATA2] ++ encodeU16LE (UInt16.ofNat len) ++ payload)
      else if decide (len ≤ 0xFFFFFFFF) then
        some (ByteArray.mk #[OP_PUSHDATA4] ++ encodeU32LE (UInt32.ofNat len) ++ payload)
      else
        none

/-- Strict `MINIMALDATA` streaming push decoder returning `(pushedPayload, remainingScriptBytes)`. -/
def decodeMinimalPushPrefix? (script : ByteArray) : Option (ByteArray × ByteArray) :=
  match script.data.toList with
  | [] => none
  | op :: rest =>
      if decide (op = OP_0) then
        some (ByteArray.empty, ByteArray.mk rest.toArray)
      else if decide (op = OP_1NEGATE) then
        some (ByteArray.mk #[0x81], ByteArray.mk rest.toArray)
      else if decide (OP_1 ≤ op) && decide (op ≤ OP_16) then
        some (ByteArray.mk #[op - 0x50], ByteArray.mk rest.toArray)
      else if decide (op = 0x01) then
        match rest with
        | [] => none
        | b :: tail =>
            if (decide (1 ≤ b.toNat) && decide (b.toNat ≤ 16)) || decide (b = 0x81) then
              none
            else
              some (ByteArray.mk #[b], ByteArray.mk tail.toArray)
      else if decide (2 ≤ op.toNat) && decide (op.toNat ≤ 75) then
        let len := op.toNat
        if decide (rest.length < len) then
          none
        else
          some (ByteArray.mk (rest.take len).toArray, ByteArray.mk (rest.drop len).toArray)
      else if decide (op = OP_PUSHDATA1) then
        match rest with
        | [] => none
        | lenByte :: tail =>
            let len := lenByte.toNat
            if decide (len < 76) || decide (tail.length < len) then
              none
            else
              some (ByteArray.mk (tail.take len).toArray, ByteArray.mk (tail.drop len).toArray)
      else if decide (op = OP_PUSHDATA2) then
        match rest with
        | b0 :: b1 :: tail =>
            let len := b0.toNat + 256 * b1.toNat
            if decide (len < 256) || decide (tail.length < len) then
              none
            else
              some (ByteArray.mk (tail.take len).toArray, ByteArray.mk (tail.drop len).toArray)
        | _ => none
      else if decide (op = OP_PUSHDATA4) then
        match rest with
        | b0 :: b1 :: b2 :: b3 :: tail =>
            let len := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat
            if decide (len < 65536) || decide (tail.length < len) then
              none
            else
              some (ByteArray.mk (tail.take len).toArray, ByteArray.mk (tail.drop len).toArray)
        | _ => none
      else
        none

/-- Bounded `MINIMALDATA` push sequence validator (`0..budget` pushes). -/
def checkMinimalPushesBounded : Nat → List UInt8 → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] => true
  | budget + 1, bytes =>
      match decodeMinimalPushPrefix? (ByteArray.mk bytes.toArray) with
      | none => false
      | some (_, rem) => checkMinimalPushesBounded budget rem.data.toList

/-- Validate BOLOS's standard `OP_RETURN` output formatting rules (`≤ 83` bytes, `≤ 5` `MINIMALDATA` pushes). -/
def isValidOpReturnScript (script : ByteArray) : Bool :=
  decide (script.size ≤ MAX_STANDARD_OP_RETURN_LEN) &&
    match script.data.toList with
    | 0x6A :: tail => checkMinimalPushesBounded MAX_STANDARD_OP_RETURN_PUSHES tail
    | _ => false

abbrev StandardScript := Spec.StandardScript

/-- Serialize a `StandardScript` into its raw `scriptPubKey` bytes. -/
def standardScriptToPubKey : StandardScript → ByteArray
  | .p2pkh h => mkP2PKH h
  | .p2sh h => mkP2SH h
  | .p2wpkh h => mkP2WPKH h
  | .p2wsh h => mkP2WSH h
  | .p2tr k => mkP2TR k
  | .unknownWitness v prog =>
      let op := if decide (v = 0) then OP_0 else 0x50 + v
      ByteArray.mk #[op, UInt8.ofNat prog.size] ++ prog
  | .opReturn tail =>
      ByteArray.mk #[OP_RETURN] ++ tail

/-- Executable standard `scriptPubKey` classifier (`P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, `P2TR`,
    `UnknownWitness`, `OpReturn`). -/
def classifyScript? (script : ByteArray) : Option StandardScript :=
  match script.data.toList with
  | 0x6A :: tail =>
      some (.opReturn (ByteArray.mk tail.toArray))
  | 0x76 :: 0xA9 :: 0x14 :: rest =>
      if decide (rest.length = 22) then
        let hash20 := rest.take 20
        let suffix := rest.drop 20
        if eqByteList suffix [0x88, 0xAC] then
          some (.p2pkh (ByteArray.mk hash20.toArray))
        else
          none
      else
        none
  | 0xA9 :: 0x14 :: rest =>
      if decide (rest.length = 21) then
        let hash20 := rest.take 20
        let suffix := rest.drop 20
        if eqByteList suffix [0x87] then
          some (.p2sh (ByteArray.mk hash20.toArray))
        else
          none
      else
        none
  | op :: pushLen :: prog =>
      match decodeWitnessVersionOpcode? op with
      | none => none
      | some ver =>
          if decide (pushLen.toNat = prog.length) &&
             decide (2 ≤ prog.length) && decide (prog.length ≤ 40) then
            let progBytes := ByteArray.mk prog.toArray
            if decide (ver = 0) && decide (prog.length = 20) then
              some (.p2wpkh progBytes)
            else if decide (ver = 0) && decide (prog.length = 32) then
              some (.p2wsh progBytes)
            else if decide (ver = 1) && decide (prog.length = 32) then
              some (.p2tr progBytes)
            else
              some (.unknownWitness ver progBytes)
          else
            none
  | _ => none

/-! ## 3. Constructive Base58 & Base58Check Codec -/

/-- Convert a `String` of 7-bit ASCII bytes (`< 128`) into `List Char` constructively. -/
def asciiCharsOfString? (s : String) : Option (List Char) :=
  let utf8 := s.toUTF8.data.toList
  if utf8.all (fun b => decide (b < 128)) then
    some (utf8.map Char.ofUInt8)
  else
    none

/-- Bitcoin Base58 alphabet (`58` characters). -/
def BASE58_ALPHABET : List Char := Spec.BASE58_ALPHABET

/-- Decode a Base58 character into its digit value in `0..57`. -/
def base58CharToDigit? (c : Char) : Option Nat :=
  BASE58_ALPHABET.findIdx? (fun x => decide (x = c))

/-- Encode a digit in `0..57` into its Base58 character. -/
def base58DigitToChar? (d : Nat) : Option Char :=
  BASE58_ALPHABET[d]?

/-- Interpret a list of bytes as a big-endian natural number. -/
def bytesToNatBE (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- Interpret a list of Base58 digits (`0..57`) as a big-endian base-58 natural number. -/
def digitsToNat58 (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => 58 * acc + d) 0

/-- Count leading elements satisfying predicate `p`. -/
def countLeading {α : Type} (p : α → Bool) : List α → Nat := Spec.countLeading p

def natToBytesBEAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, n, acc => natToBytesBEAux fuel (n / 256) (UInt8.ofNat (n % 256) :: acc)

def natToDigits58Aux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, n, acc => natToDigits58Aux fuel (n / 58) ((n % 58) :: acc)

/-- Canonical Bitcoin Base58 encoder (preserving leading `0x00` bytes as `'1'`). -/
def encodeBase58? (raw : ByteArray) : Option String :=
  Spec.encodeBase58? raw

/-- Canonical **Base58Check** encoder over `(version, payload)` using `doubleSha256`. -/
def encodeBase58Check?
    (doubleSha256 : ByteArray → ByteArray)
    (version : ByteArray)
    (payload : ByteArray) : Option String :=
  let body := version ++ payload
  let digest := doubleSha256 body
  if decide (digest.size < 4) then
    none
  else
    let checksum4 := ByteArray.mk (digest.data.toList.take 4).toArray
    encodeBase58? (body ++ checksum4)

/-- Decode a Base58 string into raw bytes, enforcing canonical leading-`'1'` preservation. -/
def decodeBase58? (encoded : String) : Option ByteArray :=
  Spec.decodeBase58? encoded

/-- Decode and verify a Base58Check string against `doubleSha256`, returning `version ++ payload`. -/
def decodeBase58Check? (doubleSha256 : ByteArray → ByteArray) (addr : String) : Option ByteArray :=
  match decodeBase58? addr with
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
            some body
          else
            none

/-! ## 4. BIP-173 & BIP-350 Bech32 / Bech32m Polymod, 8↔5 Bit Codec & SegWit Addresses -/

abbrev Bech32Encoding := Spec.Bech32Encoding

def bech32FinalConstant : Bech32Encoding → UInt32
  | .bech32  => 1
  | .bech32m => 0x2bc830a3

def SEGWIT_BECH32_MAX_LEN : Nat := 90
def SILENT_PAYMENT_BECH32M_MAX_LEN : Nat := 1023
def BECH32_MIN_HRP_LEN : Nat := 1
def BECH32_MAX_HRP_LEN : Nat := 83

def bech32CharToVal? : Char → Option UInt8 := Spec.bech32CharToVal?
def bech32ValToChar? : UInt8 → Option Char := Spec.bech32ValToChar?

/-- Single GF(32) BCH generator step (`app-bitcoin/src/common/segwit_addr.c:31-38`). -/
def bech32PolymodStep (pre : UInt32) (val : UInt8) : UInt32 :=
  let b := pre >>> 25
  let shifted := ((pre &&& 0x1FFFFFF) <<< 5) ^^^ val.toUInt32
  let g0 := if !decide ((b &&& 1) = 0) then (0x3b6a57b2 : UInt32) else 0
  let g1 := if !decide ((b &&& 2) = 0) then (0x26508e6d : UInt32) else 0
  let g2 := if !decide ((b &&& 4) = 0) then (0x1ea119fa : UInt32) else 0
  let g3 := if !decide ((b &&& 8) = 0) then (0x3d4233dd : UInt32) else 0
  let g4 := if !decide ((b &&& 16) = 0) then (0x2a1462b3 : UInt32) else 0
  shifted ^^^ g0 ^^^ g1 ^^^ g2 ^^^ g3 ^^^ g4

/-- Compute the Bech32 BCH polymod over a sequence of 5-bit values (seeded with `1`). -/
def bech32Polymod (values : List UInt8) : UInt32 :=
  values.foldl bech32PolymodStep 1

/-- Expand a lowercase ASCII human-readable part (`hrp`) into its 5-bit polymod prefix. -/
def bech32HrpExpand (hrpLower : List Char) : List UInt8 :=
  let hi := hrpLower.map (fun c => ((c.val >>> (5 : UInt32)) &&& (31 : UInt32)).toUInt8)
  let lo := hrpLower.map (fun c => (c.val &&& (31 : UInt32)).toUInt8)
  hi ++ [0] ++ lo

/-- Compute the 6-symbol (5-bit each) Bech32 or Bech32m checksum for `(hrpLower, data5)`. -/
def bech32CreateChecksum (enc : Bech32Encoding) (hrpLower : List Char) (data5 : List UInt8) : List UInt8 :=
  let mod := bech32Polymod (bech32HrpExpand hrpLower ++ data5 ++ [0, 0, 0, 0, 0, 0]) ^^^ bech32FinalConstant enc
  [ ((mod >>> 25) &&& 31).toUInt8,
    ((mod >>> 20) &&& 31).toUInt8,
    ((mod >>> 15) &&& 31).toUInt8,
    ((mod >>> 10) &&& 31).toUInt8,
    ((mod >>> 5)  &&& 31).toUInt8,
    (mod          &&& 31).toUInt8 ]

/-- Verify a Bech32/Bech32m payload+checksum 5-bit array and identify its unique `Bech32Encoding`. -/
def bech32VerifyChecksum? (hrpLower : List Char) (dataAndChecksum5 : List UInt8) : Option Bech32Encoding :=
  if decide (dataAndChecksum5.length < 6) then
    none
  else if !(dataAndChecksum5.all (fun v => decide (v < 32))) then
    none
  else
    let c := bech32Polymod (bech32HrpExpand hrpLower ++ dataAndChecksum5)
    if decide (c = bech32FinalConstant .bech32) then
      some .bech32
    else if decide (c = bech32FinalConstant .bech32m) then
      some .bech32m
    else
      none

def isAsciiUpper (c : Char) : Bool :=
  decide ((65 : UInt32) ≤ c.val) && decide (c.val ≤ 90)

def isAsciiLower (c : Char) : Bool :=
  decide ((97 : UInt32) ≤ c.val) && decide (c.val ≤ 122)

def toAsciiLower (c : Char) : Char :=
  if isAsciiUpper c then Char.ofUInt8 (c.val.toUInt8 + 32) else c

def isValidHrpCharLower (c : Char) : Bool :=
  decide ((33 : UInt32) ≤ c.val) && decide (c.val ≤ 126) && !isAsciiUpper c

def lastSeparatorOneIndex? (chars : List Char) : Option Nat :=
  Spec.lastSeparatorOneIndex? chars

/-- Decode a Bech32 or Bech32m string (up to `maxLen` characters), enforcing printable ASCII,
    no mixed case, BIP-173 HRP bounds `1..83`, and valid Bech32/Bech32m checksum. -/
def decodeBech32Raw? (maxLen : Nat) (input : String) : Option (Bech32Encoding × String × List UInt8) :=
  Spec.decodeBech32Raw? maxLen input

/-- Encode `(enc, hrp, data5)` as a lowercase Bech32 / Bech32m string (up to `maxLen` characters). -/
def encodeBech32Raw? (maxLen : Nat) (enc : Bech32Encoding) (hrp : String) (data5 : List UInt8) : Option String :=
  Spec.encodeBech32Raw? maxLen enc hrp data5

def extract5BitChunks : Nat → UInt32 → UInt32 → List UInt8
  | 0, _, _ => []
  | fuel + 1, bits, acc =>
      if decide (5 ≤ bits) then
        let remBits := bits - 5
        let chunk := ((acc >>> remBits) &&& 31).toUInt8
        let mask := ((1 : UInt32) <<< remBits) - 1
        chunk :: extract5BitChunks fuel remBits (acc &&& mask)
      else
        []

def convert8to5Loop : List UInt8 → UInt32 → UInt32 → List UInt8
  | [], 0, _ => []
  | [], bits, acc =>
      [((acc <<< (5 - bits)) &&& 31).toUInt8]
  | b :: bs, bits, acc =>
      let bits' := bits + 8
      let acc' := (acc <<< 8) ||| b.toUInt32
      let emitted := extract5BitChunks 3 bits' acc'
      let remBits := bits' % 5
      let mask := ((1 : UInt32) <<< remBits) - 1
      let remAcc := acc' &&& mask
      emitted ++ convert8to5Loop bs remBits remAcc

/-- Convert 8-bit witness program bytes into 5-bit groups (zero-padded on the right per BIP-173). -/
def convertBits8to5 (bytes : ByteArray) : List UInt8 :=
  convert8to5Loop bytes.data.toList 0 0

def extract8BitChunks : Nat → UInt32 → UInt32 → List UInt8
  | 0, _, _ => []
  | fuel + 1, bits, acc =>
      if decide (8 ≤ bits) then
        let remBits := bits - 8
        let chunk := ((acc >>> remBits) &&& 0xFF).toUInt8
        let mask := ((1 : UInt32) <<< remBits) - 1
        chunk :: extract8BitChunks fuel remBits (acc &&& mask)
      else
        []

def convert5to8Loop : List UInt8 → UInt32 → UInt32 → Option (List UInt8)
  | [], bits, acc =>
      if decide (bits ≥ 5) || !decide (acc = 0) then
        none
      else
        some []
  | v :: vs, bits, acc =>
      if decide (v ≥ 32) then
        none
      else
        let bits' := bits + 5
        let acc' := (acc <<< 5) ||| v.toUInt32
        let emitted := extract8BitChunks 2 bits' acc'
        let remBits := bits' % 8
        let mask := ((1 : UInt32) <<< remBits) - 1
        let remAcc := acc' &&& mask
        match convert5to8Loop vs remBits remAcc with
        | none => none
        | some rest => some (emitted ++ rest)

/-- Strictly decode 5-bit groups into 8-bit witness program bytes (enforcing zero-padding per BIP-173). -/
def convertBits5to8? (groups5 : List UInt8) : Option ByteArray :=
  (convert5to8Loop groups5 0 0).map (fun bs => ByteArray.mk bs.toArray)

/-- Required Bech32 checksum variant for a SegWit witness version (`v0 -> Bech32`, `v1..16 -> Bech32m`). -/
def requiredSegwitEncoding? (witver : UInt8) : Option Bech32Encoding :=
  if decide (witver = 0) then
    some .bech32
  else if decide (witver ≤ 16) then
    some .bech32m
  else
    none

/-- Valid SegWit witness program length rules (`v0`: 20 or 32 bytes; `v1..16`: 2..40 bytes). -/
def isValidSegwitProgram (witver : UInt8) (witprog : ByteArray) : Bool :=
  if decide (witver = 0) then
    decide (witprog.size = 20) || decide (witprog.size = 32)
  else if decide (witver ≤ 16) then
    decide (2 ≤ witprog.size) && decide (witprog.size ≤ 40)
  else
    false

/-- Encode a SegWit address `(hrp, witver, witprog)` enforcing BIP-173 / BIP-350 segregation. -/
def encodeSegwitAddr? (hrp : String) (witver : UInt8) (witprog : ByteArray) : Option String :=
  if !isValidSegwitProgram witver witprog then
    none
  else
    match requiredSegwitEncoding? witver with
    | none => none
    | some enc =>
        let data5 := witver :: convertBits8to5 witprog
        encodeBech32Raw? SEGWIT_BECH32_MAX_LEN enc hrp data5

/-- Decode and validate a SegWit address for `expectedHrp` (lowercase, e.g. `"bc"`, `"tb"`, `"bcrt"`). -/
def decodeSegwitAddr? (expectedHrp : String) (addr : String) : Option (UInt8 × ByteArray) :=
  match decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr with
  | none => none
  | some (enc, hrp, payload5) =>
      if !decide (hrp = expectedHrp) then
        none
      else
        match payload5 with
        | [] => none
        | witver :: prog5 =>
            if decide (witver > 16) then
              none
            else if !decide (requiredSegwitEncoding? witver = some enc) then
              none
            else
              match convertBits5to8? prog5 with
              | none => none
              | some witprog =>
                  if isValidSegwitProgram witver witprog then
                    some (witver, witprog)
                  else
                    none

abbrev AddressTarget := Spec.AddressTarget

/-- Format a classified `StandardScript` into a Bitcoin address string for `(target, net)`. -/
def standardScriptToAddress?
    (target : AddressTarget)
    (doubleSha256 : ByteArray → ByteArray)
    (net : Network)
    (sc : StandardScript) : Option String :=
  match sc with
  | .p2pkh hash20 =>
      if isBytes20 hash20 then
        encodeBase58Check? doubleSha256 (ByteArray.mk #[(networkParams net).p2pkhVersion]) hash20
      else
        none
  | .p2sh hash20 =>
      if isBytes20 hash20 then
        encodeBase58Check? doubleSha256 (ByteArray.mk #[(networkParams net).p2shVersion]) hash20
      else
        none
  | .p2wpkh hash20 =>
      if isBytes20 hash20 then
        encodeSegwitAddr? (networkParams net).bech32Hrp 0 hash20
      else
        none
  | .p2wsh hash32 =>
      if isBytes32 hash32 then
        encodeSegwitAddr? (networkParams net).bech32Hrp 0 hash32
      else
        none
  | .p2tr key32 =>
      if isBytes32 key32 then
        encodeSegwitAddr? (networkParams net).bech32Hrp 1 key32
      else
        none
  | .unknownWitness ver prog =>
      match target with
      | .bolos => none
      | .vanadium =>
          encodeSegwitAddr? (networkParams net).bech32Hrp ver prog
  | .opReturn _ => none

/-- Target-aware `scriptPubKey` → address encoder (`scriptToAddress?`). -/
def scriptToAddress?
    (target : AddressTarget)
    (doubleSha256 : ByteArray → ByteArray)
    (net : Network)
    (script : ByteArray) : Option String :=
  match classifyScript? script with
  | none => none
  | some sc => standardScriptToAddress? target doubleSha256 net sc

end BitcoinLedger.Script

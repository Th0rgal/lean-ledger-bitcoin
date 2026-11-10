import Spec.Basic

namespace Spec

/-!
# `Spec.Script` — Standard Scripts, Pushdata Canonicality, Base58Check, and Bech32/Bech32m

Implementation-independent plain Lean 4 specifications for:
1. Standard Bitcoin script classification & construction (`P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, `P2TR`,
   `OpReturn`, and forward-compatible `UnknownWitness` `v0..v16` programs)
2. `MINIMALDATA` pushdata canonicality (`app-bitcoin/src/common/script.c` & BIP-62 Rule 3)
3. Base58Check payload relation & codec (with 4-byte double-SHA256 checksum)
4. BIP-173 / BIP-350 Bech32 vs Bech32m polymod, 8↔5 bit conversion with strict zero-padding check,
   and SegWit witness-version segregation (`v0 ↔ Bech32` with 20 or 32 bytes ONLY; `v1..v16 ↔ Bech32m`
   with 2..40 bytes ONLY)
-/

/-! ## 1. Bitcoin Script Opcodes & Standard Output Scripts -/

/-- `OP_0` / `OP_FALSE` (`0x00`): pushes empty byte array `[]`. -/
def OP_0 : UInt8 := 0x00
/-- `OP_PUSHDATA1` (`0x4c`): next 1 byte is length (`76..255` when minimal). -/
def OP_PUSHDATA1 : UInt8 := 0x4C
/-- `OP_PUSHDATA2` (`0x4d`): next 2 LE bytes are length (`256..65535` when minimal). -/
def OP_PUSHDATA2 : UInt8 := 0x4D
/-- `OP_PUSHDATA4` (`0x4e`): next 4 LE bytes are length (`≥ 65536` when minimal). -/
def OP_PUSHDATA4 : UInt8 := 0x4E
/-- `OP_1NEGATE` (`0x4f`): pushes `[-1]` (`[0x81]`). -/
def OP_1NEGATE : UInt8 := 0x4F
/-- `OP_RESERVED` (`0x50`). -/
def OP_RESERVED : UInt8 := 0x50
/-- `OP_1` / `OP_TRUE` (`0x51`). -/
def OP_1 : UInt8 := 0x51
/-- `OP_16` (`0x60`). -/
def OP_16 : UInt8 := 0x60
/-- `OP_RETURN` (`0x6a`): provably unspendable data-carrier output. -/
def OP_RETURN : UInt8 := 0x6A
/-- `OP_DUP` (`0x76`). -/
def OP_DUP : UInt8 := 0x76
/-- `OP_EQUAL` (`0x87`). -/
def OP_EQUAL : UInt8 := 0x87
/-- `OP_EQUALVERIFY` (`0x88`). -/
def OP_EQUALVERIFY : UInt8 := 0x88
/-- `OP_HASH160` (`0xa9`). -/
def OP_HASH160 : UInt8 := 0xA9
/-- `OP_CHECKSIG` (`0xac`). -/
def OP_CHECKSIG : UInt8 := 0xAC

/-- Maximum standard `OP_RETURN` scriptPubKey length in BOLOS (`MAX_OUTPUT_SCRIPTPUBKEY_LEN = 83`). -/
def MAX_STANDARD_OP_RETURN_LEN : Nat := 83

/-- Maximum number of push instructions formatted in BOLOS `format_opscript_script` (`5`). -/
def MAX_STANDARD_OP_RETURN_PUSHES : Nat := 5

/-- Map a SegWit witness version `0..16` to its `scriptPubKey` opcode (`0x00` for `0`, `0x50 + v` for `1..16`). -/
def encodeWitnessVersionOpcode? (ver : UInt8) : Option UInt8 :=
  if ver = 0 then
    some OP_0
  else if ver ≤ 16 then
    some (0x50 + ver)
  else
    none

/-- Decode a `scriptPubKey` witness version opcode (`OP_0` -> `0`, `OP_1..OP_16` -> `1..16`). -/
def decodeWitnessVersionOpcode? (op : UInt8) : Option UInt8 :=
  if op = OP_0 then
    some 0
  else if OP_1 ≤ op && op ≤ OP_16 then
    some (op - 0x50)
  else
    none

theorem decode_encodeWitnessVersionOpcode {ver op : UInt8}
    (h : encodeWitnessVersionOpcode? ver = some op) :
    decodeWitnessVersionOpcode? op = some ver := by
  unfold encodeWitnessVersionOpcode? at h
  by_cases hv0 : ver = 0
  · subst hv0
    simp at h
    subst h
    rfl
  · simp only [hv0, ↓reduceIte] at h
    split at h
    · rename_i hv16
      simp only [Option.some.injEq] at h
      subst h
      have hv1 : 1 ≤ ver.toNat := by
        have : ver.toNat ≠ 0 := fun h0 => hv0 (UInt8.toNat_inj.mp h0)
        omega
      have hv16n : ver.toNat ≤ 16 := hv16
      have hopNat : ((0x50 : UInt8) + ver).toNat = 80 + ver.toNat := by
        change ((80 + ver.toNat) % 256) = 80 + ver.toNat
        omega
      unfold decodeWitnessVersionOpcode?
      have hne0 : (0x50 : UInt8) + ver ≠ OP_0 := by
        intro heq
        have := congrArg UInt8.toNat heq
        rw [hopNat] at this
        change 80 + ver.toNat = 0 at this
        omega
      have hge1 : decide (OP_1 ≤ (0x50 : UInt8) + ver) = true := by
        simp only [decide_eq_true_eq]
        change 81 ≤ ((0x50 : UInt8) + ver).toNat
        omega
      have hle16 : decide ((0x50 : UInt8) + ver ≤ OP_16) = true := by
        simp only [decide_eq_true_eq]
        change ((0x50 : UInt8) + ver).toNat ≤ 96
        omega
      simp only [hne0, ↓reduceIte, hge1, hle16, Bool.and_self, Option.some.injEq]
      apply UInt8.toNat_inj.mp
      have hle80 : (0x50 : UInt8) ≤ (0x50 : UInt8) + ver := by
        change 80 ≤ (80 + ver.toNat) % 256
        omega
      rw [UInt8.toNat_sub_of_le _ _ hle80]
      change (80 + ver.toNat) % 256 - 80 = ver.toNat
      omega
    · simp at h

/-- Construct a 25-byte `P2PKH` scriptPubKey:
    `OP_DUP OP_HASH160 0x14 <pubKeyHash20> OP_EQUALVERIFY OP_CHECKSIG`. -/
def mkP2PKH (pubKeyHash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_DUP, OP_HASH160, 0x14] ++ pubKeyHash20 ++ ByteArray.mk #[OP_EQUALVERIFY, OP_CHECKSIG]

/-- Construct a 23-byte `P2SH` scriptPubKey:
    `OP_HASH160 0x14 <scriptHash20> OP_EQUAL`. -/
def mkP2SH (scriptHash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_HASH160, 0x14] ++ scriptHash20 ++ ByteArray.mk #[OP_EQUAL]

/-- Construct a 22-byte `P2WPKH` (SegWit v0) scriptPubKey:
    `OP_0 0x14 <pubKeyHash20>`. -/
def mkP2WPKH (pubKeyHash20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_0, 0x14] ++ pubKeyHash20

/-- Construct a 34-byte `P2WSH` (SegWit v0) scriptPubKey:
    `OP_0 0x20 <witnessScriptHash32>`. -/
def mkP2WSH (witnessScriptHash32 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_0, 0x20] ++ witnessScriptHash32

/-- Construct a 34-byte `P2TR` (SegWit v1 Taproot) scriptPubKey:
    `OP_1 0x20 <outputKeyXOnly32>`. -/
def mkP2TR (outputKeyXOnly32 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_1, 0x20] ++ outputKeyXOnly32

/-! ## 2. Pushdata Canonicality (`MINIMALDATA` Rules) & Standard `OP_RETURN` Validation -/

/-- Minimal push-opcode script size for a non-negative `CScriptNum` integer `n`
    (exact specification of BOLOS `get_push_script_size` in `app-bitcoin/src/common/script.c:17-30`). -/
def minimalScriptNumPushSize (n : UInt32) : Nat :=
  if n ≤ 16 then 1
  else if n < 0x80 then 2
  else if n < 0x8000 then 3
  else if n < 0x800000 then 4
  else if n < 0x80000000 then 5
  else 6

/-- Relational specification of BIP-62 Rule 3 (`MINIMALDATA`) canonical push encoding:
    - `[]` -> `[OP_0]` (`0x00`)
    - `[b]` with `1 ≤ b ≤ 16` -> `[0x50 + b]` (`OP_1..OP_16`)
    - `[0x81]` -> `[OP_1NEGATE]` (`0x4f`)
    - `[b]` otherwise -> `[0x01, b]`
    - `2 ≤ len ≤ 75` -> `[len] ++ payload`
    - `76 ≤ len ≤ 255` -> `[OP_PUSHDATA1, len] ++ payload`
    - `256 ≤ len ≤ 65535` -> `[OP_PUSHDATA2] ++ u16le(len) ++ payload`
    - `65536 ≤ len ≤ 0xFFFFFFFF` -> `[OP_PUSHDATA4] ++ u32le(len) ++ payload`. -/
def isMinimalPush (payload : ByteArray) (encoded : ByteArray) : Prop :=
  (payload.size = 0 ∧ encoded = ByteArray.mk #[OP_0]) ∨
  (∃ b : UInt8,
    payload = ByteArray.mk #[b] ∧
    ((1 ≤ b.toNat ∧ b.toNat ≤ 16 ∧ encoded = ByteArray.mk #[UInt8.ofNat (0x50 + b.toNat)]) ∨
     (b = 0x81 ∧ encoded = ByteArray.mk #[OP_1NEGATE]) ∨
     ((b = 0 ∨ (17 ≤ b.toNat ∧ b ≠ 0x81)) ∧ encoded = ByteArray.mk #[0x01, b]))) ∨
  (2 ≤ payload.size ∧ payload.size ≤ 75 ∧
    encoded = ByteArray.mk #[UInt8.ofNat payload.size] ++ payload) ∨
  (76 ≤ payload.size ∧ payload.size ≤ 255 ∧
    encoded = ByteArray.mk #[OP_PUSHDATA1, UInt8.ofNat payload.size] ++ payload) ∨
  (256 ≤ payload.size ∧ payload.size ≤ 65535 ∧
    encoded = ByteArray.mk #[OP_PUSHDATA2] ++ encodeU16LEBytes (UInt16.ofNat payload.size) ++ payload) ∨
  (65536 ≤ payload.size ∧ payload.size ≤ 0xFFFFFFFF ∧
    encoded = ByteArray.mk #[OP_PUSHDATA4] ++ encodeU32LEBytes (UInt32.ofNat payload.size) ++ payload)

/-- Canonical `MINIMALDATA` push encoder (`none` only if `payload.size > 0xFFFFFFFF`). -/
def encodeMinimalPush? (payload : ByteArray) : Option ByteArray :=
  match payload.data.toList with
  | [] => some (ByteArray.mk #[OP_0])
  | [b] =>
      if 1 ≤ b.toNat && b.toNat ≤ 16 then
        some (ByteArray.mk #[UInt8.ofNat (0x50 + b.toNat)])
      else if b = 0x81 then
        some (ByteArray.mk #[OP_1NEGATE])
      else
        some (ByteArray.mk #[0x01, b])
  | _ =>
      let len := payload.size
      if len ≤ 75 then
        some (ByteArray.mk #[UInt8.ofNat len] ++ payload)
      else if len ≤ 255 then
        some (ByteArray.mk #[OP_PUSHDATA1, UInt8.ofNat len] ++ payload)
      else if len ≤ 65535 then
        some (ByteArray.mk #[OP_PUSHDATA2] ++ encodeU16LEBytes (UInt16.ofNat len) ++ payload)
      else if len ≤ 0xFFFFFFFF then
        some (ByteArray.mk #[OP_PUSHDATA4] ++ encodeU32LEBytes (UInt32.ofNat len) ++ payload)
      else
        none

/-- Strict `MINIMALDATA` streaming push decoder returning `(pushedPayload, remainingScriptBytes)`.
    Rejects non-push opcodes, truncated pushes, and every non-minimal push encoding. -/
def decodeMinimalPushPrefix? (script : ByteArray) : Option (ByteArray × ByteArray) :=
  match script.data.toList with
  | [] => none
  | op :: rest =>
      if op = OP_0 then
        some (ByteArray.empty, ByteArray.mk rest.toArray)
      else if op = OP_1NEGATE then
        some (ByteArray.mk #[0x81], ByteArray.mk rest.toArray)
      else if OP_1 ≤ op && op ≤ OP_16 then
        some (ByteArray.mk #[op - 0x50], ByteArray.mk rest.toArray)
      else if op = 0x01 then
        match rest with
        | [] => none
        | b :: tail =>
            if (1 ≤ b.toNat && b.toNat ≤ 16) || decide (b = 0x81) then
              none
            else
              some (ByteArray.mk #[b], ByteArray.mk tail.toArray)
      else if 2 ≤ op.toNat && op.toNat ≤ 75 then
        let len := op.toNat
        if rest.length < len then
          none
        else
          some (ByteArray.mk (rest.take len).toArray, ByteArray.mk (rest.drop len).toArray)
      else if op = OP_PUSHDATA1 then
        match rest with
        | [] => none
        | lenByte :: tail =>
            let len := lenByte.toNat
            if len < 76 || tail.length < len then
              none
            else
              some (ByteArray.mk (tail.take len).toArray, ByteArray.mk (tail.drop len).toArray)
      else if op = OP_PUSHDATA2 then
        match rest with
        | b0 :: b1 :: tail =>
            let len := b0.toNat + 256 * b1.toNat
            if len < 256 || tail.length < len then
              none
            else
              some (ByteArray.mk (tail.take len).toArray, ByteArray.mk (tail.drop len).toArray)
        | _ => none
      else if op = OP_PUSHDATA4 then
        match rest with
        | b0 :: b1 :: b2 :: b3 :: tail =>
            let len := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat
            if len < 65536 || tail.length < len then
              none
            else
              some (ByteArray.mk (tail.take len).toArray, ByteArray.mk (tail.drop len).toArray)
        | _ => none
      else
        none

/-- Validate BOLOS's standard `OP_RETURN` output formatting rules (`format_opscript_script`,
    `app-bitcoin/src/common/script.c:139-203` and `unit-tests/test_script.c:294-303`):
    - Starts with `OP_RETURN (0x6a)` and total length `≤ 83` (`MAX_STANDARD_OP_RETURN_LEN`)
    - Either bare `OP_RETURN` (length 1, used e.g. in BIP-322 virtual to_spend) or `1..5` canonical
      `MINIMALDATA` pushes (rejecting non-minimal 1-byte pushes `0x01 0x01..0x10` and `0x01 0x81`,
      non-minimal `OP_PUSHDATA1`, `OP_PUSHDATA2`/`4`, non-push opcodes, `> 5` pushes, and `> 83` bytes). -/
def checkMinimalPushesBounded : Nat → List UInt8 → Bool
  | 0, [] => true
  | 0, _ :: _ => false
  | _ + 1, [] => true
  | budget + 1, bytes =>
      match decodeMinimalPushPrefix? (ByteArray.mk bytes.toArray) with
      | none => false
      | some (_, rem) => checkMinimalPushesBounded budget rem.data.toList

def isValidOpReturnScript (script : ByteArray) : Bool :=
  script.size ≤ MAX_STANDARD_OP_RETURN_LEN &&
    match script.data.toList with
    | 0x6A :: tail => checkMinimalPushesBounded MAX_STANDARD_OP_RETURN_PUSHES tail
    | _ => false

abbrev isValidBolosOpReturnScript : ByteArray → Bool := isValidOpReturnScript

/-- Classified standard output script representations. -/
inductive StandardScript where
  /-- Pay-to-PubKey-Hash (`20`-byte `HASH160`). -/
  | p2pkh (hash20 : ByteArray)
  /-- Pay-to-Script-Hash (`20`-byte `HASH160`). -/
  | p2sh (hash20 : ByteArray)
  /-- Pay-to-Witness-PubKey-Hash (`v0`, `20`-byte `HASH160`). -/
  | p2wpkh (hash20 : ByteArray)
  /-- Pay-to-Witness-Script-Hash (`v0`, `32`-byte `SHA256`). -/
  | p2wsh (hash32 : ByteArray)
  /-- Pay-to-Taproot (`v1`, `32`-byte x-only Tweaked PubKey). -/
  | p2tr (key32 : ByteArray)
  /-- Forward-compatible witness program (`v0..v16`, `2..40` bytes, excluding `P2WPKH`/`P2WSH`/`P2TR`). -/
  | unknownWitness (version : UInt8) (program : ByteArray)
  /-- Unspendable `OP_RETURN` script carrying raw tail bytes after `0x6a`. -/
  | opReturn (rawTail : ByteArray)
  deriving DecidableEq, Inhabited

/-- Structural and `MINIMALDATA` validity of each `StandardScript` constructor:
    for `.opReturn rawTail`, requires `isValidOpReturnScript ([OP_RETURN] ++ rawTail)`
    (enforcing `≤ 83` bytes, `≤ 5` pushes, and canonical `MINIMALDATA` pushes). -/
def StandardScript.WellFormed : StandardScript → Prop
  | .p2pkh h => Bytes20 h
  | .p2sh h => Bytes20 h
  | .p2wpkh h => Bytes20 h
  | .p2wsh h => Bytes32 h
  | .p2tr k => Bytes32 k
  | .unknownWitness v prog =>
      v.toNat ≤ 16 ∧
      2 ≤ prog.size ∧ prog.size ≤ 40 ∧
      ¬ (v = 0 ∧ (prog.size = 20 ∨ prog.size = 32)) ∧
      ¬ (v = 1 ∧ prog.size = 32)
  | .opReturn rawTail =>
      isValidOpReturnScript (ByteArray.mk #[OP_RETURN] ++ rawTail) = true

instance (s : StandardScript) : Decidable s.WellFormed :=
  match s with
  | .p2pkh h => inferInstanceAs (Decidable (Bytes20 h))
  | .p2sh h => inferInstanceAs (Decidable (Bytes20 h))
  | .p2wpkh h => inferInstanceAs (Decidable (Bytes20 h))
  | .p2wsh h => inferInstanceAs (Decidable (Bytes32 h))
  | .p2tr k => inferInstanceAs (Decidable (Bytes32 k))
  | .unknownWitness v prog =>
      inferInstanceAs (Decidable
        (v.toNat ≤ 16 ∧ 2 ≤ prog.size ∧ prog.size ≤ 40 ∧
         ¬ (v = 0 ∧ (prog.size = 20 ∨ prog.size = 32)) ∧ ¬ (v = 1 ∧ prog.size = 32)))
  | .opReturn rawTail =>
      inferInstanceAs (Decidable (isValidOpReturnScript (ByteArray.mk #[OP_RETURN] ++ rawTail) = true))

/-- Serialize a `StandardScript` into its raw `scriptPubKey` bytes. -/
def StandardScript.toScriptPubKey : StandardScript → ByteArray
  | .p2pkh h => mkP2PKH h
  | .p2sh h => mkP2SH h
  | .p2wpkh h => mkP2WPKH h
  | .p2wsh h => mkP2WSH h
  | .p2tr k => mkP2TR k
  | .unknownWitness v prog =>
      let op := if v = 0 then OP_0 else 0x50 + v
      ByteArray.mk #[op, UInt8.ofNat prog.size] ++ prog
  | .opReturn tail =>
      ByteArray.mk #[OP_RETURN] ++ tail

/-- Classify an arbitrary `scriptPubKey` byte array into `StandardScript`
    (matching BOLOS `get_script_type` in `app-bitcoin/src/common/script.c` plus `OP_RETURN`). -/
def classifyScript? (script : ByteArray) : Option StandardScript :=
  let bytes := script.data.toList
  match bytes with
  | 0x6A :: tail =>
      some (.opReturn (ByteArray.mk tail.toArray))
  | 0x76 :: 0xA9 :: 0x14 :: rest =>
      if rest.length = 22 then
        let hash20 := rest.take 20
        let suffix := rest.drop 20
        if suffix = [0x88, 0xAC] then
          some (.p2pkh (ByteArray.mk hash20.toArray))
        else
          none
      else
        none
  | 0xA9 :: 0x14 :: rest =>
      if rest.length = 21 then
        let hash20 := rest.take 20
        let suffix := rest.drop 20
        if suffix = [0x87] then
          some (.p2sh (ByteArray.mk hash20.toArray))
        else
          none
      else
        none
  | op :: pushLen :: prog =>
      match decodeWitnessVersionOpcode? op with
      | none => none
      | some ver =>
          if pushLen.toNat = prog.length ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 then
            let progBytes := ByteArray.mk prog.toArray
            if ver = 0 ∧ prog.length = 20 then
              some (.p2wpkh progBytes)
            else if ver = 0 ∧ prog.length = 32 then
              some (.p2wsh progBytes)
            else if ver = 1 ∧ prog.length = 32 then
              some (.p2tr progBytes)
            else
              some (.unknownWitness ver progBytes)
          else
            none
  | _ => none

theorem classifyScript?_mkP2PKH {h : ByteArray} (h20 : Bytes20 h) :
    classifyScript? (mkP2PKH h) = some (.p2pkh h) := by
  unfold classifyScript? mkP2PKH
  cases h with
  | mk arr =>
      have hl : arr.toList.length = 20 := h20
      have htake : List.take 20 (arr.toList ++ [136, 172]) = arr.toList := by
        rw [List.take_append_of_le_length (by omega), ← hl, List.take_length]
      have hdrop : List.drop 20 (arr.toList ++ [136, 172]) = [136, 172] := by
        rw [List.drop_append_of_le_length (by omega), ← hl, List.drop_length]
        rfl
      simp only [ByteArray.data_append, OP_DUP, OP_HASH160, OP_EQUALVERIFY, OP_CHECKSIG]
      simp [htake, hdrop]
      exact h20

theorem classifyScript?_mkP2SH {h : ByteArray} (h20 : Bytes20 h) :
    classifyScript? (mkP2SH h) = some (.p2sh h) := by
  unfold classifyScript? mkP2SH
  cases h with
  | mk arr =>
      have hl : arr.toList.length = 20 := h20
      have htake : List.take 20 (arr.toList ++ [135]) = arr.toList := by
        rw [List.take_append_of_le_length (by omega), ← hl, List.take_length]
      have hdrop : List.drop 20 (arr.toList ++ [135]) = [135] := by
        rw [List.drop_append_of_le_length (by omega), ← hl, List.drop_length]
        rfl
      simp only [ByteArray.data_append, OP_HASH160, OP_EQUAL]
      simp [htake, hdrop]
      exact h20

theorem classifyScript?_mkP2WPKH {h : ByteArray} (h20 : Bytes20 h) :
    classifyScript? (mkP2WPKH h) = some (.p2wpkh h) := by
  unfold classifyScript? mkP2WPKH
  cases h with
  | mk arr =>
      have hl : arr.toList.length = 20 := h20
      simp [ByteArray.data_append, OP_0, decodeWitnessVersionOpcode?, hl]

theorem classifyScript?_mkP2WSH {h : ByteArray} (h32 : Bytes32 h) :
    classifyScript? (mkP2WSH h) = some (.p2wsh h) := by
  unfold classifyScript? mkP2WSH
  cases h with
  | mk arr =>
      have hl : arr.toList.length = 32 := h32
      simp [ByteArray.data_append, OP_0, decodeWitnessVersionOpcode?, hl]

theorem classifyScript?_mkP2TR {k : ByteArray} (h32 : Bytes32 k) :
    classifyScript? (mkP2TR k) = some (.p2tr k) := by
  unfold classifyScript? mkP2TR
  have hdec : decodeWitnessVersionOpcode? 81 = some 1 := rfl
  cases k with
  | mk arr =>
      have hl : arr.toList.length = 32 := h32
      simp [ByteArray.data_append, OP_1, hdec, hl]

/-! ## 2b. `MINIMALDATA` & `OP_RETURN` Sanity Theorems -/

/-- Non-minimal 1-byte push `[0x01, 0x05]` is rejected (must use `OP_5 = 0x55`). -/
theorem minimalPush_rejects_direct_small_int :
    decodeMinimalPushPrefix? (ByteArray.mk #[0x01, 0x05]) = none ∧
    encodeMinimalPush? (ByteArray.mk #[0x05]) = some (ByteArray.mk #[0x55]) := by
  decide

/-- Non-minimal 1-byte push `[0x01, 0x81]` is rejected (must use `OP_1NEGATE = 0x4f`). -/
theorem minimalPush_rejects_direct_1negate :
    decodeMinimalPushPrefix? (ByteArray.mk #[0x01, 0x81]) = none ∧
    encodeMinimalPush? (ByteArray.mk #[0x81]) = some (ByteArray.mk #[OP_1NEGATE]) := by
  decide

/-- Non-minimal `OP_PUSHDATA1` with length `≤ 75` (`[0x4c, 0x01, 0x42]`) is rejected. -/
theorem minimalPush_rejects_pushdata1_short :
    decodeMinimalPushPrefix? (ByteArray.mk #[OP_PUSHDATA1, 0x01, 0x42]) = none := by
  decide

/-- Pushing single zero byte `[0x00]` uses `[0x01, 0x00]`, whereas `OP_0` pushes empty `[]`. -/
theorem minimalPush_zero_byte_vs_empty :
    decodeMinimalPushPrefix? (ByteArray.mk #[OP_0]) = some (ByteArray.empty, ByteArray.empty) ∧
    decodeMinimalPushPrefix? (ByteArray.mk #[0x01, 0x00]) = some (ByteArray.mk #[0x00], ByteArray.empty) := by
  decide

/-! ## 3. Base58Check Address & Payload Encoding Specification -/

/-- Convert a `String` of 7-bit ASCII bytes (`< 128`) into `List Char` without invoking
    classical UTF-8 codepoint decoding axioms (`String.toUTF8` and `Char.ofUInt8` are axiom-free). -/
def asciiCharsOfString? (s : String) : Option (List Char) :=
  let utf8 := s.toUTF8.data.toList
  if utf8.all (fun b => decide (b < 128)) then
    some (utf8.map Char.ofUInt8)
  else
    none

/-- Bitcoin Base58 alphabet (`58` characters, omitting `'0'`, `'O'`, `'I'`, `'l'`). -/
def BASE58_ALPHABET : List Char :=
  [ '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'J', 'K', 'L', 'M', 'N', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
    'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z' ]

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
def countLeading {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => if p x then 1 + countLeading p xs else 0

/-- Relational specification of canonical Bitcoin Base58 encoding:
    1. `encoded` is 7-bit ASCII and every character belongs to `BASE58_ALPHABET`
    2. Leading `'1'`s (`digit = 0`) match leading `0x00` bytes 1-for-1
    3. The first non-leading Base58 digit (if any) is strictly non-zero (`≠ 0`)
    4. The base-58 value equals the big-endian byte value. -/
def isCanonicalBase58 (raw : ByteArray) (encoded : String) : Prop :=
  ∃ chars : List Char, ∃ digits : List Nat,
    asciiCharsOfString? encoded = some chars ∧
    chars.mapM base58CharToDigit? = some digits ∧
    countLeading (fun d => decide (d = 0)) digits = countLeading (fun b => decide (b = 0)) raw.data.toList ∧
    (match digits.drop (countLeading (fun d => decide (d = 0)) digits) with
     | [] => raw.data.toList.all (fun b => decide (b = 0)) = true
     | d0 :: _ => d0 ≠ 0) ∧
    digitsToNat58 digits = bytesToNatBE raw.data.toList

/-- Relational specification of **Base58Check** over `(version, payload)` using a double-SHA256
    function (`doubleSha256`): appends the first 4 bytes of `SHA256(SHA256(version ++ payload))`
    and encodes canonically in Base58. -/
def isValidBase58Check
    (doubleSha256 : ByteArray → ByteArray)
    (version : ByteArray)
    (payload : ByteArray)
    (addr : String) : Prop :=
  let body := version ++ payload
  let digest := doubleSha256 body
  digest.size = 32 ∧
  let checksum4 := ByteArray.mk (digest.data.toList.take 4).toArray
  isCanonicalBase58 (body ++ checksum4) addr

/-- Convert a natural number to big-endian bytes of exact minimum non-zero width. -/
private def natToBytesBEAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, n, acc => natToBytesBEAux fuel (n / 256) (UInt8.ofNat (n % 256) :: acc)

/-- Convert a natural number to big-endian Base58 digits (`0..57`) of minimum non-zero width. -/
private def natToDigits58Aux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, n, acc => natToDigits58Aux fuel (n / 58) ((n % 58) :: acc)

/-- Canonical Bitcoin Base58 encoder (preserving leading `0x00` bytes as `'1'`). -/
def encodeBase58? (raw : ByteArray) : Option String :=
  let bytes := raw.data.toList
  let leadingZeros := countLeading (fun b => decide (b = 0)) bytes
  let val := bytesToNatBE bytes
  let magDigits := natToDigits58Aux (2 * bytes.length + 1) val []
  match magDigits.mapM base58DigitToChar? with
  | none => none
  | some magChars =>
      let prefixOnes := List.replicate leadingZeros '1'
      some (String.ofList (prefixOnes ++ magChars))

/-- Canonical **Base58Check** encoder over `(version, payload)` using `doubleSha256`. -/
def encodeBase58Check?
    (doubleSha256 : ByteArray → ByteArray)
    (version : ByteArray)
    (payload : ByteArray) : Option String :=
  let body := version ++ payload
  let digest := doubleSha256 body
  if digest.size < 4 then
    none
  else
    let checksum4 := ByteArray.mk (digest.data.toList.take 4).toArray
    encodeBase58? (body ++ checksum4)

/-- Decode a Base58 string into raw bytes, enforcing canonical leading-`'1'` preservation. -/
def decodeBase58? (encoded : String) : Option ByteArray :=
  match asciiCharsOfString? encoded with
  | none => none
  | some chars =>
      match chars.mapM base58CharToDigit? with
      | none => none
      | some digits =>
          let leadingZeros := countLeading (fun d => decide (d = 0)) digits
          let val := digitsToNat58 digits
          let magBytes := natToBytesBEAux (digits.length + 1) val []
          if val = 0 ∧ digits.length ≠ leadingZeros then
            none
          else
            let prefixZeros := List.replicate leadingZeros (0 : UInt8)
            some (ByteArray.mk (prefixZeros ++ magBytes).toArray)

/-- Decode and verify a Base58Check string against `doubleSha256`, returning the payload
    without its 4-byte trailing checksum (`version ++ data`). Rejects checksum mismatches. -/
def decodeBase58Check? (doubleSha256 : ByteArray → ByteArray) (addr : String) : Option ByteArray :=
  match decodeBase58? addr with
  | none => none
  | some raw =>
      if raw.size < 4 then
        none
      else
        let bodyLen := raw.size - 4
        let body := ByteArray.mk (raw.data.toList.take bodyLen).toArray
        let givenChecksum := ByteArray.mk (raw.data.toList.drop bodyLen).toArray
        let digest := doubleSha256 body
        if digest.size < 4 then
          none
        else
          let expectedChecksum := ByteArray.mk (digest.data.toList.take 4).toArray
          if givenChecksum = expectedChecksum then
            some body
          else
            none

/-! ## 4. BIP-173 & BIP-350 Bech32 / Bech32m Polymod & SegWit Segregation -/

/-- Bech32 checksum variant (`bech32` per BIP-173 vs `bech32m` per BIP-350). -/
inductive Bech32Encoding where
  | bech32
  | bech32m
  deriving Repr, DecidableEq, Inhabited

/-- Final polymod residue constant: `1` for BIP-173 `Bech32`, `0x2bc830a3` for BIP-350 `Bech32m`. -/
def bech32FinalConstant : Bech32Encoding → UInt32
  | .bech32  => 1
  | .bech32m => 0x2bc830a3

theorem bech32_final_constants_ne :
    bech32FinalConstant .bech32 ≠ bech32FinalConstant .bech32m := by
  decide

/-- Maximum total character length of a BIP-173 / BIP-350 SegWit address (`90`). -/
def SEGWIT_BECH32_MAX_LEN : Nat := 90

/-- Maximum total character length of a BIP-352 Silent Payment Bech32m address (`1023`). -/
def SILENT_PAYMENT_BECH32M_MAX_LEN : Nat := 1023

/-- Bech32 32-character data alphabet (`0..31`: `"qpzry9x8gf2tvdw0s3jn54khce6mua7l"`). -/
def bech32CharToVal? : Char → Option UInt8
  | 'q' => some 0  | 'p' => some 1  | 'z' => some 2  | 'r' => some 3
  | 'y' => some 4  | '9' => some 5  | 'x' => some 6  | '8' => some 7
  | 'g' => some 8  | 'f' => some 9  | '2' => some 10 | 't' => some 11
  | 'v' => some 12 | 'd' => some 13 | 'w' => some 14 | '0' => some 15
  | 's' => some 16 | '3' => some 17 | 'j' => some 18 | 'n' => some 19
  | '5' => some 20 | '4' => some 21 | 'k' => some 22 | 'h' => some 23
  | 'c' => some 24 | 'e' => some 25 | '6' => some 26 | 'm' => some 27
  | 'u' => some 28 | 'a' => some 29 | '7' => some 30 | 'l' => some 31
  | _   => none

/-- Map a 5-bit value (`0..31`) to its lowercase Bech32 character. -/
def bech32ValToChar? (v : UInt8) : Option Char :=
  match v.toNat with
  | 0  => some 'q' | 1  => some 'p' | 2  => some 'z' | 3  => some 'r'
  | 4  => some 'y' | 5  => some '9' | 6  => some 'x' | 7  => some '8'
  | 8  => some 'g' | 9  => some 'f' | 10 => some '2' | 11 => some 't'
  | 12 => some 'v' | 13 => some 'd' | 14 => some 'w' | 15 => some '0'
  | 16 => some 's' | 17 => some '3' | 18 => some 'j' | 19 => some 'n'
  | 20 => some '5' | 21 => some '4' | 22 => some 'k' | 23 => some 'h'
  | 24 => some 'c' | 25 => some 'e' | 26 => some '6' | 27 => some 'm'
  | 28 => some 'u' | 29 => some 'a' | 30 => some '7' | 31 => some 'l'
  | _  => none

/-- Single GF(32) BCH generator step (`app-bitcoin/src/common/segwit_addr.c:31-38`). -/
def bech32PolymodStep (pre : UInt32) (val : UInt8) : UInt32 :=
  let b := pre >>> 25
  let shifted := ((pre &&& 0x1FFFFFF) <<< 5) ^^^ UInt32.ofNat val.toNat
  let g0 := if (b &&& 1) ≠ 0 then (0x3b6a57b2 : UInt32) else 0
  let g1 := if (b &&& 2) ≠ 0 then (0x26508e6d : UInt32) else 0
  let g2 := if (b &&& 4) ≠ 0 then (0x1ea119fa : UInt32) else 0
  let g3 := if (b &&& 8) ≠ 0 then (0x3d4233dd : UInt32) else 0
  let g4 := if (b &&& 16) ≠ 0 then (0x2a1462b3 : UInt32) else 0
  shifted ^^^ g0 ^^^ g1 ^^^ g2 ^^^ g3 ^^^ g4

/-- Compute the Bech32 BCH polymod over a sequence of 5-bit values (seeded with `1`). -/
def bech32Polymod (values : List UInt8) : UInt32 :=
  values.foldl bech32PolymodStep 1

/-- Expand a lowercase ASCII human-readable part (`hrp`) into its 5-bit polymod prefix:
    `[c >> 5 | c ← hrp] ++ [0] ++ [c & 31 | c ← hrp]`. -/
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
  if dataAndChecksum5.length < 6 then
    none
  else if !(dataAndChecksum5.all (fun v => v < 32)) then
    none
  else
    let c := bech32Polymod (bech32HrpExpand hrpLower ++ dataAndChecksum5)
    if c = bech32FinalConstant .bech32 then
      some .bech32
    else if c = bech32FinalConstant .bech32m then
      some .bech32m
    else
      none

/-- ASCII character helpers for BIP-173 case-uniformity validation. -/
private def isAsciiUpper (c : Char) : Bool :=
  (65 : UInt32) ≤ c.val && c.val ≤ 90

private def isAsciiLower (c : Char) : Bool :=
  (97 : UInt32) ≤ c.val && c.val ≤ 122

private def toAsciiLower (c : Char) : Char :=
  if isAsciiUpper c then Char.ofUInt8 (c.val.toUInt8 + 32) else c

private def isValidHrpCharLower (c : Char) : Bool :=
  (33 : UInt32) ≤ c.val && c.val ≤ 126 && !isAsciiUpper c

/-- Find the index of the **last** `'1'` separator in `chars`. -/
private def lastIndexOfOneAux : Nat → Option Nat → List Char → Option Nat
  | _, acc, [] => acc
  | idx, acc, c :: cs =>
      lastIndexOfOneAux (idx + 1) (if c = '1' then some idx else acc) cs

def lastSeparatorOneIndex? (chars : List Char) : Option Nat :=
  lastIndexOfOneAux 0 none chars

/-- Minimum and maximum BIP-173 human-readable part (`hrp`) lengths (`1..83`). -/
def BECH32_MIN_HRP_LEN : Nat := 1
def BECH32_MAX_HRP_LEN : Nat := 83

/-- Decode a Bech32 or Bech32m string (up to `maxLen` characters), enforcing:
    - Printable ASCII (`33..126`), no mixed case (`!(hasLower && hasUpper)`), `length ≤ maxLen`
    - BIP-173 HRP length bounds `1 ≤ hrp.length ≤ 83` before the last `'1'` separator,
      and `≥ 6` checksum characters after `'1'`
    - Valid `Bech32` (`1`) or `Bech32m` (`0x2bc830a3`) polymod residue.
    Returns `(encoding, lowercaseHrp, data5WithoutChecksum)`. -/
def decodeBech32Raw? (maxLen : Nat) (input : String) : Option (Bech32Encoding × String × List UInt8) :=
  match asciiCharsOfString? input with
  | none => none
  | some chars =>
      if chars.length < 8 || chars.length > maxLen then
        none
      else if !(chars.all (fun c => (33 : UInt32) ≤ c.val && c.val ≤ 126)) then
        none
      else
        let hasUpper := chars.any isAsciiUpper
        let hasLower := chars.any isAsciiLower
        if hasUpper && hasLower then
          none
        else
          let lowerChars := chars.map toAsciiLower
          match lastSeparatorOneIndex? lowerChars with
          | none => none
          | some sepIdx =>
              if sepIdx < BECH32_MIN_HRP_LEN || sepIdx > BECH32_MAX_HRP_LEN ||
                 sepIdx + 7 > lowerChars.length then
                none
              else
                let hrpChars := lowerChars.take sepIdx
                let dataChars := lowerChars.drop (sepIdx + 1)
                match dataChars.mapM bech32CharToVal? with
                | none => none
                | some full5 =>
                    match bech32VerifyChecksum? hrpChars full5 with
                    | none => none
                    | some enc =>
                        let payload5 := full5.take (full5.length - 6)
                        some (enc, String.ofList hrpChars, payload5)

/-- Encode `(enc, hrp, data5)` as a lowercase Bech32 / Bech32m string (up to `maxLen` characters),
    enforcing BIP-173 `1 ≤ hrp.length ≤ 83`.
    Uses `asciiCharsOfString? hrp` (rather than `hrp.length`, which decodes UTF-8 codepoints via
    `Classical.choice` in Lean 4's standard library) so the definition stays strictly constructive. -/
def encodeBech32Raw? (maxLen : Nat) (enc : Bech32Encoding) (hrp : String) (data5 : List UInt8) : Option String :=
  match asciiCharsOfString? hrp with
  | none => none
  | some hrpChars =>
      if hrpChars.length < BECH32_MIN_HRP_LEN || hrpChars.length > BECH32_MAX_HRP_LEN ||
         !(hrpChars.all isValidHrpCharLower) then
        none
      else if !(data5.all (fun v => v < 32)) then
        none
      else
        let checksum := bech32CreateChecksum enc hrpChars data5
        match (data5 ++ checksum).mapM bech32ValToChar? with
        | none => none
        | some dataChars =>
            let outChars := hrpChars ++ ['1'] ++ dataChars
            if outChars.length > maxLen then
              none
            else
              some (String.ofList outChars)

/-! ### 8-bit ↔ 5-bit Witness Program Bit Conversion -/

private def extract5BitChunks : Nat → UInt32 → UInt32 → List UInt8
  | 0, _, _ => []
  | fuel + 1, bits, acc =>
      if 5 ≤ bits then
        let remBits := bits - 5
        let chunk := ((acc >>> remBits) &&& 31).toUInt8
        let mask := ((1 : UInt32) <<< remBits) - 1
        chunk :: extract5BitChunks fuel remBits (acc &&& mask)
      else
        []

private def convert8to5Loop : List UInt8 → UInt32 → UInt32 → List UInt8
  | [], 0, _ => []
  | [], bits, acc =>
      -- Zero-pad remaining `< 5` bits on the right (`(acc << (5 - bits)) & 31`)
      [((acc <<< (5 - bits)) &&& 31).toUInt8]
  | b :: bs, bits, acc =>
      -- Since `bits < 5`, `bits' = bits + 8 ≤ 12`, so at most 2 five-bit chunks are emitted (`fuel = 3`).
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

private def extract8BitChunks : Nat → UInt32 → UInt32 → List UInt8
  | 0, _, _ => []
  | fuel + 1, bits, acc =>
      if 8 ≤ bits then
        let remBits := bits - 8
        let chunk := ((acc >>> remBits) &&& 0xFF).toUInt8
        let mask := ((1 : UInt32) <<< remBits) - 1
        chunk :: extract8BitChunks fuel remBits (acc &&& mask)
      else
        []

private def convert5to8Loop : List UInt8 → UInt32 → UInt32 → Option (List UInt8)
  | [], bits, acc =>
      -- BIP-173 strict padding check: leftover bits must be `< 5` and all zero!
      if bits ≥ 5 ∨ acc ≠ 0 then
        none
      else
        some []
  | v :: vs, bits, acc =>
      if v ≥ 32 then
        none
      else
        -- Since `bits < 8`, `bits' = bits + 5 ≤ 12`, so at most 1 eight-bit chunk is emitted (`fuel = 2`).
        let bits' := bits + 5
        let acc' := (acc <<< 5) ||| v.toUInt32
        let emitted := extract8BitChunks 2 bits' acc'
        let remBits := bits' % 8
        let mask := ((1 : UInt32) <<< remBits) - 1
        let remAcc := acc' &&& mask
        match convert5to8Loop vs remBits remAcc with
        | none => none
        | some rest => some (emitted ++ rest)

/-- Strictly decode 5-bit groups into 8-bit witness program bytes, rejecting `≥ 5` leftover bits
    or any non-zero trailing padding bits (BIP-173). -/
def convertBits5to8? (groups5 : List UInt8) : Option ByteArray :=
  (convert5to8Loop groups5 0 0).map (fun bs => ByteArray.mk bs.toArray)

/-! ### BIP-173 / BIP-350 SegWit Witness-Version Segregation -/

/-- Required Bech32 checksum variant for a SegWit witness version (`v0 -> Bech32`, `v1..v16 -> Bech32m`). -/
def requiredSegwitEncoding? (witver : UInt8) : Option Bech32Encoding :=
  if witver = 0 then
    some .bech32
  else if witver ≤ 16 then
    some .bech32m
  else
    none

/-- Valid SegWit witness program length rules (BIP-141 / BIP-173 / BIP-350):
    - `witver = 0`: **ONLY** `20` bytes (P2WPKH) or `32` bytes (P2WSH)
    - `1 ≤ witver ≤ 16`: `2 ≤ witprog.size ≤ 40`
    - `witver > 16`: invalid. -/
def isValidSegwitProgram (witver : UInt8) (witprog : ByteArray) : Bool :=
  if witver = 0 then
    decide (witprog.size = 20 ∨ witprog.size = 32)
  else if witver ≤ 16 then
    decide (2 ≤ witprog.size ∧ witprog.size ≤ 40)
  else
    false

/-- Encode a SegWit address `(hrp, witver, witprog)` enforcing BIP-173 (`v0 -> Bech32`, 20/32B)
    and BIP-350 (`v1..v16 -> Bech32m`, 2..40B) and total length `≤ 90`. -/
def encodeSegwitAddr? (hrp : String) (witver : UInt8) (witprog : ByteArray) : Option String :=
  if !isValidSegwitProgram witver witprog then
    none
  else
    match requiredSegwitEncoding? witver with
    | none => none
    | some enc =>
        let data5 := witver :: convertBits8to5 witprog
        encodeBech32Raw? SEGWIT_BECH32_MAX_LEN enc hrp data5

/-- Decode and validate a SegWit address for `expectedHrp` (lowercase, e.g. `"bc"`, `"tb"`, `"bcrt"`),
    strictly enforcing BIP-173 / BIP-350 witness-version segregation:
    - Rejects `witver = 0` with `Bech32m`
    - Rejects `witver ∈ 1..16` with `Bech32`
    - Rejects `witver > 16`
    - Rejects `witver = 0` programs of length `≠ 20` and `≠ 32`
    - Rejects `witver ∈ 1..16` programs of length `< 2` or `> 40`. -/
def decodeSegwitAddr? (expectedHrp : String) (addr : String) : Option (UInt8 × ByteArray) :=
  match decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr with
  | none => none
  | some (enc, hrp, payload5) =>
      if hrp ≠ expectedHrp then
        none
      else
        match payload5 with
        | [] => none
        | witver :: prog5 =>
            if witver > 16 then
              none
            else if requiredSegwitEncoding? witver ≠ some enc then
              none
            else
              match convertBits5to8? prog5 with
              | none => none
              | some witprog =>
                  if isValidSegwitProgram witver witprog then
                    some (witver, witprog)
                  else
                    none

/-! ### Target-Aware Script-to-Address Conversion (`scriptToAddress?`) -/

/-- Target implementation profile for `scriptToAddress?`:
    - `bolos`: BOLOS C app (`get_script_address` policy rejecting forward SegWit `v2..v16`
      witness programs and non-20/32 `v0` / non-32 `v1` unknown witness scripts; only defined
      standard `P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, and `P2TR` scripts format to an address).
    - `vanadium`: Vanadium Rust app / BIP-350 (`Address::from_script`), encoding `v0` (20/32B)
      as Bech32 and `v1..v16` (2..40B, including forward SegWit `v2..v16` programs) as Bech32m. -/
inductive AddressTarget where
  | bolos
  | vanadium
  deriving Repr, DecidableEq, Inhabited

/-- Format a classified `StandardScript` into a Bitcoin address string for `(target, net)`:
    - `.p2pkh` / `.p2sh`: Base58Check using `doubleSha256` and `net.params.p2pkhVersion` / `p2shVersion`
    - `.p2wpkh` / `.p2wsh`: BIP-173 Bech32 (`v0`, `net.params.bech32Hrp`)
    - `.p2tr`: BIP-350 Bech32m (`v1`, `net.params.bech32Hrp`)
    - `.unknownWitness v prog`: rejected (`none`) on `.bolos` (including SegWit `v2..v16`),
      whereas `.vanadium` encodes valid BIP-350 witness programs (`v1` non-32B and `v2..v16` `2..40B`)
      as Bech32m via `encodeSegwitAddr?`
    - `.opReturn _`: `none` (provably unspendable data-carrier output has no address). -/
def standardScriptToAddress?
    (target : AddressTarget)
    (doubleSha256 : ByteArray → ByteArray)
    (net : Network)
    (sc : StandardScript) : Option String :=
  match sc with
  | .p2pkh hash20 =>
      if hash20.size = 20 then
        encodeBase58Check? doubleSha256 (ByteArray.mk #[net.params.p2pkhVersion]) hash20
      else
        none
  | .p2sh hash20 =>
      if hash20.size = 20 then
        encodeBase58Check? doubleSha256 (ByteArray.mk #[net.params.p2shVersion]) hash20
      else
        none
  | .p2wpkh hash20 =>
      if hash20.size = 20 then
        encodeSegwitAddr? net.params.bech32Hrp 0 hash20
      else
        none
  | .p2wsh hash32 =>
      if hash32.size = 32 then
        encodeSegwitAddr? net.params.bech32Hrp 0 hash32
      else
        none
  | .p2tr key32 =>
      if key32.size = 32 then
        encodeSegwitAddr? net.params.bech32Hrp 1 key32
      else
        none
  | .unknownWitness ver prog =>
      match target with
      | .bolos =>
          if 2 ≤ ver.toNat then
            none
          else
            none
      | .vanadium =>
          encodeSegwitAddr? net.params.bech32Hrp ver prog
  | .opReturn _ => none

/-- Target-aware `scriptPubKey` → address encoder (`scriptToAddress?`).
    On `.bolos`, SegWit `v2..v16` witness scripts return `none`, whereas on `.vanadium` (BIP-350)
    valid `v2..v16` witness scripts (`2..40` bytes) encode as Bech32m. -/
def scriptToAddress?
    (target : AddressTarget)
    (doubleSha256 : ByteArray → ByteArray)
    (net : Network)
    (script : ByteArray) : Option String :=
  match classifyScript? script with
  | none => none
  | some sc => standardScriptToAddress? target doubleSha256 net sc

/-! ## 5. Security & Sanity Theorems for Script & Bech32/Bech32m (`0 sorryAx`) -/

/-- Security Theorem 1: A 6-symbol checksum is NEVER simultaneously valid as both `Bech32` and `Bech32m`
    because their final polymod constants (`1` vs `0x2bc830a3`) are distinct. -/
theorem bech32VerifyChecksum_unique_variant
    (hrpLower : List Char) (data5 : List UInt8) (e1 e2 : Bech32Encoding)
    (h1 : bech32VerifyChecksum? hrpLower data5 = some e1)
    (h2 : bech32VerifyChecksum? hrpLower data5 = some e2) :
    e1 = e2 := by
  rw [h1] at h2
  exact Option.some.inj h2

/-- Security Theorem 2 (Witness v0 Segregation): Every accepted SegWit `v0` address MUST have been
    encoded with **Bech32** (never Bech32m!) and MUST have witness program length `20` or `32`. -/
theorem decodeSegwitAddr?_v0_segregation
    {expectedHrp addr : String} {prog : ByteArray}
    (hdec : decodeSegwitAddr? expectedHrp addr = some (0, prog)) :
    (∃ payload5, decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr = some (.bech32, expectedHrp, 0 :: payload5)) ∧
    (prog.size = 20 ∨ prog.size = 32) := by
  unfold decodeSegwitAddr? at hdec
  cases hraw : decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr with
  | none => simp [hraw] at hdec
  | some triple =>
      rcases triple with ⟨enc, hrp, payload5⟩
      simp only [hraw] at hdec
      by_cases hhrp : hrp = expectedHrp
      · subst hhrp
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hdec
        cases payload5 with
        | nil => simp at hdec
        | cons witver prog5 =>
            simp only at hdec
            by_cases hvgt : witver > 16
            · simp [hvgt] at hdec
            · simp only [hvgt, ↓reduceIte] at hdec
              by_cases henc : requiredSegwitEncoding? witver = some enc
              · simp only [henc, not_true_eq_false, ↓reduceIte] at hdec
                cases hconv : convertBits5to8? prog5 with
                | none => simp [hconv] at hdec
                | some witprog =>
                    simp only [hconv] at hdec
                    split at hdec
                    · rename_i hvalid
                      simp only [Option.some.injEq, Prod.mk.injEq] at hdec
                      rcases hdec with ⟨rfl, rfl⟩
                      have hencEq : enc = .bech32 := by
                        simp [requiredSegwitEncoding?] at henc
                        exact henc.symm
                      subst hencEq
                      refine ⟨⟨prog5, rfl⟩, ?_⟩
                      unfold isValidSegwitProgram at hvalid
                      simp only [↓reduceIte, decide_eq_true_eq] at hvalid
                      exact hvalid
                    · simp at hdec
              · simp [henc] at hdec
      · simp [hhrp] at hdec

/-- Security Theorem 3 (Witness v1..v16 Segregation): Every accepted SegWit `v1..v16` address (`witver ≠ 0`)
    MUST have been encoded with **Bech32m** (never Bech32!), with `1 ≤ witver ≤ 16` and `2 ≤ prog.size ≤ 40`. -/
theorem decodeSegwitAddr?_v1_to_16_segregation
    {expectedHrp addr : String} {ver : UInt8} {prog : ByteArray}
    (hne0 : ver ≠ 0)
    (hdec : decodeSegwitAddr? expectedHrp addr = some (ver, prog)) :
    1 ≤ ver.toNat ∧ ver.toNat ≤ 16 ∧
    (∃ payload5, decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr = some (.bech32m, expectedHrp, ver :: payload5)) ∧
    2 ≤ prog.size ∧ prog.size ≤ 40 := by
  unfold decodeSegwitAddr? at hdec
  cases hraw : decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr with
  | none => simp [hraw] at hdec
  | some triple =>
      rcases triple with ⟨enc, hrp, payload5⟩
      simp only [hraw] at hdec
      by_cases hhrp : hrp = expectedHrp
      · subst hhrp
        simp only [ne_eq, not_true_eq_false, ↓reduceIte] at hdec
        cases payload5 with
        | nil => simp at hdec
        | cons witver prog5 =>
            simp only at hdec
            by_cases hvgt : witver > 16
            · simp [hvgt] at hdec
            · simp only [hvgt, ↓reduceIte] at hdec
              by_cases henc : requiredSegwitEncoding? witver = some enc
              · simp only [henc, not_true_eq_false, ↓reduceIte] at hdec
                cases hconv : convertBits5to8? prog5 with
                | none => simp [hconv] at hdec
                | some witprog =>
                    simp only [hconv] at hdec
                    split at hdec
                    · rename_i hvalid
                      simp only [Option.some.injEq, Prod.mk.injEq] at hdec
                      rcases hdec with ⟨rfl, rfl⟩
                      have hv16Nat : witver.toNat ≤ 16 := by
                        have hnot : ¬ (16 < witver.toNat) := hvgt
                        omega
                      have hvLe16 : witver ≤ 16 := hv16Nat
                      have hv1 : 1 ≤ witver.toNat := by
                        have : witver.toNat ≠ 0 := fun h0 => hne0 (UInt8.toNat_inj.mp h0)
                        omega
                      have hencEq : enc = .bech32m := by
                        unfold requiredSegwitEncoding? at henc
                        simp only [hne0, ↓reduceIte, hvLe16, Option.some.injEq] at henc
                        exact henc.symm
                      subst hencEq
                      unfold isValidSegwitProgram at hvalid
                      simp only [hne0, ↓reduceIte, hvLe16, decide_eq_true_eq] at hvalid
                      exact ⟨hv1, hv16Nat, ⟨prog5, rfl⟩, hvalid.1, hvalid.2⟩
                    · simp at hdec
              · simp [henc] at hdec
      · simp [hhrp] at hdec

/-- Security Theorem 4: Any raw **Bech32m** string carrying witness version `0` is ALWAYS rejected by `decodeSegwitAddr?`. -/
theorem segwit_rejects_v0_with_bech32m
    (expectedHrp addr hrp : String) (prog5 : List UInt8)
    (hraw : decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr = some (.bech32m, hrp, 0 :: prog5)) :
    decodeSegwitAddr? expectedHrp addr = none := by
  unfold decodeSegwitAddr?
  rw [hraw]
  by_cases hhrp : hrp = expectedHrp
  · subst hhrp
    simp [requiredSegwitEncoding?]
  · simp [hhrp]

/-- Security Theorem 5: Any raw **Bech32** string carrying witness version `1..16` (`ver ≠ 0`) is ALWAYS rejected by `decodeSegwitAddr?`. -/
theorem segwit_rejects_v1_to_16_with_bech32
    (expectedHrp addr hrp : String) (ver : UInt8) (prog5 : List UInt8)
    (hne0 : ver ≠ 0)
    (hraw : decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr = some (.bech32, hrp, ver :: prog5)) :
    decodeSegwitAddr? expectedHrp addr = none := by
  unfold decodeSegwitAddr?
  rw [hraw]
  by_cases hhrp : hrp = expectedHrp
  · subst hhrp
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases hvgt : ver > 16
    · simp [hvgt]
    · have hv16Nat : ver.toNat ≤ 16 := by
        have hnot : ¬ (16 < ver.toNat) := hvgt
        omega
      have hvLe16 : ver ≤ 16 := hv16Nat
      simp [hvgt, requiredSegwitEncoding?, hne0, hvLe16]
  · simp [hhrp]

/-- Security Theorem 6: Witness version `0` with any program length other than `20` or `32`
    (such as BOLOS's `OP_0 0x02 <2 bytes>` unknown-segwit edge case) is rejected by `encodeSegwitAddr?`. -/
theorem encodeSegwitAddr?_rejects_v0_bad_length
    (hrp : String) (prog : ByteArray)
    (hne20 : prog.size ≠ 20) (hne32 : prog.size ≠ 32) :
    encodeSegwitAddr? hrp 0 prog = none := by
  unfold encodeSegwitAddr? isValidSegwitProgram
  simp [hne20, hne32]

set_option maxRecDepth 16384 in
/-- Sanity Theorem (BIP-173 Official Vector): Mainnet `v0` P2WPKH address decodes and roundtrips,
    whereas re-encoding the exact same `v0` payload with `Bech32m` is rejected, and mixed-case is rejected. -/
theorem bip173_v0_vector_and_rejections :
    let prog20 := ByteArray.mk #[
      0x75, 0x1e, 0x76, 0xe8, 0x19, 0x91, 0x96, 0xd4, 0x54, 0x94,
      0x1c, 0x45, 0xd1, 0xb3, 0xa3, 0x23, 0xf1, 0x43, 0x3b, 0xd6
    ]
    encodeSegwitAddr? "bc" 0 prog20 = some "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" ∧
    decodeSegwitAddr? "bc" "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" = some (0, prog20) ∧
    decodeSegwitAddr? "bc" "bc1qW508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" = none ∧
    (encodeBech32Raw? 90 .bech32m "bc" (0 :: convertBits8to5 prog20)).map (decodeSegwitAddr? "bc") =
      some none := by
  decide

set_option maxRecDepth 16384 in
/-- Sanity Theorem (BIP-350 Official Vector): Mainnet `v1` P2TR address decodes and roundtrips with `Bech32m`,
    whereas re-encoding the exact same `v1` payload with legacy `Bech32` is rejected. -/
theorem bip350_v1_vector_and_bech32_rejection :
    let key32 := ByteArray.mk #[
      0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac,
      0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b, 0x07,
      0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9,
      0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98
    ]
    encodeSegwitAddr? "bc" 1 key32 =
      some "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" ∧
    decodeSegwitAddr? "bc" "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" =
      some (1, key32) ∧
    (encodeBech32Raw? 90 .bech32 "bc" (1 :: convertBits8to5 key32)).map (decodeSegwitAddr? "bc") =
      some none := by
  decide

/-- Remediation Theorem (m-02a): `StandardScript.WellFormed` on `.opReturn` enforces
    `isValidOpReturnScript`, accepting canonical pushes while rejecting non-minimal 1-byte pushes
    `0x01 0x01..0x10` and `0x01 0x81`, non-minimal `OP_PUSHDATA1`, `> 5` pushes, and non-push opcodes. -/
theorem opReturn_wellFormed_rejects_nonminimal :
    (StandardScript.opReturn ByteArray.empty).WellFormed ∧
    (StandardScript.opReturn (ByteArray.mk #[0x55])).WellFormed ∧
    (StandardScript.opReturn (ByteArray.mk #[OP_1NEGATE])).WellFormed ∧
    ¬ (StandardScript.opReturn (ByteArray.mk #[0x01, 0x01])).WellFormed ∧
    ¬ (StandardScript.opReturn (ByteArray.mk #[0x01, 0x10])).WellFormed ∧
    ¬ (StandardScript.opReturn (ByteArray.mk #[0x01, 0x81])).WellFormed ∧
    ¬ (StandardScript.opReturn (ByteArray.mk #[OP_PUSHDATA1, 0x01, 0x81])).WellFormed ∧
    ¬ (StandardScript.opReturn (ByteArray.mk #[OP_1, OP_1, OP_1, OP_1, OP_1, OP_1])).WellFormed := by
  decide

set_option maxRecDepth 32768 in
/-- Remediation Theorem (m-02b): `encodeBech32Raw?` and `decodeBech32Raw?` strictly enforce
    BIP-173 HRP length bounds (`1 ≤ hrp.length ≤ 83`), rejecting empty HRPs (`""`) and `> 83`-char HRPs
    even when `maxLen = 1023`. -/
theorem bech32Raw_enforces_bip173_hrp_bounds :
    encodeBech32Raw? 1023 .bech32m "" [0] = none ∧
    encodeBech32Raw? 1023 .bech32m (String.ofList (List.replicate 83 'a')) [0] ≠ none ∧
    encodeBech32Raw? 1023 .bech32m (String.ofList (List.replicate 84 'a')) [0] = none ∧
    decodeBech32Raw? 1023 ("1qqqqqqqq") = none ∧
    decodeBech32Raw? 1023 (String.ofList (List.replicate 84 'a' ++ ['1', 'q', 'q', 'q', 'q', 'q', 'q'])) = none := by
  decide

set_option maxRecDepth 32768 in
/-- Remediation Theorem (m-02c): Target-aware `scriptToAddress?` rejects SegWit `v2..v16` scripts
    under `AddressTarget.bolos` while encoding them as BIP-350 Bech32m under `AddressTarget.vanadium`. -/
theorem scriptToAddress?_bolos_vs_vanadium_segwit_v2 :
    let dummyDSha := fun (_ : ByteArray) => ByteArray.mk (List.replicate 32 0).toArray
    let v2Script := ByteArray.mk #[0x52, 0x02, 0x00, 0x01] -- OP_2 PUSHBYTES_2 0001
    let v16Script := ByteArray.mk (#[0x60, 0x14] ++ (List.replicate 20 0x11).toArray)
    scriptToAddress? .bolos dummyDSha .mainnet v2Script = none ∧
    scriptToAddress? .bolos dummyDSha .mainnet v16Script = none ∧
    (scriptToAddress? .vanadium dummyDSha .mainnet v2Script).bind (decodeSegwitAddr? "bc") =
      some (2, ByteArray.mk #[0x00, 0x01]) ∧
    (scriptToAddress? .vanadium dummyDSha .mainnet v16Script).bind (decodeSegwitAddr? "bc") =
      some (16, ByteArray.mk (List.replicate 20 0x11).toArray) := by
  decide

end Spec

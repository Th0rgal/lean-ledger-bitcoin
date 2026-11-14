import BitcoinLedger.FreestandingKernels

/-!
# Spec — what the compiled kernel guarantees

Every statement below is about a function of `BitcoinLedger.FreestandingKernels`, the
module that `turbo-lean` compiles into the BOLOS and Vanadium apps. Nothing here refers
to a model of the apps.

Rules for this file:

* statements only, written with natural numbers, so they can be read without knowing
  the implementation;
* each statement is an "accepts exactly when" or an equality, so an implementation that
  always rejects (or always accepts) does not satisfy it;
* each statement is proved in `Proofs/KernelSpec.lean`, next to one accepted and one
  rejected concrete input.

Exported functions that have no statement here yet are listed, with the reason, in
`scripts/check_kernel_spec.py`.
-/

namespace Spec

open BitcoinLedger.FreestandingKernels

/-- 21 million BTC, in satoshis. -/
def maxMoney : Nat := 21000000 * 100000000

/-! ## Amounts -/

/-- An amount is accepted exactly when it is at most 21M BTC. -/
def ValidAmount : Prop :=
  ∀ a : UInt64, llbValidAmount a = true ↔ a.toNat ≤ maxMoney

/-- A sum is accepted exactly when the true sum is at most 21M BTC, and then the
    returned value is the true sum (no wrap-around). A rejected sum returns 0. -/
def CheckedAdd : Prop :=
  ∀ a b : UInt64,
    (llbCheckedAddSatsOk a b = true ↔ a.toNat + b.toNat ≤ maxMoney) ∧
    (llbCheckedAddSatsOk a b = true → (llbCheckedAddSatsVal a b).toNat = a.toNat + b.toNat) ∧
    (llbCheckedAddSatsOk a b = false → llbCheckedAddSatsVal a b = 0)

/-- A difference is accepted exactly when it does not go below zero and the minuend is
    at most 21M BTC, and then the returned value is the true difference. A rejected
    difference returns 0. -/
def CheckedSub : Prop :=
  ∀ a b : UInt64,
    (llbCheckedSubSatsOk a b = true ↔ b.toNat ≤ a.toNat ∧ a.toNat ≤ maxMoney) ∧
    (llbCheckedSubSatsOk a b = true → (llbCheckedSubSatsVal a b).toNat = a.toNat - b.toNat) ∧
    (llbCheckedSubSatsOk a b = false → llbCheckedSubSatsVal a b = 0)

/-- The division-free BTC / satoshi split is exact for every 64-bit amount. The two functions
    are not exported on their own: they are compiled into `llb_format_sats_ascii`. -/
def SplitBtc : Prop :=
  ∀ a : UInt64,
    (llbSatsDiv1e8 a).toNat = a.toNat / 100000000 ∧
    (llbSatsMod1e8 a).toNat = a.toNat % 100000000

/-! ## BIP-32 path elements -/

/-- A path element is hardened exactly when it is at least 2^31, and clearing the
    hardened bit yields the index below 2^31. -/
def HardenedBit : Prop :=
  ∀ i : UInt32,
    (llbBip32IsHardened i = true ↔ 2147483648 ≤ i.toNat) ∧
    (llbBip32Unharden i).toNat = i.toNat % 2147483648

/-- Path depth limits: at most 10 steps on BOLOS, at most 16 on Vanadium. -/
def DepthLimits : Prop :=
  ∀ d : UInt8,
    (llbBip32BolosDepthOk d = true ↔ d.toNat ≤ 10) ∧
    (llbBip32VanadiumDepthOk d = true ↔ d.toNat ≤ 16)

/-! ## Script and signature-hash classification -/

/-- BIP-141 / BIP-341 witness programs: version 0 needs a 20- or 32-byte program,
    versions 1 to 16 need 2 to 40 bytes, anything else is rejected. -/
def SegwitProgram : Prop :=
  ∀ v len : UInt8,
    llbSegwitProgramValid v len = true ↔
      (v.toNat = 0 ∧ (len.toNat = 20 ∨ len.toNat = 32)) ∨
      (1 ≤ v.toNat ∧ v.toNat ≤ 16 ∧ 2 ≤ len.toNat ∧ len.toNat ≤ 40)

/-- A witness-version opcode decodes to its version: `OP_0` to 0, `OP_1`..`OP_16`
    (0x51..0x60) to 1..16, anything else to the error value 255. -/
def WitnessOpcode : Prop :=
  ∀ op : UInt8,
    (llbWitnessOpcodeToVersion op).toNat =
      if op.toNat = 0 then 0
      else if 81 ≤ op.toNat ∧ op.toNat ≤ 96 then op.toNat - 80
      else 255

/-- Legacy and SegWit v0 signature-hash types: exactly ALL, NONE, SINGLE (1, 2, 3),
    each optionally with ANYONECANPAY (+128). -/
def SighashType : Prop :=
  ∀ s : UInt32,
    llbSighashTypeValid s = true ↔
      s.toNat ∈ [1, 2, 3, 129, 130, 131]

/-- Taproot signature-hash types: the same six, plus DEFAULT (0). -/
def TaprootSighashType : Prop :=
  ∀ s : UInt8,
    llbTaprootSighashValid s = true ↔
      s.toNat ∈ [0, 1, 2, 3, 129, 130, 131]

/-! ## CompactSize -/

/-- A CompactSize prefix byte is accepted for a decoded value exactly when it is the
    prefix of the shortest encoding of that value. -/
def CompactSizeCanonical : Prop :=
  ∀ (tag : UInt8) (v : UInt64),
    llbVarIntPrefixIsCanonical tag v = true ↔
      (v.toNat ≤ 252 ∧ tag.toNat = v.toNat) ∨
      (253 ≤ v.toNat ∧ v.toNat ≤ 65535 ∧ tag.toNat = 253) ∨
      (65536 ≤ v.toNat ∧ v.toNat ≤ 4294967295 ∧ tag.toNat = 254) ∨
      (4294967296 ≤ v.toNat ∧ tag.toNat = 255)

/-! ## Buffers

A buffer argument is a map from an index to the element stored there (see section 7 of the
kernel). The statements below speak about the first `len` elements, as a list of numbers. -/

/-- The first `len` bytes of a read-only buffer. -/
def bytes (b : ConstBytes) (len : Nat) : List Nat :=
  (List.range len).map fun i => (b.get (UInt32.ofNat i)).toNat

/-! ## Dual UTXO (CVE-2020-14199) -/

/-- The witness UTXO and the output of the non-witness UTXO are accepted exactly when the
    amount is at most 21M BTC, both amounts are equal, and both scripts have the same
    length and the same bytes. -/
def DualUtxo : Prop :=
  ∀ (witAmount nonWitAmount : UInt64) (witSpk nonWitSpk : ConstBytes) (witLen nonWitLen : UInt32),
    llbCheckDualUtxo witAmount witSpk witLen nonWitAmount nonWitSpk nonWitLen = true ↔
      witAmount.toNat ≤ maxMoney ∧ witAmount.toNat = nonWitAmount.toNat ∧
      bytes witSpk witLen.toNat = bytes nonWitSpk nonWitLen.toNat

/-! ## CompactSize reader -/

/-- The CompactSize encoding of `v` (Bitcoin's variable-length integer): the shortest of the
    1, 3, 5 and 9 byte forms, little-endian after the tag byte. -/
def compactSize (v : Nat) : List Nat :=
  if v < 253 then [v]
  else if v < 65536 then [253, v % 256, v / 256]
  else if v < 4294967296 then [254, v % 256, v / 256 % 256, v / 65536 % 256, v / 16777216]
  else [255, v % 256, v / 256 % 256, v / 65536 % 256, v / 16777216 % 256, v / 4294967296 % 256,
        v / 1099511627776 % 256, v / 281474976710656 % 256, v / 72057594037927936]

/-- When the buffer starts with the encoding of some `v ≤ maxVal`, the reader returns
    `(number of bytes read) * 2^32 + v`, which is never `0`. In every other case (encoding
    not the shortest one, cut by the end of the buffer, or value above `maxVal`) it returns `0`. -/
def CompactSizeRead : Prop :=
  ∀ (buf : ConstBytes) (bufLen maxVal : UInt32),
    (∀ v : Nat, v ≤ maxVal.toNat → compactSize v <+: bytes buf bufLen.toNat →
      (llbReadCompactSizeChecked buf bufLen maxVal).toNat = (compactSize v).length * 2 ^ 32 + v) ∧
    ((¬ ∃ v : Nat, v ≤ maxVal.toNat ∧ compactSize v <+: bytes buf bufLen.toNat) →
      (llbReadCompactSizeChecked buf bufLen maxVal).toNat = 0)

/-! ## BIP-32 export path -/

/-- The first `len` words of a read-only buffer of 32-bit words. -/
def words (b : ConstU32s) (len : Nat) : List Nat :=
  (List.range len).map fun i => (b.get (UInt32.ofNat i)).toNat

/-- The hardened derivation step `n'`. -/
def hardened (n : Nat) : Nat := 2147483648 + n

/-- The paths whose public key may be exported without confirmation, for coin type `coin`
    (`0` mainnet, `1` testnet):
    * `m/4541509'/1112098098'` (used by Electrum to derive encryption keys);
    * `m/purpose'/coin'/account'/...` with purpose 44, 49, 84, 86, 87 or 45;
    * `m/48'/coin'/account'/scriptType'/...` with script type 1 or 2 (BIP-48);
    where `account ≤ 100` and no step after the listed ones is hardened. -/
def ExportPath (coin : Nat) (p : List Nat) : Prop :=
  p = [hardened 4541509, hardened 1112098098] ∨
  (∃ purpose account tail,
    p = hardened purpose :: hardened coin :: hardened account :: tail ∧
    purpose ∈ [44, 49, 84, 86, 87, 45] ∧ account ≤ 100 ∧ ∀ x ∈ tail, x < 2147483648) ∨
  (∃ account scriptType tail,
    p = hardened 48 :: hardened coin :: hardened account :: hardened scriptType :: tail ∧
    account ≤ 100 ∧ (scriptType = 1 ∨ scriptType = 2) ∧ ∀ x ∈ tail, x < 2147483648)

/-- A path is accepted exactly when it has at most 10 steps and is one of `ExportPath`. -/
def Bip32ExportPath : Prop :=
  ∀ (path : ConstU32s) (pathLen : UInt8) (coinType : UInt32),
    llbBip32CheckExportPath path pathLen coinType = true ↔
      pathLen.toNat ≤ 10 ∧ ExportPath coinType.toNat (words path pathLen.toNat)

/-! ## Merkle descent -/

/-- The split point of a tree of `s ≥ 2` leaves is the power of two `m` with `m < s ≤ 2 * m`
    (RFC 6962). -/
def MerkleSplit : Prop :=
  ∀ (s : UInt32) (e : Nat), 2 ^ e < s.toNat → s.toNat ≤ 2 * 2 ^ e →
    (largestPow2LtU32 s).toNat = 2 ^ e

/-- One step of the descent toward leaf `index` in a tree of `size` leaves, the state being
    `size * 2 ^ 32 + index`. A tree of at most one leaf does not move. Otherwise, with `m`
    the split point: the left subtree `(m, index)` when `index < m`, else the right subtree
    `(size - m, index - m)`. -/
def MerkleStep : Prop :=
  ∀ (st : UInt64) (size index : Nat), st.toNat = size * 2 ^ 32 + index → index < 2 ^ 32 →
    (size ≤ 1 → llbMerkleAdvanceState st = st) ∧
    ∀ e, 2 ^ e < size → size ≤ 2 * 2 ^ e →
      (llbMerkleAdvanceState st).toNat =
        if index < 2 ^ e then 2 ^ e * 2 ^ 32 + index
        else (size - 2 ^ e) * 2 ^ 32 + (index - 2 ^ e)

/-! ## BIP-370 locktime -/

/-- What one input requires: `(height, time)`, each optional. The input is given to the
    kernel as `(hasHeight, height, hasTime, time)`; a zero flag means "absent". -/
def lockReq (i : UInt8 × UInt32 × UInt8 × UInt32) : Option Nat × Option Nat :=
  (if i.1 = 0 then none else some i.2.1.toNat,
   if i.2.2.1 = 0 then none else some i.2.2.2.toNat)

/-- The kernel state after the inputs `ins`, fed one at a time from the initial state. -/
def locktimeRun (ins : List (UInt8 × UInt32 × UInt8 × UInt32)) : UInt64 :=
  ins.foldl (fun st i => llbPsbtLocktimeStep st i.1 i.2.1 i.2.2.1 i.2.2.2) llbPsbtLocktimeInit

/-- A height requirement is in `1 .. 499999999`; a time requirement is `≥ 500000000`. -/
def lockReqInRange (r : Option Nat × Option Nat) : Bool :=
  (match r.1 with
    | none => true
    | some h => decide (0 < h ∧ h < 500000000)) &&
  (match r.2 with
    | none => true
    | some t => decide (500000000 ≤ t))

def maxOf (l : List Nat) : Nat := l.foldl max 0

/-- An input accepts a height locktime unless it requires a time and no height. -/
def supportsHeight (r : Option Nat × Option Nat) : Bool := r.1.isSome || r.2.isNone

/-- An input accepts a time locktime unless it requires a height and no time. -/
def supportsTime (r : Option Nat × Option Nat) : Bool := r.2.isSome || r.1.isNone

/-- The transaction locktime of BIP-370, or `none` when there is none:
    * every requirement must be in range;
    * if no input requires anything, the fallback;
    * else if every input accepts a height, the largest required height;
    * else if every input accepts a time, the largest required time;
    * else there is no valid locktime. -/
def bip370Locktime (fallback : Nat) (reqs : List (Option Nat × Option Nat)) : Option Nat :=
  if !reqs.all lockReqInRange then none
  else if reqs.all (fun r => r.1.isNone && r.2.isNone) then some fallback
  else if reqs.all supportsHeight then some (maxOf (reqs.filterMap fun r => r.1))
  else if reqs.all supportsTime then some (maxOf (reqs.filterMap fun r => r.2))
  else none

/-- Running the kernel over a list of inputs and finalizing returns `2 ^ 32 + locktime`
    with the BIP-370 locktime of that list, and `0` exactly when there is none. -/
def PsbtLocktime : Prop :=
  ∀ (ins : List (UInt8 × UInt32 × UInt8 × UInt32)) (fallback : UInt32),
    (llbPsbtLocktimeFinalize (locktimeRun ins) fallback).toNat =
      match bip370Locktime fallback.toNat (ins.map lockReq) with
      | some v => 2 ^ 32 + v
      | none => 0

/-! ## Sorts -/

/-- The first `len` words of a buffer of 16-bit words. -/
def u16s (b : MutU16s) (len : Nat) : List Nat :=
  (List.range len).map fun i => (b.get (UInt32.ofNat i)).toNat

/-- `llb_sort_u16` leaves the first `count` words in non-decreasing order, as a permutation
    of what they were, and changes no word from `count` on. -/
def SortU16 : Prop :=
  ∀ (arr : MutU16s) (count : UInt32),
    (u16s (llbSortU16 arr count) count.toNat).Pairwise (· ≤ ·) ∧
    (u16s (llbSortU16 arr count) count.toNat).Perm (u16s arr count.toNat) ∧
    ∀ i : UInt32, count.toNat ≤ i.toNat → (llbSortU16 arr count).get i = arr.get i

/-- `a` is before or equal to `b`, comparing byte by byte from the first byte. -/
def lexLe : List Nat → List Nat → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => x < y ∨ (x = y ∧ lexLe xs ys)

/-- The first `count` records of `stride` bytes of a buffer. -/
def records (b : MutBytes) (count stride : Nat) : List (List Nat) :=
  (List.range count).map fun r =>
    (List.range stride).map fun k => (b.get (UInt32.ofNat (r * stride + k))).toNat

/-- `llb_sort_fixed_bytes` leaves the first `count` records of `stride` bytes in
    lexicographic order, as a permutation of what they were, and changes no byte after
    them. The records must fit in the 32-bit address space. -/
def SortFixedBytes : Prop :=
  ∀ (buf : MutBytes) (count stride : UInt32), count.toNat * stride.toNat ≤ 2 ^ 32 →
    (records (llbSortFixedBytes buf count stride) count.toNat stride.toNat).Pairwise lexLe ∧
    (records (llbSortFixedBytes buf count stride) count.toNat stride.toNat).Perm
      (records buf count.toNat stride.toNat) ∧
    ∀ i : UInt32, count.toNat * stride.toNat ≤ i.toNat →
      (llbSortFixedBytes buf count stride).get i = buf.get i

/-! ## Amount formatter -/

/-- The first `len` bytes of a buffer that is written. -/
def written (b : MutBytes) (len : Nat) : List Nat :=
  (List.range len).map fun i => (b.get (UInt32.ofNat i)).toNat

/-- An ASCII decimal digit. -/
def isDigit (c : Nat) : Bool := decide (48 ≤ c) && decide (c ≤ 57)

/-- The number written by a list of ASCII digits. -/
def digitsValue (l : List Nat) : Nat := l.foldl (fun acc c => 10 * acc + (c - 48)) 0

/-- Reads `<digits>[.<at most 8 digits>][ <ticker>]` as an amount in satoshis and a ticker. -/
def parseAmount (text : List Nat) : Option (Nat × List Nat) :=
  let int := text.takeWhile isDigit
  let afterInt := text.dropWhile isDigit
  let hasDot := decide (afterInt.head? = some 46)
  let frac := if hasDot then afterInt.tail.takeWhile isDigit else []
  let afterFrac := if hasDot then afterInt.tail.dropWhile isDigit else afterInt
  let sats := digitsValue int * 100000000 + digitsValue frac * 10 ^ (8 - frac.length)
  if int.isEmpty || decide (8 < frac.length) then none
  else if afterFrac.isEmpty then some (sats, [])
  else if decide (afterFrac.head? = some 32) then some (sats, afterFrac.tail)
  else none

/-- Format `amount` satoshis in `out`:
    * when `256 < tickerLen`, or the formatted string and its trailing NUL do not fit in
      `outCap` bytes, returns `0` and leaves `out` unchanged;
    * otherwise writes `<integer>[.<1..8 fractional digits>][ <ticker>]\0`, returns its
      byte length `len` (`1 ≤ len < outCap`), and leaves `out` past `len` unchanged;
    * the written string is canonical: the integer part has no leading `'0'` except `"0"`
      itself, the fractional part is omitted when zero with `padFrac8 = 0`, has 8 digits
      when `padFrac8 ≠ 0`, and has no trailing `'0'` when `padFrac8 = 0`. -/
def FormatSats : Prop :=
  ∀ (amount : UInt64) (ticker : ConstBytes) (tickerLen : UInt32) (padFrac8 : UInt8)
    (out : MutBytes) (outCap : UInt32),
    ((llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2 = 0 →
      (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).1 = out) ∧
    ((llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2 ≠ 0 →
      (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2.toNat < outCap.toNat ∧
      parseAmount (written (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).1
          (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2.toNat) =
        some (amount.toNat, bytes ticker tickerLen.toNat) ∧
      (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).1.get
          (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2 = 0 ∧
      ∀ i : UInt32,
        (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2.toNat < i.toNat →
          (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).1.get i = out.get i) ∧
    (tickerLen.toNat ≤ 256 → 22 + tickerLen.toNat < outCap.toNat →
      (llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap).2 ≠ 0)

/-- Everything this file states. `Proofs.KernelSpec.kernel_meets_spec` proves it. -/
def KernelSpec : Prop :=
  ValidAmount ∧ CheckedAdd ∧ CheckedSub ∧ SplitBtc ∧
  HardenedBit ∧ DepthLimits ∧
  SegwitProgram ∧ WitnessOpcode ∧ SighashType ∧ TaprootSighashType ∧
  CompactSizeCanonical ∧
  DualUtxo ∧
  CompactSizeRead ∧
  Bip32ExportPath ∧
  MerkleSplit ∧
  MerkleStep ∧
  PsbtLocktime ∧
  SortU16 ∧
  SortFixedBytes ∧
  FormatSats

end Spec

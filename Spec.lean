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
  MerkleStep

end Spec

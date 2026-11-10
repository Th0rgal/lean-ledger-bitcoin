namespace Spec

/-!
# `Spec.Basic` — Foundational Bitcoin & Ledger Primitives

Implementation-independent plain Lean 4 specifications for:
1. Satoshi amounts (`MAX_MONEY = 2_100_000_000_000_000`) and checked summation (`sumAmounts?`)
2. Fixed-width byte-slice predicates (`Bytes4`, `Bytes20`, `Bytes32`, `Bytes33`, `Bytes64`, `Bytes65`)
3. Little-endian / big-endian integer encodings (`encodeU16LE`, `encodeU32LE`, `encodeU64LE`, `encodeU32BE`)
4. Canonical Bitcoin CompactSize / VarInt encoding & total canonical decoder (`isCanonicalVarInt`, `decodeVarIntCanonical?`)
5. Network parameters (`Mainnet`, `Testnet`, `Regtest`, `Signet`)
6. Canonical Ledger error taxonomy (`SpecError`) and deterministic mappings to BOLOS status words and Vanadium `AppError`
-/

/-! ## 1. Satoshi Amounts & Overflow-Safe Arithmetic -/

/-- Number of satoshis per BTC (`10^8`). -/
def SATS_PER_BTC : UInt64 := 100_000_000

/-- Consensus maximum Bitcoin supply in satoshis (`21_000_000 * 100_000_000 = 2_100_000_000_000_000`). -/
def MAX_MONEY : UInt64 := 2_100_000_000_000_000

/-- Consensus validity predicate for a satoshi amount (`0 ≤ a ≤ MAX_MONEY`). -/
def ValidAmount (a : UInt64) : Prop :=
  a.toNat ≤ MAX_MONEY.toNat

instance (a : UInt64) : Decidable (ValidAmount a) :=
  inferInstanceAs (Decidable (a.toNat ≤ MAX_MONEY.toNat))

/-- Checked addition of two satoshi amounts, rejecting `UInt64` wraparound and sums `> MAX_MONEY`. -/
def addAmounts? (a b : UInt64) : Option UInt64 :=
  if a.toNat ≤ MAX_MONEY.toNat ∧ b.toNat ≤ MAX_MONEY.toNat ∧ a.toNat + b.toNat ≤ MAX_MONEY.toNat then
    some (UInt64.ofNat (a.toNat + b.toNat))
  else
    none

/-- Checked subtraction of two valid satoshi amounts (e.g. `fee = inputsTotal - outputsTotal`). -/
def subAmounts? (total part : UInt64) : Option UInt64 :=
  if total.toNat ≤ MAX_MONEY.toNat ∧ part.toNat ≤ total.toNat then
    some (UInt64.ofNat (total.toNat - part.toNat))
  else
    none

/-- Checked summation of a list of satoshi amounts.
    Returns `some total` iff every element satisfies `≤ MAX_MONEY`, no intermediate or final
    addition wraps `UInt64`, and the mathematical sum satisfies `≤ MAX_MONEY`. -/
def sumAmounts? : List UInt64 → Option UInt64
  | [] => some 0
  | x :: xs =>
      match sumAmounts? xs with
      | none => none
      | some rest => addAmounts? x rest

/-- Exact natural-number sum of `UInt64` values (without modular `2^64` wraparound). -/
def natAmountSum : List UInt64 → Nat
  | [] => 0
  | x :: xs => x.toNat + natAmountSum xs

theorem max_money_val : MAX_MONEY.toNat = 2_100_000_000_000_000 := rfl

theorem addAmounts?_eq_some_iff (a b total : UInt64) :
    addAmounts? a b = some total ↔
      a.toNat ≤ MAX_MONEY.toNat ∧
      b.toNat ≤ MAX_MONEY.toNat ∧
      a.toNat + b.toNat ≤ MAX_MONEY.toNat ∧
      total = UInt64.ofNat (a.toNat + b.toNat) := by
  unfold addAmounts?
  split
  · rename_i h
    rcases h with ⟨ha, hb, hab⟩
    simp only [Option.some.injEq]
    constructor
    · intro htot
      exact ⟨ha, hb, hab, htot.symm⟩
    · rintro ⟨_, _, _, rfl⟩
      rfl
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨ha, hb, hab, _⟩
    exact h ⟨ha, hb, hab⟩

theorem addAmounts?_toNat {a b total : UInt64} (h : addAmounts? a b = some total) :
    total.toNat = a.toNat + b.toNat ∧ total.toNat ≤ MAX_MONEY.toNat := by
  rw [addAmounts?_eq_some_iff] at h
  rcases h with ⟨_, _, hab, rfl⟩
  rw [max_money_val] at hab ⊢
  rw [UInt64.toNat_ofNat']
  constructor <;> omega

theorem sumAmounts?_sound :
    ∀ {xs : List UInt64} {total : UInt64},
      sumAmounts? xs = some total →
        total.toNat = natAmountSum xs ∧
        total.toNat ≤ MAX_MONEY.toNat ∧
        ∀ x ∈ xs, ValidAmount x
  | [], total, h => by
      simp [sumAmounts?] at h
      subst h
      simp [natAmountSum]
  | x :: xs, total, h => by
      simp only [sumAmounts?] at h
      cases hrest : sumAmounts? xs with
      | none => simp [hrest] at h
      | some rest =>
          simp only [hrest] at h
          obtain ⟨hrestSum, _, hrestValid⟩ := sumAmounts?_sound hrest
          have hadd := h
          rw [addAmounts?_eq_some_iff] at hadd
          rcases hadd with ⟨hx, _, _, _⟩
          obtain ⟨htotalEq, htotalLe⟩ := addAmounts?_toNat h
          refine ⟨?_, htotalLe, ?_⟩
          · simp [natAmountSum, htotalEq, hrestSum]
          · intro y hy
            cases hy with
            | head => exact hx
            | tail _ hmem => exact hrestValid y hmem

theorem sumAmounts?_complete :
    ∀ (xs : List UInt64),
      natAmountSum xs ≤ MAX_MONEY.toNat →
      ∃ total : UInt64, sumAmounts? xs = some total ∧ total.toNat = natAmountSum xs
  | [], _ => ⟨0, rfl, rfl⟩
  | x :: xs, hle => by
      simp only [natAmountSum] at hle
      have hrestLe : natAmountSum xs ≤ MAX_MONEY.toNat := by omega
      have hxLe : x.toNat ≤ MAX_MONEY.toNat := by omega
      obtain ⟨rest, hrest, hrestEq⟩ := sumAmounts?_complete xs hrestLe
      have hcomb : x.toNat + rest.toNat ≤ MAX_MONEY.toNat := by omega
      refine ⟨UInt64.ofNat (x.toNat + rest.toNat), ?_, ?_⟩
      · unfold sumAmounts?
        rw [hrest]
        unfold addAmounts?
        have hcond : x.toNat ≤ MAX_MONEY.toNat ∧ rest.toNat ≤ MAX_MONEY.toNat ∧ x.toNat + rest.toNat ≤ MAX_MONEY.toNat :=
          ⟨hxLe, by omega, hcomb⟩
        simp [hcond]
      · rw [max_money_val] at hcomb
        rw [UInt64.toNat_ofNat', natAmountSum]
        omega

/-- Any list whose exact natural sum exceeds `MAX_MONEY` (including `UInt64`-wrapping inputs) is rejected. -/
theorem sumAmounts?_rejects_overflow {xs : List UInt64}
    (hover : MAX_MONEY.toNat < natAmountSum xs) :
    sumAmounts? xs = none := by
  cases h : sumAmounts? xs with
  | none => rfl
  | some total =>
      obtain ⟨heq, hle, _⟩ := sumAmounts?_sound h
      omega

/-- Concrete `UInt64` wraparound attempt (`2^64 - 1 + 1 ≡ 0 (mod 2^64)`) is rejected. -/
theorem sumAmounts?_rejects_u64_wraparound :
    sumAmounts? [0xFFFFFFFFFFFFFFFF, 1] = none := by
  decide

/-- Concrete `MAX_MONEY + 1` supply overflow is rejected. -/
theorem sumAmounts?_rejects_above_max_money :
    sumAmounts? [MAX_MONEY, 1] = none := by
  decide

/-! ## 2. Fixed-Width Byte Predicates -/

/-- Predicate asserting a `ByteArray` has exact byte length `n`. -/
def BytesN (n : Nat) (bs : ByteArray) : Prop :=
  bs.size = n

instance (n : Nat) (bs : ByteArray) : Decidable (BytesN n bs) :=
  inferInstanceAs (Decidable (bs.size = n))

/-- 4-byte slice predicate (BIP-32 master/parent key fingerprint, version prefix, checksum). -/
def Bytes4 (bs : ByteArray) : Prop := BytesN 4 bs

/-- 20-byte slice predicate (`HASH160 = RIPEMD160(SHA256(·))` for P2PKH, P2SH, P2WPKH). -/
def Bytes20 (bs : ByteArray) : Prop := BytesN 20 bs

/-- 32-byte slice predicate (SHA-256 digest, txid, chain code, Taproot x-only pubkey, P2WSH). -/
def Bytes32 (bs : ByteArray) : Prop := BytesN 32 bs

/-- 33-byte slice predicate (SEC1 compressed secp256k1 public key `0x02`/`0x03 || X`). -/
def Bytes33 (bs : ByteArray) : Prop := BytesN 33 bs

/-- 64-byte slice predicate (BIP-340 Schnorr signature or compact ECDSA `(r, s)`). -/
def Bytes64 (bs : ByteArray) : Prop := BytesN 64 bs

/-- 65-byte slice predicate (SEC1 uncompressed secp256k1 public key `0x04 || X || Y` or recoverable sig). -/
def Bytes65 (bs : ByteArray) : Prop := BytesN 65 bs

instance (bs : ByteArray) : Decidable (Bytes4 bs) := inferInstanceAs (Decidable (bs.size = 4))
instance (bs : ByteArray) : Decidable (Bytes20 bs) := inferInstanceAs (Decidable (bs.size = 20))
instance (bs : ByteArray) : Decidable (Bytes32 bs) := inferInstanceAs (Decidable (bs.size = 32))
instance (bs : ByteArray) : Decidable (Bytes33 bs) := inferInstanceAs (Decidable (bs.size = 33))
instance (bs : ByteArray) : Decidable (Bytes64 bs) := inferInstanceAs (Decidable (bs.size = 64))
instance (bs : ByteArray) : Decidable (Bytes65 bs) := inferInstanceAs (Decidable (bs.size = 65))

/-! ## 3. Little-Endian & Big-Endian Integer Encodings -/

private theorem byteArray_eq_of_data_toList_eq {a b : ByteArray}
    (h : a.data.toList = b.data.toList) : a = b := by
  cases a
  cases b
  simp at h ⊢
  exact h

private theorem uint8_ofNat_mod256_toNat (n : Nat) :
    (UInt8.ofNat (n % 256)).toNat = n % 256 := by
  rw [UInt8.toNat_ofNat']
  omega

/-- Total 2-byte little-endian encoder for `UInt16`. -/
def encodeU16LEBytes (v : UInt16) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (v.toNat % 256),
    UInt8.ofNat ((v.toNat / 256) % 256)
  ]

/-- Total 2-byte little-endian decoder for `UInt16` (requires exact length 2). -/
def decodeU16LE? (bs : ByteArray) : Option UInt16 :=
  match bs.data.toList with
  | [b0, b1] => some (UInt16.ofNat (b0.toNat + 256 * b1.toNat))
  | _ => none

/-- Relational specification of 2-byte little-endian `UInt16` encoding. -/
def encodeU16LE (v : UInt16) (bs : ByteArray) : Prop :=
  ∃ b0 b1 : UInt8,
    bs = ByteArray.mk #[b0, b1] ∧
    b0.toNat + 256 * b1.toNat = v.toNat

/-- Total 4-byte little-endian encoder for `UInt32`. -/
def encodeU32LEBytes (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256)
  ]

/-- Total 4-byte little-endian decoder for `UInt32` (requires exact length 4). -/
def decodeU32LE? (bs : ByteArray) : Option UInt32 :=
  match bs.data.toList with
  | [b0, b1, b2, b3] =>
      some (UInt32.ofNat (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat))
  | _ => none

/-- Relational specification of 4-byte little-endian `UInt32` encoding. -/
def encodeU32LE (v : UInt32) (bs : ByteArray) : Prop :=
  ∃ b0 b1 b2 b3 : UInt8,
    bs = ByteArray.mk #[b0, b1, b2, b3] ∧
    b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat = v.toNat

/-- Total 8-byte little-endian encoder for `UInt64`. -/
def encodeU64LEBytes (v : UInt64) : ByteArray :=
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

/-- Total 8-byte little-endian decoder for `UInt64` (requires exact length 8). -/
def decodeU64LE? (bs : ByteArray) : Option UInt64 :=
  match bs.data.toList with
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
      some (UInt64.ofNat (
        b0.toNat +
        256 * b1.toNat +
        65536 * b2.toNat +
        16777216 * b3.toNat +
        4294967296 * b4.toNat +
        1099511627776 * b5.toNat +
        281474976710656 * b6.toNat +
        72057594037927936 * b7.toNat))
  | _ => none

/-- Relational specification of 8-byte little-endian `UInt64` encoding. -/
def encodeU64LE (v : UInt64) (bs : ByteArray) : Prop :=
  ∃ b0 b1 b2 b3 b4 b5 b6 b7 : UInt8,
    bs = ByteArray.mk #[b0, b1, b2, b3, b4, b5, b6, b7] ∧
    b0.toNat +
      256 * b1.toNat +
      65536 * b2.toNat +
      16777216 * b3.toNat +
      4294967296 * b4.toNat +
      1099511627776 * b5.toNat +
      281474976710656 * b6.toNat +
      72057594037927936 * b7.toNat = v.toNat

/-- Total 4-byte big-endian encoder for `UInt32` (used in BIP-32 paths, fingerprints, xpubs). -/
def encodeU32BEBytes (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat (n % 256)
  ]

/-- Total 4-byte big-endian decoder for `UInt32` (requires exact length 4). -/
def decodeU32BE? (bs : ByteArray) : Option UInt32 :=
  match bs.data.toList with
  | [b0, b1, b2, b3] =>
      some (UInt32.ofNat (16777216 * b0.toNat + 65536 * b1.toNat + 256 * b2.toNat + b3.toNat))
  | _ => none

/-- Relational specification of 4-byte big-endian `UInt32` encoding. -/
def encodeU32BE (v : UInt32) (bs : ByteArray) : Prop :=
  ∃ b0 b1 b2 b3 : UInt8,
    bs = ByteArray.mk #[b0, b1, b2, b3] ∧
    16777216 * b0.toNat + 65536 * b1.toNat + 256 * b2.toNat + b3.toNat = v.toNat

theorem encodeU16LEBytes_satisfies (v : UInt16) : encodeU16LE v (encodeU16LEBytes v) := by
  refine ⟨UInt8.ofNat (v.toNat % 256), UInt8.ofNat ((v.toNat / 256) % 256), rfl, ?_⟩
  have hv := v.toNat_lt
  repeat rw [uint8_ofNat_mod256_toNat]
  omega

theorem encodeU32LEBytes_satisfies (v : UInt32) : encodeU32LE v (encodeU32LEBytes v) := by
  refine ⟨
    UInt8.ofNat (v.toNat % 256),
    UInt8.ofNat ((v.toNat / 256) % 256),
    UInt8.ofNat ((v.toNat / 65536) % 256),
    UInt8.ofNat ((v.toNat / 16777216) % 256),
    rfl, ?_⟩
  have hv := v.toNat_lt
  repeat rw [uint8_ofNat_mod256_toNat]
  omega

theorem encodeU64LEBytes_satisfies (v : UInt64) : encodeU64LE v (encodeU64LEBytes v) := by
  refine ⟨
    UInt8.ofNat (v.toNat % 256),
    UInt8.ofNat ((v.toNat / 256) % 256),
    UInt8.ofNat ((v.toNat / 65536) % 256),
    UInt8.ofNat ((v.toNat / 16777216) % 256),
    UInt8.ofNat ((v.toNat / 4294967296) % 256),
    UInt8.ofNat ((v.toNat / 1099511627776) % 256),
    UInt8.ofNat ((v.toNat / 281474976710656) % 256),
    UInt8.ofNat ((v.toNat / 72057594037927936) % 256),
    rfl, ?_⟩
  have hv := v.toNat_lt
  repeat rw [uint8_ofNat_mod256_toNat]
  omega

theorem encodeU32BEBytes_satisfies (v : UInt32) : encodeU32BE v (encodeU32BEBytes v) := by
  refine ⟨
    UInt8.ofNat ((v.toNat / 16777216) % 256),
    UInt8.ofNat ((v.toNat / 65536) % 256),
    UInt8.ofNat ((v.toNat / 256) % 256),
    UInt8.ofNat (v.toNat % 256),
    rfl, ?_⟩
  have hv := v.toNat_lt
  repeat rw [uint8_ofNat_mod256_toNat]
  omega

theorem decodeU16LE?_roundtrip (v : UInt16) : decodeU16LE? (encodeU16LEBytes v) = some v := by
  obtain ⟨b0, b1, heq, hsum⟩ := encodeU16LEBytes_satisfies v
  rw [heq]
  simp [decodeU16LE?, hsum]

theorem decodeU32LE?_roundtrip (v : UInt32) : decodeU32LE? (encodeU32LEBytes v) = some v := by
  obtain ⟨b0, b1, b2, b3, heq, hsum⟩ := encodeU32LEBytes_satisfies v
  rw [heq]
  simp [decodeU32LE?, hsum]

theorem decodeU64LE?_roundtrip (v : UInt64) : decodeU64LE? (encodeU64LEBytes v) = some v := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, heq, hsum⟩ := encodeU64LEBytes_satisfies v
  rw [heq]
  simp [decodeU64LE?, hsum]

theorem decodeU32BE?_roundtrip (v : UInt32) : decodeU32BE? (encodeU32BEBytes v) = some v := by
  obtain ⟨b0, b1, b2, b3, heq, hsum⟩ := encodeU32BEBytes_satisfies v
  rw [heq]
  simp [decodeU32BE?, hsum]

/-! ## 4. Bitcoin CompactSize / VarInt Canonical Encoding & Decoder -/

/-- Relational specification of Bitcoin's **canonical (minimal)** CompactSize / VarInt encoding:
    - `0x00..0xFC`: 1 byte `[b0]`
    - `0xFD..0xFFFF`: 3 bytes `[0xFD, b0, b1]` (LE `u16`, strictly `≥ 0xFD`)
    - `0x10000..0xFFFFFFFF`: 5 bytes `[0xFE, b0, b1, b2, b3]` (LE `u32`, strictly `≥ 0x10000`)
    - `0x100000000..0xFFFFFFFFFFFFFFFF`: 9 bytes `[0xFF, b0..b7]` (LE `u64`, strictly `≥ 0x100000000`) -/
def isCanonicalVarInt (n : UInt64) (bs : ByteArray) : Prop :=
  (n.toNat ≤ 0xFC ∧
    ∃ b0 : UInt8, bs = ByteArray.mk #[b0] ∧ b0.toNat = n.toNat) ∨
  (0xFD ≤ n.toNat ∧ n.toNat ≤ 0xFFFF ∧
    ∃ b0 b1 : UInt8,
      bs = ByteArray.mk #[0xFD, b0, b1] ∧
      b0.toNat + 256 * b1.toNat = n.toNat) ∨
  (0x10000 ≤ n.toNat ∧ n.toNat ≤ 0xFFFFFFFF ∧
    ∃ b0 b1 b2 b3 : UInt8,
      bs = ByteArray.mk #[0xFE, b0, b1, b2, b3] ∧
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat = n.toNat) ∨
  (0x100000000 ≤ n.toNat ∧
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : UInt8,
      bs = ByteArray.mk #[0xFF, b0, b1, b2, b3, b4, b5, b6, b7] ∧
      b0.toNat +
        256 * b1.toNat +
        65536 * b2.toNat +
        16777216 * b3.toNat +
        4294967296 * b4.toNat +
        1099511627776 * b5.toNat +
        281474976710656 * b6.toNat +
        72057594037927936 * b7.toNat = n.toNat)

/-- Canonical CompactSize / VarInt encoder. -/
def encodeVarIntCanonical (n : UInt64) : ByteArray :=
  let v := n.toNat
  if v ≤ 0xFC then
    ByteArray.mk #[UInt8.ofNat v]
  else if v ≤ 0xFFFF then
    ByteArray.mk #[
      0xFD,
      UInt8.ofNat (v % 256),
      UInt8.ofNat ((v / 256) % 256)
    ]
  else if v ≤ 0xFFFFFFFF then
    ByteArray.mk #[
      0xFE,
      UInt8.ofNat (v % 256),
      UInt8.ofNat ((v / 256) % 256),
      UInt8.ofNat ((v / 65536) % 256),
      UInt8.ofNat ((v / 16777216) % 256)
    ]
  else
    ByteArray.mk #[
      0xFF,
      UInt8.ofNat (v % 256),
      UInt8.ofNat ((v / 256) % 256),
      UInt8.ofNat ((v / 65536) % 256),
      UInt8.ofNat ((v / 16777216) % 256),
      UInt8.ofNat ((v / 4294967296) % 256),
      UInt8.ofNat ((v / 1099511627776) % 256),
      UInt8.ofNat ((v / 281474976710656) % 256),
      UInt8.ofNat ((v / 72057594037927936) % 256)
    ]

/-- Total canonical CompactSize / VarInt decoder over an exact byte slice.
    Rejects empty/truncated slices, trailing bytes, and non-minimal encodings
    (such as `0xFD 0xFC 0x00` for `252`). -/
def decodeVarIntCanonical? (bs : ByteArray) : Option UInt64 :=
  match bs.data.toList with
  | [b0] =>
      if b0.toNat ≤ 0xFC then
        some (UInt64.ofNat b0.toNat)
      else
        none
  | [tag, b0, b1] =>
      if tag = 0xFD then
        let val := b0.toNat + 256 * b1.toNat
        if 0xFD ≤ val then
          some (UInt64.ofNat val)
        else
          none
      else
        none
  | [tag, b0, b1, b2, b3] =>
      if tag = 0xFE then
        let val := b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat
        if 0x10000 ≤ val then
          some (UInt64.ofNat val)
        else
          none
      else
        none
  | [tag, b0, b1, b2, b3, b4, b5, b6, b7] =>
      if tag = 0xFF then
        let val :=
          b0.toNat +
          256 * b1.toNat +
          65536 * b2.toNat +
          16777216 * b3.toNat +
          4294967296 * b4.toNat +
          1099511627776 * b5.toNat +
          281474976710656 * b6.toNat +
          72057594037927936 * b7.toNat
        if 0x100000000 ≤ val then
          some (UInt64.ofNat val)
        else
          none
      else
        none
  | _ => none

/-- Streaming canonical CompactSize / VarInt prefix decoder returning `(value, remainingBytes)`.
    Rejects truncated inputs and non-minimal encodings. -/
def decodeVarIntCanonicalPrefix? (bs : ByteArray) : Option (UInt64 × ByteArray) :=
  match bs.data.toList with
  | [] => none
  | tag :: _ =>
      let needed :=
        if tag.toNat ≤ 0xFC then 1
        else if tag = 0xFD then 3
        else if tag = 0xFE then 5
        else 9
      if bs.size < needed then
        none
      else
        let head := bs.extract 0 needed
        let tail := bs.extract needed bs.size
        match decodeVarIntCanonical? head with
        | some v => some (v, tail)
        | none => none

theorem encodeVarIntCanonical_isCanonical (n : UInt64) :
    isCanonicalVarInt n (encodeVarIntCanonical n) := by
  unfold encodeVarIntCanonical
  have hnMax := n.toNat_lt
  by_cases hfc : n.toNat ≤ 0xFC
  · simp only [hfc, ↓reduceIte]
    left
    refine ⟨hfc, UInt8.ofNat n.toNat, rfl, ?_⟩
    rw [UInt8.toNat_ofNat']
    omega
  · simp only [hfc, ↓reduceIte]
    by_cases h16 : n.toNat ≤ 0xFFFF
    · simp only [h16, ↓reduceIte]
      right; left
      refine ⟨by omega, h16, UInt8.ofNat (n.toNat % 256), UInt8.ofNat ((n.toNat / 256) % 256), rfl, ?_⟩
      repeat rw [uint8_ofNat_mod256_toNat]
      omega
    · simp only [h16, ↓reduceIte]
      by_cases h32 : n.toNat ≤ 0xFFFFFFFF
      · simp only [h32, ↓reduceIte]
        right; right; left
        refine ⟨by omega, h32,
          UInt8.ofNat (n.toNat % 256),
          UInt8.ofNat ((n.toNat / 256) % 256),
          UInt8.ofNat ((n.toNat / 65536) % 256),
          UInt8.ofNat ((n.toNat / 16777216) % 256),
          rfl, ?_⟩
        repeat rw [uint8_ofNat_mod256_toNat]
        omega
      · simp only [h32, ↓reduceIte]
        right; right; right
        refine ⟨by omega,
          UInt8.ofNat (n.toNat % 256),
          UInt8.ofNat ((n.toNat / 256) % 256),
          UInt8.ofNat ((n.toNat / 65536) % 256),
          UInt8.ofNat ((n.toNat / 16777216) % 256),
          UInt8.ofNat ((n.toNat / 4294967296) % 256),
          UInt8.ofNat ((n.toNat / 1099511627776) % 256),
          UInt8.ofNat ((n.toNat / 281474976710656) % 256),
          UInt8.ofNat ((n.toNat / 72057594037927936) % 256),
          rfl, ?_⟩
        repeat rw [uint8_ofNat_mod256_toNat]
        omega

theorem decodeVarIntCanonical_of_isCanonical {n : UInt64} {bs : ByteArray}
    (h : isCanonicalVarInt n bs) :
    decodeVarIntCanonical? bs = some n := by
  rcases h with
    ⟨hfc, b0, rfl, hb0⟩ |
    ⟨hlo, _, b0, b1, rfl, hsum⟩ |
    ⟨hlo, _, b0, b1, b2, b3, rfl, hsum⟩ |
    ⟨hlo, b0, b1, b2, b3, b4, b5, b6, b7, rfl, hsum⟩
  · simp [decodeVarIntCanonical?, hb0, hfc]
  · simp [decodeVarIntCanonical?, hsum, hlo]
  · simp [decodeVarIntCanonical?, hsum, hlo]
  · simp [decodeVarIntCanonical?, hsum, hlo]

theorem isCanonicalVarInt_of_decodeVarIntCanonical {bs : ByteArray} {n : UInt64}
    (h : decodeVarIntCanonical? bs = some n) :
    isCanonicalVarInt n bs := by
  unfold decodeVarIntCanonical? at h
  match hlist : bs.data.toList with
  | [] =>
      rw [hlist] at h
      simp at h
  | [b0] =>
      rw [hlist] at h
      simp only at h
      split at h
      · rename_i hb0
        simp only [Option.some.injEq] at h
        subst h
        have hlt0 := b0.toNat_lt
        have htoNat : (UInt64.ofNat b0.toNat).toNat = b0.toNat := by
          rw [UInt64.toNat_ofNat']
          omega
        left
        refine ⟨by omega, b0, byteArray_eq_of_data_toList_eq hlist, htoNat.symm⟩
      · simp at h
  | [b0, b1] =>
      rw [hlist] at h
      simp at h
  | [tag, b0, b1] =>
      rw [hlist] at h
      simp only at h
      split at h
      · rename_i htag
        subst htag
        split at h
        · rename_i hmin
          simp only [Option.some.injEq] at h
          subst h
          have l0 := b0.toNat_lt
          have l1 := b1.toNat_lt
          have htoNat : (UInt64.ofNat (b0.toNat + 256 * b1.toNat)).toNat = b0.toNat + 256 * b1.toNat := by
            rw [UInt64.toNat_ofNat']
            omega
          right; left
          refine ⟨by omega, by omega, b0, b1, byteArray_eq_of_data_toList_eq hlist, htoNat.symm⟩
        · simp at h
      · simp at h
  | [b0, b1, b2, b3] =>
      rw [hlist] at h
      simp at h
  | [tag, b0, b1, b2, b3] =>
      rw [hlist] at h
      simp only at h
      split at h
      · rename_i htag
        subst htag
        split at h
        · rename_i hmin
          simp only [Option.some.injEq] at h
          subst h
          have l0 := b0.toNat_lt
          have l1 := b1.toNat_lt
          have l2 := b2.toNat_lt
          have l3 := b3.toNat_lt
          have htoNat :
              (UInt64.ofNat (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat)).toNat =
                b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
            rw [UInt64.toNat_ofNat']
            omega
          right; right; left
          refine ⟨by omega, by omega, b0, b1, b2, b3, byteArray_eq_of_data_toList_eq hlist, htoNat.symm⟩
        · simp at h
      · simp at h
  | [b0, b1, b2, b3, b4, b5] =>
      rw [hlist] at h
      simp at h
  | [b0, b1, b2, b3, b4, b5, b6] =>
      rw [hlist] at h
      simp at h
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
      rw [hlist] at h
      simp at h
  | [tag, b0, b1, b2, b3, b4, b5, b6, b7] =>
      rw [hlist] at h
      simp only at h
      split at h
      · rename_i htag
        subst htag
        split at h
        · rename_i hmin
          simp only [Option.some.injEq] at h
          subst h
          have l0 := b0.toNat_lt
          have l1 := b1.toNat_lt
          have l2 := b2.toNat_lt
          have l3 := b3.toNat_lt
          have l4 := b4.toNat_lt
          have l5 := b5.toNat_lt
          have l6 := b6.toNat_lt
          have l7 := b7.toNat_lt
          have htoNat :
              (UInt64.ofNat (
                b0.toNat +
                256 * b1.toNat +
                65536 * b2.toNat +
                16777216 * b3.toNat +
                4294967296 * b4.toNat +
                1099511627776 * b5.toNat +
                281474976710656 * b6.toNat +
                72057594037927936 * b7.toNat)).toNat =
                b0.toNat +
                256 * b1.toNat +
                65536 * b2.toNat +
                16777216 * b3.toNat +
                4294967296 * b4.toNat +
                1099511627776 * b5.toNat +
                281474976710656 * b6.toNat +
                72057594037927936 * b7.toNat := by
            rw [UInt64.toNat_ofNat']
            omega
          right; right; right
          refine ⟨by omega, b0, b1, b2, b3, b4, b5, b6, b7,
            byteArray_eq_of_data_toList_eq hlist, htoNat.symm⟩
        · simp at h
      · simp at h
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
      rw [hlist] at h
      simp at h

/-- Exact soundness & completeness equivalence between `decodeVarIntCanonical?` and `isCanonicalVarInt`. -/
theorem decodeVarIntCanonical_iff (bs : ByteArray) (n : UInt64) :
    decodeVarIntCanonical? bs = some n ↔ isCanonicalVarInt n bs :=
  ⟨isCanonicalVarInt_of_decodeVarIntCanonical, decodeVarIntCanonical_of_isCanonical⟩

/-- Canonical VarInt roundtrip theorem: `decodeVarIntCanonical? (encodeVarIntCanonical n) = some n`. -/
theorem decodeVarIntCanonical_roundtrip (n : UInt64) :
    decodeVarIntCanonical? (encodeVarIntCanonical n) = some n :=
  decodeVarIntCanonical_of_isCanonical (encodeVarIntCanonical_isCanonical n)

/-- Canonical VarInt value injectivity on byte slices: a byte slice encodes at most one `UInt64`. -/
theorem isCanonicalVarInt_injective_value {n1 n2 : UInt64} {bs : ByteArray}
    (h1 : isCanonicalVarInt n1 bs) (h2 : isCanonicalVarInt n2 bs) :
    n1 = n2 := by
  have hd1 := decodeVarIntCanonical_of_isCanonical h1
  have hd2 := decodeVarIntCanonical_of_isCanonical h2
  rw [hd1] at hd2
  exact Option.some.inj hd2

/-- Canonical VarInt representation uniqueness: each `UInt64` has a unique canonical `ByteArray`. -/
theorem isCanonicalVarInt_unique_bytes {n : UInt64} {bs1 bs2 : ByteArray}
    (h1 : isCanonicalVarInt n bs1) (h2 : isCanonicalVarInt n bs2) :
    bs1 = bs2 := by
  suffices hcanon : ∀ bs, isCanonicalVarInt n bs → bs = encodeVarIntCanonical n by
    rw [hcanon bs1 h1, hcanon bs2 h2]
  intro bs hbs
  unfold encodeVarIntCanonical
  rcases hbs with
    ⟨hfc, b0, rfl, hb0⟩ |
    ⟨hlo, hhi, b0, b1, rfl, hsum⟩ |
    ⟨hlo, hhi, b0, b1, b2, b3, rfl, hsum⟩ |
    ⟨hlo, b0, b1, b2, b3, b4, b5, b6, b7, rfl, hsum⟩
  · simp only [hfc, ↓reduceIte]
    apply congrArg ByteArray.mk
    apply congrArg (fun x => #[x])
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat']
    omega
  · have hnotfc : ¬ n.toNat ≤ 0xFC := by omega
    simp only [hnotfc, ↓reduceIte, hhi]
    have l0 := b0.toNat_lt
    have l1 := b1.toNat_lt
    have e0 : b0 = UInt8.ofNat (n.toNat % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e1 : b1 = UInt8.ofNat ((n.toNat / 256) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    rw [e0, e1]
  · have hnotfc : ¬ n.toNat ≤ 0xFC := by omega
    have hnot16 : ¬ n.toNat ≤ 0xFFFF := by omega
    simp only [hnotfc, hnot16, ↓reduceIte, hhi]
    have l0 := b0.toNat_lt
    have l1 := b1.toNat_lt
    have l2 := b2.toNat_lt
    have l3 := b3.toNat_lt
    have e0 : b0 = UInt8.ofNat (n.toNat % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e1 : b1 = UInt8.ofNat ((n.toNat / 256) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e2 : b2 = UInt8.ofNat ((n.toNat / 65536) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e3 : b3 = UInt8.ofNat ((n.toNat / 16777216) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    rw [e0, e1, e2, e3]
  · have hnotfc : ¬ n.toNat ≤ 0xFC := by omega
    have hnot16 : ¬ n.toNat ≤ 0xFFFF := by omega
    have hnot32 : ¬ n.toNat ≤ 0xFFFFFFFF := by omega
    simp only [hnotfc, hnot16, hnot32, ↓reduceIte]
    have l0 := b0.toNat_lt
    have l1 := b1.toNat_lt
    have l2 := b2.toNat_lt
    have l3 := b3.toNat_lt
    have l4 := b4.toNat_lt
    have l5 := b5.toNat_lt
    have l6 := b6.toNat_lt
    have l7 := b7.toNat_lt
    have e0 : b0 = UInt8.ofNat (n.toNat % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e1 : b1 = UInt8.ofNat ((n.toNat / 256) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e2 : b2 = UInt8.ofNat ((n.toNat / 65536) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e3 : b3 = UInt8.ofNat ((n.toNat / 16777216) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e4 : b4 = UInt8.ofNat ((n.toNat / 4294967296) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e5 : b5 = UInt8.ofNat ((n.toNat / 1099511627776) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e6 : b6 = UInt8.ofNat ((n.toNat / 281474976710656) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    have e7 : b7 = UInt8.ofNat ((n.toNat / 72057594037927936) % 256) := by
      apply UInt8.toNat_inj.mp; rw [uint8_ofNat_mod256_toNat]; omega
    rw [e0, e1, e2, e3, e4, e5, e6, e7]

/-- Canonical VarInt encoder injectivity: `encodeVarIntCanonical n1 = encodeVarIntCanonical n2 → n1 = n2`. -/
theorem encodeVarIntCanonical_injective {n1 n2 : UInt64}
    (heq : encodeVarIntCanonical n1 = encodeVarIntCanonical n2) :
    n1 = n2 := by
  have h1 := encodeVarIntCanonical_isCanonical n1
  rw [heq] at h1
  exact isCanonicalVarInt_injective_value h1 (encodeVarIntCanonical_isCanonical n2)

/-- Non-minimal CompactSize `0xFD 0xFC 0x00` (encoding `252` with a 3-byte `0xFD` prefix) is rejected. -/
theorem decodeVarIntCanonical_rejects_fd_fc :
    decodeVarIntCanonical? (ByteArray.mk #[0xFD, 0xFC, 0x00]) = none := by
  decide

/-- General non-minimal 3-byte `0xFD` CompactSize rejection (`val < 0xFD` is always rejected). -/
theorem decodeVarIntCanonical_rejects_nonminimal_u16 (b0 b1 : UInt8)
    (hnonmin : b0.toNat + 256 * b1.toNat < 0xFD) :
    decodeVarIntCanonical? (ByteArray.mk #[0xFD, b0, b1]) = none := by
  have hnot : ¬ 0xFD ≤ b0.toNat + 256 * b1.toNat := by omega
  simp [decodeVarIntCanonical?, hnot]

/-- General non-minimal 5-byte `0xFE` CompactSize rejection (`val < 0x10000` is always rejected). -/
theorem decodeVarIntCanonical_rejects_nonminimal_u32 (b0 b1 b2 b3 : UInt8)
    (hnonmin : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 0x10000) :
    decodeVarIntCanonical? (ByteArray.mk #[0xFE, b0, b1, b2, b3]) = none := by
  have hnot : ¬ 0x10000 ≤ b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by omega
  simp [decodeVarIntCanonical?, hnot]

/-- General non-minimal 9-byte `0xFF` CompactSize rejection (`val < 0x100000000` is always rejected). -/
theorem decodeVarIntCanonical_rejects_nonminimal_u64 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8)
    (hnonmin :
      b0.toNat +
      256 * b1.toNat +
      65536 * b2.toNat +
      16777216 * b3.toNat +
      4294967296 * b4.toNat +
      1099511627776 * b5.toNat +
      281474976710656 * b6.toNat +
      72057594037927936 * b7.toNat < 0x100000000) :
    decodeVarIntCanonical? (ByteArray.mk #[0xFF, b0, b1, b2, b3, b4, b5, b6, b7]) = none := by
  have hnot :
    ¬ 0x100000000 ≤
      b0.toNat +
      256 * b1.toNat +
      65536 * b2.toNat +
      16777216 * b3.toNat +
      4294967296 * b4.toNat +
      1099511627776 * b5.toNat +
      281474976710656 * b6.toNat +
      72057594037927936 * b7.toNat := by omega
  simp [decodeVarIntCanonical?, hnot]

/-! ## 5. Bitcoin Network Parameters -/

/-- Bitcoin network selector across Mainnet, Testnet (v3/v4), Regtest, and Signet. -/
inductive Network where
  | mainnet
  | testnet
  | regtest
  | signet
  deriving Repr, DecidableEq, Inhabited

/-- BIP-32 `xpub` version magic on Bitcoin Mainnet (`0x0488B21E`). -/
def XPUB_VERSION_MAINNET : UInt32 := 0x0488B21E

/-- BIP-32 `tpub` version magic on Testnet / Regtest / Signet (`0x043587CF`). -/
def XPUB_VERSION_TESTNET : UInt32 := 0x043587CF

/-- Consensus and address/key-encoding parameters associated with a `Network`. -/
structure NetworkParams where
  /-- Base58Check version byte for P2PKH (`0x00` mainnet, `0x6F` test networks). -/
  p2pkhVersion : UInt8
  /-- Base58Check version byte for P2SH (`0x05` mainnet, `0xC4` test networks). -/
  p2shVersion : UInt8
  /-- BIP-173 / BIP-350 SegWit Bech32(m) human-readable part (`"bc"`, `"tb"`, `"bcrt"`). -/
  bech32Hrp : String
  /-- BIP-352 Silent Payment Bech32m human-readable part (`"sp"`, `"tsp"`). -/
  silentPaymentHrp : String
  /-- BIP-32 serialized extended public key 4-byte version prefix (`0x0488B21E` vs `0x043587CF`). -/
  xpubVersion : UInt32
  /-- Unhardened BIP-44 coin type index (`0` on Mainnet, `1` on Testnet/Regtest/Signet). -/
  bip44CoinType : UInt32
  /-- Hardened BIP-44 coin type step (`0'` = `0x80000000` vs `1'` = `0x80000001`). -/
  bip44CoinTypeHardened : UInt32
  deriving Repr, DecidableEq, Inhabited

/-- Canonical parameter table for `Mainnet`, `Testnet`, `Regtest`, and `Signet`. -/
def Network.params : Network → NetworkParams
  | .mainnet =>
      { p2pkhVersion := 0x00
        p2shVersion := 0x05
        bech32Hrp := "bc"
        silentPaymentHrp := "sp"
        xpubVersion := XPUB_VERSION_MAINNET
        bip44CoinType := 0
        bip44CoinTypeHardened := 0x80000000 }
  | .testnet =>
      { p2pkhVersion := 0x6F
        p2shVersion := 0xC4
        bech32Hrp := "tb"
        silentPaymentHrp := "tsp"
        xpubVersion := XPUB_VERSION_TESTNET
        bip44CoinType := 1
        bip44CoinTypeHardened := 0x80000001 }
  | .regtest =>
      { p2pkhVersion := 0x6F
        p2shVersion := 0xC4
        bech32Hrp := "bcrt"
        silentPaymentHrp := "tsp"
        xpubVersion := XPUB_VERSION_TESTNET
        bip44CoinType := 1
        bip44CoinTypeHardened := 0x80000001 }
  | .signet =>
      { p2pkhVersion := 0x6F
        p2shVersion := 0xC4
        bech32Hrp := "tb"
        silentPaymentHrp := "tsp"
        xpubVersion := XPUB_VERSION_TESTNET
        bip44CoinType := 1
        bip44CoinTypeHardened := 0x80000001 }

/-! ## 6. Canonical Ledger Error Taxonomy & Reference Mappings -/

/-- BOLOS ISO-7816 / application APDU status words (`app-bitcoin/src/boilerplate/sw.h` & `src/error_codes.h`). -/
inductive BolosStatusWord where
  | swWrongLength                -- 0x6700 (ISO-7816 SWO_WRONG_LENGTH)
  | swSecurityStatusNotSatisfied -- 0x6982
  | swDeny                       -- 0x6985
  | swIncorrectData              -- 0x6A80
  | swNotSupported               -- 0x6A82
  | swWrongP1P2                  -- 0x6A86
  | swWrongDataLength            -- 0x6A87
  | swFailSwap                   -- 0x6B00
  | swInsNotSupported            -- 0x6D00
  | swClaNotSupported            -- 0x6E00
  | swWrongResponseLength        -- 0xB000
  | swDisplayBip32PathFail       -- 0xB001 (legacy BOLOS boilerplate app range 0xB000..0xB008)
  | swDisplayAddressFail         -- 0xB002
  | swDisplayAmountFail          -- 0xB003
  | swWrongTxLength              -- 0xB004
  | swTxParsingFail              -- 0xB005
  | swTxHashFail                 -- 0xB006
  | swBadState                   -- 0xB007
  | swSignatureFail              -- 0xB008
  | swInterruptedExecution       -- 0xE000 (client-command continuation, non-success terminal SW)
  | swOk                         -- 0x9000
  deriving Repr, DecidableEq, Inhabited

/-- Wire `UInt16` status-word encoding for `BolosStatusWord`. -/
def BolosStatusWord.toUInt16 : BolosStatusWord → UInt16
  | .swWrongLength                => 0x6700
  | .swSecurityStatusNotSatisfied => 0x6982
  | .swDeny                       => 0x6985
  | .swIncorrectData              => 0x6A80
  | .swNotSupported               => 0x6A82
  | .swWrongP1P2                  => 0x6A86
  | .swWrongDataLength            => 0x6A87
  | .swFailSwap                   => 0x6B00
  | .swInsNotSupported            => 0x6D00
  | .swClaNotSupported            => 0x6E00
  | .swWrongResponseLength        => 0xB000
  | .swDisplayBip32PathFail       => 0xB001
  | .swDisplayAddressFail         => 0xB002
  | .swDisplayAmountFail          => 0xB003
  | .swWrongTxLength              => 0xB004
  | .swTxParsingFail              => 0xB005
  | .swTxHashFail                 => 0xB006
  | .swBadState                   => 0xB007
  | .swSignatureFail              => 0xB008
  | .swInterruptedExecution       => 0xE000
  | .swOk                         => 0x9000

/-- Partial decoder from a 16-bit APDU status word to `BolosStatusWord`. -/
def BolosStatusWord.fromUInt16? : UInt16 → Option BolosStatusWord
  | 0x6700 => some .swWrongLength
  | 0x6982 => some .swSecurityStatusNotSatisfied
  | 0x6985 => some .swDeny
  | 0x6A80 => some .swIncorrectData
  | 0x6A82 => some .swNotSupported
  | 0x6A86 => some .swWrongP1P2
  | 0x6A87 => some .swWrongDataLength
  | 0x6B00 => some .swFailSwap
  | 0x6D00 => some .swInsNotSupported
  | 0x6E00 => some .swClaNotSupported
  | 0xB000 => some .swWrongResponseLength
  | 0xB001 => some .swDisplayBip32PathFail
  | 0xB002 => some .swDisplayAddressFail
  | 0xB003 => some .swDisplayAmountFail
  | 0xB004 => some .swWrongTxLength
  | 0xB005 => some .swTxParsingFail
  | 0xB006 => some .swTxHashFail
  | 0xB007 => some .swBadState
  | 0xB008 => some .swSignatureFail
  | 0xE000 => some .swInterruptedExecution
  | 0x9000 => some .swOk
  | _      => none

theorem BolosStatusWord.fromUInt16?_toUInt16 (sw : BolosStatusWord) :
    BolosStatusWord.fromUInt16? sw.toUInt16 = some sw := by
  cases sw <;> rfl

/-- Vanadium Bitcoin V-App CBOR error enum (`vanadium/apps/bitcoin/common/src/errors.rs`, `#[n(0..58)]`). -/
inductive AppError where
  | invalidRequest                 -- #[n(0)]
  | unexpectedMessage              -- #[n(1)]
  | requestDecodeFailed            -- #[n(2)]
  | responseEncodeFailed           -- #[n(3)]
  | rawRequestFailed               -- #[n(4)]
  | sendBufferFailed               -- #[n(5)]
  | receiveBufferFailed            -- #[n(6)]
  | storeGetFailed                 -- #[n(7)]
  | storeSetFailed                 -- #[n(8)]
  | derivationPathTooLong          -- #[n(9)]
  | masterFingerprintFailed        -- #[n(10)]
  | deriveHdNodeFailed             -- #[n(11)]
  | pubkeyFromSliceFailed          -- #[n(12)]
  | xpubSliceFailed                -- #[n(13)]
  | xpubDecodeFailed               -- #[n(14)]
  | residentKeyInvalidIndex        -- #[n(15)]
  | residentKeyDeriveFailed        -- #[n(16)]
  | userRejected                   -- #[n(17)]
  | accountConversionFailed        -- #[n(18)]
  | accountDecodeFailed            -- #[n(19)]
  | accountInvalidHmac             -- #[n(20)]
  | accountUnsupportedType         -- #[n(21)]
  | accountXpubDerivationFailed    -- #[n(22)]
  | accountResidentKeyUnsupported  -- #[n(23)]
  | accountSpPubkeyNotAllowed      -- #[n(24)]
  | accountCoordinatesMismatch     -- #[n(25)]
  | addressInvalidIndex            -- #[n(26)]
  | addressNotSupported            -- #[n(27)]
  | psbtParseFailed                -- #[n(28)]
  | psbtPrevoutVerifyFailed        -- #[n(29)]
  | psbtMissingTxData              -- #[n(30)]
  | psbtUnsupportedInput           -- #[n(31)]
  | psbtSignFailed                -- #[n(32)]
  | psbtTooManyAccounts            -- #[n(33)]
  | psbtOutputsExceedInputs        -- #[n(34)]
  | psbtNoInputs                   -- #[n(35)]
  | psbtNoSignableInput            -- #[n(36)]
  | psbtMissingSighash             -- #[n(37)]
  | psbtUnsupportedSighash         -- #[n(38)]
  | psbtTaprootKeyDerivFailed      -- #[n(39)]
  | psbtTaprootTweakFailed         -- #[n(40)]
  | psbtSchnorrSignFailed          -- #[n(41)]
  | psbtEcdsaSignFailed            -- #[n(42)]
  | psbtSigFromSliceFailed         -- #[n(43)]
  | addressFromScriptFailed        -- #[n(44)]
  | sighashComputeFailed           -- #[n(45)]
  | invalidCoordinates             -- #[n(46)]
  | messageTooLong                 -- #[n(47)]
  | messageSigningFailed          -- #[n(48)]
  | identityInvalidIndex           -- #[n(49)]
  | identityDerivationFailed      -- #[n(50)]
  | identitySigningFailed          -- #[n(51)]
  | spKeyDerivationFailed          -- #[n(52)]
  | spAddressFormatFailed          -- #[n(53)]
  | spOutputCheckFailed            -- #[n(54)]
  | silentPaymentDuplicateAccount  -- #[n(55)]
  | silentPaymentMixedInputs       -- #[n(56)]
  | silentPaymentWrongNetwork      -- #[n(57)]
  | silentPaymentChangeLabel       -- #[n(58)]
  deriving Repr, DecidableEq, Inhabited

/-- CBOR `#[n(...)]` discriminant of Vanadium's `common::errors::Error` (`AppError`). -/
def AppError.toCborCode : AppError → Nat
  | .invalidRequest                => 0
  | .unexpectedMessage             => 1
  | .requestDecodeFailed           => 2
  | .responseEncodeFailed          => 3
  | .rawRequestFailed              => 4
  | .sendBufferFailed              => 5
  | .receiveBufferFailed           => 6
  | .storeGetFailed                => 7
  | .storeSetFailed                => 8
  | .derivationPathTooLong         => 9
  | .masterFingerprintFailed       => 10
  | .deriveHdNodeFailed            => 11
  | .pubkeyFromSliceFailed         => 12
  | .xpubSliceFailed               => 13
  | .xpubDecodeFailed              => 14
  | .residentKeyInvalidIndex       => 15
  | .residentKeyDeriveFailed       => 16
  | .userRejected                  => 17
  | .accountConversionFailed       => 18
  | .accountDecodeFailed           => 19
  | .accountInvalidHmac            => 20
  | .accountUnsupportedType        => 21
  | .accountXpubDerivationFailed   => 22
  | .accountResidentKeyUnsupported => 23
  | .accountSpPubkeyNotAllowed     => 24
  | .accountCoordinatesMismatch    => 25
  | .addressInvalidIndex           => 26
  | .addressNotSupported           => 27
  | .psbtParseFailed               => 28
  | .psbtPrevoutVerifyFailed       => 29
  | .psbtMissingTxData             => 30
  | .psbtUnsupportedInput          => 31
  | .psbtSignFailed                => 32
  | .psbtTooManyAccounts           => 33
  | .psbtOutputsExceedInputs       => 34
  | .psbtNoInputs                  => 35
  | .psbtNoSignableInput           => 36
  | .psbtMissingSighash            => 37
  | .psbtUnsupportedSighash        => 38
  | .psbtTaprootKeyDerivFailed     => 39
  | .psbtTaprootTweakFailed        => 40
  | .psbtSchnorrSignFailed         => 41
  | .psbtEcdsaSignFailed           => 42
  | .psbtSigFromSliceFailed        => 43
  | .addressFromScriptFailed       => 44
  | .sighashComputeFailed          => 45
  | .invalidCoordinates            => 46
  | .messageTooLong                => 47
  | .messageSigningFailed          => 48
  | .identityInvalidIndex          => 49
  | .identityDerivationFailed      => 50
  | .identitySigningFailed         => 51
  | .spKeyDerivationFailed         => 52
  | .spAddressFormatFailed         => 53
  | .spOutputCheckFailed           => 54
  | .silentPaymentDuplicateAccount => 55
  | .silentPaymentMixedInputs      => 56
  | .silentPaymentWrongNetwork     => 57
  | .silentPaymentChangeLabel      => 58

/-- Canonical, implementation-independent Ledger Bitcoin specification error category. -/
inductive SpecError where
  /-- Malformed APDU / framing / transport payload length (`0x6700`). -/
  | wrongLength
  /-- Malformed command data payload length (`0x6A87` / `RequestDecodeFailed`). -/
  | wrongDataLength
  /-- Unsupported APDU instruction code (`0x6D00`). -/
  | unsupportedInstruction
  /-- Unsupported APDU class byte (`0x6E00`). -/
  | unsupportedClass
  /-- Invalid APDU `P1`/`P2` header flags (`0x6A86`). -/
  | wrongP1P2
  /-- Interactive UI confirmation rejected by the user (`0x6985` / `UserRejected`). -/
  | userRejected
  /-- Security precondition or wallet HMAC / device lock status not satisfied (`0x6982`). -/
  | securityStatusNotSatisfied
  /-- Ledger Exchange / Swap pre-signed parameters mismatch (`0x6B00`). -/
  | swapValidationFailed
  /-- Malformed, out-of-range, or non-canonical input data (`0x6A80`). -/
  | invalidData
  /-- BIP-32 path exceeds depth limits (`0x6A80` / `DerivationPathTooLong`). -/
  | bip32PathTooLong
  /-- BIP-32 path violates policy or silent-export safety rules (`0x6A82` / `InvalidRequest`). -/
  | unsupportedBip32Path
  /-- Requested script, witness version, or feature is unsupported (`0x6A82` / `AddressNotSupported`). -/
  | notSupported
  /-- Satoshi amount exceeds `MAX_MONEY`, wraps `UInt64`, or outputs exceed inputs (`0x6A80` / `PsbtOutputsExceedInputs`). -/
  | invalidAmount
  /-- Script or address serialization / checksum / witness-program validation failed (`0x6A80` / `AddressFromScriptFailed`). -/
  | invalidScriptOrAddress
  /-- Wallet policy descriptor or key-information vector invalid (`0x6A80` / `AccountDecodeFailed`). -/
  | invalidWalletPolicy
  /-- PSBT global/input/output structure or UTXO proof invalid (`0x6A80` / `PsbtParseFailed`). -/
  | invalidPsbt
  /-- Protocol state machine invariant violated (`0xB007` / `UnexpectedMessage`). -/
  | badState
  /-- Response buffer capacity exceeded (`0xB000` / `ResponseEncodeFailed`). -/
  | wrongResponseLength
  /-- Cryptographic derivation or signature failure (`0xB008` / `PsbtSignFailed`). -/
  | cryptoOrSignatureFailed
  deriving Repr, DecidableEq, Inhabited

/-- Deterministic mapping from canonical `SpecError` to BOLOS `BolosStatusWord`. -/
def SpecError.toBolosStatusWord : SpecError → BolosStatusWord
  | .wrongLength                => .swWrongLength
  | .wrongDataLength            => .swWrongDataLength
  | .unsupportedInstruction     => .swInsNotSupported
  | .unsupportedClass           => .swClaNotSupported
  | .wrongP1P2                  => .swWrongP1P2
  | .userRejected               => .swDeny
  | .securityStatusNotSatisfied => .swSecurityStatusNotSatisfied
  | .swapValidationFailed       => .swFailSwap
  | .invalidData                => .swIncorrectData
  | .bip32PathTooLong           => .swIncorrectData
  | .unsupportedBip32Path       => .swNotSupported
  | .notSupported               => .swNotSupported
  | .invalidAmount              => .swIncorrectData
  | .invalidScriptOrAddress     => .swIncorrectData
  | .invalidWalletPolicy        => .swIncorrectData
  | .invalidPsbt                => .swIncorrectData
  | .badState                   => .swBadState
  | .wrongResponseLength        => .swWrongResponseLength
  | .cryptoOrSignatureFailed    => .swSignatureFail

/-- Deterministic mapping from canonical `SpecError` to BOLOS 16-bit wire status word. -/
def SpecError.toBolosCode (err : SpecError) : UInt16 :=
  err.toBolosStatusWord.toUInt16

/-- Deterministic mapping from canonical `SpecError` to Vanadium `AppError`. -/
def SpecError.toVanadiumError : SpecError → AppError
  | .wrongLength                => .requestDecodeFailed
  | .wrongDataLength            => .requestDecodeFailed
  | .unsupportedInstruction     => .invalidRequest
  | .unsupportedClass           => .invalidRequest
  | .wrongP1P2                  => .invalidRequest
  | .userRejected               => .userRejected
  | .securityStatusNotSatisfied => .accountInvalidHmac
  | .swapValidationFailed       => .invalidRequest
  | .invalidData                => .invalidRequest
  | .bip32PathTooLong           => .derivationPathTooLong
  | .unsupportedBip32Path       => .invalidRequest
  | .notSupported               => .addressNotSupported
  | .invalidAmount              => .psbtOutputsExceedInputs
  | .invalidScriptOrAddress     => .addressFromScriptFailed
  | .invalidWalletPolicy        => .accountDecodeFailed
  | .invalidPsbt                => .psbtParseFailed
  | .badState                   => .unexpectedMessage
  | .wrongResponseLength        => .responseEncodeFailed
  | .cryptoOrSignatureFailed    => .psbtSignFailed

/-- No `SpecError` ever maps to BOLOS `SW_OK` (`0x9000`) or `SW_INTERRUPTED_EXECUTION` (`0xE000`). -/
theorem SpecError.toBolosCode_ne_ok_and_interrupted (err : SpecError) :
    err.toBolosCode ≠ 0x9000 ∧ err.toBolosCode ≠ 0xE000 := by
  cases err <;> decide

end Spec

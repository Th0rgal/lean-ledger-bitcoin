import InternalSpec
import BitcoinLedger.Basic

namespace Proofs.Basic

/-!
# `Proofs.Basic` — Machine-Checked Refinement & Roundtrip Proofs for `BitcoinLedger.Basic`

Constructive (`0 Classical.choice`, `0 sorryAx`, `0 native_decide`, `0 omega`) proofs connecting
the fixed-width executable primitives in `BitcoinLedger.Basic` to the normative specifications in
`InternalSpec.Basic`:
1. Checked `UInt64` satoshi arithmetic equivalence (`checkedAddSats? = InternalSpec.addAmounts?`,
   `checkedSubSats? = InternalSpec.subAmounts?`, `checkedSumSats? = InternalSpec.sumAmounts?`) and concrete
   `2^64 - 1 + 1` / `MAX_MONEY + 1` overflow rejection theorems.
2. Constructive byte-slice equality (`eqBytes`) and fixed-width validators (`isBytes4..65`).
3. Fixed-width shift/OR LE & BE integer codec equivalence with `InternalSpec.encodeU*` / `InternalSpec.decodeU*?`
   plus bijective encode/decode roundtrips.
4. Canonical CompactSize / VarInt (`encodeVarInt`, `decodeVarIntCanonical?`, `varIntByteLen`,
   `decodeVarIntCanonicalPrefix?`) exact equivalence with `Spec`, bijective roundtrip, and
   non-canonical rejection (`0xFD`, `0xFE`, `0xFF`).
5. Bitcoin `NetworkParams` equivalence (`Mainnet`, `Testnet`, `Regtest`, `Signet`).
6. Ledger `SpecError` ↔ BOLOS `UInt16` status word & Vanadium `AppError` CBOR code totality,
   roundtrips, injectivity, and non-`SW_OK` (`0x9000`) / non-`0xE000` safety.
-/

/-! ### Constructive `BEq` Instances (`0 Classical.choice`) -/
local instance (priority := high) : BEq UInt8 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt16 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt32 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt64 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : LawfulBEq UInt8 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt16 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt32 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt64 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-! ## Section 1: Satoshi Arithmetic Refinement (`checkedAddSats?`, `checkedSubSats?`, `checkedSumSats?`) -/

theorem sats_per_btc_eq : BitcoinLedger.Basic.SATS_PER_BTC = InternalSpec.SATS_PER_BTC := rfl

theorem max_money_eq : BitcoinLedger.Basic.MAX_MONEY = InternalSpec.MAX_MONEY := rfl

theorem isValidAmount_iff (a : UInt64) :
    BitcoinLedger.Basic.isValidAmount a = true ↔ InternalSpec.ValidAmount a := by
  unfold BitcoinLedger.Basic.isValidAmount InternalSpec.ValidAmount
  rw [decide_eq_true_eq, max_money_eq, UInt64.le_iff_toNat_le]

private theorem max_money_lt_two_pow_64 :
    InternalSpec.MAX_MONEY.toNat < 2 ^ 64 := InternalSpec.MAX_MONEY.toNat_lt

private theorem u64_add_eq_ofNat (a b : UInt64) :
    a + b = UInt64.ofNat (a.toNat + b.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']

private theorem u64_sub_eq_ofNat_of_le {a b : UInt64} (hba : b ≤ a) :
    a - b = UInt64.ofNat (a.toNat - b.toNat) := by
  apply UInt64.toNat_inj.mp
  have hsub_lt : a.toNat - b.toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.toNat_lt
  rw [UInt64.toNat_sub_of_le a b hba, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hsub_lt]

/-- Exact equivalence between fixed-width `checkedAddSats?` (`b ≤ MAX_MONEY - a`) and `InternalSpec.addAmounts?`. -/
theorem checkedAddSats?_eq (a b : UInt64) :
    BitcoinLedger.Basic.checkedAddSats? a b = InternalSpec.addAmounts? a b := by
  unfold BitcoinLedger.Basic.checkedAddSats? InternalSpec.addAmounts?
  rw [max_money_eq]
  cases ha : decide (a ≤ InternalSpec.MAX_MONEY)
  · have hna : ¬ (a.toNat ≤ InternalSpec.MAX_MONEY.toNat) := by
      intro hle
      exact of_decide_eq_false ha (UInt64.le_iff_toNat_le.mpr hle)
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    have hnot : ¬ (a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                   a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat) := fun h => hna h.1
    simp only [hnot, ↓reduceIte]
  · have haLe : a ≤ InternalSpec.MAX_MONEY := of_decide_eq_true ha
    have haNat : a.toNat ≤ InternalSpec.MAX_MONEY.toNat := UInt64.le_iff_toNat_le.mp haLe
    have hSubNat : (InternalSpec.MAX_MONEY - a).toNat = InternalSpec.MAX_MONEY.toNat - a.toNat :=
      UInt64.toNat_sub_of_le InternalSpec.MAX_MONEY a haLe
    cases hb : decide (b ≤ InternalSpec.MAX_MONEY - a)
    · have hnb : ¬ (b.toNat ≤ InternalSpec.MAX_MONEY.toNat - a.toNat) := by
        intro hle
        apply of_decide_eq_false hb
        rw [UInt64.le_iff_toNat_le, hSubNat]
        exact hle
      simp only [Bool.true_and, Bool.false_eq_true, ↓reduceIte]
      have hnot : ¬ (a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                     a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat) := by
        intro ⟨_, _, hab⟩
        exact hnb (Nat.le_sub_of_add_le' hab)
      simp only [hnot, ↓reduceIte]
    · have hbLe : b ≤ InternalSpec.MAX_MONEY - a := of_decide_eq_true hb
      have hbSub : b.toNat ≤ InternalSpec.MAX_MONEY.toNat - a.toNat := by
        rw [← hSubNat]
        exact UInt64.le_iff_toNat_le.mp hbLe
      have hab : a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat := by
        rw [Nat.add_comm]
        exact Nat.add_le_of_le_sub haNat hbSub
      have hbMax : b.toNat ≤ InternalSpec.MAX_MONEY.toNat :=
        Nat.le_trans (Nat.le_add_left b.toNat a.toNat) hab
      simp only [Bool.true_and, haNat, hbMax, hab, and_self, ↓reduceIte, u64_add_eq_ofNat a b]

/-- Exact equivalence between fixed-width `checkedSubSats?` and `InternalSpec.subAmounts?`. -/
theorem checkedSubSats?_eq (total part : UInt64) :
    BitcoinLedger.Basic.checkedSubSats? total part = InternalSpec.subAmounts? total part := by
  unfold BitcoinLedger.Basic.checkedSubSats? InternalSpec.subAmounts?
  rw [max_money_eq]
  cases ht : decide (total ≤ InternalSpec.MAX_MONEY)
  · have hnt : ¬ (total.toNat ≤ InternalSpec.MAX_MONEY.toNat) :=
      fun hle => of_decide_eq_false ht (UInt64.le_iff_toNat_le.mpr hle)
    have hnot : ¬ (total.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ part.toNat ≤ total.toNat) :=
      fun h => hnt h.1
    simp only [Bool.false_and, Bool.false_eq_true, hnot, ↓reduceIte]
  · have htNat : total.toNat ≤ InternalSpec.MAX_MONEY.toNat :=
      UInt64.le_iff_toNat_le.mp (of_decide_eq_true ht)
    cases hp : decide (part ≤ total)
    · have hnp : ¬ (part.toNat ≤ total.toNat) :=
        fun hle => of_decide_eq_false hp (UInt64.le_iff_toNat_le.mpr hle)
      have hnot : ¬ (total.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ part.toNat ≤ total.toNat) :=
        fun h => hnp h.2
      simp only [Bool.true_and, Bool.false_eq_true, hnot, ↓reduceIte]
    · have hpLe : part ≤ total := of_decide_eq_true hp
      have hpNat : part.toNat ≤ total.toNat := UInt64.le_iff_toNat_le.mp hpLe
      simp only [Bool.true_and, htNat, hpNat, and_self, ↓reduceIte, u64_sub_eq_ofNat_of_le hpLe]

private theorem addAmounts?_comm (a b : UInt64) :
    InternalSpec.addAmounts? a b = InternalSpec.addAmounts? b a := by
  unfold InternalSpec.addAmounts?
  by_cases h1 : a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat
  · rcases h1 with ⟨ha, hb, hab⟩
    have hba : b.toNat + a.toNat ≤ InternalSpec.MAX_MONEY.toNat := by
      rw [Nat.add_comm]
      exact hab
    simp only [ha, hb, hab, hba, and_self, ↓reduceIte]
    rw [Nat.add_comm]
  · have h2 : ¬ (b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                 b.toNat + a.toNat ≤ InternalSpec.MAX_MONEY.toNat) := by
      intro ⟨hb, ha, hba⟩
      apply h1
      refine ⟨ha, hb, ?_⟩
      rw [Nat.add_comm]
      exact hba
    simp only [h1, h2, ↓reduceIte]

private theorem addAmounts?_zero_left (a : UInt64) (ha : a.toNat ≤ InternalSpec.MAX_MONEY.toNat) :
    InternalSpec.addAmounts? 0 a = some a := by
  unfold InternalSpec.addAmounts?
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h0Le : 0 ≤ InternalSpec.MAX_MONEY.toNat := Nat.zero_le _
  simp only [h0, Nat.zero_add, h0Le, ha, and_self, ↓reduceIte]
  apply congrArg some
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt a.toNat_lt]

private theorem addAmounts?_assoc (a b c : UInt64)
    (ha : a.toNat ≤ InternalSpec.MAX_MONEY.toNat) :
    (match InternalSpec.addAmounts? a b with
     | none => none
     | some ab => InternalSpec.addAmounts? ab c) =
    (match InternalSpec.addAmounts? b c with
     | none => none
     | some bc => InternalSpec.addAmounts? a bc) := by
  by_cases hb : b.toNat ≤ InternalSpec.MAX_MONEY.toNat
  · by_cases hc : c.toNat ≤ InternalSpec.MAX_MONEY.toNat
    · by_cases habc : a.toNat + b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat
      · have hab : a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat :=
          Nat.le_trans (Nat.le_add_right _ _) habc
        have hbc : b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat := by
          have : b.toNat + c.toNat ≤ a.toNat + (b.toNat + c.toNat) := Nat.le_add_left _ _
          rw [← Nat.add_assoc] at this
          exact Nat.le_trans this habc
        have habEq : InternalSpec.addAmounts? a b = some (UInt64.ofNat (a.toNat + b.toNat)) := by
          unfold InternalSpec.addAmounts?
          simp only [ha, hb, hab, and_self, ↓reduceIte]
        have hbcEq : InternalSpec.addAmounts? b c = some (UInt64.ofNat (b.toNat + c.toNat)) := by
          unfold InternalSpec.addAmounts?
          simp only [hb, hc, hbc, and_self, ↓reduceIte]
        have habNat : (UInt64.ofNat (a.toNat + b.toNat)).toNat = a.toNat + b.toNat := by
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hab max_money_lt_two_pow_64)]
        have hbcNat : (UInt64.ofNat (b.toNat + c.toNat)).toNat = b.toNat + c.toNat := by
          rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hbc max_money_lt_two_pow_64)]
        rw [habEq, hbcEq]
        simp only [InternalSpec.addAmounts?, habNat, hbcNat, hab, hc, ha, hbc, habc,
          ← Nat.add_assoc, and_self, ↓reduceIte]
      · cases hL : InternalSpec.addAmounts? a b with
        | none =>
            cases hR : InternalSpec.addAmounts? b c with
            | none => rfl
            | some bc =>
                have hbcNat : bc.toNat = b.toNat + c.toNat := (InternalSpec.addAmounts?_toNat hR).1
                simp only [InternalSpec.addAmounts?, hbcNat]
                have hnot : ¬ (a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                               a.toNat + (b.toNat + c.toNat) ≤ InternalSpec.MAX_MONEY.toNat) := by
                  intro ⟨_, _, hsum⟩
                  rw [← Nat.add_assoc] at hsum
                  exact habc hsum
                simp only [hnot, ↓reduceIte]
        | some ab =>
            have habNat : ab.toNat = a.toNat + b.toNat := (InternalSpec.addAmounts?_toNat hL).1
            have hL2 : InternalSpec.addAmounts? ab c = none := by
              unfold InternalSpec.addAmounts?
              rw [habNat]
              have hnot : ¬ (a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ c.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                             a.toNat + b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat) :=
                fun ⟨_, _, hsum⟩ => habc hsum
              simp only [hnot, ↓reduceIte]
            simp only [hL2]
            cases hR : InternalSpec.addAmounts? b c with
            | none => rfl
            | some bc =>
                have hbcNat : bc.toNat = b.toNat + c.toNat := (InternalSpec.addAmounts?_toNat hR).1
                simp only [InternalSpec.addAmounts?, hbcNat]
                have hnot : ¬ (a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                               a.toNat + (b.toNat + c.toNat) ≤ InternalSpec.MAX_MONEY.toNat) := by
                  intro ⟨_, _, hsum⟩
                  rw [← Nat.add_assoc] at hsum
                  exact habc hsum
                simp only [hnot, ↓reduceIte]
    · have hbcNone : InternalSpec.addAmounts? b c = none := by
        unfold InternalSpec.addAmounts?
        have hnot : ¬ (b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ c.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                       b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat) := fun h => hc h.2.1
        simp only [hnot, ↓reduceIte]
      rw [hbcNone]
      cases InternalSpec.addAmounts? a b with
      | none => rfl
      | some ab =>
          simp only [InternalSpec.addAmounts?]
          have hnot : ¬ (ab.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ c.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                         ab.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat) := fun h => hc h.2.1
          simp only [hnot, ↓reduceIte]
  · have habNone : InternalSpec.addAmounts? a b = none := by
      unfold InternalSpec.addAmounts?
      have hnot : ¬ (a.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                     a.toNat + b.toNat ≤ InternalSpec.MAX_MONEY.toNat) := fun h => hb h.2.1
      simp only [hnot, ↓reduceIte]
    have hbcNone : InternalSpec.addAmounts? b c = none := by
      unfold InternalSpec.addAmounts?
      have hnot : ¬ (b.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧ c.toNat ≤ InternalSpec.MAX_MONEY.toNat ∧
                     b.toNat + c.toNat ≤ InternalSpec.MAX_MONEY.toNat) := fun h => hb h.1
      simp only [hnot, ↓reduceIte]
    rw [habNone, hbcNone]

private theorem checkedSumSatsLoop_eq_spec :
    ∀ (xs : List UInt64) (acc : UInt64),
      acc.toNat ≤ InternalSpec.MAX_MONEY.toNat →
      BitcoinLedger.Basic.checkedSumSatsLoop acc xs =
        match InternalSpec.sumAmounts? xs with
        | none => none
        | some rest => InternalSpec.addAmounts? acc rest
  | [], acc, hacc => by
      simp only [BitcoinLedger.Basic.checkedSumSatsLoop, InternalSpec.sumAmounts?]
      rw [addAmounts?_comm, addAmounts?_zero_left acc hacc]
  | x :: xs, acc, hacc => by
      simp only [BitcoinLedger.Basic.checkedSumSatsLoop, checkedAddSats?_eq, InternalSpec.sumAmounts?]
      cases hax : InternalSpec.addAmounts? acc x with
      | none =>
          cases hrest : InternalSpec.sumAmounts? xs with
          | none => rfl
          | some rest =>
              simp only
              have hAssocInst := addAmounts?_assoc acc x rest hacc
              rw [hax] at hAssocInst
              exact hAssocInst
      | some acc' =>
          have hacc' : acc'.toNat ≤ InternalSpec.MAX_MONEY.toNat := (InternalSpec.addAmounts?_toNat hax).2
          simp only [checkedSumSatsLoop_eq_spec xs acc' hacc']
          cases hrest : InternalSpec.sumAmounts? xs with
          | none => rfl
          | some rest =>
              have hAssocInst := addAmounts?_assoc acc x rest hacc
              rw [hax] at hAssocInst
              exact hAssocInst

/-- Exact refinement theorem: tail-recursive `UInt64` `checkedSumSats?` equals `InternalSpec.sumAmounts?`. -/
theorem checkedSumSats?_eq (xs : List UInt64) :
    BitcoinLedger.Basic.checkedSumSats? xs = InternalSpec.sumAmounts? xs := by
  unfold BitcoinLedger.Basic.checkedSumSats?
  have h0 : (0 : UInt64).toNat ≤ InternalSpec.MAX_MONEY.toNat := Nat.zero_le _
  rw [checkedSumSatsLoop_eq_spec xs 0 h0]
  cases h : InternalSpec.sumAmounts? xs with
  | none => rfl
  | some total =>
      have htLe : total.toNat ≤ InternalSpec.MAX_MONEY.toNat := (InternalSpec.sumAmounts?_sound h).2.1
      exact addAmounts?_zero_left total htLe

theorem checkedSumSatsArray?_eq (xs : Array UInt64) :
    BitcoinLedger.Basic.checkedSumSatsArray? xs = InternalSpec.sumAmounts? xs.toList :=
  checkedSumSats?_eq xs.toList

/-- Concrete witness: `checkedSumSats?` rejects `UInt64` wraparound `[2^64 - 1, 1]` and `[MAX_MONEY, 1]`,
    while accepting valid sums up to `MAX_MONEY`. -/
theorem checkedSumSats?_overflow_and_valid_witness :
    BitcoinLedger.Basic.checkedSumSats? [0xFFFFFFFFFFFFFFFF, 1] = none ∧
    BitcoinLedger.Basic.checkedSumSats? [BitcoinLedger.Basic.MAX_MONEY, 1] = none ∧
    BitcoinLedger.Basic.checkedSumSats? [100_000_000, 250_000_000] = some 350_000_000 ∧
    BitcoinLedger.Basic.checkedSubSats? 350_000_000 100_000_000 = some 250_000_000 := by
  decide

/-! ## Section 2: Fixed-Width Byte-Slice Validators & Constructive Byte Equality -/

theorem eqByteList_iff : ∀ (xs ys : List UInt8),
    BitcoinLedger.Basic.eqByteList xs ys = true ↔ xs = ys
  | [], [] => ⟨fun _ => rfl, fun _ => rfl⟩
  | [], _ :: _ => ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | _ :: _, [] => ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | x :: xs, y :: ys => by
      unfold BitcoinLedger.Basic.eqByteList
      rw [Bool.and_eq_true, decide_eq_true_eq, eqByteList_iff xs ys]
      exact ⟨fun ⟨h1, h2⟩ => by rw [h1, h2], fun h => List.cons.inj h⟩

theorem eqBytes_iff (a b : ByteArray) :
    BitcoinLedger.Basic.eqBytes a b = true ↔ a = b := by
  unfold BitcoinLedger.Basic.eqBytes
  rw [eqByteList_iff]
  constructor
  · intro h
    cases a with | mk da =>
    cases b with | mk db =>
    congr
    exact Array.ext' h
  · intro h
    subst h
    rfl

theorem eqBytes_refl (a : ByteArray) : BitcoinLedger.Basic.eqBytes a a = true :=
  (eqBytes_iff a a).mpr rfl

theorem isBytesN_iff (n : Nat) (bs : ByteArray) :
    BitcoinLedger.Basic.isBytesN n bs = true ↔ InternalSpec.BytesN n bs := by
  simp only [BitcoinLedger.Basic.isBytesN, InternalSpec.BytesN, decide_eq_true_eq]

theorem isBytes4_iff (bs : ByteArray) :
    BitcoinLedger.Basic.isBytes4 bs = true ↔ InternalSpec.Bytes4 bs := isBytesN_iff 4 bs

theorem isBytes20_iff (bs : ByteArray) :
    BitcoinLedger.Basic.isBytes20 bs = true ↔ InternalSpec.Bytes20 bs := isBytesN_iff 20 bs

theorem isBytes32_iff (bs : ByteArray) :
    BitcoinLedger.Basic.isBytes32 bs = true ↔ InternalSpec.Bytes32 bs := isBytesN_iff 32 bs

theorem isBytes33_iff (bs : ByteArray) :
    BitcoinLedger.Basic.isBytes33 bs = true ↔ InternalSpec.Bytes33 bs := isBytesN_iff 33 bs

theorem isBytes64_iff (bs : ByteArray) :
    BitcoinLedger.Basic.isBytes64 bs = true ↔ InternalSpec.Bytes64 bs := isBytesN_iff 64 bs

theorem isBytes65_iff (bs : ByteArray) :
    BitcoinLedger.Basic.isBytes65 bs = true ↔ InternalSpec.Bytes65 bs := isBytesN_iff 65 bs

/-! ## Section 3: Little-Endian & Big-Endian Fixed-Width Integer Codec Refinement -/

private theorem nat_toUInt8_eq_ofNat_mod (n : Nat) :
    n.toUInt8 = UInt8.ofNat (n % 256) := by
  apply UInt8.toNat_inj.mp
  change n % 256 = (n % 256) % 256
  exact (Nat.mod_mod _ _).symm

private theorem u16_shift_byte (v : UInt16) (s : UInt16) (hs : s.toNat < 16) :
    (v >>> s).toUInt8 = UInt8.ofNat ((v.toNat / (2 ^ s.toNat)) % 256) := by
  change (v >>> s).toNat.toUInt8 = _
  rw [UInt16.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  exact nat_toUInt8_eq_ofNat_mod _

private theorem u32_shift_byte (v : UInt32) (s : UInt32) (hs : s.toNat < 32) :
    (v >>> s).toUInt8 = UInt8.ofNat ((v.toNat / (2 ^ s.toNat)) % 256) := by
  change (v >>> s).toNat.toUInt8 = _
  rw [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  exact nat_toUInt8_eq_ofNat_mod _

private theorem u64_shift_byte (v : UInt64) (s : UInt64) (hs : s.toNat < 64) :
    (v >>> s).toUInt8 = UInt8.ofNat ((v.toNat / (2 ^ s.toNat)) % 256) := by
  change (v >>> s).toNat.toUInt8 = _
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hs, Nat.shiftRight_eq_div_pow]
  exact nat_toUInt8_eq_ofNat_mod _

private theorem nat_or_shiftLeft_eq_add {k a b : Nat} (ha : a < 2 ^ k) :
    a ||| (b <<< k) = a + 2 ^ k * b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.add_comm, Nat.testBit_two_pow_mul_add b ha j]
  cases hjk : decide (j < k)
  · have hge : k ≤ j := Nat.le_of_not_lt (of_decide_eq_false hjk)
    have hnotlt : ¬ (j < k) := of_decide_eq_false hjk
    have haFalse : a.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hge))
    simp [hge, hnotlt, haFalse]
  · have hlt : j < k := of_decide_eq_true hjk
    have hnotge : ¬ (k ≤ j) := Nat.not_le_of_gt hlt
    simp [hlt, hnotge]

private theorem u8_shiftLeft_u16_toNat (b : UInt8) :
    (b.toUInt16 <<< 8).toNat = b.toNat <<< 8 := by
  rw [UInt16.toNat_shiftLeft]
  have hb : b.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_lt_mul_of_pos_right b.toNat_lt (by decide : 0 < 2 ^ 8)
  exact Nat.mod_eq_of_lt hb

private theorem u8_shiftLeft_u32_toNat (b : UInt8) (k : UInt32)
    (hk : k.toNat ≤ 24) :
    (b.toUInt32 <<< k).toNat = b.toNat <<< k.toNat := by
  have hk32 : k.toNat < 32 := Nat.lt_of_le_of_lt hk (by decide)
  rw [UInt32.toNat_shiftLeft, Nat.mod_eq_of_lt hk32]
  have hb : b.toNat <<< k.toNat < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have h1 : b.toNat * 2 ^ k.toNat ≤ b.toNat * 2 ^ 24 :=
      Nat.mul_le_mul_left b.toNat (Nat.pow_le_pow_right (by decide) hk)
    have h2 : b.toNat * 2 ^ 24 < 256 * 2 ^ 24 :=
      Nat.mul_lt_mul_of_pos_right b.toNat_lt (by decide : 0 < 2 ^ 24)
    exact Nat.lt_of_le_of_lt h1 h2
  exact Nat.mod_eq_of_lt hb

private theorem u8_shiftLeft_u64_toNat (b : UInt8) (k : UInt64)
    (hk : k.toNat ≤ 56) :
    (b.toUInt64 <<< k).toNat = b.toNat <<< k.toNat := by
  have hk64 : k.toNat < 64 := Nat.lt_of_le_of_lt hk (by decide)
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk64]
  have hb : b.toNat <<< k.toNat < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have h1 : b.toNat * 2 ^ k.toNat ≤ b.toNat * 2 ^ 56 :=
      Nat.mul_le_mul_left b.toNat (Nat.pow_le_pow_right (by decide) hk)
    have h2 : b.toNat * 2 ^ 56 < 256 * 2 ^ 56 :=
      Nat.mul_lt_mul_of_pos_right b.toNat_lt (by decide : 0 < 2 ^ 56)
    exact Nat.lt_of_le_of_lt h1 h2
  exact Nat.mod_eq_of_lt hb

theorem encodeU16LE_eq (v : UInt16) :
    BitcoinLedger.Basic.encodeU16LE v = InternalSpec.encodeU16LEBytes v := by
  unfold BitcoinLedger.Basic.encodeU16LE InternalSpec.encodeU16LEBytes
  have e0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := nat_toUInt8_eq_ofNat_mod v.toNat
  have e1 : (v >>> 8).toUInt8 = UInt8.ofNat ((v.toNat / 256) % 256) :=
    u16_shift_byte v 8 (by decide)
  rw [e0, e1]

theorem encodeU16LE_satisfies (v : UInt16) :
    InternalSpec.encodeU16LE v (BitcoinLedger.Basic.encodeU16LE v) := by
  rw [encodeU16LE_eq]
  exact InternalSpec.encodeU16LEBytes_satisfies v

theorem decodeU16LE?_eq (bs : ByteArray) :
    BitcoinLedger.Basic.decodeU16LE? bs = InternalSpec.decodeU16LE? bs := by
  unfold BitcoinLedger.Basic.decodeU16LE? InternalSpec.decodeU16LE?
  cases bs.data.toList with
  | nil => rfl
  | cons b0 r0 =>
      cases r0 with
      | nil => rfl
      | cons b1 r1 =>
          cases r1 with
          | cons _ _ => rfl
          | nil =>
              apply congrArg some
              apply UInt16.toNat_inj.mp
              rw [UInt16.toNat_or, u8_shiftLeft_u16_toNat]
              have hb0Nat : b0.toUInt16.toNat = b0.toNat := rfl
              rw [hb0Nat, nat_or_shiftLeft_eq_add b0.toNat_lt, UInt16.toNat_ofNat']
              have hlt : b0.toNat + 2 ^ 8 * b1.toNat < 2 ^ 16 := by
                have h1 : 2 ^ 8 * b1.toNat ≤ 256 * 255 :=
                  Nat.mul_le_mul_left 256 (Nat.le_of_lt_succ b1.toNat_lt)
                have h2 : b0.toNat + 2 ^ 8 * b1.toNat ≤ 255 + 256 * 255 :=
                  Nat.add_le_add (Nat.le_of_lt_succ b0.toNat_lt) h1
                exact Nat.lt_of_le_of_lt h2 (by decide)
              exact (Nat.mod_eq_of_lt hlt).symm

theorem decodeU16LE?_roundtrip (v : UInt16) :
    BitcoinLedger.Basic.decodeU16LE? (BitcoinLedger.Basic.encodeU16LE v) = some v := by
  rw [decodeU16LE?_eq, encodeU16LE_eq]
  exact InternalSpec.decodeU16LE?_roundtrip v

theorem encodeU32LE_eq (v : UInt32) :
    BitcoinLedger.Basic.encodeU32LE v = InternalSpec.encodeU32LEBytes v := by
  unfold BitcoinLedger.Basic.encodeU32LE InternalSpec.encodeU32LEBytes
  have e0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := nat_toUInt8_eq_ofNat_mod v.toNat
  have e1 : (v >>> 8).toUInt8 = UInt8.ofNat ((v.toNat / 256) % 256) :=
    u32_shift_byte v 8 (by decide)
  have e2 : (v >>> 16).toUInt8 = UInt8.ofNat ((v.toNat / 65536) % 256) :=
    u32_shift_byte v 16 (by decide)
  have e3 : (v >>> 24).toUInt8 = UInt8.ofNat ((v.toNat / 16777216) % 256) :=
    u32_shift_byte v 24 (by decide)
  rw [e0, e1, e2, e3]

theorem encodeU32LE_satisfies (v : UInt32) :
    InternalSpec.encodeU32LE v (BitcoinLedger.Basic.encodeU32LE v) := by
  rw [encodeU32LE_eq]
  exact InternalSpec.encodeU32LEBytes_satisfies v

private theorem u32_pack_le_toNat (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
      u8_shiftLeft_u32_toNat b1 8 (by decide),
      u8_shiftLeft_u32_toNat b2 16 (by decide),
      u8_shiftLeft_u32_toNat b3 24 (by decide)]
  change b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24) = _
  rw [nat_or_shiftLeft_eq_add b0.toNat_lt]
  have lt16 : b0.toNat + 2 ^ 8 * b1.toNat < 2 ^ 16 := by
    have h1 : 2 ^ 8 * b1.toNat ≤ 256 * 255 := Nat.mul_le_mul_left 256 (Nat.le_of_lt_succ b1.toNat_lt)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt_succ b0.toNat_lt) h1) (by decide)
  rw [nat_or_shiftLeft_eq_add lt16]
  have lt24 : b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat < 2 ^ 24 := by
    have h1 : b0.toNat + 2 ^ 8 * b1.toNat ≤ 65535 := Nat.le_of_lt_succ lt16
    have h2 : 2 ^ 16 * b2.toNat ≤ 65536 * 255 := Nat.mul_le_mul_left 65536 (Nat.le_of_lt_succ b2.toNat_lt)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) (by decide)
  exact nat_or_shiftLeft_eq_add lt24

theorem decodeU32LE?_eq (bs : ByteArray) :
    BitcoinLedger.Basic.decodeU32LE? bs = InternalSpec.decodeU32LE? bs := by
  unfold BitcoinLedger.Basic.decodeU32LE? InternalSpec.decodeU32LE?
  match bs.data.toList with
  | [b0, b1, b2, b3] =>
      apply congrArg some
      apply UInt32.toNat_inj.mp
      rw [u32_pack_le_toNat, UInt32.toNat_ofNat']
      have hlt : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 2 ^ 32 := by
        rw [← u32_pack_le_toNat]
        exact UInt32.toNat_lt _
      exact (Nat.mod_eq_of_lt hlt).symm
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem decodeU32LE?_roundtrip (v : UInt32) :
    BitcoinLedger.Basic.decodeU32LE? (BitcoinLedger.Basic.encodeU32LE v) = some v := by
  rw [decodeU32LE?_eq, encodeU32LE_eq]
  exact InternalSpec.decodeU32LE?_roundtrip v

theorem encodeU32BE_eq (v : UInt32) :
    BitcoinLedger.Basic.encodeU32BE v = InternalSpec.encodeU32BEBytes v := by
  unfold BitcoinLedger.Basic.encodeU32BE InternalSpec.encodeU32BEBytes
  have e3 : (v >>> 24).toUInt8 = UInt8.ofNat ((v.toNat / 16777216) % 256) :=
    u32_shift_byte v 24 (by decide)
  have e2 : (v >>> 16).toUInt8 = UInt8.ofNat ((v.toNat / 65536) % 256) :=
    u32_shift_byte v 16 (by decide)
  have e1 : (v >>> 8).toUInt8 = UInt8.ofNat ((v.toNat / 256) % 256) :=
    u32_shift_byte v 8 (by decide)
  have e0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := nat_toUInt8_eq_ofNat_mod v.toNat
  rw [e3, e2, e1, e0]

theorem encodeU32BE_satisfies (v : UInt32) :
    InternalSpec.encodeU32BE v (BitcoinLedger.Basic.encodeU32BE v) := by
  rw [encodeU32BE_eq]
  exact InternalSpec.encodeU32BEBytes_satisfies v

private theorem nat_or4_reverse (x0 x1 x2 x3 : Nat) :
    x0 ||| x1 ||| x2 ||| x3 = x3 ||| x2 ||| x1 ||| x0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or]
  cases x0.testBit i <;> cases x1.testBit i <;> cases x2.testBit i <;> cases x3.testBit i <;> rfl

theorem decodeU32BE?_eq (bs : ByteArray) :
    BitcoinLedger.Basic.decodeU32BE? bs = InternalSpec.decodeU32BE? bs := by
  unfold BitcoinLedger.Basic.decodeU32BE? InternalSpec.decodeU32BE?
  match bs.data.toList with
  | [b0, b1, b2, b3] =>
      apply congrArg some
      apply UInt32.toNat_inj.mp
      have hcomm :
          ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32).toNat =
          (b3.toUInt32 ||| (b2.toUInt32 <<< 8) ||| (b1.toUInt32 <<< 16) ||| (b0.toUInt32 <<< 24)).toNat := by
        rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
            UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or]
        exact nat_or4_reverse _ _ _ _
      rw [hcomm, u32_pack_le_toNat, UInt32.toNat_ofNat']
      have hsum :
          b3.toNat + 256 * b2.toNat + 65536 * b1.toNat + 16777216 * b0.toNat =
          16777216 * b0.toNat + 65536 * b1.toNat + 256 * b2.toNat + b3.toNat := by
        rw [Nat.add_comm (b3.toNat + 256 * b2.toNat + 65536 * b1.toNat),
            Nat.add_comm (b3.toNat + 256 * b2.toNat),
            Nat.add_comm b3.toNat,
            ← Nat.add_assoc, ← Nat.add_assoc]
      rw [hsum]
      have hlt : 16777216 * b0.toNat + 65536 * b1.toNat + 256 * b2.toNat + b3.toNat < 2 ^ 32 := by
        rw [← hsum, ← u32_pack_le_toNat]
        exact UInt32.toNat_lt _
      exact (Nat.mod_eq_of_lt hlt).symm
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem decodeU32BE?_roundtrip (v : UInt32) :
    BitcoinLedger.Basic.decodeU32BE? (BitcoinLedger.Basic.encodeU32BE v) = some v := by
  rw [decodeU32BE?_eq, encodeU32BE_eq]
  exact InternalSpec.decodeU32BE?_roundtrip v

theorem encodeU64LE_eq (v : UInt64) :
    BitcoinLedger.Basic.encodeU64LE v = InternalSpec.encodeU64LEBytes v := by
  unfold BitcoinLedger.Basic.encodeU64LE InternalSpec.encodeU64LEBytes
  have e0 : v.toUInt8 = UInt8.ofNat (v.toNat % 256) := nat_toUInt8_eq_ofNat_mod v.toNat
  have e1 := u64_shift_byte v 8 (by decide)
  have e2 := u64_shift_byte v 16 (by decide)
  have e3 := u64_shift_byte v 24 (by decide)
  have e4 := u64_shift_byte v 32 (by decide)
  have e5 := u64_shift_byte v 40 (by decide)
  have e6 := u64_shift_byte v 48 (by decide)
  have e7 := u64_shift_byte v 56 (by decide)
  rw [e0, e1, e2, e3, e4, e5, e6, e7]
  rfl

theorem encodeU64LE_satisfies (v : UInt64) :
    InternalSpec.encodeU64LE v (BitcoinLedger.Basic.encodeU64LE v) := by
  rw [encodeU64LE_eq]
  exact InternalSpec.encodeU64LEBytes_satisfies v

private theorem u64_pack_le_toNat (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 |||
     (b1.toUInt64 <<< 8) |||
     (b2.toUInt64 <<< 16) |||
     (b3.toUInt64 <<< 24) |||
     (b4.toUInt64 <<< 32) |||
     (b5.toUInt64 <<< 40) |||
     (b6.toUInt64 <<< 48) |||
     (b7.toUInt64 <<< 56)).toNat =
      b0.toNat +
      256 * b1.toNat +
      65536 * b2.toNat +
      16777216 * b3.toNat +
      4294967296 * b4.toNat +
      1099511627776 * b5.toNat +
      281474976710656 * b6.toNat +
      72057594037927936 * b7.toNat := by
  repeat rw [UInt64.toNat_or]
  rw [u8_shiftLeft_u64_toNat b1 8 (by decide),
      u8_shiftLeft_u64_toNat b2 16 (by decide),
      u8_shiftLeft_u64_toNat b3 24 (by decide),
      u8_shiftLeft_u64_toNat b4 32 (by decide),
      u8_shiftLeft_u64_toNat b5 40 (by decide),
      u8_shiftLeft_u64_toNat b6 48 (by decide),
      u8_shiftLeft_u64_toNat b7 56 (by decide)]
  change b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24) |||
         (b4.toNat <<< 32) ||| (b5.toNat <<< 40) ||| (b6.toNat <<< 48) ||| (b7.toNat <<< 56) = _
  have boundStep : ∀ {acc k : Nat} {b : UInt8},
      acc < 2 ^ k → acc + 2 ^ k * b.toNat < 2 ^ (k + 8) := by
    intro acc k b hacc
    have h1 : acc + 2 ^ k * b.toNat ≤ (2 ^ k - 1) + 2 ^ k * 255 :=
      Nat.add_le_add (Nat.le_pred_of_lt hacc)
        (Nat.mul_le_mul_left (2 ^ k) (Nat.le_of_lt_succ b.toNat_lt))
    have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
    have h2 : (2 ^ k - 1) + 2 ^ k * 255 < 2 ^ k + 2 ^ k * 255 :=
      Nat.add_lt_add_right (Nat.sub_lt hpow (by decide)) _
    have h3 : 2 ^ k + 2 ^ k * 255 = 2 ^ (k + 8) := by
      have hmul1 : 2 ^ k = 2 ^ k * 1 := (Nat.mul_one _).symm
      conv => lhs; lhs; rw [hmul1]
      rw [← Nat.mul_add, Nat.pow_add]
    rw [← h3]
    exact Nat.lt_of_le_of_lt h1 h2
  have lt8 : b0.toNat < 2 ^ 8 := b0.toNat_lt
  rw [nat_or_shiftLeft_eq_add lt8]
  have lt16 := boundStep (b := b1) lt8
  rw [nat_or_shiftLeft_eq_add lt16]
  have lt24 := boundStep (b := b2) lt16
  rw [nat_or_shiftLeft_eq_add lt24]
  have lt32 := boundStep (b := b3) lt24
  rw [nat_or_shiftLeft_eq_add lt32]
  have lt40 := boundStep (b := b4) lt32
  rw [nat_or_shiftLeft_eq_add lt40]
  have lt48 := boundStep (b := b5) lt40
  rw [nat_or_shiftLeft_eq_add lt48]
  have lt56 := boundStep (b := b6) lt48
  exact nat_or_shiftLeft_eq_add lt56

theorem decodeU64LE?_eq (bs : ByteArray) :
    BitcoinLedger.Basic.decodeU64LE? bs = InternalSpec.decodeU64LE? bs := by
  unfold BitcoinLedger.Basic.decodeU64LE? InternalSpec.decodeU64LE?
  match bs.data.toList with
  | [b0, b1, b2, b3, b4, b5, b6, b7] =>
      apply congrArg some
      apply UInt64.toNat_inj.mp
      rw [u64_pack_le_toNat, UInt64.toNat_ofNat']
      have hlt :
          b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat +
          4294967296 * b4.toNat + 1099511627776 * b5.toNat + 281474976710656 * b6.toNat +
          72057594037927936 * b7.toNat < 2 ^ 64 := by
        rw [← u64_pack_le_toNat]
        exact UInt64.toNat_lt _
      exact (Nat.mod_eq_of_lt hlt).symm
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _, _, _] | [_, _, _, _, _, _, _]
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem decodeU64LE?_roundtrip (v : UInt64) :
    BitcoinLedger.Basic.decodeU64LE? (BitcoinLedger.Basic.encodeU64LE v) = some v := by
  rw [decodeU64LE?_eq, encodeU64LE_eq]
  exact InternalSpec.decodeU64LE?_roundtrip v

/-! ## Section 4: Canonical CompactSize / VarInt Refinement, Roundtrip & Non-Canonical Rejection -/

theorem encodeVarInt_eq (n : UInt64) :
    BitcoinLedger.Basic.encodeVarInt n = InternalSpec.encodeVarIntCanonical n := by
  unfold BitcoinLedger.Basic.encodeVarInt InternalSpec.encodeVarIntCanonical
  have e0 : n.toUInt8 = UInt8.ofNat (n.toNat % 256) := nat_toUInt8_eq_ofNat_mod n.toNat
  have e1 := u64_shift_byte n 8 (by decide)
  have e2 := u64_shift_byte n 16 (by decide)
  have e3 := u64_shift_byte n 24 (by decide)
  have e4 := u64_shift_byte n 32 (by decide)
  have e5 := u64_shift_byte n 40 (by decide)
  have e6 := u64_shift_byte n 48 (by decide)
  have e7 := u64_shift_byte n 56 (by decide)
  cases hfc : decide (n ≤ 0xFC)
  · have hnfc : ¬ (n.toNat ≤ 0xFC) :=
      fun h => of_decide_eq_false hfc (UInt64.le_iff_toNat_le.mpr h)
    simp only [Bool.false_eq_true, hnfc, ↓reduceIte]
    cases h16 : decide (n ≤ 0xFFFF)
    · have hn16 : ¬ (n.toNat ≤ 0xFFFF) :=
        fun h => of_decide_eq_false h16 (UInt64.le_iff_toNat_le.mpr h)
      simp only [Bool.false_eq_true, hn16, ↓reduceIte]
      cases h32 : decide (n ≤ 0xFFFFFFFF)
      · have hn32 : ¬ (n.toNat ≤ 0xFFFFFFFF) :=
          fun h => of_decide_eq_false h32 (UInt64.le_iff_toNat_le.mpr h)
        simp only [Bool.false_eq_true, hn32, ↓reduceIte]
        rw [e0, e1, e2, e3, e4, e5, e6, e7]
        rfl
      · have hy32 : n.toNat ≤ 0xFFFFFFFF := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h32)
        simp only [hy32, ↓reduceIte]
        rw [e0, e1, e2, e3]
        rfl
    · have hy16 : n.toNat ≤ 0xFFFF := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h16)
      simp only [hy16, ↓reduceIte]
      rw [e0, e1]
      rfl
  · have hyfc : n.toNat ≤ 0xFC := UInt64.le_iff_toNat_le.mp (of_decide_eq_true hfc)
    simp only [hyfc, ↓reduceIte]
    have hlt256 : n.toNat < 256 := Nat.lt_of_le_of_lt hyfc (by decide)
    rw [e0, Nat.mod_eq_of_lt hlt256]

theorem varIntByteLen_eq_size (n : UInt64) :
    BitcoinLedger.Basic.varIntByteLen n = (BitcoinLedger.Basic.encodeVarInt n).size := by
  unfold BitcoinLedger.Basic.varIntByteLen BitcoinLedger.Basic.encodeVarInt
  cases decide (n ≤ 0xFC) <;>
    cases decide (n ≤ 0xFFFF) <;>
    cases decide (n ≤ 0xFFFFFFFF) <;> rfl

theorem encodeVarInt_isCanonical (n : UInt64) :
    InternalSpec.isCanonicalVarInt n (BitcoinLedger.Basic.encodeVarInt n) := by
  rw [encodeVarInt_eq]
  exact InternalSpec.encodeVarIntCanonical_isCanonical n

private theorem u16_in_u64_toNat (b0 b1 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8)).toNat = b0.toNat + 256 * b1.toNat := by
  rw [UInt64.toNat_or, u8_shiftLeft_u64_toNat b1 8 (by decide)]
  change b0.toNat ||| (b1.toNat <<< 8) = _
  exact nat_or_shiftLeft_eq_add b0.toNat_lt

private theorem u32_in_u64_toNat (b0 b1 b2 b3 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
      u8_shiftLeft_u64_toNat b1 8 (by decide),
      u8_shiftLeft_u64_toNat b2 16 (by decide),
      u8_shiftLeft_u64_toNat b3 24 (by decide)]
  change b0.toNat ||| (b1.toNat <<< 8) ||| (b2.toNat <<< 16) ||| (b3.toNat <<< 24) = _
  rw [nat_or_shiftLeft_eq_add b0.toNat_lt]
  have lt16 : b0.toNat + 2 ^ 8 * b1.toNat < 2 ^ 16 := by
    have h1 : 2 ^ 8 * b1.toNat ≤ 256 * 255 := Nat.mul_le_mul_left 256 (Nat.le_of_lt_succ b1.toNat_lt)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt_succ b0.toNat_lt) h1) (by decide)
  rw [nat_or_shiftLeft_eq_add lt16]
  have lt24 : b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat < 2 ^ 24 := by
    have h1 : b0.toNat + 2 ^ 8 * b1.toNat ≤ 65535 := Nat.le_of_lt_succ lt16
    have h2 : 2 ^ 16 * b2.toNat ≤ 65536 * 255 := Nat.mul_le_mul_left 65536 (Nat.le_of_lt_succ b2.toNat_lt)
    exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) (by decide)
  exact nat_or_shiftLeft_eq_add lt24

theorem decodeVarIntCanonical?_eq (bs : ByteArray) :
    BitcoinLedger.Basic.decodeVarIntCanonical? bs = InternalSpec.decodeVarIntCanonical? bs := by
  unfold BitcoinLedger.Basic.decodeVarIntCanonical? InternalSpec.decodeVarIntCanonical?
  match bs.data.toList with
  | [] => rfl
  | [b0] =>
      cases h : decide (b0 ≤ (0xFC : UInt8))
      · have hn : ¬ (b0.toNat ≤ 0xFC) := fun hle => of_decide_eq_false h (UInt8.le_iff_toNat_le.mpr hle)
        simp only [h, Bool.false_eq_true, hn, ↓reduceIte]
      · have hy : b0.toNat ≤ 0xFC := UInt8.le_iff_toNat_le.mp (of_decide_eq_true h)
        simp only [h, hy, ↓reduceIte]
        apply congrArg some
        apply UInt64.toNat_inj.mp
        have hb0 : b0.toUInt64.toNat = b0.toNat := rfl
        rw [hb0, UInt64.toNat_ofNat']
        have hlt : b0.toNat < 2 ^ 64 := Nat.lt_trans b0.toNat_lt (by decide)
        exact (Nat.mod_eq_of_lt hlt).symm
  | [_, _] => rfl
  | [tag, b0, b1] =>
      dsimp only
      cases ht : decide (tag = 0xFD)
      · have hnt : tag ≠ 0xFD := of_decide_eq_false ht
        simp only [Bool.false_eq_true, hnt, ↓reduceIte]
      · have hyt : tag = 0xFD := of_decide_eq_true ht
        subst hyt
        simp only [↓reduceIte]
        have hvalNat : (b0.toUInt64 ||| (b1.toUInt64 <<< 8)).toNat = b0.toNat + 256 * b1.toNat :=
          u16_in_u64_toNat b0 b1
        cases hm : decide ((0xFD : UInt64) ≤ (b0.toUInt64 ||| (b1.toUInt64 <<< 8)))
        · have hnm : ¬ (0xFD ≤ b0.toNat + 256 * b1.toNat) := by
            intro hle
            apply of_decide_eq_false hm
            rw [UInt64.le_iff_toNat_le, hvalNat]
            exact hle
          simp only [Bool.false_eq_true, hnm, ↓reduceIte]
        · have hym : 0xFD ≤ b0.toNat + 256 * b1.toNat := by
            rw [← hvalNat]
            exact UInt64.le_iff_toNat_le.mp (of_decide_eq_true hm)
          simp only [hym, ↓reduceIte]
          apply congrArg some
          apply UInt64.toNat_inj.mp
          rw [hvalNat, UInt64.toNat_ofNat']
          have hlt : b0.toNat + 256 * b1.toNat < 2 ^ 64 := by
            rw [← hvalNat]
            exact UInt64.toNat_lt _
          exact (Nat.mod_eq_of_lt hlt).symm
  | [_, _, _, _] => rfl
  | [tag, b0, b1, b2, b3] =>
      dsimp only
      cases ht : decide (tag = 0xFE)
      · have hnt : tag ≠ 0xFE := of_decide_eq_false ht
        simp only [Bool.false_eq_true, hnt, ↓reduceIte]
      · have hyt : tag = 0xFE := of_decide_eq_true ht
        subst hyt
        simp only [↓reduceIte]
        have hvalNat :
            (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)).toNat =
              b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat :=
          u32_in_u64_toNat b0 b1 b2 b3
        cases hm : decide ((0x10000 : UInt64) ≤
            (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24)))
        · have hnm : ¬ (0x10000 ≤ b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat) := by
            intro hle
            apply of_decide_eq_false hm
            rw [UInt64.le_iff_toNat_le, hvalNat]
            exact hle
          simp only [Bool.false_eq_true, hnm, ↓reduceIte]
        · have hym : 0x10000 ≤ b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
            rw [← hvalNat]
            exact UInt64.le_iff_toNat_le.mp (of_decide_eq_true hm)
          simp only [hym, ↓reduceIte]
          apply congrArg some
          apply UInt64.toNat_inj.mp
          rw [hvalNat, UInt64.toNat_ofNat']
          have hlt : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 2 ^ 64 := by
            rw [← hvalNat]
            exact UInt64.toNat_lt _
          exact (Nat.mod_eq_of_lt hlt).symm
  | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] => rfl
  | [tag, b0, b1, b2, b3, b4, b5, b6, b7] =>
      dsimp only
      cases ht : decide (tag = 0xFF)
      · have hnt : tag ≠ 0xFF := of_decide_eq_false ht
        simp only [Bool.false_eq_true, hnt, ↓reduceIte]
      · have hyt : tag = 0xFF := of_decide_eq_true ht
        subst hyt
        simp only [↓reduceIte]
        have hvalNat := u64_pack_le_toNat b0 b1 b2 b3 b4 b5 b6 b7
        cases hm : decide ((0x100000000 : UInt64) ≤
            (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
             (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)))
        · have hnm := fun hle => of_decide_eq_false hm (UInt64.le_iff_toNat_le.mpr hle)
          change ¬ (0x100000000 ≤ _) at hnm
          rw [hvalNat] at hnm
          simp only [Bool.false_eq_true, hnm, ↓reduceIte]
        · have hym := UInt64.le_iff_toNat_le.mp (of_decide_eq_true hm)
          change 0x100000000 ≤ _ at hym
          rw [hvalNat] at hym
          simp only [hym, ↓reduceIte]
          apply congrArg some
          apply UInt64.toNat_inj.mp
          rw [hvalNat, UInt64.toNat_ofNat']
          have hlt := UInt64.toNat_lt
            (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
             (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))
          rw [hvalNat] at hlt
          exact (Nat.mod_eq_of_lt hlt).symm
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem decodeVarIntCanonicalPrefix?_eq (bs : ByteArray) :
    BitcoinLedger.Basic.decodeVarIntCanonicalPrefix? bs = InternalSpec.decodeVarIntCanonicalPrefix? bs := by
  unfold BitcoinLedger.Basic.decodeVarIntCanonicalPrefix? InternalSpec.decodeVarIntCanonicalPrefix?
  cases bs.data.toList with
  | nil => rfl
  | cons tag _ =>
      have hNeeded :
          (if decide (tag ≤ (0xFC : UInt8)) = true then 1
           else if decide (tag = 0xFD) = true then 3
           else if decide (tag = 0xFE) = true then 5
           else 9) =
          (if tag.toNat ≤ 0xFC then 1
           else if tag = 0xFD then 3
           else if tag = 0xFE then 5
           else 9) := by
        cases h1 : decide (tag ≤ (0xFC : UInt8))
        · have hn1 : ¬ (tag.toNat ≤ 0xFC) :=
            fun h => of_decide_eq_false h1 (UInt8.le_iff_toNat_le.mpr h)
          simp only [Bool.false_eq_true, hn1, ↓reduceIte]
          cases h2 : decide (tag = 0xFD)
          · have hn2 : tag ≠ 0xFD := of_decide_eq_false h2
            simp only [Bool.false_eq_true, hn2, ↓reduceIte]
            cases h3 : decide (tag = 0xFE)
            · have hn3 : tag ≠ 0xFE := of_decide_eq_false h3
              simp only [Bool.false_eq_true, hn3, ↓reduceIte]
            · have hy3 : tag = 0xFE := of_decide_eq_true h3
              simp only [hy3, ↓reduceIte]
          · have hy2 : tag = 0xFD := of_decide_eq_true h2
            simp only [hy2, ↓reduceIte]
        · have hy1 : tag.toNat ≤ 0xFC := UInt8.le_iff_toNat_le.mp (of_decide_eq_true h1)
          simp only [hy1, ↓reduceIte]
      dsimp only
      rw [hNeeded, decodeVarIntCanonical?_eq]
      cases hsz : decide (bs.size < (if tag.toNat ≤ 0xFC then 1 else if tag = 0xFD then 3 else if tag = 0xFE then 5 else 9))
      · have hnsz := of_decide_eq_false hsz
        simp only [Bool.false_eq_true, hnsz, ↓reduceIte]
        rfl
      · have hysz := of_decide_eq_true hsz
        simp only [hysz, ↓reduceIte]

/-- Bijective roundtrip theorem for `encodeVarInt` and `decodeVarIntCanonical?`. -/
theorem decodeVarIntCanonical?_encodeVarInt (n : UInt64) :
    BitcoinLedger.Basic.decodeVarIntCanonical? (BitcoinLedger.Basic.encodeVarInt n) = some n := by
  rw [decodeVarIntCanonical?_eq, encodeVarInt_eq]
  exact InternalSpec.decodeVarIntCanonical_roundtrip n

theorem encodeVarInt_decodeVarIntCanonical? {bs : ByteArray} {n : UInt64}
    (h : BitcoinLedger.Basic.decodeVarIntCanonical? bs = some n) :
    BitcoinLedger.Basic.encodeVarInt n = bs := by
  rw [decodeVarIntCanonical?_eq] at h
  rw [encodeVarInt_eq]
  have h1 := InternalSpec.encodeVarIntCanonical_isCanonical n
  have h2 := InternalSpec.isCanonicalVarInt_of_decodeVarIntCanonical h
  exact InternalSpec.isCanonicalVarInt_unique_bytes h1 h2

/-- Non-canonical CompactSize encodings are rejected across all three multi-byte tags (`0xFD`, `0xFE`, `0xFF`). -/
theorem decodeVarIntCanonical?_rejects_noncanonical :
    (∀ b0 b1 : UInt8, b0.toNat + 256 * b1.toNat < 0xFD →
      BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFD, b0, b1]) = none) ∧
    (∀ b0 b1 b2 b3 : UInt8, b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 0x10000 →
      BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFE, b0, b1, b2, b3]) = none) ∧
    BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFD, 0xFC, 0x00]) = none ∧
    BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFE, 0xFF, 0xFF, 0x00, 0x00]) = none ∧
    BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00]) = none := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · intro b0 b1 hlt
    rw [decodeVarIntCanonical?_eq]
    exact InternalSpec.decodeVarIntCanonical_rejects_nonminimal_u16 b0 b1 hlt
  · intro b0 b1 b2 b3 hlt
    rw [decodeVarIntCanonical?_eq]
    exact InternalSpec.decodeVarIntCanonical_rejects_nonminimal_u32 b0 b1 b2 b3 hlt

/-! ## Section 5: Network Parameters & Error Mapping Refinement, Roundtrip & Injectivity -/

theorem networkParams_eq (net : InternalSpec.Network) :
    BitcoinLedger.Basic.networkParams net = net.params := by
  cases net <;> rfl

theorem bolosStatusWordToU16_eq (sw : InternalSpec.BolosStatusWord) :
    BitcoinLedger.Basic.bolosStatusWordToU16 sw = sw.toUInt16 := by
  cases sw <;> rfl

theorem bolosStatusWordFromU16?_eq (w : UInt16) :
    BitcoinLedger.Basic.bolosStatusWordFromU16? w = InternalSpec.BolosStatusWord.fromUInt16? w := rfl

theorem bolosStatusWord_roundtrip (sw : InternalSpec.BolosStatusWord) :
    BitcoinLedger.Basic.bolosStatusWordFromU16? (BitcoinLedger.Basic.bolosStatusWordToU16 sw) = some sw := by
  cases sw <;> rfl

theorem bolosStatusWordToU16_injective {s1 s2 : InternalSpec.BolosStatusWord}
    (h : BitcoinLedger.Basic.bolosStatusWordToU16 s1 = BitcoinLedger.Basic.bolosStatusWordToU16 s2) :
    s1 = s2 := by
  have r1 := bolosStatusWord_roundtrip s1
  have r2 := bolosStatusWord_roundtrip s2
  rw [h] at r1
  rw [r1] at r2
  exact Option.some.inj r2

theorem appErrorToCborU8_toNat_eq (e : InternalSpec.AppError) :
    (BitcoinLedger.Basic.appErrorToCborU8 e).toNat = e.toCborCode := by
  cases e <;> rfl

theorem appError_cbor_roundtrip (e : InternalSpec.AppError) :
    BitcoinLedger.Basic.appErrorFromCborU8? (BitcoinLedger.Basic.appErrorToCborU8 e) = some e := by
  cases e <;> rfl

theorem appErrorToCborU8_injective {e1 e2 : InternalSpec.AppError}
    (h : BitcoinLedger.Basic.appErrorToCborU8 e1 = BitcoinLedger.Basic.appErrorToCborU8 e2) :
    e1 = e2 := by
  have r1 := appError_cbor_roundtrip e1
  have r2 := appError_cbor_roundtrip e2
  rw [h] at r1
  rw [r1] at r2
  exact Option.some.inj r2

theorem specErrorToBolosSw_eq (err : InternalSpec.SpecError) :
    BitcoinLedger.Basic.specErrorToBolosSw err = err.toBolosStatusWord := by
  cases err <;> rfl

theorem specErrorToBolosU16_eq (err : InternalSpec.SpecError) :
    BitcoinLedger.Basic.specErrorToBolosU16 err = err.toBolosCode := by
  cases err <;> rfl

theorem specErrorToVanadiumError_eq (err : InternalSpec.SpecError) :
    BitcoinLedger.Basic.specErrorToVanadiumError err = err.toVanadiumError := by
  cases err <;> rfl

theorem specErrorToBolosU16_never_ok_or_interrupted (err : InternalSpec.SpecError) :
    BitcoinLedger.Basic.specErrorToBolosU16 err ≠ 0x9000 ∧
    BitcoinLedger.Basic.specErrorToBolosU16 err ≠ 0xE000 := by
  rw [specErrorToBolosU16_eq]
  exact InternalSpec.SpecError.toBolosCode_ne_ok_and_interrupted err

theorem specErrorTag_roundtrip (err : InternalSpec.SpecError) :
    BitcoinLedger.Basic.specErrorFromTag? (BitcoinLedger.Basic.specErrorToTag err) = some err ∧
    (BitcoinLedger.Basic.specErrorToTag err).toNat ≤ 18 := by
  cases err <;> decide

theorem specErrorToTag_injective {e1 e2 : InternalSpec.SpecError}
    (h : BitcoinLedger.Basic.specErrorToTag e1 = BitcoinLedger.Basic.specErrorToTag e2) :
    e1 = e2 := by
  have r1 := (specErrorTag_roundtrip e1).1
  have r2 := (specErrorTag_roundtrip e2).1
  rw [h] at r1
  rw [r1] at r2
  exact Option.some.inj r2

end Proofs.Basic

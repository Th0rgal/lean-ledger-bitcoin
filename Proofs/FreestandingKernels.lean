import InternalSpec
import BitcoinLedger.Basic
import BitcoinLedger.Bip32
import BitcoinLedger.Script
import BitcoinLedger.Psbt
import BitcoinLedger.WalletPolicy
import BitcoinLedger.FreestandingKernels
import Proofs.Basic
import Proofs.Bip32
import Proofs.Script
import Proofs.Psbt
import Proofs.WalletPolicy

namespace Proofs.FreestandingKernels

/-!
# `Proofs.FreestandingKernels` — Machine-Checked Refinement Proofs for Freestanding C99 Kernels

Constructive (`0 Classical.choice`, `0 sorryAx`, `0 native_decide`) refinement theorems
proving that the `@[export llb_*]` scalar and buffer entrypoints in `BitcoinLedger.FreestandingKernels`
refine the corresponding executable primitives in `BitcoinLedger.{Basic,Bip32,Script,Psbt,WalletPolicy}`
and the normative specification in `InternalSpec.{Basic,Bip32,Script,Psbt,WalletPolicy,MerkleProtocol}`.
-/

open BitcoinLedger.FreestandingKernels

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

/-! ## 1. Version & Satoshi Overflow-Safe Arithmetic Refinement -/

theorem llbVersionPacked_bytes :
    (llbVersionPacked >>> 16).toUInt8 = InternalSpec.ledgerBitcoinTargetVersion.major ∧
    ((llbVersionPacked >>> 8) &&& 0xff).toUInt8 = InternalSpec.ledgerBitcoinTargetVersion.minor ∧
    (llbVersionPacked &&& 0xff).toUInt8 = InternalSpec.ledgerBitcoinTargetVersion.patch := by
  exact ⟨rfl, rfl, rfl⟩

theorem llbVersionPacked_eq_hex :
    llbVersionPacked = 0x00020401 := rfl

theorem llbValidAmount_eq (sats : UInt64) :
    llbValidAmount sats = BitcoinLedger.Basic.isValidAmount sats := rfl

theorem llbValidAmount_iff (sats : UInt64) :
    llbValidAmount sats = true ↔ InternalSpec.ValidAmount sats :=
  Proofs.Basic.isValidAmount_iff sats

theorem llbCheckedAddSats_refines (a b : UInt64) :
    (if llbCheckedAddSatsOk a b then some (llbCheckedAddSatsVal a b) else none) =
      BitcoinLedger.Basic.checkedAddSats? a b ∧
    (if llbCheckedAddSatsOk a b then some (llbCheckedAddSatsVal a b) else none) =
      InternalSpec.addAmounts? a b := by
  have h1 :
      (if llbCheckedAddSatsOk a b then some (llbCheckedAddSatsVal a b) else none) =
        BitcoinLedger.Basic.checkedAddSats? a b := by
    unfold llbCheckedAddSatsVal BitcoinLedger.Basic.checkedAddSats?
    have hokEq : llbCheckedAddSatsOk a b =
        (decide (a ≤ BitcoinLedger.Basic.MAX_MONEY) && decide (b ≤ BitcoinLedger.Basic.MAX_MONEY - a)) := rfl
    rw [← hokEq]
    cases llbCheckedAddSatsOk a b <;> rfl
  exact ⟨h1, h1.trans (Proofs.Basic.checkedAddSats?_eq a b)⟩

theorem llbCheckedSubSats_refines (a b : UInt64) :
    (if llbCheckedSubSatsOk a b then some (llbCheckedSubSatsVal a b) else none) =
      BitcoinLedger.Basic.checkedSubSats? a b ∧
    (if llbCheckedSubSatsOk a b then some (llbCheckedSubSatsVal a b) else none) =
      InternalSpec.subAmounts? a b := by
  have h1 :
      (if llbCheckedSubSatsOk a b then some (llbCheckedSubSatsVal a b) else none) =
        BitcoinLedger.Basic.checkedSubSats? a b := by
    unfold llbCheckedSubSatsVal BitcoinLedger.Basic.checkedSubSats?
    have hokEq : llbCheckedSubSatsOk a b =
        (decide (a ≤ BitcoinLedger.Basic.MAX_MONEY) && decide (b ≤ a)) := rfl
    rw [← hokEq]
    cases llbCheckedSubSatsOk a b <;> rfl
  exact ⟨h1, h1.trans (Proofs.Basic.checkedSubSats?_eq a b)⟩

/-! ## 2. CompactSize / VarInt Header Length & Canonicality Refinement -/

theorem llbVarIntPrefixIsCanonical_encodeVarInt (n : UInt64) :
    llbVarIntPrefixIsCanonical ((BitcoinLedger.Basic.encodeVarInt n).data.toList.headD 0) n = true := by
  unfold BitcoinLedger.Basic.encodeVarInt
  cases hfc : decide (n ≤ 0xFC)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnfc : ¬ (n ≤ 0xFC) := of_decide_eq_false hfc
    have hge_fd : (0xFD : UInt64) ≤ n := by
      have hgt : 0xFC < n.toNat := Nat.lt_of_not_le (fun h => hnfc (UInt64.le_iff_toNat_le.mpr h))
      exact UInt64.le_iff_toNat_le.mpr hgt
    cases hffff : decide (n ≤ 0xFFFF)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hnffff : ¬ (n ≤ 0xFFFF) := of_decide_eq_false hffff
      have hge_10000 : (0x10000 : UInt64) ≤ n := by
        have hgt : 0xFFFF < n.toNat := Nat.lt_of_not_le (fun h => hnffff (UInt64.le_iff_toNat_le.mpr h))
        exact UInt64.le_iff_toNat_le.mpr hgt
      cases h32 : decide (n ≤ 0xFFFFFFFF)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hn32 : ¬ (n ≤ 0xFFFFFFFF) := of_decide_eq_false h32
        have hge_32 : (0x100000000 : UInt64) ≤ n := by
          have hgt : 0xFFFFFFFF < n.toNat := Nat.lt_of_not_le (fun h => hn32 (UInt64.le_iff_toNat_le.mpr h))
          exact UInt64.le_iff_toNat_le.mpr hgt
        have hhead : ((ByteArray.mk #[0xFF, n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8,
            (n >>> 24).toUInt8, (n >>> 32).toUInt8, (n >>> 40).toUInt8, (n >>> 48).toUInt8,
            (n >>> 56).toUInt8]).data.toList.headD 0) = 0xFF := rfl
        rw [hhead]
        unfold llbVarIntPrefixIsCanonical
        change decide ((0x100000000 : UInt64) ≤ n) = true
        exact decide_eq_true hge_32
      · simp only [↓reduceIte]
        have hle32 : n ≤ 0xFFFFFFFF := of_decide_eq_true h32
        have hhead : ((ByteArray.mk #[0xFE, n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8,
            (n >>> 24).toUInt8]).data.toList.headD 0) = 0xFE := rfl
        rw [hhead]
        unfold llbVarIntPrefixIsCanonical
        change (decide ((0x10000 : UInt64) ≤ n) && decide (n ≤ 0xFFFFFFFF)) = true
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hge_10000, decide_eq_true hle32⟩
    · simp only [↓reduceIte]
      have hleffff : n ≤ 0xFFFF := of_decide_eq_true hffff
      have hhead : ((ByteArray.mk #[0xFD, n.toUInt8, (n >>> 8).toUInt8]).data.toList.headD 0) = 0xFD := rfl
      rw [hhead]
      unfold llbVarIntPrefixIsCanonical
      change (decide ((0xFD : UInt64) ≤ n) && decide (n ≤ 0xFFFF)) = true
      exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hge_fd, decide_eq_true hleffff⟩
  · simp only [↓reduceIte]
    have hlefc : n ≤ 0xFC := of_decide_eq_true hfc
    have hleNat : n.toNat ≤ 0xFC := UInt64.le_iff_toNat_le.mp hlefc
    have hlt256 : n.toNat < 256 := Nat.lt_of_le_of_lt hleNat (by decide)
    have htagLe : n.toUInt8 ≤ 0xFC := by
      rw [UInt8.le_iff_toNat_le, UInt64.toNat_toUInt8, Nat.mod_eq_of_lt hlt256]
      exact hleNat
    have hvalEq : n = n.toUInt8.toUInt64 := by
      apply UInt64.toNat_inj.mp
      rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, Nat.mod_eq_of_lt hlt256]
    have hhead : ((ByteArray.mk #[n.toUInt8]).data.toList.headD 0) = n.toUInt8 := rfl
    rw [hhead]
    unfold llbVarIntPrefixIsCanonical
    rw [decide_eq_true htagLe]
    simp only [↓reduceIte]
    exact decide_eq_true hvalEq

/-! ## 3. BIP-32 Hardened Index & Depth Gate Refinement -/

theorem llbBip32IsHardened_eq (idx : UInt32) :
    llbBip32IsHardened idx = BitcoinLedger.Bip32.isHardened idx ∧
    llbBip32IsHardened idx = InternalSpec.isHardened idx :=
  ⟨rfl, Proofs.Bip32.isHardened_eq idx⟩

theorem llbBip32Unharden_eq (idx : UInt32) :
    llbBip32Unharden idx = BitcoinLedger.Bip32.unharden idx ∧
    llbBip32Unharden idx = InternalSpec.unharden idx :=
  ⟨rfl, Proofs.Bip32.unharden_eq idx⟩

theorem llbBip32BolosDepthOk_eq (path : InternalSpec.Bip32Path) (hbyte : path.size ≤ 255) :
    llbBip32BolosDepthOk (UInt8.ofNat path.size) = BitcoinLedger.Bip32.checkBolosDepth path := by
  unfold llbBip32BolosDepthOk BitcoinLedger.Bip32.checkBolosDepth BitcoinLedger.Bip32.MAX_BIP32_PATH_STEPS
  have hlt : path.size < 256 := Nat.lt_of_le_of_lt hbyte (by decide)
  have h1 : (UInt8.ofNat path.size ≤ 10) ↔ (path.size ≤ 10) := by
    rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
    rfl
  cases h : decide (path.size ≤ 10)
  · have hn : ¬ (UInt8.ofNat path.size ≤ 10) := fun hu => of_decide_eq_false h (h1.mp hu)
    simp [hn]
  · have hy : UInt8.ofNat path.size ≤ 10 := h1.mpr (of_decide_eq_true h)
    simp [hy]

theorem llbBip32VanadiumDepthOk_eq (path : InternalSpec.Bip32Path) (hbyte : path.size ≤ 255) :
    llbBip32VanadiumDepthOk (UInt8.ofNat path.size) = BitcoinLedger.Bip32.checkVanadiumDepth path := by
  unfold llbBip32VanadiumDepthOk BitcoinLedger.Bip32.checkVanadiumDepth BitcoinLedger.Bip32.MAX_BIP32_PATH_LEN
  have hlt : path.size < 256 := Nat.lt_of_le_of_lt hbyte (by decide)
  have h1 : (UInt8.ofNat path.size ≤ 16) ↔ (path.size ≤ 16) := by
    rw [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
    rfl
  cases h : decide (path.size ≤ 16)
  · have hn : ¬ (UInt8.ofNat path.size ≤ 16) := fun hu => of_decide_eq_false h (h1.mp hu)
    simp [hn]
  · have hy : UInt8.ofNat path.size ≤ 16 := h1.mpr (of_decide_eq_true h)
    simp [hy]

theorem llbBip32StandardPurposeOk_eq (purposeStep : UInt32) :
    llbBip32StandardPurposeOk purposeStep =
      (BitcoinLedger.Bip32.isHardened purposeStep &&
        BitcoinLedger.Bip32.isStandard3StepPurpose (BitcoinLedger.Bip32.unharden purposeStep)) := rfl

/-! ## 4. Script, SegWit, Bech32 Polymod & `MINIMALDATA` Refinement -/

theorem llbWitnessOpcodeToVersion_refines (op : UInt8) :
    (if decide (llbWitnessOpcodeToVersion op = 0xFF) then none else some (llbWitnessOpcodeToVersion op)) =
      BitcoinLedger.Script.decodeWitnessVersionOpcode? op ∧
    (if decide (llbWitnessOpcodeToVersion op = 0xFF) then none else some (llbWitnessOpcodeToVersion op)) =
      InternalSpec.decodeWitnessVersionOpcode? op := by
  have h1 :
      (if decide (llbWitnessOpcodeToVersion op = 0xFF) then none else some (llbWitnessOpcodeToVersion op)) =
        BitcoinLedger.Script.decodeWitnessVersionOpcode? op := by
    unfold llbWitnessOpcodeToVersion BitcoinLedger.Script.decodeWitnessVersionOpcode?
      BitcoinLedger.Script.OP_0 BitcoinLedger.Script.OP_1 BitcoinLedger.Script.OP_16
    cases h0 : decide (op = 0x00)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases h16 : (decide (0x51 ≤ op) && decide (op ≤ 0x60))
      · rfl
      · simp only [↓reduceIte]
        have ⟨hge, hle⟩ := Bool.and_eq_true_iff.mp h16
        have hgeNat : 0x51 ≤ op.toNat := UInt8.le_iff_toNat_le.mp (of_decide_eq_true hge)
        have hleNat : op.toNat ≤ 0x60 := UInt8.le_iff_toNat_le.mp (of_decide_eq_true hle)
        have hne : op - 0x50 ≠ 0xFF := by
          intro heq
          have hsub : (op - 0x50).toNat = op.toNat - 0x50 :=
            UInt8.toNat_sub_of_le op 0x50 (UInt8.le_iff_toNat_le.mpr (Nat.le_trans (by decide) hgeNat))
          have h255 : (op - 0x50).toNat = 255 := congrArg UInt8.toNat heq
          rw [hsub] at h255
          have hbound : op.toNat - 0x50 ≤ 16 :=
            Nat.sub_le_of_le_add (by
              have : 16 + 0x50 = 0x60 := rfl
              rw [this]
              exact hleNat)
          rw [h255] at hbound
          exact absurd hbound (by decide)
        simp [hne]
    · simp
  exact ⟨h1, h1.trans (Proofs.Script.decodeWitnessVersionOpcode?_eq op)⟩

theorem llbSegwitProgramValid_refines (witver : UInt8) (witprog : ByteArray)
    (hlen : witprog.size ≤ 255) :
    llbSegwitProgramValid witver (UInt8.ofNat witprog.size) =
      BitcoinLedger.Script.isValidSegwitProgram witver witprog ∧
    llbSegwitProgramValid witver (UInt8.ofNat witprog.size) =
      InternalSpec.isValidSegwitProgram witver witprog := by
  have hlt : witprog.size < 256 := Nat.lt_of_le_of_lt hlen (by decide)
  have htoNat : (UInt8.ofNat witprog.size).toNat = witprog.size := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt]
  have h1 :
      llbSegwitProgramValid witver (UInt8.ofNat witprog.size) =
        BitcoinLedger.Script.isValidSegwitProgram witver witprog := by
    unfold llbSegwitProgramValid BitcoinLedger.Script.isValidSegwitProgram
    cases h0 : decide (witver = 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases h16 : decide (witver ≤ 16)
      · rfl
      · simp only [↓reduceIte]
        have h2 : decide ((2 : UInt8) ≤ UInt8.ofNat witprog.size) = decide (2 ≤ witprog.size) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, UInt8.le_iff_toNat_le, htoNat]
          rfl
        have h40 : decide (UInt8.ofNat witprog.size ≤ 40) = decide (witprog.size ≤ 40) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, UInt8.le_iff_toNat_le, htoNat]
          rfl
        rw [h2, h40]
    · simp only [↓reduceIte]
      have h20 : decide (UInt8.ofNat witprog.size = 20) = decide (witprog.size = 20) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, ← UInt8.toNat_inj, htoNat]
        rfl
      have h32 : decide (UInt8.ofNat witprog.size = 32) = decide (witprog.size = 32) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, ← UInt8.toNat_inj, htoNat]
        rfl
      rw [h20, h32]
  exact ⟨h1, h1.trans (Proofs.Script.isValidSegwitProgram_eq witver witprog)⟩

/-! ## 5. BOLOS APDU, Sighash & Merkle Scalar Refinement + Concrete Witnesses -/

private theorem forall_u8_of_range {p : UInt8 → Bool}
    (h : (List.range 256).all (fun k => p (UInt8.ofNat k)) = true) :
    ∀ b : UInt8, p b = true := by
  intro b
  have hmem : b.toNat ∈ List.range 256 := List.mem_range.mpr b.toNat_lt
  have hb := List.all_eq_true.mp h b.toNat hmem
  have heq : UInt8.ofNat b.toNat = b := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt b.toNat_lt]
  rwa [heq] at hb

set_option maxRecDepth 16384 in
private theorem u8_segwit_sighash_valid_eq (b : UInt8) :
    (decide (1 ≤ b.toUInt32 &&& 0x7F) && decide (b.toUInt32 &&& 0x7F ≤ 3)) =
      decide ((InternalSpec.Psbt.classifySighash .segwitV0 (some b.toUInt32)).1 ≠ .unsupported) := by
  have hall :
      ∀ x : UInt8,
        decide
          ((decide (1 ≤ x.toUInt32 &&& 0x7F) && decide (x.toUInt32 &&& 0x7F ≤ 3)) =
            decide ((InternalSpec.Psbt.classifySighash .segwitV0 (some x.toUInt32)).1 ≠ .unsupported)) = true :=
    forall_u8_of_range (by decide)
  exact of_decide_eq_true (hall b)

theorem llbSighashTypeValid_refines_psbt (sighashU32 : UInt32) :
    llbSighashTypeValid sighashU32 =
      decide ((InternalSpec.Psbt.classifySighash .segwitV0 (some sighashU32)).1 ≠ .unsupported) := by
  cases hle : decide (sighashU32 ≤ 0xFF)
  · have hgt : sighashU32.toNat > 0xFF :=
      Nat.lt_of_not_le (fun h => of_decide_eq_false hle (UInt32.le_iff_toNat_le.mpr h))
    unfold llbSighashTypeValid InternalSpec.Psbt.classifySighash
    simp [hle, hgt]
  · have hleNat : sighashU32.toNat ≤ 0xFF := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hle)
    have hlt256 : sighashU32.toNat < 256 := Nat.lt_of_le_of_lt hleNat (by decide)
    have hb32 : sighashU32 = (UInt8.ofNat sighashU32.toNat).toUInt32 := by
      apply UInt32.toNat_inj.mp
      rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt256]
    unfold llbSighashTypeValid
    rw [hle, Bool.true_and, hb32]
    exact u8_segwit_sighash_valid_eq (UInt8.ofNat sighashU32.toNat)

set_option maxRecDepth 16384 in
theorem llbTaprootSighashValid_refines_psbt (sighashByte : UInt8) :
    llbTaprootSighashValid sighashByte =
      decide ((InternalSpec.Psbt.classifySighash .taprootV1 (some sighashByte.toUInt32)).1 ≠ .unsupported) := by
  have hall :
      ∀ x : UInt8,
        decide
          (llbTaprootSighashValid x =
            decide ((InternalSpec.Psbt.classifySighash .taprootV1 (some x.toUInt32)).1 ≠ .unsupported)) = true :=
    forall_u8_of_range (by decide)
  exact of_decide_eq_true (hall sighashByte)

set_option maxRecDepth 16384 in

/-! ## 6. Wave 4 BOLOS Optimization Kernels — Machine-Checked Refinement (`0 Classical.choice`) -/

private def B32 : Nat := 4294967296
private def B64 : Nat := 18446744073709551616
private def M0  : Nat := 0x8461CEFD
private def M1  : Nat := 0xABCC7711
private def M64 : Nat := 0xABCC77118461CEFD

private theorem div_lt_of_lt_mul_c {a b c : Nat} (h : a < b * c) : a / b < c := by
  have h1 : b * (a / b) ≤ a := Nat.mul_div_le a b
  have h2 : b * (a / b) < b * c := Nat.lt_of_le_of_lt h1 h
  exact Nat.lt_of_not_le (fun hle => Nat.lt_irrefl (b * c) (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left b hle) h2))

private theorem mulU32ToU64_toNat (a b : UInt32) :
    (mulU32ToU64 a b).toNat = a.toNat * b.toNat := by
  unfold mulU32ToU64
  rw [UInt64.toNat_mul, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  have ha : a.toNat ≤ 4294967295 := Nat.le_sub_one_of_lt a.toNat_lt
  have hb : b.toNat ≤ 4294967295 := Nat.le_sub_one_of_lt b.toNat_lt
  have hprod : a.toNat * b.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul ha hb
  have hlt : a.toNat * b.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt hprod (by decide)
  exact Nat.mod_eq_of_lt hlt

private theorem nat_shr_32 (n : Nat) : n >>> 32 = n / B32 :=
  Nat.shiftRight_eq_div_pow n 32

private theorem mulHiRecip1e8_toNat (x : UInt64) :
    (mulHiRecip1e8 x).toNat = (x.toNat * M64) / B64 := by
  unfold mulHiRecip1e8
  dsimp only
  let p00 := mulU32ToU64 x.toUInt32 0x8461CEFD
  let p01 := mulU32ToU64 x.toUInt32 0xABCC7711
  let p10 := mulU32ToU64 (x >>> 32).toUInt32 0x8461CEFD
  let p11 := mulU32ToU64 (x >>> 32).toUInt32 0xABCC7711
  let midU := (p00 >>> 32) + p01.toUInt32.toUInt64 + p10.toUInt32.toUInt64
  change (p11 + (p01 >>> 32) + (p10 >>> 32) + (midU >>> 32)).toNat = (x.toNat * M64) / B64
  let a0 := x.toNat % B32
  let a1 := x.toNat / B32
  have ha0_lt : a0 < B32 := Nat.mod_lt _ (by decide)
  have ha1_lt : a1 < B32 := div_lt_of_lt_mul_c (by
    have : B32 * B32 = 2 ^ 64 := rfl
    rw [this]; exact x.toNat_lt)
  have hx0 : x.toUInt32.toNat = a0 := UInt64.toNat_toUInt32 x
  have hx1 : (x >>> 32).toUInt32.toNat = a1 := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    have hsh : (32 : UInt64).toNat % 64 = 32 := rfl
    rw [hsh, nat_shr_32]
    exact Nat.mod_eq_of_lt ha1_lt
  have hp00 : p00.toNat = a0 * M0 := by dsimp [p00]; rw [mulU32ToU64_toNat, hx0]; rfl
  have hp01 : p01.toNat = a0 * M1 := by dsimp [p01]; rw [mulU32ToU64_toNat, hx0]; rfl
  have hp10 : p10.toNat = a1 * M0 := by dsimp [p10]; rw [mulU32ToU64_toNat, hx1]; rfl
  have hp11 : p11.toNat = a1 * M1 := by dsimp [p11]; rw [mulU32ToU64_toNat, hx1]; rfl
  have hb1 : (a0 * M0) / B32 < B32 :=
    div_lt_of_lt_mul_c (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right ha0_lt (by decide)) (by decide))
  have hb2 : (a0 * M1) % B32 < B32 := Nat.mod_lt _ (by decide)
  have hb3 : (a1 * M0) % B32 < B32 := Nat.mod_lt _ (by decide)
  have hmid_val : midU.toNat = (a0 * M0) / B32 + (a0 * M1) % B32 + (a1 * M0) % B32 := by
    dsimp [midU]
    have ht1 : (p00 >>> 32).toNat = (a0 * M0) / B32 := by
      rw [UInt64.toNat_shiftRight, hp00]; exact nat_shr_32 _
    have ht2 : p01.toUInt32.toUInt64.toNat = (a0 * M1) % B32 := by
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, hp01]; rfl
    have ht3 : p10.toUInt32.toUInt64.toNat = (a1 * M0) % B32 := by
      rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, hp10]; rfl
    rw [UInt64.toNat_add, UInt64.toNat_add, ht1, ht2, ht3]
    have hs12 : (a0 * M0) / B32 + (a0 * M1) % B32 < 2 ^ 64 :=
      Nat.lt_trans (Nat.add_lt_add hb1 hb2) (by decide)
    rw [Nat.mod_eq_of_lt hs12]
    have hs123 : (a0 * M0) / B32 + (a0 * M1) % B32 + (a1 * M0) % B32 < 2 ^ 64 :=
      Nat.lt_trans (Nat.add_lt_add (Nat.add_lt_add hb1 hb2) hb3) (by decide)
    exact Nat.mod_eq_of_lt hs123
  have hs1 : (p01 >>> 32).toNat = (a0 * M1) / B32 := by
    rw [UInt64.toNat_shiftRight, hp01]; exact nat_shr_32 _
  have hs2 : (p10 >>> 32).toNat = (a1 * M0) / B32 := by
    rw [UInt64.toNat_shiftRight, hp10]; exact nat_shr_32 _
  have hs3 : (midU >>> 32).toNat = ((a0 * M0) / B32 + (a0 * M1) % B32 + (a1 * M0) % B32) / B32 := by
    rw [UInt64.toNat_shiftRight, hmid_val]; exact nat_shr_32 _
  have hk0 : a1 * M1 ≤ 4294967295 * M1 := Nat.mul_le_mul_right M1 (Nat.le_sub_one_of_lt ha1_lt)
  have hk1 : (a0 * M1) / B32 < B32 :=
    div_lt_of_lt_mul_c (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right ha0_lt (by decide)) (by decide))
  have hk2 : (a1 * M0) / B32 < B32 :=
    div_lt_of_lt_mul_c (Nat.lt_trans (Nat.mul_lt_mul_of_pos_right ha1_lt (by decide)) (by decide))
  have hk3 : ((a0 * M0) / B32 + (a0 * M1) % B32 + (a1 * M0) % B32) / B32 < 3 :=
    div_lt_of_lt_mul_c (Nat.lt_of_lt_of_le (Nat.add_lt_add (Nat.add_lt_add hb1 hb2) hb3) (by decide))
  have htot_lt : a1 * M1 + (a0 * M1) / B32 + (a1 * M0) / B32 +
      ((a0 * M0) / B32 + (a0 * M1) % B32 + (a1 * M0) % B32) / B32 < 2 ^ 64 := by
    have hle := Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add hk0 (Nat.le_of_lt hk1)) (Nat.le_of_lt hk2))
      (Nat.le_of_lt hk3)
    exact Nat.lt_of_le_of_lt hle (by decide)
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, hp11, hs1, hs2, hs3]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) htot_lt))]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) htot_lt)]
  rw [Nat.mod_eq_of_lt htot_lt]
  let mid := (a0 * M0) / B32 + (a0 * M1) % B32 + (a1 * M0) % B32
  let lo0 := (a0 * M0) % B32
  let lo1 := mid % B32
  let hi := a1 * M1 + (a0 * M1) / B32 + (a1 * M0) / B32 + mid / B32
  have hx_decomp : x.toNat = B32 * a1 + a0 := (Nat.div_add_mod x.toNat B32).symm
  have hm_decomp : M64 = B32 * M1 + M0 := rfl
  have hp00_eq : a0 * M0 = B32 * ((a0 * M0) / B32) + lo0 := (Nat.div_add_mod (a0 * M0) B32).symm
  have hp01_eq : a0 * M1 = B32 * ((a0 * M1) / B32) + (a0 * M1) % B32 := (Nat.div_add_mod (a0 * M1) B32).symm
  have hp10_eq : a1 * M0 = B32 * ((a1 * M0) / B32) + (a1 * M0) % B32 := (Nat.div_add_mod (a1 * M0) B32).symm
  have hmid_eq : mid = B32 * (mid / B32) + lo1 := (Nat.div_add_mod mid B32).symm
  have hprod_eq : x.toNat * M64 = B64 * hi + (B32 * lo1 + lo0) := by
    have hbb : B32 * B32 = B64 := rfl
    rw [hx_decomp, hm_decomp, Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have ht1 : (B32 * a1) * (B32 * M1) = B64 * (a1 * M1) := by
      rw [← hbb]
      calc (B32 * a1) * (B32 * M1)
        _ = B32 * (a1 * (B32 * M1)) := Nat.mul_assoc _ _ _
        _ = B32 * ((a1 * B32) * M1) := by rw [Nat.mul_assoc a1 B32 M1]
        _ = B32 * ((B32 * a1) * M1) := by rw [Nat.mul_comm a1 B32]
        _ = (B32 * B32) * (a1 * M1) := by simp only [Nat.mul_assoc]
    have ht2 : (B32 * a1) * M0 = B32 * (a1 * M0) := Nat.mul_assoc B32 a1 M0
    have ht3 : a0 * (B32 * M1) = B32 * (a0 * M1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm a0 B32, Nat.mul_assoc]
    rw [ht1, ht2, ht3, hp00_eq, hp01_eq, hp10_eq]
    have hsub :
        B64 * (a1 * M1) + B32 * (B32 * ((a1 * M0) / B32) + (a1 * M0) % B32) +
        (B32 * (B32 * ((a0 * M1) / B32) + (a0 * M1) % B32) + (B32 * ((a0 * M0) / B32) + lo0)) =
        B64 * (a1 * M1 + (a0 * M1) / B32 + (a1 * M0) / B32) + B32 * mid + lo0 := by
      dsimp only [mid]
      simp only [Nat.mul_add, ← Nat.mul_assoc, hbb, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    rw [hsub, hmid_eq]
    dsimp only [hi]
    simp only [Nat.mul_add, ← Nat.mul_assoc, hbb, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hrem_lt : B32 * lo1 + lo0 < B64 := by
    have hlo1_le : lo1 ≤ 4294967295 := Nat.le_sub_one_of_lt (Nat.mod_lt mid (by decide))
    have hlo0_lt : lo0 < B32 := Nat.mod_lt (a0 * M0) (by decide)
    have h1 : B32 * lo1 + lo0 < B32 * 4294967295 + B32 :=
      Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left B32 hlo1_le) hlo0_lt
    exact Nat.lt_of_lt_of_le h1 (by decide)
  rw [hprod_eq, Nat.mul_add_div (by decide : 0 < B64),
      Nat.div_eq_of_lt hrem_lt, Nat.add_zero]

/-- Exact division-free `amount / 100_000_000` for all `2^64` values of `amount : UInt64`. -/
theorem llbSatsDiv1e8_eq (amount : UInt64) :
    llbSatsDiv1e8 amount = amount / 100000000 := by
  apply UInt64.toNat_inj.mp
  unfold llbSatsDiv1e8
  rw [UInt64.toNat_shiftRight, mulHiRecip1e8_toNat, UInt64.toNat_div]
  have hsh : (26 : UInt64).toNat % 64 = 26 := rfl
  rw [hsh, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
  have hb90 : B64 * 2 ^ 26 = 2 ^ 90 := rfl
  have hm_id : (100000000 : UInt64).toNat = 100000000 := rfl
  rw [hb90, hm_id]
  let x := amount.toNat
  let q := x / 100000000
  let r := x % 100000000
  have hx : x = 100000000 * q + r := (Nat.div_add_mod x 100000000).symm
  have hr_lt : r < 100000000 := Nat.mod_lt x (by decide)
  have hr_le : r ≤ 99999999 := Nat.le_sub_one_of_lt hr_lt
  have hq_lt : q < 184467440738 :=
    div_lt_of_lt_mul_c (Nat.lt_trans amount.toNat_lt (by decide))
  have hq_le : q ≤ 184467440737 := Nat.le_sub_one_of_lt hq_lt
  have h_magic : 100000000 * M64 = 2 ^ 90 + 875776 := rfl
  have h_prod : x * M64 = 2 ^ 90 * q + (875776 * q + r * M64) := by
    calc x * M64
      _ = (100000000 * q + r) * M64 := by rw [hx]
      _ = q * (100000000 * M64) + r * M64 := by
        rw [Nat.add_mul, Nat.mul_comm 100000000 q, Nat.mul_assoc]
      _ = q * (2 ^ 90 + 875776) + r * M64 := by rw [h_magic]
      _ = 2 ^ 90 * q + (875776 * q + r * M64) := by
        rw [Nat.mul_add, Nat.mul_comm q (2 ^ 90), Nat.mul_comm q 875776, Nat.add_assoc]
  have herr_lt : 875776 * q + r * M64 < 2 ^ 90 := by
    have hle := Nat.add_le_add (Nat.mul_le_mul_left 875776 hq_le) (Nat.mul_le_mul_right M64 hr_le)
    exact Nat.lt_of_le_of_lt hle (by decide)
  rw [h_prod, Nat.mul_add_div (by decide : 0 < 2 ^ 90),
      Nat.div_eq_of_lt herr_lt, Nat.add_zero]

/-- Exact division-free `amount % 100_000_000` (`0..99_999_999`) for all `2^64` values of `amount : UInt64`. -/
theorem llbSatsMod1e8_eq (amount : UInt64) :
    (llbSatsMod1e8 amount).toUInt64 = amount % 100000000 := by
  unfold llbSatsMod1e8
  rw [llbSatsDiv1e8_eq]
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64, UInt64.toNat_mod]
  let x := amount.toNat
  let D : Nat := 100000000
  have hd_u64 : (100000000 : UInt64).toNat = D := rfl
  rw [hd_u64]
  let q := x / D
  let r := x % D
  have hx : x = D * q + r := (Nat.div_add_mod x D).symm
  have hr_lt : r < 2 ^ 32 := Nat.lt_trans (Nat.mod_lt x (by decide : 0 < D)) (by decide)
  have hsub_u32 :
      amount.toUInt32 - (amount / 100000000).toUInt32 * 100000000 = UInt32.ofNat r := by
    have h1 : amount.toUInt32 = UInt32.ofNat x := by
      apply UInt32.toNat_inj.mp
      rw [UInt64.toNat_toUInt32, UInt32.toNat_ofNat']
    have h2 : (amount / 100000000).toUInt32 = UInt32.ofNat q := by
      apply UInt32.toNat_inj.mp
      rw [UInt64.toNat_toUInt32, UInt64.toNat_div, hd_u64, UInt32.toNat_ofNat']
    have h3 : (100000000 : UInt32) = UInt32.ofNat D := rfl
    rw [h1, h2, h3, hx]
    have hadd : UInt32.ofNat (D * q + r) = UInt32.ofNat q * UInt32.ofNat D + UInt32.ofNat r := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
          UInt32.toNat_ofNat', UInt32.toNat_ofNat']
      rw [Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_comm q D]
    rw [hadd]
    let a := UInt32.ofNat q * UInt32.ofNat D
    let b := UInt32.ofNat r
    show (a + b) - a = b
    rw [UInt32.add_comm a b, UInt32.add_sub_cancel b a]
  rw [hsub_u32, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hr_lt]

private theorem pow2_le_pow2 {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    calc 2 ^ a ≤ 2 ^ _ := ih
      _ ≤ 2 ^ _ * 2 := Nat.le_mul_of_pos_right _ (by decide)

private theorem pow2_pos (e : Nat) : 0 < 2 ^ e := by
  induction e with
  | zero => decide
  | succ k ih => exact Nat.mul_pos ih (by decide)

private theorem pow2_lt_pow2_of_lt {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have h1 : 2 ^ (a + 1) ≤ 2 ^ b := pow2_le_pow2 h
  have h2 : 2 ^ a < 2 ^ (a + 1) := by
    change 2 ^ a < 2 ^ a * 2
    rw [Nat.mul_two]
    exact Nat.lt_add_of_pos_right (pow2_pos a)
  exact Nat.lt_of_lt_of_le h2 h1

private theorem largestPow2LtGo_of_pow2_sandwich {n fuel d e : Nat}
    (hd_le : d ≤ e)
    (hfuel : e - d ≤ fuel)
    (hlo : 2 ^ e < n)
    (hhi : n ≤ 2 ^ e * 2) :
    InternalSpec.MerkleProtocol.largestPow2LtGo n fuel (2 ^ d) = 2 ^ e := by
  induction fuel generalizing d with
  | zero =>
    have hsub0 : e - d = 0 := Nat.eq_zero_of_le_zero hfuel
    have hed : e ≤ d := Nat.le_of_sub_eq_zero hsub0
    have hde : d = e := Nat.le_antisymm hd_le hed
    subst hde
    rfl
  | succ f ih =>
    unfold InternalSpec.MerkleProtocol.largestPow2LtGo
    cases hde_eq : decide (d = e)
    · have hd_lt : d < e := Nat.lt_of_le_of_ne hd_le (of_decide_eq_false hde_eq)
      have hd1_le : d + 1 ≤ e := hd_lt
      have hp_le : 2 ^ d * 2 ≤ 2 ^ e := pow2_le_pow2 hd1_le
      have hcmp_true : 2 ^ d * 2 < n := Nat.lt_of_le_of_lt hp_le hlo
      rw [ite_eq_left hcmp_true]
      let k := e - (d + 1)
      have he_eq : e = d + (k + 1) := by
        calc e = (d + 1) + k := (Nat.add_sub_of_le hd1_le).symm
          _ = d + (k + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hsub : e - d = k + 1 := by
        conv => lhs; rw [he_eq]
        exact Nat.add_sub_cancel_left d (k + 1)
      have hf1 : k + 1 ≤ f + 1 := by rw [← hsub]; exact hfuel
      have hf' : k ≤ f := Nat.le_of_succ_le_succ hf1
      change InternalSpec.MerkleProtocol.largestPow2LtGo n f (2 ^ (d + 1)) = 2 ^ e
      exact ih hd1_le hf'
    · have hde : d = e := of_decide_eq_true hde_eq
      subst hde
      have hnot : ¬ (2 ^ d * 2 < n) := Nat.not_lt.mpr hhi
      exact ite_eq_right hnot

private theorem bv32_testBit_smear (x : BitVec 32) (i : Nat) (_hi : i < 32) :
    let m1 := x ||| (x >>> 1)
    let m2 := m1 ||| (m1 >>> 2)
    let m4 := m2 ||| (m2 >>> 4)
    let m8 := m4 ||| (m4 >>> 8)
    let m16 := m8 ||| (m8 >>> 16)
    (m16.getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < 32 ∧ x.getLsbD j = true) := by
  have step_dbl : ∀ (y : BitVec 32) (b : Nat),
      (∀ p, y.getLsbD p = true ↔ ∃ d < b, x.getLsbD (p + d) = true) →
      ∀ p, (y ||| (y >>> b)).getLsbD p = true ↔ ∃ d < b + b, x.getLsbD (p + d) = true := by
    intro y b hy p
    rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, Bool.or_eq_true, hy p, hy (b + p)]
    constructor
    · rintro (⟨d, hd, hxd⟩ | ⟨d, hd, hxd⟩)
      · exact ⟨d, Nat.lt_of_lt_of_le hd (Nat.le_add_right b b), hxd⟩
      · refine ⟨b + d, by omega, ?_⟩
        have heq : p + (b + d) = b + p + d := by omega
        rwa [heq]
    · rintro ⟨d, hd, hxd⟩
      cases hlt : decide (d < b)
      · right
        have hge : b ≤ d := Nat.not_lt.mp (of_decide_eq_false hlt)
        refine ⟨d - b, by omega, ?_⟩
        have heq : b + p + (d - b) = p + d := by omega
        rwa [heq]
      · left; exact ⟨d, of_decide_eq_true hlt, hxd⟩
  have h0 : ∀ p, x.getLsbD p = true ↔ ∃ d < 1, x.getLsbD (p + d) = true := by
    intro p
    constructor
    · intro hx; exact ⟨0, by decide, by simpa using hx⟩
    · rintro ⟨d, hd, hxd⟩
      have hd0 : d = 0 := by omega
      subst hd0; simpa using hxd
  have h1 := step_dbl x 1 h0
  have h2 := step_dbl (x ||| (x >>> 1)) 2 h1
  have h4 := step_dbl _ 4 h2
  have h8 := step_dbl _ 8 h4
  have h16 := step_dbl _ 16 h8 i
  dsimp only
  rw [h16]
  constructor
  · rintro ⟨d, _hd, hxd⟩
    have hlt32 : i + d < 32 := by
      apply Nat.lt_of_not_le
      intro hge
      rw [BitVec.getLsbD_of_ge _ _ hge] at hxd
      cases hxd
    exact ⟨i + d, Nat.le_add_right i d, hlt32, hxd⟩
  · rintro ⟨j, hij, hj32, hxj⟩
    refine ⟨j - i, by omega, ?_⟩
    have heq : i + (j - i) = j := Nat.add_sub_of_le hij
    rwa [heq]

private def msbIdxGo : BitVec 32 → Nat → Nat
  | _, 0 => 0
  | x, k + 1 => if x.getLsbD k then k else msbIdxGo x k

private theorem msbIdxGo_spec (x : BitVec 32) (n : Nat) (hn : n ≤ 32)
    (hex : ∃ j, j < n ∧ x.getLsbD j = true) :
    msbIdxGo x n < n ∧
    x.getLsbD (msbIdxGo x n) = true ∧
    ∀ j, msbIdxGo x n < j → j < n → x.getLsbD j = false := by
  induction n with
  | zero =>
    rcases hex with ⟨j, hj, _⟩
    exact absurd hj (Nat.not_lt_zero j)
  | succ k ih =>
    unfold msbIdxGo
    cases hxk : x.getLsbD k
    · change (if false = true then k else msbIdxGo x k) < k + 1 ∧
        x.getLsbD (if false = true then k else msbIdxGo x k) = true ∧
        ∀ j, (if false = true then k else msbIdxGo x k) < j → j < k + 1 → x.getLsbD j = false
      rw [ite_eq_right Bool.noConfusion]
      have hex' : ∃ j, j < k ∧ x.getLsbD j = true := by
        rcases hex with ⟨j, hj, hxj⟩
        cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with
        | inl hjk => subst hjk; rw [hxk] at hxj; cases hxj
        | inr hjk => exact ⟨j, hjk, hxj⟩
      rcases ih (Nat.le_of_succ_le hn) hex' with ⟨hlt, htrue, hhigh⟩
      refine ⟨Nat.lt_succ_of_lt hlt, htrue, ?_⟩
      intro j hgt hjlt
      cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hjlt) with
      | inl hjk => subst hjk; exact hxk
      | inr hjk => exact hhigh j hgt hjk
    · change (if true = true then k else msbIdxGo x k) < k + 1 ∧
        x.getLsbD (if true = true then k else msbIdxGo x k) = true ∧
        ∀ j, (if true = true then k else msbIdxGo x k) < j → j < k + 1 → x.getLsbD j = false
      rw [ite_eq_left rfl]
      refine ⟨Nat.lt_succ_self k, hxk, ?_⟩
      intro j hgt hjlt
      exact absurd (Nat.lt_of_lt_of_le hgt (Nat.le_of_lt_succ hjlt)) (Nat.lt_irrefl k)

private theorem bv32_ones_eq (e : Nat) (_he : e < 32) :
    ∀ y : BitVec 32,
      (∀ i < 32, y.getLsbD i = decide (i ≤ e)) →
      y = BitVec.ofNat 32 (2 ^ (e + 1) - 1) := by
  intro y hy
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [hy i hi, BitVec.getLsbD_ofNat]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit]
  rw [Nat.shiftRight_eq_div_pow]
  cases hle : decide (i ≤ e)
  · have hgt : e + 1 ≤ i := Nat.lt_of_not_le (of_decide_eq_false hle)
    have hdiv0 : (2 ^ (e + 1) - 1) / 2 ^ i = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.sub_lt (pow2_pos (e + 1)) (by decide)) (pow2_le_pow2 hgt))
    rw [hdiv0]; rfl
  · have hi_le : i ≤ e := of_decide_eq_true hle
    have hsplit : 2 ^ (e + 1) - 1 = 2 ^ i * (2 ^ (e - i + 1) - 1) + (2 ^ i - 1) := by
      have hei : i + (e - i + 1) = e + 1 := by omega
      have hp : 2 ^ (e + 1) = 2 ^ i * 2 ^ (e - i + 1) := by rw [← Nat.pow_add, hei]
      have hpos1 : 1 ≤ 2 ^ i := pow2_pos i
      have hpos2 : 1 ≤ 2 ^ (e - i + 1) := pow2_pos (e - i + 1)
      have hmul : 2 ^ i * (2 ^ (e - i + 1) - 1) + 2 ^ i = 2 ^ i * 2 ^ (e - i + 1) := by
        calc 2 ^ i * (2 ^ (e - i + 1) - 1) + 2 ^ i
            = 2 ^ i * (2 ^ (e - i + 1) - 1) + 2 ^ i * 1 := by rw [Nat.mul_one]
          _ = 2 ^ i * (2 ^ (e - i + 1) - 1 + 1) := (Nat.mul_add _ _ _).symm
          _ = 2 ^ i * 2 ^ (e - i + 1) := by rw [Nat.sub_add_cancel hpos2]
      omega
    rw [hsplit, Nat.mul_add_div (pow2_pos i),
        Nat.div_eq_of_lt (Nat.sub_lt (pow2_pos i) (by decide)), Nat.add_zero]
    rw [Nat.pow_succ, Nat.and_comm]
    have hp : 1 ≤ 2 ^ (e - i) := pow2_pos (e - i)
    have hodd : (2 ^ (e - i) * 2 - 1) &&& 1 = 1 := by
      rw [Nat.and_one_is_mod]
      omega
    rw [hodd]; rfl

theorem largestPow2LtU32_eq (s : UInt32) (hs : 2 ≤ s.toNat) :
    (largestPow2LtU32 s).toNat = InternalSpec.MerkleProtocol.largestPow2Lt s.toNat := by
  let m0 : UInt32 := s - 1
  have hm0_nat : m0.toNat = s.toNat - 1 := by
    have h1le : (1 : UInt32) ≤ s := UInt32.le_iff_toNat_le.mpr (Nat.le_trans (by decide) hs)
    exact UInt32.toNat_sub_of_le s 1 h1le
  have hex_bit : ∃ j, j < 32 ∧ m0.toBitVec.getLsbD j = true := by
    have hne0 : m0.toBitVec ≠ 0#32 := by
      intro h0
      have hm0_zero : m0.toNat = 0 := congrArg BitVec.toNat h0
      rw [hm0_nat] at hm0_zero
      have hle1 : s.toNat ≤ 1 := Nat.le_of_sub_eq_zero hm0_zero
      exact Nat.not_lt_of_ge hle1 hs
    let check : (n : Nat) → (∀ j < n, m0.toBitVec.getLsbD j = false) ∨ (∃ j, j < n ∧ m0.toBitVec.getLsbD j = true) := by
      intro n
      induction n with
      | zero => left; intro j hj; exact absurd hj (Nat.not_lt_zero j)
      | succ k ih =>
        rcases ih with hall | hex
        · cases hk : m0.toBitVec.getLsbD k
          · left
            intro j hj
            cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with
            | inl hjk => subst hjk; exact hk
            | inr hjk => exact hall j hjk
          · right; exact ⟨k, Nat.lt_succ_self k, hk⟩
        · right; rcases hex with ⟨j, hj, hxj⟩; exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
    rcases check 32 with hall | hex
    · exfalso
      apply hne0
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [hall i hi, BitVec.getLsbD_zero]
    · exact hex
  rcases msbIdxGo_spec m0.toBitVec 32 (Nat.le_refl 32) hex_bit with ⟨he_lt, he_true, he_high⟩
  let e := msbIdxGo m0.toBitVec 32
  change e < 32 at he_lt
  change m0.toBitVec.getLsbD e = true at he_true
  have hm0_lo : 2 ^ e ≤ m0.toNat :=
    Nat.ge_two_pow_of_testBit he_true
  have hm0_hi : m0.toNat < 2 ^ (e + 1) := by
    apply Nat.lt_of_not_le
    intro hge
    have hdiv_pos : 0 < m0.toNat / 2 ^ (e + 1) := Nat.div_pos hge (pow2_pos (e + 1))
    have hshr0 : m0.toBitVec >>> (e + 1) = 0#32 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i _hi
      rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
      cases hi32 : decide (e + 1 + i < 32)
      · exact BitVec.getLsbD_of_ge _ _ (Nat.not_lt.mp (of_decide_eq_false hi32))
      · have hgt : e < e + 1 + i := Nat.lt_of_lt_of_le (Nat.lt_succ_self e) (Nat.le_add_right (e + 1) i)
        exact he_high (e + 1 + i) hgt (of_decide_eq_true hi32)
    have hdiv0 : m0.toNat / 2 ^ (e + 1) = 0 := by
      have hbn := congrArg BitVec.toNat hshr0
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hbn
      exact hbn
    rw [hdiv0] at hdiv_pos
    exact Nat.lt_irrefl 0 hdiv_pos
  -- Show largestPow2LtU32 s = 2^e
  have hsmear_bv : (largestPow2LtU32 s).toNat = 2 ^ e := by
    unfold largestPow2LtU32
    let x := m0.toBitVec
    let m1b := x ||| (x >>> 1)
    let m2b := m1b ||| (m1b >>> 2)
    let m4b := m2b ||| (m2b >>> 4)
    let m8b := m4b ||| (m4b >>> 8)
    let m16b := m8b ||| (m8b >>> 16)
    have hm16_ones : m16b = BitVec.ofNat 32 (2 ^ (e + 1) - 1) := by
      apply bv32_ones_eq e he_lt m16b
      intro i hi
      cases hle : decide (i ≤ e)
      · rw [Bool.eq_false_iff]
        intro htr
        rcases (bv32_testBit_smear x i hi).mp htr with ⟨j, hij, hj32, hxj⟩
        have hej : e < j := Nat.lt_of_lt_of_le (Nat.lt_of_not_le (of_decide_eq_false hle)) hij
        rw [he_high j hej hj32] at hxj
        cases hxj
      · exact (bv32_testBit_smear x i hi).mpr ⟨e, of_decide_eq_true hle, he_lt, he_true⟩
    -- Relate UInt32 operations in largestPow2LtU32 to m16b
    have hu32_m16 :
        (let m1 : UInt32 := m0 ||| (m0 >>> 1)
         let m2 : UInt32 := m1 ||| (m1 >>> 2)
         let m4 : UInt32 := m2 ||| (m2 >>> 4)
         let m8 : UInt32 := m4 ||| (m4 >>> 8)
         m8 ||| (m8 >>> 16)).toBitVec = m16b := rfl
    have hval_m16 :
        (let m1 : UInt32 := m0 ||| (m0 >>> 1)
         let m2 : UInt32 := m1 ||| (m1 >>> 2)
         let m4 : UInt32 := m2 ||| (m2 >>> 4)
         let m8 : UInt32 := m4 ||| (m4 >>> 8)
         m8 ||| (m8 >>> 16)).toNat = 2 ^ (e + 1) - 1 := by
      have hbn := congrArg BitVec.toNat (hu32_m16.trans hm16_ones)
      have hlt32 : 2 ^ (e + 1) - 1 < 2 ^ 32 :=
        Nat.lt_of_lt_of_le (Nat.sub_lt (pow2_pos (e + 1)) (by decide)) (pow2_le_pow2 he_lt)
      change _ = (BitVec.ofNat 32 (2 ^ (e + 1) - 1)).toNat at hbn
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt32] at hbn
      exact hbn
    dsimp only
    rw [UInt32.toNat_add, UInt32.toNat_shiftRight]
    change ((let m1 : UInt32 := m0 ||| (m0 >>> 1)
             let m2 : UInt32 := m1 ||| (m1 >>> 2)
             let m4 : UInt32 := m2 ||| (m2 >>> 4)
             let m8 : UInt32 := m4 ||| (m4 >>> 8)
             m8 ||| (m8 >>> 16)).toNat >>> ((1 : UInt32).toNat % 32) + (1 : UInt32).toNat) % 2 ^ 32 = 2 ^ e
    rw [hval_m16]
    have hsh1 : (1 : UInt32).toNat % 32 = 1 := rfl
    have hone : (1 : UInt32).toNat = 1 := rfl
    rw [hsh1, hone, Nat.shiftRight_eq_div_pow]
    have hdiv : (2 ^ (e + 1) - 1) / 2 = 2 ^ e - 1 := by
      have hp : 1 ≤ 2 ^ e := pow2_pos e
      have hsplit2 : 2 ^ (e + 1) - 1 = 2 * (2 ^ e - 1) + 1 := by
        calc 2 ^ (e + 1) - 1
            = 2 * 2 ^ e - 1 := by rw [Nat.pow_succ, Nat.mul_comm]
          _ = (2 * (2 ^ e - 1) + 2) - 1 := by
              have h2 : 2 * (2 ^ e - 1) + 2 = 2 * 2 ^ e := by
                calc 2 * (2 ^ e - 1) + 2
                    = 2 * (2 ^ e - 1) + 2 * 1 := rfl
                  _ = 2 * (2 ^ e - 1 + 1) := (Nat.mul_add 2 _ 1).symm
                  _ = 2 * 2 ^ e := by rw [Nat.sub_add_cancel hp]
              rw [h2]
          _ = 2 * (2 ^ e - 1) + 1 := Nat.add_sub_assoc (by decide : 1 ≤ 2) _
      change (2 ^ (e + 1) - 1) / 2 ^ 1 = 2 ^ e - 1
      have hp1 : 2 ^ 1 = 2 := rfl
      rw [hp1, hsplit2, Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2), Nat.add_zero]
    rw [hdiv, Nat.sub_add_cancel (pow2_pos e), Nat.mod_eq_of_lt (pow2_lt_pow2_of_lt he_lt)]
  rw [hsmear_bv]
  have hs_pos : 1 ≤ s.toNat := Nat.le_trans (by decide) hs
  have hs_lo : 2 ^ e < s.toNat := by
    have h1 : 2 ^ e + 1 ≤ m0.toNat + 1 := Nat.add_le_add_right hm0_lo 1
    rwa [hm0_nat, Nat.sub_add_cancel hs_pos] at h1
  have hs_hi : s.toNat ≤ 2 ^ e * 2 := by
    have h1 : m0.toNat + 1 ≤ 2 ^ (e + 1) := hm0_hi
    rwa [hm0_nat, Nat.sub_add_cancel hs_pos, Nat.pow_succ] at h1
  have hfuel : e - 0 ≤ s.toNat := by
    rw [Nat.sub_zero]
    have he_le_pow : ∀ x : Nat, x ≤ 2 ^ x := by
      intro x
      induction x with
      | zero => decide
      | succ y ihy =>
        calc y + 1 ≤ 2 ^ y + 1 := Nat.add_le_add_right ihy 1
          _ ≤ 2 ^ y + 2 ^ y := Nat.add_le_add_left (pow2_pos y) _
          _ = 2 ^ (y + 1) := by rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (he_le_pow e) hs_lo)
  unfold InternalSpec.MerkleProtocol.largestPow2Lt
  exact (largestPow2LtGo_of_pow2_sandwich (Nat.zero_le e) hfuel hs_lo hs_hi).symm

/-- Round-trip unpacking of `packMerkleState size index` into upper and lower 32-bit halves. -/
theorem packMerkleState_roundtrip (size index : UInt32) :
    ((packMerkleState size index) >>> 32).toUInt32 = size ∧
    (packMerkleState size index).toUInt32 = index := by
  unfold packMerkleState
  have hsh : (32 : UInt64).toNat % 64 = 32 := rfl
  have hsize_lt : size.toNat * 2 ^ 32 < 2 ^ 64 := by
    have h1 : size.toNat ≤ 4294967295 := Nat.le_sub_one_of_lt size.toNat_lt
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ h1) (by decide)
  have hsum_lt : size.toNat * 2 ^ 32 + index.toNat < 2 ^ 64 := by
    have h1 : size.toNat ≤ 4294967295 := Nat.le_sub_one_of_lt size.toNat_lt
    have h2 : index.toNat < 2 ^ 32 := index.toNat_lt
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right _ h1) h2) (by decide)
  have hpack_nat : ((size.toUInt64 <<< 32) + index.toUInt64).toNat = size.toNat * 2 ^ 32 + index.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64,
        hsh, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hsize_lt, Nat.mod_eq_of_lt hsum_lt]
  constructor
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hpack_nat, hsh, Nat.shiftRight_eq_div_pow,
        Nat.mul_comm size.toNat (2 ^ 32), Nat.mul_add_div (by decide : 0 < 2 ^ 32),
        Nat.div_eq_of_lt index.toNat_lt, Nat.add_zero, Nat.mod_eq_of_lt size.toNat_lt]
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, hpack_nat, Nat.mul_comm size.toNat (2 ^ 32),
        Nat.mul_add_mod, Nat.mod_eq_of_lt index.toNat_lt]

/-- Byte encoding of optional Merkle proof directions matching BOLOS `merkle_get_ith_direction`. -/
def encodeMerkleDir? : Option InternalSpec.MerkleProtocol.MerkleDir → UInt8
  | some .left => 0
  | some .right => 1
  | none => 0xFF

/-- Iterate `llbMerkleAdvanceState` `n` times from an initial packed `(size, index)` state. -/
def merkleAdvanceSteps : Nat → UInt64 → UInt64
  | 0, st => st
  | n + 1, st => merkleAdvanceSteps n (llbMerkleAdvanceState st)

/-- Proof-side reader of the branch direction at a packed `(size, index)` state
    (`0` = left, `1` = right, `0xFF` = leaf / invalid). It is not part of the compiled kernel:
    the app derives the direction from two consecutive `llbMerkleAdvanceState` states. -/
def merkleStateDir (st : UInt64) : UInt8 :=
  let size : UInt32 := (st >>> 32).toUInt32
  let index : UInt32 := st.toUInt32
  if decide (size ≤ 1) || !decide (index < size) then
    0xFF
  else
    let mask := largestPow2LtU32 size
    if decide (index < mask) then 0 else 1

/-- Single-step refinement: `merkleStateDir` computes the head direction of `InternalSpec.MerkleProtocol.merkleDirections`. -/
theorem merkleStateDir_spec (size index : UInt32) :
    merkleStateDir (packMerkleState size index) =
      encodeMerkleDir? (InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat).head? := by
  unfold merkleStateDir
  dsimp only
  have ⟨hhi, hlo⟩ := packMerkleState_roundtrip size index
  rw [hhi, hlo]
  cases hsize1 : decide (size ≤ 1)
  · simp only [Bool.false_or]
    have hge2 : 2 ≤ size.toNat :=
      Nat.lt_of_not_le (fun h => of_decide_eq_false hsize1 (UInt32.le_iff_toNat_le.mpr h))
    cases hidx : decide (index < size)
    · simp only [Bool.not_false, ↓reduceIte]
      have hge_idx : ¬ (index.toNat < size.toNat) := of_decide_eq_false hidx
      rw [InternalSpec.MerkleProtocol.merkleDirections]
      split
      · rename_i hcond; exact absurd hcond.2 hge_idx
      · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hlt_idx : index.toNat < size.toNat := of_decide_eq_true hidx
      have hmask : (largestPow2LtU32 size).toNat = InternalSpec.MerkleProtocol.largestPow2Lt size.toNat :=
        largestPow2LtU32_eq size hge2
      cases hdir : decide (index < largestPow2LtU32 size)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnot_lt : ¬ (index.toNat < InternalSpec.MerkleProtocol.largestPow2Lt size.toNat) := by
          rw [← hmask]; exact of_decide_eq_false hdir
        rw [InternalSpec.MerkleProtocol.merkleDirections]
        split
        · dsimp only
          split
          · rename_i hc; exact absurd hc hnot_lt
          · rfl
        · rename_i hnc; exact absurd ⟨hge2, hlt_idx⟩ hnc
      · simp only [↓reduceIte]
        have hlt_m : index.toNat < InternalSpec.MerkleProtocol.largestPow2Lt size.toNat := by
          rw [← hmask]; exact of_decide_eq_true hdir
        rw [InternalSpec.MerkleProtocol.merkleDirections]
        split
        · dsimp only
          split
          · rfl
          · rename_i hnc; exact absurd hlt_m hnc
        · rename_i hnc; exact absurd ⟨hge2, hlt_idx⟩ hnc
  · simp only [Bool.true_or, ↓reduceIte]
    have hle1 : size.toNat ≤ 1 := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hsize1)
    rw [InternalSpec.MerkleProtocol.merkleDirections]
    split
    · rename_i hc; exact absurd (Nat.le_trans hc.1 hle1) (by decide)
    · rfl

/-- Multi-step refinement: `step` iterations of `llbMerkleAdvanceState` followed by `merkleStateDir`
    computes the exact `step`-th top-down Merkle proof direction of `InternalSpec.MerkleProtocol.merkleDirections` in `O(step)`. -/
theorem llbMerkleAdvanceState_steps_spec
    (step : Nat) (size index : UInt32) (hidx_valid : index < size ∨ size ≤ 1) :
    merkleStateDir (merkleAdvanceSteps step (packMerkleState size index)) =
      encodeMerkleDir? ((InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat)[step]?) := by
  induction step generalizing size index with
  | zero =>
    unfold merkleAdvanceSteps
    have h0 : (InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat)[0]? =
        (InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat).head? := by
      cases InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat <;> rfl
    rw [h0]
    exact merkleStateDir_spec size index
  | succ n ih =>
    unfold merkleAdvanceSteps
    have hadv :
        llbMerkleAdvanceState (packMerkleState size index) =
          if decide (size ≤ 1) then packMerkleState size index
          else
            let mask := largestPow2LtU32 size
            if decide (index < mask) then packMerkleState mask index
            else packMerkleState (size - mask) (index - mask) := by
      unfold llbMerkleAdvanceState
      dsimp only
      have ⟨hhi, hlo⟩ := packMerkleState_roundtrip size index
      rw [hhi, hlo]
    rw [hadv]
    cases hsize1 : decide (size ≤ 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hge2 : 2 ≤ size.toNat :=
        Nat.lt_of_not_le (fun h => of_decide_eq_false hsize1 (UInt32.le_iff_toNat_le.mpr h))
      have hidx_lt : index < size := by
        cases hidx_valid with
        | inl h => exact h
        | inr hle => exact absurd hle (of_decide_eq_false hsize1)
      have hmask_nat : (largestPow2LtU32 size).toNat = InternalSpec.MerkleProtocol.largestPow2Lt size.toNat :=
        largestPow2LtU32_eq size hge2
      have hk_bounds := InternalSpec.MerkleProtocol.largestPow2Lt_bounds hge2
      have hcond : 2 ≤ size.toNat ∧ index.toNat < size.toNat := ⟨hge2, hidx_lt⟩
      cases hdir : decide (index < largestPow2LtU32 size)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnot_lt_nat : ¬ (index.toNat < InternalSpec.MerkleProtocol.largestPow2Lt size.toNat) := by
          rw [← hmask_nat]; exact of_decide_eq_false hdir
        have hdirs_eq : InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat =
            .right :: InternalSpec.MerkleProtocol.merkleDirections
              (size.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat)
              (index.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat) := by
          rw [InternalSpec.MerkleProtocol.merkleDirections]
          split
          · dsimp only
            split
            · rename_i hc; exact absurd hc hnot_lt_nat
            · rfl
          · rename_i hnc; exact absurd hcond hnc
        rw [hdirs_eq]
        have hcons : (InternalSpec.MerkleProtocol.MerkleDir.right ::
            InternalSpec.MerkleProtocol.merkleDirections (size.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat)
              (index.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat))[n + 1]? =
            (InternalSpec.MerkleProtocol.merkleDirections (size.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat)
              (index.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat))[n]? := rfl
        rw [hcons]
        have hmask_le_size : largestPow2LtU32 size ≤ size :=
          UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt (hmask_nat.symm ▸ hk_bounds.2))
        have hmask_le_idx : largestPow2LtU32 size ≤ index :=
          UInt32.le_iff_toNat_le.mpr (Nat.le_of_not_lt (of_decide_eq_false hdir))
        have hsub_size : (size - largestPow2LtU32 size).toNat = size.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat := by
          rw [UInt32.toNat_sub_of_le size _ hmask_le_size, hmask_nat]
        have hsub_idx : (index - largestPow2LtU32 size).toNat = index.toNat - InternalSpec.MerkleProtocol.largestPow2Lt size.toNat := by
          rw [UInt32.toNat_sub_of_le index _ hmask_le_idx, hmask_nat]
        rw [← hsub_size, ← hsub_idx]
        have hsub_lt : index - largestPow2LtU32 size < size - largestPow2LtU32 size := by
          rw [UInt32.lt_iff_toNat_lt, hsub_idx, hsub_size]
          exact Nat.sub_lt_sub_right (hmask_nat ▸ UInt32.le_iff_toNat_le.mp hmask_le_idx) hidx_lt
        exact ih (size - largestPow2LtU32 size) (index - largestPow2LtU32 size) (Or.inl hsub_lt)
      · simp only [↓reduceIte]
        have hlt_nat : index.toNat < InternalSpec.MerkleProtocol.largestPow2Lt size.toNat := by
          rw [← hmask_nat]; exact of_decide_eq_true hdir
        have hdirs_eq : InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat =
            .left :: InternalSpec.MerkleProtocol.merkleDirections
              (InternalSpec.MerkleProtocol.largestPow2Lt size.toNat) index.toNat := by
          rw [InternalSpec.MerkleProtocol.merkleDirections]
          split
          · dsimp only
            split
            · rfl
            · rename_i hnc; exact absurd hlt_nat hnc
          · rename_i hnc; exact absurd hcond hnc
        rw [hdirs_eq]
        have hcons : (InternalSpec.MerkleProtocol.MerkleDir.left ::
            InternalSpec.MerkleProtocol.merkleDirections (InternalSpec.MerkleProtocol.largestPow2Lt size.toNat) index.toNat)[n + 1]? =
            (InternalSpec.MerkleProtocol.merkleDirections (InternalSpec.MerkleProtocol.largestPow2Lt size.toNat) index.toNat)[n]? := rfl
        rw [hcons, ← hmask_nat]
        exact ih (largestPow2LtU32 size) index (Or.inl (of_decide_eq_true hdir))
    · simp only [↓reduceIte]
      have hle1 : size.toNat ≤ 1 := UInt32.le_iff_toNat_le.mp (of_decide_eq_true hsize1)
      have hnil : InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat = [] := by
        rw [InternalSpec.MerkleProtocol.merkleDirections]
        split
        · rename_i hc; exact absurd (Nat.le_trans hc.1 hle1) (by decide)
        · rfl
      rw [hnil]
      have hih := ih size index (Or.inr (of_decide_eq_true hsize1))
      rw [hnil] at hih
      have hnil_get : ∀ k : Nat, ([] : List InternalSpec.MerkleProtocol.MerkleDir)[k]? = none := fun _ => rfl
      rw [hnil_get n] at hih
      rw [hnil_get (n + 1)]
      exact hih

/-! ## 8. Bech32 Final Constant, Wallet Name Character Check & BIP-32 Pubkey Export Prefix -/

/-- Exact specification of `llbBech32FinalConstant` for Bech32 (`1`) and Bech32m (`0x2bc830a3`). -/
theorem llbBech32FinalConstant_spec (enc : UInt8) :
    llbBech32FinalConstant enc =
      (if decide (enc = 1) then 1 else if decide (enc = 2) then 0x2bc830a3 else 0) ∧
    llbBech32FinalConstant 1 = 1 ∧
    llbBech32FinalConstant 2 = 0x2bc830a3 ∧
    (enc ≠ 1 → enc ≠ 2 → llbBech32FinalConstant enc = 0) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h1 h2
  unfold llbBech32FinalConstant
  simp [h1, h2]

/-- Exact printable-ASCII specification of `llbWalletNameCharOk` (`0x21..0x7E` at edges, `0x20..0x7E` interior). -/
theorem llbWalletNameCharOk_spec (c : UInt8) (isEdge : Bool) :
    llbWalletNameCharOk c isEdge =
      (if isEdge then decide (0x21 ≤ c.toNat) && decide (c.toNat ≤ 0x7E)
       else decide (0x20 ≤ c.toNat) && decide (c.toNat ≤ 0x7E)) := by
  cases isEdge <;> rfl

/-- Exact refinement of `llbBip32PubkeyExportPrefixOk` against `BitcoinLedger.Bip32.isBolosSafePubkeyExportPath`
    across all path depths `0..255` and all networks. -/
theorem llbBip32PubkeyExportPrefixOk_refines
    (net : InternalSpec.Network) (path : InternalSpec.Bip32Path) (hbyte : path.size ≤ 255) :
    let p0 := path[0]?.getD 0
    let p1 := path[1]?.getD 0
    let p2 := path[2]?.getD 0
    let p3 := path[3]?.getD 0
    let tailStart :=
      if decide (BitcoinLedger.Bip32.unharden p0 = 48) then 4 else 3
    let tailUnhardened := BitcoinLedger.Bip32.allUnhardened (path.toList.drop tailStart)
    llbBip32PubkeyExportPrefixOk p0 p1 p2 p3
      (UInt8.ofNat path.size)
      (BitcoinLedger.Basic.networkParams net).bip44CoinType
      tailUnhardened =
    BitcoinLedger.Bip32.isBolosSafePubkeyExportPath net path := by
  dsimp only
  have hlt256 : path.size < 256 := Nat.lt_of_le_of_lt hbyte (by decide)
  have hu8_nat : (UInt8.ofNat path.size).toNat = path.size := by
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt256]
  unfold llbBip32PubkeyExportPrefixOk BitcoinLedger.Bip32.isBolosSafePubkeyExportPath
  cases hlist : path.toList with
  | nil =>
    have hsz : path.size = 0 := by rw [← Array.length_toList, hlist]; rfl
    rw [hsz]; rfl
  | cons s0 rest0 =>
    cases rest0 with
    | nil =>
      have hsz : path.size = 1 := by rw [← Array.length_toList, hlist]; rfl
      rw [hsz]; rfl
    | cons s1 rest1 =>
      have hp0 : path[0]?.getD 0 = s0 := by rw [← Array.getElem?_toList, hlist]; rfl
      have hp1 : path[1]?.getD 0 = s1 := by rw [← Array.getElem?_toList, hlist]; rfl
      cases rest1 with
      | nil =>
        have hsz : path.size = 2 := by rw [← Array.length_toList, hlist]; rfl
        rw [hsz, hp0, hp1]
        rfl
      | cons s2 rest2 =>
        have hp2 : path[2]?.getD 0 = s2 := by rw [← Array.getElem?_toList, hlist]; rfl
        have hlen_ge3 : 3 ≤ path.size := by
          rw [← Array.length_toList, hlist]
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))
        have hne2 : decide (UInt8.ofNat path.size = 2) = false := by
          apply decide_eq_false
          intro heq
          have h2 : (UInt8.ofNat path.size).toNat = 2 := congrArg UInt8.toNat heq
          rw [hu8_nat] at h2
          rw [h2] at hlen_ge3
          exact absurd hlen_ge3 (by decide)
        have hnot_lt3 : decide (UInt8.ofNat path.size < 3) = false := by
          apply decide_eq_false
          intro hlt
          have hlt' : path.size < 3 := by
            have := UInt8.lt_iff_toNat_lt.mp hlt
            rwa [hu8_nat] at this
          exact Nat.not_le.mpr hlt' hlen_ge3
        rw [hp0, hp1, hp2, hne2, hnot_lt3]
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or]
        have hhard_eq :
            (llbBip32IsHardened s0 && llbBip32IsHardened s1 && llbBip32IsHardened s2) =
            (BitcoinLedger.Bip32.isHardened s0 && BitcoinLedger.Bip32.isHardened s1 && BitcoinLedger.Bip32.isHardened s2) := rfl
        rw [hhard_eq]
        cases hhard : (BitcoinLedger.Bip32.isHardened s0 && BitcoinLedger.Bip32.isHardened s1 && BitcoinLedger.Bip32.isHardened s2)
        · simp only [Bool.not_false, ↓reduceIte]
          cases BitcoinLedger.Bip32.allUnhardened (List.drop (if decide (BitcoinLedger.Bip32.unharden s0 = 48) = true then 4 else 3) (s0 :: s1 :: s2 :: rest2)) <;> rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          have hs0_hard : llbBip32IsHardened s0 = true := by
            have ⟨h01, _⟩ := Bool.and_eq_true_iff.mp hhard
            exact (Bool.and_eq_true_iff.mp h01).1
          have hunh : llbBip32Unharden = BitcoinLedger.Bip32.unharden := rfl
          have hmax : BitcoinLedger.Bip32.MAX_BIP44_ACCOUNT_RECOMMENDED = 100 := rfl
          rw [hunh, hmax]
          cases hca : (!decide (BitcoinLedger.Bip32.unharden s1 = (BitcoinLedger.Basic.networkParams net).bip44CoinType) ||
              decide (100 < BitcoinLedger.Bip32.unharden s2))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hstd_eq : llbBip32StandardPurposeOk s0 = BitcoinLedger.Bip32.isStandard3StepPurpose (BitcoinLedger.Bip32.unharden s0) := by
              unfold llbBip32StandardPurposeOk
              rw [hs0_hard, Bool.true_and]; rfl
            rw [hstd_eq]
            cases hstd : BitcoinLedger.Bip32.isStandard3StepPurpose (BitcoinLedger.Bip32.unharden s0)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases hp48 : decide (BitcoinLedger.Bip32.unharden s0 = 48)
              · simp only [Bool.false_eq_true, ↓reduceIte]
                have hdrop3 : List.drop 3 (s0 :: s1 :: s2 :: rest2) = rest2 := rfl
                rw [hdrop3]
                cases BitcoinLedger.Bip32.allUnhardened rest2 <;> rfl
              · simp only [↓reduceIte]
                cases rest2 with
                | nil =>
                  have hsz3 : path.size = 3 := by rw [← Array.length_toList, hlist]; rfl
                  rw [hsz3]
                  rfl
                | cons s3 tail =>
                  have hp3 : path[3]?.getD 0 = s3 := by rw [← Array.getElem?_toList, hlist]; rfl
                  have hge4 : decide ((4 : UInt8) ≤ UInt8.ofNat path.size) = true := by
                    apply decide_eq_true
                    rw [UInt8.le_iff_toNat_le, hu8_nat, ← Array.length_toList, hlist]
                    exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))))
                  have hdrop4 : List.drop 4 (s0 :: s1 :: s2 :: s3 :: tail) = tail := rfl
                  have hs3h : llbBip32IsHardened s3 = BitcoinLedger.Bip32.isHardened s3 := rfl
                  dsimp only
                  rw [hp3, hge4, Bool.true_and, hdrop4, hs3h]
                  cases BitcoinLedger.Bip32.allUnhardened tail <;>
                    cases BitcoinLedger.Bip32.isHardened s3 <;>
                    cases (decide (BitcoinLedger.Bip32.unharden s3 = 1) || decide (BitcoinLedger.Bip32.unharden s3 = 2)) <;>
                    rfl
            · simp only [↓reduceIte]
              have hnot48 : decide (BitcoinLedger.Bip32.unharden s0 = 48) = false := by
                apply decide_eq_false
                intro h48
                rw [h48] at hstd
                exact Bool.noConfusion hstd
              rw [hnot48]
              simp only [Bool.false_eq_true, ↓reduceIte]
              have hdrop3 : List.drop 3 (s0 :: s1 :: s2 :: rest2) = rest2 := rfl
              rw [hdrop3]
              cases BitcoinLedger.Bip32.allUnhardened rest2 <;> rfl
          · simp only [↓reduceIte]
            cases BitcoinLedger.Bip32.allUnhardened (List.drop (if decide (BitcoinLedger.Bip32.unharden s0 = 48) = true then 4 else 3) (s0 :: s1 :: s2 :: rest2)) <;> rfl

/-! ## 8. Option 2 Branchless Primitives & BIP-370 Locktime State Machine (VND-04) -/

private theorem allOnes16_getLsbD : ∀ i < 16, ((0xFFFF : UInt16).toBitVec).getLsbD i = true := by decide
private theorem one16_getLsbD : ∀ i < 16, ((1 : UInt16).toBitVec).getLsbD i = decide (i = 0) := by decide
private theorem mask3_16_high_zero : ∀ i < 16, 2 ≤ i → ((3 : UInt16).toBitVec).getLsbD i = false := by decide
private theorem allOnes32_getLsbD : ∀ i < 32, ((0xFFFFFFFF : UInt32).toBitVec).getLsbD i = true := by decide
private theorem allOnes64_getLsbD : ∀ i < 64, ((0xFFFFFFFFFFFFFFFF : UInt64).toBitVec).getLsbD i = true := by decide

theorem bnot_eq (a : Bool) : bnot a = !a := by cases a <;> rfl
theorem band_eq (a b : Bool) : band a b = (a && b) := by cases a <;> cases b <;> rfl
theorem bor_eq (a b : Bool) : bor a b = (a || b) := by cases a <;> cases b <;> rfl

theorem selU16_eq (c : Bool) (t f : UInt16) : selU16 c t f = (if c then t else f) := by
  cases c
  · change f ^^^ (0 &&& (t ^^^ f)) = f
    apply UInt16.eq_of_toBitVec_eq
    rw [UInt16.toBitVec_xor, UInt16.toBitVec_and]
    change f.toBitVec ^^^ (0#16 &&& (t.toBitVec ^^^ f.toBitVec)) = f.toBitVec
    rw [BitVec.zero_and, BitVec.xor_zero]
  · change f ^^^ (0xFFFF &&& (t ^^^ f)) = t
    apply UInt16.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [UInt16.toBitVec_xor, UInt16.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    rw [allOnes16_getLsbD i hi, Bool.true_and]
    cases f.toBitVec.getLsbD i <;> cases t.toBitVec.getLsbD i <;> rfl

theorem selU32_eq (c : Bool) (t f : UInt32) : selU32 c t f = (if c then t else f) := by
  cases c
  · change f ^^^ (0 &&& (t ^^^ f)) = f
    apply UInt32.eq_of_toBitVec_eq
    rw [UInt32.toBitVec_xor, UInt32.toBitVec_and]
    change f.toBitVec ^^^ (0#32 &&& (t.toBitVec ^^^ f.toBitVec)) = f.toBitVec
    rw [BitVec.zero_and, BitVec.xor_zero]
  · change f ^^^ (0xFFFFFFFF &&& (t ^^^ f)) = t
    apply UInt32.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [UInt32.toBitVec_xor, UInt32.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    rw [allOnes32_getLsbD i hi, Bool.true_and]
    cases f.toBitVec.getLsbD i <;> cases t.toBitVec.getLsbD i <;> rfl

theorem selU64_eq (c : Bool) (t f : UInt64) : selU64 c t f = (if c then t else f) := by
  cases c
  · change f ^^^ (0 &&& (t ^^^ f)) = f
    apply UInt64.eq_of_toBitVec_eq
    rw [UInt64.toBitVec_xor, UInt64.toBitVec_and]
    change f.toBitVec ^^^ (0#64 &&& (t.toBitVec ^^^ f.toBitVec)) = f.toBitVec
    rw [BitVec.zero_and, BitVec.xor_zero]
  · change f ^^^ (0xFFFFFFFFFFFFFFFF &&& (t ^^^ f)) = t
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [UInt64.toBitVec_xor, UInt64.toBitVec_and, BitVec.getLsbD_xor, BitVec.getLsbD_and]
    rw [allOnes64_getLsbD i hi, Bool.true_and]
    cases f.toBitVec.getLsbD i <;> cases t.toBitVec.getLsbD i <;> rfl

theorem u32Max_eq (a b : UInt32) :
    u32Max a b = (if a.toNat < b.toNat then b else a) := by
  unfold u32Max
  rw [selU32_eq]
  have heq : decide (a < b) = decide (a.toNat < b.toNat) := rfl
  rw [heq]
  cases h : decide (a.toNat < b.toNat)
  · simp [of_decide_eq_false h]
  · simp [of_decide_eq_true h]

theorem u32Max_zero_left (b : UInt32) : u32Max 0 b = b := by
  unfold u32Max
  rw [selU32_eq]
  cases h : decide ((0 : UInt32) < b)
  · have hle : b.toNat ≤ 0 := Nat.not_lt.mp (of_decide_eq_false h)
    have hb0 : b = 0 := UInt32.toNat_inj.mp (Nat.eq_zero_of_le_zero hle)
    rw [hb0]; rfl
  · rfl

theorem u32Max_lt_of_lt {a b m : UInt32} (ha : a < m) (hb : b < m) :
    u32Max a b < m := by
  unfold u32Max
  rw [selU32_eq]
  cases decide (a < b) <;> assumption

private theorem u32_toU64_getLsbD_high (x : UInt32) {i : Nat} (hi : 32 ≤ i) :
    (x.toUInt64.toBitVec).getLsbD i = false := by
  show Nat.testBit x.toUInt64.toNat i = false
  rw [UInt32.toNat_toUInt64]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.toNat_lt (Nat.pow_le_pow_right (by decide : 0 < 2) hi))

private theorem u32_toU64_getLsbD_eq (x : UInt32) (i : Nat) :
    (x.toUInt64.toBitVec).getLsbD i = x.toBitVec.getLsbD i := by
  show Nat.testBit x.toUInt64.toNat i = Nat.testBit x.toNat i
  rw [UInt32.toNat_toUInt64]

private theorem u64_toU32_getLsbD_eq (x : UInt64) {i : Nat} (hi : i < 32) :
    (x.toUInt32.toBitVec).getLsbD i = x.toBitVec.getLsbD i := by
  show Nat.testBit x.toUInt32.toNat i = Nat.testBit x.toNat i
  rw [UInt64.toNat_toUInt32, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

private theorem u32_lt_29_getLsbD (h : UInt32) (hlt : h < 500000000) {i : Nat} (hi : 29 ≤ i) :
    (h.toUInt64.toBitVec).getLsbD i = false := by
  show Nat.testBit h.toUInt64.toNat i = false
  rw [UInt32.toNat_toUInt64]
  have hlt29 : h.toNat < 2 ^ 29 := Nat.lt_trans (UInt32.lt_iff_toNat_lt.mp hlt) (by decide)
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt29 (Nat.pow_le_pow_right (by decide : 0 < 2) hi))

theorem ltPack_mode1_eq (h t : UInt32) :
    ltPack 1 h t = (0xA000000000000000 : UInt64) ||| (h.toUInt64 <<< 32) ||| t.toUInt64 := by
  unfold ltPack; repeat rw [selU64_eq]
  rfl

theorem ltPack_mode2_eq (h t : UInt32) :
    ltPack 2 h t = (0xC000000000000000 : UInt64) ||| h.toUInt64 := by
  unfold ltPack; repeat rw [selU64_eq]
  rfl

theorem ltPack_mode3_eq (h t : UInt32) :
    ltPack 3 h t = (0xE000000000000000 : UInt64) ||| t.toUInt64 := by
  unfold ltPack; repeat rw [selU64_eq]
  rfl

theorem ltPack_mode1_ne_zero (h t : UInt32) : ltPack 1 h t ≠ 0 := by
  intro heq
  have hbit := congrArg (fun v : UInt64 => v.toBitVec.getLsbD 63) heq
  rw [ltPack_mode1_eq] at hbit
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or] at hbit
  have hb63 : ((0xA000000000000000 : UInt64).toBitVec).getLsbD 63 = true := by decide
  have hz : ((0 : UInt64).toBitVec).getLsbD 63 = false := BitVec.getLsbD_zero
  rw [hb63, hz, Bool.true_or, Bool.true_or] at hbit
  exact Bool.noConfusion hbit

theorem ltPack_mode2_ne_zero (h t : UInt32) : ltPack 2 h t ≠ 0 := by
  intro heq
  have hbit := congrArg (fun v : UInt64 => v.toBitVec.getLsbD 63) heq
  rw [ltPack_mode2_eq] at hbit
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or] at hbit
  have hb63 : ((0xC000000000000000 : UInt64).toBitVec).getLsbD 63 = true := by decide
  have hz : ((0 : UInt64).toBitVec).getLsbD 63 = false := BitVec.getLsbD_zero
  rw [hb63, hz, Bool.true_or] at hbit
  exact Bool.noConfusion hbit

theorem ltPack_mode3_ne_zero (h t : UInt32) : ltPack 3 h t ≠ 0 := by
  intro heq
  have hbit := congrArg (fun v : UInt64 => v.toBitVec.getLsbD 63) heq
  rw [ltPack_mode3_eq] at hbit
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or] at hbit
  have hb63 : ((0xE000000000000000 : UInt64).toBitVec).getLsbD 63 = true := by decide
  have hz : ((0 : UInt64).toBitVec).getLsbD 63 = false := BitVec.getLsbD_zero
  rw [hb63, hz, Bool.true_or] at hbit
  exact Bool.noConfusion hbit

private theorem mask3_high_zero : ∀ i < 64, 2 ≤ i → ((3 : UInt64).toBitVec).getLsbD i = false := by decide
private theorem mask29_getLsbD : ∀ i < 64, ((0x1FFFFFFF : UInt64).toBitVec).getLsbD i = decide (i < 29) := by decide

theorem ltMode_mode1 (h t : UInt32) (hlt : h < 500000000) :
    ltMode (ltPack 1 h t) = 1 := by
  unfold ltMode; rw [ltPack_mode1_eq]
  apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq',
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  cases hi2 : decide (i < 2)
  · have hge2 : 2 ≤ i := Nat.not_lt.mp (of_decide_eq_false hi2)
    rw [mask3_high_zero i hi hge2, Bool.and_false]
    have h1z : ∀ j < 64, 2 ≤ j → ((1 : UInt64).toBitVec).getLsbD j = false := by decide
    exact (h1z i hi hge2).symm
  · have hlt2 : i < 2 := of_decide_eq_true hi2
    have hsh61 : (((61 : UInt64).toBitVec) % 64).toNat = 61 := rfl
    have hsh32 : (((32 : UInt64).toBitVec) % 64).toNat = 32 := rfl
    rw [hsh61, hsh32]
    have ht_zero : (t.toUInt64.toBitVec).getLsbD (61 + i) = false :=
      u32_toU64_getLsbD_high t (Nat.le_trans (by decide : 32 ≤ 61) (Nat.le_add_right 61 i))
    have hh_zero : (h.toUInt64.toBitVec).getLsbD (61 + i - 32) = false := by
      have hge29 : 29 ≤ 61 + i - 32 := by
        cases i with
        | zero => decide
        | succ k =>
          cases k with
          | zero => decide
          | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt2)))
      exact u32_lt_29_getLsbD h hlt hge29
    rw [ht_zero, hh_zero, Bool.and_false, Bool.or_false, Bool.or_false]
    cases i with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt2)))

theorem ltMode_mode2 (h : UInt32) :
    ltMode (ltPack 2 h 0) = 2 := by
  unfold ltMode; rw [ltPack_mode2_eq]
  apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
      BitVec.ushiftRight_eq', BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
  cases hi2 : decide (i < 2)
  · have hge2 : 2 ≤ i := Nat.not_lt.mp (of_decide_eq_false hi2)
    rw [mask3_high_zero i hi hge2, Bool.and_false]
    have h2z : ∀ j < 64, 2 ≤ j → ((2 : UInt64).toBitVec).getLsbD j = false := by decide
    exact (h2z i hi hge2).symm
  · have hlt2 : i < 2 := of_decide_eq_true hi2
    have hsh61 : (((61 : UInt64).toBitVec) % 64).toNat = 61 := rfl
    rw [hsh61]
    have hh_zero : (h.toUInt64.toBitVec).getLsbD (61 + i) = false :=
      u32_toU64_getLsbD_high h (Nat.le_trans (by decide : 32 ≤ 61) (Nat.le_add_right 61 i))
    rw [hh_zero, Bool.or_false]
    cases i with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt2)))

theorem ltMode_mode3 (t : UInt32) :
    ltMode (ltPack 3 0 t) = 3 := by
  unfold ltMode; rw [ltPack_mode3_eq]
  apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
      BitVec.ushiftRight_eq', BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or]
  cases hi2 : decide (i < 2)
  · have hge2 : 2 ≤ i := Nat.not_lt.mp (of_decide_eq_false hi2)
    rw [mask3_high_zero i hi hge2, Bool.and_false]
  · have hlt2 : i < 2 := of_decide_eq_true hi2
    have hsh61 : (((61 : UInt64).toBitVec) % 64).toNat = 61 := rfl
    rw [hsh61]
    have ht_zero : (t.toUInt64.toBitVec).getLsbD (61 + i) = false :=
      u32_toU64_getLsbD_high t (Nat.le_trans (by decide : 32 ≤ 61) (Nat.le_add_right 61 i))
    rw [ht_zero]
    cases i with
    | zero => decide
    | succ k =>
      cases k with
      | zero => decide
      | succ m => exact False.elim (Nat.not_lt_zero m (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt2)))

theorem ltMaxH_mode1 (h t : UInt32) (hlt : h < 500000000) :
    ltMaxH (ltPack 1 h t) = h := by
  unfold ltMaxH
  rw [selU32_eq, ltMode_mode1 h t hlt]
  change (((ltPack 1 h t) >>> 32) &&& 0x1FFFFFFF).toUInt32 = h
  rw [ltPack_mode1_eq]
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [u64_toU32_getLsbD_eq _ hi]
  have hi64 : i < 64 := Nat.lt_trans hi (by decide)
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_or,
      UInt64.toBitVec_shiftLeft, BitVec.ushiftRight_eq', BitVec.shiftLeft_eq',
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  rw [mask29_getLsbD i hi64]
  have hsh32 : (((32 : UInt64).toBitVec) % 64).toNat = 32 := rfl
  rw [hsh32]
  cases hi29 : decide (i < 29)
  · rw [Bool.and_false]
    have hge29 : 29 ≤ i := Nat.not_lt.mp (of_decide_eq_false hi29)
    rw [← u32_toU64_getLsbD_eq h i, u32_lt_29_getLsbD h hlt hge29]
  · rw [Bool.and_true]
    have hlt29 : i < 29 := of_decide_eq_true hi29
    have hb_hi : ∀ j < 29, ((0xA000000000000000 : UInt64).toBitVec).getLsbD (32 + j) = false := by decide
    have ht_hi : (t.toUInt64.toBitVec).getLsbD (32 + i) = false :=
      u32_toU64_getLsbD_high t (Nat.le_add_right 32 i)
    have hlt64 : decide (32 + i < 64) = true := decide_eq_true (Nat.add_lt_add_left (Nat.lt_trans hlt29 (by decide : 29 < 32)) 32)
    have hnotlt32 : decide (32 + i < 32) = false := decide_eq_false (Nat.not_lt.mpr (Nat.le_add_right 32 i))
    have hsub : 32 + i - 32 = i := Nat.add_sub_cancel_left 32 i
    rw [hb_hi i hlt29, ht_hi, hlt64, hnotlt32, hsub, Bool.false_or, Bool.or_false,
        Bool.not_false, Bool.and_true, Bool.true_and, u32_toU64_getLsbD_eq h i]

theorem ltMaxT_mode1 (h t : UInt32) :
    ltMaxT (ltPack 1 h t) = t := by
  unfold ltMaxT; rw [ltPack_mode1_eq]
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [u64_toU32_getLsbD_eq _ hi]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq',
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have hsh32 : (((32 : UInt64).toBitVec) % 64).toNat = 32 := rfl
  rw [hsh32]
  have hb_lo : ∀ j < 32, ((0xA000000000000000 : UInt64).toBitVec).getLsbD j = false := by decide
  have hlt32 : decide (i < 32) = true := decide_eq_true hi
  rw [hb_lo i hi, hlt32, Bool.not_true, Bool.and_false, Bool.false_and,
      Bool.false_or, Bool.false_or, u32_toU64_getLsbD_eq t i]

theorem ltMaxH_mode2 (h : UInt32) :
    ltMaxH (ltPack 2 h 0) = h := by
  unfold ltMaxH
  rw [selU32_eq, ltMode_mode2 h]
  change (ltPack 2 h 0).toUInt32 = h
  rw [ltPack_mode2_eq]
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [u64_toU32_getLsbD_eq _ hi]
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  have hb_lo : ∀ j < 32, ((0xC000000000000000 : UInt64).toBitVec).getLsbD j = false := by decide
  rw [hb_lo i hi, Bool.false_or, u32_toU64_getLsbD_eq h i]

theorem ltMaxT_mode3 (t : UInt32) :
    ltMaxT (ltPack 3 0 t) = t := by
  unfold ltMaxT; rw [ltPack_mode3_eq]
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [u64_toU32_getLsbD_eq _ hi]
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  have hb_lo : ∀ j < 32, ((0xE000000000000000 : UInt64).toBitVec).getLsbD j = false := by decide
  rw [hb_lo i hi, Bool.false_or, u32_toU64_getLsbD_eq t i]

/-- Step helper folding a `InternalSpec.Psbt.PsbtInput` into the 64-bit freestanding state. -/
def psbtInputStep64 (st : UInt64) (inp : InternalSpec.Psbt.PsbtInput) : UInt64 :=
  let hasH : UInt8 := if inp.requiredHeightLocktime.isSome then 1 else 0
  let h : UInt32 := inp.requiredHeightLocktime.getD 0
  let hasT : UInt8 := if inp.requiredTimeLocktime.isSome then 1 else 0
  let t : UInt32 := inp.requiredTimeLocktime.getD 0
  llbPsbtLocktimeStep st hasH h hasT t

def psbtFoldInputs64 (st : UInt64) : List InternalSpec.Psbt.PsbtInput → UInt64
  | [] => st
  | inp :: rest => psbtFoldInputs64 (psbtInputStep64 st inp) rest

theorem psbtFoldInputs64_eq_foldl (st : UInt64) (inputs : List InternalSpec.Psbt.PsbtInput) :
    psbtFoldInputs64 st inputs = inputs.foldl psbtInputStep64 st := by
  induction inputs generalizing st with
  | nil => rfl
  | cons inp rest ih => exact ih (psbtInputStep64 st inp)

/-- Simulation relation between the 64-bit freestanding BIP-370 state and `BitcoinLedger.Psbt.LocktimeScanState`. -/
inductive LocktimeSim : UInt64 → Option BitcoinLedger.Psbt.LocktimeScanState → Prop where
  | errNone : LocktimeSim 0 none
  | errConflict (s : BitcoinLedger.Psbt.LocktimeScanState)
      (hh : s.hasHeightOnly = true) (ht : s.hasTimeOnly = true) :
      LocktimeSim 0 (some s)
  | mode0 :
      LocktimeSim llbPsbtLocktimeInit (some {})
  | mode1 (h t : UInt32) (hlt : h < 500000000) :
      LocktimeSim (ltPack 1 h t) (some {
        hasHeightOnly := false, hasTimeOnly := false,
        anyHeight := true, anyTime := true,
        maxHeight := h, maxTime := t })
  | mode2 (h t : UInt32) (anyT : Bool) :
      LocktimeSim (ltPack 2 h 0) (some {
        hasHeightOnly := true, hasTimeOnly := false,
        anyHeight := true, anyTime := anyT,
        maxHeight := h, maxTime := t })
  | mode3 (h t : UInt32) (anyH : Bool) :
      LocktimeSim (ltPack 3 0 t) (some {
        hasHeightOnly := false, hasTimeOnly := true,
        anyHeight := anyH, anyTime := true,
        maxHeight := h, maxTime := t })

private theorem llbPsbtLocktimeStep_zero (hasH : UInt8) (h : UInt32) (hasT : UInt8) (t : UInt32) :
    llbPsbtLocktimeStep 0 hasH h hasT t = 0 := by
  unfold llbPsbtLocktimeStep
  dsimp only
  rw [selU64_eq, band_eq]
  have hz : decide ((0 : UInt64) ≠ 0) = false := rfl
  rw [hz, Bool.false_and]
  rfl

private theorem psbtInputBounds_eq (inp : InternalSpec.Psbt.PsbtInput) :
    let hasH : UInt8 := if inp.requiredHeightLocktime.isSome then 1 else 0
    let h : UInt32 := inp.requiredHeightLocktime.getD 0
    let hasT : UInt8 := if inp.requiredTimeLocktime.isSome then 1 else 0
    let t : UInt32 := inp.requiredTimeLocktime.getD 0
    band (bor (bnot (decide (hasH ≠ 0))) (band (decide (1 ≤ h)) (decide (h < 500000000))))
         (bor (bnot (decide (hasT ≠ 0))) (decide (500000000 ≤ t))) =
      BitcoinLedger.Psbt.checkInputLocktimeBounds inp := by
  dsimp only
  rw [band_eq, bor_eq, bor_eq, bnot_eq, bnot_eq, band_eq]
  unfold BitcoinLedger.Psbt.checkInputLocktimeBounds
  have hthr : BitcoinLedger.Psbt.LOCKTIME_THRESHOLD_U32.toNat = 500000000 := rfl
  cases inp.requiredHeightLocktime with
  | none =>
    cases inp.requiredTimeLocktime with
    | none => rfl
    | some t =>
      change (true && (false || decide (500000000 ≤ t))) = (true && decide (BitcoinLedger.Psbt.LOCKTIME_THRESHOLD_U32.toNat ≤ t.toNat))
      rw [Bool.true_and, Bool.true_and, Bool.false_or, hthr]; rfl
  | some h =>
    have hhEq : (decide (1 ≤ h) && decide (h < 500000000)) = decide (0 < h.toNat ∧ h.toNat < 500000000) := by
      have h1 : decide (1 ≤ h) = decide (0 < h.toNat) := rfl
      have h2 : decide (h < 500000000) = decide (h.toNat < 500000000) := rfl
      rw [h1, h2]
      cases h0 : decide (0 < h.toNat) <;> cases h5 : decide (h.toNat < 500000000)
      · exact (decide_eq_false (fun ⟨a, _⟩ => of_decide_eq_false h0 a)).symm
      · exact (decide_eq_false (fun ⟨a, _⟩ => of_decide_eq_false h0 a)).symm
      · exact (decide_eq_false (fun ⟨_, b⟩ => of_decide_eq_false h5 b)).symm
      · exact (decide_eq_true ⟨of_decide_eq_true h0, of_decide_eq_true h5⟩).symm
    cases inp.requiredTimeLocktime with
    | none =>
      change ((false || (decide (1 ≤ h) && decide (h < 500000000))) && true) =
        (decide (0 < h.toNat ∧ h.toNat < BitcoinLedger.Psbt.LOCKTIME_THRESHOLD_U32.toNat) && true)
      rw [Bool.false_or, Bool.and_true, Bool.and_true, hthr, hhEq]
    | some t =>
      change ((false || (decide (1 ≤ h) && decide (h < 500000000))) && (false || decide (500000000 ≤ t))) =
        (decide (0 < h.toNat ∧ h.toNat < BitcoinLedger.Psbt.LOCKTIME_THRESHOLD_U32.toNat) &&
         decide (BitcoinLedger.Psbt.LOCKTIME_THRESHOLD_U32.toNat ≤ t.toNat))
      rw [Bool.false_or, Bool.false_or, hthr, hhEq]; rfl

theorem psbtInputStep_sim {st : UInt64} {s : BitcoinLedger.Psbt.LocktimeScanState}
    (hsim : LocktimeSim st (some s)) (inp : InternalSpec.Psbt.PsbtInput) :
    LocktimeSim (psbtInputStep64 st inp)
      (if !BitcoinLedger.Psbt.checkInputLocktimeBounds inp then none
       else some {
         hasHeightOnly := s.hasHeightOnly || (inp.requiredHeightLocktime.isSome && inp.requiredTimeLocktime.isNone)
         hasTimeOnly := s.hasTimeOnly || (inp.requiredTimeLocktime.isSome && inp.requiredHeightLocktime.isNone)
         anyHeight := s.anyHeight || inp.requiredHeightLocktime.isSome
         anyTime := s.anyTime || inp.requiredTimeLocktime.isSome
         maxHeight := match inp.requiredHeightLocktime with
           | some h => if s.maxHeight.toNat < h.toNat then h else s.maxHeight
           | none => s.maxHeight
         maxTime := match inp.requiredTimeLocktime with
           | some t => if s.maxTime.toNat < t.toNat then t else s.maxTime
           | none => s.maxTime }) := by
  cases hbounds : BitcoinLedger.Psbt.checkInputLocktimeBounds inp
  · simp only [Bool.not_false, ↓reduceIte]
    unfold psbtInputStep64 llbPsbtLocktimeStep
    dsimp only
    have hb := psbtInputBounds_eq inp
    dsimp only at hb
    rw [hbounds] at hb
    rw [hb, band_eq, Bool.and_false, selU64_eq]
    exact LocktimeSim.errNone
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hb := psbtInputBounds_eq inp
    dsimp only at hb
    rw [hbounds] at hb
    cases hsim with
    | errConflict s hh ht =>
      unfold psbtInputStep64
      rw [llbPsbtLocktimeStep_zero]
      apply LocktimeSim.errConflict
      · rw [hh, Bool.true_or]
      · rw [ht, Bool.true_or]
    | mode0 =>
      unfold psbtInputStep64 llbPsbtLocktimeStep
      dsimp only
      rw [hb]
      have hinit_ne : decide (llbPsbtLocktimeInit ≠ 0) = true := by decide
      have hinit_m : ltMode llbPsbtLocktimeInit = 0 := rfl
      rw [band_eq, hinit_ne, Bool.true_and, hinit_m]
      repeat rw [selU64_eq]
      cases hh : inp.requiredHeightLocktime <;> cases ht : inp.requiredTimeLocktime
      · exact LocktimeSim.mode0
      · rename_i t
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.and_true, Bool.false_and]
        rw [bnot_eq, bnot_eq, band_eq]
        change LocktimeSim (ltPack 3 0 t) _
        rw [← u32Max_eq 0 t, u32Max_zero_left t]
        exact LocktimeSim.mode3 0 t false
      · rename_i h
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.and_true, Bool.false_and]
        rw [bnot_eq, bnot_eq, band_eq, band_eq]
        change LocktimeSim (ltPack 2 h 0) _
        rw [← u32Max_eq 0 h, u32Max_zero_left h]
        exact LocktimeSim.mode2 h 0 false
      · rename_i h t
        have hh_lt : h < 500000000 := by
          unfold BitcoinLedger.Psbt.checkInputLocktimeBounds at hbounds
          rw [hh, ht] at hbounds
          have ⟨hhOk, _⟩ := Bool.and_eq_true_iff.mp hbounds
          exact UInt32.lt_iff_toNat_lt.mpr (of_decide_eq_true hhOk).2
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.and_false]
        rw [band_eq, band_eq]
        change LocktimeSim (ltPack 1 h t) _
        rw [← u32Max_eq 0 h, u32Max_zero_left h, ← u32Max_eq 0 t, u32Max_zero_left t]
        exact LocktimeSim.mode1 h t hh_lt
    | mode1 h0 t0 hlt0 =>
      unfold psbtInputStep64 llbPsbtLocktimeStep
      dsimp only
      rw [hb]
      have hne : decide (ltPack 1 h0 t0 ≠ 0) = true := decide_eq_true (ltPack_mode1_ne_zero h0 t0)
      rw [band_eq, hne, Bool.true_and, ltMode_mode1 h0 t0 hlt0,
          ltMaxH_mode1 h0 t0 hlt0, ltMaxT_mode1 h0 t0]
      repeat rw [selU64_eq]
      cases hh : inp.requiredHeightLocktime <;> cases ht : inp.requiredTimeLocktime
      · simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_false, Bool.false_and]
        exact LocktimeSim.mode1 h0 t0 hlt0
      · rename_i t
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.or_true, Bool.and_true, Bool.false_and, bor_eq]
        rw [bnot_eq, band_eq, ← u32Max_eq t0 t]
        exact LocktimeSim.mode3 h0 (u32Max t0 t) true
      · rename_i h
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.or_false, Bool.and_true, Bool.false_and, bor_eq]
        rw [bnot_eq, band_eq, ← u32Max_eq h0 h]
        exact LocktimeSim.mode2 (u32Max h0 h) t0 true
      · rename_i h t
        have hh_lt : h < 500000000 := by
          unfold BitcoinLedger.Psbt.checkInputLocktimeBounds at hbounds
          rw [hh, ht] at hbounds
          have ⟨hhOk, _⟩ := Bool.and_eq_true_iff.mp hbounds
          exact UInt32.lt_iff_toNat_lt.mpr (of_decide_eq_true hhOk).2
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.or_true, Bool.and_false]
        rw [band_eq, band_eq, ← u32Max_eq h0 h, ← u32Max_eq t0 t]
        exact LocktimeSim.mode1 (u32Max h0 h) (u32Max t0 t) (u32Max_lt_of_lt hlt0 hh_lt)
    | mode2 h0 t0 anyT =>
      unfold psbtInputStep64 llbPsbtLocktimeStep
      dsimp only
      rw [hb]
      have hne : decide (ltPack 2 h0 0 ≠ 0) = true := decide_eq_true (ltPack_mode2_ne_zero h0 0)
      rw [band_eq, hne, Bool.true_and, ltMode_mode2 h0, ltMaxH_mode2 h0]
      repeat rw [selU64_eq]
      cases hh : inp.requiredHeightLocktime <;> cases ht : inp.requiredTimeLocktime
      · simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_false, Bool.false_and]
        exact LocktimeSim.mode2 h0 t0 anyT
      · rename_i t
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_true, Bool.and_true, Bool.false_and, bor_eq]
        rw [bnot_eq, band_eq]
        exact LocktimeSim.errConflict _ rfl rfl
      · rename_i h
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_false, Bool.and_true, Bool.false_and, bor_eq]
        rw [bnot_eq, band_eq, ← u32Max_eq h0 h]
        exact LocktimeSim.mode2 (u32Max h0 h) t0 anyT
      · rename_i h t
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.or_true, Bool.and_false]
        rw [band_eq, band_eq, ← u32Max_eq h0 h, ← u32Max_eq t0 t]
        exact LocktimeSim.mode2 (u32Max h0 h) (u32Max t0 t) true
    | mode3 h0 t0 anyH =>
      unfold psbtInputStep64 llbPsbtLocktimeStep
      dsimp only
      rw [hb]
      have hne : decide (ltPack 3 0 t0 ≠ 0) = true := decide_eq_true (ltPack_mode3_ne_zero 0 t0)
      rw [band_eq, hne, Bool.true_and, ltMode_mode3 t0, ltMaxT_mode3 t0]
      repeat rw [selU64_eq]
      cases hh : inp.requiredHeightLocktime <;> cases ht : inp.requiredTimeLocktime
      · simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_false, Bool.false_and]
        exact LocktimeSim.mode3 h0 t0 anyH
      · rename_i t
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_false, Bool.and_true, Bool.false_and, bor_eq]
        rw [bnot_eq, band_eq, ← u32Max_eq t0 t]
        exact LocktimeSim.mode3 h0 (u32Max t0 t) anyH
      · rename_i h
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.or_true, Bool.and_true, Bool.false_and, bor_eq]
        rw [bnot_eq, band_eq]
        exact LocktimeSim.errConflict _ rfl rfl
      · rename_i h t
        simp only [Option.isSome, Option.isNone, Option.getD, Bool.false_or, Bool.or_true, Bool.and_false]
        rw [band_eq, band_eq, ← u32Max_eq h0 h, ← u32Max_eq t0 t]
        exact LocktimeSim.mode3 (u32Max h0 h) (u32Max t0 t) true

private theorem psbtFoldInputs64_zero (inputs : List InternalSpec.Psbt.PsbtInput) :
    psbtFoldInputs64 0 inputs = 0 := by
  induction inputs with
  | nil => rfl
  | cons inp rest ih =>
    unfold psbtFoldInputs64 psbtInputStep64
    rw [llbPsbtLocktimeStep_zero]
    exact ih

theorem psbtFoldInputs64_sim (inputs : List InternalSpec.Psbt.PsbtInput) :
    ∀ {st : UInt64} {opt : Option BitcoinLedger.Psbt.LocktimeScanState},
      LocktimeSim st opt →
      LocktimeSim (psbtFoldInputs64 st inputs)
        (match opt with
         | none => none
         | some s => BitcoinLedger.Psbt.scanLocktimeInputs s inputs) := by
  induction inputs with
  | nil =>
    intro st opt hsim
    cases opt <;> exact hsim
  | cons inp rest ih =>
    intro st opt hsim
    cases opt with
    | none =>
      cases hsim
      rw [psbtFoldInputs64_zero]
      exact LocktimeSim.errNone
    | some s =>
      unfold psbtFoldInputs64 BitcoinLedger.Psbt.scanLocktimeInputs
      have hstep := psbtInputStep_sim hsim inp
      cases hbounds : BitcoinLedger.Psbt.checkInputLocktimeBounds inp
      · simp only [hbounds, Bool.not_false, ↓reduceIte] at hstep ⊢
        exact ih hstep
      · simp only [hbounds, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep ⊢
        exact ih hstep

/-- Encode `Except PsbtError UInt32` into the freestanding C ABI `UInt64` return convention
    (`(1 <<< 32) ||| locktime` on `.ok locktime`, `0` on `.error _`). -/
def encodeLocktimeResult : Except InternalSpec.Psbt.PsbtError UInt32 → UInt64
  | .ok lt => ((1 : UInt64) <<< 32) ||| lt.toUInt64
  | .error _ => 0

/-- Exact end-to-end BIP-370 refinement (VND-04): folding `llbPsbtLocktimeStep` from
    `llbPsbtLocktimeInit` and finalizing with `llbPsbtLocktimeFinalize` computes the exact
    same result as `BitcoinLedger.Psbt.determineLocktime` for all input lists and fallbacks. -/
theorem llbPsbtLocktime_eq_determineLocktime
    (fallbackLocktime : Option UInt32) (inputs : List InternalSpec.Psbt.PsbtInput) :
    llbPsbtLocktimeFinalize (psbtFoldInputs64 llbPsbtLocktimeInit inputs) (fallbackLocktime.getD 0) =
      encodeLocktimeResult (BitcoinLedger.Psbt.determineLocktime fallbackLocktime inputs) := by
  have hsim := psbtFoldInputs64_sim inputs LocktimeSim.mode0
  dsimp only at hsim
  unfold BitcoinLedger.Psbt.determineLocktime llbPsbtLocktimeFinalize
  generalize hst : psbtFoldInputs64 llbPsbtLocktimeInit inputs = stFinal at hsim ⊢
  generalize hopt : BitcoinLedger.Psbt.scanLocktimeInputs {} inputs = optFinal at hsim ⊢
  dsimp only
  cases hsim with
  | errNone =>
    rw [selU64_eq]; rfl
  | errConflict s hh ht =>
    rw [selU64_eq]
    simp only [hh, ht, Bool.true_and]
    rfl
  | mode0 =>
    rw [selU64_eq, selU32_eq]
    have hne : decide (llbPsbtLocktimeInit ≠ 0) = true := by decide
    have hm : ltMode llbPsbtLocktimeInit = 0 := rfl
    rw [hne, hm]; rfl
  | mode1 h t hlt =>
    rw [selU64_eq, selU32_eq, selU32_eq, bor_eq]
    have hne : decide (ltPack 1 h t ≠ 0) = true := decide_eq_true (ltPack_mode1_ne_zero h t)
    rw [hne, ltMode_mode1 h t hlt, ltMaxH_mode1 h t hlt]; rfl
  | mode2 h t anyT =>
    rw [selU64_eq, selU32_eq, selU32_eq, bor_eq]
    have hne : decide (ltPack 2 h 0 ≠ 0) = true := decide_eq_true (ltPack_mode2_ne_zero h 0)
    rw [hne, ltMode_mode2 h, ltMaxH_mode2 h]
    cases anyT <;> rfl
  | mode3 h t anyH =>
    rw [selU64_eq, selU32_eq, selU32_eq, bor_eq]
    have hne : decide (ltPack 3 0 t ≠ 0) = true := decide_eq_true (ltPack_mode3_ne_zero 0 t)
    rw [hne, ltMode_mode3 t, ltMaxT_mode3 t]
    cases anyH <;> rfl

/-! ## 9. Exact Division/Modulo by 10 (`div10U32`, `mod10U32`) & BIP-379 Miniscript Refinement -/

private theorem div_lt_of_lt_mul10 {a b c : Nat} (h : a < b * c) : a / b < c := by
  have h1 : b * (a / b) ≤ a := Nat.mul_div_le a b
  have h2 : b * (a / b) < b * c := Nat.lt_of_le_of_lt h1 h
  exact Nat.lt_of_not_le (fun hle => Nat.lt_irrefl (b * c) (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left b hle) h2))

private def M10 : Nat := 0xCCCCCCCD
private def P35 : Nat := 34359738368

/-- Exact division-free `v / 10` for all `2^32` values of `v : UInt32`. -/
theorem div10U32_eq (v : UInt32) : div10U32 v = v / 10 := by
  apply UInt32.toNat_inj.mp
  unfold div10U32
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_div]
  have hsh : (35 : UInt64).toNat % 64 = 35 := rfl
  have hd10 : (10 : UInt32).toNat = 10 := rfl
  have hp35 : 2 ^ 35 = P35 := rfl
  rw [hsh, hd10, Nat.shiftRight_eq_div_pow, hp35]
  have hx_le : v.toNat ≤ 4294967295 := Nat.le_sub_one_of_lt v.toNat_lt
  have hm_eq : (v.toUInt64 * 0xCCCCCCCD).toNat = v.toNat * M10 := by
    rw [UInt64.toNat_mul, UInt32.toNat_toUInt64]
    have hm_val : (0xCCCCCCCD : UInt64).toNat = M10 := rfl
    rw [hm_val]
    have hlt64 : v.toNat * M10 < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right M10 hx_le) (by decide)
    exact Nat.mod_eq_of_lt hlt64
  rw [hm_eq]
  have hx : v.toNat = 10 * (v.toNat / 10) + v.toNat % 10 := (Nat.div_add_mod v.toNat 10).symm
  have hr_le : v.toNat % 10 ≤ 9 := Nat.le_sub_one_of_lt (Nat.mod_lt v.toNat (by decide))
  have hq_lt : v.toNat / 10 < 429496730 := div_lt_of_lt_mul10 (Nat.lt_trans v.toNat_lt (by decide))
  have hq_le : v.toNat / 10 ≤ 429496729 := Nat.le_sub_one_of_lt hq_lt
  generalize v.toNat / 10 = q at hx hq_lt hq_le ⊢
  generalize v.toNat % 10 = r at hx hr_le
  have h_magic : 10 * M10 = P35 + 2 := rfl
  have h_prod : v.toNat * M10 = P35 * q + (2 * q + r * M10) := by
    calc v.toNat * M10
      _ = (10 * q + r) * M10 := by rw [hx]
      _ = q * (10 * M10) + r * M10 := by rw [Nat.add_mul, Nat.mul_comm 10 q, Nat.mul_assoc]
      _ = q * (P35 + 2) + r * M10 := by rw [h_magic]
      _ = P35 * q + (2 * q + r * M10) := by
        rw [Nat.mul_add, Nat.mul_comm q P35, Nat.mul_comm q 2, Nat.add_assoc]
  have herr_lt : 2 * q + r * M10 < P35 := by
    have hle := Nat.add_le_add (Nat.mul_le_mul_left 2 hq_le) (Nat.mul_le_mul_right M10 hr_le)
    exact Nat.lt_of_le_of_lt hle (by decide)
  have hdiv_eq : (v.toNat * M10) / P35 = q := by
    rw [h_prod, Nat.mul_add_div (by decide : 0 < P35), Nat.div_eq_of_lt herr_lt, Nat.add_zero]
  rw [hdiv_eq]
  exact Nat.mod_eq_of_lt (Nat.lt_trans hq_lt (by decide))

/-- Exact division-free `v % 10` for all `2^32` values of `v : UInt32`. -/
theorem mod10U32_eq (v : UInt32) : mod10U32 v = v % 10 := by
  unfold mod10U32
  rw [div10U32_eq]
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub_of_le, UInt32.toNat_mul, UInt32.toNat_div, UInt32.toNat_mod]
  · have hd10 : (10 : UInt32).toNat = 10 := rfl
    rw [hd10]
    have hprod_le : (v.toNat / 10) * 10 ≤ v.toNat := Nat.div_mul_le_self v.toNat 10
    have hprod_lt : (v.toNat / 10) * 10 < 2 ^ 32 := Nat.lt_of_le_of_lt hprod_le v.toNat_lt
    rw [Nat.mod_eq_of_lt hprod_lt]
    have hx : v.toNat = (v.toNat / 10) * 10 + v.toNat % 10 := by
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod v.toNat 10).symm
    generalize v.toNat / 10 = q at hx ⊢
    generalize v.toNat % 10 = r at hx ⊢
    rw [hx, Nat.add_sub_cancel_left]
  · rw [UInt32.le_iff_toNat_le, UInt32.toNat_mul, UInt32.toNat_div]
    have hd10 : (10 : UInt32).toNat = 10 := rfl
    rw [hd10]
    have hprod_le : (v.toNat / 10) * 10 ≤ v.toNat := Nat.div_mul_le_self v.toNat 10
    rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hprod_le v.toNat_lt)]
    exact hprod_le

/-! ### Miniscript Scalar Validators (`VND-01`, `VND-06`) -/

theorem llbMiniscriptOlderOk_eq_validOlderBitmask (n : UInt32) :
    llbMiniscriptOlderOk n = BitcoinLedger.WalletPolicy.validOlderBitmask n := by
  unfold llbMiniscriptOlderOk BitcoinLedger.WalletPolicy.validOlderBitmask
    BitcoinLedger.WalletPolicy.olderInvalidUpperMask
  rw [band_eq]
  have hbeq : ((n &&& 0xFFBF0000) == 0) = decide ((n &&& 0xFFBF0000) = 0) := rfl
  rw [hbeq]

theorem llbMiniscriptOlderOk_eq_validOlderArg (n : UInt32) :
    llbMiniscriptOlderOk n = BitcoinLedger.WalletPolicy.validOlderArg n ∧
    llbMiniscriptOlderOk n = InternalSpec.WalletPolicy.validOlderArg n := by
  have h1 := (llbMiniscriptOlderOk_eq_validOlderBitmask n).trans
    (Proofs.WalletPolicy.validOlderBitmask_eq_validOlderArg n)
  exact ⟨h1, h1.trans (Proofs.WalletPolicy.validOlderArg_eq n)⟩

theorem llbMiniscriptOlderOk_iff (n : UInt32) :
    llbMiniscriptOlderOk n = true ↔
      (n &&& 0xFFBF0000) = 0 ∧ (1 : UInt32) ≤ (n &&& 0xFFFF) := by
  unfold llbMiniscriptOlderOk
  rw [band_eq, Bool.and_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]

theorem llbMiniscriptAfterOk_eq_validAfterArg (n : UInt32) :
    llbMiniscriptAfterOk n = BitcoinLedger.WalletPolicy.validAfterArg n ∧
    llbMiniscriptAfterOk n = InternalSpec.WalletPolicy.validAfterArg n := by
  have h1 : llbMiniscriptAfterOk n = BitcoinLedger.WalletPolicy.validAfterArg n := by
    unfold llbMiniscriptAfterOk BitcoinLedger.WalletPolicy.validAfterArg
    exact band_eq _ _
  exact ⟨h1, h1.trans (Proofs.WalletPolicy.validAfterArg_eq n)⟩

theorem llbMiniscriptAfterOk_iff (n : UInt32) :
    llbMiniscriptAfterOk n = true ↔ (1 : UInt32) ≤ n ∧ n < 0x80000000 := by
  unfold llbMiniscriptAfterOk
  rw [band_eq, Bool.and_eq_true_iff, decide_eq_true_iff, decide_eq_true_iff]

/-! ### Packed `UInt16` Miniscript Node Algebra (`msBit`, `msOrBit`, `msPack`) -/

private theorem msBit_eq_getLsbD (x b : UInt16) (hb : b.toNat < 16) :
    msBit x b = x.toBitVec.getLsbD b.toNat := by
  unfold msBit
  have hmod : (b.toBitVec % 16).toNat = b.toNat := by
    rw [BitVec.toNat_umod]
    have h16 : BitVec.toNat (16 : BitVec 16) = 16 := rfl
    have hb_eq : b.toBitVec.toNat = b.toNat := rfl
    rw [h16, hb_eq, Nat.mod_eq_of_lt hb]
  cases hbit : x.toBitVec.getLsbD b.toNat
  · apply decide_eq_false
    intro heq
    have h0 := congrArg (fun u : UInt16 => u.toBitVec.getLsbD 0) heq
    simp only [UInt16.toBitVec_and, UInt16.toBitVec_shiftRight, BitVec.ushiftRight_eq',
        BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight] at h0
    rw [hmod, Nat.add_zero, hbit, Bool.false_and] at h0
    exact Bool.noConfusion h0
  · apply decide_eq_true
    apply UInt16.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [UInt16.toBitVec_and, UInt16.toBitVec_shiftRight, BitVec.ushiftRight_eq',
        BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
    rw [hmod, one16_getLsbD i hi]
    cases i with
    | zero =>
      rw [Nat.add_zero, hbit]; rfl
    | succ k =>
      have hk : decide (Nat.succ k = 0) = false := rfl
      rw [hk, Bool.and_false]

private theorem msOrBit_getLsbD (x b : UInt16) (v : Bool) {i : Nat} (hb : b.toNat < 16) (hi : i < 16) :
    (msOrBit x b v).toBitVec.getLsbD i =
      (x.toBitVec.getLsbD i || (decide (i = b.toNat) && v)) := by
  unfold msOrBit
  have hmod : (b.toBitVec % 16).toNat = b.toNat := by
    rw [BitVec.toNat_umod]
    have h16 : BitVec.toNat (16 : BitVec 16) = 16 := rfl
    have hb_eq : b.toBitVec.toNat = b.toNat := rfl
    rw [h16, hb_eq, Nat.mod_eq_of_lt hb]
  cases v
  · simp only [Bool.and_false, Bool.or_false, UInt16.toBitVec_or, UInt16.toBitVec_shiftLeft,
        BitVec.shiftLeft_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod]
    have hz : ((false.toUInt16).toBitVec).getLsbD (i - b.toNat) = false := by
      change (0#16).getLsbD (i - b.toNat) = false
      exact BitVec.getLsbD_zero
    rw [hz, Bool.and_false, Bool.or_false]
  · simp only [Bool.and_true, UInt16.toBitVec_or, UInt16.toBitVec_shiftLeft,
        BitVec.shiftLeft_eq', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hmod]
    rw [decide_eq_true hi, Bool.true_and]
    have hlt16 : i - b.toNat < 16 := Nat.lt_of_le_of_lt (Nat.sub_le i b.toNat) hi
    change (x.toBitVec.getLsbD i || (!decide (i < b.toNat) && ((1 : UInt16).toBitVec).getLsbD (i - b.toNat))) =
      (x.toBitVec.getLsbD i || decide (i = b.toNat))
    rw [one16_getLsbD (i - b.toNat) hlt16]
    cases hlt : decide (i < b.toNat)
    · have hge : b.toNat ≤ i := Nat.not_lt.mp (of_decide_eq_false hlt)
      cases heq : decide (i = b.toNat)
      · have hne : i ≠ b.toNat := of_decide_eq_false heq
        have hsub_ne : decide (i - b.toNat = 0) = false := by
          apply decide_eq_false; intro h0
          exact hne (Nat.le_antisymm (Nat.le_of_sub_eq_zero h0) hge)
        rw [hsub_ne]; rfl
      · rw [of_decide_eq_true heq, Nat.sub_self]; rfl
    · have hne : decide (i = b.toNat) = false :=
        decide_eq_false (Nat.ne_of_lt (of_decide_eq_true hlt))
      rw [hne]; rfl

private theorem msOrBit_mask3 (x b : UInt16) (v : Bool) (hb2 : 2 ≤ b.toNat) (hb16 : b.toNat < 16) :
    (msOrBit x b v) &&& 3 = x &&& 3 := by
  apply UInt16.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [UInt16.toBitVec_and, BitVec.getLsbD_and]
  rw [msOrBit_getLsbD x b v hb16 hi]
  cases hi2 : decide (i < 2)
  · have hge2 : 2 ≤ i := Nat.not_lt.mp (of_decide_eq_false hi2)
    rw [mask3_16_high_zero i hi hge2, Bool.and_false, Bool.and_false]
  · have hlt2 : i < 2 := of_decide_eq_true hi2
    have hne : decide (i = b.toNat) = false :=
      decide_eq_false (Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt2 hb2))
    rw [hne, Bool.false_and, Bool.or_false]

theorem msPack_base (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    (msPack base z o n d u s f e m g h i j k) &&& 3 = base &&& 3 := by
  unfold msPack; dsimp only
  repeat rw [msOrBit_mask3 _ _ _ (by decide) (by decide)]
  apply UInt16.eq_of_toBitVec_eq; apply BitVec.eq_of_getLsbD_eq; intro idx hidx
  simp only [UInt16.toBitVec_and, BitVec.getLsbD_and, Bool.and_assoc, Bool.and_self]

private theorem msPack_getLsbD (base : UInt16) (z o n d u s f e m g h i j k : Bool)
    {idx : Nat} (hge2 : 2 ≤ idx) (hidx : idx < 16) :
    (msPack base z o n d u s f e m g h i j k).toBitVec.getLsbD idx =
      ((decide (idx = 2) && z) || (decide (idx = 3) && o) || (decide (idx = 4) && n) ||
       (decide (idx = 5) && d) || (decide (idx = 6) && u) || (decide (idx = 7) && s) ||
       (decide (idx = 8) && f) || (decide (idx = 9) && e) || (decide (idx = 10) && m) ||
       (decide (idx = 11) && g) || (decide (idx = 12) && h) || (decide (idx = 13) && i) ||
       (decide (idx = 14) && j) || (decide (idx = 15) && k)) := by
  unfold msPack; dsimp only
  repeat rw [msOrBit_getLsbD _ _ _ (by decide) hidx]
  have hbase : ((base &&& 3).toBitVec).getLsbD idx = false := by
    simp only [UInt16.toBitVec_and, BitVec.getLsbD_and]
    rw [mask3_16_high_zero idx hidx hge2, Bool.and_false]
  rw [hbase, Bool.false_or]
  rfl

theorem msPack_z (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_Z = z := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases z <;> rfl

theorem msPack_o (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_O = o := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases o <;> rfl

theorem msPack_n (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_N = n := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases n <;> rfl

theorem msPack_d (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_D = d := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases d <;> rfl

theorem msPack_u (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_U = u := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases u <;> rfl

theorem msPack_s (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_S = s := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases s <;> rfl

theorem msPack_f (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_F = f := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases f <;> rfl

theorem msPack_e (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_E = e := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases e <;> rfl

theorem msPack_m (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_M = m := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases m <;> rfl

theorem msPack_g (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_G = g := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases g <;> rfl

theorem msPack_h (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_H = h := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases h <;> rfl

theorem msPack_i (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_I = i := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases i <;> rfl

theorem msPack_j (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_J = j := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases j <;> rfl

theorem msPack_k (base : UInt16) (z o n d u s f e m g h i j k : Bool) :
    msBit (msPack base z o n d u s f e m g h i j k) MSB_K = k := by
  rw [msBit_eq_getLsbD _ _ (by decide), msPack_getLsbD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide) (by decide)]
  cases k <;> rfl

/-- Any packed Miniscript node satisfying the BIP-379 `!(z && o)` invariant is distinct from `0xFFFF` (`msErr = false`). -/
theorem msPack_ne_err_of_not_zo (base : UInt16) (z o n d u s f e m g h i j k : Bool)
    (hzo : !(z && o) = true) :
    msErr (msPack base z o n d u s f e m g h i j k) = false := by
  unfold msErr
  apply decide_eq_false
  intro heq
  have hz := msPack_z base z o n d u s f e m g h i j k
  have ho := msPack_o base z o n d u s f e m g h i j k
  rw [heq] at hz ho
  have hz1 : msBit 0xFFFF MSB_Z = true := rfl
  have ho1 : msBit 0xFFFF MSB_O = true := rfl
  rw [← hz, ← ho, hz1, ho1] at hzo
  exact Bool.noConfusion hzo

/-! ### Refinement of Packed Miniscript Combinators Against `WalletPolicy` -/

/-- Encode `BasicType` (`B=0`, `V=1`, `K=2`, `W=3`) into bits `0..1` of a packed `UInt16` node. -/
def encodeBasicType : InternalSpec.WalletPolicy.BasicType → UInt16
  | .B => 0
  | .V => 1
  | .K => 2
  | .W => 3

/-- Pack all 15 BIP-379 type/malleability/timelock fields of `MiniscriptExtInfo` into a `UInt16`. -/
def packExtInfo (info : InternalSpec.WalletPolicy.MiniscriptExtInfo) : UInt16 :=
  msPack (encodeBasicType info.ty.base)
    info.ty.z info.ty.o info.ty.n info.ty.d info.ty.u
    info.s info.f info.e info.m
    info.g info.h info.i info.j info.k

/-- Packed `UInt16` projection of `Except _ MiniscriptExtInfo` (`0xFFFF` on `.error`). -/
def packExtResult : Except InternalSpec.WalletPolicy.PolicyError InternalSpec.WalletPolicy.MiniscriptExtInfo → UInt16
  | .ok out => packExtInfo out
  | .error _ => 0xFFFF

private theorem packExtResult_ok (out : InternalSpec.WalletPolicy.MiniscriptExtInfo) :
    packExtResult (.ok out) =
      msPack (encodeBasicType out.ty.base)
        out.ty.z out.ty.o out.ty.n out.ty.d out.ty.u
        out.s out.f out.e out.m
        out.g out.h out.i out.j out.k := rfl

private theorem packExtResult_err (e : InternalSpec.WalletPolicy.PolicyError) :
    packExtResult (.error e) = 0xFFFF := rfl

private theorem packExtResult_ite (c : Bool)
    (a b : Except InternalSpec.WalletPolicy.PolicyError InternalSpec.WalletPolicy.MiniscriptExtInfo) :
    packExtResult (if c then a else b) = (if c then packExtResult a else packExtResult b) := by
  cases c <;> rfl

theorem packExtInfo_base (info : InternalSpec.WalletPolicy.MiniscriptExtInfo) :
    (packExtInfo info) &&& 3 = encodeBasicType info.ty.base := by
  unfold packExtInfo
  rw [msPack_base]
  cases info.ty.base <;> rfl

/-- Exact refinement of `msConflict` against `BitcoinLedger.WalletPolicy.hasTimelockConflict`. -/
theorem msConflict_packExtInfo (a b : InternalSpec.WalletPolicy.MiniscriptExtInfo) :
    msConflict (packExtInfo a) (packExtInfo b) =
      BitcoinLedger.WalletPolicy.hasTimelockConflict a b := by
  unfold msConflict packExtInfo BitcoinLedger.WalletPolicy.hasTimelockConflict
  rw [bor_eq, bor_eq, bor_eq, band_eq, band_eq, band_eq, band_eq,
      msPack_g, msPack_h, msPack_h, msPack_g, msPack_i, msPack_j, msPack_j, msPack_i]
  cases a.g <;> cases a.h <;> cases a.i <;> cases a.j <;>
    cases b.g <;> cases b.h <;> cases b.i <;> cases b.j <;> rfl

/-- Postfix opcode encoding of `Wrapper` (`0x10..0x19`). -/
def wrapperOpcode : InternalSpec.WalletPolicy.MiniscriptWrapper → UInt8
  | .a => 0x10
  | .s => 0x11
  | .c => 0x12
  | .t => 0x13
  | .d => 0x14
  | .v => 0x15
  | .j => 0x16
  | .n => 0x17
  | .l => 0x18
  | .u => 0x19

private theorem msPack_congr
    {b1 b2 : UInt16} {z1 z2 o1 o2 n1 n2 d1 d2 u1 u2 s1 s2 f1 f2 e1 e2 m1 m2 g1 g2 h1 h2 i1 i2 j1 j2 k1 k2 : Bool}
    (hb : b1 = b2) (hz : z1 = z2) (ho : o1 = o2) (hn : n1 = n2) (hd : d1 = d2) (hu : u1 = u2)
    (hs : s1 = s2) (hf : f1 = f2) (he : e1 = e2) (hm : m1 = m2)
    (hg : g1 = g2) (hh : h1 = h2) (hi : i1 = i2) (hj : j1 = j2) (hk : k1 = k2) :
    msPack b1 z1 o1 n1 d1 u1 s1 f1 e1 m1 g1 h1 i1 j1 k1 =
      msPack b2 z2 o2 n2 d2 u2 s2 f2 e2 m2 g2 h2 i2 j2 k2 := by
  subst hb hz ho hn hd hu hs hf he hm hg hh hi hj hk; rfl

private theorem ite_pos {c : Prop} [Decidable c] (hc : c) {α : Type} {t e : α} :
    (if c then t else e) = t := by
  cases ‹Decidable c› with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h

private theorem ite_neg {c : Prop} [Decidable c] (hc : ¬c) {α : Type} {t e : α} :
    (if c then t else e) = e := by
  cases ‹Decidable c› with
  | isTrue h => exact absurd h hc
  | isFalse _ => rfl

/-- Exact refinement of `msApplyUnary` against all 10 `Wrapper` rules in `WalletPolicy.analyzeMiniscript`
    (both well-typed node packing and ill-typed `0xFFFF` rejection, including Tapscript `MINIMALIF` on `d:`). -/
theorem msApplyUnary_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (w : InternalSpec.WalletPolicy.MiniscriptWrapper)
    (sub : InternalSpec.WalletPolicy.Miniscript)
    (x : InternalSpec.WalletPolicy.MiniscriptExtInfo)
    (hsub : BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig sub = .ok x) :
    let isTap : UInt8 := if ctx == .tapscriptCtx then 1 else 0
    msApplyUnary (wrapperOpcode w) isTap (packExtInfo x) =
      match BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.wrap w sub) with
      | .ok out => packExtInfo out
      | .error _ => 0xFFFF := by
  rcases x with ⟨⟨xb, xz, xo, xn, xd, xu⟩, xs, xf, xe, xm, xg, xh, xi, xj, xk, xx, xoc, xos, xod, xss, xsd, xsz⟩
  dsimp only
  change msApplyUnary (wrapperOpcode w) (if ctx == .tapscriptCtx then 1 else 0) (packExtInfo _) =
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.wrap w sub))
  cases w <;> dsimp only [wrapperOpcode] <;> unfold msApplyUnary <;> dsimp only
  case a =>
    rw [ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_d] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)
  case s =>
    rw [ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_o] | rw [msPack_d] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq]
    cases xb <;> cases xo <;> first | rfl | (apply msPack_congr <;> rfl)
  case c =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_o] | rw [msPack_n] | rw [msPack_d] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)
  case t =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_n] | rw [msPack_u] | rw [msPack_s] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)
  case d =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_s] | rw [msPack_f] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq]
    cases ctx <;> cases xb <;> cases xz <;> first | rfl | (apply msPack_congr <;> first | rfl | decide)
  case v =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_n] | rw [msPack_s] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)
  case j =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_o] | rw [msPack_n] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq]
    cases xb <;> cases xn <;> first | rfl | (apply msPack_congr <;> rfl)
  case n =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_n] | rw [msPack_d] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)
  case l =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)
  case u =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hsub]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base]; unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq]
    cases xb <;> first | rfl | (apply msPack_congr <;> rfl)

/-- Exact refinement of `msApplyAndor` against the `.andor` rule in `WalletPolicy.analyzeMiniscript`
    (VND-01 / BIP-379 `andor(X, Y, Z)` typechecking and `hasTimelockConflict x y`). -/
theorem msApplyAndor_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (xNode yNode zNode : InternalSpec.WalletPolicy.Miniscript)
    (x y z : InternalSpec.WalletPolicy.MiniscriptExtInfo)
    (hx : BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig xNode = .ok x)
    (hy : BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig yNode = .ok y)
    (hz : BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig zNode = .ok z) :
    msApplyAndor (packExtInfo x) (packExtInfo y) (packExtInfo z) =
      match BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.andor xNode yNode zNode) with
      | .ok out => packExtInfo out
      | .error _ => 0xFFFF := by
  rcases x with ⟨⟨xb, xz, xo, xn, xd, xu⟩, xs, xf, xe, xm, xg, xh, xi, xj, xk, xx, xoc, xos, xod, xss, xsd, xsz⟩
  rcases y with ⟨⟨yb, yz, yo, yn, yd, yu⟩, ys, yf, ye, ym, yg, yh, yi, yj, yk, yx, yoc, yos, yod, yss, ysd, ysz⟩
  rcases z with ⟨⟨zb, zz, zo, zn, zd, zu⟩, zs, zf, ze, zm, zg, zh, zi, zj, zk, zx0, zoc, zos, zod, zss, zsd, zsz⟩
  unfold BitcoinLedger.WalletPolicy.analyzeMiniscript
  rw [hx, hy, hz]
  unfold msApplyAndor
  dsimp only
  rw [msConflict_packExtInfo, packExtInfo_base, packExtInfo_base, packExtInfo_base]
  unfold packExtInfo
  dsimp only
  repeat rw [msPack_z]
  repeat rw [msPack_o]
  repeat rw [msPack_d]
  repeat rw [msPack_u]
  repeat rw [msPack_s]
  repeat rw [msPack_f]
  repeat rw [msPack_e]
  repeat rw [msPack_m]
  repeat rw [msPack_g]
  repeat rw [msPack_h]
  repeat rw [msPack_i]
  repeat rw [msPack_j]
  repeat rw [msPack_k]
  rw [selU16_eq]
  repeat rw [band_eq]
  repeat rw [bor_eq]
  repeat rw [bnot_eq]
  cases xb <;> cases xd <;> cases xu <;> cases yb <;> cases zb <;> (
    simp (config := { decide := false }) only [encodeBasicType, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, bne, BEq.beq,
      Bool.and_assoc, Bool.or_assoc,
      Bool.false_and, Bool.true_and, Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or]
    <;> rfl)

/-- Enumeration of the 7 BIP-379 binary Miniscript combinators handled by `msApplyBinary`. -/
inductive MsBinOp where
  | and_v | and_b | and_n | or_b | or_c | or_d | or_i

/-- Postfix opcode (`0x20..0x26`) for each binary Miniscript combinator. -/
def MsBinOp.opcode : MsBinOp → UInt8
  | .and_v => 0x20
  | .and_b => 0x21
  | .and_n => 0x22
  | .or_b  => 0x23
  | .or_c  => 0x24
  | .or_d  => 0x25
  | .or_i  => 0x26

/-- AST constructor corresponding to each `MsBinOp`. -/
def MsBinOp.mkAst : MsBinOp → InternalSpec.WalletPolicy.Miniscript → InternalSpec.WalletPolicy.Miniscript →
    InternalSpec.WalletPolicy.Miniscript
  | .and_v => .and_v
  | .and_b => .and_b
  | .and_n => .and_n
  | .or_b  => .or_b
  | .or_c  => .or_c
  | .or_d  => .or_d
  | .or_i  => .or_i

/-- Exact refinement of `msApplyBinary` across all 7 BIP-379 binary combinators (`and_v`, `and_b`,
    `and_n`, `or_b`, `or_c`, `or_d`, `or_i`) against `WalletPolicy.analyzeMiniscript`. -/
theorem msApplyBinary_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (op : MsBinOp)
    (xNode yNode : InternalSpec.WalletPolicy.Miniscript)
    (x y : InternalSpec.WalletPolicy.MiniscriptExtInfo)
    (hx : BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig xNode = .ok x)
    (hy : BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig yNode = .ok y) :
    msApplyBinary op.opcode (packExtInfo x) (packExtInfo y) =
      match BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (op.mkAst xNode yNode) with
      | .ok out => packExtInfo out
      | .error _ => 0xFFFF := by
  rcases x with ⟨⟨xb, xz, xo, xn, xd, xu⟩, xs, xf, xe, xm, xg, xh, xi, xj, xk, xx, xoc, xos, xod, xss, xsd, xsz⟩
  rcases y with ⟨⟨yb, yz, yo, yn, yd, yu⟩, ys, yf, ye, ym, yg, yh, yi, yj, yk, yx, yoc, yos, yod, yss, ysd, ysz⟩
  change msApplyBinary op.opcode (packExtInfo _) (packExtInfo _) =
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (op.mkAst xNode yNode))
  cases op <;> dsimp only [MsBinOp.opcode, MsBinOp.mkAst] <;> unfold msApplyBinary <;> dsimp only
  case and_v =>
    rw [ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [msConflict_packExtInfo, packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_n] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq] | rw [bnot_eq]
    cases xb <;> cases yb <;> first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc, Bool.or_assoc])
  case and_b =>
    rw [ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [msConflict_packExtInfo, packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_n] | rw [msPack_d] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq] | rw [bnot_eq]
    cases xb <;> cases yb <;> first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc, Bool.or_assoc])
  case and_n =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [msConflict_packExtInfo, packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_d] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq] | rw [bnot_eq]
    cases xb <;> cases yb <;> cases xd <;> cases xu <;>
      first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc, Bool.or_assoc])
  case or_b =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_d] | rw [msPack_s] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq]
    cases xb <;> cases yb <;> cases xd <;> cases yd <;>
      first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc])
  case or_c =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_d] | rw [msPack_u] | rw [msPack_s] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq]
    cases xb <;> cases yb <;> cases xd <;> cases xu <;>
      first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc, Bool.or_assoc])
  case or_d =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_o] | rw [msPack_d] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq]
    cases xb <;> cases yb <;> cases xd <;> cases xu <;>
      first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc, Bool.or_assoc])
  case or_i =>
    rw [ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_neg (by decide), ite_pos (by decide)]
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hx, hy]
    dsimp only [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [packExtInfo_base, packExtInfo_base]
    unfold packExtInfo; dsimp only
    repeat first | rw [msPack_z] | rw [msPack_d] | rw [msPack_u] | rw [msPack_s] | rw [msPack_f] | rw [msPack_e] | rw [msPack_m] | rw [msPack_g] | rw [msPack_h] | rw [msPack_i] | rw [msPack_j] | rw [msPack_k] | rw [selU16_eq] | rw [band_eq] | rw [bor_eq]
    cases xb <;> cases yb <;>
      first | rfl | (apply msPack_congr <;> simp only [encodeBasicType, Bool.and_assoc, Bool.or_assoc])

/-- Exact leaf packing correspondence for `.ms0` and `.ms1` against `WalletPolicy.analyzeMiniscript`. -/
theorem msLeafB_ms0_ms1_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat) :
    (match BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig .ms0 with
     | .ok out => packExtInfo out
     | .error _ => 0xFFFF) = msLeafB true false false true true true false true true ∧
    (match BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig .ms1 with
     | .ok out => packExtInfo out
     | .error _ => 0xFFFF) = msLeafB true false false false true false true false true := by
  constructor <;> (
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript packExtInfo encodeBasicType msLeafB
    rfl)

/-- Exact packing correspondence for `msThreshPack` (when bit 40 is clear) against the `thresh`
    result formula in `WalletPolicy.analyzeMiniscript`. -/
theorem msThreshPack_ok
    (acc : UInt64) (k n : UInt32)
    (hok : ((acc >>> 40) &&& 1) = 0) :
    msThreshPack acc k n =
      msPack 0
        (decide (((acc >>> 0) &&& 0x7F).toUInt32 = n))
        (decide (((acc >>> 0) &&& 0x7F).toUInt32 = n - 1) && decide (((acc >>> 7) &&& 0x7F).toUInt32 = 1))
        false true true
        (decide (((acc >>> 14) &&& 0x7F).toUInt32 ≤ k - 1))
        false
        (decide (((acc >>> 21) &&& 0x7F).toUInt32 = n) && decide (((acc >>> 14) &&& 0x7F).toUInt32 = 0))
        ((decide (((acc >>> 21) &&& 0x7F).toUInt32 = n) && decide (((acc >>> 28) &&& 0x7F).toUInt32 = n)) &&
          decide (((acc >>> 14) &&& 0x7F).toUInt32 ≤ k))
        (decide ((acc >>> 35) &&& 1 = 1))
        (decide ((acc >>> 36) &&& 1 = 1))
        (decide ((acc >>> 37) &&& 1 = 1))
        (decide ((acc >>> 38) &&& 1 = 1))
        (decide ((acc >>> 39) &&& 1 = 0)) := by
  unfold msThreshPack
  have hbad : decide ((acc >>> 40) &&& 1 ≠ 0) = false := decide_eq_false (fun hne => hne hok)
  rw [hbad]
  dsimp only
  repeat rw [band_eq]
  rfl

theorem msThreshPack_err (acc : UInt64) (k n : UInt32) (herr : ((acc >>> 40) &&& 1) ≠ 0) :
    msThreshPack acc k n = 0xFFFF := by
  unfold msThreshPack
  rw [decide_eq_true herr]
  rfl

/-- Exact leaf packing correspondence for `pk_k` (`0x02`), `pk_h` (`0x03`), `pk` (`0x04`),
    and `pkh` (`0x05`) against `WalletPolicy.analyzeMiniscript` once key-expression context checks succeed. -/
theorem msLeaf_keys_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (ke : InternalSpec.WalletPolicy.KeyExpr)
    (hke : BitcoinLedger.WalletPolicy.checkKeyExprInContext fmt (ctx == .tapscriptCtx) maxMusig ke = .ok ()) :
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.pk_k ke)) =
      msPack 2 false true true true true true false true true false false false false true ∧
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.pk_h ke)) =
      msPack 2 false false true true true true false true true false false false false true ∧
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.pk ke)) =
      msPack 0 false true true true true true false true true false false false false true ∧
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.pkh ke)) =
      msPack 0 false false true true true true false true true false false false false true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript
    rw [hke]
    rfl)

/-- Exact leaf packing correspondence for `sha256`/`hash256` (32-byte digest) and
    `ripemd160`/`hash160` (20-byte digest) against `WalletPolicy.analyzeMiniscript`. -/
theorem msLeaf_hashes_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (h32 h20 : ByteArray)
    (hh32 : h32.size = 32) (hh20 : h20.size = 20) :
    let leafHash := msLeafB false true true true true false false false true
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.sha256 h32)) = leafHash ∧
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.hash256 h32)) = leafHash ∧
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.ripemd160 h20)) = leafHash ∧
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.hash160 h20)) = leafHash := by
  dsimp only
  have hb32 : (h32.size != 32) = false := by rw [hh32]; rfl
  have hb20 : (h20.size != 20) = false := by rw [hh20]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hb32]; rfl
  · unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hb32]; rfl
  · unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hb20]; rfl
  · unfold BitcoinLedger.WalletPolicy.analyzeMiniscript; rw [hb20]; rfl

/-- Exact leaf packing correspondence for `.older val` (`0x06`) against `WalletPolicy.analyzeMiniscript`. -/
theorem msLeaf_older_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (val : UInt32) :
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.older val)) =
      if llbMiniscriptOlderOk val then
        let tBool := decide ((val &&& 0x00400000) ≠ 0)
        msPack 0 true false false false false false true false true tBool (!tBool) false false true
      else 0xFFFF := by
  unfold BitcoinLedger.WalletPolicy.analyzeMiniscript
  rw [(llbMiniscriptOlderOk_eq_validOlderArg val).1]
  cases h : BitcoinLedger.WalletPolicy.validOlderArg val
  · rfl
  · have hflag : BitcoinLedger.WalletPolicy.sequenceLocktimeTypeFlag = (0x00400000 : UInt32) := rfl
    have ht : ((val &&& BitcoinLedger.WalletPolicy.sequenceLocktimeTypeFlag) != 0) =
        decide ((val &&& 0x00400000) ≠ 0) := by
      rw [hflag]
      simp only [bne, BEq.beq]
      cases h0 : decide (val &&& 0x00400000 = 0)
      · have hne : val &&& 0x00400000 ≠ 0 := of_decide_eq_false h0
        rw [decide_eq_true hne]; rfl
      · have heq : val &&& 0x00400000 = 0 := of_decide_eq_true h0
        rw [decide_eq_false (fun hne => hne heq)]; rfl
    rw [ht]
    rfl

/-- Exact leaf packing correspondence for `.after val` (`0x07`) against `WalletPolicy.analyzeMiniscript`. -/
theorem msLeaf_after_refines
    (fmt : InternalSpec.WalletPolicy.PolicyFormat)
    (ctx : InternalSpec.WalletPolicy.MiniscriptCtx)
    (maxMulti maxMultiA maxMusig : Nat)
    (val : UInt32) :
    packExtResult (BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMulti maxMultiA maxMusig (.after val)) =
      if llbMiniscriptAfterOk val then
        let tBool := decide (500000000 ≤ val)
        msPack 0 true false false false false false true false true false false tBool (!tBool) true
      else 0xFFFF := by
  unfold BitcoinLedger.WalletPolicy.analyzeMiniscript
  rw [(llbMiniscriptAfterOk_eq_validAfterArg val).1]
  cases h : BitcoinLedger.WalletPolicy.validAfterArg val
  · rfl
  · rfl

/-- Exact root sanity check correspondence: the final `llbMiniscriptCheckPostfix` root check on
    `top = packExtInfo info` matches the type, timelock-mix, malleability, and signature checks
    in `WalletPolicy.checkMiniscriptSane`. -/
theorem msRootCheck_packExtInfo
    (info : InternalSpec.WalletPolicy.MiniscriptExtInfo)
    (requireFlags : UInt8) :
    let top := packExtInfo info
    let reqM := bor (decide ((requireFlags &&& 1) = 0)) (msBit top MSB_M)
    let reqS := bor (decide ((requireFlags &&& 2) = 0)) (msBit top MSB_S)
    band (band (decide ((top &&& 3) = 0)) (msBit top MSB_K)) (band reqM reqS) =
      ((info.ty.base == .B) && info.k &&
        (decide ((requireFlags &&& 1) = 0) || info.m) &&
        (decide ((requireFlags &&& 2) = 0) || info.s)) := by
  dsimp only
  rw [packExtInfo_base]
  unfold packExtInfo
  rw [msPack_k, msPack_m, msPack_s, bor_eq, bor_eq, band_eq, band_eq, band_eq]
  cases info.ty.base <;> cases info.k <;> cases info.m <;> cases info.s <;>
    cases decide (requireFlags &&& 1 = 0) <;> cases decide (requireFlags &&& 2 = 0) <;> rfl

/-! ## 10. Buffer-Manipulating Entrypoints, Unrolled Loops, and Prefix Decoders -/

private theorem forRangeU64_go_eq_foldl
    (step : UInt32 → UInt64 → UInt64) (fuel : Nat) (cur : UInt32) (acc : UInt64) :
    forRangeU64.go step fuel cur acc =
      (List.range fuel).foldl (fun a k => step (cur + UInt32.ofNat k) a) acc := by
  induction fuel generalizing cur acc with
  | zero => rfl
  | succ fuel' ih =>
    unfold forRangeU64.go
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have h0 : cur + UInt32.ofNat 0 = cur := UInt32.add_zero cur
    rw [h0, ih (cur + 1) (step cur acc)]
    have hfun :
        (fun a k => step (cur + 1 + UInt32.ofNat k) a) =
          (fun a k => step (cur + UInt32.ofNat (k + 1)) a) := by
      funext a k
      have hk : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        rw [UInt32.ofNat_add, UInt32.add_comm]
        rfl
      rw [UInt32.add_assoc, hk]
    rw [hfun]

theorem forRangeU64_eq_foldl (lo hi : UInt32) (init : UInt64) (step : UInt32 → UInt64 → UInt64) :
    forRangeU64 lo hi init step =
      if decide (lo < hi) then
        (List.range (hi - lo).toNat).foldl (fun acc k => step (lo + UInt32.ofNat k) acc) init
      else init := by
  unfold forRangeU64
  cases h : decide (lo < hi)
  · rfl
  · simp only [↓reduceIte]
    exact forRangeU64_go_eq_foldl step (hi - lo).toNat lo init

theorem forRangeU64_zero_eq_foldl (len : UInt32) (init : UInt64) (step : UInt32 → UInt64 → UInt64) :
    forRangeU64 0 len init step =
      (List.range len.toNat).foldl (fun acc k => step (UInt32.ofNat k) acc) init := by
  rw [forRangeU64_eq_foldl]
  cases h : decide ((0 : UInt32) < len)
  · have hle : len.toNat ≤ 0 := Nat.not_lt.mp (of_decide_eq_false h)
    have hz : len.toNat = 0 := Nat.eq_zero_of_le_zero hle
    rw [hz]
    rfl
  · simp only [↓reduceIte]
    have hsub : (len - 0).toNat = len.toNat := by rw [UInt32.sub_zero]
    rw [hsub]
    have hfun :
        (fun acc k => step ((0 : UInt32) + UInt32.ofNat k) acc) =
          (fun acc k => step (UInt32.ofNat k) acc) := by
      funext acc k
      rw [UInt32.zero_add]
    rw [hfun]

private theorem foldl_guard_one_eq_zero (p : α → Bool) (xs : List α) :
    xs.foldl (fun (acc : UInt64) x => if p x then acc else 0) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases p x <;> exact ih

private theorem foldl_guard_one_eq_all (p : α → Bool) (xs : List α) :
    decide (xs.foldl (fun (acc : UInt64) x => if p x then acc else 0) 1 = 1) = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, List.all_cons]
    cases hx : p x
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
      rw [foldl_guard_one_eq_zero]
      rfl
    · simp only [↓reduceIte, Bool.true_and]
      exact ih

theorem forRangeU64_guard_iff (lo hi : UInt32) (p : UInt32 → Bool) :
    decide (forRangeU64 lo hi 1 (fun i acc => if p i then acc else 0) = 1) = true ↔
      ∀ (i : UInt32), lo ≤ i → i < hi → p i = true := by
  rw [forRangeU64_eq_foldl]
  cases hlt : decide (lo < hi)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnlt : ¬ (lo < hi) := of_decide_eq_false hlt
    constructor
    · intro _ i hlo hhi
      have h1 : lo.toNat ≤ i.toNat := UInt32.le_iff_toNat_le.mp hlo
      have h2 : i.toNat < hi.toNat := UInt32.lt_iff_toNat_lt.mp hhi
      exact absurd (UInt32.lt_iff_toNat_lt.mpr (Nat.lt_of_le_of_lt h1 h2)) hnlt
    · intro _; rfl
  · simp only [↓reduceIte]
    rw [foldl_guard_one_eq_all]
    have hlt_u : lo < hi := of_decide_eq_true hlt
    have hlt' : lo.toNat < hi.toNat := UInt32.lt_iff_toNat_lt.mp hlt_u
    have hle_u : lo ≤ hi := UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt hlt')
    have hsub : (hi - lo).toNat = hi.toNat - lo.toNat := UInt32.toNat_sub_of_le hi lo hle_u
    rw [List.all_eq_true]
    constructor
    · intro hall i hlo hhi
      have hlo' : lo.toNat ≤ i.toNat := UInt32.le_iff_toNat_le.mp hlo
      have hhi' : i.toNat < hi.toNat := UInt32.lt_iff_toNat_lt.mp hhi
      let k := i.toNat - lo.toNat
      have hk_lt_diff : k < hi.toNat - lo.toNat := by
        have hadd : lo.toNat + k < lo.toNat + (hi.toNat - lo.toNat) := by
          rw [Nat.add_sub_of_le hlo', Nat.add_sub_of_le (Nat.le_of_lt hlt')]
          exact hhi'
        exact Nat.lt_of_add_lt_add_left hadd
      have hk : k ∈ List.range (hi - lo).toNat := by
        rw [List.mem_range, hsub]; exact hk_lt_diff
      have heqi : lo + UInt32.ofNat k = i := by
        apply UInt32.toNat_inj.mp
        rw [UInt32.toNat_add, UInt32.toNat_ofNat']
        have hk_lt : k < UInt32.size := Nat.lt_of_le_of_lt (Nat.sub_le i.toNat lo.toNat) i.toNat_lt
        rw [Nat.mod_eq_of_lt hk_lt, Nat.add_sub_of_le hlo', Nat.mod_eq_of_lt i.toNat_lt]
      rw [← heqi]
      exact hall k hk
    · intro hall k hk
      rw [List.mem_range, hsub] at hk
      have hsum_lt : lo.toNat + k < hi.toNat := by
        have := Nat.add_lt_add_left hk lo.toNat
        rwa [Nat.add_sub_of_le (Nat.le_of_lt hlt')] at this
      have hk_lt : k < UInt32.size := Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_add_left k lo.toNat) hsum_lt) hi.toNat_lt
      have hsum_u32 : (lo + UInt32.ofNat k).toNat = lo.toNat + k := by
        rw [UInt32.toNat_add, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hk_lt,
            Nat.mod_eq_of_lt (Nat.lt_trans hsum_lt hi.toNat_lt)]
      apply hall (lo + UInt32.ofNat k)
      · rw [UInt32.le_iff_toNat_le, hsum_u32]; exact Nat.le_add_right lo.toNat k
      · rw [UInt32.lt_iff_toNat_lt, hsum_u32]; exact hsum_lt

/-! ## 2. `llbBytesEq` & `llbCheckDualUtxo` (VND-02, CVE-2020-14199) -/

theorem llbBytesEq_iff (a b : ConstBytes) (len : UInt32) :
    llbBytesEq a b len = true ↔ ∀ (i : UInt32), i < len → readU8 a i = readU8 b i := by
  unfold llbBytesEq
  rw [forRangeU64_guard_iff 0 len (fun i => decide (readU8 a i = readU8 b i))]
  constructor
  · intro h i hlt
    have h0le : (0 : UInt32) ≤ i := UInt32.le_iff_toNat_le.mpr (Nat.zero_le i.toNat)
    exact of_decide_eq_true (h i h0le hlt)
  · intro h i _ hlt
    exact decide_eq_true (h i hlt)

private theorem eqByteList_iff_getElem (xs ys : List UInt8) :
    BitcoinLedger.Psbt.eqByteList xs ys = true ↔
      xs.length = ys.length ∧ ∀ (k : Nat) (hkx : k < xs.length) (hky : k < ys.length), xs[k]'hkx = ys[k]'hky := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      constructor
      · intro _; exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      · intro _; rfl
    | cons y ys =>
      constructor
      · intro h; exact Bool.noConfusion h
      · rintro ⟨hlen, _⟩; exact Nat.noConfusion hlen
  | cons x xs ih =>
    cases ys with
    | nil =>
      constructor
      · intro h; exact Bool.noConfusion h
      · rintro ⟨hlen, _⟩; exact Nat.noConfusion hlen
    | cons y ys =>
      unfold BitcoinLedger.Psbt.eqByteList
      rw [Bool.and_eq_true, decide_eq_true_eq, ih ys]
      constructor
      · rintro ⟨hxy, hlen, hall⟩
        refine ⟨congrArg Nat.succ hlen, ?_⟩
        intro k hkx hky
        cases k with
        | zero => exact hxy
        | succ k' => exact hall k' (Nat.lt_of_succ_lt_succ hkx) (Nat.lt_of_succ_lt_succ hky)
      · rintro ⟨hlen, hall⟩
        refine ⟨hall 0 (Nat.succ_pos _) (Nat.succ_pos _), Nat.succ.inj hlen, ?_⟩
        intro k hkx hky
        exact hall (k + 1) (Nat.succ_lt_succ hkx) (Nat.succ_lt_succ hky)

private theorem eqBytes_iff_getElem (a b : ByteArray) :
    BitcoinLedger.Psbt.eqBytes a b = true ↔
      a.size = b.size ∧ ∀ (k : Nat) (hka : k < a.size) (hkb : k < b.size), a[k]'hka = b[k]'hkb := by
  unfold BitcoinLedger.Psbt.eqBytes
  rw [eqByteList_iff_getElem]
  have ha : a.data.toList.length = a.size := Array.length_toList
  have hb : b.data.toList.length = b.size := Array.length_toList
  constructor
  · rintro ⟨hlen, hall⟩
    have hsz : a.size = b.size := by rw [← ha, ← hb]; exact hlen
    refine ⟨hsz, fun k hka hkb => ?_⟩
    have h1 : (a.data.toList)[k]'(by rw [ha]; exact hka) = a[k]'hka := Array.getElem_toList hka
    have h2 : (b.data.toList)[k]'(by rw [hb]; exact hkb) = b[k]'hkb := Array.getElem_toList hkb
    rw [← h1, ← h2]
    exact hall k (by rw [ha]; exact hka) (by rw [hb]; exact hkb)
  · rintro ⟨hsz, hall⟩
    refine ⟨by rw [ha, hb]; exact hsz, fun k hka hkb => ?_⟩
    have hka' : k < a.size := by rwa [← ha]
    have hkb' : k < b.size := by rwa [← hb]
    have h1 : (a.data.toList)[k]'hka = a[k]'hka' := Array.getElem_toList hka'
    have h2 : (b.data.toList)[k]'hkb = b[k]'hkb' := Array.getElem_toList hkb'
    rw [h1, h2]
    exact hall k hka' hkb'

/-- Exact refinement of `llbCheckDualUtxo` against `llbValidAmount` + `BitcoinLedger.Psbt.eqTxOut`
    for `wOut = ⟨witAmount.toNat, wSpk⟩` and `nwOut = ⟨nonWitAmount.toNat, nwSpk⟩` (CVE-2020-14199). -/
theorem llbCheckDualUtxo_refines
    (witAmount nonWitAmount : UInt64)
    (wSpk nwSpk : ByteArray)
    (witSpk nonWitSpk : ConstBytes)
    (witSpkLen nonWitSpkLen : UInt32)
    (hwLen : witSpkLen.toNat = wSpk.size)
    (hnwLen : nonWitSpkLen.toNat = nwSpk.size)
    (hwBuf : ∀ (k : Nat) (hk : k < wSpk.size), readU8 witSpk (UInt32.ofNat k) = wSpk[k]'hk)
    (hnwBuf : ∀ (k : Nat) (hk : k < nwSpk.size), readU8 nonWitSpk (UInt32.ofNat k) = nwSpk[k]'hk) :
    llbCheckDualUtxo witAmount witSpk witSpkLen nonWitAmount nonWitSpk nonWitSpkLen =
      (llbValidAmount witAmount &&
        BitcoinLedger.Psbt.eqTxOut ⟨nonWitAmount.toNat, nwSpk⟩ ⟨witAmount.toNat, wSpk⟩) := by
  unfold llbCheckDualUtxo BitcoinLedger.Psbt.eqTxOut
  dsimp only
  cases hv : llbValidAmount witAmount
  · rfl
  · simp only [Bool.true_and]
    have hamt : decide (witAmount = nonWitAmount) = decide (nonWitAmount.toNat = witAmount.toNat) := by
      cases h : decide (witAmount = nonWitAmount)
      · exact (decide_eq_false (fun heq => of_decide_eq_false h (UInt64.toNat_inj.mp heq.symm))).symm
      · exact (decide_eq_true (congrArg UInt64.toNat (of_decide_eq_true h).symm)).symm
    rw [hamt]
    cases ha : decide (nonWitAmount.toNat = witAmount.toNat)
    · rfl
    · simp only [Bool.true_and]
      cases hlen : decide (witSpkLen = nonWitSpkLen)
      · simp only [Bool.false_and]
        cases heqb : BitcoinLedger.Psbt.eqBytes nwSpk wSpk
        · rfl
        · exfalso
          have ⟨hsz, _⟩ := (eqBytes_iff_getElem nwSpk wSpk).mp heqb
          have hlen_eq : witSpkLen = nonWitSpkLen := UInt32.toNat_inj.mp (by rw [hwLen, hnwLen, hsz])
          exact of_decide_eq_false hlen hlen_eq
      · simp only [Bool.true_and]
        have hlen_eq : witSpkLen = nonWitSpkLen := of_decide_eq_true hlen
        have hsz_eq : nwSpk.size = wSpk.size := by rw [← hnwLen, ← hwLen, hlen_eq]
        cases heqb : BitcoinLedger.Psbt.eqBytes nwSpk wSpk
        · apply Bool.eq_false_iff.mpr
          intro hbytes
          have hall := (llbBytesEq_iff witSpk nonWitSpk witSpkLen).mp hbytes
          have heqb' : BitcoinLedger.Psbt.eqBytes nwSpk wSpk = true := by
            apply (eqBytes_iff_getElem _ _).mpr
            refine ⟨hsz_eq, fun k hknw hkw => ?_⟩
            have hk_lt : k < witSpkLen.toNat := by rwa [hwLen]
            have hi_lt : UInt32.ofNat k < witSpkLen := by
              rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat',
                  Nat.mod_eq_of_lt (Nat.lt_trans hk_lt witSpkLen.toNat_lt)]
              exact hk_lt
            have hread := hall (UInt32.ofNat k) hi_lt
            rw [hwBuf k hkw, hnwBuf k hknw] at hread
            exact hread.symm
          exact Bool.noConfusion (heqb.symm.trans heqb')
        · apply (llbBytesEq_iff witSpk nonWitSpk witSpkLen).mpr
          have ⟨_, hall⟩ := (eqBytes_iff_getElem _ _).mp heqb
          intro i hi
          have hi_nat : i.toNat < witSpkLen.toNat := UInt32.lt_iff_toNat_lt.mp hi
          have hkw : i.toNat < wSpk.size := by rwa [← hwLen]
          have hknw : i.toNat < nwSpk.size := by rwa [hsz_eq]
          have hof : UInt32.ofNat i.toNat = i := UInt32.ofNat_toNat
          have hw := hwBuf i.toNat hkw
          have hnw := hnwBuf i.toNat hknw
          rw [hof] at hw hnw
          rw [hw, hnw]
          exact (hall i.toNat hknw hkw).symm

/-! ## 4. `bip32TailClear` & `llbBip32CheckExportPath` (VND-07) -/

theorem bip32TailClear_iff (path : ConstU32s) (lo pathLen : UInt32) :
    bip32TailClear path lo pathLen = true ↔
      ∀ (i : UInt32), lo ≤ i → i < pathLen → llbBip32IsHardened (readU32 path i) = false := by
  unfold bip32TailClear
  have hfun :
      (fun i (acc : UInt64) => if llbBip32IsHardened (readU32 path i) then 0 else acc) =
        (fun i (acc : UInt64) => if !llbBip32IsHardened (readU32 path i) then acc else 0) := by
    funext i acc
    cases llbBip32IsHardened (readU32 path i) <;> rfl
  rw [hfun, forRangeU64_guard_iff]
  constructor
  · intro hall i hlo hhi
    cases hb : llbBip32IsHardened (readU32 path i)
    · rfl
    · have := hall i hlo hhi
      rw [hb] at this
      exact Bool.noConfusion this
  · intro hall i hlo hhi
    rw [hall i hlo hhi]
    rfl

private theorem allUnhardened_iff_getElem (xs : List UInt32) :
    BitcoinLedger.Bip32.allUnhardened xs = true ↔
      ∀ (k : Nat) (hk : k < xs.length), BitcoinLedger.Bip32.isHardened (xs[k]'hk) = false := by
  unfold BitcoinLedger.Bip32.allUnhardened
  rw [List.all_eq_true]
  constructor
  · intro hall k hk
    have hmem : xs[k]'hk ∈ xs := List.getElem_mem hk
    have hb := hall (xs[k]'hk) hmem
    cases hh : BitcoinLedger.Bip32.isHardened (xs[k]'hk)
    · rfl
    · rw [hh] at hb; exact Bool.noConfusion hb
  · intro hall x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    rw [hall k hk]
    rfl

/-- Exact full-buffer BIP-32 pubkey-export refinement (VND-07): `llbBip32CheckExportPath` equals
    the BOLOS 10-step depth gate conjoined with `BitcoinLedger.Bip32.isBolosSafePubkeyExportPath`
    (assuming the caller's `pathLen : UInt8` equals `arr.size`). -/
theorem llbBip32CheckExportPath_refines
    (net : InternalSpec.Network)
    (arr : InternalSpec.Bip32Path)
    (path : ConstU32s)
    (pathLen : UInt8)
    (hlen : pathLen.toNat = arr.size)
    (hbuf : ∀ (k : Nat) (hk : k < arr.size), readU32 path (UInt32.ofNat k) = arr[k]'hk) :
    llbBip32CheckExportPath path pathLen (BitcoinLedger.Basic.networkParams net).bip44CoinType =
      (decide (arr.size ≤ 10) && BitcoinLedger.Bip32.isBolosSafePubkeyExportPath net arr) := by
  unfold llbBip32CheckExportPath
  have hdepth : llbBip32BolosDepthOk pathLen = decide (arr.size ≤ 10) := by
    unfold llbBip32BolosDepthOk
    have : decide (pathLen ≤ 10) = decide (pathLen.toNat ≤ 10) := rfl
    rw [this, hlen]
  rw [hdepth]
  cases hd : decide (arr.size ≤ 10)
  · simp
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
    have hbyte : arr.size ≤ 255 := Nat.le_trans (of_decide_eq_true hd) (by decide)
    have hlen_u8 : UInt8.ofNat arr.size = pathLen := by
      rw [← hlen]; exact UInt8.ofNat_toNat
    have hn_nat : pathLen.toUInt32.toNat = arr.size := by
      rw [UInt8.toNat_toUInt32, hlen]
    have hread_idx : ∀ (j : Nat), j < 4 →
        (if decide (UInt32.ofNat j < pathLen.toUInt32) then readU32 path (UInt32.ofNat j) else 0) =
          arr[j]?.getD 0 := by
      intro j hj4
      have hj_u32 : (UInt32.ofNat j).toNat = j := by
        rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hj4 (by decide))]
      cases hlt : decide (UInt32.ofNat j < pathLen.toUInt32)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hge : arr.size ≤ j := by
          have := Nat.not_lt.mp (fun h => of_decide_eq_false hlt (by
            rw [UInt32.lt_iff_toNat_lt, hj_u32, hn_nat]; exact h))
          exact this
        rw [Array.getElem?_eq_none hge]; rfl
      · simp only [↓reduceIte]
        have hj_lt : j < arr.size := by
          have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hlt)
          rwa [hj_u32, hn_nat] at this
        rw [hbuf j hj_lt, Array.getElem?_eq_getElem hj_lt]; rfl
    have hp0 := hread_idx 0 (by decide)
    have hp1 := hread_idx 1 (by decide)
    have hp2 := hread_idx 2 (by decide)
    have hp3 := hread_idx 3 (by decide)
    change llbBip32PubkeyExportPrefixOk
      (if decide (UInt32.ofNat 0 < pathLen.toUInt32) then readU32 path (UInt32.ofNat 0) else 0)
      (if decide (UInt32.ofNat 1 < pathLen.toUInt32) then readU32 path (UInt32.ofNat 1) else 0)
      (if decide (UInt32.ofNat 2 < pathLen.toUInt32) then readU32 path (UInt32.ofNat 2) else 0)
      (if decide (UInt32.ofNat 3 < pathLen.toUInt32) then readU32 path (UInt32.ofNat 3) else 0)
      pathLen (BitcoinLedger.Basic.networkParams net).bip44CoinType
      (bip32TailClear path
        (if decide (llbBip32Unharden (if decide (UInt32.ofNat 0 < pathLen.toUInt32) then readU32 path (UInt32.ofNat 0) else 0) = 48) &&
            decide ((3 : UInt32) ≤ pathLen.toUInt32) then 4 else 3)
        pathLen.toUInt32) = _
    rw [hp0, hp1, hp2, hp3]
    let p0 := arr[0]?.getD 0
    let tailStart : Nat := if decide (BitcoinLedger.Bip32.unharden p0 = 48) then 4 else 3
    let tailAt : UInt32 :=
      if decide (llbBip32Unharden p0 = 48) && decide ((3 : UInt32) ≤ pathLen.toUInt32) then 4 else 3
    have htail : bip32TailClear path tailAt pathLen.toUInt32 =
        BitcoinLedger.Bip32.allUnhardened (arr.toList.drop tailStart) := by
      have hunh : llbBip32Unharden p0 = BitcoinLedger.Bip32.unharden p0 := rfl
      cases hge3 : decide ((3 : UInt32) ≤ pathLen.toUInt32)
      · have hlt3 : arr.size < 3 := by
          apply Nat.lt_of_not_le
          intro h3
          exact of_decide_eq_false hge3 (by rw [UInt32.le_iff_toNat_le, hn_nat]; exact h3)
        have hta3 : tailAt = 3 := by simp [tailAt, hge3]
        have hdrop_nil : arr.toList.drop tailStart = [] := by
          apply List.drop_eq_nil_of_le
          rw [Array.length_toList]
          have hts : 3 ≤ tailStart := by
            unfold tailStart
            cases decide (BitcoinLedger.Bip32.unharden p0 = 48) <;> decide
          exact Nat.le_trans (Nat.le_of_lt hlt3) hts
        rw [hta3, hdrop_nil]
        have hclear : bip32TailClear path 3 pathLen.toUInt32 = true := by
          rw [bip32TailClear_iff]
          intro i hlo hhi
          have h1 : 3 ≤ i.toNat := UInt32.le_iff_toNat_le.mp hlo
          have h2 : i.toNat < arr.size := by have := UInt32.lt_iff_toNat_lt.mp hhi; rwa [hn_nat] at this
          exact absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.not_lt.mpr (Nat.le_of_lt hlt3))
        rw [hclear]; rfl
      · have hta_nat : tailAt.toNat = tailStart := by
          simp only [tailAt, tailStart, hunh, hge3, Bool.and_true]
          cases decide (BitcoinLedger.Bip32.unharden p0 = 48) <;> rfl
        cases hall : BitcoinLedger.Bip32.allUnhardened (arr.toList.drop tailStart)
        · apply Bool.eq_false_iff.mpr
          intro htc
          have htc' := (bip32TailClear_iff path tailAt pathLen.toUInt32).mp htc
          have hall' : BitcoinLedger.Bip32.allUnhardened (arr.toList.drop tailStart) = true := by
            rw [allUnhardened_iff_getElem]
            intro k hk
            rw [List.length_drop, Array.length_toList] at hk
            have hidx_lt : tailStart + k < arr.size := by
              have hts_le : tailStart ≤ arr.size :=
                Nat.le_of_lt (Nat.lt_of_not_le (fun hle => by
                  rw [Nat.sub_eq_zero_of_le hle] at hk
                  exact Nat.not_lt_zero k hk))
              have := Nat.add_lt_add_left hk tailStart
              rwa [Nat.add_sub_of_le hts_le] at this
            let idx := UInt32.ofNat (tailStart + k)
            have hidx_nat : idx.toNat = tailStart + k := by
              rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hidx_lt (Nat.le_trans hbyte (by decide)))]
            have hlo : tailAt ≤ idx := by
              rw [UInt32.le_iff_toNat_le, hta_nat, hidx_nat]; exact Nat.le_add_right _ _
            have hhi : idx < pathLen.toUInt32 := by
              rw [UInt32.lt_iff_toNat_lt, hidx_nat, hn_nat]; exact hidx_lt
            have hh := htc' idx hlo hhi
            have hread := hbuf (tailStart + k) hidx_lt
            rw [hread] at hh
            have hget : (arr.toList.drop tailStart)[k]'(by rw [List.length_drop, Array.length_toList]; exact hk) =
                arr[tailStart + k]'hidx_lt := by
              rw [List.getElem_drop, Array.getElem_toList]
            rw [hget]
            exact hh
          exact Bool.noConfusion (hall.symm.trans hall')
        · apply (bip32TailClear_iff path tailAt pathLen.toUInt32).mpr
          have hall' := (allUnhardened_iff_getElem _).mp hall
          intro i hlo hhi
          have hi_ge : tailStart ≤ i.toNat := by
            rw [← hta_nat]; exact UInt32.le_iff_toNat_le.mp hlo
          have hi_lt : i.toNat < arr.size := by
            have := UInt32.lt_iff_toNat_lt.mp hhi; rwa [hn_nat] at this
          let k := i.toNat - tailStart
          have hk_lt : k < (arr.toList.drop tailStart).length := by
            rw [List.length_drop, Array.length_toList]
            have hadd : tailStart + k < tailStart + (arr.size - tailStart) := by
              rw [Nat.add_sub_of_le hi_ge, Nat.add_sub_of_le (Nat.le_trans hi_ge (Nat.le_of_lt hi_lt))]
              exact hi_lt
            exact Nat.lt_of_add_lt_add_left hadd
          have hget : (arr.toList.drop tailStart)[k]'hk_lt = arr[i.toNat]'hi_lt := by
            rw [List.getElem_drop]
            have hadd : tailStart + k = i.toNat := Nat.add_sub_of_le hi_ge
            simp only [hadd]
            exact Array.getElem_toList hi_lt
          have hh := hall' k hk_lt
          rw [hget] at hh
          have hread := hbuf i.toNat hi_lt
          rw [UInt32.ofNat_toNat] at hread
          rw [hread]
          exact hh
    rw [htail, ← hlen_u8]
    exact llbBip32PubkeyExportPrefixOk_refines net arr hbyte

/-! ## 6. `llbReadCompactSizeChecked` Canonical VarInt Prefix Refinement (VND-09) -/

private theorem u8_shift_lt (b : UInt8) (s : UInt64) (k : Nat)
    (hs : s.toNat < 64) (hbound : 255 * 2 ^ s.toNat < 2 ^ k) (hk64 : 2 ^ k ≤ 2 ^ 64) :
    (b.toUInt64 <<< s).toNat < 2 ^ k := by
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.mod_eq_of_lt hs, Nat.shiftLeft_eq]
  have hmul : b.toNat * 2 ^ s.toNat < 2 ^ k :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ s.toNat) (Nat.le_sub_one_of_lt b.toNat_lt)) hbound
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hmul hk64)]
  exact hmul

private theorem u16_le_ffff (b1 b2 : UInt8) :
    (b1.toUInt64 ||| (b2.toUInt64 <<< 8)) ≤ (0xFFFF : UInt64) := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_or]
  have h1 : b1.toUInt64.toNat < 2 ^ 16 := by
    rw [UInt8.toNat_toUInt64]; exact Nat.lt_trans b1.toNat_lt (by decide)
  have h2 : (b2.toUInt64 <<< 8).toNat < 2 ^ 16 :=
    u8_shift_lt b2 8 16 (by decide) (by decide) (by decide)
  exact Nat.le_sub_one_of_lt (Nat.or_lt_two_pow h1 h2)

private theorem u32_le_ffffffff (b1 b2 b3 b4 : UInt8) :
    (b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24)) ≤
      (0xFFFFFFFF : UInt64) := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or]
  have h1 : b1.toUInt64.toNat < 2 ^ 32 := by
    rw [UInt8.toNat_toUInt64]; exact Nat.lt_trans b1.toNat_lt (by decide)
  have h2 : (b2.toUInt64 <<< 8).toNat < 2 ^ 32 :=
    u8_shift_lt b2 8 32 (by decide) (by decide) (by decide)
  have h3 : (b3.toUInt64 <<< 16).toNat < 2 ^ 32 :=
    u8_shift_lt b3 16 32 (by decide) (by decide) (by decide)
  have h4 : (b4.toUInt64 <<< 24).toNat < 2 ^ 32 :=
    u8_shift_lt b4 24 32 (by decide) (by decide) (by decide)
  exact Nat.le_sub_one_of_lt (Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h1 h2) h3) h4)

/-- Required byte length of a CompactSize header starting with `tag`. -/
def varIntTagNeed (tag : UInt8) : Nat :=
  if decide (tag ≤ 0xFC) then 1
  else if decide (tag = 0xFD) then 3
  else if decide (tag = 0xFE) then 5
  else 9

/-- Pure specification of `llbReadCompactSizeChecked` in terms of `BitcoinLedger.Basic.decodeVarIntCanonical?`
    applied to the `varIntTagNeed`-byte prefix of `bs`. -/
def specReadCompactSizeChecked (bs : ByteArray) (maxVal : UInt32) : UInt64 :=
  match bs.data.toList with
  | [] => 0
  | tag :: _ =>
    let need := varIntTagNeed tag
    if decide (bs.size < need) then 0
    else
      let head := ByteArray.mk (bs.data.toList.take need).toArray
      match BitcoinLedger.Basic.decodeVarIntCanonical? head with
      | some v =>
        if decide (v ≤ maxVal.toUInt64) then
          ((UInt64.ofNat need) <<< 32) ||| v
        else 0
      | none => 0

/-- Exact refinement of `llbReadCompactSizeChecked` against `BitcoinLedger.Basic.decodeVarIntCanonical?`
    across all buffer lengths (`0`, truncated `1..8`, and full `1`/`3`/`5`/`9`-byte headers),
    all tag bytes (`0x00..0xFF`), all non-minimal encodings, and all `maxVal : UInt32` bounds (VND-09). -/
theorem llbReadCompactSizeChecked_refines
    (bs : ByteArray) (buf : ConstBytes) (bufLen maxVal : UInt32)
    (hlen : bufLen.toNat = bs.size)
    (hbuf : ∀ (k : Nat) (hk : k < bs.size), readU8 buf (UInt32.ofNat k) = bs[k]'hk) :
    llbReadCompactSizeChecked buf bufLen maxVal = specReadCompactSizeChecked bs maxVal := by
  unfold llbReadCompactSizeChecked specReadCompactSizeChecked
  have hsz_list : bs.data.toList.length = bs.size := Array.length_toList
  have hread_list : ∀ (k : Nat) (hk : k < bs.data.toList.length),
      readU8 buf (UInt32.ofNat k) = (bs.data.toList)[k]'hk := by
    intro k hk
    have hk_sz : k < bs.size := by rwa [← hsz_list]
    rw [hbuf k hk_sz]
    exact (Array.getElem_toList hk_sz).symm
  cases hlist : bs.data.toList with
  | nil =>
    have hsz0 : bs.size = 0 := by rw [← hsz_list, hlist]; rfl
    have hbl0 : bufLen = 0 := UInt32.toNat_inj.mp (by rw [hlen, hsz0]; rfl)
    rw [hbl0]; rfl
  | cons tag rest0 =>
    have hsz_pos : 0 < bs.size := by rw [← hsz_list, hlist]; exact Nat.succ_pos _
    have hbl_ne0 : decide (bufLen = 0) = false := by
      apply decide_eq_false
      intro heq
      have : bufLen.toNat = 0 := congrArg UInt32.toNat heq
      rw [hlen] at this
      exact Nat.ne_of_gt hsz_pos this
    have htag0 : readU8 buf 0 = tag := by
      have h0 := hread_list 0 (by rw [hlist]; exact Nat.succ_pos _)
      simp only [hlist] at h0
      exact h0
    simp only [hbl_ne0, Bool.false_eq_true, ↓reduceIte]
    rw [htag0]
    unfold varIntTagNeed
    cases hfc : decide (tag ≤ 0xFC)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hfd : decide (tag = 0xFD)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hfe : decide (tag = 0xFE)
        · -- tag = 0xFF
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hff : decide (tag = 0xFF) = true := by
            apply decide_eq_true
            apply UInt8.toNat_inj.mp
            have hle255 : tag.toNat ≤ 255 := Nat.le_sub_one_of_lt tag.toNat_lt
            have hge253 : 253 ≤ tag.toNat :=
              Nat.lt_of_not_le (fun h => of_decide_eq_false hfc (UInt8.le_iff_toNat_le.mpr h))
            have hne253 : 253 ≠ tag.toNat :=
              fun h => of_decide_eq_false hfd (UInt8.toNat_inj.mp h.symm)
            have hge254 : 254 ≤ tag.toNat := Nat.lt_of_le_of_ne hge253 hne253
            have hne254 : 254 ≠ tag.toNat :=
              fun h => of_decide_eq_false hfe (UInt8.toNat_inj.mp h.symm)
            have hge255 : 255 ≤ tag.toNat := Nat.lt_of_le_of_ne hge254 hne254
            exact Nat.le_antisymm hle255 hge255
          simp only [hff, Bool.or_true, ↓reduceIte]
          cases hlt9 : decide (bs.size < 9)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            unfold BitcoinLedger.Basic.decodeVarIntCanonical?
            rw [List.toList_toArray]
            cases htake : List.take 9 (tag :: rest0) with
            | nil => rfl
            | cons x0 xs0 =>
              cases xs0 with
              | nil =>
                have hx0 : x0 = tag := by
                  have := congrArg List.head? htake
                  simp only [List.take, List.head?] at this
                  exact Option.some.inj this.symm
                simp only [hx0, hfc, Bool.false_eq_true, ↓reduceIte]
              | cons x1 xs1 =>
                cases xs1 with
                | nil => rfl
                | cons x2 xs2 =>
                  cases xs2 with
                  | nil =>
                    have hx0 : x0 = tag := by
                      have := congrArg List.head? htake
                      simp only [List.take, List.head?] at this
                      exact Option.some.inj this.symm
                    simp only [hx0, hfd, Bool.false_eq_true, ↓reduceIte]
                  | cons x3 xs3 =>
                    cases xs3 with
                    | nil => rfl
                    | cons x4 xs4 =>
                      cases xs4 with
                      | nil =>
                        have hx0 : x0 = tag := by
                          have := congrArg List.head? htake
                          simp only [List.take, List.head?] at this
                          exact Option.some.inj this.symm
                        simp only [hx0, hfe, Bool.false_eq_true, ↓reduceIte]
                      | cons x5 xs5 =>
                        cases xs5 with
                        | nil => rfl
                        | cons x6 xs6 =>
                          cases xs6 with
                          | nil => rfl
                          | cons x7 xs7 =>
                            cases xs7 with
                            | nil => rfl
                            | cons x8 xs8 =>
                              cases xs8 with
                              | nil =>
                                dsimp only
                                cases decide (x0 = 0xFF)
                                · rfl
                                · simp only [↓reduceIte]
                                  let v64 : UInt64 :=
                                    x1.toUInt64 ||| (x2.toUInt64 <<< 8) ||| (x3.toUInt64 <<< 16) |||
                                    (x4.toUInt64 <<< 24) ||| (x5.toUInt64 <<< 32) ||| (x6.toUInt64 <<< 40) |||
                                    (x7.toUInt64 <<< 48) ||| (x8.toUInt64 <<< 56)
                                  cases hge : decide ((0x100000000 : UInt64) ≤ v64)
                                  · rfl
                                  · simp only [↓reduceIte]
                                    have hnot_le : decide (v64 ≤ maxVal.toUInt64) = false := by
                                      apply decide_eq_false
                                      intro hle
                                      have h1 : 0x100000000 ≤ v64.toNat :=
                                        UInt64.le_iff_toNat_le.mp (of_decide_eq_true hge)
                                      have h2 : v64.toNat ≤ maxVal.toNat := by
                                        rw [← UInt32.toNat_toUInt64]
                                        exact UInt64.le_iff_toNat_le.mp hle
                                      have h3 : maxVal.toNat < 0x100000000 := maxVal.toNat_lt
                                      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h2 h3) h1)
                                    rw [hnot_le]; rfl
                              | cons _ _ => rfl
          · rfl
        · -- tag = 0xFE (need = 5)
          simp only [↓reduceIte]
          have hff : decide (tag = 0xFF) = false := by
            rw [of_decide_eq_true hfe]; rfl
          have hbl_lt5 : decide (bufLen < 5) = decide (bs.size < 5) := by
            rw [← hlen]; rfl
          rw [hff, Bool.or_false, hbl_lt5]
          cases hlt5 : decide (bs.size < 5)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hge5 : 5 ≤ (tag :: rest0).length := by
              rw [← hlist, hsz_list]
              exact Nat.not_lt.mp (of_decide_eq_false hlt5)
            rcases rest0 with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, rest4⟩⟩⟩⟩
            · exact absurd hge5 (Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.zero_lt_succ 3)))
            · exact absurd hge5 (Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 2))))
            · exact absurd hge5 (Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))))
            · exact absurd hge5 (Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))))
            · have hr1 : readU8 buf 1 = b1 := by
                have := hread_list 1 (by rw [hlist]; exact Nat.succ_lt_succ (Nat.zero_lt_succ _)); simp only [hlist] at this; exact this
              have hr2 : readU8 buf 2 = b2 := by
                have := hread_list 2 (by rw [hlist]; exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))); simp only [hlist] at this; exact this
              have hr3 : readU8 buf 3 = b3 := by
                have := hread_list 3 (by rw [hlist]; exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))); simp only [hlist] at this; exact this
              have hr4 : readU8 buf 4 = b4 := by
                have := hread_list 4 (by rw [hlist]; exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))))); simp only [hlist] at this; exact this
              rw [hr1, hr2, hr3, hr4]
              unfold BitcoinLedger.Basic.decodeVarIntCanonical? llbVarIntPrefixIsCanonical
              rw [List.toList_toArray]
              simp only [List.take, hfc, hfd, hfe, Bool.false_eq_true, ↓reduceIte]
              have hle32 : decide ((b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24)) ≤ 0xFFFFFFFF) = true :=
                decide_eq_true (u32_le_ffffffff b1 b2 b3 b4)
              rw [hle32, Bool.and_true]
              cases decide ((0x10000 : UInt64) ≤ (b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24)))
              · rfl
              · simp only [↓reduceIte]
                cases decide ((b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24)) ≤ maxVal.toUInt64) <;> rfl
          · rfl
      · -- tag = 0xFD (need = 3)
        simp only [↓reduceIte]
        have hff : decide (tag = 0xFF) = false := by
          rw [of_decide_eq_true hfd]; rfl
        have hbl_lt3 : decide (bufLen < 3) = decide (bs.size < 3) := by
          rw [← hlen]; rfl
        rw [hff, Bool.or_false, hbl_lt3]
        cases hlt3 : decide (bs.size < 3)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hge3 : 3 ≤ (tag :: rest0).length := by
            rw [← hlist, hsz_list]
            exact Nat.not_lt.mp (of_decide_eq_false hlt3)
          rcases rest0 with _ | ⟨b1, _ | ⟨b2, rest2⟩⟩
          · exact absurd hge3 (Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.zero_lt_succ 1)))
          · exact absurd hge3 (Nat.not_le_of_gt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 0))))
          · have hr1 : readU8 buf 1 = b1 := by
              have := hread_list 1 (by rw [hlist]; exact Nat.succ_lt_succ (Nat.zero_lt_succ _)); simp only [hlist] at this; exact this
            have hr2 : readU8 buf 2 = b2 := by
              have := hread_list 2 (by rw [hlist]; exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))); simp only [hlist] at this; exact this
            rw [hr1, hr2]
            unfold BitcoinLedger.Basic.decodeVarIntCanonical? llbVarIntPrefixIsCanonical
            rw [List.toList_toArray]
            simp only [List.take, hfc, hfd, Bool.false_eq_true, ↓reduceIte]
            have hle16 : decide ((b1.toUInt64 ||| (b2.toUInt64 <<< 8)) ≤ 0xFFFF) = true :=
              decide_eq_true (u16_le_ffff b1 b2)
            rw [hle16, Bool.and_true]
            cases decide ((0xFD : UInt64) ≤ (b1.toUInt64 ||| (b2.toUInt64 <<< 8)))
            · rfl
            · simp only [↓reduceIte]
              cases decide ((b1.toUInt64 ||| (b2.toUInt64 <<< 8)) ≤ maxVal.toUInt64) <;> rfl
        · rfl
    · -- tag ≤ 0xFC (need = 1)
      simp only [↓reduceIte]
      have hff : decide (tag = 0xFF) = false := by
        apply decide_eq_false
        intro heq
        have hle := UInt8.le_iff_toNat_le.mp (of_decide_eq_true hfc)
        rw [heq] at hle
        exact absurd hle (by decide)
      have hbl_lt1 : decide (bufLen < 1) = false := by
        apply decide_eq_false
        intro hlt1
        have : bs.size < 1 := by rw [← hlen]; exact UInt32.lt_iff_toNat_lt.mp hlt1
        exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hsz_pos (Nat.le_of_lt_succ this))
      have hbs_lt1 : decide (bs.size < 1) = false :=
        decide_eq_false (Nat.not_lt.mpr hsz_pos)
      rw [hff, Bool.or_false, hbl_lt1, hbs_lt1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      unfold BitcoinLedger.Basic.decodeVarIntCanonical? llbVarIntPrefixIsCanonical
      rw [List.toList_toArray]
      simp only [List.take, hfc, ↓reduceIte]
      cases decide (tag.toUInt64 ≤ maxVal.toUInt64) <;> rfl

/-- Concrete Witness: Freestanding C99 entrypoints agree on representative Bitcoin / Ledger vectors. -/
theorem witness_freestanding_kernels :
    llbVersionPacked = 0x00020401 ∧
    llbValidAmount 2100000000000000 = true ∧
    llbValidAmount 2100000000000001 = false ∧
    llbCheckedAddSatsOk 2100000000000000 1 = false ∧
    llbCheckedAddSatsVal 100000000 250000000 = 350000000 ∧
    llbCheckedSubSatsOk 100 101 = false ∧
    llbSatsDiv1e8 2100000000000000 = 21000000 ∧
    llbSatsMod1e8 123456789 = 23456789 ∧
    llbVarIntPrefixIsCanonical 0xFD 252 = false ∧
    llbVarIntPrefixIsCanonical 0xFD 253 = true ∧
    llbBip32StandardPurposeOk 0x80000054 = true ∧
    llbBip32StandardPurposeOk 84 = false ∧
    llbBip32PubkeyExportPrefixOk 0x80000054 0x80000000 0x80000000 0 3 0 true = true ∧
    llbBip32PubkeyExportPrefixOk 0x80454C45 0xC2494532 0 0 2 0 true = true ∧
    llbSegwitProgramValid 0 20 = true ∧
    llbSegwitProgramValid 0 2 = false ∧
    llbSegwitProgramValid 2 2 = true ∧
    llbBech32FinalConstant 1 = 1 ∧
    llbBech32FinalConstant 2 = 0x2bc830a3 ∧
    llbWalletNameCharOk 0x20 true = false ∧
    llbWalletNameCharOk 0x20 false = true ∧
    llbSighashTypeValid 0x00 = false ∧
    llbSighashTypeValid 0x81 = true ∧
    llbTaprootSighashValid 0x00 = true ∧
    merkleStateDir (merkleAdvanceSteps 1 (packMerkleState 5 4)) = 0xFF ∧
    merkleStateDir (merkleAdvanceSteps 2 (packMerkleState 5 3)) = 1 ∧
    div10U32 4294967295 = 429496729 ∧
    mod10U32 4294967295 = 5 ∧
    llbMiniscriptOlderOk 144 = true ∧
    llbMiniscriptOlderOk 0 = false ∧
    llbMiniscriptAfterOk 800000 = true ∧
    llbMiniscriptAfterOk 0x80000000 = false ∧
    llbPsbtLocktimeFinalize (llbPsbtLocktimeStep (llbPsbtLocktimeStep llbPsbtLocktimeInit 1 800000 0 0) 1 750000 1 1700000000) 0 =
      (((1 : UInt64) <<< 32) ||| 800000) ∧
    llbPsbtLocktimeFinalize (llbPsbtLocktimeStep (llbPsbtLocktimeStep llbPsbtLocktimeInit 1 800000 0 0) 0 0 1 1700000000) 0 = 0 := by
  decide

end Proofs.FreestandingKernels

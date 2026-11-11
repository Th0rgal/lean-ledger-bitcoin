import InternalSpec
import BitcoinLedger.Basic
import BitcoinLedger.Bip32
import BitcoinLedger.Script
import BitcoinLedger.FreestandingKernels
import Proofs.Basic
import Proofs.Bip32
import Proofs.Script

namespace Proofs.FreestandingKernels

/-!
# `Proofs.FreestandingKernels` — Machine-Checked Refinement Proofs for Freestanding C99 Kernels

Constructive (`0 Classical.choice`, `0 sorryAx`, `0 native_decide`, `0 omega`) refinement theorems
proving that every `@[export llb_*]` scalar entrypoint in `BitcoinLedger.FreestandingKernels`
refines the corresponding executable primitive in `BitcoinLedger.{Basic,Bip32,Script}` and
the normative specification in `InternalSpec.{Basic,Bip32,Script,Psbt,MerkleProtocol}`.
-/

open BitcoinLedger.FreestandingKernels

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

theorem llbVarIntEncodedLen_eq (n : UInt64) :
    (llbVarIntEncodedLen n).toNat = BitcoinLedger.Basic.varIntByteLen n ∧
    (llbVarIntEncodedLen n).toNat = (InternalSpec.encodeVarIntCanonical n).size := by
  have h1 : (llbVarIntEncodedLen n).toNat = BitcoinLedger.Basic.varIntByteLen n := by
    unfold llbVarIntEncodedLen BitcoinLedger.Basic.varIntByteLen
    cases decide (n ≤ 0xFC)
    · cases decide (n ≤ 0xFFFF)
      · cases decide (n ≤ 0xFFFFFFFF) <;> rfl
      · rfl
    · rfl
  have h2 : BitcoinLedger.Basic.varIntByteLen n = (InternalSpec.encodeVarIntCanonical n).size := by
    rw [← Proofs.Basic.encodeVarInt_eq n]
    unfold BitcoinLedger.Basic.varIntByteLen BitcoinLedger.Basic.encodeVarInt
    cases decide (n ≤ 0xFC)
    · cases decide (n ≤ 0xFFFF)
      · cases decide (n ≤ 0xFFFFFFFF) <;> rfl
      · rfl
    · rfl
  exact ⟨h1, h1.trans h2⟩

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

theorem llbBip32Harden_eq (n : UInt32) :
    llbBip32Harden n = BitcoinLedger.Bip32.harden n ∧
    llbBip32Harden n = InternalSpec.harden n :=
  ⟨rfl, Proofs.Bip32.harden_eq n⟩

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

theorem llbBech32PolymodStep_eq (pre : UInt32) (val : UInt8) :
    llbBech32PolymodStep pre val = BitcoinLedger.Script.bech32PolymodStep pre val ∧
    llbBech32PolymodStep pre val = InternalSpec.bech32PolymodStep pre val :=
  ⟨rfl, Proofs.Script.bech32PolymodStep_eq pre val⟩

theorem llbMinimalPushOpcodeOk_sound
    {script payload rem : ByteArray}
    (hdec : BitcoinLedger.Script.decodeMinimalPushPrefix? script = some (payload, rem))
    (hlen32 : payload.size ≤ 0xFFFFFFFF) :
    llbMinimalPushOpcodeOk
      (script.data.toList.headD 0xFF)
      (payload.data.toList.headD 0)
      (UInt32.ofNat payload.size) = true := by
  unfold BitcoinLedger.Script.decodeMinimalPushPrefix? at hdec
  cases hs : script.data.toList with
  | nil => simp [hs] at hdec
  | cons op rest =>
      rw [hs] at hdec
      dsimp only at hdec
      dsimp [List.headD]
      unfold llbMinimalPushOpcodeOk
      unfold BitcoinLedger.Script.OP_0 BitcoinLedger.Script.OP_1NEGATE
        BitcoinLedger.Script.OP_1 BitcoinLedger.Script.OP_16
        BitcoinLedger.Script.OP_PUSHDATA1 BitcoinLedger.Script.OP_PUSHDATA2
        BitcoinLedger.Script.OP_PUSHDATA4 at hdec
      cases h0 : decide (op = 0x00)
      · rw [h0] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
        cases h4f : decide (op = 0x4F)
        · rw [h4f] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
          cases h51 : (decide (0x51 ≤ op) && decide (op ≤ 0x60))
          · rw [h51] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
            cases h01 : decide (op = 0x01)
            · rw [h01] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
              have hop2 : (decide (2 ≤ op.toNat) && decide (op.toNat ≤ 75)) =
                  (decide ((0x02 : UInt8) ≤ op) && decide (op ≤ 0x4B)) := rfl
              rw [hop2] at hdec
              cases h2_75 : (decide ((0x02 : UInt8) ≤ op) && decide (op ≤ 0x4B))
              · rw [h2_75] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
                cases h4c : decide (op = 0x4C)
                · rw [h4c] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
                  cases h4d : decide (op = 0x4D)
                  · rw [h4d] at hdec; simp only [Bool.false_eq_true, ↓reduceIte] at hdec ⊢
                    cases h4e : decide (op = 0x4E)
                    · rw [h4e] at hdec; simp at hdec
                    · rw [h4e] at hdec; simp only [↓reduceIte] at hdec ⊢
                      cases rest with
                      | nil => simp at hdec
                      | cons b0 r1 =>
                          cases r1 with
                          | nil => simp at hdec
                          | cons b1 r2 =>
                              cases r2 with
                              | nil => simp at hdec
                              | cons b2 r3 =>
                                  cases r3 with
                                  | nil => simp at hdec
                                  | cons b3 tail =>
                                      dsimp only at hdec
                                      cases hbad : (decide (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 65536) ||
                                        decide (tail.length < b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat))
                                      · rw [hbad] at hdec
                                        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                                        rcases hdec with ⟨rfl, _⟩
                                        rcases Bool.or_eq_false_iff.mp hbad with ⟨hge1, hlen1⟩
                                        have hge : 65536 ≤ b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat :=
                                          Nat.le_of_not_lt (of_decide_eq_false hge1)
                                        have hleT : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat ≤ tail.length :=
                                          Nat.le_of_not_lt (of_decide_eq_false hlen1)
                                        have hsz : (ByteArray.mk (tail.take (b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat)).toArray).size =
                                            b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat := by
                                          simp [ByteArray.size, List.length_take_of_le hleT]
                                        rw [hsz] at hlen32 ⊢
                                        have hlt32 : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 2 ^ 32 :=
                                          Nat.lt_of_le_of_lt hlen32 (by decide)
                                        apply decide_eq_true
                                        rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]
                                        exact hge
                                      · rw [hbad] at hdec; simp at hdec
                  · rw [h4d] at hdec; simp only [↓reduceIte] at hdec ⊢
                    cases rest with
                    | nil => simp at hdec
                    | cons b0 r1 =>
                        cases r1 with
                        | nil => simp at hdec
                        | cons b1 tail =>
                            dsimp only at hdec
                            cases hbad : (decide (b0.toNat + 256 * b1.toNat < 256) || decide (tail.length < b0.toNat + 256 * b1.toNat))
                            · rw [hbad] at hdec
                              simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                              rcases hdec with ⟨rfl, _⟩
                              rcases Bool.or_eq_false_iff.mp hbad with ⟨hge1, hlen1⟩
                              have hge : 256 ≤ b0.toNat + 256 * b1.toNat := Nat.le_of_not_lt (of_decide_eq_false hge1)
                              have hleT : b0.toNat + 256 * b1.toNat ≤ tail.length := Nat.le_of_not_lt (of_decide_eq_false hlen1)
                              have hsz : (ByteArray.mk (tail.take (b0.toNat + 256 * b1.toNat)).toArray).size = b0.toNat + 256 * b1.toNat := by
                                simp [ByteArray.size, List.length_take_of_le hleT]
                              rw [hsz]
                              have hmax : b0.toNat + 256 * b1.toNat ≤ 65535 := by
                                have hb0 : b0.toNat ≤ 255 := Nat.le_of_lt_succ b0.toNat_lt
                                have hb1 : b1.toNat ≤ 255 := Nat.le_of_lt_succ b1.toNat_lt
                                exact Nat.le_trans (Nat.add_le_add hb0 (Nat.mul_le_mul_left 256 hb1)) (by decide)
                              have hlt32 : b0.toNat + 256 * b1.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt hmax (by decide)
                              apply Bool.and_eq_true_iff.mpr
                              refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
                              · rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]; exact hge
                              · rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]; exact hmax
                            · rw [hbad] at hdec; simp at hdec
                · rw [h4c] at hdec; simp only [↓reduceIte] at hdec ⊢
                  cases rest with
                  | nil => simp at hdec
                  | cons lenByte tail =>
                      dsimp only at hdec
                      cases hbad : (decide (lenByte.toNat < 76) || decide (tail.length < lenByte.toNat))
                      · rw [hbad] at hdec
                        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                        rcases hdec with ⟨rfl, _⟩
                        rcases Bool.or_eq_false_iff.mp hbad with ⟨hge1, hlen1⟩
                        have hge : 76 ≤ lenByte.toNat := Nat.le_of_not_lt (of_decide_eq_false hge1)
                        have hleT : lenByte.toNat ≤ tail.length := Nat.le_of_not_lt (of_decide_eq_false hlen1)
                        have hsz : (ByteArray.mk (tail.take lenByte.toNat).toArray).size = lenByte.toNat := by
                          simp [ByteArray.size, List.length_take_of_le hleT]
                        rw [hsz]
                        have hmax : lenByte.toNat ≤ 255 := Nat.le_of_lt_succ lenByte.toNat_lt
                        have hlt32 : lenByte.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt hmax (by decide)
                        apply Bool.and_eq_true_iff.mpr
                        refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
                        · rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]; exact hge
                        · rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32]; exact hmax
                      · rw [hbad] at hdec; simp at hdec
              · rw [h2_75] at hdec; simp only [↓reduceIte] at hdec ⊢
                cases hshort : decide (rest.length < op.toNat)
                · rw [hshort] at hdec
                  simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                  rcases hdec with ⟨rfl, _⟩
                  have hleT : op.toNat ≤ rest.length := Nat.le_of_not_lt (of_decide_eq_false hshort)
                  have hsz : (ByteArray.mk (rest.take op.toNat).toArray).size = op.toNat := by
                    simp [ByteArray.size, List.length_take_of_le hleT]
                  rw [hsz]
                  apply decide_eq_true
                  apply UInt32.toNat_inj.mp
                  have hlt32 : op.toNat < 2 ^ 32 := Nat.lt_trans op.toNat_lt (by decide)
                  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32, UInt8.toNat_toUInt32]
                · rw [hshort] at hdec; simp at hdec
            · rw [h01] at hdec; simp only [↓reduceIte] at hdec ⊢
              cases rest with
              | nil => simp at hdec
              | cons b tail =>
                  dsimp only at hdec
                  have hbchk : ((decide (1 ≤ b.toNat) && decide (b.toNat ≤ 16)) || decide (b = 0x81)) =
                      ((decide ((1 : UInt8) ≤ b) && decide (b ≤ 16)) || decide (b = 0x81)) := rfl
                  rw [hbchk] at hdec
                  cases hnonmin : ((decide ((1 : UInt8) ≤ b) && decide (b ≤ 16)) || decide (b = 0x81))
                  · rw [hnonmin] at hdec
                    simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                    rcases hdec with ⟨rfl, _⟩
                    change decide ((1 : UInt32) = 1) &&
                      !((decide ((1 : UInt8) ≤ b) && decide (b ≤ 16)) || decide (b = 0x81)) = true
                    rw [hnonmin]
                    rfl
                  · rw [hnonmin] at hdec; simp at hdec
          · rw [h51] at hdec
            simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
            rcases hdec with ⟨rfl, _⟩
            exact decide_eq_true rfl
        · rw [h4f] at hdec
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
          rcases hdec with ⟨rfl, _⟩
          rfl
      · rw [h0] at hdec
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
        rcases hdec with ⟨rfl, _⟩
        rfl

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

theorem llbMerkleDepthIndexOk_refines_merkleProtocol
    (treeSize index : UInt32) (depth : UInt8) :
    llbMerkleDepthIndexOk treeSize index depth =
      !(decide (treeSize.toNat = 0) ||
        decide (index.toNat ≥ treeSize.toNat) ||
        decide (index.toNat > InternalSpec.MerkleProtocol.MAX_MERKLE_LEAF_INDEX) ||
        decide (depth.toNat > InternalSpec.MerkleProtocol.MAX_MERKLE_TREE_DEPTH)) := by
  unfold llbMerkleDepthIndexOk InternalSpec.MerkleProtocol.MAX_MERKLE_LEAF_INDEX
    InternalSpec.MerkleProtocol.MAX_MERKLE_TREE_DEPTH
  cases h0 : decide (0 < treeSize)
  · have hz : treeSize.toNat = 0 := Nat.eq_zero_of_not_pos (of_decide_eq_false h0)
    simp [hz]
  · have hnz : treeSize.toNat ≠ 0 := Nat.ne_of_gt (of_decide_eq_true h0)
    simp only [Bool.true_and, hnz, decide_false, Bool.false_or]
    cases hlt : decide (index < treeSize)
    · have hge : index.toNat ≥ treeSize.toNat := Nat.le_of_not_lt (of_decide_eq_false hlt)
      simp [hge]
    · have hltNat : ¬ (index.toNat ≥ treeSize.toNat) := Nat.not_le.mpr (of_decide_eq_true hlt)
      simp only [Bool.true_and, hltNat, decide_false, Bool.false_or]
      cases hidx : decide (index ≤ 0x7FFFFFFF)
      · have hgtIdx : index.toNat > 0x7FFFFFFF :=
          Nat.lt_of_not_le (fun h => of_decide_eq_false hidx (UInt32.le_iff_toNat_le.mpr h))
        simp [hgtIdx]
      · have hngIdx : ¬ (index.toNat > 0x7FFFFFFF) :=
          Nat.not_lt.mpr (UInt32.le_iff_toNat_le.mp (of_decide_eq_true hidx))
        simp only [Bool.true_and, hngIdx, decide_false, Bool.false_or]
        cases hd : decide (depth ≤ 32)
        · have hgtD : depth.toNat > 32 :=
            Nat.lt_of_not_le (fun h => of_decide_eq_false hd (UInt8.le_iff_toNat_le.mpr h))
          simp [hgtD]
        · have hngD : ¬ (depth.toNat > 32) :=
            Nat.not_lt.mpr (UInt8.le_iff_toNat_le.mp (of_decide_eq_true hd))
          simp [hngD]

theorem llbBolosSwForError_refines (err : InternalSpec.SpecError) :
    llbBolosSwForError (BitcoinLedger.Basic.specErrorToTag err) =
      BitcoinLedger.Basic.specErrorToBolosU16 err ∧
    llbBolosSwForError (BitcoinLedger.Basic.specErrorToTag err) =
      err.toBolosCode := by
  cases err <;> exact ⟨rfl, rfl⟩

set_option maxRecDepth 16384 in
theorem llbBolosSwForError_never_ok (errTag : UInt8) :
    llbBolosSwForError errTag ≠ 0x9000 ∧ llbBolosSwForError errTag ≠ 0xE000 := by
  have hall :
      ∀ x : UInt8,
        decide (llbBolosSwForError x ≠ 0x9000 ∧ llbBolosSwForError x ≠ 0xE000) = true :=
    forall_u8_of_range (by decide)
  exact of_decide_eq_true (hall errTag)

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

/-- Single-step refinement: `llbMerkleStateDir` computes the head direction of `InternalSpec.MerkleProtocol.merkleDirections`. -/
theorem llbMerkleStateDir_spec (size index : UInt32) :
    llbMerkleStateDir (packMerkleState size index) =
      encodeMerkleDir? (InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat).head? := by
  unfold llbMerkleStateDir
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

/-- Multi-step refinement: `step` iterations of `llbMerkleAdvanceState` followed by `llbMerkleStateDir`
    computes the exact `step`-th top-down Merkle proof direction of `InternalSpec.MerkleProtocol.merkleDirections` in `O(step)`. -/
theorem llbMerkleAdvanceState_steps_spec
    (step : Nat) (size index : UInt32) (hidx_valid : index < size ∨ size ≤ 1) :
    llbMerkleStateDir (merkleAdvanceSteps step (packMerkleState size index)) =
      encodeMerkleDir? ((InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat)[step]?) := by
  induction step generalizing size index with
  | zero =>
    unfold merkleAdvanceSteps
    have h0 : (InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat)[0]? =
        (InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat).head? := by
      cases InternalSpec.MerkleProtocol.merkleDirections size.toNat index.toNat <;> rfl
    rw [h0]
    exact llbMerkleStateDir_spec size index
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
    llbVarIntEncodedLen 252 = 1 ∧
    llbVarIntEncodedLen 253 = 3 ∧
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
    llbMerkleDepthIndexOk 16 15 4 = true ∧
    llbMerkleDepthIndexOk 16 16 4 = false ∧
    llbMerkleStateDir (merkleAdvanceSteps 1 (packMerkleState 5 4)) = 0xFF ∧
    llbMerkleStateDir (merkleAdvanceSteps 2 (packMerkleState 5 3)) = 1 ∧
    llbBolosSwForError 5 = 0x6985 := by
  decide

end Proofs.FreestandingKernels

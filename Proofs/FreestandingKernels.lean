import Spec
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
the normative specification in `Spec.{Basic,Bip32,Script,Psbt,MerkleProtocol}`.
-/

open BitcoinLedger.FreestandingKernels

/-! ## 1. Version & Satoshi Overflow-Safe Arithmetic Refinement -/

theorem llbVersionPacked_bytes :
    (llbVersionPacked >>> 16).toUInt8 = Spec.ledgerBitcoinTargetVersion.major ∧
    ((llbVersionPacked >>> 8) &&& 0xff).toUInt8 = Spec.ledgerBitcoinTargetVersion.minor ∧
    (llbVersionPacked &&& 0xff).toUInt8 = Spec.ledgerBitcoinTargetVersion.patch := by
  exact ⟨rfl, rfl, rfl⟩

theorem llbVersionPacked_eq_hex :
    llbVersionPacked = 0x00020401 := rfl

theorem llbValidAmount_eq (sats : UInt64) :
    llbValidAmount sats = BitcoinLedger.Basic.isValidAmount sats := rfl

theorem llbValidAmount_iff (sats : UInt64) :
    llbValidAmount sats = true ↔ Spec.ValidAmount sats :=
  Proofs.Basic.isValidAmount_iff sats

theorem llbCheckedAddSats_refines (a b : UInt64) :
    (if llbCheckedAddSatsOk a b then some (llbCheckedAddSatsVal a b) else none) =
      BitcoinLedger.Basic.checkedAddSats? a b ∧
    (if llbCheckedAddSatsOk a b then some (llbCheckedAddSatsVal a b) else none) =
      Spec.addAmounts? a b := by
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
      Spec.subAmounts? a b := by
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
    (llbVarIntEncodedLen n).toNat = (Spec.encodeVarIntCanonical n).size := by
  have h1 : (llbVarIntEncodedLen n).toNat = BitcoinLedger.Basic.varIntByteLen n := by
    unfold llbVarIntEncodedLen BitcoinLedger.Basic.varIntByteLen
    cases decide (n ≤ 0xFC)
    · cases decide (n ≤ 0xFFFF)
      · cases decide (n ≤ 0xFFFFFFFF) <;> rfl
      · rfl
    · rfl
  have h2 : BitcoinLedger.Basic.varIntByteLen n = (Spec.encodeVarIntCanonical n).size := by
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
    llbBip32IsHardened idx = Spec.isHardened idx :=
  ⟨rfl, Proofs.Bip32.isHardened_eq idx⟩

theorem llbBip32Harden_eq (n : UInt32) :
    llbBip32Harden n = BitcoinLedger.Bip32.harden n ∧
    llbBip32Harden n = Spec.harden n :=
  ⟨rfl, Proofs.Bip32.harden_eq n⟩

theorem llbBip32Unharden_eq (idx : UInt32) :
    llbBip32Unharden idx = BitcoinLedger.Bip32.unharden idx ∧
    llbBip32Unharden idx = Spec.unharden idx :=
  ⟨rfl, Proofs.Bip32.unharden_eq idx⟩

theorem llbBip32BolosDepthOk_eq (path : Spec.Bip32Path) (hbyte : path.size ≤ 255) :
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

theorem llbBip32VanadiumDepthOk_eq (path : Spec.Bip32Path) (hbyte : path.size ≤ 255) :
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
      Spec.decodeWitnessVersionOpcode? op := by
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
      Spec.isValidSegwitProgram witver witprog := by
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
    llbBech32PolymodStep pre val = Spec.bech32PolymodStep pre val :=
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
      decide ((Spec.Psbt.classifySighash .segwitV0 (some b.toUInt32)).1 ≠ .unsupported) := by
  have hall :
      ∀ x : UInt8,
        decide
          ((decide (1 ≤ x.toUInt32 &&& 0x7F) && decide (x.toUInt32 &&& 0x7F ≤ 3)) =
            decide ((Spec.Psbt.classifySighash .segwitV0 (some x.toUInt32)).1 ≠ .unsupported)) = true :=
    forall_u8_of_range (by decide)
  exact of_decide_eq_true (hall b)

theorem llbSighashTypeValid_refines_psbt (sighashU32 : UInt32) :
    llbSighashTypeValid sighashU32 =
      decide ((Spec.Psbt.classifySighash .segwitV0 (some sighashU32)).1 ≠ .unsupported) := by
  cases hle : decide (sighashU32 ≤ 0xFF)
  · have hgt : sighashU32.toNat > 0xFF :=
      Nat.lt_of_not_le (fun h => of_decide_eq_false hle (UInt32.le_iff_toNat_le.mpr h))
    unfold llbSighashTypeValid Spec.Psbt.classifySighash
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
      decide ((Spec.Psbt.classifySighash .taprootV1 (some sighashByte.toUInt32)).1 ≠ .unsupported) := by
  have hall :
      ∀ x : UInt8,
        decide
          (llbTaprootSighashValid x =
            decide ((Spec.Psbt.classifySighash .taprootV1 (some x.toUInt32)).1 ≠ .unsupported)) = true :=
    forall_u8_of_range (by decide)
  exact of_decide_eq_true (hall sighashByte)

theorem llbMerkleDepthIndexOk_refines_merkleProtocol
    (treeSize index : UInt32) (depth : UInt8) :
    llbMerkleDepthIndexOk treeSize index depth =
      !(decide (treeSize.toNat = 0) ||
        decide (index.toNat ≥ treeSize.toNat) ||
        decide (index.toNat > Spec.MerkleProtocol.MAX_MERKLE_LEAF_INDEX) ||
        decide (depth.toNat > Spec.MerkleProtocol.MAX_MERKLE_TREE_DEPTH)) := by
  unfold llbMerkleDepthIndexOk Spec.MerkleProtocol.MAX_MERKLE_LEAF_INDEX
    Spec.MerkleProtocol.MAX_MERKLE_TREE_DEPTH
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

theorem llbBolosSwForError_refines (err : Spec.SpecError) :
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

/-- Concrete Witness: Freestanding C99 entrypoints agree on representative Bitcoin / Ledger vectors. -/
theorem witness_freestanding_kernels :
    llbVersionPacked = 0x00020401 ∧
    llbValidAmount 2100000000000000 = true ∧
    llbValidAmount 2100000000000001 = false ∧
    llbCheckedAddSatsOk 2100000000000000 1 = false ∧
    llbCheckedAddSatsVal 100000000 250000000 = 350000000 ∧
    llbCheckedSubSatsOk 100 101 = false ∧
    llbVarIntEncodedLen 252 = 1 ∧
    llbVarIntEncodedLen 253 = 3 ∧
    llbVarIntPrefixIsCanonical 0xFD 252 = false ∧
    llbVarIntPrefixIsCanonical 0xFD 253 = true ∧
    llbBip32StandardPurposeOk 0x80000054 = true ∧
    llbBip32StandardPurposeOk 84 = false ∧
    llbSegwitProgramValid 0 20 = true ∧
    llbSegwitProgramValid 0 2 = false ∧
    llbSegwitProgramValid 2 2 = true ∧
    llbSighashTypeValid 0x00 = false ∧
    llbSighashTypeValid 0x81 = true ∧
    llbTaprootSighashValid 0x00 = true ∧
    llbMerkleDepthIndexOk 16 15 4 = true ∧
    llbMerkleDepthIndexOk 16 16 4 = false ∧
    llbBolosSwForError 5 = 0x6985 := by
  decide

end Proofs.FreestandingKernels

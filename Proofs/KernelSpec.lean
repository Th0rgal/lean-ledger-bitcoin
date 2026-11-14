import Spec
import Proofs.FreestandingKernels

/-!
# Proofs of `Spec.lean`

One theorem per statement of `Spec.lean`, then `kernel_meets_spec`, then one accepted and
one rejected concrete input per statement (so no statement holds for an empty reason).

Only `SplitBtc` reuses earlier work (`Proofs.FreestandingKernels.llbSatsDiv1e8_eq` and
`llbSatsMod1e8_eq`, which are themselves stated on the kernel functions). Every other proof
unfolds the kernel function directly.
-/

namespace Proofs.KernelSpec

open BitcoinLedger.FreestandingKernels

/-- `omega`, after splitting `↔` and `∧` by hand: `omega` itself proves an `↔` goal by
    contradiction, which would bring in `Classical.choice`. -/
local macro "omega_split" : tactic =>
  `(tactic| ((repeat' (first | apply Iff.intro | apply And.intro | intro _)) <;> omega))

private theorem forall_byte {p : UInt8 → Bool}
    (h : (List.range 256).all (fun k => p (UInt8.ofNat k)) = true) :
    ∀ b : UInt8, p b = true := by
  intro b
  have hb := List.all_eq_true.mp h b.toNat (List.mem_range.mpr b.toNat_lt)
  have heq : UInt8.ofNat b.toNat = b := by
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt b.toNat_lt]
  rwa [heq] at hb

private theorem testBit_mask_low : ∀ j, j < 31 → Nat.testBit 2147483647 j = true := by decide

private theorem testBit_mask_high (j : Nat) (h : 31 ≤ j) : Nat.testBit 2147483647 j = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hp : 2147483647 < 2 ^ j :=
    Nat.lt_of_lt_of_le (by decide : 2147483647 < 2 ^ 31) (Nat.pow_le_pow_right (by decide) h)
  rw [Nat.div_eq_of_lt hp]; rfl

/-- Masking with `2^31 - 1` is reduction modulo `2^31`. (The core lemma
    `Nat.and_two_pow_sub_one_eq_mod` depends on `Classical.choice`.) -/
private theorem and_mask31 (n : Nat) : n &&& 2147483647 = n % 2147483648 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e : (2147483648 : Nat) = 2 ^ 31 := by decide
  rw [Nat.testBit_and, e, Nat.testBit_mod_two_pow]
  by_cases h : j < 31
  · rw [testBit_mask_low j h]; simp [h]
  · rw [testBit_mask_high j (Nat.le_of_not_lt h)]; simp [h]

private theorem and31 (n : Nat) : n &&& 2147483648 = 0 ↔ n / 2147483648 % 2 = 0 := by
  have e : (2147483648 : Nat) = 2 ^ 31 := by decide
  have hbit : (n &&& 2 ^ 31 = 0) ↔ n.testBit 31 = false := by
    constructor
    · intro h0
      have h : (n &&& 2 ^ 31).testBit 31 = false := by rw [h0]; exact Nat.zero_testBit 31
      rw [Nat.testBit_and, Nat.testBit_two_pow] at h
      simpa using h
    · intro hb
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : 31 = j
      · subst hj; simp [hb]
      · simp [hj]
  rw [e, hbit, Nat.testBit_eq_decide_div_mod_eq]
  simp

theorem validAmount : Spec.ValidAmount := by
  intro a
  simp [llbValidAmount, MAX_MONEY_U64, Spec.maxMoney, UInt64.le_iff_toNat_le]

theorem checkedAdd : Spec.CheckedAdd := by
  intro a b
  simp only [llbCheckedAddSatsVal, llbCheckedAddSatsOk, MAX_MONEY_U64, Spec.maxMoney]
  have ha := a.toNat_lt; have hb := b.toNat_lt
  by_cases h1 : a ≤ 2100000000000000
  · have h1' : a.toNat ≤ 2100000000000000 := by simpa [UInt64.le_iff_toNat_le] using h1
    have hs : (2100000000000000 - a : UInt64).toNat = 2100000000000000 - a.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ h1]; rfl
    by_cases h2 : b ≤ 2100000000000000 - a
    · have h2' : b.toNat ≤ 2100000000000000 - a.toNat := by
        rw [← hs]; exact UInt64.le_iff_toNat_le.mp h2
      simp [h1, h2]
      omega_split
    · have h2' : ¬ b.toNat ≤ 2100000000000000 - a.toNat := by
        rw [← hs]; exact fun h => h2 (UInt64.le_iff_toNat_le.mpr h)
      simp [h1, h2]; omega_split
  · have h1' : ¬ a.toNat ≤ 2100000000000000 := fun h => h1 (UInt64.le_iff_toNat_le.mpr h)
    simp [h1]; omega_split

theorem checkedSub : Spec.CheckedSub := by
  intro a b
  simp only [llbCheckedSubSatsVal, llbCheckedSubSatsOk, MAX_MONEY_U64, Spec.maxMoney]
  have hM : (2100000000000000 : UInt64).toNat = 2100000000000000 := rfl
  by_cases h1 : a ≤ 2100000000000000 <;> by_cases h2 : b ≤ a
  all_goals
    have h1' := h1; have h2' := h2
    rw [UInt64.le_iff_toNat_le, hM] at h1'
    rw [UInt64.le_iff_toNat_le] at h2'
    simp [h1, h2]
    try omega_split

theorem splitBtc : Spec.SplitBtc := by
  intro a
  constructor
  · rw [Proofs.FreestandingKernels.llbSatsDiv1e8_eq, UInt64.toNat_div]; rfl
  · have h := Proofs.FreestandingKernels.llbSatsMod1e8_eq a
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_mod] at this
    simpa using this

theorem hardenedBit : Spec.HardenedBit := by
  intro i
  have hi : i.toNat < 4294967296 := i.toNat_lt
  refine ⟨?_, ?_⟩
  · simp only [llbBip32IsHardened, ← UInt32.toNat_inj, UInt32.toNat_and]
    have : (2147483648 : UInt32).toNat = 2147483648 := rfl
    have z : (0 : UInt32).toNat = 0 := rfl
    simp only [this, z, Bool.not_eq_true', decide_eq_false_iff_not, and31]
    omega_split
  · simp only [llbBip32Unharden, UInt32.toNat_and]
    have : (2147483647 : UInt32).toNat = 2147483647 := rfl
    rw [this, and_mask31]

theorem depthLimits : Spec.DepthLimits := by
  intro d; simp [llbBip32BolosDepthOk, llbBip32VanadiumDepthOk, UInt8.le_iff_toNat_le]

theorem segwitProgram : Spec.SegwitProgram := by
  intro v len
  simp [llbSegwitProgramValid, ← UInt8.toNat_inj, UInt8.le_iff_toNat_le]
  split <;> simp_all <;> omega_split

set_option maxRecDepth 100000 in
theorem witnessOpcode : Spec.WitnessOpcode := by
  have h := forall_byte (p := fun op => decide ((llbWitnessOpcodeToVersion op).toNat =
      if op.toNat = 0 then 0 else if 81 ≤ op.toNat ∧ op.toNat ≤ 96 then op.toNat - 80 else 255)) (by decide)
  intro op; exact of_decide_eq_true (h op)


set_option maxRecDepth 100000 in
private theorem byteSighash : ∀ b : UInt8,
    (decide (llbSighashTypeValid b.toUInt32 = true ↔ b.toNat ∈ [1, 2, 3, 129, 130, 131])) = true :=
  forall_byte (by decide)


theorem sighashType : Spec.SighashType := by
  intro s
  by_cases h : s.toNat ≤ 255
  · have hs : s = (UInt8.ofNat s.toNat).toUInt32 := by
      apply UInt32.toNat_inj.mp
      rw [UInt8.toNat_toUInt32, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega_split)]
    have hb := of_decide_eq_true (byteSighash (UInt8.ofNat s.toNat))
    rw [← hs, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega_split)] at hb
    exact hb
  · have hgt : ¬ s ≤ 0xFF := fun hle => h (UInt32.le_iff_toNat_le.mp hle)
    simp [llbSighashTypeValid, hgt]
    omega_split

set_option maxRecDepth 100000 in
theorem taprootSighashType : Spec.TaprootSighashType := by
  have h := forall_byte (p := fun s => decide (llbTaprootSighashValid s = true ↔
      s.toNat ∈ [0, 1, 2, 3, 129, 130, 131])) (by decide)
  intro s; exact of_decide_eq_true (h s)


theorem compactSizeCanonical : Spec.CompactSizeCanonical := by
  intro tag v
  have ht := tag.toNat_lt
  simp only [llbVarIntPrefixIsCanonical]
  by_cases h1 : tag ≤ 0xFC
  · have h1' : tag.toNat ≤ 252 := UInt8.le_iff_toNat_le.mp h1
    simp [h1, ← UInt64.toNat_inj]
    constructor
    · intro h; exact Or.inl ⟨by omega, by omega⟩
    · intro h; omega
  · have h1' : ¬ tag.toNat ≤ 252 := fun h => h1 (UInt8.le_iff_toNat_le.mpr h)
    simp [h1, ← UInt8.toNat_inj, UInt64.le_iff_toNat_le]
    by_cases h253 : tag.toNat = 253
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h253)]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨h.1, h.2, h253⟩)
      · intro h; omega_split
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h253)]
      by_cases h254 : tag.toNat = 254
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h254)]
        constructor
        · intro h; exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2, h254⟩))
        · intro h; omega_split
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h254)]
        constructor
        · intro h; exact Or.inr (Or.inr (Or.inr ⟨h, by omega⟩))
        · intro h; omega

/-! ### Buffers -/

private theorem u32_ofNat_toNat (i : UInt32) : UInt32.ofNat i.toNat = i := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt i.toNat_lt]

/-- Two buffer prefixes are the same list exactly when they have the same length and the
    same byte at every index below it. -/
private theorem bytes_eq_iff (a b : ConstBytes) (n m : UInt32) :
    Spec.bytes a n.toNat = Spec.bytes b m.toNat ↔
      n = m ∧ ∀ i : UInt32, i < n → readU8 a i = readU8 b i := by
  unfold Spec.bytes readU8
  constructor
  · intro h
    have hlen : n.toNat = m.toNat := by
      have := congrArg List.length h
      simpa using this
    refine ⟨UInt32.toNat_inj.mp hlen, ?_⟩
    intro i hi
    have hi' : i.toNat < n.toNat := UInt32.lt_iff_toNat_lt.mp hi
    have hget := congrArg (fun l => l[i.toNat]?) h
    simp only [List.getElem?_map, List.getElem?_range hi', List.getElem?_range (hlen ▸ hi'),
      Option.map_some, Option.some.injEq, u32_ofNat_toNat] at hget
    exact UInt8.toNat_inj.mp hget
  · rintro ⟨rfl, h⟩
    apply List.map_congr_left
    intro i hi
    have hi' : i < n.toNat := List.mem_range.mp hi
    have hlt : UInt32.ofNat i < n := by
      rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans hi' n.toNat_lt)]
      exact hi'
    rw [h _ hlt]

theorem dualUtxo : Spec.DualUtxo := by
  intro wAmt nAmt wSpk nSpk wLen nLen
  rw [bytes_eq_iff]
  unfold llbCheckDualUtxo
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, validAmount wAmt,
    Proofs.FreestandingKernels.llbBytesEq_iff, decide_eq_true_eq, decide_eq_true_eq, ← UInt64.toNat_inj]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- The compiled kernel satisfies every statement of `Spec.lean`. -/
theorem kernel_meets_spec : Spec.KernelSpec :=
  ⟨validAmount, checkedAdd, checkedSub, splitBtc, hardenedBit, depthLimits,
   segwitProgram, witnessOpcode, sighashType, taprootSighashType,
   compactSizeCanonical, dualUtxo⟩

/-! ## One accepted and one rejected input per statement -/

/-- A read-only byte buffer holding `l` (zero past its end). -/
private def constBytes (l : List UInt8) : ConstBytes := ⟨fun i => l.getD i.toNat 0, ()⟩

theorem witness_validAmount :
    llbValidAmount 2100000000000000 = true ∧ llbValidAmount 2100000000000001 = false := by decide

theorem witness_checkedAdd :
    llbCheckedAddSatsOk 2000000000000000 100000000000000 = true ∧
    llbCheckedAddSatsVal 2000000000000000 100000000000000 = 2100000000000000 ∧
    llbCheckedAddSatsOk 2000000000000000 100000000000001 = false ∧
    llbCheckedAddSatsOk 18446744073709551615 1 = false := by decide

theorem witness_checkedSub :
    llbCheckedSubSatsOk 100 100 = true ∧ llbCheckedSubSatsVal 100 99 = 1 ∧
    llbCheckedSubSatsOk 100 101 = false := by decide

theorem witness_splitBtc :
    llbSatsDiv1e8 2100000000000000 = 21000000 ∧ llbSatsMod1e8 123456789 = 23456789 ∧
    llbSatsDiv1e8 18446744073709551615 = 184467440737 := by decide

theorem witness_hardenedBit :
    llbBip32IsHardened 2147483692 = true ∧ llbBip32Unharden 2147483692 = 44 ∧
    llbBip32IsHardened 44 = false := by decide

theorem witness_depthLimits :
    llbBip32BolosDepthOk 10 = true ∧ llbBip32BolosDepthOk 11 = false ∧
    llbBip32VanadiumDepthOk 16 = true ∧ llbBip32VanadiumDepthOk 17 = false := by decide

theorem witness_segwitProgram :
    llbSegwitProgramValid 0 20 = true ∧ llbSegwitProgramValid 1 32 = true ∧
    llbSegwitProgramValid 0 21 = false ∧ llbSegwitProgramValid 17 32 = false := by decide

theorem witness_witnessOpcode :
    llbWitnessOpcodeToVersion 0 = 0 ∧ llbWitnessOpcodeToVersion 81 = 1 ∧
    llbWitnessOpcodeToVersion 96 = 16 ∧ llbWitnessOpcodeToVersion 97 = 255 := by decide

theorem witness_sighashType :
    llbSighashTypeValid 1 = true ∧ llbSighashTypeValid 131 = true ∧
    llbSighashTypeValid 0 = false ∧ llbSighashTypeValid 4 = false ∧
    llbSighashTypeValid 257 = false := by decide

theorem witness_taprootSighashType :
    llbTaprootSighashValid 0 = true ∧ llbTaprootSighashValid 129 = true ∧
    llbTaprootSighashValid 4 = false ∧ llbTaprootSighashValid 128 = false := by decide

theorem witness_compactSize :
    llbVarIntPrefixIsCanonical 252 252 = true ∧ llbVarIntPrefixIsCanonical 253 253 = true ∧
    llbVarIntPrefixIsCanonical 253 252 = false ∧ llbVarIntPrefixIsCanonical 254 65535 = false := by
  decide

theorem witness_dualUtxo :
    llbCheckDualUtxo 5000 (constBytes [0, 20, 7]) 3 5000 (constBytes [0, 20, 7]) 3 = true ∧
    llbCheckDualUtxo 5000 (constBytes [0, 20, 7]) 3 5001 (constBytes [0, 20, 7]) 3 = false ∧
    llbCheckDualUtxo 5000 (constBytes [0, 20, 7]) 3 5000 (constBytes [0, 20, 8]) 3 = false ∧
    llbCheckDualUtxo 5000 (constBytes [0, 20, 7]) 3 5000 (constBytes [0, 20, 7]) 2 = false := by
  decide

end Proofs.KernelSpec

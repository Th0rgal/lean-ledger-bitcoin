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

/-! ### CompactSize reader -/

private theorem or_shift (x y k : Nat) (hx : x < 2 ^ k) : x ||| (y <<< k) = x + y * 2 ^ k := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

private theorem shl8 (b : UInt8) (s : UInt64) (hs : s.toNat ≤ 32) :
    (b.toUInt64 <<< s).toNat = b.toNat <<< s.toNat := by
  have hb := b.toNat_lt
  have hs64 : s.toNat % 64 = s.toNat := Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hs64, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  have h1 : 2 ^ s.toNat ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hs
  have h2 : b.toNat * 2 ^ s.toNat ≤ 255 * 2 ^ 32 := Nat.mul_le_mul (by omega) h1
  have h3 : 255 * 2 ^ 32 < 2 ^ 64 := by decide
  exact Nat.lt_of_le_of_lt h2 h3

private theorem or8 (a b : UInt8) :
    (a.toUInt64 ||| (b.toUInt64 <<< 8)).toNat = a.toNat + 256 * b.toNat := by
  have ha := a.toNat_lt
  rw [UInt64.toNat_or, shl8 b 8 (by decide), UInt8.toNat_toUInt64]
  have e : (8 : UInt64).toNat = 8 := rfl
  rw [e, or_shift _ _ 8 (by omega)]; omega

private theorem or32 (a b c d : UInt8) :
    (a.toUInt64 ||| (b.toUInt64 <<< 8) ||| (c.toUInt64 <<< 16) ||| (d.toUInt64 <<< 24)).toNat =
      a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_or, or8, shl8 c 16 (by decide), shl8 d 24 (by decide)]
  have e1 : (16 : UInt64).toNat = 16 := rfl
  have e2 : (24 : UInt64).toNat = 24 := rfl
  rw [e1, e2, or_shift _ _ 16 (by omega), or_shift _ _ 24 (by omega)]; omega

private theorem pack32 (n : UInt32) (raw : UInt64) (hn : n.toNat ≤ 9) (h : raw.toNat < 4294967296) :
    ((n.toUInt64 <<< 32) ||| raw).toNat = n.toNat * 4294967296 + raw.toNat := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
  have e : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [e, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.or_comm,
    show n.toNat * 2 ^ 32 = n.toNat <<< 32 from (Nat.shiftLeft_eq _ _).symm,
    or_shift _ _ 32 h, Nat.shiftLeft_eq]; omega

private theorem readCs_eq (buf : ConstBytes) (bufLen maxVal : UInt32) :
    (llbReadCompactSizeChecked buf bufLen maxVal).toNat =
      (let t := (buf.get 0).toNat
       let x2 := (buf.get 1).toNat + 256 * (buf.get 2).toNat
       let x4 := (buf.get 1).toNat + 256 * (buf.get 2).toNat + 65536 * (buf.get 3).toNat +
         16777216 * (buf.get 4).toNat
       if bufLen.toNat = 0 then 0
       else if t ≤ 252 then (if t ≤ maxVal.toNat then 4294967296 + t else 0)
       else if t = 253 then
         (if 3 ≤ bufLen.toNat ∧ 253 ≤ x2 ∧ x2 ≤ maxVal.toNat then 3 * 4294967296 + x2 else 0)
       else if t = 254 then
         (if 5 ≤ bufLen.toNat ∧ 65536 ≤ x4 ∧ x4 ≤ maxVal.toNat then 5 * 4294967296 + x4 else 0)
       else 0) := by
  unfold llbReadCompactSizeChecked readU8
  generalize buf.get 0 = tag
  generalize buf.get 1 = b1
  generalize buf.get 2 = b2
  generalize buf.get 3 = b3
  generalize buf.get 4 = b4
  have htl := tag.toNat_lt
  have h1l := b1.toNat_lt; have h2l := b2.toNat_lt; have h3l := b3.toNat_lt; have h4l := b4.toNat_lt
  have hml := maxVal.toNat_lt
  have hmx : (maxVal.toUInt64).toNat = maxVal.toNat := UInt32.toNat_toUInt64 maxVal
  have z0 : (0 : UInt64).toNat = 0 := rfl
  dsimp only
  by_cases h0 : bufLen = 0
  · subst h0; rfl
  · have h0' : ¬ bufLen.toNat = 0 := fun h => h0 (UInt32.toNat_inj.mp h)
    rw [ite_eq_right (by simpa using h0), ite_eq_right h0']
    by_cases c1 : tag ≤ 0xFC
    · have c1' : tag.toNat ≤ 252 := UInt8.le_iff_toNat_le.mp c1
      have hff : ¬ tag = 0xFF := by
        intro h; subst h; exact absurd c1' (by decide)
      have hlen : ¬ bufLen < 1 := by
        intro h; have := UInt32.lt_iff_toNat_lt.mp h
        have e : (1 : UInt32).toNat = 1 := rfl
        omega
      have hcan : llbVarIntPrefixIsCanonical tag tag.toUInt64 = true :=
        (compactSizeCanonical tag tag.toUInt64).mpr
          (Or.inl ⟨by rw [UInt8.toNat_toUInt64]; exact c1', by rw [UInt8.toNat_toUInt64]⟩)
      simp only [c1, decide_true, ↓reduceIte, hlen, hff, decide_false, Bool.or_false,
        Bool.false_eq_true, hcan, Bool.true_and, decide_eq_true_eq, c1', UInt64.le_iff_toNat_le,
        hmx, UInt8.toNat_toUInt64]
      by_cases hm : tag.toNat ≤ maxVal.toNat
      · rw [ite_eq_left hm, ite_eq_left hm]
        have e : (1 : UInt32).toNat ≤ 9 := by decide
        rw [pack32 1 tag.toUInt64 e (by rw [UInt8.toNat_toUInt64]; omega), UInt8.toNat_toUInt64]
        rfl
      · rw [ite_eq_right hm, ite_eq_right hm]; rfl
    · have c1' : ¬ tag.toNat ≤ 252 := fun h => c1 (UInt8.le_iff_toNat_le.mpr h)
      have e3 : (3 : UInt32).toNat = 3 := rfl
      have e5 : (5 : UInt32).toNat = 5 := rfl
      by_cases c2 : tag = 0xFD
      · subst c2
        have hraw := or8 b1 b2
        have e253 : (0xFD : UInt8).toNat = 253 := rfl
        have hcan := compactSizeCanonical 0xFD (b1.toUInt64 ||| (b2.toUInt64 <<< 8))
        rw [hraw, e253] at hcan
        have hcan' : llbVarIntPrefixIsCanonical 0xFD (b1.toUInt64 ||| (b2.toUInt64 <<< 8)) = true ↔
            253 ≤ b1.toNat + 256 * b2.toNat := by
          rw [hcan]; constructor
          · intro h; omega
          · intro h; exact Or.inr (Or.inl ⟨h, by omega, rfl⟩)
        simp only [show ¬ ((0xFD : UInt8) ≤ 0xFC) from by decide,
          show ¬ ((0xFD : UInt8) = 0xFF) from by decide, decide_false, decide_true,
          Bool.false_eq_true, ↓reduceIte, Bool.or_false, decide_eq_true_eq, Bool.and_eq_true, hcan',
          UInt64.le_iff_toNat_le, hmx, hraw, e253, UInt32.lt_iff_toNat_lt, e3,
          show ¬ ((253 : Nat) ≤ 252) from by decide]
        by_cases hl : bufLen.toNat < 3
        · rw [ite_eq_left hl, ite_eq_right (by omega)]; rfl
        · rw [ite_eq_right hl]
          by_cases hc : 253 ≤ b1.toNat + 256 * b2.toNat ∧ b1.toNat + 256 * b2.toNat ≤ maxVal.toNat
          · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc⟩,
              pack32 3 _ (by decide) (by rw [hraw]; omega), hraw, e3]
          · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.2)]; rfl
      · by_cases c3 : tag = 0xFE
        · subst c3
          have hraw := or32 b1 b2 b3 b4
          have e254 : (0xFE : UInt8).toNat = 254 := rfl
          have hcan := compactSizeCanonical 0xFE
            (b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24))
          rw [hraw, e254] at hcan
          have hcan' : llbVarIntPrefixIsCanonical 0xFE
              (b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24)) = true ↔
              65536 ≤ b1.toNat + 256 * b2.toNat + 65536 * b3.toNat + 16777216 * b4.toNat := by
            rw [hcan]; constructor
            · intro h; omega
            · intro h; exact Or.inr (Or.inr (Or.inl ⟨h, by omega, rfl⟩))
          simp only [show ¬ ((0xFE : UInt8) ≤ 0xFC) from by decide,
            show ¬ ((0xFE : UInt8) = 0xFF) from by decide, show ¬ ((0xFE : UInt8) = 0xFD) from by decide,
            decide_false, decide_true,
            Bool.false_eq_true, ↓reduceIte, Bool.or_false, decide_eq_true_eq, Bool.and_eq_true, hcan',
            UInt64.le_iff_toNat_le, hmx, hraw, e254, UInt32.lt_iff_toNat_lt, e5,
            show ¬ ((254 : Nat) ≤ 252) from by decide, show ¬ ((254 : Nat) = 253) from by decide]
          by_cases hl : bufLen.toNat < 5
          · rw [ite_eq_left hl, ite_eq_right (by omega)]; rfl
          · rw [ite_eq_right hl]
            by_cases hc : 65536 ≤ b1.toNat + 256 * b2.toNat + 65536 * b3.toNat + 16777216 * b4.toNat ∧
                b1.toNat + 256 * b2.toNat + 65536 * b3.toNat + 16777216 * b4.toNat ≤ maxVal.toNat
            · rw [ite_eq_left hc, ite_eq_left ⟨by omega, hc⟩,
                pack32 5 _ (by decide) (by rw [hraw]; omega), hraw, e5]
            · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.2)]; rfl
        · have hff : tag = 0xFF := by
            apply UInt8.toNat_inj.mp
            have n2 : ¬ tag.toNat = 253 := fun h => c2 (UInt8.toNat_inj.mp h)
            have n3 : ¬ tag.toNat = 254 := fun h => c3 (UInt8.toNat_inj.mp h)
            have e : (0xFF : UInt8).toNat = 255 := rfl
            omega
          subst hff
          simp only [eq_self, decide_true, Bool.or_true, ↓reduceIte,
            show (0xFF : UInt8).toNat = 255 from rfl, show ¬ ((255 : Nat) ≤ 252) from by decide,
            show ¬ ((255 : Nat) = 253) from by decide, show ¬ ((255 : Nat) = 254) from by decide]
          rfl

private theorem pfx_cons {α} (a b : α) (l m : List α) : a :: l <+: b :: m ↔ a = b ∧ l <+: m := by
  constructor
  · rintro ⟨t, h⟩
    rw [List.cons_append] at h
    exact ⟨(List.cons.inj h).1, t, (List.cons.inj h).2⟩
  · rintro ⟨rfl, t, h⟩
    exact ⟨t, by rw [List.cons_append, h]⟩

private theorem pfx_iff_get {α} (l : List α) : ∀ L : List α,
    l <+: L ↔ ∀ i (h : i < l.length), L[i]? = some l[i] := by
  induction l with
  | nil => intro L; exact ⟨fun _ i h => absurd h (Nat.not_lt_zero i), fun _ => List.nil_prefix⟩
  | cons a l ih =>
    intro L
    cases L with
    | nil =>
      constructor
      · rintro ⟨t, h⟩; cases h
      · intro h; cases h 0 (Nat.zero_lt_succ _)
    | cons b m =>
      rw [pfx_cons, ih m]
      constructor
      · rintro ⟨rfl, h⟩ i hi
        cases i with
        | zero => rfl
        | succ k => exact h k (Nat.lt_of_succ_lt_succ hi)
      · intro h
        refine ⟨(Option.some.inj (h 0 (Nat.zero_lt_succ _))).symm, ?_⟩
        intro i hi
        exact h (i + 1) (Nat.succ_lt_succ hi)

private theorem prefix_bytes (l : List Nat) (b : ConstBytes) (n : Nat) :
    l <+: Spec.bytes b n ↔
      ∀ i (h : i < l.length), i < n ∧ (b.get (UInt32.ofNat i)).toNat = l[i] := by
  rw [pfx_iff_get]
  unfold Spec.bytes
  constructor
  · intro h i hi
    have hh := h i hi
    by_cases hn : i < n
    · rw [List.getElem?_map, List.getElem?_range hn] at hh
      exact ⟨hn, Option.some.inj hh⟩
    · rw [List.getElem?_eq_none (by rw [List.length_map, List.length_range]; exact Nat.le_of_not_lt hn)] at hh
      cases hh
  · intro h i hi
    obtain ⟨hn, e⟩ := h i hi
    rw [List.getElem?_map, List.getElem?_range hn, ← e]; rfl

private theorem prefix1 (a : Nat) (b : ConstBytes) (n : Nat) :
    [a] <+: Spec.bytes b n ↔ 1 ≤ n ∧ (b.get 0).toNat = a := by
  rw [prefix_bytes]
  constructor
  · intro h
    have h0 := h 0 (Nat.lt_of_sub_eq_succ rfl)
    exact ⟨h0.1, h0.2⟩
  · rintro ⟨hn, e0⟩ i hi
    match i, hi with
    | 0, _ => exact ⟨hn, e0⟩

private theorem prefix3 (a0 a1 a2 : Nat) (b : ConstBytes) (n : Nat) :
    [a0, a1, a2] <+: Spec.bytes b n ↔
      3 ≤ n ∧ (b.get 0).toNat = a0 ∧ (b.get 1).toNat = a1 ∧ (b.get 2).toNat = a2 := by
  rw [prefix_bytes]
  constructor
  · intro h
    have h0 := h 0 (Nat.lt_of_sub_eq_succ rfl); have h1 := h 1 (Nat.lt_of_sub_eq_succ rfl); have h2 := h 2 (Nat.lt_of_sub_eq_succ rfl)
    exact ⟨h2.1, h0.2, h1.2, h2.2⟩
  · rintro ⟨hn, e0, e1, e2⟩ i hi
    match i, hi with
    | 0, _ => exact ⟨by omega, e0⟩
    | 1, _ => exact ⟨by omega, e1⟩
    | 2, _ => exact ⟨by omega, e2⟩

private theorem prefix5 (a0 a1 a2 a3 a4 : Nat) (b : ConstBytes) (n : Nat) :
    [a0, a1, a2, a3, a4] <+: Spec.bytes b n ↔
      5 ≤ n ∧ (b.get 0).toNat = a0 ∧ (b.get 1).toNat = a1 ∧ (b.get 2).toNat = a2 ∧
        (b.get 3).toNat = a3 ∧ (b.get 4).toNat = a4 := by
  rw [prefix_bytes]
  constructor
  · intro h
    have h0 := h 0 (Nat.lt_of_sub_eq_succ rfl); have h1 := h 1 (Nat.lt_of_sub_eq_succ rfl); have h2 := h 2 (Nat.lt_of_sub_eq_succ rfl)
    have h3 := h 3 (Nat.lt_of_sub_eq_succ rfl); have h4 := h 4 (Nat.lt_of_sub_eq_succ rfl)
    exact ⟨h4.1, h0.2, h1.2, h2.2, h3.2, h4.2⟩
  · rintro ⟨hn, e0, e1, e2, e3, e4⟩ i hi
    match i, hi with
    | 0, _ => exact ⟨by omega, e0⟩
    | 1, _ => exact ⟨by omega, e1⟩
    | 2, _ => exact ⟨by omega, e2⟩
    | 3, _ => exact ⟨by omega, e3⟩
    | 4, _ => exact ⟨by omega, e4⟩

private theorem csA (buf : ConstBytes) (bufLen maxVal : UInt32) :
    ∀ v : Nat, v ≤ maxVal.toNat → Spec.compactSize v <+: Spec.bytes buf bufLen.toNat →
      (llbReadCompactSizeChecked buf bufLen maxVal).toNat = (Spec.compactSize v).length * 2 ^ 32 + v := by
  have hb0 := (buf.get 0).toNat_lt; have hb1 := (buf.get 1).toNat_lt
  have hb2 := (buf.get 2).toNat_lt; have hb3 := (buf.get 3).toNat_lt
  have hb4 := (buf.get 4).toNat_lt
  have hml := maxVal.toNat_lt
  rw [readCs_eq]
  dsimp only
  intro v hv hpre
  unfold Spec.compactSize at hpre ⊢
  by_cases c1 : v < 253
  · rw [ite_eq_left c1] at hpre ⊢
    obtain ⟨hn, e0⟩ := (prefix1 _ _ _).mp hpre
    rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega), e0,
      show [v].length = 1 from rfl]
  · rw [ite_eq_right c1] at hpre ⊢
    by_cases c2 : v < 65536
    · rw [ite_eq_left c2] at hpre ⊢
      obtain ⟨hn, e0, e1, e2⟩ := (prefix3 _ _ _ _ _).mp hpre
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left e0,
        ite_eq_left ⟨hn, by omega, by omega⟩, show [253, v % 256, v / 256].length = 3 from rfl]
      omega
    · rw [ite_eq_right c2, ite_eq_left (show v < 4294967296 by omega)] at hpre ⊢
      obtain ⟨hn, e0, e1, e2, e3, e4⟩ := (prefix5 _ _ _ _ _ _ _).mp hpre
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left e0, ite_eq_left ⟨hn, by omega, by omega⟩,
        show [254, v % 256, v / 256 % 256, v / 65536 % 256, v / 16777216].length = 5 from rfl]
      omega

private theorem csB (buf : ConstBytes) (bufLen maxVal : UInt32) :
    (¬ ∃ v : Nat, v ≤ maxVal.toNat ∧ Spec.compactSize v <+: Spec.bytes buf bufLen.toNat) →
      (llbReadCompactSizeChecked buf bufLen maxVal).toNat = 0 := by
  have hb0 := (buf.get 0).toNat_lt; have hb1 := (buf.get 1).toNat_lt
  have hb2 := (buf.get 2).toNat_lt; have hb3 := (buf.get 3).toNat_lt
  have hb4 := (buf.get 4).toNat_lt
  have hml := maxVal.toNat_lt
  rw [readCs_eq]
  dsimp only
  intro hno
  by_cases h0 : bufLen.toNat = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0]
    by_cases c1 : (buf.get 0).toNat ≤ 252
    · rw [ite_eq_left c1]
      by_cases hm : (buf.get 0).toNat ≤ maxVal.toNat
      · refine absurd ⟨(buf.get 0).toNat, hm, ?_⟩ hno
        unfold Spec.compactSize
        rw [ite_eq_left (by omega)]
        exact (prefix1 _ _ _).mpr ⟨by omega, rfl⟩
      · rw [ite_eq_right hm]
    · rw [ite_eq_right c1]
      by_cases c2 : (buf.get 0).toNat = 253
      · rw [ite_eq_left c2]
        by_cases hc : 3 ≤ bufLen.toNat ∧ 253 ≤ (buf.get 1).toNat + 256 * (buf.get 2).toNat ∧
            (buf.get 1).toNat + 256 * (buf.get 2).toNat ≤ maxVal.toNat
        · have hc1 := hc.1; have hc2 := hc.2.1; have hc3 := hc.2.2
          refine absurd ⟨(buf.get 1).toNat + 256 * (buf.get 2).toNat, hc.2.2, ?_⟩ hno
          unfold Spec.compactSize
          rw [ite_eq_right (by omega), ite_eq_left (by omega)]
          exact (prefix3 _ _ _ _ _).mpr ⟨hc.1, c2, by omega, by omega⟩
        · rw [ite_eq_right hc]
      · rw [ite_eq_right c2]
        by_cases c3 : (buf.get 0).toNat = 254
        · rw [ite_eq_left c3]
          by_cases hc : 5 ≤ bufLen.toNat ∧
              65536 ≤ (buf.get 1).toNat + 256 * (buf.get 2).toNat + 65536 * (buf.get 3).toNat +
                16777216 * (buf.get 4).toNat ∧
              (buf.get 1).toNat + 256 * (buf.get 2).toNat + 65536 * (buf.get 3).toNat +
                16777216 * (buf.get 4).toNat ≤ maxVal.toNat
          · have hc1 := hc.1; have hc2 := hc.2.1; have hc3 := hc.2.2
            refine absurd ⟨(buf.get 1).toNat + 256 * (buf.get 2).toNat +
              65536 * (buf.get 3).toNat + 16777216 * (buf.get 4).toNat, hc.2.2, ?_⟩ hno
            unfold Spec.compactSize
            rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
            exact (prefix5 _ _ _ _ _ _ _).mpr ⟨hc.1, c3, by omega, by omega, by omega, by omega⟩
          · rw [ite_eq_right hc]
        · rw [ite_eq_right c3]

theorem compactSizeRead : Spec.CompactSizeRead :=
  fun buf bufLen maxVal => ⟨csA buf bufLen maxVal, csB buf bufLen maxVal⟩

/-- The compiled kernel satisfies every statement of `Spec.lean`. -/
theorem kernel_meets_spec : Spec.KernelSpec :=
  ⟨validAmount, checkedAdd, checkedSub, splitBtc, hardenedBit, depthLimits,
   segwitProgram, witnessOpcode, sighashType, taprootSighashType,
   compactSizeCanonical, dualUtxo, compactSizeRead⟩

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

theorem witness_compactSizeRead :
    (llbReadCompactSizeChecked (constBytes [0xFD, 0x2C, 0x01]) 3 1000).toNat = 3 * 2 ^ 32 + 300 ∧
    (llbReadCompactSizeChecked (constBytes [0xFD, 0x2C, 0x00]) 3 1000).toNat = 0 ∧
    (llbReadCompactSizeChecked (constBytes [0xFD, 0x2C, 0x01]) 2 1000).toNat = 0 ∧
    (llbReadCompactSizeChecked (constBytes [0xFD, 0x2C, 0x01]) 3 299).toNat = 0 := by
  decide

end Proofs.KernelSpec

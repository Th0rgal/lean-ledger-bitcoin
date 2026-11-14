import Spec
import Proofs.FreestandingKernels

/-!
# Proofs of `Spec.lean`

One theorem per statement of `Spec.lean`, then `kernel_meets_spec`, then one accepted and
one rejected concrete input per statement (so no statement holds for an empty reason).

Some proofs reuse lemmas of `Proofs/FreestandingKernels.lean` that are themselves stated on
the kernel functions: `llbSatsDiv1e8_eq` and `llbSatsMod1e8_eq` (`SplitBtc`), `llbBytesEq_iff`
(`DualUtxo`), `bip32TailClear_iff` (`Bip32ExportPath`), `largestPow2LtU32_eq` (`MerkleSplit`) and
`llbPsbtLocktime_eq_determineLocktime` (`PsbtLocktime`) and `forRangeU64_eq_foldl`
(`SortFixedBytes`). Every other proof unfolds the kernel function directly.
-/

namespace Proofs.KernelSpec

open BitcoinLedger.FreestandingKernels

/-- `omega`, after splitting `↔` and `∧` by hand: `omega` itself proves an `↔` goal by
    contradiction, which would bring in `Classical.choice`. -/
local macro "omega_split" : tactic =>
  `(tactic| ((repeat' (first | apply Iff.intro | apply And.intro | intro _)) <;> omega))

/-- `omega`, after rewriting negated conjunctions (which `omega` handles with
    `Classical.choice`) into disjunctions. -/
local macro "omega_nc" : tactic =>
  `(tactic| ((repeat' (first | apply Iff.intro | apply And.intro | intro _)) <;>
     first
       | contradiction
       | trivial
       | (apply Decidable.byContradiction; intro _;
          (try simp only [not_or, Decidable.not_and_iff_not_or_not, Nat.not_lt, Nat.not_le] at *);
          omega)))

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

/-! ### BIP-32 export path -/

private theorem isH (p : UInt32) : llbBip32IsHardened p = decide (2147483648 ≤ p.toNat) :=
  Bool.eq_iff_iff.mpr (by rw [decide_eq_true_eq]; exact (hardenedBit p).1)

private theorem unH (p : UInt32) : (llbBip32Unharden p).toNat = p.toNat % 2147483648 :=
  (hardenedBit p).2

private theorem prefixOk_iff (p0 p1 p2 p3 : UInt32) (len : UInt8) (coin : UInt32) (tail : Bool) :
    llbBip32PubkeyExportPrefixOk p0 p1 p2 p3 len coin tail = true ↔
      (len.toNat = 2 ∧ p0.toNat = 2147483648 + 4541509 ∧ p1.toNat = 2147483648 + 1112098098) ∨
      (3 ≤ len.toNat ∧ tail = true ∧ p1.toNat = 2147483648 + coin.toNat ∧
        2147483648 ≤ p2.toNat ∧ p2.toNat ≤ 2147483648 + 100 ∧
        ((p0.toNat = 2147483648 + 44 ∨ p0.toNat = 2147483648 + 49 ∨ p0.toNat = 2147483648 + 84 ∨
          p0.toNat = 2147483648 + 86 ∨ p0.toNat = 2147483648 + 87 ∨ p0.toNat = 2147483648 + 45) ∨
         (p0.toNat = 2147483648 + 48 ∧ 4 ≤ len.toNat ∧
           (p3.toNat = 2147483648 + 1 ∨ p3.toNat = 2147483648 + 2)))) := by
  have h0 := p0.toNat_lt; have h1 := p1.toNat_lt; have h2 := p2.toNat_lt; have h3 := p3.toNat_lt
  have hc := coin.toNat_lt
  unfold llbBip32PubkeyExportPrefixOk llbBip32StandardPurposeOk
  simp only [isH, ← UInt32.toNat_inj, ← UInt8.toNat_inj, UInt32.lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt,
    UInt8.le_iff_toNat_le, unH]
  have e2 : (2 : UInt8).toNat = 2 := rfl
  have e3 : (3 : UInt8).toNat = 3 := rfl
  have e4 : (4 : UInt8).toNat = 4 := rfl
  have a1 : (0x80454C45 : UInt32).toNat = 2147483648 + 4541509 := rfl
  have a2 : (0xC2494532 : UInt32).toNat = 2147483648 + 1112098098 := rfl
  have n100 : (100 : UInt32).toNat = 100 := rfl
  have n48 : (48 : UInt32).toNat = 48 := rfl
  have n44 : (44 : UInt32).toNat = 44 := rfl
  have n49 : (49 : UInt32).toNat = 49 := rfl
  have n84 : (84 : UInt32).toNat = 84 := rfl
  have n86 : (86 : UInt32).toNat = 86 := rfl
  have n87 : (87 : UInt32).toNat = 87 := rfl
  have n45 : (45 : UInt32).toNat = 45 := rfl
  have n1 : (1 : UInt32).toNat = 1 := rfl
  have n2 : (2 : UInt32).toNat = 2 := rfl
  simp only [e2, e3, e4, a1, a2, n100, n48, n44, n49, n84, n86, n87, n45, n1, n2]
  cases tail <;>
  simp only [Bool.not_true, Bool.not_false, Bool.or_true, Bool.or_false,
    Bool.false_eq_true, false_and, and_false, or_false, true_and] <;>
  (repeat' split) <;>
  (try simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Bool.false_eq_true, not_true_eq_false,
    Bool.not_eq_true', not_or, Decidable.not_and_iff_not_or_not,
    Decidable.not_not, Nat.not_lt, Nat.not_le] at *) <;>
  omega_nc

private theorem exportCore (path : ConstU32s) (len : UInt8) (coin : UInt32) :
    llbBip32CheckExportPath path len coin = true ↔
      len.toNat ≤ 10 ∧
      ((len.toNat = 2 ∧ (path.get 0).toNat = 2147483648 + 4541509 ∧
          (path.get 1).toNat = 2147483648 + 1112098098) ∨
       (3 ≤ len.toNat ∧ (path.get 1).toNat = 2147483648 + coin.toNat ∧
          2147483648 ≤ (path.get 2).toNat ∧ (path.get 2).toNat ≤ 2147483648 + 100 ∧
          ((((path.get 0).toNat = 2147483648 + 44 ∨ (path.get 0).toNat = 2147483648 + 49 ∨
              (path.get 0).toNat = 2147483648 + 84 ∨ (path.get 0).toNat = 2147483648 + 86 ∨
              (path.get 0).toNat = 2147483648 + 87 ∨ (path.get 0).toNat = 2147483648 + 45) ∧
             bip32TailClear path 3 len.toUInt32 = true) ∨
           ((path.get 0).toNat = 2147483648 + 48 ∧ 4 ≤ len.toNat ∧
             ((path.get 3).toNat = 2147483648 + 1 ∨ (path.get 3).toNat = 2147483648 + 2) ∧
             bip32TailClear path 4 len.toUInt32 = true)))) := by
  have hg0 := (path.get 0).toNat_lt; have hg1 := (path.get 1).toNat_lt
  have hg2 := (path.get 2).toNat_lt; have hg3 := (path.get 3).toNat_lt
  have hc := coin.toNat_lt
  have hl := len.toNat_lt
  unfold llbBip32CheckExportPath readU32
  by_cases hd : len.toNat ≤ 10
  · have hd' : llbBip32BolosDepthOk len = true := (depthLimits len).1.mpr hd
    simp only [hd', Bool.not_true, Bool.false_eq_true, ↓reduceIte, UInt32.lt_iff_toNat_lt,
      UInt32.le_iff_toNat_le, UInt8.toNat_toUInt32, ← UInt32.toNat_inj, unH,
      show (0 : UInt32).toNat = 0 from rfl, show (1 : UInt32).toNat = 1 from rfl,
      show (2 : UInt32).toNat = 2 from rfl, show (3 : UInt32).toNat = 3 from rfl,
      show (48 : UInt32).toNat = 48 from rfl]
    rw [prefixOk_iff]
    have z0 : (0 : UInt32).toNat = 0 := rfl
    by_cases h3 : 3 ≤ len.toNat
    · have i0 : 0 < len.toNat := by omega
      have i1 : 1 < len.toNat := by omega
      have i2 : 2 < len.toNat := by omega
      simp only [i0, i1, i2, h3, decide_true, ↓reduceIte, Bool.and_true]
      by_cases h48 : (path.get 0).toNat % 2147483648 = 48
      · simp only [h48, decide_true, ↓reduceIte]
        generalize bip32TailClear path 3 len.toUInt32 = t3
        generalize bip32TailClear path 4 len.toUInt32 = t4
        by_cases h4 : 3 < len.toNat
        · simp only [h4, decide_true, ↓reduceIte]
          cases t3 <;> cases t4 <;>
            simp only [Bool.false_eq_true, and_false, false_and, or_false, false_or, and_true, true_and] <;>
            omega_nc
        · simp only [h4, decide_false, Bool.false_eq_true, ↓reduceIte, z0]
          cases t3 <;> cases t4 <;>
            simp only [Bool.false_eq_true, and_false, false_and, or_false, false_or, and_true, true_and] <;>
            omega_nc
      · simp only [h48, decide_false, Bool.false_eq_true, ↓reduceIte]
        generalize bip32TailClear path 3 len.toUInt32 = t3
        generalize bip32TailClear path 4 len.toUInt32 = t4
        generalize (if decide (3 < len.toNat) = true then path.get 3 else 0) = q3
        cases t3 <;> cases t4 <;>
          simp only [Bool.false_eq_true, and_false, false_and, or_false, false_or, and_true, true_and] <;>
          omega_nc
    · generalize bip32TailClear path _ len.toUInt32 = t
      generalize bip32TailClear path 3 len.toUInt32 = t3
      generalize bip32TailClear path 4 len.toUInt32 = t4
      generalize (if decide (3 < len.toNat) = true then path.get 3 else 0) = q3
      have i2 : ¬ 2 < len.toNat := by omega
      simp only [i2, decide_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : len.toNat = 2
      · have i0 : 0 < len.toNat := by omega
        have i1 : 1 < len.toNat := by omega
        simp only [i0, i1, decide_true, ↓reduceIte]
        omega_nc
      · omega_nc
  · have hd' : llbBip32BolosDepthOk len = false := by
      cases h : llbBip32BolosDepthOk len
      · rfl
      · exact absurd ((depthLimits len).1.mp h) hd
    simp only [hd', Bool.not_false, ↓reduceIte, Bool.false_eq_true, false_iff]
    intro h; exact hd h.1

private theorem words_length (b : ConstU32s) (n : Nat) : (Spec.words b n).length = n := by
  unfold Spec.words; rw [List.length_map, List.length_range]

private theorem words_succ3 (b : ConstU32s) (k : Nat) :
    Spec.words b (k + 3) = (b.get 0).toNat :: (b.get 1).toNat :: (b.get 2).toNat ::
      (List.range' 3 k).map (fun i => (b.get (UInt32.ofNat i)).toNat) := by
  unfold Spec.words; rw [List.range_eq_range']; rfl

private theorem words_succ4 (b : ConstU32s) (k : Nat) :
    Spec.words b (k + 4) = (b.get 0).toNat :: (b.get 1).toNat :: (b.get 2).toNat ::
      (b.get 3).toNat :: (List.range' 4 k).map (fun i => (b.get (UInt32.ofNat i)).toNat) := by
  unfold Spec.words; rw [List.range_eq_range']; rfl

private theorem tail_iff (f : Nat → Nat) (s k N : Nat) :
    (∀ x ∈ (List.range' s k).map f, x < N) ↔ ∀ j, s ≤ j → j < k + s → f j < N := by
  constructor
  · intro h j h1 h2
    exact h _ (List.mem_map.mpr ⟨j, List.mem_range'_1.mpr ⟨h1, by omega⟩, rfl⟩)
  · intro h x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have hh := List.mem_range'_1.mp hj
    exact h j hh.1 (by omega)

private theorem tailClear_nat (path : ConstU32s) (lo : UInt32) (len : UInt8) :
    bip32TailClear path lo len.toUInt32 = true ↔
      ∀ j, lo.toNat ≤ j → j < len.toNat → (path.get (UInt32.ofNat j)).toNat < 2147483648 := by
  have hl := len.toNat_lt
  rw [Proofs.FreestandingKernels.bip32TailClear_iff]
  constructor
  · intro h j h1 h2
    have hj : (UInt32.ofNat j).toNat = j := by
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    have hh := h (UInt32.ofNat j) (UInt32.le_iff_toNat_le.mpr (by rw [hj]; exact h1))
      (UInt32.lt_iff_toNat_lt.mpr (by rw [hj, UInt8.toNat_toUInt32]; exact h2))
    rw [isH] at hh
    have := of_decide_eq_false hh
    unfold readU32 at this
    omega
  · intro h i h1 h2
    have hh := h i.toNat (UInt32.le_iff_toNat_le.mp h1)
      (by have := UInt32.lt_iff_toNat_lt.mp h2; rwa [UInt8.toNat_toUInt32] at this)
    rw [u32_ofNat_toNat] at hh
    rw [isH]; unfold readU32
    exact decide_eq_false (by omega)

private theorem exportPath_iff (path : ConstU32s) (n coin : Nat) :
    Spec.ExportPath coin (Spec.words path n) ↔
      ((n = 2 ∧ (path.get 0).toNat = 2147483648 + 4541509 ∧
          (path.get 1).toNat = 2147483648 + 1112098098) ∨
       (3 ≤ n ∧ (path.get 1).toNat = 2147483648 + coin ∧
          2147483648 ≤ (path.get 2).toNat ∧ (path.get 2).toNat ≤ 2147483648 + 100 ∧
          ((((path.get 0).toNat = 2147483648 + 44 ∨ (path.get 0).toNat = 2147483648 + 49 ∨
              (path.get 0).toNat = 2147483648 + 84 ∨ (path.get 0).toNat = 2147483648 + 86 ∨
              (path.get 0).toNat = 2147483648 + 87 ∨ (path.get 0).toNat = 2147483648 + 45) ∧
             (∀ j, 3 ≤ j → j < n → (path.get (UInt32.ofNat j)).toNat < 2147483648)) ∨
           ((path.get 0).toNat = 2147483648 + 48 ∧ 4 ≤ n ∧
             ((path.get 3).toNat = 2147483648 + 1 ∨ (path.get 3).toNat = 2147483648 + 2) ∧
             (∀ j, 4 ≤ j → j < n → (path.get (UInt32.ofNat j)).toNat < 2147483648))))) := by
  unfold Spec.ExportPath
  constructor
  · rintro (hp | ⟨purpose, account, tail, hp, hmem, hacc, htail⟩ |
      ⟨account, st, tail, hp, hacc, hst, htail⟩)
    · have hn : n = 2 := by
        have := congrArg List.length hp
        rwa [words_length] at this
      subst hn
      have hp' : [(path.get 0).toNat, (path.get 1).toNat] =
          [Spec.hardened 4541509, Spec.hardened 1112098098] := hp
      obtain ⟨e0, hp'⟩ := List.cons.inj hp'
      obtain ⟨e1, _⟩ := List.cons.inj hp'
      exact Or.inl ⟨rfl, e0, e1⟩
    · have hn : n = tail.length + 3 := by
        have := congrArg List.length hp
        rwa [words_length] at this
      subst hn
      rw [words_succ3] at hp
      obtain ⟨e0, hp⟩ := List.cons.inj hp
      obtain ⟨e1, hp⟩ := List.cons.inj hp
      obtain ⟨e2, hp⟩ := List.cons.inj hp
      unfold Spec.hardened at e0 e1 e2
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rw [← hp, tail_iff] at htail
      exact Or.inr ⟨by omega, e1, by omega, by omega, Or.inl ⟨by omega, htail⟩⟩
    · have hn : n = tail.length + 4 := by
        have := congrArg List.length hp
        rwa [words_length] at this
      subst hn
      rw [words_succ4] at hp
      obtain ⟨e0, hp⟩ := List.cons.inj hp
      obtain ⟨e1, hp⟩ := List.cons.inj hp
      obtain ⟨e2, hp⟩ := List.cons.inj hp
      obtain ⟨e3, hp⟩ := List.cons.inj hp
      unfold Spec.hardened at e0 e1 e2 e3
      rw [← hp, tail_iff] at htail
      exact Or.inr ⟨by omega, e1, by omega, by omega, Or.inr ⟨e0, by omega, by omega, htail⟩⟩
  · rintro (⟨h2, e0, e1⟩ | ⟨h3, e1, h2a, h2b, (⟨hstd, hT⟩ | ⟨h48, h4, hst, hT⟩)⟩)
    · subst h2
      refine Or.inl ?_
      show [(path.get 0).toNat, (path.get 1).toNat] = _
      rw [e0, e1]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      have hacc : (path.get 2).toNat - 2147483648 ≤ 100 := by omega
      refine Or.inr (Or.inl ⟨(path.get 0).toNat - 2147483648, (path.get 2).toNat - 2147483648,
        (List.range' 3 k).map (fun i => (path.get (UInt32.ofNat i)).toNat), ?_, ?_, hacc,
        (tail_iff (fun i => (path.get (UInt32.ofNat i)).toNat) 3 k 2147483648).mpr hT⟩)
      · rw [words_succ3]; unfold Spec.hardened
        have a0 : 2147483648 + ((path.get 0).toNat - 2147483648) = (path.get 0).toNat := by omega
        have a2 : 2147483648 + ((path.get 2).toNat - 2147483648) = (path.get 2).toNat :=
          Nat.add_sub_of_le h2a
        rw [a0, a2, ← e1]
      · simp only [List.mem_cons, List.mem_nil_iff, or_false]; omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have hacc : (path.get 2).toNat - 2147483648 ≤ 100 := by omega
      have hst' : (path.get 3).toNat - 2147483648 = 1 ∨ (path.get 3).toNat - 2147483648 = 2 := by
        omega
      refine Or.inr (Or.inr ⟨(path.get 2).toNat - 2147483648, (path.get 3).toNat - 2147483648,
        (List.range' 4 k).map (fun i => (path.get (UInt32.ofNat i)).toNat), ?_, hacc, hst',
        (tail_iff (fun i => (path.get (UInt32.ofNat i)).toNat) 4 k 2147483648).mpr hT⟩)
      rw [words_succ4]; unfold Spec.hardened
      have a2 : 2147483648 + ((path.get 2).toNat - 2147483648) = (path.get 2).toNat :=
        Nat.add_sub_of_le h2a
      have h3a : 2147483648 ≤ (path.get 3).toNat := by omega
      have a3 : 2147483648 + ((path.get 3).toNat - 2147483648) = (path.get 3).toNat :=
        Nat.add_sub_of_le h3a
      rw [a2, a3, ← e1, ← h48]

theorem bip32ExportPath : Spec.Bip32ExportPath := by
  intro path len coin
  rw [exportCore, exportPath_iff, tailClear_nat, tailClear_nat]
  exact Iff.rfl

/-! ### Merkle descent -/

private theorem go_sandwich (n e : Nat) (hlo : 2 ^ e < n) (hhi : n ≤ 2 * 2 ^ e) :
    ∀ fuel d, d ≤ e → e - d ≤ fuel →
      InternalSpec.MerkleProtocol.largestPow2LtGo n fuel (2 ^ d) = 2 ^ e := by
  intro fuel
  induction fuel with
  | zero =>
    intro d h1 h2
    have : d = e := by omega
    subst this; rfl
  | succ f ih =>
    intro d h1 h2
    unfold InternalSpec.MerkleProtocol.largestPow2LtGo
    by_cases h : 2 ^ d * 2 < n
    · rw [ite_eq_left h]
      have hde : d < e := by
        apply Nat.lt_of_le_of_ne h1
        intro hd; subst hd; omega
      rw [← Nat.pow_succ]
      exact ih (d + 1) hde (by omega)
    · rw [ite_eq_right h]
      have hde : d = e := by
        apply Decidable.byContradiction
        intro hne
        have hlt : d + 1 ≤ e := by omega
        have hp : 2 ^ (d + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) hlt
        rw [Nat.pow_succ] at hp
        omega
      rw [hde]

theorem merkleSplit : Spec.MerkleSplit := by
  intro s e hlo hhi
  have hp : 0 < 2 ^ e := Nat.pow_pos (by decide)
  rw [Proofs.FreestandingKernels.largestPow2LtU32_eq s (by omega)]
  unfold InternalSpec.MerkleProtocol.largestPow2Lt
  have he : e < 2 ^ e := Nat.lt_two_pow_self
  exact go_sandwich s.toNat e hlo hhi s.toNat 0 (Nat.zero_le e) (by omega)

private theorem pack_toNat (a b : UInt32) :
    (packMerkleState a b).toNat = a.toNat * 4294967296 + b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  unfold packMerkleState
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  have e : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [e, Nat.shiftLeft_eq]
  have e2 : (2 : Nat) ^ 32 = 4294967296 := rfl
  have e3 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [e2, e3]
  omega

theorem merkleStep : Spec.MerkleStep := by
  intro st size index hst hidx
  have e32 : (2 : Nat) ^ 32 = 4294967296 := rfl
  rw [e32] at hst hidx
  have hlt : st.toNat < 18446744073709551616 := st.toNat_lt
  have hS : ((st >>> 32).toUInt32).toNat = size := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    have e : (32 : UInt64).toNat % 64 = 32 := rfl
    rw [e, Nat.shiftRight_eq_div_pow, e32]
    omega
  have hI : st.toUInt32.toNat = index := by
    rw [UInt64.toNat_toUInt32, e32]; omega
  unfold llbMerkleAdvanceState
  simp only []
  generalize (st >>> 32).toUInt32 = S at hS ⊢
  generalize st.toUInt32 = I at hI ⊢
  constructor
  · intro h1
    have : S ≤ 1 := UInt32.le_iff_toNat_le.mpr (by rw [hS]; exact h1)
    rw [decide_eq_true this]; rfl
  · intro e hlo hhi
    have hp : 0 < 2 ^ e := Nat.pow_pos (by decide)
    have hm := merkleSplit S e (by rw [hS]; exact hlo) (by rw [hS]; exact hhi)
    generalize 2 ^ e = m at hlo hhi hp hm ⊢
    have hn1 : ¬ S ≤ 1 := fun h => by
      have := UInt32.le_iff_toNat_le.mp h
      rw [hS] at this
      have e1 : (1 : UInt32).toNat = 1 := rfl
      omega
    rw [decide_eq_false hn1, e32]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hc : index < m
    · have : I < largestPow2LtU32 S := UInt32.lt_iff_toNat_lt.mpr (by rw [hI, hm]; exact hc)
      rw [decide_eq_true this, ite_eq_left hc]
      simp only [↓reduceIte]
      rw [pack_toNat, hm, hI]
    · have hnl : ¬ I < largestPow2LtU32 S := fun h => by
        have := UInt32.lt_iff_toNat_lt.mp h
        rw [hI, hm] at this
        exact hc this
      rw [decide_eq_false hnl, ite_eq_right hc]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have l1 : largestPow2LtU32 S ≤ S := UInt32.le_iff_toNat_le.mpr (by rw [hS, hm]; omega)
      have l2 : largestPow2LtU32 S ≤ I := UInt32.le_iff_toNat_le.mpr (by rw [hI, hm]; omega)
      rw [pack_toNat, UInt32.toNat_sub_of_le _ _ l1, UInt32.toNat_sub_of_le _ _ l2, hm, hS, hI]

/-! ### BIP-370 locktime -/

section Locktime

open BitcoinLedger.Psbt InternalSpec.Psbt Proofs.FreestandingKernels

private def mkInp (i : UInt8 × UInt32 × UInt8 × UInt32) : PsbtInput :=
  { prevout := default
    requiredHeightLocktime := if i.1 = 0 then none else some i.2.1
    requiredTimeLocktime := if i.2.2.1 = 0 then none else some i.2.2.2 }

private theorem step_flags (st : UInt64) (a a' : UInt8) (h : UInt32) (b b' : UInt8) (t : UInt32)
    (ha : decide (a ≠ 0) = decide (a' ≠ 0)) (hb : decide (b ≠ 0) = decide (b' ≠ 0)) :
    llbPsbtLocktimeStep st a h b t = llbPsbtLocktimeStep st a' h b' t := by
  unfold llbPsbtLocktimeStep
  simp only [ha, hb]

private theorem step_noH (st : UInt64) (h : UInt32) (b : UInt8) (t : UInt32) :
    llbPsbtLocktimeStep st 0 h b t = llbPsbtLocktimeStep st 0 0 b t := by
  have hz : decide ((0 : UInt8) ≠ 0) = false := by decide
  unfold llbPsbtLocktimeStep
  simp only [hz, selU64_eq, bnot_eq, band_eq, bor_eq, Bool.not_false, Bool.true_or,
    Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

set_option linter.unusedSimpArgs false in
private theorem step_noT (st : UInt64) (a : UInt8) (h t : UInt32) :
    llbPsbtLocktimeStep st a h 0 t = llbPsbtLocktimeStep st a h 0 0 := by
  have hz : decide ((0 : UInt8) ≠ 0) = false := by decide
  unfold llbPsbtLocktimeStep
  cases hd : decide (a ≠ 0) <;>
  simp only [hd, hz, selU64_eq, bnot_eq, band_eq, bor_eq, Bool.not_false, Bool.not_true,
    Bool.true_or, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, ↓reduceIte]

private theorem step_mk (st : UInt64) (a : UInt8) (h : UInt32) (b : UInt8) (t : UInt32) :
    llbPsbtLocktimeStep st a h b t = psbtInputStep64 st (mkInp (a, h, b, t)) := by
  have h1 : decide ((1 : UInt8) ≠ 0) = true := by decide
  unfold psbtInputStep64 mkInp
  dsimp only
  by_cases ha : a = 0 <;> by_cases hb : b = 0
  · subst ha; subst hb
    simp only [↓reduceIte, Option.isSome_none, Option.getD_none, Bool.false_eq_true]
    rw [step_noH, step_noT]
  · subst ha
    simp only [hb, ↓reduceIte, Option.isSome_none, Option.isSome_some, Option.getD_none,
      Option.getD_some, Bool.false_eq_true]
    rw [step_noH]
    exact step_flags _ _ _ _ _ _ _ rfl (by rw [h1]; exact decide_eq_true hb)
  · subst hb
    simp only [ha, ↓reduceIte, Option.isSome_none, Option.isSome_some, Option.getD_none,
      Option.getD_some, Bool.false_eq_true]
    rw [step_noT]
    exact step_flags _ _ _ _ _ _ _ (by rw [h1]; exact decide_eq_true ha) rfl
  · simp only [ha, hb, ↓reduceIte, Option.isSome_some, Option.getD_some]
    exact step_flags _ _ _ _ _ _ _ (by rw [h1]; exact decide_eq_true ha)
      (by rw [h1]; exact decide_eq_true hb)

private theorem run_mk (ins : List (UInt8 × UInt32 × UInt8 × UInt32)) : ∀ st : UInt64,
    ins.foldl (fun st i => llbPsbtLocktimeStep st i.1 i.2.1 i.2.2.1 i.2.2.2) st =
      psbtFoldInputs64 st (ins.map mkInp) := by
  induction ins with
  | nil => intro st; rfl
  | cons i rest ih =>
    intro st
    rcases i with ⟨a, h, b, t⟩
    rw [List.foldl_cons, List.map_cons]
    show _ = psbtFoldInputs64 (psbtInputStep64 st (mkInp (a, h, b, t))) (rest.map mkInp)
    rw [← step_mk]
    exact ih _

private def reqOf (inp : PsbtInput) : Option Nat × Option Nat :=
  (inp.requiredHeightLocktime.map UInt32.toNat, inp.requiredTimeLocktime.map UInt32.toNat)

private def stepH (m : UInt32) (inp : PsbtInput) : UInt32 :=
  match inp.requiredHeightLocktime with
  | some h => if m.toNat < h.toNat then h else m
  | none => m

private def stepT (m : UInt32) (inp : PsbtInput) : UInt32 :=
  match inp.requiredTimeLocktime with
  | some t => if m.toNat < t.toNat then t else m
  | none => m

private theorem scan_closed (l : List PsbtInput) : ∀ st : LocktimeScanState,
    scanLocktimeInputs st l =
      if l.all checkInputLocktimeBounds then
        some { hasHeightOnly := st.hasHeightOnly ||
                 l.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone)
               hasTimeOnly := st.hasTimeOnly ||
                 l.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone)
               anyHeight := st.anyHeight || l.any (fun i => i.requiredHeightLocktime.isSome)
               anyTime := st.anyTime || l.any (fun i => i.requiredTimeLocktime.isSome)
               maxHeight := l.foldl stepH st.maxHeight
               maxTime := l.foldl stepT st.maxTime }
      else none := by
  induction l with
  | nil =>
    intro st
    simp only [List.all_nil, List.any_nil, Bool.or_false, List.foldl_nil, ↓reduceIte]
    rfl
  | cons inp rest ih =>
    intro st
    rw [scanLocktimeInputs]
    cases hb : checkInputLocktimeBounds inp
    · simp only [List.all_cons, hb, Bool.false_and, Bool.not_false, ↓reduceIte, Bool.false_eq_true]
    · simp only [List.all_cons, hb, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      simp only [List.any_cons, List.foldl_cons, Bool.or_assoc]
      rfl

private theorem enc_ok (x : UInt32) :
    (encodeLocktimeResult (.ok x)).toNat = 2 ^ 32 + x.toNat := by
  have hx := x.toNat_lt
  show (((1 : UInt64) <<< 32) ||| x.toUInt64).toNat = _
  rw [UInt64.toNat_or, UInt32.toNat_toUInt64, show ((1 : UInt64) <<< 32).toNat = 1 <<< 32 from rfl,
    Nat.or_comm, or_shift _ _ 32 hx, Nat.one_mul, Nat.add_comm]

private theorem range_eq (l : List PsbtInput) :
    (l.map reqOf).all Spec.lockReqInRange = l.all checkInputLocktimeBounds := by
  induction l with
  | nil => rfl
  | cons inp rest ih =>
    rw [List.map_cons, List.all_cons, List.all_cons, ih]
    have : Spec.lockReqInRange (reqOf inp) = checkInputLocktimeBounds inp := by
      unfold Spec.lockReqInRange reqOf checkInputLocktimeBounds
      cases inp.requiredHeightLocktime <;> cases inp.requiredTimeLocktime <;> rfl
    rw [this]

private theorem maxH_eq (l : List PsbtInput) : ∀ m : UInt32,
    ((l.map reqOf).filterMap (fun r => r.1)).foldl max m.toNat = (l.foldl stepH m).toNat := by
  induction l with
  | nil => intro m; rfl
  | cons inp rest ih =>
    intro m
    rw [List.map_cons, List.foldl_cons]
    cases hh : inp.requiredHeightLocktime with
    | none =>
      have e1 : (reqOf inp).1 = none := by simp only [reqOf, hh, Option.map_none]
      have e2 : stepH m inp = m := by simp only [stepH, hh]
      rw [List.filterMap_cons_none e1, e2]
      exact ih m
    | some h =>
      have e1 : (reqOf inp).1 = some h.toNat := by simp only [reqOf, hh, Option.map_some]
      have e2 : stepH m inp = if m.toNat < h.toNat then h else m := by simp only [stepH, hh]
      rw [List.filterMap_cons_some e1, List.foldl_cons, e2]
      by_cases hlt : m.toNat < h.toNat
      · rw [ite_eq_left hlt, ← ih h, Nat.max_eq_right (Nat.le_of_lt hlt)]
      · rw [ite_eq_right hlt, ← ih m, Nat.max_eq_left (Nat.le_of_not_lt hlt)]

private theorem maxT_eq (l : List PsbtInput) : ∀ m : UInt32,
    ((l.map reqOf).filterMap (fun r => r.2)).foldl max m.toNat = (l.foldl stepT m).toNat := by
  induction l with
  | nil => intro m; rfl
  | cons inp rest ih =>
    intro m
    rw [List.map_cons, List.foldl_cons]
    cases hh : inp.requiredTimeLocktime with
    | none =>
      have e1 : (reqOf inp).2 = none := by simp only [reqOf, hh, Option.map_none]
      have e2 : stepT m inp = m := by simp only [stepT, hh]
      rw [List.filterMap_cons_none e1, e2]
      exact ih m
    | some h =>
      have e1 : (reqOf inp).2 = some h.toNat := by simp only [reqOf, hh, Option.map_some]
      have e2 : stepT m inp = if m.toNat < h.toNat then h else m := by simp only [stepT, hh]
      rw [List.filterMap_cons_some e1, List.foldl_cons, e2]
      by_cases hlt : m.toNat < h.toNat
      · rw [ite_eq_left hlt, ← ih h, Nat.max_eq_right (Nat.le_of_lt hlt)]
      · rw [ite_eq_right hlt, ← ih m, Nat.max_eq_left (Nat.le_of_not_lt hlt)]

private theorem flags (l : List PsbtInput) :
    (l.map reqOf).all (fun r => r.1.isNone && r.2.isNone) =
      (!l.any (fun i => i.requiredHeightLocktime.isSome) &&
       !l.any (fun i => i.requiredTimeLocktime.isSome)) ∧
    (l.map reqOf).all Spec.supportsHeight =
      (!l.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone)) ∧
    (l.map reqOf).all Spec.supportsTime =
      (!l.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone)) ∧
    (l.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone) = true →
      l.any (fun i => i.requiredHeightLocktime.isSome) = true) ∧
    (l.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone) = true →
      l.any (fun i => i.requiredTimeLocktime.isSome) = true) ∧
    (l.any (fun i => i.requiredTimeLocktime.isSome) = true →
      l.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone) = true ∨
      l.any (fun i => i.requiredHeightLocktime.isSome) = true) := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl, fun h => h, fun h => h, fun h => Or.inl h⟩
  | cons inp rest ih =>
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih
    simp only [List.map_cons, List.all_cons, List.any_cons, i1, i2, i3]
    unfold reqOf Spec.supportsHeight Spec.supportsTime
    generalize rest.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone) = a at *
    generalize rest.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone) = b at *
    generalize rest.any (fun i => i.requiredHeightLocktime.isSome) = c at *
    generalize rest.any (fun i => i.requiredTimeLocktime.isSome) = d at *
    revert i4 i5 i6
    cases inp.requiredHeightLocktime <;> cases inp.requiredTimeLocktime <;>
      simp only [Option.isSome_some, Option.isSome_none, Option.isNone_some, Option.isNone_none,
        Option.map_some, Option.map_none] <;>
      cases a <;> cases b <;> cases c <;> cases d <;> decide

set_option linter.unusedSimpArgs false in
private theorem det_eq (fb : UInt32) (l : List PsbtInput) :
    (encodeLocktimeResult (BitcoinLedger.Psbt.determineLocktime (some fb) l)).toNat =
      match Spec.bip370Locktime fb.toNat (l.map reqOf) with
      | some v => 2 ^ 32 + v
      | none => 0 := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := flags l
  have mh : Spec.maxOf ((l.map reqOf).filterMap (fun r => r.1)) = (l.foldl stepH 0).toNat :=
    maxH_eq l 0
  have mt : Spec.maxOf ((l.map reqOf).filterMap (fun r => r.2)) = (l.foldl stepT 0).toNat :=
    maxT_eq l 0
  unfold BitcoinLedger.Psbt.determineLocktime Spec.bip370Locktime
  rw [scan_closed, range_eq, f1, f2, f3, mh, mt]
  cases l.all checkInputLocktimeBounds
  · rfl
  · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, Bool.false_or, Option.getD_some]
    generalize l.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone) = a at *
    generalize l.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone) = b at *
    generalize l.any (fun i => i.requiredHeightLocktime.isSome) = c at *
    generalize l.any (fun i => i.requiredTimeLocktime.isSome) = d at *
    clear f1 f2 f3 mh mt
    revert f4 f5 f6
    cases a <;> cases b <;> cases c <;> cases d <;> intro f4 f5 f6 <;>
      simp only [Bool.and_self, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
      first
        | exact enc_ok _
        | rfl
        | exact absurd (f4 rfl) (by decide)
        | exact absurd (f5 rfl) (by decide)
        | (rcases f6 rfl with h | h <;> exact absurd h (by decide))

private theorem mk_req (i : UInt8 × UInt32 × UInt8 × UInt32) : reqOf (mkInp i) = Spec.lockReq i := by
  unfold reqOf mkInp Spec.lockReq
  dsimp only
  by_cases ha : i.1 = 0 <;> by_cases hb : i.2.2.1 = 0 <;>
    simp only [ha, hb, ↓reduceIte, Option.map_some, Option.map_none]

theorem psbtLocktime : Spec.PsbtLocktime := by
  intro ins fallback
  unfold Spec.locktimeRun
  rw [run_mk]
  have h := llbPsbtLocktime_eq_determineLocktime (some fallback) (ins.map mkInp)
  rw [Option.getD_some] at h
  rw [h, det_eq, List.map_map]
  have e : reqOf ∘ mkInp = Spec.lockReq := funext mk_req
  rw [e]
  rfl

end Locktime

/-! ### Sorts

Insertion sort over a view `Nat → α` of a buffer, then the two kernel sorts as instances. -/

private theorem foldl_range_inv {β : Type} (P : Nat → β → Prop) (f : β → Nat → β) (n : Nat) (init : β)
    (h0 : P 0 init) (hs : ∀ k b, k < n → P k b → P (k + 1) (f b k)) :
    P n ((List.range n).foldl f init) := by
  induction n with
  | zero => exact h0
  | succ m ih =>
    rw [List.range_succ, List.foldl_append]
    exact hs m _ (Nat.lt_succ_self m) (ih (fun k b hk hp => hs k b (Nat.lt_succ_of_lt hk) hp))

private def lst {α : Type} (f : Nat → α) (n : Nat) : List α := (List.range n).map f

private theorem lst_succ {α : Type} (f : Nat → α) (n : Nat) : lst f (n + 1) = lst f n ++ [f n] := by
  unfold lst; rw [List.range_succ, List.map_append]; rfl

private theorem lst_congr {α : Type} (f g : Nat → α) (n : Nat) (h : ∀ i, i < n → f i = g i) :
    lst f n = lst g n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [lst_succ, lst_succ, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h m (Nat.lt_succ_self m)]

private theorem swap_perm {α : Type} (f g : Nat → α) (j : Nat) (h1 : g j = f (j + 1)) (h2 : g (j + 1) = f j) :
    ∀ n, j + 1 < n → (∀ i, i < n → i ≠ j → i ≠ j + 1 → g i = f i) → (lst g n).Perm (lst f n) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih =>
    intro hlt hrest
    rw [lst_succ, lst_succ]
    by_cases hm : j + 1 < m
    · have n1 : m ≠ j := by omega
      have n2 : m ≠ j + 1 := by omega
      have e : g m = f m := hrest m (Nat.lt_succ_self m) n1 n2
      rw [e]
      exact List.Perm.append_right _ (ih hm (fun i hi => hrest i (Nat.lt_succ_of_lt hi)))
    · have hm' : m = j + 1 := by omega
      rw [hm', lst_succ, lst_succ, h1, h2,
        lst_congr g f j (fun i hi => hrest i (by omega) (by omega) (by omega)),
        List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ (List.Perm.swap _ _ _)

private theorem sorted_lst {α : Type} (le : α → α → Prop) (f : Nat → α) :
    ∀ n, (∀ i i', i < i' → i' < n → le (f i) (f i')) → (lst f n).Pairwise le := by
  intro n
  induction n with
  | zero => intro _; exact List.Pairwise.nil
  | succ m ih =>
    intro h
    rw [lst_succ, List.pairwise_append]
    refine ⟨ih (fun i i' h1 h2 => h i i' h1 (Nat.lt_succ_of_lt h2)), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    obtain ⟨i, hi, e⟩ := List.mem_map.mp ha
    rw [List.mem_singleton.mp hb, ← e]
    exact h i m (List.mem_range.mp hi) (Nat.lt_succ_self m)

private theorem ins_step {α : Type} (le : α → α → Prop) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, ¬ le a b → le b a) (f g : Nat → α) (s q : Nat) (hqs : q + 1 ≤ s)
    (h1 : ∀ i i', i < i' → i' ≤ s → i ≠ q + 1 → i' ≠ q + 1 → le (f i) (f i'))
    (h2 : ∀ i, q + 1 < i → i ≤ s → le (f (q + 1)) (f i))
    (hg : (¬ le (f q) (f (q + 1)) ∧ g q = f (q + 1) ∧ g (q + 1) = f q ∧
            ∀ i, i ≤ s → i ≠ q → i ≠ q + 1 → g i = f i) ∨
          (le (f q) (f (q + 1)) ∧ ∀ i, i ≤ s → g i = f i)) :
    (∀ i i', i < i' → i' ≤ s → i ≠ q → i' ≠ q → le (g i) (g i')) ∧
    (∀ i, q < i → i ≤ s → le (g q) (g i)) := by
  have qq : q ≠ q + 1 := Nat.ne_of_lt (Nat.lt_succ_self q)
  have qs : q ≤ s := Nat.le_of_succ_le hqs
  rcases hg with ⟨hn, e1, e2, er⟩ | ⟨hl, er⟩
  · constructor
    · intro i i' hii hi's hi hi'
      by_cases c1 : i = q + 1
      · have n1 : i' ≠ q + 1 := by omega
        have l1 : q < i' := by omega
        rw [c1, e2, er i' hi's hi' n1]
        exact h1 q i' l1 hi's qq n1
      · by_cases c2 : i' = q + 1
        · have l1 : i < q := by omega
          have l2 : i ≤ s := by omega
          rw [c2, e2, er i l2 hi c1]
          exact h1 i q l1 qs c1 qq
        · have l2 : i ≤ s := by omega
          rw [er i l2 hi c1, er i' hi's hi' c2]
          exact h1 i i' hii hi's c1 c2
    · intro i hi his
      rw [e1]
      by_cases c : i = q + 1
      · rw [c, e2]; exact total _ _ hn
      · have n1 : i ≠ q := by omega
        have l1 : q + 1 < i := by omega
        rw [er i his n1 c]; exact h2 i l1 his
  · constructor
    · intro i i' hii hi's hi hi'
      have l2 : i ≤ s := by omega
      rw [er i l2, er i' hi's]
      by_cases c1 : i = q + 1
      · have l1 : q + 1 < i' := by omega
        rw [c1]; exact h2 i' l1 hi's
      · by_cases c2 : i' = q + 1
        · have l1 : i < q := by omega
          rw [c2]
          exact trans _ _ _ (h1 i q l1 qs c1 qq) hl
        · exact h1 i i' hii hi's c1 c2
    · intro i hi his
      rw [er q qs, er i his]
      by_cases c : i = q + 1
      · rw [c]; exact hl
      · exact h1 q i hi his qq c

private theorem foldl_range_congr {β : Type} (f g : β → Nat → β) (n : Nat) (a : β)
    (h : ∀ k b, k < n → f b k = g b k) : (List.range n).foldl f a = (List.range n).foldl g a := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun k b hk => h k b (Nat.lt_succ_of_lt hk))]
    exact h m _ (Nat.lt_succ_self m)

/-- One insertion pass: `step b q` compares positions `q` and `q + 1` and swaps them when
    they are out of order. -/
private theorem ins_pass {α β : Type} (le : α → α → Prop) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, ¬ le a b → le b a) (view : β → Nat → α) (keep : β → β → Prop)
    (keep_refl : ∀ b, keep b b) (keep_trans : ∀ a b c, keep a b → keep b c → keep a c)
    (n : Nat) (step : β → Nat → β)
    (hstep : ∀ b q, q + 1 < n → keep (step b q) b ∧
      ((¬ le (view b q) (view b (q + 1)) ∧ view (step b q) q = view b (q + 1) ∧
          view (step b q) (q + 1) = view b q ∧
          ∀ i, i < n → i ≠ q → i ≠ q + 1 → view (step b q) i = view b i) ∨
       (le (view b q) (view b (q + 1)) ∧ ∀ i, i < n → view (step b q) i = view b i)))
    (s : Nat) (hsn : s < n) (a : β)
    (hsorted : ∀ i i', i < i' → i' < s → le (view a i) (view a i')) :
    (∀ i i', i < i' → i' ≤ s →
      le (view ((List.range s).foldl (fun b k => step b (s - 1 - k)) a) i)
         (view ((List.range s).foldl (fun b k => step b (s - 1 - k)) a) i')) ∧
    (lst (view ((List.range s).foldl (fun b k => step b (s - 1 - k)) a)) n).Perm (lst (view a) n) ∧
    keep ((List.range s).foldl (fun b k => step b (s - 1 - k)) a) a := by
  have key := foldl_range_inv
    (fun k (b : β) =>
      (∀ i i', i < i' → i' ≤ s → i ≠ s - k → i' ≠ s - k → le (view b i) (view b i')) ∧
      (∀ i, s - k < i → i ≤ s → le (view b (s - k)) (view b i)) ∧
      (lst (view b) n).Perm (lst (view a) n) ∧ keep b a)
    (fun (b : β) k => step b (s - 1 - k)) s a ?h0 ?hs
  · obtain ⟨k1, k2, k3, k4⟩ := key
    rw [Nat.sub_self] at k1 k2
    refine ⟨?_, k3, k4⟩
    intro i i' hii hi'
    by_cases c : i = 0
    · rw [c]; exact k2 i' (by omega) hi'
    · exact k1 i i' hii hi' c (by omega)
  case h0 =>
    refine ⟨?_, ?_, List.Perm.refl _, keep_refl a⟩
    · intro i i' hii hi' _ hne
      exact hsorted i i' hii (by omega)
    · intro i h1 h2; exfalso; omega
  case hs =>
    intro k b hk ⟨p1, p2, p3, p4⟩
    have hq : s - k = (s - 1 - k) + 1 := by omega
    generalize s - 1 - k = q at hq ⊢
    rw [hq] at p1 p2
    have hqs : q + 1 ≤ s := by omega
    have hqn : q + 1 < n := by omega
    have hq' : s - (k + 1) = q := by omega
    have hin : ∀ i, i ≤ s → i < n := fun i hi => Nat.lt_of_le_of_lt hi hsn
    rw [hq']
    obtain ⟨hkeep, hcase⟩ := hstep b q hqn
    rcases hcase with ⟨hn, e1, e2, er⟩ | ⟨hl, er⟩
    · have st := ins_step le trans total (view b) (view (step b q)) s q hqs p1 p2
        (Or.inl ⟨hn, e1, e2, fun i hi n1 n2 => er i (hin i hi) n1 n2⟩)
      exact ⟨st.1, st.2, (swap_perm (view b) (view (step b q)) q e1 e2 n hqn
        (fun i hi n1 n2 => er i hi n1 n2)).trans p3, keep_trans _ _ _ hkeep p4⟩
    · have st := ins_step le trans total (view b) (view (step b q)) s q hqs p1 p2
        (Or.inr ⟨hl, fun i hi => er i (hin i hi)⟩)
      rw [lst_congr (view (step b q)) (view b) n er]
      exact ⟨st.1, st.2, p3, keep_trans _ _ _ hkeep p4⟩

/-- Insertion sort: pass `k` inserts position `k + 1` into the sorted prefix. -/
private theorem ins_sort {α β : Type} (le : α → α → Prop) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, ¬ le a b → le b a) (view : β → Nat → α) (keep : β → β → Prop)
    (keep_refl : ∀ b, keep b b) (keep_trans : ∀ a b c, keep a b → keep b c → keep a c)
    (n : Nat) (step : β → Nat → β)
    (hstep : ∀ b q, q + 1 < n → keep (step b q) b ∧
      ((¬ le (view b q) (view b (q + 1)) ∧ view (step b q) q = view b (q + 1) ∧
          view (step b q) (q + 1) = view b q ∧
          ∀ i, i < n → i ≠ q → i ≠ q + 1 → view (step b q) i = view b i) ∨
       (le (view b q) (view b (q + 1)) ∧ ∀ i, i < n → view (step b q) i = view b i)))
    (a : β) :
    (lst (view ((List.range (n - 1)).foldl
      (fun b k => (List.range (k + 1)).foldl (fun b k' => step b (k + 1 - 1 - k')) b) a)) n).Pairwise le ∧
    (lst (view ((List.range (n - 1)).foldl
      (fun b k => (List.range (k + 1)).foldl (fun b k' => step b (k + 1 - 1 - k')) b) a)) n).Perm
        (lst (view a) n) ∧
    keep ((List.range (n - 1)).foldl
      (fun b k => (List.range (k + 1)).foldl (fun b k' => step b (k + 1 - 1 - k')) b) a) a := by
  have key := foldl_range_inv
    (fun k (b : β) =>
      (∀ i i', i < i' → i' < k + 1 → le (view b i) (view b i')) ∧
      (lst (view b) n).Perm (lst (view a) n) ∧ keep b a)
    (fun (b : β) k => (List.range (k + 1)).foldl (fun b k' => step b (k + 1 - 1 - k')) b)
    (n - 1) a ?h0 ?hs
  · obtain ⟨k1, k2, k3⟩ := key
    exact ⟨sorted_lst le _ n (fun i i' h1 h2 => k1 i i' h1 (by omega)), k2, k3⟩
  case h0 =>
    exact ⟨fun i i' h1 h2 => by exfalso; omega, List.Perm.refl _, keep_refl a⟩
  case hs =>
    intro k b hk ⟨p1, p2, p3⟩
    obtain ⟨q1, q2, q3⟩ := ins_pass le trans total view keep keep_refl keep_trans n step hstep
      (k + 1) (by omega) b (fun i i' h1 h2 => p1 i i' h1 h2)
    exact ⟨fun i i' h1 h2 => q1 i i' h1 (by omega), q2.trans p2, keep_trans _ _ _ q3 p3⟩

private theorem forRangeU16s_go_eq (step : UInt32 → MutU16s → MutU16s) (fuel : Nat) :
    ∀ (cur : UInt32) (b : MutU16s), forRangeU16s.go step fuel cur b =
      (List.range fuel).foldl (fun a k => step (cur + UInt32.ofNat k) a) b := by
  induction fuel with
  | zero => intro cur b; rfl
  | succ fuel' ih =>
    intro cur b
    unfold forRangeU16s.go
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have h0 : cur + UInt32.ofNat 0 = cur := UInt32.add_zero cur
    rw [h0, ih (cur + 1) (step cur b)]
    have hfun :
        (fun a k => step (cur + 1 + UInt32.ofNat k) a) =
          (fun a k => step (cur + UInt32.ofNat (k + 1)) a) := by
      funext a k
      have hk : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        rw [UInt32.ofNat_add, UInt32.add_comm]
        rfl
      rw [UInt32.add_assoc, hk]
    rw [hfun]

private theorem forRangeU16s_eq (lo hi : UInt32) (buf : MutU16s) (step : UInt32 → MutU16s → MutU16s) :
    forRangeU16s lo hi buf step =
      (List.range (hi.toNat - lo.toNat)).foldl (fun b k => step (lo + UInt32.ofNat k) b) buf := by
  unfold forRangeU16s
  by_cases h : lo < hi
  · rw [decide_eq_true h]
    simp only [↓reduceIte]
    rw [forRangeU16s_go_eq, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr
      (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h)))]
  · rw [decide_eq_false h]
    have : hi.toNat - lo.toNat = 0 := by
      have hnl : ¬ lo.toNat < hi.toNat := fun h' => h (UInt32.lt_iff_toNat_lt.mpr h')
      omega
    rw [this]; rfl

private theorem ofNat_eq_iff (i : Nat) (hi : i < 4294967296) (j : UInt32) :
    UInt32.ofNat i = j ↔ i = j.toNat := by
  constructor
  · intro h; rw [← h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hi]
  · intro h; rw [h, u32_ofNat_toNat]

private theorem ofNat_toNat_lt (i : Nat) (hi : i < 4294967296) : (UInt32.ofNat i).toNat = i := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hi]

private theorem slot_toNat (k : Nat) (hk : k + 1 < 4294967296) : (1 + UInt32.ofNat k : UInt32).toNat = k + 1 := by
  have e1 : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.toNat_add, e1, ofNat_toNat_lt k (by omega), Nat.add_comm]
  exact Nat.mod_eq_of_lt hk

private theorem idx_eq (slot : UInt32) (k k' : Nat) (hs : slot.toNat = k + 1) (hk' : k' < k + 1) :
    slot - 1 - (0 + UInt32.ofNat k') = UInt32.ofNat (k + 1 - 1 - k') := by
  have hlt := slot.toNat_lt
  apply UInt32.toNat_inj.mp
  have hk2 : (0 + UInt32.ofNat k' : UInt32).toNat = k' := by
    rw [UInt32.zero_add, ofNat_toNat_lt k' (by omega)]
  have h1 : (1 : UInt32) ≤ slot := UInt32.le_iff_toNat_le.mpr (by rw [hs]; show 1 ≤ k + 1; omega)
  have h1n : (slot - 1).toNat = k := by rw [UInt32.toNat_sub_of_le _ _ h1, hs]; rfl
  have h2 : (0 + UInt32.ofNat k' : UInt32) ≤ slot - 1 :=
    UInt32.le_iff_toNat_le.mpr (by rw [hk2, h1n]; omega)
  rw [UInt32.toNat_sub_of_le _ _ h2, h1n, hk2, ofNat_toNat_lt _ (by omega)]
  omega

/-! ### `llb_sort_u16` -/

private def fn16 (a : MutU16s) : Nat → Nat := fun i => (a.get (UInt32.ofNat i)).toNat

/-- Compare-and-swap of words `j` and `j + 1`: the body of the kernel's private pass. -/
private def cmpSwap16 (a : MutU16s) (j : UInt32) : MutU16s :=
  let x := readMutU16 a j
  let y := readMutU16 a (j + 1)
  if decide (y < x) then
    let a1 := writeU16 a j y
    writeU16 a1 (j + 1) x
  else a

private theorem sortU16_unfold (arr : MutU16s) (count : UInt32) :
    llbSortU16 arr count =
      if decide (count ≤ 1) then arr
      else forRangeU16s 1 count arr (fun slot a =>
        forRangeU16s 0 slot a (fun k a => cmpSwap16 a (slot - 1 - k))) := rfl

private theorem step16 (n : Nat) (hn : n ≤ 4294967296) (b : MutU16s) (q : Nat) (hq : q + 1 < n) :
    (∀ i : UInt32, n ≤ i.toNat → (cmpSwap16 b (UInt32.ofNat q)).get i = b.get i) ∧
    ((¬ fn16 b q ≤ fn16 b (q + 1) ∧ fn16 (cmpSwap16 b (UInt32.ofNat q)) q = fn16 b (q + 1) ∧
        fn16 (cmpSwap16 b (UInt32.ofNat q)) (q + 1) = fn16 b q ∧
        ∀ i, i < n → i ≠ q → i ≠ q + 1 → fn16 (cmpSwap16 b (UInt32.ofNat q)) i = fn16 b i) ∨
     (fn16 b q ≤ fn16 b (q + 1) ∧ ∀ i, i < n → fn16 (cmpSwap16 b (UInt32.ofNat q)) i = fn16 b i)) := by
  have hjn : (UInt32.ofNat q).toNat = q := ofNat_toNat_lt q (by omega)
  generalize UInt32.ofNat q = j at hjn ⊢
  have hj1 : (j + 1).toNat = q + 1 := by
    have e1 : (1 : UInt32).toNat = 1 := rfl
    rw [UInt32.toNat_add, hjn, e1]; exact Nat.mod_eq_of_lt (by omega)
  have ej : UInt32.ofNat q = j := (ofNat_eq_iff q (by omega) j).mpr hjn.symm
  have ej1 : UInt32.ofNat (q + 1) = j + 1 := (ofNat_eq_iff (q + 1) (by omega) (j + 1)).mpr hj1.symm
  have fq : fn16 b q = (b.get j).toNat := by unfold fn16; rw [ej]
  have fq1 : fn16 b (q + 1) = (b.get (j + 1)).toNat := by unfold fn16; rw [ej1]
  have jne : j ≠ j + 1 := fun h => by
    have := congrArg UInt32.toNat h
    rw [hjn, hj1] at this; omega
  unfold cmpSwap16
  dsimp only
  by_cases hlt' : readMutU16 b (j + 1) < readMutU16 b j
  · rw [decide_eq_true hlt']
    have hlt : b.get (j + 1) < b.get j := hlt'
    simp only [↓reduceIte, readMutU16, writeU16]
    have hltn := UInt16.lt_iff_toNat_lt.mp hlt
    refine ⟨?_, Or.inl ⟨by rw [fq, fq1]; omega, ?_, ?_, ?_⟩⟩
    · intro i hi
      have m1 : ¬ i = j + 1 := fun h => by rw [h, hj1] at hi; omega
      have m2 : ¬ i = j := fun h => by rw [h, hjn] at hi; omega
      rw [ite_eq_right m1, ite_eq_right m2]
    · show (if UInt32.ofNat q = j + 1 then b.get j else if UInt32.ofNat q = j then b.get (j + 1)
        else b.get (UInt32.ofNat q)).toNat = _
      rw [ej, ite_eq_right jne, ite_eq_left rfl, fq1]
    · show (if UInt32.ofNat (q + 1) = j + 1 then b.get j else if UInt32.ofNat (q + 1) = j then b.get (j + 1)
        else b.get (UInt32.ofNat (q + 1))).toNat = _
      rw [ej1, ite_eq_left rfl, fq]
    · intro i hi n1 n2
      have hi' : i < 4294967296 := by omega
      have m1 : ¬ UInt32.ofNat i = j + 1 := fun h => n2 (by
        have := (ofNat_eq_iff i hi' (j + 1)).mp h; omega)
      have m2 : ¬ UInt32.ofNat i = j := fun h => n1 (by
        have := (ofNat_eq_iff i hi' j).mp h; omega)
      show (if UInt32.ofNat i = j + 1 then b.get j else if UInt32.ofNat i = j then b.get (j + 1)
        else b.get (UInt32.ofNat i)).toNat = _
      rw [ite_eq_right m1, ite_eq_right m2]; rfl
  · rw [decide_eq_false hlt']
    have hlt : ¬ b.get (j + 1) < b.get j := hlt'
    rw [ite_eq_right Bool.false_ne_true]
    have hnl : ¬ (b.get (j + 1)).toNat < (b.get j).toNat :=
      fun h => hlt (UInt16.lt_iff_toNat_lt.mpr h)
    exact ⟨fun _ _ => rfl, Or.inr ⟨by rw [fq, fq1]; omega, fun _ _ => rfl⟩⟩

theorem sortU16 : Spec.SortU16 := by
  intro arr count
  rw [sortU16_unfold]
  have hc := count.toNat_lt
  have e1 : (1 : UInt32).toNat = 1 := rfl
  by_cases hle : count ≤ 1
  · rw [decide_eq_true hle]
    simp only [↓reduceIte]
    have hn : count.toNat ≤ 1 := UInt32.le_iff_toNat_le.mp hle
    refine ⟨?_, List.Perm.refl _, ?_⟩
    · exact sorted_lst (fun x y : Nat => x ≤ y) (fn16 arr) count.toNat
        (fun i i' h1 h2 => by exfalso; omega)
    · exact fun _ _ => trivial
  · rw [decide_eq_false hle]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [forRangeU16s_eq, e1]
    generalize hnd : count.toNat = n at hc ⊢
    have conv : (List.range (n - 1)).foldl (fun b k =>
          forRangeU16s 0 (1 + UInt32.ofNat k) b
            (fun k' a => cmpSwap16 a (1 + UInt32.ofNat k - 1 - k'))) arr =
        (List.range (n - 1)).foldl (fun b k => (List.range (k + 1)).foldl
          (fun b k' => cmpSwap16 b (UInt32.ofNat (k + 1 - 1 - k'))) b) arr := by
      apply foldl_range_congr
      intro k b hk
      have hs := slot_toNat k (by omega)
      have hz : (0 : UInt32).toNat = 0 := rfl
      rw [forRangeU16s_eq, hs, hz, Nat.sub_zero]
      apply foldl_range_congr
      intro k' b' hk'
      show cmpSwap16 b' (1 + UInt32.ofNat k - 1 - (0 + UInt32.ofNat k')) = _
      rw [idx_eq _ k k' hs hk']
    rw [conv]
    obtain ⟨r1, r2, r3⟩ := ins_sort (fun x y : Nat => x ≤ y) (fun _ _ _ => Nat.le_trans)
      (fun _ _ h => Nat.le_of_lt (Nat.lt_of_not_le h)) fn16
      (fun b' b : MutU16s => ∀ i : UInt32, n ≤ i.toNat → b'.get i = b.get i)
      (fun _ _ _ => rfl) (fun _ _ _ h1 h2 i hi => (h1 i hi).trans (h2 i hi))
      n (fun b q => cmpSwap16 b (UInt32.ofNat q)) (step16 n (Nat.le_of_lt hc)) arr
    exact ⟨r1, r2, r3⟩

/-! ### `llb_sort_fixed_bytes` -/

private theorem forRangeBytes_go_eq (step : UInt32 → MutBytes → MutBytes) (fuel : Nat) :
    ∀ (cur : UInt32) (b : MutBytes), forRangeBytes.go step fuel cur b =
      (List.range fuel).foldl (fun a k => step (cur + UInt32.ofNat k) a) b := by
  induction fuel with
  | zero => intro cur b; rfl
  | succ fuel' ih =>
    intro cur b
    unfold forRangeBytes.go
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have h0 : cur + UInt32.ofNat 0 = cur := UInt32.add_zero cur
    rw [h0, ih (cur + 1) (step cur b)]
    have hfun :
        (fun a k => step (cur + 1 + UInt32.ofNat k) a) =
          (fun a k => step (cur + UInt32.ofNat (k + 1)) a) := by
      funext a k
      have hk : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        rw [UInt32.ofNat_add, UInt32.add_comm]
        rfl
      rw [UInt32.add_assoc, hk]
    rw [hfun]

private theorem forRangeBytes_eq (lo hi : UInt32) (buf : MutBytes) (step : UInt32 → MutBytes → MutBytes) :
    forRangeBytes lo hi buf step =
      (List.range (hi.toNat - lo.toNat)).foldl (fun b k => step (lo + UInt32.ofNat k) b) buf := by
  unfold forRangeBytes
  by_cases h : lo < hi
  · rw [decide_eq_true h]
    simp only [↓reduceIte]
    rw [forRangeBytes_go_eq, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr
      (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h)))]
  · rw [decide_eq_false h]
    have : hi.toNat - lo.toNat = 0 := by
      have hnl : ¬ lo.toNat < hi.toNat := fun h' => h (UInt32.lt_iff_toNat_lt.mpr h')
      omega
    rw [this]; rfl


private theorem forRangeU64_eq' (lo hi : UInt32) (init : UInt64) (step : UInt32 → UInt64 → UInt64) :
    forRangeU64 lo hi init step =
      (List.range (hi.toNat - lo.toNat)).foldl (fun acc k => step (lo + UInt32.ofNat k) acc) init := by
  rw [Proofs.FreestandingKernels.forRangeU64_eq_foldl]
  by_cases h : lo < hi
  · rw [decide_eq_true h, ite_eq_left rfl, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr
      (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h)))]
  · rw [decide_eq_false h, ite_eq_right Bool.false_ne_true]
    have : hi.toNat - lo.toNat = 0 := by
      have hnl : ¬ lo.toNat < hi.toNat := fun h' => h (UInt32.lt_iff_toNat_lt.mpr h')
      omega
    rw [this]; rfl

private theorem lexLe_trans : ∀ a b c : List Nat, Spec.lexLe a b → Spec.lexLe b c → Spec.lexLe a c
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    show x < z ∨ (x = z ∧ Spec.lexLe xs zs)
    have h1' : x < y ∨ (x = y ∧ Spec.lexLe xs ys) := h1
    have h2' : y < z ∨ (y = z ∧ Spec.lexLe ys zs) := h2
    rcases h1' with h | ⟨e, h⟩
    · rcases h2' with h' | ⟨e', _⟩
      · exact Or.inl (Nat.lt_trans h h')
      · exact Or.inl (e' ▸ h)
    · rcases h2' with h' | ⟨e', h'⟩
      · exact Or.inl (e ▸ h')
      · exact Or.inr ⟨e.trans e', lexLe_trans xs ys zs h h'⟩

private theorem lexLe_total : ∀ a b : List Nat, ¬ Spec.lexLe a b → Spec.lexLe b a
  | [], _, h => (h trivial).elim
  | _ :: _, [], _ => trivial
  | x :: xs, y :: ys, h => by
    show y < x ∨ (y = x ∧ Spec.lexLe ys xs)
    have h' : ¬ (x < y ∨ (x = y ∧ Spec.lexLe xs ys)) := h
    rcases Nat.lt_trichotomy x y with c | c | c
    · exact (h' (Or.inl c)).elim
    · exact Or.inr ⟨c.symm, lexLe_total xs ys (fun hh => h' (Or.inr ⟨c, hh⟩))⟩
    · exact Or.inl c

private def cmpNat (acc : UInt64) (p : Nat × Nat) : UInt64 :=
  if decide (acc ≠ 2) then acc
  else if decide (p.1 < p.2) then 0 else if decide (p.2 < p.1) then 1 else 2

private theorem cmp_stuck (l : List (Nat × Nat)) (acc : UInt64) (h : acc ≠ 2) : l.foldl cmpNat acc = acc := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have e : cmpNat acc p = acc := by unfold cmpNat; rw [decide_eq_true h]; rfl
    rw [List.foldl_cons, e]; exact ih

private theorem cmp_fold : ∀ l : List (Nat × Nat),
    (l.foldl cmpNat 2 = 1 → ¬ Spec.lexLe (l.map Prod.fst) (l.map Prod.snd)) ∧
    (l.foldl cmpNat 2 ≠ 1 → Spec.lexLe (l.map Prod.fst) (l.map Prod.snd))
  | [] => ⟨fun h => absurd h (by decide), fun _ => trivial⟩
  | (x, y) :: l => by
    rw [List.foldl_cons]
    show (_ → ¬ (x < y ∨ (x = y ∧ Spec.lexLe (l.map Prod.fst) (l.map Prod.snd)))) ∧
      (_ → (x < y ∨ (x = y ∧ Spec.lexLe (l.map Prod.fst) (l.map Prod.snd))))
    rcases Nat.lt_trichotomy x y with c | c | c
    · have e : cmpNat 2 (x, y) = 0 := by
        show (if decide (x < y) = true then (0 : UInt64) else _) = 0
        rw [decide_eq_true c]; rfl
      rw [e, cmp_stuck l 0 (by decide)]
      exact ⟨fun h => absurd h (by decide), fun _ => Or.inl c⟩
    · have e : cmpNat 2 (x, y) = 2 := by
        show (if decide (x < y) = true then (0 : UInt64) else
          if decide (y < x) = true then 1 else 2) = 2
        rw [decide_eq_false (by omega), decide_eq_false (by omega)]; rfl
      rw [e]
      refine ⟨fun h hh => ?_, fun h => Or.inr ⟨c, (cmp_fold l).2 h⟩⟩
      rcases hh with h1 | ⟨_, h2⟩
      · omega
      · exact (cmp_fold l).1 h h2
    · have e : cmpNat 2 (x, y) = 1 := by
        show (if decide (x < y) = true then (0 : UInt64) else
          if decide (y < x) = true then 1 else 2) = 1
        rw [decide_eq_false (by omega), decide_eq_true c]; rfl
      rw [e, cmp_stuck l 1 (by decide)]
      refine ⟨fun _ hh => ?_, fun h => absurd rfl h⟩
      rcases hh with h1 | ⟨h1, _⟩
      · omega
      · omega

private def cmpLoop (buf : MutBytes) (stride j : UInt32) : UInt64 :=
  forRangeU64 0 stride 2 (fun (k : UInt32) (acc : UInt64) =>
    if decide (acc ≠ 2) then acc
    else
      let x := readMutU8 buf (j * stride + k)
      let y := readMutU8 buf ((j + 1) * stride + k)
      if decide (x < y) then 0 else if decide (y < x) then 1 else 2)

private def swapRec (buf : MutBytes) (stride j : UInt32) : MutBytes :=
  forRangeBytes 0 stride buf (fun k b =>
    let a := j * stride + k
    let c := (j + 1) * stride + k
    let x := readMutU8 b a
    let y := readMutU8 b c
    let b1 := writeU8 b a y
    writeU8 b1 c x)

private def cmpSwapRec (b : MutBytes) (stride j : UInt32) : MutBytes :=
  if decide ((if decide (cmpLoop b stride j = 1) then (1 : UInt64) else 0) = 1) then swapRec b stride j
  else b

private theorem sortFixed_unfold (buf : MutBytes) (count stride : UInt32) :
    llbSortFixedBytes buf count stride =
      if decide (count ≤ 1) || decide (stride = 0) then buf
      else forRangeBytes 1 count buf (fun slot b =>
        forRangeBytes 0 slot b (fun k b => cmpSwapRec b stride (slot - 1 - k))) := rfl

private theorem cmpSwapRec_pos (b : MutBytes) (stride j : UInt32) (h : cmpLoop b stride j = 1) :
    cmpSwapRec b stride j = swapRec b stride j := by
  unfold cmpSwapRec; rw [decide_eq_true h]; rfl

private theorem cmpSwapRec_neg (b : MutBytes) (stride j : UInt32) (h : cmpLoop b stride j ≠ 1) :
    cmpSwapRec b stride j = b := by
  unfold cmpSwapRec; rw [decide_eq_false h]; rfl

private def viewB (m : Nat) (b : MutBytes) (r : Nat) : List Nat :=
  lst (fun t => (b.get (UInt32.ofNat (r * m + t))).toNat) m

private theorem view_eq (m : Nat) (b : MutBytes) (r : Nat) (idx : Nat → UInt32)
    (h : ∀ t, t < m → (idx t).toNat = r * m + t) (hb : r * m + m ≤ 4294967296) :
    viewB m b r = lst (fun t => (b.get (idx t)).toNat) m :=
  lst_congr _ _ m (fun t ht => by
    rw [(ofNat_eq_iff (r * m + t) (by omega) (idx t)).mpr (h t ht).symm])

private theorem rec_idx (stride j : UInt32) (q t : Nat) (hj : j.toNat = q)
    (h : q * stride.toNat + t < 4294967296) :
    (j * stride + (0 + UInt32.ofNat t)).toNat = q * stride.toNat + t := by
  have ht : t < 4294967296 := by omega
  have hq : q * stride.toNat < 4294967296 := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul, UInt32.zero_add, ofNat_toNat_lt t ht, hj,
    Nat.mod_eq_of_lt hq]
  exact Nat.mod_eq_of_lt h

private theorem swap_loop (b0 : MutBytes) (m A : Nat) (ia ic : Nat → UInt32)
    (hA : ∀ t, t < m → (ia t).toNat = A + t) (hC : ∀ t, t < m → (ic t).toNat = A + m + t)
    (step : MutBytes → Nat → MutBytes)
    (hstep : ∀ t b, t < m → step b t =
      writeU8 (writeU8 b (ia t) (readMutU8 b (ic t))) (ic t) (readMutU8 b (ia t))) :
    (∀ t, t < m → ((List.range m).foldl step b0).get (ia t) = b0.get (ic t)) ∧
    (∀ t, t < m → ((List.range m).foldl step b0).get (ic t) = b0.get (ia t)) ∧
    (∀ i : UInt32, i.toNat < A ∨ A + 2 * m ≤ i.toNat →
      ((List.range m).foldl step b0).get i = b0.get i) := by
  have ne_of : ∀ (u v : UInt32), u.toNat ≠ v.toNat → u ≠ v :=
    fun u v h e => h (congrArg UInt32.toNat e)
  have key := foldl_range_inv
    (fun k (b : MutBytes) =>
      (∀ t, t < k → b.get (ia t) = b0.get (ic t)) ∧
      (∀ t, t < k → b.get (ic t) = b0.get (ia t)) ∧
      (∀ i : UInt32, (∀ t, t < k → i ≠ ia t) → (∀ t, t < k → i ≠ ic t) → b.get i = b0.get i))
    step m b0
    ⟨fun t h => absurd h (Nat.not_lt_zero t), fun t h => absurd h (Nat.not_lt_zero t),
      fun _ _ _ => rfl⟩ ?hs
  · obtain ⟨k1, k2, k3⟩ := key
    refine ⟨k1, k2, fun i hi => k3 i (fun t ht e => ?_) (fun t ht e => ?_)⟩
    · have := hA t ht; rw [← e] at this; omega
    · have := hC t ht; rw [← e] at this; omega
  case hs =>
    intro k b hk ⟨p1, p2, p3⟩
    rw [hstep k b hk]
    have gA := hA k hk
    have gC := hC k hk
    have ac : ia k ≠ ic k := ne_of _ _ (by omega)
    have ra : b.get (ia k) = b0.get (ia k) :=
      p3 _ (fun t ht => ne_of _ _ (by have := hA t (by omega); omega))
        (fun t ht => ne_of _ _ (by have := hC t (by omega); omega))
    have rc : b.get (ic k) = b0.get (ic k) :=
      p3 _ (fun t ht => ne_of _ _ (by have := hA t (by omega); omega))
        (fun t ht => ne_of _ _ (by have := hC t (by omega); omega))
    have get' : ∀ i, (writeU8 (writeU8 b (ia k) (readMutU8 b (ic k))) (ic k)
        (readMutU8 b (ia k))).get i =
          if i = ic k then b.get (ia k) else if i = ia k then b.get (ic k) else b.get i :=
      fun _ => rfl
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [get']
      by_cases c : t = k
      · rw [c, ite_eq_right ac, ite_eq_left rfl, rc]
      · have n1 : ia t ≠ ic k := ne_of _ _ (by have := hA t (by omega); omega)
        have n2 : ia t ≠ ia k := ne_of _ _ (by have := hA t (by omega); omega)
        rw [ite_eq_right n1, ite_eq_right n2]; exact p1 t (by omega)
    · intro t ht
      rw [get']
      by_cases c : t = k
      · rw [c, ite_eq_left rfl, ra]
      · have n1 : ic t ≠ ic k := ne_of _ _ (by have := hC t (by omega); omega)
        have n2 : ic t ≠ ia k := ne_of _ _ (by have := hC t (by omega); omega)
        rw [ite_eq_right n1, ite_eq_right n2]; exact p2 t (by omega)
    · intro i h1 h2
      rw [get', ite_eq_right (h2 k (Nat.lt_succ_self k)), ite_eq_right (h1 k (Nat.lt_succ_self k))]
      exact p3 i (fun t ht => h1 t (Nat.lt_succ_of_lt ht)) (fun t ht => h2 t (Nat.lt_succ_of_lt ht))

private theorem cmp_step (acc : UInt64) (x y : UInt8) :
    (if decide (acc ≠ 2) then acc
      else if decide (x < y) then 0 else if decide (y < x) then 1 else 2) =
      cmpNat acc (x.toNat, y.toNat) := by
  unfold cmpNat
  by_cases h : acc ≠ 2
  · rw [decide_eq_true h]; rfl
  · rw [decide_eq_false h]
    by_cases c1 : x < y
    · have c1' : (x.toNat, y.toNat).1 < (x.toNat, y.toNat).2 := UInt8.lt_iff_toNat_lt.mp c1
      rw [decide_eq_true c1, decide_eq_true c1']; rfl
    · have c1' : ¬ (x.toNat, y.toNat).1 < (x.toNat, y.toNat).2 :=
        fun hh => c1 (UInt8.lt_iff_toNat_lt.mpr hh)
      rw [decide_eq_false c1, decide_eq_false c1']
      by_cases c2 : y < x
      · have c2' : (x.toNat, y.toNat).2 < (x.toNat, y.toNat).1 := UInt8.lt_iff_toNat_lt.mp c2
        rw [decide_eq_true c2, decide_eq_true c2']
      · have c2' : ¬ (x.toNat, y.toNat).2 < (x.toNat, y.toNat).1 :=
          fun hh => c2 (UInt8.lt_iff_toNat_lt.mpr hh)
        rw [decide_eq_false c2, decide_eq_false c2']

private theorem succ_toNat (j : UInt32) (q : Nat) (hj : j.toNat = q) (hq : q + 1 < 4294967296) :
    (j + 1).toNat = q + 1 := by
  have e1 : (1 : UInt32).toNat = 1 := rfl
  rw [UInt32.toNat_add, hj, e1]; exact Nat.mod_eq_of_lt hq

private theorem cmp_spec (b : MutBytes) (stride j : UInt32) (q : Nat) (hj : j.toNat = q)
    (hb : q * stride.toNat + 2 * stride.toNat ≤ 4294967296) (hq : q + 1 < 4294967296) :
    (cmpLoop b stride j = 1 →
      ¬ Spec.lexLe (viewB stride.toNat b q) (viewB stride.toNat b (q + 1))) ∧
    (cmpLoop b stride j ≠ 1 →
      Spec.lexLe (viewB stride.toNat b q) (viewB stride.toNat b (q + 1))) := by
  have hj1 := succ_toNat j q hj hq
  have hsm : (q + 1) * stride.toNat = q * stride.toNat + stride.toNat := by
    rw [Nat.add_mul, Nat.one_mul]
  have e : cmpLoop b stride j =
      (lst (fun t => ((b.get (j * stride + (0 + UInt32.ofNat t))).toNat,
        (b.get ((j + 1) * stride + (0 + UInt32.ofNat t))).toNat)) stride.toNat).foldl cmpNat 2 := by
    have hz : (0 : UInt32).toNat = 0 := rfl
    unfold cmpLoop lst
    rw [forRangeU64_eq', List.foldl_map, hz, Nat.sub_zero]
    exact foldl_range_congr _ _ _ _ (fun k acc _ => cmp_step acc _ _)
  have f1 : (lst (fun t => ((b.get (j * stride + (0 + UInt32.ofNat t))).toNat,
        (b.get ((j + 1) * stride + (0 + UInt32.ofNat t))).toNat)) stride.toNat).map Prod.fst =
      viewB stride.toNat b q := by
    rw [view_eq stride.toNat b q (fun t => j * stride + (0 + UInt32.ofNat t))
      (fun t ht => rec_idx stride j q t hj (by omega)) (by omega)]
    unfold lst; rw [List.map_map]; rfl
  have f2 : (lst (fun t => ((b.get (j * stride + (0 + UInt32.ofNat t))).toNat,
        (b.get ((j + 1) * stride + (0 + UInt32.ofNat t))).toNat)) stride.toNat).map Prod.snd =
      viewB stride.toNat b (q + 1) := by
    rw [view_eq stride.toNat b (q + 1) (fun t => (j + 1) * stride + (0 + UInt32.ofNat t))
      (fun t ht => rec_idx stride (j + 1) (q + 1) t hj1 (by omega)) (by omega)]
    unfold lst; rw [List.map_map]; rfl
  rw [e, ← f1, ← f2]
  exact cmp_fold _

private theorem stepB (stride : UInt32) (n : Nat) (hm : 0 < stride.toNat)
    (hn : n * stride.toNat ≤ 4294967296) (b : MutBytes) (q : Nat) (hq : q + 1 < n) :
    (∀ i : UInt32, n * stride.toNat ≤ i.toNat →
      (cmpSwapRec b stride (UInt32.ofNat q)).get i = b.get i) ∧
    ((¬ Spec.lexLe (viewB stride.toNat b q) (viewB stride.toNat b (q + 1)) ∧
        viewB stride.toNat (cmpSwapRec b stride (UInt32.ofNat q)) q = viewB stride.toNat b (q + 1) ∧
        viewB stride.toNat (cmpSwapRec b stride (UInt32.ofNat q)) (q + 1) = viewB stride.toNat b q ∧
        ∀ i, i < n → i ≠ q → i ≠ q + 1 →
          viewB stride.toNat (cmpSwapRec b stride (UInt32.ofNat q)) i = viewB stride.toNat b i) ∨
     (Spec.lexLe (viewB stride.toNat b q) (viewB stride.toNat b (q + 1)) ∧
        ∀ i, i < n → viewB stride.toNat (cmpSwapRec b stride (UInt32.ofNat q)) i =
          viewB stride.toNat b i)) := by
  generalize hmd : stride.toNat = m at hm hn ⊢
  have hnle : n ≤ n * m := Nat.le_mul_of_pos_right n hm
  have hq2 : (q + 2) * m ≤ n * m := Nat.mul_le_mul_right m hq
  have hsm : (q + 1) * m = q * m + m := by rw [Nat.add_mul, Nat.one_mul]
  have hsm2 : (q + 2) * m = q * m + 2 * m := by rw [Nat.add_mul]
  have hjn : (UInt32.ofNat q).toNat = q := ofNat_toNat_lt q (by omega)
  generalize UInt32.ofNat q = j at hjn ⊢
  have hj1 := succ_toNat j q hjn (by omega)
  have cs := cmp_spec b stride j q hjn (by rw [hmd]; omega) (by omega)
  rw [hmd] at cs
  by_cases h : cmpLoop b stride j = 1
  · rw [cmpSwapRec_pos b stride j h]
    have hA : ∀ t, t < m → (j * stride + (0 + UInt32.ofNat t)).toNat = q * m + t :=
      fun t ht => by rw [← hmd]; exact rec_idx stride j q t hjn (by rw [hmd]; omega)
    have hC : ∀ t, t < m → ((j + 1) * stride + (0 + UInt32.ofNat t)).toNat = q * m + m + t :=
      fun t ht => by
        rw [← hsm, ← hmd]; exact rec_idx stride (j + 1) (q + 1) t hj1 (by rw [hmd]; omega)
    have hC' : ∀ t, t < m → ((j + 1) * stride + (0 + UInt32.ofNat t)).toNat = (q + 1) * m + t :=
      fun t ht => by rw [hsm]; exact hC t ht
    have e : swapRec b stride j = (List.range m).foldl (fun (b : MutBytes) (t : Nat) =>
        writeU8 (writeU8 b (j * stride + (0 + UInt32.ofNat t))
          (readMutU8 b ((j + 1) * stride + (0 + UInt32.ofNat t))))
          ((j + 1) * stride + (0 + UInt32.ofNat t))
          (readMutU8 b (j * stride + (0 + UInt32.ofNat t)))) b := by
      have hz : (0 : UInt32).toNat = 0 := rfl
      unfold swapRec
      rw [forRangeBytes_eq, hz, Nat.sub_zero, hmd]
    rw [e]
    obtain ⟨s1, s2, s3⟩ := swap_loop b m (q * m)
      (fun t => j * stride + (0 + UInt32.ofNat t)) (fun t => (j + 1) * stride + (0 + UInt32.ofNat t))
      hA hC _ (fun _ _ _ => rfl)
    refine ⟨fun i hi => s3 i (Or.inr (by omega)), Or.inl ⟨cs.1 h, ?_, ?_, ?_⟩⟩
    · rw [view_eq m _ q _ hA (by omega), view_eq m b (q + 1) _ hC' (by omega)]
      exact lst_congr _ _ m (fun t ht => by rw [s1 t ht])
    · rw [view_eq m _ (q + 1) _ hC' (by omega), view_eq m b q _ hA (by omega)]
      exact lst_congr _ _ m (fun t ht => by rw [s2 t ht])
    · intro i hi n1 n2
      have him : (i + 1) * m ≤ n * m := Nat.mul_le_mul_right m hi
      have him' : (i + 1) * m = i * m + m := by rw [Nat.add_mul, Nat.one_mul]
      refine lst_congr _ _ m (fun t ht => ?_)
      have ht' : (UInt32.ofNat (i * m + t)).toNat = i * m + t := ofNat_toNat_lt _ (by omega)
      rw [s3 (UInt32.ofNat (i * m + t)) ?_]
      rw [ht']
      rcases Nat.lt_or_ge i q with c | c
      · have : (i + 1) * m ≤ q * m := Nat.mul_le_mul_right m c
        exact Or.inl (by omega)
      · have c' : q + 2 ≤ i := by omega
        have : (q + 2) * m ≤ i * m := Nat.mul_le_mul_right m c'
        exact Or.inr (by omega)
  · rw [cmpSwapRec_neg b stride j h]
    exact ⟨fun _ _ => rfl, Or.inr ⟨cs.2 h, fun _ _ => rfl⟩⟩

private theorem records_eq (b : MutBytes) (n m : Nat) : Spec.records b n m = lst (viewB m b) n := rfl

theorem sortFixedBytes : Spec.SortFixedBytes := by
  intro buf count stride hfit
  rw [sortFixed_unfold]
  have hc := count.toNat_lt
  have e1 : (1 : UInt32).toNat = 1 := rfl
  have hz : (0 : UInt32).toNat = 0 := rfl
  by_cases hle : count ≤ 1
  · rw [decide_eq_true hle, Bool.true_or, ite_eq_left rfl]
    have hn : count.toNat ≤ 1 := UInt32.le_iff_toNat_le.mp hle
    refine ⟨?_, List.Perm.refl _, fun _ _ => rfl⟩
    rw [records_eq]
    exact sorted_lst Spec.lexLe _ count.toNat (fun i i' h1 h2 => by exfalso; omega)
  · by_cases hs0 : stride = 0
    · rw [decide_eq_true hs0, Bool.or_true, ite_eq_left rfl]
      refine ⟨?_, List.Perm.refl _, fun _ _ => rfl⟩
      rw [records_eq, hs0, hz]
      exact sorted_lst Spec.lexLe _ count.toNat (fun _ _ _ _ => trivial)
    · rw [decide_eq_false hle, decide_eq_false hs0, Bool.or_false,
        ite_eq_right Bool.false_ne_true, forRangeBytes_eq, e1]
      have hm : 0 < stride.toNat := by
        have hne : stride.toNat ≠ 0 := fun h => hs0 (UInt32.toNat_inj.mp h)
        omega
      generalize hnd : count.toNat = n at hc hfit ⊢
      have conv : (List.range (n - 1)).foldl (fun b k =>
            forRangeBytes 0 (1 + UInt32.ofNat k) b
              (fun k' a => cmpSwapRec a stride (1 + UInt32.ofNat k - 1 - k'))) buf =
          (List.range (n - 1)).foldl (fun b k => (List.range (k + 1)).foldl
            (fun b k' => cmpSwapRec b stride (UInt32.ofNat (k + 1 - 1 - k'))) b) buf := by
        apply foldl_range_congr
        intro k b hk
        have hs := slot_toNat k (by omega)
        rw [forRangeBytes_eq, hs, hz, Nat.sub_zero]
        apply foldl_range_congr
        intro k' b' hk'
        show cmpSwapRec b' stride (1 + UInt32.ofNat k - 1 - (0 + UInt32.ofNat k')) = _
        rw [idx_eq _ k k' hs hk']
      rw [conv, records_eq, records_eq]
      exact ins_sort Spec.lexLe lexLe_trans lexLe_total (viewB stride.toNat)
        (fun b' b : MutBytes => ∀ i : UInt32, n * stride.toNat ≤ i.toNat → b'.get i = b.get i)
        (fun _ _ _ => rfl) (fun _ _ _ h1 h2 i hi => (h1 i hi).trans (h2 i hi))
        n (fun b q => cmpSwapRec b stride (UInt32.ofNat q)) (stepB stride n hm hfit) buf

/-! ### Amount formatter -/

section Formatter
open Proofs.FreestandingKernels (selU32_eq selU64_eq bor_eq bnot_eq div10U32_eq mod10U32_eq)

private theorem forRangeU32_go_eq (step : UInt32 → UInt32 → UInt32) (fuel : Nat) :
    ∀ (cur : UInt32) (b : UInt32), forRangeU32.go step fuel cur b =
      (List.range fuel).foldl (fun a k => step (cur + UInt32.ofNat k) a) b := by
  induction fuel with
  | zero => intro cur b; rfl
  | succ fuel' ih =>
    intro cur b
    unfold forRangeU32.go
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have h0 : cur + UInt32.ofNat 0 = cur := UInt32.add_zero cur
    rw [h0, ih (cur + 1) (step cur b)]
    have hfun :
        (fun a k => step (cur + 1 + UInt32.ofNat k) a) =
          (fun a k => step (cur + UInt32.ofNat (k + 1)) a) := by
      funext a k
      have hk : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        rw [UInt32.ofNat_add, UInt32.add_comm]
        rfl
      rw [UInt32.add_assoc, hk]
    rw [hfun]

private theorem forRangeU32_eq (lo hi : UInt32) (buf : UInt32) (step : UInt32 → UInt32 → UInt32) :
    forRangeU32 lo hi buf step =
      (List.range (hi.toNat - lo.toNat)).foldl (fun b k => step (lo + UInt32.ofNat k) b) buf := by
  unfold forRangeU32
  by_cases h : lo < hi
  · rw [decide_eq_true h]
    simp only [↓reduceIte]
    rw [forRangeU32_go_eq, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr
      (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h)))]
  · rw [decide_eq_false h]
    have : hi.toNat - lo.toNat = 0 := by
      have hnl : ¬ lo.toNat < hi.toNat := fun h' => h (UInt32.lt_iff_toNat_lt.mpr h')
      omega
    rw [this]; rfl

/-! ### Amount formatter: numbers -/

private theorem lst_append {α : Type} (f : Nat → α) (a n : Nat) :
    lst f (a + n) = lst f a ++ lst (fun t => f (a + t)) n := by
  induction n with
  | zero => rw [Nat.add_zero]; exact (List.append_nil _).symm
  | succ m ih => rw [← Nat.add_assoc, lst_succ, ih, lst_succ, List.append_assoc]

private theorem lo32 (acc : UInt64) : acc.toUInt32.toNat = acc.toNat % 4294967296 :=
  UInt64.toNat_toUInt32 acc

private theorem hi32 (acc : UInt64) : (acc >>> 32).toUInt32.toNat = acc.toNat / 4294967296 := by
  have h := acc.toNat_lt
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  have e : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [e, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by omega)

private theorem pack64 (a b : UInt32) :
    ((a.toUInt64 <<< 32) ||| b.toUInt64).toNat = a.toNat * 4294967296 + b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64]
  have e : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [e, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.or_comm,
    show a.toNat * 2 ^ 32 = a.toNat <<< 32 from (Nat.shiftLeft_eq _ _).symm,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

private theorem div10_toNat (v : UInt32) : (div10U32 v).toNat = v.toNat / 10 := by
  rw [div10U32_eq, UInt32.toNat_div]; rfl

private theorem mod10_toNat (v : UInt32) : (mod10U32 v).toNat = v.toNat % 10 := by
  rw [mod10U32_eq, UInt32.toNat_mod]; rfl

private def decStep (acc : UInt64) : UInt64 :=
  if decide (acc.toUInt32 = 0) then acc
  else (((acc >>> 32).toUInt32 + 1).toUInt64 <<< 32) ||| (div10U32 acc.toUInt32).toUInt64

private theorem decLen_unfold (v : UInt32) : decLenU32 v =
    (if decide (((forRangeU64 0 10 v.toUInt64 (fun _ acc => decStep acc)) >>> 32).toUInt32 = 0)
      then (1 : UInt32)
      else ((forRangeU64 0 10 v.toUInt64 (fun _ acc => decStep acc)) >>> 32).toUInt32) := rfl

private theorem bump (acc : UInt64) (n : Nat) (hn : acc.toNat / 4294967296 = n) (h : n ≤ 9) :
    ((((acc >>> 32).toUInt32 + 1).toUInt64 <<< 32) ||| (div10U32 acc.toUInt32).toUInt64).toNat =
      (n + 1) * 4294967296 + acc.toNat % 4294967296 / 10 := by
  have e1 : (1 : UInt32).toNat = 1 := rfl
  rw [pack64, div10_toNat, lo32, UInt32.toNat_add, hi32, hn, e1, Nat.mod_eq_of_lt (by omega)]

private theorem decStep_inv (v k : Nat) (hk : k < 10) (acc : UInt64)
    (h : acc.toNat / 4294967296 ≤ k ∧ acc.toNat % 4294967296 = v / 10 ^ (acc.toNat / 4294967296) ∧
      (acc.toNat % 4294967296 = 0 ∨ acc.toNat / 4294967296 = k) ∧
      (acc.toNat / 4294967296 = 0 ∨ v / 10 ^ (acc.toNat / 4294967296 - 1) ≠ 0)) :
    (decStep acc).toNat / 4294967296 ≤ k + 1 ∧
      (decStep acc).toNat % 4294967296 = v / 10 ^ ((decStep acc).toNat / 4294967296) ∧
      ((decStep acc).toNat % 4294967296 = 0 ∨ (decStep acc).toNat / 4294967296 = k + 1) ∧
      ((decStep acc).toNat / 4294967296 = 0 ∨ v / 10 ^ ((decStep acc).toNat / 4294967296 - 1) ≠ 0) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold decStep
  by_cases hz : acc.toUInt32 = 0
  · rw [decide_eq_true hz, ite_eq_left rfl]
    have hc : acc.toNat % 4294967296 = 0 := by rw [← lo32, hz]; rfl
    exact ⟨Nat.le_succ_of_le h1, h2, Or.inl hc, h4⟩
  · rw [decide_eq_false hz, ite_eq_right Bool.false_ne_true]
    have hc : acc.toNat % 4294967296 ≠ 0 := fun e => hz (UInt32.toNat_inj.mp (by rw [lo32, e]; rfl))
    have hnk : acc.toNat / 4294967296 = k := by
      rcases h3 with h3 | h3
      · exact absurd h3 hc
      · exact h3
    generalize hn : acc.toNat / 4294967296 = n at h1 h2 h4 hnk
    generalize hcd : acc.toNat % 4294967296 = c at h2 hc
    have hclt : c < 4294967296 := by rw [← hcd]; exact Nat.mod_lt _ (by decide)
    have e := bump acc n hn (by omega)
    rw [hcd] at e
    have q1 : ((n + 1) * 4294967296 + c / 10) / 4294967296 = n + 1 := by omega
    have q2 : ((n + 1) * 4294967296 + c / 10) % 4294967296 = c / 10 := by omega
    rw [e, q1, q2]
    refine ⟨by omega, ?_, Or.inr (by omega), Or.inr ?_⟩
    · rw [h2, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · rw [Nat.add_sub_cancel, ← h2]; exact hc

private theorem decLen_spec (v : UInt32) :
    1 ≤ (decLenU32 v).toNat ∧ (decLenU32 v).toNat ≤ 10 ∧ v.toNat < 10 ^ (decLenU32 v).toNat ∧
      ((decLenU32 v).toNat = 1 ∨ 10 ^ ((decLenU32 v).toNat - 1) ≤ v.toNat) := by
  have hv := v.toNat_lt
  have hz : (0 : UInt32).toNat = 0 := rfl
  have h10 : (10 : UInt32).toNat = 10 := rfl
  have key := foldl_range_inv
    (fun k (acc : UInt64) =>
      acc.toNat / 4294967296 ≤ k ∧ acc.toNat % 4294967296 = v.toNat / 10 ^ (acc.toNat / 4294967296) ∧
      (acc.toNat % 4294967296 = 0 ∨ acc.toNat / 4294967296 = k) ∧
      (acc.toNat / 4294967296 = 0 ∨ v.toNat / 10 ^ (acc.toNat / 4294967296 - 1) ≠ 0))
    (fun (acc : UInt64) (k : Nat) => decStep acc) 10 v.toUInt64 ?h0
    (fun k acc hk hp => decStep_inv v.toNat k hk acc hp)
  · rw [decLen_unfold, forRangeU64_eq', h10, hz, Nat.sub_zero]
    generalize (List.range 10).foldl (fun (acc : UInt64) (k : Nat) => decStep acc) v.toUInt64 = r at key
    obtain ⟨k1, k2, k3, k4⟩ := key
    have hn := hi32 r
    generalize hnn : r.toNat / 4294967296 = n at k1 k2 k3 k4 hn
    have hc0 : v.toNat / 10 ^ n = 0 := by
      rcases k3 with k3 | k3
      · rw [← k2]; exact k3
      · rw [k3]; exact Nat.div_eq_of_lt (by omega)
    have hlt : v.toNat < 10 ^ n := by
      rcases Nat.lt_or_ge v.toNat (10 ^ n) with c | c
      · exact c
      · have := Nat.div_pos c (Nat.pow_pos (by decide))
        omega
    by_cases hn0 : (r >>> 32).toUInt32 = 0
    · rw [decide_eq_true hn0, ite_eq_left rfl]
      have e1 : (1 : UInt32).toNat = 1 := rfl
      have n0 : n = 0 := by rw [← hn, hn0]; rfl
      rw [n0] at hlt
      rw [e1]
      exact ⟨Nat.le_refl 1, by decide, Nat.lt_of_lt_of_le hlt (by decide), Or.inl rfl⟩
    · rw [decide_eq_false hn0, ite_eq_right Bool.false_ne_true, hn]
      have n0 : n ≠ 0 := fun e => hn0 (UInt32.toNat_inj.mp (by rw [hn, e]; rfl))
      refine ⟨by omega, k1, hlt, Or.inr ?_⟩
      rcases k4 with k4 | k4
      · exact absurd k4 n0
      · rcases Nat.lt_or_ge v.toNat (10 ^ (n - 1)) with c | c
        · exact absurd (Nat.div_eq_of_lt c) k4
        · exact c
  case h0 =>
    have e : v.toUInt64.toNat = v.toNat := UInt32.toNat_toUInt64 v
    rw [e]
    have q1 : v.toNat / 4294967296 = 0 := by omega
    have q2 : v.toNat % 4294967296 = v.toNat := by omega
    rw [q1, q2]
    exact ⟨Nat.le_refl 0, by rw [Nat.pow_zero, Nat.div_one], Or.inr rfl, Or.inl rfl⟩

/-! ### Amount formatter: digits and the parser -/

private theorem lst_length {α : Type} (f : Nat → α) (n : Nat) : (lst f n).length = n := by
  unfold lst; rw [List.length_map, List.length_range]

private theorem lst_mem {α : Type} (f : Nat → α) (n : Nat) (x : α) (h : x ∈ lst f n) :
    ∃ t, t < n ∧ f t = x := by
  obtain ⟨t, ht, e⟩ := List.mem_map.mp h
  exact ⟨t, List.mem_range.mp ht, e⟩

private theorem dvFold (b : List Nat) : ∀ x, b.foldl (fun acc c => 10 * acc + (c - 48)) x =
    x * 10 ^ b.length + b.foldl (fun acc c => 10 * acc + (c - 48)) 0 := by
  induction b with
  | nil => intro x; show x = x * 1 + 0; omega
  | cons c b ih =>
    intro x
    rw [List.foldl_cons, List.foldl_cons, ih, ih (10 * 0 + (c - 48)), List.length_cons, Nat.pow_succ]
    generalize 10 ^ b.length = P
    have e : (10 * x + (c - 48)) * P = x * (P * 10) + (10 * 0 + (c - 48)) * P := by
      rw [Nat.add_mul, Nat.mul_comm P 10, ← Nat.mul_assoc, Nat.mul_comm x 10, Nat.mul_zero,
        Nat.zero_add]
    omega

private theorem dv_append (a b : List Nat) :
    Spec.digitsValue (a ++ b) = Spec.digitsValue a * 10 ^ b.length + Spec.digitsValue b := by
  unfold Spec.digitsValue
  rw [List.foldl_append, dvFold]

/-- The `n` low decimal digits of `v`, most significant first, in ASCII. -/
private def digs (v n : Nat) : List Nat := lst (fun t => 48 + v / 10 ^ (n - 1 - t) % 10) n

private theorem digs_digit (v n c : Nat) (h : c ∈ digs v n) : Spec.isDigit c = true := by
  obtain ⟨t, _, e⟩ := lst_mem _ _ _ h
  have hm : v / 10 ^ (n - 1 - t) % 10 < 10 := Nat.mod_lt _ (by decide)
  unfold Spec.isDigit
  rw [← e, decide_eq_true (by omega), decide_eq_true (by omega)]; rfl

private theorem mod_mul10 (v P : Nat) (hP : 0 < P) : v % (10 * P) = 10 * (v / 10 % P) + v % 10 := by
  have hlt : v / 10 % P < P := Nat.mod_lt _ hP
  have hr : v % 10 < 10 := Nat.mod_lt _ (by decide)
  have h2 : P * (v / 10 / P) + v / 10 % P = v / 10 := Nat.div_add_mod _ P
  have h1 : 10 * (v / 10) + v % 10 = v := Nat.div_add_mod v 10
  generalize v / 10 = q at h1 h2 hlt ⊢
  generalize q % P = b at h2 hlt ⊢
  generalize q / P = a at h2
  generalize hrd : v % 10 = r at h1 hr ⊢
  have e : v = 10 * P * a + (10 * b + r) := by
    rw [← h1, ← h2, Nat.mul_add, ← Nat.mul_assoc, Nat.add_assoc]
  have hb : 10 * b + r < 10 * P := by omega
  rw [e, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hb

private theorem dv_digs : ∀ (n v : Nat), Spec.digitsValue (digs v n) = v % 10 ^ n
  | 0, v => by rw [Nat.pow_zero, Nat.mod_one]; rfl
  | n + 1, v => by
    unfold digs
    rw [lst_succ, dv_append]
    have e : lst (fun t => 48 + v / 10 ^ (n + 1 - 1 - t) % 10) n = digs (v / 10) n := by
      unfold digs
      refine lst_congr _ _ n (fun t ht => ?_)
      have e1 : n + 1 - 1 - t = (n - 1 - t) + 1 := by omega
      rw [e1, Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    rw [e, dv_digs n (v / 10)]
    have e2 : n + 1 - 1 - n = 0 := by omega
    have e3 : Spec.digitsValue [48 + v / 10 ^ 0 % 10] = v % 10 := by
      show 10 * 0 + (48 + v / 10 ^ 0 % 10 - 48) = v % 10
      rw [Nat.pow_zero, Nat.div_one]; omega
    rw [e2, e3, Nat.pow_succ, Nat.mul_comm (10 ^ n) 10, mod_mul10 v (10 ^ n) (Nat.pow_pos (by decide))]
    show v / 10 % 10 ^ n * 10 ^ 1 + v % 10 = _
    generalize v / 10 % 10 ^ n = z
    omega

private theorem tw_append (p : Nat → Bool) (r : List Nat)
    (hr : r = [] ∨ ∃ c t, r = c :: t ∧ p c = false) :
    ∀ a : List Nat, (∀ c, c ∈ a → p c = true) →
      (a ++ r).takeWhile p = a ∧ (a ++ r).dropWhile p = r
  | [], _ => by
    rcases hr with h | ⟨c, t, h, hc⟩
    · rw [h]; exact ⟨rfl, rfl⟩
    · rw [h, List.nil_append, List.takeWhile_cons, List.dropWhile_cons, hc]; exact ⟨rfl, rfl⟩
  | x :: a, h => by
    have hx : p x = true := h x (List.mem_cons_self ..)
    obtain ⟨i1, i2⟩ := tw_append p r hr a (fun c hc => h c (List.mem_cons_of_mem _ hc))
    rw [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, hx, i1, i2]
    exact ⟨rfl, rfl⟩

private theorem isEmpty_false (l : List Nat) (h : 0 < l.length) : l.isEmpty = false := by
  cases l with
  | nil => exact absurd h (Nat.lt_irrefl 0)
  | cons _ _ => rfl

private theorem parse_tail (sats : Nat) (T r : List Nat) (hr : (r = [] ∧ T = []) ∨ r = 32 :: T) :
    (if r.isEmpty = true then some (sats, ([] : List Nat))
      else if decide (r.head? = some 32) = true then some (sats, r.tail) else none) =
      some (sats, T) := by
  rcases hr with ⟨h1, h2⟩ | h
  · rw [h1, h2]; rfl
  · rw [h]
    have e1 : (32 :: T).isEmpty = false := rfl
    have e2 : decide ((32 :: T).head? = some 32) = true := decide_eq_true rfl
    rw [e1, ite_eq_right Bool.false_ne_true, e2, ite_eq_left rfl]; rfl

private theorem no_dot (T r : List Nat) (hr : (r = [] ∧ T = []) ∨ r = 32 :: T) :
    decide (r.head? = some 46) = false := by
  rcases hr with ⟨h1, _⟩ | h
  · rw [h1]; rfl
  · rw [h]; exact decide_eq_false (fun e => absurd (Option.some.inj e) (by decide))

/-- Text without a fractional part: digits, then nothing or a space and the ticker. -/
private theorem parse_plain (I T r : List Nat) (hI : ∀ c, c ∈ I → Spec.isDigit c = true)
    (hne : 0 < I.length) (hr : (r = [] ∧ T = []) ∨ r = 32 :: T) :
    Spec.parseAmount (I ++ r) = some (Spec.digitsValue I * 100000000, T) := by
  have hr' : r = [] ∨ ∃ c t, r = c :: t ∧ Spec.isDigit c = false := by
    rcases hr with h | h
    · exact Or.inl h.1
    · exact Or.inr ⟨32, T, h, rfl⟩
  obtain ⟨t1, t2⟩ := tw_append Spec.isDigit r hr' I hI
  have e0 : Spec.digitsValue [] = 0 := rfl
  have e8 : decide (8 < ([] : List Nat).length) = false := rfl
  unfold Spec.parseAmount
  rw [t1, t2]
  dsimp only
  rw [isEmpty_false I hne, no_dot T r hr]
  rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true, e8, Bool.or_false,
    ite_eq_right Bool.false_ne_true, e0, Nat.zero_mul, Nat.add_zero]
  exact parse_tail _ T r hr

/-- Text with a fractional part. -/
private theorem parse_frac (I F T r : List Nat) (hI : ∀ c, c ∈ I → Spec.isDigit c = true)
    (hF : ∀ c, c ∈ F → Spec.isDigit c = true) (hne : 0 < I.length) (hlen : F.length ≤ 8)
    (hr : (r = [] ∧ T = []) ∨ r = 32 :: T) :
    Spec.parseAmount (I ++ 46 :: (F ++ r)) =
      some (Spec.digitsValue I * 100000000 + Spec.digitsValue F * 10 ^ (8 - F.length), T) := by
  have hr' : r = [] ∨ ∃ c t, r = c :: t ∧ Spec.isDigit c = false := by
    rcases hr with h | h
    · exact Or.inl h.1
    · exact Or.inr ⟨32, T, h, rfl⟩
  obtain ⟨t1, t2⟩ := tw_append Spec.isDigit (46 :: (F ++ r)) (Or.inr ⟨46, F ++ r, rfl, rfl⟩) I hI
  obtain ⟨t3, t4⟩ := tw_append Spec.isDigit r hr' F hF
  have ed : decide ((46 :: (F ++ r)).head? = some 46) = true := decide_eq_true rfl
  unfold Spec.parseAmount
  rw [t1, t2]
  dsimp only
  rw [isEmpty_false I hne, ed]
  rw [ite_eq_left rfl, ite_eq_left rfl, List.tail_cons, t3, t4,
    decide_eq_false (by omega : ¬ 8 < F.length), Bool.or_false, ite_eq_right Bool.false_ne_true]
  exact parse_tail _ T r hr

/-! ### Amount formatter: what each stage writes -/

private def seg (b : MutBytes) (a n : Nat) : List Nat :=
  lst (fun t => (b.get (UInt32.ofNat (a + t))).toNat) n

/-- `b'` is `b` with the bytes `l` written from index `a`, and nothing else changed. -/
private def Writes (b' b : MutBytes) (a : Nat) (l : List Nat) : Prop :=
  seg b' a l.length = l ∧
    ∀ i : UInt32, i.toNat < a ∨ a + l.length ≤ i.toNat → b'.get i = b.get i

private theorem writes_nil (b : MutBytes) (a : Nat) : Writes b b a [] := ⟨rfl, fun _ _ => rfl⟩

private theorem writes_append (b0 b1 b2 : MutBytes) (a : Nat) (l1 l2 : List Nat)
    (hb : a + l1.length + l2.length ≤ 4294967296)
    (h1 : Writes b1 b0 a l1) (h2 : Writes b2 b1 (a + l1.length) l2) :
    Writes b2 b0 a (l1 ++ l2) := by
  obtain ⟨s1, f1⟩ := h1
  obtain ⟨s2, f2⟩ := h2
  constructor
  · rw [List.length_append]
    unfold seg
    rw [lst_append]
    have e1 : lst (fun t => (b2.get (UInt32.ofNat (a + t))).toNat) l1.length = l1 :=
      (lst_congr _ _ _ (fun t ht => by
        rw [f2 _ (Or.inl (by rw [ofNat_toNat_lt _ (by omega)]; omega))])).trans s1
    have e2 : lst (fun t => (b2.get (UInt32.ofNat (a + (l1.length + t)))).toNat) l2.length = l2 :=
      (lst_congr _ _ _ (fun t ht => by rw [Nat.add_assoc])).trans s2
    rw [e1, e2]
  · intro i hi
    rw [List.length_append] at hi
    rcases hi with h | h
    · rw [f2 i (Or.inl (by omega)), f1 i (Or.inl h)]
    · rw [f2 i (Or.inr (by omega)), f1 i (Or.inr (by omega))]

private theorem writes_one (b : MutBytes) (pos : UInt32) (v : UInt8) (a : Nat) (ha : pos.toNat = a) :
    Writes (writeU8 b pos v) b a [v.toNat] := by
  constructor
  · show [((if UInt32.ofNat (a + 0) = pos then v else b.get (UInt32.ofNat (a + 0)))).toNat] = _
    rw [Nat.add_zero, ← ha, u32_ofNat_toNat, ite_eq_left rfl]
  · intro i hi
    have ne : ¬ i = pos := fun e => by
      rw [e, ha] at hi
      rcases hi with h | h
      · omega
      · have : a + 1 ≤ a := h
        omega
    show (if i = pos then v else b.get i) = _
    rw [ite_eq_right ne]

private def maybeWrite' (cond : Bool) (out : MutBytes) (pos : UInt32) (val : UInt8) : MutBytes :=
  if cond then writeU8 out pos val else out

private theorem writes_maybe (c : Bool) (b : MutBytes) (pos : UInt32) (v : UInt8) (a : Nat)
    (ha : pos.toNat = a) :
    Writes (maybeWrite' c b pos v) b a (if c then [v.toNat] else []) := by
  cases c
  · exact writes_nil b a
  · exact writes_one b pos v a ha

private theorem goBU32_eq (step : UInt32 → MutBytes → UInt32 → MutBytes × UInt32) (fuel : Nat) :
    ∀ (cur : UInt32) (b : MutBytes) (acc : UInt32), forRangeBytesU32.go step fuel cur b acc =
      (List.range fuel).foldl (fun p k => step (cur + UInt32.ofNat k) p.1 p.2) (b, acc) := by
  induction fuel with
  | zero => intro cur b acc; rfl
  | succ fuel' ih =>
    intro cur b acc
    have e : forRangeBytesU32.go step (fuel' + 1) cur b acc =
        forRangeBytesU32.go step fuel' (cur + 1) (step cur b acc).1 (step cur b acc).2 := rfl
    rw [e, ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    have h0 : cur + UInt32.ofNat 0 = cur := UInt32.add_zero cur
    have hfun :
        (fun (p : MutBytes × UInt32) k => step (cur + 1 + UInt32.ofNat k) p.1 p.2) =
          (fun p k => step (cur + UInt32.ofNat (k + 1)) p.1 p.2) := by
      funext p k
      have hk : (1 : UInt32) + UInt32.ofNat k = UInt32.ofNat (k + 1) := by
        rw [UInt32.ofNat_add, UInt32.add_comm]
        rfl
      rw [UInt32.add_assoc, hk]
    rw [hfun, h0]
    all_goals rfl

private theorem forRangeBytesU32_eq (hi : UInt32) (buf : MutBytes) (init : UInt32)
    (step : UInt32 → MutBytes → UInt32 → MutBytes × UInt32) :
    forRangeBytesU32 0 hi buf init step =
      (List.range hi.toNat).foldl (fun p k => step (0 + UInt32.ofNat k) p.1 p.2) (buf, init) := by
  unfold forRangeBytesU32
  have hz : (0 : UInt32).toNat = 0 := rfl
  by_cases h : (0 : UInt32) < hi
  · rw [decide_eq_true h]
    simp only [↓reduceIte]
    rw [goBU32_eq, UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr
      (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp h))), hz, Nat.sub_zero]
  · rw [decide_eq_false h]
    have : hi.toNat = 0 := by
      have hnl : ¬ (0 : UInt32).toNat < hi.toNat := fun h' => h (UInt32.lt_iff_toNat_lt.mpr h')
      omega
    rw [this]; rfl

private def emitDec' (out : MutBytes) (pos v len : UInt32) : MutBytes :=
  (forRangeBytesU32 0 len out v (fun k (b : MutBytes) (cur : UInt32) =>
    (writeU8 b (pos - 1 - k) (0x30 + (mod10U32 cur).toUInt8), div10U32 cur))).1

private theorem digit_byte (cur : UInt32) :
    ((0x30 : UInt8) + (mod10U32 cur).toUInt8).toNat = 48 + cur.toNat % 10 := by
  have hm : cur.toNat % 10 < 10 := Nat.mod_lt _ (by decide)
  have e : (0x30 : UInt8).toNat = 48 := rfl
  rw [UInt8.toNat_add, UInt32.toNat_toUInt8, mod10_toNat, e, Nat.mod_eq_of_lt (by omega : cur.toNat % 10 < 256)]
  exact Nat.mod_eq_of_lt (by omega)

private theorem writes_emit (out : MutBytes) (pos v len : UInt32) (hle : len.toNat ≤ pos.toNat) :
    Writes (emitDec' out pos v len) out (pos.toNat - len.toNat) (digs v.toNat len.toNat) := by
  have hp := pos.toNat_lt
  generalize hP : pos.toNat = P at hle hp
  generalize hn : len.toNat = n at hle
  unfold emitDec'
  rw [forRangeBytesU32_eq, hn]
  have key := foldl_range_inv
    (fun k (p : MutBytes × UInt32) =>
      p.2.toNat = v.toNat / 10 ^ k ∧
      (∀ t, t < k → (p.1.get (UInt32.ofNat (P - 1 - t))).toNat = 48 + v.toNat / 10 ^ t % 10) ∧
      (∀ i : UInt32, i.toNat < P - k ∨ P ≤ i.toNat → p.1.get i = out.get i))
    (fun (p : MutBytes × UInt32) (k : Nat) =>
      (writeU8 p.1 (pos - 1 - (0 + UInt32.ofNat k)) (0x30 + (mod10U32 p.2).toUInt8), div10U32 p.2))
    n (out, v) ⟨by rw [Nat.pow_zero, Nat.div_one], fun t h => absurd h (Nat.not_lt_zero t),
      fun _ _ => rfl⟩ ?hs
  · obtain ⟨_, k2, k3⟩ := key
    constructor
    · unfold digs seg
      rw [lst_length]
      refine lst_congr _ _ n (fun t ht => ?_)
      have e : P - n + t = P - 1 - (n - 1 - t) := by omega
      rw [e]; exact k2 (n - 1 - t) (by omega)
    · intro i hi
      unfold digs at hi
      rw [lst_length] at hi
      rcases hi with h | h
      · exact k3 i (Or.inl h)
      · exact k3 i (Or.inr (by omega))
  case hs =>
    intro k p hk ⟨p1, p2, p3⟩
    have hidx : pos - 1 - (0 + UInt32.ofNat k) = UInt32.ofNat (P - 1 - k) := by
      have := idx_eq pos (P - 1) k (by omega) (by omega)
      rw [this]
      have e : P - 1 + 1 - 1 - k = P - 1 - k := by omega
      rw [e]
    have hidxn : (UInt32.ofNat (P - 1 - k)).toNat = P - 1 - k := ofNat_toNat_lt _ (by omega)
    have get' : ∀ i, (writeU8 p.1 (UInt32.ofNat (P - 1 - k))
        (0x30 + (mod10U32 p.2).toUInt8)).get i =
          if i = UInt32.ofNat (P - 1 - k) then 0x30 + (mod10U32 p.2).toUInt8 else p.1.get i :=
      fun _ => rfl
    show (div10U32 p.2).toNat = _ ∧ (∀ t, t < k + 1 →
        ((writeU8 p.1 (pos - 1 - (0 + UInt32.ofNat k)) (0x30 + (mod10U32 p.2).toUInt8)).get
          (UInt32.ofNat (P - 1 - t))).toNat = _) ∧
      (∀ i : UInt32, i.toNat < P - (k + 1) ∨ P ≤ i.toNat →
        (writeU8 p.1 (pos - 1 - (0 + UInt32.ofNat k)) (0x30 + (mod10U32 p.2).toUInt8)).get i = _)
    rw [hidx]
    refine ⟨?_, ?_, ?_⟩
    · rw [div10_toNat, p1, Nat.div_div_eq_div_mul, Nat.pow_succ]
    · intro t ht
      rw [get']
      by_cases c : t = k
      · rw [c, ite_eq_left rfl, digit_byte, p1]
      · have ne : ¬ UInt32.ofNat (P - 1 - t) = UInt32.ofNat (P - 1 - k) := fun e => by
          have := congrArg UInt32.toNat e
          rw [hidxn, ofNat_toNat_lt _ (by omega)] at this
          omega
        rw [ite_eq_right ne]; exact p2 t (by omega)
    · intro i hi
      have ne : ¬ i = UInt32.ofNat (P - 1 - k) := fun e => by
        rw [e, hidxn] at hi
        rcases hi with h | h
        · omega
        · omega
      rw [get', ite_eq_right ne]
      rcases hi with h | h
      · exact p3 i (Or.inl (by omega))
      · exact p3 i (Or.inr h)

private def copyTicker' (ticker : ConstBytes) (tickerLen : UInt32) (out : MutBytes) (pos : UInt32) : MutBytes :=
  forRangeBytes 0 tickerLen out (fun k b => writeU8 b (pos + k) (readU8 ticker k))

private theorem writes_ticker (ticker : ConstBytes) (tl : UInt32) (out : MutBytes) (pos : UInt32)
    (hfit : pos.toNat + tl.toNat < 4294967296) :
    Writes (copyTicker' ticker tl out pos) out pos.toNat (Spec.bytes ticker tl.toNat) := by
  have hz : (0 : UInt32).toNat = 0 := rfl
  have blen : (Spec.bytes ticker tl.toNat).length = tl.toNat := lst_length _ _
  generalize hP : pos.toNat = P at hfit
  generalize hn : tl.toNat = n at hfit blen
  unfold copyTicker'
  rw [forRangeBytes_eq, hz, Nat.sub_zero, hn]
  have hix : ∀ t, t < n → (pos + (0 + UInt32.ofNat t)).toNat = P + t := fun t ht => by
    rw [UInt32.toNat_add, UInt32.zero_add, ofNat_toNat_lt t (by omega), hP]
    exact Nat.mod_eq_of_lt (by omega)
  have key := foldl_range_inv
    (fun k (b : MutBytes) =>
      (∀ t, t < k → b.get (UInt32.ofNat (P + t)) = ticker.get (UInt32.ofNat t)) ∧
      (∀ i : UInt32, i.toNat < P ∨ P + k ≤ i.toNat → b.get i = out.get i))
    (fun (b : MutBytes) (k : Nat) =>
      writeU8 b (pos + (0 + UInt32.ofNat k)) (readU8 ticker (0 + UInt32.ofNat k)))
    n out ⟨fun t h => absurd h (Nat.not_lt_zero t), fun _ _ => rfl⟩ ?hs
  · obtain ⟨k1, k2⟩ := key
    constructor
    · rw [blen]
      exact lst_congr _ _ n (fun t ht => by rw [k1 t ht])
    · intro i hi
      rw [blen] at hi
      exact k2 i hi
  case hs =>
    intro k b hk ⟨p1, p2⟩
    have hidx : pos + (0 + UInt32.ofNat k) = UInt32.ofNat (P + k) :=
      ((ofNat_eq_iff (P + k) (by omega) _).mpr (hix k hk).symm).symm
    have get' : ∀ i, (writeU8 b (UInt32.ofNat (P + k)) (readU8 ticker (0 + UInt32.ofNat k))).get i =
        if i = UInt32.ofNat (P + k) then ticker.get (0 + UInt32.ofNat k) else b.get i := fun _ => rfl
    rw [hidx]
    refine ⟨?_, ?_⟩
    · intro t ht
      rw [get']
      by_cases c : t = k
      · rw [c, ite_eq_left rfl, UInt32.zero_add]
      · have ne : ¬ UInt32.ofNat (P + t) = UInt32.ofNat (P + k) := fun e => by
          have := congrArg UInt32.toNat e
          rw [ofNat_toNat_lt _ (by omega), ofNat_toNat_lt _ (by omega)] at this
          omega
        rw [ite_eq_right ne]; exact p1 t (by omega)
    · intro i hi
      have ne : ¬ i = UInt32.ofNat (P + k) := fun e => by
        rw [e, ofNat_toNat_lt _ (by omega)] at hi
        rcases hi with h | h
        · omega
        · omega
      rw [get', ite_eq_right ne]
      rcases hi with h | h
      · exact p2 i (Or.inl h)
      · exact p2 i (Or.inr (by omega))

/-! ### Amount formatter: trailing zeros and the shown fraction -/

private def fracStep (acc : UInt64) : UInt64 :=
  selU64 (bor (decide (acc.toUInt32 = 0)) (decide (mod10U32 acc.toUInt32 ≠ 0))) acc
    ((((acc >>> 32).toUInt32 + 1).toUInt64 <<< 32) ||| (div10U32 acc.toUInt32).toUInt64)

private theorem fracSig_unfold (f : UInt32) : fracSigLen f =
    selU32 (decide (f = 0)) 0
      ((8 : UInt32) - ((forRangeU64 0 8 f.toUInt64 (fun _ acc => fracStep acc)) >>> 32).toUInt32) := rfl

private theorem fracStep_inv (F k : Nat) (hk : k < 8) (acc : UInt64)
    (h : acc.toNat / 4294967296 ≤ k ∧ acc.toNat % 4294967296 = F / 10 ^ (acc.toNat / 4294967296) ∧
      F / 10 ^ (acc.toNat / 4294967296) * 10 ^ (acc.toNat / 4294967296) = F) :
    (fracStep acc).toNat / 4294967296 ≤ k + 1 ∧
      (fracStep acc).toNat % 4294967296 = F / 10 ^ ((fracStep acc).toNat / 4294967296) ∧
      F / 10 ^ ((fracStep acc).toNat / 4294967296) * 10 ^ ((fracStep acc).toNat / 4294967296) = F := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold fracStep
  rw [selU64_eq, bor_eq]
  by_cases hz : acc.toUInt32 = 0
  · rw [decide_eq_true hz, Bool.true_or, ite_eq_left rfl]
    exact ⟨Nat.le_succ_of_le h1, h2, h3⟩
  · by_cases hm : mod10U32 acc.toUInt32 ≠ 0
    · rw [decide_eq_false hz, decide_eq_true hm, Bool.false_or, ite_eq_left rfl]
      exact ⟨Nat.le_succ_of_le h1, h2, h3⟩
    · rw [decide_eq_false hz, decide_eq_false hm, Bool.false_or, ite_eq_right Bool.false_ne_true]
      have hm0 : mod10U32 acc.toUInt32 = 0 := Decidable.not_not.mp hm
      have hc10 : acc.toNat % 4294967296 % 10 = 0 := by
        rw [← lo32, ← mod10_toNat, hm0]; rfl
      generalize hn : acc.toNat / 4294967296 = n at h1 h2 h3
      generalize hcd : acc.toNat % 4294967296 = c at h2 hc10
      have hclt : c < 4294967296 := by rw [← hcd]; exact Nat.mod_lt _ (by decide)
      have e := bump acc n hn (by omega)
      rw [hcd] at e
      have q1 : ((n + 1) * 4294967296 + c / 10) / 4294967296 = n + 1 := by omega
      have q2 : ((n + 1) * 4294967296 + c / 10) % 4294967296 = c / 10 := by omega
      have ediv : F / 10 ^ (n + 1) = c / 10 := by
        rw [h2, Nat.div_div_eq_div_mul, Nat.pow_succ]
      rw [e, q1, q2, ediv]
      refine ⟨by omega, rfl, ?_⟩
      have hc : c / 10 * 10 = c := by omega
      rw [← h2] at h3
      rw [Nat.pow_succ, Nat.mul_comm (10 ^ n) 10, ← Nat.mul_assoc, hc, h3]

private theorem fracSig_spec (f : UInt32) :
    (fracSigLen f).toNat ≤ 8 ∧ (f = 0 → fracSigLen f = 0) ∧
      f.toNat / 10 ^ (8 - (fracSigLen f).toNat) * 10 ^ (8 - (fracSigLen f).toNat) = f.toNat := by
  have hv := f.toNat_lt
  have hz : (0 : UInt32).toNat = 0 := rfl
  have h8 : (8 : UInt32).toNat = 8 := rfl
  rw [fracSig_unfold, selU32_eq]
  by_cases h0 : f = 0
  · rw [decide_eq_true h0, ite_eq_left rfl, h0]
    exact ⟨by decide, fun _ => rfl, by decide⟩
  · rw [decide_eq_false h0, ite_eq_right Bool.false_ne_true]
    have key := foldl_range_inv
      (fun k (acc : UInt64) =>
        acc.toNat / 4294967296 ≤ k ∧
        acc.toNat % 4294967296 = f.toNat / 10 ^ (acc.toNat / 4294967296) ∧
        f.toNat / 10 ^ (acc.toNat / 4294967296) * 10 ^ (acc.toNat / 4294967296) = f.toNat)
      (fun (acc : UInt64) (k : Nat) => fracStep acc) 8 f.toUInt64 ?h0
      (fun k acc hk hp => fracStep_inv f.toNat k hk acc hp)
    · rw [forRangeU64_eq', h8, hz, Nat.sub_zero]
      generalize (List.range 8).foldl (fun (acc : UInt64) (k : Nat) => fracStep acc) f.toUInt64 = r at key
      obtain ⟨k1, _, k3⟩ := key
      have hn := hi32 r
      generalize r.toNat / 4294967296 = n at k1 k3 hn
      have hle : (r >>> 32).toUInt32 ≤ 8 := UInt32.le_iff_toNat_le.mpr (by rw [hn, h8]; exact k1)
      have es : ((8 : UInt32) - (r >>> 32).toUInt32).toNat = 8 - n := by
        rw [UInt32.toNat_sub_of_le _ _ hle, hn, h8]
      rw [es]
      have e2 : 8 - (8 - n) = n := by omega
      rw [e2]
      exact ⟨by omega, fun e => absurd e h0, k3⟩
    case h0 =>
      have e : f.toUInt64.toNat = f.toNat := UInt32.toNat_toUInt64 f
      rw [e]
      have q1 : f.toNat / 4294967296 = 0 := by omega
      have q2 : f.toNat % 4294967296 = f.toNat := by omega
      rw [q1, q2, Nat.pow_zero, Nat.div_one, Nat.mul_one]
      exact ⟨Nat.le_refl 0, rfl, rfl⟩

private theorem div_iter (v : UInt32) (n : Nat) :
    ((List.range n).foldl (fun (b : UInt32) (_ : Nat) => div10U32 b) v).toNat = v.toNat / 10 ^ n :=
  foldl_range_inv (fun k (b : UInt32) => b.toNat = v.toNat / 10 ^ k)
    (fun (b : UInt32) (_ : Nat) => div10U32 b) n v (by rw [Nat.pow_zero, Nat.div_one])
    (fun k b _ hp => by
      show (div10U32 b).toNat = _
      rw [div10_toNat, hp, Nat.div_div_eq_div_mul, Nat.pow_succ])

private theorem format_unfold (amount : UInt64) (ticker : ConstBytes) (tickerLen : UInt32)
    (padFrac8 : UInt8) (out : MutBytes) (outCap : UInt32) :
    llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap =
      if decide (256 < tickerLen) then (out, 0)
      else
        let q := llbSatsDiv1e8 amount
        let frac := llbSatsMod1e8 amount
        let qHi := (llbSatsDiv1e8 q).toUInt32
        let qLo := llbSatsMod1e8 q
        let hiZero := decide (qHi = 0)
        let hiLen := selU32 hiZero 0 (decLenU32 qHi)
        let loLen := selU32 hiZero (decLenU32 qLo) 8
        let intLen := hiLen + loLen
        let pad := bnot (decide (padFrac8 = 0))
        let showFrac := bor pad (bnot (decide (frac = 0)))
        let fracLen := selU32 pad 8 (fracSigLen frac)
        let dotLen : UInt32 := showFrac.toUInt32
        let hasTicker := bnot (decide (tickerLen = 0))
        let spaceLen : UInt32 := hasTicker.toUInt32
        let total := intLen + dotLen + fracLen + spaceLen + tickerLen
        if decide (outCap ≤ total) then (out, 0)
        else
          let o1 := emitDec' out hiLen qHi hiLen
          let o2 := emitDec' o1 (hiLen + loLen) qLo loLen
          let o3 := maybeWrite' showFrac o2 intLen 0x2E
          let drop := selU32 pad 0 (8 - fracLen)
          let fracShown := forRangeU32 0 drop frac (fun _ cur => div10U32 cur)
          let emitFracLen := selU32 showFrac fracLen 0
          let o4 := emitDec' o3 (intLen + 1 + emitFracLen) fracShown emitFracLen
          let o5 := maybeWrite' hasTicker o4 (intLen + dotLen + fracLen) 0x20
          let o6 := copyTicker' ticker tickerLen o5 (intLen + dotLen + fracLen + spaceLen)
          (writeU8 o6 total 0, total) := rfl

private theorem written_eq (b : MutBytes) (n : Nat) : Spec.written b n = seg b 0 n := by
  unfold Spec.written seg lst
  exact lst_congr _ _ n (fun t _ => by rw [Nat.zero_add])

private theorem toNat_div1e8 (a : UInt64) : (llbSatsDiv1e8 a).toNat = a.toNat / 100000000 :=
  (splitBtc a).1

private theorem toNat_mod1e8 (a : UInt64) : (llbSatsMod1e8 a).toNat = a.toNat % 100000000 :=
  (splitBtc a).2

private theorem sats_parts (amount : UInt64) :
    let q := llbSatsDiv1e8 amount
    let frac := llbSatsMod1e8 amount
    let qHi := (llbSatsDiv1e8 q).toUInt32
    let qLo := llbSatsMod1e8 q
    q.toNat = amount.toNat / 100000000 ∧
    frac.toNat = amount.toNat % 100000000 ∧
    frac.toNat < 100000000 ∧
    qHi.toNat = q.toNat / 100000000 ∧
    qHi.toNat ≤ 1844 ∧
    qLo.toNat = q.toNat % 100000000 ∧
    qLo.toNat < 100000000 ∧
    q.toNat = qHi.toNat * 100000000 + qLo.toNat ∧
    amount.toNat = q.toNat * 100000000 + frac.toNat := by
  dsimp only
  have hlt := amount.toNat_lt
  have hq := toNat_div1e8 amount
  have hf := toNat_mod1e8 amount
  have hqHi64 := toNat_div1e8 (llbSatsDiv1e8 amount)
  have hqLo := toNat_mod1e8 (llbSatsDiv1e8 amount)
  have hqHi : (llbSatsDiv1e8 (llbSatsDiv1e8 amount)).toUInt32.toNat =
      (llbSatsDiv1e8 amount).toNat / 100000000 := by
    rw [lo32, hqHi64]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hq, hf, by omega, hqHi, by omega, hqLo, by omega, ?_, ?_⟩
  · omega
  · omega

private theorem bool_toUInt32_toNat (b : Bool) : b.toUInt32.toNat = if b then 1 else 0 := by
  cases b <;> rfl

private theorem digs_length (v n : Nat) : (digs v n).length = n := lst_length _ n

private theorem int_stage (out : MutBytes) (qHi qLo : UInt32) (q : Nat)
    (hqHi : qHi.toNat ≤ 1844) (hqLo : qLo.toNat < 100000000)
    (hq : q = qHi.toNat * 100000000 + qLo.toNat) :
    let hiZero := decide (qHi = 0)
    let hiLen := selU32 hiZero 0 (decLenU32 qHi)
    let loLen := selU32 hiZero (decLenU32 qLo) 8
    let intLen := hiLen + loLen
    let o1 := emitDec' out hiLen qHi hiLen
    let o2 := emitDec' o1 intLen qLo loLen
    let I := digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat
    1 ≤ intLen.toNat ∧ intLen.toNat ≤ 12 ∧ I.length = intLen.toNat ∧
    (∀ c, c ∈ I → Spec.isDigit c = true) ∧
    Spec.digitsValue I = q ∧
    Writes o2 out 0 I := by
  dsimp only
  have dHi := decLen_spec qHi
  have dLo := decLen_spec qLo
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have hz : (0 : UInt32).toNat = 0 := rfl
  have hhiLe4 : (decLenU32 qHi).toNat ≤ 4 := by
    rcases dHi.2.2.2 with h1 | hge
    · omega
    · rcases Nat.lt_or_ge 4 (decLenU32 qHi).toNat with hgt | hle
      · have h5 : 4 ≤ (decLenU32 qHi).toNat - 1 := by omega
        have hp : 10 ^ 4 ≤ 10 ^ ((decLenU32 qHi).toNat - 1) := Nat.pow_le_pow_right (by decide) h5
        omega
      · exact hle
  have hloLe8 : (decLenU32 qLo).toNat ≤ 8 := by
    rcases dLo.2.2.2 with h1 | hge
    · omega
    · rcases Nat.lt_or_ge 8 (decLenU32 qLo).toNat with hgt | hle
      · have h8' : 8 ≤ (decLenU32 qLo).toNat - 1 := by omega
        have hp : 10 ^ 8 ≤ 10 ^ ((decLenU32 qLo).toNat - 1) := Nat.pow_le_pow_right (by decide) h8'
        omega
      · exact hle
  generalize hiLen_def : selU32 (decide (qHi = 0)) 0 (decLenU32 qHi) = hiLen
  generalize loLen_def : selU32 (decide (qHi = 0)) (decLenU32 qLo) 8 = loLen
  have hbounds : (hiLen.toNat = 0 ∧ loLen.toNat = (decLenU32 qLo).toNat ∧ qHi.toNat = 0) ∨
      (hiLen.toNat = (decLenU32 qHi).toNat ∧ loLen.toNat = 8) := by
    rw [selU32_eq] at hiLen_def loLen_def
    by_cases h0 : qHi = 0
    · rw [decide_eq_true h0, ite_eq_left rfl] at hiLen_def loLen_def
      exact Or.inl ⟨by rw [← hiLen_def, hz], by rw [← loLen_def], by rw [h0]; rfl⟩
    · rw [decide_eq_false h0, ite_eq_right Bool.false_ne_true] at hiLen_def loLen_def
      exact Or.inr ⟨by rw [← hiLen_def], by rw [← loLen_def, h8]⟩
  have hintAdd : (hiLen + loLen).toNat = hiLen.toNat + loLen.toNat := by
    rw [UInt32.toNat_add]
    rcases hbounds with ⟨h1, h2, _⟩ | ⟨h1, h2⟩
    · exact Nat.mod_eq_of_lt (by omega)
    · exact Nat.mod_eq_of_lt (by omega)
  have h1le_l : 1 ≤ (hiLen + loLen).toNat := by
    rcases hbounds with ⟨h1, h2, _⟩ | ⟨h1, h2⟩ <;> omega
  have h1le_r : (hiLen + loLen).toNat ≤ 12 := by
    rcases hbounds with ⟨h1, h2, _⟩ | ⟨h1, h2⟩ <;> omega
  have hlenI : (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat).length = (hiLen + loLen).toNat := by
    rw [List.length_append, digs_length, digs_length, hintAdd]
  have hdigI : ∀ c, c ∈ digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat → Spec.isDigit c = true := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact digs_digit _ _ c h
    · exact digs_digit _ _ c h
  have hvalI : Spec.digitsValue (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat) = q := by
    rw [dv_append, dv_digs, dv_digs, digs_length]
    rcases hbounds with ⟨h1, h2, hq0⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hq0, Nat.zero_mod, Nat.zero_mul, Nat.zero_add,
        Nat.mod_eq_of_lt dLo.2.2.1, hq, hq0, Nat.zero_mul, Nat.zero_add]
    · rw [h1, h2, Nat.mod_eq_of_lt dHi.2.2.1, Nat.mod_eq_of_lt hqLo]
      exact hq.symm
  have w1 : Writes (emitDec' out hiLen qHi hiLen) out 0 (digs qHi.toNat hiLen.toNat) := by
    have := writes_emit out hiLen qHi hiLen (Nat.le_refl _)
    rwa [Nat.sub_self] at this
  have w2 : Writes (emitDec' (emitDec' out hiLen qHi hiLen) (hiLen + loLen) qLo loLen)
      (emitDec' out hiLen qHi hiLen) hiLen.toNat (digs qLo.toNat loLen.toNat) := by
    have := writes_emit (emitDec' out hiLen qHi hiLen) (hiLen + loLen) qLo loLen (by omega)
    have hsub : (hiLen + loLen).toNat - loLen.toNat = hiLen.toNat := by omega
    rwa [hsub] at this
  have w12 : Writes (emitDec' (emitDec' out hiLen qHi hiLen) (hiLen + loLen) qLo loLen) out 0
      (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat) := by
    have := writes_append out (emitDec' out hiLen qHi hiLen)
      (emitDec' (emitDec' out hiLen qHi hiLen) (hiLen + loLen) qLo loLen)
      0 (digs qHi.toNat hiLen.toNat) (digs qLo.toNat loLen.toNat)
      (by rw [digs_length, digs_length]; omega) w1 (by rw [Nat.zero_add, digs_length]; exact w2)
    exact this
  exact ⟨h1le_l, h1le_r, hlenI, hdigI, hvalI, w12⟩

private theorem frac_stage (o2 : MutBytes) (intLen : UInt32) (padFrac8 : UInt8) (frac : UInt32)
    (hint : intLen.toNat ≤ 12) (hfrac : frac.toNat < 100000000) :
    let pad := bnot (decide (padFrac8 = 0))
    let showFrac := bor pad (bnot (decide (frac = 0)))
    let fracLen := selU32 pad 8 (fracSigLen frac)
    let dotLen : UInt32 := showFrac.toUInt32
    let o3 := maybeWrite' showFrac o2 intLen 0x2E
    let drop := selU32 pad 0 (8 - fracLen)
    let fracShown := forRangeU32 0 drop frac (fun _ cur => div10U32 cur)
    let emitFracLen := selU32 showFrac fracLen 0
    let o4 := emitDec' o3 (intLen + 1 + emitFracLen) fracShown emitFracLen
    let F := digs fracShown.toNat emitFracLen.toNat
    dotLen.toNat + fracLen.toNat ≤ 9 ∧
    (intLen + dotLen + fracLen).toNat = intLen.toNat + dotLen.toNat + fracLen.toNat ∧
    ((showFrac = false ∧ frac.toNat = 0 ∧ dotLen.toNat = 0 ∧ fracLen.toNat = 0 ∧
        Writes o4 o2 intLen.toNat []) ∨
     (showFrac = true ∧ dotLen.toNat = 1 ∧ F.length = fracLen.toNat ∧ fracLen.toNat ≤ 8 ∧
        (∀ c, c ∈ F → Spec.isDigit c = true) ∧
        Spec.digitsValue F * 10 ^ (8 - F.length) = frac.toNat ∧
        Writes o4 o2 intLen.toNat (46 :: F))) := by
  dsimp only
  have fs := fracSig_spec frac
  have h8 : (8 : UInt32).toNat = 8 := rfl
  have hz : (0 : UInt32).toNat = 0 := rfl
  have h1 : (1 : UInt32).toNat = 1 := rfl
  have h46 : (0x2E : UInt8).toNat = 46 := rfl
  generalize hpad : bnot (decide (padFrac8 = 0)) = pad
  generalize hsf : bor pad (bnot (decide (frac = 0))) = showFrac
  generalize hfl : selU32 pad 8 (fracSigLen frac) = fracLen
  generalize hdl : showFrac.toUInt32 = dotLen
  generalize hdrop : selU32 pad 0 (8 - fracLen) = drop
  generalize hfs : forRangeU32 0 drop frac (fun _ cur => div10U32 cur) = fracShown
  generalize hefl : selU32 showFrac fracLen 0 = emitFracLen
  have hfs_val : fracShown.toNat = frac.toNat / 10 ^ drop.toNat := by
    rw [← hfs, forRangeU32_eq, hz, Nat.sub_zero]
    exact div_iter frac drop.toNat
  have hf_cases : (showFrac = false ∧ frac.toNat = 0 ∧ dotLen.toNat = 0 ∧ fracLen.toNat = 0 ∧ emitFracLen.toNat = 0) ∨
      (showFrac = true ∧ dotLen.toNat = 1 ∧ emitFracLen.toNat = fracLen.toNat ∧
        fracLen.toNat ≤ 8 ∧ drop.toNat = 8 - fracLen.toNat ∧
        frac.toNat / 10 ^ (8 - fracLen.toNat) * 10 ^ (8 - fracLen.toNat) = frac.toNat) := by
    rw [bor_eq, bnot_eq] at hsf
    rw [selU32_eq] at hfl hdrop hefl
    cases pad
    · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hsf hfl hdrop
      by_cases hf0 : frac = 0
      · rw [decide_eq_true hf0, Bool.not_true] at hsf
        subst hsf
        simp only [Bool.false_eq_true, ↓reduceIte] at hefl
        refine Or.inl ⟨rfl, by rw [hf0]; rfl, by rw [← hdl]; rfl, ?_, by rw [← hefl]; rfl⟩
        rw [← hfl, fs.2.1 hf0]; rfl
      · rw [decide_eq_false hf0, Bool.not_false] at hsf
        subst hsf
        simp only [↓reduceIte] at hefl
        have hfl_le : fracLen ≤ 8 := UInt32.le_iff_toNat_le.mpr (by rw [← hfl, h8]; exact fs.1)
        have hdrop_nat : drop.toNat = 8 - fracLen.toNat := by
          rw [← hdrop, UInt32.toNat_sub_of_le _ _ hfl_le, h8]
        exact Or.inr ⟨rfl, by rw [← hdl]; rfl, by rw [← hefl], by rw [← hfl]; exact fs.1,
          hdrop_nat, by rw [← hfl]; exact fs.2.2⟩
    · simp only [Bool.true_or, ↓reduceIte] at hsf hfl hdrop
      subst hsf
      simp only [↓reduceIte] at hefl
      exact Or.inr ⟨rfl, by rw [← hdl]; rfl, by rw [← hefl], by rw [← hfl, h8]; exact Nat.le_refl 8,
        by rw [← hdrop, ← hfl, h8, hz], by rw [← hfl, h8, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.mul_one]⟩
  have hdf_le : dotLen.toNat + fracLen.toNat ≤ 9 := by
    rcases hf_cases with ⟨_, _, d0, f0, _⟩ | ⟨_, d1, _, fle, _, _⟩ <;> omega
  have hdf_add : (intLen + dotLen + fracLen).toNat = intLen.toNat + dotLen.toNat + fracLen.toNat := by
    rw [UInt32.toNat_add, UInt32.toNat_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have w3 : Writes (maybeWrite' showFrac o2 intLen 0x2E) o2 intLen.toNat
      (if showFrac then [46] else []) := by
    have := writes_maybe showFrac o2 intLen 0x2E intLen.toNat rfl
    rwa [h46] at this
  have hpos4 : (intLen + 1 + emitFracLen).toNat = intLen.toNat + 1 + emitFracLen.toNat := by
    have hefl_le : emitFracLen.toNat ≤ 8 := by
      rcases hf_cases with ⟨_, _, _, _, e0⟩ | ⟨_, _, eeq, fle, _, _⟩ <;> omega
    rw [UInt32.toNat_add, UInt32.toNat_add, h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have w4 : Writes (emitDec' (maybeWrite' showFrac o2 intLen 0x2E) (intLen + 1 + emitFracLen) fracShown emitFracLen)
      (maybeWrite' showFrac o2 intLen 0x2E) (intLen.toNat + 1)
      (digs fracShown.toNat emitFracLen.toNat) := by
    have := writes_emit (maybeWrite' showFrac o2 intLen 0x2E) (intLen + 1 + emitFracLen) fracShown emitFracLen (by omega)
    have hsub : (intLen + 1 + emitFracLen).toNat - emitFracLen.toNat = intLen.toNat + 1 := by omega
    rwa [hsub] at this
  refine ⟨hdf_le, hdf_add, ?_⟩
  rcases hf_cases with ⟨hsf0, hf0, hd0, hfl0, he0⟩ | ⟨hsf1, hd1, hefl_eq, hfl_le, hdrop_eq, hdiv_mul⟩
  · left
    rw [hsf0] at w3 w4 ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at w3
    have w4' : Writes (emitDec' (maybeWrite' false o2 intLen 0x2E) (intLen + 1 + emitFracLen) fracShown emitFracLen)
        (maybeWrite' false o2 intLen 0x2E) intLen.toNat [] := by
      have hdig0 : digs fracShown.toNat emitFracLen.toNat = [] := by
        rw [he0]; rfl
      rw [hdig0] at w4
      exact ⟨rfl, fun i _ => w4.2 i (by rw [List.length_nil]; omega)⟩
    have w34 := writes_append o2 (maybeWrite' false o2 intLen 0x2E)
      (emitDec' (maybeWrite' false o2 intLen 0x2E) (intLen + 1 + emitFracLen) fracShown emitFracLen)
      intLen.toNat [] [] (by rw [List.length_nil]; omega) w3 (by rw [List.length_nil, Nat.add_zero]; exact w4')
    exact ⟨rfl, hf0, hd0, hfl0, w34⟩
  · right
    rw [hsf1] at w3 w4 ⊢
    simp only [↓reduceIte] at w3
    have hF_len : (digs fracShown.toNat emitFracLen.toNat).length = fracLen.toNat := by
      rw [digs_length, hefl_eq]
    have hF_dig : ∀ c, c ∈ digs fracShown.toNat emitFracLen.toNat → Spec.isDigit c = true :=
      fun c hc => digs_digit _ _ c hc
    have hF_val : Spec.digitsValue (digs fracShown.toNat emitFracLen.toNat) *
        10 ^ (8 - (digs fracShown.toNat emitFracLen.toNat).length) = frac.toNat := by
      rw [dv_digs, digs_length, hefl_eq, hfs_val, hdrop_eq]
      have hlt_pow : frac.toNat / 10 ^ (8 - fracLen.toNat) < 10 ^ fracLen.toNat := by
        have hp : 10 ^ (8 - fracLen.toNat) * 10 ^ fracLen.toNat = 100000000 := by
          rw [← Nat.pow_add]
          have e8 : 8 - fracLen.toNat + fracLen.toNat = 8 := by omega
          rw [e8]
        rcases Nat.lt_or_ge (frac.toNat / 10 ^ (8 - fracLen.toNat)) (10 ^ fracLen.toNat) with c | c
        · exact c
        · have hge := Nat.mul_le_mul_right (10 ^ (8 - fracLen.toNat)) c
          rw [hdiv_mul, Nat.mul_comm, hp] at hge
          omega
      rw [Nat.mod_eq_of_lt hlt_pow, hdiv_mul]
    have w34 := writes_append o2 (maybeWrite' true o2 intLen 0x2E)
      (emitDec' (maybeWrite' true o2 intLen 0x2E) (intLen + 1 + emitFracLen) fracShown emitFracLen)
      intLen.toNat [46] (digs fracShown.toNat emitFracLen.toNat)
      (by rw [List.length_singleton, hF_len]; omega) w3 (by rw [List.length_singleton]; exact w4)
    exact ⟨rfl, hd1, hF_len, hfl_le, hF_dig, hF_val, w34⟩

private theorem bytes_length (t : ConstBytes) (n : Nat) : (Spec.bytes t n).length = n := lst_length _ n

private theorem ticker_stage (o4 : MutBytes) (pos : UInt32) (ticker : ConstBytes) (tickerLen : UInt32)
    (hpos : pos.toNat ≤ 21) (htick : tickerLen.toNat ≤ 256) :
    let hasTicker := bnot (decide (tickerLen = 0))
    let spaceLen : UInt32 := hasTicker.toUInt32
    let total := pos + spaceLen + tickerLen
    let o5 := maybeWrite' hasTicker o4 pos 0x20
    let o6 := copyTicker' ticker tickerLen o5 (pos + spaceLen)
    let o7 := writeU8 o6 total 0
    total.toNat = pos.toNat + spaceLen.toNat + tickerLen.toNat ∧
    total.toNat + 1 ≤ 280 ∧
    Writes o7 o4 pos.toNat
      ((if tickerLen.toNat = 0 then [] else 32 :: Spec.bytes ticker tickerLen.toNat) ++ [0]) := by
  dsimp only
  have h32 : (0x20 : UInt8).toNat = 32 := rfl
  have hz8 : (0 : UInt8).toNat = 0 := rfl
  have hz32 : (0 : UInt32).toNat = 0 := rfl
  generalize hht : bnot (decide (tickerLen = 0)) = hasTicker
  generalize hsl : hasTicker.toUInt32 = spaceLen
  have hcases : (hasTicker = false ∧ tickerLen.toNat = 0 ∧ spaceLen.toNat = 0) ∨
      (hasTicker = true ∧ tickerLen.toNat ≠ 0 ∧ spaceLen.toNat = 1) := by
    rw [bnot_eq] at hht
    by_cases ht0 : tickerLen = 0
    · rw [decide_eq_true ht0, Bool.not_true] at hht
      subst hht
      exact Or.inl ⟨rfl, by rw [ht0]; rfl, by rw [← hsl]; rfl⟩
    · rw [decide_eq_false ht0, Bool.not_false] at hht
      subst hht
      have hne : tickerLen.toNat ≠ 0 := fun h => ht0 (UInt32.toNat_inj.mp (by rw [h, hz32]))
      exact Or.inr ⟨rfl, hne, by rw [← hsl]; rfl⟩
  have hps : (pos + spaceLen).toNat = pos.toNat + spaceLen.toNat := by
    rw [UInt32.toNat_add]
    rcases hcases with ⟨_, _, s0⟩ | ⟨_, _, s1⟩ <;> exact Nat.mod_eq_of_lt (by omega)
  have htot : (pos + spaceLen + tickerLen).toNat = pos.toNat + spaceLen.toNat + tickerLen.toNat := by
    rw [UInt32.toNat_add, hps]
    rcases hcases with ⟨_, _, s0⟩ | ⟨_, _, s1⟩ <;> exact Nat.mod_eq_of_lt (by omega)
  have htot_le : (pos + spaceLen + tickerLen).toNat + 1 ≤ 280 := by
    rcases hcases with ⟨_, _, s0⟩ | ⟨_, _, s1⟩ <;> omega
  have w5 : Writes (maybeWrite' hasTicker o4 pos 0x20) o4 pos.toNat
      (if hasTicker then [32] else []) := by
    have := writes_maybe hasTicker o4 pos 0x20 pos.toNat rfl
    rwa [h32] at this
  have w6 : Writes (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
      (maybeWrite' hasTicker o4 pos 0x20) (pos.toNat + spaceLen.toNat) (Spec.bytes ticker tickerLen.toNat) := by
    have := writes_ticker ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen) (by omega)
    rwa [hps] at this
  have w56 : Writes (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
      o4 pos.toNat (if tickerLen.toNat = 0 then [] else 32 :: Spec.bytes ticker tickerLen.toNat) := by
    rcases hcases with ⟨hht0, htl0, hsl0⟩ | ⟨hht1, htl1, hsl1⟩
    · rw [hht0] at w5 w6 ⊢
      simp only [Bool.false_eq_true, ↓reduceIte, htl0] at w5 ⊢
      have ht0 : Spec.bytes ticker tickerLen.toNat = [] := by rw [htl0]; rfl
      rw [ht0, hsl0, Nat.add_zero] at w6
      exact writes_append o4 (maybeWrite' false o4 pos 0x20)
        (copyTicker' ticker tickerLen (maybeWrite' false o4 pos 0x20) (pos + spaceLen))
        pos.toNat [] [] (by rw [List.length_nil]; omega) w5 (by rw [List.length_nil, Nat.add_zero]; exact w6)
    · rw [hht1] at w5 w6 ⊢
      simp only [↓reduceIte, ite_eq_right htl1] at w5 ⊢
      rw [hsl1] at w6
      exact writes_append o4 (maybeWrite' true o4 pos 0x20)
        (copyTicker' ticker tickerLen (maybeWrite' true o4 pos 0x20) (pos + spaceLen))
        pos.toNat [32] (Spec.bytes ticker tickerLen.toNat)
        (by rw [List.length_singleton, bytes_length]; omega) w5
        (by rw [List.length_singleton]; exact w6)
  have hlen56 : (if tickerLen.toNat = 0 then ([] : List Nat) else 32 :: Spec.bytes ticker tickerLen.toNat).length =
      spaceLen.toNat + tickerLen.toNat := by
    rcases hcases with ⟨_, htl0, hsl0⟩ | ⟨_, htl1, hsl1⟩
    · simp only [htl0, ↓reduceIte, List.length_nil, hsl0]
    · simp only [ite_eq_right htl1, List.length_cons, bytes_length, hsl1]; omega
  have w7 : Writes (writeU8 (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
      (pos + spaceLen + tickerLen) 0)
      (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
      (pos.toNat + (if tickerLen.toNat = 0 then ([] : List Nat) else 32 :: Spec.bytes ticker tickerLen.toNat).length)
      [0] := by
    have := writes_one (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
      (pos + spaceLen + tickerLen) 0
      (pos.toNat + (if tickerLen.toNat = 0 then ([] : List Nat) else 32 :: Spec.bytes ticker tickerLen.toNat).length)
      (by rw [htot, hlen56, ← Nat.add_assoc])
    rwa [hz8] at this
  have w567 := writes_append o4
    (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
    (writeU8 (copyTicker' ticker tickerLen (maybeWrite' hasTicker o4 pos 0x20) (pos + spaceLen))
      (pos + spaceLen + tickerLen) 0)
    pos.toNat (if tickerLen.toNat = 0 then [] else 32 :: Spec.bytes ticker tickerLen.toNat) [0]
    (by rw [hlen56, List.length_singleton]; omega) w56 w7
  exact ⟨htot, htot_le, w567⟩

private theorem seg_append (b : MutBytes) (a n m : Nat) :
    seg b a (n + m) = seg b a n ++ seg b (a + n) m := by
  unfold seg
  rw [lst_append]
  refine congrArg (lst (fun t => (b.get (UInt32.ofNat (a + t))).toNat) n ++ ·) ?_
  exact lst_congr _ _ m (fun t _ => by rw [Nat.add_assoc])

private theorem writes_prefix_get_zero (b1 b0 : MutBytes) (L : List Nat) (pos : UInt32)
    (hpos : pos.toNat = L.length) (hw : Writes b1 b0 0 (L ++ [0])) :
    Spec.written b1 pos.toNat = L ∧ b1.get pos = 0 ∧
    (∀ i : UInt32, pos.toNat < i.toNat → b1.get i = b0.get i) := by
  obtain ⟨hseg, hout⟩ := hw
  have hlen : (L ++ [0]).length = L.length + 1 := by rw [List.length_append, List.length_singleton]
  have h1 := seg_append b1 0 L.length 1
  rw [Nat.zero_add] at h1
  rw [hlen, h1] at hseg
  have hseg1_len : (seg b1 0 L.length).length = L.length := lst_length _ L.length
  have hseg2_len : (seg b1 L.length 1).length = ([0] : List Nat).length := lst_length _ 1
  obtain ⟨heq1, heq2⟩ := List.append_inj hseg hseg1_len
  refine ⟨?_, ?_, ?_⟩
  · rw [written_eq, hpos]
    exact heq1
  · have h3 : seg b1 L.length 1 = [(b1.get (UInt32.ofNat (L.length + 0))).toNat] := rfl
    rw [h3, Nat.add_zero, ← hpos, u32_ofNat_toNat] at heq2
    have h4 : (b1.get pos).toNat = (0 : UInt8).toNat := List.head_eq_of_cons_eq heq2
    exact UInt8.toNat_inj.mp h4
  · intro i hi
    apply hout i
    rw [hlen, Nat.zero_add, ← hpos]
    exact Or.inr hi

theorem formatSats : Spec.FormatSats := by
  intro amount ticker tickerLen padFrac8 out outCap
  have h256 : (256 : UInt32).toNat = 256 := rfl
  have hz : (0 : UInt32).toNat = 0 := rfl
  by_cases htick : 256 < tickerLen.toNat
  · have hlt : (256 : UInt32) < tickerLen := UInt32.lt_iff_toNat_lt.mpr (by rw [h256]; exact htick)
    have hres : llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap = (out, 0) := by
      rw [format_unfold, decide_eq_true hlt, ite_eq_left rfl]
    refine ⟨fun _ => by rw [hres], fun h => absurd (by rw [hres]) h, fun hle => absurd htick (Nat.not_lt_of_ge hle)⟩
  · have hnlt : ¬ (256 : UInt32) < tickerLen := fun h => htick (by rw [← h256]; exact UInt32.lt_iff_toNat_lt.mp h)
    have htick_le : tickerLen.toNat ≤ 256 := Nat.le_of_not_lt htick
    have sp := sats_parts amount
    dsimp only at sp
    obtain ⟨hq, hfrac, hfrac_lt, hqHi, hqHi_le, hqLo, hqLo_lt, hq_eq, hamt_eq⟩ := sp
    generalize hq_def : llbSatsDiv1e8 amount = q at hq hqHi hqHi_le hqLo hqLo_lt hq_eq hamt_eq
    generalize hfrac_def : llbSatsMod1e8 amount = frac at hfrac hfrac_lt hamt_eq
    generalize hqHi_def : (llbSatsDiv1e8 q).toUInt32 = qHi at hqHi hqHi_le hq_eq
    generalize hqLo_def : llbSatsMod1e8 q = qLo at hqLo hqLo_lt hq_eq
    have stI := int_stage out qHi qLo q.toNat hqHi_le hqLo_lt hq_eq
    dsimp only at stI
    generalize hhiZero : decide (qHi = 0) = hiZero at stI
    generalize hhiLen : selU32 hiZero 0 (decLenU32 qHi) = hiLen at stI
    generalize hloLen : selU32 hiZero (decLenU32 qLo) 8 = loLen at stI
    generalize hintLen : hiLen + loLen = intLen at stI
    generalize ho1 : emitDec' out hiLen qHi hiLen = o1 at stI
    generalize ho2 : emitDec' o1 intLen qLo loLen = o2 at stI
    obtain ⟨hint1, hint12, hI_len, hI_dig, hI_val, w12⟩ := stI
    have stF := frac_stage o2 intLen padFrac8 frac hint12 hfrac_lt
    dsimp only at stF
    generalize hpad : bnot (decide (padFrac8 = 0)) = pad at stF
    generalize hsf : bor pad (bnot (decide (frac = 0))) = showFrac at stF
    generalize hfl : selU32 pad 8 (fracSigLen frac) = fracLen at stF
    generalize hdl : showFrac.toUInt32 = dotLen at stF
    generalize ho3 : maybeWrite' showFrac o2 intLen 0x2E = o3 at stF
    generalize hdrop : selU32 pad 0 (8 - fracLen) = drop at stF
    generalize hfs : forRangeU32 0 drop frac (fun _ cur => div10U32 cur) = fracShown at stF
    generalize hefl : selU32 showFrac fracLen 0 = emitFracLen at stF
    generalize ho4 : emitDec' o3 (intLen + 1 + emitFracLen) fracShown emitFracLen = o4 at stF
    obtain ⟨hdf_le, hdf_add, hf_cases⟩ := stF
    have hpos_le : (intLen + dotLen + fracLen).toNat ≤ 21 := by omega
    have stT := ticker_stage o4 (intLen + dotLen + fracLen) ticker tickerLen hpos_le htick_le
    dsimp only at stT
    generalize hht : bnot (decide (tickerLen = 0)) = hasTicker at stT
    generalize hsl : hasTicker.toUInt32 = spaceLen at stT
    generalize htot : intLen + dotLen + fracLen + spaceLen + tickerLen = total at stT
    generalize ho5 : maybeWrite' hasTicker o4 (intLen + dotLen + fracLen) 0x20 = o5 at stT
    generalize ho6 : copyTicker' ticker tickerLen o5 (intLen + dotLen + fracLen + spaceLen) = o6 at stT
    generalize ho7 : writeU8 o6 total 0 = o7 at stT
    obtain ⟨htot_add, htot_le, w567⟩ := stT
    have hunf : llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap =
        if decide (outCap ≤ total) then (out, 0) else (o7, total) := by
      rw [format_unfold, decide_eq_false hnlt, ite_eq_right Bool.false_ne_true]
      dsimp only
      rw [hq_def, hfrac_def, hqHi_def, hqLo_def, hhiZero, hhiLen, hloLen, hintLen,
        hpad, hsf, hfl, hdl, hht, hsl, htot,
        ho1, ho2, ho3, hdrop, hfs, hefl, ho4, ho5, ho6, ho7]
    have htot_pos : 1 ≤ total.toNat := by omega
    have htot_ne0 : total ≠ 0 := fun h => by
      have : total.toNat = 0 := by rw [h]; rfl
      exact absurd this (Nat.ne_of_gt htot_pos)
    have hsl_le : spaceLen.toNat ≤ 1 := by
      rw [← hsl, bool_toUInt32_toNat]
      cases hasTicker <;> decide
    have htot_max : total.toNat ≤ 22 + tickerLen.toNat := by omega
    by_cases hcap : outCap ≤ total
    · have hcap_nat : outCap.toNat ≤ total.toNat := UInt32.le_iff_toNat_le.mp hcap
      have hres : llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap = (out, 0) := by
        rw [hunf, decide_eq_true hcap, ite_eq_left rfl]
      refine ⟨fun _ => by rw [hres], fun h => absurd (by rw [hres]) h, fun _ h22 => ?_⟩
      exact absurd hcap_nat (Nat.not_le_of_gt (Nat.lt_of_le_of_lt htot_max h22))
    · have hcap_gt : total.toNat < outCap.toNat := Nat.lt_of_not_le (fun h => hcap (UInt32.le_iff_toNat_le.mpr h))
      have hres : llbFormatSatsAscii amount ticker tickerLen padFrac8 out outCap = (o7, total) := by
        rw [hunf, decide_eq_false hcap, ite_eq_right Bool.false_ne_true]
      refine ⟨fun h => absurd (by rw [hres] at h; exact h) htot_ne0, ?_, fun _ _ => by rw [hres]; exact htot_ne0⟩
      intro _
      rw [hres]
      dsimp only
      let T : List Nat := if tickerLen.toNat = 0 then [] else 32 :: Spec.bytes ticker tickerLen.toNat
      have hT_len : T.length = spaceLen.toNat + tickerLen.toNat := by
        dsimp [T]
        by_cases ht0 : tickerLen.toNat = 0
        · have hs0 : spaceLen.toNat = 0 := by
            have ht_eq : tickerLen = 0 := UInt32.toNat_inj.mp (by rw [ht0, hz])
            rw [← hsl, ← hht, decide_eq_true ht_eq]; rfl
          simp only [ht0, ↓reduceIte, List.length_nil, hs0]
        · have hs1 : spaceLen.toNat = 1 := by
            have ht_ne : tickerLen ≠ 0 := fun e => ht0 (by rw [e]; rfl)
            rw [← hsl, ← hht, decide_eq_false ht_ne]; rfl
          simp only [ite_eq_right ht0, List.length_cons, bytes_length, hs1]; omega
      have hTr : (T = [] ∧ Spec.bytes ticker tickerLen.toNat = []) ∨ T = 32 :: Spec.bytes ticker tickerLen.toNat := by
        dsimp [T]
        by_cases ht0 : tickerLen.toNat = 0
        · left
          rw [ite_eq_left ht0]
          exact ⟨rfl, by rw [ht0]; rfl⟩
        · right
          rw [ite_eq_right ht0]
      have hI_pos : 0 < (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat).length := by omega
      rcases hf_cases with ⟨_, hf0, hd0, hfl0, w34⟩ | ⟨_, hd1, hF_len, hfl_le, hF_dig, hF_val, w34⟩
      · have w14 := writes_append out o2 o4 0
          (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat) []
          (by rw [hI_len, List.length_nil]; omega) w12 (by rw [Nat.zero_add, hI_len]; exact w34)
        rw [List.append_nil] at w14
        have hpos_eq : (intLen + dotLen + fracLen).toNat =
            (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat).length := by omega
        have w17 := writes_append out o4 o7 0
          (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat) (T ++ [0])
          (by rw [hI_len, List.length_append, hT_len, List.length_singleton]; omega) w14
          (by rw [Nat.zero_add, ← hpos_eq]; exact w567)
        rw [← List.append_assoc] at w17
        have hlen_full : total.toNat =
            (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat ++ T).length := by
          rw [List.length_append, hI_len, hT_len]; omega
        obtain ⟨hwrit, hget0, hout⟩ := writes_prefix_get_zero o7 out
          (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat ++ T) total hlen_full w17
        refine ⟨hcap_gt, ?_, hget0, hout⟩
        rw [hwrit, parse_plain _ (Spec.bytes ticker tickerLen.toNat) T hI_dig hI_pos hTr,
          hI_val, hamt_eq, hf0, Nat.add_zero]
      · have w14 := writes_append out o2 o4 0
          (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat)
          (46 :: digs fracShown.toNat emitFracLen.toNat)
          (by rw [hI_len, List.length_cons, hF_len]; omega) w12 (by rw [Nat.zero_add, hI_len]; exact w34)
        have hpos_eq : (intLen + dotLen + fracLen).toNat =
            (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat ++
              (46 :: digs fracShown.toNat emitFracLen.toNat)).length := by
          rw [List.length_append, hI_len, List.length_cons, hF_len]; omega
        have w17 := writes_append out o4 o7 0
          (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat ++
            (46 :: digs fracShown.toNat emitFracLen.toNat)) (T ++ [0])
          (by rw [← hpos_eq, List.length_append, hT_len, List.length_singleton]; omega) w14
          (by rw [Nat.zero_add, ← hpos_eq]; exact w567)
        rw [← List.append_assoc] at w17
        have hlen_full : total.toNat =
            (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat ++
              (46 :: digs fracShown.toNat emitFracLen.toNat) ++ T).length := by
          rw [List.length_append, ← hpos_eq, hT_len]; omega
        obtain ⟨hwrit, hget0, hout⟩ := writes_prefix_get_zero o7 out
          (digs qHi.toNat hiLen.toNat ++ digs qLo.toNat loLen.toNat ++
            (46 :: digs fracShown.toNat emitFracLen.toNat) ++ T) total hlen_full w17
        refine ⟨hcap_gt, ?_, hget0, hout⟩
        rw [hwrit, List.append_assoc, List.cons_append,
          parse_frac _ _ (Spec.bytes ticker tickerLen.toNat) T hI_dig hF_dig hI_pos
            (by rw [hF_len]; exact hfl_le) hTr,
          hI_val, hF_val, hamt_eq]

end Formatter

/-- The compiled kernel satisfies every statement of `Spec.lean`. -/
theorem kernel_meets_spec : Spec.KernelSpec :=
  ⟨validAmount, checkedAdd, checkedSub, splitBtc, hardenedBit, depthLimits,
   segwitProgram, witnessOpcode, sighashType, taprootSighashType,
   compactSizeCanonical, dualUtxo, compactSizeRead, bip32ExportPath, merkleSplit, merkleStep,
   psbtLocktime, sortU16, sortFixedBytes, formatSats⟩

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

/-- A read-only buffer of 32-bit words holding `l` (zero past its end). -/
private def constU32s (l : List UInt32) : ConstU32s := ⟨fun i => l.getD i.toNat 0, ()⟩

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

/-- `m/84'/0'/0'/0/5` and `m/48'/0'/0'/2'` are accepted on mainnet. Rejected: a hardened
    step after the account, the wrong coin type, account 101, script type 3, and a purpose
    outside the list. -/
theorem witness_bip32ExportPath :
    llbBip32CheckExportPath (constU32s [0x80000054, 0x80000000, 0x80000000, 0, 5]) 5 0 = true ∧
    llbBip32CheckExportPath (constU32s [0x80000030, 0x80000000, 0x80000000, 0x80000002]) 4 0 = true ∧
    llbBip32CheckExportPath (constU32s [0x80000054, 0x80000000, 0x80000000, 0x80000000, 5]) 5 0 = false ∧
    llbBip32CheckExportPath (constU32s [0x80000054, 0x80000000, 0x80000000, 0, 5]) 5 1 = false ∧
    llbBip32CheckExportPath (constU32s [0x80000054, 0x80000000, 0x80000065]) 3 0 = false ∧
    llbBip32CheckExportPath (constU32s [0x80000030, 0x80000000, 0x80000000, 0x80000003]) 4 0 = false ∧
    llbBip32CheckExportPath (constU32s [0x80000000, 0x80000000, 0x80000000]) 3 0 = false := by
  decide

theorem witness_merkleSplit :
    largestPow2LtU32 2 = 1 ∧ largestPow2LtU32 5 = 4 ∧ largestPow2LtU32 8 = 4 ∧
    largestPow2LtU32 9 = 8 ∧ largestPow2LtU32 4294967295 = 2147483648 := by decide

/-- In a tree of 5 leaves, leaf 3 is in the left subtree of 4 and leaf 4 is the right
    subtree of 1. A tree of one leaf does not move. -/
theorem witness_merkleStep :
    llbMerkleAdvanceState (5 * 4294967296 + 3) = 4 * 4294967296 + 3 ∧
    llbMerkleAdvanceState (5 * 4294967296 + 4) = 1 * 4294967296 + 0 ∧
    llbMerkleAdvanceState (1 * 4294967296 + 0) = 1 * 4294967296 + 0 := by decide

/-- Inputs are `(hasHeight, height, hasTime, time)`. Accepted: no requirement (fallback 7),
    two heights (the larger), a height-only input next to one with both (height wins), a
    time-only input next to one with both (time). Rejected: a height-only input next to a
    time-only one, height 0, a time below 500000000. -/
theorem witness_psbtLocktime :
    llbPsbtLocktimeFinalize (Spec.locktimeRun [(0, 0, 0, 0)]) 7 = 4294967296 + 7 ∧
    llbPsbtLocktimeFinalize (Spec.locktimeRun [(1, 100, 0, 0), (1, 200, 0, 0)]) 7 =
      4294967296 + 200 ∧
    llbPsbtLocktimeFinalize
      (Spec.locktimeRun [(1, 100, 0, 0), (1, 200, 1, 600000000)]) 7 = 4294967296 + 200 ∧
    llbPsbtLocktimeFinalize
      (Spec.locktimeRun [(0, 0, 1, 500000001), (1, 200, 1, 600000000)]) 7 =
        4294967296 + 600000000 ∧
    llbPsbtLocktimeFinalize
      (Spec.locktimeRun [(1, 100, 0, 0), (0, 0, 1, 600000000)]) 7 = 0 ∧
    llbPsbtLocktimeFinalize (Spec.locktimeRun [(1, 0, 0, 0)]) 7 = 0 ∧
    llbPsbtLocktimeFinalize (Spec.locktimeRun [(0, 0, 1, 499999999)]) 7 = 0 := by decide

private def mutU16s (l : List UInt16) : MutU16s := ⟨fun i => l.getD i.toNat 0, ()⟩

/-- Four words sorted; only the first three sorted, the fourth left alone; one word untouched. -/
theorem witness_sortU16 :
    Spec.u16s (llbSortU16 (mutU16s [3, 1, 2, 1]) 4) 4 = [1, 1, 2, 3] ∧
    Spec.u16s (llbSortU16 (mutU16s [3, 1, 2, 0]) 3) 4 = [1, 2, 3, 0] ∧
    Spec.u16s (llbSortU16 (mutU16s [5, 4]) 1) 2 = [5, 4] := by decide

private def mutBytes (l : List UInt8) : MutBytes := ⟨fun i => l.getD i.toNat 0, ()⟩

/-- Three two-byte records sorted (the tie on the first byte is broken by the second); only
    the first two sorted, the third left alone; one record untouched. -/
theorem witness_sortFixedBytes :
    Spec.records (llbSortFixedBytes (mutBytes [2, 9, 1, 7, 2, 3]) 3 2) 3 2 =
      [[1, 7], [2, 3], [2, 9]] ∧
    Spec.records (llbSortFixedBytes (mutBytes [2, 9, 1, 7, 0, 0]) 2 2) 3 2 =
      [[1, 7], [2, 9], [0, 0]] ∧
    Spec.records (llbSortFixedBytes (mutBytes [2, 9, 1, 7]) 1 2) 2 2 = [[2, 9], [1, 7]] := by
  decide

/-- Accepted: `0` as `"0\0"`, `1.5 BTC` as `"1.5 BTC\0"` without padding and
    `"1.50000000 BTC\0"` with padding. Rejected: capacity equal to the string length (no room
    for the trailing NUL), and a ticker past 256 bytes. -/
theorem witness_formatSats :
    let btc := constBytes [66, 84, 67]
    (llbFormatSatsAscii 0 btc 0 0 (mutBytes []) 2).2 = 1 ∧
    Spec.written (llbFormatSatsAscii 0 btc 0 0 (mutBytes []) 2).1 2 = [48, 0] ∧
    (llbFormatSatsAscii 150000000 btc 3 0 (mutBytes []) 8).2 = 7 ∧
    Spec.written (llbFormatSatsAscii 150000000 btc 3 0 (mutBytes []) 8).1 8 =
      [49, 46, 53, 32, 66, 84, 67, 0] ∧
    (llbFormatSatsAscii 150000000 btc 3 1 (mutBytes []) 15).2 = 14 ∧
    Spec.written (llbFormatSatsAscii 150000000 btc 3 1 (mutBytes []) 15).1 15 =
      [49, 46, 53, 48, 48, 48, 48, 48, 48, 48, 32, 66, 84, 67, 0] ∧
    (llbFormatSatsAscii 150000000 btc 3 0 (mutBytes []) 7).2 = 0 ∧
    (llbFormatSatsAscii 0 btc 257 0 (mutBytes []) 300).2 = 0 := by
  decide

end Proofs.KernelSpec

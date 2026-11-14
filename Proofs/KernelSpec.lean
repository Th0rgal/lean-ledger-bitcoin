import Spec
import Proofs.FreestandingKernels

/-!
# Proofs of `Spec.lean`

One theorem per statement of `Spec.lean`, then `kernel_meets_spec`, then one accepted and
one rejected concrete input per statement (so no statement holds for an empty reason).

Some proofs reuse lemmas of `Proofs/FreestandingKernels.lean` that are themselves stated on
the kernel functions: `llbSatsDiv1e8_eq` and `llbSatsMod1e8_eq` (`SplitBtc`), `llbBytesEq_iff`
(`DualUtxo`), `bip32TailClear_iff` (`Bip32ExportPath`) and `largestPow2LtU32_eq`
(`MerkleSplit`). Every other proof unfolds the kernel function directly.
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

/-- The compiled kernel satisfies every statement of `Spec.lean`. -/
theorem kernel_meets_spec : Spec.KernelSpec :=
  ⟨validAmount, checkedAdd, checkedSub, splitBtc, hardenedBit, depthLimits,
   segwitProgram, witnessOpcode, sighashType, taprootSighashType,
   compactSizeCanonical, dualUtxo, compactSizeRead, bip32ExportPath, merkleSplit, merkleStep⟩

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

end Proofs.KernelSpec

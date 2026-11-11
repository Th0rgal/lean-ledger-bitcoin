import InternalSpec
import BitcoinLedger.Basic
import BitcoinLedger.Bip32
import Proofs.Basic

namespace Proofs.Bip32

/-!
# `Proofs.Bip32` — Refinement & Security Proofs for `BitcoinLedger.Bip32`

Constructive (`0 Classical.choice`, `0 sorryAx`, `0 native_decide`) refinement theorems connecting
`BitcoinLedger.Bip32` to `InternalSpec.Bip32`:
1. Bitwise `isHardened`, `harden`, and `unharden` equivalence with `InternalSpec.Bip32` + algebraic roundtrips
   + BOLOS/BIP-388/Vanadium/BIP-32 depth gate theorems
2. Wire BIP-32 path serializer/parser roundtrip (`parseBip32Path?` ↔ `serializeBip32Path?`) and malformed rejection
3. 78-byte `ExtendedPubKey` serializer/deserializer equivalence, roundtrip, and Base58Check framing equivalence
4. `deriveChildExtendedPubKey?`, `deriveMasterFingerprint?`, and `deriveExtendedPubKeyWithOracle` equivalence & homomorphism
5. Ledger `GET_EXTENDED_PUBKEY` export policy equivalence (`classifyExpubPathWithTree`, `classifyExpubPath`,
   `authorizeExtendedPubKeyExport`, `evalGetExtendedPubkey`), security theorems (silent export requires `.allowSilent`,
   over-depth rejection, short/unhardened silent export rejection, warning soundness), and concrete witnesses
-/

open BitcoinLedger.Bip32

/-! ## 1. Bitwise Hardening Operations & Depth Gates -/

private theorem nat_and_pow31_eq_zero_iff (n : Nat) (hlt : n < 2 ^ 32) :
    n &&& 0x80000000 = 0 ↔ n < 0x80000000 := by
  have h231 : (0x80000000 : Nat) = 2 ^ 31 := by decide
  have h232 : (2 ^ 32 : Nat) = 2 * 2 ^ 31 := by decide
  constructor
  · intro hand
    cases hle : decide (2 ^ 31 ≤ n)
    · rw [h231]
      exact Nat.lt_of_not_le (of_decide_eq_false hle)
    · exfalso
      have hge : 2 ^ 31 ≤ n := of_decide_eq_true hle
      have hm : n - 2 ^ 31 < 2 ^ 31 := by
        have hadd : (n - 2 ^ 31) + 2 ^ 31 < 2 ^ 31 + 2 ^ 31 := by
          rw [Nat.sub_add_cancel hge, ← Nat.two_mul, ← h232]
          exact hlt
        exact Nat.lt_of_add_lt_add_right hadd
      have hdecomp : n = 2 ^ 31 * 1 + (n - 2 ^ 31) := by
        rw [Nat.mul_one, Nat.add_comm, Nat.sub_add_cancel hge]
      have hbit : n.testBit 31 = true := by
        rw [hdecomp, Nat.testBit_two_pow_mul_add 1 hm]
        simp only [Nat.lt_irrefl, ↓reduceIte]
        decide
      have handBit : (n &&& 0x80000000).testBit 31 = true := by
        rw [Nat.testBit_and, hbit]
        decide
      rw [hand] at handBit
      cases handBit
  · intro hlt31
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    cases hk : decide (k < 31)
    · have hge31 : 31 ≤ k := Nat.le_of_not_lt (of_decide_eq_false hk)
      have hnk : n < 2 ^ k := by
        rw [h231] at hlt31
        exact Nat.lt_of_lt_of_le hlt31 (Nat.pow_le_pow_right (by decide) hge31)
      rw [Nat.testBit_lt_two_pow hnk, Bool.false_and]
    · have hlt_k : k < 31 := of_decide_eq_true hk
      have hmask : (0x80000000 : Nat).testBit k = false := by
        rw [h231]
        have hdecomp : (2 ^ 31 : Nat) = 2 ^ 31 * 1 + 0 := by decide
        rw [hdecomp, Nat.testBit_two_pow_mul_add 1 (by decide : 0 < 2 ^ 31)]
        simp [hlt_k]
      rw [hmask, Bool.and_false]

/-- Executable bitwise `isHardened` refines `InternalSpec.isHardened`. -/
theorem isHardened_eq (idx : UInt32) :
    BitcoinLedger.Bip32.isHardened idx = InternalSpec.isHardened idx := by
  unfold BitcoinLedger.Bip32.isHardened HARDENED_BIT InternalSpec.isHardened
  have handNat : (idx &&& (0x80000000 : UInt32)).toNat = idx.toNat &&& 0x80000000 :=
    UInt32.toNat_and idx 0x80000000
  cases h : decide ((idx &&& (0x80000000 : UInt32)) = 0)
  · have hne : (idx &&& (0x80000000 : UInt32)).toNat ≠ 0 :=
      fun hz => of_decide_eq_false h (UInt32.toNat_inj.mp hz)
    rw [handNat] at hne
    have hge : 0x80000000 ≤ idx.toNat := by
      apply Nat.le_of_not_lt
      intro hlt31
      exact hne ((nat_and_pow31_eq_zero_iff idx.toNat idx.toNat_lt).mpr hlt31)
    simp [hge]
  · have heq0 : idx.toNat &&& 0x80000000 = 0 := by
      rw [← handNat]
      exact congrArg UInt32.toNat (of_decide_eq_true h)
    have hlt31 : idx.toNat < 0x80000000 :=
      (nat_and_pow31_eq_zero_iff idx.toNat idx.toNat_lt).mp heq0
    have hnle : ¬ (0x80000000 ≤ idx.toNat) := Nat.not_le_of_lt hlt31
    simp [hnle]

private theorem nat_and_mask31_eq_mod (n : Nat) :
    n &&& 0x7FFFFFFF = n % 0x80000000 := by
  have hmod : n % 0x80000000 = n % 2 ^ 31 := rfl
  rw [hmod]
  have mask_bit : ∀ k : Nat, k < 31 → (0x7FFFFFFF : Nat).testBit k = true := by
    intro k hk
    match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
    | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
    | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 => decide
    | _ + 31 => exact absurd hk (Nat.not_lt_of_ge (Nat.le_add_left 31 _))
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow]
  cases hk : decide (k < 31)
  · have hge31 : 31 ≤ k := Nat.le_of_not_lt (of_decide_eq_false hk)
    have hlt : (0x7FFFFFFF : Nat) < 2 ^ k :=
      Nat.lt_of_lt_of_le (by decide : 0x7FFFFFFF < 2 ^ 31) (Nat.pow_le_pow_right (by decide) hge31)
    rw [Nat.testBit_lt_two_pow hlt, Bool.and_false, Bool.false_and]
  · rw [mask_bit k (of_decide_eq_true hk), Bool.and_true, Bool.true_and]

/-- Executable bitwise `unharden` refines `InternalSpec.unharden`. -/
theorem unharden_eq (idx : UInt32) :
    BitcoinLedger.Bip32.unharden idx = InternalSpec.unharden idx := by
  unfold BitcoinLedger.Bip32.unharden UNHARDENED_MASK InternalSpec.unharden
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, UInt32.toNat_ofNat']
  change idx.toNat &&& 0x7FFFFFFF = (idx.toNat % 0x80000000) % 2 ^ 32
  rw [nat_and_mask31_eq_mod]
  have hlt : idx.toNat % 0x80000000 < 2 ^ 32 :=
    Nat.lt_trans (Nat.mod_lt idx.toNat (by decide)) (by decide)
  exact (Nat.mod_eq_of_lt hlt).symm

/-- Executable bitwise `harden` refines `InternalSpec.harden`. -/
theorem harden_eq (n : UInt32) :
    BitcoinLedger.Bip32.harden n = InternalSpec.harden n := by
  unfold BitcoinLedger.Bip32.harden HARDENED_BIT InternalSpec.harden
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, UInt32.toNat_ofNat']
  change n.toNat ||| 0x80000000 = (0x80000000 + n.toNat % 0x80000000) % 2 ^ 32
  have hlt31 : n.toNat % 0x80000000 < 2 ^ 31 := Nat.mod_lt n.toNat (by decide)
  have hsumLt : 0x80000000 + n.toNat % 0x80000000 < 2 ^ 32 := by
    have hle : n.toNat % 0x80000000 ≤ 0x7FFFFFFF := Nat.le_of_lt_succ hlt31
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hle 0x80000000) (by decide)
  rw [Nat.mod_eq_of_lt hsumLt]
  have hdecomp : 0x80000000 + n.toNat % 0x80000000 = 2 ^ 31 * 1 + (n.toNat % 2 ^ 31) := by
    change 0x80000000 + n.toNat % 0x80000000 = 0x80000000 * 1 + n.toNat % 0x80000000
    rw [Nat.mul_one]
  rw [hdecomp]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add 1 hlt31]
  cases hk : decide (k < 31)
  · have hnlt : ¬ (k < 31) := of_decide_eq_false hk
    have hge31 : 31 ≤ k := Nat.le_of_not_lt hnlt
    simp only [hnlt, ↓reduceIte]
    cases hk31 : decide (k = 31)
    · have hgt31 : 32 ≤ k := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hge31 (Ne.symm (of_decide_eq_false hk31)))
      have hnLt : n.toNat < 2 ^ k := Nat.lt_of_lt_of_le n.toNat_lt (Nat.pow_le_pow_right (by decide) hgt31)
      have hmLt : (0x80000000 : Nat) < 2 ^ k :=
        Nat.lt_of_lt_of_le (by decide : 0x80000000 < 2 ^ 32) (Nat.pow_le_pow_right (by decide) hgt31)
      have h1Lt : (1 : Nat) < 2 ^ (k - 31) := by
        have hpos : 1 ≤ k - 31 := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hgt31)
        exact Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) hpos)
      rw [Nat.testBit_lt_two_pow hnLt, Nat.testBit_lt_two_pow hmLt, Nat.testBit_lt_two_pow h1Lt]
      rfl
    · have heq31 : k = 31 := of_decide_eq_true hk31
      subst heq31
      have hb : (0x80000000 : Nat).testBit 31 = true := by decide
      have h1 : (1 : Nat).testBit (31 - 31) = true := by decide
      rw [hb, h1, Bool.or_true]
  · have hlt_k : k < 31 := of_decide_eq_true hk
    simp only [hlt_k, ↓reduceIte]
    have hb : (0x80000000 : Nat).testBit k = false := by
      have hd : (0x80000000 : Nat) = 2 ^ 31 * 1 + 0 := by decide
      rw [hd, Nat.testBit_two_pow_mul_add 1 (by decide : 0 < 2 ^ 31)]
      simp [hlt_k]
    have hmod : n.toNat % 0x80000000 = n.toNat % 2 ^ 31 := rfl
    rw [hb, Bool.or_false, hmod, Nat.testBit_mod_two_pow, hk, Bool.true_and]

theorem isHardened_harden (n : UInt32) :
    BitcoinLedger.Bip32.isHardened (BitcoinLedger.Bip32.harden n) = true := by
  rw [isHardened_eq, harden_eq]
  unfold InternalSpec.isHardened InternalSpec.harden
  rw [UInt32.toNat_ofNat']
  have hlt31 : n.toNat % 0x80000000 < 0x80000000 := Nat.mod_lt n.toNat (by decide)
  have hlt32 : 0x80000000 + n.toNat % 0x80000000 < 2 ^ 32 := by
    have hle : n.toNat % 0x80000000 ≤ 0x7FFFFFFF := Nat.le_of_lt_succ hlt31
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hle 0x80000000) (by decide)
  rw [Nat.mod_eq_of_lt hlt32]
  exact decide_eq_true (Nat.le_add_right _ _)

theorem unharden_harden {n : UInt32} (h : n.toNat < 0x80000000) :
    BitcoinLedger.Bip32.unharden (BitcoinLedger.Bip32.harden n) = n := by
  apply UInt32.toNat_inj.mp
  rw [unharden_eq, harden_eq]
  unfold InternalSpec.unharden InternalSpec.harden
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt h]
  have hlt32 : 0x80000000 + n.toNat < 2 ^ 32 := by
    have hle : n.toNat ≤ 0x7FFFFFFF := Nat.le_of_lt_succ h
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left hle 0x80000000) (by decide)
  rw [Nat.mod_eq_of_lt hlt32]
  have hmod : (0x80000000 + n.toNat) % 0x80000000 = n.toNat := by
    rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt h]
  rw [hmod, Nat.mod_eq_of_lt n.toNat_lt]

theorem harden_unharden {idx : UInt32} (h : BitcoinLedger.Bip32.isHardened idx = true) :
    BitcoinLedger.Bip32.harden (BitcoinLedger.Bip32.unharden idx) = idx := by
  rw [isHardened_eq, InternalSpec.isHardened_iff] at h
  unfold InternalSpec.Hardened at h
  apply UInt32.toNat_inj.mp
  rw [harden_eq, unharden_eq]
  unfold InternalSpec.harden InternalSpec.unharden
  rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat']
  have hlt31 : idx.toNat % 0x80000000 < 0x80000000 := Nat.mod_lt idx.toNat (by decide)
  have hlt32 : idx.toNat % 0x80000000 < 2 ^ 32 := Nat.lt_trans hlt31 (by decide)
  rw [Nat.mod_eq_of_lt hlt32, Nat.mod_eq_of_lt hlt31]
  have hdiv1 : idx.toNat / 0x80000000 = 1 := by
    have hge1 : 1 ≤ idx.toNat / 0x80000000 := (Nat.le_div_iff_mul_le (by decide)).mpr (by rw [Nat.one_mul]; exact h)
    have hlt2 : idx.toNat / 0x80000000 < 2 := (Nat.div_lt_iff_lt_mul (by decide)).mpr idx.toNat_lt
    exact Nat.le_antisymm (Nat.le_of_lt_succ hlt2) hge1
  have hsum : 0x80000000 + idx.toNat % 0x80000000 = idx.toNat := by
    have hdm := Nat.div_add_mod idx.toNat 0x80000000
    rw [hdiv1, Nat.mul_one] at hdm
    exact hdm
  rw [hsum, Nat.mod_eq_of_lt idx.toNat_lt]

theorem checkBolosDepth_iff (path : Bip32Path) :
    checkBolosDepth path = true ↔ path.size ≤ InternalSpec.MAX_BIP32_PATH_STEPS := by
  unfold checkBolosDepth MAX_BIP32_PATH_STEPS InternalSpec.MAX_BIP32_PATH_STEPS
  exact decide_eq_true_iff

theorem checkBip388Depth_iff (path : Bip32Path) :
    checkBip388Depth path = true ↔ path.size ≤ InternalSpec.MAX_BIP388_XPUB_DERIVATION_STEPS := by
  unfold checkBip388Depth MAX_BIP388_XPUB_DERIVATION_STEPS InternalSpec.MAX_BIP388_XPUB_DERIVATION_STEPS
  exact decide_eq_true_iff

theorem checkVanadiumDepth_iff (path : Bip32Path) :
    checkVanadiumDepth path = true ↔ path.size ≤ InternalSpec.MAX_BIP32_PATH_LEN := by
  unfold checkVanadiumDepth MAX_BIP32_PATH_LEN InternalSpec.MAX_BIP32_PATH_LEN
  exact decide_eq_true_iff

/-! ## 2. Wire BIP-32 Path Serializer & Parser Roundtrip -/

private def encodeStepsList : List UInt32 → List UInt8
  | [] => []
  | step :: rest => (BitcoinLedger.Basic.encodeU32BE step).data.toList ++ encodeStepsList rest

private theorem encodePathStepsAux_toList (steps : List UInt32) (acc : ByteArray) :
    (BitcoinLedger.Bip32.encodePathStepsAux steps acc).data.toList =
      acc.data.toList ++ encodeStepsList steps := by
  induction steps generalizing acc with
  | nil =>
      unfold BitcoinLedger.Bip32.encodePathStepsAux encodeStepsList
      rw [List.append_nil]
  | cons step rest ih =>
      unfold BitcoinLedger.Bip32.encodePathStepsAux encodeStepsList
      rw [ih]
      cases acc with
      | mk arr =>
          cases h : BitcoinLedger.Basic.encodeU32BE step with
          | mk sarr =>
              simp [List.append_assoc]

private theorem encodeStepsList_length (steps : List UInt32) :
    (encodeStepsList steps).length = 4 * steps.length := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
      unfold encodeStepsList
      have hs : (BitcoinLedger.Basic.encodeU32BE step).data.toList.length = 4 := rfl
      rw [List.length_append, hs, ih, List.length_cons, Nat.mul_succ, Nat.add_comm]

private theorem parsePathStepsAux_encodeStepsList (steps : List UInt32) (acc : Array UInt32) :
    BitcoinLedger.Bip32.parsePathStepsAux steps.length (encodeStepsList steps) acc =
      some (acc ++ steps.toArray) := by
  induction steps generalizing acc with
  | nil =>
      unfold BitcoinLedger.Bip32.parsePathStepsAux encodeStepsList
      simp
  | cons step rest ih =>
      have hdec := Proofs.Basic.decodeU32BE?_roundtrip step
      unfold BitcoinLedger.Basic.encodeU32BE BitcoinLedger.Basic.decodeU32BE? at hdec
      dsimp only at hdec
      have hstep :
          (((step >>> 24).toUInt8.toUInt32 <<< 24) |||
           ((step >>> 16).toUInt8.toUInt32 <<< 16) |||
           ((step >>> 8).toUInt8.toUInt32 <<< 8) |||
           step.toUInt8.toUInt32) = step := Option.some.inj hdec
      unfold encodeStepsList BitcoinLedger.Basic.encodeU32BE
      change BitcoinLedger.Bip32.parsePathStepsAux (rest.length + 1)
        ((step >>> 24).toUInt8 :: (step >>> 16).toUInt8 :: (step >>> 8).toUInt8 :: step.toUInt8 ::
          encodeStepsList rest) acc = some (acc ++ (step :: rest).toArray)
      unfold BitcoinLedger.Bip32.parsePathStepsAux
      dsimp only
      rw [hstep, ih]
      apply congrArg some
      apply Array.ext'
      simp

/-- Roundtrip theorem for wire-serialized BIP-32 paths (`path.size ≤ 255`). -/
theorem parseBip32Path?_serializeBip32Path? {path : Bip32Path}
    (hle : path.size ≤ MAX_BIP32_BYTE_DEPTH) :
    ∃ bs : ByteArray,
      serializeBip32Path? path = some bs ∧
      bs.size = 1 + 4 * path.size ∧
      parseBip32Path? bs = some path := by
  have hnotGt : decide (path.size > MAX_BIP32_BYTE_DEPTH) = false :=
    decide_eq_false (Nat.not_lt_of_ge hle)
  let bs := BitcoinLedger.Bip32.encodePathStepsAux path.toList (ByteArray.mk #[UInt8.ofNat path.size])
  refine ⟨bs, ?_, ?_, ?_⟩
  · unfold serializeBip32Path?
    rw [hnotGt]
    rfl
  · have hlist := encodePathStepsAux_toList path.toList (ByteArray.mk #[UInt8.ofNat path.size])
    have hsize : bs.size = bs.data.toList.length := rfl
    rw [hsize, hlist, List.length_append, encodeStepsList_length]
    rfl
  · unfold parseBip32Path?
    have hlist := encodePathStepsAux_toList path.toList (ByteArray.mk #[UInt8.ofNat path.size])
    change (match bs.data.toList with
      | [] => none
      | lenByte :: rest =>
          if decide (rest.length ≠ 4 * lenByte.toNat) = true then none
          else BitcoinLedger.Bip32.parsePathStepsAux lenByte.toNat rest #[]) = some path
    rw [hlist]
    change (if decide ((encodeStepsList path.toList).length ≠ 4 * (UInt8.ofNat path.size).toNat) = true
            then none
            else BitcoinLedger.Bip32.parsePathStepsAux (UInt8.ofNat path.size).toNat
              (encodeStepsList path.toList) #[]) = some path
    have hlt256 : path.size < 256 := Nat.lt_succ_of_le hle
    have hu8 : (UInt8.ofNat path.size).toNat = path.size := by
      rw [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt hlt256
    rw [hu8, encodeStepsList_length]
    have hplen : path.toList.length = path.size := rfl
    rw [hplen]
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [← hplen, parsePathStepsAux_encodeStepsList]
    simp

/-- `serializeBip32Path?` rejects paths exceeding the 1-byte BIP-32 ceiling (`> 255`). -/
theorem serializeBip32Path?_rejects_over_255 {path : Bip32Path}
    (hgt : MAX_BIP32_BYTE_DEPTH < path.size) :
    serializeBip32Path? path = none := by
  unfold serializeBip32Path?
  have hd : decide (path.size > MAX_BIP32_BYTE_DEPTH) = true := decide_eq_true hgt
  rw [hd]
  rfl

/-- `parseBip32Path?` rejects empty buffers and buffers whose trailing byte count is not `4 * count`. -/
theorem parseBip32Path?_rejects_malformed :
    parseBip32Path? ByteArray.empty = none ∧
    parseBip32Path? (ByteArray.mk #[1, 0x80, 0x00, 0x00]) = none ∧
    parseBip32Path? (ByteArray.mk #[0, 0x00]) = none := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## 3. 78-Byte `ExtendedPubKey` & Base58Check Equivalence & Roundtrips -/

theorem isValidCompressedPubKey_eq (bs : ByteArray) :
    BitcoinLedger.Bip32.isValidCompressedPubKey bs = InternalSpec.isValidCompressedPubKey bs :=
  rfl

theorem isWellFormedExtendedPubKey_iff (xpub : ExtendedPubKey) :
    isWellFormedExtendedPubKey xpub = true ↔ xpub.WellFormed := by
  unfold isWellFormedExtendedPubKey InternalSpec.ExtendedPubKey.WellFormed
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  rw [Proofs.Basic.isBytes4_iff, Proofs.Basic.isBytes32_iff, isValidCompressedPubKey_eq]
  constructor
  · rintro ⟨⟨⟨hfp, hcc⟩, hpk⟩, hroot⟩
    refine ⟨hfp, hcc, hpk, ?_⟩
    intro hd0
    have hd : decide (xpub.depth = 0) = true := decide_eq_true hd0
    rw [hd] at hroot
    simp only [↓reduceIte, Bool.and_eq_true, Proofs.Basic.eqBytes_iff, decide_eq_true_iff] at hroot
    exact hroot
  · rintro ⟨hfp, hcc, hpk, hroot⟩
    refine ⟨⟨⟨hfp, hcc⟩, hpk⟩, ?_⟩
    cases hd : decide (xpub.depth = 0)
    · rfl
    · simp only [↓reduceIte, Bool.and_eq_true, Proofs.Basic.eqBytes_iff, decide_eq_true_iff]
      exact hroot (of_decide_eq_true hd)

/-- Executable `serializeExtendedPubKey` refines `InternalSpec.ExtendedPubKey.serialize`. -/
theorem serializeExtendedPubKey_eq (xpub : ExtendedPubKey) :
    serializeExtendedPubKey xpub = xpub.serialize := by
  unfold serializeExtendedPubKey InternalSpec.ExtendedPubKey.serialize
  rw [Proofs.Basic.encodeU32BE_eq, Proofs.Basic.encodeU32BE_eq]

/-- Executable `deserializeExtendedPubKey?` refines `InternalSpec.deserializeExtendedPubKey?`. -/
theorem deserializeExtendedPubKey?_eq (bs : ByteArray) :
    BitcoinLedger.Bip32.deserializeExtendedPubKey? bs = InternalSpec.deserializeExtendedPubKey? bs := by
  unfold BitcoinLedger.Bip32.deserializeExtendedPubKey? InternalSpec.deserializeExtendedPubKey?
  cases hsz : decide (bs.size ≠ 78)
  · have hnsz : ¬ (bs.size ≠ 78) := of_decide_eq_false hsz
    simp only [Bool.false_eq_true, hnsz, ↓reduceIte]
    let bytes := bs.data.toList
    let verBytes := ByteArray.mk ((bytes.drop 0).take 4).toArray
    let depthByte := (ByteArray.mk ((bytes.drop 4).take 1).toArray).data.toList.headD 0
    let parentFp := ByteArray.mk ((bytes.drop 5).take 4).toArray
    let childBytes := ByteArray.mk ((bytes.drop 9).take 4).toArray
    let chainCode := ByteArray.mk ((bytes.drop 13).take 32).toArray
    let pubkey := ByteArray.mk ((bytes.drop 45).take 33).toArray
    change
      (match BitcoinLedger.Basic.decodeU32BE? verBytes, BitcoinLedger.Basic.decodeU32BE? childBytes with
       | some version, some childNumber =>
           if !isValidCompressedPubKey pubkey then none
           else if decide (depthByte = 0) && (!BitcoinLedger.Basic.eqBytes parentFp zeroFingerprint4 || !decide (childNumber = 0)) then none
           else some ({ version, depth := depthByte, parentFingerprint := parentFp, childNumber, chainCode, pubkey } : ExtendedPubKey)
       | _, _ => none) =
      (match InternalSpec.decodeU32BE? verBytes, InternalSpec.decodeU32BE? childBytes with
       | some version, some childNumber =>
           if !InternalSpec.isValidCompressedPubKey pubkey then none
           else if depthByte = 0 ∧ (parentFp ≠ InternalSpec.zeroFingerprint4 ∨ childNumber ≠ 0) then none
           else some ({ version, depth := depthByte, parentFingerprint := parentFp, childNumber, chainCode, pubkey } : ExtendedPubKey)
       | _, _ => none)
    rw [Proofs.Basic.decodeU32BE?_eq, Proofs.Basic.decodeU32BE?_eq, isValidCompressedPubKey_eq]
    cases InternalSpec.decodeU32BE? verBytes with
    | none => rfl
    | some ver =>
        cases InternalSpec.decodeU32BE? childBytes with
        | none => rfl
        | some ch =>
            dsimp only
            cases InternalSpec.isValidCompressedPubKey pubkey
            · rfl
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              cases hd0 : decide (depthByte = 0)
              · have hnd0 : depthByte ≠ 0 := of_decide_eq_false hd0
                simp [hnd0]
              · have hyd0 : depthByte = 0 := of_decide_eq_true hd0
                cases hfp : BitcoinLedger.Basic.eqBytes parentFp zeroFingerprint4
                · have hnfp : parentFp ≠ InternalSpec.zeroFingerprint4 := by
                    intro heq
                    have htrue := (Proofs.Basic.eqBytes_iff parentFp zeroFingerprint4).mpr heq
                    rw [hfp] at htrue
                    cases htrue
                  simp [hyd0, hnfp]
                · have hyfp : parentFp = InternalSpec.zeroFingerprint4 :=
                    (Proofs.Basic.eqBytes_iff parentFp zeroFingerprint4).mp hfp
                  cases hch0 : decide (ch = 0)
                  · have hnch : ch ≠ 0 := of_decide_eq_false hch0
                    simp [hyd0, hyfp, hnch]
                  · have hych : ch = 0 := of_decide_eq_true hch0
                    simp [hyd0, hyfp, hych]
  · have hysz : bs.size ≠ 78 := of_decide_eq_true hsz
    simp [hysz]

/-- Roundtrip theorem for 78-byte `ExtendedPubKey` serialization & deserialization
    (strictly constructive, `0 Classical.choice`). -/
theorem deserializeExtendedPubKey?_serializeExtendedPubKey {xpub : ExtendedPubKey}
    (hwf : xpub.WellFormed) :
    BitcoinLedger.Bip32.deserializeExtendedPubKey? (serializeExtendedPubKey xpub) = some xpub := by
  rcases hwf with ⟨hfp, hcc, hpk, hroot⟩
  unfold InternalSpec.Bytes4 InternalSpec.BytesN at hfp
  unfold InternalSpec.Bytes32 InternalSpec.BytesN at hcc
  have hpkBool : isValidCompressedPubKey xpub.pubkey = true := hpk
  have hpkSize : xpub.pubkey.size = 33 := by
    unfold isValidCompressedPubKey BitcoinLedger.Basic.isBytes33 BitcoinLedger.Basic.isBytesN at hpkBool
    cases h : decide (xpub.pubkey.size = 33)
    · simp [h] at hpkBool
    · exact of_decide_eq_true h
  let bVer := BitcoinLedger.Basic.encodeU32BE xpub.version
  let bDep := ByteArray.mk #[xpub.depth]
  let bFp := xpub.parentFingerprint
  let bCh := BitcoinLedger.Basic.encodeU32BE xpub.childNumber
  let bCc := xpub.chainCode
  let bPk := xpub.pubkey
  have sVer : bVer.size = 4 := rfl
  have sDep : bDep.size = 1 := rfl
  have sCh : bCh.size = 4 := rfl
  have hsize : (serializeExtendedPubKey xpub).size = 78 := by
    unfold serializeExtendedPubKey
    simp only [ByteArray.size_append]
    rw [sVer, sDep, hfp, sCh, hcc, hpkSize]
  have hser : serializeExtendedPubKey xpub = bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk)))) := by
    unfold serializeExtendedPubKey
    simp only [bVer, bDep, bFp, bCh, bCc, bPk, ByteArray.append_assoc]
  have slice_head : ∀ {a b : ByteArray} {n : Nat}, a.size = n →
      BitcoinLedger.Bip32.sliceListBytes (a ++ b).data.toList 0 n = a := by
    intro a b n ha
    have hl : a.data.toList.length = n := ha
    unfold BitcoinLedger.Bip32.sliceListBytes
    cases a; cases b
    simp [ByteArray.data_append, hl]
  have slice_tail : ∀ {a b : ByteArray} {k s m : Nat}, a.size = k →
      BitcoinLedger.Bip32.sliceListBytes (a ++ b).data.toList (k + s) m =
        BitcoinLedger.Bip32.sliceListBytes b.data.toList s m := by
    intro a b k s m ha
    unfold BitcoinLedger.Bip32.sliceListBytes
    cases a with
    | mk arrA =>
        cases b with
        | mk arrB =>
            have hl : arrA.toList.length = k := ha
            have hdrop : List.drop (k + s) arrA.toList = [] :=
              List.drop_eq_nil_of_le (by rw [hl]; exact Nat.le_add_right k s)
            simp [ByteArray.data_append, List.drop_append, hl, hdrop]
  have slice_exact : ∀ {a : ByteArray} {n : Nat}, a.size = n →
      BitcoinLedger.Bip32.sliceListBytes a.data.toList 0 n = a := by
    intro a n ha
    unfold BitcoinLedger.Bip32.sliceListBytes
    cases a with
    | mk arr =>
        have hl : arr.toList.length = n := ha
        simp only [List.drop_zero]
        rw [← hl, List.take_length]
  unfold BitcoinLedger.Bip32.deserializeExtendedPubKey?
  simp only [hsize, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [hser]
  have eVer : BitcoinLedger.Bip32.sliceListBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 0 4 = bVer :=
    slice_head sVer
  have eDep : BitcoinLedger.Bip32.sliceListBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 4 1 = bDep := by
    rw [show (4 : Nat) = 4 + 0 from rfl, slice_tail sVer]
    exact slice_head sDep
  have eFp : BitcoinLedger.Bip32.sliceListBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 5 4 = bFp := by
    rw [show (5 : Nat) = 4 + (1 + 0) from rfl, slice_tail sVer, slice_tail sDep]
    exact slice_head hfp
  have eCh : BitcoinLedger.Bip32.sliceListBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 9 4 = bCh := by
    rw [show (9 : Nat) = 4 + (1 + (4 + 0)) from rfl, slice_tail sVer, slice_tail sDep, slice_tail hfp]
    exact slice_head sCh
  have eCc : BitcoinLedger.Bip32.sliceListBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 13 32 = bCc := by
    rw [show (13 : Nat) = 4 + (1 + (4 + (4 + 0))) from rfl, slice_tail sVer, slice_tail sDep, slice_tail hfp, slice_tail sCh]
    exact slice_head hcc
  have ePk : BitcoinLedger.Bip32.sliceListBytes (bVer ++ (bDep ++ (bFp ++ (bCh ++ (bCc ++ bPk))))).data.toList 45 33 = bPk := by
    rw [show (45 : Nat) = 4 + (1 + (4 + (4 + (32 + 0)))) from rfl, slice_tail sVer, slice_tail sDep, slice_tail hfp, slice_tail sCh, slice_tail hcc]
    exact slice_exact hpkSize
  rw [eVer, eDep, eFp, eCh, eCc, ePk]
  rw [Proofs.Basic.decodeU32BE?_roundtrip, Proofs.Basic.decodeU32BE?_roundtrip]
  have hHead : bDep.data.toList.headD 0 = xpub.depth := rfl
  rw [hHead]
  simp only [bFp, bCc, bPk, hpkBool, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hd0 : decide (xpub.depth = 0)
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hfp0, hch0⟩ := hroot (of_decide_eq_true hd0)
    have hfpEq : BitcoinLedger.Basic.eqBytes xpub.parentFingerprint zeroFingerprint4 = true :=
      (Proofs.Basic.eqBytes_iff _ _).mpr hfp0
    simp only [hfpEq, hch0, decide_true, Bool.not_true, Bool.or_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    cases xpub
    simp_all

/-- Base58Check `ExtendedPubKey` encoder refines `InternalSpec.encodeBase58Check?` over the 78-byte serialized payload. -/
theorem encodeExtendedPubKeyBase58Check?_eq
    (doubleSha256 : ByteArray → ByteArray) (xpub : ExtendedPubKey) (hwf : xpub.WellFormed) :
    encodeExtendedPubKeyBase58Check? doubleSha256 xpub =
      InternalSpec.encodeBase58Check? doubleSha256 ByteArray.empty xpub.serialize := by
  have hwfB : isWellFormedExtendedPubKey xpub = true := (isWellFormedExtendedPubKey_iff xpub).mpr hwf
  have hempty : ByteArray.empty ++ xpub.serialize = xpub.serialize := by
    cases xpub.serialize with
    | mk arr =>
        apply congrArg ByteArray.mk
        apply Array.ext'
        change ([] ++ arr.toList) = arr.toList
        rfl
  unfold encodeExtendedPubKeyBase58Check? InternalSpec.encodeBase58Check?
  rw [hwfB, serializeExtendedPubKey_eq, hempty]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases h : decide ((doubleSha256 xpub.serialize).size < 4)
  · have hn := of_decide_eq_false h
    simp [hn]
  · have hy := of_decide_eq_true h
    simp [hy]

/-- Base58Check `ExtendedPubKey` decoder refines `InternalSpec.decodeBase58Check? >>= InternalSpec.deserializeExtendedPubKey?`. -/
theorem decodeExtendedPubKeyBase58Check?_eq
    (doubleSha256 : ByteArray → ByteArray) (encoded : String) :
    decodeExtendedPubKeyBase58Check? doubleSha256 encoded =
      (InternalSpec.decodeBase58Check? doubleSha256 encoded).bind InternalSpec.deserializeExtendedPubKey? := by
  unfold decodeExtendedPubKeyBase58Check? InternalSpec.decodeBase58Check?
  cases InternalSpec.decodeBase58? encoded with
  | none => rfl
  | some raw =>
      dsimp only
      cases hr : decide (raw.size < 4)
      · have hnr := of_decide_eq_false hr
        simp only [Bool.false_eq_true, hnr, ↓reduceIte]
        let body := ByteArray.mk (raw.data.toList.take (raw.size - 4)).toArray
        cases hd : decide ((doubleSha256 body).size < 4)
        · have hnd := of_decide_eq_false hd
          simp only [body, Bool.false_eq_true, hnd, ↓reduceIte]
          let gcs := ByteArray.mk (raw.data.toList.drop (raw.size - 4)).toArray
          let ecs := ByteArray.mk ((doubleSha256 body).data.toList.take 4).toArray
          change (if BitcoinLedger.Basic.eqBytes gcs ecs = true then deserializeExtendedPubKey? body else none) =
                 (if gcs = ecs then some body else none).bind InternalSpec.deserializeExtendedPubKey?
          cases hc : BitcoinLedger.Basic.eqBytes gcs ecs
          · have hnc : gcs ≠ ecs := fun heq => by
              have ht := (Proofs.Basic.eqBytes_iff gcs ecs).mpr heq
              rw [hc] at ht; cases ht
            simp [hnc, Option.bind]
          · have hyc : gcs = ecs := (Proofs.Basic.eqBytes_iff gcs ecs).mp hc
            simp [hyc, Option.bind, deserializeExtendedPubKey?_eq]
        · have hyd := of_decide_eq_true hd
          simp [body, hyd, Option.bind]
      · have hyr := of_decide_eq_true hr
        simp [hyr, Option.bind]

/-! ## 4. HD Derivation & `GET_EXTENDED_PUBKEY` Policy Equivalence -/

theorem deriveChildExtendedPubKey?_eq
    (oracle : CryptoDerivationOracle) (parent : ExtendedPubKey) (childIdx : UInt32) :
    BitcoinLedger.Bip32.deriveChildExtendedPubKey? oracle parent childIdx =
      InternalSpec.deriveChildExtendedPubKey? oracle parent childIdx := by
  unfold BitcoinLedger.Bip32.deriveChildExtendedPubKey? InternalSpec.deriveChildExtendedPubKey?
  rw [isHardened_eq]
  rfl

theorem deriveMasterFingerprint?_eq (oracle : CryptoDerivationOracle) (tree : KeyTree) :
    BitcoinLedger.Bip32.deriveMasterFingerprint? oracle tree =
      InternalSpec.deriveMasterFingerprint? oracle tree :=
  rfl

theorem deriveExtendedPubKeyWithOracle_eq
    (oracle : CryptoDerivationOracle) (net : InternalSpec.Network) (tree : KeyTree) (path : Bip32Path) :
    BitcoinLedger.Bip32.deriveExtendedPubKeyWithOracle oracle net tree path =
      InternalSpec.deriveExtendedPubKeyWithOracle oracle net tree path := by
  unfold BitcoinLedger.Bip32.deriveExtendedPubKeyWithOracle InternalSpec.deriveExtendedPubKeyWithOracle
  unfold MAX_BIP32_BYTE_DEPTH InternalSpec.MAX_BIP32_BYTE_DEPTH zeroFingerprint4 InternalSpec.zeroFingerprint4
  rw [Proofs.Basic.networkParams_eq, deriveMasterFingerprint?_eq]
  cases hgt : decide (path.size > 255)
  · have hngt := of_decide_eq_false hgt
    simp only [Bool.false_eq_true, hngt, ↓reduceIte]
    cases oracle.deriveNode tree path with
    | none => rfl
    | some pair =>
        dsimp only
        cases h0 : decide (path.size = 0)
        · have hn0 := of_decide_eq_false h0
          simp only [Bool.false_eq_true, hn0, ↓reduceIte]
          cases h1 : decide (path.size = 1)
          · have hn1 := of_decide_eq_false h1
            simp only [Bool.false_eq_true, hn1, ↓reduceIte]
            cases oracle.deriveNode tree path.pop with
            | none => rfl
            | some ppair =>
                dsimp only
                cases hlt : decide ((oracle.hash160 ppair.1).size < 4)
                · have hnlt := of_decide_eq_false hlt
                  simp [hnlt]
                · have hylt := of_decide_eq_true hlt
                  simp [hylt]
          · have hy1 := of_decide_eq_true h1
            simp only [hy1, ↓reduceIte]
            rfl
        · have hy0 := of_decide_eq_true h0
          simp [hy0]
  · have hygt := of_decide_eq_true hgt
    simp [hygt]

theorem allHardened_eq (steps : List UInt32) :
    BitcoinLedger.Bip32.allHardened steps = InternalSpec.allHardened steps := by
  unfold BitcoinLedger.Bip32.allHardened InternalSpec.allHardened
  induction steps with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons, isHardened_eq]
      exact congrArg _ ih

theorem allUnhardened_eq (steps : List UInt32) :
    BitcoinLedger.Bip32.allUnhardened steps = InternalSpec.allUnhardened steps := by
  unfold BitcoinLedger.Bip32.allUnhardened InternalSpec.allUnhardened
  induction steps with
  | nil => rfl
  | cons x xs ih =>
      change (!BitcoinLedger.Bip32.isHardened x && xs.all (fun idx => !BitcoinLedger.Bip32.isHardened idx)) =
             (!InternalSpec.isHardened x && xs.all (fun idx => !InternalSpec.isHardened idx))
      rw [isHardened_eq]
      exact congrArg _ ih

theorem isStandard3StepPurpose_eq (purpose : UInt32) :
    BitcoinLedger.Bip32.isStandard3StepPurpose purpose = InternalSpec.isStandard3StepPurpose purpose := by
  unfold BitcoinLedger.Bip32.isStandard3StepPurpose InternalSpec.isStandard3StepPurpose
  cases h1 : decide (purpose = 44) <;>
  cases h2 : decide (purpose = 49) <;>
  cases h3 : decide (purpose = 84) <;>
  cases h4 : decide (purpose = 86) <;>
  cases h5 : decide (purpose = 87) <;>
  cases h6 : decide (purpose = 45)
  all_goals
    try (have := of_decide_eq_true h1; simp [*])
    try (have := of_decide_eq_true h2; simp [*])
    try (have := of_decide_eq_true h3; simp [*])
    try (have := of_decide_eq_true h4; simp [*])
    try (have := of_decide_eq_true h5; simp [*])
    try (have := of_decide_eq_true h6; simp [*])
    try (
      have n1 := of_decide_eq_false h1
      have n2 := of_decide_eq_false h2
      have n3 := of_decide_eq_false h3
      have n4 := of_decide_eq_false h4
      have n5 := of_decide_eq_false h5
      have n6 := of_decide_eq_false h6
      simp [n1, n2, n3, n4, n5, n6]
    )

theorem isBolosOsPermittedPath_eq (net : InternalSpec.Network) (path : Bip32Path) :
    BitcoinLedger.Bip32.isBolosOsPermittedPath net path = InternalSpec.isBolosOsPermittedPath net path := by
  unfold BitcoinLedger.Bip32.isBolosOsPermittedPath InternalSpec.isBolosOsPermittedPath
  unfold BIP45_PURPOSE InternalSpec.BIP45_PURPOSE ELECTRUM_ENCRYPTION_PURPOSE InternalSpec.ELECTRUM_ENCRYPTION_PURPOSE
  rw [Proofs.Basic.networkParams_eq]
  simp only [harden_eq]
  match path.toList with
  | [] => rfl
  | [s0] =>
      dsimp only
      cases h1 : decide (s0 = InternalSpec.harden 4541509) <;>
      cases h2 : decide (s0 = InternalSpec.harden 45)
      all_goals
        try (have := of_decide_eq_true h1; simp [*])
        try (have := of_decide_eq_true h2; simp [*])
        try (have n1 := of_decide_eq_false h1; have n2 := of_decide_eq_false h2; simp [n1, n2])
  | s0 :: s1 :: rest =>
      dsimp only
      cases h1 : decide (s0 = InternalSpec.harden 4541509) <;>
      cases h2 : decide (s0 = InternalSpec.harden 45) <;>
      cases h3 : decide (s1 = InternalSpec.harden net.params.bip44CoinType)
      all_goals
        try (have := of_decide_eq_true h1; simp [*])
        try (have := of_decide_eq_true h2; simp [*])
        try (have := of_decide_eq_true h3; simp [*])
        try (
          have n1 := of_decide_eq_false h1
          have n2 := of_decide_eq_false h2
          have n3 := of_decide_eq_false h3
          simp [n1, n2, n3]
        )

theorem isBolosSafePubkeyExportPath_eq (net : InternalSpec.Network) (path : Bip32Path) :
    BitcoinLedger.Bip32.isBolosSafePubkeyExportPath net path =
      InternalSpec.isBolosSafePubkeyExportPath net path := by
  unfold BitcoinLedger.Bip32.isBolosSafePubkeyExportPath InternalSpec.isBolosSafePubkeyExportPath
  unfold ELECTRUM_ENCRYPTION_PURPOSE InternalSpec.ELECTRUM_ENCRYPTION_PURPOSE
  unfold ELECTRUM_ENCRYPTION_SUBPATH InternalSpec.ELECTRUM_ENCRYPTION_SUBPATH
  unfold MAX_BIP44_ACCOUNT_RECOMMENDED InternalSpec.MAX_BIP44_ACCOUNT_RECOMMENDED
  rw [Proofs.Basic.networkParams_eq]
  simp only [harden_eq, isHardened_eq, unharden_eq, isStandard3StepPurpose_eq, allUnhardened_eq]
  match path.toList with
  | [] => rfl
  | [_] => rfl
  | [s0, s1] =>
      dsimp only
      cases h1 : decide (s0 = InternalSpec.harden 4541509) <;>
      cases h2 : decide (s1 = InternalSpec.harden 1112098098)
      all_goals
        try (have n1 := of_decide_eq_false h1; simp [n1])
        try (have n2 := of_decide_eq_false h2; simp [n2])
        try (have y1 := of_decide_eq_true h1; have y2 := of_decide_eq_true h2; simp [y1, y2])
  | s0 :: s1 :: s2 :: rest =>
      dsimp only
      cases hh : (InternalSpec.isHardened s0 && InternalSpec.isHardened s1 && InternalSpec.isHardened s2)
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hc : decide (InternalSpec.unharden s1 = net.params.bip44CoinType)
        · have hnc := of_decide_eq_false hc
          simp [hnc]
        · have hyc := of_decide_eq_true hc
          cases ha : decide ((100 : UInt32) < InternalSpec.unharden s2)
          · have hna := of_decide_eq_false ha
            simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, hyc, ne_eq, not_true_eq_false, hna, false_or, ↓reduceIte]
            cases InternalSpec.isStandard3StepPurpose (InternalSpec.unharden s0)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases hp48 : decide (InternalSpec.unharden s0 = 48)
              · have hnp := of_decide_eq_false hp48
                simp [hnp]
              · have hyp := of_decide_eq_true hp48
                simp only [hyp, ↓reduceIte]
                cases rest with
                | nil => rfl
                | cons s3 tail =>
                    dsimp only
                    cases InternalSpec.isHardened s3
                    · rfl
                    · cases hs1 : decide (InternalSpec.unharden s3 = 1) <;>
                      cases hs2 : decide (InternalSpec.unharden s3 = 2)
                      all_goals
                        try (have := of_decide_eq_true hs1; simp [*])
                        try (have := of_decide_eq_true hs2; simp [*])
                        try (have m1 := of_decide_eq_false hs1; have m2 := of_decide_eq_false hs2; simp [m1, m2])
            · rfl
          · have hya := of_decide_eq_true ha
            simp [hyc, hya]

theorem isStandardBip352Path_eq (net : InternalSpec.Network) (path : Bip32Path) :
    BitcoinLedger.Bip32.isStandardBip352Path net path = InternalSpec.isStandardBip352Path net path := by
  unfold BitcoinLedger.Bip32.isStandardBip352Path InternalSpec.isStandardBip352Path
  unfold MAX_BIP44_ACCOUNT_RECOMMENDED InternalSpec.MAX_BIP44_ACCOUNT_RECOMMENDED
  rw [Proofs.Basic.networkParams_eq]
  match path.toList with
  | s0 :: s1 :: s2 :: s3 :: tail =>
      dsimp only
      rw [isHardened_eq, isHardened_eq, isHardened_eq, isHardened_eq,
          unharden_eq, unharden_eq, unharden_eq, unharden_eq, allUnhardened_eq]
      have hor :
          (decide (InternalSpec.unharden s3 = 0) || decide (InternalSpec.unharden s3 = 1)) =
          decide (InternalSpec.unharden s3 = 0 ∨ InternalSpec.unharden s3 = 1) := by
        cases h0 : decide (InternalSpec.unharden s3 = 0) <;>
        cases h1 : decide (InternalSpec.unharden s3 = 1)
        · exact (decide_eq_false (fun h => h.elim (of_decide_eq_false h0) (of_decide_eq_false h1))).symm
        · exact (decide_eq_true (Or.inr (of_decide_eq_true h1))).symm
        · exact (decide_eq_true (Or.inl (of_decide_eq_true h0))).symm
        · exact (decide_eq_true (Or.inl (of_decide_eq_true h0))).symm
      rw [hor]
  | [] | [_] | [_, _] | [_, _, _] => rfl

/-- Exact equivalence between `BitcoinLedger.Bip32.classifyExpubPathWithTree` and `InternalSpec.classifyExpubPathWithTree`. -/
theorem classifyExpubPathWithTree_eq
    (cfg : ExpubPolicyConfig) (net : InternalSpec.Network) (tree : KeyTree) (path : Bip32Path) :
    BitcoinLedger.Bip32.classifyExpubPathWithTree cfg net tree path =
      InternalSpec.classifyExpubPathWithTree cfg net tree path := by
  unfold BitcoinLedger.Bip32.classifyExpubPathWithTree InternalSpec.classifyExpubPathWithTree
  unfold MAX_BIP32_BYTE_DEPTH InternalSpec.MAX_BIP32_BYTE_DEPTH
  rw [isBolosOsPermittedPath_eq, isBolosSafePubkeyExportPath_eq, isStandardBip352Path_eq]
  rfl

theorem classifyExpubPath_eq
    (cfg : ExpubPolicyConfig) (net : InternalSpec.Network) (path : Bip32Path) :
    BitcoinLedger.Bip32.classifyExpubPath cfg net path =
      InternalSpec.classifyExpubPath cfg net path :=
  classifyExpubPathWithTree_eq cfg net .standard path

theorem authorizeExtendedPubKeyExport_eq
    (cfg : ExpubPolicyConfig) (net : InternalSpec.Network) (tree : KeyTree)
    (path : Bip32Path) (display userApproved : Bool) :
    BitcoinLedger.Bip32.authorizeExtendedPubKeyExport cfg net tree path display userApproved =
      InternalSpec.authorizeExtendedPubKeyExport cfg net tree path display userApproved := by
  unfold BitcoinLedger.Bip32.authorizeExtendedPubKeyExport InternalSpec.authorizeExtendedPubKeyExport
  rw [classifyExpubPathWithTree_eq]
  rfl

theorem evalGetExtendedPubkey_eq
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : InternalSpec.Network)
    (tree : KeyTree) (path : Bip32Path) (display userApproved : Bool) :
    BitcoinLedger.Bip32.evalGetExtendedPubkey oracle cfg net tree path display userApproved =
      InternalSpec.evalGetExtendedPubkey oracle cfg net tree path display userApproved := by
  unfold BitcoinLedger.Bip32.evalGetExtendedPubkey InternalSpec.evalGetExtendedPubkey
  rw [authorizeExtendedPubKeyExport_eq, deriveExtendedPubKeyWithOracle_eq]
  rfl

/-! ## 5. Constructive Security Theorems & Concrete Witnesses (`0 Classical.choice`) -/

/-- Security Theorem 1: Silent export (`display = false`) succeeds ONLY when the path is classified
    `.allowSilent` and has depth `≤ 255`. -/
theorem silent_export_requires_allowSilent
    {oracle : CryptoDerivationOracle} {cfg : ExpubPolicyConfig} {net : InternalSpec.Network}
    {tree : KeyTree} {path : Bip32Path} {userApproved : Bool} {xpub : ExtendedPubKey}
    (hok : BitcoinLedger.Bip32.evalGetExtendedPubkey oracle cfg net tree path false userApproved = .ok xpub) :
    BitcoinLedger.Bip32.classifyExpubPathWithTree cfg net tree path = .allowSilent ∧
    path.size ≤ MAX_BIP32_BYTE_DEPTH := by
  unfold BitcoinLedger.Bip32.evalGetExtendedPubkey BitcoinLedger.Bip32.authorizeExtendedPubKeyExport at hok
  cases hdec : BitcoinLedger.Bip32.classifyExpubPathWithTree cfg net tree path with
  | reject err => simp [hdec, bind, Except.bind] at hok
  | warnUnusual => simp [hdec, bind, Except.bind] at hok
  | allowSilent =>
      refine ⟨rfl, ?_⟩
      unfold BitcoinLedger.Bip32.classifyExpubPathWithTree at hdec
      cases tree <;> dsimp only at hdec
      · cases hgt : (decide (path.size > cfg.maxSteps) || decide (path.size > MAX_BIP32_BYTE_DEPTH))
        · simp only [Bool.or_eq_false_iff] at hgt
          exact Nat.le_of_not_lt (of_decide_eq_false hgt.2)
        · rw [hgt] at hdec; cases hdec
      · cases hres : cfg.maxResidentSteps? with
        | none => rw [hres] at hdec; cases hdec
        | some maxR =>
            rw [hres] at hdec
            dsimp only at hdec
            cases hgt : (decide (path.size > maxR) || decide (path.size > MAX_BIP32_BYTE_DEPTH))
            · simp only [Bool.or_eq_false_iff] at hgt
              exact Nat.le_of_not_lt (of_decide_eq_false hgt.2)
            · rw [hgt] at hdec; cases hdec

/-- Security Theorem 2: Over-depth paths (`cfg.maxSteps < path.size`) on `.standard` are ALWAYS rejected
    with `.bip32PathTooLong`, regardless of `display` or `userApproved`. -/
theorem over_depth_always_rejected
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : InternalSpec.Network)
    (path : Bip32Path) (display userApproved : Bool)
    (hover : cfg.maxSteps < path.size) :
    BitcoinLedger.Bip32.evalGetExtendedPubkey oracle cfg net .standard path display userApproved =
      .error .bip32PathTooLong := by
  have hd : decide (path.size > cfg.maxSteps) = true := decide_eq_true hover
  unfold BitcoinLedger.Bip32.evalGetExtendedPubkey BitcoinLedger.Bip32.authorizeExtendedPubKeyExport
  unfold BitcoinLedger.Bip32.classifyExpubPathWithTree
  simp [hd, bind, Except.bind]

/-- Security Theorem 3 (Unhardened First Step Rejection): Under whitelist-enforcing policies
    (`cfg.requireSafeWhitelistForSilent = true`), any path starting with an unhardened index
    is ALWAYS rejected when `display = false`. -/
theorem unhardened_first_step_rejected_silently
    (oracle : CryptoDerivationOracle) (cfg : ExpubPolicyConfig) (net : InternalSpec.Network)
    (path : Bip32Path) (userApproved : Bool)
    (s0 : UInt32) (rest : List UInt32)
    (hReq : cfg.requireSafeWhitelistForSilent = true)
    (hlist : path.toList = s0 :: rest)
    (hunhard : BitcoinLedger.Bip32.isHardened s0 = false) :
    ∃ err : InternalSpec.SpecError,
      BitcoinLedger.Bip32.evalGetExtendedPubkey oracle cfg net .standard path false userApproved = .error err := by
  have hnotBolos : BitcoinLedger.Bip32.isBolosSafePubkeyExportPath net path = false := by
    unfold BitcoinLedger.Bip32.isBolosSafePubkeyExportPath
    rw [hlist]
    cases rest with
    | nil => rfl
    | cons s1 r1 =>
        cases r1 with
        | nil =>
            dsimp only
            cases hs0 : decide (s0 = BitcoinLedger.Bip32.harden ELECTRUM_ENCRYPTION_PURPOSE)
            · rfl
            · exfalso
              have heq := of_decide_eq_true hs0
              rw [heq, isHardened_harden] at hunhard
              cases hunhard
        | cons s2 r2 =>
            simp [hunhard]
  have hnot352 : BitcoinLedger.Bip32.isStandardBip352Path net path = false := by
    unfold BitcoinLedger.Bip32.isStandardBip352Path
    rw [hlist]
    cases rest with
    | nil => rfl
    | cons s1 r1 =>
        cases r1 with
        | nil => rfl
        | cons s2 r2 =>
            cases r2 with
            | nil => rfl
            | cons s3 r3 => simp [hunhard]
  unfold BitcoinLedger.Bip32.evalGetExtendedPubkey BitcoinLedger.Bip32.authorizeExtendedPubKeyExport
  unfold BitcoinLedger.Bip32.classifyExpubPathWithTree
  dsimp only
  cases hlen : (decide (path.size > cfg.maxSteps) || decide (path.size > MAX_BIP32_BYTE_DEPTH))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hos : (cfg.enforceBolosOsPathLock && !BitcoinLedger.Bip32.isBolosOsPermittedPath net path)
    · simp only [Bool.false_eq_true, ↓reduceIte, hReq, Bool.not_true, hnotBolos, hnot352,
        Bool.and_false, Bool.or_false]
      cases cfg.strictRejectUnusual <;> simp [bind, Except.bind]
    · simp [bind, Except.bind]
  · simp [bind, Except.bind]

/-- Security Theorem 4 (Warning Soundness): Whenever a path is classified `.warnUnusual`,
    silent export (`display = false`) fails with `.unsupportedBip32Path`, and interactive export
    (`display = true`) without user approval (`userApproved = false`) fails with `.userRejected`. -/
theorem warnUnusual_soundness
    {cfg : ExpubPolicyConfig} {net : InternalSpec.Network} {tree : KeyTree} {path : Bip32Path}
    (hwarn : BitcoinLedger.Bip32.classifyExpubPathWithTree cfg net tree path = .warnUnusual) :
    (∀ userApproved,
      BitcoinLedger.Bip32.authorizeExtendedPubKeyExport cfg net tree path false userApproved =
        .error .unsupportedBip32Path) ∧
    BitcoinLedger.Bip32.authorizeExtendedPubKeyExport cfg net tree path true false =
      .error .userRejected ∧
    BitcoinLedger.Bip32.authorizeExtendedPubKeyExport cfg net tree path true true =
      .ok () := by
  unfold BitcoinLedger.Bip32.authorizeExtendedPubKeyExport
  rw [hwarn]
  exact ⟨fun _ => rfl, rfl, rfl⟩

/-- Concrete witness theorem exercising standard BIP-84, BIP-48, Electrum, BIP-45, OS path lock,
    BOLOS depth-10 vs Vanadium depth-16 gates, and wire path roundtrip. -/
theorem witness_bip32_policies_and_wire_codec :
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 84, harden 0, harden 0] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 48, harden 0, harden 0, harden 2] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 48, harden 0, harden 0, harden 3] = .warnUnusual ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 4541509, harden 1112098098] = .allowSilent ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[harden 45] = .warnUnusual ∧
    classifyExpubPath bolosExpubPolicyConfig .mainnet #[] = .reject .notSupported ∧
    classifyExpubPath bolosExpubPolicyConfig .testnet #[harden 84, harden 0, harden 0] = .reject .notSupported ∧
    classifyExpubPath bolosRecoveryExpubPolicyConfig .testnet #[harden 84, harden 0, harden 0] = .warnUnusual ∧
    checkBolosDepth (Array.mk (List.replicate 10 0)) = true ∧
    checkBolosDepth (Array.mk (List.replicate 11 0)) = false ∧
    checkVanadiumDepth (Array.mk (List.replicate 16 0)) = true ∧
    checkVanadiumDepth (Array.mk (List.replicate 17 0)) = false ∧
    (serializeBip32Path? #[harden 84, harden 0, harden 0]).bind parseBip32Path? =
      some #[harden 84, harden 0, harden 0] := by
  decide

end Proofs.Bip32

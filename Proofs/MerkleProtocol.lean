import Spec
import BitcoinLedger.MerkleProtocol

namespace Proofs.MerkleProtocol

open Spec.Psbt (Bytes32 zeroBytes32)
open Spec.MerkleProtocol (
  MerkleDir
  MerkleElementOpening
  MerkleMapCommitment
  ClientCommandTag
  UntrustedHostOracle
  MapLookupResult
  MapLookupProof
  MerkleizedPsbtCommitment
  ContinuationApdu
  DeviceInterruptFrame
  PreimageInitFrame
  MoreElementsChunk
  PreimageStreamError
  CollisionFreeOn
)

/-!
# `Proofs.MerkleProtocol` — Constructive Refinement & Collision-Relative Soundness Proofs

Machine-checked constructive (`0 sorryAx`, `0 Classical.choice`, `0 native_decide`) refinement and
security theorems linking `BitcoinLedger.MerkleProtocol` to `Spec.MerkleProtocol`:
1. BOLOS APDU / client-command constants & primitive structural equality agreement.
2. Tail-recursive `merkleDirectionsBottomUp`, fuel-bounded `merkleRoot` / `buildMerkleAuditPath`,
   and bottom-up proof verification equivalence (`verifyMerkleLeafHashProof_eq_spec`,
   `verifyMerkleElementOpening_eq_spec`).
3. Strict lexicographic key sorting & single-pass `verifySortedKeyOpeningsLoop` refinement
   (`verifySortedMerkleMapOpenings_eq_spec`, `verifyMerkleMapLookup_eq_spec`).
4. Stateful `PreimageStreamState` / `feedPreimageChunk` streaming preimage refinement,
   multi-chunk reconstruction completeness, and malformed-frame rejection theorems.
5. Audit path completeness, duplicate/unsorted key rejection, depth/index/key-header overflow
   rejection, and finite-pool `CollisionFreeOn` soundness & anti-equivocation theorems.
6. Concrete non-vacuous execution witnesses.
-/

private theorem dite_true_constructive {α : Sort u} {p : Prop} [Decidable p]
    (h : p) (t : p → α) (e : ¬p → α) : (if hp : p then t hp else e hp) = t h := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd h hnp

private theorem dite_false_constructive {α : Sort u} {p : Prop} [Decidable p]
    (h : ¬p) (t : p → α) (e : ¬p → α) : (if hp : p then t hp else e hp) = e h := by
  cases ‹Decidable p› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

/-! ## 1. BOLOS Constants, Client-Command Codec & Primitive Equality Refinement -/

theorem constants_eq_spec :
    BitcoinLedger.MerkleProtocol.MAX_MERKLE_TREE_DEPTH = Spec.MerkleProtocol.MAX_MERKLE_TREE_DEPTH ∧
    BitcoinLedger.MerkleProtocol.MAX_MERKLE_LEAF_INDEX = Spec.MerkleProtocol.MAX_MERKLE_LEAF_INDEX ∧
    BitcoinLedger.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE = Spec.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE ∧
    BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_TOTAL_SIZE = Spec.MerkleProtocol.MAX_PREIMAGE_TOTAL_SIZE ∧
    BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_PARTIAL_SIZE = Spec.MerkleProtocol.MAX_PREIMAGE_PARTIAL_SIZE ∧
    BitcoinLedger.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT = Spec.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT ∧
    BitcoinLedger.MerkleProtocol.SW_INTERRUPTED_EXECUTION = Spec.MerkleProtocol.SW_INTERRUPTED_EXECUTION ∧
    BitcoinLedger.MerkleProtocol.CLA_FRAMEWORK = Spec.MerkleProtocol.CLA_FRAMEWORK ∧
    BitcoinLedger.MerkleProtocol.INS_CONTINUE = Spec.MerkleProtocol.INS_CONTINUE :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem client_command_opcodes_exact :
    BitcoinLedger.MerkleProtocol.CLA_APP = 0xE1 ∧
    BitcoinLedger.MerkleProtocol.CLA_FRAMEWORK = 0xF8 ∧
    BitcoinLedger.MerkleProtocol.INS_CONTINUE = 0x01 ∧
    BitcoinLedger.MerkleProtocol.SW_INTERRUPTED_EXECUTION = 0xE000 ∧
    BitcoinLedger.MerkleProtocol.CCMD_YIELD = 0x10 ∧
    BitcoinLedger.MerkleProtocol.CCMD_GET_PREIMAGE = 0x40 ∧
    BitcoinLedger.MerkleProtocol.CCMD_GET_MERKLE_LEAF_PROOF = 0x41 ∧
    BitcoinLedger.MerkleProtocol.CCMD_GET_MERKLE_LEAF_INDEX = 0x42 ∧
    BitcoinLedger.MerkleProtocol.CCMD_GET_MORE_ELEMENTS = 0xA0 ∧
    BitcoinLedger.MerkleProtocol.MAX_MERKLE_TREE_DEPTH = 32 ∧
    BitcoinLedger.MerkleProtocol.MAX_MERKLE_LEAF_INDEX = 0x7FFFFFFF ∧
    BitcoinLedger.MerkleProtocol.MAX_MAP_KEY_HEADER_LEN = 64 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem encodeClientCommandTag_eq_spec (tag : ClientCommandTag) :
    BitcoinLedger.MerkleProtocol.encodeClientCommandTag tag = tag.toByte := by
  cases tag <;> rfl

theorem decode_encode_clientCommandTag (tag : ClientCommandTag) :
    BitcoinLedger.MerkleProtocol.decodeClientCommandTag?
      (BitcoinLedger.MerkleProtocol.encodeClientCommandTag tag) = some tag := by
  cases tag <;> rfl

theorem eqByteList_eq_spec (xs ys : List UInt8) :
    BitcoinLedger.MerkleProtocol.eqByteList xs ys = Spec.MerkleProtocol.byteListEq xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          unfold BitcoinLedger.MerkleProtocol.eqByteList Spec.MerkleProtocol.byteListEq
          rw [ih ys]

theorem eqBytes_eq_spec (a b : ByteArray) :
    BitcoinLedger.MerkleProtocol.eqBytes a b = Spec.MerkleProtocol.merkleBytesEq a b :=
  eqByteList_eq_spec a.data.toList b.data.toList

theorem eqBytes32_eq_spec (a b : Bytes32) :
    BitcoinLedger.MerkleProtocol.eqBytes32 a b = Spec.MerkleProtocol.bytes32Eq a b :=
  eqBytes_eq_spec a.bytes b.bytes

theorem leafPreimage_eq_spec (data : ByteArray) :
    BitcoinLedger.MerkleProtocol.leafPreimage data = Spec.MerkleProtocol.leafPreimage data := rfl

theorem nodePreimage_eq_spec (l r : Bytes32) :
    BitcoinLedger.MerkleProtocol.nodePreimage l r = Spec.MerkleProtocol.nodePreimage l r := rfl

theorem merkleLeafHash_eq_spec (sha256 : ByteArray → Bytes32) (data : ByteArray) :
    BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 data =
      Spec.MerkleProtocol.merkleLeafHash sha256 data := rfl

theorem merkleNodeHash_eq_spec (sha256 : ByteArray → Bytes32) (l r : Bytes32) :
    BitcoinLedger.MerkleProtocol.merkleNodeHash sha256 l r =
      Spec.MerkleProtocol.merkleNodeHash sha256 l r := rfl

theorem largestPow2LtLoop_eq_spec (n fuel acc : Nat) :
    BitcoinLedger.MerkleProtocol.largestPow2LtLoop n fuel acc =
      Spec.MerkleProtocol.largestPow2LtGo n fuel acc := by
  induction fuel generalizing acc with
  | zero => rfl
  | succ f ih =>
      unfold BitcoinLedger.MerkleProtocol.largestPow2LtLoop Spec.MerkleProtocol.largestPow2LtGo
      cases Nat.decLt (acc * 2) n with
      | isFalse h =>
          simp only [h, ↓reduceIte]
      | isTrue h =>
          simp only [h, ↓reduceIte]
          exact ih (acc * 2)

theorem largestPow2Lt_eq_spec (n : Nat) :
    BitcoinLedger.MerkleProtocol.largestPow2Lt n = Spec.MerkleProtocol.largestPow2Lt n :=
  largestPow2LtLoop_eq_spec n n 1

/-! ## 2. Tail-Recursive Merkle Audit Engine, Root & Audit Path Refinement -/

theorem computeDirectionsAcc_eq_spec_reverse
    (fuel size index : Nat)
    (acc : List MerkleDir)
    (hFuel : size ≤ fuel) :
    BitcoinLedger.MerkleProtocol.computeDirectionsAcc fuel size index acc =
      (Spec.MerkleProtocol.merkleDirections size index).reverse ++ acc := by
  induction fuel generalizing size index acc with
  | zero =>
      have hSz0 : size = 0 := Nat.eq_zero_of_le_zero hFuel
      subst hSz0
      unfold BitcoinLedger.MerkleProtocol.computeDirectionsAcc
      conv => rhs; arg 1; arg 1; rw [Spec.MerkleProtocol.merkleDirections]
      have hNot : ¬(2 ≤ 0 ∧ index < 0) := fun h => absurd h.1 (by decide)
      rw [dite_false_constructive hNot]
      rfl
  | succ f ih =>
      unfold BitcoinLedger.MerkleProtocol.computeDirectionsAcc
      by_cases hGe2 : 2 ≤ size
      · by_cases hLtSz : index < size
        · have hCond : 2 ≤ size ∧ index < size := ⟨hGe2, hLtSz⟩
          have hDecBoth : (decide (2 ≤ size) && decide (index < size)) = true := by
            rw [decide_eq_true hGe2, decide_eq_true hLtSz]; rfl
          rw [hDecBoth]
          simp only [↓reduceIte, largestPow2Lt_eq_spec]
          have hk := Spec.MerkleProtocol.largestPow2Lt_bounds hGe2
          conv => rhs; arg 1; arg 1; rw [Spec.MerkleProtocol.merkleDirections]
          rw [dite_true_constructive hCond]
          dsimp only
          by_cases hIdxLtK : index < Spec.MerkleProtocol.largestPow2Lt size
          · simp only [hIdxLtK, ↓reduceIte, List.reverse_cons, List.append_assoc, List.singleton_append]
            have hkLeF : Spec.MerkleProtocol.largestPow2Lt size ≤ f :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hk.2 hFuel)
            exact ih _ index (.left :: acc) hkLeF
          · simp only [hIdxLtK, ↓reduceIte, List.reverse_cons, List.append_assoc, List.singleton_append]
            have hSubLtSz : size - Spec.MerkleProtocol.largestPow2Lt size < size :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hGe2) hk.1
            have hSubLeF : size - Spec.MerkleProtocol.largestPow2Lt size ≤ f :=
              Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hSubLtSz hFuel)
            exact ih _ (index - Spec.MerkleProtocol.largestPow2Lt size) (.right :: acc) hSubLeF
        · have hNotCond : ¬(2 ≤ size ∧ index < size) := fun h => hLtSz h.2
          have hDecFalse : (decide (2 ≤ size) && decide (index < size)) = false := by
            rw [decide_eq_false hLtSz, Bool.and_false]
          rw [hDecFalse]
          simp only [Bool.false_eq_true, ↓reduceIte]
          conv => rhs; arg 1; arg 1; rw [Spec.MerkleProtocol.merkleDirections]
          rw [dite_false_constructive hNotCond]
          rfl
      · have hNotCond : ¬(2 ≤ size ∧ index < size) := fun h => hGe2 h.1
        have hDecFalse : (decide (2 ≤ size) && decide (index < size)) = false := by
          rw [decide_eq_false hGe2, Bool.false_and]
        rw [hDecFalse]
        simp only [Bool.false_eq_true, ↓reduceIte]
        conv => rhs; arg 1; arg 1; rw [Spec.MerkleProtocol.merkleDirections]
        rw [dite_false_constructive hNotCond]
        rfl

theorem merkleDirectionsBottomUp_eq_spec_reverse (size index : Nat) :
    BitcoinLedger.MerkleProtocol.merkleDirectionsBottomUp size index =
      (Spec.MerkleProtocol.merkleDirections size index).reverse := by
  unfold BitcoinLedger.MerkleProtocol.merkleDirectionsBottomUp
  rw [computeDirectionsAcc_eq_spec_reverse size size index [] (Nat.le_refl _), List.append_nil]

theorem merkleDirections_eq_spec (size index : Nat) :
    BitcoinLedger.MerkleProtocol.merkleDirections size index =
      Spec.MerkleProtocol.merkleDirections size index := by
  unfold BitcoinLedger.MerkleProtocol.merkleDirections
  rw [merkleDirectionsBottomUp_eq_spec_reverse, List.reverse_reverse]

theorem foldMerkleProofBottomUp_eq_spec
    (sha256 : ByteArray → Bytes32)
    (curHash : Bytes32)
    (dirs : List MerkleDir)
    (sibs : List Bytes32) :
    BitcoinLedger.MerkleProtocol.foldMerkleProofBottomUp sha256 curHash dirs sibs =
      Spec.MerkleProtocol.foldMerkleProofBottomUp sha256 curHash dirs sibs := by
  induction dirs generalizing curHash sibs with
  | nil => cases sibs <;> rfl
  | cons d ds ih =>
      cases sibs with
      | nil => cases d <;> rfl
      | cons s ss =>
          cases d <;> exact ih _ ss

theorem verifyMerkleLeafHashProof_eq_spec
    (sha256 : ByteArray → Bytes32)
    (expectedRoot : Bytes32)
    (treeSize leafIndex : Nat)
    (leafHash : Bytes32)
    (siblingsBottomUp : List Bytes32) :
    BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof
      sha256 expectedRoot treeSize leafIndex leafHash siblingsBottomUp =
    Spec.MerkleProtocol.verifyMerkleLeafHashProof
      sha256 expectedRoot treeSize leafIndex leafHash siblingsBottomUp := by
  unfold BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof
         Spec.MerkleProtocol.verifyMerkleLeafHashProof
  simp only [constants_eq_spec, merkleDirectionsBottomUp_eq_spec_reverse,
             foldMerkleProofBottomUp_eq_spec]
  split
  · rfl
  · cases Spec.MerkleProtocol.foldMerkleProofBottomUp sha256 leafHash
        (Spec.MerkleProtocol.merkleDirections treeSize leafIndex).reverse siblingsBottomUp with
    | none => rfl
    | some r => exact eqBytes32_eq_spec r expectedRoot

theorem verifyRawPreimage_eq_spec
    (sha256 : ByteArray → Bytes32)
    (expectedHash : Bytes32)
    (rawPreimage : ByteArray) :
    BitcoinLedger.MerkleProtocol.verifyRawPreimage sha256 expectedHash rawPreimage =
      Spec.MerkleProtocol.verifyRawPreimage sha256 expectedHash rawPreimage := by
  unfold BitcoinLedger.MerkleProtocol.verifyRawPreimage Spec.MerkleProtocol.verifyRawPreimage
  rw [eqBytes32_eq_spec]
  rfl

theorem verifyMerkleLeafPreimage_eq_spec
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (rawPreimageWithPrefix : ByteArray) :
    BitcoinLedger.MerkleProtocol.verifyMerkleLeafPreimage sha256 expectedLeafHash rawPreimageWithPrefix =
      Spec.MerkleProtocol.verifyMerkleLeafPreimage sha256 expectedLeafHash rawPreimageWithPrefix := by
  unfold BitcoinLedger.MerkleProtocol.verifyMerkleLeafPreimage
         Spec.MerkleProtocol.verifyMerkleLeafPreimage
  rw [eqBytes32_eq_spec]
  rfl

theorem verifyMerkleElementOpening_eq_spec
    (sha256 : ByteArray → Bytes32)
    (expectedRoot : Bytes32)
    (treeSize leafIndex : Nat)
    (opening : MerkleElementOpening) :
    BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening sha256 expectedRoot treeSize leafIndex opening =
      Spec.MerkleProtocol.verifyMerkleElementOpening sha256 expectedRoot treeSize leafIndex opening := by
  unfold BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening
         Spec.MerkleProtocol.verifyMerkleElementOpening
  rw [verifyMerkleLeafHashProof_eq_spec, eqBytes32_eq_spec]
  rfl

theorem merkleRootFuel_eq_spec
    (sha256 : ByteArray → Bytes32)
    (fuel : Nat)
    (leaves : List ByteArray)
    (hFuel : leaves.length < fuel) :
    BitcoinLedger.MerkleProtocol.merkleRootFuel sha256 fuel leaves =
      Spec.MerkleProtocol.merkleRoot sha256 leaves := by
  induction fuel generalizing leaves with
  | zero => exact absurd hFuel (Nat.not_lt_zero _)
  | succ f ih =>
      match leaves with
      | [] =>
          unfold BitcoinLedger.MerkleProtocol.merkleRootFuel
          rw [Spec.MerkleProtocol.merkleRoot]
      | [x] =>
          unfold BitcoinLedger.MerkleProtocol.merkleRootFuel
          rw [Spec.MerkleProtocol.merkleRoot]
          rfl
      | x :: y :: rest =>
          let all := x :: y :: rest
          have hGe2 : 2 ≤ all.length :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
          have hk := Spec.MerkleProtocol.largestPow2Lt_bounds hGe2
          let k := Spec.MerkleProtocol.largestPow2Lt all.length
          have hAllLeF : all.length ≤ f := Nat.le_of_lt_succ hFuel
          have hTakeLtF : (all.take k).length < f := by
            rw [List.length_take]
            exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.lt_of_lt_of_le hk.2 hAllLeF)
          have hDropLtF : (all.drop k).length < f := by
            rw [List.length_drop]
            have hSubLt : all.length - k < all.length :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hGe2) hk.1
            exact Nat.lt_of_lt_of_le hSubLt hAllLeF
          unfold BitcoinLedger.MerkleProtocol.merkleRootFuel
          simp only [largestPow2Lt_eq_spec, merkleNodeHash_eq_spec]
          rw [ih (all.take k) hTakeLtF, ih (all.drop k) hDropLtF]
          conv => rhs; rw [Spec.MerkleProtocol.merkleRoot]

theorem merkleRoot_eq_spec (sha256 : ByteArray → Bytes32) (leaves : List ByteArray) :
    BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves =
      Spec.MerkleProtocol.merkleRoot sha256 leaves :=
  merkleRootFuel_eq_spec sha256 (leaves.length + 1) leaves (Nat.lt_succ_self _)

theorem buildMerkleAuditPathFuel_eq_spec
    (sha256 : ByteArray → Bytes32)
    (fuel : Nat)
    (leaves : List ByteArray)
    (index : Nat)
    (hFuel : leaves.length < fuel) :
    BitcoinLedger.MerkleProtocol.buildMerkleAuditPathFuel sha256 fuel leaves index =
      Spec.MerkleProtocol.buildMerkleAuditPath sha256 leaves index := by
  induction fuel generalizing leaves index with
  | zero => exact absurd hFuel (Nat.not_lt_zero _)
  | succ f ih =>
      match leaves with
      | [] =>
          unfold BitcoinLedger.MerkleProtocol.buildMerkleAuditPathFuel
          rw [Spec.MerkleProtocol.buildMerkleAuditPath]
      | [x] =>
          unfold BitcoinLedger.MerkleProtocol.buildMerkleAuditPathFuel
          rw [Spec.MerkleProtocol.buildMerkleAuditPath]
      | x :: y :: rest =>
          let all := x :: y :: rest
          have hGe2 : 2 ≤ all.length :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
          have hk := Spec.MerkleProtocol.largestPow2Lt_bounds hGe2
          let k := Spec.MerkleProtocol.largestPow2Lt all.length
          have hAllLeF : all.length ≤ f := Nat.le_of_lt_succ hFuel
          have hTakeLtF : (all.take k).length < f := by
            rw [List.length_take]
            exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.lt_of_lt_of_le hk.2 hAllLeF)
          have hDropLtF : (all.drop k).length < f := by
            rw [List.length_drop]
            have hSubLt : all.length - k < all.length :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hGe2) hk.1
            exact Nat.lt_of_lt_of_le hSubLt hAllLeF
          unfold BitcoinLedger.MerkleProtocol.buildMerkleAuditPathFuel
          simp only [largestPow2Lt_eq_spec, merkleRoot_eq_spec]
          conv => rhs; rw [Spec.MerkleProtocol.buildMerkleAuditPath]
          by_cases hLt : index < Spec.MerkleProtocol.largestPow2Lt (x :: y :: rest).length
          · simp only [hLt, ↓reduceIte]
            rw [ih (all.take k) index hTakeLtF]
          · simp only [hLt, ↓reduceIte]
            rw [ih (all.drop k) (index - k) hDropLtF]

theorem buildMerkleAuditPath_eq_spec
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (index : Nat) :
    BitcoinLedger.MerkleProtocol.buildMerkleAuditPath sha256 leaves index =
      Spec.MerkleProtocol.buildMerkleAuditPath sha256 leaves index :=
  buildMerkleAuditPathFuel_eq_spec sha256 (leaves.length + 1) leaves index (Nat.lt_succ_self _)

/-! ## 3. Strict Lexicographic Key Sorting & Single-Pass Sorted Map Verification Refinement -/

theorem listUInt8Lt_eq_spec (xs ys : List UInt8) :
    BitcoinLedger.MerkleProtocol.listUInt8Lt xs ys = Spec.MerkleProtocol.listUInt8Lt xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih =>
      cases ys with
      | nil => rfl
      | cons b bs =>
          unfold BitcoinLedger.MerkleProtocol.listUInt8Lt Spec.MerkleProtocol.listUInt8Lt
          by_cases hab : a.toNat < b.toNat
          · simp only [hab, ↓reduceIte]
          · simp only [hab, ↓reduceIte]
            by_cases hba : b.toNat < a.toNat
            · simp only [hba, ↓reduceIte]
            · simp only [hba, ↓reduceIte]
              exact ih bs

theorem byteArrayLt_eq_spec (a b : ByteArray) :
    BitcoinLedger.MerkleProtocol.byteArrayLt a b = Spec.MerkleProtocol.byteArrayLt a b :=
  listUInt8Lt_eq_spec a.data.toList b.data.toList

theorem isStrictlySortedFrom_eq_spec (prev : ByteArray) (rest : List ByteArray) :
    BitcoinLedger.MerkleProtocol.isStrictlySortedFrom prev rest =
      Spec.MerkleProtocol.isStrictlySorted (prev :: rest) := by
  induction rest generalizing prev with
  | nil => rfl
  | cons cur tail ih =>
      unfold BitcoinLedger.MerkleProtocol.isStrictlySortedFrom Spec.MerkleProtocol.isStrictlySorted
      rw [byteArrayLt_eq_spec, ih cur]
      cases Spec.MerkleProtocol.byteArrayLt prev cur <;> rfl

theorem isStrictlySorted_eq_spec (keys : List ByteArray) :
    BitcoinLedger.MerkleProtocol.isStrictlySorted keys =
      Spec.MerkleProtocol.isStrictlySorted keys := by
  cases keys with
  | nil => rfl
  | cons first rest =>
      unfold BitcoinLedger.MerkleProtocol.isStrictlySorted
      exact isStrictlySortedFrom_eq_spec first rest

private def rangeFrom (start : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => start :: rangeFrom (start + 1) n

private theorem rangeFrom_snoc (start m : Nat) :
    rangeFrom start m ++ [start + m] = rangeFrom start (m + 1) := by
  induction m generalizing start with
  | zero =>
      unfold rangeFrom
      rw [Nat.add_zero]
      rfl
  | succ m ih =>
      unfold rangeFrom
      have hAdd : start + (m + 1) = (start + 1) + m := by
        rw [← Nat.add_assoc, Nat.add_right_comm, Nat.add_assoc]
      rw [List.cons_append, hAdd, ih (start + 1)]

private theorem list_range_loop_eq_rangeFrom (k : Nat) (acc : List Nat) :
    List.range.loop k acc = rangeFrom 0 k ++ acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
      unfold List.range.loop
      rw [ih (k :: acc)]
      have hSnoc : rangeFrom 0 k ++ [k] = rangeFrom 0 (k + 1) := by
        have h := rangeFrom_snoc 0 k
        rw [Nat.zero_add] at h
        exact h
      rw [← hSnoc, List.append_assoc, List.singleton_append]

private theorem list_range_eq_rangeFrom (n : Nat) :
    List.range n = rangeFrom 0 n := by
  unfold List.range
  rw [list_range_loop_eq_rangeFrom, List.append_nil]

private theorem verifySortedKeyOpeningsLoop_invariant
    (sha256 : ByteArray → Bytes32)
    (keysRoot : Bytes32)
    (curIdx : Nat)
    (prevKey? : Option ByteArray)
    (ops : List MerkleElementOpening) :
    BitcoinLedger.MerkleProtocol.verifySortedKeyOpeningsLoop
      sha256 keysRoot (curIdx + ops.length) curIdx prevKey? ops =
    (((rangeFrom curIdx ops.length).zip ops).all (fun (i, op) =>
        decide (op.element.size ≤ Spec.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE) &&
        Spec.MerkleProtocol.verifyMerkleElementOpening sha256 keysRoot (curIdx + ops.length) i op) &&
      match prevKey? with
      | none => Spec.MerkleProtocol.isStrictlySorted (ops.map (·.element))
      | some prev => Spec.MerkleProtocol.isStrictlySorted (prev :: ops.map (·.element))) := by
  induction ops generalizing curIdx prevKey? with
  | nil =>
      unfold BitcoinLedger.MerkleProtocol.verifySortedKeyOpeningsLoop rangeFrom
      simp only [List.length_nil, Nat.add_zero, decide_true, List.zip_nil_left, List.all_nil,
                 Bool.true_and, List.map_nil]
      cases prevKey? <;> rfl
  | cons op rest ih =>
      have hSumEq : curIdx + (rest.length + 1) = (curIdx + 1) + rest.length := by
        rw [← Nat.add_assoc, Nat.add_right_comm]
      simp only [List.length_cons, List.map_cons]
      unfold BitcoinLedger.MerkleProtocol.verifySortedKeyOpeningsLoop rangeFrom
      simp only [constants_eq_spec, verifyMerkleElementOpening_eq_spec, List.zip_cons_cons,
                 List.all_cons]
      rw [hSumEq, ih (curIdx + 1) (some op.element)]
      cases prevKey? with
      | none =>
          simp only
          cases decide (op.element.size ≤ Spec.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE) <;>
          cases Spec.MerkleProtocol.verifyMerkleElementOpening sha256 keysRoot (curIdx + 1 + rest.length) curIdx op <;>
          rfl
      | some prev =>
          simp only [byteArrayLt_eq_spec]
          have hSortDef :
              Spec.MerkleProtocol.isStrictlySorted (prev :: op.element :: rest.map (·.element)) =
              (Spec.MerkleProtocol.byteArrayLt prev op.element &&
               Spec.MerkleProtocol.isStrictlySorted (op.element :: rest.map (·.element))) := rfl
          rw [hSortDef]
          cases decide (op.element.size ≤ Spec.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE) <;>
          cases Spec.MerkleProtocol.verifyMerkleElementOpening sha256 keysRoot (curIdx + 1 + rest.length) curIdx op <;>
          cases Spec.MerkleProtocol.byteArrayLt prev op.element <;>
          cases (((rangeFrom (curIdx + 1) rest.length).zip rest).all fun x =>
            decide (x.2.element.size ≤ Spec.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE) &&
            Spec.MerkleProtocol.verifyMerkleElementOpening sha256 keysRoot (curIdx + 1 + rest.length) x.1 x.2) <;>
          cases Spec.MerkleProtocol.isStrictlySorted (op.element :: rest.map (·.element)) <;>
          rfl

theorem verifySortedMerkleMapOpenings_eq_spec
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening) :
    BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings =
      Spec.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings := by
  unfold BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings
         Spec.MerkleProtocol.verifySortedMerkleMapOpenings
  simp only [eqBytes32_eq_spec]
  by_cases hLen : keyOpenings.length = map.size
  · rw [decide_eq_true hLen, ← hLen]
    have hInv := verifySortedKeyOpeningsLoop_invariant sha256 map.keysRoot 0 none keyOpenings
    rw [Nat.zero_add] at hInv
    rw [hInv, list_range_eq_rangeFrom]
    cases (if decide (keyOpenings.length = 0) then
        Spec.MerkleProtocol.bytes32Eq map.keysRoot zeroBytes32 &&
        Spec.MerkleProtocol.bytes32Eq map.valuesRoot zeroBytes32
      else true) <;>
    cases (((rangeFrom 0 keyOpenings.length).zip keyOpenings).all fun x =>
      decide (x.2.element.size ≤ Spec.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE) &&
      Spec.MerkleProtocol.verifyMerkleElementOpening sha256 map.keysRoot keyOpenings.length x.1 x.2) <;>
    cases Spec.MerkleProtocol.isStrictlySorted (keyOpenings.map (·.element)) <;>
    rfl
  · rw [decide_eq_false hLen]
    simp only [Bool.and_false, Bool.false_and]

theorem verifyMerkleMapLookup_eq_spec
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (proof : MapLookupProof) :
    BitcoinLedger.MerkleProtocol.verifyMerkleMapLookup sha256 map key proof =
      Spec.MerkleProtocol.verifyMapLookupProof sha256 map key proof := by
  unfold BitcoinLedger.MerkleProtocol.verifyMerkleMapLookup
         Spec.MerkleProtocol.verifyMapLookupProof
  dsimp only
  rw [merkleLeafHash_eq_spec, verifyMerkleLeafHashProof_eq_spec, verifyMerkleElementOpening_eq_spec]

theorem deviceFetchLeafElement_eq_spec
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (root : Bytes32)
    (treeSize leafIndex : Nat) :
    BitcoinLedger.MerkleProtocol.deviceFetchLeafElement sha256 host root treeSize leafIndex =
      Spec.MerkleProtocol.deviceFetchLeafElement sha256 host root treeSize leafIndex := by
  unfold BitcoinLedger.MerkleProtocol.deviceFetchLeafElement
         Spec.MerkleProtocol.deviceFetchLeafElement
  cases host.queryLeafProof root treeSize leafIndex with
  | none => rfl
  | some p =>
      rcases p with ⟨lh, sibs⟩
      simp only [verifyMerkleLeafHashProof_eq_spec, verifyMerkleLeafPreimage_eq_spec]
      rfl

theorem deviceLookupMerkleMapValue_eq_spec
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray) :
    BitcoinLedger.MerkleProtocol.deviceLookupMerkleMapValue sha256 host map key =
      Spec.MerkleProtocol.deviceLookupMerkleMapValue sha256 host map key := by
  unfold BitcoinLedger.MerkleProtocol.deviceLookupMerkleMapValue
         Spec.MerkleProtocol.deviceLookupMerkleMapValue
  dsimp only
  simp only [constants_eq_spec, merkleLeafHash_eq_spec, eqBytes32_eq_spec,
             verifyMerkleLeafHashProof_eq_spec, deviceFetchLeafElement_eq_spec]
  rfl

theorem serializeMerkleMapCommitment_eq_spec (m : MerkleMapCommitment) :
    BitcoinLedger.MerkleProtocol.serializeMerkleMapCommitment m =
      Spec.MerkleProtocol.serializeMerkleMapCommitment m := rfl

theorem commitMerkleMap_eq_spec
    (sha256 : ByteArray → Bytes32)
    (entries : List (ByteArray × ByteArray)) :
    BitcoinLedger.MerkleProtocol.commitMerkleMap sha256 entries =
      Spec.MerkleProtocol.commitMerkleMap sha256 entries := by
  unfold BitcoinLedger.MerkleProtocol.commitMerkleMap Spec.MerkleProtocol.commitMerkleMap
  simp only [merkleRoot_eq_spec]

/-! ## 4. Stateful Streaming Preimage Accumulator Refinement & Completeness -/

theorem validateContinuationApdu_eq_spec (hdr : ContinuationApdu) :
    BitcoinLedger.MerkleProtocol.validateContinuationApdu hdr =
      Spec.MerkleProtocol.validateContinuationApdu hdr := rfl

theorem feedPreimageChunks_finalize_eq_fold
    (sha256 : ByteArray → Bytes32)
    (st : BitcoinLedger.MerkleProtocol.PreimageStreamState)
    (chunks : List MoreElementsChunk) :
    (do
      let stF ← BitcoinLedger.MerkleProtocol.feedPreimageChunks st chunks
      BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream sha256 stF) =
    (match Spec.MerkleProtocol.foldPreimageChunks st.bytesRemaining st.buffer chunks with
     | .error e => .error e
     | .ok assembled =>
         if !Spec.MerkleProtocol.bytes32Eq (sha256 assembled) st.expectedHash then
           .error .digestMismatch
         else
           .ok assembled) := by
  induction chunks generalizing st with
  | nil =>
      unfold BitcoinLedger.MerkleProtocol.feedPreimageChunks
             BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream
             Spec.MerkleProtocol.foldPreimageChunks
      simp only [Bind.bind, Except.bind, eqBytes32_eq_spec]
      cases decide (st.bytesRemaining = 0) <;> rfl
  | cons c rest ih =>
      unfold BitcoinLedger.MerkleProtocol.feedPreimageChunks
             BitcoinLedger.MerkleProtocol.feedPreimageChunk
             Spec.MerkleProtocol.foldPreimageChunks
      simp only [validateContinuationApdu_eq_spec, constants_eq_spec]
      cases Spec.MerkleProtocol.validateContinuationApdu c.continuation
      · rfl
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decide (c.elementSize ≠ 1)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases (decide (c.nElements = 0) || decide (c.nElements > Spec.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases decide (c.chunkData.size ≠ c.nElements)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases decide (c.nElements > st.bytesRemaining)
              · simp only [Bool.false_eq_true, ↓reduceIte]
                exact ih {
                  expectedHash := st.expectedHash
                  declaredTotalSize := st.declaredTotalSize
                  bytesRemaining := st.bytesRemaining - c.nElements
                  buffer := st.buffer ++ c.chunkData
                }
              · rfl
            · rfl
          · rfl
        · rfl

theorem streamVerifyRawPreimage_eq_spec
    (sha256 : ByteArray → Bytes32)
    (expectedHash : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk) :
    BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage sha256 expectedHash init chunks =
      Spec.MerkleProtocol.streamVerifyRawPreimage sha256 expectedHash init chunks := by
  unfold BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage
         BitcoinLedger.MerkleProtocol.initPreimageStream
         Spec.MerkleProtocol.streamVerifyRawPreimage
  simp only [Bind.bind, Except.bind, validateContinuationApdu_eq_spec, constants_eq_spec]
  cases Spec.MerkleProtocol.validateContinuationApdu init.continuation
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases (decide (init.declaredTotalSize = 0) ||
           decide (init.declaredTotalSize > Spec.MerkleProtocol.MAX_PREIMAGE_TOTAL_SIZE))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases (decide (init.partialData.size > Spec.MerkleProtocol.MAX_PREIMAGE_PARTIAL_SIZE) ||
             decide (init.partialData.size > init.declaredTotalSize))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact feedPreimageChunks_finalize_eq_fold sha256 {
          expectedHash := expectedHash
          declaredTotalSize := init.declaredTotalSize
          bytesRemaining := init.declaredTotalSize - init.partialData.size
          buffer := init.partialData
        } chunks
      · rfl
    · rfl

theorem streamVerifyMerkleLeafPreimage_eq_spec
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk) :
    BitcoinLedger.MerkleProtocol.streamVerifyMerkleLeafPreimage sha256 expectedLeafHash init chunks =
      Spec.MerkleProtocol.streamVerifyMerkleLeafPreimage sha256 expectedLeafHash init chunks := by
  have hAssoc :
      BitcoinLedger.MerkleProtocol.streamVerifyMerkleLeafPreimage sha256 expectedLeafHash init chunks =
      (match BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage sha256 expectedLeafHash init chunks with
       | .error e => .error e
       | .ok assembled =>
           match assembled.data.toList with
           | 0x00 :: rest => .ok (ByteArray.mk rest.toArray)
           | _ => .error .missingMerkleLeafPrefix) := by
    unfold BitcoinLedger.MerkleProtocol.streamVerifyMerkleLeafPreimage
           BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage
    simp only [Bind.bind, Except.bind]
    cases BitcoinLedger.MerkleProtocol.initPreimageStream expectedLeafHash init with
    | error _ => rfl
    | ok st0 =>
        dsimp only
        cases BitcoinLedger.MerkleProtocol.feedPreimageChunks st0 chunks with
        | error _ => rfl
        | ok stF =>
            dsimp only
            unfold BitcoinLedger.MerkleProtocol.finalizeMerkleLeafPreimageStream
            cases BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream sha256 stF <;> rfl
  rw [hAssoc, streamVerifyRawPreimage_eq_spec]
  rfl

private theorem feedPreimageChunk_step_ok
    (st : BitcoinLedger.MerkleProtocol.PreimageStreamState)
    (c : MoreElementsChunk)
    (hHdr : BitcoinLedger.MerkleProtocol.validateContinuationApdu c.continuation = true)
    (hW : c.elementSize = 1)
    (hCnt : 1 ≤ c.nElements ∧ c.nElements ≤ BitcoinLedger.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT)
    (hSz : c.chunkData.size = c.nElements)
    (hLeRem : c.nElements ≤ st.bytesRemaining) :
    BitcoinLedger.MerkleProtocol.feedPreimageChunk st c =
    .ok {
      expectedHash := st.expectedHash
      declaredTotalSize := st.declaredTotalSize
      bytesRemaining := st.bytesRemaining - c.nElements
      buffer := st.buffer ++ c.chunkData
    } := by
  unfold BitcoinLedger.MerkleProtocol.feedPreimageChunk
  simp only [hHdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
             decide_eq_false (fun h : c.elementSize ≠ 1 => h hW),
             decide_eq_false (Nat.ne_of_gt hCnt.1),
             decide_eq_false (Nat.not_lt.mpr hCnt.2),
             decide_eq_false (fun h : c.chunkData.size ≠ c.nElements => h hSz),
             decide_eq_false (Nat.not_lt.mpr hLeRem), Bool.or_self]

/-- Multi-chunk streaming reconstruction: feeding two valid `CCMD_GET_MORE_ELEMENTS (0xA0)` chunks
    after `initPreimageStream` reconstructs `init.partialData ++ c1.chunkData ++ c2.chunkData`
    with `bytesRemaining = 0` when `init.partialData.size + c1.nElements + c2.nElements = init.declaredTotalSize`. -/
theorem feedPreimageChunks_two_chunks_reconstructs
    (expectedHash : Bytes32)
    (init : PreimageInitFrame)
    (c1 c2 : MoreElementsChunk)
    (hInitHdr : BitcoinLedger.MerkleProtocol.validateContinuationApdu init.continuation = true)
    (hDeclBounds : 1 ≤ init.declaredTotalSize ∧
                   init.declaredTotalSize ≤ BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_TOTAL_SIZE)
    (hPartBound : init.partialData.size ≤ BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_PARTIAL_SIZE)
    (hHdr1 : BitcoinLedger.MerkleProtocol.validateContinuationApdu c1.continuation = true)
    (hW1 : c1.elementSize = 1)
    (hCnt1 : 1 ≤ c1.nElements ∧ c1.nElements ≤ BitcoinLedger.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT)
    (hSz1 : c1.chunkData.size = c1.nElements)
    (hHdr2 : BitcoinLedger.MerkleProtocol.validateContinuationApdu c2.continuation = true)
    (hW2 : c2.elementSize = 1)
    (hCnt2 : 1 ≤ c2.nElements ∧ c2.nElements ≤ BitcoinLedger.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT)
    (hSz2 : c2.chunkData.size = c2.nElements)
    (hTotalEq : init.partialData.size + c1.nElements + c2.nElements = init.declaredTotalSize) :
    (do
      let st0 ← BitcoinLedger.MerkleProtocol.initPreimageStream expectedHash init
      BitcoinLedger.MerkleProtocol.feedPreimageChunks st0 [c1, c2]) =
    .ok {
      expectedHash := expectedHash
      declaredTotalSize := init.declaredTotalSize
      bytesRemaining := 0
      buffer := init.partialData ++ c1.chunkData ++ c2.chunkData
    } := by
  have hPartLeDecl : init.partialData.size ≤ init.declaredTotalSize := by
    rw [← hTotalEq]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hRem1 : init.declaredTotalSize - init.partialData.size = c1.nElements + c2.nElements := by
    have hEq : init.declaredTotalSize = (c1.nElements + c2.nElements) + init.partialData.size := by
      rw [← hTotalEq, Nat.add_assoc, Nat.add_comm init.partialData.size]
    rw [hEq, Nat.add_sub_cancel]
  have hRem2 : (c1.nElements + c2.nElements) - c1.nElements = c2.nElements := by
    rw [Nat.add_comm c1.nElements c2.nElements, Nat.add_sub_cancel]
  have hInitOk :
      BitcoinLedger.MerkleProtocol.initPreimageStream expectedHash init =
      .ok {
        expectedHash := expectedHash
        declaredTotalSize := init.declaredTotalSize
        bytesRemaining := c1.nElements + c2.nElements
        buffer := init.partialData
      } := by
    unfold BitcoinLedger.MerkleProtocol.initPreimageStream
    simp only [hInitHdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
               decide_eq_false (Nat.ne_of_gt hDeclBounds.1),
               decide_eq_false (Nat.not_lt.mpr hDeclBounds.2),
               decide_eq_false (Nat.not_lt.mpr hPartBound),
               decide_eq_false (Nat.not_lt.mpr hPartLeDecl),
               Bool.or_self, hRem1]
  rw [hInitOk]
  simp only [Bind.bind, Except.bind, BitcoinLedger.MerkleProtocol.feedPreimageChunks]
  rw [feedPreimageChunk_step_ok _ c1 hHdr1 hW1 hCnt1 hSz1 (Nat.le_add_right _ _)]
  simp only [hRem2]
  rw [feedPreimageChunk_step_ok _ c2 hHdr2 hW2 hCnt2 hSz2 (Nat.le_refl _)]
  simp only [Nat.sub_self]

/-- Streaming Raw Preimage Soundness on `BitcoinLedger.MerkleProtocol`. -/
theorem streamVerifyRawPreimage_sound
    {sha256 : ByteArray → Bytes32}
    {expected : Bytes32}
    {init : PreimageInitFrame}
    {chunks : List MoreElementsChunk}
    {out : ByteArray}
    (hOk : BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage sha256 expected init chunks = .ok out) :
    BitcoinLedger.MerkleProtocol.validateContinuationApdu init.continuation = true ∧
    1 ≤ init.declaredTotalSize ∧
    init.declaredTotalSize ≤ BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_TOTAL_SIZE ∧
    init.partialData.size ≤ BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_PARTIAL_SIZE ∧
    out.size = init.declaredTotalSize ∧
    sha256 out = expected ∧
    BitcoinLedger.MerkleProtocol.verifyRawPreimage sha256 expected out = some out := by
  rw [streamVerifyRawPreimage_eq_spec] at hOk
  rw [validateContinuationApdu_eq_spec, verifyRawPreimage_eq_spec]
  exact Spec.MerkleProtocol.streamVerifyRawPreimage_sound hOk

/-- Streaming Merkle Leaf Preimage Soundness on `BitcoinLedger.MerkleProtocol`. -/
theorem streamVerifyMerkleLeafPreimage_sound
    {sha256 : ByteArray → Bytes32}
    {expectedLeafHash : Bytes32}
    {init : PreimageInitFrame}
    {chunks : List MoreElementsChunk}
    {leafBytes : ByteArray}
    (hOk : BitcoinLedger.MerkleProtocol.streamVerifyMerkleLeafPreimage sha256 expectedLeafHash init chunks = .ok leafBytes) :
    BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 leafBytes = expectedLeafHash := by
  rw [streamVerifyMerkleLeafPreimage_eq_spec] at hOk
  exact Spec.MerkleProtocol.streamVerifyMerkleLeafPreimage_sound hOk

theorem stream_bad_continuation_rejected
    (sha256 : ByteArray → Bytes32)
    (expected : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk)
    (hBad : init.continuation.cla ≠ BitcoinLedger.MerkleProtocol.CLA_FRAMEWORK ∨
            init.continuation.ins ≠ BitcoinLedger.MerkleProtocol.INS_CONTINUE) :
    BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage sha256 expected init chunks =
      .error .badContinuationHeader := by
  rw [streamVerifyRawPreimage_eq_spec]
  exact Spec.MerkleProtocol.streamPreimage_rejects_bad_continuation sha256 expected init chunks hBad

theorem stream_oversized_partial_rejected
    (sha256 : ByteArray → Bytes32)
    (expected : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk)
    (hHdr : BitcoinLedger.MerkleProtocol.validateContinuationApdu init.continuation = true)
    (hDecl : 1 ≤ init.declaredTotalSize ∧
             init.declaredTotalSize ≤ BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_TOTAL_SIZE)
    (hOver : init.partialData.size > BitcoinLedger.MerkleProtocol.MAX_PREIMAGE_PARTIAL_SIZE) :
    BitcoinLedger.MerkleProtocol.streamVerifyRawPreimage sha256 expected init chunks =
      .error .invalidPartialSliceLength := by
  rw [streamVerifyRawPreimage_eq_spec]
  exact Spec.MerkleProtocol.streamPreimage_rejects_oversized_partial_slice sha256 expected init chunks hHdr hDecl hOver

theorem feedPreimageChunk_empty_or_oversized_rejected
    (st : BitcoinLedger.MerkleProtocol.PreimageStreamState)
    (c : MoreElementsChunk)
    (hHdr : BitcoinLedger.MerkleProtocol.validateContinuationApdu c.continuation = true)
    (hWidth : c.elementSize = 1)
    (hBadCnt : c.nElements = 0 ∨ c.nElements > BitcoinLedger.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT) :
    BitcoinLedger.MerkleProtocol.feedPreimageChunk st c = .error .invalidChunkElementCount := by
  unfold BitcoinLedger.MerkleProtocol.feedPreimageChunk
  have hNotNe1 : ¬(c.elementSize ≠ 1) := fun h => h hWidth
  simp only [hHdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_false hNotNe1]
  rcases hBadCnt with hZero | hGt
  · simp only [decide_eq_true hZero, Bool.true_or, ↓reduceIte]
  · simp only [decide_eq_true hGt, Bool.or_true, ↓reduceIte]

theorem feedPreimageChunk_overflow_rejected
    (st : BitcoinLedger.MerkleProtocol.PreimageStreamState)
    (c : MoreElementsChunk)
    (hHdr : BitcoinLedger.MerkleProtocol.validateContinuationApdu c.continuation = true)
    (hWidth : c.elementSize = 1)
    (hCnt : 1 ≤ c.nElements ∧ c.nElements ≤ BitcoinLedger.MerkleProtocol.MAX_MORE_ELEMENTS_COUNT)
    (hSz : c.chunkData.size = c.nElements)
    (hOver : c.nElements > st.bytesRemaining) :
    BitcoinLedger.MerkleProtocol.feedPreimageChunk st c = .error .streamOverflowBeyondDeclared := by
  unfold BitcoinLedger.MerkleProtocol.feedPreimageChunk
  simp only [hHdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
             decide_eq_false (fun h : c.elementSize ≠ 1 => h hWidth),
             decide_eq_false (Nat.ne_of_gt hCnt.1),
             decide_eq_false (Nat.not_lt.mpr hCnt.2),
             decide_eq_false (fun h : c.chunkData.size ≠ c.nElements => h hSz),
             Bool.or_self, decide_eq_true hOver]

theorem finalize_truncated_stream_rejected
    (sha256 : ByteArray → Bytes32)
    (st : BitcoinLedger.MerkleProtocol.PreimageStreamState)
    (hTrunc : st.bytesRemaining ≠ 0) :
    BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream sha256 st =
      .error .streamTruncatedBeforeDeclared := by
  unfold BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream
  simp only [decide_eq_false hTrunc, Bool.not_false, ↓reduceIte]

theorem finalize_digest_mismatch_rejected
    (sha256 : ByteArray → Bytes32)
    (st : BitcoinLedger.MerkleProtocol.PreimageStreamState)
    (hDone : st.bytesRemaining = 0)
    (hMismatch : sha256 st.buffer ≠ st.expectedHash) :
    BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream sha256 st = .error .digestMismatch := by
  unfold BitcoinLedger.MerkleProtocol.finalizeRawPreimageStream
  have hEqFalse : BitcoinLedger.MerkleProtocol.eqBytes32 (sha256 st.buffer) st.expectedHash = false := by
    rw [eqBytes32_eq_spec]
    cases hB : Spec.MerkleProtocol.bytes32Eq (sha256 st.buffer) st.expectedHash with
    | false => rfl
    | true => exact absurd ((Spec.MerkleProtocol.bytes32Eq_iff _ _).mp hB) hMismatch
  simp only [decide_eq_true hDone, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hEqFalse, Bool.not_false]

/-! ## 5. Audit Path Completeness, Key Sorting / Bounds Rejection & `CollisionFreeOn` Soundness -/

/-- Audit Path Folding Completeness on `BitcoinLedger.MerkleProtocol`:
    Every leaf `leaves[idx]? = some el` folds along `merkleDirectionsBottomUp` and `buildMerkleAuditPath`
    to `merkleRoot sha256 leaves`. -/
theorem audit_path_fold_complete
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (idx : Nat)
    (el : ByteArray)
    (hGet : leaves[idx]? = some el) :
    BitcoinLedger.MerkleProtocol.foldMerkleProofBottomUp
      sha256
      (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 el)
      (BitcoinLedger.MerkleProtocol.merkleDirectionsBottomUp leaves.length idx)
      (BitcoinLedger.MerkleProtocol.buildMerkleAuditPath sha256 leaves idx) =
    some (BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves) := by
  rw [foldMerkleProofBottomUp_eq_spec, merkleLeafHash_eq_spec,
      merkleDirectionsBottomUp_eq_spec_reverse, buildMerkleAuditPath_eq_spec, merkleRoot_eq_spec]
  exact Spec.MerkleProtocol.buildMerkleAuditPath_complete sha256 leaves idx el hGet

/-- Full Verifier Completeness: any honest leaf opening within BOLOS index & depth bounds is accepted
    by both `verifyMerkleLeafHashProof` and `verifyMerkleElementOpening`. -/
theorem audit_path_verify_complete
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (idx : Nat)
    (el : ByteArray)
    (hGet : leaves[idx]? = some el)
    (hIdxBound : idx ≤ BitcoinLedger.MerkleProtocol.MAX_MERKLE_LEAF_INDEX)
    (hDepthBound : (BitcoinLedger.MerkleProtocol.buildMerkleAuditPath sha256 leaves idx).length ≤
                   BitcoinLedger.MerkleProtocol.MAX_MERKLE_TREE_DEPTH) :
    BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening
      sha256
      (BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves)
      leaves.length
      idx
      { element := el
        leafHash := BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 el
        siblingsBottomUp := BitcoinLedger.MerkleProtocol.buildMerkleAuditPath sha256 leaves idx } = true := by
  have hIdxLt : idx < leaves.length := by
    cases Nat.lt_or_ge idx leaves.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  have hNe0 : ¬(leaves.length = 0) := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le idx) hIdxLt)
  have hNotGe : ¬(idx ≥ leaves.length) := Nat.not_le.mpr hIdxLt
  have hNotGtMax : ¬(idx > BitcoinLedger.MerkleProtocol.MAX_MERKLE_LEAF_INDEX) := Nat.not_lt.mpr hIdxBound
  have hNotGtDepth : ¬((BitcoinLedger.MerkleProtocol.buildMerkleAuditPath sha256 leaves idx).length >
                       BitcoinLedger.MerkleProtocol.MAX_MERKLE_TREE_DEPTH) := Nat.not_lt.mpr hDepthBound
  have hFold := audit_path_fold_complete sha256 leaves idx el hGet
  have hRefl : BitcoinLedger.MerkleProtocol.eqBytes32
      (BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves)
      (BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves) = true := by
    rw [eqBytes32_eq_spec]; exact Spec.MerkleProtocol.bytes32Eq_refl _
  have hLeafRefl : BitcoinLedger.MerkleProtocol.eqBytes32
      (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 el)
      (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 el) = true := by
    rw [eqBytes32_eq_spec]; exact Spec.MerkleProtocol.bytes32Eq_refl _
  unfold BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening
         BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof
  simp only [decide_eq_false hNe0, decide_eq_false hNotGe, decide_eq_false hNotGtMax,
             decide_eq_false hNotGtDepth, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
             hFold, hRefl, hLeafRefl, Bool.and_self]

/-- Duplicate Key Rejection: any `keyOpenings` with equal keys at distinct indices `i ≠ j` is rejected. -/
theorem duplicate_keys_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    {i j : Nat} {op1 op2 : MerkleElementOpening}
    (hNe : i ≠ j)
    (hi : keyOpenings[i]? = some op1)
    (hj : keyOpenings[j]? = some op2)
    (hSameKey : op1.element = op2.element) :
    BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  rw [verifySortedMerkleMapOpenings_eq_spec]
  exact Spec.MerkleProtocol.duplicate_keys_rejected sha256 map keyOpenings hNe hi hj hSameKey

/-- Unsorted Key Rejection: if `i < j` and `!(op1.element < op2.element)`, `verifySortedMerkleMapOpenings` rejects. -/
theorem unsorted_keys_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    {i j : Nat} {op1 op2 : MerkleElementOpening}
    (hij : i < j)
    (hi : keyOpenings[i]? = some op1)
    (hj : keyOpenings[j]? = some op2)
    (hNotLt : BitcoinLedger.MerkleProtocol.byteArrayLt op1.element op2.element = false) :
    BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  cases hV : BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings with
  | false => rfl
  | true =>
      exfalso
      rw [verifySortedMerkleMapOpenings_eq_spec] at hV
      unfold Spec.MerkleProtocol.verifySortedMerkleMapOpenings at hV
      simp only [Bool.and_eq_true] at hV
      have hStrict := hV.2
      have hMap1 : (keyOpenings.map (·.element))[i]? = some op1.element := by
        rw [List.getElem?_map, hi]; rfl
      have hMap2 : (keyOpenings.map (·.element))[j]? = some op2.element := by
        rw [List.getElem?_map, hj]; rfl
      have hLtSpec := Spec.MerkleProtocol.strictlySorted_index_lt hStrict hij hMap1 hMap2
      rw [← byteArrayLt_eq_spec, hNotLt] at hLtSpec
      contradiction

/-- Empty-Map Nonzero-Root Rejection on `BitcoinLedger.MerkleProtocol`. -/
theorem empty_map_nonzero_root_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    (hZeroSz : map.size = 0)
    (hNonZero : map.keysRoot ≠ zeroBytes32 ∨ map.valuesRoot ≠ zeroBytes32) :
    BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  rw [verifySortedMerkleMapOpenings_eq_spec]
  exact Spec.MerkleProtocol.empty_map_nonzero_root_rejected sha256 map keyOpenings hZeroSz hNonZero

/-- BOLOS Depth Overflow Rejection (`siblingsBottomUp.length > MAX_MERKLE_TREE_DEPTH = 32`). -/
theorem depth_overflow_rejected
    (sha256 : ByteArray → Bytes32)
    (root : Bytes32) (size idx : Nat) (lh : Bytes32) (sibs : List Bytes32)
    (hDepth : sibs.length > BitcoinLedger.MerkleProtocol.MAX_MERKLE_TREE_DEPTH) :
    BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof sha256 root size idx lh sibs = false := by
  rw [verifyMerkleLeafHashProof_eq_spec]
  exact Spec.MerkleProtocol.depth_gt_32_rejected sha256 root size idx lh sibs hDepth

/-- BOLOS Leaf Index Overflow Rejection in `verifyMerkleLeafHashProof` (`idx ≥ size` or `idx > 0x7FFFFFFF`). -/
theorem leaf_index_overflow_rejected_in_proof
    (sha256 : ByteArray → Bytes32)
    (root : Bytes32) (size idx : Nat) (lh : Bytes32) (sibs : List Bytes32)
    (hOob : idx ≥ size ∨ idx > BitcoinLedger.MerkleProtocol.MAX_MERKLE_LEAF_INDEX) :
    BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof sha256 root size idx lh sibs = false := by
  unfold BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof
  rcases hOob with hGe | hGt
  · simp only [decide_eq_true hGe, Bool.or_true, Bool.true_or, ↓reduceIte]
  · simp only [decide_eq_true hGt, Bool.or_true, Bool.true_or, ↓reduceIte]

/-- BOLOS Leaf Index Overflow Rejection in `deviceLookupMerkleMapValue` (`get_merkle_leaf_index.c:34`). -/
theorem leaf_index_overflow_rejected_in_lookup
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (found : Bool)
    (idx : Nat)
    (hHost : host.queryLeafIndex map.keysRoot (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 key) = some (found, idx))
    (hOob : idx ≥ map.size ∨ idx > BitcoinLedger.MerkleProtocol.MAX_MERKLE_LEAF_INDEX) :
    BitcoinLedger.MerkleProtocol.deviceLookupMerkleMapValue sha256 host map key = .protocolError := by
  rw [deviceLookupMerkleMapValue_eq_spec]
  exact Spec.MerkleProtocol.out_of_bounds_index_rejected sha256 host map key found idx hHost hOob

/-- BOLOS Sorted Map Key Size Overflow Rejection (`key.size > MAX_MERKLE_MAP_KEY_SIZE = 128`). -/
theorem map_key_size_overflow_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    {i : Nat} {op : MerkleElementOpening}
    (hi : keyOpenings[i]? = some op)
    (hOver : op.element.size > BitcoinLedger.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE) :
    BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  rw [verifySortedMerkleMapOpenings_eq_spec]
  exact Spec.MerkleProtocol.oversized_map_key_rejected sha256 map keyOpenings hi hOver

/-- BOLOS Key-Header Stack Buffer Overflow Rejection (`keyHeader.size > MAX_MAP_KEY_HEADER_LEN = 64`). -/
theorem map_key_header_overflow_rejected
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (keyHeader : ByteArray)
    (hOver : keyHeader.size > BitcoinLedger.MerkleProtocol.MAX_MAP_KEY_HEADER_LEN) :
    BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader sha256 host map keyHeader = .protocolError := by
  unfold BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader
         BitcoinLedger.MerkleProtocol.checkMapKeyHeaderBound
  have hNotLe : ¬(keyHeader.size ≤ BitcoinLedger.MerkleProtocol.MAX_MAP_KEY_HEADER_LEN) :=
    Nat.not_le.mpr hOver
  simp only [decide_eq_false hNotLe, Bool.not_false, ↓reduceIte]

/-! ### 5.2 Finite-Pool `CollisionFreeOn` Soundness & Anti-Equivocation on `BitcoinLedger.MerkleProtocol` -/

/-- Domain Separation (`0x00` vs `0x01`) on `BitcoinLedger.MerkleProtocol`:
    Under `CollisionFreeOn sha256 pool`, a leaf hash never collides with an internal node hash. -/
theorem leaf_hash_ne_node_hash_on
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {leaf : ByteArray} {l r : Bytes32}
    (hLeaf : BitcoinLedger.MerkleProtocol.leafPreimage leaf ∈ pool)
    (hNode : BitcoinLedger.MerkleProtocol.nodePreimage l r ∈ pool) :
    BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 leaf ≠
      BitcoinLedger.MerkleProtocol.merkleNodeHash sha256 l r :=
  Spec.MerkleProtocol.merkleLeafHash_ne_nodeHash_on hCF hLeaf hNode

/-- Leaf-Hash Proof Determinism (`CollisionFreeOn` Soundness at `(root, size, idx)`):
    Any two valid proofs accepted by `BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof`
    open the exact same `leafHash` and identical sibling paths. -/
theorem leaf_hash_proof_unique_on
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {root : Bytes32} {size idx : Nat}
    {lh1 lh2 : Bytes32} {sibs1 sibs2 : List Bytes32}
    (hSub1 : ∀ x, x ∈ Spec.MerkleProtocol.proofPreimages sha256 size idx lh1 sibs1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ Spec.MerkleProtocol.proofPreimages sha256 size idx lh2 sibs2 → x ∈ pool)
    (h1 : BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof sha256 root size idx lh1 sibs1 = true)
    (h2 : BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof sha256 root size idx lh2 sibs2 = true) :
    lh1 = lh2 ∧ sibs1 = sibs2 := by
  rw [verifyMerkleLeafHashProof_eq_spec] at h1 h2
  exact Spec.MerkleProtocol.verifyMerkleLeafHashProof_unique hCF hSub1 hSub2 h1 h2

/-- Element Preimage Binding (`CollisionFreeOn` Soundness at `(root, size, idx)`):
    Any two valid `MerkleElementOpening`s accepted by `BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening`
    open the exact same `ByteArray` element. -/
theorem element_opening_unique_on
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {root : Bytes32} {size idx : Nat}
    {op1 op2 : MerkleElementOpening}
    (hSub1 : ∀ x, x ∈ Spec.MerkleProtocol.openingPreimages sha256 size idx op1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ Spec.MerkleProtocol.openingPreimages sha256 size idx op2 → x ∈ pool)
    (h1 : BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening sha256 root size idx op1 = true)
    (h2 : BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening sha256 root size idx op2 = true) :
    op1.element = op2.element := by
  rw [verifyMerkleElementOpening_eq_spec] at h1 h2
  exact Spec.MerkleProtocol.verifyMerkleElementOpening_unique hCF hSub1 hSub2 h1 h2

/-- Tree-Relative Merkle Opening Soundness on `BitcoinLedger.MerkleProtocol`:
    Under `CollisionFreeOn sha256 pool`, any valid `verifyMerkleElementOpening` against
    `BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves` at `idx` guarantees `leaves[idx]? = some opening.element`. -/
theorem merkle_opening_sound_against_committed_tree
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    (leaves : List ByteArray)
    (idx : Nat)
    (opening : MerkleElementOpening)
    (hTreeSub : ∀ x, x ∈ Spec.MerkleProtocol.treePreimages sha256 leaves → x ∈ pool)
    (hOpenSub : ∀ x, x ∈ Spec.MerkleProtocol.openingPreimages sha256 leaves.length idx opening → x ∈ pool)
    (hValid : BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening
      sha256 (BitcoinLedger.MerkleProtocol.merkleRoot sha256 leaves) leaves.length idx opening = true) :
    leaves[idx]? = some opening.element := by
  rw [verifyMerkleElementOpening_eq_spec, merkleRoot_eq_spec] at hValid
  exact Spec.MerkleProtocol.merkleProof_sound_against_committed_tree
    hCF leaves idx opening hTreeSub hOpenSub hValid

/-- Sorted Merkle Map Key-Index Uniqueness on `BitcoinLedger.MerkleProtocol`:
    Under `CollisionFreeOn sha256 pool` and `verifySortedMerkleMapOpenings = true`, no key `k`
    can open at two distinct indices `i1 ≠ i2` in `map.keysRoot`. -/
theorem sorted_map_unique_key_index
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    {i1 i2 : Nat} {sibs1 sibs2 : List Bytes32}
    (hSortedSub : ∀ x, x ∈ Spec.MerkleProtocol.sortedMapOpeningsPreimages sha256 map.size keyOpenings → x ∈ pool)
    (hLeafKey : BitcoinLedger.MerkleProtocol.leafPreimage key ∈ pool)
    (hProofSub1 : ∀ x, x ∈ Spec.MerkleProtocol.proofPreimages sha256 map.size i1
      (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 key) sibs1 → x ∈ pool)
    (hProofSub2 : ∀ x, x ∈ Spec.MerkleProtocol.proofPreimages sha256 map.size i2
      (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 key) sibs2 → x ∈ pool)
    (hProof1 : BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof
      sha256 map.keysRoot map.size i1 (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 key) sibs1 = true)
    (hProof2 : BitcoinLedger.MerkleProtocol.verifyMerkleLeafHashProof
      sha256 map.keysRoot map.size i2 (BitcoinLedger.MerkleProtocol.merkleLeafHash sha256 key) sibs2 = true) :
    i1 = i2 := by
  rw [verifySortedMerkleMapOpenings_eq_spec] at hSortedMap
  rw [verifyMerkleLeafHashProof_eq_spec, merkleLeafHash_eq_spec] at hProof1 hProof2
  exact Spec.MerkleProtocol.sorted_merkle_map_unique_key_index
    hCF hSortedMap hSortedSub hLeafKey hProofSub1 hProofSub2 hProof1 hProof2

/-- Sorted Merkle Map Value Uniqueness (`verifyMerkleMapLookup` Anti-Equivocation):
    Under `CollisionFreeOn sha256 pool` and `verifySortedMerkleMapOpenings = true`, any two valid
    `verifyMerkleMapLookup` proofs for `key` must agree on both `index` and `valueOpening.element`. -/
theorem sorted_map_lookup_unique
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    {p1 p2 : MapLookupProof}
    (hSortedSub : ∀ x, x ∈ Spec.MerkleProtocol.sortedMapOpeningsPreimages sha256 map.size keyOpenings → x ∈ pool)
    (hSub1 : ∀ x, x ∈ Spec.MerkleProtocol.mapLookupProofPreimages sha256 map key p1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ Spec.MerkleProtocol.mapLookupProofPreimages sha256 map key p2 → x ∈ pool)
    (hLookup1 : BitcoinLedger.MerkleProtocol.verifyMerkleMapLookup sha256 map key p1 = true)
    (hLookup2 : BitcoinLedger.MerkleProtocol.verifyMerkleMapLookup sha256 map key p2 = true) :
    p1.index = p2.index ∧ p1.valueOpening.element = p2.valueOpening.element := by
  rw [verifySortedMerkleMapOpenings_eq_spec] at hSortedMap
  rw [verifyMerkleMapLookup_eq_spec] at hLookup1 hLookup2
  exact Spec.MerkleProtocol.sorted_merkle_map_lookup_proof_unique
    hCF hSortedMap hSortedSub hSub1 hSub2 hLookup1 hLookup2

/-- Interactive Untrusted-Host Oracle Lookup Anti-Equivocation on `BitcoinLedger.MerkleProtocol`:
    Even two distinct malicious/adaptive `UntrustedHostOracle`s `host1, host2` cannot equivocate on
    the value returned by `deviceLookupMerkleMapValue` (or `deviceLookupBoundedKeyHeader`) for `key`. -/
theorem interactive_host_cannot_equivocate
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    (host1 host2 : UntrustedHostOracle)
    (key v1 v2 : ByteArray)
    (hSortedSub : ∀ x, x ∈ Spec.MerkleProtocol.sortedMapOpeningsPreimages sha256 map.size keyOpenings → x ∈ pool)
    (hHostSub1 : ∀ x, x ∈ Spec.MerkleProtocol.hostLookupPreimages sha256 host1 map key → x ∈ pool)
    (hHostSub2 : ∀ x, x ∈ Spec.MerkleProtocol.hostLookupPreimages sha256 host2 map key → x ∈ pool)
    (hRes1 : BitcoinLedger.MerkleProtocol.deviceLookupMerkleMapValue sha256 host1 map key = .present v1)
    (hRes2 : BitcoinLedger.MerkleProtocol.deviceLookupMerkleMapValue sha256 host2 map key = .present v2) :
    v1 = v2 := by
  rw [verifySortedMerkleMapOpenings_eq_spec] at hSortedMap
  rw [deviceLookupMerkleMapValue_eq_spec] at hRes1 hRes2
  exact Spec.MerkleProtocol.interactive_host_cannot_equivocate_map_value
    hCF hSortedMap host1 host2 key v1 v2 hSortedSub hHostSub1 hHostSub2 hRes1 hRes2

/-- Key-Scan Omission Detection on `BitcoinLedger.MerkleProtocol`. -/
theorem verified_key_scan_detects_omission
    {sha256 : ByteArray → Bytes32}
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    (hSeenInScan : key ∈ keyOpenings.map (·.element)) :
    ∃ (idx : Nat) (op : MerkleElementOpening),
      idx < map.size ∧
      op.element = key ∧
      op.element.size ≤ BitcoinLedger.MerkleProtocol.MAX_MERKLE_MAP_KEY_SIZE ∧
      BitcoinLedger.MerkleProtocol.verifyMerkleElementOpening sha256 map.keysRoot map.size idx op = true := by
  rw [verifySortedMerkleMapOpenings_eq_spec] at hSortedMap
  obtain ⟨idx, op, hIdx, hEl, hSz, hOpen⟩ :=
    Spec.MerkleProtocol.verified_key_scan_detects_omission hSortedMap hSeenInScan
  rw [← verifyMerkleElementOpening_eq_spec] at hOpen
  exact ⟨idx, op, hIdx, hEl, hSz, hOpen⟩

/-- PSBT Merkle Bundle Soundness: accepting `verifyPsbtMerkleBundle` guarantees that `psbt.globalMap`
    has verified strictly sorted keys and exact input/output bundle counts (`nInputs`, `nOutputs`). -/
theorem verifyPsbtMerkleBundle_sound
    {sha256 : ByteArray → Bytes32}
    {psbt : MerkleizedPsbtCommitment}
    {globalKeys : List MerkleElementOpening}
    {inBundles outBundles : List (MerkleMapCommitment × MerkleElementOpening × List MerkleElementOpening)}
    (hOk : BitcoinLedger.MerkleProtocol.verifyPsbtMerkleBundle
      sha256 psbt globalKeys inBundles outBundles = true) :
    BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 psbt.globalMap globalKeys = true ∧
    inBundles.length = psbt.nInputs ∧
    outBundles.length = psbt.nOutputs := by
  unfold BitcoinLedger.MerkleProtocol.verifyPsbtMerkleBundle at hOk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hOk
  rcases hOk with ⟨⟨⟨⟨⟨⟨hGlob, _⟩, _⟩, hInLen⟩, hOutLen⟩, _⟩, _⟩
  exact ⟨hGlob, hInLen, hOutLen⟩

/-! ## 6. Concrete Non-Vacuous Execution Witnesses (`0 Classical.choice`, `0 native_decide`) -/

/-- End-to-End Executable Merkle Map & Bounded Key Lookup Non-Vacuity Witness:
    1. `CollisionFreeOn sha256 pool` holds constructively on a finite preimage pool,
    2. `BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings` accepts the 3-entry sorted PSBT map,
    3. `BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader` returns `.present #[0xBB, 0xCC]` for key `#[0x01]`, and
    4. `BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader` returns `.absentClaimed` for absent key `#[0x02]`. -/
theorem non_vacuity_executable_merkle_map_and_lookup :
    ∃ (sha256 : ByteArray → Bytes32)
      (pool : List ByteArray)
      (map : MerkleMapCommitment)
      (keyOpenings : List MerkleElementOpening)
      (host : UntrustedHostOracle),
      CollisionFreeOn sha256 pool ∧
      map.size = 3 ∧
      BitcoinLedger.MerkleProtocol.verifySortedMerkleMapOpenings sha256 map keyOpenings = true ∧
      BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader
        sha256 host map (ByteArray.mk #[0x01]) = .present (ByteArray.mk #[0xBB, 0xCC]) ∧
      BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader
        sha256 host map (ByteArray.mk #[0x02]) = .absentClaimed := by
  obtain ⟨sha256, pool, map, keyOpenings, host, hCF, hSz, hSorted, hPresent, hAbsent⟩ :=
    Spec.MerkleProtocol.non_vacuity_honest_merkle_map_verified_and_queried
  refine ⟨sha256, pool, map, keyOpenings, host, hCF, hSz, ?_, ?_, ?_⟩
  · rw [verifySortedMerkleMapOpenings_eq_spec]
    exact hSorted
  · unfold BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader
           BitcoinLedger.MerkleProtocol.checkMapKeyHeaderBound
    have hSz1 : decide ((ByteArray.mk #[0x01]).size ≤ BitcoinLedger.MerkleProtocol.MAX_MAP_KEY_HEADER_LEN) = true :=
      by decide
    rw [hSz1]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, deviceLookupMerkleMapValue_eq_spec]
    exact hPresent
  · unfold BitcoinLedger.MerkleProtocol.deviceLookupBoundedKeyHeader
           BitcoinLedger.MerkleProtocol.checkMapKeyHeaderBound
    have hSz2 : decide ((ByteArray.mk #[0x02]).size ≤ BitcoinLedger.MerkleProtocol.MAX_MAP_KEY_HEADER_LEN) = true :=
      by decide
    rw [hSz2]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, deviceLookupMerkleMapValue_eq_spec]
    exact hAbsent

/-- End-to-End Executable Lookup Uniqueness Witness on `toyLenPrefixHash` + `concretePool`:
    Any `MapLookupProof` `p` accepted by `BitcoinLedger.MerkleProtocol.verifyMerkleMapLookup`
    for key `#[0x01]` on `witnessMap` uniquely yields `p.index = 1` and `p.valueOpening.element = #[0xBB, 0xCC]`. -/
theorem non_vacuity_executable_lookup_uniqueness
    (p : MapLookupProof)
    (hSub : ∀ x, x ∈ Spec.MerkleProtocol.mapLookupProofPreimages
      Spec.MerkleProtocol.toyLenPrefixHash Spec.MerkleProtocol.witnessMap (ByteArray.mk #[0x01]) p →
      x ∈ Spec.MerkleProtocol.concretePool)
    (hValid : BitcoinLedger.MerkleProtocol.verifyMerkleMapLookup
      Spec.MerkleProtocol.toyLenPrefixHash Spec.MerkleProtocol.witnessMap (ByteArray.mk #[0x01]) p = true) :
    p.index = 1 ∧ p.valueOpening.element = ByteArray.mk #[0xBB, 0xCC] := by
  rw [verifyMerkleMapLookup_eq_spec] at hValid
  exact Spec.MerkleProtocol.non_vacuity_end_to_end_lookup_uniqueness p hSub hValid

/-- Concrete Multi-Chunk `0xE000` Preimage Streaming Execution Witness:
    Exercises `BitcoinLedger.MerkleProtocol.streamVerifyMerkleLeafPreimage` across an initial
    `CCMD_GET_PREIMAGE (0x40)` partial slice (`[0x00, 0xCA]`) followed by two `CCMD_GET_MORE_ELEMENTS (0xA0)`
    continuation chunks (`[0xFE]` and `[0xBA, 0xBE]`), reconstructing the stripped leaf `#[0xCA, 0xFE, 0xBA, 0xBE]`. -/
theorem non_vacuity_multi_chunk_preimage_stream :
    let cont : ContinuationApdu := {
      cla := BitcoinLedger.MerkleProtocol.CLA_FRAMEWORK
      ins := BitcoinLedger.MerkleProtocol.INS_CONTINUE
      p1 := 0
      p2 := 0
    }
    let leafPayload := ByteArray.mk #[0xCA, 0xFE, 0xBA, 0xBE]
    let expectedLeafHash :=
      BitcoinLedger.MerkleProtocol.merkleLeafHash Spec.MerkleProtocol.toyLenPrefixHash leafPayload
    let init : PreimageInitFrame := {
      continuation := cont
      declaredTotalSize := 5
      partialData := ByteArray.mk #[0x00, 0xCA]
    }
    let c1 : MoreElementsChunk := {
      continuation := cont
      nElements := 1
      elementSize := 1
      chunkData := ByteArray.mk #[0xFE]
    }
    let c2 : MoreElementsChunk := {
      continuation := cont
      nElements := 2
      elementSize := 1
      chunkData := ByteArray.mk #[0xBA, 0xBE]
    }
    BitcoinLedger.MerkleProtocol.streamVerifyMerkleLeafPreimage
      Spec.MerkleProtocol.toyLenPrefixHash expectedLeafHash init [c1, c2] = .ok leafPayload :=
  rfl

end Proofs.MerkleProtocol

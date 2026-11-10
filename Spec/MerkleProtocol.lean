/-
  Spec/MerkleProtocol.lean
  Canonical, implementation-independent formal specification for Ledger's BOLOS
  RFC-6962-style Merkle trees, Merkleized key-value map commitments, strict
  lexicographic key-sorting verification, interactive untrusted-host client
  commands (`YIELD`, `GET_PREIMAGE`, `GET_MERKLE_LEAF_PROOF`,
  `GET_MERKLE_LEAF_INDEX`, `GET_MORE_ELEMENTS`), and machine-checked
  collision-relative Merkleized map soundness (`0 sorryAx`).

  Deduced from:
  - LedgerHQ/app-bitcoin (`f010982d3050e02813cd7129bebd68cf2d1f2099`):
    `doc/merkle.md`, `src/common/merkle.{h,c}`, `src/handler/client_commands.h`,
    `src/handler/lib/check_merkle_tree_sorted.c`, `get_merkle_leaf_hash.c`,
    `get_merkle_preimage.c`, `get_merkle_leaf_index.c`, `get_merkleized_map.c`,
    `get_merkleized_map_value.c`.
-/

import Spec.Psbt

namespace Spec.MerkleProtocol

open Spec.Psbt

/-! ## 0. Pure Constructive Byte Equality & BOLOS Protocol Bounds -/

/-- Pure structural byte-list equality (`0 Classical.choice`, avoids `Std.PreorderPackage.toBEq`). -/
def byteListEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && byteListEq xs ys
  | _, _ => false

theorem byteListEq_refl (xs : List UInt8) : byteListEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      unfold byteListEq
      rw [decide_eq_true (rfl : x = x), Bool.true_and, ih]

theorem byteListEq_iff (xs ys : List UInt8) : byteListEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
      | cons _ _ =>
          unfold byteListEq
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | cons x xRest ih =>
      cases ys with
      | nil =>
          unfold byteListEq
          exact ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
      | cons y yRest =>
          unfold byteListEq
          simp only [Bool.and_eq_true, decide_eq_true_eq, ih]
          exact ⟨fun ⟨hxy, hRest⟩ => by rw [hxy, hRest], fun h => List.cons.inj h⟩

/-- Pure structural `ByteArray` equality backed by `byteListEq`. -/
def merkleBytesEq (a b : ByteArray) : Bool :=
  byteListEq a.data.toList b.data.toList

theorem merkleBytesEq_iff (a b : ByteArray) : merkleBytesEq a b = true ↔ a = b := by
  unfold merkleBytesEq
  rw [byteListEq_iff]
  constructor
  · intro h
    cases a with | mk da =>
    cases b with | mk db =>
    congr
    exact Array.ext' h
  · intro h
    subst h
    rfl

theorem merkleBytesEq_refl (a : ByteArray) : merkleBytesEq a a = true :=
  (merkleBytesEq_iff a a).mpr rfl

/-- Maximum Merkle audit path depth (`MAX_MERKLE_TREE_DEPTH = 32` in `src/common/merkle.h`). -/
def MAX_MERKLE_TREE_DEPTH : Nat := 32

/-- Maximum key length in sorted Merkleized maps (`MAX_MERKLE_MAP_KEY_SIZE = 128`). -/
def MAX_MERKLE_MAP_KEY_SIZE : Nat := 128

/-- Maximum signed 32-bit Merkle leaf index (`INT_MAX = 0x7FFFFFFF` in `get_merkle_leaf_index.c:34`). -/
def MAX_MERKLE_LEAF_INDEX : Nat := 0x7FFFFFFF

/-- Maximum 32-bit preimage length (`UINT32_MAX = 0xFFFFFFFF` in `get_preimage.c` / `stream_preimage.c`). -/
def MAX_PREIMAGE_TOTAL_SIZE : Nat := 0xFFFFFFFF

/-- Maximum initial `CCMD_GET_PREIMAGE (0x40)` inline slice (`uint8_t partial_data_len ≤ 255`). -/
def MAX_PREIMAGE_PARTIAL_SIZE : Nat := 255

/-- Maximum `CCMD_GET_MORE_ELEMENTS (0xA0)` elements per frame (`uint8_t n_elements ≤ 255`). -/
def MAX_MORE_ELEMENTS_COUNT : Nat := 255

/-- BOLOS framework status word requesting an interactive host continuation (`constants.h`). -/
def SW_INTERRUPTED_EXECUTION : UInt16 := 0xE000

/-- BOLOS continuation APDU class byte (`CLA_FRAMEWORK = 0xF8` in `constants.h`). -/
def CLA_FRAMEWORK : UInt8 := 0xF8

/-- BOLOS continuation APDU instruction byte (`INS_CONTINUE = 0x01` in `constants.h`). -/
def INS_CONTINUE : UInt8 := 0x01

/-! ## 1. RFC-6962-Variant Merkle Tree Specification (`doc/merkle.md` & `src/common/merkle.c`) -/

/-- Raw preimage `0x00 || leaf` hashed for a Merkle tree leaf (`merkle_compute_element_hash`). -/
def leafPreimage (leaf : ByteArray) : ByteArray :=
  ByteArray.mk (#[0x00] ++ leaf.data)

/-- Raw preimage `0x01 || left || right` hashed for an internal Merkle node (`merkle_combine_hashes`). -/
def nodePreimage (left right : Bytes32) : ByteArray :=
  ByteArray.mk (#[0x01] ++ left.bytes.data ++ right.bytes.data)

/-- Domain-separated Merkle leaf hash: `SHA256(0x00 || leaf)` (`merkle_compute_element_hash`). -/
def merkleLeafHash (sha256 : ByteArray → Bytes32) (leaf : ByteArray) : Bytes32 :=
  sha256 (leafPreimage leaf)

/-- Domain-separated Merkle internal node hash: `SHA256(0x01 || left || right)` (`merkle_combine_hashes`). -/
def merkleNodeHash (sha256 : ByteArray → Bytes32) (left right : Bytes32) : Bytes32 :=
  sha256 (nodePreimage left right)

/-- Helper doubling `acc` while `acc * 2 < n`. -/
def largestPow2LtGo (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc * 2 < n then
        largestPow2LtGo n fuel (acc * 2)
      else
        acc

/-- Largest power of `2` strictly smaller than `n` (for `n >= 2`), matching RFC 6962 `k < n`
    and `mask = 1 << (ceil_lg(size) - 1)` in `src/common/merkle.c`. -/
def largestPow2Lt (n : Nat) : Nat :=
  largestPow2LtGo n n 1

theorem largestPow2LtGo_pos (n fuel acc : Nat) (hPos : 0 < acc) :
    0 < largestPow2LtGo n fuel acc := by
  induction fuel generalizing acc with
  | zero => exact hPos
  | succ f ih =>
      unfold largestPow2LtGo
      split
      · exact ih (acc * 2) (Nat.mul_pos hPos (by decide))
      · exact hPos

theorem largestPow2LtGo_lt (n fuel acc : Nat) (hLt : acc < n) :
    largestPow2LtGo n fuel acc < n := by
  induction fuel generalizing acc with
  | zero => exact hLt
  | succ f ih =>
      unfold largestPow2LtGo
      split
      · rename_i hDouble
        exact ih (acc * 2) hDouble
      · exact hLt

theorem largestPow2Lt_bounds {n : Nat} (h : 2 ≤ n) :
    0 < largestPow2Lt n ∧ largestPow2Lt n < n :=
  ⟨largestPow2LtGo_pos n n 1 (by decide),
   largestPow2LtGo_lt n n 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) h)⟩

/-- Exact BOLOS Merkle Tree Hash (`MTH(D[n])` in `doc/merkle.md`):
    - `MTH([]) = zeroBytes32` (32 zero bytes — intentional Ledger deviation from RFC 6962!)
    - `MTH([d]) = SHA256(0x00 || d)`
    - `MTH(D[n]) = SHA256(0x01 || MTH(D[0:k]) || MTH(D[k:n]))` where `k = largestPow2Lt n` (`n >= 2`). -/
def merkleRoot (sha256 : ByteArray → Bytes32) (leaves : List ByteArray) : Bytes32 :=
  match leaves with
  | [] => zeroBytes32
  | [x] => merkleLeafHash sha256 x
  | x :: y :: rest =>
      have hLen : 2 ≤ (x :: y :: rest).length :=
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
      have _hk := largestPow2Lt_bounds hLen
      let k := largestPow2Lt (x :: y :: rest).length
      merkleNodeHash sha256
        (merkleRoot sha256 ((x :: y :: rest).take k))
        (merkleRoot sha256 ((x :: y :: rest).drop k))
termination_by leaves.length
decreasing_by
  · rw [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) _hk.2
  · rw [List.length_drop]
    exact Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hLen) _hk.1

/-! ## 2. Merkle Audit Directions & Bottom-Up Proof Verification (`merkle.c` & `get_merkle_leaf_hash.c`) -/

/-- Branch direction from an internal node (`left = 0`, `right = 1` in `merkle_get_ith_direction`). -/
inductive MerkleDir where
  | left
  | right
  deriving Repr, DecidableEq, Inhabited

/-- Top-down sequence of directions from the root to `index` in a tree of `size` leaves (`0 <= index < size`).
    Matches `merkle_get_ith_direction(size, index, 0 .. depth-1)` in `src/common/merkle.c`:
    - If `size <= 1` or `index >= size`, `[]`.
    - Otherwise let `k = largestPow2Lt size`:
      - if `index < k`, go `.left` into a left subtree of size `k` at `index`;
      - if `index >= k`, go `.right` into a right subtree of size `size - k` at `index - k`. -/
def merkleDirections (size index : Nat) : List MerkleDir :=
  if h : 2 ≤ size ∧ index < size then
    let k := largestPow2Lt size
    have hk := largestPow2Lt_bounds h.1
    if index < k then
      have _ : k < size := hk.2
      .left :: merkleDirections k index
    else
      have _ : size - k < size := Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) h.1) hk.1
      .right :: merkleDirections (size - k) (index - k)
  else
    []
termination_by size

/-- Fold a bottom-up list of sibling hashes along the reversed top-down directions
    (`get_merkle_leaf_hash.c:96-112`, where `cur_step = 0` pairs with `i = proof_size - 1`, i.e.,
    `dirsTopDown.reverse`). -/
def foldMerkleProofBottomUp
    (sha256 : ByteArray → Bytes32)
    (curHash : Bytes32)
    (dirsBottomUp : List MerkleDir)
    (siblingsBottomUp : List Bytes32) : Option Bytes32 :=
  match dirsBottomUp, siblingsBottomUp with
  | [], [] => some curHash
  | .left :: dRest, sib :: sRest =>
      foldMerkleProofBottomUp sha256 (merkleNodeHash sha256 curHash sib) dRest sRest
  | .right :: dRest, sib :: sRest =>
      foldMerkleProofBottomUp sha256 (merkleNodeHash sha256 sib curHash) dRest sRest
  | _, _ => none

/-- Pure structural 32-byte digest equality (`merkleBytesEq a.bytes b.bytes`) that reduces transparently
    in the Lean kernel without invoking `@[extern] ByteArray.beq` or `Classical.choice`. -/
def bytes32Eq (a b : Bytes32) : Bool :=
  merkleBytesEq a.bytes b.bytes

theorem bytes32Eq_iff (a b : Bytes32) : bytes32Eq a b = true ↔ a = b := by
  unfold bytes32Eq
  rw [merkleBytesEq_iff]
  cases a; cases b
  simp only [Bytes32.mk.injEq]

theorem bytes32Eq_refl (a : Bytes32) : bytes32Eq a a = true :=
  (bytes32Eq_iff a a).mpr rfl

/-- Canonical Merkle leaf-hash proof verification (`get_merkle_leaf_hash` in `get_merkle_leaf_hash.c`
    and `get_merkle_leaf_index.c:34`):
    1. `0 < treeSize`, `leafIndex < treeSize`, and `leafIndex ≤ MAX_MERKLE_LEAF_INDEX (0x7FFFFFFF)`.
    2. `siblingsBottomUp.length ≤ MAX_MERKLE_TREE_DEPTH (32)`.
    3. `siblingsBottomUp.length == (merkleDirections treeSize leafIndex).length` (exact leaf depth check!).
    4. Folding `leafHash` bottom-up with `siblingsBottomUp` equals `expectedRoot`. -/
def verifyMerkleLeafHashProof
    (sha256 : ByteArray → Bytes32)
    (expectedRoot : Bytes32)
    (treeSize : Nat)
    (leafIndex : Nat)
    (leafHash : Bytes32)
    (siblingsBottomUp : List Bytes32) : Bool :=
  if decide (treeSize = 0) || decide (leafIndex ≥ treeSize) ||
     decide (leafIndex > MAX_MERKLE_LEAF_INDEX) ||
     decide (siblingsBottomUp.length > MAX_MERKLE_TREE_DEPTH) then
    false
  else
    let dirsBottomUp := (merkleDirections treeSize leafIndex).reverse
    match foldMerkleProofBottomUp sha256 leafHash dirsBottomUp siblingsBottomUp with
    | some computedRoot => bytes32Eq computedRoot expectedRoot
    | none => false

/-- Raw (non-`0x00`-prefixed) SHA-256 preimage verification (`get_preimage.c` / `stream_preimage.c`,
    used for wallet-policy descriptor templates & key info vectors):
    Enforces `1 ≤ rawPreimage.size ≤ MAX_PREIMAGE_TOTAL_SIZE (0xFFFFFFFF)` and `sha256 rawPreimage == expectedHash`. -/
def verifyRawPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedHash : Bytes32)
    (rawPreimage : ByteArray) : Option ByteArray :=
  if decide (rawPreimage.size = 0) || decide (rawPreimage.size > MAX_PREIMAGE_TOTAL_SIZE) then
    none
  else if !bytes32Eq (sha256 rawPreimage) expectedHash then
    none
  else
    some rawPreimage

/-- Canonical Merkle leaf preimage verification (`get_merkle_preimage.c`):
    Given a verified `leafHash`, checks `rawPreimageWithPrefix.size ≤ MAX_PREIMAGE_TOTAL_SIZE`,
    `0x00` domain prefix, and `sha256 (0x00 || element) == leafHash`. -/
def verifyMerkleLeafPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (rawPreimageWithPrefix : ByteArray) : Option ByteArray :=
  if decide (rawPreimageWithPrefix.size > MAX_PREIMAGE_TOTAL_SIZE) then
    none
  else
    match rawPreimageWithPrefix.data.toList with
    | 0x00 :: rest =>
        if !bytes32Eq (sha256 rawPreimageWithPrefix) expectedLeafHash then
          none
        else
          some (ByteArray.mk rest.toArray)
    | _ => none

/-- Combined Merkle leaf-element opening (`call_get_merkle_leaf_element`):
    Verifies both the Merkle audit path to `expectedRoot` at `(treeSize, leafIndex)` AND
    that `merkleLeafHash sha256 element == leafHash`. -/
structure MerkleElementOpening where
  element : ByteArray
  leafHash : Bytes32
  siblingsBottomUp : List Bytes32
  deriving DecidableEq

def verifyMerkleElementOpening
    (sha256 : ByteArray → Bytes32)
    (expectedRoot : Bytes32)
    (treeSize : Nat)
    (leafIndex : Nat)
    (opening : MerkleElementOpening) : Bool :=
  verifyMerkleLeafHashProof sha256 expectedRoot treeSize leafIndex opening.leafHash opening.siblingsBottomUp &&
  bytes32Eq (merkleLeafHash sha256 opening.element) opening.leafHash

/-- Construct the honest bottom-up Merkle audit path for `leaves[index]` (`0 <= index < leaves.length`). -/
def buildMerkleAuditPath
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (index : Nat) : List Bytes32 :=
  match leaves with
  | [] => []
  | [_] => []
  | x :: y :: rest =>
      have hLen : 2 ≤ (x :: y :: rest).length :=
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
      have _hk := largestPow2Lt_bounds hLen
      let k := largestPow2Lt (x :: y :: rest).length
      if index < k then
        buildMerkleAuditPath sha256 ((x :: y :: rest).take k) index ++
          [merkleRoot sha256 ((x :: y :: rest).drop k)]
      else
        buildMerkleAuditPath sha256 ((x :: y :: rest).drop k) (index - k) ++
          [merkleRoot sha256 ((x :: y :: rest).take k)]
termination_by leaves.length
decreasing_by
  · rw [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) _hk.2
  · rw [List.length_drop]
    exact Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hLen) _hk.1

/-! ## 3. Strict Lexicographic Key Ordering (`check_merkle_tree_sorted.c`) -/

/-- Strict lexicographic comparison on byte lists (`compare_byte_arrays < 0` in `check_merkle_tree_sorted.c`):
    Shorter prefix comes strictly before a longer extension. -/
def listUInt8Lt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a.toNat < b.toNat then
        true
      else if b.toNat < a.toNat then
        false
      else
        listUInt8Lt as bs

/-- Strict lexicographic comparison on `ByteArray`s. -/
def byteArrayLt (a b : ByteArray) : Bool :=
  listUInt8Lt a.data.toList b.data.toList

/-- Strict pairwise sortedness of a list of `ByteArray` keys (`k_0 < k_1 < ... < k_{n-1}`). -/
def isStrictlySorted : List ByteArray → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => byteArrayLt a b && isStrictlySorted (b :: rest)

/-! ## 4. Merkleized Key-Value Map Commitments & Interactive Client Commands -/

/-- BOLOS Merkleized Map Commitment (`merkleized_map_commitment_t` in `doc/merkle.md` & `merkle.h`):
    Commits to `size` key-value pairs via `keysRoot = MTH(keys)` and `valuesRoot = MTH(values)`. -/
structure MerkleMapCommitment where
  size : Nat
  keysRoot : Bytes32
  valuesRoot : Bytes32
  deriving Repr, DecidableEq, Inhabited

/-- Canonical wire serialization of a `MerkleMapCommitment`:
    `varint(size) || keysRoot (32B) || valuesRoot (32B)` (`65..73` bytes in `doc/merkle.md`). -/
def serializeMerkleMapCommitment (m : MerkleMapCommitment) : ByteArray :=
  encodeVarInt m.size ++ m.keysRoot.bytes ++ m.valuesRoot.bytes

/-- Construct an honest `MerkleMapCommitment` from a list of `(key, value)` pairs. -/
def commitMerkleMap (sha256 : ByteArray → Bytes32) (entries : List (ByteArray × ByteArray)) : MerkleMapCommitment :=
  { size := entries.length
    keysRoot := merkleRoot sha256 (entries.map Prod.fst)
    valuesRoot := merkleRoot sha256 (entries.map Prod.snd) }

/-- BOLOS interactive client-command opcodes (`src/handler/client_commands.h`, sent with `SW_INTERRUPTED_EXECUTION = 0xE000`). -/
inductive ClientCommandTag : Type where
  /-- `CCMD_YIELD (0x10)`: stream signature / pubnonce / progress output to host. -/
  | yield
  /-- `CCMD_GET_PREIMAGE (0x40)`: request preimage of a 32-byte SHA-256 digest. -/
  | getPreimage
  /-- `CCMD_GET_MERKLE_LEAF_PROOF (0x41)`: request `(leafHash, siblingPath)` for `(root, size, index)`. -/
  | getMerkleLeafProof
  /-- `CCMD_GET_MERKLE_LEAF_INDEX (0x42)`: query `(found, index)` of `leafHash` in `root`. -/
  | getMerkleLeafIndex
  /-- `CCMD_GET_MORE_ELEMENTS (0xA0)`: stream remaining bytes / proof hashes across APDU frames. -/
  | getMoreElements
  deriving Repr, DecidableEq, Inhabited

def ClientCommandTag.toByte : ClientCommandTag → UInt8
  | .yield              => 0x10
  | .getPreimage        => 0x40
  | .getMerkleLeafProof => 0x41
  | .getMerkleLeafIndex => 0x42
  | .getMoreElements    => 0xA0

/-- Untrusted host oracle model answering BOLOS client commands during an interactive command session. -/
structure UntrustedHostOracle where
  /-- `CCMD_GET_PREIMAGE`: given `hash`, returns raw preimage bytes (including `0x00` prefix for Merkle leaves). -/
  queryPreimage : Bytes32 → Option ByteArray
  /-- `CCMD_GET_MERKLE_LEAF_PROOF`: given `(root, treeSize, leafIndex)`, returns `(leafHash, siblingsBottomUp)`. -/
  queryLeafProof : Bytes32 → Nat → Nat → Option (Bytes32 × List Bytes32)
  /-- `CCMD_GET_MERKLE_LEAF_INDEX`: given `(root, leafHash)`, returns `(found, candidateIndex)`. -/
  queryLeafIndex : Bytes32 → Bytes32 → Option (Bool × Nat)

/-- Pure structural `find?` helper that reduces transparently in the Lean kernel. -/
private def findPure? {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else findPure? p xs

/-- Pure structural `getAt?` helper that reduces transparently in the Lean kernel. -/
private def getAtPure? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => getAtPure? xs n

/-- Pure structural `findIdx?` helper that reduces transparently in the Lean kernel. -/
private def findIdxPure? {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | x :: xs => if p x then some 0 else (findIdxPure? p xs).map (· + 1)

/-- Honest host oracle constructed from a known store of Merkle trees (indexed by root) and preimages. -/
def mkHonestTreeHostOracle (sha256 : ByteArray → Bytes32) (leaves : List ByteArray) : UntrustedHostOracle :=
  let root := merkleRoot sha256 leaves
  { queryPreimage := fun h =>
      match findPure? (fun el => bytes32Eq (merkleLeafHash sha256 el) h) leaves with
      | some el => some (leafPreimage el)
      | none => none
    queryLeafProof := fun r sz idx =>
      if bytes32Eq r root && decide (sz = leaves.length) then
        match getAtPure? leaves idx with
        | some el => some (merkleLeafHash sha256 el, buildMerkleAuditPath sha256 leaves idx)
        | none => none
      else
        none
    queryLeafIndex := fun r lh =>
      if bytes32Eq r root then
        match findIdxPure? (fun el => bytes32Eq (merkleLeafHash sha256 el) lh) leaves with
        | some idx => some (true, idx)
        | none => some (false, 0)
      else
        none }

/-- Honest host oracle constructed for a Merkleized key-value map (`keysRoot` and `valuesRoot`). -/
def mkHonestMapHostOracle
    (sha256 : ByteArray → Bytes32)
    (entries : List (ByteArray × ByteArray)) : UntrustedHostOracle :=
  let keys := entries.map Prod.fst
  let vals := entries.map Prod.snd
  let kRoot := merkleRoot sha256 keys
  let vRoot := merkleRoot sha256 vals
  let allLeaves := keys ++ vals
  { queryPreimage := fun h =>
      match findPure? (fun el => bytes32Eq (merkleLeafHash sha256 el) h) allLeaves with
      | some el => some (leafPreimage el)
      | none => none
    queryLeafProof := fun r sz idx =>
      if bytes32Eq r kRoot && decide (sz = keys.length) then
        match getAtPure? keys idx with
        | some el => some (merkleLeafHash sha256 el, buildMerkleAuditPath sha256 keys idx)
        | none => none
      else if bytes32Eq r vRoot && decide (sz = vals.length) then
        match getAtPure? vals idx with
        | some el => some (merkleLeafHash sha256 el, buildMerkleAuditPath sha256 vals idx)
        | none => none
      else
        none
    queryLeafIndex := fun r lh =>
      if bytes32Eq r kRoot then
        match findIdxPure? (fun el => bytes32Eq (merkleLeafHash sha256 el) lh) keys with
        | some idx => some (true, idx)
        | none => some (false, 0)
      else
        none }

/-- Device-side execution of `call_get_merkle_leaf_element` against an untrusted host (`get_merkle_leaf_hash.c` + `get_merkle_preimage.c`). -/
def deviceFetchLeafElement
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (root : Bytes32)
    (treeSize : Nat)
    (leafIndex : Nat) : Option ByteArray :=
  match host.queryLeafProof root treeSize leafIndex with
  | none => none
  | some (leafHash, siblings) =>
      if !verifyMerkleLeafHashProof sha256 root treeSize leafIndex leafHash siblings then
        none
      else
        match host.queryPreimage leafHash with
        | none => none
        | some rawPreimage =>
            verifyMerkleLeafPreimage sha256 leafHash rawPreimage

/-- Device-side verification that a `MerkleMapCommitment` has strictly sorted keys and obeys BOLOS bounds
    (`call_check_merkle_tree_sorted_with_callback` in `check_merkle_tree_sorted.c` & `get_merkleized_map.c`):
    - If `map.size == 0`, requires both `keysRoot` and `valuesRoot` to be `zeroBytes32` and `keyOpenings = []`.
    - If `map.size ≥ 1`, opens all `i ∈ [0, map.size)` against `(map.keysRoot, map.size, i)`,
      enforces `op.element.size ≤ MAX_MERKLE_MAP_KEY_SIZE (128)` on every key, and checks `isStrictlySorted`! -/
def verifySortedMerkleMapOpenings
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening) : Bool :=
  (if decide (map.size = 0) then
    bytes32Eq map.keysRoot zeroBytes32 && bytes32Eq map.valuesRoot zeroBytes32
  else
    true) &&
  decide (keyOpenings.length = map.size) &&
  ((List.range map.size).zip keyOpenings).all (fun (i, op) =>
    decide (op.element.size ≤ MAX_MERKLE_MAP_KEY_SIZE) &&
    verifyMerkleElementOpening sha256 map.keysRoot map.size i op) &&
  isStrictlySorted (keyOpenings.map (·.element))

/-- Result of an interactive Merkleized map lookup (`call_get_merkleized_map_value` in `get_merkleized_map_value.c`). -/
inductive MapLookupResult where
  /-- Key proven present at a verified index, returning its cryptographically verified value bytes. -/
  | present (value : ByteArray)
  /-- Host claimed key is absent (`found = 0` in `CCMD_GET_MERKLE_LEAF_INDEX`); unverified unless cross-checked against key-scan flags! -/
  | absentClaimed
  /-- Host provided an out-of-range index, invalid Merkle proof, mismatched leaf hash, or bad preimage. -/
  | protocolError
  deriving DecidableEq

/-- Device-side execution of `call_get_merkleized_map_value` (`get_merkle_leaf_index.c` + `get_merkleized_map_value.c`):
    1. Computes `keyLeafHash = merkleLeafHash sha256 key`.
    2. Queries untrusted host via `CCMD_GET_MERKLE_LEAF_INDEX(map.keysRoot, keyLeafHash)`.
    3. Rejects immediately (`MERKLE_LEAF_ERROR` -> `.protocolError`) if `map.size == 0`,
       `idx > MAX_MERKLE_LEAF_INDEX (0x7FFFFFFF)`, or `idx ≥ map.size` (`get_merkle_leaf_index.c:34-35`),
       even when `found == false`!
    4. If `found == false`, returns `.absentClaimed`.
    5. If `found == true`, verifies a Merkle leaf-hash proof at `(map.keysRoot, map.size, idx)` and enforces
       `returnedLeafHash == keyLeafHash`!
    6. Opens and verifies the corresponding value leaf element at the **exact same index** `idx` in
       `(map.valuesRoot, map.size, idx)`! -/
def deviceLookupMerkleMapValue
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray) : MapLookupResult :=
  if decide (map.size = 0) then
    .protocolError
  else
    let keyHash := merkleLeafHash sha256 key
    match host.queryLeafIndex map.keysRoot keyHash with
    | none => .protocolError
    | some (found, idx) =>
        if decide (idx > MAX_MERKLE_LEAF_INDEX) || decide (idx ≥ map.size) then
          .protocolError
        else if !found then
          .absentClaimed
        else
          match host.queryLeafProof map.keysRoot map.size idx with
          | none => .protocolError
          | some (returnedKeyHash, keySiblings) =>
              if !bytes32Eq returnedKeyHash keyHash then
                .protocolError
              else if !verifyMerkleLeafHashProof sha256 map.keysRoot map.size idx returnedKeyHash keySiblings then
                .protocolError
              else
                match deviceFetchLeafElement sha256 host map.valuesRoot map.size idx with
                | some valBytes => .present valBytes
                | none => .protocolError

/-- Proof witness bundle for a `present` map lookup (decoupled from oracle callbacks for clean relational reasoning). -/
structure MapLookupProof where
  index : Nat
  keySiblingsBottomUp : List Bytes32
  valueOpening : MerkleElementOpening
  deriving DecidableEq

def verifyMapLookupProof
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (p : MapLookupProof) : Bool :=
  let keyHash := merkleLeafHash sha256 key
  verifyMerkleLeafHashProof sha256 map.keysRoot map.size p.index keyHash p.keySiblingsBottomUp &&
  verifyMerkleElementOpening sha256 map.valuesRoot map.size p.index p.valueOpening

/-- BOLOS `SIGN_PSBT` top-level Merkleized commitment payload (`parse_sign_psbt_apdu` in `init_global_state.c`):
    Commits to the global map, `nInputs` input map commitments (`inputsRoot`), `nOutputs` output map
    commitments (`outputsRoot`), and the wallet policy (`walletId`, `walletHmac`). -/
structure MerkleizedPsbtCommitment where
  globalMap : MerkleMapCommitment
  nInputs : Nat
  inputsRoot : Bytes32
  nOutputs : Nat
  outputsRoot : Bytes32
  walletId : Bytes32
  walletHmac : Bytes32
  deriving Repr, DecidableEq, Inhabited

/-! ## 4.5 BOLOS `0xE000` (`SW_INTERRUPTED_EXECUTION`) & Streaming Preimage Protocol
    (`dispatcher.c`, `get_preimage.c`, `get_merkle_preimage.c`, `stream_preimage.c`) -/

/-- Host continuation APDU header sent in response to `SW_INTERRUPTED_EXECUTION (0xE000)`. -/
structure ContinuationApdu where
  cla : UInt8
  ins : UInt8
  p1 : UInt8 := 0
  p2 : UInt8 := 0
  deriving Repr, DecidableEq, Inhabited

/-- Device-side framework validation of an interrupted-execution continuation APDU (`dispatcher.c:108`):
    MUST have `cla = CLA_FRAMEWORK (0xF8)`, `ins = INS_CONTINUE (0x01)`, and `p1 = p2 = 0`. -/
def validateContinuationApdu (hdr : ContinuationApdu) : Bool :=
  decide (hdr.cla = CLA_FRAMEWORK) &&
  decide (hdr.ins = INS_CONTINUE) &&
  decide (hdr.p1 = 0) &&
  decide (hdr.p2 = 0)

/-- Device-emitted interruption frame pairing a `ClientCommandTag` payload with `SW_INTERRUPTED_EXECUTION (0xE000)`. -/
structure DeviceInterruptFrame where
  command : ClientCommandTag
  requestPayload : ByteArray
  statusWord : UInt16 := SW_INTERRUPTED_EXECUTION
  deriving DecidableEq

/-- Initial host response to `CCMD_GET_PREIMAGE (0x40)` (`get_preimage.c` / `stream_preimage.c`):
    - `continuation`: continuation APDU header (`CLA=0xF8, INS=0x01`)
    - `declaredTotalSize`: VarInt-decoded total byte length (`1 .. 0xFFFFFFFF`)
    - `partialData`: inline initial slice accompanied by a 1-byte `partialData.size ≤ 255` prefix. -/
structure PreimageInitFrame where
  continuation : ContinuationApdu
  declaredTotalSize : Nat
  partialData : ByteArray
  deriving DecidableEq

/-- Subsequent host response chunk to `CCMD_GET_MORE_ELEMENTS (0xA0)` (`stream_preimage.c` / `get_preimage.c`):
    - `continuation`: continuation APDU header (`CLA=0xF8, INS=0x01`)
    - `nElements`: 1-byte element count (`1 .. 255`; `0` is rejected to prevent infinite streaming loops!)
    - `elementSize`: 1-byte element width (`1` for preimage byte streaming; `32` for Merkle sibling hashes)
    - `chunkData`: raw payload of exact byte width `nElements * elementSize`. -/
structure MoreElementsChunk where
  continuation : ContinuationApdu
  nElements : Nat
  elementSize : Nat
  chunkData : ByteArray
  deriving DecidableEq

/-- Errors raised during BOLOS `0xE000` interrupted preimage streaming. -/
inductive PreimageStreamError where
  | badContinuationHeader
  | invalidDeclaredLength
  | invalidPartialSliceLength
  | invalidElementWidth
  | invalidChunkElementCount
  | chunkPayloadSizeMismatch
  | streamOverflowBeyondDeclared
  | streamTruncatedBeforeDeclared
  | missingMerkleLeafPrefix
  | digestMismatch
  deriving Repr, DecidableEq, Inhabited

/-- Accumulate `CCMD_GET_MORE_ELEMENTS (0xA0)` byte chunks (`elementSize = 1`) onto `acc`,
    enforcing non-empty chunks `1 ≤ nElements ≤ 255`, exact payload width, and no over-read past `bytesRemaining`. -/
def foldPreimageChunks
    (bytesRemaining : Nat)
    (acc : ByteArray) : List MoreElementsChunk → Except PreimageStreamError ByteArray
  | [] =>
      if decide (bytesRemaining = 0) then
        .ok acc
      else
        .error .streamTruncatedBeforeDeclared
  | c :: rest =>
      if !validateContinuationApdu c.continuation then
        .error .badContinuationHeader
      else if decide (c.elementSize ≠ 1) then
        .error .invalidElementWidth
      else if decide (c.nElements = 0) || decide (c.nElements > MAX_MORE_ELEMENTS_COUNT) then
        .error .invalidChunkElementCount
      else if decide (c.chunkData.size ≠ c.nElements) then
        .error .chunkPayloadSizeMismatch
      else if decide (c.nElements > bytesRemaining) then
        .error .streamOverflowBeyondDeclared
      else
        foldPreimageChunks (bytesRemaining - c.nElements) (acc ++ c.chunkData) rest

/-- Full BOLOS interactive streaming verifier for raw (non-`0x00`-prefixed) preimages (`stream_preimage.c` / `get_preimage.c`,
    used for wallet policy descriptor templates and key-info payloads):
    1. Validates `CLA=0xF8, INS=0x01` on `init` and every `CCMD_GET_MORE_ELEMENTS` continuation frame.
    2. Enforces `1 ≤ declaredTotalSize ≤ 0xFFFFFFFF`, `partialData.size ≤ 255`, and `partialData.size ≤ declaredTotalSize`
       (and non-empty initial data when `chunks = []` or `declaredTotalSize > 0` with `partialData.size ≤ 255`).
    3. Enforces `elementSize == 1`, `1 ≤ nElements ≤ 255`, and exact byte count across `chunks`.
    4. Checks final `SHA-256` digest equality against `expectedHash` before releasing assembled bytes! -/
def streamVerifyRawPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedHash : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk) : Except PreimageStreamError ByteArray :=
  if !validateContinuationApdu init.continuation then
    .error .badContinuationHeader
  else if decide (init.declaredTotalSize = 0) || decide (init.declaredTotalSize > MAX_PREIMAGE_TOTAL_SIZE) then
    .error .invalidDeclaredLength
  else if decide (init.partialData.size > MAX_PREIMAGE_PARTIAL_SIZE) ||
          decide (init.partialData.size > init.declaredTotalSize) then
    .error .invalidPartialSliceLength
  else
    match foldPreimageChunks (init.declaredTotalSize - init.partialData.size) init.partialData chunks with
    | .error e => .error e
    | .ok assembled =>
        if !bytes32Eq (sha256 assembled) expectedHash then
          .error .digestMismatch
        else
          .ok assembled

/-- Full BOLOS interactive streaming verifier for `0x00`-prefixed Merkle leaf preimages (`get_merkle_preimage.c`):
    Runs `streamVerifyRawPreimage` (enforcing `0xE000` continuation headers, `partialData.size ≤ 255`,
    `CCMD_GET_MORE_ELEMENTS` `elementSize = 1` & `1 ≤ nElements ≤ 255`, exact total length, and final `SHA-256`)
    and additionally enforces and strips the leading `0x00` RFC-6962 leaf domain separator! -/
def streamVerifyMerkleLeafPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk) : Except PreimageStreamError ByteArray :=
  match streamVerifyRawPreimage sha256 expectedLeafHash init chunks with
  | .error e => .error e
  | .ok assembled =>
      match assembled.data.toList with
      | 0x00 :: rest => .ok (ByteArray.mk rest.toArray)
      | _ => .error .missingMerkleLeafPrefix

/-! ## 5. Finite-Pool Collision-Relative Soundness & Uniqueness Proofs (`0 sorryAx`, `0 Classical.choice`) -/

/-- Finite-pool cryptographic collision-resistance predicate (`Audit C-03` remediation):
    Unlike global injectivity `∀ a b : ByteArray, sha256 a = sha256 b → a = b` (which is false by pigeonhole
    since `ByteArray` is infinite while `Bytes32` has `2^256` inhabitants), `CollisionFreeOn sha256 pool`
    asserts only that no two distinct preimages *within the finite list `pool` of preimages actually hashed
    during tree construction and protocol execution* collide under `sha256`. -/
def CollisionFreeOn (sha256 : ByteArray → Bytes32) (pool : List ByteArray) : Prop :=
  ∀ a, a ∈ pool → ∀ b, b ∈ pool → sha256 a = sha256 b → a = b

theorem CollisionFreeOn.mono {sha256 : ByteArray → Bytes32} {p1 p2 : List ByteArray}
    (hSub : ∀ x, x ∈ p1 → x ∈ p2)
    (hCF : CollisionFreeOn sha256 p2) :
    CollisionFreeOn sha256 p1 :=
  fun a ha b hb hEq => hCF a (hSub a ha) b (hSub b hb) hEq

/-! ### 5.0 Deterministic Preimage Collectors (`treePreimages`, `proofPreimages`, `mapLookupProofPreimages`) -/

/-- Collect every `0x00 || leaf` and `0x01 || left || right` preimage hashed by `merkleRoot sha256 leaves`. -/
def treePreimages (sha256 : ByteArray → Bytes32) (leaves : List ByteArray) : List ByteArray :=
  match leaves with
  | [] => []
  | [x] => [leafPreimage x]
  | x :: y :: rest =>
      have hLen : 2 ≤ (x :: y :: rest).length :=
        Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
      have _hk := largestPow2Lt_bounds hLen
      let k := largestPow2Lt (x :: y :: rest).length
      let leftLeaves := (x :: y :: rest).take k
      let rightLeaves := (x :: y :: rest).drop k
      nodePreimage (merkleRoot sha256 leftLeaves) (merkleRoot sha256 rightLeaves) ::
        (treePreimages sha256 leftLeaves ++ treePreimages sha256 rightLeaves)
termination_by leaves.length
decreasing_by
  · rw [List.length_take]
    exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) _hk.2
  · rw [List.length_drop]
    exact Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hLen) _hk.1

/-- Collect every `0x01 || left || right` internal-node preimage hashed along `foldMerkleProofBottomUp`. -/
def foldProofPreimages
    (sha256 : ByteArray → Bytes32)
    (curHash : Bytes32)
    (dirsBottomUp : List MerkleDir)
    (siblingsBottomUp : List Bytes32) : List ByteArray :=
  match dirsBottomUp, siblingsBottomUp with
  | [], [] => []
  | .left :: dRest, sib :: sRest =>
      nodePreimage curHash sib ::
        foldProofPreimages sha256 (merkleNodeHash sha256 curHash sib) dRest sRest
  | .right :: dRest, sib :: sRest =>
      nodePreimage sib curHash ::
        foldProofPreimages sha256 (merkleNodeHash sha256 sib curHash) dRest sRest
  | _, _ => []

/-- Collect every internal-node preimage hashed during `verifyMerkleLeafHashProof`. -/
def proofPreimages
    (sha256 : ByteArray → Bytes32)
    (treeSize leafIndex : Nat)
    (leafHash : Bytes32)
    (siblingsBottomUp : List Bytes32) : List ByteArray :=
  foldProofPreimages sha256 leafHash (merkleDirections treeSize leafIndex).reverse siblingsBottomUp

/-- Collect the leaf preimage `0x00 || op.element` and all audit-path node preimages for `op`. -/
def openingPreimages
    (sha256 : ByteArray → Bytes32)
    (treeSize leafIndex : Nat)
    (op : MerkleElementOpening) : List ByteArray :=
  leafPreimage op.element :: proofPreimages sha256 treeSize leafIndex op.leafHash op.siblingsBottomUp

/-- Collect all leaf & internal-node preimages hashed across `verifySortedMerkleMapOpenings`. -/
def sortedMapOpeningsPreimages
    (sha256 : ByteArray → Bytes32)
    (mapSize : Nat)
    (keyOpenings : List MerkleElementOpening) : List ByteArray :=
  ((List.range mapSize).zip keyOpenings).foldr
    (fun (i, op) acc => openingPreimages sha256 mapSize i op ++ acc) []

/-- Collect all leaf & internal-node preimages hashed during `verifyMapLookupProof`. -/
def mapLookupProofPreimages
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (p : MapLookupProof) : List ByteArray :=
  leafPreimage key ::
    (proofPreimages sha256 map.size p.index (merkleLeafHash sha256 key) p.keySiblingsBottomUp ++
     openingPreimages sha256 map.size p.index p.valueOpening)

/-- Collect all leaf & internal-node preimages hashed during an interactive `deviceLookupMerkleMapValue` session. -/
def hostLookupPreimages
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray) : List ByteArray :=
  let keyHash := merkleLeafHash sha256 key
  let base := [leafPreimage key]
  match host.queryLeafIndex map.keysRoot keyHash with
  | none => base
  | some (_, idx) =>
      let keyPart :=
        match host.queryLeafProof map.keysRoot map.size idx with
        | none => []
        | some (_, keySibs) => proofPreimages sha256 map.size idx keyHash keySibs
      let valPart :=
        match host.queryLeafProof map.valuesRoot map.size idx with
        | none => []
        | some (valLh, valSibs) =>
            let prePart :=
              match host.queryPreimage valLh with
              | none => []
              | some rawPre =>
                  match verifyMerkleLeafPreimage sha256 valLh rawPre with
                  | some valBytes => [leafPreimage valBytes, rawPre]
                  | none => [rawPre]
            prePart ++ proofPreimages sha256 map.size idx valLh valSibs
      base ++ keyPart ++ valPart

/-! ### 5.1 Strict Lexicographic Order Lemmas (Irreflexivity, Transitivity, Pairwise Key Uniqueness) -/

theorem listUInt8Lt_irrefl (xs : List UInt8) : listUInt8Lt xs xs = false := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      unfold listUInt8Lt
      have hNotLt : ¬(a.toNat < a.toNat) := Nat.lt_irrefl _
      simp only [hNotLt, ↓reduceIte, ih]

theorem byteArrayLt_irrefl (x : ByteArray) : byteArrayLt x x = false :=
  listUInt8Lt_irrefl x.data.toList

theorem listUInt8Lt_trans {xs ys zs : List UInt8}
    (hxy : listUInt8Lt xs ys = true)
    (hyz : listUInt8Lt ys zs = true) :
    listUInt8Lt xs zs = true := by
  induction xs generalizing ys zs with
  | nil =>
      cases ys with
      | nil => simp only [listUInt8Lt, Bool.false_eq_true] at hxy
      | cons b bs =>
          cases zs with
          | nil => simp only [listUInt8Lt, Bool.false_eq_true] at hyz
          | cons c cs => rfl
  | cons a as ih =>
      cases ys with
      | nil => simp only [listUInt8Lt, Bool.false_eq_true] at hxy
      | cons b bs =>
          cases zs with
          | nil => simp only [listUInt8Lt, Bool.false_eq_true] at hyz
          | cons c cs =>
              unfold listUInt8Lt at hxy hyz ⊢
              by_cases hab : a.toNat < b.toNat
              · by_cases hbc : b.toNat < c.toNat
                · have hac : a.toNat < c.toNat := Nat.lt_trans hab hbc
                  simp only [hac, ↓reduceIte]
                · by_cases hcb : c.toNat < b.toNat
                  · simp only [hbc, hcb, ↓reduceIte, Bool.false_eq_true] at hyz
                  · have hEqBC : b.toNat = c.toNat :=
                      Nat.le_antisymm (Nat.le_of_not_lt hcb) (Nat.le_of_not_lt hbc)
                    have hac : a.toNat < c.toNat := hEqBC ▸ hab
                    simp only [hac, ↓reduceIte]
              · by_cases hba : b.toNat < a.toNat
                · simp only [hab, hba, ↓reduceIte, Bool.false_eq_true] at hxy
                · have hEqAB : a.toNat = b.toNat :=
                    Nat.le_antisymm (Nat.le_of_not_lt hba) (Nat.le_of_not_lt hab)
                  simp only [hab, hba, ↓reduceIte] at hxy
                  by_cases hbc : b.toNat < c.toNat
                  · have hac : a.toNat < c.toNat := hEqAB.symm ▸ hbc
                    simp only [hac, ↓reduceIte]
                  · by_cases hcb : c.toNat < b.toNat
                    · simp only [hbc, hcb, ↓reduceIte, Bool.false_eq_true] at hyz
                    · have hEqBC : b.toNat = c.toNat :=
                        Nat.le_antisymm (Nat.le_of_not_lt hcb) (Nat.le_of_not_lt hbc)
                      have hEqAC : a.toNat = c.toNat := hEqAB.trans hEqBC
                      have hNotAC : ¬(a.toNat < c.toNat) := by
                        rw [hEqAC]; exact Nat.lt_irrefl _
                      have hNotCA : ¬(c.toNat < a.toNat) := by
                        rw [hEqAC]; exact Nat.lt_irrefl _
                      simp only [hbc, hcb, ↓reduceIte] at hyz
                      simp only [hNotAC, hNotCA, ↓reduceIte, ih hxy hyz]

theorem byteArrayLt_trans {a b c : ByteArray}
    (hab : byteArrayLt a b = true)
    (hbc : byteArrayLt b c = true) :
    byteArrayLt a c = true :=
  listUInt8Lt_trans hab hbc

theorem byteArrayLt_ne {a b : ByteArray} (h : byteArrayLt a b = true) : a ≠ b := by
  intro hEq
  subst hEq
  rw [byteArrayLt_irrefl] at h
  contradiction

/-- In a strictly sorted list `x :: rest`, `x < y` holds for every element `y ∈ rest`. -/
theorem strictlySorted_head_lt_tail {x : ByteArray} {rest : List ByteArray}
    (hSorted : isStrictlySorted (x :: rest) = true) :
    ∀ y ∈ rest, byteArrayLt x y = true := by
  induction rest generalizing x with
  | nil =>
      intro y hy
      cases hy
  | cons z zs ih =>
      unfold isStrictlySorted at hSorted
      simp only [Bool.and_eq_true] at hSorted
      intro y hy
      cases hy with
      | head => exact hSorted.1
      | tail _ hyZs =>
          have hzy := ih hSorted.2 y hyZs
          exact byteArrayLt_trans hSorted.1 hzy

/-- Every pair of distinct indices `i < j` in a strictly sorted list satisfies `byteArrayLt keys[i] keys[j] = true`. -/
theorem strictlySorted_index_lt {keys : List ByteArray}
    (hSorted : isStrictlySorted keys = true)
    {i j : Nat} {ki kj : ByteArray}
    (hij : i < j)
    (hi : keys[i]? = some ki)
    (hj : keys[j]? = some kj) :
    byteArrayLt ki kj = true := by
  induction keys generalizing i j with
  | nil => simp at hi
  | cons hd tl ih =>
      cases i with
      | zero =>
          simp at hi
          subst hi
          cases j with
          | zero => exact absurd hij (Nat.lt_irrefl 0)
          | succ j' =>
              simp at hj
              have hMem : kj ∈ tl := List.mem_of_getElem? hj
              exact strictlySorted_head_lt_tail hSorted kj hMem
      | succ i' =>
          cases j with
          | zero => exact absurd hij (Nat.not_lt_zero _)
          | succ j' =>
              simp at hi hj
              have hTailSorted : isStrictlySorted tl = true := by
                cases tl with
                | nil => rfl
                | cons b bs =>
                    unfold isStrictlySorted at hSorted
                    simp only [Bool.and_eq_true] at hSorted
                    exact hSorted.2
              exact ih hTailSorted (Nat.lt_of_succ_lt_succ hij) hi hj

/-- **SORTED KEYS UNIQUENESS LEMMA**:
    In any strictly sorted list of keys, distinct indices NEVER contain equal keys (`i ≠ j → keys[i] ≠ keys[j]`). -/
theorem strictlySorted_pairwise_distinct {keys : List ByteArray}
    (hSorted : isStrictlySorted keys = true)
    {i j : Nat} {k1 k2 : ByteArray}
    (hNe : i ≠ j)
    (hi : keys[i]? = some k1)
    (hj : keys[j]? = some k2) :
    k1 ≠ k2 := by
  cases Nat.lt_or_ge i j with
  | inl hLt => exact byteArrayLt_ne (strictlySorted_index_lt hSorted hLt hi hj)
  | inr hGe =>
      cases Nat.eq_or_lt_of_le hGe with
      | inl hEqIJ => exact absurd hEqIJ.symm hNe
      | inr hGt =>
          intro hEq
          subst hEq
          exact byteArrayLt_ne (strictlySorted_index_lt hSorted hGt hj hi) rfl

/-! ### 5.2 Domain Separation & Finite-Pool Injectivity of Leaf / Internal Node Hashes -/

/-- Under `CollisionFreeOn sha256 pool`, `merkleLeafHash` is injective on any two leaves whose
    `0x00 || leaf` preimages lie in `pool`. -/
theorem merkleLeafHash_injective_on {sha256 : ByteArray → Bytes32} {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {a b : ByteArray}
    (ha : leafPreimage a ∈ pool)
    (hb : leafPreimage b ∈ pool)
    (hEq : merkleLeafHash sha256 a = merkleLeafHash sha256 b) :
    a = b := by
  have hPre := hCF (leafPreimage a) ha (leafPreimage b) hb hEq
  have hData : (ByteArray.mk (#[0x00] ++ a.data)).data.toList = (ByteArray.mk (#[0x00] ++ b.data)).data.toList :=
    congrArg (fun x => x.data.toList) hPre
  simp only [Array.toList_append, List.cons_append, List.nil_append, List.cons.injEq, true_and] at hData
  cases a with | mk da =>
  cases b with | mk db =>
  congr
  exact Array.ext' hData

/-- Under `CollisionFreeOn sha256 pool`, `merkleNodeHash` is injective in **both** left and right 32-byte children
    whenever both `0x01 || left(32) || right(32)` preimages lie in `pool`! -/
theorem merkleNodeHash_injective_on {sha256 : ByteArray → Bytes32} {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {l1 r1 l2 r2 : Bytes32}
    (h1 : nodePreimage l1 r1 ∈ pool)
    (h2 : nodePreimage l2 r2 ∈ pool)
    (hEq : merkleNodeHash sha256 l1 r1 = merkleNodeHash sha256 l2 r2) :
    l1 = l2 ∧ r1 = r2 := by
  have hPre := hCF (nodePreimage l1 r1) h1 (nodePreimage l2 r2) h2 hEq
  have hList : (ByteArray.mk (#[0x01] ++ l1.bytes.data ++ r1.bytes.data)).data.toList =
               (ByteArray.mk (#[0x01] ++ l2.bytes.data ++ r2.bytes.data)).data.toList :=
    congrArg (fun x => x.data.toList) hPre
  simp only [Array.toList_append, List.cons_append, List.nil_append, List.cons.injEq, true_and] at hList
  have hLen1 : l1.bytes.data.toList.length = 32 := by
    have hs := l1.size_eq
    rwa [ByteArray.size, ← Array.length_toList] at hs
  have hLen2 : l2.bytes.data.toList.length = 32 := by
    have hs := l2.size_eq
    rwa [ByteArray.size, ← Array.length_toList] at hs
  have hTake := congrArg (List.take 32) hList
  rw [List.take_left' hLen1, List.take_left' hLen2] at hTake
  have hDrop := congrArg (List.drop 32) hList
  rw [List.drop_left' hLen1, List.drop_left' hLen2] at hDrop
  have hlBytes : l1.bytes = l2.bytes := by
    cases hb1 : l1.bytes with | mk d1 =>
    cases hb2 : l2.bytes with | mk d2 =>
    rw [hb1, hb2] at hTake
    congr
    exact Array.ext' hTake
  have hrBytes : r1.bytes = r2.bytes := by
    cases hb1 : r1.bytes with | mk d1 =>
    cases hb2 : r2.bytes with | mk d2 =>
    rw [hb1, hb2] at hDrop
    congr
    exact Array.ext' hDrop
  cases l1; cases l2; cases r1; cases r2
  simp only [Bytes32.mk.injEq] at *
  exact ⟨hlBytes, hrBytes⟩

/-- Domain separation (`0x00` vs `0x01`) on `pool`: a leaf hash can NEVER collide with an internal node hash! -/
theorem merkleLeafHash_ne_nodeHash_on {sha256 : ByteArray → Bytes32} {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {leaf : ByteArray} {l r : Bytes32}
    (hLeaf : leafPreimage leaf ∈ pool)
    (hNode : nodePreimage l r ∈ pool) :
    merkleLeafHash sha256 leaf ≠ merkleNodeHash sha256 l r := by
  intro hEq
  have hPre := hCF (leafPreimage leaf) hLeaf (nodePreimage l r) hNode hEq
  have hHead := congrArg (fun b => b.data.toList.head?) hPre
  simp only [leafPreimage, nodePreimage, Array.toList_append, List.cons_append, List.nil_append,
             List.head?_cons, Option.some.injEq] at hHead
  exact absurd hHead (by decide)

/-! ### 5.3 Merkle Audit Proof Determinism & Soundness -/

/-- Bottom-up folding over concatenated direction/sibling lists decomposes cleanly (`fold(ds1 ++ ds2) = fold ds2 (fold ds1)`). -/
theorem foldMerkleProofBottomUp_append
    (sha256 : ByteArray → Bytes32)
    (cur : Bytes32)
    (ds1 ds2 : List MerkleDir)
    (ss1 ss2 : List Bytes32)
    (hLen : ds1.length = ss1.length) :
    foldMerkleProofBottomUp sha256 cur (ds1 ++ ds2) (ss1 ++ ss2) =
    match foldMerkleProofBottomUp sha256 cur ds1 ss1 with
    | some mid => foldMerkleProofBottomUp sha256 mid ds2 ss2
    | none => none := by
  induction ds1 generalizing cur ss1 with
  | nil =>
      cases ss1 with
      | nil => rfl
      | cons _ _ => exact absurd hLen (Nat.succ_ne_zero _).symm
  | cons d dsRest ih =>
      cases ss1 with
      | nil => exact absurd hLen (Nat.succ_ne_zero _)
      | cons s ssRest =>
          have hLen' : dsRest.length = ssRest.length := Nat.succ.inj hLen
          cases d <;> exact ih _ ssRest hLen'

/-- Preimage decomposition along concatenated bottom-up proof steps. -/
theorem foldProofPreimages_append
    (sha256 : ByteArray → Bytes32)
    (cur mid : Bytes32)
    (ds1 ds2 : List MerkleDir)
    (ss1 ss2 : List Bytes32)
    (hFold1 : foldMerkleProofBottomUp sha256 cur ds1 ss1 = some mid) :
    foldProofPreimages sha256 cur (ds1 ++ ds2) (ss1 ++ ss2) =
    foldProofPreimages sha256 cur ds1 ss1 ++ foldProofPreimages sha256 mid ds2 ss2 := by
  induction ds1 generalizing cur ss1 with
  | nil =>
      cases ss1 with
      | nil =>
          simp only [foldMerkleProofBottomUp, Option.some.injEq] at hFold1
          subst hFold1
          rfl
      | cons _ _ => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold1
  | cons d dsRest ih =>
      cases ss1 with
      | nil => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold1
      | cons s ssRest =>
          cases d with
          | left =>
              simp only [foldMerkleProofBottomUp] at hFold1
              simp only [List.cons_append, foldProofPreimages, ih _ ssRest hFold1]
          | right =>
              simp only [foldMerkleProofBottomUp] at hFold1
              simp only [List.cons_append, foldProofPreimages, ih _ ssRest hFold1]

/-- **PROOF DETERMINISM (ANTI-EQUIVOCATION AT ANY INDEX)**:
    Under `CollisionFreeOn sha256 pool`, for ANY fixed `(root, treeSize, leafIndex)` (even if `root` was
    adversarially chosen by a malicious host without corresponding to an honest full tree!),
    at most ONE `leafHash` (and hence at most ONE `element : ByteArray`) whose proof preimages lie in `pool`
    can ever pass `verifyMerkleLeafHashProof` / `verifyMerkleElementOpening`! -/
theorem foldMerkleProofBottomUp_unique_start
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    (dirs : List MerkleDir)
    {h1 h2 root : Bytes32}
    {sibs1 sibs2 : List Bytes32}
    (hSub1 : ∀ x, x ∈ foldProofPreimages sha256 h1 dirs sibs1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ foldProofPreimages sha256 h2 dirs sibs2 → x ∈ pool)
    (hFold1 : foldMerkleProofBottomUp sha256 h1 dirs sibs1 = some root)
    (hFold2 : foldMerkleProofBottomUp sha256 h2 dirs sibs2 = some root) :
    h1 = h2 ∧ sibs1 = sibs2 := by
  induction dirs generalizing h1 h2 sibs1 sibs2 with
  | nil =>
      cases sibs1 with
      | nil =>
          cases sibs2 with
          | nil =>
              simp only [foldMerkleProofBottomUp, Option.some.injEq] at hFold1 hFold2
              exact ⟨hFold1.trans hFold2.symm, rfl⟩
          | cons _ _ => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold2
      | cons _ _ => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold1
  | cons d dRest ih =>
      cases sibs1 with
      | nil => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold1
      | cons s1 sRest1 =>
          cases sibs2 with
          | nil => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold2
          | cons s2 sRest2 =>
              cases d with
              | left =>
                  simp only [foldMerkleProofBottomUp] at hFold1 hFold2
                  have hHead1 : nodePreimage h1 s1 ∈ pool :=
                    hSub1 _ (by simp only [foldProofPreimages, List.mem_cons, true_or])
                  have hHead2 : nodePreimage h2 s2 ∈ pool :=
                    hSub2 _ (by simp only [foldProofPreimages, List.mem_cons, true_or])
                  have hTail1 : ∀ x, x ∈ foldProofPreimages sha256 (merkleNodeHash sha256 h1 s1) dRest sRest1 → x ∈ pool :=
                    fun x hx => hSub1 x (by simp only [foldProofPreimages, List.mem_cons]; exact Or.inr hx)
                  have hTail2 : ∀ x, x ∈ foldProofPreimages sha256 (merkleNodeHash sha256 h2 s2) dRest sRest2 → x ∈ pool :=
                    fun x hx => hSub2 x (by simp only [foldProofPreimages, List.mem_cons]; exact Or.inr hx)
                  obtain ⟨hNodeEq, hSibRestEq⟩ := ih hTail1 hTail2 hFold1 hFold2
                  obtain ⟨hChildEq, hSibEq⟩ := merkleNodeHash_injective_on hCF hHead1 hHead2 hNodeEq
                  subst hChildEq hSibEq hSibRestEq
                  exact ⟨rfl, rfl⟩
              | right =>
                  simp only [foldMerkleProofBottomUp] at hFold1 hFold2
                  have hHead1 : nodePreimage s1 h1 ∈ pool :=
                    hSub1 _ (by simp only [foldProofPreimages, List.mem_cons, true_or])
                  have hHead2 : nodePreimage s2 h2 ∈ pool :=
                    hSub2 _ (by simp only [foldProofPreimages, List.mem_cons, true_or])
                  have hTail1 : ∀ x, x ∈ foldProofPreimages sha256 (merkleNodeHash sha256 s1 h1) dRest sRest1 → x ∈ pool :=
                    fun x hx => hSub1 x (by simp only [foldProofPreimages, List.mem_cons]; exact Or.inr hx)
                  have hTail2 : ∀ x, x ∈ foldProofPreimages sha256 (merkleNodeHash sha256 s2 h2) dRest sRest2 → x ∈ pool :=
                    fun x hx => hSub2 x (by simp only [foldProofPreimages, List.mem_cons]; exact Or.inr hx)
                  obtain ⟨hNodeEq, hSibRestEq⟩ := ih hTail1 hTail2 hFold1 hFold2
                  obtain ⟨hSibEq, hChildEq⟩ := merkleNodeHash_injective_on hCF hHead1 hHead2 hNodeEq
                  subst hChildEq hSibEq hSibRestEq
                  exact ⟨rfl, rfl⟩

/-- **THEOREM M1 (Leaf Hash Binding at `(root, size, index)`)**:
    Under `CollisionFreeOn sha256 pool`, any two valid Merkle leaf-hash proofs for the same `(root, size, index)`
    whose proof preimages lie in `pool` MUST open the exact same `leafHash` and identical sibling paths. -/
theorem verifyMerkleLeafHashProof_unique
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {root : Bytes32} {size idx : Nat}
    {lh1 lh2 : Bytes32} {sibs1 sibs2 : List Bytes32}
    (hSub1 : ∀ x, x ∈ proofPreimages sha256 size idx lh1 sibs1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ proofPreimages sha256 size idx lh2 sibs2 → x ∈ pool)
    (h1 : verifyMerkleLeafHashProof sha256 root size idx lh1 sibs1 = true)
    (h2 : verifyMerkleLeafHashProof sha256 root size idx lh2 sibs2 = true) :
    lh1 = lh2 ∧ sibs1 = sibs2 := by
  unfold verifyMerkleLeafHashProof at h1 h2
  dsimp only at h1 h2
  split at h1
  · contradiction
  · split at h2
    · contradiction
    · cases hf1 : foldMerkleProofBottomUp sha256 lh1 (merkleDirections size idx).reverse sibs1 with
      | none => rw [hf1] at h1; contradiction
      | some r1 =>
          rw [hf1] at h1
          cases hf2 : foldMerkleProofBottomUp sha256 lh2 (merkleDirections size idx).reverse sibs2 with
          | none => rw [hf2] at h2; contradiction
          | some r2 =>
              rw [hf2] at h2
              have hr1 : r1 = root := (bytes32Eq_iff r1 root).mp h1
              have hr2 : r2 = root := (bytes32Eq_iff r2 root).mp h2
              subst hr1 hr2
              exact foldMerkleProofBottomUp_unique_start hCF _ hSub1 hSub2 hf1 hf2

/-- **THEOREM M2 (Element Preimage Binding at `(root, size, index)`)**:
    Under `CollisionFreeOn sha256 pool`, any two valid `MerkleElementOpening`s for `(root, size, index)`
    whose `openingPreimages` lie in `pool` MUST open the exact same `ByteArray` element! -/
theorem verifyMerkleElementOpening_unique
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {root : Bytes32} {size idx : Nat}
    {op1 op2 : MerkleElementOpening}
    (hSub1 : ∀ x, x ∈ openingPreimages sha256 size idx op1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ openingPreimages sha256 size idx op2 → x ∈ pool)
    (h1 : verifyMerkleElementOpening sha256 root size idx op1 = true)
    (h2 : verifyMerkleElementOpening sha256 root size idx op2 = true) :
    op1.element = op2.element := by
  unfold verifyMerkleElementOpening at h1 h2
  simp only [Bool.and_eq_true] at h1 h2
  have hPSub1 : ∀ x, x ∈ proofPreimages sha256 size idx op1.leafHash op1.siblingsBottomUp → x ∈ pool :=
    fun x hx => hSub1 x (by simp only [openingPreimages, List.mem_cons]; exact Or.inr hx)
  have hPSub2 : ∀ x, x ∈ proofPreimages sha256 size idx op2.leafHash op2.siblingsBottomUp → x ∈ pool :=
    fun x hx => hSub2 x (by simp only [openingPreimages, List.mem_cons]; exact Or.inr hx)
  have hL1 : leafPreimage op1.element ∈ pool :=
    hSub1 _ (by simp only [openingPreimages, List.mem_cons, true_or])
  have hL2 : leafPreimage op2.element ∈ pool :=
    hSub2 _ (by simp only [openingPreimages, List.mem_cons, true_or])
  obtain ⟨hLhEq, _⟩ := verifyMerkleLeafHashProof_unique hCF hPSub1 hPSub2 h1.1 h2.1
  have hPre1 : merkleLeafHash sha256 op1.element = op1.leafHash := (bytes32Eq_iff _ _).mp h1.2
  have hPre2 : merkleLeafHash sha256 op2.element = op2.leafHash := (bytes32Eq_iff _ _).mp h2.2
  apply merkleLeafHash_injective_on hCF hL1 hL2
  rw [hPre1, hPre2, hLhEq]

/-- Helper: if `foldMerkleProofBottomUp` returns `some _`, its direction and sibling lists have equal length. -/
private theorem foldMerkleProofBottomUp_lengths_eq
    (sha256 : ByteArray → Bytes32)
    (cur res : Bytes32)
    (ds : List MerkleDir)
    (ss : List Bytes32)
    (hFold : foldMerkleProofBottomUp sha256 cur ds ss = some res) :
    ds.length = ss.length := by
  induction ds generalizing cur ss with
  | nil =>
      cases ss with
      | nil => rfl
      | cons _ _ => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold
  | cons d dRest ih =>
      cases ss with
      | nil => simp only [foldMerkleProofBottomUp, reduceCtorEq] at hFold
      | cons s sRest =>
          cases d with
          | left =>
              simp only [foldMerkleProofBottomUp] at hFold
              simp only [List.length_cons, ih _ sRest hFold]
          | right =>
              simp only [foldMerkleProofBottomUp] at hFold
              simp only [List.length_cons, ih _ sRest hFold]

/-- **THEOREM M3 (Honest Audit Proof Completeness)**:
    For every list `leaves` and every `idx < leaves.length` with `leaves[idx]? = some el`,
    `buildMerkleAuditPath sha256 leaves idx` folds `merkleLeafHash sha256 el` directly to `merkleRoot sha256 leaves`! -/
theorem buildMerkleAuditPath_complete
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (idx : Nat)
    (el : ByteArray)
    (hGet : leaves[idx]? = some el) :
    foldMerkleProofBottomUp sha256 (merkleLeafHash sha256 el)
      (merkleDirections leaves.length idx).reverse
      (buildMerkleAuditPath sha256 leaves idx) = some (merkleRoot sha256 leaves) := by
  have hIdxLt : idx < leaves.length := by
    cases Nat.lt_or_ge idx leaves.length with
    | inl h => exact h
    | inr h =>
        rw [List.getElem?_eq_none h] at hGet
        contradiction
  induction hLenEq : leaves.length using Nat.strongRecOn generalizing leaves idx with
  | ind n ih =>
      subst hLenEq
      match leaves with
      | [] => exact absurd hIdxLt (Nat.not_lt_zero _)
      | [x] =>
          have hIdx0 : idx = 0 := by
            cases idx with
            | zero => rfl
            | succ m => exact absurd (Nat.lt_of_succ_lt_succ hIdxLt) (Nat.not_lt_zero _)
          subst hIdx0
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
          subst hGet
          have hDirNil : merkleDirections 1 0 = [] := by
            rw [merkleDirections]
            have hFalse : ¬(2 ≤ 1 ∧ 0 < 1) := fun h => absurd h.1 (by decide)
            simp only [hFalse, ↓reduceDIte]
          have hPathNil : buildMerkleAuditPath sha256 [x] 0 = [] := by
            rw [buildMerkleAuditPath]
          have hRoot1 : merkleRoot sha256 [x] = merkleLeafHash sha256 x := by
            rw [merkleRoot]
          simp only [List.length_singleton, hDirNil, List.reverse_nil, hPathNil, hRoot1, foldMerkleProofBottomUp]
      | x :: y :: rest =>
          let all := x :: y :: rest
          have hGe2 : 2 ≤ all.length := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
          have hIdxAll : idx < all.length := hIdxLt
          have hk := largestPow2Lt_bounds hGe2
          let k := largestPow2Lt all.length
          have hk1 : 0 < k := hk.1
          have hk2 : k < all.length := hk.2
          cases Nat.lt_or_ge idx k with
          | inl hLeft =>
            have hTakeLen : (all.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk2)
            have hGetTake : (all.take k)[idx]? = some el := by
              rw [List.getElem?_take_of_lt hLeft]
              exact hGet
            have hIdxTake : idx < (all.take k).length := hTakeLen.symm ▸ hLeft
            have hSub := ih k hk2 (all.take k) idx hGetTake hIdxTake hTakeLen
            have hDirs : (merkleDirections all.length idx).reverse =
                (merkleDirections k idx).reverse ++ [.left] := by
              conv => lhs; rw [merkleDirections]
              simp only [hGe2, hIdxAll, and_self, ↓reduceDIte, k, hLeft, ↓reduceIte, List.reverse_cons]
            have hSibs : buildMerkleAuditPath sha256 (x :: y :: rest) idx =
                buildMerkleAuditPath sha256 (all.take k) idx ++ [merkleRoot sha256 (all.drop k)] := by
              rw [buildMerkleAuditPath]
              have hLeftRaw : idx < largestPow2Lt (x :: y :: rest).length := hLeft
              simp only [hLeftRaw, ↓reduceIte]
              rfl
            have hLenMatch : (merkleDirections k idx).reverse.length =
                (buildMerkleAuditPath sha256 (all.take k) idx).length :=
              foldMerkleProofBottomUp_lengths_eq sha256 _ _ _ _ hSub
            have hRootEq : merkleRoot sha256 (x :: y :: rest) =
                merkleNodeHash sha256 (merkleRoot sha256 (all.take k)) (merkleRoot sha256 (all.drop k)) := by
              rw [merkleRoot]
            change foldMerkleProofBottomUp sha256 (merkleLeafHash sha256 el)
              (merkleDirections all.length idx).reverse
              (buildMerkleAuditPath sha256 (x :: y :: rest) idx) =
              some (merkleRoot sha256 (x :: y :: rest))
            rw [hDirs, hSibs, foldMerkleProofBottomUp_append sha256 _ _ _ _ _ hLenMatch, hSub, hRootEq]
            rfl
          | inr hGeK =>
            have hLeft : ¬(idx < k) := Nat.not_lt.mpr hGeK
            have hDropLen : (all.drop k).length = all.length - k := List.length_drop
            have hGetDrop : (all.drop k)[idx - k]? = some el := by
              rw [List.getElem?_drop, Nat.add_sub_of_le hGeK]
              exact hGet
            have hDropLt : all.length - k < all.length :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hGe2) hk1
            have hIdxSubLt : idx - k < all.length - k :=
              Nat.sub_lt_sub_right hGeK hIdxAll
            have hIdxDropLt' : idx - k < (all.drop k).length := hDropLen.symm ▸ hIdxSubLt
            have hSub := ih (all.length - k) hDropLt (all.drop k) (idx - k) hGetDrop hIdxDropLt' hDropLen
            have hDirs : (merkleDirections all.length idx).reverse =
                (merkleDirections (all.length - k) (idx - k)).reverse ++ [.right] := by
              conv => lhs; rw [merkleDirections]
              simp only [hGe2, hIdxAll, and_self, ↓reduceDIte, k, hLeft, ↓reduceIte, List.reverse_cons]
            have hSibs : buildMerkleAuditPath sha256 (x :: y :: rest) idx =
                buildMerkleAuditPath sha256 (all.drop k) (idx - k) ++ [merkleRoot sha256 (all.take k)] := by
              rw [buildMerkleAuditPath]
              have hRightRaw : ¬(idx < largestPow2Lt (x :: y :: rest).length) := hLeft
              simp only [hRightRaw, ↓reduceIte]
              rfl
            have hLenMatch : (merkleDirections (all.length - k) (idx - k)).reverse.length =
                (buildMerkleAuditPath sha256 (all.drop k) (idx - k)).length :=
              foldMerkleProofBottomUp_lengths_eq sha256 _ _ _ _ hSub
            have hRootEq : merkleRoot sha256 (x :: y :: rest) =
                merkleNodeHash sha256 (merkleRoot sha256 (all.take k)) (merkleRoot sha256 (all.drop k)) := by
              rw [merkleRoot]
            change foldMerkleProofBottomUp sha256 (merkleLeafHash sha256 el)
              (merkleDirections all.length idx).reverse
              (buildMerkleAuditPath sha256 (x :: y :: rest) idx) =
              some (merkleRoot sha256 (x :: y :: rest))
            rw [hDirs, hSibs, foldMerkleProofBottomUp_append sha256 _ _ _ _ _ hLenMatch, hSub, hRootEq]
            rfl

/-- Every preimage hashed along the honest audit path `buildMerkleAuditPath sha256 leaves idx`
    (plus `leafPreimage el` at `leaves[idx]? = some el`) belongs to `treePreimages sha256 leaves`! -/
theorem honest_openingPreimages_subset_treePreimages
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (idx : Nat)
    (el : ByteArray)
    (hGet : leaves[idx]? = some el) :
    ∀ x, x ∈ openingPreimages sha256 leaves.length idx
      { element := el
        leafHash := merkleLeafHash sha256 el
        siblingsBottomUp := buildMerkleAuditPath sha256 leaves idx } →
      x ∈ treePreimages sha256 leaves := by
  have hIdxLt : idx < leaves.length := by
    cases Nat.lt_or_ge idx leaves.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  induction hLenEq : leaves.length using Nat.strongRecOn generalizing leaves idx with
  | ind n ih =>
      subst hLenEq
      match leaves with
      | [] => exact absurd hIdxLt (Nat.not_lt_zero _)
      | [a] =>
          have hIdx0 : idx = 0 := by
            cases idx with
            | zero => rfl
            | succ m => exact absurd (Nat.lt_of_succ_lt_succ hIdxLt) (Nat.not_lt_zero _)
          subst hIdx0
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hGet
          subst hGet
          have hDirNil : merkleDirections 1 0 = [] := by
            rw [merkleDirections]
            have hFalse : ¬(2 ≤ 1 ∧ 0 < 1) := fun h => absurd h.1 (by decide)
            simp only [hFalse, ↓reduceDIte]
          have hPathNil : buildMerkleAuditPath sha256 [a] 0 = [] := by rw [buildMerkleAuditPath]
          intro x hx
          simp only [openingPreimages, proofPreimages, List.length_singleton, hDirNil, List.reverse_nil,
                     hPathNil, foldProofPreimages, List.mem_singleton] at hx
          rw [treePreimages]
          simp only [List.mem_singleton, hx]
      | a :: b :: rest =>
          let all := a :: b :: rest
          have hGe2 : 2 ≤ all.length := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le rest.length))
          have hIdxAll : idx < all.length := hIdxLt
          have hk := largestPow2Lt_bounds hGe2
          let k := largestPow2Lt all.length
          have hk1 : 0 < k := hk.1
          have hk2 : k < all.length := hk.2
          intro x hx
          have hTreeUnfold : treePreimages sha256 (a :: b :: rest) =
              nodePreimage (merkleRoot sha256 (all.take k)) (merkleRoot sha256 (all.drop k)) ::
                (treePreimages sha256 (all.take k) ++ treePreimages sha256 (all.drop k)) := by
            rw [treePreimages]
          cases Nat.lt_or_ge idx k with
          | inl hLeft =>
            have hTakeLen : (all.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk2)
            have hGetTake : (all.take k)[idx]? = some el := by
              rw [List.getElem?_take_of_lt hLeft]; exact hGet
            have hIdxTake : idx < (all.take k).length := hTakeLen.symm ▸ hLeft
            have hSubMem := ih k hk2 (all.take k) idx hGetTake hIdxTake hTakeLen
            have hSubFold := buildMerkleAuditPath_complete sha256 (all.take k) idx el hGetTake
            rw [hTakeLen] at hSubFold
            have hDirs : (merkleDirections all.length idx).reverse =
                (merkleDirections k idx).reverse ++ [.left] := by
              conv => lhs; rw [merkleDirections]
              simp only [hGe2, hIdxAll, and_self, ↓reduceDIte, k, hLeft, ↓reduceIte, List.reverse_cons]
            have hSibs : buildMerkleAuditPath sha256 (a :: b :: rest) idx =
                buildMerkleAuditPath sha256 (all.take k) idx ++ [merkleRoot sha256 (all.drop k)] := by
              rw [buildMerkleAuditPath]
              have hLeftRaw : idx < largestPow2Lt (a :: b :: rest).length := hLeft
              simp only [hLeftRaw, ↓reduceIte]
              rfl
            simp only [openingPreimages, proofPreimages] at hx
            change x ∈ leafPreimage el ::
              foldProofPreimages sha256 (merkleLeafHash sha256 el)
                (merkleDirections all.length idx).reverse
                (buildMerkleAuditPath sha256 (a :: b :: rest) idx) at hx
            rw [hDirs, hSibs, foldProofPreimages_append sha256 _ _ _ _ _ _ hSubFold] at hx
            simp only [foldProofPreimages, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
            rw [hTreeUnfold]
            simp only [List.mem_cons, List.mem_append]
            rcases hx with rfl | hLeftProof | rfl
            · right; left
              exact hSubMem _ (by simp only [openingPreimages, List.mem_cons, true_or])
            · right; left
              exact hSubMem _ (by simp only [openingPreimages, proofPreimages, List.mem_cons]; exact Or.inr hLeftProof)
            · left; rfl
          | inr hGeK =>
            have hLeft : ¬(idx < k) := Nat.not_lt.mpr hGeK
            have hDropLen : (all.drop k).length = all.length - k := List.length_drop
            have hGetDrop : (all.drop k)[idx - k]? = some el := by
              rw [List.getElem?_drop, Nat.add_sub_of_le hGeK]; exact hGet
            have hDropLt : all.length - k < all.length :=
              Nat.sub_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) hGe2) hk1
            have hIdxDropLt : idx - k < (all.drop k).length :=
              hDropLen.symm ▸ Nat.sub_lt_sub_right hGeK hIdxAll
            have hSubMem := ih (all.length - k) hDropLt (all.drop k) (idx - k) hGetDrop hIdxDropLt hDropLen
            have hSubFold := buildMerkleAuditPath_complete sha256 (all.drop k) (idx - k) el hGetDrop
            rw [hDropLen] at hSubFold
            have hDirs : (merkleDirections all.length idx).reverse =
                (merkleDirections (all.length - k) (idx - k)).reverse ++ [.right] := by
              conv => lhs; rw [merkleDirections]
              simp only [hGe2, hIdxAll, and_self, ↓reduceDIte, k, hLeft, ↓reduceIte, List.reverse_cons]
            have hSibs : buildMerkleAuditPath sha256 (a :: b :: rest) idx =
                buildMerkleAuditPath sha256 (all.drop k) (idx - k) ++ [merkleRoot sha256 (all.take k)] := by
              rw [buildMerkleAuditPath]
              have hRightRaw : ¬(idx < largestPow2Lt (a :: b :: rest).length) := hLeft
              simp only [hRightRaw, ↓reduceIte]
              rfl
            simp only [openingPreimages, proofPreimages] at hx
            change x ∈ leafPreimage el ::
              foldProofPreimages sha256 (merkleLeafHash sha256 el)
                (merkleDirections all.length idx).reverse
                (buildMerkleAuditPath sha256 (a :: b :: rest) idx) at hx
            rw [hDirs, hSibs, foldProofPreimages_append sha256 _ _ _ _ _ _ hSubFold] at hx
            simp only [foldProofPreimages, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
            rw [hTreeUnfold]
            simp only [List.mem_cons, List.mem_append]
            rcases hx with rfl | hRightProof | rfl
            · right; right
              exact hSubMem _ (by simp only [openingPreimages, List.mem_cons, true_or])
            · right; right
              exact hSubMem _ (by simp only [openingPreimages, proofPreimages, List.mem_cons]; exact Or.inr hRightProof)
            · left; rfl

/-- Helper extracting bounds from `verifyMerkleLeafHashProof = true` without `omega` or `LawfulBEq`. -/
private theorem verifyMerkleLeafHashProof_bounds
    {sha256 : ByteArray → Bytes32}
    {root : Bytes32} {size idx : Nat} {lh : Bytes32} {sibs : List Bytes32}
    (h : verifyMerkleLeafHashProof sha256 root size idx lh sibs = true) :
    0 < size ∧ idx < size ∧ idx ≤ MAX_MERKLE_LEAF_INDEX ∧ sibs.length ≤ MAX_MERKLE_TREE_DEPTH := by
  unfold verifyMerkleLeafHashProof at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hNotBad
    have hFalse : (decide (size = 0) || decide (idx ≥ size) ||
                   decide (idx > MAX_MERKLE_LEAF_INDEX) ||
                   decide (sibs.length > MAX_MERKLE_TREE_DEPTH)) = false :=
      Bool.eq_false_iff.mpr hNotBad
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hFalse
    rcases hFalse with ⟨⟨⟨hSzNe, hNotGe⟩, hNotGtMax⟩, hNotGtDepth⟩
    refine ⟨Nat.pos_of_ne_zero hSzNe, ?_, Nat.le_of_not_lt hNotGtMax, Nat.le_of_not_lt hNotGtDepth⟩
    cases Nat.lt_or_ge idx size with
    | inl hLt => exact hLt
    | inr hGe => exact absurd hGe hNotGe

/-- **THEOREM M4 (Tree-Relative Merkle Proof Soundness)**:
    Under `CollisionFreeOn sha256 pool` where `pool` covers `treePreimages sha256 leaves` and
    `openingPreimages sha256 leaves.length idx opening`, if `root = merkleRoot sha256 leaves`,
    then ANY valid `MerkleElementOpening` against `(root, leaves.length, idx)` MUST equal the
    true committed leaf `leaves[idx]`! -/
theorem merkleProof_sound_against_committed_tree
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    (leaves : List ByteArray)
    (idx : Nat)
    (opening : MerkleElementOpening)
    (hTreeSub : ∀ x, x ∈ treePreimages sha256 leaves → x ∈ pool)
    (hOpenSub : ∀ x, x ∈ openingPreimages sha256 leaves.length idx opening → x ∈ pool)
    (hValid : verifyMerkleElementOpening sha256 (merkleRoot sha256 leaves) leaves.length idx opening = true) :
    leaves[idx]? = some opening.element := by
  have hProofValid : verifyMerkleLeafHashProof sha256 (merkleRoot sha256 leaves) leaves.length idx
      opening.leafHash opening.siblingsBottomUp = true := by
    unfold verifyMerkleElementOpening at hValid
    simp only [Bool.and_eq_true] at hValid
    exact hValid.1
  obtain ⟨hSzPos, hRange, hIdxMax, hSibDepth⟩ := verifyMerkleLeafHashProof_bounds hProofValid
  let trueEl := leaves[idx]'hRange
  have hGetTrue : leaves[idx]? = some trueEl := List.getElem?_eq_getElem hRange
  have hHonestFold := buildMerkleAuditPath_complete sha256 leaves idx trueEl hGetTrue
  -- Match depth of `buildMerkleAuditPath` to `opening.siblingsBottomUp` via `merkleDirections`!
  have hDirsEqOpeningLen : (merkleDirections leaves.length idx).reverse.length = opening.siblingsBottomUp.length := by
    unfold verifyMerkleLeafHashProof at hProofValid
    dsimp only at hProofValid
    split at hProofValid
    · contradiction
    · cases hf : foldMerkleProofBottomUp sha256 opening.leafHash (merkleDirections leaves.length idx).reverse opening.siblingsBottomUp with
      | none => rw [hf] at hProofValid; contradiction
      | some r => exact foldMerkleProofBottomUp_lengths_eq sha256 _ _ _ _ hf
  have hDirsEqHonestLen : (merkleDirections leaves.length idx).reverse.length =
      (buildMerkleAuditPath sha256 leaves idx).length :=
    foldMerkleProofBottomUp_lengths_eq sha256 _ _ _ _ hHonestFold
  have hHonestDepth : (buildMerkleAuditPath sha256 leaves idx).length ≤ MAX_MERKLE_TREE_DEPTH := by
    rw [← hDirsEqHonestLen, hDirsEqOpeningLen]
    exact hSibDepth
  have hHonestValid : verifyMerkleElementOpening sha256 (merkleRoot sha256 leaves) leaves.length idx
      { element := trueEl
        leafHash := merkleLeafHash sha256 trueEl
        siblingsBottomUp := buildMerkleAuditPath sha256 leaves idx } = true := by
    unfold verifyMerkleElementOpening verifyMerkleLeafHashProof
    have hNotBad : (decide (leaves.length = 0) || decide (idx ≥ leaves.length) ||
                    decide (idx > MAX_MERKLE_LEAF_INDEX) ||
                    decide ((buildMerkleAuditPath sha256 leaves idx).length > MAX_MERKLE_TREE_DEPTH)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨⟨⟨Nat.ne_of_gt hSzPos, Nat.not_le.mpr hRange⟩, Nat.not_lt.mpr hIdxMax⟩, Nat.not_lt.mpr hHonestDepth⟩
    simp only [hNotBad, Bool.false_eq_true, ↓reduceIte, hHonestFold, bytes32Eq_refl, Bool.and_self]
  have hHonestSub : ∀ x, x ∈ openingPreimages sha256 leaves.length idx
      { element := trueEl
        leafHash := merkleLeafHash sha256 trueEl
        siblingsBottomUp := buildMerkleAuditPath sha256 leaves idx } → x ∈ pool :=
    fun x hx => hTreeSub x (honest_openingPreimages_subset_treePreimages sha256 leaves idx trueEl hGetTrue x hx)
  have hElEq := verifyMerkleElementOpening_unique hCF hOpenSub hHonestSub hValid hHonestValid
  rw [hElEq]
  exact hGetTrue

/-! ### 5.4 Merkleized Map Soundness: Sorted Keys Forbid Duplicate Keys & Guarantee Unique Lookup Values -/

/-- Helper extracting the `i`-th opening validity from `((List.range n).zip ops).all ...`. -/
private theorem range_zip_all_get
    {α : Type} {n : Nat} {ops : List α} {P : Nat × α → Bool}
    (hLen : ops.length = n)
    (hAll : ((List.range n).zip ops).all P = true)
    {i : Nat} {op : α}
    (hGet : ops[i]? = some op) :
    P (i, op) = true := by
  have hi : i < n := by
    cases Nat.lt_or_ge i ops.length with
    | inl h => exact hLen ▸ h
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  have hRangeGet : (List.range n)[i]? = some i := by
    rw [List.getElem?_range hi]
  have hZipMem : (i, op) ∈ (List.range n).zip ops := by
    have hZipIdx : ((List.range n).zip ops)[i]? = some (i, op) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨hRangeGet, hGet⟩
    exact List.mem_of_getElem? hZipIdx
  exact List.all_eq_true.mp hAll (i, op) hZipMem

/-- Helper: if `(i, op) ∈ (List.range n).zip ops`, then `openingPreimages sha256 n i op` is a subset of
    `sortedMapOpeningsPreimages sha256 n ops`. -/
private theorem mem_foldr_openingPreimages
    {sha256 : ByteArray → Bytes32}
    {mapSize : Nat}
    {pairs : List (Nat × MerkleElementOpening)}
    {i : Nat} {op : MerkleElementOpening}
    (hMem : (i, op) ∈ pairs) :
    ∀ x, x ∈ openingPreimages sha256 mapSize i op →
      x ∈ pairs.foldr (fun (j, o) acc => openingPreimages sha256 mapSize j o ++ acc) [] := by
  induction pairs with
  | nil => cases hMem
  | cons hd tl ih =>
      intro x hx
      cases hMem with
      | head =>
          simp only [List.foldr_cons, List.mem_append]
          exact Or.inl hx
      | tail _ hTl =>
          rcases hd with ⟨j, o⟩
          simp only [List.foldr_cons, List.mem_append]
          exact Or.inr (ih hTl x hx)

private theorem openingPreimages_subset_sortedMapOpeningsPreimages
    {sha256 : ByteArray → Bytes32}
    {n : Nat} {ops : List MerkleElementOpening}
    (hLen : ops.length = n)
    {i : Nat} {op : MerkleElementOpening}
    (hGet : ops[i]? = some op) :
    ∀ x, x ∈ openingPreimages sha256 n i op → x ∈ sortedMapOpeningsPreimages sha256 n ops := by
  have hi : i < n := by
    cases Nat.lt_or_ge i ops.length with
    | inl h => exact hLen ▸ h
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  have hRangeGet : (List.range n)[i]? = some i := List.getElem?_range hi
  have hZipMem : (i, op) ∈ (List.range n).zip ops := by
    have hZipIdx : ((List.range n).zip ops)[i]? = some (i, op) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨hRangeGet, hGet⟩
    exact List.mem_of_getElem? hZipIdx
  exact mem_foldr_openingPreimages hZipMem

/-- **THEOREM M5 (Sorted Merkleized Map Has Zero Duplicate Keys)**:
    Suppose `verifySortedMerkleMapOpenings sha256 map keyOpenings = true`.
    Under `CollisionFreeOn sha256 pool` covering `sortedMapOpeningsPreimages` and the two candidate key proofs:
    For ANY PSBT key `k` and ANY two valid leaf-hash proofs at indices `i1` and `i2` against `map.keysRoot`,
    we MUST have `i1 = i2` (no key `k` can appear at two positions in `map.keysRoot`!). -/
theorem sorted_merkle_map_unique_key_index
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    {i1 i2 : Nat} {sibs1 sibs2 : List Bytes32}
    (hSortedSub : ∀ x, x ∈ sortedMapOpeningsPreimages sha256 map.size keyOpenings → x ∈ pool)
    (hLeafKey : leafPreimage key ∈ pool)
    (hProofSub1 : ∀ x, x ∈ proofPreimages sha256 map.size i1 (merkleLeafHash sha256 key) sibs1 → x ∈ pool)
    (hProofSub2 : ∀ x, x ∈ proofPreimages sha256 map.size i2 (merkleLeafHash sha256 key) sibs2 → x ∈ pool)
    (hProof1 : verifyMerkleLeafHashProof sha256 map.keysRoot map.size i1 (merkleLeafHash sha256 key) sibs1 = true)
    (hProof2 : verifyMerkleLeafHashProof sha256 map.keysRoot map.size i2 (merkleLeafHash sha256 key) sibs2 = true) :
    i1 = i2 := by
  unfold verifySortedMerkleMapOpenings at hSortedMap
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSortedMap
  rcases hSortedMap with ⟨⟨⟨_, hLen⟩, hAllOpen⟩, hStrict⟩
  obtain ⟨_, hi1, _, _⟩ := verifyMerkleLeafHashProof_bounds hProof1
  obtain ⟨_, hi2, _, _⟩ := verifyMerkleLeafHashProof_bounds hProof2
  have hi1Len : i1 < keyOpenings.length := hLen.symm ▸ hi1
  have hi2Len : i2 < keyOpenings.length := hLen.symm ▸ hi2
  let op1 := keyOpenings[i1]'hi1Len
  let op2 := keyOpenings[i2]'hi2Len
  have hGet1 : keyOpenings[i1]? = some op1 := List.getElem?_eq_getElem hi1Len
  have hGet2 : keyOpenings[i2]? = some op2 := List.getElem?_eq_getElem hi2Len
  have hBoth1 := range_zip_all_get hLen hAllOpen hGet1
  have hBoth2 := range_zip_all_get hLen hAllOpen hGet2
  simp only [Bool.and_eq_true] at hBoth1 hBoth2
  have hValOp1 : verifyMerkleElementOpening sha256 map.keysRoot map.size i1 op1 = true := hBoth1.2
  have hValOp2 : verifyMerkleElementOpening sha256 map.keysRoot map.size i2 op2 = true := hBoth2.2
  have hOpSub1 : ∀ x, x ∈ openingPreimages sha256 map.size i1 op1 → x ∈ pool :=
    fun x hx => hSortedSub x (openingPreimages_subset_sortedMapOpeningsPreimages hLen hGet1 x hx)
  have hOpSub2 : ∀ x, x ∈ openingPreimages sha256 map.size i2 op2 → x ∈ pool :=
    fun x hx => hSortedSub x (openingPreimages_subset_sortedMapOpeningsPreimages hLen hGet2 x hx)
  have hKeyOp1 : verifyMerkleElementOpening sha256 map.keysRoot map.size i1
      { element := key, leafHash := merkleLeafHash sha256 key, siblingsBottomUp := sibs1 } = true := by
    simp only [verifyMerkleElementOpening, hProof1, bytes32Eq_refl, Bool.and_self]
  have hKeyOp2 : verifyMerkleElementOpening sha256 map.keysRoot map.size i2
      { element := key, leafHash := merkleLeafHash sha256 key, siblingsBottomUp := sibs2 } = true := by
    simp only [verifyMerkleElementOpening, hProof2, bytes32Eq_refl, Bool.and_self]
  have hKeyOpSub1 : ∀ x, x ∈ openingPreimages sha256 map.size i1
      { element := key, leafHash := merkleLeafHash sha256 key, siblingsBottomUp := sibs1 } → x ∈ pool := by
    intro x hx
    simp only [openingPreimages, List.mem_cons] at hx
    rcases hx with rfl | hRest
    · exact hLeafKey
    · exact hProofSub1 x hRest
  have hKeyOpSub2 : ∀ x, x ∈ openingPreimages sha256 map.size i2
      { element := key, leafHash := merkleLeafHash sha256 key, siblingsBottomUp := sibs2 } → x ∈ pool := by
    intro x hx
    simp only [openingPreimages, List.mem_cons] at hx
    rcases hx with rfl | hRest
    · exact hLeafKey
    · exact hProofSub2 x hRest
  have hEqEl1 : key = op1.element := verifyMerkleElementOpening_unique hCF hKeyOpSub1 hOpSub1 hKeyOp1 hValOp1
  have hEqEl2 : key = op2.element := verifyMerkleElementOpening_unique hCF hKeyOpSub2 hOpSub2 hKeyOp2 hValOp2
  have hMapGet1 : (keyOpenings.map (·.element))[i1]? = some op1.element := by
    rw [List.getElem?_map, hGet1]; rfl
  have hMapGet2 : (keyOpenings.map (·.element))[i2]? = some op2.element := by
    rw [List.getElem?_map, hGet2]; rfl
  by_cases hIdxEq : i1 = i2
  · exact hIdxEq
  · exfalso
    have hNe := strictlySorted_pairwise_distinct hStrict hIdxEq hMapGet1 hMapGet2
    exact hNe (hEqEl1.symm.trans hEqEl2)

/-- **THEOREM M6 (Finite-Pool Collision-Relative Merkleized Map Value Uniqueness — Anti-Equivocation)**:
    Under `CollisionFreeOn sha256 pool` covering `sortedMapOpeningsPreimages` and `mapLookupProofPreimages`,
    once a `MerkleMapCommitment` passes sorted-keys verification (`verifySortedMerkleMapOpenings`),
    at most ONE value `v : ByteArray` can EVER be proven for any key `k`! -/
theorem sorted_merkle_map_lookup_proof_unique
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    {p1 p2 : MapLookupProof}
    (hSortedSub : ∀ x, x ∈ sortedMapOpeningsPreimages sha256 map.size keyOpenings → x ∈ pool)
    (hSub1 : ∀ x, x ∈ mapLookupProofPreimages sha256 map key p1 → x ∈ pool)
    (hSub2 : ∀ x, x ∈ mapLookupProofPreimages sha256 map key p2 → x ∈ pool)
    (hLookup1 : verifyMapLookupProof sha256 map key p1 = true)
    (hLookup2 : verifyMapLookupProof sha256 map key p2 = true) :
    p1.index = p2.index ∧ p1.valueOpening.element = p2.valueOpening.element := by
  unfold verifyMapLookupProof at hLookup1 hLookup2
  simp only [Bool.and_eq_true] at hLookup1 hLookup2
  have hLeafKey : leafPreimage key ∈ pool :=
    hSub1 _ (by simp only [mapLookupProofPreimages, List.mem_cons, true_or])
  have hKSub1 : ∀ x, x ∈ proofPreimages sha256 map.size p1.index (merkleLeafHash sha256 key) p1.keySiblingsBottomUp → x ∈ pool :=
    fun x hx => hSub1 x (by simp only [mapLookupProofPreimages, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hx))
  have hKSub2 : ∀ x, x ∈ proofPreimages sha256 map.size p2.index (merkleLeafHash sha256 key) p2.keySiblingsBottomUp → x ∈ pool :=
    fun x hx => hSub2 x (by simp only [mapLookupProofPreimages, List.mem_cons, List.mem_append]; exact Or.inr (Or.inl hx))
  have hVSub1 : ∀ x, x ∈ openingPreimages sha256 map.size p1.index p1.valueOpening → x ∈ pool :=
    fun x hx => hSub1 x (by simp only [mapLookupProofPreimages, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hx))
  have hVSub2 : ∀ x, x ∈ openingPreimages sha256 map.size p2.index p2.valueOpening → x ∈ pool :=
    fun x hx => hSub2 x (by simp only [mapLookupProofPreimages, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr hx))
  have hIdxEq := sorted_merkle_map_unique_key_index hCF hSortedMap hSortedSub hLeafKey hKSub1 hKSub2 hLookup1.1 hLookup2.1
  rw [hIdxEq] at hLookup1 hVSub1
  have hValEq := verifyMerkleElementOpening_unique hCF hVSub1 hVSub2 hLookup1.2 hLookup2.2
  exact ⟨hIdxEq, hValEq⟩

/-- **THEOREM M7 (Interactive Untrusted-Host Oracle Lookup Soundness)**:
    Under `CollisionFreeOn sha256 pool` and `verifySortedMerkleMapOpenings`, even if TWO DIFFERENT
    malicious/adaptive untrusted host oracles `host1` and `host2` interact with `deviceLookupMerkleMapValue`
    for the same committed `(map, key)`, if `host1` yields `.present v1` and `host2` yields `.present v2`,
    then `v1 = v2`! A compromised host CANNOT equivocate on the value of any PSBT key! -/
theorem interactive_host_cannot_equivocate_map_value
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCF : CollisionFreeOn sha256 pool)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    (host1 host2 : UntrustedHostOracle)
    (key v1 v2 : ByteArray)
    (hSortedSub : ∀ x, x ∈ sortedMapOpeningsPreimages sha256 map.size keyOpenings → x ∈ pool)
    (hHostSub1 : ∀ x, x ∈ hostLookupPreimages sha256 host1 map key → x ∈ pool)
    (hHostSub2 : ∀ x, x ∈ hostLookupPreimages sha256 host2 map key → x ∈ pool)
    (hRes1 : deviceLookupMerkleMapValue sha256 host1 map key = .present v1)
    (hRes2 : deviceLookupMerkleMapValue sha256 host2 map key = .present v2) :
    v1 = v2 := by
  have extractProof : ∀ (host : UntrustedHostOracle) (v : ByteArray),
      (∀ x, x ∈ hostLookupPreimages sha256 host map key → x ∈ pool) →
      deviceLookupMerkleMapValue sha256 host map key = .present v →
      ∃ p : MapLookupProof,
        p.valueOpening.element = v ∧
        verifyMapLookupProof sha256 map key p = true ∧
        (∀ x, x ∈ mapLookupProofPreimages sha256 map key p → x ∈ pool) := by
    intro host v hHSub hRes
    unfold deviceLookupMerkleMapValue at hRes
    dsimp only at hRes
    split at hRes
    · contradiction
    · cases hIdxQ : host.queryLeafIndex map.keysRoot (merkleLeafHash sha256 key) with
      | none => rw [hIdxQ] at hRes; contradiction
      | some pair =>
          rcases pair with ⟨found, idx⟩
          rw [hIdxQ] at hRes
          simp only at hRes
          split at hRes
          · contradiction
          · split at hRes
            · contradiction
            · cases hKeyP : host.queryLeafProof map.keysRoot map.size idx with
              | none => rw [hKeyP] at hRes; contradiction
              | some kp =>
                  rcases kp with ⟨retKh, keySibs⟩
                  rw [hKeyP] at hRes
                  simp only at hRes
                  split at hRes
                  · contradiction
                  · rename_i hKhNotNe
                    have hKhEq : retKh = merkleLeafHash sha256 key := by
                      cases hB : bytes32Eq retKh (merkleLeafHash sha256 key)
                      · rw [hB] at hKhNotNe; exact False.elim (hKhNotNe rfl)
                      · exact (bytes32Eq_iff _ _).mp hB
                    subst hKhEq
                    split at hRes
                    · contradiction
                    · rename_i hKeyValid
                      have hKeyValidTrue : verifyMerkleLeafHashProof sha256 map.keysRoot map.size idx
                          (merkleLeafHash sha256 key) keySibs = true := by
                        cases hV : verifyMerkleLeafHashProof sha256 map.keysRoot map.size idx (merkleLeafHash sha256 key) keySibs
                        · rw [hV] at hKeyValid; exact False.elim (hKeyValid rfl)
                        · rfl
                      cases hValFetch : deviceFetchLeafElement sha256 host map.valuesRoot map.size idx with
                      | none => rw [hValFetch] at hRes; contradiction
                      | some valBytes =>
                          rw [hValFetch] at hRes
                          injection hRes with hValEq
                          subst hValEq
                          unfold deviceFetchLeafElement at hValFetch
                          cases hValP : host.queryLeafProof map.valuesRoot map.size idx with
                          | none => rw [hValP] at hValFetch; contradiction
                          | some vp =>
                              rcases vp with ⟨valLh, valSibs⟩
                              rw [hValP] at hValFetch
                              simp only at hValFetch
                              split at hValFetch
                              · contradiction
                              · rename_i hValHashProofNotFalse
                                have hValHashProof : verifyMerkleLeafHashProof sha256 map.valuesRoot map.size idx valLh valSibs = true := by
                                  cases hV : verifyMerkleLeafHashProof sha256 map.valuesRoot map.size idx valLh valSibs
                                  · rw [hV] at hValHashProofNotFalse; exact False.elim (hValHashProofNotFalse rfl)
                                  · rfl
                                cases hPre : host.queryPreimage valLh with
                                | none => rw [hPre] at hValFetch; contradiction
                                | some rawPre =>
                                    rw [hPre] at hValFetch
                                    dsimp only at hValFetch
                                    have hPreVer : verifyMerkleLeafPreimage sha256 valLh rawPre = some valBytes := hValFetch
                                    unfold verifyMerkleLeafPreimage at hValFetch
                                    split at hValFetch
                                    · contradiction
                                    · cases hList : rawPre.data.toList with
                                      | nil => rw [hList] at hValFetch; contradiction
                                      | cons b0 rest =>
                                          rw [hList] at hValFetch
                                          by_cases hb0 : b0 = 0x00
                                          · subst hb0
                                            simp only at hValFetch
                                            split at hValFetch
                                            · contradiction
                                            · rename_i hShaMatch
                                              injection hValFetch with hExtractEq
                                              have hShaEq : sha256 rawPre = valLh := by
                                                cases hB : bytes32Eq (sha256 rawPre) valLh
                                                · rw [hB] at hShaMatch; exact False.elim (hShaMatch rfl)
                                                · exact (bytes32Eq_iff _ _).mp hB
                                              have hRawDecomp : leafPreimage valBytes = rawPre := by
                                                rw [← hExtractEq]
                                                unfold leafPreimage
                                                cases rawPre with | mk data =>
                                                congr
                                                apply Array.ext'
                                                simpa using hList.symm
                                              let prf : MapLookupProof := {
                                                index := idx
                                                keySiblingsBottomUp := keySibs
                                                valueOpening := {
                                                  element := valBytes
                                                  leafHash := valLh
                                                  siblingsBottomUp := valSibs
                                                }
                                              }
                                              refine ⟨prf, rfl, ?_, ?_⟩
                                              · unfold verifyMapLookupProof verifyMerkleElementOpening
                                                have hLeafEq : merkleLeafHash sha256 valBytes = valLh := by
                                                  unfold merkleLeafHash
                                                  rw [hRawDecomp, hShaEq]
                                                simp only [prf, hKeyValidTrue, hValHashProof, hLeafEq, bytes32Eq_refl, Bool.and_self]
                                              · intro x hx
                                                apply hHSub x
                                                unfold hostLookupPreimages
                                                simp only [hIdxQ, hKeyP, hValP, hPre, hPreVer,
                                                           List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
                                                simp only [mapLookupProofPreimages, openingPreimages, prf,
                                                           List.mem_cons, List.mem_append] at hx
                                                rcases hx with rfl | hK | rfl | hV
                                                · exact Or.inl (Or.inl rfl)
                                                · exact Or.inl (Or.inr hK)
                                                · exact Or.inr (Or.inl (Or.inl rfl))
                                                · exact Or.inr (Or.inr hV)
                                          · have hImpossible : (match b0 :: rest with
                                                | 0x00 :: rest =>
                                                    if !bytes32Eq (sha256 rawPre) valLh then none else some (ByteArray.mk rest.toArray)
                                                | _ => none) = none := by
                                              split
                                              · rename_i rest' hEqCons
                                                injection hEqCons with hB0Zero _
                                                exact absurd hB0Zero hb0
                                              · rfl
                                            rw [hImpossible] at hValFetch
                                            contradiction
  obtain ⟨p1, hp1El, hp1Ok, hp1Sub⟩ := extractProof host1 v1 hHostSub1 hRes1
  obtain ⟨p2, hp2El, hp2Ok, hp2Sub⟩ := extractProof host2 v2 hHostSub2 hRes2
  obtain ⟨_, hEq⟩ := sorted_merkle_map_lookup_proof_unique hCF hSortedMap hSortedSub hp1Sub hp2Sub hp1Ok hp2Ok
  rw [← hp1El, ← hp2El, hEq]

/-- **THEOREM M8 (Key-Callback Presence Completeness — Preventing Host Lying-By-Omission)**:
    If `key ∈ keyOpenings.map (·.element)` was observed during the verified sorted-keys scan, then ANY
    host returning `.absentClaimed` (`found = 0`) for `key` is provably lying (`∃ idx < map.size` where
    `key` has a valid opening in `map.keysRoot` and `key.size ≤ MAX_MERKLE_MAP_KEY_SIZE`)! -/
theorem verified_key_scan_detects_omission
    {sha256 : ByteArray → Bytes32}
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    (hSeenInScan : key ∈ keyOpenings.map (·.element)) :
    ∃ (idx : Nat) (op : MerkleElementOpening),
      idx < map.size ∧
      op.element = key ∧
      op.element.size ≤ MAX_MERKLE_MAP_KEY_SIZE ∧
      verifyMerkleElementOpening sha256 map.keysRoot map.size idx op = true := by
  unfold verifySortedMerkleMapOpenings at hSortedMap
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSortedMap
  rcases hSortedMap with ⟨⟨⟨_, hLen⟩, hAllOpen⟩, _⟩
  rw [List.mem_map] at hSeenInScan
  rcases hSeenInScan with ⟨op, hOpMem, hOpEl⟩
  obtain ⟨idx, hIdxLt, hGetIdx⟩ := List.mem_iff_getElem.mp hOpMem
  have hGetOpt : keyOpenings[idx]? = some op := by
    rw [List.getElem?_eq_getElem hIdxLt]
    exact congrArg some hGetIdx
  have hBoth := range_zip_all_get hLen hAllOpen hGetOpt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hBoth
  exact ⟨idx, op, hLen ▸ hIdxLt, hOpEl, hBoth.1, hBoth.2⟩

/-- **THEOREM M9 (Duplicate Keys Unconditionally Rejected by `verifySortedMerkleMapOpenings`)**:
    Any `keyOpenings` list containing the same key at two distinct positions `i ≠ j` is unconditionally
    rejected (`verifySortedMerkleMapOpenings = false`). -/
theorem duplicate_keys_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    {i j : Nat} {op1 op2 : MerkleElementOpening}
    (hNe : i ≠ j)
    (hi : keyOpenings[i]? = some op1)
    (hj : keyOpenings[j]? = some op2)
    (hSameKey : op1.element = op2.element) :
    verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  cases hV : verifySortedMerkleMapOpenings sha256 map keyOpenings
  · rfl
  · exfalso
    unfold verifySortedMerkleMapOpenings at hV
    simp only [Bool.and_eq_true] at hV
    have hStrict := hV.2
    have hMap1 : (keyOpenings.map (·.element))[i]? = some op1.element := by
      rw [List.getElem?_map, hi]; rfl
    have hMap2 : (keyOpenings.map (·.element))[j]? = some op2.element := by
      rw [List.getElem?_map, hj]; rfl
    exact strictlySorted_pairwise_distinct hStrict hNe hMap1 hMap2 hSameKey

/-- **THEOREM M10 (Out-of-Bounds or Overflowing Leaf Index Unconditionally Rejected in `deviceLookupMerkleMapValue`)**:
    If a malicious host responds to `CCMD_GET_MERKLE_LEAF_INDEX` with `idx >= map.size` OR `idx > MAX_MERKLE_LEAF_INDEX`
    (even with `found = false`!), `deviceLookupMerkleMapValue` rejects with `.protocolError`, matching `get_merkle_leaf_index.c:34`. -/
theorem out_of_bounds_index_rejected
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (found : Bool)
    (idx : Nat)
    (hHost : host.queryLeafIndex map.keysRoot (merkleLeafHash sha256 key) = some (found, idx))
    (hOob : idx ≥ map.size ∨ idx > MAX_MERKLE_LEAF_INDEX) :
    deviceLookupMerkleMapValue sha256 host map key = .protocolError := by
  unfold deviceLookupMerkleMapValue
  dsimp only
  split
  · rfl
  · rw [hHost]
    simp only
    rcases hOob with hGe | hGt
    · simp only [decide_eq_true hGe, Bool.or_true, ↓reduceIte]
    · simp only [decide_eq_true hGt, Bool.true_or, ↓reduceIte]

/-! ### 5.5 BOLOS Bounds & `0xE000` Streaming Preimage Soundness / Rejection Theorems (`Audit M-03 & m-04`) -/

/-- BOLOS Depth Cap Theorem (`MAX_MERKLE_TREE_DEPTH = 32`): any proof with `> 32` sibling hashes is rejected. -/
theorem depth_gt_32_rejected
    (sha256 : ByteArray → Bytes32)
    (root : Bytes32) (size idx : Nat) (lh : Bytes32) (sibs : List Bytes32)
    (hDepth : sibs.length > MAX_MERKLE_TREE_DEPTH) :
    verifyMerkleLeafHashProof sha256 root size idx lh sibs = false := by
  unfold verifyMerkleLeafHashProof
  simp only [decide_eq_true hDepth, Bool.or_true, ↓reduceIte]

/-- BOLOS Key Size Cap Theorem (`MAX_MERKLE_MAP_KEY_SIZE = 128`): any sorted map opening with a key `> 128` bytes is rejected. -/
theorem oversized_map_key_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    {i : Nat} {op : MerkleElementOpening}
    (hi : keyOpenings[i]? = some op)
    (hOver : op.element.size > MAX_MERKLE_MAP_KEY_SIZE) :
    verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  cases hV : verifySortedMerkleMapOpenings sha256 map keyOpenings
  · rfl
  · exfalso
    unfold verifySortedMerkleMapOpenings at hV
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hV
    rcases hV with ⟨⟨⟨_, hLen⟩, hAll⟩, _⟩
    have hBoth := range_zip_all_get hLen hAll hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hBoth
    exact absurd hOver (Nat.not_lt.mpr hBoth.1)

/-- Empty-Map Zero-Roots Enforcement: `verifySortedMerkleMapOpenings` rejects `map.size = 0` unless both roots are `zeroBytes32`. -/
theorem empty_map_nonzero_root_rejected
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening)
    (hZeroSz : map.size = 0)
    (hNonZero : map.keysRoot ≠ zeroBytes32 ∨ map.valuesRoot ≠ zeroBytes32) :
    verifySortedMerkleMapOpenings sha256 map keyOpenings = false := by
  cases hV : verifySortedMerkleMapOpenings sha256 map keyOpenings
  · rfl
  · exfalso
    unfold verifySortedMerkleMapOpenings at hV
    have hDecZero : decide (map.size = 0) = true := decide_eq_true hZeroSz
    rw [hDecZero] at hV
    simp only [↓reduceIte, Bool.and_eq_true, bytes32Eq_iff] at hV
    rcases hV with ⟨⟨⟨⟨hK, hVal⟩, _⟩, _⟩, _⟩
    rcases hNonZero with hNeK | hNeV
    · exact hNeK hK
    · exact hNeV hVal

/-- Raw Preimage Soundness (`get_preimage.c`): if `verifyRawPreimage sha256 expected raw = some out`,
    then `out = raw`, `1 ≤ out.size ≤ MAX_PREIMAGE_TOTAL_SIZE`, and `sha256 out = expected` (with NO `0x00` prefix stripped). -/
theorem verifyRawPreimage_sound
    {sha256 : ByteArray → Bytes32}
    {expected : Bytes32}
    {raw out : ByteArray}
    (hOk : verifyRawPreimage sha256 expected raw = some out) :
    out = raw ∧ 1 ≤ out.size ∧ out.size ≤ MAX_PREIMAGE_TOTAL_SIZE ∧ sha256 out = expected := by
  unfold verifyRawPreimage at hOk
  split at hOk
  · contradiction
  · rename_i hLenOk
    have hLenFalse : (decide (raw.size = 0) || decide (raw.size > MAX_PREIMAGE_TOTAL_SIZE)) = false :=
      Bool.eq_false_iff.mpr hLenOk
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hLenFalse
    split at hOk
    · contradiction
    · rename_i hEqOk
      injection hOk with hOutEq
      rw [← hOutEq]
      have hDigest : sha256 raw = expected := by
        cases hB : bytes32Eq (sha256 raw) expected
        · rw [hB] at hEqOk; exact False.elim (hEqOk rfl)
        · exact (bytes32Eq_iff _ _).mp hB
      exact ⟨rfl, Nat.pos_of_ne_zero hLenFalse.1, Nat.le_of_not_lt hLenFalse.2, hDigest⟩

/-- Helper lemma: `foldPreimageChunks rem acc chunks = .ok out` implies `out.size = acc.size + rem`
    and every continuation frame obeyed `CLA=0xF8, INS=0x01`, `elementSize = 1`, and `1 ≤ nElements ≤ 255`. -/
theorem foldPreimageChunks_sound
    {rem : Nat} {acc out : ByteArray} {chunks : List MoreElementsChunk}
    (hFold : foldPreimageChunks rem acc chunks = .ok out) :
    out.size = acc.size + rem ∧
    ∀ c ∈ chunks,
      validateContinuationApdu c.continuation = true ∧
      c.elementSize = 1 ∧
      1 ≤ c.nElements ∧ c.nElements ≤ MAX_MORE_ELEMENTS_COUNT ∧
      c.chunkData.size = c.nElements := by
  induction chunks generalizing rem acc with
  | nil =>
      unfold foldPreimageChunks at hFold
      split at hFold
      · rename_i hRem0
        injection hFold with hEq
        subst hEq
        have hr : rem = 0 := of_decide_eq_true hRem0
        subst hr
        exact ⟨Nat.add_zero _, fun _ hm => False.elim (List.not_mem_nil hm)⟩
      · contradiction
  | cons c rest ih =>
      unfold foldPreimageChunks at hFold
      split at hFold
      · contradiction
      · rename_i hHdrNotFalse
        have hHdr : validateContinuationApdu c.continuation = true := by
          cases hB : validateContinuationApdu c.continuation
          · rw [hB] at hHdrNotFalse; exact False.elim (hHdrNotFalse rfl)
          · rfl
        split at hFold
        · contradiction
        · rename_i hElWidthNot
          have hElWidth : c.elementSize = 1 := by
            by_cases hEq1 : c.elementSize = 1
            · exact hEq1
            · exact False.elim (hElWidthNot (decide_eq_true hEq1))
          split at hFold
          · contradiction
          · rename_i hCntNotBad
            have hCntFalse : (decide (c.nElements = 0) || decide (c.nElements > MAX_MORE_ELEMENTS_COUNT)) = false :=
              Bool.eq_false_iff.mpr hCntNotBad
            simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hCntFalse
            split at hFold
            · contradiction
            · rename_i hSzNotBad
              have hChunkSz : c.chunkData.size = c.nElements := by
                by_cases hEqSz : c.chunkData.size = c.nElements
                · exact hEqSz
                · exact False.elim (hSzNotBad (decide_eq_true hEqSz))
              split at hFold
              · contradiction
              · rename_i hRemNotOver
                have hLeRem : c.nElements ≤ rem := Nat.le_of_not_lt (fun hGt => hRemNotOver (decide_eq_true hGt))
                obtain ⟨hRecSz, hRecAll⟩ := ih hFold
                have hAppSz : (acc ++ c.chunkData).size = acc.size + c.nElements := by
                  rw [ByteArray.size_append, hChunkSz]
                have hTotalSz : out.size = acc.size + rem := by
                  rw [hRecSz, hAppSz, Nat.add_assoc, Nat.add_comm c.nElements, Nat.sub_add_cancel hLeRem]
                refine ⟨hTotalSz, ?_⟩
                intro x hx
                cases hx with
                | head =>
                    exact ⟨hHdr, hElWidth, Nat.pos_of_ne_zero hCntFalse.1, Nat.le_of_not_lt hCntFalse.2, hChunkSz⟩
                | tail _ hxRest =>
                    exact hRecAll x hxRest

/-- Streaming Raw Preimage Soundness (`stream_preimage.c` / `get_preimage.c`):
    Whenever `streamVerifyRawPreimage sha256 expected init chunks = .ok out`:
    1. `init.continuation` and every chunk continuation passed `validateContinuationApdu` (`CLA=0xF8, INS=0x01`),
    2. `init.partialData.size ≤ 255` and `1 ≤ init.declaredTotalSize ≤ 0xFFFFFFFF`,
    3. Every `CCMD_GET_MORE_ELEMENTS` chunk had `elementSize = 1` and `1 ≤ nElements ≤ 255`,
    4. Exact total byte count `out.size = init.declaredTotalSize` was received, and
    5. Final digest matched `sha256 out = expected` (`verifyRawPreimage sha256 expected out = some out`)! -/
theorem streamVerifyRawPreimage_sound
    {sha256 : ByteArray → Bytes32}
    {expected : Bytes32}
    {init : PreimageInitFrame}
    {chunks : List MoreElementsChunk}
    {out : ByteArray}
    (hOk : streamVerifyRawPreimage sha256 expected init chunks = .ok out) :
    validateContinuationApdu init.continuation = true ∧
    1 ≤ init.declaredTotalSize ∧ init.declaredTotalSize ≤ MAX_PREIMAGE_TOTAL_SIZE ∧
    init.partialData.size ≤ MAX_PREIMAGE_PARTIAL_SIZE ∧
    out.size = init.declaredTotalSize ∧
    sha256 out = expected ∧
    verifyRawPreimage sha256 expected out = some out := by
  unfold streamVerifyRawPreimage at hOk
  split at hOk
  · contradiction
  · rename_i hInitHdrNotFalse
    have hInitHdr : validateContinuationApdu init.continuation = true := by
      cases hB : validateContinuationApdu init.continuation
      · rw [hB] at hInitHdrNotFalse; exact False.elim (hInitHdrNotFalse rfl)
      · rfl
    split at hOk
    · contradiction
    · rename_i hDeclOk
      have hDeclFalse : (decide (init.declaredTotalSize = 0) || decide (init.declaredTotalSize > MAX_PREIMAGE_TOTAL_SIZE)) = false :=
        Bool.eq_false_iff.mpr hDeclOk
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hDeclFalse
      split at hOk
      · contradiction
      · rename_i hPartOk
        have hPartFalse : (decide (init.partialData.size > MAX_PREIMAGE_PARTIAL_SIZE) ||
                           decide (init.partialData.size > init.declaredTotalSize)) = false :=
          Bool.eq_false_iff.mpr hPartOk
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hPartFalse
        cases hFold : foldPreimageChunks (init.declaredTotalSize - init.partialData.size) init.partialData chunks with
        | error e => rw [hFold] at hOk; contradiction
        | ok assembled =>
            rw [hFold] at hOk
            simp only at hOk
            split at hOk
            · contradiction
            · rename_i hDigestNotFalse
              injection hOk with hOutEq
              rw [← hOutEq]
              have hDigest : sha256 assembled = expected := by
                cases hB : bytes32Eq (sha256 assembled) expected
                · rw [hB] at hDigestNotFalse; exact False.elim (hDigestNotFalse rfl)
                · exact (bytes32Eq_iff _ _).mp hB
              obtain ⟨hSzFold, _⟩ := foldPreimageChunks_sound hFold
              have hPartLeDecl : init.partialData.size ≤ init.declaredTotalSize := Nat.le_of_not_lt hPartFalse.2
              have hOutSz : assembled.size = init.declaredTotalSize := by
                rw [hSzFold, Nat.add_comm, Nat.sub_add_cancel hPartLeDecl]
              have hDeclPos : 1 ≤ init.declaredTotalSize := Nat.pos_of_ne_zero hDeclFalse.1
              have hDeclMax : init.declaredTotalSize ≤ MAX_PREIMAGE_TOTAL_SIZE := Nat.le_of_not_lt hDeclFalse.2
              have hRawOk : verifyRawPreimage sha256 expected assembled = some assembled := by
                unfold verifyRawPreimage
                have hOutNe0 : ¬(assembled.size = 0) := by rw [hOutSz]; exact hDeclFalse.1
                have hOutNotGt : ¬(assembled.size > MAX_PREIMAGE_TOTAL_SIZE) := by rw [hOutSz]; exact hDeclFalse.2
                simp only [decide_eq_false hOutNe0, decide_eq_false hOutNotGt, Bool.or_self,
                           Bool.false_eq_true, ↓reduceIte, hDigest, bytes32Eq_refl, Bool.not_true]
              exact ⟨hInitHdr, hDeclPos, hDeclMax, Nat.le_of_not_lt hPartFalse.1, hOutSz, hDigest, hRawOk⟩

/-- Streaming Merkle Leaf Preimage Soundness (`get_merkle_preimage.c`):
    Whenever `streamVerifyMerkleLeafPreimage sha256 expectedLeafHash init chunks = .ok leafBytes`,
    `merkleLeafHash sha256 leafBytes = expectedLeafHash`! -/
theorem streamVerifyMerkleLeafPreimage_sound
    {sha256 : ByteArray → Bytes32}
    {expectedLeafHash : Bytes32}
    {init : PreimageInitFrame}
    {chunks : List MoreElementsChunk}
    {leafBytes : ByteArray}
    (hOk : streamVerifyMerkleLeafPreimage sha256 expectedLeafHash init chunks = .ok leafBytes) :
    merkleLeafHash sha256 leafBytes = expectedLeafHash := by
  unfold streamVerifyMerkleLeafPreimage at hOk
  cases hRaw : streamVerifyRawPreimage sha256 expectedLeafHash init chunks with
  | error e => rw [hRaw] at hOk; contradiction
  | ok assembled =>
      rw [hRaw] at hOk
      simp only at hOk
      obtain ⟨_, _, _, _, _, hDigest, _⟩ := streamVerifyRawPreimage_sound hRaw
      cases hList : assembled.data.toList with
      | nil => rw [hList] at hOk; contradiction
      | cons b0 rest =>
          rw [hList] at hOk
          by_cases hb0 : b0 = 0x00
          · subst hb0
            injection hOk with hLeafEq
            subst hLeafEq
            have hAssembledEq : leafPreimage (ByteArray.mk rest.toArray) = assembled := by
              unfold leafPreimage
              cases assembled with | mk data =>
              congr
              apply Array.ext'
              simpa using hList.symm
            unfold merkleLeafHash
            rw [hAssembledEq, hDigest]
          · have hBad : (match b0 :: rest with
                | 0x00 :: rest => Except.ok (ByteArray.mk rest.toArray)
                | _ => Except.error PreimageStreamError.missingMerkleLeafPrefix) =
                Except.error PreimageStreamError.missingMerkleLeafPrefix := by
              split
              · rename_i rest' hCons
                injection hCons with hZero _
                exact absurd hZero hb0
              · rfl
            rw [hBad] at hOk
            contradiction

/-- Rejection of Non-Continuation APDU Headers (`dispatcher.c:108`):
    Any initial preimage frame whose APDU header is not `CLA=0xF8, INS=0x01, P1=0, P2=0` is rejected with `.badContinuationHeader`. -/
theorem streamPreimage_rejects_bad_continuation
    (sha256 : ByteArray → Bytes32)
    (expected : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk)
    (hBad : init.continuation.cla ≠ CLA_FRAMEWORK ∨ init.continuation.ins ≠ INS_CONTINUE) :
    streamVerifyRawPreimage sha256 expected init chunks = .error .badContinuationHeader := by
  unfold streamVerifyRawPreimage
  have hHdrFalse : validateContinuationApdu init.continuation = false := by
    unfold validateContinuationApdu
    rcases hBad with hCla | hIns
    · simp only [decide_eq_false hCla, Bool.false_and]
    · simp only [decide_eq_false hIns, Bool.and_false, Bool.false_and]
  simp only [hHdrFalse, Bool.not_false, ↓reduceIte]

/-- Rejection of Oversized Initial Slice (`partialData.size > 255` in `CCMD_GET_PREIMAGE = 0x40`): -/
theorem streamPreimage_rejects_oversized_partial_slice
    (sha256 : ByteArray → Bytes32)
    (expected : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk)
    (hHdr : validateContinuationApdu init.continuation = true)
    (hDecl : 1 ≤ init.declaredTotalSize ∧ init.declaredTotalSize ≤ MAX_PREIMAGE_TOTAL_SIZE)
    (hOver : init.partialData.size > MAX_PREIMAGE_PARTIAL_SIZE) :
    streamVerifyRawPreimage sha256 expected init chunks = .error .invalidPartialSliceLength := by
  unfold streamVerifyRawPreimage
  have hNe0 : ¬(init.declaredTotalSize = 0) := Nat.ne_of_gt hDecl.1
  have hNotGt : ¬(init.declaredTotalSize > MAX_PREIMAGE_TOTAL_SIZE) := Nat.not_lt.mpr hDecl.2
  simp only [hHdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
             decide_eq_false hNe0, decide_eq_false hNotGt, Bool.or_self,
             decide_eq_true hOver, Bool.true_or]

/-- Rejection of Empty (`nElements = 0`) or Oversized (`nElements > 255`) `CCMD_GET_MORE_ELEMENTS (0xA0)` Chunks
    (prevents host-induced infinite streaming loops on device!). -/
theorem foldPreimageChunks_rejects_empty_or_oversized_chunk
    (rem : Nat) (acc : ByteArray) (c : MoreElementsChunk) (rest : List MoreElementsChunk)
    (hHdr : validateContinuationApdu c.continuation = true)
    (hWidth : c.elementSize = 1)
    (hBadCnt : c.nElements = 0 ∨ c.nElements > MAX_MORE_ELEMENTS_COUNT) :
    foldPreimageChunks rem acc (c :: rest) = .error .invalidChunkElementCount := by
  unfold foldPreimageChunks
  have hNotNe1 : ¬(c.elementSize ≠ 1) := fun h => h hWidth
  simp only [hHdr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, decide_eq_false hNotNe1]
  rcases hBadCnt with hZero | hGt
  · simp only [decide_eq_true hZero, Bool.true_or, ↓reduceIte]
  · simp only [decide_eq_true hGt, Bool.or_true, ↓reduceIte]

/-! ### 5.6 Constructive Non-Vacuity Witnesses (`0 sorryAx`, `0 Classical.choice`, `0 ofReduceBool`) -/

/-- Decidable finite-pool collision check: verifies constructively that every pair `(a, b)` in `pool`
    with equal digests `bytes32Eq (sha256 a) (sha256 b)` has identical bytes `merkleBytesEq a b`. -/
def checkCollisionFreeOn (sha256 : ByteArray → Bytes32) (pool : List ByteArray) : Bool :=
  pool.all fun a =>
    pool.all fun b =>
      !bytes32Eq (sha256 a) (sha256 b) || merkleBytesEq a b

/-- Constructive reflection theorem: `checkCollisionFreeOn sha256 pool = true` implies `CollisionFreeOn sha256 pool`
    with `0 Classical.choice` and `0 ofReduceBool`! -/
theorem collisionFreeOn_of_check
    {sha256 : ByteArray → Bytes32}
    {pool : List ByteArray}
    (hCheck : checkCollisionFreeOn sha256 pool = true) :
    CollisionFreeOn sha256 pool := by
  intro a ha b hb hDigestEq
  have hOuter := List.all_eq_true.mp hCheck a ha
  have hInner := List.all_eq_true.mp hOuter b hb
  have hDigTrue : bytes32Eq (sha256 a) (sha256 b) = true := (bytes32Eq_iff _ _).mpr hDigestEq
  simp only [hDigTrue, Bool.not_true, Bool.false_or] at hInner
  exact (merkleBytesEq_iff a b).mp hInner

/-- Concrete length-tagged / child-preserving 32-byte hash function `toyLenPrefixHash` for constructive
    finite-pool collision-freeness witnesses (`Audit C-03`):
    - For leaf preimages `0x00 || leaf` (or any input not starting with `0x01` of length `65`):
      encodes `[tag, UInt8.ofNat input.size, input[1], input[2], input[3], 0 ... 0]`.
    - For 65-byte internal node preimages `0x01 || left(32) || right(32)`:
      encodes `[0x01, left[0..14], right[0..14], 0]` (1 + 15 + 15 + 1 = 32 bytes!), injectively preserving
      15 bytes of both left and right child digests across multi-level unbalanced trees! -/
def toyLenPrefixHash (input : ByteArray) : Bytes32 :=
  let b0 := (byteAt? input 0).getD 0
  if decide (b0 = 0x01) && decide (input.size = 65) then
    let getB (i : Nat) : UInt8 := (byteAt? input i).getD 0
    { bytes := ByteArray.mk #[
        0x01,
        getB 1, getB 2, getB 3, getB 4, getB 5, getB 6, getB 7, getB 8,
        getB 9, getB 10, getB 11, getB 12, getB 13, getB 14, getB 15,
        getB 33, getB 34, getB 35, getB 36, getB 37, getB 38, getB 39, getB 40,
        getB 41, getB 42, getB 43, getB 44, getB 45, getB 46, getB 47,
        0x00
      ]
      size_eq := rfl }
  else
    let lenByte := UInt8.ofNat input.size
    let b1 := (byteAt? input 1).getD 0
    let b2 := (byteAt? input 2).getD 0
    let b3 := (byteAt? input 3).getD 0
    { bytes := ByteArray.mk #[
        b0, lenByte, b1, b2, b3,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
      ]
      size_eq := rfl }

/-- Concrete unbalanced 3-entry sorted PSBT map witness (`#[0x00] ↦ #[0xAA]`, `#[0x01] ↦ #[0xBB, 0xCC]`, `#[0x03] ↦ #[0xDD]`). -/
def witnessMapEntries : List (ByteArray × ByteArray) := [
  (ByteArray.mk #[0x00], ByteArray.mk #[0xAA]),
  (ByteArray.mk #[0x01], ByteArray.mk #[0xBB, 0xCC]),
  (ByteArray.mk #[0x03], ByteArray.mk #[0xDD])
]

/-- Committed `MerkleMapCommitment` for `witnessMapEntries` under `toyLenPrefixHash`. -/
def witnessMap : MerkleMapCommitment :=
  commitMerkleMap toyLenPrefixHash witnessMapEntries

/-- Honest key openings for `witnessMapEntries` under `toyLenPrefixHash`. -/
def witnessKeyOpenings : List MerkleElementOpening :=
  let keys := witnessMapEntries.map Prod.fst
  [ { element := ByteArray.mk #[0x00]
      leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x00])
      siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash keys 0 },
    { element := ByteArray.mk #[0x01]
      leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])
      siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash keys 1 },
    { element := ByteArray.mk #[0x03]
      leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x03])
      siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash keys 2 } ]

/-- Honest `MapLookupProof` for key `#[0x01]` in `witnessMap` under `toyLenPrefixHash`. -/
def witnessHonestLookupProof1 : MapLookupProof :=
  let keys := witnessMapEntries.map Prod.fst
  let vals := witnessMapEntries.map Prod.snd
  { index := 1
    keySiblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash keys 1
    valueOpening := {
      element := ByteArray.mk #[0xBB, 0xCC]
      leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC])
      siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash vals 1
    } }

/-- Concrete finite preimage pool covering the entire keys tree, values tree, sorted openings, and lookup queries
    for `witnessMapEntries` under `toyLenPrefixHash`. -/
def concretePool : List ByteArray :=
  let keys := witnessMapEntries.map Prod.fst
  let vals := witnessMapEntries.map Prod.snd
  treePreimages toyLenPrefixHash keys ++
  treePreimages toyLenPrefixHash vals ++
  [leafPreimage (ByteArray.mk #[0x02])]

/-! ### Explicit 1/2/3-Leaf Unfolding Helpers (Eliminates `WellFounded.fix` for Kernel Reduction) -/

private theorem merkleRoot_one (sha256 : ByteArray → Bytes32) (x : ByteArray) :
    merkleRoot sha256 [x] = merkleLeafHash sha256 x := by
  rw [merkleRoot]

private theorem merkleRoot_two (sha256 : ByteArray → Bytes32) (x y : ByteArray) :
    merkleRoot sha256 [x, y] =
      merkleNodeHash sha256 (merkleLeafHash sha256 x) (merkleLeafHash sha256 y) := by
  rw [merkleRoot]
  change merkleNodeHash sha256 (merkleRoot sha256 [x]) (merkleRoot sha256 [y]) = _
  rw [merkleRoot_one, merkleRoot_one]

private theorem merkleRoot_three (sha256 : ByteArray → Bytes32) (x y z : ByteArray) :
    merkleRoot sha256 [x, y, z] =
      merkleNodeHash sha256
        (merkleNodeHash sha256 (merkleLeafHash sha256 x) (merkleLeafHash sha256 y))
        (merkleLeafHash sha256 z) := by
  rw [merkleRoot]
  change merkleNodeHash sha256 (merkleRoot sha256 [x, y]) (merkleRoot sha256 [z]) = _
  rw [merkleRoot_two, merkleRoot_one]

private theorem buildMerkleAuditPath_one (sha256 : ByteArray → Bytes32) (x : ByteArray) (i : Nat) :
    buildMerkleAuditPath sha256 [x] i = [] := by
  rw [buildMerkleAuditPath]

private theorem buildMerkleAuditPath_two_0 (sha256 : ByteArray → Bytes32) (x y : ByteArray) :
    buildMerkleAuditPath sha256 [x, y] 0 = [merkleLeafHash sha256 y] := by
  rw [buildMerkleAuditPath]
  change (if 0 < 1 then buildMerkleAuditPath sha256 [x] 0 ++ [merkleRoot sha256 [y]]
          else buildMerkleAuditPath sha256 [y] 0 ++ [merkleRoot sha256 [x]]) = _
  simp only [Nat.zero_lt_one, ↓reduceIte, buildMerkleAuditPath_one, merkleRoot_one, List.nil_append]

private theorem buildMerkleAuditPath_two_1 (sha256 : ByteArray → Bytes32) (x y : ByteArray) :
    buildMerkleAuditPath sha256 [x, y] 1 = [merkleLeafHash sha256 x] := by
  rw [buildMerkleAuditPath]
  change (if 1 < 1 then buildMerkleAuditPath sha256 [x] 1 ++ [merkleRoot sha256 [y]]
          else buildMerkleAuditPath sha256 [y] 0 ++ [merkleRoot sha256 [x]]) = _
  simp only [Nat.lt_irrefl, ↓reduceIte, buildMerkleAuditPath_one, merkleRoot_one, List.nil_append]

private theorem buildMerkleAuditPath_three_0 (sha256 : ByteArray → Bytes32) (x y z : ByteArray) :
    buildMerkleAuditPath sha256 [x, y, z] 0 = [merkleLeafHash sha256 y, merkleLeafHash sha256 z] := by
  rw [buildMerkleAuditPath]
  change (if 0 < 2 then buildMerkleAuditPath sha256 [x, y] 0 ++ [merkleRoot sha256 [z]]
          else buildMerkleAuditPath sha256 [z] 0 ++ [merkleRoot sha256 [x, y]]) = _
  have hLt : (0 : Nat) < 2 := by decide
  simp only [hLt, ↓reduceIte, buildMerkleAuditPath_two_0, merkleRoot_one, List.cons_append, List.nil_append]

private theorem buildMerkleAuditPath_three_1 (sha256 : ByteArray → Bytes32) (x y z : ByteArray) :
    buildMerkleAuditPath sha256 [x, y, z] 1 = [merkleLeafHash sha256 x, merkleLeafHash sha256 z] := by
  rw [buildMerkleAuditPath]
  change (if 1 < 2 then buildMerkleAuditPath sha256 [x, y] 1 ++ [merkleRoot sha256 [z]]
          else buildMerkleAuditPath sha256 [z] 0 ++ [merkleRoot sha256 [x, y]]) = _
  have hLt : (1 : Nat) < 2 := by decide
  simp only [hLt, ↓reduceIte, buildMerkleAuditPath_two_1, merkleRoot_one, List.cons_append, List.nil_append]

private theorem buildMerkleAuditPath_three_2 (sha256 : ByteArray → Bytes32) (x y z : ByteArray) :
    buildMerkleAuditPath sha256 [x, y, z] 2 =
      [merkleNodeHash sha256 (merkleLeafHash sha256 x) (merkleLeafHash sha256 y)] := by
  rw [buildMerkleAuditPath]
  change (if 2 < 2 then buildMerkleAuditPath sha256 [x, y] 2 ++ [merkleRoot sha256 [z]]
          else buildMerkleAuditPath sha256 [z] 0 ++ [merkleRoot sha256 [x, y]]) = _
  simp only [Nat.lt_irrefl, ↓reduceIte, buildMerkleAuditPath_one, merkleRoot_two, List.nil_append]

private theorem treePreimages_one (sha256 : ByteArray → Bytes32) (x : ByteArray) :
    treePreimages sha256 [x] = [leafPreimage x] := by
  rw [treePreimages]

private theorem treePreimages_two (sha256 : ByteArray → Bytes32) (x y : ByteArray) :
    treePreimages sha256 [x, y] =
      nodePreimage (merkleLeafHash sha256 x) (merkleLeafHash sha256 y) ::
        [leafPreimage x, leafPreimage y] := by
  rw [treePreimages]
  change nodePreimage (merkleRoot sha256 [x]) (merkleRoot sha256 [y]) ::
      (treePreimages sha256 [x] ++ treePreimages sha256 [y]) = _
  rw [merkleRoot_one, merkleRoot_one, treePreimages_one, treePreimages_one]
  rfl

private theorem treePreimages_three (sha256 : ByteArray → Bytes32) (x y z : ByteArray) :
    treePreimages sha256 [x, y, z] =
      nodePreimage
        (merkleNodeHash sha256 (merkleLeafHash sha256 x) (merkleLeafHash sha256 y))
        (merkleLeafHash sha256 z) ::
      nodePreimage (merkleLeafHash sha256 x) (merkleLeafHash sha256 y) ::
      [leafPreimage x, leafPreimage y, leafPreimage z] := by
  rw [treePreimages]
  change nodePreimage (merkleRoot sha256 [x, y]) (merkleRoot sha256 [z]) ::
      (treePreimages sha256 [x, y] ++ treePreimages sha256 [z]) = _
  rw [merkleRoot_two, merkleRoot_one, treePreimages_two, treePreimages_one]
  rfl

private theorem merkleDirections_one (i : Nat) : merkleDirections 1 i = [] := by
  rw [merkleDirections]
  have hFalse : ¬(2 ≤ 1 ∧ i < 1) := fun h => absurd h.1 (by decide)
  simp only [hFalse, ↓reduceDIte]

private theorem merkleDirections_two_0 : merkleDirections 2 0 = [.left] := by
  rw [merkleDirections]
  have hCond : 2 ≤ 2 ∧ 0 < 2 := ⟨Nat.le_refl 2, by decide⟩
  simp only [hCond]
  change (if 0 < 1 then MerkleDir.left :: merkleDirections 1 0 else MerkleDir.right :: merkleDirections 1 0) = _
  simp only [Nat.zero_lt_one, ↓reduceIte, merkleDirections_one]

private theorem merkleDirections_two_1 : merkleDirections 2 1 = [.right] := by
  rw [merkleDirections]
  have hCond : 2 ≤ 2 ∧ 1 < 2 := ⟨Nat.le_refl 2, by decide⟩
  simp only [hCond]
  change (if 1 < 1 then MerkleDir.left :: merkleDirections 1 1 else MerkleDir.right :: merkleDirections 1 0) = _
  simp only [Nat.lt_irrefl, ↓reduceIte, merkleDirections_one]

private theorem merkleDirections_three_0 : merkleDirections 3 0 = [.left, .left] := by
  rw [merkleDirections]
  have hCond : 2 ≤ 3 ∧ 0 < 3 := ⟨by decide, by decide⟩
  simp only [hCond]
  change (if 0 < 2 then MerkleDir.left :: merkleDirections 2 0 else MerkleDir.right :: merkleDirections 1 0) = _
  have hLt : (0 : Nat) < 2 := by decide
  simp only [hLt, ↓reduceIte, merkleDirections_two_0]

private theorem merkleDirections_three_1 : merkleDirections 3 1 = [.left, .right] := by
  rw [merkleDirections]
  have hCond : 2 ≤ 3 ∧ 1 < 3 := ⟨by decide, by decide⟩
  simp only [hCond]
  change (if 1 < 2 then MerkleDir.left :: merkleDirections 2 1 else MerkleDir.right :: merkleDirections 1 0) = _
  have hLt : (1 : Nat) < 2 := by decide
  simp only [hLt, ↓reduceIte, merkleDirections_two_1]

private theorem merkleDirections_three_2 : merkleDirections 3 2 = [.right] := by
  rw [merkleDirections]
  have hCond : 2 ≤ 3 ∧ 2 < 3 := ⟨by decide, by decide⟩
  simp only [hCond]
  change (if 2 < 2 then MerkleDir.left :: merkleDirections 2 2 else MerkleDir.right :: merkleDirections 1 0) = _
  simp only [Nat.lt_irrefl, ↓reduceIte, merkleDirections_one]

/-- Flat `WellFounded.fix`-free list equal to `concretePool`. -/
private def concretePoolFlat : List ByteArray :=
  let k0 := ByteArray.mk #[0x00]
  let k1 := ByteArray.mk #[0x01]
  let k2 := ByteArray.mk #[0x03]
  let v0 := ByteArray.mk #[0xAA]
  let v1 := ByteArray.mk #[0xBB, 0xCC]
  let v2 := ByteArray.mk #[0xDD]
  [ nodePreimage
      (merkleNodeHash toyLenPrefixHash (merkleLeafHash toyLenPrefixHash k0) (merkleLeafHash toyLenPrefixHash k1))
      (merkleLeafHash toyLenPrefixHash k2),
    nodePreimage (merkleLeafHash toyLenPrefixHash k0) (merkleLeafHash toyLenPrefixHash k1),
    leafPreimage k0, leafPreimage k1, leafPreimage k2,
    nodePreimage
      (merkleNodeHash toyLenPrefixHash (merkleLeafHash toyLenPrefixHash v0) (merkleLeafHash toyLenPrefixHash v1))
      (merkleLeafHash toyLenPrefixHash v2),
    nodePreimage (merkleLeafHash toyLenPrefixHash v0) (merkleLeafHash toyLenPrefixHash v1),
    leafPreimage v0, leafPreimage v1, leafPreimage v2,
    leafPreimage (ByteArray.mk #[0x02]) ]

private theorem concretePool_eq_flat : concretePool = concretePoolFlat := by
  unfold concretePool concretePoolFlat witnessMapEntries
  dsimp only [List.map]
  rw [treePreimages_three, treePreimages_three]
  rfl

/-- **CONSTRUCTIVE FINITE-POOL COLLISION-FREENESS WITNESS (`Audit C-03`)**:
    Proves constructively (`0 sorryAx`, `0 Classical.choice`, `0 ofReduceBool`) that `toyLenPrefixHash`
    has ZERO collisions on `concretePool`! -/
theorem concretePool_collisionFree : CollisionFreeOn toyLenPrefixHash concretePool := by
  rw [concretePool_eq_flat]
  exact collisionFreeOn_of_check (by decide)

/-- Honest opening completeness with BOLOS bounds (`idx ≤ MAX_MERKLE_LEAF_INDEX` and depth `≤ 32`). -/
theorem honest_opening_valid
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (idx : Nat)
    (el : ByteArray)
    (hGet : leaves[idx]? = some el)
    (hIdxMax : idx ≤ MAX_MERKLE_LEAF_INDEX)
    (hDepth : (buildMerkleAuditPath sha256 leaves idx).length ≤ MAX_MERKLE_TREE_DEPTH) :
    verifyMerkleElementOpening sha256 (merkleRoot sha256 leaves) leaves.length idx
      { element := el
        leafHash := merkleLeafHash sha256 el
        siblingsBottomUp := buildMerkleAuditPath sha256 leaves idx } = true := by
  have hRange : idx < leaves.length := by
    cases Nat.lt_or_ge idx leaves.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  have hSzPos : 0 < leaves.length := Nat.lt_of_le_of_lt (Nat.zero_le idx) hRange
  have hFold := buildMerkleAuditPath_complete sha256 leaves idx el hGet
  unfold verifyMerkleElementOpening verifyMerkleLeafHashProof
  have hNotBad : (decide (leaves.length = 0) || decide (idx ≥ leaves.length) ||
                  decide (idx > MAX_MERKLE_LEAF_INDEX) ||
                  decide ((buildMerkleAuditPath sha256 leaves idx).length > MAX_MERKLE_TREE_DEPTH)) = false := by
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨⟨⟨Nat.ne_of_gt hSzPos, Nat.not_le.mpr hRange⟩, Nat.not_lt.mpr hIdxMax⟩, Nat.not_lt.mpr hDepth⟩
  simp only [hNotBad, Bool.false_eq_true, ↓reduceIte, hFold, bytes32Eq_refl, Bool.and_self]

private theorem witnessKeyOpenings_valid :
    verifySortedMerkleMapOpenings toyLenPrefixHash witnessMap witnessKeyOpenings = true := by
  have h0 : verifyMerkleElementOpening toyLenPrefixHash witnessMap.keysRoot 3 0
      { element := ByteArray.mk #[0x00]
        leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x00])
        siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 0 } = true := by
    refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.fst) 0 (ByteArray.mk #[0x00]) rfl (by decide) ?_
    dsimp only [witnessMapEntries, List.map]
    rw [buildMerkleAuditPath_three_0]
    decide
  have h1 : verifyMerkleElementOpening toyLenPrefixHash witnessMap.keysRoot 3 1
      { element := ByteArray.mk #[0x01]
        leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])
        siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 } = true := by
    refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 (ByteArray.mk #[0x01]) rfl (by decide) ?_
    dsimp only [witnessMapEntries, List.map]
    rw [buildMerkleAuditPath_three_1]
    decide
  have h2 : verifyMerkleElementOpening toyLenPrefixHash witnessMap.keysRoot 3 2
      { element := ByteArray.mk #[0x03]
        leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x03])
        siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 2 } = true := by
    refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.fst) 2 (ByteArray.mk #[0x03]) rfl (by decide) ?_
    dsimp only [witnessMapEntries, List.map]
    rw [buildMerkleAuditPath_three_2]
    decide
  have hSize : witnessMap.size = 3 := rfl
  have hSorted : isStrictlySorted (witnessKeyOpenings.map (·.element)) = true := by decide
  have hLenDec : decide (witnessKeyOpenings.length = 3) = true := by decide
  have hNotZero : decide ((3 : Nat) = 0) = false := by decide
  have hSz0 : decide ((ByteArray.mk #[0x00]).size ≤ MAX_MERKLE_MAP_KEY_SIZE) = true := by decide
  have hSz1 : decide ((ByteArray.mk #[0x01]).size ≤ MAX_MERKLE_MAP_KEY_SIZE) = true := by decide
  have hSz2 : decide ((ByteArray.mk #[0x03]).size ≤ MAX_MERKLE_MAP_KEY_SIZE) = true := by decide
  unfold verifySortedMerkleMapOpenings
  rw [hSize]
  have hZip : (List.range 3).zip witnessKeyOpenings =
      [(0, ({ element := ByteArray.mk #[0x00]
              leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x00])
              siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 0 } : MerkleElementOpening)),
       (1, ({ element := ByteArray.mk #[0x01]
              leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])
              siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 } : MerkleElementOpening)),
       (2, ({ element := ByteArray.mk #[0x03]
              leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x03])
              siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 2 } : MerkleElementOpening))] := rfl
  rw [hZip]
  simp only [hNotZero, Bool.false_eq_true, ↓reduceIte, hLenDec, List.all_cons, List.all_nil,
             hSz0, hSz1, hSz2, h0, h1, h2, hSorted, Bool.and_self]

/-- **THEOREM M11 (Non-Vacuity Witness: Unbalanced 3-Entry Sorted Merkleized PSBT Map Verified & Queried)**:
    Proves with `0 sorryAx` and `0 Classical.choice` that on `toyLenPrefixHash` and `witnessMapEntries`:
    1. `CollisionFreeOn toyLenPrefixHash concretePool` holds constructively,
    2. Its honest `witnessKeyOpenings` pass `verifySortedMerkleMapOpenings`, and
    3. `deviceLookupMerkleMapValue` against `mkHonestMapHostOracle` resolves key `#[0x01]` to
       `.present #[0xBB, 0xCC]` and absent key `#[0x02]` to `.absentClaimed`! -/
theorem non_vacuity_honest_merkle_map_verified_and_queried :
    ∃ (sha256 : ByteArray → Bytes32)
      (pool : List ByteArray)
      (map : MerkleMapCommitment)
      (keyOpenings : List MerkleElementOpening)
      (host : UntrustedHostOracle),
      CollisionFreeOn sha256 pool ∧
      map.size = 3 ∧
      verifySortedMerkleMapOpenings sha256 map keyOpenings = true ∧
      deviceLookupMerkleMapValue sha256 host map (ByteArray.mk #[0x01]) =
        .present (ByteArray.mk #[0xBB, 0xCC]) ∧
      deviceLookupMerkleMapValue sha256 host map (ByteArray.mk #[0x02]) =
        .absentClaimed := by
  refine ⟨toyLenPrefixHash, concretePool, witnessMap, witnessKeyOpenings,
          mkHonestMapHostOracle toyLenPrefixHash witnessMapEntries,
          concretePool_collisionFree, rfl, witnessKeyOpenings_valid, ?_, ?_⟩
  · have hKeyProof :
        verifyMerkleLeafHashProof toyLenPrefixHash witnessMap.keysRoot 3 1
          (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01]))
          (buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1) = true := by
      have hOp : verifyMerkleElementOpening toyLenPrefixHash witnessMap.keysRoot 3 1
          { element := ByteArray.mk #[0x01]
            leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])
            siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 } = true := by
        refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 (ByteArray.mk #[0x01]) rfl (by decide) ?_
        dsimp only [witnessMapEntries, List.map]
        rw [buildMerkleAuditPath_three_1]
        decide
      exact (Bool.and_eq_true _ _).mp hOp |>.1
    have hValProof :
        verifyMerkleLeafHashProof toyLenPrefixHash witnessMap.valuesRoot 3 1
          (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC]))
          (buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.snd) 1) = true := by
      have hOp : verifyMerkleElementOpening toyLenPrefixHash witnessMap.valuesRoot 3 1
          { element := ByteArray.mk #[0xBB, 0xCC]
            leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC])
            siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.snd) 1 } = true := by
        refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.snd) 1 (ByteArray.mk #[0xBB, 0xCC]) rfl (by decide) ?_
        dsimp only [witnessMapEntries, List.map]
        rw [buildMerkleAuditPath_three_1]
        decide
      exact (Bool.and_eq_true _ _).mp hOp |>.1
    have hHostIdx1 :
        (mkHonestMapHostOracle toyLenPrefixHash witnessMapEntries).queryLeafIndex
          witnessMap.keysRoot (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])) = some (true, 1) := by
      unfold mkHonestMapHostOracle
      dsimp only
      have hKR : bytes32Eq witnessMap.keysRoot (merkleRoot toyLenPrefixHash (witnessMapEntries.map Prod.fst)) = true :=
        bytes32Eq_refl _
      have hFind : findIdxPure?
          (fun el => bytes32Eq (merkleLeafHash toyLenPrefixHash el)
                               (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])))
          (witnessMapEntries.map Prod.fst) = some 1 := by decide
      simp only [hKR, ↓reduceIte, hFind]
    have hHostKeyPrf1 :
        (mkHonestMapHostOracle toyLenPrefixHash witnessMapEntries).queryLeafProof
          witnessMap.keysRoot 3 1 =
          some (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01]),
                buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1) := by
      unfold mkHonestMapHostOracle
      dsimp only
      have hKR : bytes32Eq witnessMap.keysRoot (merkleRoot toyLenPrefixHash (witnessMapEntries.map Prod.fst)) = true :=
        bytes32Eq_refl _
      have hSzEq : decide (3 = (witnessMapEntries.map Prod.fst).length) = true := by decide
      simp only [hKR, hSzEq, Bool.and_self, ↓reduceIte]
      rfl
    have hHostValPrf1 :
        (mkHonestMapHostOracle toyLenPrefixHash witnessMapEntries).queryLeafProof
          witnessMap.valuesRoot 3 1 =
          some (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC]),
                buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.snd) 1) := by
      unfold mkHonestMapHostOracle
      dsimp only
      have hKeysRoot : witnessMap.keysRoot =
          merkleNodeHash toyLenPrefixHash
            (merkleNodeHash toyLenPrefixHash
              (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x00]))
              (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])))
            (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x03])) := by
        unfold witnessMap commitMerkleMap witnessMapEntries
        dsimp only [List.map]
        exact merkleRoot_three _ _ _ _
      have hValsRoot : witnessMap.valuesRoot =
          merkleNodeHash toyLenPrefixHash
            (merkleNodeHash toyLenPrefixHash
              (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xAA]))
              (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC])))
            (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xDD])) := by
        unfold witnessMap commitMerkleMap witnessMapEntries
        dsimp only [List.map]
        exact merkleRoot_three _ _ _ _
      have hMKR : merkleRoot toyLenPrefixHash (witnessMapEntries.map Prod.fst) = witnessMap.keysRoot := rfl
      have hMVR : merkleRoot toyLenPrefixHash (witnessMapEntries.map Prod.snd) = witnessMap.valuesRoot := rfl
      rw [hMKR, hMVR]
      have hNe : bytes32Eq witnessMap.valuesRoot witnessMap.keysRoot = false := by
        rw [hKeysRoot, hValsRoot]
        decide
      have hCond1 : ¬((bytes32Eq witnessMap.valuesRoot witnessMap.keysRoot &&
                       decide (3 = (witnessMapEntries.map Prod.fst).length)) = true) := by
        rw [hNe, Bool.false_and]
        decide
      have hCond2 : (bytes32Eq witnessMap.valuesRoot witnessMap.valuesRoot &&
                     decide (3 = (witnessMapEntries.map Prod.snd).length)) = true := by
        rw [bytes32Eq_refl, Bool.true_and]
        decide
      rw [ite_eq_right_iff.mpr (fun h => absurd h hCond1), ite_eq_left_iff.mpr (fun h => absurd hCond2 h)]
      rfl
    have hHostPre1 :
        (mkHonestMapHostOracle toyLenPrefixHash witnessMapEntries).queryPreimage
          (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC])) =
          some (leafPreimage (ByteArray.mk #[0xBB, 0xCC])) := by
      unfold mkHonestMapHostOracle
      dsimp only
      have hFind : findPure?
          (fun el => bytes32Eq (merkleLeafHash toyLenPrefixHash el)
                               (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC])))
          (witnessMapEntries.map Prod.fst ++ witnessMapEntries.map Prod.snd) =
          some (ByteArray.mk #[0xBB, 0xCC]) := by decide
      rw [hFind]
    have hPreVer1 :
        verifyMerkleLeafPreimage toyLenPrefixHash
          (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC]))
          (leafPreimage (ByteArray.mk #[0xBB, 0xCC])) =
          some (ByteArray.mk #[0xBB, 0xCC]) := by
      unfold verifyMerkleLeafPreimage
      have hSzOk : decide ((leafPreimage (ByteArray.mk #[0xBB, 0xCC])).size > MAX_PREIMAGE_TOTAL_SIZE) = false := by
        decide
      have hListEq : (leafPreimage (ByteArray.mk #[0xBB, 0xCC])).data.toList = [0x00, 0xBB, 0xCC] := rfl
      have hShaOk : (!bytes32Eq (toyLenPrefixHash (leafPreimage (ByteArray.mk #[0xBB, 0xCC])))
                      (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC]))) = false := by decide
      simp only [hSzOk, Bool.false_eq_true, ↓reduceIte, hListEq, hShaOk]
    unfold deviceLookupMerkleMapValue deviceFetchLeafElement
    have hSz : witnessMap.size = 3 := rfl
    rw [hSz]
    have hNotZ : decide ((3 : Nat) = 0) = false := by decide
    have hNotOob : (decide (1 > MAX_MERKLE_LEAF_INDEX) || decide (1 ≥ 3)) = false := by decide
    have hKeyEq : (!bytes32Eq (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01]))
                              (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01]))) = false := by decide
    simp only [hNotZ, Bool.false_eq_true, ↓reduceIte, hHostIdx1, hNotOob, Bool.not_true,
               hHostKeyPrf1, hKeyEq, hKeyProof, hHostValPrf1, hValProof, hHostPre1, hPreVer1]
  · have hHostIdx2 :
        (mkHonestMapHostOracle toyLenPrefixHash witnessMapEntries).queryLeafIndex
          witnessMap.keysRoot (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x02])) = some (false, 0) := by
      unfold mkHonestMapHostOracle
      dsimp only
      have hKR : bytes32Eq witnessMap.keysRoot (merkleRoot toyLenPrefixHash (witnessMapEntries.map Prod.fst)) = true :=
        bytes32Eq_refl _
      have hFind : findIdxPure?
          (fun el => bytes32Eq (merkleLeafHash toyLenPrefixHash el)
                               (merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x02])))
          (witnessMapEntries.map Prod.fst) = none := by decide
      simp only [hKR, ↓reduceIte, hFind]
    unfold deviceLookupMerkleMapValue
    have hSz : witnessMap.size = 3 := rfl
    rw [hSz]
    have hNotZ : decide ((3 : Nat) = 0) = false := by decide
    have hNotOob : (decide (0 > MAX_MERKLE_LEAF_INDEX) || decide (0 ≥ 3)) = false := by decide
    simp only [hNotZ, Bool.false_eq_true, ↓reduceIte, hHostIdx2, hNotOob, Bool.not_false]

/-- **THEOREM M12 (End-to-End Constructive Uniqueness Instantiation on `toyLenPrefixHash` + `concretePool`)**:
    Instantiates `sorted_merkle_map_lookup_proof_unique` end-to-end on the concrete 3-entry sorted map
    without any uninstantiated collision-resistance hypothesis: for ANY candidate `MapLookupProof` `p`
    whose preimages lie in `concretePool`, if `verifyMapLookupProof toyLenPrefixHash witnessMap #[0x01] p = true`,
    then `p.index = 1` and `p.valueOpening.element = #[0xBB, 0xCC]`! -/
theorem non_vacuity_end_to_end_lookup_uniqueness
    (p : MapLookupProof)
    (hSub : ∀ x, x ∈ mapLookupProofPreimages toyLenPrefixHash witnessMap (ByteArray.mk #[0x01]) p →
      x ∈ concretePool)
    (hValid : verifyMapLookupProof toyLenPrefixHash witnessMap (ByteArray.mk #[0x01]) p = true) :
    p.index = 1 ∧ p.valueOpening.element = ByteArray.mk #[0xBB, 0xCC] := by
  have hHonestKeyOp : verifyMerkleElementOpening toyLenPrefixHash witnessMap.keysRoot 3 1
      { element := ByteArray.mk #[0x01]
        leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])
        siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 } = true := by
    refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 (ByteArray.mk #[0x01]) rfl (by decide) ?_
    dsimp only [witnessMapEntries, List.map]
    rw [buildMerkleAuditPath_three_1]
    decide
  have hHonestValOp : verifyMerkleElementOpening toyLenPrefixHash witnessMap.valuesRoot 3 1
      { element := ByteArray.mk #[0xBB, 0xCC]
        leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0xBB, 0xCC])
        siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.snd) 1 } = true := by
    refine honest_opening_valid toyLenPrefixHash (witnessMapEntries.map Prod.snd) 1 (ByteArray.mk #[0xBB, 0xCC]) rfl (by decide) ?_
    dsimp only [witnessMapEntries, List.map]
    rw [buildMerkleAuditPath_three_1]
    decide
  have hHonestLookup :
      verifyMapLookupProof toyLenPrefixHash witnessMap (ByteArray.mk #[0x01]) witnessHonestLookupProof1 = true := by
    unfold verifyMapLookupProof witnessHonestLookupProof1
    have hSz : witnessMap.size = 3 := rfl
    rw [hSz]
    exact (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mp hHonestKeyOp |>.1, hHonestValOp⟩
  have hKeysSub : ∀ x, x ∈ treePreimages toyLenPrefixHash (witnessMapEntries.map Prod.fst) → x ∈ concretePool := by
    intro x hx
    unfold concretePool
    exact List.mem_append_left _ (List.mem_append_left _ hx)
  have hValsSub : ∀ x, x ∈ treePreimages toyLenPrefixHash (witnessMapEntries.map Prod.snd) → x ∈ concretePool := by
    intro x hx
    unfold concretePool
    exact List.mem_append_left _ (List.mem_append_right _ hx)
  have hSortedSub :
      ∀ x, x ∈ sortedMapOpeningsPreimages toyLenPrefixHash witnessMap.size witnessKeyOpenings → x ∈ concretePool := by
    intro x hx
    have hSz : witnessMap.size = 3 := rfl
    rw [hSz] at hx
    unfold sortedMapOpeningsPreimages at hx
    have hZip : (List.range 3).zip witnessKeyOpenings =
        [ (0, ({ element := ByteArray.mk #[0x00]
                 leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x00])
                 siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 0 } : MerkleElementOpening)),
          (1, ({ element := ByteArray.mk #[0x01]
                 leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x01])
                 siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 1 } : MerkleElementOpening)),
          (2, ({ element := ByteArray.mk #[0x03]
                 leafHash := merkleLeafHash toyLenPrefixHash (ByteArray.mk #[0x03])
                 siblingsBottomUp := buildMerkleAuditPath toyLenPrefixHash (witnessMapEntries.map Prod.fst) 2 } : MerkleElementOpening)) ] := rfl
    rw [hZip] at hx
    simp only [List.foldr, List.mem_append, List.not_mem_nil, or_false] at hx
    rcases hx with hx0 | hx1 | hx2
    · exact hKeysSub x (honest_openingPreimages_subset_treePreimages toyLenPrefixHash
        (witnessMapEntries.map Prod.fst) 0 (ByteArray.mk #[0x00]) rfl x hx0)
    · exact hKeysSub x (honest_openingPreimages_subset_treePreimages toyLenPrefixHash
        (witnessMapEntries.map Prod.fst) 1 (ByteArray.mk #[0x01]) rfl x hx1)
    · exact hKeysSub x (honest_openingPreimages_subset_treePreimages toyLenPrefixHash
        (witnessMapEntries.map Prod.fst) 2 (ByteArray.mk #[0x03]) rfl x hx2)
  have hHonestSub :
      ∀ x, x ∈ mapLookupProofPreimages toyLenPrefixHash witnessMap (ByteArray.mk #[0x01]) witnessHonestLookupProof1 →
        x ∈ concretePool := by
    intro x hx
    unfold mapLookupProofPreimages witnessHonestLookupProof1 at hx
    have hSz : witnessMap.size = 3 := rfl
    rw [hSz] at hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hxKeyPrf | hxValOp
    · exact hKeysSub _ (honest_openingPreimages_subset_treePreimages toyLenPrefixHash
        (witnessMapEntries.map Prod.fst) 1 (ByteArray.mk #[0x01]) rfl _ List.mem_cons_self)
    · exact hKeysSub x (honest_openingPreimages_subset_treePreimages toyLenPrefixHash
        (witnessMapEntries.map Prod.fst) 1 (ByteArray.mk #[0x01]) rfl x (List.mem_cons_of_mem _ hxKeyPrf))
    · exact hValsSub x (honest_openingPreimages_subset_treePreimages toyLenPrefixHash
        (witnessMapEntries.map Prod.snd) 1 (ByteArray.mk #[0xBB, 0xCC]) rfl x hxValOp)
  exact sorted_merkle_map_lookup_proof_unique
    concretePool_collisionFree witnessKeyOpenings_valid hSortedSub hSub hHonestSub hValid hHonestLookup

end Spec.MerkleProtocol

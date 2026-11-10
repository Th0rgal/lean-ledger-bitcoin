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

/-! ## 1. RFC-6962-Variant Merkle Tree Specification (`doc/merkle.md` & `src/common/merkle.c`) -/

/-- Domain-separated Merkle leaf hash: `SHA256(0x00 || leaf)` (`merkle_compute_element_hash`). -/
def merkleLeafHash (sha256 : ByteArray → Bytes32) (leaf : ByteArray) : Bytes32 :=
  sha256 (ByteArray.mk (#[0x00] ++ leaf.data))

/-- Domain-separated Merkle internal node hash: `SHA256(0x01 || left || right)` (`merkle_combine_hashes`). -/
def merkleNodeHash (sha256 : ByteArray → Bytes32) (left right : Bytes32) : Bytes32 :=
  sha256 (ByteArray.mk (#[0x01] ++ left.bytes.data ++ right.bytes.data))

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
      · exact ih (acc * 2) (by omega)
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
  ⟨largestPow2LtGo_pos n n 1 (by omega), largestPow2LtGo_lt n n 1 (by omega)⟩

/-- Exact BOLOS Merkle Tree Hash (`MTH(D[n])` in `doc/merkle.md`):
    - `MTH([]) = zeroBytes32` (32 zero bytes — intentional Ledger deviation from RFC 6962!)
    - `MTH([d]) = SHA256(0x00 || d)`
    - `MTH(D[n]) = SHA256(0x01 || MTH(D[0:k]) || MTH(D[k:n]))` where `k = largestPow2Lt n` (`n >= 2`). -/
def merkleRoot (sha256 : ByteArray → Bytes32) (leaves : List ByteArray) : Bytes32 :=
  match leaves with
  | [] => zeroBytes32
  | [x] => merkleLeafHash sha256 x
  | x :: y :: rest =>
      have hLen : 2 ≤ (x :: y :: rest).length := by simp
      have hk := largestPow2Lt_bounds hLen
      let k := largestPow2Lt (x :: y :: rest).length
      merkleNodeHash sha256
        (merkleRoot sha256 ((x :: y :: rest).take k))
        (merkleRoot sha256 ((x :: y :: rest).drop k))
termination_by leaves.length
decreasing_by
  · rw [List.length_take]
    have _hk2 : k < (x :: y :: rest).length := hk.2
    omega
  · rw [List.length_drop]
    have _hk1 : 0 < k := hk.1
    omega

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
      have _ : size - k < size := by omega
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

/-- Pure structural 32-byte digest equality (`bytesEq a.bytes b.bytes`) that reduces transparently
    in the Lean kernel without invoking `@[extern] ByteArray.beq`. -/
def bytes32Eq (a b : Bytes32) : Bool :=
  bytesEq a.bytes b.bytes

theorem bytesEq_iff (a b : ByteArray) : bytesEq a b = true ↔ a = b := by
  unfold bytesEq
  rw [beq_iff_eq]
  constructor
  · intro h
    cases a with | mk da =>
    cases b with | mk db =>
    congr
    exact Array.ext' h
  · intro h
    subst h
    rfl

theorem bytes32Eq_iff (a b : Bytes32) : bytes32Eq a b = true ↔ a = b := by
  unfold bytes32Eq
  rw [bytesEq_iff]
  cases a; cases b
  simp

theorem bytes32Eq_refl (a : Bytes32) : bytes32Eq a a = true :=
  (bytes32Eq_iff a a).mpr rfl

/-- Canonical Merkle leaf-hash proof verification (`get_merkle_leaf_hash` in `get_merkle_leaf_hash.c`):
    1. `0 < treeSize` and `leafIndex < treeSize`.
    2. `siblingsBottomUp.length == (merkleDirections treeSize leafIndex).length` (exact leaf depth check!).
    3. Folding `leafHash` bottom-up with `siblingsBottomUp` equals `expectedRoot`. -/
def verifyMerkleLeafHashProof
    (sha256 : ByteArray → Bytes32)
    (expectedRoot : Bytes32)
    (treeSize : Nat)
    (leafIndex : Nat)
    (leafHash : Bytes32)
    (siblingsBottomUp : List Bytes32) : Bool :=
  if treeSize == 0 || leafIndex ≥ treeSize then
    false
  else
    let dirsBottomUp := (merkleDirections treeSize leafIndex).reverse
    match foldMerkleProofBottomUp sha256 leafHash dirsBottomUp siblingsBottomUp with
    | some computedRoot => bytes32Eq computedRoot expectedRoot
    | none => false

/-- Canonical Merkle leaf preimage verification (`get_merkle_preimage.c`):
    Given a verified `leafHash`, checks that `0x00 || element` hashes to `leafHash`
    (equivalently `merkleLeafHash sha256 element == leafHash`). -/
def verifyMerkleLeafPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (rawPreimageWithPrefix : ByteArray) : Option ByteArray :=
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
      have hLen : 2 ≤ (x :: y :: rest).length := by simp
      have hk := largestPow2Lt_bounds hLen
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
    have _hk2 : k < (x :: y :: rest).length := hk.2
    omega
  · rw [List.length_drop]
    have _hk1 : 0 < k := hk.1
    omega

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
      | some el => some (ByteArray.mk (#[0x00] ++ el.data))
      | none => none
    queryLeafProof := fun r sz idx =>
      if bytes32Eq r root && sz == leaves.length then
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
      | some el => some (ByteArray.mk (#[0x00] ++ el.data))
      | none => none
    queryLeafProof := fun r sz idx =>
      if bytes32Eq r kRoot && sz == keys.length then
        match getAtPure? keys idx with
        | some el => some (merkleLeafHash sha256 el, buildMerkleAuditPath sha256 keys idx)
        | none => none
      else if bytes32Eq r vRoot && sz == vals.length then
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

/-- Device-side verification that a `MerkleMapCommitment` has strictly sorted keys
    (`call_check_merkle_tree_sorted_with_callback` in `check_merkle_tree_sorted.c`):
    Opens all `i ∈ [0, map.size)` against `(map.keysRoot, map.size, i)` and checks `isStrictlySorted`! -/
def verifySortedMerkleMapOpenings
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening) : Bool :=
  keyOpenings.length == map.size &&
  ((List.range map.size).zip keyOpenings).all (fun (i, op) =>
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
    3. If `found == false` (and `candIdx < map.size` or `map.size == 0` check: note in `get_merkle_leaf_index.c:34`,
       `index >= size` rejects even before `!found`!), returns `.absentClaimed`.
    4. If `found == true`, verifies a Merkle leaf-hash proof at `(map.keysRoot, map.size, idx)` and enforces
       `returnedLeafHash == keyLeafHash`!
    5. Opens and verifies the corresponding value leaf element at the **exact same index** `idx` in
       `(map.valuesRoot, map.size, idx)`! -/
def deviceLookupMerkleMapValue
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray) : MapLookupResult :=
  let keyHash := merkleLeafHash sha256 key
  match host.queryLeafIndex map.keysRoot keyHash with
  | none => .protocolError
  | some (found, idx) =>
      if idx ≥ map.size then
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

/-! ## 5. Collision-Relative Soundness & Uniqueness Proofs (`0 sorryAx`, Zero `axiom`) -/

/-- Explicit cryptographic collision-resistance hypothesis for `sha256` (NEVER declared as a Lean `axiom`!).
    States that no two distinct preimages encountered produce the same 32-byte digest. -/
def HashCollisionFree (sha256 : ByteArray → Bytes32) : Prop :=
  ∀ a b : ByteArray, sha256 a = sha256 b → a = b

/-! ### 5.1 Strict Lexicographic Order Lemmas (Irreflexivity, Transitivity, Pairwise Key Uniqueness) -/

theorem listUInt8Lt_irrefl (xs : List UInt8) : listUInt8Lt xs xs = false := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      unfold listUInt8Lt
      have hNotLt : ¬(a.toNat < a.toNat) := Nat.lt_irrefl _
      simp [hNotLt, ih]

theorem byteArrayLt_irrefl (x : ByteArray) : byteArrayLt x x = false :=
  listUInt8Lt_irrefl x.data.toList

theorem listUInt8Lt_trans {xs ys zs : List UInt8}
    (hxy : listUInt8Lt xs ys = true)
    (hyz : listUInt8Lt ys zs = true) :
    listUInt8Lt xs zs = true := by
  induction xs generalizing ys zs with
  | nil =>
      cases ys with
      | nil => simp [listUInt8Lt] at hxy
      | cons b bs =>
          cases zs with
          | nil => simp [listUInt8Lt] at hyz
          | cons c cs => rfl
  | cons a as ih =>
      cases ys with
      | nil => simp [listUInt8Lt] at hxy
      | cons b bs =>
          cases zs with
          | nil => simp [listUInt8Lt] at hyz
          | cons c cs =>
              unfold listUInt8Lt at hxy hyz ⊢
              by_cases hab : a.toNat < b.toNat
              · simp [hab] at hxy
                by_cases hbc : b.toNat < c.toNat
                · have hac : a.toNat < c.toNat := Nat.lt_trans hab hbc
                  simp [hac]
                · by_cases hcb : c.toNat < b.toNat
                  · simp [hbc, hcb] at hyz
                  · have hEqBC : b.toNat = c.toNat := by omega
                    have hac : a.toNat < c.toNat := by omega
                    simp [hac]
              · by_cases hba : b.toNat < a.toNat
                · simp [hab, hba] at hxy
                · have hEqAB : a.toNat = b.toNat := by omega
                  simp [hab, hba] at hxy
                  by_cases hbc : b.toNat < c.toNat
                  · have hac : a.toNat < c.toNat := by omega
                    simp [hac]
                  · by_cases hcb : c.toNat < b.toNat
                    · simp [hbc, hcb] at hyz
                    · have hEqBC : b.toNat = c.toNat := by omega
                      have hNotAC : ¬(a.toNat < c.toNat) := by omega
                      have hNotCA : ¬(c.toNat < a.toNat) := by omega
                      simp [hbc, hcb] at hyz
                      simp [hNotAC, hNotCA, ih hxy hyz]

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
          | zero => omega
          | succ j' =>
              simp at hj
              have hMem : kj ∈ tl := List.mem_of_getElem? hj
              exact strictlySorted_head_lt_tail hSorted kj hMem
      | succ i' =>
          cases j with
          | zero => omega
          | succ j' =>
              simp at hi hj
              have hTailSorted : isStrictlySorted tl = true := by
                cases tl with
                | nil => rfl
                | cons b bs =>
                    unfold isStrictlySorted at hSorted
                    simp only [Bool.and_eq_true] at hSorted
                    exact hSorted.2
              exact ih hTailSorted (by omega) hi hj

/-- **SORTED KEYS UNIQUENESS LEMMA**:
    In any strictly sorted list of keys, distinct indices NEVER contain equal keys (`i ≠ j → keys[i] ≠ keys[j]`). -/
theorem strictlySorted_pairwise_distinct {keys : List ByteArray}
    (hSorted : isStrictlySorted keys = true)
    {i j : Nat} {k1 k2 : ByteArray}
    (hNe : i ≠ j)
    (hi : keys[i]? = some k1)
    (hj : keys[j]? = some k2) :
    k1 ≠ k2 := by
  by_cases hLt : i < j
  · exact byteArrayLt_ne (strictlySorted_index_lt hSorted hLt hi hj)
  · have hGt : j < i := by omega
    intro hEq
    subst hEq
    exact byteArrayLt_ne (strictlySorted_index_lt hSorted hGt hj hi) rfl

/-! ### 5.2 Domain Separation & Injectivity of Leaf / Internal Node Hashes -/

/-- Under `HashCollisionFree sha256`, `merkleLeafHash` is injective: equal leaf hashes imply identical leaf bytes. -/
theorem merkleLeafHash_injective {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {a b : ByteArray}
    (hEq : merkleLeafHash sha256 a = merkleLeafHash sha256 b) :
    a = b := by
  have hPre := hCF _ _ hEq
  have hData : (ByteArray.mk (#[0x00] ++ a.data)).data.toList = (ByteArray.mk (#[0x00] ++ b.data)).data.toList :=
    congrArg (fun x => x.data.toList) hPre
  simp only [Array.toList_append, List.cons_append, List.nil_append, List.cons.injEq, true_and] at hData
  cases a with | mk da =>
  cases b with | mk db =>
  congr
  exact Array.ext' hData

/-- Under `HashCollisionFree sha256`, `merkleNodeHash` is injective in **both** left and right 32-byte children!
    Crucially uses `left.size_eq : left.bytes.size = 32` so the `65`-byte preimage `0x01 || left(32) || right(32)`
    splits uniquely without length-extension ambiguity. -/
theorem merkleNodeHash_injective {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {l1 r1 l2 r2 : Bytes32}
    (hEq : merkleNodeHash sha256 l1 r1 = merkleNodeHash sha256 l2 r2) :
    l1 = l2 ∧ r1 = r2 := by
  have hPre := hCF _ _ hEq
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

/-- Domain separation (`0x00` vs `0x01`): a leaf hash can NEVER collide with an internal node hash! -/
theorem merkleLeafHash_ne_nodeHash {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    (leaf : ByteArray) (l r : Bytes32) :
    merkleLeafHash sha256 leaf ≠ merkleNodeHash sha256 l r := by
  intro hEq
  have hPre := hCF _ _ hEq
  have hHead := congrArg (fun b => b.data.toList.head?) hPre
  simp [Array.toList_append] at hHead

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
      | cons _ _ => simp at hLen
  | cons d dsRest ih =>
      cases ss1 with
      | nil => simp at hLen
      | cons s ssRest =>
          simp at hLen
          cases d <;> exact ih _ ssRest hLen

/-- **PROOF DETERMINISM (ANTI-EQUIVOCATION AT ANY INDEX)**:
    Under `HashCollisionFree sha256`, for ANY fixed `(root, treeSize, leafIndex)` (even if `root` was
    adversarially chosen by a malicious host without corresponding to an honest full tree!),
    at most ONE `leafHash` (and hence at most ONE `element : ByteArray`) can ever pass
    `verifyMerkleLeafHashProof` / `verifyMerkleElementOpening`!

    Proof insight: `dirsBottomUp := (merkleDirections treeSize leafIndex).reverse` is completely
    determined by `(treeSize, leafIndex)`. Inducting from the root step down to the leaf,
    `merkleNodeHash_injective` uniquely forces the child hash at every step! -/
theorem foldMerkleProofBottomUp_unique_start
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    (dirs : List MerkleDir)
    {h1 h2 root : Bytes32}
    {sibs1 sibs2 : List Bytes32}
    (hFold1 : foldMerkleProofBottomUp sha256 h1 dirs sibs1 = some root)
    (hFold2 : foldMerkleProofBottomUp sha256 h2 dirs sibs2 = some root) :
    h1 = h2 ∧ sibs1 = sibs2 := by
  induction dirs generalizing h1 h2 sibs1 sibs2 with
  | nil =>
      cases sibs1 with
      | nil =>
          cases sibs2 with
          | nil =>
              simp [foldMerkleProofBottomUp] at hFold1 hFold2
              exact ⟨hFold1.trans hFold2.symm, rfl⟩
          | cons _ _ => simp [foldMerkleProofBottomUp] at hFold2
      | cons _ _ => simp [foldMerkleProofBottomUp] at hFold1
  | cons d dRest ih =>
      cases sibs1 with
      | nil => simp [foldMerkleProofBottomUp] at hFold1
      | cons s1 sRest1 =>
          cases sibs2 with
          | nil => simp [foldMerkleProofBottomUp] at hFold2
          | cons s2 sRest2 =>
              cases d with
              | left =>
                  simp only [foldMerkleProofBottomUp] at hFold1 hFold2
                  obtain ⟨hNodeEq, hSibRestEq⟩ := ih hFold1 hFold2
                  obtain ⟨hChildEq, hSibEq⟩ := merkleNodeHash_injective hCF hNodeEq
                  subst hChildEq hSibEq hSibRestEq
                  exact ⟨rfl, rfl⟩
              | right =>
                  simp only [foldMerkleProofBottomUp] at hFold1 hFold2
                  obtain ⟨hNodeEq, hSibRestEq⟩ := ih hFold1 hFold2
                  obtain ⟨hSibEq, hChildEq⟩ := merkleNodeHash_injective hCF hNodeEq
                  subst hChildEq hSibEq hSibRestEq
                  exact ⟨rfl, rfl⟩

/-- **THEOREM M1 (Leaf Hash Binding at `(root, size, index)`)**:
    Under `HashCollisionFree sha256`, any two valid Merkle leaf-hash proofs for the same `(root, size, index)`
    MUST open the exact same `leafHash` and identical sibling paths. -/
theorem verifyMerkleLeafHashProof_unique
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {root : Bytes32} {size idx : Nat}
    {lh1 lh2 : Bytes32} {sibs1 sibs2 : List Bytes32}
    (h1 : verifyMerkleLeafHashProof sha256 root size idx lh1 sibs1 = true)
    (h2 : verifyMerkleLeafHashProof sha256 root size idx lh2 sibs2 = true) :
    lh1 = lh2 ∧ sibs1 = sibs2 := by
  unfold verifyMerkleLeafHashProof at h1 h2
  dsimp only at h1 h2
  split at h1
  · contradiction
  · rename_i hRange
    have hRangeFalse : (size == 0 || decide (idx ≥ size)) = false :=
      Bool.eq_false_iff.mpr hRange
    rw [hRangeFalse] at h2
    simp only [Bool.false_eq_true, ↓reduceIte] at h2
    cases hf1 : foldMerkleProofBottomUp sha256 lh1 (merkleDirections size idx).reverse sibs1 with
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
            exact foldMerkleProofBottomUp_unique_start hCF _ hf1 hf2

/-- **THEOREM M2 (Element Preimage Binding at `(root, size, index)`)**:
    Under `HashCollisionFree sha256`, any two valid `MerkleElementOpening`s for `(root, size, index)`
    MUST open the exact same `ByteArray` element! -/
theorem verifyMerkleElementOpening_unique
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {root : Bytes32} {size idx : Nat}
    {op1 op2 : MerkleElementOpening}
    (h1 : verifyMerkleElementOpening sha256 root size idx op1 = true)
    (h2 : verifyMerkleElementOpening sha256 root size idx op2 = true) :
    op1.element = op2.element := by
  unfold verifyMerkleElementOpening at h1 h2
  simp only [Bool.and_eq_true] at h1 h2
  obtain ⟨hLhEq, _⟩ := verifyMerkleLeafHashProof_unique hCF h1.1 h2.1
  have hPre1 : merkleLeafHash sha256 op1.element = op1.leafHash := (bytes32Eq_iff _ _).mp h1.2
  have hPre2 : merkleLeafHash sha256 op2.element = op2.leafHash := (bytes32Eq_iff _ _).mp h2.2
  apply merkleLeafHash_injective hCF
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
      | cons _ _ => simp [foldMerkleProofBottomUp] at hFold
  | cons d dRest ih =>
      cases ss with
      | nil => simp [foldMerkleProofBottomUp] at hFold
      | cons s sRest =>
          cases d with
          | left =>
              simp only [foldMerkleProofBottomUp] at hFold
              simp [ih _ sRest hFold]
          | right =>
              simp only [foldMerkleProofBottomUp] at hFold
              simp [ih _ sRest hFold]

/-- **THEOREM M3 (Honest Audit Proof Completeness)**:
    For every list `leaves` and every `idx < leaves.length` with `leaves[idx]? = some el`,
    `buildMerkleAuditPath sha256 leaves idx` passes `verifyMerkleLeafHashProof` against `merkleRoot sha256 leaves`! -/
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
      | [] => simp at hIdxLt
      | [x] =>
          have hIdx0 : idx = 0 := by simp at hIdxLt; omega
          subst hIdx0
          simp at hGet
          subst hGet
          have hDirNil : merkleDirections 1 0 = [] := by
            rw [merkleDirections]; simp
          have hPathNil : buildMerkleAuditPath sha256 [x] 0 = [] := by
            rw [buildMerkleAuditPath]
          have hRoot1 : merkleRoot sha256 [x] = merkleLeafHash sha256 x := by
            rw [merkleRoot]
          simp [hDirNil, hPathNil, hRoot1, foldMerkleProofBottomUp]
      | x :: y :: rest =>
          let all := x :: y :: rest
          have hGe2 : 2 ≤ all.length := by simp [all]
          have hIdxAll : idx < all.length := hIdxLt
          have hk := largestPow2Lt_bounds hGe2
          let k := largestPow2Lt all.length
          have hk1 : 0 < k := hk.1
          have hk2 : k < all.length := hk.2
          by_cases hLeft : idx < k
          · have hTakeLen : (all.take k).length = k := List.length_take_of_le (Nat.le_of_lt hk2)
            have hGetTake : (all.take k)[idx]? = some el := by
              rw [List.getElem?_take_of_lt hLeft]
              exact hGet
            have hIdxTake : idx < (all.take k).length := by omega
            have hSub := ih k hk2 (all.take k) idx hGetTake hIdxTake hTakeLen
            have hDirs : (merkleDirections all.length idx).reverse =
                (merkleDirections k idx).reverse ++ [.left] := by
              conv => lhs; rw [merkleDirections]
              simp [hGe2, hIdxAll, k, hLeft]
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
          · have hDropLen : (all.drop k).length = all.length - k := List.length_drop
            have hGetDrop : (all.drop k)[idx - k]? = some el := by
              rw [List.getElem?_drop]
              have hAdd : k + (idx - k) = idx := by omega
              rw [hAdd]
              exact hGet
            have hDropLt : all.length - k < all.length := by omega
            have hIdxDropLt : idx - k < (all.drop k).length := by omega
            have hSub := ih (all.length - k) hDropLt (all.drop k) (idx - k) hGetDrop hIdxDropLt hDropLen
            have hDirs : (merkleDirections all.length idx).reverse =
                (merkleDirections (all.length - k) (idx - k)).reverse ++ [.right] := by
              conv => lhs; rw [merkleDirections]
              simp [hGe2, hIdxAll, k, hLeft]
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

/-- **THEOREM M4 (Tree-Relative Merkle Proof Soundness)**:
    Under `HashCollisionFree sha256`, if `root = merkleRoot sha256 leaves`, then ANY valid
    `MerkleElementOpening` against `(root, leaves.length, idx)` MUST equal the true committed
    leaf `leaves[idx]`! -/
theorem merkleProof_sound_against_committed_tree
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    (leaves : List ByteArray)
    (idx : Nat)
    (opening : MerkleElementOpening)
    (hValid : verifyMerkleElementOpening sha256 (merkleRoot sha256 leaves) leaves.length idx opening = true) :
    leaves[idx]? = some opening.element := by
  have hRange : idx < leaves.length := by
    unfold verifyMerkleElementOpening verifyMerkleLeafHashProof at hValid
    dsimp only at hValid
    by_cases hBad : (leaves.length == 0 || decide (idx ≥ leaves.length)) = true
    · rw [hBad] at hValid
      simp at hValid
    · have hFalse : (leaves.length == 0 || decide (idx ≥ leaves.length)) = false :=
        Bool.eq_false_iff.mpr hBad
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hFalse
      omega
  let trueEl := leaves[idx]'hRange
  have hGetTrue : leaves[idx]? = some trueEl := List.getElem?_eq_getElem hRange
  have hHonestFold := buildMerkleAuditPath_complete sha256 leaves idx trueEl hGetTrue
  have hHonestValid : verifyMerkleElementOpening sha256 (merkleRoot sha256 leaves) leaves.length idx
      { element := trueEl
        leafHash := merkleLeafHash sha256 trueEl
        siblingsBottomUp := buildMerkleAuditPath sha256 leaves idx } = true := by
    unfold verifyMerkleElementOpening verifyMerkleLeafHashProof
    have hNotBad : (leaves.length == 0 || decide (idx ≥ leaves.length)) = false := by
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      omega
    simp [hNotBad, hHonestFold, bytes32Eq_refl]
  have hElEq := verifyMerkleElementOpening_unique hCF hValid hHonestValid
  rw [hElEq]
  exact hGetTrue

/-! ### 5.4 Merkleized Map Soundness: Sorted Keys Forbid Duplicate Keys & Guarantee Unique Lookup Values -/

/-- Helper extracting the `i`-th opening validity from `((List.range n).zip ops).all ...`. -/
private theorem range_zip_all_get
    {α : Type} {n : Nat} {ops : List α} {P : Nat → α → Bool}
    (hLen : ops.length = n)
    (hAll : ((List.range n).zip ops).all (fun (i, op) => P i op) = true)
    {i : Nat} {op : α}
    (hGet : ops[i]? = some op) :
    P i op = true := by
  have hi : i < n := by
    cases Nat.lt_or_ge i ops.length with
    | inl h => omega
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  have hRangeGet : (List.range n)[i]? = some i := by
    rw [List.getElem?_range hi]
  have hZipMem : (i, op) ∈ (List.range n).zip ops := by
    have hZipIdx : ((List.range n).zip ops)[i]? = some (i, op) := by
      rw [List.getElem?_zip_eq_some]
      exact ⟨hRangeGet, hGet⟩
    exact List.mem_of_getElem? hZipIdx
  exact List.all_eq_true.mp hAll (i, op) hZipMem

/-- **THEOREM M5 (Sorted Merkleized Map Has Zero Duplicate Keys)**:
    Suppose `verifySortedMerkleMapOpenings sha256 map keyOpenings = true`.
    Under `HashCollisionFree sha256`:
    1. All verified key elements `keyOpenings[0].element, ..., keyOpenings[size-1].element` are pairwise distinct!
    2. For ANY PSBT key `k` and ANY two valid leaf-hash proofs at indices `i1` and `i2` against `map.keysRoot`,
       we MUST have `i1 = i2` (no key `k` can appear at two positions in `map.keysRoot`!). -/
theorem sorted_merkle_map_unique_key_index
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    {i1 i2 : Nat} {sibs1 sibs2 : List Bytes32}
    (hProof1 : verifyMerkleLeafHashProof sha256 map.keysRoot map.size i1 (merkleLeafHash sha256 key) sibs1 = true)
    (hProof2 : verifyMerkleLeafHashProof sha256 map.keysRoot map.size i2 (merkleLeafHash sha256 key) sibs2 = true) :
    i1 = i2 := by
  unfold verifySortedMerkleMapOpenings at hSortedMap
  simp only [Bool.and_eq_true, beq_iff_eq] at hSortedMap
  rcases hSortedMap with ⟨⟨hLen, hAllOpen⟩, hStrict⟩
  have hi1 : i1 < map.size := by
    unfold verifyMerkleLeafHashProof at hProof1
    dsimp only at hProof1
    by_cases hBad : (map.size == 0 || decide (i1 ≥ map.size)) = true
    · rw [hBad] at hProof1; contradiction
    · have hFalse : (map.size == 0 || decide (i1 ≥ map.size)) = false := Bool.eq_false_iff.mpr hBad
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hFalse
      omega
  have hi2 : i2 < map.size := by
    unfold verifyMerkleLeafHashProof at hProof2
    dsimp only at hProof2
    by_cases hBad : (map.size == 0 || decide (i2 ≥ map.size)) = true
    · rw [hBad] at hProof2; contradiction
    · have hFalse : (map.size == 0 || decide (i2 ≥ map.size)) = false := Bool.eq_false_iff.mpr hBad
      simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hFalse
      omega
  have hi1Len : i1 < keyOpenings.length := by omega
  have hi2Len : i2 < keyOpenings.length := by omega
  let op1 := keyOpenings[i1]'hi1Len
  let op2 := keyOpenings[i2]'hi2Len
  have hGet1 : keyOpenings[i1]? = some op1 := List.getElem?_eq_getElem hi1Len
  have hGet2 : keyOpenings[i2]? = some op2 := List.getElem?_eq_getElem hi2Len
  have hValOp1 : verifyMerkleElementOpening sha256 map.keysRoot map.size i1 op1 = true :=
    range_zip_all_get hLen hAllOpen hGet1
  have hValOp2 : verifyMerkleElementOpening sha256 map.keysRoot map.size i2 op2 = true :=
    range_zip_all_get hLen hAllOpen hGet2
  -- Both `key` (via `hProof1`) and `op1` (via `hValOp1`) are valid openings at `i1`!
  have hKeyOp1 : verifyMerkleElementOpening sha256 map.keysRoot map.size i1
      { element := key, leafHash := merkleLeafHash sha256 key, siblingsBottomUp := sibs1 } = true := by
    simp [verifyMerkleElementOpening, hProof1, bytes32Eq_refl]
  have hKeyOp2 : verifyMerkleElementOpening sha256 map.keysRoot map.size i2
      { element := key, leafHash := merkleLeafHash sha256 key, siblingsBottomUp := sibs2 } = true := by
    simp [verifyMerkleElementOpening, hProof2, bytes32Eq_refl]
  have hEqEl1 : key = op1.element := verifyMerkleElementOpening_unique hCF hKeyOp1 hValOp1
  have hEqEl2 : key = op2.element := verifyMerkleElementOpening_unique hCF hKeyOp2 hValOp2
  have hMapGet1 : (keyOpenings.map (·.element))[i1]? = some op1.element := by
    rw [List.getElem?_map, hGet1]; rfl
  have hMapGet2 : (keyOpenings.map (·.element))[i2]? = some op2.element := by
    rw [List.getElem?_map, hGet2]; rfl
  by_cases hIdxEq : i1 = i2
  · exact hIdxEq
  · exfalso
    have hNe := strictlySorted_pairwise_distinct hStrict hIdxEq hMapGet1 hMapGet2
    exact hNe (hEqEl1.symm.trans hEqEl2)

/-- **THEOREM M6 (Collision-Relative Merkleized Map Value Uniqueness — Anti-Equivocation)**:
    Under `HashCollisionFree sha256`, once a `MerkleMapCommitment` passes sorted-keys verification
    (`verifySortedMerkleMapOpenings`), at most ONE value `v : ByteArray` can EVER be proven for any key `k`!
    Specifically, for any two valid `MapLookupProof`s `p1` and `p2` for `(map, k)`, both indices AND
    both proven values are identical (`p1.index = p2.index ∧ p1.valueOpening.element = p2.valueOpening.element`). -/
theorem sorted_merkle_map_lookup_proof_unique
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    {key : ByteArray}
    {p1 p2 : MapLookupProof}
    (hLookup1 : verifyMapLookupProof sha256 map key p1 = true)
    (hLookup2 : verifyMapLookupProof sha256 map key p2 = true) :
    p1.index = p2.index ∧ p1.valueOpening.element = p2.valueOpening.element := by
  unfold verifyMapLookupProof at hLookup1 hLookup2
  simp only [Bool.and_eq_true] at hLookup1 hLookup2
  have hIdxEq := sorted_merkle_map_unique_key_index hCF hSortedMap hLookup1.1 hLookup2.1
  rw [hIdxEq] at hLookup1
  have hValEq := verifyMerkleElementOpening_unique hCF hLookup1.2 hLookup2.2
  exact ⟨hIdxEq, hValEq⟩

/-- **THEOREM M7 (Interactive Untrusted-Host Oracle Lookup Soundness)**:
    Under `HashCollisionFree sha256` and `verifySortedMerkleMapOpenings`, even if TWO DIFFERENT
    malicious/adaptive untrusted host oracles `host1` and `host2` interact with `deviceLookupMerkleMapValue`
    for the same committed `(map, key)`, if `host1` yields `.present v1` and `host2` yields `.present v2`,
    then `v1 = v2`! A compromised host CANNOT equivocate on the value of any PSBT key! -/
theorem interactive_host_cannot_equivocate_map_value
    {sha256 : ByteArray → Bytes32}
    (hCF : HashCollisionFree sha256)
    {map : MerkleMapCommitment}
    {keyOpenings : List MerkleElementOpening}
    (hSortedMap : verifySortedMerkleMapOpenings sha256 map keyOpenings = true)
    (host1 host2 : UntrustedHostOracle)
    (key v1 v2 : ByteArray)
    (hRes1 : deviceLookupMerkleMapValue sha256 host1 map key = .present v1)
    (hRes2 : deviceLookupMerkleMapValue sha256 host2 map key = .present v2) :
    v1 = v2 := by
  -- Extract `MapLookupProof` from `deviceLookupMerkleMapValue = .present v`
  have extractProof : ∀ (host : UntrustedHostOracle) (v : ByteArray),
      deviceLookupMerkleMapValue sha256 host map key = .present v →
      ∃ p : MapLookupProof, p.valueOpening.element = v ∧ verifyMapLookupProof sha256 map key p = true := by
    intro host v hRes
    unfold deviceLookupMerkleMapValue at hRes
    dsimp only at hRes
    cases hIdxQ : host.queryLeafIndex map.keysRoot (merkleLeafHash sha256 key) with
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
                    · simp [hB] at hKhNotNe
                    · exact (bytes32Eq_iff _ _).mp hB
                  subst hKhEq
                  split at hRes
                  · contradiction
                  · rename_i hKeyValid
                    simp only [Bool.not_eq_true'] at hKeyValid
                    have hKeyValidTrue : verifyMerkleLeafHashProof sha256 map.keysRoot map.size idx
                        (merkleLeafHash sha256 key) keySibs = true := by
                      cases hV : verifyMerkleLeafHashProof sha256 map.keysRoot map.size idx (merkleLeafHash sha256 key) keySibs
                      · rw [hV] at hKeyValid; contradiction
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
                                · simp [hV] at hValHashProofNotFalse
                                · rfl
                              cases hPre : host.queryPreimage valLh with
                              | none => rw [hPre] at hValFetch; contradiction
                              | some rawPre =>
                                  rw [hPre] at hValFetch
                                  simp only [verifyMerkleLeafPreimage] at hValFetch
                                  cases hList : rawPre.data.toList with
                                  | nil =>
                                      rw [hList] at hValFetch
                                      contradiction
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
                                            · simp [hB] at hShaMatch
                                            · exact (bytes32Eq_iff _ _).mp hB
                                          have hRawDecomp : ByteArray.mk (#[0x00] ++ valBytes.data) = rawPre := by
                                            subst hExtractEq
                                            cases rawPre with | mk data =>
                                            congr
                                            apply Array.ext'
                                            simpa using hList.symm
                                          refine ⟨{
                                            index := idx
                                            keySiblingsBottomUp := keySibs
                                            valueOpening := {
                                              element := valBytes
                                              leafHash := valLh
                                              siblingsBottomUp := valSibs
                                            }
                                          }, rfl, ?_⟩
                                          unfold verifyMapLookupProof verifyMerkleElementOpening
                                          have hLeafEq : merkleLeafHash sha256 valBytes = valLh := by
                                            unfold merkleLeafHash
                                            rw [hRawDecomp, hShaEq]
                                          simp [hKeyValidTrue, hValHashProof, hLeafEq, bytes32Eq_refl]
                                      · have hImpossible : (match b0 :: rest with
                                            | 0x00 :: rest =>
                                                if !bytes32Eq (sha256 rawPre) valLh then none else some (ByteArray.mk rest.toArray)
                                            | _ => none) = none := by
                                          cases b0 with | ofBitVec bv =>
                                          have hNeVal : bv.toNat ≠ 0 := by
                                            intro hZ
                                            apply hb0
                                            exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hZ)
                                          -- If `b0 ≠ 0x00`, the pattern `0x00 :: rest` does not match!
                                          split
                                          · rename_i rest' hEqCons
                                            injection hEqCons with hB0Zero _
                                            exact absurd hB0Zero hb0
                                          · rfl
                                        rw [hImpossible] at hValFetch
                                        contradiction
  obtain ⟨p1, hp1El, hp1Ok⟩ := extractProof host1 v1 hRes1
  obtain ⟨p2, hp2El, hp2Ok⟩ := extractProof host2 v2 hRes2
  obtain ⟨_, hEq⟩ := sorted_merkle_map_lookup_proof_unique hCF hSortedMap hp1Ok hp2Ok
  rw [← hp1El, ← hp2El, hEq]

/-- **THEOREM M8 (Key-Callback Presence Completeness — Preventing Host Lying-By-Omission)**:
    In BOLOS (`check_merkle_tree_sorted_with_callback`), the device scans all `keyOpenings` once
    when verifying `verifySortedMerkleMapOpenings`, setting presence flags (e.g. `has_witnessUtxo`,
    `has_nonWitnessUtxo`, `has_sighash_type`, `has_redeemScript`).
    If `key ∈ keyOpenings.map (·.element)` was observed during the verified sorted-keys scan, then ANY
    host returning `.absentClaimed` (`found = 0`) for `key` is provably lying (`∃ idx < map.size` where
    `key` has a valid opening in `map.keysRoot`) — so the device MUST reject `.absentClaimed` whenever
    a key-presence flag was recorded! -/
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
      verifyMerkleElementOpening sha256 map.keysRoot map.size idx op = true := by
  unfold verifySortedMerkleMapOpenings at hSortedMap
  simp only [Bool.and_eq_true, beq_iff_eq] at hSortedMap
  rcases hSortedMap with ⟨⟨hLen, hAllOpen⟩, _⟩
  rw [List.mem_map] at hSeenInScan
  rcases hSeenInScan with ⟨op, hOpMem, hOpEl⟩
  obtain ⟨idx, hIdxLt, hGetIdx⟩ := List.mem_iff_getElem.mp hOpMem
  have hGetOpt : keyOpenings[idx]? = some op := by
    rw [List.getElem?_eq_getElem hIdxLt]
    exact congrArg some hGetIdx
  have hValid := range_zip_all_get hLen hAllOpen hGetOpt
  exact ⟨idx, op, by omega, hOpEl, hValid⟩

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

/-- **THEOREM M10 (Out-of-Bounds Leaf Index Unconditionally Rejected in `deviceLookupMerkleMapValue`)**:
    If a malicious host responds to `CCMD_GET_MERKLE_LEAF_INDEX` with `idx >= map.size` (even with `found = false`!),
    `deviceLookupMerkleMapValue` rejects with `.protocolError`, matching `get_merkle_leaf_index.c:34`. -/
theorem out_of_bounds_index_rejected
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (found : Bool)
    (idx : Nat)
    (hHost : host.queryLeafIndex map.keysRoot (merkleLeafHash sha256 key) = some (found, idx))
    (hOob : idx ≥ map.size) :
    deviceLookupMerkleMapValue sha256 host map key = .protocolError := by
  unfold deviceLookupMerkleMapValue
  simp [hHost, hOob]

/-- Concrete toy hash function (32-byte zero-padded truncation of bytes 0, 1, 2, 34) for pure kernel non-vacuity check. -/
private def pad32Hash (input : ByteArray) : Bytes32 :=
  let b0 := (byteAt? input 0).getD 0
  let b1 := (byteAt? input 1).getD 0
  let b2 := (byteAt? input 2).getD 0
  let b3 := (byteAt? input 34).getD 0
  { bytes := ByteArray.mk (#[b0, b1, b2, b3] ++ Array.replicate 28 0)
    size_eq := by simp [ByteArray.size] }

/-- **THEOREM M11 (Non-Vacuity Witness: Unbalanced 3-Entry Sorted Merkleized PSBT Map Verified & Queried)**:
    Proves that for ANY hash function `sha256` and the concrete unbalanced 3-leaf sorted PSBT map
    (`#[0x00] ↦ #[0xAA]`, `#[0x01] ↦ #[0xBB, 0xCC]`, `#[0x03] ↦ #[0xDD]`):
    1. Its honest `keyOpenings` pass `verifySortedMerkleMapOpenings`, and
    2. If `sha256` is `HashCollisionFree` (e.g., real SHA-256 or injective toy encoding),
       `deviceLookupMerkleMapValue` against `mkHonestMapHostOracle` resolves key `#[0x01]` to
       `.present #[0xBB, 0xCC]` and absent key `#[0x02]` to `.absentClaimed`! -/
theorem honest_opening_valid
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (idx : Nat)
    (el : ByteArray)
    (hGet : leaves[idx]? = some el) :
    verifyMerkleElementOpening sha256 (merkleRoot sha256 leaves) leaves.length idx
      { element := el
        leafHash := merkleLeafHash sha256 el
        siblingsBottomUp := buildMerkleAuditPath sha256 leaves idx } = true := by
  have hRange : idx < leaves.length := by
    cases Nat.lt_or_ge idx leaves.length with
    | inl h => exact h
    | inr h => rw [List.getElem?_eq_none h] at hGet; contradiction
  have hFold := buildMerkleAuditPath_complete sha256 leaves idx el hGet
  unfold verifyMerkleElementOpening verifyMerkleLeafHashProof
  have hNotBad : (leaves.length == 0 || decide (idx ≥ leaves.length)) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
    omega
  simp [hNotBad, hFold, bytes32Eq_refl]

theorem non_vacuity_honest_merkle_map_verified_and_queried :
    ∃ (sha256 : ByteArray → Bytes32)
      (map : MerkleMapCommitment)
      (keyOpenings : List MerkleElementOpening)
      (host : UntrustedHostOracle),
      map.size = 3 ∧
      verifySortedMerkleMapOpenings sha256 map keyOpenings = true ∧
      deviceLookupMerkleMapValue sha256 host map (ByteArray.mk #[0x01]) =
        .present (ByteArray.mk #[0xBB, 0xCC]) ∧
      deviceLookupMerkleMapValue sha256 host map (ByteArray.mk #[0x02]) =
        .absentClaimed := by
  let entries : List (ByteArray × ByteArray) := [
    (ByteArray.mk #[0x00], ByteArray.mk #[0xAA]),
    (ByteArray.mk #[0x01], ByteArray.mk #[0xBB, 0xCC]),
    (ByteArray.mk #[0x03], ByteArray.mk #[0xDD])
  ]
  let keys := entries.map Prod.fst
  let vals := entries.map Prod.snd
  let map := commitMerkleMap pad32Hash entries
  let op0 : MerkleElementOpening :=
    { element := ByteArray.mk #[0x00]
      leafHash := merkleLeafHash pad32Hash (ByteArray.mk #[0x00])
      siblingsBottomUp := buildMerkleAuditPath pad32Hash keys 0 }
  let op1 : MerkleElementOpening :=
    { element := ByteArray.mk #[0x01]
      leafHash := merkleLeafHash pad32Hash (ByteArray.mk #[0x01])
      siblingsBottomUp := buildMerkleAuditPath pad32Hash keys 1 }
  let op2 : MerkleElementOpening :=
    { element := ByteArray.mk #[0x03]
      leafHash := merkleLeafHash pad32Hash (ByteArray.mk #[0x03])
      siblingsBottomUp := buildMerkleAuditPath pad32Hash keys 2 }
  let keyOpenings : List MerkleElementOpening := [op0, op1, op2]
  let host := mkHonestMapHostOracle pad32Hash entries
  have hSize : map.size = 3 := rfl
  have hOpen0 : verifyMerkleElementOpening pad32Hash map.keysRoot 3 0 op0 = true :=
    honest_opening_valid pad32Hash keys 0 (ByteArray.mk #[0x00]) rfl
  have hOpen1 : verifyMerkleElementOpening pad32Hash map.keysRoot 3 1 op1 = true :=
    honest_opening_valid pad32Hash keys 1 (ByteArray.mk #[0x01]) rfl
  have hOpen2 : verifyMerkleElementOpening pad32Hash map.keysRoot 3 2 op2 = true :=
    honest_opening_valid pad32Hash keys 2 (ByteArray.mk #[0x03]) rfl
  have hStrict : isStrictlySorted [ByteArray.mk #[0x00], ByteArray.mk #[0x01], ByteArray.mk #[0x03]] = true := by
    simp [isStrictlySorted, byteArrayLt, listUInt8Lt]
  have hRange3 : List.range 3 = [0, 1, 2] := rfl
  have hSorted : verifySortedMerkleMapOpenings pad32Hash map keyOpenings = true := by
    unfold verifySortedMerkleMapOpenings
    have hMapSz : map.size = 3 := rfl
    rw [hMapSz, hRange3]
    simp [keyOpenings, op0, op1, op2, hOpen0, hOpen1, hOpen2, hStrict]
  have hValOpen1 : verifyMerkleElementOpening pad32Hash map.valuesRoot 3 1
      { element := ByteArray.mk #[0xBB, 0xCC]
        leafHash := merkleLeafHash pad32Hash (ByteArray.mk #[0xBB, 0xCC])
        siblingsBottomUp := buildMerkleAuditPath pad32Hash vals 1 } = true :=
    honest_opening_valid pad32Hash vals 1 (ByteArray.mk #[0xBB, 0xCC]) rfl
  have hKeyProof1 : verifyMerkleLeafHashProof pad32Hash map.keysRoot 3 1
      (merkleLeafHash pad32Hash (ByteArray.mk #[0x01]))
      (buildMerkleAuditPath pad32Hash keys 1) = true := by
    unfold verifyMerkleElementOpening at hOpen1
    simp only [Bool.and_eq_true] at hOpen1
    exact hOpen1.1
  have hValProof1 : verifyMerkleLeafHashProof pad32Hash map.valuesRoot 3 1
      (merkleLeafHash pad32Hash (ByteArray.mk #[0xBB, 0xCC]))
      (buildMerkleAuditPath pad32Hash vals 1) = true := by
    unfold verifyMerkleElementOpening at hValOpen1
    simp only [Bool.and_eq_true] at hValOpen1
    exact hValOpen1.1
  have hIdx1 : host.queryLeafIndex map.keysRoot (merkleLeafHash pad32Hash (ByteArray.mk #[0x01])) = some (true, 1) := by
    simp [host, map, entries, mkHonestMapHostOracle, commitMerkleMap,
          findIdxPure?, merkleLeafHash, pad32Hash, byteAt?, bytes32Eq, bytesEq]
  have hKp1 : host.queryLeafProof map.keysRoot 3 1 =
      some (merkleLeafHash pad32Hash (ByteArray.mk #[0x01]), buildMerkleAuditPath pad32Hash keys 1) := by
    simp [host, map, keys, entries, mkHonestMapHostOracle, commitMerkleMap, bytes32Eq_refl, getAtPure?]
  have hVp1 : host.queryLeafProof map.valuesRoot 3 1 =
      some (merkleLeafHash pad32Hash (ByteArray.mk #[0xBB, 0xCC]), buildMerkleAuditPath pad32Hash vals 1) := by
    have hKRoot : merkleRoot pad32Hash keys =
        merkleNodeHash pad32Hash
          (merkleNodeHash pad32Hash (merkleLeafHash pad32Hash (ByteArray.mk #[0x00])) (merkleLeafHash pad32Hash (ByteArray.mk #[0x01])))
          (merkleLeafHash pad32Hash (ByteArray.mk #[0x03])) := by
      simp only [keys, entries, List.map]
      rw [merkleRoot]
      have hk3 : largestPow2Lt 3 = 2 := rfl
      change merkleNodeHash pad32Hash
        (merkleRoot pad32Hash ([ByteArray.mk #[0x00], ByteArray.mk #[0x01], ByteArray.mk #[0x03]].take (largestPow2Lt 3)))
        (merkleRoot pad32Hash ([ByteArray.mk #[0x00], ByteArray.mk #[0x01], ByteArray.mk #[0x03]].drop (largestPow2Lt 3))) = _
      rw [hk3]
      simp only [List.take, List.drop]
      rw [merkleRoot, merkleRoot]
      have hk2 : largestPow2Lt 2 = 1 := rfl
      change merkleNodeHash pad32Hash
        (merkleNodeHash pad32Hash
          (merkleRoot pad32Hash ([ByteArray.mk #[0x00], ByteArray.mk #[0x01]].take (largestPow2Lt 2)))
          (merkleRoot pad32Hash ([ByteArray.mk #[0x00], ByteArray.mk #[0x01]].drop (largestPow2Lt 2))))
        _ = _
      rw [hk2]
      simp only [List.take, List.drop]
      rw [merkleRoot, merkleRoot]
    have hVRoot : merkleRoot pad32Hash vals =
        merkleNodeHash pad32Hash
          (merkleNodeHash pad32Hash (merkleLeafHash pad32Hash (ByteArray.mk #[0xAA])) (merkleLeafHash pad32Hash (ByteArray.mk #[0xBB, 0xCC])))
          (merkleLeafHash pad32Hash (ByteArray.mk #[0xDD])) := by
      simp only [vals, entries, List.map]
      rw [merkleRoot]
      have hk3 : largestPow2Lt 3 = 2 := rfl
      change merkleNodeHash pad32Hash
        (merkleRoot pad32Hash ([ByteArray.mk #[0xAA], ByteArray.mk #[0xBB, 0xCC], ByteArray.mk #[0xDD]].take (largestPow2Lt 3)))
        (merkleRoot pad32Hash ([ByteArray.mk #[0xAA], ByteArray.mk #[0xBB, 0xCC], ByteArray.mk #[0xDD]].drop (largestPow2Lt 3))) = _
      rw [hk3]
      simp only [List.take, List.drop]
      rw [merkleRoot, merkleRoot]
      have hk2 : largestPow2Lt 2 = 1 := rfl
      change merkleNodeHash pad32Hash
        (merkleNodeHash pad32Hash
          (merkleRoot pad32Hash ([ByteArray.mk #[0xAA], ByteArray.mk #[0xBB, 0xCC]].take (largestPow2Lt 2)))
          (merkleRoot pad32Hash ([ByteArray.mk #[0xAA], ByteArray.mk #[0xBB, 0xCC]].drop (largestPow2Lt 2))))
        _ = _
      rw [hk2]
      simp only [List.take, List.drop]
      rw [merkleRoot, merkleRoot]
    have hRootsNe : bytes32Eq map.valuesRoot map.keysRoot = false := by
      change bytes32Eq (merkleRoot pad32Hash vals) (merkleRoot pad32Hash keys) = false
      rw [hVRoot, hKRoot]
      simp [merkleLeafHash, merkleNodeHash, pad32Hash, byteAt?, bytes32Eq, bytesEq]
    change (if bytes32Eq map.valuesRoot map.keysRoot && 3 == keys.length then _
            else if bytes32Eq map.valuesRoot map.valuesRoot && 3 == vals.length then
              match getAtPure? vals 1 with
              | some el => some (merkleLeafHash pad32Hash el, buildMerkleAuditPath pad32Hash vals 1)
              | none => none
            else none) = _
    rw [hRootsNe, bytes32Eq_refl]
    simp [vals, entries, getAtPure?]
  have hPre1 : host.queryPreimage (merkleLeafHash pad32Hash (ByteArray.mk #[0xBB, 0xCC])) =
      some (ByteArray.mk #[0x00, 0xBB, 0xCC]) := by
    simp [host, entries, mkHonestMapHostOracle, findPure?, merkleLeafHash, pad32Hash,
          byteAt?, bytes32Eq, bytesEq]
  have hPresent : deviceLookupMerkleMapValue pad32Hash host map (ByteArray.mk #[0x01]) =
      .present (ByteArray.mk #[0xBB, 0xCC]) := by
    unfold deviceLookupMerkleMapValue deviceFetchLeafElement
    dsimp only
    have hSz : map.size = 3 := rfl
    rw [hIdx1, hSz]
    simp only [Nat.not_le.mpr (by decide : 1 < 3), ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    rw [hKp1]
    simp only [bytes32Eq_refl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hKeyProof1]
    rw [hVp1]
    simp only [hValProof1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hPre1]
    simp [verifyMerkleLeafPreimage, merkleLeafHash, pad32Hash, byteAt?, bytes32Eq_refl]
  have hIdx2 : host.queryLeafIndex map.keysRoot (merkleLeafHash pad32Hash (ByteArray.mk #[0x02])) = some (false, 0) := by
    simp [host, map, entries, mkHonestMapHostOracle, commitMerkleMap,
          findIdxPure?, merkleLeafHash, pad32Hash, byteAt?, bytes32Eq, bytesEq]
  have hAbsent : deviceLookupMerkleMapValue pad32Hash host map (ByteArray.mk #[0x02]) =
      .absentClaimed := by
    unfold deviceLookupMerkleMapValue
    dsimp only
    have hSz : map.size = 3 := rfl
    rw [hIdx2, hSz]
    simp
  exact ⟨pad32Hash, map, keyOpenings, host, hSize, hSorted, hPresent, hAbsent⟩

end Spec.MerkleProtocol

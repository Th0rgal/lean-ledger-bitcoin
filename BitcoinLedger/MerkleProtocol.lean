import Spec

namespace BitcoinLedger.MerkleProtocol

open Spec.Psbt
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
# `BitcoinLedger.MerkleProtocol` — Executable BOLOS Interactive Merkle & Client-Command Engine

Executable constructive (`0 sorryAx`, `0 Classical.choice`, `0 native_decide`) implementation of
Ledger's BOLOS interactive Merkleized map/tree & `SW_INTERRUPTED_EXECUTION` (`0xE000`) client-command
commitment engine (`app-bitcoin/src/common/merkle.{h,c}`, `src/handler/client_commands.h`,
`src/handler/lib/check_merkle_tree_sorted.c`, `get_preimage.c`, `get_merkle_leaf_index.c`,
`get_merkleized_map.c`, `get_merkleized_map_value.c`).
-/

/-! ## 1. BOLOS APDU, Client-Command & Resource Bound Constants -/

/-- BOLOS Bitcoin application APDU class byte (`CLA_APP = 0xE1` in `constants.h`). -/
def CLA_APP : UInt8 := 0xE1

/-- BOLOS interrupted-execution continuation APDU class byte (`CLA_FRAMEWORK = 0xF8`). -/
def CLA_FRAMEWORK : UInt8 := 0xF8

/-- BOLOS interrupted-execution continuation APDU instruction byte (`INS_CONTINUE = 0x01`). -/
def INS_CONTINUE : UInt8 := 0x01

/-- BOLOS status word requesting an interactive host client-command response (`0xE000`). -/
def SW_INTERRUPTED_EXECUTION : UInt16 := 0xE000

/-- Client command `CCMD_YIELD = 0x10` (`client_commands.h`). -/
def CCMD_YIELD : UInt8 := 0x10

/-- Client command `CCMD_GET_PREIMAGE = 0x40` (`client_commands.h`). -/
def CCMD_GET_PREIMAGE : UInt8 := 0x40

/-- Client command `CCMD_GET_MERKLE_LEAF_PROOF = 0x41` (`client_commands.h`). -/
def CCMD_GET_MERKLE_LEAF_PROOF : UInt8 := 0x41

/-- Client command `CCMD_GET_MERKLE_LEAF_INDEX = 0x42` (`client_commands.h`). -/
def CCMD_GET_MERKLE_LEAF_INDEX : UInt8 := 0x42

/-- Client command `CCMD_GET_MORE_ELEMENTS = 0xA0` (`client_commands.h`). -/
def CCMD_GET_MORE_ELEMENTS : UInt8 := 0xA0

/-- Maximum Merkle audit path depth (`MAX_MERKLE_TREE_DEPTH = 32` in `merkle.h`). -/
def MAX_MERKLE_TREE_DEPTH : Nat := 32

/-- Maximum signed 32-bit Merkle leaf index (`INT_MAX = 0x7FFFFFFF` in `get_merkle_leaf_index.c:34`). -/
def MAX_MERKLE_LEAF_INDEX : Nat := 0x7FFFFFFF

/-- Maximum stack-allocated PSBT map key lookup header (`64` bytes in `get_merkleized_map_value`). -/
def MAX_MAP_KEY_HEADER_LEN : Nat := 64

/-- Maximum key length in sorted Merkleized maps (`128` bytes in `check_merkle_tree_sorted`). -/
def MAX_MERKLE_MAP_KEY_SIZE : Nat := 128

/-- Maximum 32-bit preimage length (`UINT32_MAX = 0xFFFFFFFF` in `get_preimage.c`). -/
def MAX_PREIMAGE_TOTAL_SIZE : Nat := 0xFFFFFFFF

/-- Maximum initial `CCMD_GET_PREIMAGE` inline slice (`uint8_t partial_data_len ≤ 255`). -/
def MAX_PREIMAGE_PARTIAL_SIZE : Nat := 255

/-- Maximum `CCMD_GET_MORE_ELEMENTS` elements per frame (`uint8_t n_elements ≤ 255`). -/
def MAX_MORE_ELEMENTS_COUNT : Nat := 255

/-! ## 2. Pure Constructive Byte Equality & Wire Encoding Helpers -/

def eqByteList : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide (x = y) && eqByteList xs ys
  | _, _ => false

def eqBytes (a b : ByteArray) : Bool :=
  eqByteList a.data.toList b.data.toList

def eqBytes32 (a b : Bytes32) : Bool :=
  eqBytes a.bytes b.bytes

def putU32BE (v : UInt32) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((v >>> 24).toNat % 256),
    UInt8.ofNat ((v >>> 16).toNat % 256),
    UInt8.ofNat ((v >>> 8).toNat % 256),
    UInt8.ofNat (v.toNat % 256)
  ]

/-! ## 3. RFC-6962 / Ledger `merkle.c` Hashing & Tail-Recursive Audit Engine -/

/-- Domain-separated leaf preimage `0x00 || data` (`merkle_compute_element_hash`). -/
def leafPreimage (data : ByteArray) : ByteArray :=
  ByteArray.mk (#[0x00] ++ data.data)

/-- Domain-separated internal node preimage `0x01 || left || right` (`merkle_combine_hashes`). -/
def nodePreimage (left right : Bytes32) : ByteArray :=
  ByteArray.mk (#[0x01] ++ left.bytes.data ++ right.bytes.data)

/-- Compute RFC-6962 / BOLOS leaf hash `SHA256(0x00 || data)`. -/
def merkleLeafHash (sha256 : ByteArray → Bytes32) (data : ByteArray) : Bytes32 :=
  sha256 (leafPreimage data)

/-- Compute RFC-6962 / BOLOS internal node hash `SHA256(0x01 || left || right)`. -/
def merkleNodeHash (sha256 : ByteArray → Bytes32) (left right : Bytes32) : Bytes32 :=
  sha256 (nodePreimage left right)

/-- Tail-recursive power-of-two doubler while `acc * 2 < n`. -/
def largestPow2LtLoop (n : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | fuel + 1, acc =>
      if acc * 2 < n then
        largestPow2LtLoop n fuel (acc * 2)
      else
        acc

/-- Largest power of two strictly less than `n` (for `n ≥ 2`). -/
def largestPow2Lt (n : Nat) : Nat :=
  largestPow2LtLoop n n 1

/-- Tail-recursive accumulator computing bottom-up Merkle audit directions in a single pass:
    Descending from the root, prepending each step `.left` / `.right` onto `acc` naturally yields
    the reversed (leaf-to-root) direction sequence without allocating and reversing an intermediate list! -/
def computeDirectionsAcc : Nat → Nat → Nat → List MerkleDir → List MerkleDir
  | 0, _, _, acc => acc
  | fuel + 1, size, index, acc =>
      if decide (2 ≤ size) && decide (index < size) then
        let k := largestPow2Lt size
        if index < k then
          computeDirectionsAcc fuel k index (.left :: acc)
        else
          computeDirectionsAcc fuel (size - k) (index - k) (.right :: acc)
      else
        acc

/-- Bottom-up (leaf-to-root) Merkle branch directions for `(size, index)`. -/
def merkleDirectionsBottomUp (size index : Nat) : List MerkleDir :=
  computeDirectionsAcc size size index []

/-- Top-down (root-to-leaf) Merkle branch directions for `(size, index)`. -/
def merkleDirections (size index : Nat) : List MerkleDir :=
  (merkleDirectionsBottomUp size index).reverse

/-- Tail-recursive bottom-up Merkle proof folder (`get_merkle_leaf_hash.c:96-112`). -/
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

/-- Executable BOLOS Merkle leaf-hash proof verifier (`get_merkle_leaf_hash.c` & `get_merkle_leaf_index.c:34`):
    Enforces `0 < treeSize`, `leafIndex < treeSize`, `leafIndex ≤ MAX_MERKLE_LEAF_INDEX (0x7FFFFFFF)`,
    `siblingsBottomUp.length ≤ MAX_MERKLE_TREE_DEPTH (32)`, exact leaf depth match, and root equality. -/
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
    let dirsBottomUp := merkleDirectionsBottomUp treeSize leafIndex
    match foldMerkleProofBottomUp sha256 leafHash dirsBottomUp siblingsBottomUp with
    | some computedRoot => eqBytes32 computedRoot expectedRoot
    | none => false

/-- Verify raw (non-`0x00`-prefixed) SHA-256 preimage (`get_preimage.c` / `stream_preimage.c`). -/
def verifyRawPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedHash : Bytes32)
    (rawPreimage : ByteArray) : Option ByteArray :=
  if decide (rawPreimage.size = 0) || decide (rawPreimage.size > MAX_PREIMAGE_TOTAL_SIZE) then
    none
  else if !eqBytes32 (sha256 rawPreimage) expectedHash then
    none
  else
    some rawPreimage

/-- Verify `0x00`-prefixed Merkle leaf preimage and strip the `0x00` prefix (`get_merkle_preimage.c`). -/
def verifyMerkleLeafPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (rawPreimageWithPrefix : ByteArray) : Option ByteArray :=
  if decide (rawPreimageWithPrefix.size > MAX_PREIMAGE_TOTAL_SIZE) then
    none
  else
    match rawPreimageWithPrefix.data.toList with
    | 0x00 :: rest =>
        if !eqBytes32 (sha256 rawPreimageWithPrefix) expectedLeafHash then
          none
        else
          some (ByteArray.mk rest.toArray)
    | _ => none

/-- Verify a complete Merkle element opening (`call_get_merkle_leaf_element`). -/
def verifyMerkleElementOpening
    (sha256 : ByteArray → Bytes32)
    (expectedRoot : Bytes32)
    (treeSize : Nat)
    (leafIndex : Nat)
    (opening : MerkleElementOpening) : Bool :=
  verifyMerkleLeafHashProof sha256 expectedRoot treeSize leafIndex opening.leafHash opening.siblingsBottomUp &&
  eqBytes32 (merkleLeafHash sha256 opening.element) opening.leafHash

/-- Fuel-bounded BOLOS Merkle root computation (`MTH([]) = zeroBytes32`, `MTH([d]) = H(0x00||d)`). -/
def merkleRootFuel (sha256 : ByteArray → Bytes32) : Nat → List ByteArray → Bytes32
  | 0, _ => zeroBytes32
  | _ + 1, [] => zeroBytes32
  | _ + 1, [x] => merkleLeafHash sha256 x
  | fuel + 1, x :: y :: rest =>
      let all := x :: y :: rest
      let k := largestPow2Lt all.length
      merkleNodeHash sha256
        (merkleRootFuel sha256 fuel (all.take k))
        (merkleRootFuel sha256 fuel (all.drop k))

/-- Compute BOLOS Merkle Tree Hash (`MTH(leaves)` in `doc/merkle.md`). -/
def merkleRoot (sha256 : ByteArray → Bytes32) (leaves : List ByteArray) : Bytes32 :=
  merkleRootFuel sha256 (leaves.length + 1) leaves

/-- Fuel-bounded bottom-up Merkle audit path builder. -/
def buildMerkleAuditPathFuel
    (sha256 : ByteArray → Bytes32) : Nat → List ByteArray → Nat → List Bytes32
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | _ + 1, [_], _ => []
  | fuel + 1, x :: y :: rest, index =>
      let all := x :: y :: rest
      let k := largestPow2Lt all.length
      if index < k then
        buildMerkleAuditPathFuel sha256 fuel (all.take k) index ++
          [merkleRoot sha256 (all.drop k)]
      else
        buildMerkleAuditPathFuel sha256 fuel (all.drop k) (index - k) ++
          [merkleRoot sha256 (all.take k)]

/-- Construct the honest bottom-up Merkle sibling audit path for `leaves[index]`. -/
def buildMerkleAuditPath
    (sha256 : ByteArray → Bytes32)
    (leaves : List ByteArray)
    (index : Nat) : List Bytes32 :=
  buildMerkleAuditPathFuel sha256 (leaves.length + 1) leaves index

/-! ## 4. Strict Lexicographic Key Sorting & Key Header Bounds (`check_merkle_tree_sorted.c`) -/

/-- Strict lexicographic byte-list comparison (`compare_byte_arrays < 0`). -/
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

/-- Strict lexicographic comparison on `ByteArray` keys (`a < b`). -/
def byteArrayLt (a b : ByteArray) : Bool :=
  listUInt8Lt a.data.toList b.data.toList

/-- Tail-recursive strict lexicographic key-list verifier. -/
def isStrictlySortedFrom (prev : ByteArray) : List ByteArray → Bool
  | [] => true
  | cur :: rest =>
      if byteArrayLt prev cur then
        isStrictlySortedFrom cur rest
      else
        false

/-- Verify strict pairwise lexicographic key order `k_0 < k_1 < ... < k_{n-1}`. -/
def isStrictlySorted : List ByteArray → Bool
  | [] => true
  | first :: rest => isStrictlySortedFrom first rest

/-- Enforce BOLOS stack-allocated PSBT key-header cap (`keyHeader.size ≤ MAX_MAP_KEY_HEADER_LEN = 64`). -/
def checkMapKeyHeaderBound (keyHeader : ByteArray) : Bool :=
  decide (keyHeader.size ≤ MAX_MAP_KEY_HEADER_LEN)

/-! ## 5. BOLOS Client-Command Codec & Stateful Streaming Preimage Accumulator -/

/-- Validate a top-level Bitcoin application APDU class byte (`CLA = 0xE1`). -/
def validateAppApduCla (cla : UInt8) : Bool :=
  decide (cla = CLA_APP)

/-- Validate a BOLOS interrupted-execution continuation APDU header (`CLA=0xF8, INS=0x01, P1=0, P2=0`). -/
def validateContinuationApdu (hdr : ContinuationApdu) : Bool :=
  decide (hdr.cla = CLA_FRAMEWORK) &&
  decide (hdr.ins = INS_CONTINUE) &&
  decide (hdr.p1 = 0) &&
  decide (hdr.p2 = 0)

/-- Encode a `ClientCommandTag` into its BOLOS 1-byte client-command opcode (`0x10`/`0x40`/`0x41`/`0x42`/`0xA0`). -/
def encodeClientCommandTag : ClientCommandTag → UInt8
  | .yield              => CCMD_YIELD
  | .getPreimage        => CCMD_GET_PREIMAGE
  | .getMerkleLeafProof => CCMD_GET_MERKLE_LEAF_PROOF
  | .getMerkleLeafIndex => CCMD_GET_MERKLE_LEAF_INDEX
  | .getMoreElements    => CCMD_GET_MORE_ELEMENTS

/-- Decode a BOLOS 1-byte client-command opcode into a `ClientCommandTag`. -/
def decodeClientCommandTag? (b : UInt8) : Option ClientCommandTag :=
  if decide (b = CCMD_YIELD) then some .yield
  else if decide (b = CCMD_GET_PREIMAGE) then some .getPreimage
  else if decide (b = CCMD_GET_MERKLE_LEAF_PROOF) then some .getMerkleLeafProof
  else if decide (b = CCMD_GET_MERKLE_LEAF_INDEX) then some .getMerkleLeafIndex
  else if decide (b = CCMD_GET_MORE_ELEMENTS) then some .getMoreElements
  else none

/-- Build a `0xE000` (`SW_INTERRUPTED_EXECUTION`) `CCMD_YIELD (0x10)` frame (`client_commands.h`). -/
def mkYieldFrame (payload : ByteArray) : DeviceInterruptFrame :=
  { command := .yield
    requestPayload := ByteArray.mk (#[CCMD_YIELD] ++ payload.data)
    statusWord := SW_INTERRUPTED_EXECUTION }

/-- Build a `0xE000` `CCMD_GET_PREIMAGE (0x40)` request frame: `[0x40, 0x00, hash(32)]` (`get_preimage.c:17-22`). -/
def mkGetPreimageFrame (hash : Bytes32) : DeviceInterruptFrame :=
  { command := .getPreimage
    requestPayload := ByteArray.mk (#[CCMD_GET_PREIMAGE, 0x00] ++ hash.bytes.data)
    statusWord := SW_INTERRUPTED_EXECUTION }

/-- Build a `0xE000` `CCMD_GET_MERKLE_LEAF_PROOF (0x41)` request frame:
    `[0x41, root(32), treeSize(u32be), leafIndex(u32be)]` (`client_commands.h:17`). -/
def mkGetMerkleLeafProofFrame (root : Bytes32) (treeSize leafIndex : UInt32) : DeviceInterruptFrame :=
  { command := .getMerkleLeafProof
    requestPayload :=
      ByteArray.mk (#[CCMD_GET_MERKLE_LEAF_PROOF] ++ root.bytes.data) ++
      putU32BE treeSize ++ putU32BE leafIndex
    statusWord := SW_INTERRUPTED_EXECUTION }

/-- Build a `0xE000` `CCMD_GET_MERKLE_LEAF_INDEX (0x42)` request frame:
    `[0x42, root(32), leafHash(32)]` (`get_merkle_leaf_index.c:18-23`). -/
def mkGetMerkleLeafIndexFrame (root leafHash : Bytes32) : DeviceInterruptFrame :=
  { command := .getMerkleLeafIndex
    requestPayload := ByteArray.mk (#[CCMD_GET_MERKLE_LEAF_INDEX] ++ root.bytes.data ++ leafHash.bytes.data)
    statusWord := SW_INTERRUPTED_EXECUTION }

/-- Build a `0xE000` `CCMD_GET_MORE_ELEMENTS (0xA0)` request frame: `[0xA0]` (`get_preimage.c:77`). -/
def mkGetMoreElementsFrame : DeviceInterruptFrame :=
  { command := .getMoreElements
    requestPayload := ByteArray.mk #[CCMD_GET_MORE_ELEMENTS]
    statusWord := SW_INTERRUPTED_EXECUTION }

/-- Stateful chunked preimage streaming accumulator (`stream_preimage.c` / `get_preimage.c`):
    Models the BOLOS device accumulator across `CCMD_GET_PREIMAGE (0x40)` followed by zero or more
    `CCMD_GET_MORE_ELEMENTS (0xA0)` continuation APDUs (`CLA=0xF8, INS=0x01`). -/
structure PreimageStreamState where
  expectedHash : Bytes32
  declaredTotalSize : Nat
  bytesRemaining : Nat
  buffer : ByteArray
  deriving DecidableEq

/-- Initialize `PreimageStreamState` from the initial `CCMD_GET_PREIMAGE (0x40)` host response (`get_preimage.c:28-75`). -/
def initPreimageStream
    (expectedHash : Bytes32)
    (init : PreimageInitFrame) : Except PreimageStreamError PreimageStreamState :=
  if !validateContinuationApdu init.continuation then
    .error .badContinuationHeader
  else if decide (init.declaredTotalSize = 0) || decide (init.declaredTotalSize > MAX_PREIMAGE_TOTAL_SIZE) then
    .error .invalidDeclaredLength
  else if decide (init.partialData.size > MAX_PREIMAGE_PARTIAL_SIZE) ||
          decide (init.partialData.size > init.declaredTotalSize) then
    .error .invalidPartialSliceLength
  else
    .ok {
      expectedHash := expectedHash
      declaredTotalSize := init.declaredTotalSize
      bytesRemaining := init.declaredTotalSize - init.partialData.size
      buffer := init.partialData
    }

/-- Feed a single `CCMD_GET_MORE_ELEMENTS (0xA0)` continuation chunk into `PreimageStreamState`
    (`get_preimage.c:86-115`). Rejects non-`0xF8/0x01` headers, `elementSize ≠ 1`, `nElements = 0`
    (anti-infinite-loop guard!), `nElements > 255`, payload size mismatch, and over-read past `bytesRemaining`. -/
def feedPreimageChunk
    (st : PreimageStreamState)
    (chunk : MoreElementsChunk) : Except PreimageStreamError PreimageStreamState :=
  if !validateContinuationApdu chunk.continuation then
    .error .badContinuationHeader
  else if decide (chunk.elementSize ≠ 1) then
    .error .invalidElementWidth
  else if decide (chunk.nElements = 0) || decide (chunk.nElements > MAX_MORE_ELEMENTS_COUNT) then
    .error .invalidChunkElementCount
  else if decide (chunk.chunkData.size ≠ chunk.nElements) then
    .error .chunkPayloadSizeMismatch
  else if decide (chunk.nElements > st.bytesRemaining) then
    .error .streamOverflowBeyondDeclared
  else
    .ok {
      expectedHash := st.expectedHash
      declaredTotalSize := st.declaredTotalSize
      bytesRemaining := st.bytesRemaining - chunk.nElements
      buffer := st.buffer ++ chunk.chunkData
    }

/-- Feed a sequence of `CCMD_GET_MORE_ELEMENTS` chunks into `PreimageStreamState`. -/
def feedPreimageChunks
    (st : PreimageStreamState) : List MoreElementsChunk → Except PreimageStreamError PreimageStreamState
  | [] => .ok st
  | c :: rest =>
      match feedPreimageChunk st c with
      | .error e => .error e
      | .ok st' => feedPreimageChunks st' rest

/-- Finalize a raw preimage stream: requires `bytesRemaining = 0` and `sha256 buffer == expectedHash`
    before releasing the verified buffer (`call_get_preimage` zeroizes output on mismatch!). -/
def finalizeRawPreimageStream
    (sha256 : ByteArray → Bytes32)
    (st : PreimageStreamState) : Except PreimageStreamError ByteArray :=
  if !decide (st.bytesRemaining = 0) then
    .error .streamTruncatedBeforeDeclared
  else if !eqBytes32 (sha256 st.buffer) st.expectedHash then
    .error .digestMismatch
  else
    .ok st.buffer

/-- Finalize a `0x00`-prefixed Merkle leaf preimage stream (`get_merkle_preimage.c`), enforcing and
    stripping the leading `0x00` RFC-6962 leaf domain separator. -/
def finalizeMerkleLeafPreimageStream
    (sha256 : ByteArray → Bytes32)
    (st : PreimageStreamState) : Except PreimageStreamError ByteArray :=
  match finalizeRawPreimageStream sha256 st with
  | .error e => .error e
  | .ok assembled =>
      match assembled.data.toList with
      | 0x00 :: rest => .ok (ByteArray.mk rest.toArray)
      | _ => .error .missingMerkleLeafPrefix

/-- Executable stateful streaming verifier for raw SHA-256 preimages (`stream_preimage.c` / `get_preimage.c`). -/
def streamVerifyRawPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedHash : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk) : Except PreimageStreamError ByteArray := do
  let st0 ← initPreimageStream expectedHash init
  let stF ← feedPreimageChunks st0 chunks
  finalizeRawPreimageStream sha256 stF

/-- Executable stateful streaming verifier for `0x00`-prefixed Merkle leaf preimages (`get_merkle_preimage.c`). -/
def streamVerifyMerkleLeafPreimage
    (sha256 : ByteArray → Bytes32)
    (expectedLeafHash : Bytes32)
    (init : PreimageInitFrame)
    (chunks : List MoreElementsChunk) : Except PreimageStreamError ByteArray := do
  let st0 ← initPreimageStream expectedLeafHash init
  let stF ← feedPreimageChunks st0 chunks
  finalizeMerkleLeafPreimageStream sha256 stF

/-! ## 6. Sorted Merkleized Map Commitments & PSBT Merkle Bundle Verification -/

/-- Canonical wire serialization of a `MerkleMapCommitment`: `varint(size) || keysRoot(32) || valuesRoot(32)`. -/
def serializeMerkleMapCommitment (m : MerkleMapCommitment) : ByteArray :=
  encodeVarInt m.size ++ m.keysRoot.bytes ++ m.valuesRoot.bytes

/-- Construct an honest `MerkleMapCommitment` from `(key, value)` pairs. -/
def commitMerkleMap (sha256 : ByteArray → Bytes32) (entries : List (ByteArray × ByteArray)) : MerkleMapCommitment :=
  { size := entries.length
    keysRoot := merkleRoot sha256 (entries.map Prod.fst)
    valuesRoot := merkleRoot sha256 (entries.map Prod.snd) }

/-- Single-pass tail-recursive verifier for `call_check_merkle_tree_sorted_with_callback`
    (`check_merkle_tree_sorted.c:25-55`):
    Walks `curIdx = 0 .. mapSize - 1`, checking at each step:
    1. `op.element.size ≤ MAX_MERKLE_MAP_KEY_SIZE (128)`,
    2. `verifyMerkleElementOpening sha256 keysRoot mapSize curIdx op`, and
    3. `prevKey < op.element` whenever `prevKey? = some prevKey`. -/
def verifySortedKeyOpeningsLoop
    (sha256 : ByteArray → Bytes32)
    (keysRoot : Bytes32)
    (mapSize : Nat)
    (curIdx : Nat)
    (prevKey? : Option ByteArray) : List MerkleElementOpening → Bool
  | [] => decide (curIdx = mapSize)
  | op :: rest =>
      let sizeOk := decide (op.element.size ≤ MAX_MERKLE_MAP_KEY_SIZE)
      let openOk := verifyMerkleElementOpening sha256 keysRoot mapSize curIdx op
      let orderOk := match prevKey? with
        | none => true
        | some prev => byteArrayLt prev op.element
      if sizeOk && openOk && orderOk then
        verifySortedKeyOpeningsLoop sha256 keysRoot mapSize (curIdx + 1) (some op.element) rest
      else
        false

/-- Executable sorted Merkleized map commitment verifier (`get_merkleized_map.c` + `check_merkle_tree_sorted.c`):
    - Enforces zero `keysRoot` and `valuesRoot` when `map.size = 0`,
    - Enforces exact opening count `keyOpenings.length = map.size`,
    - Runs single-pass `verifySortedKeyOpeningsLoop` over `0 .. map.size - 1`. -/
def verifySortedMerkleMapOpenings
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (keyOpenings : List MerkleElementOpening) : Bool :=
  let emptyOk :=
    if decide (map.size = 0) then
      eqBytes32 map.keysRoot zeroBytes32 && eqBytes32 map.valuesRoot zeroBytes32
    else
      true
  emptyOk &&
  decide (keyOpenings.length = map.size) &&
  verifySortedKeyOpeningsLoop sha256 map.keysRoot map.size 0 none keyOpenings

/-- Executable Merkleized map key-value lookup proof verifier (`verifyMerkleMapLookup`). -/
def verifyMerkleMapLookup
    (sha256 : ByteArray → Bytes32)
    (map : MerkleMapCommitment)
    (key : ByteArray)
    (proof : MapLookupProof) : Bool :=
  let keyHash := merkleLeafHash sha256 key
  verifyMerkleLeafHashProof sha256 map.keysRoot map.size proof.index keyHash proof.keySiblingsBottomUp &&
  verifyMerkleElementOpening sha256 map.valuesRoot map.size proof.index proof.valueOpening

/-- Alias matching `Spec.MerkleProtocol.verifyMapLookupProof`. -/
abbrev verifyMapLookupProof := verifyMerkleMapLookup

/-- Device-side interactive leaf element fetch (`call_get_merkle_leaf_element`). -/
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

/-- Device-side interactive Merkleized map lookup (`call_get_merkleized_map_value` in `get_merkleized_map_value.c`
    and `call_get_merkle_leaf_index` in `get_merkle_leaf_index.c:34-64`). -/
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
              if !eqBytes32 returnedKeyHash keyHash then
                .protocolError
              else if !verifyMerkleLeafHashProof sha256 map.keysRoot map.size idx returnedKeyHash keySiblings then
                .protocolError
              else
                match deviceFetchLeafElement sha256 host map.valuesRoot map.size idx with
                | some valBytes => .present valBytes
                | none => .protocolError

/-- Bounded PSBT map key-header lookup enforcing `keyHeader.size ≤ MAX_MAP_KEY_HEADER_LEN (64)`
    before querying the untrusted host (`get_merkleized_map_value`). -/
def deviceLookupBoundedKeyHeader
    (sha256 : ByteArray → Bytes32)
    (host : UntrustedHostOracle)
    (map : MerkleMapCommitment)
    (keyHeader : ByteArray) : MapLookupResult :=
  if !checkMapKeyHeaderBound keyHeader then
    .protocolError
  else
    deviceLookupMerkleMapValue sha256 host map keyHeader

/-- Verify a list of per-input or per-output `MerkleMapCommitment`s (and their sorted key openings)
    committed under a top-level `mapsRoot` Merkle tree (`inputsRoot` / `outputsRoot` in `SIGN_PSBT`). -/
def verifyMapCommitmentListLoop
    (sha256 : ByteArray → Bytes32)
    (mapsRoot : Bytes32)
    (totalCount : Nat)
    (curIdx : Nat) : List (MerkleMapCommitment × MerkleElementOpening × List MerkleElementOpening) → Bool
  | [] => decide (curIdx = totalCount)
  | (subMap, mapLeafOpening, subKeyOpenings) :: rest =>
      let serializedMatch := eqBytes mapLeafOpening.element (serializeMerkleMapCommitment subMap)
      let leafOpenOk := verifyMerkleElementOpening sha256 mapsRoot totalCount curIdx mapLeafOpening
      let keysSortedOk := verifySortedMerkleMapOpenings sha256 subMap subKeyOpenings
      if serializedMatch && leafOpenOk && keysSortedOk then
        verifyMapCommitmentListLoop sha256 mapsRoot totalCount (curIdx + 1) rest
      else
        false

/-- Verify a full PSBT Merkleized commitment bundle (`SIGN_PSBT` in `init_global_state.c`):
    1. Global map commitment has strictly sorted keys (`verifySortedMerkleMapOpenings`),
    2. All `nInputs` input map commitments open against `inputsRoot` (or `inputsRoot == zeroBytes32` when `nInputs = 0`)
       and each input map has strictly sorted keys,
    3. All `nOutputs` output map commitments open against `outputsRoot` (or `outputsRoot == zeroBytes32` when `nOutputs = 0`)
       and each output map has strictly sorted keys. -/
def verifyPsbtMerkleBundle
    (sha256 : ByteArray → Bytes32)
    (psbt : MerkleizedPsbtCommitment)
    (globalKeyOpenings : List MerkleElementOpening)
    (inputBundles : List (MerkleMapCommitment × MerkleElementOpening × List MerkleElementOpening))
    (outputBundles : List (MerkleMapCommitment × MerkleElementOpening × List MerkleElementOpening)) : Bool :=
  let globalOk := verifySortedMerkleMapOpenings sha256 psbt.globalMap globalKeyOpenings
  let inputsRootOk :=
    if decide (psbt.nInputs = 0) then eqBytes32 psbt.inputsRoot zeroBytes32 else true
  let outputsRootOk :=
    if decide (psbt.nOutputs = 0) then eqBytes32 psbt.outputsRoot zeroBytes32 else true
  globalOk &&
  inputsRootOk &&
  outputsRootOk &&
  decide (inputBundles.length = psbt.nInputs) &&
  decide (outputBundles.length = psbt.nOutputs) &&
  verifyMapCommitmentListLoop sha256 psbt.inputsRoot psbt.nInputs 0 inputBundles &&
  verifyMapCommitmentListLoop sha256 psbt.outputsRoot psbt.nOutputs 0 outputBundles

end BitcoinLedger.MerkleProtocol

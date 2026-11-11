import InternalSpec

/-!
# `BitcoinLedger.Musig2` — Executable BIP-327 MuSig2 & BIP-328 Implementation

Pure Lean 4 executable implementation of:
1. BIP-327 `KeySort`, second-unique-key optimization, `KeyAgg`, and BIP-328/341 `applyTweak`.
2. Synthetic aggregate xpub chaincode (`868087ca02a6f974c4598924c36b57762d32cb45717167e300622c7167e38965`)
   and per-input `(placeholderIdx, inputIdx)` derivation (`deriveMusigPerInputInfo`).
3. BOLOS vs Vanadium `psbt_session_id` derivation (`computeBolosPsbtSessionId`, `computeVanadiumPsbtSessionId`).
4. Deterministic synthetic nonce randomness (`syntheticRandIJ`), BIP-327 `nonceGen`, `nonceAgg`,
   `getSessionValues`, `partialSign`, and `partialSigAgg`.
5. Bounded NVRAM/RAM session store (`capacity = 32` / `28B` prefix on BOLOS, `capacity = 1` / `32B`
   on Vanadium) supporting Round-1 registration, atomic Round-2 nonce consumption, re-registration
   after Round-2 deletion, and self-pubnonce verification.

Written with zero `Classical.choice` (`decide`-based equality, pure `ByteArray.mk` / `Array`
loops) for clean freestanding 32-bit compilation and constructive refinement proofs in `Proofs.Musig2`.
-/

namespace BitcoinLedger.Musig2

open InternalSpec.Musig2 (
  SizedBytes Bytes32 CompressedPubKey XOnlyPubKey PubNonce
  PsbtSessionId RandRoot PartialSig SchnorrSig
  CurvePoint MusigCrypto MusigError KeyAggContext MusigTweak
  MusigSpendPath MusigPerInputInfo SecNonce SessionContext SessionValues
  NonceAggPkMode SessionLifecycle MusigSessionStore
  MusigSignTask MusigRound1Output MusigRound2TaskInput MusigRound2Output
  MusigOp MusigStepEvent
)

/-! ## 1. Domain Constants & Byte Encoding Primitives -/

/-- Secp256k1 group order `n`. -/
def secp256k1Order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- Maximum number of cosigner public keys in a Ledger `musig(...)` expression. -/
def maxPubkeysPerMusig : Nat := 5

/-- BOLOS persistent NVRAM MuSig2 session slot capacity (`32`). -/
def bolosMaxMusigSessions : Nat := 32

/-- Vanadium RAM MuSig2 session slot capacity (`1`). -/
def vanadiumMaxMusigSessions : Nat := 1

/-- BOLOS stored `psbt_session_id` prefix length (`28` bytes). -/
def bolosStoredIdPrefixLen : Nat := 28

/-- Maximum length of `PSBT_GLOBAL_MUSIG2_SESSION_ID` on BOLOS (`32` bytes). -/
def maxProprietarySessionIdLen : Nat := 32

/-- BIP-32 hardened child bit (`0x80000000`). -/
def bip32HardenedBit : UInt32 := 0x80000000

/-- Fixed BIP-328 chaincode (`SHA256("MuSig2MuSig2MuSig2")`) bytes:
    `868087ca02a6f974c4598924c36b57762d32cb45717167e300622c7167e38965`. -/
def bip328ChaincodeBytes : List UInt8 :=
  [ 0x86, 0x80, 0x87, 0xCA, 0x02, 0xA6, 0xF9, 0x74,
    0xC4, 0x59, 0x89, 0x24, 0xC3, 0x6B, 0x57, 0x76,
    0x2D, 0x32, 0xCB, 0x45, 0x71, 0x71, 0x67, 0xE3,
    0x00, 0x62, 0x2C, 0x71, 0x67, 0xE3, 0x89, 0x65 ]

/-- Fixed BIP-328 synthetic aggregate xpub chaincode as `Bytes32`. -/
def bip328Chaincode : Bytes32 :=
  ⟨ByteArray.mk #[
      0x86, 0x80, 0x87, 0xCA, 0x02, 0xA6, 0xF9, 0x74,
      0xC4, 0x59, 0x89, 0x24, 0xC3, 0x6B, 0x57, 0x76,
      0x2D, 0x32, 0xCB, 0x45, 0x71, 0x71, 0x67, 0xE3,
      0x00, 0x62, 0x2C, 0x71, 0x67, 0xE3, 0x89, 0x65 ],
    rfl⟩

/-- Pure byte-list equality (`0 Classical.choice`). -/
def byteListEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a = b) && byteListEq as bs
  | _, _ => false

/-- Pure universal list check (`0 Classical.choice`). -/
def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

/-- Pure list membership check (`0 Classical.choice`). -/
def listMem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || listMem x ys

/-- Check whether every byte of `b` is zero. -/
def isAllZeros {n : Nat} (b : SizedBytes n) : Bool :=
  listAll (fun x => decide (x = 0)) b.bytes.data.toList

/-- Compare two `PsbtSessionId`s on their first `idMatchBytes` bytes (`28` on BOLOS, `32` on Vanadium). -/
def sessionIdPrefixEq (idMatchBytes : Nat) (a b : PsbtSessionId) : Bool :=
  byteListEq (a.bytes.data.toList.take idMatchBytes) (b.bytes.data.toList.take idMatchBytes)

/-- Pure `ByteArray` concatenation avoiding `@[extern]` `copySlice`. -/
def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

/-- Pure multi-`ByteArray` concatenation. -/
def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl appendBytes (ByteArray.mk #[])

/-- Concatenate two `SizedBytes`. -/
def appendSized {m n : Nat} (a : SizedBytes m) (b : SizedBytes n) : SizedBytes (m + n) :=
  { bytes := ByteArray.mk (a.bytes.data ++ b.bytes.data)
    size_eq := by
      have ha : a.bytes.data.size = m := a.size_eq
      have hb : b.bytes.data.size = n := b.size_eq
      simp [ByteArray.size, ha, hb] }

/-- Extract `R_1` (first 33 bytes) of a 66-byte `PubNonce`. -/
def pubNonceR1 (pn : PubNonce) : CompressedPubKey :=
  let arr := (pn.bytes.data.toList.take 33).toArray
  have hlen : (ByteArray.mk arr).size = 33 := by
    have h1 : pn.bytes.data.toList.length = 66 := by
      rw [Array.length_toList]; exact pn.size_eq
    change arr.size = 33
    rw [List.size_toArray, List.length_take, h1]
    decide
  ⟨ByteArray.mk arr, hlen⟩

/-- Extract `R_2` (last 33 bytes) of a 66-byte `PubNonce`. -/
def pubNonceR2 (pn : PubNonce) : CompressedPubKey :=
  let arr := (pn.bytes.data.toList.drop 33).toArray
  have hlen : (ByteArray.mk arr).size = 33 := by
    have h1 : pn.bytes.data.toList.length = 66 := by
      rw [Array.length_toList]; exact pn.size_eq
    change arr.size = 33
    rw [List.size_toArray, List.length_drop, h1]
  ⟨ByteArray.mk arr, hlen⟩

/-- Pack two 33-byte compressed points into a 66-byte `PubNonce`. -/
def mkPubNonce (r1 r2 : CompressedPubKey) : PubNonce :=
  appendSized r1 r2

/-- Extract the 32-byte x-only coordinate (`bytes[1..33]`) of a 33-byte compressed key. -/
def xOnlyOfCompressed (pk : CompressedPubKey) : XOnlyPubKey :=
  let arr := (pk.bytes.data.toList.drop 1).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    have h1 : pk.bytes.data.toList.length = 33 := by
      rw [Array.length_toList]; exact pk.size_eq
    change arr.size = 32
    rw [List.size_toArray, List.length_drop, h1]
  ⟨ByteArray.mk arr, hlen⟩

/-- Encode `UInt32` in big-endian (4 bytes). -/
def encodeU32BE (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat ((n >>> 24) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat (n &&& 0xFF)
  ]

/-- Decode big-endian bytes to `Nat`. -/
def natFromBytesBE (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Tail-recursive big-endian byte encoder. -/
def natToBytesBEAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, v, acc => natToBytesBEAux k (v / 256) (UInt8.ofNat (v % 256) :: acc)

theorem natToBytesBEAux_length (k v : Nat) (acc : List UInt8) :
    (natToBytesBEAux k v acc).length = k + acc.length := by
  induction k generalizing v acc with
  | zero => simp [natToBytesBEAux]
  | succ k ih =>
    simp [natToBytesBEAux, ih, Nat.add_comm, Nat.add_left_comm]

/-- Serialize `v : Nat` as 32 big-endian bytes (`ser_256`). -/
def scalarToBytes32 (v : Nat) : Bytes32 :=
  let arr := (natToBytesBEAux 32 v []).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    change arr.size = 32
    rw [List.size_toArray, natToBytesBEAux_length]
    rfl
  ⟨ByteArray.mk arr, hlen⟩

/-- Decode a 32-byte big-endian integer. -/
def bytes32ToNat (b : Bytes32) : Nat :=
  natFromBytesBE b.bytes.data.toList

/-- Parse a strict scalar `< n`. -/
def parseScalarStrict (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if decide (s < secp256k1Order) then some s else none

/-- Parse a non-zero strict scalar `0 < s < n`. -/
def parseNonZeroScalar (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if decide (0 < s) && decide (s < secp256k1Order) then some s else none

/-- Reduce a 32-byte big-endian integer modulo `n`. -/
def parseScalarModN (b : Bytes32) : Nat :=
  bytes32ToNat b % secp256k1Order

/-! ## 2. BIP-327 `keySort` & Second-Unique-Key Optimization -/

/-- Lexicographical `≤` on byte lists. -/
def listLexLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else listLexLe as bs

/-- Lexicographical `≤` on 33-byte SEC1 compressed public keys. -/
def pubKeyLe (a b : CompressedPubKey) : Bool :=
  listLexLe a.bytes.data.toList b.bytes.data.toList

/-- Insert one compressed public key into an ascending-sorted list. -/
def insertPubKey (x : CompressedPubKey) : List CompressedPubKey → List CompressedPubKey
  | [] => [x]
  | y :: ys => if pubKeyLe x y then x :: y :: ys else y :: insertPubKey x ys

/-- BIP-327 `KeySort`: ascending lexicographical sort of compressed public keys. -/
def keySort : List CompressedPubKey → List CompressedPubKey
  | [] => []
  | x :: xs => insertPubKey x (keySort xs)

/-- Recursive finder for the first key distinct from `first` (`0 Classical.choice`). -/
def findSecondUnique (first : CompressedPubKey) : List CompressedPubKey → Option CompressedPubKey
  | [] => none
  | pk :: rest => if decide (pk ≠ first) then some pk else findSecondUnique first rest

/-- BIP-327 second-unique-key optimization (`get_second_key`):
    returns the first key in `pubkeys` distinct from `pubkeys[0]`, or `none` if empty/all-equal. -/
def secondUniqueKey : List CompressedPubKey → Option CompressedPubKey
  | [] => none
  | first :: rest => findSecondUnique first rest

/-! ## 3. BIP-327 `keyAgg`, BIP-328 Tweaking & Per-Input Info Derivation -/

/-- BIP-327 `cpoint`: strict SEC1 33-byte point decompression. -/
def cpoint {Affine : Type} (c : MusigCrypto Affine) (pk : CompressedPubKey) :
    Except MusigError Affine :=
  match c.decompress pk with
  | some p => .ok p
  | none => .error .invalidPoint

/-- BIP-327 `cpoint_ext`: decompress 33-byte point where 33 zero bytes encode infinity. -/
def cpointExt {Affine : Type} (c : MusigCrypto Affine) (pk : CompressedPubKey) :
    Except MusigError (CurvePoint Affine) :=
  if isAllZeros pk then
    .ok .infinity
  else
    match c.decompress pk with
    | some p => .ok (.affine p)
    | none => .error .invalidPoint

/-- `hash_keys(pk_1, ..., pk_u) = H_{"KeyAgg list"}(pk_1 || ... || pk_u)`. -/
def hashKeys {Affine : Type} (c : MusigCrypto Affine) (pubkeys : List CompressedPubKey) : Bytes32 :=
  let payload := pubkeys.foldl (fun acc pk => appendBytes acc pk.bytes) (ByteArray.mk #[])
  c.taggedHash "KeyAgg list" payload

/-- `KeyAgg_coeff_internal(pubkeys, pk, pk2)`: returns `1` for the second unique key, else
    `H_{"KeyAgg coefficient"}(L || pk) mod n`. -/
def keyAggCoeffInternal {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) (pk : CompressedPubKey)
    (pk2 : Option CompressedPubKey) : Nat :=
  if decide (pk2 = some pk) then
    1
  else
    let l := hashKeys c pubkeys
    parseScalarModN (c.taggedHash "KeyAgg coefficient" (appendBytes l.bytes pk.bytes))

/-- BIP-327 `KeyAgg_coeff(pubkeys, pk)`. -/
def keyAggCoeff {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) (pk : CompressedPubKey) : Nat :=
  keyAggCoeffInternal c pubkeys pk (secondUniqueKey pubkeys)

/-- Tail-recursive point accumulation `∑ a_i * P_i`. -/
def keyAggLoop {Affine : Type} (c : MusigCrypto Affine)
    (allPks : List CompressedPubKey) (pk2 : Option CompressedPubKey) :
    List CompressedPubKey → CurvePoint Affine → Except MusigError (CurvePoint Affine)
  | [], acc => .ok acc
  | pk :: rest, acc =>
    match cpoint c pk with
    | .error e => .error e
    | .ok p =>
      let a_i := keyAggCoeffInternal c allPks pk pk2
      let scaled := c.pointMul a_i (.affine p)
      keyAggLoop c allPks pk2 rest (c.pointAdd acc scaled)

/-- BIP-327 `KeyAgg(pubkeys)` producing initial `KeyAggContext` `(Q, gacc = 1, tacc = 0)`. -/
def keyAgg {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) : Except MusigError (KeyAggContext Affine) :=
  if pubkeys.isEmpty then
    .error .emptyPubkeyList
  else
    let pk2 := secondUniqueKey pubkeys
    match keyAggLoop c pubkeys pk2 pubkeys .infinity with
    | .error e => .error e
    | .ok .infinity => .error .keyAggInfinity
    | .ok (.affine q) => .ok { q := q, gacc := 1, tacc := 0 }

/-- BIP-327 `apply_tweak(ctx, tweak, is_xonly)`. -/
def applyTweak {Affine : Type} (c : MusigCrypto Affine)
    (ctx : KeyAggContext Affine) (tweak : MusigTweak) :
    Except MusigError (KeyAggContext Affine) :=
  match parseScalarStrict tweak.scalar with
  | none => .error .tweakOutOfRange
  | some t =>
    let g := if tweak.isXOnly && !c.hasEvenY ctx.q then secp256k1Order - 1 else 1
    let gQ := c.pointMul g (.affine ctx.q)
    let tG := c.pointMul t (.affine c.generator)
    match c.pointAdd gQ tG with
    | .infinity => .error .tweakInfinity
    | .affine q' =>
      .ok {
        q := q'
        gacc := (g * ctx.gacc) % secp256k1Order
        tacc := (g * ctx.tacc + t) % secp256k1Order
      }

/-- Apply a list of BIP-328 / BIP-341 tweaks sequentially. -/
def applyTweaks {Affine : Type} (c : MusigCrypto Affine)
    (ctx : KeyAggContext Affine) : List MusigTweak → Except MusigError (KeyAggContext Affine)
  | [] => .ok ctx
  | tw :: rest =>
    match applyTweak c ctx tw with
    | .error e => .error e
    | .ok ctx' => applyTweaks c ctx' rest

/-- Compute the BIP-341 `TapTweak` scalar (`H_{"TapTweak"}(xOnly(P) [|| taptreeHash])`). -/
def computeTapTweakScalar {Affine : Type} (c : MusigCrypto Affine)
    (internalAggPk : CompressedPubKey) (taptreeHash : Option Bytes32) : MusigTweak :=
  let xOnly := xOnlyOfCompressed internalAggPk
  let tapPayload := match taptreeHash with
    | none => xOnly.bytes
    | some h => appendBytes xOnly.bytes h.bytes
  { scalar := c.taggedHash "TapTweak" tapPayload, isXOnly := true }

/-- Derive per-`(inputIdx, placeholderIdx)` MuSig2 aggregate key & tweak stack:
    1. Sort participant keys via `keySort`,
    2. Compute untweaked `keyAgg`,
    3. Derive two unhardened BIP-32 child steps `(changeStep, addressIndex)` from synthetic
       chaincode `bip328Chaincode` (`868087ca...`),
    4. Apply x-only BIP-341 `TapTweak` on `.keypath`, or record `.tapscript leafHash`. -/
def deriveMusigPerInputInfo {Affine : Type} (c : MusigCrypto Affine)
    (participantPubkeys : List CompressedPubKey)
    (numFirst numSecond : UInt32)
    (isChange : Bool)
    (addressIndex : UInt32)
    (spend : MusigSpendPath) : Except MusigError MusigPerInputInfo :=
  if participantPubkeys.isEmpty then
    .error .emptyPubkeyList
  else if decide (participantPubkeys.length > maxPubkeysPerMusig) then
    .error .tooManyPubkeys
  else
    let changeStep : UInt32 := if isChange then numSecond else numFirst
    if decide (bip32HardenedBit ≤ changeStep) || decide (bip32HardenedBit ≤ addressIndex) then
      .error .derivationFailed
    else
      let sorted := keySort participantPubkeys
      match keyAgg c sorted with
      | .error e => .error e
      | .ok baseCtx =>
        let untweakedAggPk := c.compress baseCtx.q
        match c.ckdPubUnhardened untweakedAggPk bip328Chaincode changeStep with
        | none => .error .derivationFailed
        | some (child1Pk, child1Cc, t0) =>
          match c.ckdPubUnhardened child1Pk child1Cc addressIndex with
          | none => .error .derivationFailed
          | some (child2Pk, _child2Cc, t1) =>
            let tw0 : MusigTweak := { scalar := t0, isXOnly := false }
            let tw1 : MusigTweak := { scalar := t1, isXOnly := false }
            match spend with
            | .tapscript lh =>
              .ok {
                sortedPubkeys := sorted
                untweakedAggPk := untweakedAggPk
                preTapTweakAggPk := child2Pk
                tweakedAggPk := child2Pk
                tweaks := [tw0, tw1]
                leafHash := some lh
              }
            | .keypath treeOpt =>
              let tw2 := computeTapTweakScalar c child2Pk treeOpt
              match cpoint c child2Pk with
              | .error e => .error e
              | .ok child2Point =>
                match applyTweak c { q := child2Point, gacc := 1, tacc := 0 } tw2 with
                | .error e => .error e
                | .ok tweakedCtx =>
                  .ok {
                    sortedPubkeys := sorted
                    untweakedAggPk := untweakedAggPk
                    preTapTweakAggPk := child2Pk
                    tweakedAggPk := c.compress tweakedCtx.q
                    tweaks := [tw0, tw1, tw2]
                    leafHash := none
                  }

/-- Build a `MusigSignTask` for `(inputIdx, placeholderIdx)` from derived `MusigPerInputInfo`. -/
def deriveMusigSignTask {Affine : Type} (c : MusigCrypto Affine)
    (inputIndex placeholderIndex : UInt32)
    (internalPk : CompressedPubKey)
    (participantPubkeys : List CompressedPubKey)
    (numFirst numSecond : UInt32)
    (isChange : Bool)
    (addressIndex : UInt32)
    (spend : MusigSpendPath) : Except MusigError MusigSignTask :=
  match deriveMusigPerInputInfo c participantPubkeys numFirst numSecond isChange addressIndex spend with
  | .error e => .error e
  | .ok info =>
    .ok {
      inputIndex := inputIndex
      placeholderIndex := placeholderIndex
      internalPk := internalPk
      untweakedAggPk := info.untweakedAggPk
      tweakedAggPk := info.tweakedAggPk
      sortedPubkeys := info.sortedPubkeys
      tweaks := info.tweaks
      leafHash := info.leafHash
    }

/-! ## 4. Nonce Generation, Nonce Aggregation & Partial Signing -/

/-- BIP-327 `nonce_hash` specialized to Ledger's deterministic `(rand, pk, aggpk)` profile
    (`msg_prefixed = [0x00]`, `extra_in = empty`, tag `"MuSig/nonce"`). -/
def nonceHash {Affine : Type} (c : MusigCrypto Affine)
    (rand : ByteArray) (pk : CompressedPubKey) (aggpk : XOnlyPubKey) (idx : UInt8) : Bytes32 :=
  let msgPrefixed := ByteArray.mk #[0x00]
  let extraLenBE := encodeU32BE 0
  let payload := concatBytes [
    rand,
    ByteArray.mk #[33], pk.bytes,
    ByteArray.mk #[32], aggpk.bytes,
    msgPrefixed,
    extraLenBE,
    ByteArray.mk #[idx]
  ]
  c.taggedHash "MuSig/nonce" payload

/-- BIP-327 `NonceGen(rand, pk, aggpk)` producing `(SecNonce, PubNonce)`. -/
def nonceGen {Affine : Type} (c : MusigCrypto Affine)
    (rand : Bytes32) (pk : CompressedPubKey) (aggpk : XOnlyPubKey) :
    Except MusigError (SecNonce × PubNonce) :=
  let k1 := parseScalarModN (nonceHash c rand.bytes pk aggpk 0)
  let k2 := parseScalarModN (nonceHash c rand.bytes pk aggpk 1)
  if decide (k1 = 0) || decide (k2 = 0) then
    .error .nonceGenFailed
  else
    match c.pointMul k1 (.affine c.generator), c.pointMul k2 (.affine c.generator) with
    | .affine r1, .affine r2 =>
      let pn := mkPubNonce (c.compress r1) (c.compress r2)
      .ok ({ k1 := k1, k2 := k2, pk := pk }, pn)
    | _, _ => .error .nonceGenFailed

/-- Sum one component (`R_1` or `R_2`) across cosigner pubnonces, blaming `idx` on invalid point. -/
def sumNonceComponent {Affine : Type} (c : MusigCrypto Affine)
    (select : PubNonce → CompressedPubKey) :
    Nat → List PubNonce → CurvePoint Affine → Except MusigError CompressedPubKey
  | _, [], acc =>
    match acc with
    | .infinity => .ok (SizedBytes.zeros 33)
    | .affine r => .ok (c.compress r)
  | idx, pn :: rest, acc =>
    match c.decompress (select pn) with
    | none => .error (.invalidContribution idx)
    | some rij => sumNonceComponent c select (idx + 1) rest (c.pointAdd acc (.affine rij))

/-- BIP-327 `NonceAgg(pubnonces)`. -/
def nonceAgg {Affine : Type} (c : MusigCrypto Affine)
    (pubnonces : List PubNonce) : Except MusigError PubNonce :=
  if pubnonces.isEmpty then
    .error .emptyPubkeyList
  else
    match sumNonceComponent c pubNonceR1 0 pubnonces .infinity with
    | .error e => .error e
    | .ok r1 =>
      match sumNonceComponent c pubNonceR2 0 pubnonces .infinity with
      | .error e => .error e
      | .ok r2 => .ok (mkPubNonce r1 r2)

/-- Derive BIP-327 session values `(Q, gacc, tacc, b, R, e)`. -/
def getSessionValues {Affine : Type} (c : MusigCrypto Affine)
    (ctx : SessionContext) : Except MusigError (SessionValues Affine) :=
  match keyAgg c ctx.pubkeys with
  | .error e => .error e
  | .ok baseCtx =>
    match applyTweaks c baseCtx ctx.tweaks with
    | .error e => .error e
    | .ok tweakedCtx =>
      let qx := c.xCoord tweakedCtx.q
      let bBytes := c.taggedHash "MuSig/noncecoef" (concatBytes [ctx.aggnonce.bytes, qx.bytes, ctx.msg])
      let b := parseScalarModN bBytes
      match cpointExt c (pubNonceR1 ctx.aggnonce) with
      | .error e => .error e
      | .ok r1 =>
        match cpointExt c (pubNonceR2 ctx.aggnonce) with
        | .error e => .error e
        | .ok r2 =>
          let rPoint := c.pointAdd r1 (c.pointMul b r2)
          let rFinal := match rPoint with
            | .infinity => c.generator
            | .affine r => r
          let rx := c.xCoord rFinal
          let eBytes := c.taggedHash "BIP0340/challenge" (concatBytes [rx.bytes, qx.bytes, ctx.msg])
          let e := parseScalarModN eBytes
          .ok {
            q := tweakedCtx.q
            gacc := tweakedCtx.gacc
            tacc := tweakedCtx.tacc
            b := b
            r := rFinal
            e := e
          }

/-- BIP-327 Round-2 `partialSign(secnonce, sk, ctx)` producing a 32-byte partial signature. -/
def partialSign {Affine : Type} (c : MusigCrypto Affine)
    (secnonce : SecNonce) (skBytes : Bytes32) (ctx : SessionContext) :
    Except MusigError PartialSig :=
  match getSessionValues c ctx with
  | .error e => .error e
  | .ok vals =>
    if !(decide (0 < secnonce.k1) && decide (secnonce.k1 < secp256k1Order)) then
      .error .nonceOutOfRange
    else if !(decide (0 < secnonce.k2) && decide (secnonce.k2 < secp256k1Order)) then
      .error .nonceOutOfRange
    else
      let k1 := if c.hasEvenY vals.r then secnonce.k1 else secp256k1Order - secnonce.k1
      let k2 := if c.hasEvenY vals.r then secnonce.k2 else secp256k1Order - secnonce.k2
      match parseNonZeroScalar skBytes with
      | none => .error .secretKeyOutOfRange
      | some sk =>
        match c.pointMul sk (.affine c.generator) with
        | .infinity => .error .secretKeyOutOfRange
        | .affine pubPoint =>
          let computedPk := c.compress pubPoint
          if decide (computedPk ≠ secnonce.pk) then
            .error .pubkeyMismatch
          else if !listMem computedPk ctx.pubkeys then
            .error .pubkeyNotInList
          else
            let a := keyAggCoeff c ctx.pubkeys computedPk
            let g := if c.hasEvenY vals.q then 1 else secp256k1Order - 1
            let d := (g * vals.gacc * sk) % secp256k1Order
            let s := (k1 + vals.b * k2 + vals.e * a * d) % secp256k1Order
            .ok (scalarToBytes32 s)

/-- Helper loop summing strict partial signature scalars modulo `n`. -/
def sumPartialSigsLoop : List PartialSig → Nat → Except MusigError Nat
  | [], acc => .ok acc
  | psig :: rest, acc =>
    match parseScalarStrict psig with
    | none => .error .invalidPartialSignature
    | some s_i => sumPartialSigsLoop rest ((acc + s_i) % secp256k1Order)

/-- BIP-327 `PartialSigAgg(psigs, session_ctx)`. -/
def partialSigAgg {Affine : Type} (c : MusigCrypto Affine)
    (ctx : SessionContext) (psigs : List PartialSig) :
    Except MusigError SchnorrSig :=
  if decide (psigs.length ≠ ctx.pubkeys.length) then
    .error .invalidPartialSignature
  else
    match getSessionValues c ctx with
    | .error e => .error e
    | .ok vals =>
      match sumPartialSigsLoop psigs 0 with
      | .error e => .error e
      | .ok sumS =>
        let g := if c.hasEvenY vals.q then 1 else secp256k1Order - 1
        let sFinal := (sumS + vals.e * g * vals.tacc) % secp256k1Order
        .ok (appendSized (c.xCoord vals.r) (scalarToBytes32 sFinal))

/-! ## 5. Synthetic Nonce Randomness & BOLOS vs Vanadium `psbt_session_id` -/

/-- Exact 12-byte `"MuSig2 nonce"` domain prefix (`musig_signing.c:127`, `musig_signing.rs:34`). -/
def musig2NonceDomainTag : ByteArray :=
  ByteArray.mk #[0x4D, 0x75, 0x53, 0x69, 0x67, 0x32, 0x20, 0x6E, 0x6F, 0x6E, 0x63, 0x65]

/-- Deterministic per-`(inputIndex, placeholderIndex)` synthetic nonce randomness:
    `SHA256(rand_root || be32(inputIndex) || be32(placeholderIndex))`. -/
def syntheticRandIJ {Affine : Type} (c : MusigCrypto Affine)
    (randRoot : RandRoot) (inputIndex placeholderIndex : UInt32) : Bytes32 :=
  c.sha256 (concatBytes [randRoot.bytes, encodeU32BE inputIndex, encodeU32BE placeholderIndex])

/-- Explicit tagged `"MuSig2 nonce"` helper (`SHA256("MuSig2 nonce" || rand_root || be32(i) || be32(j))`). -/
def syntheticTaggedMusig2NonceRandIJ {Affine : Type} (c : MusigCrypto Affine)
    (randRoot : RandRoot) (inputIndex placeholderIndex : UInt32) : Bytes32 :=
  c.sha256 (concatBytes [
    musig2NonceDomainTag,
    randRoot.bytes,
    encodeU32BE inputIndex,
    encodeU32BE placeholderIndex
  ])

/-- BOLOS transaction-independent `psbt_session_id`:
    `H_{"PsbtSessionId"}(descriptor_template_sha256 || keys_info_merkle_root || u8(len) || musig2_session_id)`.
    Rejects `some bs` when `bs.size = 0` or `bs.size > 32`. -/
def computeBolosPsbtSessionId {Affine : Type} (c : MusigCrypto Affine)
    (descriptorTemplateSha256 : Bytes32) (keysInfoMerkleRoot : Bytes32)
    (musig2SessionId : Option ByteArray) : Option PsbtSessionId :=
  match musig2SessionId with
  | none =>
    let payload := concatBytes [
      descriptorTemplateSha256.bytes,
      keysInfoMerkleRoot.bytes,
      ByteArray.mk #[0]
    ]
    some (c.taggedHash "PsbtSessionId" payload)
  | some bs =>
    if decide (1 ≤ bs.size) && decide (bs.size ≤ maxProprietarySessionIdLen) then
      let payload := concatBytes [
        descriptorTemplateSha256.bytes,
        keysInfoMerkleRoot.bytes,
        ByteArray.mk #[UInt8.ofNat bs.size],
        bs
      ]
      some (c.taggedHash "PsbtSessionId" payload)
    else
      none

/-- Vanadium transaction-bound `psbt_session_id`:
    `H_{"PsbtSessionId"}(wallet_id || unsigned_tx_id)`. -/
def computeVanadiumPsbtSessionId {Affine : Type} (c : MusigCrypto Affine)
    (walletId : Bytes32) (unsignedTxId : Bytes32) : PsbtSessionId :=
  c.taggedHash "PsbtSessionId" (appendBytes walletId.bytes unsignedTxId.bytes)

/-- Select the `aggpk` passed into `nonceGen` (`.untweakedBolos` vs `.tweakedVanadium`). -/
def selectNonceAggPk (mode : NonceAggPkMode)
    (untweakedAggPk tweakedAggPk : CompressedPubKey) : XOnlyPubKey :=
  match mode with
  | .untweakedBolos => xOnlyOfCompressed untweakedAggPk
  | .tweakedVanadium => xOnlyOfCompressed tweakedAggPk

/-! ## 6. Session Store (`capacity = 32` / `28B` on BOLOS, `capacity = 1` / `32B` on Vanadium) -/

/-- Default BOLOS NVRAM MuSig2 session store (`capacity = some 32`, `idMatchBytes = 28`). -/
def bolosDefaultStore : MusigSessionStore :=
  { activeEntries := []
    consumedRandRoots := []
    capacity := some bolosMaxMusigSessions
    idMatchBytes := bolosStoredIdPrefixLen }

/-- Default Vanadium RAM MuSig2 session store (`capacity = some 1`, `idMatchBytes = 32`). -/
def vanadiumDefaultStore : MusigSessionStore :=
  { activeEntries := []
    consumedRandRoots := []
    capacity := some vanadiumMaxMusigSessions
    idMatchBytes := 32 }

/-- Check whether `rr` has already been consumed by Round 2. -/
def isRandRootConsumed (store : MusigSessionStore) (rr : RandRoot) : Bool :=
  listMem rr store.consumedRandRoots

/-- Recursive lookup of an active `RandRoot` matching `sid` on `idMatchBytes`. -/
def findActiveEntry (idMatchBytes : Nat) (sid : PsbtSessionId) :
    List (PsbtSessionId × RandRoot) → Option (PsbtSessionId × RandRoot)
  | [] => none
  | p :: rest =>
    if sessionIdPrefixEq idMatchBytes p.1 sid then some p
    else findActiveEntry idMatchBytes sid rest

/-- Look up an active `RandRoot` for `sid`. -/
def lookupActive (store : MusigSessionStore) (sid : PsbtSessionId) : Option RandRoot :=
  match findActiveEntry store.idMatchBytes sid store.activeEntries with
  | some (_, rr) => some rr
  | none => none

/-- Query `SessionLifecycle` status of `sid`. -/
def sessionStatus (store : MusigSessionStore) (sid : PsbtSessionId) : SessionLifecycle :=
  match lookupActive store sid with
  | some rr => .active rr
  | none => .unseen

/-- Enforce optional slot capacity via FIFO eviction of oldest entries. -/
def trimToCapacity (cap : Option Nat) (entries : List (PsbtSessionId × RandRoot)) :
    List (PsbtSessionId × RandRoot) :=
  match cap with
  | none => entries
  | some 0 => []
  | some maxSlots =>
    if decide (entries.length ≤ maxSlots) then
      entries
    else
      entries.drop (entries.length - maxSlots)

/-- Filter out entries matching `sid` on `idMatchBytes`. -/
def filterOutMatchingSid (idMatchBytes : Nat) (sid : PsbtSessionId) :
    List (PsbtSessionId × RandRoot) → List (PsbtSessionId × RandRoot)
  | [] => []
  | p :: rest =>
    if !sessionIdPrefixEq idMatchBytes p.1 sid then
      p :: filterOutMatchingSid idMatchBytes sid rest
    else
      filterOutMatchingSid idMatchBytes sid rest

/-- Register/commit a Round-1 MuSig2 session `(sid, randRoot)`.
    Supports re-registration of `sid` after Round-2 deletion when given a fresh `randRoot`. -/
def registerRound1 (store : MusigSessionStore)
    (sid : PsbtSessionId) (randRoot : RandRoot) : Except MusigError MusigSessionStore :=
  if isAllZeros sid || isAllZeros randRoot || isRandRootConsumed store randRoot then
    .error .nonceGenFailed
  else
    let filtered := filterOutMatchingSid store.idMatchBytes sid store.activeEntries
    let updated := trimToCapacity store.capacity (filtered ++ [(sid, randRoot)])
    .ok { store with activeEntries := updated }

/-- Atomically pop `sid` from `activeEntries` for Round 2 and mark `randRoot` consumed. -/
def consumeRound2 (store : MusigSessionStore) (sid : PsbtSessionId) :
    Except MusigError (RandRoot × MusigSessionStore) :=
  match findActiveEntry store.idMatchBytes sid store.activeEntries with
  | none => .error .missingSession
  | some (_, randRoot) =>
    if isRandRootConsumed store randRoot then
      .error .sessionAlreadyConsumed
    else
      let remaining := filterOutMatchingSid store.idMatchBytes sid store.activeEntries
      let store' : MusigSessionStore := {
        store with
        activeEntries := remaining
        consumedRandRoots := randRoot :: store.consumedRandRoots
      }
      .ok (randRoot, store')

/-- Evict an unconsumed active session matching `sid` while preserving `consumedRandRoots`. -/
def evictUnconsumed (store : MusigSessionStore) (sid : PsbtSessionId) : MusigSessionStore :=
  { store with
    activeEntries := filterOutMatchingSid store.idMatchBytes sid store.activeEntries }

/-! ## 7. Round-1 & Round-2 PSBT Execution Passes -/

/-- Pairwise distinctness check on `(inputIndex, placeholderIndex, internalPk)` coordinates. -/
def distinctTaskCoordinates : List (UInt32 × UInt32 × CompressedPubKey) → Bool
  | [] => true
  | c :: cs => !listMem c cs && distinctTaskCoordinates cs

/-- Produce a Round-1 `MusigRound1Output` for a single task. -/
def round1ProduceTaskNonce {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (task : MusigSignTask) :
    Except MusigError MusigRound1Output :=
  if task.sortedPubkeys.isEmpty then
    .error .emptyPubkeyList
  else if decide (task.sortedPubkeys.length > maxPubkeysPerMusig) then
    .error .tooManyPubkeys
  else
    let randIJ := syntheticRandIJ c randRoot task.inputIndex task.placeholderIndex
    let aggpk := selectNonceAggPk mode task.untweakedAggPk task.tweakedAggPk
    match nonceGen c randIJ task.internalPk aggpk with
    | .error e => .error e
    | .ok (_secnonce, pubnonce) =>
      .ok {
        inputIndex := task.inputIndex
        pubnonce := pubnonce
        participantPk := task.internalPk
        aggregatePubkey := task.tweakedAggPk
        leafHash := task.leafHash
      }

/-- Execute a complete Round-1 PSBT pass for `sid`. -/
def executeRound1Pass {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (freshRandRoot : RandRoot)
    (tasks : List MusigSignTask) :
    Except (MusigError × MusigSessionStore) (List MusigRound1Output × MusigSessionStore) :=
  if isAllZeros sid || isAllZeros freshRandRoot || isRandRootConsumed store freshRandRoot then
    .error (.nonceGenFailed, store)
  else
    let poppedStore := evictUnconsumed store sid
    let coords := tasks.map (fun t => (t.inputIndex, t.placeholderIndex, t.internalPk))
    if !distinctTaskCoordinates coords then
      .error (.nonceOutOfRange, poppedStore)
    else
      match tasks.mapM (round1ProduceTaskNonce c mode freshRandRoot) with
      | .error err => .error (err, poppedStore)
      | .ok outputs =>
        match registerRound1 poppedStore sid freshRandRoot with
        | .error err => .error (err, poppedStore)
        | .ok committedStore => .ok (outputs, committedStore)

/-- Produce a Round-2 `MusigRound2Output` for one task, enforcing self-pubnonce byte-equality
    when `checkSelfPubnonce = true`. -/
def round2SignTask {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (inp : MusigRound2TaskInput)
    (checkSelfPubnonce : Bool := true) :
    Except MusigError MusigRound2Output :=
  if inp.task.sortedPubkeys.isEmpty then
    .error .emptyPubkeyList
  else if decide (inp.task.sortedPubkeys.length > maxPubkeysPerMusig) then
    .error .tooManyPubkeys
  else
    match inp.psbtMyPubnonce with
    | none => .error .missingPubnonce
    | some myPubnonce =>
      if decide (inp.cosignerPubnonces.length ≠ inp.task.sortedPubkeys.length) then
        .error .missingPubnonce
      else
        match nonceAgg c inp.cosignerPubnonces with
        | .error e => .error e
        | .ok aggnonce =>
          let randIJ := syntheticRandIJ c randRoot inp.task.inputIndex inp.task.placeholderIndex
          let aggpk := selectNonceAggPk mode inp.task.untweakedAggPk inp.task.tweakedAggPk
          match nonceGen c randIJ inp.task.internalPk aggpk with
          | .error e => .error e
          | .ok (secnonce, recomputedPubnonce) =>
            if checkSelfPubnonce && decide (recomputedPubnonce ≠ myPubnonce) then
              .error .pubnonceMismatch
            else
              let ctx : SessionContext := {
                aggnonce := aggnonce
                pubkeys := inp.task.sortedPubkeys
                tweaks := inp.task.tweaks
                msg := inp.sighash.bytes
              }
              match partialSign c secnonce inp.secretKey ctx with
              | .error e => .error e
              | .ok psig =>
                .ok {
                  inputIndex := inp.task.inputIndex
                  signature := psig
                  participantPk := inp.task.internalPk
                  aggregatePubkey := inp.task.tweakedAggPk
                  leafHash := inp.task.leafHash
                }

/-- Execute a complete Round-2 PSBT pass for `sid`, atomically consuming `sid` beforehand. -/
def executeRound2Pass {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
    (checkSelfPubnonce : Bool := true) :
    Except (MusigError × MusigSessionStore) (List MusigRound2Output × MusigSessionStore) :=
  match consumeRound2 store sid with
  | .error err => .error (err, store)
  | .ok (randRoot, consumedStore) =>
    let coords := inputs.map (fun inp => (inp.task.inputIndex, inp.task.placeholderIndex, inp.task.internalPk))
    if !distinctTaskCoordinates coords then
      .error (.nonceOutOfRange, consumedStore)
    else
      match inputs.mapM (fun inp => round2SignTask c mode randRoot inp checkSelfPubnonce) with
      | .error err => .error (err, consumedStore)
      | .ok sigs => .ok (sigs, consumedStore)

/-- Execute a single `MusigOp` transition. -/
def stepMusigOp {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) (op : MusigOp) (checkSelfPubnonce : Bool := true) :
    MusigStepEvent × MusigSessionStore :=
  match op with
  | .round1 sid freshRand tasks =>
    match executeRound1Pass c mode store sid freshRand tasks with
    | .ok (nonces, store') => (.round1Ok sid nonces, store')
    | .error (err, store') => (.failed sid err, store')
  | .round2 sid inputs =>
    match lookupActive store sid, executeRound2Pass c mode store sid inputs checkSelfPubnonce with
    | some rr, .ok (sigs, store') => (.round2Ok sid rr sigs, store')
    | none, .ok (_, store') => (.failed sid .missingSession, store')
    | _, .error (err, store') => (.failed sid err, store')
  | .evict sid =>
    (.evicted sid, evictUnconsumed store sid)

/-- Execute a multi-step trace of `MusigOp`s. -/
def runMusigTrace {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) (ops : List MusigOp) (checkSelfPubnonce : Bool := true) :
    List MusigStepEvent × MusigSessionStore :=
  match ops with
  | [] => ([], store)
  | op :: restOps =>
    let (ev, store') := stepMusigOp c mode store op checkSelfPubnonce
    let (restEvs, finalStore) := runMusigTrace c mode store' restOps checkSelfPubnonce
    (ev :: restEvs, finalStore)

end BitcoinLedger.Musig2

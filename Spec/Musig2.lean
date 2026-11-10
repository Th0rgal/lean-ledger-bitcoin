/-
  Spec/Musig2.lean

  Formal specification of BIP-327 MuSig2 multi-round signing, BIP-328 synthetic
  aggregate xpub tweaks, and single-use nonce session linearity deduced from:
    - LedgerHQ/app-bitcoin (`doc/musig.md`, `src/musig/musig.c`,
      `src/musig/musig_sessions.c`, `src/handler/sign_psbt/musig_signing.c`)
    - LedgerHQ/vanadium (`apps/bitcoin/common/src/musig/*`,
      `apps/bitcoin/app/src/handlers/musig_signing.rs`)
-/

namespace Spec.Musig2

/-! ## 1. Core Domain Constants & Fixed-Width Byte Wrappers -/

/-- The secp256k1 group order `n` (`0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141`). -/
def secp256k1Order : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

theorem secp256k1Order_pos : 0 < secp256k1Order := by
  decide

/-- Maximum number of participant keys allowed in a `musig(...)` expression in Ledger Bitcoin apps. -/
def maxPubkeysPerMusig : Nat := 5

/-- Persistent MuSig2 session capacity on BOLOS (`app-bitcoin`). -/
def bolosMaxMusigSessions : Nat := 32

/-- Persistent MuSig2 session capacity on Vanadium (`apps/bitcoin` initial cut). -/
def vanadiumMaxMusigSessions : Nat := 1

/-- Prefix length (in bytes) of `psbt_session_id` stored per 64-byte NVRAM slot on BOLOS. -/
def bolosStoredIdPrefixLen : Nat := 28

/-- Maximum byte length of the optional proprietary `PSBT_GLOBAL_MUSIG2_SESSION_ID` field on BOLOS. -/
def maxProprietarySessionIdLen : Nat := 32

/-- Fixed BIP-328 chaincode (`SHA256("MuSig2MuSig2MuSig2")`) used for synthetic aggregate xpubs. -/
def bip328ChaincodeBytes : List UInt8 :=
  [ 0x86, 0x80, 0x87, 0xCA, 0x02, 0xA6, 0xF9, 0x74,
    0xC4, 0x59, 0x89, 0x24, 0xC3, 0x6B, 0x57, 0x76,
    0x2D, 0x32, 0xCB, 0x45, 0x71, 0x71, 0x67, 0xE3,
    0x00, 0x62, 0x2C, 0x71, 0x67, 0xE3, 0x89, 0x65 ]

theorem bip328ChaincodeBytes_length : bip328ChaincodeBytes.length = 32 := by
  rfl

/-- Exact-size byte sequence (`ByteArray` of length `n`). -/
structure SizedBytes (n : Nat) where
  bytes : ByteArray
  size_eq : bytes.size = n
  deriving DecidableEq

instance (n : Nat) : Repr (SizedBytes n) where
  reprPrec b p := reprPrec b.bytes.data p

/-- Construct an all-zero `SizedBytes n`. -/
def SizedBytes.zeros (n : Nat) : SizedBytes n :=
  { bytes := ByteArray.mk (Array.replicate n 0)
    size_eq := by simp [ByteArray.size] }

instance (n : Nat) : Inhabited (SizedBytes n) :=
  ⟨SizedBytes.zeros n⟩

/-- Pure recursive universal predicate on lists (avoids `Classical.choice` in `List.all`). -/
def listAll {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

/-- Pure recursive `DecidableEq` membership test on lists (avoids `Classical.choice` in `List.contains`). -/
def listMem {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || listMem x ys

@[simp] theorem listMem_nil {α : Type} [DecidableEq α] (x : α) : listMem x [] = false := rfl
@[simp] theorem listMem_cons {α : Type} [DecidableEq α] (x y : α) (ys : List α) :
    listMem x (y :: ys) = (decide (x = y) || listMem x ys) := rfl

/-- Check whether every byte in `b` is `0` (via `bytes.data.toList`). -/
def SizedBytes.isAllZeros {n : Nat} (b : SizedBytes n) : Bool :=
  listAll (fun x => decide (x = 0)) b.bytes.data.toList

abbrev Bytes32 := SizedBytes 32
abbrev CompressedPubKey := SizedBytes 33
abbrev XOnlyPubKey := SizedBytes 32
abbrev PubNonce := SizedBytes 66
abbrev PsbtSessionId := Bytes32
abbrev RandRoot := Bytes32
abbrev PartialSig := Bytes32
abbrev SchnorrSig := SizedBytes 64

/-- Concatenate two exact-size byte arrays. -/
def SizedBytes.append {m n : Nat} (a : SizedBytes m) (b : SizedBytes n) : SizedBytes (m + n) :=
  { bytes := ByteArray.mk (a.bytes.data ++ b.bytes.data)
    size_eq := by
      have ha : a.bytes.data.size = m := a.size_eq
      have hb : b.bytes.data.size = n := b.size_eq
      simp [ByteArray.size, ha, hb] }

/-- Pure kernel-reducible concatenation of `ByteArray`s (avoiding `@[extern]` `ByteArray.copySlice`). -/
def appendBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk (a.data ++ b.data)

/-- Concatenate a list of `ByteArray`s purely in the Lean kernel. -/
def concatBytes (xs : List ByteArray) : ByteArray :=
  xs.foldl appendBytes (ByteArray.mk #[])

/-- Extract the first 33-byte compressed point `R_s1` from a 66-byte `PubNonce`. -/
def PubNonce.r1Bytes (pn : PubNonce) : CompressedPubKey :=
  let arr := (pn.bytes.data.toList.take 33).toArray
  have hlen : (ByteArray.mk arr).size = 33 := by
    have h1 : pn.bytes.data.toList.length = 66 := by
      rw [Array.length_toList]
      exact pn.size_eq
    change arr.size = 33
    rw [List.size_toArray, List.length_take, h1]
    decide
  ⟨ByteArray.mk arr, hlen⟩

/-- Extract the second 33-byte compressed point `R_s2` from a 66-byte `PubNonce`. -/
def PubNonce.r2Bytes (pn : PubNonce) : CompressedPubKey :=
  let arr := (pn.bytes.data.toList.drop 33).toArray
  have hlen : (ByteArray.mk arr).size = 33 := by
    have h1 : pn.bytes.data.toList.length = 66 := by
      rw [Array.length_toList]
      exact pn.size_eq
    change arr.size = 33
    rw [List.size_toArray, List.length_drop, h1]
  ⟨ByteArray.mk arr, hlen⟩

/-- Construct a 66-byte `PubNonce` from two 33-byte compressed point encodings. -/
def PubNonce.ofParts (r1 r2 : CompressedPubKey) : PubNonce :=
  SizedBytes.append r1 r2

/-- Extract the 32-byte x-only coordinate (`bytes[1..33]`) of a 33-byte compressed key. -/
def CompressedPubKey.xOnly (pk : CompressedPubKey) : XOnlyPubKey :=
  let arr := (pk.bytes.data.toList.drop 1).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    have h1 : pk.bytes.data.toList.length = 33 := by
      rw [Array.length_toList]
      exact pk.size_eq
    change arr.size = 32
    rw [List.size_toArray, List.length_drop, h1]
  ⟨ByteArray.mk arr, hlen⟩

/-- Encode a `UInt32` in big-endian (4 bytes). -/
def encodeU32BE (v : UInt32) : ByteArray :=
  let n := v.toNat
  ByteArray.mk #[
    UInt8.ofNat ((n >>> 24) &&& 0xFF),
    UInt8.ofNat ((n >>> 16) &&& 0xFF),
    UInt8.ofNat ((n >>> 8) &&& 0xFF),
    UInt8.ofNat (n &&& 0xFF)
  ]

/-- Decode a big-endian byte list into a natural number. -/
def natFromBytesBE (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Encode a natural number into `len` big-endian bytes (modulo `256^len`). -/
def natToBytesBEAux : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | k + 1, v, acc => natToBytesBEAux k (v / 256) (UInt8.ofNat (v % 256) :: acc)

theorem natToBytesBEAux_length (k v : Nat) (acc : List UInt8) :
    (natToBytesBEAux k v acc).length = k + acc.length := by
  induction k generalizing v acc with
  | zero => simp [natToBytesBEAux]
  | succ k ih =>
    simp [natToBytesBEAux, ih, Nat.add_comm, Nat.add_left_comm]

/-- Encode a scalar `v : Nat` into 32 big-endian bytes. -/
def scalarToBytes32 (v : Nat) : Bytes32 :=
  let arr := (natToBytesBEAux 32 v []).toArray
  have hlen : (ByteArray.mk arr).size = 32 := by
    change arr.size = 32
    rw [List.size_toArray, natToBytesBEAux_length]
    rfl
  ⟨ByteArray.mk arr, hlen⟩

/-- Decode a 32-byte big-endian scalar as `Nat`. -/
def bytes32ToNat (b : Bytes32) : Nat :=
  natFromBytesBE b.bytes.data.toList

/-- Strict scalar parser (`< secp256k1Order`). -/
def parseScalarStrict (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if s < secp256k1Order then some s else none

/-- Non-zero strict scalar parser (`0 < s < secp256k1Order`). -/
def parseNonZeroScalar (b : Bytes32) : Option Nat :=
  let s := bytes32ToNat b
  if 0 < s && s < secp256k1Order then some s else none

/-- Modular reduction of a 32-byte big-endian integer modulo `secp256k1Order`. -/
def parseScalarModN (b : Bytes32) : Nat :=
  bytes32ToNat b % secp256k1Order

/-! ## 2. Lexicographical `KeySort` & Second-Unique-Key Optimization -/

/-- Lexicographical comparison of byte lists. -/
def listLexLe : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else listLexLe as bs

/-- Lexicographical comparison of 33-byte compressed public keys (BIP-327 `KeySort`). -/
def pubKeyLe (a b : CompressedPubKey) : Bool :=
  listLexLe a.bytes.data.toList b.bytes.data.toList

/-- Insertion helper for deterministic `keySort`. -/
def insertPubKey (x : CompressedPubKey) : List CompressedPubKey → List CompressedPubKey
  | [] => [x]
  | y :: ys => if pubKeyLe x y then x :: y :: ys else y :: insertPubKey x ys

/-- BIP-327 `KeySort`: sort compressed public keys in ascending lexicographical order. -/
def keySort : List CompressedPubKey → List CompressedPubKey
  | [] => []
  | x :: xs => insertPubKey x (keySort xs)

theorem insertPubKey_length (x : CompressedPubKey) (xs : List CompressedPubKey) :
    (insertPubKey x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [insertPubKey]
    split <;> simp [ih]

/-- `keySort` preserves the number of participant public keys. -/
theorem keySort_length (pks : List CompressedPubKey) :
    (keySort pks).length = pks.length := by
  induction pks with
  | nil => rfl
  | cons x xs ih =>
    simp [keySort, insertPubKey_length, ih]

theorem mem_insertPubKey (z x : CompressedPubKey) (xs : List CompressedPubKey) :
    z ∈ insertPubKey x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil => simp [insertPubKey]
  | cons y ys ih =>
    simp only [insertPubKey]
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)

/-- `keySort` preserves participant key membership. -/
theorem mem_keySort (z : CompressedPubKey) (pks : List CompressedPubKey) :
    z ∈ keySort pks ↔ z ∈ pks := by
  induction pks with
  | nil => simp [keySort]
  | cons x xs ih =>
    simp [keySort, mem_insertPubKey, ih]

/-- BIP-327 `get_second_key`: returns the first public key in `pubkeys` distinct from `pubkeys[0]`,
    or `none` (encoded as 33 zero bytes in C/Rust) when all keys are identical or empty. -/
def secondUniqueKey : List CompressedPubKey → Option CompressedPubKey
  | [] => none
  | first :: rest => rest.find? (fun pk => pk != first)

theorem secondUniqueKey_all_equal (pk : CompressedPubKey) (k : Nat) :
    secondUniqueKey (List.replicate k pk) = none := by
  cases k with
  | zero => rfl
  | succ m =>
    simp only [List.replicate_succ, secondUniqueKey]
    induction m with
    | zero => rfl
    | succ m' ih =>
      simp [List.replicate_succ, ih]

/-! ## 3. Abstract Cryptographic & Curve Interface for BIP-327 -/

/-- Abstract secp256k1 point (either infinity or a valid affine curve point). -/
inductive CurvePoint (Affine : Type) where
  | infinity : CurvePoint Affine
  | affine (p : Affine) : CurvePoint Affine
  deriving Repr, DecidableEq

/-- Domain-independent cryptographic primitives required by BIP-327 / BIP-328. -/
structure MusigCrypto (Affine : Type) where
  /-- Standard secp256k1 generator `G`. -/
  generator : Affine
  /-- Group addition on `CurvePoint Affine`. -/
  pointAdd : CurvePoint Affine → CurvePoint Affine → CurvePoint Affine
  /-- Scalar multiplication `k * P` for `k : Nat`. -/
  pointMul : Nat → CurvePoint Affine → CurvePoint Affine
  /-- Point negation `-P`. -/
  pointNeg : CurvePoint Affine → CurvePoint Affine
  /-- Parity predicate `has_even_y(P)` on non-infinity points. -/
  hasEvenY : Affine → Bool
  /-- Extract the 32-byte big-endian x-coordinate `x(P)` of a non-infinity point. -/
  xCoord : Affine → XOnlyPubKey
  /-- SEC1 33-byte compressed point encoding (`0x02`/`0x03 || x(P)`). -/
  compress : Affine → CompressedPubKey
  /-- Strict SEC1 33-byte compressed point decompression (`0x02`/`0x03` only; rejects infinity/0x00). -/
  decompress : CompressedPubKey → Option Affine
  /-- BIP-340 tagged hash `SHA256(SHA256(tag) || SHA256(tag) || msg)`. -/
  taggedHash : String → ByteArray → Bytes32
  /-- Plain SHA-256 digest. -/
  sha256 : ByteArray → Bytes32
  /-- BIP-32 unhardened public child derivation returning `(childPubkey, childChaincode, tweakScalarBytes)`. -/
  ckdPubUnhardened : CompressedPubKey → Bytes32 → UInt32 → Option (CompressedPubKey × Bytes32 × Bytes32)

/-- Error taxonomy for BIP-327 MuSig2 operations and session lifecycle. -/
inductive MusigError where
  | emptyPubkeyList
  | tooManyPubkeys
  | invalidPoint
  | invalidContribution (cosignerIndex : Nat)
  | keyAggInfinity
  | tweakOutOfRange
  | tweakInfinity
  | nonceGenFailed
  | nonceOutOfRange
  | secretKeyOutOfRange
  | pubkeyMismatch
  | pubkeyNotInList
  | invalidPartialSignature
  | missingSession
  | sessionAlreadyConsumed
  | missingPubnonce
  | pubnonceMismatch
  | derivationFailed
  deriving Repr, DecidableEq

/-- BIP-327 `cpoint`: decompress a strict 33-byte SEC1 point. -/
def cpoint {Affine : Type} (c : MusigCrypto Affine) (pk : CompressedPubKey) :
    Except MusigError Affine :=
  match c.decompress pk with
  | some p => .ok p
  | none => .error .invalidPoint

/-- BIP-327 `cpoint_ext`: decompress a 33-byte point where 33 zero bytes denote infinity. -/
def cpointExt {Affine : Type} (c : MusigCrypto Affine) (pk : CompressedPubKey) :
    Except MusigError (CurvePoint Affine) :=
  if pk.isAllZeros then
    .ok .infinity
  else
    match c.decompress pk with
    | some p => .ok (.affine p)
    | none => .error .invalidPoint

/-! ## 4. BIP-327 `KeyAgg` & Tweaking (`apply_tweak`) -/

/-- BIP-327 `KeyAggContext`: aggregate point `Q` (non-infinity), parity accumulator `gacc`,
    and additive tweak accumulator `tacc` (scalars `< n`). -/
structure KeyAggContext (Affine : Type) where
  q : Affine
  gacc : Nat
  tacc : Nat
  deriving Repr, DecidableEq

/-- Single tweak step (either BIP-32 unhardened additive tweak or BIP-341 x-only TapTweak). -/
structure MusigTweak where
  scalar : Bytes32
  isXOnly : Bool
  deriving Repr, DecidableEq

/-- `hash_keys(pk_1, ..., pk_u) = H_{"KeyAgg list"}(pk_1 || ... || pk_u)`. -/
def hashKeys {Affine : Type} (c : MusigCrypto Affine) (pubkeys : List CompressedPubKey) : Bytes32 :=
  let payload := pubkeys.foldl (fun acc pk => appendBytes acc pk.bytes) (ByteArray.mk #[])
  c.taggedHash "KeyAgg list" payload

/-- `KeyAgg_coeff_internal(pubkeys, pk', pk2)`: returns `1` if `some pk' = pk2`,
    otherwise `H_{"KeyAgg coefficient"}(L || pk') mod n`. -/
def keyAggCoeffInternal {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) (pk : CompressedPubKey)
    (pk2 : Option CompressedPubKey) : Nat :=
  if pk2 == some pk then
    1
  else
    let l := hashKeys c pubkeys
    parseScalarModN (c.taggedHash "KeyAgg coefficient" (appendBytes l.bytes pk.bytes))

/-- BIP-327 `KeyAgg_coeff(pubkeys, pk')`. -/
def keyAggCoeff {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) (pk : CompressedPubKey) : Nat :=
  keyAggCoeffInternal c pubkeys pk (secondUniqueKey pubkeys)

theorem keyAggCoeff_second_unique_is_one {Affine : Type}
    (c : MusigCrypto Affine) (pubkeys : List CompressedPubKey) (pk2 : CompressedPubKey)
    (h : secondUniqueKey pubkeys = some pk2) :
    keyAggCoeff c pubkeys pk2 = 1 := by
  simp [keyAggCoeff, keyAggCoeffInternal, h]

/-- Accumulate `sum_i (a_i * P_i)` across participant public keys. -/
def keyAggLoop {Affine : Type} (c : MusigCrypto Affine)
    (allPks : List CompressedPubKey) (pk2 : Option CompressedPubKey) :
    List CompressedPubKey → CurvePoint Affine → Except MusigError (CurvePoint Affine)
  | [], acc => .ok acc
  | pk :: rest, acc => do
    let p ← cpoint c pk
    let a_i := keyAggCoeffInternal c allPks pk pk2
    let scaled := c.pointMul a_i (.affine p)
    keyAggLoop c allPks pk2 rest (c.pointAdd acc scaled)

/-- BIP-327 `KeyAgg(pubkeys)`: aggregates compressed public keys into `(Q, gacc = 1, tacc = 0)`. -/
def keyAgg {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) : Except MusigError (KeyAggContext Affine) := do
  if pubkeys.isEmpty then
    .error .emptyPubkeyList
  let pk2 := secondUniqueKey pubkeys
  let qPoint ← keyAggLoop c pubkeys pk2 pubkeys .infinity
  match qPoint with
  | .infinity => .error .keyAggInfinity
  | .affine q => .ok { q := q, gacc := 1, tacc := 0 }

/-- BIP-327 `apply_tweak(ctx, tweak, is_xonly)`. -/
def applyTweak {Affine : Type} (c : MusigCrypto Affine)
    (ctx : KeyAggContext Affine) (tweak : MusigTweak) :
    Except MusigError (KeyAggContext Affine) := do
  let t ← match parseScalarStrict tweak.scalar with
    | some s => .ok s
    | none => .error .tweakOutOfRange
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

/-- Apply a list of tweaks sequentially to a `KeyAggContext`. -/
def applyTweaks {Affine : Type} (c : MusigCrypto Affine)
    (ctx : KeyAggContext Affine) : List MusigTweak → Except MusigError (KeyAggContext Affine)
  | [] => .ok ctx
  | tw :: rest => do
    let ctx' ← applyTweak c ctx tw
    applyTweaks c ctx' rest

/-! ## 5. Nonce Generation, Nonce Aggregation & Partial Signing -/

/-- Secret nonce `(k_1, k_2, pk)` generated in Round 1 and recomputed in Round 2. -/
structure SecNonce where
  k1 : Nat
  k2 : Nat
  pk : CompressedPubKey
  deriving Repr, DecidableEq

/-- BIP-327 `nonce_hash` specialized to Ledger's mandatory `(rand, pk, aggpk)` profile
    (`msg_prefixed = [0x00]`, `extra_in = empty`). -/
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

/-- BIP-327 `NonceGen(rand, pk, aggpk)` in Ledger's deterministic session-rooted design. -/
def nonceGen {Affine : Type} (c : MusigCrypto Affine)
    (rand : Bytes32) (pk : CompressedPubKey) (aggpk : XOnlyPubKey) :
    Except MusigError (SecNonce × PubNonce) := do
  let k1 := parseScalarModN (nonceHash c rand.bytes pk aggpk 0)
  let k2 := parseScalarModN (nonceHash c rand.bytes pk aggpk 1)
  if k1 == 0 || k2 == 0 then
    .error .nonceGenFailed
  match c.pointMul k1 (.affine c.generator), c.pointMul k2 (.affine c.generator) with
  | .affine r1, .affine r2 =>
    let pn := PubNonce.ofParts (c.compress r1) (c.compress r2)
    .ok ({ k1 := k1, k2 := k2, pk := pk }, pn)
  | _, _ => .error .nonceGenFailed

/-- Sum the `j`-th point component across cosigner pubnonces, blaming cosigner index `idx` on invalid point. -/
def sumNonceComponent {Affine : Type} (c : MusigCrypto Affine)
    (select : PubNonce → CompressedPubKey) :
    Nat → List PubNonce → CurvePoint Affine → Except MusigError CompressedPubKey
  | _, [], acc =>
    match acc with
    | .infinity => .ok (SizedBytes.zeros 33)
    | .affine r => .ok (c.compress r)
  | idx, pn :: rest, acc => do
    match c.decompress (select pn) with
    | none => .error (.invalidContribution idx)
    | some rij => sumNonceComponent c select (idx + 1) rest (c.pointAdd acc (.affine rij))

/-- BIP-327 `NonceAgg(pubnonces)`: aggregates cosigner `PubNonce`s into `aggnonce`. -/
def nonceAgg {Affine : Type} (c : MusigCrypto Affine)
    (pubnonces : List PubNonce) : Except MusigError PubNonce := do
  if pubnonces.isEmpty then
    .error .emptyPubkeyList
  let r1 ← sumNonceComponent c PubNonce.r1Bytes 0 pubnonces .infinity
  let r2 ← sumNonceComponent c PubNonce.r2Bytes 0 pubnonces .infinity
  .ok (PubNonce.ofParts r1 r2)

/-- BIP-327 signing session context (`aggnonce`, sorted `pubkeys`, `tweaks`, `msg`). -/
structure SessionContext where
  aggnonce : PubNonce
  pubkeys : List CompressedPubKey
  tweaks : List MusigTweak
  msg : ByteArray
  deriving DecidableEq

/-- Derived BIP-327 session values `(Q, gacc, tacc, b, R, e)`. -/
structure SessionValues (Affine : Type) where
  q : Affine
  gacc : Nat
  tacc : Nat
  b : Nat
  r : Affine
  e : Nat
  deriving Repr, DecidableEq

/-- Derive BIP-327 session values (`b = H_{"MuSig/noncecoef"}`, `R = R_1 + b*R_2` with infinity → `G`,
    `e = H_{"BIP0340/challenge"}`). -/
def getSessionValues {Affine : Type} (c : MusigCrypto Affine)
    (ctx : SessionContext) : Except MusigError (SessionValues Affine) := do
  let baseCtx ← keyAgg c ctx.pubkeys
  let tweakedCtx ← applyTweaks c baseCtx ctx.tweaks
  let qx := c.xCoord tweakedCtx.q
  let bBytes := c.taggedHash "MuSig/noncecoef" (concatBytes [ctx.aggnonce.bytes, qx.bytes, ctx.msg])
  let b := parseScalarModN bBytes
  let r1 ← cpointExt c (PubNonce.r1Bytes ctx.aggnonce)
  let r2 ← cpointExt c (PubNonce.r2Bytes ctx.aggnonce)
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

/-- BIP-327 Round 2 `Sign(secnonce, sk, session_ctx)` producing a 32-byte partial signature. -/
def partialSign {Affine : Type} (c : MusigCrypto Affine)
    (secnonce : SecNonce) (skBytes : Bytes32) (ctx : SessionContext) :
    Except MusigError PartialSig := do
  let vals ← getSessionValues c ctx
  if !(0 < secnonce.k1 && secnonce.k1 < secp256k1Order) then
    .error .nonceOutOfRange
  if !(0 < secnonce.k2 && secnonce.k2 < secp256k1Order) then
    .error .nonceOutOfRange
  let k1 := if c.hasEvenY vals.r then secnonce.k1 else secp256k1Order - secnonce.k1
  let k2 := if c.hasEvenY vals.r then secnonce.k2 else secp256k1Order - secnonce.k2
  let sk ← match parseNonZeroScalar skBytes with
    | some d => .ok d
    | none => .error .secretKeyOutOfRange
  let pubPoint ← match c.pointMul sk (.affine c.generator) with
    | .affine p => .ok p
    | .infinity => .error .secretKeyOutOfRange
  let computedPk := c.compress pubPoint
  if computedPk != secnonce.pk then
    .error .pubkeyMismatch
  if !listMem computedPk ctx.pubkeys then
    .error .pubkeyNotInList
  let a := keyAggCoeff c ctx.pubkeys computedPk
  let g := if c.hasEvenY vals.q then 1 else secp256k1Order - 1
  let d := (g * vals.gacc * sk) % secp256k1Order
  let s := (k1 + vals.b * k2 + vals.e * a * d) % secp256k1Order
  .ok (scalarToBytes32 s)

/-- BIP-327 `PartialSigAgg(psigs, session_ctx)`: combines cosigner partial signatures into a
    64-byte BIP-340 Schnorr signature `R.x || ser_256(s)`. -/
def partialSigAgg {Affine : Type} (c : MusigCrypto Affine)
    (ctx : SessionContext) (psigs : List PartialSig) :
    Except MusigError SchnorrSig := do
  if psigs.length != ctx.pubkeys.length then
    .error .invalidPartialSignature
  let vals ← getSessionValues c ctx
  let sumS ← psigs.foldlM (fun acc psig => do
    match parseScalarStrict psig with
    | some s_i => .ok ((acc + s_i) % secp256k1Order)
    | none => .error .invalidPartialSignature) 0
  let g := if c.hasEvenY vals.q then 1 else secp256k1Order - 1
  let sFinal := (sumS + vals.e * g * vals.tacc) % secp256k1Order
  .ok (SizedBytes.append (c.xCoord vals.r) (scalarToBytes32 sFinal))

/-! ## 6. Synthetic Session Randomness & Target `psbt_session_id` Variants -/

/-- Domain-separated per-`(input_index, placeholder_index)` nonce randomness:
    `rand_{i,j} = SHA256(rand_root || be32(input_index) || be32(placeholder_index))`. -/
def syntheticRandIJ {Affine : Type} (c : MusigCrypto Affine)
    (randRoot : RandRoot) (inputIndex placeholderIndex : UInt32) : Bytes32 :=
  c.sha256 (concatBytes [randRoot.bytes, encodeU32BE inputIndex, encodeU32BE placeholderIndex])

/-- BOLOS (`app-bitcoin`) transaction-independent `psbt_session_id`:
    `H_{"PsbtSessionId"}(descriptor_template_sha256 || keys_info_merkle_root || u8(len) || musig2_session_id)`. -/
def computeBolosPsbtSessionId {Affine : Type} (c : MusigCrypto Affine)
    (descriptorTemplateSha256 : Bytes32) (keysInfoMerkleRoot : Bytes32)
    (proprietarySessionId : ByteArray) : Option PsbtSessionId :=
  if proprietarySessionId.size > maxProprietarySessionIdLen then
    none
  else
    let payload := concatBytes [
      descriptorTemplateSha256.bytes,
      keysInfoMerkleRoot.bytes,
      ByteArray.mk #[UInt8.ofNat proprietarySessionId.size],
      proprietarySessionId
    ]
    some (c.taggedHash "PsbtSessionId" payload)

/-- Vanadium (`apps/bitcoin`) transaction-bound `psbt_session_id`:
    `H_{"PsbtSessionId"}(wallet_id || unsigned_tx_id)`. -/
def computeVanadiumPsbtSessionId {Affine : Type} (c : MusigCrypto Affine)
    (walletId : Bytes32) (unsignedTxId : Bytes32) : PsbtSessionId :=
  c.taggedHash "PsbtSessionId" (appendBytes walletId.bytes unsignedTxId.bytes)

/-- Target difference in the auxiliary `aggpk` passed to `NonceGen`:
    - BOLOS passes the **untweaked** aggregate x-only key (before BIP-32/TapTweak) for tx-independence.
    - Vanadium passes the **post-tweaked** aggregate x-only key. -/
inductive NonceAggPkMode where
  | untweakedBolos
  | tweakedVanadium
  deriving Repr, DecidableEq

/-- Select the `aggpk` passed into `nonceGen` according to target profile. -/
def selectNonceAggPk (mode : NonceAggPkMode)
    (untweakedAggPk tweakedAggPk : CompressedPubKey) : XOnlyPubKey :=
  match mode with
  | .untweakedBolos => untweakedAggPk.xOnly
  | .tweakedVanadium => tweakedAggPk.xOnly

/-! ## 7. Per-PSBT Session Store & Nonce Single-Use Linearity -/

/-- Lifecycle status of a `PsbtSessionId` in the MuSig2 session state machine. -/
inductive SessionLifecycle where
  | unseen
  | active (randRoot : RandRoot)
  | consumed
  deriving Repr, DecidableEq

/-- Canonical `MusigSessionStore`: tracks active Round-1 sessions (bounded by `capacity` if set)
    and the monotonic set of consumed session IDs. -/
structure MusigSessionStore where
  activeEntries : List (PsbtSessionId × RandRoot) := []
  consumedIds : List PsbtSessionId := []
  capacity : Option Nat := none
  deriving Repr, DecidableEq

instance : Inhabited MusigSessionStore :=
  ⟨{}⟩

/-- Whether `sid` has already been consumed by a Round 2 signing invocation. -/
def MusigSessionStore.isConsumed (store : MusigSessionStore) (sid : PsbtSessionId) : Bool :=
  listMem sid store.consumedIds

/-- Look up an unconsumed active `randRoot` for `sid`. -/
def MusigSessionStore.lookupActive (store : MusigSessionStore) (sid : PsbtSessionId) :
    Option RandRoot :=
  if store.isConsumed sid then
    none
  else
    match store.activeEntries.find? (fun p => p.1 == sid) with
    | some (_, rr) => some rr
    | none => none

/-- Query the logical `SessionLifecycle` of `sid`. -/
def MusigSessionStore.status (store : MusigSessionStore) (sid : PsbtSessionId) : SessionLifecycle :=
  if store.isConsumed sid then
    .consumed
  else
    match store.activeEntries.find? (fun p => p.1 == sid) with
    | some (_, rr) => .active rr
    | none => .unseen

/-- Enforce optional slot capacity by evicting oldest active entries if needed. -/
def trimToCapacity (cap : Option Nat) (entries : List (PsbtSessionId × RandRoot)) :
    List (PsbtSessionId × RandRoot) :=
  match cap with
  | none => entries
  | some 0 => []
  | some maxSlots =>
    if entries.length <= maxSlots then
      entries
    else
      entries.drop (entries.length - maxSlots)

/-- Register/commit a Round-1 MuSig2 session `(sid, randRoot)`.
    - Rejects if `sid` is `0x00..00` (reserved sentinel) or already `.consumed`.
    - Replaces any stale unconsumed `.active` entry for `sid` (matching C/Rust Round-1 retry). -/
def MusigSessionStore.registerRound1 (store : MusigSessionStore)
    (sid : PsbtSessionId) (randRoot : RandRoot) : Except MusigError MusigSessionStore :=
  if sid.isAllZeros then
    .error .nonceGenFailed
  else if store.isConsumed sid then
    .error .sessionAlreadyConsumed
  else
    let filtered := store.activeEntries.filter (fun p => p.1 != sid)
    let updated := trimToCapacity store.capacity (filtered ++ [(sid, randRoot)])
    .ok { store with activeEntries := updated }

/-- Atomically consume `sid` for Round 2, returning `(randRoot, updatedStore)`. -/
def MusigSessionStore.consumeRound2 (store : MusigSessionStore) (sid : PsbtSessionId) :
    Except MusigError (RandRoot × MusigSessionStore) :=
  if store.isConsumed sid then
    .error .sessionAlreadyConsumed
  else
    match store.activeEntries.find? (fun p => p.1 == sid) with
    | none => .error .missingSession
    | some (_, randRoot) =>
      let remaining := store.activeEntries.filter (fun p => p.1 != sid)
      let store' : MusigSessionStore := {
        store with
        activeEntries := remaining
        consumedIds := sid :: store.consumedIds
      }
      .ok (randRoot, store')

/-- Evict an unconsumed stale session (consumed tombstones are NEVER removed). -/
def MusigSessionStore.evictUnconsumed (store : MusigSessionStore) (sid : PsbtSessionId) :
    MusigSessionStore :=
  { store with activeEntries := store.activeEntries.filter (fun p => p.1 != sid) }

/-! ## 8. Round 1 & Round 2 PSBT Placeholder Operations -/

/-- Specification of one `(input_index, placeholder_index)` MuSig2 signing task within a PSBT. -/
structure MusigSignTask where
  inputIndex : UInt32
  placeholderIndex : UInt32
  internalPk : CompressedPubKey
  untweakedAggPk : CompressedPubKey
  tweakedAggPk : CompressedPubKey
  sortedPubkeys : List CompressedPubKey
  tweaks : List MusigTweak
  leafHash : Option Bytes32
  deriving Repr, DecidableEq

/-- Round 1 output entry (`CCMD_YIELD_MUSIG_PUBNONCE_TAG` / `MuSig2Pubnonce`). -/
structure MusigRound1Output where
  inputIndex : UInt32
  pubnonce : PubNonce
  participantPk : CompressedPubKey
  aggregatePubkey : CompressedPubKey
  leafHash : Option Bytes32
  deriving Repr, DecidableEq

/-- Round 2 input context for a single `(inputIndex, placeholderIndex)` signing task. -/
structure MusigRound2TaskInput where
  task : MusigSignTask
  secretKey : Bytes32
  sighash : Bytes32
  psbtMyPubnonce : Option PubNonce
  cosignerPubnonces : List PubNonce
  deriving Repr, DecidableEq

/-- Round 2 output entry (`CCMD_YIELD_MUSIG_PARTIALSIGNATURE_TAG` / `MuSig2PartialSignature`). -/
structure MusigRound2Output where
  inputIndex : UInt32
  signature : PartialSig
  participantPk : CompressedPubKey
  aggregatePubkey : CompressedPubKey
  leafHash : Option Bytes32
  deriving Repr, DecidableEq

/-- Check pairwise distinctness of `(inputIndex, placeholderIndex)` across tasks in a single pass. -/
def distinctTaskCoordinates : List (UInt32 × UInt32) → Bool
  | [] => true
  | c :: cs => !listMem c cs && distinctTaskCoordinates cs

/-- Produce a Round-1 `MusigRound1Output` for a single task given session `randRoot`. -/
def round1ProduceTaskNonce {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (task : MusigSignTask) :
    Except MusigError MusigRound1Output := do
  if task.sortedPubkeys.isEmpty then
    .error .emptyPubkeyList
  if task.sortedPubkeys.length > maxPubkeysPerMusig then
    .error .tooManyPubkeys
  let randIJ := syntheticRandIJ c randRoot task.inputIndex task.placeholderIndex
  let aggpk := selectNonceAggPk mode task.untweakedAggPk task.tweakedAggPk
  let (_secnonce, pubnonce) ← nonceGen c randIJ task.internalPk aggpk
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
  if sid.isAllZeros then
    .error (.nonceGenFailed, store)
  else if store.isConsumed sid then
    .error (.sessionAlreadyConsumed, store)
  else
    let poppedStore := store.evictUnconsumed sid
    let coords := tasks.map (fun t => (t.inputIndex, t.placeholderIndex))
    if !distinctTaskCoordinates coords then
      .error (.nonceOutOfRange, poppedStore)
    else
      match tasks.mapM (round1ProduceTaskNonce c mode freshRandRoot) with
      | .error err => .error (err, poppedStore)
      | .ok outputs =>
        match poppedStore.registerRound1 sid freshRandRoot with
        | .error err => .error (err, poppedStore)
        | .ok committedStore => .ok (outputs, committedStore)

/-- Produce a Round-2 `MusigRound2Output` for one task, enforcing BOLOS's self-pubnonce match
    (`recomputedPubnonce == myPubnonce`) before invoking `partialSign`. -/
def round2SignTask {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (inp : MusigRound2TaskInput) :
    Except MusigError MusigRound2Output := do
  if inp.task.sortedPubkeys.isEmpty then
    .error .emptyPubkeyList
  if inp.task.sortedPubkeys.length > maxPubkeysPerMusig then
    .error .tooManyPubkeys
  let myPubnonce ← match inp.psbtMyPubnonce with
    | some pn => .ok pn
    | none => .error .missingPubnonce
  if inp.cosignerPubnonces.length != inp.task.sortedPubkeys.length then
    .error .missingPubnonce
  let aggnonce ← nonceAgg c inp.cosignerPubnonces
  let randIJ := syntheticRandIJ c randRoot inp.task.inputIndex inp.task.placeholderIndex
  let aggpk := selectNonceAggPk mode inp.task.untweakedAggPk inp.task.tweakedAggPk
  let (secnonce, recomputedPubnonce) ← nonceGen c randIJ inp.task.internalPk aggpk
  if recomputedPubnonce != myPubnonce then
    .error .pubnonceMismatch
  let ctx : SessionContext := {
    aggnonce := aggnonce
    pubkeys := inp.task.sortedPubkeys
    tweaks := inp.task.tweaks
    msg := inp.sighash.bytes
  }
  let psig ← partialSign c secnonce inp.secretKey ctx
  .ok {
    inputIndex := inp.task.inputIndex
    signature := psig
    participantPk := inp.task.internalPk
    aggregatePubkey := inp.task.tweakedAggPk
    leafHash := inp.task.leafHash
  }

/-- Execute a complete Round-2 PSBT pass for `sid`, atomically consuming `sid` before signing. -/
def executeRound2Pass {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput) :
    Except (MusigError × MusigSessionStore) (List MusigRound2Output × MusigSessionStore) :=
  match store.consumeRound2 sid with
  | .error err => .error (err, store)
  | .ok (randRoot, consumedStore) =>
    let coords := inputs.map (fun inp => (inp.task.inputIndex, inp.task.placeholderIndex))
    if !distinctTaskCoordinates coords then
      .error (.nonceOutOfRange, consumedStore)
    else
      match inputs.mapM (round2SignTask c mode randRoot) with
      | .error err => .error (err, consumedStore)
      | .ok sigs => .ok (sigs, consumedStore)

/-! ## 9. Multi-Step Session Transition System & Linearity Proofs -/

/-- Observable operations on `MusigSessionStore`. -/
inductive MusigOp where
  | round1 (sid : PsbtSessionId) (freshRand : RandRoot) (tasks : List MusigSignTask)
  | round2 (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
  | evict (sid : PsbtSessionId)
  deriving Repr, DecidableEq

/-- Observable event emitted by one `MusigOp` step. -/
inductive MusigStepEvent where
  | round1Ok (sid : PsbtSessionId) (nonces : List MusigRound1Output)
  | round2Ok (sid : PsbtSessionId) (sigs : List MusigRound2Output)
  | evicted (sid : PsbtSessionId)
  | failed (sid : PsbtSessionId) (err : MusigError)
  deriving Repr, DecidableEq

/-- Execute a single `MusigOp`, always returning `(event, postStore)`. -/
def stepMusigOp {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) (op : MusigOp) : MusigStepEvent × MusigSessionStore :=
  match op with
  | .round1 sid freshRand tasks =>
    match executeRound1Pass c mode store sid freshRand tasks with
    | .ok (nonces, store') => (.round1Ok sid nonces, store')
    | .error (err, store') => (.failed sid err, store')
  | .round2 sid inputs =>
    match executeRound2Pass c mode store sid inputs with
    | .ok (sigs, store') => (.round2Ok sid sigs, store')
    | .error (err, store') => (.failed sid err, store')
  | .evict sid =>
    (.evicted sid, store.evictUnconsumed sid)

/-- Execute a multi-step sequence of `MusigOp`s, collecting all emitted events. -/
def runMusigTrace {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) : List MusigOp → List MusigStepEvent × MusigSessionStore
  | [] => ([], store)
  | op :: ops =>
    let (ev, store') := stepMusigOp c mode store op
    let (restEvs, finalStore) := runMusigTrace c mode store' ops
    (ev :: restEvs, finalStore)

/-- Count how many times `sid` successfully produced Round-2 partial signatures in an event trace. -/
def countRound2SuccessFor (sid : PsbtSessionId) : List MusigStepEvent → Nat
  | [] => 0
  | .round2Ok sid' _ :: rest =>
    (if sid' == sid then 1 else 0) + countRound2SuccessFor sid rest
  | _ :: rest => countRound2SuccessFor sid rest

/-! ### Key Security Theorems: Monotonicity & Single-Use Nonce Linearity -/

theorem isConsumed_evictUnconsumed (store : MusigSessionStore) (sid target : PsbtSessionId) :
    (store.evictUnconsumed sid).isConsumed target = store.isConsumed target := by
  rfl

theorem isConsumed_registerRound1 {store store' : MusigSessionStore}
    {sid : PsbtSessionId} {rr : RandRoot}
    (h : store.registerRound1 sid rr = .ok store') (target : PsbtSessionId) :
    store'.isConsumed target = store.isConsumed target := by
  unfold MusigSessionStore.registerRound1 at h
  by_cases hZ : sid.isAllZeros = true
  · simp [hZ] at h
  · simp only [hZ, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hC : store.isConsumed sid = true
    · simp [hC] at h
    · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h
      injection h with hEq
      rw [← hEq]
      rfl

theorem consumeRound2_marks_consumed {store store' : MusigSessionStore}
    {sid : PsbtSessionId} {rr : RandRoot}
    (h : store.consumeRound2 sid = .ok (rr, store')) :
    store'.isConsumed sid = true := by
  unfold MusigSessionStore.consumeRound2 at h
  by_cases hC : store.isConsumed sid = true
  · simp [hC] at h
  · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h
    cases hFind : store.activeEntries.find? (fun p => p.1 == sid) with
    | none => simp [hFind] at h
    | some pair =>
      rcases pair with ⟨_, rr'⟩
      simp only [hFind] at h
      injection h with hPair
      cases hPair
      simp [MusigSessionStore.isConsumed, listMem]

theorem consumeRound2_preserves_consumed {store store' : MusigSessionStore}
    {sid target : PsbtSessionId} {rr : RandRoot}
    (h : store.consumeRound2 sid = .ok (rr, store'))
    (hCons : store.isConsumed target = true) :
    store'.isConsumed target = true := by
  unfold MusigSessionStore.consumeRound2 at h
  by_cases hC : store.isConsumed sid = true
  · simp [hC] at h
  · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h
    cases hFind : store.activeEntries.find? (fun p => p.1 == sid) with
    | none => simp [hFind] at h
    | some pair =>
      rcases pair with ⟨_, rr'⟩
      simp only [hFind] at h
      injection h with hPair
      cases hPair
      simp only [MusigSessionStore.isConsumed, listMem, Bool.or_eq_true]
      exact Or.inr hCons

theorem consumeRound2_rejects_when_consumed (store : MusigSessionStore) (sid : PsbtSessionId)
    (hCons : store.isConsumed sid = true) :
    store.consumeRound2 sid = .error .sessionAlreadyConsumed := by
  unfold MusigSessionStore.consumeRound2
  simp [hCons]

theorem executeRound1Pass_preserves_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid target : PsbtSessionId) (freshRand : RandRoot) (tasks : List MusigSignTask)
    (hCons : store.isConsumed target = true) :
    (match executeRound1Pass c mode store sid freshRand tasks with
     | .ok (_, s') => s'
     | .error (_, s') => s').isConsumed target = true := by
  dsimp only [executeRound1Pass]
  by_cases hZero : sid.isAllZeros = true
  · simp [hZero, hCons]
  · simp only [Bool.not_eq_true] at hZero
    simp only [hZero, Bool.false_eq_true, ↓reduceIte]
    by_cases hAlready : store.isConsumed sid = true
    · simp [hAlready, hCons]
    · simp only [Bool.not_eq_true] at hAlready
      simp only [hAlready, Bool.false_eq_true, ↓reduceIte]
      by_cases hDist : (!distinctTaskCoordinates (List.map (fun t => (t.inputIndex, t.placeholderIndex)) tasks)) = true
      · simp [hDist, isConsumed_evictUnconsumed, hCons]
      · simp only [Bool.not_eq_true] at hDist
        simp only [hDist, Bool.false_eq_true, ↓reduceIte]
        cases List.mapM (round1ProduceTaskNonce c mode freshRand) tasks with
        | error _ =>
          simp [isConsumed_evictUnconsumed, hCons]
        | ok _ =>
          cases hReg : (store.evictUnconsumed sid).registerRound1 sid freshRand with
          | error _ =>
            simp [isConsumed_evictUnconsumed, hCons]
          | ok committed =>
            simp only [isConsumed_registerRound1 hReg, isConsumed_evictUnconsumed, hCons]

theorem executeRound2Pass_preserves_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid target : PsbtSessionId) (inputs : List MusigRound2TaskInput)
    (hCons : store.isConsumed target = true) :
    (match executeRound2Pass c mode store sid inputs with
     | .ok (_, s') => s'
     | .error (_, s') => s').isConsumed target = true := by
  dsimp only [executeRound2Pass]
  cases hPop : store.consumeRound2 sid with
  | error _ =>
    exact hCons
  | ok pair =>
    rcases pair with ⟨rr, consumedStore⟩
    have hPres : consumedStore.isConsumed target = true :=
      consumeRound2_preserves_consumed hPop hCons
    by_cases hDist : (!distinctTaskCoordinates (List.map (fun inp => (inp.task.inputIndex, inp.task.placeholderIndex)) inputs)) = true
    · simp [hDist, hPres]
    · simp only [Bool.not_eq_true] at hDist
      simp only [hDist, Bool.false_eq_true, ↓reduceIte]
      cases List.mapM (round2SignTask c mode rr) inputs <;> exact hPres

/-- **Irreversibility of Consumed Nonce Sessions**:
    No single `stepMusigOp` transition (whether succeeding or failing!) can ever clear or
    resurrect a consumed `PsbtSessionId`. -/
theorem stepMusigOp_preserves_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore) (op : MusigOp) (target : PsbtSessionId)
    (hCons : store.isConsumed target = true) :
    (stepMusigOp c mode store op).2.isConsumed target = true := by
  cases op with
  | evict sid =>
    exact hCons
  | round1 sid freshRand tasks =>
    have h := executeRound1Pass_preserves_consumed c mode store sid target freshRand tasks hCons
    simp only [stepMusigOp]
    cases hEx : executeRound1Pass c mode store sid freshRand tasks with
    | ok p =>
      rcases p with ⟨nonces, store'⟩
      rw [hEx] at h
      exact h
    | error p =>
      rcases p with ⟨err, store'⟩
      rw [hEx] at h
      exact h
  | round2 sid inputs =>
    have h := executeRound2Pass_preserves_consumed c mode store sid target inputs hCons
    simp only [stepMusigOp]
    cases hEx : executeRound2Pass c mode store sid inputs with
    | ok p =>
      rcases p with ⟨sigs, store'⟩
      rw [hEx] at h
      exact h
    | error p =>
      rcases p with ⟨err, store'⟩
      rw [hEx] at h
      exact h

theorem executeRound2Pass_ok_consumes {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store store' : MusigSessionStore)
    (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput) (sigs : List MusigRound2Output)
    (hOk : executeRound2Pass c mode store sid inputs = .ok (sigs, store')) :
    store.isConsumed sid = false ∧ store'.isConsumed sid = true := by
  unfold executeRound2Pass at hOk
  cases hPop : store.consumeRound2 sid with
  | error err =>
    rw [hPop] at hOk
    contradiction
  | ok pair =>
    rcases pair with ⟨rr, consumedStore⟩
    rw [hPop] at hOk
    have hNotCons : store.isConsumed sid = false := by
      cases hC : store.isConsumed sid
      · rfl
      · rw [consumeRound2_rejects_when_consumed store sid hC] at hPop
        contradiction
    have hNowCons : consumedStore.isConsumed sid = true :=
      consumeRound2_marks_consumed hPop
    simp only at hOk
    split at hOk
    · contradiction
    · cases hMap : List.mapM (round2SignTask c mode rr) inputs with
      | error err =>
        rw [hMap] at hOk
        contradiction
      | ok outs =>
        rw [hMap] at hOk
        injection hOk with hPair
        have hSt : consumedStore = store' := congrArg Prod.snd hPair
        rw [← hSt]
        exact ⟨hNotCons, hNowCons⟩

/-- If `stepMusigOp` emits `.round2Ok sid sigs`, then `sid` was NOT consumed beforehand and IS
    consumed in the post-state. -/
theorem stepMusigOp_round2Ok_consumes {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store store' : MusigSessionStore) (op : MusigOp)
    (sid : PsbtSessionId) (sigs : List MusigRound2Output)
    (hStep : stepMusigOp c mode store op = (.round2Ok sid sigs, store')) :
    store.isConsumed sid = false ∧ store'.isConsumed sid = true := by
  cases op with
  | evict s =>
    simp [stepMusigOp] at hStep
  | round1 s r ts =>
    simp only [stepMusigOp] at hStep
    cases hEx : executeRound1Pass c mode store s r ts with
    | ok p =>
      rcases p with ⟨nonces, st'⟩
      rw [hEx] at hStep
      injection hStep with hEv _
      contradiction
    | error p =>
      rcases p with ⟨err, st'⟩
      rw [hEx] at hStep
      injection hStep with hEv _
      contradiction
  | round2 s inputs =>
    simp only [stepMusigOp] at hStep
    cases hEx : executeRound2Pass c mode store s inputs with
    | error p =>
      rcases p with ⟨err, st'⟩
      rw [hEx] at hStep
      injection hStep with hEv _
      contradiction
    | ok p =>
      rcases p with ⟨outs, st'⟩
      rw [hEx] at hStep
      injection hStep with hEv hSt
      injection hEv with hs hSigs
      subst hs
      subst hSt
      exact executeRound2Pass_ok_consumes c mode store st' s inputs outs hEx

/-- Once `sid` is consumed in `store`, no future trace `ops` can ever emit `.round2Ok sid _`. -/
theorem countRound2SuccessFor_zero_of_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (sid : PsbtSessionId) :
    ∀ (ops : List MusigOp) (store : MusigSessionStore),
      store.isConsumed sid = true →
      countRound2SuccessFor sid (runMusigTrace c mode store ops).1 = 0
  | [], _, _ => rfl
  | op :: ops, store, hCons => by
    simp only [runMusigTrace]
    have hNextCons : (stepMusigOp c mode store op).2.isConsumed sid = true :=
      stepMusigOp_preserves_consumed c mode store op sid hCons
    have ih := countRound2SuccessFor_zero_of_consumed c mode sid ops (stepMusigOp c mode store op).2 hNextCons
    cases hEv : (stepMusigOp c mode store op).1 with
    | round1Ok s ns => simp [countRound2SuccessFor, ih]
    | evicted s => simp [countRound2SuccessFor, ih]
    | failed s e => simp [countRound2SuccessFor, ih]
    | round2Ok s sigs =>
      simp only [countRound2SuccessFor]
      by_cases hEq : s = sid
      · subst hEq
        have hStepEq : stepMusigOp c mode store op = (.round2Ok s sigs, (stepMusigOp c mode store op).2) :=
          Prod.ext hEv rfl
        have ⟨hNotCons, _⟩ := stepMusigOp_round2Ok_consumes c mode store _ op s sigs hStepEq
        rw [hCons] at hNotCons
        contradiction
      · have hBeq : (s == sid) = false := beq_false_of_ne hEq
        simp [hBeq, ih]

/-- **Critical Security Theorem — MuSig2 Nonce Single-Use Linearity**:
    Across ANY arbitrary sequence of Round-1, Round-2, and eviction operations `ops` from ANY
    initial `MusigSessionStore`, a `PsbtSessionId` produces Round-2 partial signatures
    **at most once** (`countRound2SuccessFor sid events ≤ 1`). -/
theorem musig_nonce_single_use_linearity {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (sid : PsbtSessionId) :
    ∀ (ops : List MusigOp) (store : MusigSessionStore),
      countRound2SuccessFor sid (runMusigTrace c mode store ops).1 ≤ 1
  | [], _ => by simp [runMusigTrace, countRound2SuccessFor]
  | op :: ops, store => by
    simp only [runMusigTrace]
    cases hEv : (stepMusigOp c mode store op).1 with
    | round1Ok s ns =>
      simp [countRound2SuccessFor, musig_nonce_single_use_linearity c mode sid ops]
    | evicted s =>
      simp [countRound2SuccessFor, musig_nonce_single_use_linearity c mode sid ops]
    | failed s e =>
      simp [countRound2SuccessFor, musig_nonce_single_use_linearity c mode sid ops]
    | round2Ok s sigs =>
      simp only [countRound2SuccessFor]
      by_cases hEq : s = sid
      · subst hEq
        have hStepEq : stepMusigOp c mode store op = (.round2Ok s sigs, (stepMusigOp c mode store op).2) :=
          Prod.ext hEv rfl
        have ⟨_, hNowCons⟩ := stepMusigOp_round2Ok_consumes c mode store _ op s sigs hStepEq
        have hZero := countRound2SuccessFor_zero_of_consumed c mode s ops (stepMusigOp c mode store op).2 hNowCons
        simp [hZero]
      · have hBeq : (s == sid) = false := beq_false_of_ne hEq
        simp [hBeq, musig_nonce_single_use_linearity c mode sid ops]

/-! ## 10. Negative Security Rejection Theorems & Non-Vacuity Witness -/

/-- Round 2 rejects immediately when no session for `sid` exists in `MusigSessionStore`. -/
theorem executeRound2Pass_rejects_missing_session {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput) :
    executeRound2Pass c mode {} sid inputs = .error (.missingSession, {}) := by
  simp [executeRound2Pass, MusigSessionStore.consumeRound2, MusigSessionStore.isConsumed]

/-- Round 2 rejects with `.pubnonceMismatch` when the PSBT's self-pubnonce differs from the
    session's recomputed pubnonce (preventing Vanadium's unaggregatable-signature hazard). -/
theorem round2SignTask_rejects_mismatched_self_pubnonce {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (inp : MusigRound2TaskInput)
    (myPn recomputedPn aggnonce : PubNonce) (sec : SecNonce)
    (hNonEmpty : inp.task.sortedPubkeys.isEmpty = false)
    (hBound : !(inp.task.sortedPubkeys.length > maxPubkeysPerMusig))
    (hMyPn : inp.psbtMyPubnonce = some myPn)
    (hLen : inp.cosignerPubnonces.length = inp.task.sortedPubkeys.length)
    (hAgg : nonceAgg c inp.cosignerPubnonces = .ok aggnonce)
    (hGen : nonceGen c (syntheticRandIJ c randRoot inp.task.inputIndex inp.task.placeholderIndex)
              inp.task.internalPk (selectNonceAggPk mode inp.task.untweakedAggPk inp.task.tweakedAggPk)
            = .ok (sec, recomputedPn))
    (hMismatch : recomputedPn != myPn) :
    round2SignTask c mode randRoot inp = .error .pubnonceMismatch := by
  unfold round2SignTask
  have hNotGt : ¬ (inp.task.sortedPubkeys.length > maxPubkeysPerMusig) := by
    simpa using hBound
  simp [hNonEmpty, hNotGt, hMyPn, hLen, hAgg, hGen, hMismatch, Bind.bind, Except.bind]

/-- `partialSign` rejects secret keys outside `1 .. n-1`. -/
theorem partialSign_rejects_zero_sk {Affine : Type} (c : MusigCrypto Affine)
    (secnonce : SecNonce) (ctx : SessionContext) (vals : SessionValues Affine)
    (hVals : getSessionValues c ctx = .ok vals)
    (hk1 : 0 < secnonce.k1 ∧ secnonce.k1 < secp256k1Order)
    (hk2 : 0 < secnonce.k2 ∧ secnonce.k2 < secp256k1Order) :
    partialSign c secnonce (SizedBytes.zeros 32) ctx = .error .secretKeyOutOfRange := by
  have hZero : bytes32ToNat (SizedBytes.zeros 32) = 0 := by
    decide
  unfold partialSign parseNonZeroScalar
  simp [hVals, hk1.1, hk1.2, hk2.1, hk2.2, hZero, Bind.bind, Except.bind]

/-- Concrete toy model of `MusigCrypto Unit` proving non-vacuity of Round 1 → Round 2 signing
    and immediate consumption rejection on a second Round 2 attempt. -/
def oneByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[1]), by simp [ByteArray.size]⟩

def xByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[0x11]), by simp [ByteArray.size]⟩

def sidByte32 : PsbtSessionId :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[7]), by simp [ByteArray.size]⟩

def rrByte32 : RandRoot :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[42]), by simp [ByteArray.size]⟩

def sighashByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[99]), by simp [ByteArray.size]⟩

def threeByte32 : PartialSig :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[3]), by simp [ByteArray.size]⟩

def toyCompressedPk : CompressedPubKey :=
  ⟨ByteArray.mk (#[0x02] ++ Array.replicate 32 0x11), by simp [ByteArray.size]⟩

def nonVacuousToyCrypto : MusigCrypto Unit :=
  { generator := ()
    pointAdd := fun p q =>
      match p, q with
      | .infinity, x => x
      | x, .infinity => x
      | .affine _, .affine _ => .affine ()
    pointMul := fun k p =>
      if k % secp256k1Order == 0 then .infinity else p
    pointNeg := fun p => p
    hasEvenY := fun _ => true
    xCoord := fun _ => xByte32
    compress := fun _ => toyCompressedPk
    decompress := fun _ => some ()
    taggedHash := fun _ _ => oneByte32
    sha256 := fun _ => oneByte32
    ckdPubUnhardened := fun pk cc _ => some (pk, cc, oneByte32) }

theorem bytes32ToNat_oneByte32 : bytes32ToNat oneByte32 = 1 := by
  decide

theorem scalarToBytes32_three : scalarToBytes32 3 = threeByte32 := by
  decide

/-- **Non-Vacuity Witness**: There exist concrete cryptographic parameters, a Round-1 task, and a
    Round-2 task such that Round 1 commits a session, Round 2 produces a non-empty partial signature
    list and marks the session consumed, and any replay of Round 2 fails with `.sessionAlreadyConsumed`. -/
theorem nonvacuous_round1_then_round2_and_replay_rejected :
    ∃ (sid : PsbtSessionId) (rr : RandRoot)
      (t1 : MusigSignTask) (t2 : MusigRound2TaskInput)
      (r1Out : List MusigRound1Output) (s1 : MusigSessionStore)
      (r2Out : List MusigRound2Output) (s2 : MusigSessionStore),
      executeRound1Pass nonVacuousToyCrypto .untweakedBolos {} sid rr [t1] = .ok (r1Out, s1) ∧
      r1Out.length = 1 ∧
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s1 sid [t2] = .ok (r2Out, s2) ∧
      r2Out.length = 1 ∧
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s2 sid [t2] =
        .error (.sessionAlreadyConsumed, s2) := by
  let sid : PsbtSessionId := sidByte32
  let rr : RandRoot := rrByte32
  let pk : CompressedPubKey := toyCompressedPk
  let pn : PubNonce := PubNonce.ofParts pk pk
  let task : MusigSignTask := {
    inputIndex := 0
    placeholderIndex := 0
    internalPk := pk
    untweakedAggPk := pk
    tweakedAggPk := pk
    sortedPubkeys := [pk]
    tweaks := []
    leafHash := none
  }
  let r2Inp : MusigRound2TaskInput := {
    task := task
    secretKey := oneByte32
    sighash := sighashByte32
    psbtMyPubnonce := some pn
    cosignerPubnonces := [pn]
  }
  let s1 : MusigSessionStore := { activeEntries := [(sid, rr)], consumedIds := [], capacity := none }
  let s2 : MusigSessionStore := { activeEntries := [], consumedIds := [sid], capacity := none }
  have hOrdNe1 : secp256k1Order ≠ 1 := by decide
  have hOrd1 : 1 < secp256k1Order := by decide
  have hSidZero : sid.isAllZeros = false := by decide
  have hPnZero : (PubNonce.r1Bytes pn).isAllZeros = false := by decide
  have hPn2Zero : (PubNonce.r2Bytes pn).isAllZeros = false := by decide
  have hOneMod : parseScalarModN oneByte32 = 1 := by
    unfold parseScalarModN
    rw [bytes32ToNat_oneByte32]
    decide
  have hOneNz : parseNonZeroScalar oneByte32 = some 1 := by
    unfold parseNonZeroScalar
    rw [bytes32ToNat_oneByte32]
    decide
  have hHash : ∀ tag msg, nonVacuousToyCrypto.taggedHash tag msg = oneByte32 := fun _ _ => rfl
  have hSha : ∀ msg, nonVacuousToyCrypto.sha256 msg = oneByte32 := fun _ => rfl
  have hComp : ∀ p, nonVacuousToyCrypto.compress p = toyCompressedPk := fun _ => rfl
  have hDecomp : ∀ b, nonVacuousToyCrypto.decompress b = some () := fun _ => rfl
  have hEven : ∀ p, nonVacuousToyCrypto.hasEvenY p = true := fun _ => rfl
  have hMul1 : ∀ p, nonVacuousToyCrypto.pointMul 1 p = p := by
    intro p
    show (if 1 % secp256k1Order == 0 then CurvePoint.infinity else p) = p
    have h1 : (1 % secp256k1Order == 0) = false := by decide
    rw [h1]
    rfl
  have hAddAff : nonVacuousToyCrypto.pointAdd .infinity (.affine ()) = .affine () := rfl
  have hAddAff2 : nonVacuousToyCrypto.pointAdd (.affine ()) (.affine ()) = .affine () := rfl
  have hGen : nonceGen nonVacuousToyCrypto oneByte32 pk pk.xOnly =
      .ok ({ k1 := 1, k2 := 1, pk := pk }, pn) := by
    unfold nonceGen nonceHash
    simp [hHash, hOneMod, hMul1, hComp, pk, pn]
  have hR1 :
      executeRound1Pass nonVacuousToyCrypto .untweakedBolos {} sid rr [task] =
        .ok ([{ inputIndex := 0, pubnonce := pn, participantPk := pk, aggregatePubkey := pk, leafHash := none }], s1) := by
    unfold executeRound1Pass round1ProduceTaskNonce syntheticRandIJ selectNonceAggPk
    simp [sid, s1, task, hSidZero, MusigSessionStore.isConsumed, MusigSessionStore.evictUnconsumed,
      MusigSessionStore.registerRound1, trimToCapacity, distinctTaskCoordinates, maxPubkeysPerMusig,
      hSha, hGen, List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hAgg : nonceAgg nonVacuousToyCrypto [pn] = .ok pn := by
    unfold nonceAgg
    simp [sumNonceComponent, hDecomp, hAddAff, hComp, pn, pk, Bind.bind, Except.bind]
  have hSign : partialSign nonVacuousToyCrypto { k1 := 1, k2 := 1, pk := pk } oneByte32
      { aggnonce := pn, pubkeys := [pk], tweaks := [], msg := sighashByte32.bytes } = .ok threeByte32 := by
    have hThreeMod : 3 % secp256k1Order = 3 := by decide
    unfold partialSign getSessionValues keyAgg applyTweaks cpointExt keyAggCoeff secondUniqueKey
    simp [keyAggLoop, cpoint, keyAggCoeffInternal, hDecomp, hHash, hEven, hMul1, hAddAff, hAddAff2, hComp,
      hPnZero, hPn2Zero, hOneMod, hOneNz, hOrd1, hThreeMod, scalarToBytes32_three, pk, Bind.bind, Except.bind]
  have hR2 :
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s1 sid [r2Inp] =
        .ok ([{ inputIndex := 0, signature := threeByte32, participantPk := pk, aggregatePubkey := pk, leafHash := none }], s2) := by
    unfold executeRound2Pass MusigSessionStore.consumeRound2 round2SignTask syntheticRandIJ selectNonceAggPk
    simp [sid, s1, s2, r2Inp, task, MusigSessionStore.isConsumed, distinctTaskCoordinates,
      maxPubkeysPerMusig, hSha, hAgg, hGen, hSign,
      List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hReplay :
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s2 sid [r2Inp] =
        .error (.sessionAlreadyConsumed, s2) := by
    unfold executeRound2Pass MusigSessionStore.consumeRound2
    simp [s2, sid, MusigSessionStore.isConsumed]
  exact ⟨sid, rr, task, r2Inp, _, s1, _, s2, hR1, rfl, hR2, rfl, hReplay⟩

end Spec.Musig2

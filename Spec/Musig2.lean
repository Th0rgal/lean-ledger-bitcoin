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

/-- Pure recursive byte-list equality (avoids `Classical.choice` in `BEq` on `List UInt8`). -/
def byteListEq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => decide (a = b) && byteListEq as bs
  | _, _ => false

theorem byteListEq_refl (xs : List UInt8) : byteListEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [byteListEq, ih]

theorem byteListEq_symm (xs ys : List UInt8) : byteListEq xs ys = byteListEq ys xs := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [byteListEq]
      by_cases hxy : x = y
      · subst hxy
        simp [ih ys]
      · have hyx : y ≠ x := fun h => hxy h.symm
        simp [hxy, hyx]

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

/-- Fixed BIP-328 synthetic aggregate xpub chaincode (`SHA256("MuSig2MuSig2MuSig2")`) as `Bytes32`. -/
def bip328Chaincode : Bytes32 :=
  ⟨ByteArray.mk bip328ChaincodeBytes.toArray, by
    change bip328ChaincodeBytes.toArray.size = 32
    rw [List.size_toArray, bip328ChaincodeBytes_length]⟩

/-- Compare two `PsbtSessionId`s on their first `idMatchBytes` bytes
    (`idMatchBytes = 28` on BOLOS NVRAM slots, `idMatchBytes = 32` on Vanadium). -/
def sessionIdPrefixEq (idMatchBytes : Nat) (a b : PsbtSessionId) : Bool :=
  byteListEq (a.bytes.data.toList.take idMatchBytes) (b.bytes.data.toList.take idMatchBytes)

theorem sessionIdPrefixEq_refl (idMatchBytes : Nat) (a : PsbtSessionId) :
    sessionIdPrefixEq idMatchBytes a a = true := by
  unfold sessionIdPrefixEq
  exact byteListEq_refl _

theorem sessionIdPrefixEq_symm (idMatchBytes : Nat) (a b : PsbtSessionId) :
    sessionIdPrefixEq idMatchBytes a b = sessionIdPrefixEq idMatchBytes b a := by
  unfold sessionIdPrefixEq
  exact byteListEq_symm _ _

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

/-! ### BIP-388 / BIP-328 Per-Input MuSig2 Key & Tweak Derivation -/

/-- Taproot spend path for a `musig(...)` key expression (`keypath` vs `tapscript`). -/
inductive MusigSpendPath where
  | keypath (taptreeHash : Option Bytes32)
  | tapscript (leafHash : Bytes32)
  deriving Repr, DecidableEq

/-- Derived per-`(input, placeholder)` MuSig2 keys and tweak stack
    (mirroring `compute_musig_per_input_info` in C and `compute_per_input_info` in Vanadium). -/
structure MusigPerInputInfo where
  sortedPubkeys : List CompressedPubKey
  untweakedAggPk : CompressedPubKey
  preTapTweakAggPk : CompressedPubKey
  tweakedAggPk : CompressedPubKey
  tweaks : List MusigTweak
  leafHash : Option Bytes32
  deriving Repr, DecidableEq

/-- First hardened BIP-32 child index (`2^31`). -/
def bip32HardenedBit : UInt32 := 0x80000000

/-- Derive sorted participant keys, BIP-328 synthetic aggregate xpub, two unhardened BIP-32
    derivation tweaks `(changeStep, addressIndex)`, and conditional BIP-341 `TapTweak`. -/
def deriveMusigPerInputInfo {Affine : Type} (c : MusigCrypto Affine)
    (participantPubkeys : List CompressedPubKey)
    (numFirst numSecond : UInt32)
    (isChange : Bool)
    (addressIndex : UInt32)
    (spend : MusigSpendPath) : Except MusigError MusigPerInputInfo := do
  if participantPubkeys.isEmpty then
    .error .emptyPubkeyList
  if participantPubkeys.length > maxPubkeysPerMusig then
    .error .tooManyPubkeys
  let changeStep : UInt32 := if isChange then numSecond else numFirst
  if decide (bip32HardenedBit ≤ changeStep) || decide (bip32HardenedBit ≤ addressIndex) then
    .error .derivationFailed
  let sorted := keySort participantPubkeys
  let baseCtx ← keyAgg c sorted
  let untweakedAggPk := c.compress baseCtx.q
  let (child1Pk, child1Cc, t0) ← match c.ckdPubUnhardened untweakedAggPk bip328Chaincode changeStep with
    | some res => .ok res
    | none => .error .derivationFailed
  let (child2Pk, _child2Cc, t1) ← match c.ckdPubUnhardened child1Pk child1Cc addressIndex with
    | some res => .ok res
    | none => .error .derivationFailed
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
    let tapPayload := match treeOpt with
      | none => child2Pk.xOnly.bytes
      | some h => appendBytes child2Pk.xOnly.bytes h.bytes
    let t2 := c.taggedHash "TapTweak" tapPayload
    let tw2 : MusigTweak := { scalar := t2, isXOnly := true }
    let child2Point ← cpoint c child2Pk
    let tweakedCtx ← applyTweak c { q := child2Point, gacc := 1, tacc := 0 } tw2
    .ok {
      sortedPubkeys := sorted
      untweakedAggPk := untweakedAggPk
      preTapTweakAggPk := child2Pk
      tweakedAggPk := c.compress tweakedCtx.q
      tweaks := [tw0, tw1, tw2]
      leafHash := none
    }

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
    `H_{"PsbtSessionId"}(descriptor_template_sha256 || keys_info_merkle_root || u8(len) || musig2_session_id)`.
    - When `musig2SessionId = none` (field absent in PSBT), `len = 0` is hashed.
    - When `musig2SessionId = some bs` (field present in PSBT), `psbt_get_global_musig2_session_id`
      requires `1 ≤ bs.size ≤ 32` (rejecting empty `some #[]` as well as `> 32` bytes). -/
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
  deriving Repr, DecidableEq

/-- Canonical `MusigSessionStore`: tracks active Round-1 sessions (bounded by `capacity` if set,
    matching session IDs on their `idMatchBytes` prefix: `28` on BOLOS, `32` on Vanadium)
    and the ghost monotonic history `consumedRandRoots` of single-use Round-2 nonce roots.
    Unlike a tombstone list on `PsbtSessionId`, Round 2 deletes `sid` from `activeEntries`,
    allowing a fresh Round 1 with a fresh `RandRoot` to re-register the same `sid`
    (as tested in `test_sign_psbt_musig.py:509`). -/
structure MusigSessionStore where
  activeEntries : List (PsbtSessionId × RandRoot) := []
  consumedRandRoots : List RandRoot := []
  capacity : Option Nat := none
  idMatchBytes : Nat := 32
  deriving Repr, DecidableEq

instance : Inhabited MusigSessionStore :=
  ⟨{}⟩

/-- Default BOLOS MuSig2 NVRAM session store (`capacity := some 32, idMatchBytes := 28`). -/
def MusigSessionStore.bolosDefault : MusigSessionStore :=
  { activeEntries := []
    consumedRandRoots := []
    capacity := some bolosMaxMusigSessions
    idMatchBytes := bolosStoredIdPrefixLen }

/-- Default Vanadium MuSig2 RAM session store (`capacity := some 1, idMatchBytes := 32`). -/
def MusigSessionStore.vanadiumDefault : MusigSessionStore :=
  { activeEntries := []
    consumedRandRoots := []
    capacity := some vanadiumMaxMusigSessions
    idMatchBytes := 32 }

/-- Whether a `RandRoot` has already been consumed by a Round-2 signing invocation. -/
def MusigSessionStore.isRandRootConsumed (store : MusigSessionStore) (rr : RandRoot) : Bool :=
  listMem rr store.consumedRandRoots

/-- Look up an active `randRoot` for `sid` (matching on `store.idMatchBytes`). -/
def MusigSessionStore.lookupActive (store : MusigSessionStore) (sid : PsbtSessionId) :
    Option RandRoot :=
  match store.activeEntries.find? (fun p => sessionIdPrefixEq store.idMatchBytes p.1 sid) with
  | some (_, rr) => some rr
  | none => none

/-- Query the logical `SessionLifecycle` of `sid`. -/
def MusigSessionStore.status (store : MusigSessionStore) (sid : PsbtSessionId) : SessionLifecycle :=
  match store.lookupActive sid with
  | some rr => .active rr
  | none => .unseen

/-- Enforce optional slot capacity by evicting oldest active entries (FIFO) if needed. -/
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
    - Rejects if `sid` or `randRoot` is `0x00..00` (reserved sentinel) or if a faulty RNG
      re-supplies an already-consumed `randRoot`.
    - Overwrites any existing matching `.active` entry for `sid` (on `idMatchBytes` prefix)
      and evicts FIFO when `activeEntries` exceeds `capacity`. -/
def MusigSessionStore.registerRound1 (store : MusigSessionStore)
    (sid : PsbtSessionId) (randRoot : RandRoot) : Except MusigError MusigSessionStore :=
  if sid.isAllZeros || randRoot.isAllZeros || store.isRandRootConsumed randRoot then
    .error .nonceGenFailed
  else
    let filtered := store.activeEntries.filter
      (fun p => !sessionIdPrefixEq store.idMatchBytes p.1 sid)
    let updated := trimToCapacity store.capacity (filtered ++ [(sid, randRoot)])
    .ok { store with activeEntries := updated }

/-- Atomically pop `sid` from `activeEntries` for Round 2, returning `(randRoot, updatedStore)`.
    - Fails with `.missingSession` when no active entry matches `sid` (including on any
      immediate Round-2 replay after `sid` was already popped!).
    - Records `randRoot` in ghost `consumedRandRoots` so no `RandRoot` can ever sign twice. -/
def MusigSessionStore.consumeRound2 (store : MusigSessionStore) (sid : PsbtSessionId) :
    Except MusigError (RandRoot × MusigSessionStore) :=
  match store.activeEntries.find? (fun p => sessionIdPrefixEq store.idMatchBytes p.1 sid) with
  | none => .error .missingSession
  | some (_, randRoot) =>
    if store.isRandRootConsumed randRoot then
      .error .sessionAlreadyConsumed
    else
      let remaining := store.activeEntries.filter
        (fun p => !sessionIdPrefixEq store.idMatchBytes p.1 sid)
      let store' : MusigSessionStore := {
        store with
        activeEntries := remaining
        consumedRandRoots := randRoot :: store.consumedRandRoots
      }
      .ok (randRoot, store')

/-- Evict an unconsumed active session matching `sid` (ghost `consumedRandRoots` are preserved). -/
def MusigSessionStore.evictUnconsumed (store : MusigSessionStore) (sid : PsbtSessionId) :
    MusigSessionStore :=
  { store with
    activeEntries := store.activeEntries.filter
      (fun p => !sessionIdPrefixEq store.idMatchBytes p.1 sid) }

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

/-- Construct a `MusigSignTask` from derived `MusigPerInputInfo`. -/
def MusigPerInputInfo.toSignTask (info : MusigPerInputInfo)
    (inputIndex placeholderIndex : UInt32) (internalPk : CompressedPubKey) : MusigSignTask :=
  { inputIndex := inputIndex
    placeholderIndex := placeholderIndex
    internalPk := internalPk
    untweakedAggPk := info.untweakedAggPk
    tweakedAggPk := info.tweakedAggPk
    sortedPubkeys := info.sortedPubkeys
    tweaks := info.tweaks
    leafHash := info.leafHash }

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

/-- Check pairwise distinctness of `(inputIndex, placeholderIndex, internalPk)` across tasks
    in a single pass (allowing Vanadium multi-internal-key `musig(@0, @1)` where the device
    holds multiple participant keys for the same `(inputIndex, placeholderIndex)`). -/
def distinctTaskCoordinates : List (UInt32 × UInt32 × CompressedPubKey) → Bool
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
  if sid.isAllZeros || freshRandRoot.isAllZeros || store.isRandRootConsumed freshRandRoot then
    .error (.nonceGenFailed, store)
  else
    let poppedStore := store.evictUnconsumed sid
    let coords := tasks.map (fun t => (t.inputIndex, t.placeholderIndex, t.internalPk))
    if !distinctTaskCoordinates coords then
      .error (.nonceOutOfRange, poppedStore)
    else
      match tasks.mapM (round1ProduceTaskNonce c mode freshRandRoot) with
      | .error err => .error (err, poppedStore)
      | .ok outputs =>
        match poppedStore.registerRound1 sid freshRandRoot with
        | .error err => .error (err, poppedStore)
        | .ok committedStore => .ok (outputs, committedStore)

/-- Produce a Round-2 `MusigRound2Output` for one task, optionally enforcing self-pubnonce
    byte-equality (`checkSelfPubnonce = true` on BOLOS, configurable on Vanadium) before
    invoking `partialSign`. -/
def round2SignTask {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (inp : MusigRound2TaskInput)
    (checkSelfPubnonce : Bool := true) :
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
  if checkSelfPubnonce && decide (recomputedPubnonce ≠ myPubnonce) then
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

/-- Execute a complete Round-2 PSBT pass for `sid`, atomically popping `sid` before signing. -/
def executeRound2Pass {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
    (checkSelfPubnonce : Bool := true) :
    Except (MusigError × MusigSessionStore) (List MusigRound2Output × MusigSessionStore) :=
  match store.consumeRound2 sid with
  | .error err => .error (err, store)
  | .ok (randRoot, consumedStore) =>
    let coords := inputs.map (fun inp => (inp.task.inputIndex, inp.task.placeholderIndex, inp.task.internalPk))
    if !distinctTaskCoordinates coords then
      .error (.nonceOutOfRange, consumedStore)
    else
      match inputs.mapM (fun inp => round2SignTask c mode randRoot inp checkSelfPubnonce) with
      | .error err => .error (err, consumedStore)
      | .ok sigs => .ok (sigs, consumedStore)

/-! ## 9. Multi-Step Session Transition System & Linearity Proofs -/

/-- Observable operations on `MusigSessionStore`. -/
inductive MusigOp where
  | round1 (sid : PsbtSessionId) (freshRand : RandRoot) (tasks : List MusigSignTask)
  | round2 (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
  | evict (sid : PsbtSessionId)
  deriving Repr, DecidableEq

/-- Observable event emitted by one `MusigOp` step.
    `.round2Ok` records the consumed `RandRoot` alongside `sid` and emitted signatures so
    single-use nonce linearity is directly observable per generated `RandRoot`. -/
inductive MusigStepEvent where
  | round1Ok (sid : PsbtSessionId) (nonces : List MusigRound1Output)
  | round2Ok (sid : PsbtSessionId) (randRoot : RandRoot) (sigs : List MusigRound2Output)
  | evicted (sid : PsbtSessionId)
  | failed (sid : PsbtSessionId) (err : MusigError)
  deriving Repr, DecidableEq

/-- Execute a single `MusigOp`, always returning `(event, postStore)`. -/
def stepMusigOp {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) (op : MusigOp) (checkSelfPubnonce : Bool := true) :
    MusigStepEvent × MusigSessionStore :=
  match op with
  | .round1 sid freshRand tasks =>
    match executeRound1Pass c mode store sid freshRand tasks with
    | .ok (nonces, store') => (.round1Ok sid nonces, store')
    | .error (err, store') => (.failed sid err, store')
  | .round2 sid inputs =>
    match store.lookupActive sid, executeRound2Pass c mode store sid inputs checkSelfPubnonce with
    | some rr, .ok (sigs, store') => (.round2Ok sid rr sigs, store')
    | none, .ok (_, store') => (.failed sid .missingSession, store')
    | _, .error (err, store') => (.failed sid err, store')
  | .evict sid =>
    (.evicted sid, store.evictUnconsumed sid)

/-- Execute a multi-step sequence of `MusigOp`s, collecting all emitted events. -/
def runMusigTrace {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) (ops : List MusigOp) (checkSelfPubnonce : Bool := true) :
    List MusigStepEvent × MusigSessionStore :=
  match ops with
  | [] => ([], store)
  | op :: restOps =>
    let (ev, store') := stepMusigOp c mode store op checkSelfPubnonce
    let (restEvs, finalStore) := runMusigTrace c mode store' restOps checkSelfPubnonce
    (ev :: restEvs, finalStore)

/-- Count how many times a given `RandRoot` successfully produced Round-2 partial signatures
    in an event trace. -/
def countRound2SuccessForRandRoot (rr : RandRoot) : List MusigStepEvent → Nat
  | [] => 0
  | .round2Ok _ rr' _ :: rest =>
    (if decide (rr' = rr) then 1 else 0) + countRound2SuccessForRandRoot rr rest
  | _ :: rest => countRound2SuccessForRandRoot rr rest

/-- Count how many times `sid` successfully produced Round-2 partial signatures in an event trace. -/
def countRound2SuccessFor (sid : PsbtSessionId) : List MusigStepEvent → Nat
  | [] => 0
  | .round2Ok sid' _ _ :: rest =>
    (if decide (sid' = sid) then 1 else 0) + countRound2SuccessFor sid rest
  | _ :: rest => countRound2SuccessFor sid rest

/-! ### Key Security Theorems: Monotonicity, Replay Rejection & Single-Use Nonce Linearity -/

theorem find_none_of_filter_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter (fun x => !p x)).find? p = none
  | [] => rfl
  | x :: xs => by
    simp only [List.filter]
    cases hp : p x with
    | true =>
      simp [find_none_of_filter_false p xs]
    | false =>
      simp [hp, find_none_of_filter_false p xs]

theorem isRandRootConsumed_evictUnconsumed (store : MusigSessionStore)
    (sid : PsbtSessionId) (target : RandRoot) :
    (store.evictUnconsumed sid).isRandRootConsumed target = store.isRandRootConsumed target := by
  rfl

theorem isRandRootConsumed_registerRound1 {store store' : MusigSessionStore}
    {sid : PsbtSessionId} {rr : RandRoot}
    (h : store.registerRound1 sid rr = .ok store') (target : RandRoot) :
    store'.isRandRootConsumed target = store.isRandRootConsumed target := by
  unfold MusigSessionStore.registerRound1 at h
  by_cases hBad : (sid.isAllZeros || rr.isAllZeros || store.isRandRootConsumed rr) = true
  · simp [hBad] at h
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h
    injection h with hEq
    rw [← hEq]
    rfl

theorem consumeRound2_marks_randRoot_consumed {store store' : MusigSessionStore}
    {sid : PsbtSessionId} {rr : RandRoot}
    (h : store.consumeRound2 sid = .ok (rr, store')) :
    store.lookupActive sid = some rr ∧
    store.isRandRootConsumed rr = false ∧
    store'.isRandRootConsumed rr = true ∧
    store'.lookupActive sid = none := by
  unfold MusigSessionStore.consumeRound2 at h
  unfold MusigSessionStore.lookupActive
  cases hFind : store.activeEntries.find? (fun p => sessionIdPrefixEq store.idMatchBytes p.1 sid) with
  | none => simp [hFind] at h
  | some pair =>
    rcases pair with ⟨matchedSid, foundRr⟩
    simp only [hFind] at h
    cases hCons : store.isRandRootConsumed foundRr with
    | true => simp [hCons] at h
    | false =>
      simp only [hCons, Bool.false_eq_true, ↓reduceIte] at h
      injection h with hPair
      have hRr : foundRr = rr := congrArg Prod.fst hPair
      have hSt : { store with
          activeEntries := store.activeEntries.filter (fun p => !sessionIdPrefixEq store.idMatchBytes p.1 sid)
          consumedRandRoots := foundRr :: store.consumedRandRoots } = store' := congrArg Prod.snd hPair
      subst hRr
      subst hSt
      refine ⟨rfl, hCons, ?_, ?_⟩
      · simp [MusigSessionStore.isRandRootConsumed, listMem]
      · have hNone := find_none_of_filter_false
          (fun p : PsbtSessionId × RandRoot => sessionIdPrefixEq store.idMatchBytes p.1 sid)
          store.activeEntries
        dsimp only
        rw [hNone]

theorem consumeRound2_preserves_randRoot_consumed {store store' : MusigSessionStore}
    {sid : PsbtSessionId} {rr target : RandRoot}
    (h : store.consumeRound2 sid = .ok (rr, store'))
    (hCons : store.isRandRootConsumed target = true) :
    store'.isRandRootConsumed target = true := by
  unfold MusigSessionStore.consumeRound2 at h
  cases hFind : store.activeEntries.find? (fun p => sessionIdPrefixEq store.idMatchBytes p.1 sid) with
  | none => simp [hFind] at h
  | some pair =>
    rcases pair with ⟨_, foundRr⟩
    simp only [hFind] at h
    cases hAlready : store.isRandRootConsumed foundRr with
    | true => simp [hAlready] at h
    | false =>
      simp only [hAlready, Bool.false_eq_true, ↓reduceIte] at h
      injection h with hPair
      have hSt : { store with
          activeEntries := store.activeEntries.filter (fun p => !sessionIdPrefixEq store.idMatchBytes p.1 sid)
          consumedRandRoots := foundRr :: store.consumedRandRoots } = store' := congrArg Prod.snd hPair
      subst hSt
      simp only [MusigSessionStore.isRandRootConsumed, listMem, Bool.or_eq_true]
      exact Or.inr hCons

theorem executeRound1Pass_preserves_randRoot_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (freshRand target : RandRoot) (tasks : List MusigSignTask)
    (hCons : store.isRandRootConsumed target = true) :
    (match executeRound1Pass c mode store sid freshRand tasks with
     | .ok (_, s') => s'
     | .error (_, s') => s').isRandRootConsumed target = true := by
  dsimp only [executeRound1Pass]
  by_cases hBad : (sid.isAllZeros || freshRand.isAllZeros || store.isRandRootConsumed freshRand) = true
  · simp [hBad, hCons]
  · simp only [Bool.not_eq_true] at hBad
    simp only [hBad, Bool.false_eq_true, ↓reduceIte]
    by_cases hDist : (!distinctTaskCoordinates (List.map (fun t => (t.inputIndex, t.placeholderIndex, t.internalPk)) tasks)) = true
    · simp [hDist, isRandRootConsumed_evictUnconsumed, hCons]
    · simp only [Bool.not_eq_true] at hDist
      simp only [hDist, Bool.false_eq_true, ↓reduceIte]
      cases List.mapM (round1ProduceTaskNonce c mode freshRand) tasks with
      | error _ =>
        simp [isRandRootConsumed_evictUnconsumed, hCons]
      | ok _ =>
        cases hReg : (store.evictUnconsumed sid).registerRound1 sid freshRand with
        | error _ =>
          simp [isRandRootConsumed_evictUnconsumed, hCons]
        | ok committed =>
          simp only [isRandRootConsumed_registerRound1 hReg, isRandRootConsumed_evictUnconsumed, hCons]

theorem executeRound2Pass_preserves_randRoot_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (target : RandRoot) (inputs : List MusigRound2TaskInput)
    (checkSelfPubnonce : Bool)
    (hCons : store.isRandRootConsumed target = true) :
    (match executeRound2Pass c mode store sid inputs checkSelfPubnonce with
     | .ok (_, s') => s'
     | .error (_, s') => s').isRandRootConsumed target = true := by
  dsimp only [executeRound2Pass]
  cases hPop : store.consumeRound2 sid with
  | error _ =>
    exact hCons
  | ok pair =>
    rcases pair with ⟨rr, consumedStore⟩
    have hPres : consumedStore.isRandRootConsumed target = true :=
      consumeRound2_preserves_randRoot_consumed hPop hCons
    by_cases hDist : (!distinctTaskCoordinates (List.map (fun inp => (inp.task.inputIndex, inp.task.placeholderIndex, inp.task.internalPk)) inputs)) = true
    · simp [hDist, hPres]
    · simp only [Bool.not_eq_true] at hDist
      simp only [hDist, Bool.false_eq_true, ↓reduceIte]
      cases List.mapM (fun inp => round2SignTask c mode rr inp checkSelfPubnonce) inputs <;> exact hPres

/-- **Irreversibility of Consumed Nonce Roots**:
    No single `stepMusigOp` transition (whether succeeding or failing!) can ever clear or
    resurrect a consumed `RandRoot`. -/
theorem stepMusigOp_preserves_randRoot_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore) (op : MusigOp) (target : RandRoot)
    (checkSelfPubnonce : Bool := true)
    (hCons : store.isRandRootConsumed target = true) :
    (stepMusigOp c mode store op checkSelfPubnonce).2.isRandRootConsumed target = true := by
  cases op with
  | evict sid =>
    exact hCons
  | round1 sid freshRand tasks =>
    have h := executeRound1Pass_preserves_randRoot_consumed c mode store sid freshRand target tasks hCons
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
    have h := executeRound2Pass_preserves_randRoot_consumed c mode store sid target inputs checkSelfPubnonce hCons
    simp only [stepMusigOp]
    cases hLook : store.lookupActive sid with
    | none =>
      cases hEx : executeRound2Pass c mode store sid inputs checkSelfPubnonce with
      | ok p =>
        rcases p with ⟨sigs, store'⟩
        rw [hEx] at h
        exact h
      | error p =>
        rcases p with ⟨err, store'⟩
        rw [hEx] at h
        exact h
    | some rr =>
      cases hEx : executeRound2Pass c mode store sid inputs checkSelfPubnonce with
      | ok p =>
        rcases p with ⟨sigs, store'⟩
        rw [hEx] at h
        exact h
      | error p =>
        rcases p with ⟨err, store'⟩
        rw [hEx] at h
        exact h

theorem executeRound2Pass_ok_consumes_randRoot {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store store' : MusigSessionStore)
    (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
    (checkSelfPubnonce : Bool) (sigs : List MusigRound2Output)
    (hOk : executeRound2Pass c mode store sid inputs checkSelfPubnonce = .ok (sigs, store')) :
    ∃ rr : RandRoot,
      store.lookupActive sid = some rr ∧
      store.isRandRootConsumed rr = false ∧
      store'.isRandRootConsumed rr = true ∧
      store'.lookupActive sid = none := by
  unfold executeRound2Pass at hOk
  cases hPop : store.consumeRound2 sid with
  | error err =>
    rw [hPop] at hOk
    contradiction
  | ok pair =>
    rcases pair with ⟨rr, consumedStore⟩
    rw [hPop] at hOk
    have ⟨hLook, hNotCons, hNowCons, hGone⟩ := consumeRound2_marks_randRoot_consumed hPop
    simp only at hOk
    split at hOk
    · contradiction
    · cases hMap : List.mapM (fun inp => round2SignTask c mode rr inp checkSelfPubnonce) inputs with
      | error err =>
        rw [hMap] at hOk
        contradiction
      | ok outs =>
        rw [hMap] at hOk
        injection hOk with hPair
        have hSt : consumedStore = store' := congrArg Prod.snd hPair
        rw [← hSt]
        exact ⟨rr, hLook, hNotCons, hNowCons, hGone⟩

/-- **Immediate Round-2 Replay Fails with `.missingSession`**:
    Whenever Round 2 succeeds on `sid` producing `store'`, any immediate Round-2 replay on `sid`
    without an intervening Round 1 fails with `.missingSession`. -/
theorem round2_replay_without_round1_missingSession {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store store' : MusigSessionStore)
    (sid : PsbtSessionId) (inputs replayInputs : List MusigRound2TaskInput)
    (checkSelfPubnonce replayCheck : Bool) (sigs : List MusigRound2Output)
    (hOk : executeRound2Pass c mode store sid inputs checkSelfPubnonce = .ok (sigs, store')) :
    executeRound2Pass c mode store' sid replayInputs replayCheck = .error (.missingSession, store') := by
  obtain ⟨_rr, _hLook, _hNotCons, _hNowCons, hGone⟩ :=
    executeRound2Pass_ok_consumes_randRoot c mode store store' sid inputs checkSelfPubnonce sigs hOk
  unfold executeRound2Pass MusigSessionStore.consumeRound2
  unfold MusigSessionStore.lookupActive at hGone
  cases hFind : store'.activeEntries.find? (fun p => sessionIdPrefixEq store'.idMatchBytes p.1 sid) with
  | none => rfl
  | some pair =>
    rw [hFind] at hGone
    contradiction

/-- If `stepMusigOp` emits `.round2Ok sid rr sigs`, then `rr` was NOT consumed beforehand and IS
    consumed in the post-state. -/
theorem stepMusigOp_round2Ok_consumes_randRoot {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store store' : MusigSessionStore) (op : MusigOp)
    (checkSelfPubnonce : Bool)
    (sid : PsbtSessionId) (rr : RandRoot) (sigs : List MusigRound2Output)
    (hStep : stepMusigOp c mode store op checkSelfPubnonce = (.round2Ok sid rr sigs, store')) :
    store.isRandRootConsumed rr = false ∧ store'.isRandRootConsumed rr = true := by
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
    cases hLook : store.lookupActive s with
    | none =>
      rw [hLook] at hStep
      cases hEx : executeRound2Pass c mode store s inputs checkSelfPubnonce with
      | ok p =>
        rcases p with ⟨outs, st'⟩
        rw [hEx] at hStep
        injection hStep with hEv _
        contradiction
      | error p =>
        rcases p with ⟨err, st'⟩
        rw [hEx] at hStep
        injection hStep with hEv _
        contradiction
    | some activeRr =>
      rw [hLook] at hStep
      cases hEx : executeRound2Pass c mode store s inputs checkSelfPubnonce with
      | error p =>
        rcases p with ⟨err, st'⟩
        rw [hEx] at hStep
        injection hStep with hEv _
        contradiction
      | ok p =>
        rcases p with ⟨outs, st'⟩
        rw [hEx] at hStep
        injection hStep with hEv hSt
        injection hEv with hs hRr hSigs
        subst hs
        subst hRr
        subst hSt
        obtain ⟨rr2, hLook2, hNotCons, hNowCons, _⟩ :=
          executeRound2Pass_ok_consumes_randRoot c mode store st' s inputs checkSelfPubnonce outs hEx
        rw [hLook] at hLook2
        injection hLook2 with hEqRr
        subst hEqRr
        exact ⟨hNotCons, hNowCons⟩

/-- Once `rr` is consumed in `store`, no future trace `ops` can ever emit `.round2Ok _ rr _`. -/
theorem countRound2SuccessForRandRoot_zero_of_consumed {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (rr : RandRoot) (checkSelfPubnonce : Bool) :
    ∀ (ops : List MusigOp) (store : MusigSessionStore),
      store.isRandRootConsumed rr = true →
      countRound2SuccessForRandRoot rr (runMusigTrace c mode store ops checkSelfPubnonce).1 = 0
  | [], _, _ => rfl
  | op :: ops, store, hCons => by
    simp only [runMusigTrace]
    have hNextCons : (stepMusigOp c mode store op checkSelfPubnonce).2.isRandRootConsumed rr = true :=
      stepMusigOp_preserves_randRoot_consumed c mode store op rr checkSelfPubnonce hCons
    have ih := countRound2SuccessForRandRoot_zero_of_consumed c mode rr checkSelfPubnonce ops
      (stepMusigOp c mode store op checkSelfPubnonce).2 hNextCons
    cases hEv : (stepMusigOp c mode store op checkSelfPubnonce).1 with
    | round1Ok s ns => simp [countRound2SuccessForRandRoot, ih]
    | evicted s => simp [countRound2SuccessForRandRoot, ih]
    | failed s e => simp [countRound2SuccessForRandRoot, ih]
    | round2Ok s rr' sigs =>
      simp only [countRound2SuccessForRandRoot]
      by_cases hEq : rr' = rr
      · subst hEq
        have hStepEq : stepMusigOp c mode store op checkSelfPubnonce =
            (.round2Ok s rr' sigs, (stepMusigOp c mode store op checkSelfPubnonce).2) :=
          Prod.ext hEv rfl
        have ⟨hNotCons, _⟩ :=
          stepMusigOp_round2Ok_consumes_randRoot c mode store _ op checkSelfPubnonce s rr' sigs hStepEq
        rw [hCons] at hNotCons
        contradiction
      · simp [hEq, ih]

/-- **Critical Security Theorem — MuSig2 Nonce Single-Use Linearity per `RandRoot`**:
    Across ANY arbitrary sequence of Round-1, Round-2, and eviction operations `ops` from ANY
    initial `MusigSessionStore` (even if a faulty RNG re-supplies a duplicate `RandRoot` or a
    client re-uses the same `PsbtSessionId`), each `RandRoot` produces Round-2 partial signatures
    **at most once** (`countRound2SuccessForRandRoot rr events ≤ 1`). -/
theorem musig_nonce_single_use_linearity {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (rr : RandRoot) (checkSelfPubnonce : Bool := true) :
    ∀ (ops : List MusigOp) (store : MusigSessionStore),
      countRound2SuccessForRandRoot rr (runMusigTrace c mode store ops checkSelfPubnonce).1 ≤ 1
  | [], _ => by simp [runMusigTrace, countRound2SuccessForRandRoot]
  | op :: ops, store => by
    simp only [runMusigTrace]
    cases hEv : (stepMusigOp c mode store op checkSelfPubnonce).1 with
    | round1Ok s ns =>
      simp [countRound2SuccessForRandRoot, musig_nonce_single_use_linearity c mode rr checkSelfPubnonce ops]
    | evicted s =>
      simp [countRound2SuccessForRandRoot, musig_nonce_single_use_linearity c mode rr checkSelfPubnonce ops]
    | failed s e =>
      simp [countRound2SuccessForRandRoot, musig_nonce_single_use_linearity c mode rr checkSelfPubnonce ops]
    | round2Ok s rr' sigs =>
      simp only [countRound2SuccessForRandRoot]
      by_cases hEq : rr' = rr
      · subst hEq
        have hStepEq : stepMusigOp c mode store op checkSelfPubnonce =
            (.round2Ok s rr' sigs, (stepMusigOp c mode store op checkSelfPubnonce).2) :=
          Prod.ext hEv rfl
        have ⟨_, hNowCons⟩ :=
          stepMusigOp_round2Ok_consumes_randRoot c mode store _ op checkSelfPubnonce s rr' sigs hStepEq
        have hZero := countRound2SuccessForRandRoot_zero_of_consumed c mode rr' checkSelfPubnonce ops
          (stepMusigOp c mode store op checkSelfPubnonce).2 hNowCons
        simp [hZero]
      · simp [hEq, musig_nonce_single_use_linearity c mode rr checkSelfPubnonce ops]

/-! ## 10. Negative Security Rejection Theorems & Non-Vacuity Witnesses -/

/-- Round 2 rejects immediately when no session for `sid` exists in `MusigSessionStore`. -/
theorem executeRound2Pass_rejects_missing_session {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput) :
    executeRound2Pass c mode {} sid inputs = .error (.missingSession, {}) := by
  simp [executeRound2Pass, MusigSessionStore.consumeRound2]

/-- BOLOS `computeBolosPsbtSessionId` rejects an explicitly empty `some #[]` `musig2SessionId`,
    while accepting `none` (field absent -> length 0 hashed). -/
theorem computeBolosPsbtSessionId_rejects_empty_some {Affine : Type} (c : MusigCrypto Affine)
    (descSha256 merkleRoot : Bytes32) :
    computeBolosPsbtSessionId c descSha256 merkleRoot (some (ByteArray.mk #[])) = none ∧
    (computeBolosPsbtSessionId c descSha256 merkleRoot none).isSome = true := by
  simp [computeBolosPsbtSessionId, ByteArray.size]

/-- Round 2 rejects with `.pubnonceMismatch` when `checkSelfPubnonce = true` and the PSBT's
    self-pubnonce differs from the session's recomputed pubnonce (preventing Vanadium's
    unaggregatable-signature hazard when enabled). -/
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
    (hMismatch : recomputedPn ≠ myPn) :
    round2SignTask c mode randRoot inp true = .error .pubnonceMismatch := by
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

/-- Concrete toy model of `MusigCrypto Unit` proving non-vacuity of Round 1 → Round 2 signing,
    immediate replay rejection with `.missingSession`, and fresh Round 1 re-registration on the
    same `PsbtSessionId` with a fresh `RandRoot`. -/
def oneByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[1]), by simp [ByteArray.size]⟩

def xByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[0x11]), by simp [ByteArray.size]⟩

def sidByte32 : PsbtSessionId :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[7]), by simp [ByteArray.size]⟩

def rrByte32 : RandRoot :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[42]), by simp [ByteArray.size]⟩

def rr2Byte32 : RandRoot :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[43]), by simp [ByteArray.size]⟩

def sighashByte32 : Bytes32 :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[99]), by simp [ByteArray.size]⟩

def threeByte32 : PartialSig :=
  ⟨ByteArray.mk (Array.replicate 31 (0 : UInt8) ++ #[3]), by simp [ByteArray.size]⟩

def toyCompressedPk : CompressedPubKey :=
  ⟨ByteArray.mk (#[0x02] ++ Array.replicate 32 0x11), by simp [ByteArray.size]⟩

def toyCompressedPk2 : CompressedPubKey :=
  ⟨ByteArray.mk (#[0x02] ++ Array.replicate 32 0x22), by simp [ByteArray.size]⟩

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

/-- **Non-Vacuity Witness (`C-02`)**:
    1. Round 1 with `(sid, rr1)` commits `s1`.
    2. Round 2 on `sid` produces partial signatures and deletes `sid` from `activeEntries` (`s2`).
    3. Immediate Round-2 replay on `sid` without a new Round 1 fails with `.missingSession`.
    4. A fresh Round 1 on the **same** `sid` with a fresh `rr2` succeeds (`s3`), and the subsequent
       Round 2 on `sid` succeeds (`s4`) — matching `test_sign_psbt_musig.py:509`! -/
theorem nonvacuous_round1_then_round2_and_replay_rejected :
    ∃ (sid : PsbtSessionId) (rr1 rr2 : RandRoot)
      (t1 : MusigSignTask) (t2 : MusigRound2TaskInput)
      (r1Out : List MusigRound1Output) (s1 : MusigSessionStore)
      (r2Out : List MusigRound2Output) (s2 : MusigSessionStore)
      (r1Out2 : List MusigRound1Output) (s3 : MusigSessionStore)
      (r2Out2 : List MusigRound2Output) (s4 : MusigSessionStore),
      executeRound1Pass nonVacuousToyCrypto .untweakedBolos MusigSessionStore.bolosDefault sid rr1 [t1] = .ok (r1Out, s1) ∧
      r1Out.length = 1 ∧
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s1 sid [t2] = .ok (r2Out, s2) ∧
      r2Out.length = 1 ∧
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s2 sid [t2] =
        .error (.missingSession, s2) ∧
      executeRound1Pass nonVacuousToyCrypto .untweakedBolos s2 sid rr2 [t1] = .ok (r1Out2, s3) ∧
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s3 sid [t2] = .ok (r2Out2, s4) ∧
      r2Out2.length = 1 := by
  let sid : PsbtSessionId := sidByte32
  let rr1 : RandRoot := rrByte32
  let rr2 : RandRoot := rr2Byte32
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
  let s0 : MusigSessionStore := MusigSessionStore.bolosDefault
  let s1 : MusigSessionStore := { s0 with activeEntries := [(sid, rr1)], consumedRandRoots := [] }
  let s2 : MusigSessionStore := { s0 with activeEntries := [], consumedRandRoots := [rr1] }
  let s3 : MusigSessionStore := { s0 with activeEntries := [(sid, rr2)], consumedRandRoots := [rr1] }
  let s4 : MusigSessionStore := { s0 with activeEntries := [], consumedRandRoots := [rr2, rr1] }
  have hOrd1 : 1 < secp256k1Order := by decide
  have hSidZero : sid.isAllZeros = false := by decide
  have hRr1Zero : rr1.isAllZeros = false := by decide
  have hRr2Zero : rr2.isAllZeros = false := by decide
  have hRrNe : decide (rr2 = rr1) = false := by decide
  have hSidRefl : sessionIdPrefixEq bolosStoredIdPrefixLen sid sid = true :=
    sessionIdPrefixEq_refl bolosStoredIdPrefixLen sid
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
      executeRound1Pass nonVacuousToyCrypto .untweakedBolos s0 sid rr1 [task] =
        .ok ([{ inputIndex := 0, pubnonce := pn, participantPk := pk, aggregatePubkey := pk, leafHash := none }], s1) := by
    unfold executeRound1Pass round1ProduceTaskNonce syntheticRandIJ selectNonceAggPk
    simp [s0, s1, sid, rr1, task, hSidZero, hRr1Zero, MusigSessionStore.bolosDefault,
      bolosMaxMusigSessions, MusigSessionStore.isRandRootConsumed, MusigSessionStore.evictUnconsumed,
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
    simp [s0, s1, s2, sid, rr1, r2Inp, task, MusigSessionStore.bolosDefault, hSidRefl,
      MusigSessionStore.isRandRootConsumed, distinctTaskCoordinates,
      maxPubkeysPerMusig, hSha, hAgg, hGen, hSign,
      List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hReplay :
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s2 sid [r2Inp] =
        .error (.missingSession, s2) :=
    round2_replay_without_round1_missingSession nonVacuousToyCrypto .untweakedBolos s1 s2 sid [r2Inp] [r2Inp] true true _ hR2
  have hR1Again :
      executeRound1Pass nonVacuousToyCrypto .untweakedBolos s2 sid rr2 [task] =
        .ok ([{ inputIndex := 0, pubnonce := pn, participantPk := pk, aggregatePubkey := pk, leafHash := none }], s3) := by
    unfold executeRound1Pass round1ProduceTaskNonce syntheticRandIJ selectNonceAggPk
    simp [s0, s2, s3, sid, rr1, rr2, task, hSidZero, hRr2Zero, hRrNe, MusigSessionStore.bolosDefault,
      bolosMaxMusigSessions, MusigSessionStore.isRandRootConsumed, MusigSessionStore.evictUnconsumed,
      MusigSessionStore.registerRound1, trimToCapacity, distinctTaskCoordinates, maxPubkeysPerMusig,
      hSha, hGen, List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have hR2Again :
      executeRound2Pass nonVacuousToyCrypto .untweakedBolos s3 sid [r2Inp] =
        .ok ([{ inputIndex := 0, signature := threeByte32, participantPk := pk, aggregatePubkey := pk, leafHash := none }], s4) := by
    unfold executeRound2Pass MusigSessionStore.consumeRound2 round2SignTask syntheticRandIJ selectNonceAggPk
    simp [s0, s3, s4, sid, rr1, rr2, r2Inp, task, MusigSessionStore.bolosDefault, hSidRefl, hRrNe,
      MusigSessionStore.isRandRootConsumed, distinctTaskCoordinates,
      maxPubkeysPerMusig, hSha, hAgg, hGen, hSign,
      List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]
  exact ⟨sid, rr1, rr2, task, r2Inp, _, s1, _, s2, _, s3, _, s4,
    hR1, rfl, hR2, rfl, hReplay, hR1Again, hR2Again, rfl⟩

/-- **Multi-Internal-Key Witness (`M-04`)**:
    Two Round-1 signing tasks sharing `(inputIndex, placeholderIndex) = (0, 0)` with distinct
    participant `internalPk`s (`musig(@0, @1)` on Vanadium) pass `distinctTaskCoordinates` and
    produce two distinct Round-1 output entries. -/
theorem nonvacuous_multi_internal_key_same_placeholder_round1_ok :
    let pk1 := toyCompressedPk
    let pk2 := toyCompressedPk2
    let tA : MusigSignTask := {
      inputIndex := 0, placeholderIndex := 0, internalPk := pk1,
      untweakedAggPk := pk1, tweakedAggPk := pk1, sortedPubkeys := [pk1, pk2],
      tweaks := [], leafHash := none
    }
    let tB : MusigSignTask := { tA with internalPk := pk2 }
    ∃ outs s1,
      executeRound1Pass nonVacuousToyCrypto .tweakedVanadium MusigSessionStore.vanadiumDefault
        sidByte32 rrByte32 [tA, tB] = .ok (outs, s1) ∧ outs.length = 2 := by
  intro pk1 pk2 tA tB
  have hSidZero : sidByte32.isAllZeros = false := by decide
  have hRrZero : rrByte32.isAllZeros = false := by decide
  have hPkNe : pk1 ≠ pk2 := by decide
  have hOneMod : parseScalarModN oneByte32 = 1 := by
    unfold parseScalarModN
    rw [bytes32ToNat_oneByte32]
    decide
  have hHash : ∀ tag msg, nonVacuousToyCrypto.taggedHash tag msg = oneByte32 := fun _ _ => rfl
  have hSha : ∀ msg, nonVacuousToyCrypto.sha256 msg = oneByte32 := fun _ => rfl
  have hComp : ∀ p, nonVacuousToyCrypto.compress p = toyCompressedPk := fun _ => rfl
  have hMul1 : ∀ p, nonVacuousToyCrypto.pointMul 1 p = p := by
    intro p
    show (if 1 % secp256k1Order == 0 then CurvePoint.infinity else p) = p
    have h1 : (1 % secp256k1Order == 0) = false := by decide
    rw [h1]
    rfl
  have hGen1 : nonceGen nonVacuousToyCrypto oneByte32 pk1 pk1.xOnly =
      .ok ({ k1 := 1, k2 := 1, pk := pk1 }, PubNonce.ofParts pk1 pk1) := by
    unfold nonceGen nonceHash
    simp [hHash, hOneMod, hMul1, hComp, pk1]
  have hGen2 : nonceGen nonVacuousToyCrypto oneByte32 pk2 pk1.xOnly =
      .ok ({ k1 := 1, k2 := 1, pk := pk2 }, PubNonce.ofParts pk1 pk1) := by
    unfold nonceGen nonceHash
    simp [hHash, hOneMod, hMul1, hComp, pk1, pk2]
  let pn := PubNonce.ofParts pk1 pk1
  let out1 : MusigRound1Output :=
    { inputIndex := 0, pubnonce := pn, participantPk := pk1, aggregatePubkey := pk1, leafHash := none }
  let out2 : MusigRound1Output :=
    { inputIndex := 0, pubnonce := pn, participantPk := pk2, aggregatePubkey := pk1, leafHash := none }
  let s1 : MusigSessionStore :=
    { MusigSessionStore.vanadiumDefault with activeEntries := [(sidByte32, rrByte32)] }
  refine ⟨[out1, out2], s1, ?_, rfl⟩
  unfold executeRound1Pass round1ProduceTaskNonce syntheticRandIJ selectNonceAggPk
  simp [tA, tB, out1, out2, pn, s1, hSidZero, hRrZero, hPkNe, MusigSessionStore.vanadiumDefault,
    vanadiumMaxMusigSessions, MusigSessionStore.isRandRootConsumed,
    MusigSessionStore.evictUnconsumed, MusigSessionStore.registerRound1,
    trimToCapacity, distinctTaskCoordinates, maxPubkeysPerMusig,
    hSha, hGen1, hGen2, List.mapM, List.mapM.loop, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- **Non-Vacuity Witness for `deriveMusigPerInputInfo` (`M-04`)**:
    Keypath derivation produces 3 tweaks (2 BIP-32 unhardened + 1 x-only BIP-341 `TapTweak`),
    while tapscript derivation produces 2 tweaks and preserves `leafHash`. -/
theorem nonvacuous_deriveMusigPerInputInfo_keypath_and_tapscript :
    ∃ infoKey infoScript,
      deriveMusigPerInputInfo nonVacuousToyCrypto [toyCompressedPk] 0 1 false 0 (.keypath none) = .ok infoKey ∧
      infoKey.tweaks.length = 3 ∧
      deriveMusigPerInputInfo nonVacuousToyCrypto [toyCompressedPk] 0 1 true 5 (.tapscript oneByte32) = .ok infoScript ∧
      infoScript.tweaks.length = 2 ∧
      infoScript.leafHash = some oneByte32 := by
  have hStrict : parseScalarStrict oneByte32 = some 1 := by
    unfold parseScalarStrict
    rw [bytes32ToNat_oneByte32]
    decide
  have hOneMod : parseScalarModN oneByte32 = 1 := by
    unfold parseScalarModN
    rw [bytes32ToNat_oneByte32]
    decide
  have hHash : ∀ tag msg, nonVacuousToyCrypto.taggedHash tag msg = oneByte32 := fun _ _ => rfl
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
  have hCkd : ∀ pk cc idx, nonVacuousToyCrypto.ckdPubUnhardened pk cc idx = some (pk, cc, oneByte32) :=
    fun _ _ _ => rfl
  have hStep0 : ¬ (bip32HardenedBit ≤ (0 : UInt32)) := by decide
  have hStep1 : ¬ (bip32HardenedBit ≤ (1 : UInt32)) := by decide
  have hStep5 : ¬ (bip32HardenedBit ≤ (5 : UInt32)) := by decide
  let tw : MusigTweak := { scalar := oneByte32, isXOnly := false }
  let twX : MusigTweak := { scalar := oneByte32, isXOnly := true }
  let infoK : MusigPerInputInfo := {
    sortedPubkeys := [toyCompressedPk]
    untweakedAggPk := toyCompressedPk
    preTapTweakAggPk := toyCompressedPk
    tweakedAggPk := toyCompressedPk
    tweaks := [tw, tw, twX]
    leafHash := none
  }
  let infoS : MusigPerInputInfo := {
    sortedPubkeys := [toyCompressedPk]
    untweakedAggPk := toyCompressedPk
    preTapTweakAggPk := toyCompressedPk
    tweakedAggPk := toyCompressedPk
    tweaks := [tw, tw]
    leafHash := some oneByte32
  }
  refine ⟨infoK, infoS, ?_, rfl, ?_, rfl, rfl⟩
  · unfold deriveMusigPerInputInfo keyAgg applyTweak
    simp [infoK, tw, twX, keySort, insertPubKey, secondUniqueKey, keyAggLoop, cpoint,
      keyAggCoeffInternal, maxPubkeysPerMusig, hStep0, hDecomp, hHash, hOneMod, hMul1,
      hAddAff, hAddAff2, hComp, hCkd, hStrict, hEven, Bind.bind, Except.bind]
  · unfold deriveMusigPerInputInfo keyAgg
    simp [infoS, tw, keySort, insertPubKey, secondUniqueKey, keyAggLoop, cpoint,
      keyAggCoeffInternal, maxPubkeysPerMusig, hStep1, hStep5, hDecomp, hHash, hOneMod,
      hMul1, hAddAff, hComp, hCkd, Bind.bind, Except.bind]

end Spec.Musig2

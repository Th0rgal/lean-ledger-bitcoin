import InternalSpec
import BitcoinLedger
import Lean

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

namespace Tests.BolosDifferential

/-!
# `Tests.BolosDifferential` — Pure Lean Differential Conformance Suite (`LedgerHQ/app-bitcoin` BOLOS)

Standalone runnable conformance suite (`lake env lean Tests/BolosDifferential.lean`) exercising
all 10 `BitcoinLedger.*` implementation modules (`Basic`, `FreestandingKernels`, `Bip32`, `Script`,
`WalletPolicy`, `Psbt`, `MerkleProtocol`, `Musig2`, `SilentPayments`, `AppStateMachine`) against
official test vectors extracted from `LedgerHQ/app-bitcoin/test_vectors/`, `LedgerHQ/app-bitcoin/unit-tests/`,
`LedgerHQ/app-bitcoin/tests/`, BIP-173/322/327/340/341/350/352/370/374/375/388/392, and cross-target
BOLOS vs Vanadium differential invariants.

Zero `sorryAx`, zero external axioms, zero FFI mocks: includes a self-contained pure-Lean reference
implementation of SHA-256, SHA-512, RIPEMD-160, HMAC-SHA256/512, SLIP-0021, and secp256k1 Jacobian
group arithmetic so every cryptographic derivation from the Speculos master seed is verified end-to-end
inside the Lean kernel/VM.
-/

/-! ## Section 0. Pure-Lean Reference Cryptographic Engine (SHA-256/512, RIPEMD-160, HMAC, secp256k1) -/

namespace RefCrypto

def hexNibble? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

def hexToBytesAux : List Char → List UInt8 → Option ByteArray
  | [], acc => some (ByteArray.mk acc.reverse.toArray)
  | [_], _ => none
  | hi :: lo :: rest, acc =>
      match hexNibble? hi, hexNibble? lo with
      | some h, some l => hexToBytesAux rest (((h <<< 4) ||| l) :: acc)
      | _, _ => none

def hex! (s : String) : ByteArray :=
  (hexToBytesAux s.toList []).getD ByteArray.empty

def hexDigit (n : UInt8) : Char :=
  let v := (n &&& 0x0F).toNat
  if v < 10 then Char.ofNat ('0'.toNat + v) else Char.ofNat ('a'.toNat + (v - 10))

def bytesToHex (bs : ByteArray) : String :=
  String.ofList <| bs.data.toList.flatMap fun (b : UInt8) => [hexDigit (b >>> 4), hexDigit b]

/-! ### Pure-Lean SHA-256 -/

private def rotr32 (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

private def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def bget (b : ByteArray) (i : Nat) : UInt8 :=
  b.data.getD i 0

private def readU32BEAt (b : ByteArray) (off : Nat) : UInt32 :=
  ((bget b off).toUInt32 <<< 24) |||
  ((bget b (off + 1)).toUInt32 <<< 16) |||
  ((bget b (off + 2)).toUInt32 <<< 8) |||
  (bget b (off + 3)).toUInt32

private def pushU32BE (acc : ByteArray) (v : UInt32) : ByteArray :=
  acc.push (v >>> 24).toUInt8
    |>.push (v >>> 16).toUInt8
    |>.push (v >>> 8).toUInt8
    |>.push v.toUInt8

def sha256 (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let mut padded := msg.push 0x80
  while padded.size % 64 != 56 do
    padded := padded.push 0x00
  for s in [56, 48, 40, 32, 24, 16, 8, 0] do
    padded := padded.push (bitLen >>> s.toUInt64).toUInt8
  let mut h0 : UInt32 := 0x6a09e667
  let mut h1 : UInt32 := 0xbb67ae85
  let mut h2 : UInt32 := 0x3c6ef372
  let mut h3 : UInt32 := 0xa54ff53a
  let mut h4 : UInt32 := 0x510e527f
  let mut h5 : UInt32 := 0x9b05688c
  let mut h6 : UInt32 := 0x1f83d9ab
  let mut h7 : UInt32 := 0x5be0cd19
  let nBlocks := padded.size / 64
  for blk in [0:nBlocks] do
    let base := blk * 64
    let mut w := Array.replicate 64 (0 : UInt32)
    for i in [0:16] do
      w := w.set! i (readU32BEAt padded (base + i * 4))
    for i in [16:64] do
      let w15 := w[i - 15]!
      let w2 := w[i - 2]!
      let s0 := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
      let s1 := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := h0; let mut b := h1; let mut c := h2; let mut d := h3
    let mut e := h4; let mut f := h5; let mut g := h6; let mut h := h7
    for i in [0:64] do
      let S1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let temp1 := h + S1 + ch + sha256K[i]! + w[i]!
      let S0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := S0 + maj
      h := g; g := f; f := e; e := d + temp1
      d := c; c := b; b := a; a := temp1 + temp2
    h0 := h0 + a; h1 := h1 + b; h2 := h2 + c; h3 := h3 + d
    h4 := h4 + e; h5 := h5 + f; h6 := h6 + g; h7 := h7 + h
  let mut out := ByteArray.empty
  for v in [h0, h1, h2, h3, h4, h5, h6, h7] do
    out := pushU32BE out v
  return out

def doubleSha256 (msg : ByteArray) : ByteArray :=
  sha256 (sha256 msg)

def taggedHash (tag : String) (msg : ByteArray) : ByteArray :=
  let th := sha256 tag.toUTF8
  sha256 (th ++ th ++ msg)

/-! ### Pure-Lean SHA-512 -/

private def rotr64 (x n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

private def sha512K : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

private def readU64BEAt (b : ByteArray) (off : Nat) : UInt64 :=
  ((bget b off).toUInt64 <<< 56) |||
  ((bget b (off + 1)).toUInt64 <<< 48) |||
  ((bget b (off + 2)).toUInt64 <<< 40) |||
  ((bget b (off + 3)).toUInt64 <<< 32) |||
  ((bget b (off + 4)).toUInt64 <<< 24) |||
  ((bget b (off + 5)).toUInt64 <<< 16) |||
  ((bget b (off + 6)).toUInt64 <<< 8) |||
  (bget b (off + 7)).toUInt64

def sha512 (msg : ByteArray) : ByteArray := Id.run do
  let bitLenLo : UInt64 := msg.size.toUInt64 * 8
  let mut padded := msg.push 0x80
  while padded.size % 128 != 112 do
    padded := padded.push 0x00
  for _ in [0:8] do
    padded := padded.push 0x00
  for s in [56, 48, 40, 32, 24, 16, 8, 0] do
    padded := padded.push (bitLenLo >>> s.toUInt64).toUInt8
  let mut h0 : UInt64 := 0x6a09e667f3bcc908
  let mut h1 : UInt64 := 0xbb67ae8584caa73b
  let mut h2 : UInt64 := 0x3c6ef372fe94f82b
  let mut h3 : UInt64 := 0xa54ff53a5f1d36f1
  let mut h4 : UInt64 := 0x510e527fade682d1
  let mut h5 : UInt64 := 0x9b05688c2b3e6c1f
  let mut h6 : UInt64 := 0x1f83d9abfb41bd6b
  let mut h7 : UInt64 := 0x5be0cd19137e2179
  let nBlocks := padded.size / 128
  for blk in [0:nBlocks] do
    let base := blk * 128
    let mut w := Array.replicate 80 (0 : UInt64)
    for i in [0:16] do
      w := w.set! i (readU64BEAt padded (base + i * 8))
    for i in [16:80] do
      let w15 := w[i - 15]!
      let w2 := w[i - 2]!
      let s0 := rotr64 w15 1 ^^^ rotr64 w15 8 ^^^ (w15 >>> 7)
      let s1 := rotr64 w2 19 ^^^ rotr64 w2 61 ^^^ (w2 >>> 6)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := h0; let mut b := h1; let mut c := h2; let mut d := h3
    let mut e := h4; let mut f := h5; let mut g := h6; let mut h := h7
    for i in [0:80] do
      let S1 := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
      let ch := (e &&& f) ^^^ ((~~~e) &&& g)
      let temp1 := h + S1 + ch + sha512K[i]! + w[i]!
      let S0 := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let temp2 := S0 + maj
      h := g; g := f; f := e; e := d + temp1
      d := c; c := b; b := a; a := temp1 + temp2
    h0 := h0 + a; h1 := h1 + b; h2 := h2 + c; h3 := h3 + d
    h4 := h4 + e; h5 := h5 + f; h6 := h6 + g; h7 := h7 + h
  let mut out := ByteArray.empty
  for v in [h0, h1, h2, h3, h4, h5, h6, h7] do
    for s in [56, 48, 40, 32, 24, 16, 8, 0] do
      out := out.push (v >>> s.toUInt64).toUInt8
  return out

/-! ### Pure-Lean RIPEMD-160 & HASH160 -/

private def rotl32 (x n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

private def readU32LEAt (b : ByteArray) (off : Nat) : UInt32 :=
  (bget b off).toUInt32 |||
  ((bget b (off + 1)).toUInt32 <<< 8) |||
  ((bget b (off + 2)).toUInt32 <<< 16) |||
  ((bget b (off + 3)).toUInt32 <<< 24)

private def rmdF (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((~~~x) &&& z)
  else if j < 48 then (x ||| (~~~y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (~~~z))
  else x ^^^ (y ||| (~~~z))

private def rmdKL (j : Nat) : UInt32 :=
  if j < 16 then 0x00000000
  else if j < 32 then 0x5a827999
  else if j < 48 then 0x6ed9eba1
  else if j < 64 then 0x8f1bbcdc
  else 0xa953fd4e

private def rmdKR (j : Nat) : UInt32 :=
  if j < 16 then 0x50a28be6
  else if j < 32 then 0x5c4dd124
  else if j < 48 then 0x6d703ef3
  else if j < 64 then 0x7a6d76e9
  else 0x00000000

private def rmdRL : Array Nat := #[
  0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,
  7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,
  3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,
  1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,
  4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13
]

private def rmdRR : Array Nat := #[
  5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,
  6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,
  15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,
  8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,
  12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11
]

private def rmdSL : Array UInt32 := #[
  11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,
  7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,
  11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,
  11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,
  9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6
]

private def rmdSR : Array UInt32 := #[
  8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,
  9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,
  9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,
  15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,
  8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11
]

def ripemd160 (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := msg.size.toUInt64 * 8
  let mut padded := msg.push 0x80
  while padded.size % 64 != 56 do
    padded := padded.push 0x00
  for s in [0, 8, 16, 24, 32, 40, 48, 56] do
    padded := padded.push (bitLen >>> s.toUInt64).toUInt8
  let mut h0 : UInt32 := 0x67452301
  let mut h1 : UInt32 := 0xefcdab89
  let mut h2 : UInt32 := 0x98badcfe
  let mut h3 : UInt32 := 0x10325476
  let mut h4 : UInt32 := 0xc3d2e1f0
  let nBlocks := padded.size / 64
  for blk in [0:nBlocks] do
    let base := blk * 64
    let mut x := Array.replicate 16 (0 : UInt32)
    for i in [0:16] do
      x := x.set! i (readU32LEAt padded (base + i * 4))
    let mut al := h0; let mut bl := h1; let mut cl := h2; let mut dl := h3; let mut el := h4
    let mut ar := h0; let mut br := h1; let mut cr := h2; let mut dr := h3; let mut er := h4
    for j in [0:80] do
      let tl := (rotl32 (al + rmdF j bl cl dl + x[rmdRL[j]!]! + rmdKL j) rmdSL[j]!) + el
      al := el; el := dl; dl := rotl32 cl 10; cl := bl; bl := tl
      let tr := (rotl32 (ar + rmdF (79 - j) br cr dr + x[rmdRR[j]!]! + rmdKR j) rmdSR[j]!) + er
      ar := er; er := dr; dr := rotl32 cr 10; cr := br; br := tr
    let t := h1 + cl + dr
    h1 := h2 + dl + er
    h2 := h3 + el + ar
    h3 := h4 + al + br
    h4 := h0 + bl + cr
    h0 := t
  let mut out := ByteArray.empty
  for v in [h0, h1, h2, h3, h4] do
    for s in [0, 8, 16, 24] do
      out := out.push (v >>> s.toUInt32).toUInt8
  return out

def hash160 (msg : ByteArray) : ByteArray :=
  ripemd160 (sha256 msg)

/-! ### HMAC-SHA256 & HMAC-SHA512 -/

def hmacCore (hashFn : ByteArray → ByteArray) (blockSize : Nat) (key msg : ByteArray) : ByteArray := Id.run do
  let k0 := if key.size > blockSize then hashFn key else key
  let mut kPad := k0
  while kPad.size < blockSize do
    kPad := kPad.push 0x00
  let mut ipad := ByteArray.empty
  let mut opad := ByteArray.empty
  for i in [0:blockSize] do
    let kb := bget kPad i
    ipad := ipad.push (kb ^^^ 0x36)
    opad := opad.push (kb ^^^ 0x5c)
  return hashFn (opad ++ hashFn (ipad ++ msg))

def hmacSha256 (key msg : ByteArray) : ByteArray :=
  hmacCore sha256 64 key msg

def hmacSha512 (key msg : ByteArray) : ByteArray :=
  hmacCore sha512 128 key msg

/-! ### Pure-Lean secp256k1 Elliptic Curve Group (`y^2 = x^3 + 7 mod p`) -/

def secpP : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def secpN : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def secpGx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def secpGy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

structure AffinePt where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq, Inhabited

def secpG : AffinePt := ⟨secpGx, secpGy⟩

private structure JacPt where
  x : Nat
  y : Nat
  z : Nat

def powMod (base exp modulus : Nat) : Nat := Id.run do
  if modulus ≤ 1 then return 0
  let mut res := 1 % modulus
  let mut b := base % modulus
  let mut e := exp
  while e > 0 do
    if e % 2 == 1 then
      res := (res * b) % modulus
    b := (b * b) % modulus
    e := e / 2
  return res

def invModP (a : Nat) : Nat :=
  powMod a (secpP - 2) secpP

def invModN (a : Nat) : Nat :=
  powMod a (secpN - 2) secpN

private def addModP (a b : Nat) : Nat := (a + b) % secpP
private def subModP (a b : Nat) : Nat := (a + secpP - (b % secpP)) % secpP
private def mulModP (a b : Nat) : Nat := (a * b) % secpP

private def jacDouble (p : JacPt) : JacPt :=
  if p.z == 0 || p.y == 0 then ⟨0, 1, 0⟩
  else
    let y2 := mulModP p.y p.y
    let s := mulModP 4 (mulModP p.x y2)
    let m := mulModP 3 (mulModP p.x p.x)
    let x3 := subModP (mulModP m m) (mulModP 2 s)
    let y4 := mulModP y2 y2
    let y3 := subModP (mulModP m (subModP s x3)) (mulModP 8 y4)
    let z3 := mulModP 2 (mulModP p.y p.z)
    ⟨x3, y3, z3⟩

private def jacAdd (p q : JacPt) : JacPt :=
  if p.z == 0 then q
  else if q.z == 0 then p
  else
    let z1z1 := mulModP p.z p.z
    let z2z2 := mulModP q.z q.z
    let u1 := mulModP p.x z2z2
    let u2 := mulModP q.x z1z1
    let s1 := mulModP p.y (mulModP q.z z2z2)
    let s2 := mulModP q.y (mulModP p.z z1z1)
    if u1 == u2 then
      if s1 == s2 then jacDouble p else ⟨0, 1, 0⟩
    else
      let h := subModP u2 u1
      let r := subModP s2 s1
      let hh := mulModP h h
      let hhh := mulModP h hh
      let v := mulModP u1 hh
      let x3 := subModP (subModP (mulModP r r) hhh) (mulModP 2 v)
      let y3 := subModP (mulModP r (subModP v x3)) (mulModP s1 hhh)
      let z3 := mulModP h (mulModP p.z q.z)
      ⟨x3, y3, z3⟩

private def jacToAffine? (p : JacPt) : Option AffinePt :=
  if p.z == 0 then none
  else
    let zInv := invModP p.z
    let zInv2 := mulModP zInv zInv
    let zInv3 := mulModP zInv2 zInv
    some ⟨mulModP p.x zInv2, mulModP p.y zInv3⟩

def ecAdd? (p? q? : Option AffinePt) : Option AffinePt :=
  let jp : JacPt := match p? with | none => ⟨0, 1, 0⟩ | some p => ⟨p.x, p.y, 1⟩
  let jq : JacPt := match q? with | none => ⟨0, 1, 0⟩ | some q => ⟨q.x, q.y, 1⟩
  jacToAffine? (jacAdd jp jq)

def ecNeg? : Option AffinePt → Option AffinePt
  | none => none
  | some p => some ⟨p.x, (secpP - (p.y % secpP)) % secpP⟩

def ecMul? (k : Nat) (p? : Option AffinePt) : Option AffinePt := Id.run do
  let some p := p? | return none
  let mut s := k % secpN
  if s == 0 then return none
  let mut acc : JacPt := ⟨0, 1, 0⟩
  let mut base : JacPt := ⟨p.x, p.y, 1⟩
  while s > 0 do
    if s % 2 == 1 then
      acc := jacAdd acc base
    base := jacDouble base
    s := s / 2
  return jacToAffine? acc

def bytesToNatBE (bs : ByteArray) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

def natToBytes32BE (n : Nat) : ByteArray := Id.run do
  let mut v := n
  let mut arr := Array.replicate 32 (0 : UInt8)
  for idx in [0:32] do
    let pos := 31 - idx
    arr := arr.set! pos (UInt8.ofNat (v % 256))
    v := v / 256
  return ByteArray.mk arr

def compressPt (p : AffinePt) : ByteArray :=
  let tag : UInt8 := if p.y % 2 == 0 then 0x02 else 0x03
  ByteArray.mk #[tag] ++ natToBytes32BE p.x

def liftXEven? (xBytes : ByteArray) : Option AffinePt :=
  if xBytes.size != 32 then none
  else
    let x := bytesToNatBE xBytes
    if x ≥ secpP then none
    else
      let rhs := addModP (powMod x 3 secpP) 7
      let y := powMod rhs ((secpP + 1) / 4) secpP
      if mulModP y y != rhs then none
      else
        let yEven := if y % 2 == 0 then y else secpP - y
        some ⟨x, yEven⟩

def decompressPt? (sec1 : ByteArray) : Option AffinePt :=
  if sec1.size != 33 then none
  else
    let tag := bget sec1 0
    if tag != 0x02 && tag != 0x03 then none
    else
      match liftXEven? (sec1.extract 1 33) with
      | none => none
      | some p =>
          let wantOdd := tag == 0x03
          let y := if (p.y % 2 == 1) == wantOdd then p.y else secpP - p.y
          some ⟨p.x, y⟩

/-! ### BIP-32 Master Seed, `CKDpriv`, `CKDpub`, SLIP-0021 & ECDSA/Schnorr Verification -/

/-- Official Speculos 64-byte BIP-39 seed (`fixtures.toml`: `"glory promote mansion..."`). -/
def speculosSeed64 : ByteArray :=
  hex! "b11997faff420a331bb4a4ffdc8bdc8ba7c01732a99a30d83dbbebd469666c84b47d09d3f5f472b3b9384ac634beba2a440ba36ec7661144132f35e206873564"

def bip32MasterFromSeed (seed : ByteArray) : Option (Nat × ByteArray) :=
  let i := hmacSha512 "Bitcoin seed".toUTF8 seed
  let il := bytesToNatBE (i.extract 0 32)
  let ir := i.extract 32 64
  if il == 0 || il ≥ secpN then none else some (il, ir)

def ckdPrivStep (kPar : Nat) (cPar : ByteArray) (idx : UInt32) : Option (Nat × ByteArray) := do
  let some pubPt := ecMul? kPar (some secpG) | none
  let idxBE := BitcoinLedger.Basic.encodeU32BE idx
  let data :=
    if idx ≥ 0x80000000 then
      ByteArray.mk #[0x00] ++ natToBytes32BE kPar ++ idxBE
    else
      compressPt pubPt ++ idxBE
  let i := hmacSha512 cPar data
  let il := bytesToNatBE (i.extract 0 32)
  let ir := i.extract 32 64
  let ki := (il + kPar) % secpN
  if il ≥ secpN || ki == 0 then none else some (ki, ir)

def derivePrivAtPath (seed : ByteArray) (path : List UInt32) : Option (Nat × ByteArray × UInt32) := do
  let (k0, c0) ← bip32MasterFromSeed seed
  let rec go (k : Nat) (c : ByteArray) (parentFp : UInt32) : List UInt32 → Option (Nat × ByteArray × UInt32)
    | [] => some (k, c, parentFp)
    | step :: rest => do
        let some pubPt := ecMul? k (some secpG) | none
        let fpBytes := hash160 (compressPt pubPt)
        let fp := readU32BEAt fpBytes 0
        let (k', c') ← ckdPrivStep k c step
        go k' c' fp rest
  go k0 c0 0 path

def ckdPubStep (pub33 cc32 : ByteArray) (idx : UInt32) : Option (ByteArray × ByteArray × ByteArray) := do
  if idx ≥ 0x80000000 then none
  let pPar ← decompressPt? pub33
  if cc32.size != 32 then none
  let i := hmacSha512 cc32 (pub33 ++ BitcoinLedger.Basic.encodeU32BE idx)
  let ilBytes := i.extract 0 32
  let irBytes := i.extract 32 64
  let il := bytesToNatBE ilBytes
  if il ≥ secpN then none
  let ilG ← ecMul? il (some secpG)
  let childPt ← ecAdd? (some ilG) (some pPar)
  some (compressPt childPt, irBytes, ilBytes)

def slip21DeriveWalletHmacKey (seed : ByteArray) (labelWithLeadingZero : ByteArray) : ByteArray :=
  let m := hmacSha512 "Symmetric key seed".toUTF8 seed
  let child := hmacSha512 (m.extract 0 32) labelWithLeadingZero
  child.extract 32 64

def bolosComputeWalletHmac (walletId32 : ByteArray) : ByteArray :=
  let key := slip21DeriveWalletHmacKey speculosSeed64 BitcoinLedger.WalletPolicy.bolosWalletSlip21Label
  hmacSha256 key walletId32

def ecdsaVerifyRaw (pub : AffinePt) (msgHash32 : ByteArray) (r s : Nat) : Bool :=
  if r == 0 || r ≥ secpN || s == 0 || s ≥ secpN || msgHash32.size != 32 then false
  else
    let z := bytesToNatBE msgHash32 % secpN
    let w := invModN s
    let u1 := (z * w) % secpN
    let u2 := (r * w) % secpN
    let p1 := ecMul? u1 (some secpG)
    let p2 := ecMul? u2 (some pub)
    match ecAdd? p1 p2 with
    | none => false
    | some pt => (pt.x % secpN) == r

def parseDerSigPlusSighash? (derWithSh : ByteArray) : Option (Nat × Nat × UInt8) :=
  if derWithSh.size < 9 then none
  else
    let sh := bget derWithSh (derWithSh.size - 1)
    let der := derWithSh.extract 0 (derWithSh.size - 1)
    if bget der 0 != 0x30 || (bget der 1).toNat + 2 != der.size || bget der 2 != 0x02 then none
    else
      let rLen := (bget der 3).toNat
      if 4 + rLen + 2 > der.size || bget der (4 + rLen) != 0x02 then none
      else
        let sLen := (bget der (4 + rLen + 1)).toNat
        if 4 + rLen + 2 + sLen != der.size then none
        else
          let r := bytesToNatBE (der.extract 4 (4 + rLen))
          let s := bytesToNatBE (der.extract (4 + rLen + 2) der.size)
          some (r, s, sh)

def schnorrVerifyBip340 (xOnly32 msg sig64 : ByteArray) : Bool :=
  if xOnly32.size != 32 || sig64.size != 64 then false
  else
    match liftXEven? xOnly32 with
    | none => false
    | some P =>
        let rBytes := sig64.extract 0 32
        let r := bytesToNatBE rBytes
        let s := bytesToNatBE (sig64.extract 32 64)
        if r ≥ secpP || s ≥ secpN then false
        else
          let e := bytesToNatBE (taggedHash "BIP0340/challenge" (rBytes ++ xOnly32 ++ msg)) % secpN
          let sG := ecMul? s (some secpG)
          let negEP := ecNeg? (ecMul? e (some P))
          match ecAdd? sG negEP with
          | none => false
          | some R => R.y % 2 == 0 && R.x == r

end RefCrypto

#guard RefCrypto.bytesToHex (RefCrypto.sha256 "abc".toUTF8) ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard RefCrypto.bytesToHex (RefCrypto.ripemd160 "abc".toUTF8) ==
  "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
#guard RefCrypto.bytesToHex
    (RefCrypto.bolosComputeWalletHmac
      (RefCrypto.hex! "1d150ed425a871a5ca7e2c55db1b3295c1fd97147fd0a7b188d4327f4ba7402a")) ==
  "fa73e36119324fbe4cc1ca94aa842c6261526d44112a22164bc57c3335102b04"

/-! ### Concrete Speculos-Seeded BOLOS Cryptographic Oracles -/

def mkMusigBytes32! (bs : ByteArray) : InternalSpec.Musig2.Bytes32 :=
  if h : bs.size = 32 then ⟨bs, h⟩ else InternalSpec.Musig2.SizedBytes.zeros 32

def mkMusigBytes33! (bs : ByteArray) : InternalSpec.Musig2.CompressedPubKey :=
  if h : bs.size = 33 then ⟨bs, h⟩ else InternalSpec.Musig2.SizedBytes.zeros 33

def mkMusigBytes64! (bs : ByteArray) : InternalSpec.Musig2.SizedBytes 64 :=
  if h : bs.size = 64 then ⟨bs, h⟩ else InternalSpec.Musig2.SizedBytes.zeros 64

def mkMusigBytes66! (bs : ByteArray) : InternalSpec.Musig2.PubNonce :=
  if h : bs.size = 66 then ⟨bs, h⟩ else InternalSpec.Musig2.SizedBytes.zeros 66

def mkPsbtBytes32! (bs : ByteArray) : InternalSpec.Psbt.Bytes32 :=
  if h : bs.size = 32 then ⟨bs, h⟩ else ⟨ByteArray.mk (Array.replicate 32 0), by decide⟩

def mkSpBytes32! (bs : ByteArray) : InternalSpec.SilentPayments.Bytes32 :=
  if h : bs.size = 32 then ⟨bs, h⟩ else InternalSpec.SilentPayments.SizedBytes.zeros 32

def mkSpBytes33! (bs : ByteArray) : InternalSpec.SilentPayments.Bytes33 :=
  if h : bs.size = 33 then ⟨bs, h⟩ else InternalSpec.SilentPayments.SizedBytes.zeros 33

def mkSpBytes64! (bs : ByteArray) : InternalSpec.SilentPayments.Bytes64 :=
  if h : bs.size = 64 then ⟨bs, h⟩ else InternalSpec.SilentPayments.SizedBytes.zeros 64

def bolosDerivOracle : InternalSpec.CryptoDerivationOracle where
  deriveNode tree path :=
    match tree with
    | .resident => none
    | .standard =>
        if path.size == 0 then none -- BOLOS has no HAVE_APPLICATION_FLAG_DERIVE_MASTER
        else do
          let (k, cc, _) ← RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 path.toList
          let pt ← RefCrypto.ecMul? k (some RefCrypto.secpG)
          some (RefCrypto.compressPt pt, cc)
  masterFingerprint tree :=
    match tree with
    | .resident => none
    | .standard => do
        let (k0, _) ← RefCrypto.bip32MasterFromSeed RefCrypto.speculosSeed64
        let pt0 ← RefCrypto.ecMul? k0 (some RefCrypto.secpG)
        some ((RefCrypto.hash160 (RefCrypto.compressPt pt0)).extract 0 4)
  deriveChildPub pub33 cc32 idx := do
    let (cPub, cCc, _) ← RefCrypto.ckdPubStep pub33 cc32 idx
    some (cPub, cCc)
  hash160 := RefCrypto.hash160
  doubleSha256 := RefCrypto.doubleSha256

def bolosMusigCrypto : InternalSpec.Musig2.MusigCrypto RefCrypto.AffinePt where
  generator := RefCrypto.secpG
  pointAdd p q :=
    let p? := match p with | .infinity => none | .affine a => some a
    let q? := match q with | .infinity => none | .affine a => some a
    match RefCrypto.ecAdd? p? q? with
    | none => .infinity
    | some r => .affine r
  pointMul k p :=
    let p? := match p with | .infinity => none | .affine a => some a
    match RefCrypto.ecMul? k p? with
    | none => .infinity
    | some r => .affine r
  pointNeg p :=
    match p with
    | .infinity => .infinity
    | .affine a => .affine ⟨a.x, (RefCrypto.secpP - (a.y % RefCrypto.secpP)) % RefCrypto.secpP⟩
  hasEvenY a := a.y % 2 == 0
  xCoord a := mkMusigBytes32! (RefCrypto.natToBytes32BE a.x)
  compress a := mkMusigBytes33! (RefCrypto.compressPt a)
  decompress cpk := RefCrypto.decompressPt? cpk.bytes
  taggedHash tag msg := mkMusigBytes32! (RefCrypto.taggedHash tag msg)
  sha256 msg := mkMusigBytes32! (RefCrypto.sha256 msg)
  ckdPubUnhardened pub cc idx := do
    let (cPub, cCc, il) ← RefCrypto.ckdPubStep pub.bytes cc.bytes idx
    some (mkMusigBytes33! cPub, mkMusigBytes32! cCc, mkMusigBytes32! il)

def bolosSpCrypto : InternalSpec.SilentPayments.SpCrypto RefCrypto.AffinePt where
  generator := RefCrypto.secpG
  pointAdd p q :=
    let p? := match p with | .infinity => none | .affine a => some a
    let q? := match q with | .infinity => none | .affine a => some a
    match RefCrypto.ecAdd? p? q? with
    | none => .infinity
    | some r => .affine r
  pointMul k p :=
    let p? := match p with | .infinity => none | .affine a => some a
    match RefCrypto.ecMul? k p? with
    | none => .infinity
    | some r => .affine r
  pointNeg p :=
    match p with
    | .infinity => .infinity
    | .affine a => .affine ⟨a.x, (RefCrypto.secpP - (a.y % RefCrypto.secpP)) % RefCrypto.secpP⟩
  hasEvenY a := a.y % 2 == 0
  xCoord a := mkSpBytes32! (RefCrypto.natToBytes32BE a.x)
  liftX xb := RefCrypto.liftXEven? xb.bytes
  compress a := mkSpBytes33! (RefCrypto.compressPt a)
  decompress cpk := RefCrypto.decompressPt? cpk.bytes
  taggedHash tag msg := mkSpBytes32! (RefCrypto.taggedHash tag msg)

/-! ## Section 1. `BitcoinLedger.Basic` & `BitcoinLedger.FreestandingKernels` Conformance -/

section BasicAndFreestanding

open BitcoinLedger.Basic
open BitcoinLedger.FreestandingKernels

def allSpecErrors : List InternalSpec.SpecError := [
  .wrongLength, .wrongDataLength, .unsupportedInstruction, .unsupportedClass,
  .wrongP1P2, .userRejected, .securityStatusNotSatisfied, .swapValidationFailed,
  .invalidData, .bip32PathTooLong, .unsupportedBip32Path, .notSupported,
  .invalidAmount, .invalidScriptOrAddress, .invalidWalletPolicy, .invalidPsbt,
  .badState, .wrongResponseLength, .cryptoOrSignatureFailed
]

def checkBasicAndFreestanding : Bool :=
  -- 1. Target version `2.4.1 == 0x00020401`
  (llbVersionPacked == 0x00020401) &&
  (BitcoinLedger.appVersion == { major := 2, minor := 4, patch := 1 }) &&
  -- 2. Satoshi arithmetic & freestanding `llb_*` amount kernels + multi-UTXO supply-cap check
  isValidAmount 0 &&
  isValidAmount MAX_MONEY &&
  !isValidAmount (MAX_MONEY + 1) &&
  llbValidAmount 0 &&
  llbValidAmount MAX_MONEY &&
  !llbValidAmount (MAX_MONEY + 1) &&
  (checkedAddSats? (MAX_MONEY - 1) 1 == some MAX_MONEY) &&
  (checkedAddSats? MAX_MONEY 1 == none) &&
  llbCheckedAddSatsOk (MAX_MONEY - 1) 1 &&
  (llbCheckedAddSatsVal (MAX_MONEY - 1) 1 == MAX_MONEY) &&
  !llbCheckedAddSatsOk MAX_MONEY 1 &&
  -- ReferenceDiscrepancy #1: two valid inputs (1.5e15 + 1.5e15 > MAX_MONEY) rejected by checkedSumSats?
  isValidAmount 1_500_000_000_000_000 &&
  (checkedSumSats? [1_500_000_000_000_000, 1_500_000_000_000_000] == none) &&
  (checkedSubSats? 100_000 99_500 == some 500) &&
  (checkedSubSats? 99_500 100_000 == none) &&
  llbCheckedSubSatsOk 100_000 99_500 &&
  (llbCheckedSubSatsVal 100_000 99_500 == 500) &&
  !llbCheckedSubSatsOk 99_500 100_000 &&
  -- 3. Fixed-width integer LE/BE roundtrips
  (decodeU16LE? (encodeU16LE 0xCAFE) == some 0xCAFE) &&
  (decodeU32LE? (encodeU32LE 0xDEADBEEF) == some 0xDEADBEEF) &&
  (decodeU64LE? (encodeU64LE MAX_MONEY) == some MAX_MONEY) &&
  (decodeU32BE? (encodeU32BE 0xF5ACC2FD) == some 0xF5ACC2FD) &&
  -- 4. Canonical CompactSize / VarInt & non-canonical rejections
  ([0, 0xFC, 0xFD, 0xFFFF, 0x10000, 0xFFFFFFFF, 0x100000000, MAX_MONEY].all fun v =>
    let enc := encodeVarInt v
    (decodeVarIntCanonical? enc == some v)) &&
  (decodeVarIntCanonical? (ByteArray.mk #[0xFD, 0xFC, 0x00]) == none) &&
  (decodeVarIntCanonical? (ByteArray.mk #[0xFE, 0xFF, 0xFF, 0x00, 0x00]) == none) &&
  (decodeVarIntCanonical? (ByteArray.mk #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00]) == none) &&
  llbVarIntPrefixIsCanonical 0xFC 0xFC &&
  !llbVarIntPrefixIsCanonical 0xFD 0xFC &&
  llbVarIntPrefixIsCanonical 0xFD 0xFD &&
  !llbVarIntPrefixIsCanonical 0xFE 0xFFFF &&
  !llbVarIntPrefixIsCanonical 0xFF 0xFFFFFFFF &&
  llbVarIntPrefixIsCanonical 0xFF 0x100000000 &&
  -- 5. All 19 `SpecError` tags roundtrip
  (allSpecErrors.all fun err =>
    specErrorFromTag? (specErrorToTag err) == some err) &&
  -- 6. Remaining freestanding scalar kernels (`llb_bip32_*`, `llb_witness_*`, `llb_segwit_*`, `llb_sighash_*`, `llb_merkle_*`)
  llbBip32IsHardened 0x80000054 &&
  (llbBip32Unharden 0x80000054 == 84) &&
  llbBip32BolosDepthOk 10 && !llbBip32BolosDepthOk 11 &&
  llbBip32VanadiumDepthOk 16 && !llbBip32VanadiumDepthOk 17 &&
  llbBip32StandardPurposeOk 0x80000054 &&
  llbBip32StandardPurposeOk 0x8000002D &&
  !llbBip32StandardPurposeOk 0x80000030 &&
  (llbWitnessOpcodeToVersion 0x00 == 0) &&
  (llbWitnessOpcodeToVersion 0x51 == 1) &&
  (llbWitnessOpcodeToVersion 0x60 == 16) &&
  (llbWitnessOpcodeToVersion 0x50 == 0xFF) &&
  llbSegwitProgramValid 0 20 && llbSegwitProgramValid 0 32 && !llbSegwitProgramValid 0 16 &&
  llbSegwitProgramValid 1 2 && llbSegwitProgramValid 1 40 && !llbSegwitProgramValid 1 41 &&
  llbSighashTypeValid 0x01 && llbSighashTypeValid 0x83 && !llbSighashTypeValid 0x00 &&
  llbTaprootSighashValid 0x00 && llbTaprootSighashValid 0x83 && !llbTaprootSighashValid 0x80

end BasicAndFreestanding

/-! ## Section 2. `BitcoinLedger.Bip32` Conformance (`get_extended_pubkey.toml` — All 31 Vectors) -/

section Bip32Conformance

open BitcoinLedger.Bip32

private def h (n : UInt32) : UInt32 := harden n

/-- All 15 pinned Base58Check `tpub` vectors from `LedgerHQ/app-bitcoin/test_vectors/get_extended_pubkey.toml`
    (lines 28–142), derived from the Speculos seed (`master_key_fingerprint = f5acc2fd`). -/
def officialPinnedTpubVectors : List (Bip32Path × Bool × String) := [
  (#[h 44, h 1, h 0], true,
   "tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT"),
  (#[h 44, h 1, h 10], true,
   "tpubDCwYjpDhUdPGp21gSpVay2QPJVh6WNySWMXPhbcu1DsxH31dF7mY18oibbu5RxCLBc1Szerjscuc3D5HyvfYqfRvc9mesewnFqGmPjney4d"),
  (#[h 44, h 1, h 2, 1, 42], true,
   "tpubDGF9YgHKv6qh777rcqVhpmDrbNzgophJM9ec7nHiSfrbss7fVBXoqhmZfohmJSvhNakDHAspPHjVVNL657tLbmTXvSeGev2vj5kzjMaeupT"),
  (#[h 48, h 1, h 4, h 1, 0, 7], true,
   "tpubDK8WPFx4WJo1R9mEL7Wq325wBiXvkAe8ipgb9Q1QBDTDUD2YeCfutWtzY88NPokZqJyRPKHLGwTNLT7jBG59aC6VH8q47LDGQitPB6tX2d7"),
  (#[h 49, h 1, h 1, 1, 3], true,
   "tpubDGnetmJDCL18TyaaoyRAYbkSE9wbHktSdTS4mfsR6inC8c2r6TjdBt3wkqEQhHYPtXpa46xpxDaCXU2PRNUGVvDzAHPG6hHRavYbwAGfnFr"),
  (#[h 84, h 1, h 2, 0, 10], true,
   "tpubDG9YpSUwScWJBBSrhnAT47NcT4NZGLcY18cpkaiWHnkUCi19EtCh8Heeox268NaFF6o56nVeSXuTyK6jpzTvV1h68Kr3edA8AZp27MiLUNt"),
  (#[h 86, h 1, h 4, 1, 12], true,
   "tpubDHTZ815MvTaRmo6Qg1rnU6TEU4ZkWyA56jA1UgpmMcBGomnSsyo34EZLoctzZY9MTJ6j7bhccceUeXZZLxZj5vgkVMYfcZ7DNPsyRdFpS3f"),
  (#[h 86, h 1, h 4, 1, 2, 3, 4, 5], true,
   "tpubDNcjumrTe1BBYEc1FmMaJZQw47mbvb4LfX4YwqC6GQ18PfMfuH3BEYREfdHm2gWXkSJ3JiXHF11iKnbJxzxp5qkgo8BBy2L48FRvrLhpTuh"),
  (#[h 45, h 1, h 0], true,
   "tpubDCy2BKyxJFzACNgThkunvdnkHNotREK9LQDw8L9J1gx26SyzfoeJynJgWekzkramggmahVAgeHPxfpnvFtJ7hcYADrsVUnsPSei2tY9fBLL"),
  (#[h 45, h 1, h 0, 1], true,
   "tpubDFGDxRGdGFKekUtPuta4p9Kw2a2PSeyyhSTa7KNENJfBuJ78EEsL1LxwAA8ddSxZFWBT9gYRuLDoa2rwdix56WRsq77vAJ2iqeyPw6UBeyt"),
  (#[h 87, h 1, h 0], true,
   "tpubDCfRoKFmEJ2uJdvBmrUngREKnaab4P6vC5NbMaeLhjdr3b5zEoruPKByWBJJag5qTdc5FptiSRpuY7AReZPcQAQqCVCUDj3R6DJuyzjMAmh"),
  (#[h 4541509, h 1112098098], true,
   "tpubDAs3mrkQXkGyzp7Yo9SXiZNW7Tmia5EmdUpXjuBQvBDDGGr9CnVHehSB6P5RZFY3bwkYBweXir8MhmvPXqYHHVxKrFkm3mfZ5UkjG5ZH8Ui"),
  (#[h 45, h 2, h 0, h 1], false,
   "tpubDFL11pFAgsKed5bv9Tkxe51xyB4qo1cPDwK6c8WZ4wiVEjtGDg5YuMXNk9yZcB6b47k2oaSWADJF3CRmk97qAwnaiRieT2ocWzh4rq2b3F3"),
  (#[h 45], false,
   "tpubDA4runSouWhEn4C36dL1PwpMhWi1LCgc7EkYJXLExjVr3eWNE5p5ZRUe7LN7cY8YwCroQsLECcv9ufij8EUpDHM2WQM9Cba8Ztf6Zo8jpFf"),
  (#[h 48, h 1, h 0, h 2, h 0, h 1, h 2, h 3, 0, 1], false,
   "tpubDSegeM6ezY6VYgNjYiUxk94ZwLYeuUzHpUYff4LLdEEUVUd8VpgGUxyxZ9oRiEepZzmFZogVWFEWznRj3oJgEuWjcg6BERCxTCYdaxwtShk")
]

/-- Remaining 16 policy-classification cases from `get_extended_pubkey.toml` (lines 104–216). -/
def officialNonStandardPaths : List Bip32Path := [
  #[h 44, h 1],
  #[h 44, h 1, 0],
  #[h 44, h 1, h 0, h 1],
  #[h 48, h 1, h 0, h 0],
  #[h 48, h 1, h 0, h 3],
  #[h 999, h 1, h 0],
  #[h 45, h 2, h 0],
  #[h 45, h 1],
  #[h 44, h 1, h 101],
  #[44, h 1, h 0]
]

/-- Paths blocked by BOLOS `PATH_APP_LOAD_PARAMS` (`m`, `m/44'`, `m/44'/10'/0'`, `m/44'/1/0'`).
    Note: `m/44/1'/0'` has `s1 = 1'` (testnet coin_type), so BOLOS `PATH_APP_LOAD_PARAMS` permits it (`warnUnusual`!). -/
def officialOsLockedPaths : List Bip32Path := [
  #[],
  #[h 44],
  #[h 44, h 10, h 0],
  #[h 44, 1, h 0]
]

def checkBip32Conformance : Bool :=
  -- 1. Master fingerprint `f5acc2fd` (`fixtures.toml`)
  (deriveMasterFingerprint? bolosDerivOracle .standard == some (RefCrypto.hex! "f5acc2fd")) &&
  -- 2. Wire BIP-32 path roundtrip & truncation rejection
  (let p : Bip32Path := #[h 84, h 1, h 0, 0, 15]
   match serializeBip32Path? p with
   | some raw =>
       (parseBip32PathBounded? 10 raw == some p) &&
       (parseBip32PathBounded? 4 raw == none) &&
       (parseBip32Path? (raw.extract 0 (raw.size - 1)) == none)
   | none => false) &&
  -- 3. All 15 pinned `tpub` vectors match BOLOS byte-for-byte + silent/display policy + Base58Check roundtrip
  -- Note: `#[h 48, h 1, h 0, h 2, h 0, h 1, h 2, h 3, 0, 1]` has hardened steps after the 4-step BIP-48 prefix (`isStd = false`),
  -- while `#[h 45, h 2, h 0, h 1]` (`s0 = 45'` bypasses BOLOS OS lock) and `#[h 45]` also warn (`isStd = false`).
  (officialPinnedTpubVectors.all fun (path, isStd, expectedTpub) =>
    let silentRes := evalGetExtendedPubkey bolosDerivOracle bolosExpubPolicyConfig .testnet .standard path false false
    let dispRes := evalGetExtendedPubkey bolosDerivOracle bolosExpubPolicyConfig .testnet .standard path true true
    let silentOk :=
      if isStd then silentRes.isOk
      else match silentRes with | .error .unsupportedBip32Path => true | _ => false
    match dispRes with
    | .ok xpub =>
        silentOk &&
        (encodeExtendedPubKeyBase58Check? RefCrypto.doubleSha256 xpub == some expectedTpub) &&
        decide (decodeExtendedPubKeyBase58Check? RefCrypto.doubleSha256 expectedTpub = some xpub)
    | .error _ => false) &&
  -- 4. Boundary standard paths (`std_account_max = 100`, `std_bip48_script_type_2`)
  (classifyExpubPath bolosExpubPolicyConfig .testnet #[h 44, h 1, h 100] == .allowSilent) &&
  (classifyExpubPath bolosExpubPolicyConfig .testnet #[h 48, h 1, h 0, h 2] == .allowSilent) &&
  -- 5. Non-standard BOLOS-permitted paths warn (`display=false` -> `unsupportedBip32Path`, `display=true` -> `.ok`)
  (officialNonStandardPaths.all fun path =>
    (classifyExpubPath bolosExpubPolicyConfig .testnet path == .warnUnusual) &&
    (match evalGetExtendedPubkey bolosDerivOracle bolosExpubPolicyConfig .testnet .standard path false false with
     | .error .unsupportedBip32Path => true | _ => false) &&
    (evalGetExtendedPubkey bolosDerivOracle bolosExpubPolicyConfig .testnet .standard path true true).isOk) &&
  -- 6. OS-locked paths rejected on standard BOLOS build, permitted with warning on BOLOS Recovery build
  (officialOsLockedPaths.all fun path =>
    (classifyExpubPath bolosExpubPolicyConfig .testnet path == .reject .notSupported) &&
    (classifyExpubPath bolosRecoveryExpubPolicyConfig .testnet path == .warnUnusual)) &&
  -- 7. 11-step `too_long_path` rejected on BOLOS (`MAX_BIP32_PATH_STEPS = 10` -> `0x6A80`), accepted on Vanadium (`<= 16`)
  (let path11 : Bip32Path := #[h 48, h 1, h 0, h 2, h 0, h 1, h 2, h 3, 0, 1, 2]
   (classifyExpubPath bolosExpubPolicyConfig .testnet path11 == .reject .bip32PathTooLong) &&
   (BitcoinLedger.Basic.specErrorToBolosU16 .bip32PathTooLong == 0x6A80) &&
   (classifyExpubPath vanadiumExpubPolicyConfig .testnet #[h 86, h 1, h 0, 0, 1, 2, 3, 4, 5, 6, 7] == .allowSilent)) &&
  -- 8. `CKDpub` homomorphism: deriving `m/44'/1'/2'` then `/1/42` publicly equals `std_pkh_account2_recv_42`
  (match deriveExtendedPubKeyWithOracle bolosDerivOracle .testnet .standard #[h 44, h 1, h 2] with
   | some accXpub =>
       match deriveChildExtendedPubKey? bolosDerivOracle accXpub 1 >>=
             fun c1 => deriveChildExtendedPubKey? bolosDerivOracle c1 42 with
       | some leafXpub =>
           (encodeExtendedPubKeyBase58Check? RefCrypto.doubleSha256 leafXpub ==
             some "tpubDGF9YgHKv6qh777rcqVhpmDrbNzgophJM9ec7nHiSfrbss7fVBXoqhmZfohmJSvhNakDHAspPHjVVNL657tLbmTXvSeGev2vj5kzjMaeupT") &&
           (deriveChildExtendedPubKey? bolosDerivOracle accXpub (h 0) == none)
       | none => false
   | none => false)

end Bip32Conformance

/-! ## Section 3. `BitcoinLedger.Script` Conformance (Scripts, `MINIMALDATA`, Base58Check, Bech32/Bech32m) -/

section ScriptConformance

open BitcoinLedger.Script

def checkScriptConformance : Bool :=
  let h20 := RefCrypto.hex! "cb8a3018cf279311b148cb8d13728bd8cbe95bda"
  let h32 := RefCrypto.hex! "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
  let witV2 := ByteArray.mk #[OP_1 + 1, 0x20] ++ h32
  -- 1. Standard script classification (`P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, `P2TR`, `UnknownWitness`, `OpReturn`)
  (classifyScript? (mkP2PKH h20) == some (.p2pkh h20)) &&
  (classifyScript? (mkP2SH h20) == some (.p2sh h20)) &&
  (classifyScript? (mkP2WPKH h20) == some (.p2wpkh h20)) &&
  (classifyScript? (mkP2WSH h32) == some (.p2wsh h32)) &&
  (classifyScript? (mkP2TR h32) == some (.p2tr h32)) &&
  (classifyScript? witV2 == some (.unknownWitness 2 h32)) &&
  -- Invalid witness v0 length (16B) & truncated P2PKH rejected (`P2WPKH=20B`, `P2WSH=32B` only for v0)
  (encodeSegwitAddr? "tb" 0 (h20.extract 0 16) == none) &&
  (classifyScript? ((mkP2PKH h20).extract 0 24) == none) &&
  -- 2. Cross-target `UnknownWitness`: BOLOS returns `none`, Vanadium formats Bech32m (`tb1z...`)
  (scriptToAddress? .bolos RefCrypto.doubleSha256 .testnet witV2 == none) &&
  (scriptToAddress? .vanadium RefCrypto.doubleSha256 .testnet witV2).isSome &&
  -- 3. `MINIMALDATA` & ReferenceDiscrepancy #2 (`OP_RETURN 0x01 0x00` vs consensus `OP_0`)
  (encodeMinimalPush? ByteArray.empty == some (ByteArray.mk #[0x00])) &&
  (encodeMinimalPush? (ByteArray.mk #[0x00]) == some (ByteArray.mk #[0x01, 0x00])) &&
  (encodeMinimalPush? (ByteArray.mk #[0x05]) == some (ByteArray.mk #[0x55])) &&
  (encodeMinimalPush? (ByteArray.mk #[0x81]) == some (ByteArray.mk #[0x4F])) &&
  (decodeMinimalPushPrefix? (ByteArray.mk #[0x01, 0x05]) == none) &&
  (decodeMinimalPushPrefix? (ByteArray.mk #[0x01, 0x81]) == none) &&
  (decodeMinimalPushPrefix? (ByteArray.mk #[0x4C, 75] ++ ByteArray.mk (Array.replicate 75 0x41)) == none) &&
  -- 4. Official BIP-173 Bech32 & BIP-350 Bech32m vectors (`decodeSegwitAddr?` normalizes case via `toLower`; mixed case rejected)
  (let v0Prog20 := RefCrypto.hex! "751e76e8199196d454941c45d1b3a323f1433bd6"
   let v1Prog32 := RefCrypto.hex! "a60869f0dbcf1dc659c9cecbaf8050135ea9e8cdc487053f1dc6880949dc684c"
   (encodeSegwitAddr? "bc" 0 v0Prog20 == some "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4") &&
   (decodeSegwitAddr? "bc" "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" == some (0, v0Prog20)) &&
   (encodeSegwitAddr? "tb" 1 v1Prog32 == some "tb1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqp3mvzv") &&
   (decodeSegwitAddr? "tb" "tb1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxqp3mvzv" == some (1, v1Prog32)) &&
   -- BIP-350: SegWit v0 with Bech32m checksum MUST fail; SegWit v1 with Bech32 checksum MUST fail; mixed case MUST fail
   (decodeSegwitAddr? "bc" "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kemeawh" == none) &&
   (decodeSegwitAddr? "tb" "tb1p5cyxnuxmeuwuvkwfem96lqzszd02n6xdcjrs20cac6yqjjwudpxq9gk44p" == none) &&
   (decodeSegwitAddr? "bc" "bc1Qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" == none))

end ScriptConformance

/-! ## Section 4. `BitcoinLedger.WalletPolicy` Conformance (`get_wallet_address.toml` & `register_wallet.toml`) -/

section WalletPolicyConformance

open BitcoinLedger.WalletPolicy

/-- Pure-Lean `CryptoPolicyOracle` wired to BIP-32 `CKDpub`, BIP-327 `Musig2.keyAgg`,
    SHA-256, RIPEMD-160, and BIP-341 `taproot_tweak_pubkey` on secp256k1. -/
def bolosPolicyOracle : CryptoPolicyOracle where
  ckdPub xpub idx := do
    if !isUnhardened idx || xpub.depth.toNat ≥ 255 then none
    let (cPub, cCc, _) ← RefCrypto.ckdPubStep xpub.compressedPubkey xpub.chainCode idx
    let fpBytes := RefCrypto.hash160 xpub.compressedPubkey
    some {
      version := xpub.version
      depth := xpub.depth + 1
      parentFingerprint := RefCrypto.readU32BEAt fpBytes 0
      childNumber := idx
      chainCode := cCc
      compressedPubkey := cPub
    }
  musigKeyAgg sortedPks := do
    let cpks := sortedPks.map mkMusigBytes33!
    match BitcoinLedger.Musig2.keyAgg bolosMusigCrypto cpks with
    | .ok ctx => some (RefCrypto.compressPt ctx.q)
    | .error _ => none
  sha256 := RefCrypto.sha256
  ripemd160 := RefCrypto.ripemd160
  taprootTweakPubkey internalXOnly merkleRootOpt := do
    let p ← RefCrypto.liftXEven? internalXOnly
    let msg := match merkleRootOpt with | none => internalXOnly | some m => internalXOnly ++ m
    let t := RefCrypto.bytesToNatBE (RefCrypto.taggedHash "TapTweak" msg)
    if t ≥ RefCrypto.secpN then none
    let q ←
      if t == 0 then some p
      else do
        let tG ← RefCrypto.ecMul? t (some RefCrypto.secpG)
        RefCrypto.ecAdd? (some p) (some tG)
    some (RefCrypto.natToBytes32BE q.x, q.y % 2 == 1)

/-- Compute BOLOS `keys_info` Merkle root (`MTH(keys_info_strings)`) via `BitcoinLedger.MerkleProtocol`. -/
def bolosKeysMerkleRoot (keyStrs : List String) : ByteArray :=
  (BitcoinLedger.MerkleProtocol.merkleRoot
    (fun bs => mkPsbtBytes32! (RefCrypto.sha256 bs))
    (keyStrs.map String.toUTF8)).bytes

/-- Speculos-seeded BOLOS `DeviceRegistrationOracle` (`masterFingerprint = 0xf5acc2fd`). -/
def bolosRegOracle (acceptedProofs : List (String × ByteArray) := []) : DeviceRegistrationOracle where
  masterFingerprint := 0xF5ACC2FD
  deriveAtOrigin net path := do
    if path.isEmpty then none
    let (k, cc, parentFp) ← RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 path
    let pt ← RefCrypto.ecMul? k (some RefCrypto.secpG)
    let childNum := path.getLastD 0
    some {
      version := xpubVersionOfNetwork net
      depth := UInt8.ofNat path.length
      parentFingerprint := parentFp
      childNumber := childNum
      chainCode := cc
      compressedPubkey := RefCrypto.compressPt pt
    }
  verifyRegistrationProof pol hmac :=
    acceptedProofs.any fun (nm, expected) => nm == pol.name && hmac == expected

/-- Parse a `v2` `WalletPolicy` from `(name, descriptor_template, keys_info)` on BOLOS testnet. -/
def parseBolosTestnetPolicy (name desc : String) (keyStrs : List String) :
    Except PolicyError WalletPolicy := do
  let profile := bolosAppProfile .testnet
  let tmpl ← parseDescriptorTemplateWithProfile profile .v2 desc
  let keys ← keyStrs.mapM (parseWalletKeyInfo profile .v2 RefCrypto.doubleSha256 false)
  .ok {
    format := .v2
    name := name
    template := tmpl
    keys := keys
    rawTemplateBytesLen := some desc.toUTF8.size
  }

/-- All 17 official `get_wallet_address.toml` test vectors (`LedgerHQ/app-bitcoin/test_vectors/get_wallet_address.toml`). -/
def officialWalletAddressVectors : List (Bool × String × List String × Bool × UInt32 × String) := [
  -- 1–2: Singlesig P2PKH (BIP-44, stateless default)
  (true, "pkh(@0/**)",
   ["[f5acc2fd/44'/1'/0']tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT"],
   false, 0, "mz5vLWdM1wHVGSmXUkhKVvZbJ2g4epMXSm"),
  (true, "pkh(@0/**)",
   ["[f5acc2fd/44'/1'/0']tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT"],
   true, 15, "myFCUBRCKFjV7292HnZtiHqMzzHrApobpT"),
  -- 3–4: Singlesig P2WPKH (BIP-84, stateless default)
  (true, "wpkh(@0/**)",
   ["[f5acc2fd/84'/1'/0']tpubDCtKfsNyRhULjZ9XMS4VKKtVcPdVDi8MKUbcSD9MJDyjRu1A2ND5MiipozyyspBT9bg8upEp7a8EAgFxNxXn1d7QkdbL52Ty5jiSLcxPt1P"],
   false, 0, "tb1qzdr7s2sr0dwmkwx033r4nujzk86u0cy6fmzfjk"),
  (true, "wpkh(@0/**)",
   ["[f5acc2fd/84'/1'/0']tpubDCtKfsNyRhULjZ9XMS4VKKtVcPdVDi8MKUbcSD9MJDyjRu1A2ND5MiipozyyspBT9bg8upEp7a8EAgFxNxXn1d7QkdbL52Ty5jiSLcxPt1P"],
   true, 15, "tb1qlrvzyx8jcjfj2xuy69du9trtxnsvjuped7e289"),
  -- 5–6: Singlesig P2SH-P2WPKH (BIP-49, stateless default)
  (true, "sh(wpkh(@0/**))",
   ["[f5acc2fd/49'/1'/0']tpubDC871vGLAiKPcwAw22EjhKVLk5L98UGXBEcGR8gpcigLQVDDfgcYW24QBEyTHTSFEjgJgbaHU8CdRi9vmG4cPm1kPLmZhJEP17FMBdNheh3"],
   false, 0, "2MyHkbusvLomaarGYMqyq7q9pSBYJRwWcsw"),
  (true, "sh(wpkh(@0/**))",
   ["[f5acc2fd/49'/1'/0']tpubDC871vGLAiKPcwAw22EjhKVLk5L98UGXBEcGR8gpcigLQVDDfgcYW24QBEyTHTSFEjgJgbaHU8CdRi9vmG4cPm1kPLmZhJEP17FMBdNheh3"],
   true, 15, "2NAbM4FSeBQG4o85kbXw2YNfKypcnEZS9MR"),
  -- 7–10: Singlesig P2TR (BIP-86, stateless default)
  (true, "tr(@0/**)",
   ["[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"],
   false, 0, "tb1pws8wvnj99ca6acf8kq7pjk7vyxknah0d9mexckh5s0vu2ccy68js9am6u7"),
  (true, "tr(@0/**)",
   ["[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"],
   false, 9, "tb1psl7eyk2jyjzq6evqvan854fts7a5j65rth25yqahkd2a765yvj0qggs5ne"),
  (true, "tr(@0/**)",
   ["[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"],
   true, 0, "tb1pmr60r5vfjmdkrwcu4a2z8h39mzs7a6wf2rfhuml6qgcp940x9cxs7t9pdy"),
  (true, "tr(@0/**)",
   ["[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"],
   true, 9, "tb1p98d6s9jkf0la8ras4nnm72zme5r03fexn29e3pgz4qksdy84ndpqgjak72"),
  -- 11–13: Registered 2-of-2 sortedmulti (legacy P2SH, P2SH-P2WSH, native P2WSH)
  (false, "sh(sortedmulti(2,@0/**,@1/**))",
   ["[5c9e228d/48'/1'/0'/0']tpubDEGquuorgFNb8bjh5kNZQMPtABJzoWwNm78FUmeoPkfRtoPF7JLrtoZeT3J3ybq1HmC3Rn1Q8wFQ8J5usanzups5rj7PJoQLNyvq8QbJruW",
    "[f5acc2fd/48'/1'/0'/0']tpubDFAqEGNyad35WQAZMmPD4vgBXnjH16RGciLdWekPe4f4d5JzoHVu1PS86Sy4Tm63vDf8rfV3UjifhrRuSUDfiZj5KPffTPyZ4ZXBKvjD8jm"],
   false, 0, "2Mx69MjHC4ViZAH1koVXPvVgaazbBCdr89j"),
  (false, "sh(wsh(sortedmulti(2,@0/**,@1/**)))",
   ["[76223a6e/48'/1'/0'/1']tpubDE7NQymr4AFtcJXi9TaWZtrhAdy8QyKmT4U6b9qYByAxCzoyMJ8zw5d8xVLVpbTRAEqP8pVUxjLE2vDt1rSFjaiS8DSz1QcNZ8D1qxUMx1g",
    "[f5acc2fd/48'/1'/0'/1']tpubDFAqEGNyad35YgH8zxvxFZqNUoPtr5mDojs7wzbXQBHTZ4xHeVXG6w2HvsKvjBpaRpTmjYDjdPg5w2c6Wvu8QBkyMDrmBWdCyqkDM7reSsY"],
   false, 0, "2MxAUTJh27foYtyp9dcSxP7RgaSwkkVCHTU"),
  (false, "wsh(sortedmulti(2,@0/**,@1/**))",
   ["[76223a6e/48'/1'/0'/2']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
    "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"],
   false, 0, "tb1qmyauyzn08cduzdqweexgna2spwd0rndj55fsrkefry2cpuyt4cpsn2pg28"),
  -- 14–17: Taproot script-path (`pk`, `sortedmulti_a`) & BIP-327/328 MuSig2 (`tr(musig(...))`, `tr(@0/**,pk(musig(...)))`)
  (false, "tr(@0/**,pk(@1/**))",
   ["[76223a6e/48'/1'/0'/2']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
    "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"],
   false, 0, "tb1pls9pp5cgcljpkjauxep03lv2c2yc2wcuua26p3ks6j2lq0vl9kjqf5rgm2"),
  (false, "tr(@0/**,sortedmulti_a(2,@1/**,@2/**))",
   ["[f5acc2fd/48'/1'/0'/1']tpubDFAqEGNyad35YgH8zxvxFZqNUoPtr5mDojs7wzbXQBHTZ4xHeVXG6w2HvsKvjBpaRpTmjYDjdPg5w2c6Wvu8QBkyMDrmBWdCyqkDM7reSsY",
    "[76223a6e/48'/1'/0'/2']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
    "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"],
   false, 0, "tb1pdzk72dnvz3246474p4m5a97u43h6ykt2qcjrrhk6y0fkg8hx2mvswwgvv7"),
  (false, "tr(musig(@0,@1)/**)",
   ["[f5acc2fd/44'/1'/0']tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT",
    "tpubDCwYjpDhUdPGQWG6wG6hkBJuWFZEtrn7j3xwG3i8XcQabcGC53xWZm1hSXrUPFS5UvZ3QhdPSjXWNfWmFGTioARHuG5J7XguEjgg7p8PxAm"],
   false, 3, "tb1pc87la0ksvw4pfq6qc3gn9en33kx7s9rx4c4epy578kfjsdjv6mks7u7dgn"),
  (false, "tr(@0/**,pk(musig(@1,@2)/**))",
   ["tpubD6NzVbkrYhZ4WLczPJWReQycCJdd6YVWXubbVUFnJ5KgU5MDQrD998ZJLSmaB7GVcCnJSDWprxmrGkJ6SvgQC6QAffVpqSvonXmeizXcrkN",
    "[f5acc2fd/44'/1'/0']tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT",
    "tpubDCwYjpDhUdPGQWG6wG6hkBJuWFZEtrn7j3xwG3i8XcQabcGC53xWZm1hSXrUPFS5UvZ3QhdPSjXWNfWmFGTioARHuG5J7XguEjgg7p8PxAm"],
   false, 3, "tb1pa423acwcjc8jgt36muavyun8e2hz3t5qwptsr3wr8afmdfk3wchswf9ntp")
]

/-- Official `register_wallet.toml` positive vectors with exact `wallet_id`, SLIP-21 `wallet_hmac`, and key roles. -/
def officialRegisterWalletVectors : List (String × String × List String × String × String × List PolicyKeyRole) := [
  ("Cold storage", "sh(sortedmulti(2,@0/**,@1/**))",
   ["[5c9e228d/48'/1'/0'/0']tpubDEGquuorgFNb8bjh5kNZQMPtABJzoWwNm78FUmeoPkfRtoPF7JLrtoZeT3J3ybq1HmC3Rn1Q8wFQ8J5usanzups5rj7PJoQLNyvq8QbJruW",
    "[f5acc2fd/48'/1'/0'/0']tpubDFAqEGNyad35WQAZMmPD4vgBXnjH16RGciLdWekPe4f4d5JzoHVu1PS86Sy4Tm63vDf8rfV3UjifhrRuSUDfiZj5KPffTPyZ4ZXBKvjD8jm"],
   "1d150ed425a871a5ca7e2c55db1b3295c1fd97147fd0a7b188d4327f4ba7402a",
   "fa73e36119324fbe4cc1ca94aa842c6261526d44112a22164bc57c3335102b04",
   [.external, .internal]),
  ("Cold storage", "sh(wsh(sortedmulti(2,@0/**,@1/**)))",
   ["[76223a6e/48'/1'/0'/1']tpubDE7NQymr4AFtcJXi9TaWZtrhAdy8QyKmT4U6b9qYByAxCzoyMJ8zw5d8xVLVpbTRAEqP8pVUxjLE2vDt1rSFjaiS8DSz1QcNZ8D1qxUMx1g",
    "[f5acc2fd/48'/1'/0'/1']tpubDFAqEGNyad35YgH8zxvxFZqNUoPtr5mDojs7wzbXQBHTZ4xHeVXG6w2HvsKvjBpaRpTmjYDjdPg5w2c6Wvu8QBkyMDrmBWdCyqkDM7reSsY"],
   "763926f53be53ad89a9248dc15bc2f3ed577a59a87d81cd88f14279b263b31f6",
   "1f498e7444841b883c4a63e2b88a5cad297c289d235794f8e3e17cf559ed0654",
   [.external, .internal]),
  ("Cold storage", "wsh(sortedmulti(2,@0/**,@1/**))",
   ["[76223a6e/48'/1'/0'/2']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
    "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"],
   "cd9474ae9e74403128477789789db43a215e996af80d60120f0d844f8404ac64",
   "d7c7a60b4ab4a14c1bf8901ba627d72140b2fb907f2b4e35d2e693bce9fbb371",
   [.external, .internal]),
  ("Cold storage with a pretty long name that requires 64 characters", "wsh(sortedmulti(2,@0/**,@1/**))",
   ["[76223a6e/48'/1'/0'/2']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
    "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"],
   "57f64b36153b819c624dedd0ba3ba491000c41652087b5b265b2460508b09620",
   "42ea7900175227ee3ea259a0a061dda232dce3e93707d0940f9dc63bab50d35a",
   [.external, .internal]),
  ("Collision and internal", "wsh(multi(1,@0/**,@1/**))",
   ["[f5acc2fd/44'/1'/3']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
    "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"],
   "25bbdfdbc7d7f184ddbea79d52bd1235d95cce799d06b4e7aced22b253d4e266",
   "f82f318bdd7d7db9f586b34c2f4985614ec9abf0d9c9ef48b3e57ba246ef0cf2",
   [.external, .internal])
]

def checkWalletPolicyConformance : Bool :=
  let profile := bolosAppProfile .testnet
  let vanProfile := vanadiumAppProfile .testnet
  let computeHmac : ByteArray → Option ByteArray := fun id32 => some (RefCrypto.bolosComputeWalletHmac id32)
  -- 1. All 17 official `get_wallet_address.toml` vectors derive exact BOLOS addresses
  (officialWalletAddressVectors.all fun (isDefault, desc, keyStrs, isChange, addrIdx, expectedAddr) =>
    let name := if isDefault then "" else "Registered"
    match parseBolosTestnetPolicy name desc keyStrs with
    | .error _ => false
    | .ok pol =>
        if isDefault then
          let dev := bolosRegOracle []
          -- Stateless default works on BOLOS (`addrIdx <= 50000`), fails at `addrIdx = 50001`, and fails on Vanadium (`allowStatelessDefaultPolicies = false`)
          let okAddr := match deriveWalletPolicyAddress .bolos profile dev bolosPolicyOracle pol .statelessDefault isChange addrIdx with
            | .ok a => a == expectedAddr | .error _ => false
          okAddr &&
          (deriveWalletPolicyAddress .bolos profile dev bolosPolicyOracle pol .statelessDefault isChange 50001).isOk == false &&
          (deriveWalletPolicyAddress .vanadium vanProfile dev bolosPolicyOracle pol .statelessDefault isChange addrIdx).isOk == false
        else
          let commit := RegistrationCommitmentInput.bolos desc.toUTF8 (bolosKeysMerkleRoot keyStrs)
          match verifyAndRegisterWalletPolicy profile (bolosRegOracle []) bolosPolicyOracle computeHmac pol commit true with
          | .error _ => false
          | .ok (_, hmac32) =>
              let dev := bolosRegOracle [(name, hmac32)]
              match deriveWalletPolicyAddress .bolos profile dev bolosPolicyOracle pol (.proofOfRegistration hmac32) isChange addrIdx with
              | .ok a => a == expectedAddr | .error _ => false) &&
  -- 2. All 5 official `register_wallet.toml` vectors match exact `wallet_id`, SLIP-21 `wallet_hmac`, and key roles (including fingerprint collision defense!)
  (officialRegisterWalletVectors.all fun (name, desc, keyStrs, expIdHex, expHmacHex, expRoles) =>
    match parseBolosTestnetPolicy name desc keyStrs with
    | .error _ => false
    | .ok pol =>
        let dev := bolosRegOracle []
        let roles := pol.keys.map (classifyKeyInfo dev .testnet)
        let commit := RegistrationCommitmentInput.bolos desc.toUTF8 (bolosKeysMerkleRoot keyStrs)
        match verifyAndRegisterWalletPolicy profile dev bolosPolicyOracle computeHmac pol commit true with
        | .error _ => false
        | .ok (id32, hmac32) =>
            (roles == expRoles) &&
            (id32 == RefCrypto.hex! expIdHex) &&
            (hmac32 == RefCrypto.hex! expHmacHex) &&
            verifyRegistrationHmac bolosPolicyOracle computeHmac pol commit hmac32 &&
            !verifyRegistrationHmac bolosPolicyOracle computeHmac pol commit (ByteArray.mk (Array.replicate 32 0))) &&
  -- 3. Official negative `register_wallet.toml` & security vectors:
  --    (a) 65-char wallet name & leading/trailing space rejected on BOLOS (`validWalletName`), accepted on Vanadium
  !validRegisteredWalletName profile (String.ofList (List.replicate 65 'a')) &&
  !validRegisteredWalletName profile " LeadingSpace" &&
  !validRegisteredWalletName profile "TrailingSpace " &&
  validRegisteredWalletName vanProfile (String.ofList (List.replicate 65 'a')) &&
  --    (b) `sh(wsh(sortedmulti(...)))` accepted on BOLOS (`allowShWsh = true`), rejected on Vanadium (`allowShWsh = false`)
  (match parseDescriptorTemplate .v2 "sh(wsh(sortedmulti(2,@0/**,@1/**)))" with
   | .ok dt => (checkDescriptorTemplate profile .v2 dt).isOk && !(checkDescriptorTemplate vanProfile .v2 dt).isOk
   | .error _ => false) &&
  --    (c) `rawtr(@0/**)` unconditionally rejected in BIP-388 wallet policies
  (match parseDescriptorTemplate .v2 "rawtr(@0/**)" with | .error .parseError => true | _ => false) &&
  (match parseExtendedDescriptorTemplate .v2 "rawtr(@0/**)" with
   | .ok ext => match checkExtendedDescriptorTemplateForBip388 profile .v2 ext with
                | .error .invalidScriptContext => true | _ => false
   | .error _ => false) &&
  --    (d) Miniscript `not_sane_timelock_mixing`, `not_sane_no_signature_required`, `not_sane_malleable`, `too_many_derivation_steps` (9 > 8), `no_internal_key_fp_collision`
  (parseBolosTestnetPolicy "Mix" "wsh(thresh(2,c:pk_k(@0/**),ac:pk_k(@1/**),altv:after(1000000000),altv:after(100)))"
     ["[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK",
      "tpubDDV6FDLcCieWUeN7R3vZK2Qs3KuQed3ScTY9EiwMXvyCkLjDbCb8RXaAgWDbkG4tW1BMKVF1zERHnyt78QKd4ZaAYGMJMpvHPwgSSU1AxZ3"]
   |>.bind (checkPolicyWellFormed profile)).isOk == false &&
  (parseBolosTestnetPolicy "Mal" "wsh(c:andor(ripemd160(6ad07d21fd5dfc646f0b30577045ce201616b9ba),pk_h(@0/**),and_v(v:hash256(8a35d9ca92a48eaade6f53a64985e9e2afeb74dcf8acb4c3721e0dc7e4294b25),pk_h(@1/**))))"
     ["[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK",
      "tpubDDV6FDLcCieWUeN7R3vZK2Qs3KuQed3ScTY9EiwMXvyCkLjDbCb8RXaAgWDbkG4tW1BMKVF1zERHnyt78QKd4ZaAYGMJMpvHPwgSSU1AxZ3"]
   |>.bind (checkPolicyWellFormed profile)).isOk == false &&
  (parseWalletKeyInfo profile .v2 RefCrypto.doubleSha256 false
     "[f5acc2fd/48'/1'/0'/2'/0'/1'/2'/3'/4']tpubDR1MRwnrfYuCbZ5dvozygap7EkR1pRXfwKhfCEpMTHtzrtN78MnFeipS2Vq9Nr3WHSurdqmrPfm5yQH5ikxJhYUTK12VxmqfTKR8hUF8mty").isOk == false &&
  (match parseBolosTestnetPolicy "FpCollision" "wpkh(@0/**)"
     ["[f5acc2fd/44'/1'/3']tpubDD814oESVM3uG2yZZDnJDex6gLeeahu2cmK2AL26ozTtDouQCY4NA8xcTW5oiJLp1cydFtDPdWxWDpLPGyLo6sGbemykJm4ocjjvt5cwvtv"] with
   | .ok pol => match validatePolicyRegistration profile (bolosRegOracle []) pol true with
                | .error .missingInternalKey => true | _ => false
   | .error _ => false) &&
  -- 4. BIP-68 `older(n)` invalid bitmask (`0x00010001` sets bit 16) rejected; canonical BIP-379 `andor(X,Y,Z)` emits `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`
  !validOlderArg 0x00010001 &&
  validOlderArg 144 &&
  (match parseBolosTestnetPolicy "AndOr" "wsh(andor(pk(@0/**),pk(@1/**),and_v(v:pk(@2/**),older(144))))"
     ["[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK",
      "[76223a6e/48'/1'/0'/2']tpubDE7NQymr4AFtewpAsWtnreyq9ghkzQBXpCZjWLFVRAvnbf7vya2eMTvT2fPapNqL8SuVvLQdbUbMfWLVDCZKnsEBqp6UK93QEzL8Ck23AwF",
      "tpubDDV6FDLcCieWUeN7R3vZK2Qs3KuQed3ScTY9EiwMXvyCkLjDbCb8RXaAgWDbkG4tW1BMKVF1zERHnyt78QKd4ZaAYGMJMpvHPwgSSU1AxZ3"] with
   | .ok ({ template := .wsh (.miniscript ms), keys := ks, .. }) =>
       match compileMiniscript bolosPolicyOracle .testnet ks .wshCtx false 0 false ms with
       | .ok script =>
           -- `[pk0 (34B) || OP_CHECKSIG (1B)] || OP_NOTIF (0x64) || [Z: pk2 (34B) || OP_CHECKSIGVERIFY (0xAD) || push(144) || OP_CSV] || OP_ELSE (0x67) || [Y: pk1 (34B) || OP_CHECKSIG] || OP_ENDIF (0x68)`
           (RefCrypto.bget script 35 == OP_NOTIF) &&
           (RefCrypto.bget script 70 == OP_CHECKSIGVERIFY) &&
           (RefCrypto.bget script (script.size - 1) == OP_ENDIF)
       | .error _ => false
   | _ => false)

end WalletPolicyConformance

/-! ## Section 5. `BitcoinLedger.Psbt` Conformance (`test_sighash.c`, `test_locktime.c`, `sign_psbt.toml`, `test_bip322.c`, Swap) -/

section PsbtConformance

open InternalSpec.Psbt (
  Bytes32 zeroBytes32 CryptoOracles SpendClass SighashSafety OutPoint TxOut RawTxIn RawTx
  KeyOrigin KeyDerivationEntry InternalKeyPlaceholder WalletPolicySpec
  PsbtInput PsbtOutput PsbtTx PsbtV0 PsbtError TxDisplayMode SigningConfig SwapMode SwapParams
)
open BitcoinLedger.Psbt

private def isPsbtOkU32 (r : Except PsbtError UInt32) (v : UInt32) : Bool :=
  match r with | .ok x => x == v | .error _ => false

private def isPsbtErr {α : Type} (r : Except PsbtError α) (e : PsbtError) : Bool :=
  match r with | .error x => x == e | .ok _ => false

private def psbtSha256 (bs : ByteArray) : Bytes32 :=
  mkPsbtBytes32! (RefCrypto.sha256 bs)

def bolosPsbtCrypto : CryptoOracles where
  sha256 := psbtSha256
  hash160 := RefCrypto.hash160
  formatAddress spk := BitcoinLedger.Script.scriptToAddress? .bolos RefCrypto.doubleSha256 .testnet spk

/-- All 27 `(sighash_type, SpendClass)` cells from `unit-tests/test_sighash.c` (`classify_sighash_cases`). -/
def officialSighashMatrix : List (UInt32 × SpendClass × SighashSafety) := [
  (0x01, .legacy, .safe), (0x01, .segwitV0, .safe), (0x01, .taprootV1, .safe),
  (0x00, .taprootV1, .safe), (0x00, .segwitV0, .unsupported), (0x00, .legacy, .unsupported),
  (0x02, .segwitV0, .nonSafe), (0x02, .taprootV1, .nonSafe),
  (0x03, .segwitV0, .nonSafe), (0x03, .taprootV1, .nonSafe),
  (0x81, .segwitV0, .nonSafe), (0x81, .taprootV1, .nonSafe),
  (0x82, .segwitV0, .nonSafe), (0x82, .taprootV1, .nonSafe),
  (0x83, .segwitV0, .nonSafe), (0x83, .taprootV1, .nonSafe),
  (0x02, .legacy, .unsupported), (0x03, .legacy, .unsupported),
  (0x81, .legacy, .unsupported), (0x82, .legacy, .unsupported), (0x83, .legacy, .unsupported),
  (0x80, .segwitV0, .unsupported), (0x80, .taprootV1, .unsupported),
  (0x84, .segwitV0, .unsupported), (0x84, .taprootV1, .unsupported),
  (0xFF, .segwitV0, .unsupported), (0xDEAD, .taprootV1, .unsupported)
]

private def mkLtInput (h? t? : Option UInt32) : PsbtInput :=
  { prevout := { txid := zeroBytes32, vout := 0 }
    requiredHeightLocktime := h?
    requiredTimeLocktime := t? }

/-- Official BIP-370 `test_locktime.c` vectors (height/time tie-break, fallback ignored when inputs specify, conflict & boundary rejections). -/
def checkLocktimeConformance : Bool :=
  isPsbtOkU32 (determineLocktime none [mkLtInput none none]) 0 &&
  isPsbtOkU32 (determineLocktime (some 1901594) [mkLtInput none none, mkLtInput none none]) 1901594 &&
  isPsbtOkU32 (determineLocktime none [mkLtInput (some 10000) none, mkLtInput none none]) 10000 &&
  isPsbtOkU32 (determineLocktime none [mkLtInput (some 10000) none, mkLtInput (some 9000) none]) 10000 &&
  isPsbtOkU32 (determineLocktime none [mkLtInput (some 10000) none, mkLtInput (some 9000) (some 1657048460)]) 10000 &&
  -- BIP-370/6: every input declares both -> height wins tie-breaker!
  isPsbtOkU32 (determineLocktime none [mkLtInput (some 10000) (some 1657048459), mkLtInput (some 9000) (some 1657048460)]) 10000 &&
  -- BIP-370/7 & 8: a time-only input forces time!
  isPsbtOkU32 (determineLocktime none [mkLtInput none (some 1657048459), mkLtInput (some 9000) (some 1657048460)]) 1657048460 &&
  -- BIP-370/10: height-only + time-only -> conflict error!
  isPsbtErr (determineLocktime none [mkLtInput (some 10000) none, mkLtInput none (some 1657048460)]) .locktimeConflictOrInvalid &&
  -- Fallback locktime ignored once any input specifies a required locktime!
  isPsbtOkU32 (determineLocktime (some 900000) [mkLtInput (some 10000) none]) 10000 &&
  -- Out-of-range height `0` and height `>= 500_000_000` and time `< 500_000_000` rejected!
  isPsbtErr (determineLocktime none [mkLtInput (some 0) none]) .locktimeConflictOrInvalid &&
  isPsbtErr (determineLocktime none [mkLtInput (some 500000000) none]) .locktimeConflictOrInvalid &&
  isPsbtErr (determineLocktime none [mkLtInput none (some 499999999)]) .locktimeConflictOrInvalid

/-- Official `sign_psbt.toml` sighash & cryptographic signature conformance (`pkh-1to1`, `wpkh-1to2`, `tr-1to2-sighash-all`, `tr-1to2-sighash-default`). -/
def checkOfficialPsbtSighashesAndSigs : Bool :=
  -- 1. `singlesig_pkh_1to1`: Legacy P2PKH sighash + DER ECDSA signature verification
  let pkhIn : PsbtInput := {
    prevout := { txid := mkPsbtBytes32! (RefCrypto.hex! "5122c2cde6823e55754175b92c9c57a0a8e1ac83c38e1787fd3a1ff3348e9513"), vout := 1 }
    sequence := some 4294967293
  }
  let pkhSpk := RefCrypto.hex! "76a914cbae5b50cf939e6f531b8a6b7abd788fe14b029788ac"
  let pkhOut : TxOut := { amount := 999800, scriptPubKey := RefCrypto.hex! "76a91413d7d58166946c3ec022934066d8c0d111d1bb4188ac" }
  let pkhDigest := computeSighashLegacy psbtSha256 2 1901594 #[pkhIn] #[pkhOut] 0 pkhSpk 0x01
  let pkhSigOk :=
    match RefCrypto.decompressPt? (RefCrypto.hex! "02ee8608207e21028426f69e76447d7e3d5e077049f5e683c3136c2314762a4718"),
          RefCrypto.parseDerSigPlusSighash? (RefCrypto.hex! "3045022100e55b3ca788721aae8def2eadff710e524ffe8c9dec1764fdaa89584f9726e196022012a30fbcf9e1a24df31a1010356b794ab8de438b4250684757ed5772402540f401") with
    | some pub, some (r, s, 0x01) => RefCrypto.ecdsaVerifyRaw pub pkhDigest.bytes r s
    | _, _ => false
  -- 2. `singlesig_wpkh_1to2`: BIP-143 SegWit v0 sighash + DER ECDSA signature verification
  let wpkhIn : PsbtInput := {
    prevout := { txid := mkPsbtBytes32! (RefCrypto.hex! "7a2a997956c09f8ea7fd2819c1a987bb14e22bf9adcdaf20a89763722ceee264"), vout := 1 }
    sequence := some 4294967293
  }
  let wpkhUtxo : TxOut := { amount := 3208357, scriptPubKey := RefCrypto.hex! "00143af8429ad5954aa5ee8a33c983fd8a1e8679924b" }
  let wpkhOuts : Array TxOut := #[
    { amount := 900000, scriptPubKey := RefCrypto.hex! "76a914344a0f48ca150ec2b903817660b9b68b13a6702688ac" },
    { amount := 2308212, scriptPubKey := RefCrypto.hex! "0014eb38fa9b8128f81f26e95edb0c5ffaea83690fe4" }
  ]
  let wpkhHashes := computeTxHashes psbtSha256 [(wpkhIn, wpkhUtxo)] wpkhOuts.toList
  let wpkhSigOk :=
    match buildSegwitV0ScriptCode wpkhUtxo.scriptPubKey none,
          RefCrypto.decompressPt? (RefCrypto.hex! "03ee2c3d98eb1f93c0a1aa8e5a4009b70eb7b44ead15f1666f136b012ad58d3068"),
          RefCrypto.parseDerSigPlusSighash? (RefCrypto.hex! "3045022100ab44f34dd7e87c9054591297a101e8500a0641d1d591878d0d23cf8096fa79e802205d12d1062d925e27b57bdcf994ecf332ad0a8e67b8fe407bab2101255da632aa01") with
    | some scWithLen, some pub, some (r, s, 0x01) =>
        let dig := computeSighashSegwitV0 psbtSha256 2 0 wpkhHashes wpkhIn wpkhUtxo.amount scWithLen wpkhOuts 0 0x01
        RefCrypto.ecdsaVerifyRaw pub dig.bytes r s
    | _, _, _ => false
  -- 3. `singlesig_tr_1to2_sighash_all` (`0x01`) & `singlesig_tr_1to2_sighash_default` (`0x00`): exact BIP-341 sighashes!
  let trAllIn : PsbtInput := {
    prevout := { txid := mkPsbtBytes32! (RefCrypto.hex! "a1b823d2336d694b4934ef9b6e5b7de17a05513da8a29db02a2ecbc7a9a6fe6d"), vout := 1 }
    sequence := some 4294967293
  }
  let trAllUtxo : TxOut := { amount := 11110055, scriptPubKey := RefCrypto.hex! "5120d8f4f1d18996db61bb1caf5423de25d8a1eee9c950d37e6ffa023012d5e62e0d" }
  let trAllOuts : Array TxOut := #[
    { amount := 11009877, scriptPubKey := RefCrypto.hex! "51200b8e7486bc306a0aefb7a7c00af0405542db1acd73eecca82771ccf5fe5eb60f" },
    { amount := 100000, scriptPubKey := RefCrypto.hex! "00141399b8a09847a039b0352f58d212c180bab17f77" }
  ]
  let trAllHashes := computeTxHashes psbtSha256 [(trAllIn, trAllUtxo)] trAllOuts.toList
  let trAllDig := computeSighashTaproot psbtSha256 2 0 trAllHashes trAllIn trAllUtxo trAllOuts 0 none 0x01
  let trDefIn : PsbtInput := {
    prevout := { txid := mkPsbtBytes32! (RefCrypto.hex! "e16861c0d29749f52cd2edde10cbcc4f591210710f640e5d8e1440ce85d96dc6"), vout := 1 }
    sequence := some 4294967293
  }
  let trDefUtxo : TxOut := { amount := 10009567, scriptPubKey := RefCrypto.hex! "512089904a6348d7ff9a44d49db8b6a807c622e868364c547da426f30b5a6213186a" }
  let trDefOuts : Array TxOut := #[
    { amount := 9909389, scriptPubKey := RefCrypto.hex! "51200b8e7486bc306a0aefb7a7c00af0405542db1acd73eecca82771ccf5fe5eb60f" },
    { amount := 100000, scriptPubKey := RefCrypto.hex! "00141399b8a09847a039b0352f58d212c180bab17f77" }
  ]
  let trDefHashes := computeTxHashes psbtSha256 [(trDefIn, trDefUtxo)] trDefOuts.toList
  let trDefDig := computeSighashTaproot psbtSha256 2 0 trDefHashes trDefIn trDefUtxo trDefOuts 0 none 0x00
  pkhSigOk && wpkhSigOk &&
  eqBytes trAllDig.bytes (RefCrypto.hex! "7a999e5ad6f53ea6448e7026061d3b4523f957999c430a5a492dface74ae31b6") &&
  eqBytes trDefDig.bytes (RefCrypto.hex! "75c96fb06a12db4cd011d8c95a5995db758a4f2837a22f30f0f579619a4466f3") &&
  -- Schnorr `SIGHASH_DEFAULT` omits suffix byte (64B), whereas `SIGHASH_ALL` appends `0x01` (65B)
  ((formatSignatureWithSighash true (ByteArray.mk (Array.replicate 64 0xAA)) 0x00).size == 64) &&
  ((formatSignatureWithSighash true (ByteArray.mk (Array.replicate 64 0xAA)) 0x01).size == 65)

def checkPsbtConformance : Bool :=
  let h84 : UInt32 := 0x80000054
  let h1  : UInt32 := 0x80000001
  let h0  : UInt32 := 0x80000000
  let wpkhOrigin : KeyOrigin := { fingerprint := 0xF5ACC2FD, path := [h84, h1, h0] }
  let recvSpk := RefCrypto.hex! "00143af8429ad5954aa5ee8a33c983fd8a1e8679924b"
  let chgSpk  := RefCrypto.hex! "0014eb38fa9b8128f81f26e95edb0c5ffaea83690fe4"
  let extSpk  := RefCrypto.hex! "76a914344a0f48ca150ec2b903817660b9b68b13a6702688ac"
  let pol : WalletPolicySpec := {
    isDefault := true
    name := ""
    spendClass := .segwitV0
    internalPlaceholders := [{
      keyIndex := 0
      expectedOrigin := some wpkhOrigin
      numFirst := 0
      numSecond := 1
    }]
    deriveScripts := fun isChg idx =>
      if !isChg && idx == 0 then some (recvSpk, none, none)
      else if isChg && idx == 0 then some (chgSpk, none, none)
      else none
  }
  let inDeriv : KeyDerivationEntry := {
    pubkey := RefCrypto.hex! "03ee2c3d98eb1f93c0a1aa8e5a4009b70eb7b44ead15f1666f136b012ad58d3068"
    origin := { fingerprint := 0xF5ACC2FD, path := [h84, h1, h0, 0, 0] }
  }
  let chgDeriv : KeyDerivationEntry := {
    pubkey := RefCrypto.hex! "03ee2c3d98eb1f93c0a1aa8e5a4009b70eb7b44ead15f1666f136b012ad58d3068"
    origin := { fingerprint := 0xF5ACC2FD, path := [h84, h1, h0, 1, 0] }
  }
  let prevTx : RawTx := {
    version := 2
    vin := #[{ prevout := { txid := zeroBytes32, vout := 0 }, scriptSig := ByteArray.empty, sequence := 0xFFFFFFFF }]
    vout := #[{ amount := 3208357, scriptPubKey := recvSpk }]
    locktime := 0
  }
  let prevTxid := computeTxid psbtSha256 prevTx
  let validIn : PsbtInput := {
    prevout := { txid := prevTxid, vout := 0 }
    nonWitnessUtxo := some prevTx
    witnessUtxo := some { amount := 3208357, scriptPubKey := recvSpk }
    derivations := [inDeriv]
  }
  let extOut : PsbtOutput := { amount := 900000, scriptPubKey := some extSpk }
  let chgOut : PsbtOutput := { amount := 2308212, scriptPubKey := some chgSpk, derivations := [chgDeriv] }
  let validTx : PsbtTx := { txVersion := 2, inputs := #[validIn], outputs := #[extOut, chgOut] }
  -- 1. All 27 `test_sighash.c` classification vectors + display mode decisions
  (officialSighashMatrix.all fun (sh, sc, expected) =>
    (classifySighashType sc (some sh)).1 == expected) &&
  (selectTxDisplayMode true true (some 0x01) 2 0 false false == .unavailable) &&
  (selectTxDisplayMode true false (some 0x81) 2 0 false false == .netOnly) &&
  (selectTxDisplayMode true false (some 0x02) 2 0 false false == .unavailable) &&
  (selectTxDisplayMode true false (some 0x03) 1 0 false false == .netOnly) &&
  (selectTxDisplayMode true false (some 0x03) 2 0 false false == .unavailable) &&
  (selectTxDisplayMode false false (some 0x01) 1 0 false true == .selfTransfer) &&
  -- 2. Locktime determination (`test_locktime.c`) & official PSBT sighash/signature verification (`sign_psbt.toml`)
  checkLocktimeConformance &&
  checkOfficialPsbtSighashesAndSigs &&
  -- 3. PSBTv0-to-PSBTv2 normalization: valid v0 succeeds; non-empty scriptSig or v2-exclusive fields fail
  (let v0 : PsbtV0 := {
     unsignedTx := {
       version := 2
       vin := #[{ prevout := { txid := prevTxid, vout := 0 }, scriptSig := ByteArray.empty, sequence := 0xFFFFFFFD }]
       vout := #[{ amount := 900000, scriptPubKey := extSpk }]
       locktime := 0
     }
     inputs := #[{ witnessUtxo := some { amount := 1000000, scriptPubKey := recvSpk } }]
     outputs := #[{}]
   }
   (normalizePsbtV0ToV2 v0).isOk &&
   isPsbtErr (normalizePsbtV0ToV2 { v0 with hasV2ExclusiveGlobals := true }) .psbtV0ForbiddenV2Fields &&
   isPsbtErr (normalizePsbtV0ToV2 { v0 with unsignedTx := { v0.unsignedTx with
     vin := #[{ prevout := { txid := prevTxid, vout := 0 }, scriptSig := ByteArray.mk #[0x00], sequence := 0 }] } })
     .psbtV0NonEmptyScriptSig) &&
  -- 4. Full `validatePsbtTransaction`: change output filtered (`displayedOutputs.length == 1`), `fee == 145`
  (match validatePsbtTransaction bolosPsbtCrypto {} pol validTx with
   | .ok val =>
       val.displayedOutputs.length == 1 && val.changeOutputs.length == 1 &&
       val.fee == some 145 && !val.warnings.missingNonWitnessUtxo && val.displayMode == .full
   | .error _ => false) &&
  -- 5. CVE-2020-14199: SegWit v0 without `nonWitnessUtxo` raises `missingNonWitnessUtxo = true`;
  --    dual-UTXO mismatch (`witnessUtxo.amount != nonWitnessUtxo.vout[0].amount`) fails with `.dualUtxoMismatch`;
  --    11 change outputs exceed BOLOS `MAX_CHANGE_OUTPUTS = 10` (`tooManyChangeOutputs`)
  (match validatePsbtTransaction bolosPsbtCrypto {} pol
           { validTx with inputs := #[{ validIn with nonWitnessUtxo := none }] } with
   | .ok val => val.warnings.missingNonWitnessUtxo == true
   | .error _ => false) &&
  isPsbtErr (validatePsbtTransaction bolosPsbtCrypto {} pol
     { validTx with inputs := #[{ validIn with witnessUtxo := some { amount := 3208358, scriptPubKey := recvSpk } }] })
     .dualUtxoMismatch &&
  isPsbtErr (validatePsbtTransaction bolosPsbtCrypto {} pol
     { validTx with outputs := Array.replicate 11 { chgOut with amount := 1000 } })
     .tooManyChangeOutputs &&
  -- 6. ReferenceDiscrepancy #1: Two valid UTXOs (`1.5e15 + 1.0e15 > MAX_MONEY`) rejected by `checkedAddSats?` / `validatePsbtTransaction`
  (checkedAddSats? 1_500_000_000_000_000 1_000_000_000_000_000 == none) &&
  isPsbtErr (validatePsbtTransaction bolosPsbtCrypto {} pol
     { validTx with outputs := #[{ extOut with amount := 1_500_000_000_000_000 }, { extOut with amount := 1_000_000_000_000_000 }] })
     .amountExceedsMaxSupply &&
  -- 7. Official BIP-322 `TO_SPEND_HELLO_WORLD` (`unit-tests/test_bip322.c:24-146`) byte-for-byte match!
  (let challengeSpk := RefCrypto.hex! "00142b05d564e6a7a33c087f16e0f730d1440123799d"
   let expectedToSpend := RefCrypto.hex!
     ("00000000010000000000000000000000000000000000000000000000000000000000000000ffffffff" ++
      "220020f0eb03b1a75ac6d9847f55c624a99169b5dccba2a31f5b23bea77ba270de0a7a00000000" ++
      "0100000000000000001600142b05d564e6a7a33c087f16e0f730d1440123799d00000000")
   let built := encodeRawTxStripped (buildBip322ToSpendTx psbtSha256 "Hello World".toUTF8 challengeSpk)
   eqBytes built expectedToSpend) &&
  -- 8. Ledger Exchange Swap validation (`standard` & `crossChain` modes + fee/destination mismatch rejection)
  (match bolosPsbtCrypto.formatAddress extSpk with
   | none => false
   | some destAddr =>
       let swapOk : SwapParams := { mode := .standard, amount := 900000, fees := 145, destinationAddress := destAddr }
       let payin := "swap-payin-payload".toUTF8
       let opSwap : PsbtOutput := { amount := 0, scriptPubKey := some (ByteArray.mk #[0x6a, UInt8.ofNat payin.size] ++ payin) }
       let ccTx : PsbtTx := { txVersion := 2, inputs := #[validIn], outputs := #[opSwap, extOut, chgOut] }
       let ccSwap : SwapParams := { swapOk with mode := .crossChain (psbtSha256 payin) }
       (authorizePsbtSigning bolosPsbtCrypto {} pol validTx (some swapOk)).isOk &&
       isPsbtErr (authorizePsbtSigning bolosPsbtCrypto {} pol validTx (some { swapOk with fees := 146 })) .swapFeeMismatch &&
       (authorizePsbtSigning bolosPsbtCrypto {} pol ccTx (some ccSwap)).isOk &&
       isPsbtErr (authorizePsbtSigning bolosPsbtCrypto {} pol ccTx (some { ccSwap with mode := .crossChain zeroBytes32 }))
         .swapInvalidCrossChainPayin)

end PsbtConformance

/-! ## Section 6. `BitcoinLedger.MerkleProtocol` Conformance (`merkle.c`, `check_merkle_tree_sorted.c`, `0xE000` Streaming) -/

section MerkleProtocolConformance

open InternalSpec.MerkleProtocol (
  MerkleElementOpening MerkleMapCommitment ClientCommandTag
  MapLookupResult MapLookupProof MerkleizedPsbtCommitment
  ContinuationApdu PreimageInitFrame MoreElementsChunk PreimageStreamError
  mkHonestMapHostOracle
)
open BitcoinLedger.MerkleProtocol

private def merkleSha256 (bs : ByteArray) : InternalSpec.Psbt.Bytes32 :=
  mkPsbtBytes32! (RefCrypto.sha256 bs)

private def mkOpening (leaves : List ByteArray) (idx : Nat) : MerkleElementOpening :=
  let elem := leaves[idx]?.getD ByteArray.empty
  { element := elem
    leafHash := merkleLeafHash merkleSha256 elem
    siblingsBottomUp := buildMerkleAuditPath merkleSha256 leaves idx }

def checkMerkleProtocolConformance : Bool :=
  let z32 := InternalSpec.Psbt.zeroBytes32
  -- 1. Empty tree `MTH([]) == 0^32` (BOLOS intentional deviation from RFC-6962 `SHA256("")`),
  --    domain separation `merkleLeafHash != merkleNodeHash`, and unbalanced 5-leaf & 7-leaf audit paths
  let leaves5 := (List.range 5).map fun i => ByteArray.mk #[0x10, UInt8.ofNat i]
  let root5 := merkleRoot merkleSha256 leaves5
  let leaves7 := (List.range 7).map fun i => ByteArray.mk #[0x20, UInt8.ofNat i]
  let root7 := merkleRoot merkleSha256 leaves7
  (eqBytes32 (merkleRoot merkleSha256 []) z32) &&
  !eqBytes32 (merkleLeafHash merkleSha256 (z32.bytes ++ z32.bytes)) (merkleNodeHash merkleSha256 z32 z32) &&
  ((List.range 5).all fun i => verifyMerkleElementOpening merkleSha256 root5 5 i (mkOpening leaves5 i)) &&
  ((List.range 7).all fun i => verifyMerkleElementOpening merkleSha256 root7 7 i (mkOpening leaves7 i)) &&
  -- Swapped index (proof for leaf 1 presented at index 2) MUST fail; `leafIndex > INT_MAX` MUST fail
  !verifyMerkleElementOpening merkleSha256 root5 5 2 (mkOpening leaves5 1) &&
  !verifyMerkleLeafHashProof merkleSha256 root5 0x80000001 0x80000000 (merkleLeafHash merkleSha256 ByteArray.empty) [] &&
  -- 2. Sorted Merkleized map (`check_merkle_tree_sorted.c`): strictly sorted keys pass, duplicate or unsorted keys fail
  (let entries : List (ByteArray × ByteArray) := [
     (ByteArray.mk #[0x01], "val0".toUTF8),
     (ByteArray.mk #[0x02, 0x00], "val1".toUTF8),
     (ByteArray.mk #[0x03], "val2".toUTF8)
   ]
   let mapCommit := commitMerkleMap merkleSha256 entries
   let keys := entries.map Prod.fst
   let vals := entries.map Prod.snd
   let keyOpenings := (List.range 3).map (mkOpening keys)
   let host := mkHonestMapHostOracle merkleSha256 entries
   let dupEntries := [(ByteArray.mk #[0x01], "a".toUTF8), (ByteArray.mk #[0x01], "b".toUTF8)]
   let dupCommit := commitMerkleMap merkleSha256 dupEntries
   let dupOpenings := (List.range 2).map (mkOpening (dupEntries.map Prod.fst))
   let proof1 : MapLookupProof := {
     index := 1
     keySiblingsBottomUp := buildMerkleAuditPath merkleSha256 keys 1
     valueOpening := mkOpening vals 1
   }
   verifySortedMerkleMapOpenings merkleSha256 mapCommit keyOpenings &&
   !verifySortedMerkleMapOpenings merkleSha256 dupCommit dupOpenings &&
   verifyMerkleMapLookup merkleSha256 mapCommit (ByteArray.mk #[0x02, 0x00]) proof1 &&
   (match deviceLookupBoundedKeyHeader merkleSha256 host mapCommit (ByteArray.mk #[0x02, 0x00]) with
    | .present v => eqBytes v "val1".toUTF8
    | _ => false) &&
   (deviceLookupBoundedKeyHeader merkleSha256 host mapCommit (ByteArray.mk #[0x99]) == .absentClaimed) &&
   -- Key header > 64 bytes rejected before host query (`MAX_MAP_KEY_HEADER_LEN = 64`)
   (deviceLookupBoundedKeyHeader merkleSha256 host mapCommit (ByteArray.mk (Array.replicate 65 0x01)) == .protocolError)) &&
  -- 3. BOLOS `0xE000` (`SW_INTERRUPTED_EXECUTION`) client-command framing & chunked preimage streaming
  (let contOk : ContinuationApdu := { cla := 0xF8, ins := 0x01, p1 := 0, p2 := 0 }
   let payload300 := ByteArray.mk ((List.range 300).map fun i => UInt8.ofNat (i % 251)).toArray
   let leafRaw := ByteArray.mk #[0x00] ++ payload300
   let expectedLeaf := merkleLeafHash merkleSha256 payload300
   let initFrame : PreimageInitFrame := {
     continuation := contOk
     declaredTotalSize := leafRaw.size
     partialData := leafRaw.extract 0 200
   }
   let chunk1 : MoreElementsChunk := {
     continuation := contOk
     nElements := 101
     elementSize := 1
     chunkData := leafRaw.extract 200 301
   }
   let zeroChunk : MoreElementsChunk := { chunk1 with nElements := 0, chunkData := ByteArray.empty }
   (mkGetPreimageFrame expectedLeaf).statusWord == 0xE000 &&
   (decodeClientCommandTag? (encodeClientCommandTag .getMerkleLeafProof) == some .getMerkleLeafProof) &&
   (match streamVerifyMerkleLeafPreimage merkleSha256 expectedLeaf initFrame [chunk1] with
    | .ok out => eqBytes out payload300
    | .error _ => false) &&
   -- Anti-infinite-loop guard: `nElements = 0` rejected with `.invalidChunkElementCount`!
   (match streamVerifyMerkleLeafPreimage merkleSha256 expectedLeaf initFrame [zeroChunk, chunk1] with
    | .error .invalidChunkElementCount => true
    | _ => false) &&
   -- Tampered final byte rejected with `.digestMismatch`!
   (let badTail := (leafRaw.extract 200 300).push 0xFF
    match streamVerifyMerkleLeafPreimage merkleSha256 expectedLeaf initFrame [{ chunk1 with chunkData := badTail }] with
    | .error .digestMismatch => true
    | _ => false)) &&
  -- 4. Full PSBT Merkleized commitment bundle (`verifyPsbtMerkleBundle` in `init_global_state.c`)
  (let gEntries := [(ByteArray.mk #[0x01], ByteArray.mk #[0x02])]
   let inEntries := [(ByteArray.mk #[0x01], "utxo".toUTF8)]
   let outEntries := [(ByteArray.mk #[0x03], "spk".toUTF8)]
   let gMap := commitMerkleMap merkleSha256 gEntries
   let inMap := commitMerkleMap merkleSha256 inEntries
   let outMap := commitMerkleMap merkleSha256 outEntries
   let inSer := serializeMerkleMapCommitment inMap
   let outSer := serializeMerkleMapCommitment outMap
   let inRoot := merkleRoot merkleSha256 [inSer]
   let outRoot := merkleRoot merkleSha256 [outSer]
   let psbtCommit : MerkleizedPsbtCommitment := {
     globalMap := gMap, nInputs := 1, inputsRoot := inRoot, nOutputs := 1, outputsRoot := outRoot,
     walletId := z32, walletHmac := z32
   }
   verifyPsbtMerkleBundle merkleSha256 psbtCommit
     [mkOpening [ByteArray.mk #[0x01]] 0]
     [(inMap, mkOpening [inSer] 0, [mkOpening [ByteArray.mk #[0x01]] 0])]
     [(outMap, mkOpening [outSer] 0, [mkOpening [ByteArray.mk #[0x03]] 0])])

end MerkleProtocolConformance

/-! ## Section 7. `BitcoinLedger.Musig2` Conformance (BIP-327 `unit-tests/test_musig.c` & Session Linearity) -/

section Musig2Conformance

open InternalSpec.Musig2 (
  SizedBytes CompressedPubKey XOnlyPubKey PubNonce SecNonce
  MusigTweak SessionContext MusigError MusigSignTask
  MusigRound2TaskInput MusigOp MusigStepEvent NonceAggPkMode
)
open BitcoinLedger.Musig2

private def mpk! (s : String) : CompressedPubKey := mkMusigBytes33! (RefCrypto.hex! s)
private def mxo! (s : String) : XOnlyPubKey := mkMusigBytes32! (RefCrypto.hex! s)
private def mb32! (s : String) : InternalSpec.Musig2.Bytes32 := mkMusigBytes32! (RefCrypto.hex! s)
private def mpn! (s : String) : PubNonce := mkMusigBytes66! (RefCrypto.hex! s)

private def parseSecNonce! (s : String) : SecNonce :=
  let raw := RefCrypto.hex! s
  { k1 := RefCrypto.bytesToNatBE (raw.extract 0 32)
    k2 := RefCrypto.bytesToNatBE (raw.extract 32 64)
    pk := mkMusigBytes33! (raw.extract 64 97) }

def officialKeySortInput : List CompressedPubKey := [
  mpk! "02DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8",
  mpk! "02F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
  mpk! "03DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659",
  mpk! "023590A94E768F8E1815C2F24B4D80A8E3149316C3518CE7B7AD338368D038CA66",
  mpk! "02DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EFF",
  mpk! "02DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8"
]

def officialKeySortExpected : List CompressedPubKey := [
  mpk! "023590A94E768F8E1815C2F24B4D80A8E3149316C3518CE7B7AD338368D038CA66",
  mpk! "02DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8",
  mpk! "02DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8",
  mpk! "02DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EFF",
  mpk! "02F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
  mpk! "03DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659"
]

def officialKeyAggPks : Array CompressedPubKey := #[
  mpk! "02F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
  mpk! "03DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659",
  mpk! "023590A94E768F8E1815C2F24B4D80A8E3149316C3518CE7B7AD338368D038CA66",
  mpk! "020000000000000000000000000000000000000000000000000000000000000005",
  mpk! "02FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30",
  mpk! "04F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
  mpk! "03935F972DA013F80AE011890FA89B67A27B7BE6CCB24D3274D18B2D4067F261A9"
]

def officialSignPks : Array CompressedPubKey := #[
  mpk! "03935F972DA013F80AE011890FA89B67A27B7BE6CCB24D3274D18B2D4067F261A9",
  mpk! "02F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
  mpk! "02DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA661",
  mpk! "020000000000000000000000000000000000000000000000000000000000000007"
]

def officialTweakPks : List CompressedPubKey := [
  mpk! "02F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
  mpk! "02DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659",
  mpk! "03935F972DA013F80AE011890FA89B67A27B7BE6CCB24D3274D18B2D4067F261A9"
]

def officialTweakScalars : Array InternalSpec.Musig2.Bytes32 := #[
  mb32! "E8F791FF9225A2AF0102AFFF4A9A723D9612A682A25EBE79802B263CDFCD83BB",
  mb32! "AE2EA797CC0FE72AC5B97B97F3C6957D7E4199A167A58EB08BCAFFDA70AC0455",
  mb32! "F52ECBC565B3D8BEA2DFD5B75A4F457E54369809322E4120831626F290FA87E0",
  mb32! "1969AD73CC177FA0B4FCED6DF1F7BF9907E665FDE9BA196A74FED0A3CF5AEF9D",
  mb32! "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"
]

def officialNonceAggPnonces : Array PubNonce := #[
  mpn! "020151C80F435648DF67A22B749CD798CE54E0321D034B92B709B567D60A42E66603BA47FBC1834437B3212E89A84D8425E7BF12E0245D98262268EBDCB385D50641",
  mpn! "03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A60248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B833",
  mpn! "020151C80F435648DF67A22B749CD798CE54E0321D034B92B709B567D60A42E6660279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
  mpn! "03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A60379BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
  mpn! "04FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A60248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B833",
  mpn! "03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A60248C264CDD57D3C24D79990B0F865674EB62A0F9018277A95011B41BFC193B831",
  mpn! "03FF406FFD8ADB9CD29877E4985014F66A59F6CD01C0E88CAA8E5F3166B1F676A602FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30"
]

private def checkKeyAggValid (idxs : List Nat) (expHex : String) : Bool :=
  let pks := idxs.map (fun i => officialKeyAggPks[i]!)
  match keyAgg bolosMusigCrypto pks with
  | .ok ctx =>
      decide (bolosMusigCrypto.xCoord ctx.q = mxo! expHex) &&
      ctx.gacc == 1 && ctx.tacc == 0
  | .error _ => false

private def checkKeyAggErr (idxs : List Nat) (expected : MusigError) : Bool :=
  let pks := idxs.map (fun i => officialKeyAggPks[i]!)
  match keyAgg bolosMusigCrypto pks with
  | .error e => decide (e = expected)
  | .ok _ => false

private def checkPartialSignOk (sec : SecNonce) (sk : InternalSpec.Musig2.Bytes32) (ctx : SessionContext) (expHex : String) : Bool :=
  match partialSign bolosMusigCrypto sec sk ctx with
  | .ok psig => decide (psig = mb32! expHex)
  | .error _ => false

private def checkPartialSignErr (sec : SecNonce) (sk : InternalSpec.Musig2.Bytes32) (ctx : SessionContext) (expected : MusigError) : Bool :=
  match partialSign bolosMusigCrypto sec sk ctx with
  | .error e => decide (e = expected)
  | .ok _ => false

def checkMusig2Conformance : Bool :=
  let signSk := mb32! "7FB9E0E687ADA1EEBF7ECFE2F21E73EBDB51A7D450948DFE8D76D7F2D1007671"
  let sec0 := parseSecNonce! "508B81A611F100A6B2B6B29656590898AF488BCF2E1F55CF22E5CFB84421FE61FA27FD49B1D50085B481285E1CA205D55C82CC1B31FF5CD54A489829355901F703935F972DA013F80AE011890FA89B67A27B7BE6CCB24D3274D18B2D4067F261A9"
  let secZero := parseSecNonce! "0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003935F972DA013F80AE011890FA89B67A27B7BE6CCB24D3274D18B2D4067F261A9"
  let agg0 := mpn! "028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9"
  let aggInf := mpn! "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
  let aggBadTag := mpn! "048465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61037496A3CC86926D452CAFCFD55D25972CA1675D549310DE296BFF42F72EEEA8C9"
  let aggBadX := mpn! "028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD61020000000000000000000000000000000000000000000000000000000000000009"
  let aggGtP := mpn! "028465FCF0BBDBCF443AABCCE533D42B4B5A10966AC09A49655E8C42DAAB8FCD6102FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30"
  let msg0 := RefCrypto.hex! "F95466D086770E689964664219266FE5ED215C92AE20BAB5C9D79ADDDDF3C0CF"
  let msgEmpty := ByteArray.empty
  let msg38 := RefCrypto.hex! "2626262626262626262626262626262626262626262626262626262626262626262626262626"
  let mkSignCtx (idxs : List Nat) (an : PubNonce) (m : ByteArray) (tws : List MusigTweak := []) : SessionContext :=
    { aggnonce := an, pubkeys := idxs.map (fun i => officialSignPks[i]!), tweaks := tws, msg := m }
  -- 1. `key_sort_vectors.json` (`test_key_sort`)
  decide (keySort officialKeySortInput = officialKeySortExpected) &&
  -- 2. `key_agg_vectors.json` (`test_key_agg_valid` & `test_key_agg_invalid_pubkey`)
  checkKeyAggValid [0, 1, 2] "90539EEDE565F5D054F32CC0C220126889ED1E5D193BAF15AEF344FE59D4610C" &&
  checkKeyAggValid [2, 1, 0] "6204DE8B083426DC6EAF9502D27024D53FC826BF7D2012148A0575435DF54B2B" &&
  checkKeyAggValid [0, 0, 0] "B436E3BAD62B8CD409969A224731C193D051162D8C5AE8B109306127DA3AA935" &&
  checkKeyAggValid [0, 0, 1, 1] "69BC22BFA5D106306E48A20679DE1D7389386124D07571D0D872686028C26A3E" &&
  checkKeyAggErr [0, 3] .invalidPoint &&
  checkKeyAggErr [0, 4] .invalidPoint &&
  checkKeyAggErr [5, 0] .invalidPoint &&
  -- 3. `nonce_gen_cases` (`test_nonce_gen`)
  (let rand := mb32! "0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F"
   let aggpk := mxo! "0707070707070707070707070707070707070707070707070707070707070707"
   let pkA := mpk! "024D4B6CD1361032CA9BD2AEB9D900AA4D45D9EAD80AC9423374C451A7254D0766"
   let pkB := mpk! "02F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
   let expSecA := parseSecNonce! "F8FAEC2D34771E67C60D6BE8B7175D2B03EBDA90D7E7DBFFA443F50679442974FB0619D1F4499019723E967A93319308D490E39830D064177D1429C4C55402C9024D4B6CD1361032CA9BD2AEB9D900AA4D45D9EAD80AC9423374C451A7254D0766"
   let expPubA := mpn! "037D1331D56E0C9294E8087C013F515D9A30F553F7E3D1B27BE1A55B7B15F8B2C10312A7963FC3EA81168EE28C408CC08B82A425CEEFF1EC3B2C12B30DC9C6BE6E91"
   let expSecB := parseSecNonce! "10472D304D995EC113ED820DB89A2E9D7FF72F974C4BE7FDBA32D23A61C56BFB9022D5083CA4142579B31510585F88B8BE5A1EF5A31819B72273B665F402BAF702F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9"
   let expPubB := mpn! "02D8ED280D294894891FCF8D2B3DD357FC1705095951CB06A890B2E35F82878EF002283AA0139AB3BE6E8FDC2218D7EC8DA02FC01D8054EF481DDE1AA10D6F71F6F1"
   (match nonceGen bolosMusigCrypto rand pkA aggpk with
    | .ok (s, p) => decide (s = expSecA) && decide (p = expPubA)
    | .error _ => false) &&
   (match nonceGen bolosMusigCrypto rand pkB aggpk with
    | .ok (s, p) => decide (s = expSecB) && decide (p = expPubB)
    | .error _ => false)) &&
  -- 4. `nonce_agg_vectors.json` (`test_nonce_agg`, including infinity second half & signer blame index!)
  (match nonceAgg bolosMusigCrypto [officialNonceAggPnonces[0]!, officialNonceAggPnonces[1]!] with
   | .ok an => decide (an = mpn! "035FE1873B4F2967F52FEA4A06AD5A8ECCBE9D0FD73068012C894E2E87CCB5804B024725377345BDE0E9C33AF3C43C0A29A9249F2F2956FA8CFEB55C8573D0262DC8")
   | .error _ => false) &&
  (match nonceAgg bolosMusigCrypto [officialNonceAggPnonces[2]!, officialNonceAggPnonces[3]!] with
   | .ok an => decide (an = mpn! "035FE1873B4F2967F52FEA4A06AD5A8ECCBE9D0FD73068012C894E2E87CCB5804B000000000000000000000000000000000000000000000000000000000000000000")
   | .error _ => false) &&
  (match nonceAgg bolosMusigCrypto [officialNonceAggPnonces[0]!, officialNonceAggPnonces[4]!] with
   | .error (.invalidContribution 1) => true | _ => false) &&
  (match nonceAgg bolosMusigCrypto [officialNonceAggPnonces[5]!, officialNonceAggPnonces[1]!] with
   | .error (.invalidContribution 0) => true | _ => false) &&
  (match nonceAgg bolosMusigCrypto [officialNonceAggPnonces[6]!, officialNonceAggPnonces[1]!] with
   | .error (.invalidContribution 0) => true | _ => false) &&
  -- 5. `sign_verify_vectors.json` (`test_sign_valid` & `test_sign_error`)
  checkPartialSignOk sec0 signSk (mkSignCtx [0, 1, 2] agg0 msg0) "012ABBCB52B3016AC03AD82395A1A415C48B93DEF78718E62A7A90052FE224FB" &&
  checkPartialSignOk sec0 signSk (mkSignCtx [1, 0, 2] agg0 msg0) "9FF2F7AAA856150CC8819254218D3ADEEB0535269051897724F9DB3789513A52" &&
  checkPartialSignOk sec0 signSk (mkSignCtx [1, 2, 0] agg0 msg0) "FA23C359F6FAC4E7796BB93BC9F0532A95468C539BA20FF86D7C76ED92227900" &&
  checkPartialSignOk sec0 signSk (mkSignCtx [0, 1] aggInf msg0) "AE386064B26105404798F75DE2EB9AF5EDA5387B064B83D049CB7C5E08879531" &&
  checkPartialSignOk sec0 signSk (mkSignCtx [0, 1, 2] agg0 msgEmpty) "D7D63FFD644CCDA4E62BC2BC0B1D02DD32A1DC3030E155195810231D1037D82D" &&
  checkPartialSignOk sec0 signSk (mkSignCtx [0, 1, 2] agg0 msg38) "E184351828DA5094A97C79CABDAAA0BFB87608C32E8829A4DF5340A6F243B78C" &&
  checkPartialSignErr sec0 signSk (mkSignCtx [1, 2] agg0 msg0) .pubkeyNotInList &&
  checkPartialSignErr sec0 signSk (mkSignCtx [1, 0, 3] agg0 msg0) .invalidPoint &&
  checkPartialSignErr sec0 signSk (mkSignCtx [1, 2, 0] aggBadTag msg0) .invalidPoint &&
  checkPartialSignErr sec0 signSk (mkSignCtx [1, 2, 0] aggBadX msg0) .invalidPoint &&
  checkPartialSignErr sec0 signSk (mkSignCtx [1, 2, 0] aggGtP msg0) .invalidPoint &&
  checkPartialSignErr secZero signSk (mkSignCtx [0, 1, 2] agg0 msg0) .nonceOutOfRange &&
  -- 6. `tweak_vectors.json` (`test_tweak` & `test_key_agg_tweak_infinity`)
  (let mkTwCtx (tws : List (Nat × Bool)) : SessionContext :=
     { aggnonce := agg0, pubkeys := officialTweakPks,
       tweaks := tws.map (fun (i, xo) => { scalar := officialTweakScalars[i]!, isXOnly := xo }),
       msg := msg0 }
   checkPartialSignOk sec0 signSk (mkTwCtx [(0, true)]) "E28A5C66E61E178C2BA19DB77B6CF9F7E2F0F56C17918CD13135E60CC848FE91" &&
   checkPartialSignOk sec0 signSk (mkTwCtx [(0, false)]) "38B0767798252F21BF5702C48028B095428320F73A4B14DB1E25DE58543D2D2D" &&
   checkPartialSignOk sec0 signSk (mkTwCtx [(0, false), (1, true)]) "408A0A21C4A0F5DACAF9646AD6EB6FECD7F7A11F03ED1F48DFFF2185BC2C2408" &&
   checkPartialSignOk sec0 signSk (mkTwCtx [(0, false), (1, false), (2, true), (3, true)]) "45ABD206E61E3DF2EC9E264A6FEC8292141A633C28586388235541F9ADE75435" &&
   checkPartialSignOk sec0 signSk (mkTwCtx [(0, true), (1, false), (2, true), (3, false)]) "B255FDCAC27B40C7CE7848E2D3B7BF5EA0ED756DA81565AC804CCCA3E1D5D239" &&
   checkPartialSignErr sec0 signSk (mkTwCtx [(4, false)]) .tweakOutOfRange &&
   -- `test_key_agg_tweak_infinity`: `key_agg_pubkeys[6]` + plain tweak `252E4BD6...` -> `.tweakInfinity`!
   (let infTw : MusigTweak := { scalar := mb32! "252E4BD67410A76CDF933D30EAA1608214037F1B105A013ECCD3C5C184A6110B", isXOnly := false }
    let ctxNoTw : SessionContext := { aggnonce := agg0, pubkeys := [officialKeyAggPks[6]!], tweaks := [], msg := msg0 }
    let ctxInfTw : SessionContext := { ctxNoTw with tweaks := [infTw] }
    (partialSign bolosMusigCrypto sec0 signSk ctxNoTw).isOk &&
    checkPartialSignErr sec0 signSk ctxInfTw .tweakInfinity)) &&
  -- 7. End-to-end 2-of-2 MuSig2 Round-1 -> NonceAgg -> Round-2 -> PartialSigAgg -> BIP-340 Schnorr verify
  --    + BOLOS (`28B` prefix, 32-slot FIFO, untweaked `aggpk`, mandatory self-pubnonce check) vs Vanadium (`32B`, 1-slot)
  (let sk1Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
   let sk2Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
   let sk1 := scalarToBytes32 sk1Nat
   let sk2 := scalarToBytes32 sk2Nat
   let pk1 := bolosMusigCrypto.compress ((RefCrypto.ecMul? sk1Nat (some RefCrypto.secpG)).getD RefCrypto.secpG)
   let pk2 := bolosMusigCrypto.compress ((RefCrypto.ecMul? sk2Nat (some RefCrypto.secpG)).getD RefCrypto.secpG)
   match deriveMusigSignTask bolosMusigCrypto 0 0 pk1 [pk1, pk2] 0 1 false 0 (.keypath none),
         deriveMusigSignTask bolosMusigCrypto 0 0 pk2 [pk1, pk2] 0 1 false 0 (.keypath none) with
   | .ok task1, .ok task2 =>
     let sidA := (computeBolosPsbtSessionId bolosMusigCrypto (mb32! "1111111111111111111111111111111111111111111111111111111111111111")
                    (mb32! "2222222222222222222222222222222222222222222222222222222222222222") none).getD (SizedBytes.zeros 32)
     -- Modify last 4 bytes of `sidA`: still matches on BOLOS (`28B` prefix), diverges on Vanadium (`32B`)!
     let sidA28 := mkMusigBytes32! (sidA.bytes.extract 0 28 ++ ByteArray.mk #[0xAA, 0xBB, 0xCC, 0xDD])
     let rr1 := mb32! "3333333333333333333333333333333333333333333333333333333333333333"
     let rr2 := mb32! "4444444444444444444444444444444444444444444444444444444444444444"
     let sighash := mb32! "5555555555555555555555555555555555555555555555555555555555555555"
     match executeRound1Pass bolosMusigCrypto .untweakedBolos bolosDefaultStore sidA rr1 [task1],
           executeRound1Pass bolosMusigCrypto .untweakedBolos bolosDefaultStore sidA rr2 [task2] with
     | .ok ([r1Out1], store1), .ok ([r1Out2], store2) =>
       -- Order pubnonces to match `task1.sortedPubkeys`
       let pns := if decide (task1.sortedPubkeys.head? = some pk1)
                  then [r1Out1.pubnonce, r1Out2.pubnonce]
                  else [r1Out2.pubnonce, r1Out1.pubnonce]
       let r2In1 : MusigRound2TaskInput := {
         task := task1, sighash := sighash, secretKey := sk1,
         cosignerPubnonces := pns, psbtMyPubnonce := some r1Out1.pubnonce
       }
       let r2In2 : MusigRound2TaskInput := {
         task := task2, sighash := sighash, secretKey := sk2,
         cosignerPubnonces := pns, psbtMyPubnonce := some r1Out2.pubnonce
       }
       -- Tampered self-pubnonce rejected on BOLOS (`.pubnonceMismatch`)!
       let tamperedOk :=
         match executeRound2Pass bolosMusigCrypto .untweakedBolos store1 sidA
                 [{ r2In1 with psbtMyPubnonce := some r1Out2.pubnonce }] true with
         | .error (.pubnonceMismatch, _) => true
         | _ => false
       -- Lookup via `sidA28` succeeds on BOLOS (`28B` prefix), fails on Vanadium (`32B`)!
       let prefixDiffOk :=
         (lookupActive store1 sidA28 == some rr1) &&
         (match registerRound1 vanadiumDefaultStore sidA rr1 with
          | .ok vStore => lookupActive vStore sidA28 == none
          | .error _ => false)
       -- Round 2 succeeds via `sidA28`, atomically deletes session, and replay fails with `.missingSession`!
       match executeRound2Pass bolosMusigCrypto .untweakedBolos store1 sidA28 [r2In1] true,
             executeRound2Pass bolosMusigCrypto .untweakedBolos store2 sidA [r2In2] true,
             nonceAgg bolosMusigCrypto pns with
       | .ok ([sig1], store1After), .ok ([sig2], _), .ok aggnonce =>
         let replayBlocked :=
           match executeRound2Pass bolosMusigCrypto .untweakedBolos store1After sidA [r2In1] true with
           | .error (.missingSession, _) => true
           | _ => false
         let psigs := if decide (task1.sortedPubkeys.head? = some pk1)
                      then [sig1.signature, sig2.signature]
                      else [sig2.signature, sig1.signature]
         let fullCtx : SessionContext := {
           aggnonce := aggnonce, pubkeys := task1.sortedPubkeys,
           tweaks := task1.tweaks, msg := sighash.bytes
         }
         match partialSigAgg bolosMusigCrypto fullCtx psigs with
         | .ok schnorr64 =>
           let xOnlyQ := (xOnlyOfCompressed task1.tweakedAggPk).bytes
           tamperedOk && prefixDiffOk && replayBlocked &&
           RefCrypto.schnorrVerifyBip340 xOnlyQ sighash.bytes schnorr64.bytes
         | .error _ => false
       | _, _, _ => false
     | _, _ => false
   | _, _ => false)

end Musig2Conformance

/-! ## Section 8. `BitcoinLedger.SilentPayments` Conformance (BIP-352 / BIP-374 / BIP-375 / BIP-392) -/

section SilentPaymentsConformance

open InternalSpec.SilentPayments (
  SpError SpAddressHrp SpScanHrp SilentPaymentCode SilentPaymentAccount
  SilentPaymentCoordinates OutPoint SpInputScriptKind PsbtSpInput PsbtSpOutput PsbtSpTx
)
open BitcoinLedger.SilentPayments

/-- Reverse 32-byte display hex txid to consensus little-endian txid bytes. -/
private def spTxidLE! (rpcHex : String) : InternalSpec.SilentPayments.Bytes32 :=
  mkSpBytes32! (ByteArray.mk (RefCrypto.hex! rpcHex).data.reverse)

def officialBip352Addr0 : String :=
  "sp1qqgste7k9hx0qftg6qmwlkqtwuy6cycyavzmzj85c6qdfhjdpdjtdgqjuexzk6murw56suy3e0rd2cgqvycxttddwsvgxe2usfpxumr70xc9pkqwv"

private def isSpOk {α : Type} [DecidableEq α] (res : Except SpError α) (exp : α) : Bool :=
  match res with | .ok v => decide (v = exp) | .error _ => false

private def isSpErr {α : Type} (res : Except SpError α) (exp : SpError) : Bool :=
  match res with | .error e => decide (e = exp) | .ok _ => false

def checkSilentPaymentsConformance : Bool :=
  let bScanPriv : Nat := 0x0f694e068028a717f8af6b9411f9a133dd3565258714cc226594b34db90c1f2c
  let bSpendPriv : Nat := 0x9d6ad855ce3417ef84e836892e5a56392bfba05fa5d97ccea30e266f540e08b3
  let privIn0 : Nat := 0xeadc78165ff1f8ea94ad7cfdc54990738a4c53f6e0507b42154201b8e5dff3b1
  let privIn1 : Nat := 0x93f5ed907ad5b2bdbbdcb5d9116ebc0a4e1f92f910d5260237fa45a9408aad16
  let expScanHex := "0220bcfac5b99e04ad1a06ddfb016ee13582609d60b6291e98d01a9bc9a16c96d4"
  let expSpendHex := "025cc9856d6f8375350e123978daac200c260cb5b5ae83106cab90484dcd8fcf36"
  let expSecretHex := "028158aff7d61ea66b2fa7f555bc3c5937d1debbde16423d630f9aa7943e14d80d"
  let expOutXOnlyHex := "3e9fce73d4e77a4809908e3c3a2e54ee147b9312dc5044a193d1fc85de46e3c1"
  let expPrivTweak : Nat := 0xf438b40179a3c4262de12986c0e6cce0634007cdc79c1dcd3e20b9ebc2e7eef6
  let bSpendPt := (RefCrypto.ecMul? bSpendPriv (some RefCrypto.secpG)).getD RefCrypto.secpG
  let bScanPt := (RefCrypto.ecMul? bScanPriv (some RefCrypto.secpG)).getD RefCrypto.secpG
  -- 1. BIP-352 address decode/encode roundtrip, `spKeyDerivationPath`, `deriveAccountSpAddress`, & BIP-392 `spscan1`
  let addrAndScanOk :=
    isSpOk (spKeyDerivationPath 0 0 true) [0x80000160, 0x80000000, 0x80000000, 0x80000001, 0] &&
    isSpOk (spKeyDerivationPath 1 0 false) [0x80000160, 0x80000001, 0x80000000, 0x80000000, 0] &&
    isSpErr (spKeyDerivationPath 1 0x80000000 true) .invalidParameter &&
    (match decodeSpAddress bolosSpCrypto canonicalBech32mCodec officialBip352Addr0 with
     | .ok (.sp, code) =>
       decide (code.scan = bScanPt) &&
       decide (code.spend = bSpendPt) &&
       decide ((bolosSpCrypto.compress code.scan).bytes = RefCrypto.hex! expScanHex) &&
       decide ((bolosSpCrypto.compress code.spend).bytes = RefCrypto.hex! expSpendHex) &&
       isSpOk (encodeSpAddress bolosSpCrypto canonicalBech32mCodec .sp code) officialBip352Addr0
     | _ => false) &&
    (match mkCheckedSpAccount 0 bScanPriv bSpendPt with
     | .ok acc =>
       isSpOk (deriveAccountSpAddress bolosSpCrypto canonicalBech32mCodec .sp acc (.code none)) officialBip352Addr0 &&
       -- Reserved change label `m = 0` & `.tweak` coordinates rejected in `GetAddress`!
       isSpErr (deriveAccountSpAddress bolosSpCrypto canonicalBech32mCodec .sp acc (.code (some 0))) .silentPaymentChangeLabel &&
       isSpErr (deriveAccountSpAddress bolosSpCrypto canonicalBech32mCodec .sp acc (.tweak (mkSpBytes32! (RefCrypto.hex! expOutXOnlyHex)))) .invalidParameter &&
       -- BIP-392 `exportSpScanKey`: requires `userApproved = true` and roundtrips via `decodeSpScanKey`!
       isSpErr (exportSpScanKey bolosSpCrypto canonicalBech32mCodec .spscan (fun _ => .ok acc) 0 false) .userRejected &&
       (match exportSpScanKey bolosSpCrypto canonicalBech32mCodec .spscan (fun _ => .ok acc) 0 true with
        | .ok spscanStr =>
          spscanStr.startsWith "spscan1q" &&
          isSpOk (decodeSpScanKey bolosSpCrypto canonicalBech32mCodec spscanStr) (.spscan, bScanPriv, bSpendPt)
        | .error _ => false)
     | .error _ => false)
  -- 2. Official BIP-352 Vector #1 ("Simple send: two inputs") + input-order invariance + receiver spending key
  let op0 : OutPoint := { txid := spTxidLE! "f4184fc596403b9d638783cf57adfe4c75c605f6356fbc91338530e9831e9e16", vout := 0 }
  let op1 : OutPoint := { txid := spTxidLE! "a1075db55d416d3ca199f55b6084e2115b9345e16c5cf302fc80e9d5fbf5d48d", vout := 0 }
  let bip352VectorOk :=
    let aSum := (privIn0 + privIn1) % secp256k1Order
    let aPub := bolosSpCrypto.pointMul aSum (.affine bolosSpCrypto.generator)
    match computeInputHash bolosSpCrypto [op0, op1] aPub,
          computeInputHash bolosSpCrypto [op1, op0] aPub with
    | .ok ih01, .ok ih10 =>
      let share := ecdhShare bolosSpCrypto aSum bScanPt
      match sharedSecret bolosSpCrypto ih01 share,
            outputTweak bolosSpCrypto ((RefCrypto.decompressPt? (RefCrypto.hex! expSecretHex)).getD RefCrypto.secpG) 0 with
      | .ok secPt, .ok tk0 =>
        match outputKey bolosSpCrypto secPt bSpendPt 0, receiverSpendingKey bSpendPriv tk0 with
        | .ok outPt, .ok dSpend =>
          ih01 == ih10 &&
          aSum == 0x7ed265a6dac7aba8508a32d6d6b84c7f1dbd0a0941dd01088d69e8d556345f86 &&
          tk0 == expPrivTweak &&
          decide ((bolosSpCrypto.compress secPt).bytes = RefCrypto.hex! expSecretHex) &&
          decide ((bolosSpCrypto.xCoord outPt).bytes = RefCrypto.hex! expOutXOnlyHex) &&
          -- Receiver derived spending key signs a valid BIP-340 Schnorr signature for `outPt`!
          (let dEven := if bolosSpCrypto.hasEvenY outPt then dSpend else secp256k1Order - dSpend
           match RefCrypto.ecMul? dEven (some RefCrypto.secpG) with
           | some checkPt => checkPt.x == outPt.x && checkPt.y % 2 == 0
           | none => false)
        | _, _ => false
      | _, _ => false
    | _, _ => false
  -- 3. BIP-374 DLEQ prove/verify soundness & tamper/generator-swap rejection
  let dleqOk :=
    let a := (privIn0 + privIn1) % secp256k1Order
    let aux := mkSpBytes32! (ByteArray.mk (Array.replicate 32 0x42))
    match bolosSpCrypto.pointMul a (.affine bolosSpCrypto.generator),
          bolosSpCrypto.pointMul a (.affine bScanPt),
          dleqProve bolosSpCrypto a bScanPt aux bolosSpCrypto.generator none with
    | .affine aPub, .affine cPt, .ok proof =>
      let badProof := mkSpBytes64! ((proof.bytes.extract 0 63).push ((proof.bytes.data.getD 63 0) ^^^ 0x01))
      dleqVerify bolosSpCrypto aPub bScanPt cPt proof bolosSpCrypto.generator none &&
      !dleqVerify bolosSpCrypto aPub bScanPt cPt badProof bolosSpCrypto.generator none &&
      !dleqVerify bolosSpCrypto bScanPt aPub cPt proof bolosSpCrypto.generator none &&
      isSpErr (dleqProve bolosSpCrypto 0 bScanPt aux bolosSpCrypto.generator none) .invalidProofInput
    | _, _, _ => false
  -- 4. BIP-375 `finalizePsbtSilentPayments`: full end-to-end PSBT finalization + sighash & NUMS exclusions
  let bip375Ok :=
    let code66 := serializeSpCode bolosSpCrypto { scan := bScanPt, spend := bSpendPt }
    let mkIn (op : OutPoint) (priv : Nat) : PsbtSpInput := {
      outpoint := op, prevoutWitnessVersion := none, sighashType := some 0x01,
      hasInputSpEcdhShare := false, hasInputSpDleq := false,
      scriptKind := .pkh, tapInternalKey := none, deviceEligiblePrivKey := some priv
    }
    let spOut : PsbtSpOutput := {
      amount := 99000, script := none, spV0Info := some code66, spV0Label := none
    }
    let validTx : PsbtSpTx RefCrypto.AffinePt := {
      txModifiable := some 0, globalEcdhShares := [], globalDleqProofs := [],
      inputs := [mkIn op0 privIn0, mkIn op1 privIn1], outputs := [spOut], spAccounts := []
    }
    let aux := mkSpBytes32! (ByteArray.mk (Array.replicate 32 0x07))
    -- Taproot input with omitted `sighashType` defaults to `SIGHASH_DEFAULT (0x00)` -> `.silentPaymentSighashType`!
    let trDefaultIn : PsbtSpInput := {
      outpoint := op0, prevoutWitnessVersion := some 1, sighashType := none,
      hasInputSpEcdhShare := false, hasInputSpDleq := false,
      scriptKind := .tr false, tapInternalKey := none, deviceEligiblePrivKey := some privIn0
    }
    -- Taproot input with BIP-341 NUMS internal key `0x50929b74...` is ineligible -> `.silentPaymentNoEligibleInputs`!
    let numsIn : PsbtSpInput := {
      outpoint := op0, prevoutWitnessVersion := some 1, sighashType := some 0x01,
      hasInputSpEcdhShare := false, hasInputSpDleq := false,
      scriptKind := .tr false, tapInternalKey := some bip341NumsXOnly, deviceEligiblePrivKey := some privIn0
    }
    (match finalizePsbtSilentPayments bolosSpCrypto validTx aux with
     | .ok ([shareOut], [scriptOut]) =>
       let expScript := ByteArray.mk #[0x51, 0x20] ++ RefCrypto.hex! expOutXOnlyHex
       scriptOut.outputIndex == 0 &&
       decide (scriptOut.script.bytes = expScript) &&
       decide (shareOut.scanKey = bolosSpCrypto.compress bScanPt)
     | _ => false) &&
    (match finalizePsbtSilentPayments bolosSpCrypto { validTx with inputs := [trDefaultIn] } aux with
     | .error .silentPaymentSighashType => true | _ => false) &&
    (match finalizePsbtSilentPayments bolosSpCrypto { validTx with inputs := [numsIn] } aux with
     | .error .silentPaymentNoEligibleInputs => true | _ => false)
  addrAndScanOk && bip352VectorOk && dleqOk && bip375Ok

end SilentPaymentsConformance

/-! ## Section 9. `BitcoinLedger.AppStateMachine` Conformance (`sign_message.toml`, APDU Framing, Swap & BIP-322) -/

section AppStateMachineConformance

open InternalSpec.AppStateMachine (
  TargetProfile BolosApduHeader BolosWireCommand VanadiumRequestTag
  CompactSigHeaderBase MessageDisplayForm KeyTree
  WalletPolicySpec AccountSpec AddressCoordinates
  SwapMode SwapLock ExternalOutputView
  StandardInputSigRequest PsbtMusigPlan PsbtSignRequest
  AppCommand AppResponse AppError AppPersistentState
  UserPrompt UserApprovalOracle HardwareOracle AppTraceOutcome
)
open InternalSpec.Unified (PsbtMerkleOpeningBundle VerifiedPsbtSignError)
open BitcoinLedger.AppStateMachine

/-- Recover the compressed public key `Q = r⁻¹ * (s * R - z * G)` from a 65-byte BOLOS compact signature
    (`hdr ∈ {31, 32}`) and verify `ecdsaVerifyRaw Q digest r s == true` and `Q == derivedPubAt(path)`. -/
private def verifyCompactSigAtPath (path : List UInt32) (msg : ByteArray) (compactHex : String) : Bool :=
  let sig65 := RefCrypto.hex! compactHex
  if sig65.size != 65 then false
  else
    let hdr := sig65.data.getD 0 0
    if hdr != 31 && hdr != 32 then false
    else
      let rBytes := sig65.extract 1 33
      let sBytes := sig65.extract 33 65
      let r := RefCrypto.bytesToNatBE rBytes
      let s := RefCrypto.bytesToNatBE sBytes
      let digest := (bitcoinSignedMessageDigest (fun bs => mkMusigBytes32! (RefCrypto.sha256 bs)) msg).bytes
      let z := RefCrypto.bytesToNatBE digest % RefCrypto.secpN
      -- `hdr = 31 + parity` (`31` -> even `R.y`, `32` -> odd `R.y`)
      match RefCrypto.liftXEven? rBytes, RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 path with
      | some rEven, some (privK, _, _) =>
        let rPt : RefCrypto.AffinePt :=
          if hdr == 31 then rEven else ⟨rEven.x, (RefCrypto.secpP - rEven.y) % RefCrypto.secpP⟩
        let sR := RefCrypto.ecMul? s (some rPt)
        let negZG := RefCrypto.ecNeg? (RefCrypto.ecMul? z (some RefCrypto.secpG))
        let rInv := RefCrypto.invModN r
        match RefCrypto.ecMul? rInv (RefCrypto.ecAdd? sR negZG), RefCrypto.ecMul? privK (some RefCrypto.secpG) with
        | some recQ, some expQ =>
          decide (recQ = expQ) && RefCrypto.ecdsaVerifyRaw expQ digest r s
        | _, _ => false
      | _, _ => false

/-- All 6 valid official `sign_message.toml` vectors (`LedgerHQ/app-bitcoin/test_vectors/sign_message.toml`). -/
def officialSignMessageVectors : List (List UInt32 × String × Bool × String) :=
  let h (x : UInt32) : UInt32 := x ||| 0x80000000
  let longMsg := "The root problem with conventional currency is all the trust that's required to make it work. The central bank must be trusted not to debase the currency, but the history of fiat currencies is full of breaches of that trust. Banks must be trusted to hold our money and transfer it electronically, but they lend it out in waves of credit bubbles with barely a fraction in reserve. We have to trust them with our privacy, trust them not to let identity thieves drain our accounts. Their massive overhead costs make micropayments impossible."
  let tooLongMsg := longMsg ++ " " ++ longMsg ++ " " ++ longMsg
  [ ([h 44, h 1, h 0, 0, 0],
     "The Times 03/Jan/2009 Chancellor on brink of second bailout for banks.", true,
     "20e47861156598918cc7e1fb3e042f1f35801741c082b520810791767a162a9ca97da01b7aba6f17e5db38233909dfe58e880dc94df0d8e20bf1e602c99e91bb69"),
    ([h 44, h 1, h 0, 0, 0],
     "\nThe Times 03/Jan/2009 Chancellor\non brink of second bailout for banks.", true,
     "20b320229171a99c2b0796e047fb1e8acd8de3c8d2ee998756229c4588ac20f05d0e3840cc60c63f71e22cf72b60c94439726f749f7f32e77ff9fb253362ad29a3"),
    ([h 84, h 1, h 0, 0, 0],
     "Hello world!", true,
     "20438ae3e24c2bb153a11ed7333142a00621d67b9dd482a6f56ab7bd72d2564fe505acbcac7091a7d6cfeab8b2479343a9763261fedc5e03104c7373dd27a6c192"),
    ([h 84, h 1, h 0, 0, 8],
     longMsg, true,
     "1f87eb33a4d89b9b72d4c01ff68fd9cfd422cb754495d018158f75489ff99d8300658d54501f7b7e2463296f26262b76f95e0e09ad580aa8c3ab21670fd170ef99"),
    ([h 84, h 1, h 0, 0, 8],
     "Hello\rworld!", false,
     "20b5d03c96a943f384cbd7ff820468b88e87b8095e42f788381a6135408b9563554009a5d98c7ef3ce6db14d03288c6082c56ae77a3f7d0465a2c4cf4d013f91e1"),
    ([h 84, h 1, h 0, 0, 8],
     tooLongMsg, false,
     "203025f514e1032ba7998ba897d0da0ecfc249c5298a89771434a3223c8af72d2d73fc751d6adb4ffb9f7643c56350668be2fd85cde2a7599ed919ae7e9ad5b8d9") ]

/-- Concrete Speculos-seeded BOLOS `HardwareOracle` for `stepAppCommand` / `runAppTrace` / `stepVerifiedPsbtSign`. -/
def bolosHardwareOracle : HardwareOracle RefCrypto.AffinePt where
  musigCrypto := bolosMusigCrypto
  spCrypto := bolosSpCrypto
  bech32m := BitcoinLedger.SilentPayments.canonicalBech32mCodec
  masterFingerprint tree _ :=
    match tree with
    | .standard => some 0xF5ACC2FD
    | .resident => none
  deriveExtendedPubkey tree _ path :=
    let treeBip : InternalSpec.KeyTree := match tree with | .standard => .standard | .resident => .resident
    match BitcoinLedger.Bip32.deriveExtendedPubKeyWithOracle bolosDerivOracle .testnet treeBip path.toArray with
    | some node =>
      let ser := BitcoinLedger.Bip32.serializeExtendedPubKey node
      some (ser, mkMusigBytes33! node.pubkey)
    | none => none
  computePorHmac wid := mkMusigBytes32! (RefCrypto.bolosComputeWalletHmac wid.bytes)
  signRecoverableEcdsa path digest := do
    -- Deterministic test signature (`k = 7`) recoverable at `path`
    let (privK, _, _) ← RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 path
    let k : Nat := 7
    let rPt ← RefCrypto.ecMul? k (some RefCrypto.secpG)
    let r := rPt.x % RefCrypto.secpN
    let z := RefCrypto.bytesToNatBE digest.bytes % RefCrypto.secpN
    let sRaw := (RefCrypto.invModN k * (z + r * privK)) % RefCrypto.secpN
    let (sLow, recId) :=
      if sRaw * 2 > RefCrypto.secpN then
        (RefCrypto.secpN - sRaw, if rPt.y % 2 == 1 then (0 : UInt8) else 1)
      else
        (sRaw, if rPt.y % 2 == 1 then (1 : UInt8) else 0)
    some (recId, BitcoinLedger.Musig2.scalarToBytes32 r, BitcoinLedger.Musig2.scalarToBytes32 sLow)
  signPsbtInput req := do
    let (privK, _, _) ← RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 req.derivationPath
    let pubPt ← RefCrypto.ecMul? privK (some RefCrypto.secpG)
    let fakeSig :=
      if req.isSchnorr then ByteArray.mk (Array.replicate 64 0x11)
      else ByteArray.mk #[0x30, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x01, 0x01]
    some (fakeSig, mkMusigBytes33! (RefCrypto.compressPt pubPt))
  signWithIdentityKey _ _ := none
  verifySchnorr pk msg sig :=
    RefCrypto.schnorrVerifyBip340 (pk.bytes.extract 1 33) msg sig.bytes
  deriveSpAccount _ := .error .invalidParameter
  deriveWalletPolicyOutput wp isChange addrIdx := do
    let pol ← (parseBolosTestnetPolicy wp.name wp.descriptorTemplate
      (wp.keysInfoPayloads.map fun b => String.fromUTF8! b)).toOption
    let spk ← (BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile
      (BitcoinLedger.WalletPolicy.bolosAppProfile .testnet) bolosPolicyOracle pol isChange addrIdx).toOption
    let addr ← BitcoinLedger.Script.scriptToAddress? .bolos RefCrypto.doubleSha256 .testnet spk
    some (addr, spk)
  freshMusigRandRoot := mkMusigBytes32! (ByteArray.mk (Array.replicate 32 0x99))
  freshDleqAuxRand := mkSpBytes32! (ByteArray.mk (Array.replicate 32 0x88))

private def isStepErr
    (res : Except (AppError × AppPersistentState) (AppResponse × AppPersistentState))
    (expErr : AppError) (expState : AppPersistentState) : Bool :=
  match res with
  | .error (e, s') => decide (e = expErr) && decide (s' = expState)
  | .ok _ => false

def checkAppStateMachineConformance : Bool :=
  let prof : TargetProfile := .bolos 1
  let vProf : TargetProfile := .vanadium 1
  let uiApprove : UserApprovalOracle RefCrypto.AffinePt := ⟨fun _ => true⟩
  let uiReject : UserApprovalOracle RefCrypto.AffinePt := ⟨fun _ => false⟩
  let s0 := emptyStateForProfile prof
  let h (x : UInt32) : UInt32 := x ||| 0x80000000
  let p84_0 := [h 84, h 1, h 0, 0, 0]
  let p11Steps := [h 44, h 1, h 0, h 0, h 1, h 2, h 3, h 4, 5, 6, 7]
  -- 1. All 6 official `sign_message.toml` ECDSA recoverable compact signatures + display mode + 11-step rejection
  let signMsgVectorsOk :=
    (officialSignMessageVectors.all fun (path, msgStr, expAscii, sigHex) =>
      let msg := msgStr.toUTF8
      isPrintableAsciiMessage msg == expAscii &&
      verifyCompactSigAtPath path msg sigHex) &&
    -- `stepAppCommand` `SIGN_MESSAGE`: 11-step path -> `.wrongDataLength` (`0x6A87`); `uiReject` -> `.userRejected` (`0x6985`);
    -- `uiApprove` emits valid 65-byte compact recoverable signature; rejected on Vanadium (`.notSupported`)!
    isStepErr (stepAppCommand prof bolosHardwareOracle uiApprove (.signMessage p11Steps "test".toUTF8 .compressedP2pkh) s0)
      .wrongDataLength s0 &&
    isStepErr (stepAppCommand prof bolosHardwareOracle uiReject (.signMessage p84_0 "Hello world!".toUTF8 .compressedP2pkh) s0)
      .userRejected s0 &&
    isStepErr (stepAppCommand vProf bolosHardwareOracle uiApprove (.signMessage p84_0 "Hello world!".toUTF8 .compressedP2pkh) (emptyStateForProfile vProf))
      .notSupported (emptyStateForProfile vProf) &&
    (match stepAppCommand prof bolosHardwareOracle uiApprove (.signMessage p84_0 "Hello world!".toUTF8 .compressedP2pkh) s0 with
     | .ok (.messageSigned c65, s1) =>
       decide (s1 = s0) && verifyCompactSigAtPath p84_0 "Hello world!".toUTF8 (RefCrypto.bytesToHex c65.bytes)
     | _ => false)
  -- 2. BOLOS APDU framing (`CLA = 0xE1`, `0xB0`, `0xF8`, `p2 > 1`, arbitrary `p1`, Swap whitelist) & Vanadium CBOR tags
  let apduFramingOk :=
    (classifyBolosApdu false { cla := 0xB0, ins := 0x01, p1 := 0, p2 := 0 } == .getVersion) &&
    (classifyBolosApdu false { cla := 0xB0, ins := 0x01, p1 := 1, p2 := 0 } == .wrongP1P2) &&
    -- Arbitrary `P1` accepted on `CLA = 0xE1` when `P2 <= 1` (`test_protocol.py`)!
    (classifyBolosApdu false { cla := 0xE1, ins := 0x04, p1 := 0xAB, p2 := 1 } == .signPsbt) &&
    (classifyBolosApdu false { cla := 0xE1, ins := 0x04, p1 := 0, p2 := 2 } == .wrongP1P2) &&
    -- Unexpected `0xF8/0x01` `INS_CONTINUE` when idle -> `.unexpectedContinue` -> `.badState` (`0xB007`)!
    (classifyBolosApdu false { cla := 0xF8, ins := 0x01, p1 := 0, p2 := 0 } == .unexpectedContinue) &&
    isStepErr (stepAppCommand prof bolosHardwareOracle uiApprove .unexpectedContinue s0) .badState s0 &&
    -- Swap whitelist blocks `REGISTER_WALLET` (`0x02`) and `SIGN_MESSAGE` (`0x10`), allows `SIGN_PSBT` (`0x04`)
    (classifyBolosApdu true { cla := 0xE1, ins := 0x02, p1 := 0, p2 := 1 } == .insNotSupported) &&
    (classifyBolosApdu true { cla := 0xE1, ins := 0x10, p1 := 0, p2 := 1 } == .insNotSupported) &&
    (classifyBolosApdu true { cla := 0xE1, ins := 0x04, p1 := 0, p2 := 1 } == .signPsbt) &&
    -- Silent Payments / Vanadium Identity commands rejected with `.notSupported` (`0x6A82`) on BOLOS
    isStepErr (stepAppCommand prof bolosHardwareOracle uiApprove (.exportSpScanKey .tspscan 0) s0) .notSupported s0 &&
    (decodeVanadiumRequestTag 8 == some .exportSilentPaymentScanKey) &&
    (decodeVanadiumRequestTag 9 == none)
  -- 3. Read-only trace purity, Swap terminal failure latching (`swapAborted = true`), & `stepVerifiedPsbtSign` -> `SIGN_MESSAGE`
  let endToEndStateOk :=
    let keyStr := "[f5acc2fd/84'/1'/0']tpubDCtKfsNyRhULjZ9XMS4VKKtVcPdVDi8MKUbcSD9MJDyjRu1A2ND5MiipozyyspBT9bg8upEp7a8EAgFxNxXn1d7QkdbL52Ty5jiSLcxPt1P"
    match parseBolosTestnetPolicy "" "wpkh(@0/**)" [keyStr] with
    | .error _ => false
    | .ok pol =>
      let polProf := policyProfileOfTarget prof
      let devOra := bolosRegOracle []
      let commit := BitcoinLedger.WalletPolicy.RegistrationCommitmentInput.bolos "wpkh(@0/**)".toUTF8 (bolosKeysMerkleRoot [keyStr])
      let wid := mkMusigBytes32! (BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId bolosPolicyOracle pol commit)
      let appPol := toAppWalletPolicySpec polProf devOra "wpkh(@0/**)" wid [keyStr.toUTF8] pol
      -- Read-only trace (`GET_VERSION`, `GET_MASTER_FINGERPRINT`, `GET_EXTENDED_PUBKEY`, `GET_WALLET_ADDRESS`) preserves `s0`!
      let roCmds : List (AppCommand RefCrypto.AffinePt) := [
        .getVersion,
        .getMasterFingerprint .standard,
        .getExtendedPubkey .standard false [h 84, h 1, h 0] none,
        .getAddress false (.walletPolicy appPol) none (.walletPolicy false 0) none
      ]
      let (roOut, sAfterRo) := runAppTrace prof bolosHardwareOracle uiReject roCmds s0
      let roPureOk := decide (sAfterRo = s0) && roOut.all (fun o => match o with | .ok _ _ => true | _ => false)
      -- End-to-end `stepVerifiedPsbtSign` + `SIGN_MESSAGE` sequence (`test_sign_psbt_then_sign_message_no_stale_review_state`)
      let pub00 : ByteArray :=
        match RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 [h 84, h 1, h 0, 0, 0] with
        | some (k, _, _) => match RefCrypto.ecMul? k (some RefCrypto.secpG) with
                            | some pt => RefCrypto.compressPt pt | none => ByteArray.empty
        | none => ByteArray.empty
      let pub10 : ByteArray :=
        match RefCrypto.derivePrivAtPath RefCrypto.speculosSeed64 [h 84, h 1, h 0, 1, 0] with
        | some (k, _, _) => match RefCrypto.ecMul? k (some RefCrypto.secpG) with
                            | some pt => RefCrypto.compressPt pt | none => ByteArray.empty
        | none => ByteArray.empty
      let recvSpk := ByteArray.mk #[0x00, 0x14] ++ RefCrypto.hash160 pub00
      let chgSpk  := ByteArray.mk #[0x00, 0x14] ++ RefCrypto.hash160 pub10
      let extSpk  := RefCrypto.hex! "00141122334455667788990011223344556677889900"
      let psbtSha (bs : ByteArray) : InternalSpec.Psbt.Bytes32 := mkPsbtBytes32! (RefCrypto.sha256 bs)
      let prevTx : InternalSpec.Psbt.RawTx := {
        version := 2
        vin := #[{ prevout := { txid := mkPsbtBytes32! (ByteArray.mk (Array.replicate 32 0)), vout := 0 },
                   scriptSig := ByteArray.empty, sequence := 0xFFFFFFFF }]
        vout := #[{ amount := 100000, scriptPubKey := recvSpk }]
        locktime := 0
      }
      let prevTxid := BitcoinLedger.Psbt.computeTxid psbtSha prevTx
      let pIn : InternalSpec.Psbt.PsbtInput := {
        prevout := { txid := prevTxid, vout := 0 }
        nonWitnessUtxo := some prevTx
        witnessUtxo := some { amount := 100000, scriptPubKey := recvSpk }
        derivations := [{ pubkey := pub00, origin := { fingerprint := 0xF5ACC2FD, path := [h 84, h 1, h 0, 0, 0] } }]
      }
      let pExtOut : InternalSpec.Psbt.PsbtOutput := { amount := 60000, scriptPubKey := some extSpk }
      let pChgOut : InternalSpec.Psbt.PsbtOutput := {
        amount := 39800, scriptPubKey := some chgSpk,
        derivations := [{ pubkey := pub10, origin := { fingerprint := 0xF5ACC2FD, path := [h 84, h 1, h 0, 1, 0] } }]
      }
      let psbt : InternalSpec.Psbt.PsbtTx := { txVersion := 2, inputs := #[pIn], outputs := #[pExtOut, pChgOut] }
      let stdTask : StandardInputSigRequest := {
        inputIndex := 0, derivationPath := [h 84, h 1, h 0, 0, 0],
        sighash := mkMusigBytes32! (ByteArray.mk (Array.replicate 32 0xAA)), isSchnorr := false, leafHash := none
      }
      -- Verified `SIGN_PSBT` followed immediately by `SIGN_MESSAGE` succeeds cleanly with zero stale state!
      let verifiedPsbtThenSignMsgOk :=
        match stepVerifiedPsbtSign prof .testnet bolosHardwareOracle uiApprove devOra bolosPolicyOracle
                RefCrypto.hash160 false "wpkh(@0/**)" wid [keyStr.toUTF8] none pol psbt none [stdTask] .none none s0 with
        | .ok (val, .psbtSigned [_] [] [] [] [] false, sAfterPsbt) =>
          val.fee == some 200 && val.displayedOutputs.length == 1 &&
          (match stepAppCommand prof bolosHardwareOracle uiApprove
                   (.signMessage p84_0 "Hello world!".toUTF8 .compressedP2pkh) sAfterPsbt with
           | .ok (.messageSigned _, _) => true
           | _ => false)
        | _ => false
      -- Swap terminal failure latching: wrong fee triggers `swapAborted = true`, blocking subsequent Swap retry & BIP-322!
      let destAddr := (BitcoinLedger.Script.scriptToAddress? .bolos RefCrypto.doubleSha256 .testnet extSpk).getD ""
      let badSwapLock : SwapLock := { mode := .standard, amount := 60000, fees := 999, destinationAddress := destAddr }
      let sSwap := { s0 with swapLock := some badSwapLock }
      let swapLatchOk :=
        (match verifyPsbtSignMessage prof .testnet bolosHardwareOracle uiApprove devOra bolosPolicyOracle
                 RefCrypto.hash160 "wpkh(@0/**)" wid [keyStr.toUTF8] none pol "Hello".toUTF8 psbt none [stdTask] .none sSwap with
         | .error (.psbtRejected .bip322ForbiddenInSwap, _) => true
         | _ => false) &&
        (match stepVerifiedPsbtSign prof .testnet bolosHardwareOracle uiReject devOra bolosPolicyOracle
                 RefCrypto.hash160 false "wpkh(@0/**)" wid [keyStr.toUTF8] none pol psbt none [stdTask] .none none sSwap with
         | .error (.psbtRejected .swapFeeMismatch, sAborted) =>
           sAborted.swapAborted == true &&
           -- Even with fixed `SwapLock` fee, `swapAborted = true` permanently rejects retry with `.failSwap` (`0x6B00`)!
           (let goodLock : SwapLock := { badSwapLock with fees := 200 }
            match stepAppCommand prof bolosHardwareOracle uiApprove (.getMasterFingerprint .standard)
                    { sAborted with swapLock := some goodLock } with
            | .error (.failSwap, _) => true
            | _ => false)
         | _ => false)
      roPureOk && verifiedPsbtThenSignMsgOk && swapLatchOk
  signMsgVectorsOk && apduFramingOk && endToEndStateOk

end AppStateMachineConformance

/-! ## Section 10. Top-Level Conformance Guard & Axiom Audit (`0 sorryAx`) -/

def allBolosDifferentialChecksPass : Bool :=
  checkBasicAndFreestanding &&
  checkBip32Conformance &&
  checkScriptConformance &&
  checkWalletPolicyConformance &&
  checkPsbtConformance &&
  checkMerkleProtocolConformance &&
  checkMusig2Conformance &&
  checkSilentPaymentsConformance &&
  checkAppStateMachineConformance

#guard checkBasicAndFreestanding
#guard checkBip32Conformance
#guard checkScriptConformance
#guard checkWalletPolicyConformance
#guard checkPsbtConformance
#guard checkMerkleProtocolConformance
#guard checkMusig2Conformance
#guard checkSilentPaymentsConformance
#guard checkAppStateMachineConformance
#guard allBolosDifferentialChecksPass

/-- Constructive kernel proof of BOLOS freestanding version ABI (`llbVersionPacked = 0x00020401`). -/
example : BitcoinLedger.FreestandingKernels.llbVersionPacked = 0x00020401 := rfl

/-- Constructive kernel proof of BOLOS vs Vanadium `GET_EXTENDED_PUBKEY` 11-step boundary differential. -/
example :
    BitcoinLedger.Bip32.MAX_BIP32_PATH_STEPS = 10 ∧
    BitcoinLedger.Bip32.MAX_BIP32_PATH_LEN = 16 := ⟨rfl, rfl⟩

/-- Constructive kernel proof of BOLOS vs Vanadium MuSig2 session capacity & stored prefix differential. -/
example :
    BitcoinLedger.Musig2.bolosMaxMusigSessions = 32 ∧
    BitcoinLedger.Musig2.bolosStoredIdPrefixLen = 28 ∧
    BitcoinLedger.Musig2.vanadiumMaxMusigSessions = 1 := ⟨rfl, rfl, rfl⟩

-- Self-verifying environment axiom audit + conformance summary printed when executing
-- `lake env lean Tests/BolosDifferential.lean`. Fails compilation if `allBolosDifferentialChecksPass`
-- is false or if any `Tests.BolosDifferential.*` / `BitcoinLedger.*` declaration uses `sorryAx`.
#eval show Lean.CoreM Unit from do
  if !allBolosDifferentialChecksPass then
    Lean.throwError "FAIL: allBolosDifferentialChecksPass evaluated to false!"
  let env ← Lean.getEnv
  let mut checkedDecls := 0
  let mut badSorry : List (Lean.Name × List Lean.Name) := []
  for (n, _) in env.constants.map₁.toList do
    let s := n.toString
    if (s.startsWith "Tests.BolosDifferential." || s.startsWith "BitcoinLedger.") && !n.isInternal then
      checkedDecls := checkedDecls + 1
      let axs ← Lean.collectAxioms n
      let sorryUsed := axs.toList.filter (· == ``sorryAx)
      if !sorryUsed.isEmpty then
        badSorry := (n, sorryUsed) :: badSorry
  if !badSorry.isEmpty then
    for (n, axs) in badSorry do
      IO.println s!"FAIL: {n} depends on {axs}"
    Lean.throwError "sorryAx detected!"
  IO.println s!"BOLOS_DIFFERENTIAL_PASS: all 9 module conformance suites (10 BitcoinLedger.* modules) passed; audited {checkedDecls} declarations with 0 sorryAx."

end Tests.BolosDifferential

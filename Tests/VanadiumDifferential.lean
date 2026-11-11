import BitcoinLedger

/-!
# `Tests.VanadiumDifferential` — Pure Lean Vanadium Differential & Upstream-Bug Regression Suite

Executable differential test suite and formal upstream-bug regression suite for
`BitcoinLedger.*` against `LedgerHQ/vanadium` (`apps/bitcoin`, commit
`ace8e96982408959dea9e7fbc59ee36e8c54e645`):

1. **Pure Executable Reference Crypto Engine**:
   - FIPS 180-4 SHA-256 & SHA-512, RFC 2104 HMAC-SHA256 & HMAC-SHA512, RIPEMD-160, HASH160,
     BIP-340 tagged hashes, and affine secp256k1 EC arithmetic (`p = 2^256 - 2^32 - 977`),
     instantiating `InternalSpec.CryptoDerivationOracle`, `InternalSpec.WalletPolicy.CryptoPolicyOracle`,
     `InternalSpec.Psbt.CryptoOracles`, `InternalSpec.Musig2.MusigCrypto`, `InternalSpec.SilentPayments.SpCrypto`,
     and `InternalSpec.AppStateMachine.HardwareOracle` with zero external FFI dependencies.

2. **Part A — Official Vanadium `apps/bitcoin` Differential Test Vectors**:
   - BIP-32 `GET_EXTENDED_PUBKEY` (`KeyTree::Standard` & `KeyTree::Resident`), Base58Check
     `tpub` decoding/re-encoding, `CKDpub` child derivation, and path security classification;
   - BIP-388 Wallet Policies, `NAMED_ACCOUNT` Proof-of-Registration (`RegistrationId` + SLIP-21
     HMAC), and exact Vanadium testnet address derivation (`tb1qzdr7s2sr0dwmkwx033r4nujzk86u0cy6fmzfjk`);
   - BIP-341 Taproot keypath, BIP-327/328 `tr(musig(@0,@1)/**)` (`5120c1fdfebed0...`), and
     multipath `Simple inheritance` TapTree policies (`TapLeaf`, sorted `TapBranch`, `TapTweak`,
     BIP-341 NUMS internal key);
   - BIP-379 Miniscript parsing, typechecking, and script compilation across combinators & wrappers;
   - BIP-174/370 PSBTv0-to-PSBTv2 normalization, UTXO validation, change elimination, fee checks,
     and exact BIP-341 `TapSighash` (`75c96fb06a12db4cd011d8c95a5995db758a4f2837a22f30f0f579619a4466f3`)
     + BIP-340 Schnorr verification from `sign_psbt/tests/basic.rs`;
   - Two-round BIP-327 MuSig2 session lifecycle, BIP-352/374/375/392 Silent Payments, and
     BIP-137 / BIP-322 message signing.

3. **Part B — Explicit Regression Proofs & Evaluations for All 9 Cataloged Vanadium Bugs**:
   - `VND-BUG-001` through `VND-BUG-009` from `docs/spec-cards/vanadium-upstream-bugs.md`,
     proving (`theorem`, `0 sorry`) and evaluating (`#guard` + `#eval`) that `BitcoinLedger.*`
     handles every single bug vector safely without panic, overflow, or policy bypass.
-/

namespace Tests.VanadiumDifferential

/-! ## Section 0: Hex Codec & Pure Reference Cryptographic Primitives -/

def hexNibble? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b - 0x61 + 10)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b - 0x41 + 10)
  else none

def hexDecodeLoop : List UInt8 → Array UInt8 → ByteArray
  | hi :: lo :: rest, acc =>
      match hexNibble? hi, hexNibble? lo with
      | some h, some l => hexDecodeLoop rest (acc.push ((h <<< 4) ||| l))
      | _, _ => ByteArray.mk acc
  | _, acc => ByteArray.mk acc

def hex! (s : String) : ByteArray :=
  hexDecodeLoop s.toUTF8.data.toList #[]

def toHex (bs : ByteArray) : String :=
  let hexChars : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let chars := bs.data.toList.flatMap fun (b : UInt8) =>
    let hi := hexChars[(b.toNat >>> 4)]?.getD '0'
    let lo := hexChars[(b.toNat &&& 0x0F)]?.getD '0'
    [hi, lo]
  String.ofList chars

local instance {ε α : Type} [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

local instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b =>
      if h : a = b then isTrue (congrArg Except.ok h)
      else isFalse (by intro hEq; injection hEq; exact h ‹_›)
  | .error e1, .error e2 =>
      if h : e1 = e2 then isTrue (congrArg Except.error h)
      else isFalse (by intro hEq; injection hEq; exact h ‹_›)
  | .ok _, .error _ => isFalse (by intro hEq; cases hEq)
  | .error _, .ok _ => isFalse (by intro hEq; cases hEq)

local instance : BEq InternalSpec.Psbt.TxOut := ⟨BitcoinLedger.Psbt.eqTxOut⟩

def isPsbtErr {α : Type} (res : Except InternalSpec.Psbt.PsbtError α) (expected : InternalSpec.Psbt.PsbtError) : Bool :=
  match res with
  | .error e => e == expected
  | .ok _ => false

def mkSizedBytes! (n : Nat) (bs : ByteArray) : InternalSpec.Musig2.SizedBytes n :=
  if h : bs.size = n then
    ⟨bs, h⟩
  else
    InternalSpec.Musig2.SizedBytes.zeros n

def mkSpSizedBytes! (n : Nat) (bs : ByteArray) : InternalSpec.SilentPayments.SizedBytes n :=
  if h : bs.size = n then
    ⟨bs, h⟩
  else
    InternalSpec.SilentPayments.SizedBytes.zeros n

def mkPsbtBytes32! (bs : ByteArray) : InternalSpec.Psbt.Bytes32 :=
  if h : bs.size = 32 then
    ⟨bs, h⟩
  else
    InternalSpec.Psbt.zeroBytes32

/-! ### Pure FIPS 180-4 SHA-256 & RFC 2104 HMAC-SHA256 -/

@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

def sha256Compress (h : Array UInt32) (block : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut w := Array.replicate 64 (0 : UInt32)
  for i in [0:16] do
    let b0 := (block.data[offset + 4 * i]?.getD 0).toUInt32
    let b1 := (block.data[offset + 4 * i + 1]?.getD 0).toUInt32
    let b2 := (block.data[offset + 4 * i + 2]?.getD 0).toUInt32
    let b3 := (block.data[offset + 4 * i + 3]?.getD 0).toUInt32
    w := w.set! i ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
  for i in [16:64] do
    let w15 := w[i - 15]!
    let w2  := w[i - 2]!
    let s0 := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for i in [0:64] do
    let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := hh + s1 + ch + sha256K[i]! + w[i]!
    let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + maj
    hh := g; g := f; f := e; e := d + temp1
    d := c; c := b; b := a; a := temp1 + temp2
  #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
    h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def sha256Bytes (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let rem := (msg.size + 1) % 64
  let padZeros := if rem ≤ 56 then 56 - rem else 120 - rem
  let mut padded := msg.data.push 0x80
  for _ in [0:padZeros] do
    padded := padded.push 0x00
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    padded := padded.push ((bitLen >>> UInt64.ofNat shift).toUInt8)
  let paddedBa := ByteArray.mk padded
  let nBlocks := paddedBa.size / 64
  let mut h : Array UInt32 := #[
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ]
  for blk in [0:nBlocks] do
    h := sha256Compress h paddedBa (blk * 64)
  let mut out : Array UInt8 := Array.mkEmpty 32
  for word in h do
    out := out.push ((word >>> 24).toUInt8)
    out := out.push ((word >>> 16).toUInt8)
    out := out.push ((word >>> 8).toUInt8)
    out := out.push word.toUInt8
  ByteArray.mk out

def doubleSha256Bytes (msg : ByteArray) : ByteArray :=
  sha256Bytes (sha256Bytes msg)

def hmacSha256Bytes (key msg : ByteArray) : ByteArray := Id.run do
  let k0 := if key.size > 64 then sha256Bytes key else key
  let mut kPad := k0.data
  while kPad.size < 64 do
    kPad := kPad.push 0
  let mut ipad : Array UInt8 := Array.mkEmpty 64
  let mut opad : Array UInt8 := Array.mkEmpty 64
  for b in kPad do
    ipad := ipad.push (b ^^^ 0x36)
    opad := opad.push (b ^^^ 0x5c)
  let inner := sha256Bytes (ByteArray.mk ipad ++ msg)
  sha256Bytes (ByteArray.mk opad ++ inner)

def bip340TaggedHashBytes (tag : String) (msg : ByteArray) : ByteArray :=
  let th := sha256Bytes tag.toUTF8
  sha256Bytes (th ++ th ++ msg)

/-! ### Pure FIPS 180-4 SHA-512 & RFC 2104 HMAC-SHA512 (for BIP-32 `CKDpub` & SLIP-21) -/

@[inline] def rotr64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

def sha512K : Array UInt64 := #[
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

def sha512Compress (h : Array UInt64) (block : ByteArray) (offset : Nat) : Array UInt64 := Id.run do
  let mut w := Array.replicate 80 (0 : UInt64)
  for i in [0:16] do
    let mut word : UInt64 := 0
    for j in [0:8] do
      word := (word <<< 8) ||| (block.data[offset + 8 * i + j]?.getD 0).toUInt64
    w := w.set! i word
  for i in [16:80] do
    let w15 := w[i - 15]!
    let w2  := w[i - 2]!
    let s0 := rotr64 w15 1 ^^^ rotr64 w15 8 ^^^ (w15 >>> 7)
    let s1 := rotr64 w2 19 ^^^ rotr64 w2 61 ^^^ (w2 >>> 6)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for i in [0:80] do
    let s1 := rotr64 e 14 ^^^ rotr64 e 18 ^^^ rotr64 e 41
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := hh + s1 + ch + sha512K[i]! + w[i]!
    let s0 := rotr64 a 28 ^^^ rotr64 a 34 ^^^ rotr64 a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + maj
    hh := g; g := f; f := e; e := d + temp1
    d := c; c := b; b := a; a := temp1 + temp2
  #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d,
    h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def sha512Bytes (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let rem := (msg.size + 1) % 128
  let padZeros := if rem ≤ 112 then 112 - rem else 240 - rem
  let mut padded := msg.data.push 0x80
  for _ in [0:padZeros] do
    padded := padded.push 0x00
  for _ in [0:8] do
    padded := padded.push 0x00
  for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
    padded := padded.push ((bitLen >>> UInt64.ofNat shift).toUInt8)
  let paddedBa := ByteArray.mk padded
  let nBlocks := paddedBa.size / 128
  let mut h : Array UInt64 := #[
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
  ]
  for blk in [0:nBlocks] do
    h := sha512Compress h paddedBa (blk * 128)
  let mut out : Array UInt8 := Array.mkEmpty 64
  for word in h do
    for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
      out := out.push ((word >>> UInt64.ofNat shift).toUInt8)
  ByteArray.mk out

def hmacSha512Bytes (key msg : ByteArray) : ByteArray := Id.run do
  let k0 := if key.size > 128 then sha512Bytes key else key
  let mut kPad := k0.data
  while kPad.size < 128 do
    kPad := kPad.push 0
  let mut ipad : Array UInt8 := Array.mkEmpty 128
  let mut opad : Array UInt8 := Array.mkEmpty 128
  for b in kPad do
    ipad := ipad.push (b ^^^ 0x36)
    opad := opad.push (b ^^^ 0x5c)
  let inner := sha512Bytes (ByteArray.mk ipad ++ msg)
  sha512Bytes (ByteArray.mk opad ++ inner)

/-! ### Pure RIPEMD-160 & Bitcoin `HASH160` -/

@[inline] def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

def rmdF (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| ((~~~x) &&& z)
  else if j < 48 then (x ||| (~~~y)) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& (~~~z))
  else x ^^^ (y ||| (~~~z))

def rmdKL (j : Nat) : UInt32 :=
  if j < 16 then 0x00000000
  else if j < 32 then 0x5a827999
  else if j < 48 then 0x6ed9eba1
  else if j < 64 then 0x8f1bbcdc
  else 0xa953fd4e

def rmdKR (j : Nat) : UInt32 :=
  if j < 16 then 0x50a28be6
  else if j < 32 then 0x5c4dd124
  else if j < 48 then 0x6d703ef3
  else if j < 64 then 0x7a6d76e9
  else 0x00000000

def rmdRL : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13
]

def rmdRR : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11
]

def rmdSL : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6
]

def rmdSR : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11
]

def ripemd160Bytes (msg : ByteArray) : ByteArray := Id.run do
  let bitLen : UInt64 := (UInt64.ofNat msg.size) * 8
  let rem := (msg.size + 1) % 64
  let padZeros := if rem ≤ 56 then 56 - rem else 120 - rem
  let mut padded := msg.data.push 0x80
  for _ in [0:padZeros] do
    padded := padded.push 0x00
  for shift in [0, 8, 16, 24, 32, 40, 48, 56] do
    padded := padded.push ((bitLen >>> UInt64.ofNat shift).toUInt8)
  let paddedBa := ByteArray.mk padded
  let nBlocks := paddedBa.size / 64
  let mut h0 : UInt32 := 0x67452301
  let mut h1 : UInt32 := 0xefcdab89
  let mut h2 : UInt32 := 0x98badcfe
  let mut h3 : UInt32 := 0x10325476
  let mut h4 : UInt32 := 0xc3d2e1f0
  for blk in [0:nBlocks] do
    let base := blk * 64
    let mut x := Array.replicate 16 (0 : UInt32)
    for i in [0:16] do
      let b0 := (paddedBa.data[base + 4 * i]?.getD 0).toUInt32
      let b1 := (paddedBa.data[base + 4 * i + 1]?.getD 0).toUInt32
      let b2 := (paddedBa.data[base + 4 * i + 2]?.getD 0).toUInt32
      let b3 := (paddedBa.data[base + 4 * i + 3]?.getD 0).toUInt32
      x := x.set! i (b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24))
    let mut al := h0; let mut bl := h1; let mut cl := h2; let mut dl := h3; let mut el := h4
    let mut ar := h0; let mut br := h1; let mut cr := h2; let mut dr := h3; let mut er := h4
    for j in [0:80] do
      let tl := rotl32 (al + rmdF j bl cl dl + x[rmdRL[j]!]! + rmdKL j) rmdSL[j]! + el
      al := el; el := dl; dl := rotl32 cl 10; cl := bl; bl := tl
      let tr := rotl32 (ar + rmdF (79 - j) br cr dr + x[rmdRR[j]!]! + rmdKR j) rmdSR[j]! + er
      ar := er; er := dr; dr := rotl32 cr 10; cr := br; br := tr
    let t := h1 + cl + dr
    h1 := h2 + dl + er
    h2 := h3 + el + ar
    h3 := h4 + al + br
    h4 := h0 + bl + cr
    h0 := t
  let mut out : Array UInt8 := Array.mkEmpty 20
  for word in #[h0, h1, h2, h3, h4] do
    out := out.push word.toUInt8
    out := out.push ((word >>> 8).toUInt8)
    out := out.push ((word >>> 16).toUInt8)
    out := out.push ((word >>> 24).toUInt8)
  ByteArray.mk out

def hash160Bytes (msg : ByteArray) : ByteArray :=
  ripemd160Bytes (sha256Bytes msg)

/-! ### Pure Affine Secp256k1 Arithmetic (`p = 2^256 - 2^32 - 977`) & BIP-32/340/341 Oracles -/

def secpP : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

def secpN : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

structure SecpAffine where
  x : Nat
  y : Nat
  deriving Repr, DecidableEq, Inhabited

def secpG : SecpAffine :=
  { x := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
    y := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 }

def powModLoop (base : Nat) (modulus : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, exp, acc =>
      let acc' := if exp % 2 == 1 then (acc * base) % modulus else acc
      powModLoop ((base * base) % modulus) modulus fuel (exp / 2) acc'

def powMod (base exp modulus : Nat) : Nat :=
  powModLoop (base % modulus) modulus 260 exp 1

def modInvP (a : Nat) : Nat :=
  powMod a (secpP - 2) secpP

def fpSub (a b : Nat) : Nat :=
  (a + secpP - (b % secpP)) % secpP

def secpOnCurve (pt : SecpAffine) : Bool :=
  pt.x < secpP && pt.y < secpP &&
  ((pt.y * pt.y) % secpP == ((pt.x * pt.x) % secpP * pt.x + 7) % secpP)

def secpDouble (p : SecpAffine) : InternalSpec.Musig2.CurvePoint SecpAffine :=
  if p.y == 0 then
    .infinity
  else
    let num := (3 * ((p.x * p.x) % secpP)) % secpP
    let den := modInvP ((2 * p.y) % secpP)
    let lam := (num * den) % secpP
    let x3 := fpSub ((lam * lam) % secpP) ((2 * p.x) % secpP)
    let y3 := fpSub ((lam * fpSub p.x x3) % secpP) p.y
    .affine { x := x3, y := y3 }

def secpAdd : InternalSpec.Musig2.CurvePoint SecpAffine → InternalSpec.Musig2.CurvePoint SecpAffine →
    InternalSpec.Musig2.CurvePoint SecpAffine
  | .infinity, q => q
  | p, .infinity => p
  | .affine p, .affine q =>
      if p.x == q.x then
        if p.y == q.y then secpDouble p else .infinity
      else
        let lam := (fpSub q.y p.y * modInvP (fpSub q.x p.x)) % secpP
        let x3 := fpSub (fpSub ((lam * lam) % secpP) p.x) q.x
        let y3 := fpSub ((lam * fpSub p.x x3) % secpP) p.y
        .affine { x := x3, y := y3 }

def secpMulLoop (cur : InternalSpec.Musig2.CurvePoint SecpAffine) :
    Nat → Nat → InternalSpec.Musig2.CurvePoint SecpAffine → InternalSpec.Musig2.CurvePoint SecpAffine
  | 0, _, acc => acc
  | _ + 1, 0, acc => acc
  | fuel + 1, k, acc =>
      let acc' := if k % 2 == 1 then secpAdd acc cur else acc
      secpMulLoop (secpAdd cur cur) fuel (k / 2) acc'

def secpMul (k : Nat) (pt : InternalSpec.Musig2.CurvePoint SecpAffine) : InternalSpec.Musig2.CurvePoint SecpAffine :=
  let kMod := k % secpN
  if kMod == 0 then .infinity
  else secpMulLoop pt 260 kMod .infinity

def natOfBytesBE (bs : ByteArray) : Nat :=
  bs.data.foldl (fun acc b => acc * 256 + b.toNat) 0

def natToBytes32BE (v : Nat) : ByteArray :=
  ByteArray.mk (BitcoinLedger.Musig2.natToBytesBEAux 32 v []).toArray

def secpCompressBytes (pt : SecpAffine) : ByteArray :=
  let pfx : UInt8 := if pt.y % 2 == 0 then 0x02 else 0x03
  ByteArray.mk #[pfx] ++ natToBytes32BE pt.x

def secpDecompressBytes? (bs : ByteArray) : Option SecpAffine :=
  if bs.size != 33 then
    none
  else
    let pfx := bs.data[0]?.getD 0
    if pfx != 0x02 && pfx != 0x03 then
      none
    else
      let x := natOfBytesBE (bs.extract 1 33)
      if x ≥ secpP then
        none
      else
        let rhs := (((x * x) % secpP) * x + 7) % secpP
        -- Since secpP % 4 == 3, sqrt(rhs) = rhs^((secpP + 1) / 4) mod secpP
        let yCand := powMod rhs ((secpP + 1) / 4) secpP
        if (yCand * yCand) % secpP != rhs then
          none
        else
          let wantOdd := pfx == 0x03
          let y := if (yCand % 2 == 1) == wantOdd then yCand else secpP - yCand
          some { x := x, y := y }

def secpLiftX? (xBytes : ByteArray) : Option SecpAffine :=
  if xBytes.size != 32 then none
  else secpDecompressBytes? (ByteArray.mk #[0x02] ++ xBytes)

/-- Real BIP-340 Schnorr signature verification over 32-byte `msg` (or arbitrary `msg` for BIP-340). -/
def bip340VerifyBytes (xOnly32 msg sig64 : ByteArray) : Bool :=
  if xOnly32.size != 32 || sig64.size != 64 then
    false
  else
    match secpLiftX? xOnly32 with
    | none => false
    | some p =>
        let rBytes := sig64.extract 0 32
        let sBytes := sig64.extract 32 64
        let r := natOfBytesBE rBytes
        let s := natOfBytesBE sBytes
        if r ≥ secpP || s ≥ secpN then
          false
        else
          let e := (natOfBytesBE (bip340TaggedHashBytes "BIP0340/challenge" (rBytes ++ xOnly32 ++ msg))) % secpN
          let minusE := (secpN - e) % secpN
          match secpAdd (secpMul s (.affine secpG)) (secpMul minusE (.affine p)) with
          | .infinity => false
          | .affine rPt => rPt.y % 2 == 0 && rPt.x == r

/-- Real BIP-32 unhardened public child derivation (`CKDpub`) returning `(childPub33, childChain32, il32)`. -/
def realCkdPubUnhardened? (parentPub33 chainCode32 : ByteArray) (idx : UInt32) :
    Option (ByteArray × ByteArray × ByteArray) :=
  if idx ≥ 0x80000000 || parentPub33.size != 33 || chainCode32.size != 32 then
    none
  else
    match secpDecompressBytes? parentPub33 with
    | none => none
    | some parentPt =>
        let data := parentPub33 ++ BitcoinLedger.Basic.encodeU32BE idx
        let i64 := hmacSha512Bytes chainCode32 data
        let il := i64.extract 0 32
        let ir := i64.extract 32 64
        let tweak := natOfBytesBE il
        if tweak ≥ secpN then
          none
        else
          match secpAdd (secpMul tweak (.affine secpG)) (.affine parentPt) with
          | .infinity => none
          | .affine childPt => some (secpCompressBytes childPt, ir, il)

/-- Real BIP-32 full seed derivation (`m / step_0 / ...`) from a BIP-39 64-byte seed. -/
def deriveFromSeed? (seed : ByteArray) (steps : List UInt32) : Option (Nat × ByteArray × SecpAffine) := Id.run do
  let i0 := hmacSha512Bytes "Bitcoin seed".toUTF8 seed
  let mut priv := natOfBytesBE (i0.extract 0 32)
  let mut cc := i0.extract 32 64
  if priv == 0 || priv ≥ secpN then
    return none
  for step in steps do
    let dataOpt : Option ByteArray :=
      if step ≥ 0x80000000 then
        some (ByteArray.mk #[0x00] ++ natToBytes32BE priv ++ BitcoinLedger.Basic.encodeU32BE step)
      else
        match secpMul priv (.affine secpG) with
        | .affine p => some (secpCompressBytes p ++ BitcoinLedger.Basic.encodeU32BE step)
        | .infinity => none
    let some data := dataOpt | return none
    let i64 := hmacSha512Bytes cc data
    let il := natOfBytesBE (i64.extract 0 32)
    let ir := i64.extract 32 64
    let nextPriv := (il + priv) % secpN
    if il ≥ secpN || nextPriv == 0 then
      return none
    priv := nextPriv
    cc := ir
  match secpMul priv (.affine secpG) with
  | .affine pubPt => some (priv, cc, pubPt)
  | .infinity => none

/-- Speculos / Vanadium default mnemonic (`glory promote mansion ...`) 64-byte BIP-39 seed
    and Vanadium's test resident seed (`tprv8ZgxMBicQKsPex9oTu7vZcJnLRnxXZL41PfqipcVUU8DrpRi5JLows2s99Sw4ztgevDXvyY8NZLidoABQaWMkmDGtztsMhcT7BoRQgw41hu`). -/
def speculosSeed64 : ByteArray :=
  hex! "b11997faff420a331bb4a4ffdc8bdc8ba7c01732a99a30d83dbbebd469666c84b47d09d3f5f472b3b9384ac634beba2a440ba36ec7661144132f35e206873564"

/-- Decode Vanadium's resident root `tprv` (`get_extended_pubkey.rs:319`) and derive any path on `KeyTree::Resident`. -/
def residentRootTprv : String :=
  "tprv8ZgxMBicQKsPex9oTu7vZcJnLRnxXZL41PfqipcVUU8DrpRi5JLows2s99Sw4ztgevDXvyY8NZLidoABQaWMkmDGtztsMhcT7BoRQgw41hu"

def deriveFromExtendedPriv? (priv0 : Nat) (cc0 : ByteArray) (steps : List UInt32) :
    Option (Nat × ByteArray × SecpAffine) := Id.run do
  let mut priv := priv0
  let mut cc := cc0
  if priv == 0 || priv ≥ secpN then return none
  for step in steps do
    let dataOpt : Option ByteArray :=
      if step ≥ 0x80000000 then
        some (ByteArray.mk #[0x00] ++ natToBytes32BE priv ++ BitcoinLedger.Basic.encodeU32BE step)
      else
        match secpMul priv (.affine secpG) with
        | .affine p => some (secpCompressBytes p ++ BitcoinLedger.Basic.encodeU32BE step)
        | .infinity => none
    let some data := dataOpt | return none
    let i64 := hmacSha512Bytes cc data
    let il := natOfBytesBE (i64.extract 0 32)
    let ir := i64.extract 32 64
    let nextPriv := (il + priv) % secpN
    if il ≥ secpN || nextPriv == 0 then return none
    priv := nextPriv
    cc := ir
  match secpMul priv (.affine secpG) with
  | .affine pubPt => some (priv, cc, pubPt)
  | .infinity => none

def residentRootPrivAndCc? : Option (Nat × ByteArray) :=
  match BitcoinLedger.Script.decodeBase58Check? doubleSha256Bytes residentRootTprv with
  | none => none
  | some raw78 =>
      if raw78.size == 78 && raw78.data[45]? == some 0x00 then
        some (natOfBytesBE (raw78.extract 46 78), raw78.extract 13 45)
      else
        none

/-- Real `MusigCrypto SecpAffine` instance backed by SHA-256, HMAC-SHA512, and affine secp256k1. -/
def realMusigCrypto : InternalSpec.Musig2.MusigCrypto SecpAffine where
  sha256 bs := mkSizedBytes! 32 (sha256Bytes bs)
  taggedHash tag msg := mkSizedBytes! 32 (bip340TaggedHashBytes tag msg)
  generator := secpG
  pointAdd := secpAdd
  pointMul := secpMul
  pointNeg
    | .infinity => .infinity
    | .affine pt => .affine { x := pt.x, y := if pt.y == 0 then 0 else secpP - pt.y }
  compress pt := mkSizedBytes! 33 (secpCompressBytes pt)
  decompress pk := secpDecompressBytes? pk.bytes
  xCoord pt := mkSizedBytes! 32 (natToBytes32BE pt.x)
  hasEvenY pt := pt.y % 2 == 0
  ckdPubUnhardened pk cc idx :=
    match realCkdPubUnhardened? pk.bytes cc.bytes idx with
    | some (cpk, ccc, cil) => some (mkSizedBytes! 33 cpk, mkSizedBytes! 32 ccc, mkSizedBytes! 32 cil)
    | none => none

/-- Real `SpCrypto SecpAffine` instance backed by SHA-256 and affine secp256k1. -/
def realSpCrypto : InternalSpec.SilentPayments.SpCrypto SecpAffine where
  taggedHash tag msg := mkSpSizedBytes! 32 (bip340TaggedHashBytes tag msg)
  generator := secpG
  pointAdd a b :=
    let toM : InternalSpec.SilentPayments.SpPoint SecpAffine → InternalSpec.Musig2.CurvePoint SecpAffine
      | .infinity => .infinity
      | .affine p => .affine p
    match secpAdd (toM a) (toM b) with
    | .infinity => .infinity
    | .affine p => .affine p
  pointMul k pt :=
    let toM : InternalSpec.SilentPayments.SpPoint SecpAffine → InternalSpec.Musig2.CurvePoint SecpAffine
      | .infinity => .infinity
      | .affine p => .affine p
    match secpMul k (toM pt) with
    | .infinity => .infinity
    | .affine p => .affine p
  pointNeg
    | .infinity => .infinity
    | .affine pt => .affine { x := pt.x, y := if pt.y == 0 then 0 else secpP - pt.y }
  liftX x32 := secpLiftX? x32.bytes
  compress pt := mkSpSizedBytes! 33 (secpCompressBytes pt)
  decompress pk := secpDecompressBytes? pk.bytes
  xCoord pt := mkSpSizedBytes! 32 (natToBytes32BE pt.x)
  hasEvenY pt := pt.y % 2 == 0

/-- Real `CryptoDerivationOracle` modelling Vanadium's Speculos seed (`Standard`) and test `Resident` root. -/
def vanadiumDerivationOracle : InternalSpec.CryptoDerivationOracle where
  hash160 := hash160Bytes
  doubleSha256 := doubleSha256Bytes
  deriveChildPub parentPub cc idx :=
    match realCkdPubUnhardened? parentPub cc idx with
    | some (cpk, ccc, _) => some (cpk, ccc)
    | none => none
  masterFingerprint
    | .standard =>
        match deriveFromSeed? speculosSeed64 [] with
        | some (_, _, pub0) => some ((hash160Bytes (secpCompressBytes pub0)).extract 0 4)
        | none => none
    | .resident =>
        match residentRootPrivAndCc? with
        | some (priv0, cc0) =>
            match deriveFromExtendedPriv? priv0 cc0 [] with
            | some (_, _, pub0) => some ((hash160Bytes (secpCompressBytes pub0)).extract 0 4)
            | none => none
        | none => none
  deriveNode
    | .standard, path =>
        match deriveFromSeed? speculosSeed64 path.toList with
        | some (_, cc, pubPt) => some (secpCompressBytes pubPt, cc)
        | none => none
    | .resident, path =>
        match residentRootPrivAndCc? with
        | some (priv0, cc0) =>
            match deriveFromExtendedPriv? priv0 cc0 path.toList with
            | some (_, cc, pubPt) => some (secpCompressBytes pubPt, cc)
            | none => none
        | none => none

/-- Real `CryptoPolicyOracle` backed by SHA-256, RIPEMD-160, BIP-32 `CKDpub`, BIP-327 `KeyAgg`, and BIP-341 `TapTweak`. -/
def realPolicyOracle : BitcoinLedger.WalletPolicy.CryptoPolicyOracle where
  sha256 := sha256Bytes
  ripemd160 := ripemd160Bytes
  ckdPub parent idx :=
    if parent.depth == 255 then none
    else
      match realCkdPubUnhardened? parent.compressedPubkey parent.chainCode idx with
      | none => none
      | some (childPk, childCc, _) =>
          let fpBytes := hash160Bytes parent.compressedPubkey
          let fp := BitcoinLedger.WalletPolicy.decodeU32BE4
            (fpBytes.get! 0) (fpBytes.get! 1) (fpBytes.get! 2) (fpBytes.get! 3)
          some {
            version := parent.version
            depth := parent.depth + 1
            parentFingerprint := fp
            childNumber := idx
            chainCode := childCc
            compressedPubkey := childPk
          }
  musigKeyAgg sortedCompressedPubkeys :=
    let cPks := sortedCompressedPubkeys.map (mkSizedBytes! 33)
    match BitcoinLedger.Musig2.keyAgg realMusigCrypto cPks with
    | .ok ctx => some (secpCompressBytes ctx.q)
    | .error _ => none
  taprootTweakPubkey internalXOnly merkleRoot :=
    match secpLiftX? internalXOnly with
    | none => none
    | some p =>
        let payload := match merkleRoot with
          | none => internalXOnly
          | some root => internalXOnly ++ root
        let t := natOfBytesBE (bip340TaggedHashBytes "TapTweak" payload)
        if t ≥ secpN then none
        else
          match secpAdd (.affine p) (secpMul t (.affine secpG)) with
          | .infinity => none
          | .affine q => some (natToBytes32BE q.x, q.y % 2 == 1)

/-- SLIP-21 `m/"Proof of Registration"` key derivation (`vanadium/apps/bitcoin/common/src/por.rs`). -/
def slip21PorKey : ByteArray :=
  let master := hmacSha512Bytes "Symmetric key seed".toUTF8 speculosSeed64
  let child := hmacSha512Bytes (master.extract 0 32) (ByteArray.mk #[0x00] ++ "Proof of Registration".toUTF8)
  child.extract 32 64

def computeVanadiumPorHmacBytes (id32 : ByteArray) : ByteArray :=
  hmacSha256Bytes slip21PorKey id32

/-- Real `DeviceRegistrationOracle` for the Speculos device (`0xf5acc2fd`). -/
def vanadiumDeviceOracle : BitcoinLedger.WalletPolicy.DeviceRegistrationOracle where
  masterFingerprint := 0xf5acc2fd
  deriveAtOrigin net originPath :=
    let specNet : InternalSpec.Network := match net with | .mainnet => .mainnet | .testnet => .testnet
    match BitcoinLedger.Bip32.deriveExtendedPubKeyWithOracle
            vanadiumDerivationOracle specNet .standard originPath.toArray with
    | none => none
    | some xp =>
        let fp := BitcoinLedger.WalletPolicy.decodeU32BE4
          (xp.parentFingerprint.data[0]?.getD 0)
          (xp.parentFingerprint.data[1]?.getD 0)
          (xp.parentFingerprint.data[2]?.getD 0)
          (xp.parentFingerprint.data[3]?.getD 0)
        some {
          version := xp.version
          depth := xp.depth
          parentFingerprint := fp
          childNumber := xp.childNumber
          chainCode := xp.chainCode
          compressedPubkey := xp.pubkey
        }
  verifyRegistrationProof policy hmac :=
    let serPol := policy.name.toUTF8 -- test policy commitment binding
    BitcoinLedger.WalletPolicy.verifyRegistrationHmac
      realPolicyOracle (fun id32 => some (computeVanadiumPorHmacBytes id32))
      policy (.vanadium serPol) hmac

/-- Real `Psbt.CryptoOracles` for Vanadium Testnet. -/
def vanadiumTestnetPsbtOracles : InternalSpec.Psbt.CryptoOracles where
  sha256 bs := mkPsbtBytes32! (sha256Bytes bs)
  hash160 := hash160Bytes
  formatAddress spk := InternalSpec.scriptToAddress? .vanadium doubleSha256Bytes .testnet spk

/-! ============================================================================================
    PART A: OFFICIAL VANADIUM (`apps/bitcoin`) DIFFERENTIAL TEST VECTORS
    ============================================================================================ -/

/-! ### A.1 BIP-32 Master Fingerprint, `GET_EXTENDED_PUBKEY` (`Standard` & `Resident`), and Path Policy -/

def h44 : UInt32 := BitcoinLedger.Bip32.harden 44
def h48 : UInt32 := BitcoinLedger.Bip32.harden 48
def h49 : UInt32 := BitcoinLedger.Bip32.harden 49
def h84 : UInt32 := BitcoinLedger.Bip32.harden 84
def h86 : UInt32 := BitcoinLedger.Bip32.harden 86
def h352 : UInt32 := BitcoinLedger.Bip32.harden 352
def h0 : UInt32 := BitcoinLedger.Bip32.harden 0
def h1 : UInt32 := BitcoinLedger.Bip32.harden 1
def h2 : UInt32 := BitcoinLedger.Bip32.harden 2
def h4 : UInt32 := BitcoinLedger.Bip32.harden 4
def h10 : UInt32 := BitcoinLedger.Bip32.harden 10

/-- Derive & Base58Check-encode a `tpub` on `tree` via `BitcoinLedger.Bip32`. -/
def evalVanadiumTpub? (tree : InternalSpec.KeyTree) (path : Array UInt32) : Option String := do
  let xpub ← (BitcoinLedger.Bip32.evalGetExtendedPubkey
    vanadiumDerivationOracle BitcoinLedger.Bip32.vanadiumExpubPolicyConfig
    .testnet tree path false true).toOption
  BitcoinLedger.Bip32.encodeExtendedPubKeyBase58Check? doubleSha256Bytes xpub

/-- Vanadium `get_extended_pubkey.rs:285-323` official `KeyTree::Standard` & `KeyTree::Resident` vectors. -/
def checkBip32Vectors : Bool :=
  -- 1. Master fingerprints (`get_master_fingerprint.rs`)
  BitcoinLedger.Bip32.deriveMasterFingerprint? vanadiumDerivationOracle .standard == some (hex! "f5acc2fd") &&
  BitcoinLedger.Bip32.deriveMasterFingerprint? vanadiumDerivationOracle .resident == some (hex! "ad85d955") &&
  -- 2. All 7 `KeyTree::Standard` `GET_EXTENDED_PUBKEY` vectors (`get_extended_pubkey.rs:285-293`)
  evalVanadiumTpub? .standard #[h44, h1, h0] ==
    some "tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT" &&
  evalVanadiumTpub? .standard #[h44, h1, h10] ==
    some "tpubDCwYjpDhUdPGp21gSpVay2QPJVh6WNySWMXPhbcu1DsxH31dF7mY18oibbu5RxCLBc1Szerjscuc3D5HyvfYqfRvc9mesewnFqGmPjney4d" &&
  evalVanadiumTpub? .standard #[h44, h1, h2, 1, 42] ==
    some "tpubDGF9YgHKv6qh777rcqVhpmDrbNzgophJM9ec7nHiSfrbss7fVBXoqhmZfohmJSvhNakDHAspPHjVVNL657tLbmTXvSeGev2vj5kzjMaeupT" &&
  evalVanadiumTpub? .standard #[h48, h1, h4, h1, 0, 7] ==
    some "tpubDK8WPFx4WJo1R9mEL7Wq325wBiXvkAe8ipgb9Q1QBDTDUD2YeCfutWtzY88NPokZqJyRPKHLGwTNLT7jBG59aC6VH8q47LDGQitPB6tX2d7" &&
  evalVanadiumTpub? .standard #[h49, h1, h1, 1, 3] ==
    some "tpubDGnetmJDCL18TyaaoyRAYbkSE9wbHktSdTS4mfsR6inC8c2r6TjdBt3wkqEQhHYPtXpa46xpxDaCXU2PRNUGVvDzAHPG6hHRavYbwAGfnFr" &&
  evalVanadiumTpub? .standard #[h84, h1, h2, 0, 10] ==
    some "tpubDG9YpSUwScWJBBSrhnAT47NcT4NZGLcY18cpkaiWHnkUCi19EtCh8Heeox268NaFF6o56nVeSXuTyK6jpzTvV1h68Kr3edA8AZp27MiLUNt" &&
  evalVanadiumTpub? .standard #[h86, h1, h4, 1, 12] ==
    some "tpubDHTZ815MvTaRmo6Qg1rnU6TEU4ZkWyA56jA1UgpmMcBGomnSsyo34EZLoctzZY9MTJ6j7bhccceUeXZZLxZj5vgkVMYfcZ7DNPsyRdFpS3f" &&
  -- 3. Additional account roots used in `account.rs` & `sign_psbt/tests/basic.rs`
  evalVanadiumTpub? .standard #[h84, h1, h0] ==
    some "tpubDCtKfsNyRhULjZ9XMS4VKKtVcPdVDi8MKUbcSD9MJDyjRu1A2ND5MiipozyyspBT9bg8upEp7a8EAgFxNxXn1d7QkdbL52Ty5jiSLcxPt1P" &&
  evalVanadiumTpub? .standard #[h86, h1, h0] ==
    some "tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U" &&
  -- 4. Both `KeyTree::Resident` vectors (`get_extended_pubkey.rs:320-323`)
  evalVanadiumTpub? .resident #[h44, h1, h0] ==
    some "tpubDD7URPdwnhN6XNWRkMLhaGvhp1xaZNTAqgn8qULdENfMrUbCUcV4Kd4FQzVSHkKx9nmU7sNjBMPa96b9g3KTSJTAvTsTcT5mYDz97fUppvd" &&
  evalVanadiumTpub? .resident #[h44, h1, h0, 3] ==
    some "tpubDExN4iEszTsYJshQBJwUka8bvbyZN3dEGSXF5CsT9r9KYVu8ZszgX7F6zxystWLzrNcSdr2Hv66EbuvYjZqiSsSQ389vQdnoQKc2wJHPBuL" &&
  -- 5. Wire path round-trip & policy classification (`vanadiumHardenedExpubPolicyConfig` vs `vanadiumExpubPolicyConfig`)
  (match BitcoinLedger.Bip32.serializeBip32Path? #[h84, h1, h0, 0, 0] with
   | some wire => BitcoinLedger.Bip32.parseBip32PathBounded? 16 wire == some #[h84, h1, h0, 0, 0]
   | none => false) &&
  BitcoinLedger.Bip32.classifyExpubPath BitcoinLedger.Bip32.vanadiumExpubPolicyConfig .testnet #[h352, h1, h0, h0] == .allowSilent &&
  BitcoinLedger.Bip32.classifyExpubPath BitcoinLedger.Bip32.vanadiumHardenedExpubPolicyConfig .testnet #[h84, h1, h0] == .allowSilent &&
  BitcoinLedger.Bip32.classifyExpubPath BitcoinLedger.Bip32.vanadiumHardenedExpubPolicyConfig .testnet #[1, 2, 3] == .warnUnusual &&
  BitcoinLedger.Bip32.classifyExpubPath BitcoinLedger.Bip32.vanadiumExpubPolicyConfig .testnet (Array.replicate 17 0) == .reject .bip32PathTooLong

/-! ### A.2 Wallet Policies, Proof-of-Registration & Address Derivation (`account.rs`, `register_account.rs`) -/

def parseV2TestnetPolicy (name desc : String) (keyStrs : List String) :
    Except BitcoinLedger.WalletPolicy.PolicyError BitcoinLedger.WalletPolicy.WalletPolicy := do
  let prof := BitcoinLedger.WalletPolicy.vanadiumAppProfile .testnet
  let keys ← keyStrs.mapM (BitcoinLedger.WalletPolicy.parseWalletKeyInfo prof .v2 doubleSha256Bytes true)
  let tmpl ← BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 desc
  .ok {
    name := name
    format := .v2
    template := tmpl
    keys := keys
  }

def checkWalletPolicyAndTaprootVectors : Bool :=
  let profTestnet := BitcoinLedger.WalletPolicy.vanadiumAppProfile .testnet
  -- 1. `account.rs:154-173` & `get_address.rs:186-219`: `wpkh(@0/**)` at `(false, 0)` -> `"tb1qzdr7s2sr0dwmkwx033r4nujzk86u0cy6fmzfjk"`
  let wpkhOk :=
    match parseV2TestnetPolicy "Segwit #0" "wpkh(@0/**)"
            ["[f5acc2fd/84'/1'/0']tpubDCtKfsNyRhULjZ9XMS4VKKtVcPdVDi8MKUbcSD9MJDyjRu1A2ND5MiipozyyspBT9bg8upEp7a8EAgFxNxXn1d7QkdbL52Ty5jiSLcxPt1P"] with
    | .error _ => false
    | .ok pol =>
        match BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
                profTestnet vanadiumDeviceOracle realPolicyOracle
                (fun id32 => some (computeVanadiumPorHmacBytes id32))
                pol (.vanadium pol.name.toUTF8) true with
        | .error _ => false
        | .ok (_regId, porHmac) =>
            BitcoinLedger.WalletPolicy.deriveWalletPolicyAddress
              .vanadium profTestnet vanadiumDeviceOracle realPolicyOracle
              pol (.proofOfRegistration porHmac) false 0 ==
              .ok "tb1qzdr7s2sr0dwmkwx033r4nujzk86u0cy6fmzfjk"

  -- 2. `script.rs:518-536`: `tr(musig(@0,@1)/**)` at `(false, 3)` -> exact P2TR `5120c1fdfebed0...`
  let musigTrOk :=
    match parseV2TestnetPolicy "MuSig2 Taproot" "tr(musig(@0,@1)/**)" [
      "tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT",
      "tpubDCwYjpDhUdPGQWG6wG6hkBJuWFZEtrn7j3xwG3i8XcQabcGC53xWZm1hSXrUPFS5UvZ3QhdPSjXWNfWmFGTioARHuG5J7XguEjgg7p8PxAm"
    ] with
    | .error _ => false
    | .ok pol =>
        BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile
          profTestnet realPolicyOracle pol false 3 ==
          .ok (hex! "5120c1fdfebed063aa148340c45132e6718d8de81466ae2b90929e3d9328364cd6ed")

  -- 3. `register_account.rs:383-411`: `Simple inheritance` (`tr(@0/<0;1>/*,and_v(v:pk(@1/<0;1>/*),older(52596)))`)
  let simpleInh1Ok :=
    match parseV2TestnetPolicy "Simple inheritance"
            "tr(@0/<0;1>/*,and_v(v:pk(@1/<0;1>/*),older(52596)))" [
              "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK",
              "[d5365b22/48'/1'/0'/2']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
            ] with
    | .error _ => false
    | .ok pol =>
        (BitcoinLedger.WalletPolicy.validatePolicyRegistration profTestnet vanadiumDeviceOracle pol true).isOk &&
        (match BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profTestnet realPolicyOracle pol false 0 with
         | .ok spk => spk.size == 34 && spk.data[0]? == some 0x51 && spk.data[1]? == some 0x20
         | .error _ => false)

  -- 4. `register_account.rs:414-443`: `Simple inheritance` 2-leaf TapTree with BIP-341 NUMS unspendable internal key `@0`
  let simpleInh2Ok :=
    match parseV2TestnetPolicy "Simple inheritance"
            "tr(@0/<0;1>/*,{and_v(v:pk(@1/<2;3>/*),older(4383)),and_v(v:pk(@2/<0;1>/*),pk(@1/<0;1>/*))})" [
              "tpubD6NzVbkrYhZ4XUBKWaWfdn2icbaEDfaUgkCCbKPm31LTLRfaaEJRDAF3XXbvTaKLHATytZPGoWpVxnMnrRbn4519fP6nhZDDFtJimcZWBGC",
              "[41e8dfb4/48'/1'/0'/2']tpubDE6DKS5H4uEZwjGqvSujs1GMKY3PZKuEvsVFbvCStYs3yNjo93aeVqEGT3gsFtAPHdj19oTZCjoKarMz1Ve6bKdzh6gNaFsfH1FudHTxGrB",
              "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"
            ] with
    | .error _ => false
    | .ok pol =>
        -- Verify `@0` is classified as `.unspendable` (BIP-341 NUMS `0250929b74...`) and `@2` as `.internal`!
        let roles := pol.keys.map (BitcoinLedger.WalletPolicy.classifyKeyInfo vanadiumDeviceOracle .testnet)
        roles == [.unspendable, .external, .internal] &&
        (BitcoinLedger.WalletPolicy.validatePolicyRegistration profTestnet vanadiumDeviceOracle pol true).isOk &&
        (match BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profTestnet realPolicyOracle pol false 0 with
         | .ok spk => spk.size == 34 && spk.data[0]? == some 0x51
         | .error _ => false)

  -- 5. `pkh(@0/**)` (`basic.rs:28`), `sh(wpkh(@0/**))`, and `wsh(sortedmulti(2,@0/**,@1/**))`
  let pkhAndMultiOk :=
    match parseV2TestnetPolicy "My legacy account #0" "pkh(@0/**)"
            ["[f5acc2fd/44'/1'/0']tpubDCwYjpDhUdPGP5rS3wgNg13mTrrjBuG8V9VpWbyptX6TRPbNoZVXsoVUSkCjmQ8jJycjuDKBb9eataSymXakTTaGifxR6kmVsfFehH1ZgJT"],
          parseV2TestnetPolicy "Multisig 2-of-2" "wsh(sortedmulti(2,@0/**,@1/**))" [
            "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK",
            "[d5365b22/48'/1'/0'/2']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
          ] with
    | .ok pkhPol, .ok wshPol =>
        (match BitcoinLedger.WalletPolicy.deriveKeyExprCompressedPubkey realPolicyOracle .testnet pkhPol.keys false 0 (.single 0 .wildcard) with
         | .ok pk0 => pk0 == hex! "02ee8608207e21028426f69e76447d7e3d5e077049f5e683c3136c2314762a4718"
         | .error _ => false) &&
        (BitcoinLedger.WalletPolicy.validatePolicyRegistration profTestnet vanadiumDeviceOracle wshPol true).isOk &&
        (match BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profTestnet realPolicyOracle wshPol false 0 with
         | .ok spk => spk.size == 34 && spk.data[0]? == some 0x00 && spk.data[1]? == some 0x20
         | .error _ => false)
    | _, _ => false

  wpkhOk && musigTrOk && simpleInh1Ok && simpleInh2Ok && pkhAndMultiOk

/-! ### A.3 Miniscript Combinators & Stacked Wrappers (`script.rs` & BIP-379) -/

def checkMiniscriptCombinators : Bool :=
  let prof := BitcoinLedger.WalletPolicy.vanadiumAppProfile .testnet
  let k0 := "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"
  let k1 := "[d5365b22/48'/1'/0'/2']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
  let h32 := "0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20"
  let wshTemplates : List (String × List String) := [
    (s!"wsh(andor(pk(@0/**),older(1000),pk(@1/**)))", [k0, k1]),
    (s!"wsh(or_d(pk(@0/**),and_v(v:pkh(@1/**),older(144))))", [k0, k1]),
    (s!"wsh(t:or_c(pk(@0/**),v:pk(@1/**)))", [k0, k1]),
    (s!"wsh(and_b(pk(@0/**),s:pk(@1/**)))", [k0, k1]),
    (s!"wsh(thresh(2,pk(@0/**),s:pk(@1/**),sln:older(10)))", [k0, k1]),
    (s!"wsh(and_v(v:sha256({h32}),pk(@0/**)))", [k0]),
    (s!"tr(@0/**,multi_a(2,@0/<2;3>/*,@1/**))", [k0, k1])
  ]
  wshTemplates.all fun (desc, ks) =>
    match parseV2TestnetPolicy "Miniscript vector" desc ks with
    | .error _ => false
    | .ok pol =>
        (BitcoinLedger.WalletPolicy.validatePolicyRegistration prof vanadiumDeviceOracle pol true).isOk &&
        (BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile prof realPolicyOracle pol false 0).isOk

/-! ### A.4 PSBTv0->v2 Normalization, Signing, Taproot `TapSighash` & BIP-340 Schnorr (`sign_psbt/tests/basic.rs`) -/

/-- Exact PSBTv0 vector from `vanadium/apps/bitcoin/app/src/handlers/sign_psbt/tests/basic.rs:95-143` (`test_handle_sign_psbt_tr`). -/
def checkVanadiumTaprootPsbtVector : Bool :=
  let profTestnet := BitcoinLedger.WalletPolicy.vanadiumAppProfile .testnet
  let trKeyStr := "[f5acc2fd/86'/1'/0']tpubDDKYE6BREvDsSWMazgHoyQWiJwYaDDYPbCFjYxN3HFXJP5fokeiK4hwK5tTLBNEDBwrDXn8cQ4v9b2xdW62Xr5yxoQdMu1v6c7UDXYVH27U"
  match parseV2TestnetPolicy "My taproot account #0" "tr(@0/**)" [trKeyStr] with
  | .error _ => false
  | .ok pol =>
      -- Verify derived `scriptPubKey` at `m/86'/1'/0'/1/3` (input 0) and `m/86'/1'/0'/1/2` (change output 0) match the PSBT bytes!
      let in0Spk := hex! "512089904a6348d7ff9a44d49db8b6a807c622e868364c547da426f30b5a6213186a"
      let chg0Spk := hex! "51200b8e7486bc306a0aefb7a7c00af0405542db1acd73eecca82771ccf5fe5eb60f"
      let ext1Spk := hex! "00141399b8a09847a039b0352f58d212c180bab17f77"
      let derivedIn0Ok :=
        BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profTestnet realPolicyOracle pol true 3 == .ok in0Spk
      let derivedChg0Ok :=
        BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profTestnet realPolicyOracle pol true 2 == .ok chg0Spk
      let in0IntKey := hex! "e9c69b095ed04b562afc8d41691936ba573eb6f689bc236600be4fa3926f6412"
      let chg0Pub33 := hex! "029081ece5616aa1cb99319fc4874efee47f08ceba5f6004636c8c43409a5f0a"
      let prevTxid := mkPsbtBytes32! (hex! "e16861c0d29749f52cd2edde10cbcc4f591210710f640e5d8e1440ce85d96dc6")
      let utxo0 : InternalSpec.Psbt.TxOut := { amount := 10_009_567, scriptPubKey := in0Spk }
      let rawOut0 : InternalSpec.Psbt.TxOut := { amount := 9_909_389, scriptPubKey := chg0Spk }
      let rawOut1 : InternalSpec.Psbt.TxOut := { amount := 100_000, scriptPubKey := ext1Spk }
      let psbtV0 : InternalSpec.Psbt.PsbtV0 := {
        version := some 0
        unsignedTx := {
          version := 2
          vin := #[{
            prevout := { txid := prevTxid, vout := 1 }
            scriptSig := ByteArray.empty
            sequence := 0xFFFFFFFD
            witness := #[]
          }]
          vout := #[rawOut0, rawOut1]
          locktime := 0
        }
        inputs := #[{
          witnessUtxo := some utxo0
          derivations := [{
            pubkey := in0IntKey
            origin := { fingerprint := 0xf5acc2fd, path := [h86, h1, h0, 1, 3] }
          }]
          tapInternalKey := some in0IntKey
        }]
        outputs := #[
          { derivations := [{
              pubkey := chg0Pub33
              origin := { fingerprint := 0xf5acc2fd, path := [h86, h1, h0, 1, 2] }
            }]
            tapInternalKey := some (chg0Pub33.extract 1 33) },
          {}
        ]
      }
      match BitcoinLedger.Psbt.normalizePsbtV0ToV2 psbtV0 with
      | .error _ => false
      | .ok psbtV2 =>
          let psbtPol := BitcoinLedger.AppStateMachine.toPsbtWalletPolicySpec
            profTestnet vanadiumDeviceOracle realPolicyOracle pol
          let cfg := BitcoinLedger.AppStateMachine.signingConfigOfTarget (.vanadium 1) false
          match BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles cfg psbtPol psbtV2 with
          | .error _ => false
          | .ok val =>
              let inp0 := psbtV2.inputs[0]!
              let hashes := BitcoinLedger.Psbt.computeTxHashes
                vanadiumTestnetPsbtOracles.sha256 [(inp0, utxo0)] [rawOut0, rawOut1]
              let tapSighash := BitcoinLedger.Psbt.computeSighashTaproot
                vanadiumTestnetPsbtOracles.sha256 psbtV2.txVersion val.locktime
                hashes inp0 utxo0 #[rawOut0, rawOut1] 0 none InternalSpec.Psbt.SIGHASH_DEFAULT
              let expectedSighash := hex! "75c96fb06a12db4cd011d8c95a5995db758a4f2837a22f30f0f579619a4466f3"
              derivedIn0Ok &&
              derivedChg0Ok &&
              val.sumInputs == 10_009_567 &&
              val.sumOutputs == 10_009_389 &&
              val.sumChangeOutputs == 9_909_389 &&
              val.fee == some 178 &&
              val.displayedOutputs.length == 1 &&
              val.changeOutputs.length == 1 &&
              val.displayMode == .full &&
              !val.warnings.highFee &&
              tapSighash.bytes == expectedSighash

/-! ### A.5 Two-Round BIP-327 MuSig2 Session Lifecycle & BIP-340 Schnorr Aggregation (`musig_signing.rs`) -/

def checkMusig2EndToEndVector : Bool :=
  let sk0 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
  let sk1 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
  match secpMul sk0 (.affine secpG), secpMul sk1 (.affine secpG) with
  | .affine p0, .affine p1 =>
      let pk0 := realMusigCrypto.compress p0
      let pk1 := realMusigCrypto.compress p1
      let sorted := BitcoinLedger.Musig2.keySort [pk0, pk1]
      match BitcoinLedger.Musig2.keyAgg realMusigCrypto sorted with
      | .error _ => false
      | .ok baseCtx =>
          let untweakedPk := realMusigCrypto.compress baseCtx.q
          let tapTw := BitcoinLedger.Musig2.computeTapTweakScalar realMusigCrypto untweakedPk none
          match BitcoinLedger.Musig2.applyTweak realMusigCrypto baseCtx tapTw with
          | .error _ => false
          | .ok tweakedCtx =>
              let tweakedPk := realMusigCrypto.compress tweakedCtx.q
              let walletId := realMusigCrypto.sha256 "MuSig2 wallet".toUTF8
              let txId := realMusigCrypto.sha256 "Unsigned PSBT tx".toUTF8
              let sid := BitcoinLedger.Musig2.computeVanadiumPsbtSessionId realMusigCrypto walletId txId
              let randRoot0 := realMusigCrypto.sha256 "Device CSPRNG root 0".toUTF8
              let randPeer1 := realMusigCrypto.sha256 "Peer 1 nonce root".toUTF8
              let task0 : InternalSpec.Musig2.MusigSignTask := {
                inputIndex := 0
                placeholderIndex := 0
                internalPk := pk0
                untweakedAggPk := untweakedPk
                tweakedAggPk := tweakedPk
                sortedPubkeys := sorted
                tweaks := [tapTw]
                leafHash := none
              }
              let store0 := BitcoinLedger.Musig2.vanadiumDefaultStore
              match BitcoinLedger.Musig2.executeRound1Pass realMusigCrypto .tweakedVanadium store0 sid randRoot0 [task0],
                    BitcoinLedger.Musig2.nonceGen realMusigCrypto randPeer1 pk1 (BitcoinLedger.Musig2.xOnlyOfCompressed tweakedPk) with
              | .ok ([r1Out], store1), .ok (secPeer1, pubPeer1) =>
                  let msg32 := realMusigCrypto.sha256 "TapSighash for MuSig2 input 0".toUTF8
                  let orderedNonces :=
                    if sorted[0]? == some pk0 then [r1Out.pubnonce, pubPeer1] else [pubPeer1, r1Out.pubnonce]
                  let r2In : InternalSpec.Musig2.MusigRound2TaskInput := {
                    task := task0
                    secretKey := BitcoinLedger.Musig2.scalarToBytes32 sk0
                    sighash := msg32
                    psbtMyPubnonce := some r1Out.pubnonce
                    cosignerPubnonces := orderedNonces
                  }
                  match BitcoinLedger.Musig2.executeRound2Pass realMusigCrypto .tweakedVanadium store1 sid [r2In] true,
                        BitcoinLedger.Musig2.nonceAgg realMusigCrypto orderedNonces with
                  | .ok ([r2Out], store2), .ok aggnonce =>
                      let ctx : InternalSpec.Musig2.SessionContext := {
                        aggnonce := aggnonce
                        pubkeys := sorted
                        tweaks := [tapTw]
                        msg := msg32.bytes
                      }
                      match BitcoinLedger.Musig2.partialSign realMusigCrypto secPeer1
                              (BitcoinLedger.Musig2.scalarToBytes32 sk1) ctx with
                      | .error _ => false
                      | .ok psigPeer1 =>
                          let orderedSigs :=
                            if sorted[0]? == some pk0 then [r2Out.signature, psigPeer1] else [psigPeer1, r2Out.signature]
                          match BitcoinLedger.Musig2.partialSigAgg realMusigCrypto ctx orderedSigs with
                          | .error _ => false
                          | .ok schnorr64 =>
                              -- Session was atomically consumed (`lookupActive == none`) AND replay fails AND BIP-340 verifies!
                              let replayRejected :=
                                (BitcoinLedger.Musig2.executeRound2Pass realMusigCrypto .tweakedVanadium store2 sid [r2In] true).isOk == false
                              let sigValid :=
                                bip340VerifyBytes (realMusigCrypto.xCoord tweakedCtx.q).bytes msg32.bytes schnorr64.bytes
                              (BitcoinLedger.Musig2.lookupActive store2 sid).isNone && replayRejected && sigValid
                  | _, _ => false
              | _, _ => false
  | _, _ => false

/-! ### A.6 BIP-352 / BIP-374 / BIP-375 / BIP-392 Silent Payments & Message Signing (`integration_test.rs`) -/

def checkSilentPaymentsAndMessageSigning : Bool :=
  let bech := BitcoinLedger.SilentPayments.canonicalBech32mCodec
  -- 1. Official BIP-352 mainnet Silent Payment address from `integration_test.rs:132`
  let bip352Addr := "sp1qqgste7k9hx0qftg6qmwlkqtwuy6cycyavzmzj85c6qdfhjdpdjtdgqjuexzk6murw56suy3e0rd2cgqvycxttddwsvgxe2usfpxumr70xc9pkqwv"
  let spAddrRoundTripOk :=
    match BitcoinLedger.SilentPayments.decodeSpAddress realSpCrypto bech bip352Addr with
    | .error _ => false
    | .ok (hrp, code) =>
        hrp == .sp &&
        BitcoinLedger.SilentPayments.encodeSpAddress realSpCrypto bech hrp code == .ok bip352Addr &&
        -- Now run full BIP-375 `finalizePsbtSilentPayments` sending to `code` + verify BIP-374 DLEQ proof!
        let inPriv : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
        let outpointTxid := mkSpSizedBytes! 32 (sha256Bytes "sp-input-prevout".toUTF8)
        let spInput : InternalSpec.SilentPayments.PsbtSpInput := {
          outpoint := { txid := outpointTxid, vout := 0 }
          scriptKind := .wpkh
          prevoutWitnessVersion := some 0
          sighashType := none
          deviceEligiblePrivKey := some inPriv
          hasInputSpEcdhShare := false
          hasInputSpDleq := false
        }
        let spOut : InternalSpec.SilentPayments.PsbtSpOutput := {
          amount := 50_000
          script := none
          spV0Info := some (BitcoinLedger.SilentPayments.serializeSpCode realSpCrypto code)
          spV0Label := none
        }
        let spTx : InternalSpec.SilentPayments.PsbtSpTx SecpAffine := {
          txModifiable := some 0
          inputs := [spInput]
          outputs := [spOut]
          globalEcdhShares := []
          globalDleqProofs := []
        }
        let auxRand := mkSpSizedBytes! 32 (sha256Bytes "dleq-aux-rand".toUTF8)
        match BitcoinLedger.SilentPayments.finalizePsbtSilentPayments realSpCrypto spTx auxRand,
              realSpCrypto.pointMul inPriv (.affine secpG) with
        | .ok ([shareOut], [scriptOut]), .affine aPub =>
            match realSpCrypto.decompress shareOut.share with
            | some cPt =>
                scriptOut.outputIndex == 0 &&
                scriptOut.script.bytes.data[0]? == some 0x51 &&
                scriptOut.script.bytes.data[1]? == some 0x20 &&
                BitcoinLedger.SilentPayments.dleqVerify
                  realSpCrypto aPub code.scan cPt shareOut.dleqProof secpG none
            | none => false
        | _, _ => false

  -- 2. BIP-392 `tspscan` round-trip & change-label (`m = 0`) rejection (`account.rs:84-90`)
  let spScanAndLabelOk :=
    match secpMul 0x424242 (.affine secpG) with
    | .infinity => false
    | .affine bSpend =>
        match BitcoinLedger.SilentPayments.mkCheckedSpAccount 0 0x123456 bSpend with
        | .error _ => false
        | .ok spAcc =>
            let changeRejected :=
              BitcoinLedger.SilentPayments.deriveAccountSpAddress
                realSpCrypto bech .tsp spAcc (.code (some 0)) == .error .silentPaymentChangeLabel
            let validCodeOk :=
              (BitcoinLedger.SilentPayments.deriveAccountSpAddress
                realSpCrypto bech .tsp spAcc (.code none)).isOk
            let scanExportOk :=
              match BitcoinLedger.SilentPayments.exportSpScanKey
                      realSpCrypto bech .tspscan (fun _ => .ok spAcc) 0 true with
              | .error _ => false
              | .ok tspscanStr =>
                  BitcoinLedger.SilentPayments.decodeSpScanKey realSpCrypto bech tspscanStr ==
                    .ok (.tspscan, 0x123456, bSpend)
            let scanRejectUnapproved :=
              BitcoinLedger.SilentPayments.exportSpScanKey
                realSpCrypto bech .tspscan (fun _ => .ok spAcc) 0 false == .error .userRejected
            changeRejected && validCodeOk && scanExportOk && scanRejectUnapproved

  -- 3. BIP-137 `bitcoinSignedMessageDigest` & BIP-322 virtual PSBT (`validateBip322Psbt`)
  let msg := "Hello Vanadium & Lean!".toUTF8
  let bsmDigest := BitcoinLedger.AppStateMachine.bitcoinSignedMessageDigest realMusigCrypto.sha256 msg
  let challengeSpk := BitcoinLedger.Script.mkP2WPKH (hash160Bytes (secpCompressBytes secpG))
  let toSpendTx := BitcoinLedger.Psbt.buildBip322ToSpendTx vanadiumTestnetPsbtOracles.sha256 msg challengeSpk
  let toSpendTxid := BitcoinLedger.Psbt.computeBip322ToSpendTxid vanadiumTestnetPsbtOracles.sha256 msg challengeSpk
  let bip322Psbt : InternalSpec.Psbt.PsbtTx := {
    txVersion := 0
    fallbackLocktime := some 0
    inputs := #[{
      prevout := { txid := toSpendTxid, vout := 0 }
      sequence := some 0
      nonWitnessUtxo := some toSpendTx
      witnessUtxo := some { amount := 0, scriptPubKey := challengeSpk }
      derivations := [{
        pubkey := secpCompressBytes secpG
        origin := { fingerprint := 0xf5acc2fd, path := [h84, h1, h0, 0, 0] }
      }]
    }]
    outputs := #[{ amount := 0, scriptPubKey := some (ByteArray.mk #[0x6a]) }]
    bip322Message := some msg
  }
  let mockBip322Pol : InternalSpec.Psbt.WalletPolicySpec := {
    isDefault := true
    name := ""
    spendClass := .segwitV0
    internalPlaceholders := [{
      keyIndex := 0
      expectedOrigin := some { fingerprint := 0xf5acc2fd, path := [h84, h1, h0] }
      numFirst := 0
      numSecond := 1
      isMusig := false
    }]
    deriveScripts := fun isChg idx =>
      if !isChg && idx == 0 then some (challengeSpk, none, none) else none
  }
  let bip322Cfg := BitcoinLedger.AppStateMachine.signingConfigOfTarget (.bolos 1) false
  let bip322Ok :=
    bsmDigest.bytes.size == 32 &&
    BitcoinLedger.AppStateMachine.isPrintableAsciiMessage msg &&
    (BitcoinLedger.Psbt.authorizePsbtSigning vanadiumTestnetPsbtOracles bip322Cfg mockBip322Pol bip322Psbt none).isOk &&
    -- Tampering with the message causes `.bip322ChallengeTxidMismatch`!
    isPsbtErr
      (BitcoinLedger.Psbt.authorizePsbtSigning vanadiumTestnetPsbtOracles bip322Cfg mockBip322Pol
        { bip322Psbt with bip322Message := some "Tampered!".toUTF8 } none)
      .bip322ChallengeTxidMismatch

  spAddrRoundTripOk && spScanAndLabelOk && bip322Ok

/-! ============================================================================================
    PART B: EXPLICIT UPSTREAM-BUG REGRESSION SUITE (`VND-BUG-001` .. `VND-BUG-009`)
    From `docs/spec-cards/vanadium-upstream-bugs.md` (`LedgerHQ/vanadium` `ace8e96982408959dea9e7fbc59ee36e8c54e645`)
    ============================================================================================ -/

/-! ### `VND-BUG-001` [CRITICAL]: `Andor(X, Y, Z)` Compiles Canonical `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`
    Vanadium `apps/bitcoin/common/src/script.rs:367-373` emitted `[X] OP_NOTIF [Y] OP_ELSE [Z] OP_ENDIF`,
    swapping the true and false branches. -/

/-- Formal proof that `BitcoinLedger.WalletPolicy.compileMiniscript` on `.andor x y z` emits
    canonical BIP-379 `[sx] OP_NOTIF (0x64) [sz] OP_ELSE (0x67) [sy] OP_ENDIF (0x68)`. -/
theorem vnd_bug_001_andor_canonical_branch_order
    (ora : BitcoinLedger.WalletPolicy.CryptoPolicyOracle)
    (net : BitcoinLedger.WalletPolicy.Network)
    (keys : List BitcoinLedger.WalletPolicy.WalletKeyInfo)
    (ctx : BitcoinLedger.WalletPolicy.MiniscriptCtx)
    (isChange : Bool) (addrIdx : UInt32)
    (x y z : BitcoinLedger.WalletPolicy.Miniscript)
    (sx sy sz : ByteArray)
    (hx : BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false x = .ok sx)
    (hy : BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false y = .ok sy)
    (hz : BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false z = .ok sz) :
    BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false (.andor x y z) =
      .ok (sx ++ ByteArray.mk #[0x64] ++ sz ++ ByteArray.mk #[0x67] ++ sy ++ ByteArray.mk #[0x68]) := by
  simp [BitcoinLedger.WalletPolicy.compileMiniscript, hx, hy, hz,
    BitcoinLedger.WalletPolicy.OP_NOTIF, BitcoinLedger.WalletPolicy.OP_ELSE,
    BitcoinLedger.WalletPolicy.OP_ENDIF, BitcoinLedger.WalletPolicy.emitOpVerify]
  rfl

def checkVndBug001 : Bool :=
  let k0 := "[f5acc2fd/48'/1'/0'/2']tpubDFAqEGNyad35aBCKUAXbQGDjdVhNueno5ZZVEn3sQbW5ci457gLR7HyTmHBg93oourBssgUxuWz1jX5uhc1qaqFo9VsybY1J5FuedLfm4dK"
  let k1 := "[d5365b22/48'/1'/0'/2']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
  let _ := k1
  match parseV2TestnetPolicy "Andor regression" "wsh(andor(pk(@0/**),older(1000),pk(@1/**)))" [
          k0,
          "[d5365b22/48'/1'/0'/2']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
        ] with
  | .error _ => false
  | .ok pol =>
      let xNode : BitcoinLedger.WalletPolicy.Miniscript := .pk (.single 0 .wildcard)
      let yNode : BitcoinLedger.WalletPolicy.Miniscript := .older 1000
      let zNode : BitcoinLedger.WalletPolicy.Miniscript := .pk (.single 1 .wildcard)
      match BitcoinLedger.WalletPolicy.compileMiniscript realPolicyOracle .testnet pol.keys .wshCtx false 0 false xNode,
            BitcoinLedger.WalletPolicy.compileMiniscript realPolicyOracle .testnet pol.keys .wshCtx false 0 false yNode,
            BitcoinLedger.WalletPolicy.compileMiniscript realPolicyOracle .testnet pol.keys .wshCtx false 0 false zNode,
            BitcoinLedger.WalletPolicy.compileMiniscript realPolicyOracle .testnet pol.keys .wshCtx false 0 false (.andor xNode yNode zNode) with
      | .ok sx, .ok sy, .ok sz, .ok sAndor =>
          let canonical := sx ++ ByteArray.mk #[0x64] ++ sz ++ ByteArray.mk #[0x67] ++ sy ++ ByteArray.mk #[0x68]
          let vanadiumBuggy := sx ++ ByteArray.mk #[0x64] ++ sy ++ ByteArray.mk #[0x67] ++ sz ++ ByteArray.mk #[0x68]
          sAndor == canonical && sAndor != vanadiumBuggy
      | _, _, _, _ => false

/-! ### `VND-BUG-002` [CRITICAL]: Checked `UInt64` Satoshi Sums & `MAX_MONEY` / `i64::MIN` Sign-Flip Defense
    Vanadium `fastpsbt.rs:1052,1120`, `analyze.rs:146,179,434-435,460`, `display.rs:153` omitted
    `<= MAX_MONEY` checks, summed `u64` unchecked, and cast `value as i64` (`>= 2^63` negative!). -/

theorem vnd_bug_002_i64_min_and_u64_max_rejected :
    BitcoinLedger.Basic.isValidAmount 0x8000000000000000 = false ∧
    BitcoinLedger.Basic.isValidAmount 0xFFFFFFFFFFFFFFFF = false ∧
    BitcoinLedger.Basic.isValidAmount (BitcoinLedger.Basic.MAX_MONEY + 1) = false ∧
    BitcoinLedger.FreestandingKernels.llbValidAmount 0x8000000000000000 = false ∧
    BitcoinLedger.FreestandingKernels.llbCheckedAddSatsOk BitcoinLedger.Basic.MAX_MONEY 1 = false ∧
    BitcoinLedger.FreestandingKernels.llbCheckedSubSatsOk 100 101 = false := by
  decide

#guard BitcoinLedger.Basic.checkedAddSats? BitcoinLedger.Basic.MAX_MONEY 0 == some BitcoinLedger.Basic.MAX_MONEY
#guard BitcoinLedger.Basic.checkedAddSats? BitcoinLedger.Basic.MAX_MONEY 1 == none
#guard BitcoinLedger.Basic.checkedAddSats? 0x8000000000000000 1 == none
#guard BitcoinLedger.Basic.checkedSumSats? [1_500_000_000_000_000, 700_000_000_000_000] == none
#guard BitcoinLedger.Basic.checkedSubSats? 50_000 50_001 == none

def checkVndBug002 : Bool :=
  let spk0 := BitcoinLedger.Script.mkP2WPKH (ByteArray.mk (Array.replicate 20 0x11))
  let spkOut := BitcoinLedger.Script.mkP2WPKH (ByteArray.mk (Array.replicate 20 0x22))
  let pol : InternalSpec.Psbt.WalletPolicySpec := {
    isDefault := true
    name := ""
    spendClass := .segwitV0
    internalPlaceholders := [{
      keyIndex := 0
      expectedOrigin := some { fingerprint := 0xf5acc2fd, path := [h84, h1, h0] }
      numFirst := 0
      numSecond := 1
      isMusig := false
    }]
    deriveScripts := fun isChg idx => if !isChg && idx == 0 then some (spk0, none, none) else none
  }
  let mkInp (amt : Nat) (vout : UInt32) : InternalSpec.Psbt.PsbtInput := {
    prevout := { txid := InternalSpec.Psbt.zeroBytes32, vout := vout }
    witnessUtxo := some { amount := amt, scriptPubKey := spk0 }
    derivations := [{ pubkey := ByteArray.mk (Array.replicate 33 0x02),
                      origin := { fingerprint := 0xf5acc2fd, path := [h84, h1, h0, 0, 0] } }]
  }
  let cfg := BitcoinLedger.AppStateMachine.signingConfigOfTarget (.vanadium 1) false
  -- Subcase 1: `2^63` (`i64::MIN` cast sign-flip vector) on input UTXO -> `.amountExceedsMaxSupply`
  let psbtSignFlip : InternalSpec.Psbt.PsbtTx := {
    txVersion := 2
    inputs := #[mkInp 0x8000000000000000 0]
    outputs := #[{ amount := 1000, scriptPubKey := some spkOut }]
  }
  -- Subcase 2: Two individually valid inputs (`<= MAX_MONEY`) whose sum exceeds `MAX_MONEY`
  let psbtSumOverflow : InternalSpec.Psbt.PsbtTx := {
    txVersion := 2
    inputs := #[mkInp 1_500_000_000_000_000 0, mkInp 700_000_000_000_000 1]
    outputs := #[{ amount := 1000, scriptPubKey := some spkOut }]
  }
  -- Subcase 3: Output sum exceeds input sum -> `.negativeFeeOutputsExceedInputs`
  let psbtNegFee : InternalSpec.Psbt.PsbtTx := {
    txVersion := 2
    inputs := #[mkInp 10_000 0]
    outputs := #[{ amount := 10_001, scriptPubKey := some spkOut }]
  }
  isPsbtErr (BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles cfg pol psbtSignFlip)
    .amountExceedsMaxSupply &&
  isPsbtErr (BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles cfg pol psbtSumOverflow)
    .amountExceedsMaxSupply &&
  isPsbtErr (BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles cfg pol psbtNegFee)
    .negativeFeeOutputsExceedInputs

/-! ### `VND-BUG-003` [HIGH — CVE-2020-14199]: Dual-UTXO Cross-Check (`non_witness_utxo` vs `witness_utxo`)
    Vanadium `analyze.rs:223-243, 304-316` verified `txid(non_witness_utxo) == prevout.txid` (silencing
    `missing_nonwitnessutxo`) without checking `non_witness_utxo.output[vout] == witness_utxo`! -/

theorem vnd_bug_003_dual_utxo_mismatch_always_rejected
    (sha256 : ByteArray → InternalSpec.Psbt.Bytes32)
    (rawTx : InternalSpec.Psbt.RawTx)
    (wUtxo : InternalSpec.Psbt.TxOut)
    (inp : InternalSpec.Psbt.PsbtInput)
    (hNonWit : inp.nonWitnessUtxo = some rawTx)
    (hWit : inp.witnessUtxo = some wUtxo)
    (hTxid : BitcoinLedger.Psbt.eqBytes32 (BitcoinLedger.Psbt.computeTxid sha256 rawTx) inp.prevout.txid = true)
    (hBounds : inp.prevout.vout.toNat < rawTx.vout.size)
    (hSpoof : BitcoinLedger.Psbt.eqTxOut (rawTx.vout[inp.prevout.vout.toNat]'hBounds) wUtxo = false) :
    BitcoinLedger.Psbt.extractInputPrevout sha256 inp = .error .dualUtxoMismatch := by
  unfold BitcoinLedger.Psbt.extractInputPrevout
  simp [hNonWit, hWit, hTxid, hBounds, hSpoof]

def checkVndBug003 : Bool :=
  let spk0 := BitcoinLedger.Script.mkP2WPKH (ByteArray.mk (Array.replicate 20 0x33))
  let spkSpoof := BitcoinLedger.Script.mkP2WPKH (ByteArray.mk (Array.replicate 20 0x44))
  let realPrevTx : InternalSpec.Psbt.RawTx := {
    version := 2
    vin := #[{
      prevout := { txid := InternalSpec.Psbt.zeroBytes32, vout := 0 }
      scriptSig := ByteArray.empty
      sequence := 0xFFFFFFFF
    }]
    vout := #[{ amount := 100_000, scriptPubKey := spk0 }]
    locktime := 0
  }
  let realPrevTxid := BitcoinLedger.Psbt.computeTxid vanadiumTestnetPsbtOracles.sha256 realPrevTx
  let baseInp : InternalSpec.Psbt.PsbtInput := {
    prevout := { txid := realPrevTxid, vout := 0 }
    nonWitnessUtxo := some realPrevTx
    witnessUtxo := some { amount := 100_000, scriptPubKey := spk0 }
  }
  -- Matching dual UTXO is accepted cleanly (`hasNonWitness = true`)
  let validDualOk :=
    BitcoinLedger.Psbt.extractInputPrevout vanadiumTestnetPsbtOracles.sha256 baseInp ==
      .ok ({ amount := 100_000, scriptPubKey := spk0 }, true)
  -- Spoofed amount (`500_000_000` vs real `100_000`) with genuine `nonWitnessUtxo` -> `.dualUtxoMismatch`!
  let spoofAmtRejected :=
    BitcoinLedger.Psbt.extractInputPrevout vanadiumTestnetPsbtOracles.sha256
      { baseInp with witnessUtxo := some { amount := 500_000_000, scriptPubKey := spk0 } } ==
      .error .dualUtxoMismatch
  -- Spoofed `scriptPubKey` with genuine `nonWitnessUtxo` -> `.dualUtxoMismatch`!
  let spoofSpkRejected :=
    BitcoinLedger.Psbt.extractInputPrevout vanadiumTestnetPsbtOracles.sha256
      { baseInp with witnessUtxo := some { amount := 100_000, scriptPubKey := spkSpoof } } ==
      .error .dualUtxoMismatch
  validDualOk && spoofAmtRejected && spoofSpkRejected

/-! ### `VND-BUG-004` [HIGH — BIP-370 Locktime]: Dual-Locktime Input, Zero Height, and Fallback Domain Switch
    Vanadium `fastpsbt.rs:602-634`:
    1. Rejected valid single inputs providing both height & time locktimes;
    2. Failed to reject `requiredHeightLocktime == 0`;
    3. Computed `fallback.max(h)`, letting `fallback >= 500_000_000` switch height `h` to UNIX timestamp! -/

def vndBug004BaseInp : InternalSpec.Psbt.PsbtInput :=
  { prevout := { txid := InternalSpec.Psbt.zeroBytes32, vout := 0 } }

theorem vnd_bug_004_bip370_locktime_regressions :
    -- (1) Single input with BOTH height & time locktimes succeeds and selects height (`800_000`)
    BitcoinLedger.Psbt.determineLocktime (some 0)
      [{ vndBug004BaseInp with requiredHeightLocktime := some 800_000, requiredTimeLocktime := some 1_700_000_000 }] =
      .ok 800_000 ∧
    -- (1b) Dual-locktime input paired with a time-only input harmoniously selects time (`1_700_000_000`)
    BitcoinLedger.Psbt.determineLocktime (some 0)
      [ { vndBug004BaseInp with requiredHeightLocktime := some 800_000, requiredTimeLocktime := some 1_700_000_000 },
        { vndBug004BaseInp with requiredTimeLocktime := some 1_650_000_000 } ] =
      .ok 1_700_000_000 ∧
    -- (2) `requiredHeightLocktime = some 0` is strictly rejected
    BitcoinLedger.Psbt.determineLocktime (some 0)
      [{ vndBug004BaseInp with requiredHeightLocktime := some 0 }] =
      .error .locktimeConflictOrInvalid ∧
    -- (3) `fallbackLocktime = some 600_000_000` (timestamp) NEVER overrides input height `850_000`!
    BitcoinLedger.Psbt.determineLocktime (some 600_000_000)
      [{ vndBug004BaseInp with requiredHeightLocktime := some 850_000 }] =
      .ok 850_000 := by
  decide

#guard BitcoinLedger.Psbt.determineLocktime (some 600_000_000) [] == .ok 600_000_000
#guard BitcoinLedger.Psbt.determineLocktime (some 0)
  [ { vndBug004BaseInp with requiredHeightLocktime := some 800_000 },
    { vndBug004BaseInp with requiredTimeLocktime := some 1_700_000_000 } ] == .error .locktimeConflictOrInvalid

def checkVndBug004 : Bool :=
  BitcoinLedger.Psbt.determineLocktime (some 0)
    [{ vndBug004BaseInp with requiredHeightLocktime := some 800_000, requiredTimeLocktime := some 1_700_000_000 }] == .ok 800_000 &&
  BitcoinLedger.Psbt.determineLocktime (some 0)
    [{ vndBug004BaseInp with requiredHeightLocktime := some 0 }] == .error .locktimeConflictOrInvalid &&
  BitcoinLedger.Psbt.determineLocktime (some 600_000_000)
    [{ vndBug004BaseInp with requiredHeightLocktime := some 850_000 }] == .ok 850_000

/-! ### `VND-BUG-005` [MEDIUM — BIP-388]: `sh(wsh(...))` Consistency Between Registration & Derivation
    Vanadium `register_account` issued a valid PoR for `sh(wsh(...))` while `to_script` rejected it with
    `InvalidScriptContext`, stranding every registered `sh(wsh(...))` account.
    In `BitcoinLedger.WalletPolicy`:
    - `canonicalLedgerProfile` and `bolosAppProfile` BOTH register AND derive `sh(wsh(sortedmulti(...)))` cleanly;
    - `vanadiumAppProfile` (`allowShWsh = false`) rejects `sh(wsh(...))` upfront at `validatePolicyRegistration`,
      guaranteeing no unspendable/underivable PoR is ever issued! -/

theorem vnd_bug_005_vanadium_profile_rejects_sh_wsh_at_registration
    (net : BitcoinLedger.WalletPolicy.Network)
    (fmt : BitcoinLedger.WalletPolicy.PolicyFormat)
    (inner : BitcoinLedger.WalletPolicy.WshScript) :
    BitcoinLedger.WalletPolicy.checkDescriptorTemplate
      (BitcoinLedger.WalletPolicy.vanadiumAppProfile net) fmt (.sh (.wsh inner)) =
      .error .invalidScriptContext := by
  simp [BitcoinLedger.WalletPolicy.checkDescriptorTemplate, BitcoinLedger.WalletPolicy.vanadiumAppProfile]
  rfl

def checkVndBug005 : Bool :=
  -- Derive the authentic `m/48'/1'/0'/1'` `tpub` for Speculos device `0xf5acc2fd` (`sh(wsh(...))` script_type = `1'`)
  match evalVanadiumTpub? .standard #[h48, h1, h0, h1] with
  | none => false
  | some dev48h1Tpub =>
      let k0 := s!"[f5acc2fd/48'/1'/0'/1']{dev48h1Tpub}"
      let k1 := "[d5365b22/48'/1'/0'/1']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
      match parseV2TestnetPolicy "Nested SegWit Multisig" "sh(wsh(sortedmulti(2,@0/**,@1/**)))" [k0, k1] with
  | .error _ => false
  | .ok pol =>
      let canonProf := BitcoinLedger.WalletPolicy.canonicalLedgerProfile .testnet
      let bolosProf := BitcoinLedger.WalletPolicy.bolosAppProfile .testnet
      let vndProf := BitcoinLedger.WalletPolicy.vanadiumAppProfile .testnet
      -- Canonical & BOLOS profiles both register AND derive 23-byte P2SH `0xa9 0x14 <20B> 0x87` cleanly
      let canonConsistent :=
        (BitcoinLedger.WalletPolicy.validatePolicyRegistration canonProf vanadiumDeviceOracle pol true).isOk &&
        (match BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile canonProf realPolicyOracle pol false 0 with
         | .ok spk => spk.size == 23 && spk.data[0]? == some 0xa9 && spk.data[22]? == some 0x87
         | .error _ => false)
      let bolosConsistent :=
        (BitcoinLedger.WalletPolicy.validatePolicyRegistration bolosProf vanadiumDeviceOracle pol true).isOk &&
        (BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile bolosProf realPolicyOracle pol false 0).isOk
      -- Vanadium profile rejects upfront at registration so a stranded PoR cannot be minted
      let vndRejectsUpfront :=
        BitcoinLedger.WalletPolicy.validatePolicyRegistration vndProf vanadiumDeviceOracle pol true ==
          .error .invalidScriptContext
      canonConsistent && bolosConsistent && vndRejectsUpfront

/-! ### `VND-BUG-006` [MEDIUM — BIP-379 Soundness]: Miniscript Type, Malleability, Signature, Timelock & Ownership
    Vanadium `bip388-0.1.2/src/lib.rs:5` (`// TODO: - add type checks - add malleability checks - add stack limits`)
    and `register_account.rs` omitted BIP-379 `B/V/K/W` typechecking, non-malleability (`m`), unconditional
    signature (`s`), height/time timelock mixing (`k`), BIP-68 `older(n)` upper-bit checks, P2WSH resource
    limits, and `n_internal_keys >= 1` at registration. -/

def vndBug006Hash32 : ByteArray := ByteArray.mk (Array.replicate 32 0xAB)

theorem vnd_bug_006_miniscript_bip379_sanity_gates :
    -- (1) Non-`B` top-level (`pk_k` has type `K`, `v:pk` has type `V`) -> `.invalidMiniscriptType`
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64 (.pk_k (.single 0 .wildcard)) =
      .error .invalidMiniscriptType ∧
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64 (.wrap .v (.pk (.single 0 .wildcard))) =
      .error .invalidMiniscriptType ∧
    -- (2) Malleable Miniscript (`andor(sha256(H), pk(@0), pk(@1))` where `sha256` lacks `e` property) -> `.miniscriptMalleable`
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64
      (.andor (.sha256 vndBug006Hash32) (.pk (.single 0 .wildcard)) (.pk (.single 1 .wildcard))) =
      .error .miniscriptMalleable ∧
    -- (3) Missing unconditional signature (`or_i(pk(@0), older(10))`) -> `.miniscriptMissingSignature`
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64
      (.or_i (.pk (.single 0 .wildcard)) (.older 10)) =
      .error .miniscriptMissingSignature ∧
    -- (4) Height/time timelock mixing (`and_v(v:pk(@0), and_v(v:older(10), older(0x0040000A)))`) -> `.miniscriptTimelockMix`
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64
      (.and_v (.wrap .v (.pk (.single 0 .wildcard)))
        (.and_v (.wrap .v (.older 10)) (.older 0x0040000A))) =
      .error .miniscriptTimelockMix ∧
    -- (5) Absolute height/time mixing (`and_v(v:pk(@0), and_v(v:after(100), after(500_000_000)))`) -> `.miniscriptTimelockMix`
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64
      (.and_v (.wrap .v (.pk (.single 0 .wildcard)))
        (.and_v (.wrap .v (.after 100)) (.after 500_000_000))) =
      .error .miniscriptTimelockMix ∧
    -- (6) BIP-68 invalid `older(n)` upper bits (`0`, bit 31 disable `0x80000001`, bit 16 `0x00010001`) -> `.invalidTimelockRange`
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64 (.older 0) =
      .error .invalidTimelockRange ∧
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64 (.older 0x80000001) =
      .error .invalidTimelockRange ∧
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64 (.older 0x00010001) =
      .error .invalidTimelockRange := by
  decide

def checkVndBug006 : Bool :=
  let prof := BitcoinLedger.WalletPolicy.vanadiumAppProfile .testnet
  -- Build a P2WSH `thresh` of 210 `pk` / `s:pk` branches exceeding the 201-op P2WSH consensus limit -> `.miniscriptResourceLimit`
  let children210 : List BitcoinLedger.WalletPolicy.Miniscript :=
    (.pk (.single 0 .wildcard)) :: (List.replicate 209 (.wrap .s (.pk (.single 0 .wildcard))))
  let resourceRejected :=
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 20 999 64 (.thresh 210 children210) ==
      .error .miniscriptResourceLimit
  -- External-only policy (`0` internal device keys) rejected at registration with `.missingInternalKey`
  let extOnlyKey := "[d5365b22/84'/1'/0']tpubDFWK5mCX28dt6hfy74Bc51jjbWrimXow1bTxCMpJrWqesK3AeZiYn8tcLFW3VoBiHhM9FjKdLWaC3GZVVX5PfGNG3zfbM14bMb1SLym36nN"
  let missingInternalRejected :=
    match parseV2TestnetPolicy "Foreign watch-only" "wpkh(@0/**)" [extOnlyKey] with
    | .error _ => false
    | .ok extPol =>
        BitcoinLedger.WalletPolicy.validatePolicyRegistration prof vanadiumDeviceOracle extPol true ==
          .error .missingInternalKey
  resourceRejected && missingInternalRejected

/-! ### `VND-BUG-007` [MEDIUM — BIP-32 Serialization]: Off-by-One `depth == 256` `u8` Wraparound on `Resident`
    Vanadium `get_extended_pubkey.rs:138, 161` checked `len > 256` instead of `> 255` (`u8::MAX`),
    then cast `len as u8`, wrapping `256 -> depth = 0` with non-zero `parentFingerprint`/`childNumber`. -/

def vndBug007Path255 : Array UInt32 := Array.replicate 255 0
def vndBug007Path256 : Array UInt32 := Array.replicate 256 0

set_option maxRecDepth 4096 in
theorem vnd_bug_007_depth_256_rejected_without_u8_wraparound :
    BitcoinLedger.Bip32.checkByteDepth vndBug007Path255 = true ∧
    BitcoinLedger.Bip32.checkByteDepth vndBug007Path256 = false ∧
    BitcoinLedger.Bip32.serializeBip32Path? vndBug007Path256 = none ∧
    BitcoinLedger.Bip32.classifyExpubPathWithTree
      BitcoinLedger.Bip32.vanadiumExpubPolicyConfig .testnet .resident vndBug007Path256 =
      .reject .bip32PathTooLong ∧
    BitcoinLedger.Bip32.classifyExpubPathWithTree
      BitcoinLedger.Bip32.vanadiumHardenedExpubPolicyConfig .testnet .resident vndBug007Path256 =
      .reject .bip32PathTooLong := by
  decide

set_option maxRecDepth 4096 in
theorem vnd_bug_007_derive_and_eval_reject_depth_256
    (ora : InternalSpec.CryptoDerivationOracle) (net : InternalSpec.Network) (display approved : Bool) :
    BitcoinLedger.Bip32.deriveExtendedPubKeyWithOracle ora net .resident vndBug007Path256 = none ∧
    BitcoinLedger.Bip32.evalGetExtendedPubkey
      ora BitcoinLedger.Bip32.vanadiumExpubPolicyConfig net .resident vndBug007Path256 display approved =
      .error .bip32PathTooLong := by
  constructor
  · unfold BitcoinLedger.Bip32.deriveExtendedPubKeyWithOracle
    have hGt : decide (vndBug007Path256.size > BitcoinLedger.Bip32.MAX_BIP32_BYTE_DEPTH) = true := by decide
    simp [hGt]
  · unfold BitcoinLedger.Bip32.evalGetExtendedPubkey BitcoinLedger.Bip32.authorizeExtendedPubKeyExport
    have hRej :
        BitcoinLedger.Bip32.classifyExpubPathWithTree
          BitcoinLedger.Bip32.vanadiumExpubPolicyConfig net .resident vndBug007Path256 =
          .reject .bip32PathTooLong := by
      cases net <;> decide
    simp [hRej]
    rfl

def checkVndBug007 : Bool :=
  -- Also verify that a serialized 78-byte xpub with wrapped `depth = 0` and non-zero `parentFingerprint`
  -- or non-zero `childNumber` is strictly rejected by `deserializeExtendedPubKey?` and `deserializeXpub78`!
  let wrappedRaw78 :=
    BitcoinLedger.Basic.encodeU32BE 0x043587CF ++
    ByteArray.mk #[0x00] ++ -- wrapped depth = 0!
    hex! "ad85d955" ++      -- non-zero parentFingerprint!
    BitcoinLedger.Basic.encodeU32BE 3 ++
    ByteArray.mk (Array.replicate 32 0xAA) ++
    secpCompressBytes secpG
  let evalRejected :=
    match BitcoinLedger.Bip32.evalGetExtendedPubkey
            vanadiumDerivationOracle BitcoinLedger.Bip32.vanadiumExpubPolicyConfig
            .testnet .resident vndBug007Path256 false true with
    | .error .bip32PathTooLong => true
    | _ => false
  BitcoinLedger.Bip32.checkByteDepth vndBug007Path255 &&
  !BitcoinLedger.Bip32.checkByteDepth vndBug007Path256 &&
  (BitcoinLedger.Bip32.deserializeExtendedPubKey? wrappedRaw78).isNone &&
  (BitcoinLedger.WalletPolicy.deserializeXpub78 wrappedRaw78).isNone &&
  evalRejected

/-! ### `VND-BUG-008` [LOW/MEDIUM — MuSig2]: Round-2 Self-Pubnonce Verification (`pubnonceMismatch`)
    Vanadium `musig_signing.rs:463-485` regenerated `_pubnonce` from `rand_root` in Round 2 and discarded
    it without verifying `_pubnonce == _my_pubnonce` from `PSBT_IN_MUSIG2_PUB_NONCE`. -/

theorem vnd_bug_008_corrupted_self_pubnonce_rejected
    {Affine : Type} (c : InternalSpec.Musig2.MusigCrypto Affine)
    (mode : InternalSpec.Musig2.NonceAggPkMode)
    (randRoot : InternalSpec.Musig2.RandRoot)
    (inp : InternalSpec.Musig2.MusigRound2TaskInput)
    (myPubnonce recomputedPubnonce aggnonce : InternalSpec.Musig2.PubNonce)
    (secnonce : InternalSpec.Musig2.SecNonce)
    (hNonEmpty : inp.task.sortedPubkeys.isEmpty = false)
    (hBound : decide (inp.task.sortedPubkeys.length > BitcoinLedger.Musig2.maxPubkeysPerMusig) = false)
    (hMyPn : inp.psbtMyPubnonce = some myPubnonce)
    (hLen : decide (inp.cosignerPubnonces.length ≠ inp.task.sortedPubkeys.length) = false)
    (hAgg : BitcoinLedger.Musig2.nonceAgg c inp.cosignerPubnonces = .ok aggnonce)
    (hGen : BitcoinLedger.Musig2.nonceGen c
      (BitcoinLedger.Musig2.syntheticRandIJ c randRoot inp.task.inputIndex inp.task.placeholderIndex)
      inp.task.internalPk
      (BitcoinLedger.Musig2.selectNonceAggPk mode inp.task.untweakedAggPk inp.task.tweakedAggPk) =
      .ok (secnonce, recomputedPubnonce))
    (hTamper : decide (recomputedPubnonce ≠ myPubnonce) = true) :
    BitcoinLedger.Musig2.round2SignTask c mode randRoot inp true = .error .pubnonceMismatch := by
  unfold BitcoinLedger.Musig2.round2SignTask
  simp [hNonEmpty, hBound, hMyPn, hLen, hAgg, hGen, hTamper]

def checkVndBug008 : Bool :=
  let sk0 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
  let sk1 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
  match secpMul sk0 (.affine secpG), secpMul sk1 (.affine secpG) with
  | .affine p0, .affine p1 =>
      let pk0 := realMusigCrypto.compress p0
      let pk1 := realMusigCrypto.compress p1
      let sorted := BitcoinLedger.Musig2.keySort [pk0, pk1]
      match BitcoinLedger.Musig2.keyAgg realMusigCrypto sorted with
      | .error _ => false
      | .ok baseCtx =>
          let untweakedPk := realMusigCrypto.compress baseCtx.q
          let sid := realMusigCrypto.sha256 "bug008-session".toUTF8
          let randRoot := realMusigCrypto.sha256 "bug008-randroot".toUTF8
          let bogusRand := realMusigCrypto.sha256 "corrupted-host-nonce".toUTF8
          let peerRand := realMusigCrypto.sha256 "peer-nonce".toUTF8
          let task0 : InternalSpec.Musig2.MusigSignTask := {
            inputIndex := 0
            placeholderIndex := 0
            internalPk := pk0
            untweakedAggPk := untweakedPk
            tweakedAggPk := untweakedPk
            sortedPubkeys := sorted
            tweaks := []
            leafHash := none
          }
          match BitcoinLedger.Musig2.executeRound1Pass realMusigCrypto .tweakedVanadium
                  BitcoinLedger.Musig2.vanadiumDefaultStore sid randRoot [task0],
                BitcoinLedger.Musig2.nonceGen realMusigCrypto bogusRand pk0 (BitcoinLedger.Musig2.xOnlyOfCompressed untweakedPk),
                BitcoinLedger.Musig2.nonceGen realMusigCrypto peerRand pk1 (BitcoinLedger.Musig2.xOnlyOfCompressed untweakedPk) with
          | .ok ([r1Out], store1), .ok (_, tamperedMyPubnonce), .ok (_, peerPubnonce) =>
              let tamperedInput : InternalSpec.Musig2.MusigRound2TaskInput := {
                task := task0
                secretKey := BitcoinLedger.Musig2.scalarToBytes32 sk0
                sighash := realMusigCrypto.sha256 "bug008-msg".toUTF8
                psbtMyPubnonce := some tamperedMyPubnonce
                cosignerPubnonces := [tamperedMyPubnonce, peerPubnonce]
              }
              let validInput : InternalSpec.Musig2.MusigRound2TaskInput := {
                tamperedInput with
                psbtMyPubnonce := some r1Out.pubnonce
                cosignerPubnonces := [r1Out.pubnonce, peerPubnonce]
              }
              -- With `checkSelfPubnonce = true`, tampered `psbtMyPubnonce` is rejected with `.pubnonceMismatch`
              -- AND the session is atomically burned (`lookupActive == none`) so the nonce can never be reused!
              match BitcoinLedger.Musig2.executeRound2Pass realMusigCrypto .tweakedVanadium store1 sid [tamperedInput] true with
              | .error (.pubnonceMismatch, burnedStore) =>
                  (BitcoinLedger.Musig2.lookupActive burnedStore sid).isNone &&
                  (BitcoinLedger.Musig2.round2SignTask realMusigCrypto .tweakedVanadium randRoot validInput true).isOk
              | _ => false
          | _, _, _ => false
  | _, _ => false

/-! ### `VND-BUG-009` [LOW — Wire / Parser]: `GetVersion` No-Panic, `OP_RETURN` Support, Canonical CompactSize & `>= 253`B UTXO Script
    1. `main.rs:26`: `Request::GetVersion` panicked with `todo!()`; `stepAppCommand` returns `.error (.notSupported, s)`
       cleanly without panic or state mutation (and `.ok (.version 2.6.0, s)` on BOLOS).
    2. `display.rs:167`: `OP_RETURN` outputs failed `Address::from_script`; `BitcoinLedger.Script` & `Psbt`
       validate `OP_RETURN` (`<= 83` bytes, `MINIMALDATA` pushes) cleanly.
    3. `fastpsbt.rs:231-250, 1046`: `read_compact_size` accepted non-minimal VarInts while `wutxo[8] <= 0xfc`
       rejected witness UTXOs with `scriptPubKey.size >= 253`. -/

theorem vnd_bug_009_get_version_total_and_state_preserving
    {Affine : Type} [DecidableEq Affine]
    (ct : UInt32)
    (hw : InternalSpec.AppStateMachine.HardwareOracle Affine)
    (ui : InternalSpec.AppStateMachine.UserApprovalOracle Affine)
    (s : InternalSpec.AppStateMachine.AppPersistentState)
    (hNoSwap : s.swapLock = none) :
    BitcoinLedger.AppStateMachine.stepAppCommand (.vanadium ct) hw ui .getVersion s =
      .error (.notSupported, s) ∧
    BitcoinLedger.AppStateMachine.stepAppCommand (.bolos ct) hw ui .getVersion s =
      .ok (.version { major := 2, minor := 6, patch := 0 }, s) := by
  simp [BitcoinLedger.AppStateMachine.stepAppCommand, hNoSwap,
    BitcoinLedger.AppStateMachine.targetAppVersion]

theorem vnd_bug_009_non_minimal_compact_size_rejected :
    -- `0xFD` encoding `< 253` (`252`) -> rejected
    BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFD, 0xFC, 0x00]) = none ∧
    BitcoinLedger.FreestandingKernels.llbVarIntPrefixIsCanonical 0xFD 252 = false ∧
    -- `0xFE` encoding `< 65536` (`65535`) -> rejected
    BitcoinLedger.Basic.decodeVarIntCanonical? (ByteArray.mk #[0xFE, 0xFF, 0xFF, 0x00, 0x00]) = none ∧
    BitcoinLedger.FreestandingKernels.llbVarIntPrefixIsCanonical 0xFE 65535 = false ∧
    -- `0xFF` encoding `< 2^32` (`0xFFFFFFFF`) -> rejected
    BitcoinLedger.Basic.decodeVarIntCanonical?
      (ByteArray.mk #[0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00]) = none ∧
    BitcoinLedger.FreestandingKernels.llbVarIntPrefixIsCanonical 0xFF 0xFFFFFFFF = false ∧
    -- Canonical `300` (`>= 253`) succeeds cleanly
    BitcoinLedger.Basic.decodeVarIntCanonical? (BitcoinLedger.Basic.encodeVarInt 300) = some 300 ∧
    BitcoinLedger.FreestandingKernels.llbVarIntPrefixIsCanonical 0xFD 300 = true := by
  decide

def checkVndBug009 : Bool :=
  -- 1. `OP_RETURN` validation in `BitcoinLedger.Script` & `BitcoinLedger.Psbt`
  let validOpRet := ByteArray.mk #[0x6a, 0x04, 0xde, 0xad, 0xbe, 0xef]
  let nonMinimalOpRet := ByteArray.mk #[0x6a, 0x01, 0x05] -- `0x05` must use `OP_5` (`0x55`)
  let oversizedOpRet := ByteArray.mk (#[0x6a, 0x4c, 81] ++ Array.replicate 81 0x42) -- 84 bytes > 83
  let opRetScriptChecks :=
    BitcoinLedger.Script.isValidOpReturnScript validOpRet &&
    !BitcoinLedger.Script.isValidOpReturnScript nonMinimalOpRet &&
    !BitcoinLedger.Script.isValidOpReturnScript oversizedOpRet
  let spk0 := BitcoinLedger.Script.mkP2WPKH (ByteArray.mk (Array.replicate 20 0x55))
  let pol : InternalSpec.Psbt.WalletPolicySpec := {
    isDefault := true
    name := ""
    spendClass := .segwitV0
    internalPlaceholders := [{
      keyIndex := 0
      expectedOrigin := some { fingerprint := 0xf5acc2fd, path := [h84, h1, h0] }
      numFirst := 0
      numSecond := 1
      isMusig := false
    }]
    deriveScripts := fun isChg idx => if !isChg && idx == 0 then some (spk0, none, none) else none
  }
  let baseCfg := { BitcoinLedger.AppStateMachine.signingConfigOfTarget (.bolos 1) false with allowOpReturnOutputs := true }
  let mkOpRetPsbt (opScript : ByteArray) : InternalSpec.Psbt.PsbtTx := {
    txVersion := 2
    inputs := #[{
      prevout := { txid := InternalSpec.Psbt.zeroBytes32, vout := 0 }
      witnessUtxo := some { amount := 50_000, scriptPubKey := spk0 }
      derivations := [{ pubkey := ByteArray.mk (Array.replicate 33 0x02),
                        origin := { fingerprint := 0xf5acc2fd, path := [h84, h1, h0, 0, 0] } }]
    }]
    outputs := #[
      { amount := 0, scriptPubKey := some opScript },
      { amount := 49_000, scriptPubKey := some spk0 }
    ]
  }
  let opRetPsbtOk :=
    (BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles baseCfg pol (mkOpRetPsbt validOpRet)).isOk &&
    isPsbtErr
      (BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles baseCfg pol (mkOpRetPsbt nonMinimalOpRet))
      .invalidOpReturnScript &&
    isPsbtErr
      (BitcoinLedger.Psbt.validatePsbtTransaction vanadiumTestnetPsbtOracles baseCfg pol (mkOpRetPsbt oversizedOpRet))
      .invalidOpReturnScript

  -- 2. Witness UTXO with `scriptPubKey.size == 300` (`>= 253`, breaking Vanadium's `wutxo[8] <= 0xfc` check!)
  let largeSpk300 := ByteArray.mk (Array.replicate 300 0x51)
  let largeWutxo : InternalSpec.Psbt.TxOut := { amount := 75_000, scriptPubKey := largeSpk300 }
  let encodedLargeTxOut := BitcoinLedger.Psbt.encodeTxOut largeWutxo
  let largeInp : InternalSpec.Psbt.PsbtInput := {
    prevout := { txid := InternalSpec.Psbt.zeroBytes32, vout := 0 }
    witnessUtxo := some largeWutxo
  }
  let largeWutxoOk :=
    -- `encodeTxOut` uses 3-byte `0xFD 0x2C 0x01` CompactSize header at offset 8 (`8 + 3 + 300 = 311` bytes)
    encodedLargeTxOut.size == 311 &&
    encodedLargeTxOut.data[8]? == some 0xFD &&
    encodedLargeTxOut.data[9]? == some 0x2C &&
    encodedLargeTxOut.data[10]? == some 0x01 &&
    BitcoinLedger.Psbt.extractInputPrevout vanadiumTestnetPsbtOracles.sha256 largeInp == .ok (largeWutxo, false)

  opRetScriptChecks && opRetPsbtOk && largeWutxoOk

/-! ============================================================================================
    SUITE EXECUTION HARNESS (`lake env lean Tests/VanadiumDifferential.lean`)
    ============================================================================================ -/

def suiteSections : List (String × Bool) := [
  ("A.1 BIP-32 Master Fingerprint, Standard/Resident tpubs & Path Policy (15 vectors)", checkBip32Vectors),
  ("A.2 BIP-388 Wallet Policies, PoR HMAC & Taproot/MuSig2/Inheritance Addresses (5 suites)", checkWalletPolicyAndTaprootVectors),
  ("A.3 BIP-379 Miniscript Combinators & Stacked Wrappers (7 templates)", checkMiniscriptCombinators),
  ("A.4 PSBTv0->v2 Normalization, UTXO/Fee/Change & BIP-341 TapSighash Vector", checkVanadiumTaprootPsbtVector),
  ("A.5 Two-Round BIP-327 MuSig2 Session Lifecycle & BIP-340 Schnorr Aggregation", checkMusig2EndToEndVector),
  ("A.6 BIP-352/374/375/392 Silent Payments & BIP-137/BIP-322 Message Signing", checkSilentPaymentsAndMessageSigning),
  ("B.1 [VND-BUG-001] Andor(X,Y,Z) Canonical OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF", checkVndBug001),
  ("B.2 [VND-BUG-002] Checked UInt64 Satoshi Sums & MAX_MONEY / 2^63 Sign-Flip Defense", checkVndBug002),
  ("B.3 [VND-BUG-003] CVE-2020-14199 Dual-UTXO Cross-Check (nonWitnessUtxo vs witnessUtxo)", checkVndBug003),
  ("B.4 [VND-BUG-004] BIP-370 Dual-Locktime Input, Zero Height & Fallback Isolation", checkVndBug004),
  ("B.5 [VND-BUG-005] sh(wsh(...)) Registration vs Derivation Consistency", checkVndBug005),
  ("B.6 [VND-BUG-006] BIP-379 Type, Malleability, Sig, Timelock, Resource & Internal-Key Gates", checkVndBug006),
  ("B.7 [VND-BUG-007] BIP-32 KeyTree::Resident depth == 256 u8-Wraparound Rejection", checkVndBug007),
  ("B.8 [VND-BUG-008] MuSig2 Round-2 Self-Pubnonce Tamper Rejection & Session Burn", checkVndBug008),
  ("B.9 [VND-BUG-009] GetVersion No-Panic, OP_RETURN, Canonical VarInt & >=253B WitnessUtxo", checkVndBug009)
]

#eval show IO Unit from do
  IO.println "=== Running Tests/VanadiumDifferential.lean ==="
  let mut passed := 0
  let mut failed := 0
  for (label, ok) in suiteSections do
    if ok then
      passed := passed + 1
      IO.println s!"  [PASS] {label}"
    else
      failed := failed + 1
      IO.println s!"  [FAIL] {label}"
  IO.println s!"=== Summary: {passed}/{passed + failed} differential & VND-BUG-001..009 sections passed ==="
  if failed > 0 then
    throw (IO.userError s!"{failed} section(s) failed in Tests/VanadiumDifferential.lean")

end Tests.VanadiumDifferential

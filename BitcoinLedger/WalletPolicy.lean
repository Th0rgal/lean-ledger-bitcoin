import Spec

namespace BitcoinLedger.WalletPolicy

/-!
# `BitcoinLedger.WalletPolicy` — Executable Ledger Wallet Policy & BIP-388 / BIP-379 Engine

Pure Lean 4 freestanding-compatible implementation of:
1. BIP-388 Key Information & KeyOrigin ASCII parsing & validation (`WalletKeyInfo`, lowercase hex
   fingerprint check, hardened/unhardened origin step parsing, Base58Check 78-byte xpub decoding,
   `v1` vs `v2` wildcard check, `<M;N>` multipath inequality & unhardened restrictions, sequential
   `@0..@k` placeholder coverage, and our-key device ownership classification).
2. Stacked-wrapper BIP-379 Miniscript parser, AST resource analyzer, typechecker (`B/V/K/W`,
   `z/o/n/d/u`, `m`, `s`, `k`), BIP-68 `older(n)` bitmask check (`(n & 0xFFBF0000) == 0` and
   `1 <= (n & 0xFFFF) <= 0xFFFF`), `after(n)` height/timestamp mixing detection, and canonical
   Bitcoin Script compiler (`compileMiniscript` with canonical BIP-379
   `andor(X,Y,Z) -> [X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`).
3. Descriptor template evaluation (`pkh`, `wpkh`, `sh`, `wsh`, `sh(wpkh)`, `sh(wsh)`, `tr` single-key,
   `tr` TapTree, `sortedmulti`, `multi`, `multi_a`, `sortedmulti_a`, plus `rawtr` rejection per
   BIP-388 & Ledger security rules) parameterized by `PolicyProfile` (`canonicalLedgerProfile`,
   `bolosAppProfile`, `vanadiumAppProfile`).
4. BIP-341 `TapLeaf` (`0xC0`), lexicographically sorted `TapBranch`, and `TapTweak` `scriptPubKey`
   derivation.
5. Stateless default policy (`BIP-44/49/84/86` with `addressIndex <= 50000`) and registered wallet
   policy HMAC (`REGISTER_WALLET` / Vanadium Proof-of-Registration) verification, script derivation,
   and address derivation (`deriveWalletPolicyScript`, `deriveWalletPolicyAddress`,
   `verifyAndRegisterWalletPolicy`).
-/

/-! ### Constructive `BEq` Instances (`0 Classical.choice`) -/
local instance (priority := high) : BEq UInt8 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : BEq UInt32 := ⟨fun a b => decide (a = b)⟩
local instance (priority := high) : LawfulBEq UInt8 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl
local instance (priority := high) : LawfulBEq UInt32 where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-! ## Section 1: Core Domain Aliases, Constants & Byte Encoders -/

abbrev Network := Spec.WalletPolicy.Network
abbrev PolicyFormat := Spec.WalletPolicy.PolicyFormat
abbrev KeyOrigin := Spec.WalletPolicy.KeyOrigin
abbrev ExtendedPubKey := Spec.WalletPolicy.ExtendedPubKey
abbrev WalletKeyInfo := Spec.WalletPolicy.KeyInformation
abbrev DerivationSpec := Spec.WalletPolicy.DerivationSpec
abbrev KeyExpr := Spec.WalletPolicy.KeyExpr
abbrev MiniscriptWrapper := Spec.WalletPolicy.MiniscriptWrapper
abbrev Miniscript := Spec.WalletPolicy.Miniscript
abbrev WshScript := Spec.WalletPolicy.WshScript
abbrev ShScript := Spec.WalletPolicy.ShScript
abbrev TapLeafScript := Spec.WalletPolicy.TapLeafScript
abbrev TapTree := Spec.WalletPolicy.TapTree
abbrev DescriptorTemplate := Spec.WalletPolicy.DescriptorTemplate
abbrev WalletPolicy := Spec.WalletPolicy.WalletPolicy
abbrev PolicyError := Spec.WalletPolicy.PolicyError
abbrev MiniscriptCtx := Spec.WalletPolicy.MiniscriptCtx
abbrev BasicType := Spec.WalletPolicy.BasicType
abbrev MiniscriptType := Spec.WalletPolicy.MiniscriptType
abbrev MiniscriptExtInfo := Spec.WalletPolicy.MiniscriptExtInfo
abbrev PolicyProfile := Spec.WalletPolicy.PolicyProfile
abbrev DeviceRegistrationOracle := Spec.WalletPolicy.DeviceRegistrationOracle
abbrev PolicyKeyRole := Spec.WalletPolicy.PolicyKeyRole
abbrev PolicyAuthorization := Spec.WalletPolicy.PolicyAuthorization
abbrev CryptoPolicyOracle := Spec.WalletPolicy.CryptoPolicyOracle

def hardenedBit : UInt32 := 0x80000000

def isUnhardened (idx : UInt32) : Bool :=
  idx < hardenedBit

def hardened (idx : UInt32) : UInt32 :=
  0x80000000 ||| idx

def coinTypeOfNetwork : Network → UInt32
  | .mainnet => 0
  | .testnet => 1

def xpubVersionOfNetwork : Network → UInt32
  | .mainnet => 0x0488B21E
  | .testnet => 0x043587CF

def specNetworkOfPolicyNetwork : Network → Spec.Network
  | .mainnet => .mainnet
  | .testnet => .testnet

def maxOriginSteps : Nat := 8
def maxDefaultBip44Account : UInt32 := 100
def maxDefaultAddressIndex : UInt32 := 50000
def sequenceLocktimeTypeFlag : UInt32 := (1 : UInt32) <<< (22 : UInt32)
def locktimeThreshold : UInt32 := 500000000

/-- BIP-68 invalid upper-bit mask (`0xFFBF0000 = ~(0x0040FFFF)`), rejecting bit 31 (disable flag)
    and unused bits 23..30 and 16..21 (`policy.c:check_older_node_cb`). -/
def olderInvalidUpperMask : UInt32 := 0xFFBF0000

def bip328ChainCode : ByteArray :=
  ByteArray.mk #[
    0x86, 0x80, 0x87, 0xca, 0x02, 0xa6, 0xf9, 0x74,
    0xc4, 0x59, 0x89, 0x24, 0xc3, 0x6b, 0x57, 0x76,
    0x2d, 0x32, 0xcb, 0x45, 0x71, 0x71, 0x67, 0xe3,
    0x00, 0x62, 0x2c, 0x71, 0x67, 0xe3, 0x89, 0x65
  ]

def bip341NumsPubkey : ByteArray :=
  ByteArray.mk #[
    0x02, 0x50, 0x92, 0x9b, 0x74, 0xc1, 0xa0, 0x49, 0x54,
    0xb7, 0x8b, 0x4b, 0x60, 0x35, 0xe9, 0x7a, 0x5e, 0x07,
    0x8a, 0x5a, 0x0f, 0x28, 0xec, 0x96, 0xd5, 0x47, 0xbf,
    0xee, 0x9a, 0xce, 0x80, 0x3a, 0xc0
  ]

def zeroBytes32 : ByteArray :=
  ByteArray.mk (Array.replicate 32 0)

def encodeU32BE (n : UInt32) : ByteArray :=
  ByteArray.mk #[
    ((n >>> 24) &&& 0xFF).toUInt8,
    ((n >>> 16) &&& 0xFF).toUInt8,
    ((n >>> 8) &&& 0xFF).toUInt8,
    (n &&& 0xFF).toUInt8
  ]

def encodeU32LE (n : UInt32) : ByteArray :=
  ByteArray.mk #[
    (n &&& 0xFF).toUInt8,
    ((n >>> 8) &&& 0xFF).toUInt8,
    ((n >>> 16) &&& 0xFF).toUInt8,
    ((n >>> 24) &&& 0xFF).toUInt8
  ]

def decodeU32BE4 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

def encodeCompactSize (n : Nat) : ByteArray :=
  if n < 0xFD then
    ByteArray.mk #[UInt8.ofNat n]
  else if n <= 0xFFFF then
    ByteArray.mk #[
      0xFD,
      UInt8.ofNat (n % 256),
      UInt8.ofNat ((n / 256) % 256)
    ]
  else if n <= 0xFFFFFFFF then
    ByteArray.mk #[
      0xFE,
      UInt8.ofNat (n % 256),
      UInt8.ofNat ((n / 256) % 256),
      UInt8.ofNat ((n / 65536) % 256),
      UInt8.ofNat ((n / 16777216) % 256)
    ]
  else
    ByteArray.mk #[
      0xFF,
      UInt8.ofNat (n % 256),
      UInt8.ofNat ((n / 256) % 256),
      UInt8.ofNat ((n / 65536) % 256),
      UInt8.ofNat ((n / 16777216) % 256),
      UInt8.ofNat ((n / 4294967296) % 256),
      UInt8.ofNat ((n / 1099511627776) % 256),
      UInt8.ofNat ((n / 281474976710656) % 256),
      UInt8.ofNat ((n / 72057594037927936) % 256)
    ]

def byteListLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true
    else if b < a then false
    else byteListLt as bs

def byteArrayLt (a b : ByteArray) : Bool :=
  byteListLt a.data.toList b.data.toList

def insertByteArray (x : ByteArray) : List ByteArray → List ByteArray
  | [] => [x]
  | y :: ys =>
    if byteArrayLt x y then x :: y :: ys
    else y :: insertByteArray x ys

def sortByteArrays : List ByteArray → List ByteArray
  | [] => []
  | x :: xs => insertByteArray x (sortByteArrays xs)

/-- Constant-time-style XOR accumulator equality check on 32-byte MACs. -/
def constantTimeEqBytes32 (a b : ByteArray) : Bool :=
  if a.size != 32 || b.size != 32 then
    false
  else
    let rec go : List UInt8 → List UInt8 → UInt8 → Bool
      | [], [], acc => acc == 0
      | x :: xs, y :: ys, acc => go xs ys (acc ||| (x ^^^ y))
      | _, _, _ => false
    go a.data.toList b.data.toList 0

/-! ## Section 2: Key Information Parsing & Validation (`KeyOrigin`, `WalletKeyInfo`) -/

def canonicalLedgerProfile (net : Network := .mainnet) : PolicyProfile :=
  { network := net }

def bolosAppProfile (net : Network := .mainnet) : PolicyProfile :=
  { network := net
    maxOriginSteps := 8
    allowShWsh := true
    allowGeneralMiniscriptInShWsh := false
    requireSequentialPlaceholders := false
    allowEmptyWalletName := false
    maxWalletNameBytes := some 64
    forbidWalletNameEdgeSpaces := true
    maxTemplateBytesV1 := some 40
    maxTemplateBytesV2 := some 512
    maxMiniscriptDepth := some 16
    maxThreshNesting := some 4
    maxThreshChildren := some 24 }

def vanadiumAppProfile (net : Network := .mainnet) : PolicyProfile :=
  { network := net
    maxPolicyKeys := 4096
    maxMultiKeys := 20
    maxP2shMultiKeys := 20
    maxMultiAKeys := 999
    maxMusigKeys := 64
    maxOriginSteps := 255
    allowMusigInSortedmultiA := true
    allowShWsh := false
    allowGeneralMiniscriptInShWsh := false
    requireSequentialPlaceholders := false
    allowStatelessDefaultPolicies := false
    allowEmptyWalletName := true
    maxWalletNameBytes := none
    forbidWalletNameEdgeSpaces := false
    maxInternalKeyExpressions := 4096
    maxTemplateBytesV1 := none
    maxTemplateBytesV2 := none
    maxMiniscriptDepth := none
    maxThreshNesting := none
    maxThreshChildren := none }

def xpubWellFormed (xpub : ExtendedPubKey) : Bool :=
  xpub.chainCode.size == 32 &&
  xpub.compressedPubkey.size == 33 &&
  (let pfx := xpub.compressedPubkey.get! 0; pfx == 0x02 || pfx == 0x03) &&
  (if xpub.depth == 0 then xpub.parentFingerprint == 0 && xpub.childNumber == 0 else true)

def xpubXOnly (xpub : ExtendedPubKey) : ByteArray :=
  xpub.compressedPubkey.extract 1 33

def serializeXpub78 (xpub : ExtendedPubKey) : ByteArray :=
  encodeU32BE xpub.version ++
  ByteArray.mk #[xpub.depth] ++
  encodeU32BE xpub.parentFingerprint ++
  encodeU32BE xpub.childNumber ++
  xpub.chainCode ++
  xpub.compressedPubkey

/-- Deserialize 78 raw BIP-32 extended pubkey bytes into `ExtendedPubKey`, verifying structural
    well-formedness (`0x02`/`0x03` compressed pubkey prefix and depth-0 root constraints). -/
def deserializeXpub78 (raw : ByteArray) : Option ExtendedPubKey :=
  if raw.size != 78 then
    none
  else
    let ver := decodeU32BE4 (raw.get! 0) (raw.get! 1) (raw.get! 2) (raw.get! 3)
    let depth := raw.get! 4
    let parentFp := decodeU32BE4 (raw.get! 5) (raw.get! 6) (raw.get! 7) (raw.get! 8)
    let childNum := decodeU32BE4 (raw.get! 9) (raw.get! 10) (raw.get! 11) (raw.get! 12)
    let chainCode := raw.extract 13 45
    let compPk := raw.extract 45 78
    let xpub : ExtendedPubKey := {
      version := ver
      depth := depth
      parentFingerprint := parentFp
      childNumber := childNum
      chainCode := chainCode
      compressedPubkey := compPk
    }
    if xpubWellFormed xpub then some xpub else none

def validKeyInfoWithBounds (maxOriginLen : Nat) (fmt : PolicyFormat) (net : Network)
    (ki : WalletKeyInfo) : Bool :=
  xpubWellFormed ki.xpub &&
  ki.xpub.depth.toNat < 254 &&
  ki.xpub.version == xpubVersionOfNetwork net &&
  (match ki.origin with
   | none => true
   | some orig => orig.path.length <= maxOriginLen) &&
  (match fmt with
   | .v1 => ki.hasLegacyWildcard == true
   | .v2 => ki.hasLegacyWildcard == false)

def validKeyInfo (fmt : PolicyFormat) (net : Network) (ki : WalletKeyInfo) : Bool :=
  validKeyInfoWithBounds maxOriginSteps fmt net ki

def validWalletNameBytesWithBounds
    (allowEmpty : Bool) (maxLenOpt : Option Nat) (forbidEdgeSpaces : Bool) (bytes : List UInt8) : Bool :=
  let len := bytes.length
  (if len == 0 then allowEmpty else true) &&
  (match maxLenOpt with
   | none => true
   | some maxL => len <= maxL) &&
  bytes.all (fun b => 0x20 <= b && b <= 0x7E) &&
  (if !forbidEdgeSpaces || len == 0 then
     true
   else
     match bytes.head?, bytes.getLast? with
     | some first, some last => first != 0x20 && last != 0x20
     | _, _ => false)

def validWalletNameBytes (bytes : List UInt8) : Bool :=
  validWalletNameBytesWithBounds false (some 64) true bytes

def validWalletName (name : String) : Bool :=
  validWalletNameBytes name.toUTF8.data.toList

def validRegisteredWalletName (profile : PolicyProfile) (name : String) : Bool :=
  validWalletNameBytesWithBounds
    profile.allowEmptyWalletName
    profile.maxWalletNameBytes
    profile.forbidWalletNameEdgeSpaces
    name.toUTF8.data.toList

def validDerivationSpec (fmt : PolicyFormat) : DerivationSpec → Bool
  | .wildcard => true
  | .multipath m n =>
    fmt == .v2 && isUnhardened m && isUnhardened n && m != n

/-! ## Section 3: ASCII Parsers for `KeyOrigin`, `WalletKeyInfo`, Descriptor Templates & Miniscript -/

def isAsciiDigit (b : UInt8) : Bool :=
  0x30 <= b && b <= 0x39

def isAsciiAlphaNum (b : UInt8) : Bool :=
  isAsciiDigit b || (0x41 <= b && b <= 0x5A) || (0x61 <= b && b <= 0x7A)

def parseDecimalNat (input : List UInt8) : Option (Nat × List UInt8) :=
  let digits := input.takeWhile isAsciiDigit
  let rest := input.dropWhile isAsciiDigit
  match digits with
  | [] => none
  | [d] => some ((d - 0x30).toNat, rest)
  | d0 :: _ =>
    if d0 == 0x30 || digits.length > 10 then none
    else
      let val := digits.foldl (fun acc d => acc * 10 + (d - 0x30).toNat) 0
      some (val, rest)

def parseDecimalU32 (input : List UInt8) : Option (UInt32 × List UInt8) :=
  match parseDecimalNat input with
  | some (n, rest) =>
    if n <= 0xFFFFFFFF then some (UInt32.ofNat n, rest) else none
  | none => none

def stripAsciiPrefix (pfx : String) (input : List UInt8) : Option (List UInt8) :=
  let pbytes := pfx.toUTF8.data.toList
  let rec go : List UInt8 → List UInt8 → Option (List UInt8)
    | [], rest => some rest
    | p :: ps, c :: cs => if p == c then go ps cs else none
    | _ :: _, [] => none
  go pbytes input

/-- Lowercase hex nibble decoder (`'0'..'9'`, `'a'..'f'`; uppercase `'A'..'F'` is strictly rejected
    per `wallet.c:is_lowercase_hex` and BIP-380/388). -/
def decodeHexNibble (b : UInt8) : Option UInt8 :=
  if 0x30 <= b && b <= 0x39 then some (b - 0x30)
  else if 0x61 <= b && b <= 0x66 then some (b - 0x61 + 10)
  else none

def parseFixedHex (nBytes : Nat) (input : List UInt8) : Option (ByteArray × List UInt8) :=
  let rec loop : Nat → List UInt8 → Array UInt8 → Option (ByteArray × List UInt8)
    | 0, rest, acc => some (ByteArray.mk acc, rest)
    | k + 1, hi :: lo :: rest, acc =>
      match decodeHexNibble hi, decodeHexNibble lo with
      | some h, some l => loop k rest (acc.push ((h <<< 4) ||| l))
      | _, _ => none
    | _ + 1, _, _ => none
  loop nBytes input #[]

/-- Parse a single BIP-32 origin derivation step (`<decimal>` or `<decimal>'`;
    note `'h'` is supported on Vanadium BIP-388 while BOLOS `wallet.c:305` uses `'''`,
    controlled via `allowHardenedH`). -/
def parseOriginStep (allowHardenedH : Bool) (input : List UInt8) : Option (UInt32 × List UInt8) :=
  match parseDecimalU32 input with
  | none => none
  | some (idx, rest) =>
    if !isUnhardened idx then
      none
    else
      match rest with
      | 0x27 :: rAfter => some (hardened idx, rAfter) -- '\'' = 0x27
      | 0x68 :: rAfter => -- 'h' = 0x68
        if allowHardenedH then some (hardened idx, rAfter) else some (idx, rest)
      | _ => some (idx, rest)

/-- Parse `(/<step>)*]` inside `[fingerprint/d_1/.../d_k]`, bounded by `remSteps`. -/
def parseOriginSteps (fuel : Nat) (remSteps : Nat) (allowHardenedH : Bool)
    (acc : List UInt32) (input : List UInt8) : Option (List UInt32 × List UInt8) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match input with
    | 0x5D :: rest => -- ']' = 0x5D
      some (acc.reverse, rest)
    | 0x2F :: afterSlash => -- '/' = 0x2F
      match remSteps with
      | 0 => none
      | rem' + 1 =>
        match parseOriginStep allowHardenedH afterSlash with
        | some (step, rest) => parseOriginSteps fuel' rem' allowHardenedH (step :: acc) rest
        | none => none
    | _ => none

/-- Parse `[<8-lowercase-hex-fingerprint>(/<step>)*]` (`wallet.c:318-354`). -/
def parseKeyOriginPrefix (maxOriginLen : Nat) (allowHardenedH : Bool)
    (input : List UInt8) : Option (KeyOrigin × List UInt8) :=
  match input with
  | 0x5B :: afterBracket => -- '[' = 0x5B
    match parseFixedHex 4 afterBracket with
    | none => none
    | some (fpBytes, afterFp) =>
      let fp := decodeU32BE4 (fpBytes.get! 0) (fpBytes.get! 1) (fpBytes.get! 2) (fpBytes.get! 3)
      match parseOriginSteps (afterFp.length + 1) maxOriginLen allowHardenedH [] afterFp with
      | some (steps, rest) => some ({ fingerprint := fp, path := steps }, rest)
      | none => none
  | _ => none

/-- Parse a complete BIP-388 `KeyInformation` string (`[fp/path]xpub...` in `v2`,
    `[fp/path]xpub.../**` in `v1`), verifying Base58Check checksum, network xpub version,
    `depth < 254`, and `maxOriginSteps` (`wallet.c:parse_policy_map_key_info`). -/
def parseWalletKeyInfo (profile : PolicyProfile) (fmt : PolicyFormat)
    (doubleSha256 : ByteArray → ByteArray) (allowHardenedH : Bool := false)
    (keyInfoStr : String) : Except PolicyError WalletKeyInfo :=
  let bytes := keyInfoStr.toUTF8.data.toList
  let originParsed : Option (Option KeyOrigin × List UInt8) :=
    match bytes with
    | 0x5B :: _ =>
      match parseKeyOriginPrefix profile.maxOriginSteps allowHardenedH bytes with
      | some (orig, rest) => some (some orig, rest)
      | none => none
    | _ => some (none, bytes)
  match originParsed with
  | none => .error .invalidKeyInfo
  | some (originOpt, afterOrigin) =>
    let xpubBytes := afterOrigin.takeWhile isAsciiAlphaNum
    let suffixBytes := afterOrigin.dropWhile isAsciiAlphaNum
    if xpubBytes.length < 111 || xpubBytes.length > 112 then
      .error .invalidKeyInfo
    else
      let xpubStr := String.ofList (xpubBytes.map Char.ofUInt8)
      match Spec.decodeBase58Check? doubleSha256 xpubStr with
      | none => .error .invalidKeyInfo
      | some raw78 =>
        match deserializeXpub78 raw78 with
        | none => .error .invalidKeyInfo
        | some xpub =>
          let wildcardRes : Option Bool :=
            match fmt, suffixBytes with
            | .v2, [] => some false
            | .v1, [0x2F, 0x2A, 0x2A] => some true -- "/**"
            | _, _ => none
          match wildcardRes with
          | none => .error .invalidKeyInfo
          | some hasWild =>
            let ki : WalletKeyInfo := {
              origin := originOpt
              xpub := xpub
              hasLegacyWildcard := hasWild
            }
            if validKeyInfoWithBounds profile.maxOriginSteps fmt profile.network ki then
              .ok ki
            else
              .error .invalidKeyInfo

def parseAtIndex (input : List UInt8) : Option (Nat × List UInt8) :=
  match input with
  | 0x40 :: rest => parseDecimalNat rest
  | _ => none

def parseAtIndexList (fuel : Nat) (input : List UInt8) : Option (List Nat × List UInt8) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match parseAtIndex input with
    | none => none
    | some (idx, 0x2C :: rest) =>
      match parseAtIndexList fuel' rest with
      | some (idxs, rest') => some (idx :: idxs, rest')
      | none => none
    | some (idx, 0x29 :: rest) =>
      some ([idx], rest)
    | _ => none

def parseDerivationSpec (fmt : PolicyFormat) (input : List UInt8) : Option (DerivationSpec × List UInt8) :=
  match fmt with
  | .v1 => some (.wildcard, input)
  | .v2 =>
    match stripAsciiPrefix "/**" input with
    | some rest => some (.wildcard, rest)
    | none =>
      match stripAsciiPrefix "/<" input with
      | none => none
      | some r1 =>
        match parseDecimalU32 r1 with
        | none => none
        | some (m, 0x3B :: r2) =>
          match parseDecimalU32 r2 with
          | none => none
          | some (n, r3) =>
            match stripAsciiPrefix ">/*" r3 with
            | some r4 => some (.multipath m n, r4)
            | none => none
        | _ => none

def parseKeyExpr (fmt : PolicyFormat) (input : List UInt8) : Option (KeyExpr × List UInt8) :=
  match stripAsciiPrefix "musig(" input with
  | some r1 =>
    match parseAtIndexList (r1.length + 1) r1 with
    | none => none
    | some (idxs, r2) =>
      match parseDerivationSpec fmt r2 with
      | some (d, r3) => some (.musig idxs d, r3)
      | none => none
  | none =>
    match parseAtIndex input with
    | none => none
    | some (idx, r1) =>
      match parseDerivationSpec fmt r1 with
      | some (d, r2) => some (.single idx d, r2)
      | none => none

def parseKeyExprList (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (List KeyExpr × List UInt8) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match parseKeyExpr fmt input with
    | none => none
    | some (ke, 0x2C :: rest) =>
      match parseKeyExprList fuel' fmt rest with
      | some (kes, rest') => some (ke :: kes, rest')
      | none => none
    | some (ke, 0x29 :: rest) => some ([ke], rest)
    | _ => none

def parseMultisigArgs (fmt : PolicyFormat) (input : List UInt8) : Option (Nat × List KeyExpr × List UInt8) :=
  match parseDecimalNat input with
  | some (k, 0x2C :: rest) =>
    match parseKeyExprList (rest.length + 1) fmt rest with
    | some (keys, rest') => some (k, keys, rest')
    | none => none
  | _ => none

def decodeWrapperByte : UInt8 → Option MiniscriptWrapper
  | 0x61 => some .a
  | 0x73 => some .s
  | 0x63 => some .c
  | 0x64 => some .d
  | 0x76 => some .v
  | 0x6A => some .j
  | 0x6E => some .n
  | 0x74 => some .t
  | 0x6C => some .l
  | 0x75 => some .u
  | _ => none

def peelWrapperPrefixAux (acc : List MiniscriptWrapper) : List UInt8 → Option (List MiniscriptWrapper × List UInt8)
  | [] => none
  | b :: rest =>
    if b == 0x3A then
      if acc.isEmpty then none else some (acc.reverse, rest)
    else
      match decodeWrapperByte b with
      | some w => peelWrapperPrefixAux (w :: acc) rest
      | none => none

def peelWrapperPrefix (input : List UInt8) : Option (List MiniscriptWrapper × List UInt8) :=
  peelWrapperPrefixAux [] input

def applyMiniscriptWrappers (ws : List MiniscriptWrapper) (base : Miniscript) : Miniscript :=
  ws.foldr (fun w acc => .wrap w acc) base

mutual
  def parseMiniscriptBase (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (Miniscript × List UInt8) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match input with
      | 0x30 :: rest =>
        match rest with
        | d :: _ => if isAsciiDigit d then none else some (.ms0, rest)
        | [] => some (.ms0, [])
      | 0x31 :: rest =>
        match rest with
        | d :: _ => if isAsciiDigit d then none else some (.ms1, rest)
        | [] => some (.ms1, [])
      | _ =>
        if let some r := stripAsciiPrefix "pk_k(" input then
          match parseKeyExpr fmt r with
          | some (ke, 0x29 :: rest) => some (.pk_k ke, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "pk_h(" input then
          match parseKeyExpr fmt r with
          | some (ke, 0x29 :: rest) => some (.pk_h ke, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "pkh(" input then
          match parseKeyExpr fmt r with
          | some (ke, 0x29 :: rest) => some (.pkh ke, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "pk(" input then
          match parseKeyExpr fmt r with
          | some (ke, 0x29 :: rest) => some (.pk ke, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "older(" input then
          match parseDecimalU32 r with
          | some (v, 0x29 :: rest) => some (.older v, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "after(" input then
          match parseDecimalU32 r with
          | some (v, 0x29 :: rest) => some (.after v, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "sha256(" input then
          match parseFixedHex 32 r with
          | some (h, 0x29 :: rest) => some (.sha256 h, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "hash256(" input then
          match parseFixedHex 32 r with
          | some (h, 0x29 :: rest) => some (.hash256 h, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "ripemd160(" input then
          match parseFixedHex 20 r with
          | some (h, 0x29 :: rest) => some (.ripemd160 h, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "hash160(" input then
          match parseFixedHex 20 r with
          | some (h, 0x29 :: rest) => some (.hash160 h, rest)
          | _ => none
        else if let some r := stripAsciiPrefix "andor(" input then
          match parseMiniscript fuel' fmt r with
          | some (x, 0x2C :: r1) =>
            match parseMiniscript fuel' fmt r1 with
            | some (y, 0x2C :: r2) =>
              match parseMiniscript fuel' fmt r2 with
              | some (z, 0x29 :: rest) => some (.andor x y z, rest)
              | _ => none
            | _ => none
          | _ => none
        else if let some r := stripAsciiPrefix "and_v(" input then
          parseBinaryMiniscript fuel' fmt .and_v r
        else if let some r := stripAsciiPrefix "and_b(" input then
          parseBinaryMiniscript fuel' fmt .and_b r
        else if let some r := stripAsciiPrefix "and_n(" input then
          parseBinaryMiniscript fuel' fmt .and_n r
        else if let some r := stripAsciiPrefix "or_b(" input then
          parseBinaryMiniscript fuel' fmt .or_b r
        else if let some r := stripAsciiPrefix "or_c(" input then
          parseBinaryMiniscript fuel' fmt .or_c r
        else if let some r := stripAsciiPrefix "or_d(" input then
          parseBinaryMiniscript fuel' fmt .or_d r
        else if let some r := stripAsciiPrefix "or_i(" input then
          parseBinaryMiniscript fuel' fmt .or_i r
        else if let some r := stripAsciiPrefix "thresh(" input then
          match parseDecimalNat r with
          | some (k, 0x2C :: r1) =>
            match parseMiniscriptList fuel' fmt r1 with
            | some (subs, rest) => some (.thresh k subs, rest)
            | none => none
          | _ => none
        else if let some r := stripAsciiPrefix "multi_a(" input then
          match parseMultisigArgs fmt r with
          | some (k, keys, rest) => some (.multi_a k keys, rest)
          | none => none
        else if let some r := stripAsciiPrefix "multi(" input then
          match parseMultisigArgs fmt r with
          | some (k, keys, rest) => some (.multi k keys, rest)
          | none => none
        else none

  def parseMiniscript (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (Miniscript × List UInt8) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match peelWrapperPrefix input with
      | some (wrappers, afterColon) =>
        match parseMiniscriptBase fuel' fmt afterColon with
        | some (base, rest) => some (applyMiniscriptWrappers wrappers base, rest)
        | none => none
      | none =>
        parseMiniscriptBase fuel' fmt input

  def parseBinaryMiniscript (fuel : Nat) (fmt : PolicyFormat)
      (ctor : Miniscript → Miniscript → Miniscript) (input : List UInt8) : Option (Miniscript × List UInt8) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match parseMiniscript fuel' fmt input with
      | some (x, 0x2C :: r1) =>
        match parseMiniscript fuel' fmt r1 with
        | some (y, 0x29 :: rest) => some (ctor x y, rest)
        | _ => none
      | _ => none

  def parseMiniscriptList (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (List Miniscript × List UInt8) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match parseMiniscript fuel' fmt input with
      | some (m, 0x2C :: rest) =>
        match parseMiniscriptList fuel' fmt rest with
        | some (ms, rest') => some (m :: ms, rest')
        | none => none
      | some (m, 0x29 :: rest) => some ([m], rest)
      | _ => none
end

def parseWshScriptBody (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (WshScript × List UInt8) :=
  if let some r := stripAsciiPrefix "sortedmulti(" input then
    match parseMultisigArgs fmt r with
    | some (k, keys, 0x29 :: rest) => some (.sortedmulti k keys, rest)
    | _ => none
  else
    match parseMiniscript fuel fmt input with
    | some (ms, 0x29 :: rest) => some (.miniscript ms, rest)
    | _ => none

def parseTapLeafScript (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (TapLeafScript × List UInt8) :=
  if let some r := stripAsciiPrefix "sortedmulti_a(" input then
    match parseMultisigArgs fmt r with
    | some (k, keys, rest) => some (.sortedmulti_a k keys, rest)
    | none => none
  else
    match parseMiniscript fuel fmt input with
    | some (ms, rest) => some (.miniscript ms, rest)
    | none => none

def parseTapTree (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) : Option (TapTree × List UInt8) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match input with
    | 0x7B :: rest =>
      match parseTapTree fuel' fmt rest with
      | some (left, 0x2C :: r1) =>
        match parseTapTree fuel' fmt r1 with
        | some (right, 0x7D :: r2) =>
          some (.branch left right, r2)
        | _ => none
      | _ => none
    | _ =>
      match parseTapLeafScript fuel' fmt input with
      | some (leaf, rest) => some (.leaf leaf, rest)
      | none => none

/-- Extended descriptor template AST that adds `rawtr(KeyExpr)` (`OP_1 <untweaked-32B-xonly>`),
    which is disallowed in BIP-388 Ledger wallet policies (`KNOWN_TOKENS` in `wallet.c` and
    `bip388::DescriptorTemplate` omit `rawtr`) and exists here for standalone `rawtr` script
    evaluation and explicit BIP-388 security rejection proofs. -/
inductive ExtendedDescriptorTemplate where
  | standard (tmpl : DescriptorTemplate)
  | rawtr (key : KeyExpr)
  deriving BEq, Inhabited

/-- Parse a BIP-388 descriptor template string (strictly rejecting `rawtr(...)` per BIP-388). -/
def parseDescriptorTemplate (fmt : PolicyFormat) (desc : String) : Except PolicyError DescriptorTemplate :=
  let bytes := desc.toUTF8.data.toList
  let fuel := bytes.length + 1
  let parsed : Option (DescriptorTemplate × List UInt8) :=
    if let some r := stripAsciiPrefix "pkh(" bytes then
      match parseKeyExpr fmt r with
      | some (ke, [0x29]) => some (.pkh ke, [])
      | _ => none
    else if let some r := stripAsciiPrefix "wpkh(" bytes then
      match parseKeyExpr fmt r with
      | some (ke, [0x29]) => some (.wpkh ke, [])
      | _ => none
    else if let some r := stripAsciiPrefix "wsh(" bytes then
      match parseWshScriptBody fuel fmt r with
      | some (inner, []) => some (.wsh inner, [])
      | _ => none
    else if let some r := stripAsciiPrefix "sh(" bytes then
      if let some rw := stripAsciiPrefix "wpkh(" r then
        match parseKeyExpr fmt rw with
        | some (ke, [0x29, 0x29]) => some (.sh (.wpkh ke), [])
        | _ => none
      else if let some rw := stripAsciiPrefix "wsh(" r then
        match parseWshScriptBody fuel fmt rw with
        | some (inner, [0x29]) => some (.sh (.wsh inner), [])
        | _ => none
      else if let some rm := stripAsciiPrefix "sortedmulti(" r then
        match parseMultisigArgs fmt rm with
        | some (k, keys, [0x29]) => some (.sh (.sortedmulti k keys), [])
        | _ => none
      else if let some rm := stripAsciiPrefix "multi(" r then
        match parseMultisigArgs fmt rm with
        | some (k, keys, [0x29]) => some (.sh (.multi k keys), [])
        | _ => none
      else none
    else if let some r := stripAsciiPrefix "tr(" bytes then
      if fmt == .v1 then
        none
      else
        match parseKeyExpr fmt r with
        | some (ik, [0x29]) => some (.tr ik none, [])
        | some (ik, 0x2C :: rTree) =>
          match parseTapTree fuel fmt rTree with
          | some (tree, [0x29]) => some (.tr ik (some tree), [])
          | _ => none
        | _ => none
    else none
  match parsed with
  | some (dt, []) => .ok dt
  | _ => .error .parseError

/-- Parse either a BIP-388 `DescriptorTemplate` or an untweaked `rawtr(KeyExpr)` template (`v2` only). -/
def parseExtendedDescriptorTemplate (fmt : PolicyFormat) (desc : String) :
    Except PolicyError ExtendedDescriptorTemplate :=
  let bytes := desc.toUTF8.data.toList
  if let some r := stripAsciiPrefix "rawtr(" bytes then
    if fmt == .v1 then .error .parseError
    else
      match parseKeyExpr fmt r with
      | some (ke, [0x29]) => .ok (.rawtr ke)
      | _ => .error .parseError
  else
    match parseDescriptorTemplate fmt desc with
    | .ok dt => .ok (.standard dt)
    | .error e => .error e

def parseDescriptorTemplateWithProfile (profile : PolicyProfile) (fmt : PolicyFormat) (desc : String) :
    Except PolicyError DescriptorTemplate := do
  let byteLen := desc.toUTF8.size
  match fmt with
  | .v1 =>
    if let some maxB := profile.maxTemplateBytesV1 then
      if byteLen > maxB then throw .miniscriptResourceLimit
  | .v2 =>
    if let some maxB := profile.maxTemplateBytesV2 then
      if byteLen > maxB then throw .miniscriptResourceLimit
  parseDescriptorTemplate fmt desc

/-! ## Section 4: BIP-379 Miniscript Typechecker (`B/V/K/W`, `z/o/n/d/u`, `m`, `s`, `k`) & BIP-68/65 Timelocks -/

def pushScriptNumSize (n : UInt32) : Nat :=
  if n == 0 then 1
  else if n <= 16 then 1
  else if n <= 0x7F then 2
  else if n <= 0x7FFF then 3
  else if n <= 0x7FFFFF then 4
  else if n <= 0x7FFFFFFF then 5
  else 6

def optAdd (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (x + y)
  | _, _ => none

def optMax (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, y => y
  | x, none => x
  | some x, some y => some (if x >= y then x else y)

def hasTimelockConflict (a b : MiniscriptExtInfo) : Bool :=
  (a.g && b.h) || (a.h && b.g) || (a.i && b.j) || (a.j && b.i)

/-- BIP-68 `older(n)` safe-range check (`policy.c:check_older_node_cb`):
    Requires `1 <= n < 2^31` and `(n & ~SEQUENCE_LOCKTIME_TYPE_FLAG)` in `1..=65535`
    (equivalently `(n & 0xFFBF0000) == 0` and `1 <= (n & 0xFFFF) <= 0xFFFF`). -/
def validOlderArg (n : UInt32) : Bool :=
  let masked := n &&& (0xFFFFFFFF ^^^ sequenceLocktimeTypeFlag)
  (1 <= n && n < hardenedBit) && (1 <= masked && masked <= 65535)

/-- Explicit bitmask form of BIP-68 `older(n)` check (`(n & 0xFFBF0000) == 0` and `1 <= (n & 0xFFFF)`). -/
def validOlderBitmask (n : UInt32) : Bool :=
  ((n &&& olderInvalidUpperMask) == 0) && (1 <= (n &&& 0xFFFF))

/-- BIP-65 `after(n)` range check (`1 <= n < 2^31`). -/
def validAfterArg (n : UInt32) : Bool :=
  1 <= n && n < hardenedBit

def listNodup {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => (!xs.contains x) && listNodup xs

def checkKeyExprInContext (fmt : PolicyFormat) (allowMusig : Bool) (maxMusigKeys : Nat)
    (ke : KeyExpr) : Except PolicyError Unit := do
  match ke.deriv with
  | .wildcard => pure ()
  | .multipath m n =>
    if fmt != .v2 then throw .invalidDerivationSuffix
    if !(isUnhardened m && isUnhardened n) then throw .invalidDerivationSuffix
    if m == n then throw .nonDistinctMultipath
  match ke with
  | .single _ _ => pure ()
  | .musig ks _ =>
    if fmt != .v2 || !allowMusig then throw .invalidMusigKeyExpr
    if ks.length < 2 || ks.length > maxMusigKeys || !listNodup ks then
      throw .invalidMusigKeyExpr

def checkKeyExprList (fmt : PolicyFormat) (allowMusig : Bool) (maxMusigKeys : Nat) :
    List KeyExpr → Except PolicyError Unit
  | [] => .ok ()
  | ke :: kes => do
    checkKeyExprInContext fmt allowMusig maxMusigKeys ke
    checkKeyExprList fmt allowMusig maxMusigKeys kes

def threshDpStep (sats : List (Option Nat)) (childSat childDsat : Option Nat) : List (Option Nat) :=
  let rec go (prev : Option Nat) : List (Option Nat) → List (Option Nat)
    | [] => [optAdd prev childSat]
    | cur :: rest =>
      optMax (optAdd cur childDsat) (optAdd prev childSat) :: go cur rest
  match sats with
  | [] => []
  | s0 :: rest => optAdd s0 childDsat :: go s0 rest

def listGetOpt : List (Option Nat) → Nat → Option Nat
  | [], _ => none
  | x :: _, 0 => x
  | _ :: xs, idx + 1 => listGetOpt xs idx

def analyzeMiniscript (fmt : PolicyFormat) (ctx : MiniscriptCtx) (maxMultiKeys maxMultiAKeys maxMusigKeys : Nat) :
    Miniscript → Except PolicyError MiniscriptExtInfo
  | .ms0 =>
    .ok {
      ty := { base := .B, z := true, o := false, n := false, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := true
      opsCount := 0, opsSat := none, opsDsat := some 0
      stackSat := none, stackDsat := some 0, scriptSize := 1
    }
  | .ms1 =>
    .ok {
      ty := { base := .B, z := true, o := false, n := false, d := false, u := true }
      s := false, f := true, e := false, m := true
      g := false, h := false, i := false, j := false, k := true, x := true
      opsCount := 0, opsSat := some 0, opsDsat := none
      stackSat := some 0, stackDsat := none, scriptSize := 1
    }
  | .pk ke => do
    checkKeyExprInContext fmt (ctx == .tapscriptCtx) maxMusigKeys ke
    .ok {
      ty := { base := .B, z := false, o := true, n := true, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := false
      opsCount := 1, opsSat := some 0, opsDsat := some 0
      stackSat := some 1, stackDsat := some 1
      scriptSize := if ctx == .tapscriptCtx then 34 else 35
    }
  | .pkh ke => do
    checkKeyExprInContext fmt (ctx == .tapscriptCtx) maxMusigKeys ke
    .ok {
      ty := { base := .B, z := false, o := false, n := true, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := false
      opsCount := 4, opsSat := some 0, opsDsat := some 0
      stackSat := some 2, stackDsat := some 2, scriptSize := 25
    }
  | .pk_k ke => do
    checkKeyExprInContext fmt (ctx == .tapscriptCtx) maxMusigKeys ke
    .ok {
      ty := { base := .K, z := false, o := true, n := true, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := true
      opsCount := 0, opsSat := some 0, opsDsat := some 0
      stackSat := some 1, stackDsat := some 1
      scriptSize := if ctx == .tapscriptCtx then 33 else 34
    }
  | .pk_h ke => do
    checkKeyExprInContext fmt (ctx == .tapscriptCtx) maxMusigKeys ke
    .ok {
      ty := { base := .K, z := false, o := false, n := true, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := true
      opsCount := 3, opsSat := some 0, opsDsat := some 0
      stackSat := some 2, stackDsat := some 2, scriptSize := 24
    }
  | .older val =>
    if !validOlderArg val then .error .invalidTimelockRange
    else
      let isTime := (val &&& sequenceLocktimeTypeFlag) != 0
      .ok {
        ty := { base := .B, z := true, o := false, n := false, d := false, u := false }
        s := false, f := true, e := false, m := true
        g := isTime, h := !isTime, i := false, j := false, k := true, x := true
        opsCount := 1, opsSat := some 0, opsDsat := none
        stackSat := some 0, stackDsat := none
        scriptSize := 1 + pushScriptNumSize val
      }
  | .after val =>
    if !validAfterArg val then .error .invalidTimelockRange
    else
      let isTime := val >= locktimeThreshold
      .ok {
        ty := { base := .B, z := true, o := false, n := false, d := false, u := false }
        s := false, f := true, e := false, m := true
        g := false, h := false, i := isTime, j := !isTime, k := true, x := true
        opsCount := 1, opsSat := some 0, opsDsat := none
        stackSat := some 0, stackDsat := none
        scriptSize := 1 + pushScriptNumSize val
      }
  | .sha256 h | .hash256 h =>
    if h.size != 32 then .error .parseError
    else
      .ok {
        ty := { base := .B, z := false, o := true, n := true, d := true, u := true }
        s := false, f := false, e := false, m := true
        g := false, h := false, i := false, j := false, k := true, x := false
        opsCount := 4, opsSat := some 0, opsDsat := none
        stackSat := some 1, stackDsat := none, scriptSize := 39
      }
  | .ripemd160 h | .hash160 h =>
    if h.size != 20 then .error .parseError
    else
      .ok {
        ty := { base := .B, z := false, o := true, n := true, d := true, u := true }
        s := false, f := false, e := false, m := true
        g := false, h := false, i := false, j := false, k := true, x := false
        opsCount := 4, opsSat := some 0, opsDsat := none
        stackSat := some 1, stackDsat := none, scriptSize := 27
      }
  | .multi k keys => do
    if ctx != .wshCtx then throw .invalidScriptContext
    let n := keys.length
    if k < 1 || k > n || n > maxMultiKeys then throw .invalidMultisigThreshold
    checkKeyExprList fmt false maxMusigKeys keys
    .ok {
      ty := { base := .B, z := false, o := false, n := true, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := false
      opsCount := 1, opsSat := some n, opsDsat := some n
      stackSat := some (k + 1), stackDsat := some (k + 1)
      scriptSize := 1 + pushScriptNumSize (UInt32.ofNat k) + pushScriptNumSize (UInt32.ofNat n) + 34 * n
    }
  | .multi_a k keys => do
    if ctx != .tapscriptCtx then throw .invalidScriptContext
    let n := keys.length
    if k < 1 || k > n || n > maxMultiAKeys then throw .invalidMultisigThreshold
    checkKeyExprList fmt true maxMusigKeys keys
    .ok {
      ty := { base := .B, z := false, o := false, n := false, d := true, u := true }
      s := true, f := false, e := true, m := true
      g := false, h := false, i := false, j := false, k := true, x := false
      opsCount := n + 1, opsSat := some 0, opsDsat := some 0
      stackSat := some n, stackDsat := some n
      scriptSize := 1 + pushScriptNumSize (UInt32.ofNat k) + 34 * n
    }
  | .andor xNode yNode zNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let y ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys yNode
    let z ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys zNode
    if x.ty.base != .B || !x.ty.d || !x.ty.u then throw .invalidMiniscriptType
    if y.ty.base != z.ty.base || y.ty.base == .W then throw .invalidMiniscriptType
    let kOk := x.k && y.k && z.k && !hasTimelockConflict x y
    .ok {
      ty := {
        base := y.ty.base
        z := x.ty.z && y.ty.z && z.ty.z
        o := (x.ty.z && y.ty.o && z.ty.o) || (x.ty.o && y.ty.z && z.ty.z)
        n := false
        d := z.ty.d
        u := y.ty.u && z.ty.u
      }
      s := z.s && (x.s || y.s)
      f := z.f && (x.s || y.f)
      e := z.e && (x.s || y.f)
      m := x.m && y.m && z.m && x.e && (x.s || y.s || z.s)
      g := x.g || y.g || z.g
      h := x.h || y.h || z.h
      i := x.i || y.i || z.i
      j := x.j || y.j || z.j
      k := kOk
      x := true
      opsCount := 3 + x.opsCount + y.opsCount + z.opsCount
      opsSat := optMax (optAdd y.opsSat x.opsSat) (optAdd x.opsDsat z.opsSat)
      opsDsat := optAdd x.opsDsat z.opsDsat
      stackSat := optMax (optAdd x.stackSat y.stackSat) (optAdd x.stackDsat z.stackSat)
      stackDsat := optAdd x.stackDsat z.stackDsat
      scriptSize := 3 + x.scriptSize + y.scriptSize + z.scriptSize
    }
  | .and_v xNode yNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let y ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys yNode
    if x.ty.base != .V || y.ty.base == .W then throw .invalidMiniscriptType
    let kOk := x.k && y.k && !hasTimelockConflict x y
    .ok {
      ty := {
        base := y.ty.base
        z := x.ty.z && y.ty.z
        o := (x.ty.z && y.ty.o) || (x.ty.o && y.ty.z)
        n := x.ty.n || (x.ty.z && y.ty.n)
        d := false
        u := y.ty.u
      }
      s := x.s || y.s
      f := x.s || y.f
      e := false
      m := x.m && y.m
      g := x.g || y.g
      h := x.h || y.h
      i := x.i || y.i
      j := x.j || y.j
      k := kOk
      x := y.x
      opsCount := x.opsCount + y.opsCount
      opsSat := optAdd x.opsSat y.opsSat
      opsDsat := none
      stackSat := optAdd x.stackSat y.stackSat
      stackDsat := none
      scriptSize := x.scriptSize + y.scriptSize
    }
  | .and_b xNode yNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let y ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys yNode
    if x.ty.base != .B || y.ty.base != .W then throw .invalidMiniscriptType
    let kOk := x.k && y.k && !hasTimelockConflict x y
    .ok {
      ty := {
        base := .B
        z := x.ty.z && y.ty.z
        o := (x.ty.z && y.ty.o) || (x.ty.o && y.ty.z)
        n := x.ty.n || (x.ty.z && y.ty.n)
        d := x.ty.d && y.ty.d
        u := true
      }
      s := x.s || y.s
      f := (x.f && y.f) || (x.s && x.f) || (y.s && y.f)
      e := x.e && y.e && x.s && y.s
      m := x.m && y.m
      g := x.g || y.g
      h := x.h || y.h
      i := x.i || y.i
      j := x.j || y.j
      k := kOk
      x := true
      opsCount := 1 + x.opsCount + y.opsCount
      opsSat := optAdd x.opsSat y.opsSat
      opsDsat := optAdd x.opsDsat y.opsDsat
      stackSat := optAdd x.stackSat y.stackSat
      stackDsat := optAdd x.stackDsat y.stackDsat
      scriptSize := 1 + x.scriptSize + y.scriptSize
    }
  | .and_n xNode yNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let y ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys yNode
    if x.ty.base != .B || !x.ty.d || !x.ty.u || y.ty.base != .B then
      throw .invalidMiniscriptType
    let kOk := x.k && y.k && !hasTimelockConflict x y
    .ok {
      ty := {
        base := .B
        z := x.ty.z && y.ty.z
        o := x.ty.o && y.ty.z
        n := false
        d := true
        u := y.ty.u
      }
      s := x.s || y.s
      f := false
      e := x.s || y.f
      m := x.m && y.m && x.e
      g := x.g || y.g
      h := x.h || y.h
      i := x.i || y.i
      j := x.j || y.j
      k := kOk
      x := true
      opsCount := 3 + x.opsCount + y.opsCount
      opsSat := optAdd x.opsSat y.opsSat
      opsDsat := x.opsDsat
      stackSat := optAdd x.stackSat y.stackSat
      stackDsat := x.stackDsat
      scriptSize := 4 + x.scriptSize + y.scriptSize
    }
  | .or_b xNode zNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let z ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys zNode
    if x.ty.base != .B || !x.ty.d || z.ty.base != .W || !z.ty.d then
      throw .invalidMiniscriptType
    .ok {
      ty := {
        base := .B
        z := x.ty.z && z.ty.z
        o := (x.ty.z && z.ty.o) || (x.ty.o && z.ty.z)
        n := false
        d := true
        u := true
      }
      s := x.s && z.s
      f := false
      e := x.e && z.e
      m := x.m && z.m && x.e && z.e && (x.s || z.s)
      g := x.g || z.g
      h := x.h || z.h
      i := x.i || z.i
      j := x.j || z.j
      k := x.k && z.k
      x := true
      opsCount := 1 + x.opsCount + z.opsCount
      opsSat := optMax (optAdd x.opsSat z.opsDsat) (optAdd z.opsSat x.opsDsat)
      opsDsat := optAdd x.opsDsat z.opsDsat
      stackSat := optMax (optAdd x.stackDsat z.stackSat) (optAdd x.stackSat z.stackDsat)
      stackDsat := optAdd x.stackDsat z.stackDsat
      scriptSize := 1 + x.scriptSize + z.scriptSize
    }
  | .or_c xNode zNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let z ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys zNode
    if x.ty.base != .B || !x.ty.d || !x.ty.u || z.ty.base != .V then
      throw .invalidMiniscriptType
    .ok {
      ty := {
        base := .V
        z := x.ty.z && z.ty.z
        o := x.ty.o && z.ty.z
        n := false
        d := false
        u := false
      }
      s := x.s && z.s
      f := true
      e := false
      m := x.m && z.m && x.e && (x.s || z.s)
      g := x.g || z.g
      h := x.h || z.h
      i := x.i || z.i
      j := x.j || z.j
      k := x.k && z.k
      x := true
      opsCount := 2 + x.opsCount + z.opsCount
      opsSat := optMax x.opsSat (optAdd z.opsSat x.opsDsat)
      opsDsat := none
      stackSat := optMax x.stackSat (optAdd x.stackDsat z.stackSat)
      stackDsat := none
      scriptSize := 2 + x.scriptSize + z.scriptSize
    }
  | .or_d xNode zNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let z ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys zNode
    if x.ty.base != .B || !x.ty.d || !x.ty.u || z.ty.base != .B then
      throw .invalidMiniscriptType
    .ok {
      ty := {
        base := .B
        z := x.ty.z && z.ty.z
        o := x.ty.o && z.ty.z
        n := false
        d := z.ty.d
        u := z.ty.u
      }
      s := x.s && z.s
      f := z.f
      e := z.e
      m := x.m && z.m && x.e && (x.s || z.s)
      g := x.g || z.g
      h := x.h || z.h
      i := x.i || z.i
      j := x.j || z.j
      k := x.k && z.k
      x := true
      opsCount := 3 + x.opsCount + z.opsCount
      opsSat := optMax x.opsSat (optAdd z.opsSat x.opsDsat)
      opsDsat := optAdd x.opsDsat z.opsDsat
      stackSat := optMax x.stackSat (optAdd x.stackDsat z.stackSat)
      stackDsat := optAdd x.stackDsat z.stackDsat
      scriptSize := 3 + x.scriptSize + z.scriptSize
    }
  | .or_i xNode zNode => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys xNode
    let z ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys zNode
    if x.ty.base == .W || x.ty.base != z.ty.base then
      throw .invalidMiniscriptType
    .ok {
      ty := {
        base := x.ty.base
        z := false
        o := x.ty.z && z.ty.z
        n := false
        d := x.ty.d || z.ty.d
        u := x.ty.u && z.ty.u
      }
      s := x.s && z.s
      f := x.f && z.f
      e := (x.e && z.f) || (z.e && x.f)
      m := x.m && z.m && (x.s || z.s)
      g := x.g || z.g
      h := x.h || z.h
      i := x.i || z.i
      j := x.j || z.j
      k := x.k && z.k
      x := true
      opsCount := 3 + x.opsCount + z.opsCount
      opsSat := optMax x.opsSat z.opsSat
      opsDsat := optMax x.opsDsat z.opsDsat
      stackSat := optMax (optAdd x.stackSat (some 1)) (optAdd z.stackSat (some 1))
      stackDsat := optMax (optAdd x.stackDsat (some 1)) (optAdd z.stackDsat (some 1))
      scriptSize := 3 + x.scriptSize + z.scriptSize
    }
  | .thresh k subs => do
    let n := subs.length
    if k < 1 || k > n then throw .invalidMultisigThreshold
    let rec analyzeChildren (isFirst : Bool) : List Miniscript → Except PolicyError (List MiniscriptExtInfo)
      | [] => .ok []
      | m :: ms => do
        let inf ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys m
        let expectedBase : BasicType := if isFirst then .B else .W
        if inf.ty.base != expectedBase || !inf.ty.d || !inf.ty.u then
          throw .invalidMiniscriptType
        let rest ← analyzeChildren false ms
        .ok (inf :: rest)
    let infos ← analyzeChildren true subs
    let countZ := (infos.filter (fun inf => inf.ty.z)).length
    let countO := (infos.filter (fun inf => inf.ty.o)).length
    let countS := (infos.filter (fun inf => inf.s)).length
    let countE := (infos.filter (fun inf => inf.e)).length
    let countM := (infos.filter (fun inf => inf.m)).length
    let countNotS := n - countS
    let (accG, accH, accI, accJ, accK, childrenSize, opsCnt, opsDp, ssDp) :=
      infos.foldl
        (fun (g, h, i, j, kFlag, sz, oc, oDp, sDp) t =>
          let mix :=
            k >= 2 &&
            ((t.g && h) || (t.h && g) || (t.i && j) || (t.j && i))
          let kFlag' := kFlag && t.k && !mix
          (g || t.g, h || t.h, i || t.i, j || t.j, kFlag',
           sz + t.scriptSize, oc + t.opsCount + 1,
           threshDpStep oDp t.opsSat t.opsDsat,
           threshDpStep sDp t.stackSat t.stackDsat))
        (false, false, false, false, true, 0, 0, [some 0], [some 0])
    .ok {
      ty := {
        base := .B
        z := countZ == n
        o := countZ == n - 1 && countO == 1
        n := false
        d := true
        u := true
      }
      s := countNotS <= k - 1
      f := false
      e := countE == n && countS == n
      m := countE == n && countM == n && countNotS <= k
      g := accG, h := accH, i := accI, j := accJ, k := accK, x := false
      opsCount := opsCnt
      opsSat := listGetOpt opsDp k
      opsDsat := listGetOpt opsDp 0
      stackSat := listGetOpt ssDp k
      stackDsat := listGetOpt ssDp 0
      scriptSize := childrenSize + n + pushScriptNumSize (UInt32.ofNat k)
    }
  | .wrap w sub => do
    let x ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys sub
    match w with
    | .a =>
      if x.ty.base != .B then throw .invalidMiniscriptType
      .ok { x with
        ty := { base := .W, z := false, o := false, n := false, d := x.ty.d, u := x.ty.u }
        x := true, opsCount := 2 + x.opsCount, scriptSize := x.scriptSize + 2 }
    | .s =>
      if x.ty.base != .B || !x.ty.o then throw .invalidMiniscriptType
      .ok { x with
        ty := { base := .W, z := false, o := false, n := false, d := x.ty.d, u := x.ty.u }
        opsCount := 1 + x.opsCount, scriptSize := x.scriptSize + 1 }
    | .c =>
      if x.ty.base != .K then throw .invalidMiniscriptType
      .ok { x with
        ty := { x.ty with base := .B, z := false, u := true }
        s := true, x := false, opsCount := 1 + x.opsCount, scriptSize := x.scriptSize + 1 }
    | .t =>
      if x.ty.base != .V then throw .invalidMiniscriptType
      .ok { x with
        ty := { x.ty with base := .B, d := false, u := true }
        f := true, e := false, x := true
        opsDsat := none, stackDsat := none, scriptSize := x.scriptSize + 1 }
    | .d =>
      if x.ty.base != .V || !x.ty.z then throw .invalidMiniscriptType
      .ok { x with
        ty := { base := .B, z := false, o := true, n := true, d := true, u := (ctx == .tapscriptCtx) }
        f := false, e := x.f, x := true
        opsCount := 3 + x.opsCount, opsDsat := some 0
        stackSat := optAdd (some 1) x.stackSat, stackDsat := some 1
        scriptSize := x.scriptSize + 3 }
    | .v =>
      if x.ty.base != .B then throw .invalidMiniscriptType
      let extra := if x.x then 1 else 0
      .ok { x with
        ty := { x.ty with base := .V, d := false, u := false }
        f := true, e := false, x := true
        opsCount := x.opsCount + extra, opsDsat := none, stackDsat := none
        scriptSize := x.scriptSize + extra }
    | .j =>
      if x.ty.base != .B || !x.ty.n then throw .invalidMiniscriptType
      .ok { x with
        ty := { x.ty with z := false, n := true, d := true }
        f := false, e := x.f, x := true
        opsCount := 4 + x.opsCount, opsDsat := some 0, stackDsat := some 1
        scriptSize := x.scriptSize + 4 }
    | .n =>
      if x.ty.base != .B then throw .invalidMiniscriptType
      .ok { x with
        ty := { x.ty with u := true }
        x := true, opsCount := 1 + x.opsCount, scriptSize := x.scriptSize + 1 }
    | .l | .u =>
      if x.ty.base != .B then throw .invalidMiniscriptType
      .ok { x with
        ty := { base := .B, z := false, o := x.ty.z, n := false, d := true, u := x.ty.u }
        f := false, e := x.f, x := true
        opsCount := 3 + x.opsCount, opsDsat := optMax (some 0) x.opsDsat
        stackSat := optAdd x.stackSat (some 1)
        stackDsat := optMax (some 1) (optAdd x.stackDsat (some 1))
        scriptSize := x.scriptSize + 4 }

def checkMiniscriptSane (fmt : PolicyFormat) (ctx : MiniscriptCtx)
    (maxMultiKeys maxMultiAKeys maxMusigKeys : Nat) (ms : Miniscript) : Except PolicyError Unit := do
  let info ← analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys ms
  if info.ty.base != .B then throw .invalidMiniscriptType
  if !info.m then throw .miniscriptMalleable
  if !info.s then throw .miniscriptMissingSignature
  if !info.k then throw .miniscriptTimelockMix
  match info.stackSat, info.opsSat with
  | some ss, some os =>
    if ss > 100 || info.opsCount + os > 201 || info.scriptSize > 3600 then
      throw .miniscriptResourceLimit
  | _, _ => throw .miniscriptResourceLimit

/-! ## Section 5: Whole-Policy Validation, Placeholder Coverage, Ownership & Auth -/

def collectMiniscriptKeyExprs : Miniscript → List KeyExpr
  | .ms0 | .ms1 | .older _ | .after _
  | .sha256 _ | .hash256 _ | .ripemd160 _ | .hash160 _ => []
  | .pk ke | .pkh ke | .pk_k ke | .pk_h ke => [ke]
  | .multi _ kes | .multi_a _ kes => kes
  | .andor x y z =>
    collectMiniscriptKeyExprs x ++ collectMiniscriptKeyExprs y ++ collectMiniscriptKeyExprs z
  | .and_v x y | .and_b x y | .and_n x y
  | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
    collectMiniscriptKeyExprs x ++ collectMiniscriptKeyExprs y
  | .thresh _ subs =>
    let rec goList : List Miniscript → List KeyExpr
      | [] => []
      | m :: ms => collectMiniscriptKeyExprs m ++ goList ms
    goList subs
  | .wrap _ sub => collectMiniscriptKeyExprs sub

def collectWshKeyExprs : WshScript → List KeyExpr
  | .sortedmulti _ kes => kes
  | .miniscript ms => collectMiniscriptKeyExprs ms

def collectTapLeafKeyExprs : TapLeafScript → List KeyExpr
  | .sortedmulti_a _ kes => kes
  | .miniscript ms => collectMiniscriptKeyExprs ms

def collectTapTreeKeyExprs : TapTree → List KeyExpr
  | .leaf s => collectTapLeafKeyExprs s
  | .branch l r => collectTapTreeKeyExprs l ++ collectTapTreeKeyExprs r

def collectTemplateKeyExprs : DescriptorTemplate → List KeyExpr
  | .pkh ke | .wpkh ke => [ke]
  | .sh (.wpkh ke) => [ke]
  | .sh (.multi _ kes) | .sh (.sortedmulti _ kes) => kes
  | .sh (.wsh inner) => collectWshKeyExprs inner
  | .wsh inner => collectWshKeyExprs inner
  | .tr ik none => [ik]
  | .tr ik (some tree) => ik :: collectTapTreeKeyExprs tree

def tapTreeDepth : TapTree → Nat
  | .leaf _ => 1
  | .branch l r => 1 + max (tapTreeDepth l) (tapTreeDepth r)

def miniscriptAstDepth : Miniscript → Nat
  | .ms0 | .ms1 | .pk _ | .pkh _ | .pk_k _ | .pk_h _
  | .older _ | .after _ | .sha256 _ | .hash256 _ | .ripemd160 _ | .hash160 _
  | .multi _ _ | .multi_a _ _ => 1
  | .wrap _ sub => 1 + miniscriptAstDepth sub
  | .and_v x y | .and_b x y | .and_n x y
  | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
    1 + max (miniscriptAstDepth x) (miniscriptAstDepth y)
  | .andor x y z =>
    1 + max (miniscriptAstDepth x) (max (miniscriptAstDepth y) (miniscriptAstDepth z))
  | .thresh _ subs =>
    let rec maxList : List Miniscript → Nat
      | [] => 0
      | m :: ms => max (miniscriptAstDepth m) (maxList ms)
    1 + maxList subs

def miniscriptThreshNesting : Miniscript → Nat
  | .ms0 | .ms1 | .pk _ | .pkh _ | .pk_k _ | .pk_h _
  | .older _ | .after _ | .sha256 _ | .hash256 _ | .ripemd160 _ | .hash160 _
  | .multi _ _ | .multi_a _ _ => 0
  | .wrap _ sub => miniscriptThreshNesting sub
  | .and_v x y | .and_b x y | .and_n x y
  | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
    max (miniscriptThreshNesting x) (miniscriptThreshNesting y)
  | .andor x y z =>
    max (miniscriptThreshNesting x) (max (miniscriptThreshNesting y) (miniscriptThreshNesting z))
  | .thresh _ subs =>
    let rec maxList : List Miniscript → Nat
      | [] => 0
      | m :: ms => max (miniscriptThreshNesting m) (maxList ms)
    1 + maxList subs

def miniscriptMaxThreshArity : Miniscript → Nat
  | .ms0 | .ms1 | .pk _ | .pkh _ | .pk_k _ | .pk_h _
  | .older _ | .after _ | .sha256 _ | .hash256 _ | .ripemd160 _ | .hash160 _
  | .multi _ _ | .multi_a _ _ => 0
  | .wrap _ sub => miniscriptMaxThreshArity sub
  | .and_v x y | .and_b x y | .and_n x y
  | .or_b x y | .or_c x y | .or_d x y | .or_i x y =>
    max (miniscriptMaxThreshArity x) (miniscriptMaxThreshArity y)
  | .andor x y z =>
    max (miniscriptMaxThreshArity x) (max (miniscriptMaxThreshArity y) (miniscriptMaxThreshArity z))
  | .thresh _ subs =>
    let rec maxList : List Miniscript → Nat
      | [] => 0
      | m :: ms => max (miniscriptMaxThreshArity m) (maxList ms)
    max subs.length (maxList subs)

def checkMiniscriptResourceBounds (profile : PolicyProfile) (ms : Miniscript) : Except PolicyError Unit := do
  if let some maxD := profile.maxMiniscriptDepth then
    if miniscriptAstDepth ms > maxD then throw .policyDepthExceeded
  if let some maxTN := profile.maxThreshNesting then
    if miniscriptThreshNesting ms > maxTN then throw .miniscriptResourceLimit
  if let some maxTC := profile.maxThreshChildren then
    if miniscriptMaxThreshArity ms > maxTC then throw .miniscriptResourceLimit

def dedupFirstAppearance : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let rec go (seen : List Nat) : List Nat → List Nat
      | [] => seen.reverse
      | y :: ys => if seen.contains y then go seen ys else go (y :: seen) ys
    go [x] xs

def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x <= y then x :: y :: ys else y :: insertNat x ys

def sortNats : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNats xs)

def derivationToPair : DerivationSpec → UInt32 × UInt32
  | .wildcard => (0, 1)
  | .multipath m n => (m, n)

def derivationStepForBranch (d : DerivationSpec) (isChange : Bool) : UInt32 :=
  let (m, n) := derivationToPair d
  if isChange then n else m

def keyExprDeriv : KeyExpr → DerivationSpec
  | .single _ d => d
  | .musig _ d => d

def keyExprReferencedIndices : KeyExpr → List Nat
  | .single k _ => [k]
  | .musig ks _ => ks

def sameKeyPlaceholder (kp1 kp2 : KeyExpr) : Bool :=
  match kp1, kp2 with
  | .single i _, .single j _ => i == j
  | .musig is1 _, .musig is2 _ => sortNats is1 == sortNats is2
  | _, _ => false

def disjointDerivations (d1 d2 : DerivationSpec) : Bool :=
  let (a1, b1) := derivationToPair d1
  let (a2, b2) := derivationToPair d2
  a1 != a2 && a1 != b2 && b1 != a2 && b1 != b2

def checkPairwiseDisjointMultipaths : List KeyExpr → Bool
  | [] => true
  | kp :: rest =>
    rest.all (fun kp' => if sameKeyPlaceholder kp kp' then disjointDerivations (keyExprDeriv kp) (keyExprDeriv kp') else true) &&
    checkPairwiseDisjointMultipaths rest

def checkPlaceholderCoverage (nKeys : Nat) (requireSequential : Bool) (keyExprs : List KeyExpr) :
    Except PolicyError Unit := do
  let allIdxs := keyExprs.foldr (fun ke acc => keyExprReferencedIndices ke ++ acc) []
  if allIdxs.isEmpty then throw .noKeyPlaceholders
  if allIdxs.any (fun k => decide (k >= nKeys)) then throw .outOfRangeKeyIndex
  let firstOrder := dedupFirstAppearance allIdxs
  if firstOrder.length != nKeys then throw .unreferencedKeyIndex
  if requireSequential && firstOrder != List.range nKeys then
    throw .nonSequentialKeyIndex

def checkWshScript (profile : PolicyProfile) (fmt : PolicyFormat) (insideSh : Bool) :
    WshScript → Except PolicyError Unit
  | .sortedmulti k keys => do
    let n := keys.length
    if k < 1 || k > n || n > profile.maxMultiKeys then throw .invalidMultisigThreshold
    checkKeyExprList fmt false profile.maxMusigKeys keys
  | .miniscript ms => do
    checkMiniscriptResourceBounds profile ms
    if insideSh && !profile.allowGeneralMiniscriptInShWsh then
      match ms with
      | .multi k keys =>
        let n := keys.length
        if k < 1 || k > n || n > profile.maxMultiKeys then throw .invalidMultisigThreshold
        checkKeyExprList fmt false profile.maxMusigKeys keys
      | _ => throw .invalidScriptContext
    else
      checkMiniscriptSane fmt .wshCtx profile.maxMultiKeys profile.maxMultiAKeys profile.maxMusigKeys ms

def checkTapTree (profile : PolicyProfile) (fmt : PolicyFormat) : TapTree → Except PolicyError Unit
  | .leaf (.sortedmulti_a k keys) => do
    let n := keys.length
    if k < 1 || k > n || n > profile.maxMultiAKeys then throw .invalidMultisigThreshold
    checkKeyExprList fmt profile.allowMusigInSortedmultiA profile.maxMusigKeys keys
  | .leaf (.miniscript ms) => do
    checkMiniscriptResourceBounds profile ms
    checkMiniscriptSane fmt .tapscriptCtx profile.maxMultiKeys profile.maxMultiAKeys profile.maxMusigKeys ms
  | .branch l r => do
    checkTapTree profile fmt l
    checkTapTree profile fmt r

def checkDescriptorTemplate (profile : PolicyProfile) (fmt : PolicyFormat) :
    DescriptorTemplate → Except PolicyError Unit
  | .pkh ke => checkKeyExprInContext fmt false profile.maxMusigKeys ke
  | .wpkh ke => checkKeyExprInContext fmt false profile.maxMusigKeys ke
  | .sh (.wpkh ke) => checkKeyExprInContext fmt false profile.maxMusigKeys ke
  | .sh (.multi k keys) | .sh (.sortedmulti k keys) => do
    let n := keys.length
    if k < 1 || k > n || n > profile.maxP2shMultiKeys then throw .invalidMultisigThreshold
    checkKeyExprList fmt false profile.maxMusigKeys keys
  | .sh (.wsh inner) => do
    if !profile.allowShWsh then throw .invalidScriptContext
    checkWshScript profile fmt true inner
  | .wsh inner => checkWshScript profile fmt false inner
  | .tr ik none => do
    if fmt == .v1 then throw .invalidScriptContext
    checkKeyExprInContext fmt true profile.maxMusigKeys ik
  | .tr ik (some tree) => do
    if fmt == .v1 then throw .invalidScriptContext
    if tapTreeDepth tree > 9 then throw .policyDepthExceeded
    checkKeyExprInContext fmt true profile.maxMusigKeys ik
    checkTapTree profile fmt tree

/-- Validate `ExtendedDescriptorTemplate` under BIP-388 wallet policy rules:
    `rawtr(...)` is unconditionally rejected with `.invalidScriptContext` in BIP-388 wallet policies
    (Ledger hardware wallets never register untweaked `rawtr` policies per BIP-388 & `wallet.c`). -/
def checkExtendedDescriptorTemplateForBip388 (profile : PolicyProfile) (fmt : PolicyFormat) :
    ExtendedDescriptorTemplate → Except PolicyError Unit
  | .standard dt => checkDescriptorTemplate profile fmt dt
  | .rawtr _ => .error .invalidScriptContext

def checkTemplateByteBounds (profile : PolicyProfile) (policy : WalletPolicy) : Bool :=
  match policy.rawTemplateBytesLen with
  | none => true
  | some len =>
    match policy.format with
    | .v1 =>
      match profile.maxTemplateBytesV1 with
      | none => true
      | some maxB => len <= maxB
    | .v2 =>
      match profile.maxTemplateBytesV2 with
      | none => true
      | some maxB => len <= maxB

def checkPolicyWellFormed (profile : PolicyProfile) (policy : WalletPolicy) : Except PolicyError Unit := do
  if !checkTemplateByteBounds profile policy then throw .miniscriptResourceLimit
  let nKeys := policy.keys.length
  if nKeys == 0 || nKeys > profile.maxPolicyKeys then throw .invalidKeyInfo
  if !policy.keys.all (validKeyInfoWithBounds profile.maxOriginSteps policy.format profile.network) then
    throw .invalidKeyInfo
  let compPubkeys := policy.keys.map (fun ki => ki.xpub.compressedPubkey)
  if !listNodup compPubkeys then throw .duplicatePubkey
  checkDescriptorTemplate profile policy.format policy.template
  let keyExprs := collectTemplateKeyExprs policy.template
  checkPlaceholderCoverage nKeys profile.requireSequentialPlaceholders keyExprs
  if !checkPairwiseDisjointMultipaths keyExprs then throw .overlappingMultipath

/-! ### Device Keystore Ownership & Registration / Stateless Authorization -/

def classifyKeyInfo (dev : DeviceRegistrationOracle) (net : Network) (ki : WalletKeyInfo) : PolicyKeyRole :=
  if ki.xpub.compressedPubkey == bip341NumsPubkey then
    .unspendable
  else
    match ki.origin with
    | some orig =>
      if orig.fingerprint == dev.masterFingerprint then
        match dev.deriveAtOrigin net orig.path with
        | some derived => if derived == ki.xpub then .internal else .external
        | none => .external
      else .external
    | none => .external

def isOurKey (dev : DeviceRegistrationOracle) (net : Network) (ki : WalletKeyInfo) : Bool :=
  classifyKeyInfo dev net ki == .internal

def hasOurKey (dev : DeviceRegistrationOracle) (net : Network) (policy : WalletPolicy) : Bool :=
  policy.keys.any (isOurKey dev net)

def listNthOpt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, idx + 1 => listNthOpt xs idx

def countInternalInKeyExpr (roles : List PolicyKeyRole) (ke : KeyExpr) : Nat :=
  ((keyExprReferencedIndices ke).filter (fun idx => listNthOpt roles idx == some .internal)).length

def checkMusigSingleInternal (roles : List PolicyKeyRole) : List KeyExpr → Bool
  | [] => true
  | (.single _ _) :: rest => checkMusigSingleInternal roles rest
  | (ke@(.musig _ _)) :: rest =>
    countInternalInKeyExpr roles ke <= 1 && checkMusigSingleInternal roles rest

def checkRegisteredSignability (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (policy : WalletPolicy) : Except PolicyError Unit := do
  let roles := policy.keys.map (classifyKeyInfo dev profile.network)
  let nInternal := (roles.filter (· == .internal)).length
  if nInternal < 1 then throw .missingInternalKey
  if policy.format == .v1 && nInternal != 1 then throw .invalidInternalKeyCount
  let keyExprs := collectTemplateKeyExprs policy.template
  if !checkMusigSingleInternal roles keyExprs then throw .invalidInternalKeyCount
  let nInternalExprs := (keyExprs.filter (fun ke => countInternalInKeyExpr roles ke > 0)).length
  if nInternalExprs > profile.maxInternalKeyExpressions then
    throw .invalidInternalKeyCount

def standardBip44Purpose : DescriptorTemplate → Option UInt32
  | .pkh (.single 0 d) => if derivationToPair d == (0, 1) then some 44 else none
  | .sh (.wpkh (.single 0 d)) => if derivationToPair d == (0, 1) then some 49 else none
  | .wpkh (.single 0 d) => if derivationToPair d == (0, 1) then some 84 else none
  | .tr (.single 0 d) none => if derivationToPair d == (0, 1) then some 86 else none
  | _ => none

def isDefaultStatelessPolicy (dev : DeviceRegistrationOracle) (net : Network)
    (policy : WalletPolicy) : Bool :=
  policy.name.isEmpty &&
  match standardBip44Purpose policy.template, policy.keys with
  | some purpose, [ki] =>
    isOurKey dev net ki &&
    match ki.origin with
    | some orig =>
      match orig.path with
      | [pStep, cStep, aStep] =>
        pStep == hardened purpose &&
        cStep == hardened (coinTypeOfNetwork net) &&
        hardenedBit <= aStep &&
        aStep <= hardened maxDefaultBip44Account
      | _ => false
    | none => false
  | _, _ => false

def validatePolicyRegistration (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (policy : WalletPolicy) (userApproved : Bool) : Except PolicyError Unit := do
  if !validRegisteredWalletName profile policy.name then throw .invalidWalletName
  checkPolicyWellFormed profile policy
  checkRegisteredSignability profile dev policy
  if !userApproved then throw .unauthorizedPolicy

def authorizePolicyUse (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (policy : WalletPolicy) (auth : PolicyAuthorization) (addressIndex : UInt32) :
    Except PolicyError Unit := do
  if !isUnhardened addressIndex then throw .invalidAddressIndex
  checkPolicyWellFormed profile policy
  match auth with
  | .statelessDefault =>
    if !profile.allowStatelessDefaultPolicies then throw .unauthorizedPolicy
    if !isDefaultStatelessPolicy dev profile.network policy then throw .unauthorizedPolicy
    if addressIndex > maxDefaultAddressIndex then throw .invalidAddressIndex
  | .proofOfRegistration hmac =>
    if !validRegisteredWalletName profile policy.name then throw .invalidWalletName
    if hmac.size != 32 || hmac == zeroBytes32 then throw .unauthorizedPolicy
    if !dev.verifyRegistrationProof policy hmac then throw .unauthorizedPolicy
  | .userConfirmedRegistration =>
    throw .unauthorizedPolicy

/-! ## Section 6: Canonical Script Compiler, BIP-341 TapTree/TapTweak & Address/Registration API -/

def OP_0 : UInt8 := 0x00
def OP_1 : UInt8 := 0x51
def OP_IF : UInt8 := 0x63
def OP_NOTIF : UInt8 := 0x64
def OP_ELSE : UInt8 := 0x67
def OP_ENDIF : UInt8 := 0x68
def OP_VERIFY : UInt8 := 0x69
def OP_TOALTSTACK : UInt8 := 0x6B
def OP_FROMALTSTACK : UInt8 := 0x6C
def OP_IFDUP : UInt8 := 0x73
def OP_DUP : UInt8 := 0x76
def OP_SWAP : UInt8 := 0x7C
def OP_SIZE : UInt8 := 0x82
def OP_EQUAL : UInt8 := 0x87
def OP_EQUALVERIFY : UInt8 := 0x88
def OP_0NOTEQUAL : UInt8 := 0x92
def OP_ADD : UInt8 := 0x93
def OP_BOOLAND : UInt8 := 0x9A
def OP_BOOLOR : UInt8 := 0x9B
def OP_NUMEQUAL : UInt8 := 0x9C
def OP_NUMEQUALVERIFY : UInt8 := 0x9D
def OP_RIPEMD160 : UInt8 := 0xA6
def OP_SHA256 : UInt8 := 0xA8
def OP_HASH160 : UInt8 := 0xA9
def OP_HASH256 : UInt8 := 0xAA
def OP_CHECKSIG : UInt8 := 0xAC
def OP_CHECKSIGVERIFY : UInt8 := 0xAD
def OP_CHECKMULTISIG : UInt8 := 0xAE
def OP_CHECKMULTISIGVERIFY : UInt8 := 0xAF
def OP_CLTV : UInt8 := 0xB1
def OP_CSV : UInt8 := 0xB2
def OP_CHECKSIGADD : UInt8 := 0xBA

def pushScriptU32 (n : UInt32) : ByteArray :=
  if n == 0 then
    ByteArray.mk #[OP_0]
  else if n <= 16 then
    ByteArray.mk #[0x50 + n.toUInt8]
  else
    let le := encodeU32LE n
    if n <= 0x7F then
      ByteArray.mk #[1, le.get! 0]
    else if n <= 0x7FFF then
      ByteArray.mk #[2, le.get! 0, le.get! 1]
    else if n <= 0x7FFFFF then
      ByteArray.mk #[3, le.get! 0, le.get! 1, le.get! 2]
    else if n <= 0x7FFFFFFF then
      ByteArray.mk #[4] ++ le
    else
      ByteArray.mk #[5] ++ le ++ ByteArray.mk #[0x00]

def pushSmallBytes (bs : ByteArray) : ByteArray :=
  ByteArray.mk #[UInt8.ofNat bs.size] ++ bs

def emitOpVerify (verifyFlag : Bool) (op : UInt8) : ByteArray :=
  if verifyFlag then
    if op == OP_CHECKSIG || op == OP_CHECKMULTISIG || op == OP_NUMEQUAL || op == OP_EQUAL then
      ByteArray.mk #[op + 1]
    else
      ByteArray.mk #[op, OP_VERIFY]
  else
    ByteArray.mk #[op]

def hash160 (ora : CryptoPolicyOracle) (data : ByteArray) : ByteArray :=
  ora.ripemd160 (ora.sha256 data)

def hash256 (ora : CryptoPolicyOracle) (data : ByteArray) : ByteArray :=
  ora.sha256 (ora.sha256 data)

def taggedHash (ora : CryptoPolicyOracle) (tag : String) (msg : ByteArray) : ByteArray :=
  let tagDigest := ora.sha256 tag.toUTF8
  ora.sha256 (tagDigest ++ tagDigest ++ msg)

/-- BIP-341 `TapLeaf` hash with `leaf_version = 0xC0`:
    `SHA256_TapLeaf(0xC0 || compactSize(tapscript.size) || tapscript)`. -/
def tapLeafHash (ora : CryptoPolicyOracle) (tapscript : ByteArray) : ByteArray :=
  let payload := ByteArray.mk #[0xC0] ++ encodeCompactSize tapscript.size ++ tapscript
  taggedHash ora "TapLeaf" payload

/-- BIP-341 `TapBranch` hash sorting the two 32-byte child digests lexicographically before hashing. -/
def tapBranchHash (ora : CryptoPolicyOracle) (leftHash rightHash : ByteArray) : ByteArray :=
  let ordered :=
    if byteArrayLt leftHash rightHash then leftHash ++ rightHash
    else rightHash ++ leftHash
  taggedHash ora "TapBranch" ordered

/-- BIP-341 `TapTweak` digest `SHA256_TapTweak(internalXOnly || merkleRoot)`. -/
def tapTweakHash (ora : CryptoPolicyOracle) (internalXOnly : ByteArray)
    (merkleRoot : Option ByteArray) : ByteArray :=
  match merkleRoot with
  | none => taggedHash ora "TapTweak" internalXOnly
  | some h => taggedHash ora "TapTweak" (internalXOnly ++ h)

def lookupKeyXpub (keys : List WalletKeyInfo) (idx : Nat) : Except PolicyError ExtendedPubKey :=
  match listNthOpt keys idx with
  | some ki => .ok ki.xpub
  | none => .error .outOfRangeKeyIndex

def lookupMusigCompressedKeys (keys : List WalletKeyInfo) : List Nat → Except PolicyError (List ByteArray)
  | [] => .ok []
  | idx :: idxs => do
    let xpub ← lookupKeyXpub keys idx
    let rest ← lookupMusigCompressedKeys keys idxs
    .ok (xpub.compressedPubkey :: rest)

def deriveKeyExprCompressedPubkey (ora : CryptoPolicyOracle) (net : Network)
    (keys : List WalletKeyInfo) (isChange : Bool) (addressIndex : UInt32)
    (ke : KeyExpr) : Except PolicyError ByteArray := do
  if !isUnhardened addressIndex then throw .invalidAddressIndex
  let baseXpub ←
    match ke with
    | .single idx _ => lookupKeyXpub keys idx
    | .musig idxs _ => do
      let rawPks ← lookupMusigCompressedKeys keys idxs
      let sortedPks := sortByteArrays rawPks
      match ora.musigKeyAgg sortedPks with
      | some aggPk =>
        if aggPk.size != 33 then throw .keyDerivationFailed
        pure {
          version := xpubVersionOfNetwork net
          depth := 0
          parentFingerprint := 0
          childNumber := 0
          chainCode := bip328ChainCode
          compressedPubkey := aggPk
        }
      | none => throw .keyDerivationFailed
  let step1 := derivationStepForBranch (keyExprDeriv ke) isChange
  if !isUnhardened step1 then throw .invalidDerivationSuffix
  if baseXpub.depth.toNat >= 254 then throw .keyDerivationFailed
  let child1 ←
    match ora.ckdPub baseXpub step1 with
    | some x => pure x
    | none => throw .keyDerivationFailed
  let child2 ←
    match ora.ckdPub child1 addressIndex with
    | some x => pure x
    | none => throw .keyDerivationFailed
  if child2.compressedPubkey.size != 33 then throw .keyDerivationFailed
  .ok child2.compressedPubkey

def deriveKeyExprList (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) : List KeyExpr → Except PolicyError (List ByteArray)
  | [] => .ok []
  | ke :: kes => do
    let pk ← deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke
    let rest ← deriveKeyExprList ora net keys isChange addressIndex kes
    .ok (pk :: rest)

def compileMultiScript (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) (sorted : Bool) (verifyFlag : Bool)
    (k : Nat) (keyExprs : List KeyExpr) : Except PolicyError ByteArray := do
  let n := keyExprs.length
  if k < 1 || k > n then throw .invalidMultisigThreshold
  let derivedPks ← deriveKeyExprList ora net keys isChange addressIndex keyExprs
  let orderedPks := if sorted then sortByteArrays derivedPks else derivedPks
  let pushedKeys := orderedPks.foldl (fun acc pk => acc ++ pushSmallBytes pk) ByteArray.empty
  .ok (
    pushScriptU32 (UInt32.ofNat k) ++
    pushedKeys ++
    pushScriptU32 (UInt32.ofNat n) ++
    emitOpVerify verifyFlag OP_CHECKMULTISIG
  )

def compileMultiAScript (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) (sorted : Bool) (verifyFlag : Bool)
    (k : Nat) (keyExprs : List KeyExpr) : Except PolicyError ByteArray := do
  let n := keyExprs.length
  if k < 1 || k > n then throw .invalidMultisigThreshold
  let derivedPks ← deriveKeyExprList ora net keys isChange addressIndex keyExprs
  let xOnlyPks := derivedPks.map (fun pk => pk.extract 1 33)
  let orderedXOnly := if sorted then sortByteArrays xOnlyPks else xOnlyPks
  let body :=
    match orderedXOnly with
    | [] => ByteArray.empty
    | pk0 :: rest =>
      let init := pushSmallBytes pk0 ++ ByteArray.mk #[OP_CHECKSIG]
      rest.foldl (fun acc pk => acc ++ pushSmallBytes pk ++ ByteArray.mk #[OP_CHECKSIGADD]) init
  .ok (
    body ++
    pushScriptU32 (UInt32.ofNat k) ++
    emitOpVerify verifyFlag OP_NUMEQUAL
  )

/-- Canonical BIP-379 Miniscript-to-Bitcoin-Script compiler:
    - `andor(X,Y,Z)` compiles to `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF` (canonical BIP-379 / BOLOS,
      avoiding Vanadium `script.rs:367-373`'s inverted `Y`/`Z` bug);
    - `v:` verification fusion propagates cleanly into `a:` (`OP_FROMALTSTACK OP_VERIFY`) and `s:`. -/
def compileMiniscript (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (ctx : MiniscriptCtx) (isChange : Bool) (addressIndex : UInt32) (verifyFlag : Bool) :
    Miniscript → Except PolicyError ByteArray
  | .ms0 => .ok (emitOpVerify verifyFlag OP_0)
  | .ms1 => .ok (emitOpVerify verifyFlag OP_1)
  | .pk ke => do
    let cpk ← deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke
    let pkBytes := if ctx == .tapscriptCtx then cpk.extract 1 33 else cpk
    .ok (pushSmallBytes pkBytes ++ emitOpVerify verifyFlag OP_CHECKSIG)
  | .pkh ke => do
    let cpk ← deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke
    let pkBytes := if ctx == .tapscriptCtx then cpk.extract 1 33 else cpk
    let pkh20 := hash160 ora pkBytes
    .ok (
      ByteArray.mk #[OP_DUP, OP_HASH160] ++
      pushSmallBytes pkh20 ++
      ByteArray.mk #[OP_EQUALVERIFY] ++
      emitOpVerify verifyFlag OP_CHECKSIG
    )
  | .pk_k ke => do
    let cpk ← deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke
    let pkBytes := if ctx == .tapscriptCtx then cpk.extract 1 33 else cpk
    .ok (pushSmallBytes pkBytes ++ (if verifyFlag then ByteArray.mk #[OP_VERIFY] else ByteArray.empty))
  | .pk_h ke => do
    let cpk ← deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke
    let pkBytes := if ctx == .tapscriptCtx then cpk.extract 1 33 else cpk
    let pkh20 := hash160 ora pkBytes
    .ok (
      ByteArray.mk #[OP_DUP, OP_HASH160] ++
      pushSmallBytes pkh20 ++
      ByteArray.mk #[OP_EQUALVERIFY] ++
      (if verifyFlag then ByteArray.mk #[OP_VERIFY] else ByteArray.empty)
    )
  | .older val =>
    .ok (pushScriptU32 val ++ emitOpVerify verifyFlag OP_CSV)
  | .after val =>
    .ok (pushScriptU32 val ++ emitOpVerify verifyFlag OP_CLTV)
  | .sha256 h =>
    .ok (
      ByteArray.mk #[OP_SIZE, 0x01, 0x20, OP_EQUALVERIFY, OP_SHA256] ++
      pushSmallBytes h ++
      emitOpVerify verifyFlag OP_EQUAL
    )
  | .hash256 h =>
    .ok (
      ByteArray.mk #[OP_SIZE, 0x01, 0x20, OP_EQUALVERIFY, OP_HASH256] ++
      pushSmallBytes h ++
      emitOpVerify verifyFlag OP_EQUAL
    )
  | .ripemd160 h =>
    .ok (
      ByteArray.mk #[OP_SIZE, 0x01, 0x20, OP_EQUALVERIFY, OP_RIPEMD160] ++
      pushSmallBytes h ++
      emitOpVerify verifyFlag OP_EQUAL
    )
  | .hash160 h =>
    .ok (
      ByteArray.mk #[OP_SIZE, 0x01, 0x20, OP_EQUALVERIFY, OP_HASH160] ++
      pushSmallBytes h ++
      emitOpVerify verifyFlag OP_EQUAL
    )
  | .andor x y z => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sz ← compileMiniscript ora net keys ctx isChange addressIndex false z
    let sy ← compileMiniscript ora net keys ctx isChange addressIndex false y
    .ok (
      sx ++ ByteArray.mk #[OP_NOTIF] ++
      sz ++ ByteArray.mk #[OP_ELSE] ++
      sy ++ emitOpVerify verifyFlag OP_ENDIF
    )
  | .and_v x y => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sy ← compileMiniscript ora net keys ctx isChange addressIndex verifyFlag y
    .ok (sx ++ sy)
  | .and_b x y => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sy ← compileMiniscript ora net keys ctx isChange addressIndex false y
    .ok (sx ++ sy ++ emitOpVerify verifyFlag OP_BOOLAND)
  | .and_n x y => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sy ← compileMiniscript ora net keys ctx isChange addressIndex false y
    .ok (
      sx ++ ByteArray.mk #[OP_NOTIF, OP_0, OP_ELSE] ++
      sy ++ emitOpVerify verifyFlag OP_ENDIF
    )
  | .or_b x z => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sz ← compileMiniscript ora net keys ctx isChange addressIndex false z
    .ok (sx ++ sz ++ emitOpVerify verifyFlag OP_BOOLOR)
  | .or_c x z => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sz ← compileMiniscript ora net keys ctx isChange addressIndex false z
    .ok (sx ++ ByteArray.mk #[OP_NOTIF] ++ sz ++ emitOpVerify verifyFlag OP_ENDIF)
  | .or_d x z => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sz ← compileMiniscript ora net keys ctx isChange addressIndex false z
    .ok (sx ++ ByteArray.mk #[OP_IFDUP, OP_NOTIF] ++ sz ++ emitOpVerify verifyFlag OP_ENDIF)
  | .or_i x z => do
    let sx ← compileMiniscript ora net keys ctx isChange addressIndex false x
    let sz ← compileMiniscript ora net keys ctx isChange addressIndex false z
    .ok (
      ByteArray.mk #[OP_IF] ++ sx ++
      ByteArray.mk #[OP_ELSE] ++ sz ++
      emitOpVerify verifyFlag OP_ENDIF
    )
  | .thresh k subs => do
    if subs.isEmpty then throw .invalidMultisigThreshold
    let rec compileChildren (isFirst : Bool) : List Miniscript → Except PolicyError ByteArray
      | [] => .ok ByteArray.empty
      | m :: ms => do
        let sm ← compileMiniscript ora net keys ctx isChange addressIndex false m
        let rest ← compileChildren false ms
        if isFirst then .ok (sm ++ rest)
        else .ok (sm ++ ByteArray.mk #[OP_ADD] ++ rest)
    let body ← compileChildren true subs
    .ok (body ++ pushScriptU32 (UInt32.ofNat k) ++ emitOpVerify verifyFlag OP_EQUAL)
  | .multi k kes => do
    if ctx != .wshCtx then throw .invalidScriptContext
    compileMultiScript ora net keys isChange addressIndex false verifyFlag k kes
  | .multi_a k kes => do
    if ctx != .tapscriptCtx then throw .invalidScriptContext
    compileMultiAScript ora net keys isChange addressIndex false verifyFlag k kes
  | .wrap w sub =>
    match w with
    | .a => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (ByteArray.mk #[OP_TOALTSTACK] ++ s ++ emitOpVerify verifyFlag OP_FROMALTSTACK)
    | .s => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex verifyFlag sub
      .ok (ByteArray.mk #[OP_SWAP] ++ s)
    | .c => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (s ++ emitOpVerify verifyFlag OP_CHECKSIG)
    | .t => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (s ++ emitOpVerify verifyFlag OP_1)
    | .d => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (ByteArray.mk #[OP_DUP, OP_IF] ++ s ++ emitOpVerify verifyFlag OP_ENDIF)
    | .v =>
      compileMiniscript ora net keys ctx isChange addressIndex true sub
    | .j => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (ByteArray.mk #[OP_SIZE, OP_0NOTEQUAL, OP_IF] ++ s ++ emitOpVerify verifyFlag OP_ENDIF)
    | .n => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (s ++ emitOpVerify verifyFlag OP_0NOTEQUAL)
    | .l => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (ByteArray.mk #[OP_IF, OP_0, OP_ELSE] ++ s ++ emitOpVerify verifyFlag OP_ENDIF)
    | .u => do
      let s ← compileMiniscript ora net keys ctx isChange addressIndex false sub
      .ok (ByteArray.mk #[OP_IF] ++ s ++ ByteArray.mk #[OP_ELSE, OP_0] ++ emitOpVerify verifyFlag OP_ENDIF)

def compileWshWitnessScript (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) : WshScript → Except PolicyError ByteArray
  | .sortedmulti k kes => compileMultiScript ora net keys isChange addressIndex true false k kes
  | .miniscript ms => compileMiniscript ora net keys .wshCtx isChange addressIndex false ms

def compileTapLeafScript (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) : TapLeafScript → Except PolicyError ByteArray
  | .sortedmulti_a k kes => compileMultiAScript ora net keys isChange addressIndex true false k kes
  | .miniscript ms => compileMiniscript ora net keys .tapscriptCtx isChange addressIndex false ms

def computeTapTreeHash (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) : TapTree → Except PolicyError ByteArray
  | .leaf leafScript => do
    let script ← compileTapLeafScript ora net keys isChange addressIndex leafScript
    .ok (tapLeafHash ora script)
  | .branch left right => do
    let lh ← computeTapTreeHash ora net keys isChange addressIndex left
    let rh ← computeTapTreeHash ora net keys isChange addressIndex right
    .ok (tapBranchHash ora lh rh)

def mkP2PKH (pkh20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_DUP, OP_HASH160, 0x14] ++ pkh20 ++ ByteArray.mk #[OP_EQUALVERIFY, OP_CHECKSIG]

def mkP2WPKH (pkh20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_0, 0x14] ++ pkh20

def mkP2SH (sh20 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_HASH160, 0x14] ++ sh20 ++ ByteArray.mk #[OP_EQUAL]

def mkP2WSH (wsh32 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_0, 0x20] ++ wsh32

def mkP2TR (tweakedXOnly32 : ByteArray) : ByteArray :=
  ByteArray.mk #[OP_1, 0x20] ++ tweakedXOnly32

/-- Standalone `rawtr(KeyExpr)` output script evaluator (`OP_1 <untweaked-32B-xonly>`),
    available for low-level descriptor testing while excluded from BIP-388 wallet policy registration. -/
def compileRawtrScriptPubKey (ora : CryptoPolicyOracle) (net : Network) (keys : List WalletKeyInfo)
    (isChange : Bool) (addressIndex : UInt32) (ke : KeyExpr) : Except PolicyError ByteArray := do
  let cpk ← deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke
  let untweakedXOnly := cpk.extract 1 33
  if untweakedXOnly.size != 32 then throw .keyDerivationFailed
  .ok (mkP2TR untweakedXOnly)

/-- Derive the canonical Bitcoin `scriptPubKey` for a `WalletPolicy` at `(isChange, addressIndex)`
    under `profile` and `ora`. -/
def deriveWalletScriptPubKeyWithProfile (profile : PolicyProfile) (ora : CryptoPolicyOracle)
    (policy : WalletPolicy) (isChange : Bool) (addressIndex : UInt32) :
    Except PolicyError ByteArray := do
  if !isUnhardened addressIndex then throw .invalidAddressIndex
  checkPolicyWellFormed profile policy
  let net := profile.network
  match policy.template with
  | .pkh ke => do
    let cpk ← deriveKeyExprCompressedPubkey ora net policy.keys isChange addressIndex ke
    .ok (mkP2PKH (hash160 ora cpk))
  | .wpkh ke => do
    let cpk ← deriveKeyExprCompressedPubkey ora net policy.keys isChange addressIndex ke
    .ok (mkP2WPKH (hash160 ora cpk))
  | .sh (.wpkh ke) => do
    let cpk ← deriveKeyExprCompressedPubkey ora net policy.keys isChange addressIndex ke
    let redeemScript := mkP2WPKH (hash160 ora cpk)
    .ok (mkP2SH (hash160 ora redeemScript))
  | .sh (.multi k kes) => do
    let redeemScript ← compileMultiScript ora net policy.keys isChange addressIndex false false k kes
    .ok (mkP2SH (hash160 ora redeemScript))
  | .sh (.sortedmulti k kes) => do
    let redeemScript ← compileMultiScript ora net policy.keys isChange addressIndex true false k kes
    .ok (mkP2SH (hash160 ora redeemScript))
  | .sh (.wsh inner) => do
    let witnessScript ← compileWshWitnessScript ora net policy.keys isChange addressIndex inner
    let redeemScript := mkP2WSH (ora.sha256 witnessScript)
    .ok (mkP2SH (hash160 ora redeemScript))
  | .wsh inner => do
    let witnessScript ← compileWshWitnessScript ora net policy.keys isChange addressIndex inner
    .ok (mkP2WSH (ora.sha256 witnessScript))
  | .tr ik treeOpt => do
    let cpk ← deriveKeyExprCompressedPubkey ora net policy.keys isChange addressIndex ik
    let internalXOnly := cpk.extract 1 33
    let merkleRootOpt ←
      match treeOpt with
      | none => pure none
      | some tree => do
        let root ← computeTapTreeHash ora net policy.keys isChange addressIndex tree
        pure (some root)
    match ora.taprootTweakPubkey internalXOnly merkleRootOpt with
    | some (tweakedXOnly, _) =>
      if tweakedXOnly.size != 32 then throw .taprootTweakFailed
      .ok (mkP2TR tweakedXOnly)
    | none => throw .taprootTweakFailed

/-- Canonical `deriveWalletScriptPubKey` over `canonicalLedgerProfile .mainnet` with
    `requireSequentialPlaceholders := false`. -/
def deriveWalletScriptPubKey (ora : CryptoPolicyOracle) (policy : WalletPolicy)
    (isChange : Bool) (addressIndex : UInt32) : Except PolicyError ByteArray :=
  deriveWalletScriptPubKeyWithProfile
    { canonicalLedgerProfile .mainnet with requireSequentialPlaceholders := false }
    ora policy isChange addressIndex

/-- Authorized wallet policy `scriptPubKey` derivation (`GET_WALLET_ADDRESS` / `SIGN_PSBT` core):
    enforces stateless default policy rules (`BIP-44/49/84/86`, `addressIndex <= 50000`) or
    registered 32-byte non-zero HMAC / Proof-of-Registration verification before deriving the script. -/
def deriveWalletPolicyScript (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (ora : CryptoPolicyOracle) (policy : WalletPolicy) (auth : PolicyAuthorization)
    (isChange : Bool) (addressIndex : UInt32) : Except PolicyError ByteArray := do
  authorizePolicyUse profile dev policy auth addressIndex
  deriveWalletScriptPubKeyWithProfile profile ora policy isChange addressIndex

/-- Alias matching `Spec.WalletPolicy.deriveAuthorizedWalletScriptPubKey`. -/
abbrev deriveAuthorizedWalletScriptPubKey := deriveWalletPolicyScript

/-- Derive the formatted Bitcoin address (`Base58Check`, `Bech32`, or `Bech32m`) for an authorized
    wallet policy at `(isChange, addressIndex)` (`GET_WALLET_ADDRESS` / `GetAddress`). -/
def deriveWalletPolicyAddress (target : Spec.AddressTarget) (profile : PolicyProfile)
    (dev : DeviceRegistrationOracle) (ora : CryptoPolicyOracle) (policy : WalletPolicy)
    (auth : PolicyAuthorization) (isChange : Bool) (addressIndex : UInt32) :
    Except PolicyError String := do
  let spk ← deriveWalletPolicyScript profile dev ora policy auth isChange addressIndex
  let net := specNetworkOfPolicyNetwork profile.network
  match Spec.scriptToAddress? target (hash256 ora) net spk with
  | some addr => .ok addr
  | none => .error .invalidScriptContext

/-! ### BOLOS `wallet_id` & Vanadium `NamedAccount` PoR Registration Commitments & HMAC -/

def bolosWalletSlip21Label : ByteArray :=
  ByteArray.mk #[0x00] ++ "LEDGER-Wallet policy".toUTF8

def vanadiumPorSlip21Label : ByteArray :=
  "Proof of Registration".toUTF8

def policyFormatWireTag : PolicyFormat → UInt8
  | .v1 => 1
  | .v2 => 2

def computeBolosWalletId (ora : CryptoPolicyOracle) (fmt : PolicyFormat) (name : String)
    (descriptorBytes : ByteArray) (nKeys : Nat) (keysMerkleRoot32 : ByteArray) : ByteArray :=
  let nameBytes := name.toUTF8
  let descCommitment :=
    match fmt with
    | .v1 => descriptorBytes
    | .v2 => ora.sha256 descriptorBytes
  let preimage :=
    ByteArray.mk #[policyFormatWireTag fmt, UInt8.ofNat nameBytes.size] ++
    nameBytes ++
    encodeCompactSize descriptorBytes.size ++
    descCommitment ++
    encodeCompactSize nKeys ++
    keysMerkleRoot32
  ora.sha256 preimage

def computeVanadiumRegistrationId (ora : CryptoPolicyOracle) (name : String)
    (serializedBip388Policy : ByteArray) : ByteArray :=
  let nameBytes := name.toUTF8
  let preimage :=
    ByteArray.mk #[0x0D] ++ "NAMED_ACCOUNT".toUTF8 ++
    encodeU32BE 1 ++
    encodeCompactSize nameBytes.size ++
    nameBytes ++
    encodeU32LE 1 ++
    serializedBip388Policy
  ora.sha256 preimage

/-- Target-specific registration commitment input (`REGISTER_WALLET` on BOLOS vs
    `RegisterAccount` on Vanadium). -/
inductive RegistrationCommitmentInput where
  | bolos (descriptorBytes : ByteArray) (keysMerkleRoot32 : ByteArray)
  | vanadium (serializedBip388Policy : ByteArray)

/-- Compute the 32-byte registration ID (`wallet_id` on BOLOS, `RegistrationId` on Vanadium). -/
def computeRegistrationCommitmentId (ora : CryptoPolicyOracle) (policy : WalletPolicy) :
    RegistrationCommitmentInput → ByteArray
  | .bolos descBytes keysRoot32 =>
    computeBolosWalletId ora policy.format policy.name descBytes policy.keys.length keysRoot32
  | .vanadium serPol =>
    computeVanadiumRegistrationId ora policy.name serPol

/-- Verify a 32-byte non-zero registration HMAC / ProofOfRegistration in constant-time style
    against an expected MAC generator `computeHmac32 : ByteArray → Option ByteArray`. -/
def verifyRegistrationHmac (ora : CryptoPolicyOracle)
    (computeHmac32 : ByteArray → Option ByteArray)
    (policy : WalletPolicy) (commitment : RegistrationCommitmentInput)
    (candidateHmac : ByteArray) : Bool :=
  if candidateHmac.size != 32 || candidateHmac == zeroBytes32 then
    false
  else
    let id32 := computeRegistrationCommitmentId ora policy commitment
    match computeHmac32 id32 with
    | some expectedHmac =>
      if expectedHmac.size != 32 || expectedHmac == zeroBytes32 then
        false
      else
        constantTimeEqBytes32 candidateHmac expectedHmac
    | none => false

/-- End-to-end `REGISTER_WALLET` / `RegisterAccount` handler (`verifyAndRegisterWalletPolicy`):
    1. Validates the wallet name (`1..=64` printable ASCII without edge spaces on BOLOS, printable
       ASCII on Vanadium);
    2. Validates BIP-388 policy well-formedness & BIP-379 Miniscript sanity;
    3. Validates device key ownership & signability (`hasOurKey`, `<= 1` internal key per `musig`,
       `<= maxInternalKeyExpressions`);
    4. Enforces explicit on-device user confirmation (`userApproved == true`);
    5. Computes `(id32, hmac32)` (`wallet_id` + SLIP-21 HMAC on BOLOS, `RegistrationId` + PoR on
       Vanadium), rejecting malformed or all-zero MACs. -/
def verifyAndRegisterWalletPolicy (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (ora : CryptoPolicyOracle) (computeHmac32 : ByteArray → Option ByteArray)
    (policy : WalletPolicy) (commitment : RegistrationCommitmentInput)
    (userApproved : Bool) : Except PolicyError (ByteArray × ByteArray) := do
  validatePolicyRegistration profile dev policy userApproved
  let id32 := computeRegistrationCommitmentId ora policy commitment
  if id32.size != 32 then throw .keyDerivationFailed
  match computeHmac32 id32 with
  | some hmac32 =>
    if hmac32.size != 32 || hmac32 == zeroBytes32 then
      throw .unauthorizedPolicy
    .ok (id32, hmac32)
  | none =>
    throw .keyDerivationFailed

end BitcoinLedger.WalletPolicy

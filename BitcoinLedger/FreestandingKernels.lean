namespace BitcoinLedger.FreestandingKernels

/-!
# `BitcoinLedger.FreestandingKernels` — Standalone Freestanding C99 Kernels (`ILP32` / BOLOS / Vanadium)

Standalone root module compiled directly by `turbo-lean`'s `lean-native emit-freestanding-c-lib`
across `thumbv6m`, `thumbv8m.main`, `riscv32imac`, and `x86_64`.

Compiler & ABI guarantees:
- **Zero imports** (standalone root compilation unit)
- **Zero heap/runtime allocations** (`0` `malloc`/`free`/`lean_alloc_*`/`lean_inc`/`lean_dec`/`lean_box`)
- **Zero undefined symbols** (pure fixed-width integer shifts, masks, additions, subtractions, and comparisons;
  no 64-bit `/` or `%` libgcc helpers on `ILP32`)
- **Stack frames `< 1024` bytes** (all functions are non-recursive leaf scalar routines)
- **Constructive equality/order** (`decide (...)` only, `0 Classical.choice`)
-/

/-! ## 1. Version & Satoshi Overflow-Safe Arithmetic -/

/-- Packed target version `2.4.1` (`0x00020401`) linked by `ffi/bolos/llb_bolos_shim.h`
    and `ffi/vanadium/src/lib.rs`. -/
@[export llb_version_packed]
def llbVersionPacked : UInt32 :=
  ((2 : UInt32) <<< 16) ||| ((4 : UInt32) <<< 8) ||| (1 : UInt32)

/-- Consensus `MAX_MONEY = 21_000_000 * 100_000_000 = 2_100_000_000_000_000` satoshis. -/
def MAX_MONEY_U64 : UInt64 := 2100000000000000

/-- Check `0 ≤ sats ≤ MAX_MONEY` (`2_100_000_000_000_000` satoshis). -/
@[export llb_valid_amount]
def llbValidAmount (sats : UInt64) : Bool :=
  decide (sats ≤ MAX_MONEY_U64)

/-- Overflow-free check that `a`, `b`, and `a + b` all lie in `[0, MAX_MONEY]`. -/
@[export llb_checked_add_sats_ok]
def llbCheckedAddSatsOk (a b : UInt64) : Bool :=
  decide (a ≤ MAX_MONEY_U64) && decide (b ≤ MAX_MONEY_U64 - a)

/-- Checked satoshi sum returning `a + b` when `llb_checked_add_sats_ok a b = true` (`0` otherwise). -/
@[export llb_checked_add_sats_val]
def llbCheckedAddSatsVal (a b : UInt64) : UInt64 :=
  if llbCheckedAddSatsOk a b then a + b else 0

/-- Underflow-free check that `a ≤ MAX_MONEY` and `b ≤ a` (so `a - b ∈ [0, MAX_MONEY]`). -/
@[export llb_checked_sub_sats_ok]
def llbCheckedSubSatsOk (a b : UInt64) : Bool :=
  decide (a ≤ MAX_MONEY_U64) && decide (b ≤ a)

/-- Checked satoshi difference returning `a - b` when `llb_checked_sub_sats_ok a b = true` (`0` otherwise). -/
@[export llb_checked_sub_sats_val]
def llbCheckedSubSatsVal (a b : UInt64) : UInt64 :=
  if llbCheckedSubSatsOk a b then a - b else 0

/-! ## 2. CompactSize / VarInt Header Length & Canonicality -/

/-- Canonical CompactSize / VarInt encoded byte length (`1`, `3`, `5`, or `9`) for `n : UInt64`. -/
@[export llb_varint_encoded_len]
def llbVarIntEncodedLen (n : UInt64) : UInt8 :=
  if decide (n ≤ 0xFC) then 1
  else if decide (n ≤ 0xFFFF) then 3
  else if decide (n ≤ 0xFFFFFFFF) then 5
  else 9

/-- Check that a VarInt prefix `tag` paired with decoded little-endian payload `decodedVal` is canonical:
    - `tag ≤ 0xFC`: `decodedVal == tag`
    - `tag == 0xFD`: `0xFD ≤ decodedVal ≤ 0xFFFF`
    - `tag == 0xFE`: `0x10000 ≤ decodedVal ≤ 0xFFFFFFFF`
    - `tag == 0xFF`: `0x100000000 ≤ decodedVal`. -/
@[export llb_varint_prefix_is_canonical]
def llbVarIntPrefixIsCanonical (tag : UInt8) (decodedVal : UInt64) : Bool :=
  if decide (tag ≤ 0xFC) then
    decide (decodedVal = tag.toUInt64)
  else if decide (tag = 0xFD) then
    decide (0xFD ≤ decodedVal) && decide (decodedVal ≤ 0xFFFF)
  else if decide (tag = 0xFE) then
    decide (0x10000 ≤ decodedVal) && decide (decodedVal ≤ 0xFFFFFFFF)
  else
    decide (0x100000000 ≤ decodedVal)

/-! ## 3. BIP-32 Hardened Index & Depth Gate Checks -/

/-- Check whether BIP-32 child index `idx` has the hardened bit (`0x80000000`) set. -/
@[export llb_bip32_is_hardened]
def llbBip32IsHardened (idx : UInt32) : Bool :=
  !decide ((idx &&& 0x80000000) = 0)

/-- Set the BIP-32 hardened bit (`n ||| 0x80000000`). -/
@[export llb_bip32_harden]
def llbBip32Harden (n : UInt32) : UInt32 :=
  n ||| 0x80000000

/-- Clear the BIP-32 hardened bit (`idx &&& 0x7FFFFFFF`). -/
@[export llb_bip32_unharden]
def llbBip32Unharden (idx : UInt32) : UInt32 :=
  idx &&& 0x7FFFFFFF

/-- BOLOS standard BIP-32 path depth gate (`depth ≤ 10`, `MAX_BIP32_PATH_STEPS`). -/
@[export llb_bip32_bolos_depth_ok]
def llbBip32BolosDepthOk (depth : UInt8) : Bool :=
  decide (depth ≤ 10)

/-- Vanadium `KeyTree::Standard` BIP-32 path depth gate (`depth ≤ 16`, `MAX_BIP32_PATH_LEN`). -/
@[export llb_bip32_vanadium_depth_ok]
def llbBip32VanadiumDepthOk (depth : UInt8) : Bool :=
  decide (depth ≤ 16)

/-- Check whether `purposeStep` is a hardened standard 3-step BIP purpose
    (`44'`, `49'`, `84'`, `86'`, `87'`, or `45'`). -/
@[export llb_bip32_standard_purpose_ok]
def llbBip32StandardPurposeOk (purposeStep : UInt32) : Bool :=
  llbBip32IsHardened purposeStep &&
    (let p := llbBip32Unharden purposeStep
     decide (p = 44) || decide (p = 49) || decide (p = 84) ||
     decide (p = 86) || decide (p = 87) || decide (p = 45))

/-! ## 4. Script, SegWit, Bech32 Polymod & `MINIMALDATA` Scalar Checks -/

/-- Decode a Bitcoin Script witness-version opcode (`OP_0 = 0x00` -> `0`, `OP_1..OP_16 = 0x51..0x60` -> `1..16`),
    returning `0xFF` when `op` is not a valid witness-version opcode. -/
@[export llb_witness_opcode_to_version]
def llbWitnessOpcodeToVersion (op : UInt8) : UInt8 :=
  if decide (op = 0x00) then
    0
  else if decide (0x51 ≤ op) && decide (op ≤ 0x60) then
    op - 0x50
  else
    0xFF

/-- Check SegWit witness version & program length rules (`v0`: `20` or `32` bytes; `v1..16`: `2..40` bytes). -/
@[export llb_segwit_program_valid]
def llbSegwitProgramValid (witver : UInt8) (progLen : UInt8) : Bool :=
  if decide (witver = 0) then
    decide (progLen = 20) || decide (progLen = 32)
  else if decide (witver ≤ 16) then
    decide (2 ≤ progLen) && decide (progLen ≤ 40)
  else
    false

/-- Single GF(32) generator-polynomial step for BIP-173 Bech32 / BIP-350 Bech32m `polymod`. -/
@[export llb_bech32_polymod_step]
def llbBech32PolymodStep (pre : UInt32) (val : UInt8) : UInt32 :=
  let b := pre >>> (25 : UInt32)
  let shifted := ((pre &&& 0x1FFFFFF) <<< 5) ^^^ val.toUInt32
  let g0 := if !decide ((b &&& 1) = 0) then (0x3b6a57b2 : UInt32) else 0
  let g1 := if !decide ((b &&& 2) = 0) then (0x26508e6d : UInt32) else 0
  let g2 := if !decide ((b &&& 4) = 0) then (0x1ea119fa : UInt32) else 0
  let g3 := if !decide ((b &&& 8) = 0) then (0x3d4233dd : UInt32) else 0
  let g4 := if !decide ((b &&& 16) = 0) then (0x2a1462b3 : UInt32) else 0
  shifted ^^^ g0 ^^^ g1 ^^^ g2 ^^^ g3 ^^^ g4

/-- Validate BIP-62 `MINIMALDATA` canonicality for a single push operation header `(op, firstByte, pushLen)`:
    - `OP_0` (`0x00`): `pushLen == 0`
    - `OP_1NEGATE` (`0x4F`): `pushLen == 1 && firstByte == 0x81`
    - `OP_1..OP_16` (`0x51..0x60`): `pushLen == 1 && firstByte == op - 0x50`
    - `0x01`: `pushLen == 1` and `firstByte` is neither `1..16` nor `0x81`
    - `0x02..0x4B` (`2..75`): `pushLen == op`
    - `OP_PUSHDATA1` (`0x4C`): `76 ≤ pushLen ≤ 255`
    - `OP_PUSHDATA2` (`0x4D`): `256 ≤ pushLen ≤ 65535`
    - `OP_PUSHDATA4` (`0x4E`): `65536 ≤ pushLen`. -/
@[export llb_minimal_push_opcode_ok]
def llbMinimalPushOpcodeOk (op : UInt8) (firstByte : UInt8) (pushLen : UInt32) : Bool :=
  if decide (op = 0x00) then
    decide (pushLen = 0)
  else if decide (op = 0x4F) then
    decide (pushLen = 1) && decide (firstByte = 0x81)
  else if decide (0x51 ≤ op) && decide (op ≤ 0x60) then
    decide (pushLen = 1) && decide (firstByte = op - 0x50)
  else if decide (op = 0x01) then
    decide (pushLen = 1) &&
      !((decide (1 ≤ firstByte) && decide (firstByte ≤ 16)) || decide (firstByte = 0x81))
  else if decide (0x02 ≤ op) && decide (op ≤ 0x4B) then
    decide (pushLen = op.toUInt32)
  else if decide (op = 0x4C) then
    decide (76 ≤ pushLen) && decide (pushLen ≤ 255)
  else if decide (op = 0x4D) then
    decide (256 ≤ pushLen) && decide (pushLen ≤ 65535)
  else if decide (op = 0x4E) then
    decide (65536 ≤ pushLen)
  else
    false

/-! ## 5. BOLOS APDU, Sighash & Merkle Scalar Checks -/

/-- Validate a 32-bit non-Taproot sighash type (`0x01`, `0x02`, `0x03`, `0x81`, `0x82`, `0x83`). -/
@[export llb_sighash_type_valid]
def llbSighashTypeValid (sighashU32 : UInt32) : Bool :=
  decide (sighashU32 ≤ 0xFF) &&
    (let base := sighashU32 &&& 0x7F
     decide (1 ≤ base) && decide (base ≤ 3))

/-- Validate a 1-byte BIP-341 Taproot sighash type (`0x00` `SIGHASH_DEFAULT` or `{0x01..0x03, 0x81..0x83}`). -/
@[export llb_taproot_sighash_valid]
def llbTaprootSighashValid (sighashByte : UInt8) : Bool :=
  decide (sighashByte = 0x00) ||
    (let base := sighashByte &&& 0x7F
     decide (1 ≤ base) && decide (base ≤ 3))

/-- Validate BOLOS Merkle inclusion-proof header bounds (`0 < treeSize`, `index < treeSize`,
    `index ≤ 0x7FFFFFFF`, and `depth ≤ 32`). -/
@[export llb_merkle_depth_index_ok]
def llbMerkleDepthIndexOk (treeSize : UInt32) (index : UInt32) (depth : UInt8) : Bool :=
  decide (0 < treeSize) &&
  decide (index < treeSize) &&
  decide (index ≤ 0x7FFFFFFF) &&
  decide (depth ≤ 32)

/-- Map compact `SpecError` discriminant tag (`0..18`) to its BOLOS 16-bit APDU status word
    (defaulting unknown tags `≥ 19` to `SW_BAD_STATE = 0xB007`). -/
@[export llb_bolos_sw_for_error]
def llbBolosSwForError (errTag : UInt8) : UInt16 :=
  if decide (errTag = 0) then 0x6700 -- wrongLength -> SW_WRONG_LENGTH
  else if decide (errTag = 1) then 0x6A87 -- wrongDataLength -> SW_WRONG_DATA_LENGTH
  else if decide (errTag = 2) then 0x6D00 -- unsupportedInstruction -> SW_INS_NOT_SUPPORTED
  else if decide (errTag = 3) then 0x6E00 -- unsupportedClass -> SW_CLA_NOT_SUPPORTED
  else if decide (errTag = 4) then 0x6A86 -- wrongP1P2 -> SW_WRONG_P1P2
  else if decide (errTag = 5) then 0x6985 -- userRejected -> SW_DENY
  else if decide (errTag = 6) then 0x6982 -- securityStatusNotSatisfied -> SW_SECURITY_STATUS_NOT_SATISFIED
  else if decide (errTag = 7) then 0x6B00 -- swapValidationFailed -> SW_FAIL_SWAP
  else if decide (errTag = 8) then 0x6A80 -- invalidData -> SW_INCORRECT_DATA
  else if decide (errTag = 9) then 0x6A80 -- bip32PathTooLong -> SW_INCORRECT_DATA
  else if decide (errTag = 10) then 0x6A82 -- unsupportedBip32Path -> SW_NOT_SUPPORTED
  else if decide (errTag = 11) then 0x6A82 -- notSupported -> SW_NOT_SUPPORTED
  else if decide (errTag = 12) then 0x6A80 -- invalidAmount -> SW_INCORRECT_DATA
  else if decide (errTag = 13) then 0x6A80 -- invalidScriptOrAddress -> SW_INCORRECT_DATA
  else if decide (errTag = 14) then 0x6A80 -- invalidWalletPolicy -> SW_INCORRECT_DATA
  else if decide (errTag = 15) then 0x6A80 -- invalidPsbt -> SW_INCORRECT_DATA
  else if decide (errTag = 16) then 0xB007 -- badState -> SW_BAD_STATE
  else if decide (errTag = 17) then 0xB000 -- wrongResponseLength -> SW_WRONG_RESPONSE_LENGTH
  else if decide (errTag = 18) then 0xB008 -- cryptoOrSignatureFailed -> SW_SIGNATURE_FAIL
  else 0xB007 -- fallback -> SW_BAD_STATE

/-! ## 6. Wave 4 BOLOS Optimization Kernels (Division-Free Satoshi Split, O(log n) Merkle, BIP32 & Bech32) -/

/-- 32x32->64 unsigned product `(a.toUInt64) * (b.toUInt64)`:
    lowered to single-cycle `muls` partial products on `thumbv6m`, `umull` on `thumbv8m.main`,
    and `mul`/`mulhu` on `riscv32imac` with **zero** `__aeabi_lmul` or `__aeabi_uldivmod` libcalls! -/
def mulU32ToU64 (a b : UInt32) : UInt64 :=
  a.toUInt64 * b.toUInt64

/-- Compute the high 64 bits of `x * 0xABCC77118461CEFD` using pure 32-bit `UInt32` limb arithmetic
    (`0` undefined libgcc/compiler-rt symbols across `thumbv6m`, `thumbv8m.main`, `riscv32imac`). -/
def mulHiRecip1e8 (x : UInt64) : UInt64 :=
  let x0 : UInt32 := x.toUInt32
  let x1 : UInt32 := (x >>> 32).toUInt32
  let m0 : UInt32 := 0x8461CEFD
  let m1 : UInt32 := 0xABCC7711
  let p00 : UInt64 := mulU32ToU64 x0 m0
  let p01 : UInt64 := mulU32ToU64 x0 m1
  let p10 : UInt64 := mulU32ToU64 x1 m0
  let p11 : UInt64 := mulU32ToU64 x1 m1
  let mid : UInt64 := (p00 >>> 32) + p01.toUInt32.toUInt64 + p10.toUInt32.toUInt64
  p11 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32)

/-- Exact division-free `amount / 100_000_000` for any `amount : UInt64`
    (`⌊amount * 0xABCC77118461CEFD / 2^90⌋`), eliminating 64-bit software division on BOLOS ARM. -/
@[export llb_sats_div_1e8]
def llbSatsDiv1e8 (amount : UInt64) : UInt64 :=
  (mulHiRecip1e8 amount) >>> 26

/-- Exact division-free `amount % 100_000_000` (`0..99_999_999`) for any `amount : UInt64`
    computed in 32-bit arithmetic (`amount.toUInt32 - q.toUInt32 * 100_000_000`). -/
@[export llb_sats_mod_1e8]
def llbSatsMod1e8 (amount : UInt64) : UInt32 :=
  let q := llbSatsDiv1e8 amount
  amount.toUInt32 - (q.toUInt32 * 100000000)

/-- Compute the largest power of `2` strictly less than `s` (for `s ≥ 2`) in `O(1)` branchless
    bit-smearing (`(((m ||| m>>>1 ||| m>>>2 ||| m>>>4 ||| m>>>8 ||| m>>>16) >>> 1) + 1)` where `m = s - 1`):
    lowers to 7 straight-line ALU instructions on ARM Thumb (`0` branches, `0` callee-saved pushes)! -/
def largestPow2LtU32 (s : UInt32) : UInt32 :=
  let m0 : UInt32 := s - 1
  let m1 : UInt32 := m0 ||| (m0 >>> 1)
  let m2 : UInt32 := m1 ||| (m1 >>> 2)
  let m4 : UInt32 := m2 ||| (m2 >>> 4)
  let m8 : UInt32 := m4 ||| (m4 >>> 8)
  let m16 : UInt32 := m8 ||| (m8 >>> 16)
  (m16 >>> 1) + 1

/-- Pack `(size, index)` into a single `UInt64` (`size * 2^32 + index`) so multi-step
    Merkle descent stays 100% unboxed scalar (`0` heap tuples / `0` `isShared`). -/
def packMerkleState (size index : UInt32) : UInt64 :=
  (size.toUInt64 <<< 32) + index.toUInt64

/-- Advance packed `(size, index)` (`(size <<< 32) ||| index`) by one Merkle tree level
    toward `index`:
    - returns `st` unchanged when `size ≤ 1` (already at leaf);
    - otherwise descends into left subtree `(mask, index)` or right subtree `(size - mask, index - mask)`. -/
@[export llb_merkle_advance_state]
def llbMerkleAdvanceState (st : UInt64) : UInt64 :=
  let size : UInt32 := (st >>> 32).toUInt32
  let index : UInt32 := st.toUInt32
  if decide (size ≤ 1) then
    st
  else
    let mask := largestPow2LtU32 size
    if decide (index < mask) then
      packMerkleState mask index
    else
      packMerkleState (size - mask) (index - mask)

/-- Extract the branch direction at packed `(size, index)` (`0` = left, `1` = right, `0xFF` = leaf / invalid). -/
@[export llb_merkle_state_dir]
def llbMerkleStateDir (st : UInt64) : UInt8 :=
  let size : UInt32 := (st >>> 32).toUInt32
  let index : UInt32 := st.toUInt32
  if decide (size ≤ 1) || !decide (index < size) then
    0xFF
  else
    let mask := largestPow2LtU32 size
    if decide (index < mask) then 0 else 1

/-- Exact scalar check for BOLOS `is_path_safe_for_pubkey_export` (`get_extended_pubkey.c`):
    given `p0..p3`, `pathLen`, `expectedCoinType` (`0` mainnet / `1` testnet), and whether all
    remaining tail steps (`p3..` for 3-step purposes or `p4..` for BIP-48) are unhardened. -/
@[export llb_bip32_pubkey_export_prefix_ok]
def llbBip32PubkeyExportPrefixOk (p0 p1 p2 p3 : UInt32) (pathLen : UInt8) (expectedCoinType : UInt32) (tailUnhardened : Bool) : Bool :=
  if decide (pathLen = 2) then
    decide (p0 = 0x80454C45) && decide (p1 = 0xC2494532)
  else if decide (pathLen < 3) || !tailUnhardened then
    false
  else if !(llbBip32IsHardened p0 && llbBip32IsHardened p1 && llbBip32IsHardened p2) then
    false
  else
    let purpose := llbBip32Unharden p0
    let coinType := llbBip32Unharden p1
    let account := llbBip32Unharden p2
    if !decide (coinType = expectedCoinType) || decide (100 < account) then
      false
    else if llbBip32StandardPurposeOk p0 then
      true
    else if decide (purpose = 48) then
      decide (4 ≤ pathLen) && llbBip32IsHardened p3 &&
        (let st := llbBip32Unharden p3
         decide (st = 1) || decide (st = 2))
    else
      false

/-- BIP-173 Bech32 (`1` -> `1`) / BIP-350 Bech32m (`2` -> `0x2bc830a3`) final polymod constant (`0` otherwise). -/
@[export llb_bech32_final_constant]
def llbBech32FinalConstant (enc : UInt8) : UInt32 :=
  if decide (enc = 1) then 1
  else if decide (enc = 2) then 0x2bc830a3
  else 0

/-- BOLOS wallet policy name character check (`0x20..0x7E` interior, `0x21..0x7E` non-space at first/last char). -/
@[export llb_wallet_name_char_ok]
def llbWalletNameCharOk (c : UInt8) (isEdge : Bool) : Bool :=
  let lo : UInt8 := if isEdge then 0x21 else 0x20
  decide (lo ≤ c) && decide (c ≤ 0x7E)

/-! ## 7. Option 2 Freestanding Zero-Copy Combinators (`SPEC_ABI.md` Section 1)

Stub bodies deliberately depend on every parameter so Lean 4.35 LCNF `Phase.mono` never
generates a `._redArg` wrapper that drops pointer parameters: every exported kernel below
keeps its `ConstBytes` / `MutBytes` / `ConstU32s` / `MutU16s` argument (lowered to a raw
`ptr` parameter by `turbo-lean`) live in its LCNF signature. On the host (Lean kernel /
constructive proofs) the stubs model pure memory reads as `0` and writes as identity. -/

/-- Read-only flat byte pointer (`const uint8_t*` in C99, `*const u8` in Rust). -/
structure ConstBytes where
  addr : USize

/-- Mutable flat byte pointer (`uint8_t*` in C99, `*mut u8` in Rust). -/
structure MutBytes where
  addr : USize

/-- Read-only aligned 32-bit word pointer (`const uint32_t*` in C99, `*const u32` in Rust). -/
structure ConstU32s where
  addr : USize

/-- Mutable aligned 16-bit word pointer (`uint16_t*` in C99, `*mut u16` in Rust). -/
structure MutU16s where
  addr : USize

/-- Read byte at `idx` (`align 1`). Freestanding: `p.addr + idx` dereference;
    host: pure stub depending on both parameters (models `0`). -/
@[noinline] def readU8 (p : ConstBytes) (idx : UInt32) : UInt8 :=
  (p.addr.toUInt32 ^^^ idx).toUInt8

/-- Read byte from mutable buffer at `idx` (`align 1`). -/
@[noinline] def readMutU8 (p : MutBytes) (idx : UInt32) : UInt8 :=
  (p.addr.toUInt32 ^^^ idx).toUInt8

/-- Write byte `val` into mutable buffer `p` at `idx` (`align 1`), returning `p` (linear
    state token; host stub keeps `addr` depending on `idx`/`val`). -/
@[noinline] def writeU8 (p : MutBytes) (idx : UInt32) (val : UInt8) : MutBytes :=
  { addr := p.addr ^^^ idx.toUSize ^^^ val.toUSize }

/-- Read aligned 32-bit word at `idx` (`align 4`). -/
@[noinline] def readU32 (p : ConstU32s) (idx : UInt32) : UInt32 :=
  p.addr.toUInt32 ^^^ idx

/-- Read aligned 16-bit word from mutable buffer at `idx` (`align 2`). -/
@[noinline] def readMutU16 (p : MutU16s) (idx : UInt32) : UInt16 :=
  (p.addr.toUInt32 ^^^ idx).toUInt16

/-- Write aligned 16-bit word `val` into mutable buffer `p` at `idx` (`align 2`), returning `p`. -/
@[noinline] def writeU16 (p : MutU16s) (idx : UInt32) (val : UInt16) : MutU16s :=
  { addr := p.addr ^^^ idx.toUSize ^^^ val.toUSize }

/-- Bounded non-recursive loop over `[lo, hi)` carrying `UInt64` state
    (`seqFor` in `turbo-lean` freestanding lowering, zero recursion, `O(1)` stack;
    host: `Nat`-fuel iteration over `hi - lo` steps). -/
@[noinline] def forRangeU64 (lo hi : UInt32) (init : UInt64) (step : UInt32 → UInt64 → UInt64) : UInt64 :=
  let count := (hi - lo).toNat
  let rec go (fuel : Nat) (cur : UInt32) (acc : UInt64) : UInt64 :=
    match fuel with
    | 0 => acc
    | fuel' + 1 => go fuel' (cur + 1) (step cur acc)
  if decide (lo < hi) then go count lo init else init

/-- Bounded non-recursive loop over `[lo, hi)` carrying `UInt32` state. -/
@[noinline] def forRangeU32 (lo hi : UInt32) (init : UInt32) (step : UInt32 → UInt32 → UInt32) : UInt32 :=
  let count := (hi - lo).toNat
  let rec go (fuel : Nat) (cur : UInt32) (acc : UInt32) : UInt32 :=
    match fuel with
    | 0 => acc
    | fuel' + 1 => go fuel' (cur + 1) (step cur acc)
  if decide (lo < hi) then go count lo init else init

/-- Bounded non-recursive unit-effect loop over `[lo, hi)` (the `1` / `fuel' + 2` match arms
    keep `step` live in every non-empty case so `Phase.mono` never drops the closure). -/
@[noinline] def forRangeUnit (lo hi : UInt32) (step : UInt32 → Unit) : Unit :=
  let count := (hi - lo).toNat
  let rec go (fuel : Nat) (cur : UInt32) : Unit :=
    match fuel with
    | 0 => ()
    | 1 => step cur
    | fuel' + 2 =>
      let _ := step cur
      go (fuel' + 1) (cur + 1)
  if decide (lo < hi) then go count lo else ()

/-- Branchless Boolean helpers (`0` LCNF join points, constant-time scalar ops). -/
def bnot (a : Bool) : Bool :=
  decide (a.toUInt8 = 0)

def band (a b : Bool) : Bool :=
  decide ((a.toUInt8 &&& b.toUInt8) = 1)

def bor (a b : Bool) : Bool :=
  decide ((a.toUInt8 ||| b.toUInt8) ≠ 0)

def selU16 (c : Bool) (t f : UInt16) : UInt16 :=
  f ^^^ ((0 - c.toUInt16) &&& (t ^^^ f))

def selU32 (c : Bool) (t f : UInt32) : UInt32 :=
  f ^^^ ((0 - c.toUInt32) &&& (t ^^^ f))

def selU64 (c : Bool) (t f : UInt64) : UInt64 :=
  f ^^^ ((0 - c.toUInt64) &&& (t ^^^ f))

/-! ## 8. Option 2 Miniscript Timelock & Branch Validators (VND-01 / VND-06) -/

/-- BIP-68 `older(n)` consensus range check (`policy.c:check_older_node_cb`,
    `WalletPolicy.validOlderArg` / `validOlderBitmask`): `(n & 0xFFBF0000) == 0` and
    `1 <= (n & 0xFFFF)`. -/
@[export llb_miniscript_older_ok]
def llbMiniscriptOlderOk (n : UInt32) : Bool :=
  band (decide ((n &&& 0xFFBF0000) = 0)) (decide (1 ≤ (n &&& 0xFFFF)))

/-- BIP-65 / BIP-379 `after(n)` consensus range check (`WalletPolicy.validAfterArg`): `1 <= n < 0x80000000`. -/
@[export llb_miniscript_after_ok]
def llbMiniscriptAfterOk (n : UInt32) : Bool :=
  band (decide (1 ≤ n)) (decide (n < 0x80000000))

/-- Canonical `andor` Script branch framing (`OP_NOTIF (0x64)`, `OP_ELSE (0x67)`, `OP_ENDIF (0x68)`, VND-01). -/
@[export llb_miniscript_andor_branches_valid]
def llbMiniscriptAndorBranchesValid (notifOp elseOp endifOp : UInt8) : Bool :=
  band (band (decide (notifOp = 0x64)) (decide (elseOp = 0x67))) (decide (endifOp = 0x68))

/-! ## 9. Option 2 Postfix Miniscript Typechecker (VND-01 / VND-05 / VND-06, BIP-379 / BIP-388)

Each node's type / malleability / timelock properties are packed into a single `UInt16`
(bits 0-1 `base` `0=B 1=V 2=K 3=W`, bit 2 `z`, bit 3 `o`, bit 4 `n`, bit 5 `d`, bit 6 `u`,
bit 7 `s`, bit 8 `f`, bit 9 `e`, bit 10 `m`, bit 11 `g`, bit 12 `h`, bit 13 `i`, bit 14 `j`,
bit 15 `k`) stored as two bytes in the caller-supplied `scratch : MutBytes` stack buffer
(max depth 64 -> 128 bytes). The whole parser is a single `forRangeU64` pass over
`ops[0..opsLen)` with a 49-bit packed loop state; zero recursion, zero heap. -/

/-- Node property bit positions. -/
def MSB_BASE : UInt16 := 0
def MSB_Z : UInt16 := 2
def MSB_O : UInt16 := 3
def MSB_N : UInt16 := 4
def MSB_D : UInt16 := 5
def MSB_U : UInt16 := 6
def MSB_S : UInt16 := 7
def MSB_F : UInt16 := 8
def MSB_E : UInt16 := 9
def MSB_M : UInt16 := 10
def MSB_G : UInt16 := 11
def MSB_H : UInt16 := 12
def MSB_I : UInt16 := 13
def MSB_J : UInt16 := 14
def MSB_K : UInt16 := 15

def msBit (x : UInt16) (b : UInt16) : Bool :=
  decide ((x >>> b) &&& 1 = 1)

def msOrBit (x : UInt16) (b : UInt16) (v : Bool) : UInt16 :=
  x ||| (v.toUInt16 <<< b)

/-- Pack `(base, z, o, n, d, u, s, f, e, m, g, h, i, j, k)` into one `UInt16`. -/
def msPack (base : UInt16) (z o n d u s f e m g h i j k : Bool) : UInt16 :=
  let r := base &&& 3
  let r := msOrBit r MSB_Z z
  let r := msOrBit r MSB_O o
  let r := msOrBit r MSB_N n
  let r := msOrBit r MSB_D d
  let r := msOrBit r MSB_U u
  let r := msOrBit r MSB_S s
  let r := msOrBit r MSB_F f
  let r := msOrBit r MSB_E e
  let r := msOrBit r MSB_M m
  let r := msOrBit r MSB_G g
  let r := msOrBit r MSB_H h
  let r := msOrBit r MSB_I i
  let r := msOrBit r MSB_J j
  msOrBit r MSB_K k

/-- Leaf `0` / `1` / hash functions (`B`, `m`, `k`, no timelocks). -/
def msLeafB (z o n d u s f e m : Bool) : UInt16 :=
  msPack 0 z o n d u s f e m false false false false true

/-- Read packed node `i` from `scratch` (little-endian `scratch[2i]`, `scratch[2i+1]`). -/
private def msRead (scratch : MutBytes) (i : UInt32) : UInt16 :=
  let lo := readMutU8 scratch (i * 2)
  let hi := readMutU8 scratch (i * 2 + 1)
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/-- Write packed node `i` into `scratch`. -/
private def msWrite (scratch : MutBytes) (i : UInt32) (v : UInt16) : Unit :=
  let _ := writeU8 scratch (i * 2) v.toUInt8
  let _ := writeU8 scratch (i * 2 + 1) (v >>> 8).toUInt8
  ()

/-- BIP-379 `timelockConflict(x, y)` on packed nodes: `(g_x ∧ h_y) ∨ (h_x ∧ g_y) ∨ (i_x ∧ j_y) ∨ (j_x ∧ i_y)`. -/
def msConflict (x y : UInt16) : Bool :=
  bor (bor (band (msBit x MSB_G) (msBit y MSB_H)) (band (msBit x MSB_H) (msBit y MSB_G)))
    (bor (band (msBit x MSB_I) (msBit y MSB_J)) (band (msBit x MSB_J) (msBit y MSB_I)))

/-- `true` when packed node `v` is the error sentinel `0xFFFF`. -/
def msErr (v : UInt16) : Bool :=
  decide (v = 0xFFFF)

/-- Apply a unary wrapper opcode (`0x10` `a:`, `0x11` `s:`, `0x12` `c:`, `0x13` `t:`,
    `0x14` `d:` (MINIMALIF `u` under Tapscript), `0x15` `v:`, `0x16` `j:`, `0x17` `n:`,
    `0x18` `l:`, `0x19` `u:`) to packed node `x`. Returns `0xFFFF` on type error, else the
    packed result. Rules match `WalletPolicy.analyzeMiniscript` (`.wrap w sub`) 1-to-1. -/
def msApplyUnary (op : UInt8) (isTapscript : UInt8) (x : UInt16) : UInt16 :=
  let base := x &&& 3
  let z := msBit x MSB_Z
  let o := msBit x MSB_O
  let n := msBit x MSB_N
  let d := msBit x MSB_D
  let u := msBit x MSB_U
  let s := msBit x MSB_S
  let f := msBit x MSB_F
  let e := msBit x MSB_E
  let m := msBit x MSB_M
  let g := msBit x MSB_G
  let h := msBit x MSB_H
  let i := msBit x MSB_I
  let j := msBit x MSB_J
  let k := msBit x MSB_K
  let isB := decide (base = 0)
  let isV := decide (base = 1)
  let isK := decide (base = 2)
  if decide (op = 0x10) then
    selU16 isB (msPack 3 false false false d u s f e m g h i j k) 0xFFFF
  else if decide (op = 0x11) then
    selU16 (band isB o) (msPack 3 false false false d u s f e m g h i j k) 0xFFFF
  else if decide (op = 0x12) then
    selU16 isK (msPack 0 false o n d true true f e m g h i j k) 0xFFFF
  else if decide (op = 0x13) then
    selU16 isV (msPack 0 z o n false true s true false m g h i j k) 0xFFFF
  else if decide (op = 0x14) then
    selU16 (band isV z) (msPack 0 false true true true (decide (isTapscript ≠ 0)) s false f m g h i j k) 0xFFFF
  else if decide (op = 0x15) then
    selU16 isB (msPack 1 z o n false false s true false m g h i j k) 0xFFFF
  else if decide (op = 0x16) then
    selU16 (band isB n) (msPack 0 false o true true u s false f m g h i j k) 0xFFFF
  else if decide (op = 0x17) then
    selU16 isB (msPack 0 z o n d true s f e m g h i j k) 0xFFFF
  else if bor (decide (op = 0x18)) (decide (op = 0x19)) then
    selU16 isB (msPack 0 false z false true u s false f m g h i j k) 0xFFFF
  else 0xFFFF

/-- Apply a binary combinator opcode (`0x20` `and_v`, `0x21` `and_b`, `0x22` `and_n`,
    `0x23` `or_b`, `0x24` `or_c`, `0x25` `or_d`, `0x26` `or_i`) to packed nodes `x y`.
    Returns `0xFFFF` on type error, else the packed result. -/
def msApplyBinary (op : UInt8) (x y : UInt16) : UInt16 :=
  let bx := x &&& 3
  let yb := y &&& 3
  let zx := msBit x MSB_Z
  let zy := msBit y MSB_Z
  let ox := msBit x MSB_O
  let oy := msBit y MSB_O
  let nx := msBit x MSB_N
  let ny := msBit y MSB_N
  let dx := msBit x MSB_D
  let dy := msBit y MSB_D
  let ux := msBit x MSB_U
  let uy := msBit y MSB_U
  let sx := msBit x MSB_S
  let sy := msBit y MSB_S
  let fx := msBit x MSB_F
  let fy := msBit y MSB_F
  let ex := msBit x MSB_E
  let ey := msBit y MSB_E
  let mx := msBit x MSB_M
  let my := msBit y MSB_M
  let k := band (msBit x MSB_K) (msBit y MSB_K)
  let kres := band k (bnot (msConflict x y))
  let g := bor (msBit x MSB_G) (msBit y MSB_G)
  let h := bor (msBit x MSB_H) (msBit y MSB_H)
  let ires := bor (msBit x MSB_I) (msBit y MSB_I)
  let jres := bor (msBit x MSB_J) (msBit y MSB_J)
  let zz := band zx zy
  let oSum := bor (band zx oy) (band ox zy)
  let nSum := bor nx (band zx ny)
  let sOr := bor sx sy
  let sAnd := band sx sy
  let mAnd := band mx my
  let xBdu := band (decide (bx = 0)) (band dx ux)
  if decide (op = 0x20) then
    selU16 (band (decide (bx = 1)) (decide (yb ≠ 3)))
      (msPack yb zz oSum nSum false uy sOr (bor sx fy) false mAnd g h ires jres kres) 0xFFFF
  else if decide (op = 0x21) then
    selU16 (band (decide (bx = 0)) (decide (yb = 3)))
      (msPack 0 zz oSum nSum (band dx dy) true sOr
        (bor (band fx fy) (bor (band sx fx) (band sy fy)))
        (band (band ex ey) sAnd) mAnd g h ires jres kres) 0xFFFF
  else if decide (op = 0x22) then
    selU16 (band xBdu (decide (yb = 0)))
      (msPack 0 zz (band ox zy) false true uy sOr false (bor sx fy) (band mAnd ex) g h ires jres kres) 0xFFFF
    else if decide (op = 0x23) then
    selU16 (band (band (decide (bx = 0)) dx) (band (decide (yb = 3)) dy))
      (msPack 0 zz oSum false true true sAnd false (band ex ey)
        (band (band mAnd (band ex ey)) sOr) g h ires jres k) 0xFFFF
  else if decide (op = 0x24) then
    selU16 (band xBdu (decide (yb = 1)))
      (msPack 1 zz (band ox zy) false false false sAnd true false (band (band mAnd ex) sOr) g h ires jres k) 0xFFFF
  else if decide (op = 0x25) then
    selU16 (band xBdu (decide (yb = 0)))
      (msPack 0 zz (band ox zy) false dy uy sAnd fy ey (band (band mAnd ex) sOr) g h ires jres k) 0xFFFF
  else if decide (op = 0x26) then
    selU16 (band (decide (bx ≠ 3)) (decide (bx = yb)))
      (msPack bx false zz false (bor dx dy) (band ux uy) sAnd (band fx fy)
        (bor (band ex fy) (band ey fx)) (band mAnd sOr) g h ires jres k) 0xFFFF
  else 0xFFFF

/-- Apply `andor(x, y, z)` (`0x27`) to packed nodes `x y z` (popped in order `z`, `y`, `x`).
    Returns `0xFFFF` on type error, else the packed result. -/
def msApplyAndor (x y z : UInt16) : UInt16 :=
  let bx := x &&& 3
  let yb := y &&& 3
  let bz := z &&& 3
  let zx := msBit x MSB_Z
  let zy := msBit y MSB_Z
  let zz := msBit z MSB_Z
  let ox := msBit x MSB_O
  let oy := msBit y MSB_O
  let oz := msBit z MSB_O
  let dx := msBit x MSB_D
  let ux := msBit x MSB_U
  let uy := msBit y MSB_U
  let uz := msBit z MSB_U
  let sx := msBit x MSB_S
  let sy := msBit y MSB_S
  let sz := msBit z MSB_S
  let fy := msBit y MSB_F
  let ex := msBit x MSB_E
  let ez := msBit z MSB_E
  let mx := msBit x MSB_M
  let my := msBit y MSB_M
  let mz := msBit z MSB_M
  let kres := band (band (msBit x MSB_K) (band (msBit y MSB_K) (msBit z MSB_K))) (bnot (msConflict x y))
  let ok := band (band (decide (bx = 0)) (band dx ux)) (band (decide (yb = bz)) (decide (yb ≠ 3)))
  let sxy := bor sx sy
  selU16 ok
    (msPack yb (band zx (band zy zz))
      (bor (band zx (band oy oz)) (band ox (band zy zz)))
      false (msBit z MSB_D) (band uy uz)
      (band sz sxy)
      (band (msBit z MSB_F) (bor sx fy))
      (band ez (bor sx fy))
      (band (band mx (band my mz)) (band ex (bor sxy sz)))
      (bor (msBit x MSB_G) (bor (msBit y MSB_G) (msBit z MSB_G)))
      (bor (msBit x MSB_H) (bor (msBit y MSB_H) (msBit z MSB_H)))
      (bor (msBit x MSB_I) (bor (msBit y MSB_I) (msBit z MSB_I)))
      (bor (msBit x MSB_J) (bor (msBit y MSB_J) (msBit z MSB_J)))
      kres) 0xFFFF

/-- `true` when the node-stack depth stored in the postfix state is below `n`. -/
private def msSpLt (st : UInt64) (n : UInt64) : Bool :=
  decide (((st >>> 56) &&& 0x7F) < n)

/-- Packed node-stack depth stored in bits `56..62` of the postfix state. -/
private def msSp (st : UInt64) : UInt32 :=
  ((st >>> 56) &&& 0x7F).toUInt32

/-- Replace bits `56..62` of the postfix state with the new stack depth `sp`. -/
private def msWithSp (st : UInt64) (sp : UInt32) : UInt64 :=
  (st &&& (0x80FFFFFFFFFFFFFF : UInt64)) ||| (sp.toUInt64 <<< 56)

/-- Begin collecting `need` little-endian immediate bytes for opcode `op`. -/
private def msBeginImm (st : UInt64) (op : UInt8) : UInt64 :=
  (st &&& (0xFF00000000000000 : UInt64)) ||| (op.toUInt64 <<< 50)

/-- Store immediate byte `b` at position `byteIdx` (`0..3`) inside bits `0..31`.
    Fixed shifts only (`byteIdx * 8` is a variable shift, which RV32 lowers to `__ashldi3`). -/
private def msStoreImm (st : UInt64) (byteIdx : UInt64) (b : UInt8) : UInt64 :=
  let base := st &&& (0xFFFC7FFFFFFFFFFF : UInt64)
  let bv := b.toUInt64
  let slot0 := (base &&& (0xFFFFFFFFFFFFFF00 : UInt64)) ||| bv
  let slot1 := (base &&& (0xFFFFFFFFFFFF00FF : UInt64)) ||| (bv <<< 8)
  let slot2 := (base &&& (0xFFFFFFFFFF00FFFF : UInt64)) ||| (bv <<< 16)
  let slot3 := (base &&& (0xFFFFFFFF00FFFFFF : UInt64)) ||| (bv <<< 24)
  let stored :=
    selU64 (decide (byteIdx = 0)) slot0
      (selU64 (decide (byteIdx = 1)) slot1
        (selU64 (decide (byteIdx = 2)) slot2 slot3))
  stored ||| ((byteIdx + 1) <<< 47)

/-- Push packed node `node` at the current stack depth and bump the depth. -/
private def msPush (scratch : MutBytes) (st : UInt64) (node : UInt16) : UInt64 :=
  let sp := msSp st
  if decide (64 ≤ sp) then (1 : UInt64) <<< 63
  else
    let _w := msWrite scratch sp node
    msWithSp st (sp + 1)

/-- Overwrite the node at depth `sp - 1` (stack depth unchanged). -/
private def msReplaceTop (scratch : MutBytes) (st : UInt64) (node : UInt16) : UInt64 :=
  let sp := msSp st
  let _w := msWrite scratch (sp - 1) node
  st

/-- Fold one `thresh(k, ...)` child `v` (at index `idx`) into packed 64-bit accumulator `acc`.
    `acc` bits: `0..6` z, `7..13` o, `14..20` notS, `21..27` e, `28..34` m,
    `35` g, `36` h, `37` i, `38` j, `39` badK, `40` badType. -/
def msThreshStepVal (k : UInt32) (idx : UInt32) (v : UInt16) (acc : UInt64) : UInt64 :=
  if decide ((acc >>> 40) &&& 1 ≠ 0) then acc
  else
    let expectedBase : UInt16 := selU16 (decide (idx = 0)) 0 3
    let ok := band (decide ((v &&& 3) = expectedBase)) (band (msBit v MSB_D) (msBit v MSB_U))
    if bnot ok then acc ||| ((1 : UInt64) <<< 40)
    else
      let zc := ((acc >>> 0) &&& 0x7F) + (msBit v MSB_Z).toUInt64
      let oc := ((acc >>> 7) &&& 0x7F) + (msBit v MSB_O).toUInt64
      let nc := ((acc >>> 14) &&& 0x7F) + (bnot (msBit v MSB_S)).toUInt64
      let ec := ((acc >>> 21) &&& 0x7F) + (msBit v MSB_E).toUInt64
      let mc := ((acc >>> 28) &&& 0x7F) + (msBit v MSB_M).toUInt64
      let vg := msBit v MSB_G
      let vh := msBit v MSB_H
      let vi := msBit v MSB_I
      let vj := msBit v MSB_J
      let seenG := decide ((acc >>> 35) &&& 1 = 1)
      let seenH := decide ((acc >>> 36) &&& 1 = 1)
      let seenI := decide ((acc >>> 37) &&& 1 = 1)
      let seenJ := decide ((acc >>> 38) &&& 1 = 1)
      let mix := band (decide (2 ≤ k))
        (bor (bor (band vg seenH) (band vh seenG)) (bor (band vi seenJ) (band vj seenI)))
      let g := (bor vg seenG).toUInt64
      let h := (bor vh seenH).toUInt64
      let i := (bor vi seenI).toUInt64
      let j := (bor vj seenJ).toUInt64
      let badK := (bor (bnot (msBit v MSB_K)) (bor mix (decide ((acc >>> 39) &&& 1 = 1)))).toUInt64
      zc ||| (oc <<< 7) ||| (nc <<< 14) ||| (ec <<< 21) ||| (mc <<< 28) |||
        (g <<< 35) ||| (h <<< 36) ||| (i <<< 37) ||| (j <<< 38) ||| (badK <<< 39)

/-- One child of `thresh`: read `scratch[base + idx]` and fold into `acc`. -/
private def msThreshChild (scratch : MutBytes) (base : UInt32) (k : UInt32) (idx : UInt32) (acc : UInt64) : UInt64 :=
  if decide ((acc >>> 40) &&& 1 ≠ 0) then acc
  else msThreshStepVal k idx (msRead scratch (base + idx)) acc

/-- Packed `thresh(k, n)` result (`0xFFFF` on a type error). -/
def msThreshPack (acc : UInt64) (k n : UInt32) : UInt16 :=
  if decide ((acc >>> 40) &&& 1 ≠ 0) then 0xFFFF
  else
    let zc := ((acc >>> 0) &&& 0x7F).toUInt32
    let oc := ((acc >>> 7) &&& 0x7F).toUInt32
    let nc := ((acc >>> 14) &&& 0x7F).toUInt32
    let ec := ((acc >>> 21) &&& 0x7F).toUInt32
    let mc := ((acc >>> 28) &&& 0x7F).toUInt32
    msPack 0 (decide (zc = n)) (band (decide (zc = n - 1)) (decide (oc = 1))) false true true
      (decide (nc ≤ k - 1)) false (band (decide (ec = n)) (decide (nc = 0)))
      (band (band (decide (ec = n)) (decide (mc = n))) (decide (nc ≤ k)))
      (decide ((acc >>> 35) &&& 1 = 1)) (decide ((acc >>> 36) &&& 1 = 1))
      (decide ((acc >>> 37) &&& 1 = 1)) (decide ((acc >>> 38) &&& 1 = 1))
      (decide ((acc >>> 39) &&& 1 = 0))

/-- Finish a 4-byte immediate (`older`, `after`, `multi`, `multi_a`, `thresh`). -/
private def msFinishImm (scratch : MutBytes) (st : UInt64) (isTapscript : UInt8) : UInt64 :=
  let op := ((st >>> 50) &&& 0x3F).toUInt32
  let imm := st &&& 0xFFFFFFFF
  let k16 := (imm &&& 0xFFFF).toUInt32
  let n16 := ((imm >>> 16) &&& 0xFFFF).toUInt32
  let cleared := st &&& (0xFF00000000000000 : UInt64)
  if bor (decide (op = 6)) (decide (op = 7)) then
    let isOlder := decide (op = 6)
    let ok := selU16 isOlder (llbMiniscriptOlderOk imm.toUInt32).toUInt16 (llbMiniscriptAfterOk imm.toUInt32).toUInt16
    if decide (ok = 0) then (1 : UInt64) <<< 63
    else
      let time := selU16 isOlder (decide ((imm &&& 0x00400000) ≠ 0)).toUInt16 (decide (500000000 ≤ imm)).toUInt16
      let tBool := decide (time ≠ 0)
      let ntBool := decide (time = 0)
      let node := selU16 isOlder
        (msPack 0 true false false false false false true false true tBool ntBool false false true)
        (msPack 0 true false false false false false true false true false false tBool ntBool true)
      msPush scratch cleared node
  else if bor (decide (op = 0x0C)) (decide (op = 0x0D)) then
    let tapscript := decide (isTapscript ≠ 0)
    let isMulti := decide (op = 0x0C)
    let ctxOk := decide (isMulti != tapscript)
    let nMax : UInt32 := selU32 isMulti 20 999
    let ok := band (band ctxOk (decide (1 ≤ k16))) (band (decide (k16 ≤ n16)) (decide (n16 ≤ nMax)))
    if bnot ok then (1 : UInt64) <<< 63
    else msPush scratch cleared (msPack 0 false false isMulti true true true false true true false false false false true)
  else
    let sp := msSp st
    let ok := band (band (decide (1 ≤ k16)) (decide (k16 ≤ n16))) (band (decide (n16 ≤ sp)) (decide (n16 ≤ 64)))
    if bnot ok then (1 : UInt64) <<< 63
    else
      let base := sp - n16
      let acc := forRangeU64 0 n16 0 (fun idx a => msThreshChild scratch base k16 idx a)
      let node := msThreshPack acc k16 n16
      if msErr node then (1 : UInt64) <<< 63
      else
        let _w := msWrite scratch base node
        msWithSp cleared (base + 1)

/-- One opcode of the postfix Miniscript program. -/
private def msStep (scratch : MutBytes) (isTapscript : UInt8) (ops : ConstBytes) (pos : UInt32) (st : UInt64) : UInt64 :=
  if decide (st >>> 63 ≠ 0) then st
  else
    let b := readU8 ops pos
    let pend := (st >>> 50) &&& 0x3F
    let got := (st >>> 47) &&& 7
    if decide (pend ≠ 0) then
      let st' := msStoreImm st got b
      if decide (got + 1 ≥ 4) then msFinishImm scratch st' isTapscript else st'
    else if decide (b = 0x00) then msPush scratch st (msLeafB true false false true true true false true true)
    else if decide (b = 0x01) then msPush scratch st (msLeafB true false false false true false true false true)
    else if decide (b = 0x02) then msPush scratch st (msPack 2 false true true true true true false true true false false false false true)
    else if decide (b = 0x03) then msPush scratch st (msPack 2 false false true true true true false true true false false false false true)
    else if decide (b = 0x04) then msPush scratch st (msPack 0 false true true true true true false true true false false false false true)
    else if decide (b = 0x05) then msPush scratch st (msPack 0 false false true true true true false true true false false false false true)
    else if band (decide (0x08 ≤ b)) (decide (b ≤ 0x0B)) then
      msPush scratch st (msLeafB false true true true true false false false true)
    else if bor (bor (decide (b = 0x06)) (decide (b = 0x07))) (bor (bor (decide (b = 0x0C)) (decide (b = 0x0D))) (decide (b = 0x28))) then
      msBeginImm st b
    else if band (decide (0x10 ≤ b)) (decide (b ≤ 0x19)) then
      if msSpLt st 1 then (1 : UInt64) <<< 63
      else
        let r := msApplyUnary b isTapscript (msRead scratch (msSp st - 1))
        if msErr r then (1 : UInt64) <<< 63 else msReplaceTop scratch st r
    else if band (decide (0x20 ≤ b)) (decide (b ≤ 0x26)) then
      if msSpLt st 2 then (1 : UInt64) <<< 63
      else
        let sp := msSp st
        let r := msApplyBinary b (msRead scratch (sp - 2)) (msRead scratch (sp - 1))
        if msErr r then (1 : UInt64) <<< 63
        else
          let _w := msWrite scratch (sp - 2) r
          msWithSp st (sp - 1)
    else if decide (b = 0x27) then
      if msSpLt st 3 then (1 : UInt64) <<< 63
      else
        let sp := msSp st
        let r := msApplyAndor (msRead scratch (sp - 3)) (msRead scratch (sp - 2)) (msRead scratch (sp - 1))
        if msErr r then (1 : UInt64) <<< 63
        else
          let _w := msWrite scratch (sp - 3) r
          msWithSp st (sp - 2)
    else (1 : UInt64) <<< 63

/-- Full postfix BIP-379 / BIP-388 Miniscript typechecker over `ops[0..opsLen)` using
    caller-supplied `scratch` (128 bytes = 64 × 2). Returns `1` iff the program is a valid
    non-malleable (per `requireFlags`), signature-safe (per `requireFlags`), timelock-safe
    `B`-rooted Miniscript. -/
@[export llb_miniscript_check_postfix]
def llbMiniscriptCheckPostfix (ops : ConstBytes) (opsLen : UInt32) (isTapscript : UInt8) (requireFlags : UInt8) (scratch : MutBytes) : Bool :=
  if bor (decide (opsLen = 0)) (decide (512 < opsLen)) then false
  else
    let step := fun pos st => msStep scratch isTapscript ops pos st
    let st := forRangeU64 0 opsLen 0 step
    let doneOk := band (decide (st >>> 63 = 0)) (band (decide (msSp st = 1)) (decide (((st >>> 50) &&& 0x3F) = 0)))
    if bnot doneOk then false
    else
      let top := msRead scratch 0
      let reqM := bor (decide ((requireFlags &&& 1) = 0)) (msBit top MSB_M)
      let reqS := bor (decide ((requireFlags &&& 2) = 0)) (msBit top MSB_S)
      band (band (decide ((top &&& 3) = 0)) (msBit top MSB_K)) (band reqM reqS)

/-! ## 10. BIP-370 PSBTv2 Locktime State Machine (VND-04)

State in one `UInt64` (`0` = invalid):
- bit `63` valid
- bits `61..62` mode: `0` none, `1` both, `2` height-only, `3` time-only
- mode `1`: bits `32..60` = `maxHeight` (`< 2^29`), bits `0..31` = `maxTime`
- mode `2`: bits `0..31` = `maxHeight`; mode `3`: bits `0..31` = `maxTime`. -/

/-- Initial BIP-370 state: valid, no input has constrained locktime yet. -/
@[export llb_psbt_locktime_init]
def llbPsbtLocktimeInit : UInt64 :=
  (1 : UInt64) <<< 63

def ltMode (st : UInt64) : UInt64 :=
  (st >>> 61) &&& 3

def ltMaxH (st : UInt64) : UInt32 :=
  selU32 (decide (ltMode st = 1)) ((st >>> 32) &&& 0x1FFFFFFF).toUInt32 st.toUInt32

def ltMaxT (st : UInt64) : UInt32 :=
  st.toUInt32

def ltPack (mode : UInt64) (h t : UInt32) : UInt64 :=
  let b63 := (1 : UInt64) <<< 63
  let m0 := b63
  let m1 := b63 ||| ((1 : UInt64) <<< 61) ||| (h.toUInt64 <<< 32) ||| t.toUInt64
  let m2 := b63 ||| ((2 : UInt64) <<< 61) ||| h.toUInt64
  let m3 := b63 ||| ((3 : UInt64) <<< 61) ||| t.toUInt64
  selU64 (decide (mode = 0)) m0 (selU64 (decide (mode = 1)) m1 (selU64 (decide (mode = 2)) m2 m3))

def u32Max (a b : UInt32) : UInt32 :=
  selU32 (decide (a < b)) b a

/-- Fold one input's `(hasH, h, hasT, t)` into the BIP-370 state. `0` on a bound or conflict error. -/
@[export llb_psbt_locktime_step]
def llbPsbtLocktimeStep (st : UInt64) (hasH : UInt8) (h : UInt32) (hasT : UInt8) (t : UInt32) : UInt64 :=
  let hOn := decide (hasH ≠ 0)
  let tOn := decide (hasT ≠ 0)
  let hOk := bor (bnot hOn) (band (decide (1 ≤ h)) (decide (h < 500000000)))
  let tOk := bor (bnot tOn) (decide (500000000 ≤ t))
  let validIn := band (decide (st ≠ 0)) (band hOk tOk)
  let mode := ltMode st
  let maxH := u32Max (ltMaxH st) h
  let maxT := u32Max (ltMaxT st) t
  let resBoth :=
    selU64 (decide (mode = 0)) (ltPack 1 h t)
      (selU64 (decide (mode = 1)) (ltPack 1 maxH maxT)
        (selU64 (decide (mode = 2)) (ltPack 2 maxH 0) (ltPack 3 0 maxT)))
  let resH :=
    selU64 (decide (mode = 0)) (ltPack 2 h 0)
      (selU64 (bor (decide (mode = 1)) (decide (mode = 2))) (ltPack 2 maxH 0) 0)
  let resT :=
    selU64 (decide (mode = 0)) (ltPack 3 0 t)
      (selU64 (bor (decide (mode = 1)) (decide (mode = 3))) (ltPack 3 0 maxT) 0)
  let next :=
    selU64 (band (bnot hOn) (bnot tOn)) st
      (selU64 (band hOn tOn) resBoth (selU64 hOn resH resT))
  selU64 validIn next 0

/-- Resolve a finished BIP-370 state to `(1 <<< 32) ||| locktime`, or `0` when invalid. -/
@[export llb_psbt_locktime_finalize]
def llbPsbtLocktimeFinalize (st : UInt64) (fallbackLocktime : UInt32) : UInt64 :=
  let mode := ltMode st
  let chosen :=
    selU32 (decide (mode = 0)) fallbackLocktime
      (selU32 (bor (decide (mode = 1)) (decide (mode = 2))) (ltMaxH st) (ltMaxT st))
  selU64 (decide (st ≠ 0)) (((1 : UInt64) <<< 32) ||| chosen.toUInt64) 0

/-- One 10-byte locktime record: `hasH`, `h` LE, `hasT`, `t` LE. -/
def ltRecord (buf : ConstBytes) (i : UInt32) (st : UInt64) : UInt64 :=
  let base := i * 10
  let h := (readU8 buf (base + 1)).toUInt32 ||| ((readU8 buf (base + 2)).toUInt32 <<< 8) |||
    ((readU8 buf (base + 3)).toUInt32 <<< 16) ||| ((readU8 buf (base + 4)).toUInt32 <<< 24)
  let t := (readU8 buf (base + 6)).toUInt32 ||| ((readU8 buf (base + 7)).toUInt32 <<< 8) |||
    ((readU8 buf (base + 8)).toUInt32 <<< 16) ||| ((readU8 buf (base + 9)).toUInt32 <<< 24)
  llbPsbtLocktimeStep st (readU8 buf base) h (readU8 buf (base + 5)) t

/-- Scan `numInputs` contiguous 10-byte records and finalize the BIP-370 locktime. -/
@[export llb_psbt_determine_locktime]
def llbPsbtDetermineLocktime (buf : ConstBytes) (numInputs : UInt32) (fallbackLocktime : UInt32) : UInt64 :=
  let step := fun i st => ltRecord buf i st
  llbPsbtLocktimeFinalize (forRangeU64 0 numInputs llbPsbtLocktimeInit step) fallbackLocktime

/-! ## 11. Dual-UTXO Equality & Batch Satoshi Accounting (VND-02 / VND-03, CVE-2020-14199) -/

/-- `1` iff `a[i] = b[i]` for every `i < len` (constant iteration count). -/
@[export llb_bytes_eq]
def llbBytesEq (a b : ConstBytes) (len : UInt32) : Bool :=
  let step := fun i acc =>
    if decide (readU8 a i = readU8 b i) then acc else 0
  decide (forRangeU64 0 len 1 step = 1)

/-- Dual-UTXO cross-check: both amounts valid and equal, and both scriptPubKeys equal. -/
@[export llb_check_dual_utxo]
def llbCheckDualUtxo (witAmount : UInt64) (witSpk : ConstBytes) (witSpkLen : UInt32) (nonWitAmount : UInt64) (nonWitSpk : ConstBytes) (nonWitSpkLen : UInt32) : Bool :=
  llbValidAmount witAmount && decide (witAmount = nonWitAmount) && decide (witSpkLen = nonWitSpkLen) &&
    llbBytesEq witSpk nonWitSpk witSpkLen

/-- Read one little-endian `UInt64` at byte `base`. -/
def readU64Le (buf : ConstBytes) (base : UInt32) : UInt64 :=
  (readU8 buf base).toUInt64 ||| ((readU8 buf (base + 1)).toUInt64 <<< 8) |||
    ((readU8 buf (base + 2)).toUInt64 <<< 16) ||| ((readU8 buf (base + 3)).toUInt64 <<< 24) |||
    ((readU8 buf (base + 4)).toUInt64 <<< 32) ||| ((readU8 buf (base + 5)).toUInt64 <<< 40) |||
    ((readU8 buf (base + 6)).toUInt64 <<< 48) ||| ((readU8 buf (base + 7)).toUInt64 <<< 56)

/-- Sum `count` little-endian satoshi amounts. `(1 <<< 63) ||| sum` when every entry and the
    running total stay `≤ MAX_MONEY`; `0` on overflow. -/
@[export llb_sum_amounts_le64]
def llbSumAmountsLe64 (amounts : ConstBytes) (count : UInt32) : UInt64 :=
  let step := fun i (acc : UInt64) =>
    if decide (acc = 0) then (0 : UInt64)
    else
      let v := readU64Le amounts (i * 8)
      if llbCheckedAddSatsOk (acc &&& (0x7FFFFFFFFFFFFFFF : UInt64)) v then
        (((1 : UInt64) <<< 63) ||| ((acc &&& (0x7FFFFFFFFFFFFFFF : UInt64)) + v) : UInt64)
      else (0 : UInt64)
  forRangeU64 0 count ((1 : UInt64) <<< 63) step

/-! ## 12. Full-Buffer BIP-32 Export Path (VND-07) -/

/-- `1` iff every `path[lo..pathLen)` is unhardened. -/
def bip32TailClear (path : ConstU32s) (lo : UInt32) (pathLen : UInt32) : Bool :=
  let step := fun i acc => if llbBip32IsHardened (readU32 path i) then (0 : UInt64) else acc
  decide (forRangeU64 lo pathLen 1 step = 1)

/-- Full export-path gate: BOLOS depth, unhardened tail, and the hardened prefix. -/
@[export llb_bip32_check_export_path]
def llbBip32CheckExportPath (path : ConstU32s) (pathLen : UInt8) (expectedCoinType : UInt32) : Bool :=
  if !llbBip32BolosDepthOk pathLen then false
  else
    let n := pathLen.toUInt32
    let p0 := if decide (0 < n) then readU32 path 0 else 0
    let p1 := if decide (1 < n) then readU32 path 1 else 0
    let p2 := if decide (2 < n) then readU32 path 2 else 0
    let p3 := if decide (3 < n) then readU32 path 3 else 0
    let purpose := llbBip32Unharden p0
    let tailAt := if decide (purpose = 48) && decide (3 ≤ n) then (4 : UInt32) else 3
    llbBip32PubkeyExportPrefixOk p0 p1 p2 p3 pathLen expectedCoinType (bip32TailClear path tailAt n)

/-! ## 13. Checked CompactSize Reader (VND-09) -/

/-- Decode one canonical CompactSize. `(consumed <<< 32) ||| val` or `0`. -/
@[export llb_read_compact_size_checked]
def llbReadCompactSizeChecked (buf : ConstBytes) (bufLen : UInt32) (maxVal : UInt32) : UInt64 :=
  if decide (bufLen = 0) then 0
  else
    let tag := readU8 buf 0
    let need : UInt32 :=
      if decide (tag ≤ 0xFC) then 1
      else if decide (tag = 0xFD) then 3
      else if decide (tag = 0xFE) then 5
      else 9
    if decide (bufLen < need) || decide (tag = 0xFF) then 0
    else
      let raw :=
        if decide (tag ≤ 0xFC) then tag.toUInt64
        else if decide (tag = 0xFD) then (readU8 buf 1).toUInt64 ||| ((readU8 buf 2).toUInt64 <<< 8)
        else (readU8 buf 1).toUInt64 ||| ((readU8 buf 2).toUInt64 <<< 8) |||
          ((readU8 buf 3).toUInt64 <<< 16) ||| ((readU8 buf 4).toUInt64 <<< 24)
      if llbVarIntPrefixIsCanonical tag raw && decide (raw ≤ maxVal.toUInt64) then
        (need.toUInt64 <<< 32) ||| raw
      else 0

/-! ## 14. In-Place Insertion Sorts (BIP-67 / BIP-327 / BIP-388) -/

/-- `0` when record `j` ≤ record `j+1`, else `1`. -/
private def recGreater (buf : MutBytes) (stride j : UInt32) : UInt64 :=
  let step := fun k acc =>
    if decide (acc ≠ 2) then acc
    else
      let x := readMutU8 buf (j * stride + k)
      let y := readMutU8 buf ((j + 1) * stride + k)
      if decide (x < y) then 0 else if decide (y < x) then 1 else 2
  let r := forRangeU64 0 stride 2 step
  if decide (r = 1) then 1 else 0

/-- Swap records `j` and `j+1` of `stride` bytes in place. -/
private def recSwap (buf : MutBytes) (stride j : UInt32) : Unit :=
  forRangeUnit 0 stride (fun k =>
    let a := j * stride + k
    let b := (j + 1) * stride + k
    let x := readMutU8 buf a
    let y := readMutU8 buf b
    let _ := writeU8 buf a y
    let _ := writeU8 buf b x
    ())

/-- Bubble slot `slot` left by one insertion pass. -/
private def sortBytesPass (buf : MutBytes) (stride slot : UInt32) : Unit :=
  forRangeUnit 0 slot (fun k =>
    let j := slot - 1 - k
    if decide (recGreater buf stride j = 1) then recSwap buf stride j else ())

/-- In-place lexicographic insertion sort of `count` records of `stride` bytes. -/
@[export llb_sort_fixed_bytes]
def llbSortFixedBytes (buf : MutBytes) (count stride : UInt32) : Unit :=
  if decide (count ≤ 1) || decide (stride = 0) then ()
  else forRangeUnit 1 count (fun slot => sortBytesPass buf stride slot)

/-- One insertion pass over `UInt16` elements up to `slot`. -/
private def sortU16Pass (arr : MutU16s) (slot : UInt32) : Unit :=
  forRangeUnit 0 slot (fun k =>
    let j := slot - 1 - k
    let x := readMutU16 arr j
    let y := readMutU16 arr (j + 1)
    if decide (y < x) then
      let _ := writeU16 arr j y
      let _ := writeU16 arr (j + 1) x
      ()
    else ())

/-- In-place insertion sort of `count` `UInt16` values. -/
@[export llb_sort_u16]
def llbSortU16 (arr : MutU16s) (count : UInt32) : Unit :=
  if decide (count ≤ 1) then ()
  else forRangeUnit 1 count (fun slot => sortU16Pass arr slot)

/-! ## 15. Division-Free ASCII Satoshi Formatter -/

/-- Exact `v / 10` for every `v : UInt32` via reciprocal `0xCCCCCCCD >>> 35`. -/
def div10U32 (v : UInt32) : UInt32 :=
  ((v.toUInt64 * 0xCCCCCCCD) >>> 35).toUInt32

/-- Exact `v % 10` for every `v : UInt32`. -/
def mod10U32 (v : UInt32) : UInt32 :=
  v - div10U32 v * 10

/-- Decimal length of a `UInt32` (`1` for `0`). -/
def decLenU32 (v : UInt32) : UInt32 :=
  let step := fun (_k : UInt32) (acc : UInt64) =>
    let cur := acc.toUInt32
    let n := (acc >>> 32).toUInt32
    if decide (cur = 0) then acc
    else ((n + 1).toUInt64 <<< 32) ||| (div10U32 cur).toUInt64
  let r := forRangeU64 0 10 (v.toUInt64) step
  let n := (r >>> 32).toUInt32
  if decide (n = 0) then 1 else n

/-- Write the `len` decimal digits of `v` ending at `pos - 1`. -/
private def emitDec (out : MutBytes) (pos v len : UInt32) : Unit :=
  let step := fun k (cur : UInt32) =>
    let atPos := pos - 1 - k
    let d := mod10U32 cur
    let _ := writeU8 out atPos (0x30 + d.toUInt8)
    div10U32 cur
  let _ := forRangeU32 0 len v step
  ()

/-- Significant fractional digits (`0` when `frac = 0`). -/
def fracSigLen (frac : UInt32) : UInt32 :=
  let step := fun (_k : UInt32) (acc : UInt64) =>
    let cur := acc.toUInt32
    let n := (acc >>> 32).toUInt32
    let stop := bor (decide (cur = 0)) (decide (mod10U32 cur ≠ 0))
    selU64 stop acc (((n + 1).toUInt64 <<< 32) ||| (div10U32 cur).toUInt64)
  let r := forRangeU64 0 8 (frac.toUInt64) step
  selU32 (decide (frac = 0)) 0 ((8 : UInt32) - (r >>> 32).toUInt32)

/-- Copy `ticker[0..tickerLen)` to `out[pos..]`. -/
private def copyTicker (ticker : ConstBytes) (tickerLen : UInt32) (out : MutBytes) (pos : UInt32) : Unit :=
  forRangeUnit 0 tickerLen (fun k =>
    let _ := writeU8 out (pos + k) (readU8 ticker k)
    ())

private def maybeWriteByte (cond : Bool) (out : MutBytes) (pos : UInt32) (val : UInt8) : Unit :=
  if cond then
    let _ := writeU8 out pos val
    ()
  else ()

/-- Format `amount` satoshis plus an optional ticker. `padFrac8 ≠ 0` keeps all 8 fractional
    digits; `padFrac8 = 0` strips a trailing `.` and trailing fractional zeros. Returns the
    number of bytes written excluding the terminating NUL, or `0` when `outCap` is too small. -/
@[export llb_format_sats_ascii]
def llbFormatSatsAscii (amount : UInt64) (ticker : ConstBytes) (tickerLen : UInt32) (padFrac8 : UInt8) (out : MutBytes) (outCap : UInt32) : UInt32 :=
  if decide (256 < tickerLen) then 0
  else
    let q := llbSatsDiv1e8 amount
    let frac := llbSatsMod1e8 amount
    let qHi := (llbSatsDiv1e8 q).toUInt32
    let qLo := llbSatsMod1e8 q
    let hiZero := decide (qHi = 0)
    let hiLen := selU32 hiZero 0 (decLenU32 qHi)
    let loLen := selU32 hiZero (decLenU32 qLo) 8
    let intLen := hiLen + loLen
    let pad := decide (padFrac8 ≠ 0)
    let showFrac := bor pad (decide (frac ≠ 0))
    let fracLen := selU32 pad 8 (fracSigLen frac)
    let dotLen : UInt32 := showFrac.toUInt32
    let hasTicker := decide (tickerLen ≠ 0)
    let spaceLen : UInt32 := hasTicker.toUInt32
    let total := intLen + dotLen + fracLen + spaceLen + tickerLen
    if decide (outCap ≤ total) then 0
    else
      let _ := emitDec out hiLen qHi hiLen
      let _ := emitDec out (hiLen + loLen) qLo loLen
      let _ := maybeWriteByte showFrac out intLen 0x2E
      let drop := selU32 pad 0 (8 - fracLen)
      let fracShown := forRangeU32 0 drop frac (fun _ cur => div10U32 cur)
      let emitFracLen := selU32 showFrac fracLen 0
      let _ := emitDec out (intLen + 1 + emitFracLen) fracShown emitFracLen
      let _ := maybeWriteByte hasTicker out (intLen + dotLen + fracLen) 0x20
      let _ := copyTicker ticker tickerLen out (intLen + dotLen + fracLen + spaceLen)
      let _ := writeU8 out total 0
      total

#guard llbPsbtLocktimeInit == ((1 : UInt64) <<< 63)
#guard llbPsbtLocktimeStep llbPsbtLocktimeInit 1 0 0 0 == 0
#guard llbPsbtLocktimeStep llbPsbtLocktimeInit 0 0 1 1 == 0
#guard llbMiniscriptOlderOk 0 == false
#guard llbMiniscriptOlderOk 1 == true
#guard llbMiniscriptAfterOk 0 == false
#guard llbMiniscriptAfterOk 1 == true
#guard llbMiniscriptAndorBranchesValid 0x64 0x67 0x68 == true
#guard llbMiniscriptAndorBranchesValid 0x63 0x67 0x68 == false
#guard div10U32 0 == 0
#guard div10U32 9 == 0
#guard div10U32 10 == 1
#guard div10U32 4294967295 == 429496729
#guard mod10U32 4294967295 == 5
#guard decLenU32 0 == 1
#guard decLenU32 1844 == 4

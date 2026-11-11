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
  match errTag with
  | 0  => 0x6700 -- wrongLength -> SW_WRONG_LENGTH
  | 1  => 0x6A87 -- wrongDataLength -> SW_WRONG_DATA_LENGTH
  | 2  => 0x6D00 -- unsupportedInstruction -> SW_INS_NOT_SUPPORTED
  | 3  => 0x6E00 -- unsupportedClass -> SW_CLA_NOT_SUPPORTED
  | 4  => 0x6A86 -- wrongP1P2 -> SW_WRONG_P1P2
  | 5  => 0x6985 -- userRejected -> SW_DENY
  | 6  => 0x6982 -- securityStatusNotSatisfied -> SW_SECURITY_STATUS_NOT_SATISFIED
  | 7  => 0x6B00 -- swapValidationFailed -> SW_FAIL_SWAP
  | 8  => 0x6A80 -- invalidData -> SW_INCORRECT_DATA
  | 9  => 0x6A80 -- bip32PathTooLong -> SW_INCORRECT_DATA
  | 10 => 0x6A82 -- unsupportedBip32Path -> SW_NOT_SUPPORTED
  | 11 => 0x6A82 -- notSupported -> SW_NOT_SUPPORTED
  | 12 => 0x6A80 -- invalidAmount -> SW_INCORRECT_DATA
  | 13 => 0x6A80 -- invalidScriptOrAddress -> SW_INCORRECT_DATA
  | 14 => 0x6A80 -- invalidWalletPolicy -> SW_INCORRECT_DATA
  | 15 => 0x6A80 -- invalidPsbt -> SW_INCORRECT_DATA
  | 16 => 0xB007 -- badState -> SW_BAD_STATE
  | 17 => 0xB000 -- wrongResponseLength -> SW_WRONG_RESPONSE_LENGTH
  | 18 => 0xB008 -- cryptoOrSignatureFailed -> SW_SIGNATURE_FAIL
  | _  => 0xB007 -- fallback -> SW_BAD_STATE

end BitcoinLedger.FreestandingKernels

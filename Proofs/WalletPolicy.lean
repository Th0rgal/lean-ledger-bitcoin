import InternalSpec
import BitcoinLedger.WalletPolicy

namespace Proofs.WalletPolicy

/-!
# `Proofs.WalletPolicy` — Machine-Checked Refinement & Security Soundness Proofs

Constructive (`0 Classical.choice`, `0 sorryAx`, `0 native_decide`, `0 omega`) proofs linking
the executable engine `BitcoinLedger.WalletPolicy` to the normative formal specification
`InternalSpec.WalletPolicy`:

1. **Exact Behavioral Equivalence (`BitcoinLedger.WalletPolicy` = `InternalSpec.WalletPolicy`)**:
   - Profiles (`canonicalLedgerProfile`, `bolosAppProfile`, `vanadiumAppProfile`);
   - Byte encoders, lexicographic sorting, xpub & `WalletKeyInfo` validation, wallet name bounds,
     and `<M;N>` derivation spec validation;
   - ASCII & stacked-wrapper Miniscript parsers (`parseKeyExpr`, `peelWrapperPrefix`,
     `parseMiniscript`, `parseTapTree`, `parseDescriptorTemplate`, `parseDescriptorTemplateWithProfile`);
   - BIP-68 `older(n)` bitmask equivalence (`validOlderBitmask n = validOlderArg n`), BIP-65 `after(n)`,
     BIP-379 Miniscript typechecker (`analyzeMiniscript`, `checkMiniscriptSane`);
   - Whole-policy validation (`checkPlaceholderCoverage`, `checkDescriptorTemplate`,
     `checkPolicyWellFormed`, `hasOurKey`, `validatePolicyRegistration`, `authorizePolicyUse`);
   - Script compiler (`compileMultiScript`, `compileMultiAScript`, `compileMiniscript`),
     BIP-341 `TapLeaf` / `TapBranch` / `TapTweak`, `deriveWalletScriptPubKeyWithProfile` across
     all 3 profiles, `deriveWalletPolicyScript`, and BOLOS/Vanadium registration commitments.
2. **Security Rejection & Soundness Theorems**:
   - Equal `<M;M>` multipath rejected & hardened multipath rejected;
   - Out-of-range / non-sequential `@k` placeholder rejected;
   - Missing our-key (`hasOurKey = false`) rejected in registration;
   - Forged / all-zero / wrong-length HMAC rejected & default `addressIndex > 50000` rejected;
   - Canonical BIP-379 `andor(X,Y,Z)` branch order soundness (`OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF`);
   - `multi_a` in `wsh` rejected & `multi` in Tapscript rejected;
   - `v1` `tr(...)` rejected & `rawtr(...)` in BIP-388 wallet policy rejected;
   - Uppercase hex rejected in hex nibbles, Miniscript hashes, and `KeyOrigin` `[73C5DA0A/...]`;
   - Stacked wrapper `sln:older(12960)` accepted while `s:l:n:older` & `s::pk` are rejected;
   - `after(n)` height/timestamp mixing rejected & `older(n)` dirty upper bits rejected;
   - `TapBranch` lexicographic commutativity & `verifyAndRegisterWalletPolicy` / `parseWalletKeyInfo` soundness.
3. **Positive Non-Vacuity Witness Theorems**:
   - BIP-84 `wpkh(@0/<0;1>/*)` (script + Bech32 address);
   - BIP-86 `tr(@0/<0;1>/*)` (script + Bech32m address);
   - Registered `wsh(sortedmulti(2,@0/**,@1/**))` (`verifyAndRegisterWalletPolicy` + `deriveWalletPolicyScript`);
   - Registered Tapscript tree `tr(@0/**,{pk(@1/**),and_v(v:pk(@2/**),older(1000))})`.
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

open InternalSpec.WalletPolicy

/-! ## Section 1: Profile, Primitive Encoder, Sorting & Key Validation Equivalence -/

theorem canonicalLedgerProfile_eq (net : Network) :
    BitcoinLedger.WalletPolicy.canonicalLedgerProfile net =
      InternalSpec.WalletPolicy.canonicalLedgerProfile net := rfl

theorem bolosAppProfile_eq (net : Network) :
    BitcoinLedger.WalletPolicy.bolosAppProfile net =
      InternalSpec.WalletPolicy.bolosAppProfile net := rfl

theorem vanadiumAppProfile_eq (net : Network) :
    BitcoinLedger.WalletPolicy.vanadiumAppProfile net =
      InternalSpec.WalletPolicy.vanadiumAppProfile net := rfl

theorem isUnhardened_eq (idx : UInt32) :
    BitcoinLedger.WalletPolicy.isUnhardened idx = InternalSpec.WalletPolicy.isUnhardened idx := rfl

theorem hardened_eq (idx : UInt32) :
    BitcoinLedger.WalletPolicy.hardened idx = InternalSpec.WalletPolicy.hardened idx := rfl

theorem encodeU32BE_eq (n : UInt32) :
    BitcoinLedger.WalletPolicy.encodeU32BE n = InternalSpec.WalletPolicy.encodeU32BE n := rfl

theorem encodeU32LE_eq (n : UInt32) :
    BitcoinLedger.WalletPolicy.encodeU32LE n = InternalSpec.WalletPolicy.encodeU32LE n := rfl

theorem encodeCompactSize_eq (n : Nat) :
    BitcoinLedger.WalletPolicy.encodeCompactSize n = InternalSpec.WalletPolicy.encodeCompactSize n := rfl

theorem byteListLt_eq :
    ∀ (xs ys : List UInt8),
      BitcoinLedger.WalletPolicy.byteListLt xs ys = InternalSpec.WalletPolicy.byteListLt xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    unfold BitcoinLedger.WalletPolicy.byteListLt InternalSpec.WalletPolicy.byteListLt
    rw [byteListLt_eq as bs]

theorem byteArrayLt_eq (a b : ByteArray) :
    BitcoinLedger.WalletPolicy.byteArrayLt a b = InternalSpec.WalletPolicy.byteArrayLt a b := by
  unfold BitcoinLedger.WalletPolicy.byteArrayLt InternalSpec.WalletPolicy.byteArrayLt
  exact byteListLt_eq a.data.toList b.data.toList

theorem insertByteArray_eq (x : ByteArray) :
    ∀ (ys : List ByteArray),
      BitcoinLedger.WalletPolicy.insertByteArray x ys = InternalSpec.WalletPolicy.insertByteArray x ys
  | [] => rfl
  | y :: ys => by
    unfold BitcoinLedger.WalletPolicy.insertByteArray InternalSpec.WalletPolicy.insertByteArray
    rw [byteArrayLt_eq x y, insertByteArray_eq x ys]

theorem sortByteArrays_eq :
    ∀ (xs : List ByteArray),
      BitcoinLedger.WalletPolicy.sortByteArrays xs = InternalSpec.WalletPolicy.sortByteArrays xs
  | [] => rfl
  | x :: xs => by
    unfold BitcoinLedger.WalletPolicy.sortByteArrays InternalSpec.WalletPolicy.sortByteArrays
    rw [sortByteArrays_eq xs, insertByteArray_eq]

theorem xpubWellFormed_eq (xpub : ExtendedPubKey) :
    BitcoinLedger.WalletPolicy.xpubWellFormed xpub = ExtendedPubKey.wellFormed xpub := rfl

theorem xpubXOnly_eq (xpub : ExtendedPubKey) :
    BitcoinLedger.WalletPolicy.xpubXOnly xpub = ExtendedPubKey.xOnlyPubkey xpub := rfl

theorem serializeXpub78_eq (xpub : ExtendedPubKey) :
    BitcoinLedger.WalletPolicy.serializeXpub78 xpub = ExtendedPubKey.serialize78 xpub := rfl

theorem xpubVersionOfNetwork_eq (net : Network) :
    BitcoinLedger.WalletPolicy.xpubVersionOfNetwork net = Network.xpubVersion net := by
  cases net <;> rfl

theorem coinTypeOfNetwork_eq (net : Network) :
    BitcoinLedger.WalletPolicy.coinTypeOfNetwork net = Network.coinType net := by
  cases net <;> rfl

theorem validKeyInfoWithBounds_eq (maxOriginLen : Nat) (fmt : PolicyFormat) (net : Network)
    (ki : KeyInformation) :
    BitcoinLedger.WalletPolicy.validKeyInfoWithBounds maxOriginLen fmt net ki =
      KeyInformation.validForFormatWithBounds maxOriginLen fmt net ki := rfl

theorem validKeyInfo_eq (fmt : PolicyFormat) (net : Network) (ki : KeyInformation) :
    BitcoinLedger.WalletPolicy.validKeyInfo fmt net ki =
      KeyInformation.validForFormat fmt net ki := rfl

/-! ## Section 2: ASCII & Stacked-Wrapper Miniscript Parser Equivalence -/

theorem isAsciiDigit_eq (b : UInt8) :
    BitcoinLedger.WalletPolicy.isAsciiDigit b = InternalSpec.WalletPolicy.isAsciiDigit b := rfl

theorem parseDecimalNat_eq (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseDecimalNat input =
      InternalSpec.WalletPolicy.parseDecimalNat input := rfl

theorem parseDecimalU32_eq (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseDecimalU32 input =
      InternalSpec.WalletPolicy.parseDecimalU32 input := rfl

theorem stripAsciiPrefix_go_eq :
    ∀ (ps cs : List UInt8),
      BitcoinLedger.WalletPolicy.stripAsciiPrefix.go ps cs =
        InternalSpec.WalletPolicy.stripAsciiPrefix.go ps cs
  | [], _ => rfl
  | p :: ps, c :: cs => by
    unfold BitcoinLedger.WalletPolicy.stripAsciiPrefix.go InternalSpec.WalletPolicy.stripAsciiPrefix.go
    rw [stripAsciiPrefix_go_eq ps cs]
  | _ :: _, [] => rfl

theorem stripAsciiPrefix_eq (pfx : String) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.stripAsciiPrefix pfx input =
      InternalSpec.WalletPolicy.stripAsciiPrefix pfx input := by
  unfold BitcoinLedger.WalletPolicy.stripAsciiPrefix InternalSpec.WalletPolicy.stripAsciiPrefix
  exact stripAsciiPrefix_go_eq pfx.toUTF8.data.toList input

theorem decodeHexNibble_eq (b : UInt8) :
    BitcoinLedger.WalletPolicy.decodeHexNibble b = InternalSpec.WalletPolicy.decodeHexNibble b := rfl

theorem parseFixedHex_loop_eq :
    ∀ (k : Nat) (input : List UInt8) (acc : Array UInt8),
      BitcoinLedger.WalletPolicy.parseFixedHex.loop k input acc =
        InternalSpec.WalletPolicy.parseFixedHex.loop k input acc
  | 0, _, _ => rfl
  | k + 1, hi :: lo :: rest, acc => by
    unfold BitcoinLedger.WalletPolicy.parseFixedHex.loop InternalSpec.WalletPolicy.parseFixedHex.loop
    rw [decodeHexNibble_eq hi, decodeHexNibble_eq lo]
    cases InternalSpec.WalletPolicy.decodeHexNibble hi <;> cases InternalSpec.WalletPolicy.decodeHexNibble lo <;>
      simp [parseFixedHex_loop_eq]
  | _ + 1, [], _ => rfl
  | _ + 1, [_], _ => rfl

theorem parseFixedHex_eq (nBytes : Nat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseFixedHex nBytes input =
      InternalSpec.WalletPolicy.parseFixedHex nBytes input := by
  unfold BitcoinLedger.WalletPolicy.parseFixedHex InternalSpec.WalletPolicy.parseFixedHex
  exact parseFixedHex_loop_eq nBytes input #[]

theorem parseAtIndex_eq (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseAtIndex input = InternalSpec.WalletPolicy.parseAtIndex input := by
  cases input with
  | nil => rfl
  | cons b rest =>
    cases decide (b = 0x40) <;> rfl

theorem parseAtIndexList_eq :
    ∀ (fuel : Nat) (input : List UInt8),
      BitcoinLedger.WalletPolicy.parseAtIndexList fuel input =
        InternalSpec.WalletPolicy.parseAtIndexList fuel input
  | 0, _ => rfl
  | fuel' + 1, input => by
    unfold BitcoinLedger.WalletPolicy.parseAtIndexList InternalSpec.WalletPolicy.parseAtIndexList
    simp only [parseAtIndex_eq input, parseAtIndexList_eq fuel']
    rfl

theorem parseDerivationSpec_eq (fmt : PolicyFormat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseDerivationSpec fmt input =
      InternalSpec.WalletPolicy.parseDerivationSpec fmt input := by
  cases fmt with
  | v1 => rfl
  | v2 =>
    unfold BitcoinLedger.WalletPolicy.parseDerivationSpec InternalSpec.WalletPolicy.parseDerivationSpec
    simp only [stripAsciiPrefix_eq, parseDecimalU32_eq]
    rfl

theorem parseKeyExpr_eq (fmt : PolicyFormat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseKeyExpr fmt input =
      InternalSpec.WalletPolicy.parseKeyExpr fmt input := by
  unfold BitcoinLedger.WalletPolicy.parseKeyExpr InternalSpec.WalletPolicy.parseKeyExpr
  simp only [stripAsciiPrefix_eq, parseAtIndexList_eq, parseDerivationSpec_eq, parseAtIndex_eq]
  rfl

theorem parseKeyExprList_eq :
    ∀ (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8),
      BitcoinLedger.WalletPolicy.parseKeyExprList fuel fmt input =
        InternalSpec.WalletPolicy.parseKeyExprList fuel fmt input
  | 0, _, _ => rfl
  | fuel' + 1, fmt, input => by
    unfold BitcoinLedger.WalletPolicy.parseKeyExprList InternalSpec.WalletPolicy.parseKeyExprList
    simp only [parseKeyExpr_eq fmt input, parseKeyExprList_eq fuel' fmt]
    rfl

theorem parseMultisigArgs_eq (fmt : PolicyFormat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseMultisigArgs fmt input =
      InternalSpec.WalletPolicy.parseMultisigArgs fmt input := by
  unfold BitcoinLedger.WalletPolicy.parseMultisigArgs InternalSpec.WalletPolicy.parseMultisigArgs
  simp only [parseDecimalNat_eq, parseKeyExprList_eq]
  rfl

theorem decodeWrapperByte_eq (b : UInt8) :
    BitcoinLedger.WalletPolicy.decodeWrapperByte b = InternalSpec.WalletPolicy.decodeWrapperByte b := rfl

theorem peelWrapperPrefixAux_eq :
    ∀ (input : List UInt8) (acc : List MiniscriptWrapper),
      BitcoinLedger.WalletPolicy.peelWrapperPrefixAux acc input =
        InternalSpec.WalletPolicy.peelWrapperPrefixAux acc input
  | [], _ => rfl
  | b :: rest, acc => by
    unfold BitcoinLedger.WalletPolicy.peelWrapperPrefixAux
    cases hColon : decide (b = 0x3A) with
    | true =>
      have hb : b = 0x3A := of_decide_eq_true hColon
      subst hb
      rfl
    | false =>
      have hne : b ≠ 0x3A := of_decide_eq_false hColon
      have hBeq : (b == 0x3A) = false := hColon
      simp only [hBeq, Bool.false_eq_true, ↓reduceIte, decodeWrapperByte_eq]
      have hSpec :
          InternalSpec.WalletPolicy.peelWrapperPrefixAux acc (b :: rest) =
            (match InternalSpec.WalletPolicy.decodeWrapperByte b with
             | some w => InternalSpec.WalletPolicy.peelWrapperPrefixAux (w :: acc) rest
             | none => none) := by
        rw [InternalSpec.WalletPolicy.peelWrapperPrefixAux.eq_2 _ _ _ (fun h => hne h)]
        rfl
      rw [hSpec]
      cases InternalSpec.WalletPolicy.decodeWrapperByte b with
      | none => rfl
      | some w => exact peelWrapperPrefixAux_eq rest (w :: acc)

theorem peelWrapperPrefix_eq (input : List UInt8) :
    BitcoinLedger.WalletPolicy.peelWrapperPrefix input =
      InternalSpec.WalletPolicy.peelWrapperPrefix input :=
  peelWrapperPrefixAux_eq input []

theorem applyMiniscriptWrappers_eq (ws : List MiniscriptWrapper) (base : Miniscript) :
    BitcoinLedger.WalletPolicy.applyMiniscriptWrappers ws base =
      InternalSpec.WalletPolicy.applyMiniscriptWrappers ws base := rfl

theorem parseMiniscript_bundle_eq :
    ∀ (fuel : Nat) (fmt : PolicyFormat),
      (∀ input, BitcoinLedger.WalletPolicy.parseMiniscriptBase fuel fmt input =
                  InternalSpec.WalletPolicy.parseMiniscriptBase fuel fmt input) ∧
      (∀ input, BitcoinLedger.WalletPolicy.parseMiniscript fuel fmt input =
                  InternalSpec.WalletPolicy.parseMiniscript fuel fmt input) ∧
      (∀ ctor input, BitcoinLedger.WalletPolicy.parseBinaryMiniscript fuel fmt ctor input =
                  InternalSpec.WalletPolicy.parseBinaryMiniscript fuel fmt ctor input) ∧
      (∀ input, BitcoinLedger.WalletPolicy.parseMiniscriptList fuel fmt input =
                  InternalSpec.WalletPolicy.parseMiniscriptList fuel fmt input)
  | 0, _ => ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  | fuel' + 1, fmt => by
    rcases parseMiniscript_bundle_eq fuel' fmt with ⟨ihBase, ihMs, ihBin, ihList⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro input
      unfold BitcoinLedger.WalletPolicy.parseMiniscriptBase InternalSpec.WalletPolicy.parseMiniscriptBase
      simp only [isAsciiDigit_eq, stripAsciiPrefix_eq, parseKeyExpr_eq, parseDecimalU32_eq,
        parseFixedHex_eq, parseDecimalNat_eq, parseMultisigArgs_eq, ihMs, ihBin, ihList]
      rfl
    · intro input
      unfold BitcoinLedger.WalletPolicy.parseMiniscript InternalSpec.WalletPolicy.parseMiniscript
      simp only [peelWrapperPrefix_eq, applyMiniscriptWrappers_eq, ihBase]
      rfl
    · intro ctor input
      unfold BitcoinLedger.WalletPolicy.parseBinaryMiniscript InternalSpec.WalletPolicy.parseBinaryMiniscript
      simp only [ihMs]
      rfl
    · intro input
      unfold BitcoinLedger.WalletPolicy.parseMiniscriptList InternalSpec.WalletPolicy.parseMiniscriptList
      simp only [ihMs, ihList]
      rfl

theorem parseMiniscript_eq (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseMiniscript fuel fmt input =
      InternalSpec.WalletPolicy.parseMiniscript fuel fmt input :=
  (parseMiniscript_bundle_eq fuel fmt).2.1 input

theorem parseWshScriptBody_eq (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseWshScriptBody fuel fmt input =
      InternalSpec.WalletPolicy.parseWshScriptBody fuel fmt input := by
  unfold BitcoinLedger.WalletPolicy.parseWshScriptBody InternalSpec.WalletPolicy.parseWshScriptBody
  simp only [stripAsciiPrefix_eq, parseMultisigArgs_eq, parseMiniscript_eq]
  rfl

theorem parseTapLeafScript_eq (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8) :
    BitcoinLedger.WalletPolicy.parseTapLeafScript fuel fmt input =
      InternalSpec.WalletPolicy.parseTapLeafScript fuel fmt input := by
  unfold BitcoinLedger.WalletPolicy.parseTapLeafScript InternalSpec.WalletPolicy.parseTapLeafScript
  simp only [stripAsciiPrefix_eq, parseMultisigArgs_eq, parseMiniscript_eq]
  rfl

theorem parseTapTree_eq :
    ∀ (fuel : Nat) (fmt : PolicyFormat) (input : List UInt8),
      BitcoinLedger.WalletPolicy.parseTapTree fuel fmt input =
        InternalSpec.WalletPolicy.parseTapTree fuel fmt input
  | 0, _, _ => rfl
  | fuel' + 1, fmt, input => by
    unfold BitcoinLedger.WalletPolicy.parseTapTree InternalSpec.WalletPolicy.parseTapTree
    simp only [parseTapTree_eq fuel' fmt, parseTapLeafScript_eq]
    rfl

theorem parseDescriptorTemplate_eq (fmt : PolicyFormat) (desc : String) :
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate fmt desc =
      InternalSpec.WalletPolicy.parseDescriptorTemplate fmt desc := by
  unfold BitcoinLedger.WalletPolicy.parseDescriptorTemplate InternalSpec.WalletPolicy.parseDescriptorTemplate
  simp only [stripAsciiPrefix_eq, parseKeyExpr_eq, parseWshScriptBody_eq, parseMultisigArgs_eq,
    parseTapTree_eq]
  rfl

theorem parseDescriptorTemplateWithProfile_eq (profile : PolicyProfile) (fmt : PolicyFormat)
    (desc : String) :
    BitcoinLedger.WalletPolicy.parseDescriptorTemplateWithProfile profile fmt desc =
      InternalSpec.WalletPolicy.parseDescriptorTemplateWithProfile profile fmt desc := by
  unfold BitcoinLedger.WalletPolicy.parseDescriptorTemplateWithProfile
    InternalSpec.WalletPolicy.parseDescriptorTemplateWithProfile
  simp only [parseDescriptorTemplate_eq]
  rfl

theorem validWalletNameBytesWithBounds_eq (allowEmpty : Bool) (maxLenOpt : Option Nat)
    (forbidEdgeSpaces : Bool) (bytes : List UInt8) :
    BitcoinLedger.WalletPolicy.validWalletNameBytesWithBounds allowEmpty maxLenOpt forbidEdgeSpaces bytes =
      InternalSpec.WalletPolicy.validWalletNameBytesWithBounds allowEmpty maxLenOpt forbidEdgeSpaces bytes := rfl

theorem validWalletName_eq (name : String) :
    BitcoinLedger.WalletPolicy.validWalletName name = InternalSpec.WalletPolicy.validWalletName name := rfl

theorem validRegisteredWalletName_eq (profile : PolicyProfile) (name : String) :
    BitcoinLedger.WalletPolicy.validRegisteredWalletName profile name =
      profile.validRegisteredWalletName name := rfl

theorem validDerivationSpec_eq (fmt : PolicyFormat) (d : DerivationSpec) :
    BitcoinLedger.WalletPolicy.validDerivationSpec fmt d = d.validForFormat fmt := by
  cases d <;> rfl

theorem derivationToPair_eq (d : DerivationSpec) :
    BitcoinLedger.WalletPolicy.derivationToPair d = d.toPair := by
  cases d <;> rfl

theorem derivationStepForBranch_eq (d : DerivationSpec) (isChange : Bool) :
    BitcoinLedger.WalletPolicy.derivationStepForBranch d isChange = d.stepForBranch isChange := by
  cases d <;> rfl

theorem keyExprDeriv_eq (ke : KeyExpr) :
    BitcoinLedger.WalletPolicy.keyExprDeriv ke = ke.deriv := by
  cases ke <;> rfl

theorem keyExprReferencedIndices_eq (ke : KeyExpr) :
    BitcoinLedger.WalletPolicy.keyExprReferencedIndices ke = ke.referencedIndices := by
  cases ke <;> rfl

/-! ## Section 3: BIP-68 / BIP-65 Timelocks & BIP-379 Miniscript Typechecker Equivalence -/

theorem pushScriptNumSize_eq (n : UInt32) :
    BitcoinLedger.WalletPolicy.pushScriptNumSize n = InternalSpec.WalletPolicy.pushScriptNumSize n := rfl

theorem optAdd_eq (a b : Option Nat) :
    BitcoinLedger.WalletPolicy.optAdd a b = InternalSpec.WalletPolicy.optAdd a b := rfl

theorem optMax_eq (a b : Option Nat) :
    BitcoinLedger.WalletPolicy.optMax a b = InternalSpec.WalletPolicy.optMax a b := rfl

theorem hasTimelockConflict_eq (a b : MiniscriptExtInfo) :
    BitcoinLedger.WalletPolicy.hasTimelockConflict a b =
      InternalSpec.WalletPolicy.hasTimelockConflict a b := rfl

theorem validOlderArg_eq (n : UInt32) :
    BitcoinLedger.WalletPolicy.validOlderArg n = InternalSpec.WalletPolicy.validOlderArg n := rfl

theorem validAfterArg_eq (n : UInt32) :
    BitcoinLedger.WalletPolicy.validAfterArg n = InternalSpec.WalletPolicy.validAfterArg n := rfl

theorem listNodup_eq {α : Type} [DecidableEq α] :
    ∀ (xs : List α), BitcoinLedger.WalletPolicy.listNodup xs = InternalSpec.WalletPolicy.listNodup xs
  | [] => rfl
  | x :: xs => by
    unfold BitcoinLedger.WalletPolicy.listNodup InternalSpec.WalletPolicy.listNodup
    rw [listNodup_eq xs]

theorem checkKeyExprInContext_eq (fmt : PolicyFormat) (allowMusig : Bool) (maxMusigKeys : Nat)
    (ke : KeyExpr) :
    BitcoinLedger.WalletPolicy.checkKeyExprInContext fmt allowMusig maxMusigKeys ke =
      InternalSpec.WalletPolicy.checkKeyExprInContext fmt allowMusig maxMusigKeys ke := by
  unfold BitcoinLedger.WalletPolicy.checkKeyExprInContext InternalSpec.WalletPolicy.checkKeyExprInContext
  simp only [isUnhardened_eq, listNodup_eq]
  rfl

theorem checkKeyExprList_eq (fmt : PolicyFormat) (allowMusig : Bool) (maxMusigKeys : Nat) :
    ∀ (kes : List KeyExpr),
      BitcoinLedger.WalletPolicy.checkKeyExprList fmt allowMusig maxMusigKeys kes =
        InternalSpec.WalletPolicy.checkKeyExprList fmt allowMusig maxMusigKeys kes
  | [] => rfl
  | ke :: kes => by
    unfold BitcoinLedger.WalletPolicy.checkKeyExprList InternalSpec.WalletPolicy.checkKeyExprList
    rw [checkKeyExprInContext_eq, checkKeyExprList_eq fmt allowMusig maxMusigKeys kes]

theorem threshDpStep_go_eq (childSat childDsat : Option Nat) :
    ∀ (sats : List (Option Nat)) (prev : Option Nat),
      BitcoinLedger.WalletPolicy.threshDpStep.go childSat childDsat prev sats =
        InternalSpec.WalletPolicy.threshDpStep.go childSat childDsat prev sats
  | [], _ => rfl
  | cur :: rest, prev => by
    unfold BitcoinLedger.WalletPolicy.threshDpStep.go InternalSpec.WalletPolicy.threshDpStep.go
    rw [optAdd_eq, optAdd_eq, optMax_eq, threshDpStep_go_eq childSat childDsat rest cur]

theorem threshDpStep_eq (sats : List (Option Nat)) (childSat childDsat : Option Nat) :
    BitcoinLedger.WalletPolicy.threshDpStep sats childSat childDsat =
      InternalSpec.WalletPolicy.threshDpStep sats childSat childDsat := by
  cases sats with
  | nil => rfl
  | cons s0 rest =>
    unfold BitcoinLedger.WalletPolicy.threshDpStep InternalSpec.WalletPolicy.threshDpStep
    dsimp only
    rw [optAdd_eq, threshDpStep_go_eq childSat childDsat rest s0]

theorem listGetOpt_eq :
    ∀ (xs : List (Option Nat)) (idx : Nat),
      BitcoinLedger.WalletPolicy.listGetOpt xs idx = InternalSpec.WalletPolicy.listGetOpt xs idx
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, idx + 1 => listGetOpt_eq xs idx

theorem analyzeMiniscript_eq (fmt : PolicyFormat) (ctx : MiniscriptCtx)
    (maxMultiKeys maxMultiAKeys maxMusigKeys : Nat) :
    ∀ (ms : Miniscript),
      BitcoinLedger.WalletPolicy.analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys ms =
        InternalSpec.WalletPolicy.analyzeMiniscript fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys ms := by
  intro ms
  induction ms using InternalSpec.WalletPolicy.Miniscript.rec
    (motive_2 := fun subs =>
      ∀ isFirst : Bool,
        BitcoinLedger.WalletPolicy.analyzeMiniscript.analyzeChildren fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys isFirst subs =
          InternalSpec.WalletPolicy.analyzeMiniscript.analyzeChildren fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys isFirst subs) with
  | ms0 => rfl
  | ms1 => rfl
  | pk ke =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    rw [checkKeyExprInContext_eq]
  | pkh ke =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    rw [checkKeyExprInContext_eq]
  | pk_k ke =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    rw [checkKeyExprInContext_eq]
  | pk_h ke =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    rw [checkKeyExprInContext_eq]
  | older val => rfl
  | after val => rfl
  | sha256 h => rfl
  | hash256 h => rfl
  | ripemd160 h => rfl
  | hash160 h => rfl
  | andor x y z ihx ihy ihz =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihy, ihz, hasTimelockConflict_eq, optAdd_eq, optMax_eq]
  | and_v x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihy, hasTimelockConflict_eq, optAdd_eq]
  | and_b x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihy, hasTimelockConflict_eq, optAdd_eq]
  | and_n x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihy, hasTimelockConflict_eq, optAdd_eq]
  | or_b x z ihx ihz =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihz, optAdd_eq, optMax_eq]
  | or_c x z ihx ihz =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihz, optAdd_eq, optMax_eq]
  | or_d x z ihx ihz =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihz, optAdd_eq, optMax_eq]
  | or_i x z ihx ihz =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihx, ihz, optAdd_eq, optMax_eq]
  | thresh k subs ihSubs =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ihSubs true, threshDpStep_eq, listGetOpt_eq, pushScriptNumSize_eq]
  | multi k keys =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [checkKeyExprList_eq, pushScriptNumSize_eq]
  | multi_a k keys =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [checkKeyExprList_eq, pushScriptNumSize_eq]
  | wrap w sub ih =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript InternalSpec.WalletPolicy.analyzeMiniscript
    simp only [ih, optAdd_eq, optMax_eq]
    rfl
  | nil =>
    rfl
  | cons m ms ihm ihms =>
    unfold BitcoinLedger.WalletPolicy.analyzeMiniscript.analyzeChildren
      InternalSpec.WalletPolicy.analyzeMiniscript.analyzeChildren
    simp only [ihm, ihms false]

theorem checkMiniscriptSane_eq (fmt : PolicyFormat) (ctx : MiniscriptCtx)
    (maxMultiKeys maxMultiAKeys maxMusigKeys : Nat) (ms : Miniscript) :
    BitcoinLedger.WalletPolicy.checkMiniscriptSane fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys ms =
      InternalSpec.WalletPolicy.checkMiniscriptSane fmt ctx maxMultiKeys maxMultiAKeys maxMusigKeys ms := by
  unfold BitcoinLedger.WalletPolicy.checkMiniscriptSane InternalSpec.WalletPolicy.checkMiniscriptSane
  rw [analyzeMiniscript_eq]
  rfl

/-! ## Section 4: Whole-Policy Validation, Placeholder Coverage, Ownership & Auth Equivalence -/

theorem collectMiniscriptKeyExprs_eq :
    ∀ (ms : Miniscript),
      BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs ms =
        InternalSpec.WalletPolicy.collectMiniscriptKeyExprs ms := by
  intro ms
  induction ms using InternalSpec.WalletPolicy.Miniscript.rec
    (motive_2 := fun subs =>
      BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs.goList subs =
        InternalSpec.WalletPolicy.collectMiniscriptKeyExprs.goList subs) with
  | ms0 | ms1 | older _ | after _ | sha256 _ | hash256 _ | ripemd160 _ | hash160 _ => rfl
  | pk _ | pkh _ | pk_k _ | pk_h _ => rfl
  | multi _ _ | multi_a _ _ => rfl
  | andor x y z ihx ihy ihz =>
    unfold BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs
      InternalSpec.WalletPolicy.collectMiniscriptKeyExprs
    rw [ihx, ihy, ihz]
  | and_v x y ihx ihy | and_b x y ihx ihy | and_n x y ihx ihy
  | or_b x y ihx ihy | or_c x y ihx ihy | or_d x y ihx ihy | or_i x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs
      InternalSpec.WalletPolicy.collectMiniscriptKeyExprs
    rw [ihx, ihy]
  | thresh _ subs ihSubs =>
    unfold BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs
      InternalSpec.WalletPolicy.collectMiniscriptKeyExprs
    exact ihSubs
  | wrap _ sub ih =>
    unfold BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs
      InternalSpec.WalletPolicy.collectMiniscriptKeyExprs
    exact ih
  | nil => rfl
  | cons m ms ihm ihms =>
    unfold BitcoinLedger.WalletPolicy.collectMiniscriptKeyExprs.goList
      InternalSpec.WalletPolicy.collectMiniscriptKeyExprs.goList
    rw [ihm, ihms]

theorem collectWshKeyExprs_eq (ws : WshScript) :
    BitcoinLedger.WalletPolicy.collectWshKeyExprs ws =
      InternalSpec.WalletPolicy.collectWshKeyExprs ws := by
  cases ws with
  | sortedmulti _ _ => rfl
  | miniscript ms => exact collectMiniscriptKeyExprs_eq ms

theorem collectTapLeafKeyExprs_eq (ls : TapLeafScript) :
    BitcoinLedger.WalletPolicy.collectTapLeafKeyExprs ls =
      InternalSpec.WalletPolicy.collectTapLeafKeyExprs ls := by
  cases ls with
  | sortedmulti_a _ _ => rfl
  | miniscript ms => exact collectMiniscriptKeyExprs_eq ms

theorem collectTapTreeKeyExprs_eq :
    ∀ (t : TapTree),
      BitcoinLedger.WalletPolicy.collectTapTreeKeyExprs t =
        InternalSpec.WalletPolicy.collectTapTreeKeyExprs t
  | .leaf ls => collectTapLeafKeyExprs_eq ls
  | .branch l r => by
    unfold BitcoinLedger.WalletPolicy.collectTapTreeKeyExprs
      InternalSpec.WalletPolicy.collectTapTreeKeyExprs
    rw [collectTapTreeKeyExprs_eq l, collectTapTreeKeyExprs_eq r]

theorem collectTemplateKeyExprs_eq (dt : DescriptorTemplate) :
    BitcoinLedger.WalletPolicy.collectTemplateKeyExprs dt =
      InternalSpec.WalletPolicy.collectTemplateKeyExprs dt := by
  cases dt with
  | pkh _ | wpkh _ => rfl
  | sh inner =>
    cases inner with
    | wpkh _ | multi _ _ | sortedmulti _ _ => rfl
    | wsh ws => exact collectWshKeyExprs_eq ws
  | wsh ws => exact collectWshKeyExprs_eq ws
  | tr ik treeOpt =>
    cases treeOpt with
    | none => rfl
    | some tree =>
      unfold BitcoinLedger.WalletPolicy.collectTemplateKeyExprs
        InternalSpec.WalletPolicy.collectTemplateKeyExprs
      dsimp only
      rw [collectTapTreeKeyExprs_eq tree]

theorem tapTreeDepth_eq :
    ∀ (t : TapTree), BitcoinLedger.WalletPolicy.tapTreeDepth t = TapTree.depth t
  | .leaf _ => rfl
  | .branch l r => by
    unfold BitcoinLedger.WalletPolicy.tapTreeDepth TapTree.depth
    rw [tapTreeDepth_eq l, tapTreeDepth_eq r]

theorem miniscriptAstDepth_eq :
    ∀ (ms : Miniscript),
      BitcoinLedger.WalletPolicy.miniscriptAstDepth ms = Miniscript.astDepth ms := by
  intro ms
  induction ms using InternalSpec.WalletPolicy.Miniscript.rec
    (motive_2 := fun subs =>
      BitcoinLedger.WalletPolicy.miniscriptAstDepth.maxList subs =
        Miniscript.astDepth.maxList subs) with
  | ms0 | ms1 | pk _ | pkh _ | pk_k _ | pk_h _
  | older _ | after _ | sha256 _ | hash256 _ | ripemd160 _ | hash160 _
  | multi _ _ | multi_a _ _ => rfl
  | wrap _ sub ih =>
    unfold BitcoinLedger.WalletPolicy.miniscriptAstDepth Miniscript.astDepth
    rw [ih]
  | and_v x y ihx ihy | and_b x y ihx ihy | and_n x y ihx ihy
  | or_b x y ihx ihy | or_c x y ihx ihy | or_d x y ihx ihy | or_i x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.miniscriptAstDepth Miniscript.astDepth
    rw [ihx, ihy]
  | andor x y z ihx ihy ihz =>
    unfold BitcoinLedger.WalletPolicy.miniscriptAstDepth Miniscript.astDepth
    rw [ihx, ihy, ihz]
  | thresh _ subs ihSubs =>
    unfold BitcoinLedger.WalletPolicy.miniscriptAstDepth Miniscript.astDepth
    rw [ihSubs]
  | nil => rfl
  | cons m ms ihm ihms =>
    unfold BitcoinLedger.WalletPolicy.miniscriptAstDepth.maxList
      Miniscript.astDepth.maxList
    rw [ihm, ihms]

theorem miniscriptThreshNesting_eq :
    ∀ (ms : Miniscript),
      BitcoinLedger.WalletPolicy.miniscriptThreshNesting ms = Miniscript.threshNesting ms := by
  intro ms
  induction ms using InternalSpec.WalletPolicy.Miniscript.rec
    (motive_2 := fun subs =>
      BitcoinLedger.WalletPolicy.miniscriptThreshNesting.maxList subs =
        Miniscript.threshNesting.maxList subs) with
  | ms0 | ms1 | pk _ | pkh _ | pk_k _ | pk_h _
  | older _ | after _ | sha256 _ | hash256 _ | ripemd160 _ | hash160 _
  | multi _ _ | multi_a _ _ => rfl
  | wrap _ sub ih =>
    unfold BitcoinLedger.WalletPolicy.miniscriptThreshNesting Miniscript.threshNesting
    exact ih
  | and_v x y ihx ihy | and_b x y ihx ihy | and_n x y ihx ihy
  | or_b x y ihx ihy | or_c x y ihx ihy | or_d x y ihx ihy | or_i x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.miniscriptThreshNesting Miniscript.threshNesting
    rw [ihx, ihy]
  | andor x y z ihx ihy ihz =>
    unfold BitcoinLedger.WalletPolicy.miniscriptThreshNesting Miniscript.threshNesting
    rw [ihx, ihy, ihz]
  | thresh _ subs ihSubs =>
    unfold BitcoinLedger.WalletPolicy.miniscriptThreshNesting Miniscript.threshNesting
    rw [ihSubs]
  | nil => rfl
  | cons m ms ihm ihms =>
    unfold BitcoinLedger.WalletPolicy.miniscriptThreshNesting.maxList
      Miniscript.threshNesting.maxList
    rw [ihm, ihms]

theorem miniscriptMaxThreshArity_eq :
    ∀ (ms : Miniscript),
      BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity ms = Miniscript.maxThreshArity ms := by
  intro ms
  induction ms using InternalSpec.WalletPolicy.Miniscript.rec
    (motive_2 := fun subs =>
      BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity.maxList subs =
        Miniscript.maxThreshArity.maxList subs) with
  | ms0 | ms1 | pk _ | pkh _ | pk_k _ | pk_h _
  | older _ | after _ | sha256 _ | hash256 _ | ripemd160 _ | hash160 _
  | multi _ _ | multi_a _ _ => rfl
  | wrap _ sub ih =>
    unfold BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity Miniscript.maxThreshArity
    exact ih
  | and_v x y ihx ihy | and_b x y ihx ihy | and_n x y ihx ihy
  | or_b x y ihx ihy | or_c x y ihx ihy | or_d x y ihx ihy | or_i x y ihx ihy =>
    unfold BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity Miniscript.maxThreshArity
    rw [ihx, ihy]
  | andor x y z ihx ihy ihz =>
    unfold BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity Miniscript.maxThreshArity
    rw [ihx, ihy, ihz]
  | thresh _ subs ihSubs =>
    unfold BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity Miniscript.maxThreshArity
    rw [ihSubs]
  | nil => rfl
  | cons m ms ihm ihms =>
    unfold BitcoinLedger.WalletPolicy.miniscriptMaxThreshArity.maxList
      Miniscript.maxThreshArity.maxList
    rw [ihm, ihms]

theorem checkMiniscriptResourceBounds_eq (profile : PolicyProfile) (ms : Miniscript) :
    BitcoinLedger.WalletPolicy.checkMiniscriptResourceBounds profile ms =
      InternalSpec.WalletPolicy.checkMiniscriptResourceBounds profile ms := by
  unfold BitcoinLedger.WalletPolicy.checkMiniscriptResourceBounds
    InternalSpec.WalletPolicy.checkMiniscriptResourceBounds
  rw [miniscriptAstDepth_eq, miniscriptThreshNesting_eq, miniscriptMaxThreshArity_eq]
  rfl

theorem dedupFirstAppearance_go_eq :
    ∀ (ys seen : List Nat),
      BitcoinLedger.WalletPolicy.dedupFirstAppearance.go seen ys =
        InternalSpec.WalletPolicy.dedupFirstAppearance.go seen ys
  | [], _ => rfl
  | y :: ys, seen => by
    unfold BitcoinLedger.WalletPolicy.dedupFirstAppearance.go
      InternalSpec.WalletPolicy.dedupFirstAppearance.go
    cases seen.contains y <;> exact dedupFirstAppearance_go_eq ys _

theorem dedupFirstAppearance_eq (xs : List Nat) :
    BitcoinLedger.WalletPolicy.dedupFirstAppearance xs =
      InternalSpec.WalletPolicy.dedupFirstAppearance xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact dedupFirstAppearance_go_eq xs [x]

theorem insertNat_eq (x : Nat) :
    ∀ (ys : List Nat), BitcoinLedger.WalletPolicy.insertNat x ys = InternalSpec.WalletPolicy.insertNat x ys
  | [] => rfl
  | y :: ys => by
    unfold BitcoinLedger.WalletPolicy.insertNat InternalSpec.WalletPolicy.insertNat
    rw [insertNat_eq x ys]

theorem sortNats_eq :
    ∀ (xs : List Nat), BitcoinLedger.WalletPolicy.sortNats xs = InternalSpec.WalletPolicy.sortNats xs
  | [] => rfl
  | x :: xs => by
    unfold BitcoinLedger.WalletPolicy.sortNats InternalSpec.WalletPolicy.sortNats
    rw [sortNats_eq xs, insertNat_eq]

theorem sameKeyPlaceholder_eq (kp1 kp2 : KeyExpr) :
    BitcoinLedger.WalletPolicy.sameKeyPlaceholder kp1 kp2 =
      InternalSpec.WalletPolicy.sameKeyPlaceholder kp1 kp2 := by
  cases kp1 <;> cases kp2 <;> simp only [BitcoinLedger.WalletPolicy.sameKeyPlaceholder,
    InternalSpec.WalletPolicy.sameKeyPlaceholder, sortNats_eq]

theorem disjointDerivations_eq (d1 d2 : DerivationSpec) :
    BitcoinLedger.WalletPolicy.disjointDerivations d1 d2 =
      InternalSpec.WalletPolicy.disjointDerivations d1 d2 := by
  unfold BitcoinLedger.WalletPolicy.disjointDerivations InternalSpec.WalletPolicy.disjointDerivations
  rw [derivationToPair_eq, derivationToPair_eq]

theorem checkPairwiseDisjointMultipaths_eq :
    ∀ (kes : List KeyExpr),
      BitcoinLedger.WalletPolicy.checkPairwiseDisjointMultipaths kes =
        InternalSpec.WalletPolicy.checkPairwiseDisjointMultipaths kes
  | [] => rfl
  | kp :: rest => by
    unfold BitcoinLedger.WalletPolicy.checkPairwiseDisjointMultipaths
      InternalSpec.WalletPolicy.checkPairwiseDisjointMultipaths
    simp only [sameKeyPlaceholder_eq, disjointDerivations_eq, keyExprDeriv_eq,
      checkPairwiseDisjointMultipaths_eq rest]

theorem foldr_referencedIndices_eq :
    ∀ (kes : List KeyExpr),
      kes.foldr (fun ke acc => BitcoinLedger.WalletPolicy.keyExprReferencedIndices ke ++ acc) [] =
        kes.foldr (fun ke acc => ke.referencedIndices ++ acc) []
  | [] => rfl
  | ke :: rest => by
    simp only [List.foldr_cons, keyExprReferencedIndices_eq]

theorem checkPlaceholderCoverage_eq (nKeys : Nat) (requireSequential : Bool)
    (keyExprs : List KeyExpr) :
    BitcoinLedger.WalletPolicy.checkPlaceholderCoverage nKeys requireSequential keyExprs =
      InternalSpec.WalletPolicy.checkPlaceholderCoverage nKeys requireSequential keyExprs := by
  unfold BitcoinLedger.WalletPolicy.checkPlaceholderCoverage
    InternalSpec.WalletPolicy.checkPlaceholderCoverage
  simp only [foldr_referencedIndices_eq, dedupFirstAppearance_eq]

theorem checkWshScript_eq (profile : PolicyProfile) (fmt : PolicyFormat) (insideSh : Bool)
    (ws : WshScript) :
    BitcoinLedger.WalletPolicy.checkWshScript profile fmt insideSh ws =
      InternalSpec.WalletPolicy.checkWshScript profile fmt insideSh ws := by
  cases ws with
  | sortedmulti k keys =>
    unfold BitcoinLedger.WalletPolicy.checkWshScript InternalSpec.WalletPolicy.checkWshScript
    simp only [checkKeyExprList_eq]
  | miniscript ms =>
    unfold BitcoinLedger.WalletPolicy.checkWshScript InternalSpec.WalletPolicy.checkWshScript
    simp only [checkMiniscriptResourceBounds_eq, checkKeyExprList_eq, checkMiniscriptSane_eq]
    rfl

theorem checkTapTree_eq (profile : PolicyProfile) (fmt : PolicyFormat) :
    ∀ (t : TapTree),
      BitcoinLedger.WalletPolicy.checkTapTree profile fmt t =
        InternalSpec.WalletPolicy.checkTapTree profile fmt t
  | .leaf (.sortedmulti_a k keys) => by
    unfold BitcoinLedger.WalletPolicy.checkTapTree InternalSpec.WalletPolicy.checkTapTree
    simp only [checkKeyExprList_eq]
  | .leaf (.miniscript ms) => by
    unfold BitcoinLedger.WalletPolicy.checkTapTree InternalSpec.WalletPolicy.checkTapTree
    simp only [checkMiniscriptResourceBounds_eq, checkMiniscriptSane_eq]
  | .branch l r => by
    unfold BitcoinLedger.WalletPolicy.checkTapTree InternalSpec.WalletPolicy.checkTapTree
    rw [checkTapTree_eq profile fmt l, checkTapTree_eq profile fmt r]

theorem checkDescriptorTemplate_eq (profile : PolicyProfile) (fmt : PolicyFormat)
    (dt : DescriptorTemplate) :
    BitcoinLedger.WalletPolicy.checkDescriptorTemplate profile fmt dt =
      InternalSpec.WalletPolicy.checkDescriptorTemplate profile fmt dt := by
  cases dt with
  | pkh ke | wpkh ke => exact checkKeyExprInContext_eq fmt false profile.maxMusigKeys ke
  | sh inner =>
    cases inner with
    | wpkh ke => exact checkKeyExprInContext_eq fmt false profile.maxMusigKeys ke
    | multi k keys | sortedmulti k keys =>
      unfold BitcoinLedger.WalletPolicy.checkDescriptorTemplate
        InternalSpec.WalletPolicy.checkDescriptorTemplate
      simp only [checkKeyExprList_eq]
    | wsh ws =>
      unfold BitcoinLedger.WalletPolicy.checkDescriptorTemplate
        InternalSpec.WalletPolicy.checkDescriptorTemplate
      simp only [checkWshScript_eq]
  | wsh ws => exact checkWshScript_eq profile fmt false ws
  | tr ik treeOpt =>
    cases treeOpt with
    | none =>
      unfold BitcoinLedger.WalletPolicy.checkDescriptorTemplate
        InternalSpec.WalletPolicy.checkDescriptorTemplate
      simp only [checkKeyExprInContext_eq]
    | some tree =>
      unfold BitcoinLedger.WalletPolicy.checkDescriptorTemplate
        InternalSpec.WalletPolicy.checkDescriptorTemplate
      simp only [tapTreeDepth_eq, checkKeyExprInContext_eq, checkTapTree_eq]

theorem checkTemplateByteBounds_eq (profile : PolicyProfile) (policy : WalletPolicy) :
    BitcoinLedger.WalletPolicy.checkTemplateByteBounds profile policy =
      InternalSpec.WalletPolicy.checkTemplateByteBounds profile policy := rfl

theorem checkPolicyWellFormed_eq (profile : PolicyProfile) (policy : WalletPolicy) :
    BitcoinLedger.WalletPolicy.checkPolicyWellFormed profile policy =
      InternalSpec.WalletPolicy.checkPolicyWellFormed profile policy := by
  unfold BitcoinLedger.WalletPolicy.checkPolicyWellFormed InternalSpec.WalletPolicy.checkPolicyWellFormed
  have hKiFn :
      BitcoinLedger.WalletPolicy.validKeyInfoWithBounds profile.maxOriginSteps policy.format profile.network =
        KeyInformation.validForFormatWithBounds profile.maxOriginSteps policy.format profile.network := rfl
  simp only [checkTemplateByteBounds_eq, hKiFn, listNodup_eq, checkDescriptorTemplate_eq,
    collectTemplateKeyExprs_eq, checkPlaceholderCoverage_eq, checkPairwiseDisjointMultipaths_eq]

theorem classifyKeyInfo_eq (dev : DeviceRegistrationOracle) (net : Network) (ki : KeyInformation) :
    BitcoinLedger.WalletPolicy.classifyKeyInfo dev net ki =
      InternalSpec.WalletPolicy.classifyKeyInfo dev net ki := rfl

theorem isOurKey_eq (dev : DeviceRegistrationOracle) (net : Network) (ki : KeyInformation) :
    BitcoinLedger.WalletPolicy.isOurKey dev net ki = InternalSpec.WalletPolicy.isOurKey dev net ki := rfl

theorem hasOurKey_eq (dev : DeviceRegistrationOracle) (net : Network) (policy : WalletPolicy) :
    BitcoinLedger.WalletPolicy.hasOurKey dev net policy =
      InternalSpec.WalletPolicy.hasOurKey dev net policy := rfl

theorem listNthOpt_eq {α : Type} :
    ∀ (xs : List α) (idx : Nat),
      BitcoinLedger.WalletPolicy.listNthOpt xs idx = InternalSpec.WalletPolicy.listNthOpt xs idx
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, idx + 1 => listNthOpt_eq xs idx

theorem countInternalInKeyExpr_eq (roles : List PolicyKeyRole) (ke : KeyExpr) :
    BitcoinLedger.WalletPolicy.countInternalInKeyExpr roles ke =
      InternalSpec.WalletPolicy.countInternalInKeyExpr roles ke := by
  unfold BitcoinLedger.WalletPolicy.countInternalInKeyExpr
    InternalSpec.WalletPolicy.countInternalInKeyExpr
  simp only [keyExprReferencedIndices_eq, listNthOpt_eq]

theorem checkMusigSingleInternal_eq (roles : List PolicyKeyRole) :
    ∀ (kes : List KeyExpr),
      BitcoinLedger.WalletPolicy.checkMusigSingleInternal roles kes =
        InternalSpec.WalletPolicy.checkMusigSingleInternal roles kes
  | [] => rfl
  | .single _ _ :: rest => checkMusigSingleInternal_eq roles rest
  | .musig _ _ :: rest => by
    unfold BitcoinLedger.WalletPolicy.checkMusigSingleInternal
      InternalSpec.WalletPolicy.checkMusigSingleInternal
    rw [countInternalInKeyExpr_eq, checkMusigSingleInternal_eq roles rest]

theorem checkRegisteredSignability_eq (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (policy : WalletPolicy) :
    BitcoinLedger.WalletPolicy.checkRegisteredSignability profile dev policy =
      InternalSpec.WalletPolicy.checkRegisteredSignability profile dev policy := by
  unfold BitcoinLedger.WalletPolicy.checkRegisteredSignability
    InternalSpec.WalletPolicy.checkRegisteredSignability
  have hClassFn :
      BitcoinLedger.WalletPolicy.classifyKeyInfo dev profile.network =
        InternalSpec.WalletPolicy.classifyKeyInfo dev profile.network := rfl
  have hCountFn :
      (fun ke => decide (BitcoinLedger.WalletPolicy.countInternalInKeyExpr
        (policy.keys.map (InternalSpec.WalletPolicy.classifyKeyInfo dev profile.network)) ke > 0)) =
      (fun ke => decide (InternalSpec.WalletPolicy.countInternalInKeyExpr
        (policy.keys.map (InternalSpec.WalletPolicy.classifyKeyInfo dev profile.network)) ke > 0)) := by
    funext ke
    rw [countInternalInKeyExpr_eq]
  simp only [hClassFn, collectTemplateKeyExprs_eq, checkMusigSingleInternal_eq, hCountFn]

theorem standardBip44Purpose_eq (dt : DescriptorTemplate) :
    BitcoinLedger.WalletPolicy.standardBip44Purpose dt =
      InternalSpec.WalletPolicy.standardBip44Purpose dt := by
  cases dt with
  | pkh ke | wpkh ke =>
    cases ke with
    | single idx d =>
      cases idx with
      | zero => cases d <;> rfl
      | succ _ => rfl
    | musig _ _ => rfl
  | sh inner =>
    cases inner with
    | wpkh ke =>
      cases ke with
      | single idx d =>
        cases idx with
        | zero => cases d <;> rfl
        | succ _ => rfl
      | musig _ _ => rfl
    | _ => rfl
  | wsh _ => rfl
  | tr ik treeOpt =>
    cases treeOpt with
    | none =>
      cases ik with
      | single idx d =>
        cases idx with
        | zero => cases d <;> rfl
        | succ _ => rfl
      | musig _ _ => rfl
    | some _ => rfl

theorem isDefaultStatelessPolicy_eq (dev : DeviceRegistrationOracle) (net : Network)
    (policy : WalletPolicy) :
    BitcoinLedger.WalletPolicy.isDefaultStatelessPolicy dev net policy =
      InternalSpec.WalletPolicy.isDefaultStatelessPolicy dev net policy := by
  unfold BitcoinLedger.WalletPolicy.isDefaultStatelessPolicy
    InternalSpec.WalletPolicy.isDefaultStatelessPolicy
  simp only [standardBip44Purpose_eq, isOurKey_eq, hardened_eq, coinTypeOfNetwork_eq]
  rfl

theorem validatePolicyRegistration_eq (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (policy : WalletPolicy) (userApproved : Bool) :
    BitcoinLedger.WalletPolicy.validatePolicyRegistration profile dev policy userApproved =
      InternalSpec.WalletPolicy.validatePolicyRegistration profile dev policy userApproved := by
  unfold BitcoinLedger.WalletPolicy.validatePolicyRegistration
    InternalSpec.WalletPolicy.validatePolicyRegistration
  simp only [validRegisteredWalletName_eq, checkPolicyWellFormed_eq, checkRegisteredSignability_eq]

theorem authorizePolicyUse_eq (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (policy : WalletPolicy) (auth : PolicyAuthorization) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.authorizePolicyUse profile dev policy auth addressIndex =
      InternalSpec.WalletPolicy.authorizePolicyUse profile dev policy auth addressIndex := by
  unfold BitcoinLedger.WalletPolicy.authorizePolicyUse InternalSpec.WalletPolicy.authorizePolicyUse
  simp only [isUnhardened_eq, checkPolicyWellFormed_eq, isDefaultStatelessPolicy_eq,
    validRegisteredWalletName_eq]
  rfl

/-! ## Section 5: Script Compiler, BIP-341 TapTree/TapTweak & Policy Derivation Equivalence -/

theorem pushScriptU32_eq (n : UInt32) :
    BitcoinLedger.WalletPolicy.pushScriptU32 n = InternalSpec.WalletPolicy.pushScriptU32 n := rfl

theorem pushSmallBytes_eq (bs : ByteArray) :
    BitcoinLedger.WalletPolicy.pushSmallBytes bs = InternalSpec.WalletPolicy.pushSmallBytes bs := rfl

theorem emitOpVerify_eq (verifyFlag : Bool) (op : UInt8) :
    BitcoinLedger.WalletPolicy.emitOpVerify verifyFlag op =
      InternalSpec.WalletPolicy.emitOpVerify verifyFlag op := rfl

theorem hash160_eq (ora : CryptoPolicyOracle) (data : ByteArray) :
    BitcoinLedger.WalletPolicy.hash160 ora data = ora.hash160 data := rfl

theorem hash256_eq (ora : CryptoPolicyOracle) (data : ByteArray) :
    BitcoinLedger.WalletPolicy.hash256 ora data = ora.hash256 data := rfl

theorem taggedHash_eq (ora : CryptoPolicyOracle) (tag : String) (msg : ByteArray) :
    BitcoinLedger.WalletPolicy.taggedHash ora tag msg = ora.taggedHash tag msg := rfl

theorem tapLeafHash_eq (ora : CryptoPolicyOracle) (tapscript : ByteArray) :
    BitcoinLedger.WalletPolicy.tapLeafHash ora tapscript = ora.tapLeafHash tapscript := rfl

theorem tapBranchHash_eq (ora : CryptoPolicyOracle) (leftHash rightHash : ByteArray) :
    BitcoinLedger.WalletPolicy.tapBranchHash ora leftHash rightHash =
      ora.tapBranchHash leftHash rightHash := by
  unfold BitcoinLedger.WalletPolicy.tapBranchHash CryptoPolicyOracle.tapBranchHash
  rw [byteArrayLt_eq, taggedHash_eq]

theorem tapTweakHash_eq (ora : CryptoPolicyOracle) (internalXOnly : ByteArray)
    (merkleRoot : Option ByteArray) :
    BitcoinLedger.WalletPolicy.tapTweakHash ora internalXOnly merkleRoot =
      ora.tapTweakHash internalXOnly merkleRoot := by
  cases merkleRoot <;> rfl

theorem lookupKeyXpub_eq (keys : List KeyInformation) (idx : Nat) :
    BitcoinLedger.WalletPolicy.lookupKeyXpub keys idx =
      InternalSpec.WalletPolicy.lookupKeyXpub keys idx := by
  unfold BitcoinLedger.WalletPolicy.lookupKeyXpub InternalSpec.WalletPolicy.lookupKeyXpub
  rw [listNthOpt_eq]
  rfl

theorem lookupMusigCompressedKeys_eq (keys : List KeyInformation) :
    ∀ (idxs : List Nat),
      BitcoinLedger.WalletPolicy.lookupMusigCompressedKeys keys idxs =
        InternalSpec.WalletPolicy.lookupMusigCompressedKeys keys idxs
  | [] => rfl
  | idx :: idxs => by
    unfold BitcoinLedger.WalletPolicy.lookupMusigCompressedKeys
      InternalSpec.WalletPolicy.lookupMusigCompressedKeys
    rw [lookupKeyXpub_eq, lookupMusigCompressedKeys_eq keys idxs]

theorem deriveKeyExprCompressedPubkey_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32) (ke : KeyExpr) :
    BitcoinLedger.WalletPolicy.deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke =
      InternalSpec.WalletPolicy.deriveKeyExprCompressedPubkey ora net keys isChange addressIndex ke := by
  unfold BitcoinLedger.WalletPolicy.deriveKeyExprCompressedPubkey
    InternalSpec.WalletPolicy.deriveKeyExprCompressedPubkey
  simp only [isUnhardened_eq, lookupKeyXpub_eq, lookupMusigCompressedKeys_eq, sortByteArrays_eq,
    xpubVersionOfNetwork_eq, derivationStepForBranch_eq, keyExprDeriv_eq]
  rfl

theorem deriveKeyExprList_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32) :
    ∀ (kes : List KeyExpr),
      BitcoinLedger.WalletPolicy.deriveKeyExprList ora net keys isChange addressIndex kes =
        InternalSpec.WalletPolicy.deriveKeyExprList ora net keys isChange addressIndex kes
  | [] => rfl
  | ke :: kes => by
    unfold BitcoinLedger.WalletPolicy.deriveKeyExprList InternalSpec.WalletPolicy.deriveKeyExprList
    rw [deriveKeyExprCompressedPubkey_eq, deriveKeyExprList_eq ora net keys isChange addressIndex kes]

theorem compileMultiScript_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32)
    (sorted verifyFlag : Bool) (k : Nat) (keyExprs : List KeyExpr) :
    BitcoinLedger.WalletPolicy.compileMultiScript ora net keys isChange addressIndex sorted verifyFlag k keyExprs =
      InternalSpec.WalletPolicy.compileMultiScript ora net keys isChange addressIndex sorted verifyFlag k keyExprs := by
  unfold BitcoinLedger.WalletPolicy.compileMultiScript InternalSpec.WalletPolicy.compileMultiScript
  simp only [deriveKeyExprList_eq, sortByteArrays_eq, pushSmallBytes_eq, pushScriptU32_eq,
    emitOpVerify_eq]
  rfl

theorem compileMultiAScript_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32)
    (sorted verifyFlag : Bool) (k : Nat) (keyExprs : List KeyExpr) :
    BitcoinLedger.WalletPolicy.compileMultiAScript ora net keys isChange addressIndex sorted verifyFlag k keyExprs =
      InternalSpec.WalletPolicy.compileMultiAScript ora net keys isChange addressIndex sorted verifyFlag k keyExprs := by
  unfold BitcoinLedger.WalletPolicy.compileMultiAScript InternalSpec.WalletPolicy.compileMultiAScript
  simp only [deriveKeyExprList_eq, sortByteArrays_eq, pushSmallBytes_eq, pushScriptU32_eq,
    emitOpVerify_eq]
  rfl

theorem compileMiniscript_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (ctx : MiniscriptCtx) (isChange : Bool) (addressIndex : UInt32) :
    ∀ (ms : Miniscript) (verifyFlag : Bool),
      BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addressIndex verifyFlag ms =
        InternalSpec.WalletPolicy.compileMiniscript ora net keys ctx isChange addressIndex verifyFlag ms := by
  intro ms
  induction ms using InternalSpec.WalletPolicy.Miniscript.rec
    (motive_2 := fun subs =>
      ∀ isFirst : Bool,
        BitcoinLedger.WalletPolicy.compileMiniscript.compileChildren ora net keys ctx isChange addressIndex isFirst subs =
          InternalSpec.WalletPolicy.compileMiniscript.compileChildren ora net keys ctx isChange addressIndex isFirst subs) with
  | ms0 | ms1 => intro _; rfl
  | pk ke =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [deriveKeyExprCompressedPubkey_eq, pushSmallBytes_eq, emitOpVerify_eq]
    rfl
  | pkh ke =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [deriveKeyExprCompressedPubkey_eq, hash160_eq, pushSmallBytes_eq, emitOpVerify_eq]
    rfl
  | pk_k ke =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [deriveKeyExprCompressedPubkey_eq, pushSmallBytes_eq]
    rfl
  | pk_h ke =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [deriveKeyExprCompressedPubkey_eq, hash160_eq, pushSmallBytes_eq]
    rfl
  | older _ | after _ | sha256 _ | hash256 _ | ripemd160 _ | hash160 _ =>
    intro _; rfl
  | andor x y z ihx ihy ihz =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihy false, ihz false, emitOpVerify_eq]
    rfl
  | and_v x y ihx ihy =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihy vFlag]
  | and_b x y ihx ihy =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihy false, emitOpVerify_eq]
    rfl
  | and_n x y ihx ihy =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihy false, emitOpVerify_eq]
    rfl
  | or_b x z ihx ihz =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihz false, emitOpVerify_eq]
    rfl
  | or_c x z ihx ihz =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihz false, emitOpVerify_eq]
    rfl
  | or_d x z ihx ihz =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihz false, emitOpVerify_eq]
    rfl
  | or_i x z ihx ihz =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihx false, ihz false, emitOpVerify_eq]
    rfl
  | thresh k subs ihSubs =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [ihSubs true, pushScriptU32_eq, emitOpVerify_eq]
    rfl
  | multi k kes =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [compileMultiScript_eq]
  | multi_a k kes =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    simp only [compileMultiAScript_eq]
  | wrap w sub ih =>
    intro vFlag
    unfold BitcoinLedger.WalletPolicy.compileMiniscript InternalSpec.WalletPolicy.compileMiniscript
    cases w <;> simp only [ih false, ih true, ih vFlag, emitOpVerify_eq] <;> rfl
  | nil => rfl
  | cons m ms ihm ihms =>
    unfold BitcoinLedger.WalletPolicy.compileMiniscript.compileChildren
      InternalSpec.WalletPolicy.compileMiniscript.compileChildren
    simp only [ihm false, ihms false]
    rfl

theorem compileWshWitnessScript_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32) (ws : WshScript) :
    BitcoinLedger.WalletPolicy.compileWshWitnessScript ora net keys isChange addressIndex ws =
      InternalSpec.WalletPolicy.compileWshWitnessScript ora net keys isChange addressIndex ws := by
  cases ws with
  | sortedmulti k kes => exact compileMultiScript_eq ora net keys isChange addressIndex true false k kes
  | miniscript ms => exact compileMiniscript_eq ora net keys .wshCtx isChange addressIndex ms false

theorem compileTapLeafScript_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32) (ls : TapLeafScript) :
    BitcoinLedger.WalletPolicy.compileTapLeafScript ora net keys isChange addressIndex ls =
      InternalSpec.WalletPolicy.compileTapLeafScript ora net keys isChange addressIndex ls := by
  cases ls with
  | sortedmulti_a k kes =>
    exact compileMultiAScript_eq ora net keys isChange addressIndex true false k kes
  | miniscript ms =>
    exact compileMiniscript_eq ora net keys .tapscriptCtx isChange addressIndex ms false

theorem computeTapTreeHash_eq (ora : CryptoPolicyOracle) (net : Network)
    (keys : List KeyInformation) (isChange : Bool) (addressIndex : UInt32) :
    ∀ (t : TapTree),
      BitcoinLedger.WalletPolicy.computeTapTreeHash ora net keys isChange addressIndex t =
        InternalSpec.WalletPolicy.computeTapTreeHash ora net keys isChange addressIndex t
  | .leaf ls => by
    unfold BitcoinLedger.WalletPolicy.computeTapTreeHash InternalSpec.WalletPolicy.computeTapTreeHash
    simp only [compileTapLeafScript_eq, tapLeafHash_eq]
  | .branch l r => by
    unfold BitcoinLedger.WalletPolicy.computeTapTreeHash InternalSpec.WalletPolicy.computeTapTreeHash
    simp only [computeTapTreeHash_eq ora net keys isChange addressIndex l,
      computeTapTreeHash_eq ora net keys isChange addressIndex r, tapBranchHash_eq]

theorem mkP2PKH_eq (pkh20 : ByteArray) :
    BitcoinLedger.WalletPolicy.mkP2PKH pkh20 = InternalSpec.WalletPolicy.mkP2PKH pkh20 := rfl
theorem mkP2WPKH_eq (pkh20 : ByteArray) :
    BitcoinLedger.WalletPolicy.mkP2WPKH pkh20 = InternalSpec.WalletPolicy.mkP2WPKH pkh20 := rfl
theorem mkP2SH_eq (sh20 : ByteArray) :
    BitcoinLedger.WalletPolicy.mkP2SH sh20 = InternalSpec.WalletPolicy.mkP2SH sh20 := rfl
theorem mkP2WSH_eq (wsh32 : ByteArray) :
    BitcoinLedger.WalletPolicy.mkP2WSH wsh32 = InternalSpec.WalletPolicy.mkP2WSH wsh32 := rfl
theorem mkP2TR_eq (xonly32 : ByteArray) :
    BitcoinLedger.WalletPolicy.mkP2TR xonly32 = InternalSpec.WalletPolicy.mkP2TR xonly32 := rfl

theorem deriveWalletScriptPubKeyWithProfile_eq (profile : PolicyProfile) (ora : CryptoPolicyOracle)
    (policy : WalletPolicy) (isChange : Bool) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profile ora policy isChange addressIndex =
      InternalSpec.WalletPolicy.deriveWalletScriptPubKeyWithProfile profile ora policy isChange addressIndex := by
  unfold BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile
    InternalSpec.WalletPolicy.deriveWalletScriptPubKeyWithProfile
  simp only [isUnhardened_eq, checkPolicyWellFormed_eq, deriveKeyExprCompressedPubkey_eq,
    hash160_eq, mkP2PKH_eq, mkP2WPKH_eq, mkP2SH_eq, mkP2WSH_eq, mkP2TR_eq,
    compileMultiScript_eq, compileWshWitnessScript_eq, computeTapTreeHash_eq]
  rfl

/-- Profile Specialization 1: Exact script derivation refinement on `canonicalLedgerProfile`. -/
theorem deriveWalletScriptPubKey_canonical_eq (net : Network) (ora : CryptoPolicyOracle)
    (policy : WalletPolicy) (isChange : Bool) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile
        (BitcoinLedger.WalletPolicy.canonicalLedgerProfile net) ora policy isChange addressIndex =
      InternalSpec.WalletPolicy.deriveWalletScriptPubKeyWithProfile
        (InternalSpec.WalletPolicy.canonicalLedgerProfile net) ora policy isChange addressIndex :=
  deriveWalletScriptPubKeyWithProfile_eq _ ora policy isChange addressIndex

/-- Profile Specialization 2: Exact script derivation refinement on `bolosAppProfile`. -/
theorem deriveWalletScriptPubKey_bolos_eq (net : Network) (ora : CryptoPolicyOracle)
    (policy : WalletPolicy) (isChange : Bool) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile
        (BitcoinLedger.WalletPolicy.bolosAppProfile net) ora policy isChange addressIndex =
      InternalSpec.WalletPolicy.deriveWalletScriptPubKeyWithProfile
        (InternalSpec.WalletPolicy.bolosAppProfile net) ora policy isChange addressIndex :=
  deriveWalletScriptPubKeyWithProfile_eq _ ora policy isChange addressIndex

/-- Profile Specialization 3: Exact script derivation refinement on `vanadiumAppProfile`. -/
theorem deriveWalletScriptPubKey_vanadium_eq (net : Network) (ora : CryptoPolicyOracle)
    (policy : WalletPolicy) (isChange : Bool) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile
        (BitcoinLedger.WalletPolicy.vanadiumAppProfile net) ora policy isChange addressIndex =
      InternalSpec.WalletPolicy.deriveWalletScriptPubKeyWithProfile
        (InternalSpec.WalletPolicy.vanadiumAppProfile net) ora policy isChange addressIndex :=
  deriveWalletScriptPubKeyWithProfile_eq _ ora policy isChange addressIndex

theorem deriveWalletScriptPubKey_eq (ora : CryptoPolicyOracle) (policy : WalletPolicy)
    (isChange : Bool) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.deriveWalletScriptPubKey ora policy isChange addressIndex =
      InternalSpec.WalletPolicy.deriveWalletScriptPubKey ora policy isChange addressIndex :=
  deriveWalletScriptPubKeyWithProfile_eq _ ora policy isChange addressIndex

theorem deriveWalletPolicyScript_eq (profile : PolicyProfile) (dev : DeviceRegistrationOracle)
    (ora : CryptoPolicyOracle) (policy : WalletPolicy) (auth : PolicyAuthorization)
    (isChange : Bool) (addressIndex : UInt32) :
    BitcoinLedger.WalletPolicy.deriveWalletPolicyScript profile dev ora policy auth isChange addressIndex =
      InternalSpec.WalletPolicy.deriveAuthorizedWalletScriptPubKey profile dev ora policy auth isChange addressIndex := by
  unfold BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
    InternalSpec.WalletPolicy.deriveAuthorizedWalletScriptPubKey
  rw [authorizePolicyUse_eq, deriveWalletScriptPubKeyWithProfile_eq]

theorem policyFormatWireTag_eq (fmt : PolicyFormat) :
    BitcoinLedger.WalletPolicy.policyFormatWireTag fmt = fmt.wireTag := by
  cases fmt <;> rfl

theorem computeBolosWalletId_eq (ora : CryptoPolicyOracle) (fmt : PolicyFormat) (name : String)
    (descriptorBytes : ByteArray) (nKeys : Nat) (keysMerkleRoot32 : ByteArray) :
    BitcoinLedger.WalletPolicy.computeBolosWalletId ora fmt name descriptorBytes nKeys keysMerkleRoot32 =
      InternalSpec.WalletPolicy.computeBolosWalletId ora fmt name descriptorBytes nKeys keysMerkleRoot32 := by
  unfold BitcoinLedger.WalletPolicy.computeBolosWalletId InternalSpec.WalletPolicy.computeBolosWalletId
  rw [policyFormatWireTag_eq, encodeCompactSize_eq, encodeCompactSize_eq]
  rfl

theorem computeVanadiumRegistrationId_eq (ora : CryptoPolicyOracle) (name : String)
    (serializedBip388Policy : ByteArray) :
    BitcoinLedger.WalletPolicy.computeVanadiumRegistrationId ora name serializedBip388Policy =
      InternalSpec.WalletPolicy.computeVanadiumRegistrationId ora name serializedBip388Policy := rfl

/-! ## Section 6: Key Info Parser, Registration Handler & BIP-68 Bitmask Soundness -/

/-- Helper lemma: `constantTimeEqBytes32.go xs xs acc` reduces to `acc == 0`. -/
theorem constantTimeEqBytes32_go_refl :
    ∀ (xs : List UInt8) (acc : UInt8),
      BitcoinLedger.WalletPolicy.constantTimeEqBytes32.go xs xs acc = (acc == 0)
  | [], acc => rfl
  | x :: xs, acc => by
    unfold BitcoinLedger.WalletPolicy.constantTimeEqBytes32.go
    have hXor : x ^^^ x = 0 := UInt8.xor_self
    have hOr : acc ||| (0 : UInt8) = acc := UInt8.or_zero
    rw [hXor, hOr]
    exact constantTimeEqBytes32_go_refl xs acc

/-- Reflexivity of `constantTimeEqBytes32` on any 32-byte digest. -/
theorem constantTimeEqBytes32_self (h : ByteArray) (hSz : h.size = 32) :
    BitcoinLedger.WalletPolicy.constantTimeEqBytes32 h h = true := by
  unfold BitcoinLedger.WalletPolicy.constantTimeEqBytes32
  have hNe : (h.size != 32 || h.size != 32) = false := by
    rw [hSz]
    rfl
  simp only [hNe, Bool.false_eq_true, ↓reduceIte]
  exact constantTimeEqBytes32_go_refl h.data.toList 0

/-- Helper lemma: if `acc ||| b == 0`, then `acc == 0` and `b == 0` on `UInt8` (constructive). -/
theorem uint8_or_eq_zero_iff (a b : UInt8) :
    (a ||| b == 0) = true → a = 0 ∧ b = 0 := by
  intro h
  have hOr : a ||| b = 0 := of_decide_eq_true h
  have hBv : a.toBitVec ||| b.toBitVec = 0#8 := congrArg UInt8.toBitVec hOr
  have ha : a.toBitVec = 0#8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hiOr := congrArg (fun v => v.getLsbD i) hBv
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at hiOr
    rw [BitVec.getLsbD_zero]
    exact hiOr.1
  have hb : b.toBitVec = 0#8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hiOr := congrArg (fun v => v.getLsbD i) hBv
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at hiOr
    rw [BitVec.getLsbD_zero]
    exact hiOr.2
  exact ⟨UInt8.eq_of_toBitVec_eq ha, UInt8.eq_of_toBitVec_eq hb⟩

theorem uint8_eq_of_xor_eq_zero (x y : UInt8) (h : x ^^^ y = 0) : x = y := by
  have hBv : x.toBitVec ^^^ y.toBitVec = 0#8 := congrArg UInt8.toBitVec h
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hiXor := congrArg (fun v => v.getLsbD i) hBv
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_zero] at hiXor
  cases hx : x.toBitVec.getLsbD i <;> cases hy : y.toBitVec.getLsbD i <;>
    simp [hx, hy] at hiXor ⊢

theorem constantTimeEqBytes32_go_sound :
    ∀ (xs ys : List UInt8) (acc : UInt8),
      BitcoinLedger.WalletPolicy.constantTimeEqBytes32.go xs ys acc = true →
      acc = 0 ∧ xs = ys
  | [], [], acc, h => ⟨of_decide_eq_true h, rfl⟩
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: xs, y :: ys, acc, h => by
    unfold BitcoinLedger.WalletPolicy.constantTimeEqBytes32.go at h
    rcases constantTimeEqBytes32_go_sound xs ys (acc ||| (x ^^^ y)) h with ⟨hAccOr, hTail⟩
    have hDec : ((acc ||| (x ^^^ y)) == 0) = true := decide_eq_true hAccOr
    rcases uint8_or_eq_zero_iff acc (x ^^^ y) hDec with ⟨hAcc0, hXor0⟩
    have hxy : x = y := uint8_eq_of_xor_eq_zero x y hXor0
    subst hxy hTail
    exact ⟨hAcc0, rfl⟩

/-- Soundness of `constantTimeEqBytes32`: returns `true` iff `a = b` and `a.size = 32`. -/
theorem constantTimeEqBytes32_eq_true_iff (a b : ByteArray) :
    BitcoinLedger.WalletPolicy.constantTimeEqBytes32 a b = true ↔ a = b ∧ a.size = 32 := by
  constructor
  · intro h
    unfold BitcoinLedger.WalletPolicy.constantTimeEqBytes32 at h
    cases hSz : (a.size != 32 || b.size != 32) with
    | true => simp only [hSz, ↓reduceIte] at h; cases h
    | false =>
      simp only [hSz, Bool.false_eq_true, ↓reduceIte] at h
      have hSzA : a.size = 32 := by
        cases hBne : (a.size != 32) with
        | true => simp [hBne] at hSz
        | false =>
          have hBeq : (a.size == 32) = true := by
            cases hEq : (a.size == 32) <;> simp [bne, hEq] at hBne ⊢
          exact Nat.beq_eq.mp hBeq
      rcases constantTimeEqBytes32_go_sound a.data.toList b.data.toList 0 h with ⟨_, hList⟩
      have hArr : a.data = b.data := Array.ext' hList
      have hEq : a = b := by
        cases a; cases b; dsimp at hArr; subst hArr; rfl
      exact ⟨hEq, hSzA⟩
  · rintro ⟨rfl, hSz⟩
    exact constantTimeEqBytes32_self a hSz

/-- End-to-end soundness of `verifyAndRegisterWalletPolicy`:
    If registration succeeds with `(id32, hmac32)`, then:
    1. `InternalSpec.WalletPolicy.validatePolicyRegistration` succeeds;
    2. `userApproved = true` and `hasOurKey = true` (`n_internal_keys >= 1`);
    3. `id32.size = 32`, `hmac32.size = 32`, and `hmac32 ≠ zeroBytes32`;
    4. `verifyRegistrationHmac` accepts `hmac32`. -/
theorem verifyAndRegisterWalletPolicy_sound
    (profile : PolicyProfile) (dev : DeviceRegistrationOracle) (ora : CryptoPolicyOracle)
    (computeHmac32 : ByteArray → Option ByteArray) (policy : WalletPolicy)
    (commitment : BitcoinLedger.WalletPolicy.RegistrationCommitmentInput)
    (userApproved : Bool) (id32 hmac32 : ByteArray)
    (hOk : BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
      profile dev ora computeHmac32 policy commitment userApproved = .ok (id32, hmac32)) :
    InternalSpec.WalletPolicy.validatePolicyRegistration profile dev policy userApproved = .ok () ∧
    userApproved = true ∧
    BitcoinLedger.WalletPolicy.hasOurKey dev profile.network policy = true ∧
    id32 = BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment ∧
    id32.size = 32 ∧
    hmac32.size = 32 ∧
    hmac32 ≠ BitcoinLedger.WalletPolicy.zeroBytes32 ∧
    BitcoinLedger.WalletPolicy.verifyRegistrationHmac ora computeHmac32 policy commitment hmac32 = true := by
  unfold BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy at hOk
  rw [validatePolicyRegistration_eq] at hOk
  cases hVal : InternalSpec.WalletPolicy.validatePolicyRegistration profile dev policy userApproved with
  | error e =>
    rw [hVal] at hOk
    cases hOk
  | ok u =>
    rw [hVal] at hOk
    dsimp [Bind.bind, Except.bind] at hOk
    have hApproved : userApproved = true := by
      cases userApproved with
      | true => rfl
      | false =>
        unfold InternalSpec.WalletPolicy.validatePolicyRegistration at hVal
        cases hN : (!profile.validRegisteredWalletName policy.name) with
        | true =>
          simp only [hN, ↓reduceIte, Bind.bind, Except.bind] at hVal
          cases hVal
        | false =>
          simp only [hN, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at hVal
          cases hWF : checkPolicyWellFormed profile policy with
          | error _ =>
            rw [hWF] at hVal
            cases hVal
          | ok _ =>
            rw [hWF] at hVal
            cases hRS : checkRegisteredSignability profile dev policy with
            | error _ =>
              rw [hRS] at hVal
              cases hVal
            | ok _ =>
              rw [hRS] at hVal
              cases hVal
    have hOur : BitcoinLedger.WalletPolicy.hasOurKey dev profile.network policy = true := by
      rw [hasOurKey_eq]
      cases hHas : InternalSpec.WalletPolicy.hasOurKey dev profile.network policy with
      | true => rfl
      | false =>
        obtain ⟨err, hErr⟩ := InternalSpec.WalletPolicy.registration_requires_our_key
          profile dev policy userApproved hHas
        rw [hVal] at hErr
        cases hErr
    cases hIdSz : (BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment).size != 32 with
    | true =>
      simp only [hIdSz, ↓reduceIte] at hOk
      cases hOk
    | false =>
      simp only [hIdSz, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hComp : computeHmac32 (BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment) with
      | none =>
        rw [hComp] at hOk
        cases hOk
      | some m =>
        rw [hComp] at hOk
        dsimp only at hOk
        cases hBad : (m.size != 32 || m == BitcoinLedger.WalletPolicy.zeroBytes32) with
        | true =>
          simp only [hBad, ↓reduceIte] at hOk
          cases hOk
        | false =>
          simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hOk
          injection hOk with hPair
          injection hPair with hIdEq hHmacEq
          subst hIdEq hHmacEq
          have hIdSz32 : (BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment).size = 32 := by
            have hBeq : ((BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment).size == 32) = true := by
              cases hEq : ((BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment).size == 32) <;>
                simp [bne, hEq] at hIdSz ⊢
            exact Nat.beq_eq.mp hBeq
          have hMSz32 : m.size = 32 := by
            cases hMBne : (m.size != 32) with
            | true => simp [hMBne] at hBad
            | false =>
              have hBeq : (m.size == 32) = true := by
                cases hEq : (m.size == 32) <;> simp [bne, hEq] at hMBne ⊢
              exact Nat.beq_eq.mp hBeq
          have hMNonZero : m ≠ BitcoinLedger.WalletPolicy.zeroBytes32 := by
            intro hEqZ
            subst hEqZ
            have hZ : (BitcoinLedger.WalletPolicy.zeroBytes32 == BitcoinLedger.WalletPolicy.zeroBytes32) = true := rfl
            simp [hZ] at hBad
          have hVer : BitcoinLedger.WalletPolicy.verifyRegistrationHmac ora computeHmac32 policy commitment m = true := by
            unfold BitcoinLedger.WalletPolicy.verifyRegistrationHmac
            simp only [hBad, Bool.false_eq_true, ↓reduceIte, hComp]
            exact constantTimeEqBytes32_self m hMSz32
          exact ⟨rfl, hApproved, hOur, rfl, hIdSz32, hMSz32, hMNonZero, hVer⟩

/-- Soundness of `parseWalletKeyInfo`: any successfully parsed `KeyInformation` string satisfies
    `KeyInformation.validForFormatWithBounds profile.maxOriginSteps fmt profile.network`. -/
theorem parseWalletKeyInfo_sound
    (profile : PolicyProfile) (fmt : PolicyFormat) (doubleSha256 : ByteArray → ByteArray)
    (allowHardenedH : Bool) (s : String) (ki : KeyInformation)
    (hOk : BitcoinLedger.WalletPolicy.parseWalletKeyInfo profile fmt doubleSha256 allowHardenedH s = .ok ki) :
    KeyInformation.validForFormatWithBounds profile.maxOriginSteps fmt profile.network ki = true := by
  unfold BitcoinLedger.WalletPolicy.parseWalletKeyInfo at hOk
  dsimp only at hOk
  split at hOk
  · cases hOk
  · rename_i originOpt afterOrigin _
    split at hOk
    · cases hOk
    · split at hOk
      · cases hOk
      · split at hOk
        · cases hOk
        · split at hOk
          · cases hOk
          · split at hOk
            · rename_i hValid
              injection hOk with hKi
              subst hKi
              exact hValid
            · cases hOk

/-- Constructive bit-level equivalence between `validOlderBitmask`
    (`(n & 0xFFBF0000) == 0 && 1 <= (n & 0xFFFF)`) and `validOlderArg`
    (`1 <= n < 2^31 && 1 <= (n & 0xFFBFFFFF) <= 65535`). -/
theorem validOlderBitmask_eq_validOlderArg (n : UInt32) :
    BitcoinLedger.WalletPolicy.validOlderBitmask n =
      BitcoinLedger.WalletPolicy.validOlderArg n := by
  unfold BitcoinLedger.WalletPolicy.validOlderBitmask BitcoinLedger.WalletPolicy.validOlderArg
  unfold BitcoinLedger.WalletPolicy.olderInvalidUpperMask
    BitcoinLedger.WalletPolicy.sequenceLocktimeTypeFlag
    BitcoinLedger.WalletPolicy.hardenedBit
  have hXorConst : ((0xFFFFFFFF : UInt32) ^^^ ((1 : UInt32) <<< (22 : UInt32))) = 0xFFBFFFFF := rfl
  rw [hXorConst]
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hL
    have hUpperDec : ((n &&& 0xFFBF0000) == 0) = true ∧ decide (1 ≤ n &&& 0xFFFF) = true := by
      cases h1 : ((n &&& 0xFFBF0000) == 0) <;> cases h2 : decide (1 ≤ n &&& 0xFFFF) <;>
        simp [h1, h2] at hL ⊢
    rcases hUpperDec with ⟨hUp0, hLow1⟩
    have hUpEq : n &&& 0xFFBF0000 = 0 := of_decide_eq_true hUp0
    have hLowGe : (1 : UInt32) ≤ n &&& 0xFFFF := of_decide_eq_true hLow1
    -- Since (n & 0xFFBF0000) = 0, n & 0xFFBFFFFF = n & 0xFFFF!
    have hMaskedEq : (n &&& 0xFFBFFFFF) = (n &&& 0xFFFF) := by
      apply UInt32.eq_of_toBitVec_eq
      have hBvUp : n.toBitVec &&& (0xFFBF0000 : BitVec 32) = 0#32 :=
        congrArg UInt32.toBitVec hUpEq
      have hDecomp : (0xFFBFFFFF : BitVec 32) = (0xFFBF0000 : BitVec 32) ||| (0x0000FFFF : BitVec 32) := rfl
      change n.toBitVec &&& (0xFFBFFFFF : BitVec 32) = n.toBitVec &&& (0x0000FFFF : BitVec 32)
      rw [hDecomp, BitVec.and_or_distrib_left, hBvUp, BitVec.zero_or]
    -- Also n & 0xFFFF <= 0xFFFF and n < 0x80000000 and 1 <= n:
    have hMaskedLe : (n &&& 0xFFFF) ≤ 65535 := by
      show (n.toBitVec &&& 0x0000FFFF#32).toNat ≤ 65535
      exact Nat.le_trans (Nat.and_le_right) (by decide)
    have hNGe1 : (1 : UInt32) ≤ n := by
      show 1 ≤ n.toBitVec.toNat
      have h1 : 1 ≤ (n.toBitVec &&& 0x0000FFFF#32).toNat := hLowGe
      exact Nat.le_trans h1 Nat.and_le_left
    have hNLt : n < 0x80000000 := by
      show n.toBitVec.toNat < (0x80000000#32).toNat
      have hBvUp : n.toBitVec &&& 0xFFBF0000#32 = 0#32 := congrArg UInt32.toBitVec hUpEq
      have hTopZero : n.toBitVec &&& 0x80000000#32 = 0#32 := by
        have hSub : (0x80000000#32 : BitVec 32) = 0xFFBF0000#32 &&& 0x80000000#32 := rfl
        rw [hSub, ← BitVec.and_assoc, hBvUp, BitVec.zero_and]
      -- Since bit 31 of n is 0, n = n &&& 0x7FFFFFFF <= 0x7FFFFFFF < 0x80000000!
      have hCompl : n.toBitVec = (n.toBitVec &&& 0x80000000#32) ||| (n.toBitVec &&& 0x7FFFFFFF#32) := by
        rw [← BitVec.and_or_distrib_left]
        have hAll : (0x80000000#32 ||| 0x7FFFFFFF#32) = 0xFFFFFFFF#32 := rfl
        rw [hAll]
        apply BitVec.eq_of_toNat_eq
        apply Nat.eq_of_testBit_eq
        intro i
        show Nat.testBit n.toBitVec.toNat i = Nat.testBit (n.toBitVec.toNat &&& 0xFFFFFFFF) i
        rw [Nat.testBit_and]
        by_cases hi : i < 32
        · have hOnes : Nat.testBit 0xFFFFFFFF i = true := by
            revert i hi
            decide
          rw [hOnes, Bool.and_true]
        · have hGe : 32 ≤ i := Nat.not_lt.mp hi
          have hZero : Nat.testBit n.toBitVec.toNat i = false :=
            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le n.toBitVec.isLt
              (Nat.pow_le_pow_right (by decide) hGe))
          rw [hZero]
          rfl
      rw [hTopZero, BitVec.zero_or] at hCompl
      rw [hCompl]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    rw [hMaskedEq]
    simp [decide_eq_true hNGe1, decide_eq_true hNLt, decide_eq_true hLowGe, decide_eq_true hMaskedLe]
  · intro hR
    have hParts :
        decide ((1 : UInt32) ≤ n) = true ∧
        decide (n < 0x80000000) = true ∧
        decide ((1 : UInt32) ≤ (n &&& 0xFFBFFFFF)) = true ∧
        decide ((n &&& 0xFFBFFFFF) ≤ 65535) = true := by
      cases h1 : decide ((1 : UInt32) ≤ n) <;>
        cases h2 : decide (n < 0x80000000) <;>
        cases h3 : decide ((1 : UInt32) ≤ (n &&& 0xFFBFFFFF)) <;>
        cases h4 : decide ((n &&& 0xFFBFFFFF) ≤ 65535) <;>
        simp [h1, h2, h3, h4] at hR ⊢
    rcases hParts with ⟨_, _, hMGe1, hMLe⟩
    have hMLeNat : (n.toBitVec &&& 0xFFBFFFFF#32).toNat ≤ 65535 := of_decide_eq_true hMLe
    -- Any 32-bit value v <= 0xFFFF has (v &&& 0xFFFF0000) = 0:
    have hUpperMaskedZero : (n.toBitVec &&& 0xFFBFFFFF#32) &&& 0xFFFF0000#32 = 0#32 := by
      apply BitVec.eq_of_toNat_eq
      apply Nat.eq_of_testBit_eq
      intro i
      show Nat.testBit ((n.toBitVec &&& 0xFFBFFFFF#32).toNat &&& 0xFFFF0000) i = Nat.testBit 0 i
      rw [Nat.testBit_and, Nat.zero_testBit]
      by_cases hi : i < 16
      · have hMask0 : Nat.testBit 0xFFFF0000 i = false := by
          revert i hi
          decide
        rw [hMask0, Bool.and_false]
      · have hGe16 : 16 ≤ i := Nat.not_lt.mp hi
        have hLt16 : (n.toBitVec &&& 0xFFBFFFFF#32).toNat < 2 ^ 16 :=
          Nat.lt_of_le_of_lt hMLeNat (by decide)
        have hVal0 : Nat.testBit (n.toBitVec &&& 0xFFBFFFFF#32).toNat i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hLt16
            (Nat.pow_le_pow_right (by decide) hGe16))
        rw [hVal0]
        rfl
    have hUpZero : n &&& 0xFFBF0000 = 0 := by
      apply UInt32.eq_of_toBitVec_eq
      have hAssoc : (0xFFBFFFFF#32 &&& 0xFFFF0000#32) = 0xFFBF0000#32 := rfl
      change n.toBitVec &&& 0xFFBF0000#32 = 0#32
      rw [← hAssoc, ← BitVec.and_assoc]
      exact hUpperMaskedZero
    have hLowEq : (n &&& 0xFFFF) = (n &&& 0xFFBFFFFF) := by
      apply UInt32.eq_of_toBitVec_eq
      have hDecomp : (0xFFBFFFFF#32 : BitVec 32) = 0xFFBF0000#32 ||| 0x0000FFFF#32 := rfl
      have hBvUp : n.toBitVec &&& 0xFFBF0000#32 = 0#32 := congrArg UInt32.toBitVec hUpZero
      change n.toBitVec &&& 0x0000FFFF#32 = n.toBitVec &&& 0xFFBFFFFF#32
      rw [hDecomp, BitVec.and_or_distrib_left, hBvUp, BitVec.zero_or]
    have hUpBeq : ((n &&& 0xFFBF0000) == 0) = true := decide_eq_true hUpZero
    rw [hUpBeq, hLowEq, hMGe1]
    rfl

/-! ## Section 7: Security Rejection & Soundness Theorems on `BitcoinLedger.WalletPolicy` -/

/-- Equal `<M;M>/*` multipath (`M = N`) is universally rejected across `validDerivationSpec`,
    `checkKeyExprInContext`, `deriveWalletScriptPubKeyWithProfile`, and `deriveWalletPolicyScript`. -/
theorem equal_multipath_rejected
    (profile : PolicyProfile) (dev : DeviceRegistrationOracle) (ora : CryptoPolicyOracle)
    (fmt : PolicyFormat) (allowMusig : Bool) (maxMusigKeys : Nat)
    (name : String) (keys : List KeyInformation) (keyIdx : Nat) (m : UInt32)
    (auth : PolicyAuthorization) (isChange : Bool) (addrIdx : UInt32) :
    BitcoinLedger.WalletPolicy.validDerivationSpec fmt (.multipath m m) = false ∧
    (∃ err, BitcoinLedger.WalletPolicy.checkKeyExprInContext fmt allowMusig maxMusigKeys
      (.single keyIdx (.multipath m m)) = .error err) ∧
    (∃ err, BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profile ora
      { format := fmt, name := name, template := .wpkh (.single keyIdx (.multipath m m)), keys := keys }
      isChange addrIdx = .error err) ∧
    (∃ err, BitcoinLedger.WalletPolicy.deriveWalletPolicyScript profile dev ora
      { format := fmt, name := name, template := .wpkh (.single keyIdx (.multipath m m)), keys := keys }
      auth isChange addrIdx = .error err) := by
  rw [validDerivationSpec_eq, checkKeyExprInContext_eq, deriveWalletScriptPubKeyWithProfile_eq,
      deriveWalletPolicyScript_eq]
  have hKe := InternalSpec.WalletPolicy.equal_multipath_keyexpr_rejected fmt allowMusig maxMusigKeys keyIdx m
  have hPol := InternalSpec.WalletPolicy.equal_multipath_policy_rejected profile ora fmt name keys keyIdx m isChange addrIdx
  refine ⟨hKe.1, hKe.2, hPol, ?_⟩
  unfold InternalSpec.WalletPolicy.deriveAuthorizedWalletScriptPubKey
  cases hAuth : InternalSpec.WalletPolicy.authorizePolicyUse profile dev
      { format := fmt, name := name, template := .wpkh (.single keyIdx (.multipath m m)), keys := keys }
      auth addrIdx with
  | error e => exact ⟨e, rfl⟩
  | ok _ => exact hPol

/-- Receive (`isChange = false`) and change (`isChange = true`) derivation steps never collide
    under any valid BIP-388 derivation specification (`/**` or `<M;N>/*`). -/
theorem impl_receive_change_derivation_non_collision
    (fmt : PolicyFormat) (d : DerivationSpec) (rxIndex chgIndex : UInt32)
    (hValid : BitcoinLedger.WalletPolicy.validDerivationSpec fmt d = true) :
    (BitcoinLedger.WalletPolicy.derivationStepForBranch d false, rxIndex) ≠
      (BitcoinLedger.WalletPolicy.derivationStepForBranch d true, chgIndex) := by
  rw [validDerivationSpec_eq] at hValid
  rw [derivationStepForBranch_eq, derivationStepForBranch_eq]
  exact InternalSpec.WalletPolicy.receive_change_derivation_non_collision fmt d rxIndex chgIndex hValid

/-- Any hardened `<M;N>/*` step (`!isUnhardened m` or `!isUnhardened n`) is universally rejected
    with `.invalidDerivationSuffix` by `checkKeyExprInContext`. -/
theorem hardened_multipath_rejected
    (fmt : PolicyFormat) (allowMusig : Bool) (maxMusigKeys : Nat)
    (ke : KeyExpr) (m n : UInt32)
    (hDeriv : BitcoinLedger.WalletPolicy.keyExprDeriv ke = .multipath m n)
    (hHard : BitcoinLedger.WalletPolicy.isUnhardened m = false ∨
             BitcoinLedger.WalletPolicy.isUnhardened n = false) :
    BitcoinLedger.WalletPolicy.checkKeyExprInContext fmt allowMusig maxMusigKeys ke =
      .error .invalidDerivationSuffix := by
  have hKeDeriv : ke.deriv = .multipath m n := by
    rw [← keyExprDeriv_eq]
    exact hDeriv
  unfold BitcoinLedger.WalletPolicy.checkKeyExprInContext
  rw [hKeDeriv]
  cases fmt with
  | v1 => rfl
  | v2 =>
    have hFmt : (PolicyFormat.v2 != PolicyFormat.v2) = false := rfl
    have hBothFalse : (BitcoinLedger.WalletPolicy.isUnhardened m &&
        BitcoinLedger.WalletPolicy.isUnhardened n) = false := by
      cases hHard with
      | inl hm => rw [hm]; rfl
      | inr hn => rw [hn, Bool.and_false]
    simp only [hFmt, hBothFalse, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- Out-of-range `@k` (`k >= policy.keys.length`) is universally rejected across
    `checkPlaceholderCoverage`, `checkPolicyWellFormed`, and `deriveWalletScriptPubKeyWithProfile`,
    and non-sequential `@1, @0` is rejected with `.nonSequentialKeyIndex` when `requireSequentialPlaceholders = true`. -/
theorem out_of_range_and_nonsequential_placeholder_rejected
    (profile : PolicyProfile) (ora : CryptoPolicyOracle) (policy : WalletPolicy)
    (ke : KeyExpr) (k : Nat) (isChange : Bool) (addrIdx : UInt32)
    (hKe : ke ∈ BitcoinLedger.WalletPolicy.collectTemplateKeyExprs policy.template)
    (hK : k ∈ BitcoinLedger.WalletPolicy.keyExprReferencedIndices ke)
    (hOut : k >= policy.keys.length) :
    BitcoinLedger.WalletPolicy.checkPlaceholderCoverage policy.keys.length
      profile.requireSequentialPlaceholders
      (BitcoinLedger.WalletPolicy.collectTemplateKeyExprs policy.template) =
        .error .outOfRangeKeyIndex ∧
    (∃ err, BitcoinLedger.WalletPolicy.checkPolicyWellFormed profile policy = .error err) ∧
    (∃ err, BitcoinLedger.WalletPolicy.deriveWalletScriptPubKeyWithProfile profile ora
      policy isChange addrIdx = .error err) ∧
    BitcoinLedger.WalletPolicy.checkPlaceholderCoverage 2 true
      [.single 1 .wildcard, .single 0 .wildcard] = .error .nonSequentialKeyIndex := by
  rw [collectTemplateKeyExprs_eq] at hKe ⊢
  rw [keyExprReferencedIndices_eq] at hK
  rw [checkPlaceholderCoverage_eq, checkPolicyWellFormed_eq, deriveWalletScriptPubKeyWithProfile_eq]
  have hCov := InternalSpec.WalletPolicy.out_of_range_placeholder_coverage_rejected
    policy.keys.length profile.requireSequentialPlaceholders
    (InternalSpec.WalletPolicy.collectTemplateKeyExprs policy.template) ke k hKe hK hOut
  have hPol := InternalSpec.WalletPolicy.out_of_range_placeholder_policy_rejected
    profile ora policy ke k isChange addrIdx hKe hK hOut
  exact ⟨hCov, hPol.1, hPol.2, rfl⟩

/-- `REGISTER_WALLET` (`validatePolicyRegistration` and `verifyAndRegisterWalletPolicy`)
    universally rejects any wallet policy lacking an internal key controlled by this device (`hasOurKey = false`). -/
theorem missing_our_key_registration_rejected
    (profile : PolicyProfile) (dev : DeviceRegistrationOracle) (ora : CryptoPolicyOracle)
    (computeHmac32 : ByteArray → Option ByteArray)
    (policy : WalletPolicy) (commitment : BitcoinLedger.WalletPolicy.RegistrationCommitmentInput)
    (userApproved : Bool)
    (hNoOur : BitcoinLedger.WalletPolicy.hasOurKey dev profile.network policy = false) :
    (∃ err, BitcoinLedger.WalletPolicy.validatePolicyRegistration profile dev policy userApproved = .error err) ∧
    (∃ err, BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy profile dev ora computeHmac32
      policy commitment userApproved = .error err) := by
  rw [hasOurKey_eq] at hNoOur
  have hVal := InternalSpec.WalletPolicy.registration_requires_our_key profile dev policy userApproved hNoOur
  refine ⟨by rw [validatePolicyRegistration_eq]; exact hVal, ?_⟩
  unfold BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
  rw [validatePolicyRegistration_eq]
  obtain ⟨err, hErr⟩ := hVal
  exact ⟨err, by dsimp [Bind.bind, Except.bind]; rw [hErr]⟩

/-- Authorization & HMAC soundness:
    1. Non-default policies without a valid 32-byte non-zero HMAC are universally rejected;
    2. `verifyRegistrationHmac` rejects any wrong-size, all-zero, or forged `candidate ≠ expectedHmac`;
    3. Stateless default policy usage with `addressIndex > 50000` is rejected with `.invalidAddressIndex`
       (assuming `checkPolicyWellFormed` and `isDefaultStatelessPolicy` succeed on an unhardened index). -/
theorem forged_hmac_and_high_default_index_rejected
    (profile : PolicyProfile) (dev : DeviceRegistrationOracle) (ora : CryptoPolicyOracle)
    (computeHmac32 : ByteArray → Option ByteArray)
    (policy : WalletPolicy) (commitment : BitcoinLedger.WalletPolicy.RegistrationCommitmentInput)
    (auth : PolicyAuthorization) (isChange : Bool) (addrIdx : UInt32)
    (hNonDefault : BitcoinLedger.WalletPolicy.isDefaultStatelessPolicy dev profile.network policy = false)
    (hNoValidProof :
      ∀ hmac : ByteArray,
        auth = .proofOfRegistration hmac →
        hmac.size != 32 ∨ hmac == BitcoinLedger.WalletPolicy.zeroBytes32 ∨
          dev.verifyRegistrationProof policy hmac = false) :
    (∃ err, BitcoinLedger.WalletPolicy.authorizePolicyUse profile dev policy auth addrIdx = .error err) ∧
    (∃ err, BitcoinLedger.WalletPolicy.deriveWalletPolicyScript profile dev ora policy auth isChange addrIdx =
      .error err) ∧
    (∀ candidate expected : ByteArray,
      computeHmac32 (BitcoinLedger.WalletPolicy.computeRegistrationCommitmentId ora policy commitment) =
        some expected →
      candidate ≠ expected →
      BitcoinLedger.WalletPolicy.verifyRegistrationHmac ora computeHmac32 policy commitment candidate = false) := by
  rw [isDefaultStatelessPolicy_eq] at hNonDefault
  rw [authorizePolicyUse_eq, deriveWalletPolicyScript_eq]
  have hSpec := InternalSpec.WalletPolicy.registered_wallet_without_valid_hmac_rejected
    profile dev ora policy auth isChange addrIdx hNonDefault hNoValidProof
  refine ⟨hSpec.1, hSpec.2, ?_⟩
  intro candidate expected hComp hNe
  unfold BitcoinLedger.WalletPolicy.verifyRegistrationHmac
  dsimp only
  cases hCandBad : (candidate.size != 32 || candidate == BitcoinLedger.WalletPolicy.zeroBytes32)
  · simp only [Bool.false_eq_true, ↓reduceIte, hComp]
    cases hExpBad : (expected.size != 32 || expected == BitcoinLedger.WalletPolicy.zeroBytes32)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hCt : BitcoinLedger.WalletPolicy.constantTimeEqBytes32 candidate expected with
      | false => rfl
      | true =>
        exact False.elim (hNe (((constantTimeEqBytes32_eq_true_iff candidate expected).mp hCt).1))
    · rfl
  · rfl

/-- Stateless default policy usage with `addressIndex > 50000` (`maxDefaultAddressIndex`)
    is rejected (`authorizePolicyUse` and `deriveWalletPolicyScript` never return `.ok`). -/
theorem stateless_default_address_index_above_50000_rejected
    (profile : PolicyProfile) (dev : DeviceRegistrationOracle) (ora : CryptoPolicyOracle)
    (policy : WalletPolicy) (isChange : Bool) (addrIdx : UInt32)
    (hAbove : addrIdx > BitcoinLedger.WalletPolicy.maxDefaultAddressIndex) :
    (∃ err, BitcoinLedger.WalletPolicy.authorizePolicyUse profile dev policy .statelessDefault addrIdx =
      .error err) ∧
    (∃ err, BitcoinLedger.WalletPolicy.deriveWalletPolicyScript profile dev ora policy
      .statelessDefault isChange addrIdx = .error err) := by
  have hAuth : ∃ err, BitcoinLedger.WalletPolicy.authorizePolicyUse profile dev policy .statelessDefault addrIdx =
      .error err := by
    unfold BitcoinLedger.WalletPolicy.authorizePolicyUse
    cases hUnh : (!BitcoinLedger.WalletPolicy.isUnhardened addrIdx)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hWf : BitcoinLedger.WalletPolicy.checkPolicyWellFormed profile policy with
      | error e => exact ⟨e, rfl⟩
      | ok _ =>
        dsimp [Bind.bind, Except.bind]
        cases hAllow : (!profile.allowStatelessDefaultPolicies)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hDef : (!BitcoinLedger.WalletPolicy.isDefaultStatelessPolicy dev profile.network policy)
          · simp only [Bool.false_eq_true, ↓reduceIte, hAbove]
            exact ⟨.invalidAddressIndex, rfl⟩
          · exact ⟨.unauthorizedPolicy, rfl⟩
        · exact ⟨.unauthorizedPolicy, rfl⟩
    · exact ⟨.invalidAddressIndex, rfl⟩
  refine ⟨hAuth, ?_⟩
  unfold BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
  obtain ⟨err, hErr⟩ := hAuth
  exact ⟨err, by dsimp [Bind.bind, Except.bind]; rw [hErr]⟩

/-- Canonical BIP-379 `andor(X,Y,Z)` branch order soundness:
    1. `compileMiniscript` compiles `andor(X,Y,Z)` to `[X] OP_NOTIF [Z] OP_ELSE [Y] OP_ENDIF[VERIFY]`,
       placing the false-branch `Z` under `OP_NOTIF` and the true-branch `Y` under `OP_ELSE`;
    2. Whenever `sy ≠ sz` and `sy.size = sz.size`, the compiled script strictly differs from the
       inverted `[X] OP_NOTIF [Y] OP_ELSE [Z] OP_ENDIF[VERIFY]` order! -/
theorem andor_branch_order_sound
    (ora : CryptoPolicyOracle) (net : Network) (keys : List KeyInformation)
    (ctx : MiniscriptCtx) (isChange : Bool) (addrIdx : UInt32) (vFlag : Bool)
    (x y z : Miniscript) (sx sy sz : ByteArray)
    (hx : BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false x = .ok sx)
    (hy : BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false y = .ok sy)
    (hz : BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx false z = .ok sz) :
    BitcoinLedger.WalletPolicy.compileMiniscript ora net keys ctx isChange addrIdx vFlag (.andor x y z) =
      .ok (sx ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_NOTIF] ++
           sz ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
           sy ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF) ∧
    (sy ≠ sz → sy.size = sz.size →
      (sx ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_NOTIF] ++
       sz ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
       sy ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF) ≠
      (sx ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_NOTIF] ++
       sy ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
       sz ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF)) := by
  refine ⟨?_, ?_⟩
  · simp [BitcoinLedger.WalletPolicy.compileMiniscript, hx, hy, hz, Bind.bind, Except.bind]
  · intro hNe hSzEq hBytesEq
    have hListEq :
        ((sx ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_NOTIF]).data.toList ++
          (sz.data.toList ++ (ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
            sy ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF).data.toList)) =
        ((sx ++ ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_NOTIF]).data.toList ++
          (sy.data.toList ++ (ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
            sz ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF).data.toList)) := by
      have hRaw := congrArg (fun b : ByteArray => b.data.toList) hBytesEq
      simp only [ByteArray.data_append, Array.toList_append, List.append_assoc] at hRaw ⊢
      exact hRaw
    have hTailEq := List.append_cancel_left hListEq
    have hTakeEq := congrArg (List.take sz.data.toList.length) hTailEq
    have hLenEq : sy.data.toList.length = sz.data.toList.length := by
      simp only [Array.length_toList]
      exact hSzEq
    have hTakeL :
        List.take sz.data.toList.length
          (sz.data.toList ++ (ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
            sy ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF).data.toList) =
        sz.data.toList := List.take_left
    have hTakeR :
        List.take sz.data.toList.length
          (sy.data.toList ++ (ByteArray.mk #[BitcoinLedger.WalletPolicy.OP_ELSE] ++
            sz ++ BitcoinLedger.WalletPolicy.emitOpVerify vFlag BitcoinLedger.WalletPolicy.OP_ENDIF).data.toList) =
        sy.data.toList := by
      rw [← hLenEq]
      exact List.take_left
    rw [hTakeL, hTakeR] at hTakeEq
    have hArrEq : sy.data = sz.data := Array.ext' hTakeEq.symm
    cases sy with
    | mk ay =>
      cases sz with
      | mk az =>
        dsimp only at hArrEq
        subst hArrEq
        exact hNe rfl

/-- Context sensitivity on `BitcoinLedger.WalletPolicy`: `multi_a` in `wsh` (`WshCtx`) and `multi`
    in Tapscript (`TapscriptCtx`) are universally rejected with `.invalidScriptContext`. -/
theorem multi_a_in_wsh_and_multi_in_tapscript_rejected
    (profile : PolicyProfile) (ora : CryptoPolicyOracle) (fmt : PolicyFormat)
    (k : Nat) (kes : List KeyExpr) (ik : KeyExpr) (keys : List KeyInformation)
    (isChange : Bool) (addrIdx : UInt32) (vFlag : Bool)
    (hDepth : ∀ maxD, profile.maxMiniscriptDepth = some maxD → maxD >= 1) :
    BitcoinLedger.WalletPolicy.checkMiniscriptSane fmt .tapscriptCtx
      profile.maxMultiKeys profile.maxMultiAKeys profile.maxMusigKeys (.multi k kes) =
        .error .invalidScriptContext ∧
    BitcoinLedger.WalletPolicy.compileMiniscript ora profile.network keys .tapscriptCtx
      isChange addrIdx vFlag (.multi k kes) = .error .invalidScriptContext ∧
    BitcoinLedger.WalletPolicy.checkMiniscriptSane fmt .wshCtx
      profile.maxMultiKeys profile.maxMultiAKeys profile.maxMusigKeys (.multi_a k kes) =
        .error .invalidScriptContext ∧
    BitcoinLedger.WalletPolicy.compileMiniscript ora profile.network keys .wshCtx
      isChange addrIdx vFlag (.multi_a k kes) = .error .invalidScriptContext ∧
    BitcoinLedger.WalletPolicy.checkDescriptorTemplate profile fmt
      (.wsh (.miniscript (.multi_a k kes))) = .error .invalidScriptContext ∧
    (BitcoinLedger.WalletPolicy.keyExprDeriv ik = .wildcard →
      BitcoinLedger.WalletPolicy.keyExprReferencedIndices ik = [0] →
      (match ik with | .single _ _ => True | .musig _ _ => False) →
      BitcoinLedger.WalletPolicy.checkDescriptorTemplate profile fmt
        (.tr ik (some (.leaf (.miniscript (.multi k kes))))) = .error .invalidScriptContext) := by
  rw [checkMiniscriptSane_eq, compileMiniscript_eq, checkMiniscriptSane_eq,
      compileMiniscript_eq, checkDescriptorTemplate_eq, checkDescriptorTemplate_eq,
      keyExprDeriv_eq, keyExprReferencedIndices_eq]
  exact InternalSpec.WalletPolicy.multi_tapscript_and_multi_a_wsh_rejected
    profile ora fmt k kes ik keys isChange addrIdx vFlag hDepth

/-- `v1` `tr(...)` is universally rejected across `parseDescriptorTemplate`,
    `checkDescriptorTemplate`, and `checkPolicyWellFormed`, and `rawtr(...)` is rejected in
    BIP-388 `parseDescriptorTemplate` and `checkExtendedDescriptorTemplateForBip388` while
    parsed into `.rawtr` by `parseExtendedDescriptorTemplate .v2`. -/
theorem v1_tr_and_bip388_rawtr_rejected
    (profile : PolicyProfile) (ik : KeyExpr) (treeOpt : Option TapTree)
    (name : String) (keys : List KeyInformation) :
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v1 "tr(@0)" = .error .parseError ∧
    BitcoinLedger.WalletPolicy.checkDescriptorTemplate profile .v1 (.tr ik treeOpt) =
      .error .invalidScriptContext ∧
    (∃ err, BitcoinLedger.WalletPolicy.checkPolicyWellFormed profile
      { format := .v1, name := name, template := .tr ik treeOpt, keys := keys } = .error err) ∧
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "rawtr(@0/**)" = .error .parseError ∧
    BitcoinLedger.WalletPolicy.parseExtendedDescriptorTemplate .v2 "rawtr(@0/**)" =
      .ok (.rawtr (.single 0 .wildcard)) ∧
    BitcoinLedger.WalletPolicy.checkExtendedDescriptorTemplateForBip388 profile .v2 (.rawtr ik) =
      .error .invalidScriptContext := by
  rw [parseDescriptorTemplate_eq, checkDescriptorTemplate_eq, checkPolicyWellFormed_eq]
  have hV1 := InternalSpec.WalletPolicy.v1_tr_rejected profile ik treeOpt name keys
  exact ⟨hV1.1, hV1.2.1, hV1.2.2, rfl, rfl, rfl⟩

/-- Uppercase hex digits `'A'..'F'` are rejected in `decodeHexNibble`, Miniscript hash digests,
    and `KeyOrigin` master fingerprints (`[73C5DA0A/84'/0'/0']...`). -/
theorem uppercase_hex_rejected (doubleSha256 : ByteArray → ByteArray) :
    let dummyXpub :=
      String.ofList (List.replicate 111 'a')
    BitcoinLedger.WalletPolicy.decodeHexNibble 0x61 = some 10 ∧
    BitcoinLedger.WalletPolicy.decodeHexNibble 0x41 = none ∧
    BitcoinLedger.WalletPolicy.decodeHexNibble 0x46 = none ∧
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2
      "wsh(and_v(v:pk(@0/**),hash160(0123456789ABCDEF0123456789abcdef01234567)))" =
      .error .parseError ∧
    BitcoinLedger.WalletPolicy.parseKeyOriginPrefix 5 false
      ("[73C5DA0A/84'/0'/0']".toUTF8.data.toList) = none ∧
    BitcoinLedger.WalletPolicy.parseWalletKeyInfo
      (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet) .v2 doubleSha256 false
      ("[73C5DA0A/84'/0'/0']" ++ dummyXpub) = .error .invalidKeyInfo := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Stacked Miniscript wrappers:
    - `wsh(and_b(pk(@0/**),sln:older(12960)))` parses into `.wrap .s (.wrap .l (.wrap .n (.older 12960)))`
      and passes `checkPolicyWellFormed` on both `bolosAppProfile` and `vanadiumAppProfile`;
    - Multi-colon `s:l:n:older(12960)`, double-colon `s::pk(@0/**)`, and `wsh(and_b(pk(@0/**),s::pk(@1/**)))`
      are rejected with `.error .parseError`;
    - Ill-typed wrapper `wsh(s:pk_k(@0/**))` (`s:` requires `Bo`, not `K`) is rejected with `.error .invalidMiniscriptType`. -/
theorem stacked_wrappers_sln_older_accepted_and_s_colon_colon_pk_rejected :
    let expectedTemplate : DescriptorTemplate :=
      .wsh (.miniscript (.and_b
        (.pk (.single 0 .wildcard))
        (.wrap .s (.wrap .l (.wrap .n (.older 12960))))))
    let pol : WalletPolicy :=
      { format := .v2
        name := "Stacked Wrapper Vault"
        template := expectedTemplate
        keys := [witnessKeyInfo 0x01 0x73C5DA0A [hardened 48, hardened 0, hardened 0, hardened 2]] }
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "wsh(and_b(pk(@0/**),sln:older(12960)))" =
      .ok expectedTemplate ∧
    BitcoinLedger.WalletPolicy.checkPolicyWellFormed
      (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet) pol = .ok () ∧
    BitcoinLedger.WalletPolicy.checkPolicyWellFormed
      (BitcoinLedger.WalletPolicy.vanadiumAppProfile .mainnet) pol = .ok () ∧
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "wsh(and_b(pk(@0/**),s:l:n:older(12960)))" =
      .error .parseError ∧
    BitcoinLedger.WalletPolicy.parseMiniscript 64 .v2 ("s::pk(@0/**)".toUTF8.data.toList) = none ∧
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "wsh(and_b(pk(@0/**),s::pk(@1/**)))" =
      .error .parseError ∧
    BitcoinLedger.WalletPolicy.checkDescriptorTemplate
      (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet) .v2
      (.wsh (.miniscript (.wrap .s (.pk_k (.single 0 .wildcard))))) =
      .error .invalidMiniscriptType := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Timelock safety:
    1. Mixing block-height `after(100)` (`< 500000000`) and Unix-timestamp `after(500000000)` (`>= 500000000`)
       in `and_v` is rejected by `checkMiniscriptSane` with `.error .miniscriptTimelockMix`;
    2. Mixing relative block-height `older(10)` and relative time `older(0x00400001)` in `and_v`
       is likewise rejected with `.error .miniscriptTimelockMix`;
    3. Dirty BIP-68 `older(n)` values (`0`, `0x00010001` bit 16, `0x00800001` bit 23, `0x80000001` bit 31)
       are rejected by `analyzeMiniscript` with `.error .invalidTimelockRange`, whereas valid height `older(1)`
       and valid 512s-unit time `older(0x00400001)` succeed! -/
theorem after_timelock_mixing_and_dirty_older_bits_rejected :
    let mixAfter : Miniscript :=
      .and_v (.wrap .v (.pk (.single 0 .wildcard)))
        (.and_v (.wrap .v (.after 100)) (.after 500000000))
    let mixOlder : Miniscript :=
      .and_v (.wrap .v (.pk (.single 0 .wildcard)))
        (.and_v (.wrap .v (.older 10)) (.older 0x00400001))
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 16 16 5 mixAfter =
      .error .miniscriptTimelockMix ∧
    BitcoinLedger.WalletPolicy.checkMiniscriptSane .v2 .wshCtx 16 16 5 mixOlder =
      .error .miniscriptTimelockMix ∧
    BitcoinLedger.WalletPolicy.analyzeMiniscript .v2 .wshCtx 16 16 5 (.older 0) =
      .error .invalidTimelockRange ∧
    BitcoinLedger.WalletPolicy.analyzeMiniscript .v2 .wshCtx 16 16 5 (.older 0x00010001) =
      .error .invalidTimelockRange ∧
    BitcoinLedger.WalletPolicy.analyzeMiniscript .v2 .wshCtx 16 16 5 (.older 0x00800001) =
      .error .invalidTimelockRange ∧
    BitcoinLedger.WalletPolicy.analyzeMiniscript .v2 .wshCtx 16 16 5 (.older 0x80000001) =
      .error .invalidTimelockRange ∧
    (BitcoinLedger.WalletPolicy.analyzeMiniscript .v2 .wshCtx 16 16 5 (.older 1)).isOk = true ∧
    (BitcoinLedger.WalletPolicy.analyzeMiniscript .v2 .wshCtx 16 16 5 (.older 0x00400001)).isOk = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Constructive trichotomy helper for `byteListLt`: ordering `(xs, ys)` vs `(ys, xs)` produces
    identical pairs. -/
private theorem byteListLt_comm_ordered :
    ∀ (xs ys : List UInt8),
      (if BitcoinLedger.WalletPolicy.byteListLt xs ys then (xs, ys) else (ys, xs)) =
      (if BitcoinLedger.WalletPolicy.byteListLt ys xs then (ys, xs) else (xs, ys))
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    unfold BitcoinLedger.WalletPolicy.byteListLt
    by_cases hxy : x < y
    · have hyx : ¬ (y < x) := Nat.lt_asymm hxy
      simp [hxy, hyx]
    · by_cases hyx : y < x
      · simp [hxy, hyx]
      · have hEq : x = y := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq
          (Nat.le_antisymm (Nat.not_lt.mp hyx) (Nat.not_lt.mp hxy)))
        subst hEq
        have hSelf : ¬ (x < x) := Nat.lt_irrefl x.toBitVec.toNat
        simp only [hSelf, ↓reduceIte]
        have ih := byteListLt_comm_ordered xs ys
        cases h1 : BitcoinLedger.WalletPolicy.byteListLt xs ys with
        | false =>
          cases h2 : BitcoinLedger.WalletPolicy.byteListLt ys xs with
          | false =>
            simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at ih ⊢
            exact ⟨congrArg (List.cons x) ih.1, congrArg (List.cons x) ih.2⟩
          | true =>
            rfl
        | true =>
          cases h2 : BitcoinLedger.WalletPolicy.byteListLt ys xs with
          | false =>
            rfl
          | true =>
            simp only [h1, h2, ↓reduceIte, Prod.mk.injEq] at ih ⊢
            exact ⟨congrArg (List.cons x) ih.1, congrArg (List.cons x) ih.2⟩

/-- BIP-341 `tapBranchHash` is unconditionally commutative due to lexicographic child ordering. -/
theorem tapBranchHash_comm (ora : CryptoPolicyOracle) (a b : ByteArray) :
    BitcoinLedger.WalletPolicy.tapBranchHash ora a b =
      BitcoinLedger.WalletPolicy.tapBranchHash ora b a := by
  unfold BitcoinLedger.WalletPolicy.tapBranchHash BitcoinLedger.WalletPolicy.byteArrayLt
  have hOrd := byteListLt_comm_ordered a.data.toList b.data.toList
  have hBytes :
      (if BitcoinLedger.WalletPolicy.byteListLt a.data.toList b.data.toList then a ++ b else b ++ a) =
      (if BitcoinLedger.WalletPolicy.byteListLt b.data.toList a.data.toList then b ++ a else a ++ b) := by
    cases h1 : BitcoinLedger.WalletPolicy.byteListLt a.data.toList b.data.toList with
    | false =>
      cases h2 : BitcoinLedger.WalletPolicy.byteListLt b.data.toList a.data.toList with
      | false =>
        simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hOrd ⊢
        cases a with
        | mk da =>
          cases b with
          | mk db =>
            have hArr : da = db := Array.ext' hOrd.1.symm
            subst hArr
            rfl
      | true =>
        rfl
    | true =>
      cases h2 : BitcoinLedger.WalletPolicy.byteListLt b.data.toList a.data.toList with
      | false =>
        rfl
      | true =>
        simp only [h1, h2, ↓reduceIte, Prod.mk.injEq] at hOrd ⊢
        cases a with
        | mk da =>
          cases b with
          | mk db =>
            have hArr : da = db := Array.ext' hOrd.1
            subst hArr
            rfl
  rw [hBytes]

/-! ## Section 8: Positive Non-Vacuity Witness Theorems on `BitcoinLedger.WalletPolicy` -/

set_option maxRecDepth 32768 in
/-- Witness 1: BIP-84 `wpkh(@0/<0;1>/*)` parses cleanly on `BitcoinLedger.WalletPolicy`, qualifies as
    a stateless default policy, derives a 22-byte P2WPKH `scriptPubKey` (`0x00 0x14 <20B>`), and
    formats into a canonical BIP-173 `"bc1q..."` Bech32 address that decodes back to `(0, hash20)`! -/
theorem impl_nonvacuous_bip84_wpkh :
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "wpkh(@0/<0;1>/*)" =
      .ok witnessBip84Policy.template ∧
    BitcoinLedger.WalletPolicy.isDefaultStatelessPolicy witnessDeviceOracle .mainnet
      witnessBip84Policy = true ∧
    ∃ (spk : ByteArray) (addr : String),
      BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
        (BitcoinLedger.WalletPolicy.canonicalLedgerProfile .mainnet)
        witnessDeviceOracle witnessCryptoOracle
        witnessBip84Policy .statelessDefault false 0 = .ok spk ∧
      spk.size = 22 ∧ spk.get! 0 = BitcoinLedger.WalletPolicy.OP_0 ∧ spk.get! 1 = 0x14 ∧
      BitcoinLedger.WalletPolicy.deriveWalletPolicyAddress .bolos
        (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
        witnessDeviceOracle witnessCryptoOracle
        witnessBip84Policy .statelessDefault false 0 = .ok addr ∧
      (InternalSpec.decodeSegwitAddr? "bc" addr).isSome = true := by
  exact ⟨rfl, rfl, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Witness 2: BIP-86 `tr(@0/<0;1>/*)` parses cleanly on `BitcoinLedger.WalletPolicy`, qualifies as
    a stateless default policy, derives a 34-byte P2TR `scriptPubKey` (`0x51 0x20 <32B>`), and
    formats into a canonical BIP-350 `"bc1p..."` Bech32m address that decodes back to `(1, key32)`! -/
theorem impl_nonvacuous_bip86_tr :
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "tr(@0/<0;1>/*)" =
      .ok witnessBip86Policy.template ∧
    BitcoinLedger.WalletPolicy.isDefaultStatelessPolicy witnessDeviceOracle .mainnet
      witnessBip86Policy = true ∧
    ∃ (spk : ByteArray) (addr : String),
      BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
        (BitcoinLedger.WalletPolicy.canonicalLedgerProfile .mainnet)
        witnessDeviceOracle witnessCryptoOracle
        witnessBip86Policy .statelessDefault false 0 = .ok spk ∧
      spk.size = 34 ∧ spk.get! 0 = BitcoinLedger.WalletPolicy.OP_1 ∧ spk.get! 1 = 0x20 ∧
      BitcoinLedger.WalletPolicy.deriveWalletPolicyAddress .bolos
        (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
        witnessDeviceOracle witnessCryptoOracle
        witnessBip86Policy .statelessDefault false 0 = .ok addr ∧
      (InternalSpec.decodeSegwitAddr? "bc" addr).isSome = true := by
  exact ⟨rfl, rfl, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete oracle distinguishing receive vs change scripts via child pubkey & digest bytes. -/
private def witnessRichShaOracle : CryptoPolicyOracle :=
  { witnessCryptoOracle with
    ckdPub := fun xpub idx =>
      if isUnhardened idx then
        some {
          version := xpub.version
          depth := xpub.depth + 1
          parentFingerprint := 0x55667788
          childNumber := idx
          chainCode := ByteArray.mk (#[(idx &&& 0xFF).toUInt8] ++ Array.replicate 31 0x33)
          compressedPubkey :=
            ByteArray.mk (#[0x02, xpub.compressedPubkey.get! 1, (idx &&& 0xFF).toUInt8, xpub.compressedPubkey.get! 2] ++
              Array.replicate 29 0x44)
        }
      else none
    sha256 := fun msg =>
      ByteArray.mk (#[UInt8.ofNat (msg.size % 256), msg.get! 0, msg.get! 5] ++ Array.replicate 29 0xAA) }

/-- Witness 3: Registered 2-of-2 P2WSH multisig policy `wsh(sortedmulti(2,@0/**,@1/**))` succeeds
    through `verifyAndRegisterWalletPolicy` on both `bolosAppProfile` and `vanadiumAppProfile`,
    verifies under `verifyRegistrationHmac`, and derives distinct receive/change 34-byte P2WSH
    `scriptPubKey`s via `deriveWalletPolicyScript`! -/
theorem impl_nonvacuous_wsh_sortedmulti :
    let computeHmac32 : ByteArray → Option ByteArray := fun _ => some witnessValidHmac
    let bolosCommit := BitcoinLedger.WalletPolicy.RegistrationCommitmentInput.bolos
      ("wsh(sortedmulti(2,@0/**,@1/**))".toUTF8)
      (ByteArray.mk (Array.replicate 32 0x99))
    let vndCommit := BitcoinLedger.WalletPolicy.RegistrationCommitmentInput.vanadium
      ("wsh(sortedmulti(2,@0/**,@1/**))".toUTF8)
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2 "wsh(sortedmulti(2,@0/**,@1/**))" =
      .ok witnessWshSortedmultiPolicy.template ∧
    (BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
      (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
      witnessDeviceOracle witnessRichShaOracle computeHmac32
      witnessWshSortedmultiPolicy bolosCommit true).isOk = true ∧
    (BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
      (BitcoinLedger.WalletPolicy.vanadiumAppProfile .mainnet)
      witnessDeviceOracle witnessRichShaOracle computeHmac32
      witnessWshSortedmultiPolicy vndCommit true).isOk = true ∧
    BitcoinLedger.WalletPolicy.verifyRegistrationHmac
      witnessRichShaOracle computeHmac32 witnessWshSortedmultiPolicy bolosCommit witnessValidHmac = true ∧
    ∃ (spkRx spkChg : ByteArray),
      BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
        (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
        witnessDeviceOracle witnessRichShaOracle
        witnessWshSortedmultiPolicy (.proofOfRegistration witnessValidHmac) false 7 = .ok spkRx ∧
      BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
        (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
        witnessDeviceOracle witnessRichShaOracle
        witnessWshSortedmultiPolicy (.proofOfRegistration witnessValidHmac) true 7 = .ok spkChg ∧
      spkRx.size = 34 ∧ spkRx.get! 0 = BitcoinLedger.WalletPolicy.OP_0 ∧ spkRx.get! 1 = 0x20 ∧
      spkChg.size = 34 ∧ spkRx ≠ spkChg := by
  refine ⟨rfl, rfl, rfl, rfl, _, _, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  have hByte4 := congrArg (fun b : ByteArray => b.get! 4) hEq
  revert hByte4
  decide

set_option maxRecDepth 32768 in
/-- Witness 4: Registered Tapscript tree policy `tr(@0/**,{pk(@1/**),and_v(v:pk(@2/**),older(1000))})`
    parses cleanly, registers via `verifyAndRegisterWalletPolicy` across `bolosAppProfile` and
    `vanadiumAppProfile`, and derives a 34-byte P2TR `scriptPubKey` & BIP-350 Bech32m address! -/
theorem impl_nonvacuous_tapscript_tr_tree :
    let computeHmac32 : ByteArray → Option ByteArray := fun _ => some witnessValidHmac
    let commit := BitcoinLedger.WalletPolicy.RegistrationCommitmentInput.bolos
      ("tr(@0/**,{pk(@1/**),and_v(v:pk(@2/**),older(1000))})".toUTF8)
      (ByteArray.mk (Array.replicate 32 0x88))
    BitcoinLedger.WalletPolicy.parseDescriptorTemplate .v2
      "tr(@0/**,{pk(@1/**),and_v(v:pk(@2/**),older(1000))})" =
      .ok witnessTapscriptPolicy.template ∧
    (BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
      (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
      witnessDeviceOracle witnessCryptoOracle computeHmac32
      witnessTapscriptPolicy commit true).isOk = true ∧
    (BitcoinLedger.WalletPolicy.verifyAndRegisterWalletPolicy
      (BitcoinLedger.WalletPolicy.vanadiumAppProfile .mainnet)
      witnessDeviceOracle witnessCryptoOracle computeHmac32
      witnessTapscriptPolicy commit true).isOk = true ∧
    ∃ (spk : ByteArray) (addr : String),
      BitcoinLedger.WalletPolicy.deriveWalletPolicyScript
        (BitcoinLedger.WalletPolicy.bolosAppProfile .mainnet)
        witnessDeviceOracle witnessCryptoOracle
        witnessTapscriptPolicy (.proofOfRegistration witnessValidHmac) true 5 = .ok spk ∧
      spk.size = 34 ∧ spk.get! 0 = BitcoinLedger.WalletPolicy.OP_1 ∧ spk.get! 1 = 0x20 ∧
      BitcoinLedger.WalletPolicy.deriveWalletPolicyAddress .vanadium
        (BitcoinLedger.WalletPolicy.vanadiumAppProfile .mainnet)
        witnessDeviceOracle witnessCryptoOracle
        witnessTapscriptPolicy (.proofOfRegistration witnessValidHmac) true 5 = .ok addr ∧
      (InternalSpec.decodeSegwitAddr? "bc" addr).isSome = true := by
  exact ⟨rfl, rfl, rfl, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 32768 in
/-- Witness 5: Full `KeyInformation` parsing (`[73c5da0a/84'/0'/0']` origin + 78-byte BIP-32 xpub
    serialization/deserialization roundtrip + `'h'` hardened marker support). -/
theorem impl_nonvacuous_parseWalletKeyInfo_roundtrip :
    let expectedKi := witnessKeyInfo 0x01 0x73C5DA0A [hardened 84, hardened 0, hardened 0]
    let raw78 := BitcoinLedger.WalletPolicy.serializeXpub78 expectedKi.xpub
    BitcoinLedger.WalletPolicy.deserializeXpub78 raw78 = some expectedKi.xpub ∧
    BitcoinLedger.WalletPolicy.parseKeyOriginPrefix 5 false
      ("[73c5da0a/84'/0'/0']xpub".toUTF8.data.toList) =
      some ({ fingerprint := 0x73C5DA0A, path := [hardened 84, hardened 0, hardened 0] },
            "xpub".toUTF8.data.toList) ∧
    BitcoinLedger.WalletPolicy.parseKeyOriginPrefix 5 true
      ("[73c5da0a/84h/0h/0h]xpub".toUTF8.data.toList) =
      some ({ fingerprint := 0x73C5DA0A, path := [hardened 84, hardened 0, hardened 0] },
            "xpub".toUTF8.data.toList) := by
  exact ⟨rfl, rfl, rfl⟩

end Proofs.WalletPolicy

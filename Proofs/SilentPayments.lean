import InternalSpec
import BitcoinLedger.SilentPayments

/-!
# `Proofs.SilentPayments` — Refinement & Security Proofs for `BitcoinLedger.SilentPayments`

Connects every executable operation in `BitcoinLedger.SilentPayments` to `InternalSpec.SilentPayments`:
1. Exact refinement of BIP-352 address encoding/decoding (`encodeSpAddress`, `decodeSpAddress`),
   BIP-392 scan-key encoding/decoding (`encodeSpScanKey`, `decodeSpScanKey`), `spKeyDerivationPath`,
   `labelTweak`, `labeledSpendKey`, `deriveAccountSpAddress`, `deriveAccountTweakScript`, and
   `exportSpScanKey`.
2. Eligible input script classification (`classifySpInputScript` for P2PKH, P2WPKH, P2SH-P2WPKH,
   and P2TR excluding BIP-341 NUMS `H`), smallest-outpoint selection (`smallestOutpointBytes`),
   `normalizeInputPrivKey`, `computeInputHash`, `ecdhShare`, `sharedSecret`, `outputTweak`,
   `outputKey`, `assignK`, and `receiverSpendingKey`.
3. BIP-374 `dleqChallenge`, `dleqNonce`, `dleqVerify`, and `dleqProve` refinement & self-verification
   soundness (`impl_dleqProve_implies_dleqVerify`).
4. BIP-375 PSBT Silent Payment validation & finalization (`validatePsbtSpOutputs`,
   `verifyOutputSpLabel`, `collectSpRecipients`, `analyzePsbtSilentPayments`,
   `finalizePsbtSilentPayments`), security rejection theorems, and non-vacuity witness.

All theorems satisfy `0 sorryAx`, `0 native_decide`, and `0 Classical.choice`.
-/

namespace Proofs.SilentPayments

open InternalSpec.SilentPayments

/-! ## 1. Primitive & Byte-Encoding Refinement Lemmas -/

theorem secp256k1Order_eq :
    BitcoinLedger.SilentPayments.secp256k1Order = InternalSpec.SilentPayments.secp256k1Order := rfl

theorem spMaxOutputsPerScanKey_eq :
    BitcoinLedger.SilentPayments.spMaxOutputsPerScanKey =
      InternalSpec.SilentPayments.spMaxOutputsPerScanKey := rfl

theorem bip32HardenedBit_eq :
    BitcoinLedger.SilentPayments.bip32HardenedBit = InternalSpec.SilentPayments.bip32HardenedBit := rfl

theorem bip352Purpose_eq :
    BitcoinLedger.SilentPayments.bip352Purpose = InternalSpec.SilentPayments.bip352Purpose := rfl

theorem sighashAll_eq :
    BitcoinLedger.SilentPayments.sighashAll = InternalSpec.SilentPayments.sighashAll := rfl

theorem sighashDefault_eq :
    BitcoinLedger.SilentPayments.sighashDefault = InternalSpec.SilentPayments.sighashDefault := rfl

theorem bip341NumsXOnly_eq :
    BitcoinLedger.SilentPayments.bip341NumsXOnly = InternalSpec.SilentPayments.bip341NumsXOnly := by
  decide

theorem sizedBytes_eq_of_bytes {n : Nat} {a b : SizedBytes n} (h : a.bytes = b.bytes) :
    a = b := by
  cases a; cases b; simp at h; subst h; rfl

theorem byteListEq_iff_eq :
    ∀ (xs ys : List UInt8),
      BitcoinLedger.SilentPayments.byteListEq xs ys = decide (xs = ys)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp only [BitcoinLedger.SilentPayments.byteListEq, byteListEq_iff_eq as bs]
    by_cases hab : a = b
    · subst hab
      by_cases has : as = bs <;> simp [has]
    · simp [hab]

theorem bytesEq_eq_decide (a b : ByteArray) :
    BitcoinLedger.SilentPayments.bytesEq a b = decide (a = b) := by
  unfold BitcoinLedger.SilentPayments.bytesEq
  rw [byteListEq_iff_eq]
  cases a with
  | mk da =>
    cases b with
    | mk db =>
      by_cases h : da.toList = db.toList
      · have hArr : da = db := Array.ext' h
        subst hArr
        simp
      · have hNe : ByteArray.mk da ≠ ByteArray.mk db := by
          intro hEq
          injection hEq with hArr
          subst hArr
          exact h rfl
        simp [h, hNe]

private theorem uint8_isEqvAux_self (xs : Array UInt8) :
    ∀ (i : Nat) (hi : i ≤ xs.size),
      Array.isEqvAux xs xs rfl (fun a b => decide (a = b)) i hi = true
  | 0, _ => rfl
  | i + 1, hi => by
    unfold Array.isEqvAux
    have hSelf : decide (xs[i] = xs[i]) = true := decide_eq_true rfl
    rw [hSelf, uint8_isEqvAux_self xs i (Nat.le_trans (Nat.le_add_right i 1) hi)]
    rfl

private theorem uint8_rel_of_isEqvAux {xs ys : Array UInt8} (hsz : xs.size = ys.size) :
    ∀ (i : Nat) (hi : i ≤ xs.size),
      Array.isEqvAux xs ys hsz (fun a b => decide (a = b)) i hi = true →
      ∀ (j : Nat) (hj : j < i),
        xs[j]'(Nat.lt_of_lt_of_le hj hi) = ys[j]'(Nat.lt_of_lt_of_le hj (hsz ▸ hi))
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | i + 1, hi, heqv, j, hj => by
    unfold Array.isEqvAux at heqv
    have hPair : decide (xs[i] = ys[i]'(hsz ▸ hi)) = true ∧
        Array.isEqvAux xs ys hsz (fun a b => decide (a = b)) i
          (Nat.le_trans (Nat.le_add_right i 1) hi) = true := by
      cases h1 : decide (xs[i] = ys[i]'(hsz ▸ hi))
      · rw [h1] at heqv; cases heqv
      · rw [h1] at heqv; exact ⟨rfl, heqv⟩
    by_cases hj' : j < i
    · exact uint8_rel_of_isEqvAux hsz i _ hPair.2 j hj'
    · have hji : j = i := Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.ge_of_not_lt hj')
      subst hji
      exact of_decide_eq_true hPair.1

private theorem list_ext_getElem {α : Type} :
    ∀ {as bs : List α} (_hlen : as.length = bs.length),
      (∀ (i : Nat) (h1 : i < as.length) (h2 : i < bs.length), as[i]'h1 = bs[i]'h2) → as = bs
  | [], [], _, _ => rfl
  | _ :: _, [], hlen, _ => by cases hlen
  | [], _ :: _, hlen, _ => by cases hlen
  | a :: as, b :: bs, hlen, hget => by
    have hHead : a = b := hget 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    have hTail : as = bs := list_ext_getElem (Nat.succ.inj hlen) (fun i h1 h2 =>
      hget (i + 1) (Nat.succ_lt_succ h1) (Nat.succ_lt_succ h2))
    rw [hHead, hTail]

theorem byteArray_beq_eq_decide (a b : ByteArray) : (a == b) = decide (a = b) := by
  cases a with
  | mk xs =>
    cases b with
    | mk ys =>
      show Array.isEqv xs ys (fun x y => decide (x = y)) = decide (ByteArray.mk xs = ByteArray.mk ys)
      by_cases hEq : xs = ys
      · subst hEq
        unfold Array.isEqv
        simp [uint8_isEqvAux_self xs xs.size (Nat.le_refl _)]
      · have hBaNe : ByteArray.mk xs ≠ ByteArray.mk ys := fun hc => hEq (by injection hc)
        rw [decide_eq_false hBaNe]
        unfold Array.isEqv
        split
        · rename_i hsz
          cases hAux : Array.isEqvAux xs ys hsz (fun x y => decide (x = y)) xs.size (Nat.le_refl _)
          · rfl
          · exfalso
            apply hEq
            cases xs with
            | mk lxs =>
              cases ys with
              | mk lys =>
                congr 1
                exact list_ext_getElem hsz (fun j hj1 _ =>
                  uint8_rel_of_isEqvAux hsz lxs.length (Nat.le_refl _) hAux j hj1)
        · rfl

theorem bytesEq_not_eq_bne (a b : ByteArray) :
    (!BitcoinLedger.SilentPayments.bytesEq a b) = (a != b) := by
  rw [bytesEq_eq_decide]
  show (!decide (a = b)) = !(a == b)
  rw [byteArray_beq_eq_decide]

theorem spListAll_eq {α : Type} (p : α → Bool) :
    ∀ xs, BitcoinLedger.SilentPayments.spListAll p xs = InternalSpec.SilentPayments.spListAll p xs
  | [] => rfl
  | x :: xs => by
    simp only [BitcoinLedger.SilentPayments.spListAll, InternalSpec.SilentPayments.spListAll,
      spListAll_eq p xs]

theorem spListMem_eq {α : Type} [DecidableEq α] (x : α) :
    ∀ xs, BitcoinLedger.SilentPayments.spListMem x xs = InternalSpec.SilentPayments.spListMem x xs
  | [] => rfl
  | y :: ys => by
    simp only [BitcoinLedger.SilentPayments.spListMem, InternalSpec.SilentPayments.spListMem,
      spListMem_eq x ys]

theorem appendBytes_eq (a b : ByteArray) :
    BitcoinLedger.SilentPayments.appendBytes a b = InternalSpec.SilentPayments.appendBytes a b := rfl

theorem concatBytes_eq (xs : List ByteArray) :
    BitcoinLedger.SilentPayments.concatBytes xs = InternalSpec.SilentPayments.concatBytes xs := rfl

theorem appendSized_eq {m n : Nat} (a : SizedBytes m) (b : SizedBytes n) :
    BitcoinLedger.SilentPayments.appendSized a b = SizedBytes.append a b := rfl

theorem natToBytesBEAux_eq (k v : Nat) (acc : List UInt8) :
    BitcoinLedger.SilentPayments.natToBytesBEAux k v acc =
      InternalSpec.SilentPayments.natToBytesBEAux k v acc := by
  induction k generalizing v acc with
  | zero => rfl
  | succ k ih =>
    simp only [BitcoinLedger.SilentPayments.natToBytesBEAux,
      InternalSpec.SilentPayments.natToBytesBEAux, ih]

theorem scalarToBytes32_eq (v : Nat) :
    BitcoinLedger.SilentPayments.scalarToBytes32 v = InternalSpec.SilentPayments.scalarToBytes32 v := by
  apply sizedBytes_eq_of_bytes
  unfold BitcoinLedger.SilentPayments.scalarToBytes32 InternalSpec.SilentPayments.scalarToBytes32
  dsimp only
  rw [natToBytesBEAux_eq]

theorem bytes32ToNat_eq (b : Bytes32) :
    BitcoinLedger.SilentPayments.bytes32ToNat b = InternalSpec.SilentPayments.bytes32ToNat b := rfl

theorem parseScalarStrict_eq (b : Bytes32) :
    BitcoinLedger.SilentPayments.parseScalarStrict b =
      InternalSpec.SilentPayments.parseScalarStrict b := by
  unfold BitcoinLedger.SilentPayments.parseScalarStrict InternalSpec.SilentPayments.parseScalarStrict
  dsimp only
  rw [bytes32ToNat_eq, secp256k1Order_eq]
  by_cases h : InternalSpec.SilentPayments.bytes32ToNat b < InternalSpec.SilentPayments.secp256k1Order
  · simp [h]
  · simp [h]

theorem parseNonZeroScalar_eq (b : Bytes32) :
    BitcoinLedger.SilentPayments.parseNonZeroScalar b =
      InternalSpec.SilentPayments.parseNonZeroScalar b := rfl

theorem parseScalarModN_eq (b : Bytes32) :
    BitcoinLedger.SilentPayments.parseScalarModN b =
      InternalSpec.SilentPayments.parseScalarModN b := rfl

theorem encodeU32BE_eq (v : UInt32) :
    BitcoinLedger.SilentPayments.encodeU32BE v = InternalSpec.SilentPayments.encodeU32BE v := rfl

theorem encodeU32LE_eq (v : UInt32) :
    BitcoinLedger.SilentPayments.encodeU32LE v = InternalSpec.SilentPayments.encodeU32LE v := rfl

theorem xorBytes32_eq (a b : Bytes32) :
    BitcoinLedger.SilentPayments.xorBytes32 a b = InternalSpec.SilentPayments.xorBytes32 a b := rfl

theorem mkP2trScript_eq (xOnly : Bytes32) :
    BitcoinLedger.SilentPayments.mkP2trScript xOnly = InternalSpec.SilentPayments.mkP2trScript xOnly := rfl

theorem nat_beq_eq_decide (a b : Nat) : (a == b) = decide (a = b) := by
  by_cases h : a = b
  · subst h
    have hTrue : (a == a) = true := Nat.beq_refl a
    rw [hTrue]
    simp
  · have hFalse : (a == b) = false := by
      cases hEq : (a == b) with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hEq) h
    rw [hFalse]
    simp [h]

/-! ## 2. BIP-352 Addresses, BIP-392 Scan Keys & Account Policy Refinement -/

theorem serializeSpCode_eq {Affine : Type} (c : SpCrypto Affine)
    (code : SilentPaymentCode Affine) :
    BitcoinLedger.SilentPayments.serializeSpCode c code = code.toBytes c := rfl

theorem deserializeSpCode_eq {Affine : Type} (c : SpCrypto Affine) (raw : Bytes66) :
    BitcoinLedger.SilentPayments.deserializeSpCode c raw =
      SilentPaymentCode.fromBytes c raw := rfl

theorem encodeSpAddress_refines_spec {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpAddressHrp) (code : SilentPaymentCode Affine) :
    BitcoinLedger.SilentPayments.encodeSpAddress c bech hrp code =
      InternalSpec.SilentPayments.encodeSpAddress c bech hrp code := rfl

theorem decodeSpAddress_refines_spec {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (addr : String) :
    BitcoinLedger.SilentPayments.decodeSpAddress c bech addr =
      InternalSpec.SilentPayments.decodeSpAddress c bech addr := by
  unfold BitcoinLedger.SilentPayments.decodeSpAddress InternalSpec.SilentPayments.decodeSpAddress
  cases bech.decodeVersioned addr with
  | none => rfl
  | some triple =>
    rcases triple with ⟨hrpStr, version, payload⟩
    dsimp only [Bind.bind, Except.bind]
    cases SpAddressHrp.fromLowerString hrpStr with
    | none => rfl
    | some hrp =>
      dsimp only [Bind.bind, Except.bind]
      by_cases hV0 : decide (version = 0) = true
      · simp only [hV0, ↓reduceDIte, ↓reduceIte]
        by_cases hEq : payload.size = 66
        · simp only [hEq, ↓reduceDIte]
          rw [deserializeSpCode_eq]
          cases SilentPaymentCode.fromBytes c ⟨payload, hEq⟩ <;> rfl
        · simp [hEq]
      · simp only [hV0, Bool.false_eq_true, ↓reduceDIte, ↓reduceIte]
        by_cases hV30 : decide (version ≤ 30) = true
        · simp only [hV30, ↓reduceDIte, ↓reduceIte]
          by_cases hGe : 66 ≤ payload.size
          · simp only [hGe, ↓reduceDIte]
            rw [deserializeSpCode_eq]
            cases SilentPaymentCode.fromBytes c _ <;> rfl
          · simp [hGe]
        · simp [hV30]

theorem encodeSpScanKey_refines_spec {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (hrp : SpScanHrp) (bScan : Nat) (bSpend : Affine) :
    BitcoinLedger.SilentPayments.encodeSpScanKey c bech hrp bScan bSpend =
      InternalSpec.SilentPayments.encodeSpScanKey c bech hrp bScan bSpend := by
  unfold BitcoinLedger.SilentPayments.encodeSpScanKey InternalSpec.SilentPayments.encodeSpScanKey
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [secp256k1Order_eq]
  cases (!(decide (0 < bScan) && decide (bScan < InternalSpec.SilentPayments.secp256k1Order))) with
  | true => rfl
  | false =>
    rw [scalarToBytes32_eq, appendSized_eq]
    rfl

theorem decodeSpScanKey_refines_spec {Affine : Type} (c : SpCrypto Affine) (bech : Bech32mCodec)
    (encoded : String) :
    BitcoinLedger.SilentPayments.decodeSpScanKey c bech encoded =
      InternalSpec.SilentPayments.decodeSpScanKey c bech encoded := by
  unfold BitcoinLedger.SilentPayments.decodeSpScanKey InternalSpec.SilentPayments.decodeSpScanKey
  cases bech.decodeVersioned encoded with
  | none => rfl
  | some triple =>
    rcases triple with ⟨hrpStr, version, payload⟩
    dsimp only [Bind.bind, Except.bind]
    cases SpScanHrp.fromLowerString hrpStr with
    | none => rfl
    | some hrp =>
      dsimp only [Bind.bind, Except.bind]
      by_cases hChk : version = 0 ∧ payload.size = 65
      · rcases hChk with ⟨hV, hSz⟩
        subst hV
        simp only [hSz, and_self, ↓reduceDIte]
        rw [parseNonZeroScalar_eq]
        cases InternalSpec.SilentPayments.parseNonZeroScalar _ with
        | none => rfl
        | some bScan =>
          dsimp only [Bind.bind, Except.bind]
          cases c.decompress _ <;> rfl
      · simp [hChk]

theorem spKeyDerivationPath_refines_spec (coinType accountIndex : UInt32) (isScanBranch : Bool) :
    BitcoinLedger.SilentPayments.spKeyDerivationPath coinType accountIndex isScanBranch =
      InternalSpec.SilentPayments.spKeyDerivationPath coinType accountIndex isScanBranch := by
  unfold BitcoinLedger.SilentPayments.spKeyDerivationPath InternalSpec.SilentPayments.spKeyDerivationPath
  rw [bip32HardenedBit_eq, bip352Purpose_eq]
  by_cases h1 : InternalSpec.SilentPayments.bip32HardenedBit ≤ accountIndex
  · simp [h1]
  · by_cases h2 : InternalSpec.SilentPayments.bip32HardenedBit ≤ coinType <;> simp [h1, h2]

theorem mkCheckedSpAccount_refines_spec {Affine : Type}
    (accountIndex : UInt32) (scanKey : Nat) (spendKey : Affine) :
    BitcoinLedger.SilentPayments.mkCheckedSpAccount accountIndex scanKey spendKey =
      SilentPaymentAccount.mkChecked accountIndex scanKey spendKey := by
  unfold BitcoinLedger.SilentPayments.mkCheckedSpAccount SilentPaymentAccount.mkChecked
  rw [bip32HardenedBit_eq, secp256k1Order_eq]
  by_cases h1 : InternalSpec.SilentPayments.bip32HardenedBit ≤ accountIndex
  · simp [h1]
  · simp [h1]

theorem labelTweak_refines_spec {Affine : Type} (c : SpCrypto Affine) (bScan : Nat) (m : UInt32) :
    BitcoinLedger.SilentPayments.labelTweak c bScan m =
      InternalSpec.SilentPayments.labelTweak c bScan m := by
  unfold BitcoinLedger.SilentPayments.labelTweak InternalSpec.SilentPayments.labelTweak
  dsimp only
  rw [scalarToBytes32_eq, encodeU32BE_eq, appendBytes_eq, parseNonZeroScalar_eq]
  cases InternalSpec.SilentPayments.parseNonZeroScalar _ <;> rfl

theorem labeledSpendKey_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (bSpend : Affine) (bScan : Nat) (m : UInt32) :
    BitcoinLedger.SilentPayments.labeledSpendKey c bSpend bScan m =
      InternalSpec.SilentPayments.labeledSpendKey c bSpend bScan m := by
  unfold BitcoinLedger.SilentPayments.labeledSpendKey InternalSpec.SilentPayments.labeledSpendKey
  rw [labelTweak_refines_spec]
  cases InternalSpec.SilentPayments.labelTweak c bScan m <;> rfl

theorem deriveAccountSpAddress_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (bech : Bech32mCodec) (hrp : SpAddressHrp)
    (account : SilentPaymentAccount Affine) (coords : SilentPaymentCoordinates) :
    BitcoinLedger.SilentPayments.deriveAccountSpAddress c bech hrp account coords =
      InternalSpec.SilentPayments.deriveAccountSpAddress c bech hrp account coords := by
  cases coords with
  | tweak _ => rfl
  | code labelOpt =>
    cases labelOpt with
    | none =>
      unfold BitcoinLedger.SilentPayments.deriveAccountSpAddress
        InternalSpec.SilentPayments.deriveAccountSpAddress
      dsimp only [Bind.bind, Except.bind]
      cases c.pointMul account.scanKey (.affine c.generator) <;> rfl
    | some m =>
      by_cases hm : m = 0
      · subst hm
        rfl
      · unfold BitcoinLedger.SilentPayments.deriveAccountSpAddress
          InternalSpec.SilentPayments.deriveAccountSpAddress
        dsimp only [Bind.bind, Except.bind]
        split
        · contradiction
        · rename_i hCode0
          injection hCode0 with hOpt0
          injection hOpt0 with hm0
          exact absurd hm0 hm
        · rename_i labelOpt hNot0 hCode
          injection hCode with hOptEq
          subst hOptEq
          symm
          split
          · contradiction
          · rename_i hRhs0
            injection hRhs0 with hOptR0
            injection hOptR0 with hmR0
            exact absurd hmR0 hm
          · rename_i labelOptR _ hRhs
            injection hRhs with hRhsEq
            subst hRhsEq
            symm
            dsimp only
            rw [labeledSpendKey_refines_spec]
            cases c.pointMul account.scanKey (.affine c.generator) with
            | infinity => rfl
            | affine bScanPub =>
              cases InternalSpec.SilentPayments.labeledSpendKey c account.spendKey account.scanKey m <;> rfl

theorem deriveAccountTweakScript_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (account : SilentPaymentAccount Affine) (tweakBytes : Bytes32) :
    BitcoinLedger.SilentPayments.deriveAccountTweakScript c account tweakBytes =
      InternalSpec.SilentPayments.deriveAccountTweakScript c account tweakBytes := by
  unfold BitcoinLedger.SilentPayments.deriveAccountTweakScript
    InternalSpec.SilentPayments.deriveAccountTweakScript
  rw [parseScalarStrict_eq]
  cases InternalSpec.SilentPayments.parseScalarStrict tweakBytes with
  | none => rfl
  | some t =>
    dsimp only [Bind.bind, Except.bind]
    cases c.pointAdd (.affine account.spendKey) (c.pointMul t (.affine c.generator)) <;> rfl

theorem exportSpScanKey_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (bech : Bech32mCodec) (hrp : SpScanHrp)
    (deriveAccount : UInt32 → Except SpError (SilentPaymentAccount Affine))
    (accountIndex : UInt32) (userApproved : Bool) :
    BitcoinLedger.SilentPayments.exportSpScanKey c bech hrp deriveAccount accountIndex userApproved =
      InternalSpec.SilentPayments.exportSpScanKey c bech hrp deriveAccount accountIndex userApproved := by
  unfold BitcoinLedger.SilentPayments.exportSpScanKey InternalSpec.SilentPayments.exportSpScanKey
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [bip32HardenedBit_eq]
  by_cases hIdx : InternalSpec.SilentPayments.bip32HardenedBit ≤ accountIndex
  · simp [hIdx]
  · simp only [hIdx, decide_false, ↓reduceIte]
    cases deriveAccount accountIndex with
    | error e => rfl
    | ok acc =>
      dsimp only
      cases (!userApproved) with
      | true => rfl
      | false =>
        exact encodeSpScanKey_refines_spec c bech hrp acc.scanKey acc.spendKey

/-! ## 3. Eligible Inputs, `BIP0352/Inputs` Hash, Sender ECDH & BIP-374 DLEQ Refinement -/

theorem classifySpInputScript_p2tr_nums :
    BitcoinLedger.SilentPayments.classifySpInputScript
      (BitcoinLedger.SilentPayments.mkP2trScript BitcoinLedger.SilentPayments.bip341NumsXOnly).bytes none =
      .tr true := by
  decide

theorem isInputTaproot_eq (inp : PsbtSpInput) :
    BitcoinLedger.SilentPayments.isInputTaproot inp = inp.isTaproot := rfl

theorem effectiveInputSighashType_eq (inp : PsbtSpInput) :
    BitcoinLedger.SilentPayments.effectiveInputSighashType inp = inp.effectiveSighashType := rfl

theorem isInputEligible_eq (inp : PsbtSpInput) :
    BitcoinLedger.SilentPayments.isInputEligible inp = inp.isEligible := by
  unfold BitcoinLedger.SilentPayments.isInputEligible PsbtSpInput.isEligible
  rw [bip341NumsXOnly_eq]
  cases inp.scriptKind <;> rfl

theorem outpointBytes_eq (op : OutPoint) :
    BitcoinLedger.SilentPayments.outpointBytes op = InternalSpec.SilentPayments.outpointBytes op := rfl

theorem listLexLt_eq :
    BitcoinLedger.SilentPayments.listLexLt = InternalSpec.SilentPayments.listLexLt := by
  funext xs ys
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      simp only [BitcoinLedger.SilentPayments.listLexLt, InternalSpec.SilentPayments.listLexLt, ih]

theorem smallestOutpointBytes_refines_spec (ops : List OutPoint) :
    BitcoinLedger.SilentPayments.smallestOutpointBytes ops =
      InternalSpec.SilentPayments.smallestOutpointBytes ops := by
  cases ops with
  | nil => rfl
  | cons op rest =>
    unfold BitcoinLedger.SilentPayments.smallestOutpointBytes
      InternalSpec.SilentPayments.smallestOutpointBytes
    dsimp only
    rw [outpointBytes_eq, listLexLt_eq]
    have hFn :
        (fun best cur =>
          let curB := BitcoinLedger.SilentPayments.outpointBytes cur
          if InternalSpec.SilentPayments.listLexLt curB.bytes.data.toList best.bytes.data.toList then curB else best) =
        (fun best cur =>
          let curB := InternalSpec.SilentPayments.outpointBytes cur
          if InternalSpec.SilentPayments.listLexLt curB.bytes.data.toList best.bytes.data.toList then curB else best) := by
      funext best cur
      rfl
    rw [hFn]

theorem normalizeInputPrivKey_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (d : Nat) (isTaproot : Bool) :
    BitcoinLedger.SilentPayments.normalizeInputPrivKey c d isTaproot =
      InternalSpec.SilentPayments.normalizeInputPrivKey c d isTaproot := by
  unfold BitcoinLedger.SilentPayments.normalizeInputPrivKey
    InternalSpec.SilentPayments.normalizeInputPrivKey
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [secp256k1Order_eq]
  cases (!(decide (0 < d) && decide (d < InternalSpec.SilentPayments.secp256k1Order))) with
  | true => rfl
  | false =>
    cases (!isTaproot) with
    | true => rfl
    | false =>
      cases c.pointMul d (.affine c.generator) <;> rfl

theorem computeInputHash_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (outpoints : List OutPoint) (inputKeySum : SpPoint Affine) :
    BitcoinLedger.SilentPayments.computeInputHash c outpoints inputKeySum =
      InternalSpec.SilentPayments.computeInputHash c outpoints inputKeySum := by
  unfold BitcoinLedger.SilentPayments.computeInputHash InternalSpec.SilentPayments.computeInputHash
  rw [smallestOutpointBytes_refines_spec]
  cases InternalSpec.SilentPayments.smallestOutpointBytes outpoints with
  | error e => rfl
  | ok smallest =>
    dsimp only [Bind.bind, Except.bind]
    cases inputKeySum with
    | infinity => rfl
    | affine aAffine =>
      dsimp only [Bind.bind, Except.bind]
      rw [appendBytes_eq, parseNonZeroScalar_eq]
      cases InternalSpec.SilentPayments.parseNonZeroScalar _ <;> rfl

theorem ecdhShare_refines_spec {Affine : Type} (c : SpCrypto Affine) (a : Nat) (bScan : Affine) :
    BitcoinLedger.SilentPayments.ecdhShare c a bScan =
      InternalSpec.SilentPayments.ecdhShare c a bScan := rfl

theorem sharedSecret_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (inputHashScalar : Nat) (share : SpPoint Affine) :
    BitcoinLedger.SilentPayments.sharedSecret c inputHashScalar share =
      InternalSpec.SilentPayments.sharedSecret c inputHashScalar share := rfl

theorem outputTweak_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (secret : Affine) (k : UInt32) :
    BitcoinLedger.SilentPayments.outputTweak c secret k =
      InternalSpec.SilentPayments.outputTweak c secret k := by
  unfold BitcoinLedger.SilentPayments.outputTweak InternalSpec.SilentPayments.outputTweak
  dsimp only
  rw [encodeU32BE_eq, appendBytes_eq, parseNonZeroScalar_eq]
  cases InternalSpec.SilentPayments.parseNonZeroScalar _ <;> rfl

theorem outputKey_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (secret bSpend : Affine) (k : UInt32) :
    BitcoinLedger.SilentPayments.outputKey c secret bSpend k =
      InternalSpec.SilentPayments.outputKey c secret bSpend k := by
  unfold BitcoinLedger.SilentPayments.outputKey InternalSpec.SilentPayments.outputKey
  rw [outputTweak_refines_spec]
  cases InternalSpec.SilentPayments.outputTweak c secret k <;> rfl

theorem lookupCounter_eq {Affine : Type} [DecidableEq Affine] (scan : Affine) :
    ∀ cs, BitcoinLedger.SilentPayments.lookupCounter scan cs =
      InternalSpec.SilentPayments.lookupCounter scan cs
  | [] => rfl
  | (s, cnt) :: rest => by
    simp only [BitcoinLedger.SilentPayments.lookupCounter, InternalSpec.SilentPayments.lookupCounter]
    have hBeq : (s == scan) = decide (s = scan) := rfl
    rw [hBeq, lookupCounter_eq scan rest]

theorem incrementCounter_eq {Affine : Type} [DecidableEq Affine] (scan : Affine) :
    ∀ cs, BitcoinLedger.SilentPayments.incrementCounter scan cs =
      InternalSpec.SilentPayments.incrementCounter scan cs
  | [] => rfl
  | (s, cnt) :: rest => by
    simp only [BitcoinLedger.SilentPayments.incrementCounter,
      InternalSpec.SilentPayments.incrementCounter]
    have hBeq : (s == scan) = decide (s = scan) := rfl
    rw [hBeq, incrementCounter_eq scan rest]

theorem assignKLoop_eq {Affine : Type} [DecidableEq Affine] :
    ∀ (codes : List (SilentPaymentCode Affine)) (counters : List (Affine × Nat)),
      BitcoinLedger.SilentPayments.assignKLoop codes counters =
        InternalSpec.SilentPayments.assignKLoop codes counters
  | [], _ => rfl
  | code :: rest, counters => by
    unfold BitcoinLedger.SilentPayments.assignKLoop InternalSpec.SilentPayments.assignKLoop
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [lookupCounter_eq, spMaxOutputsPerScanKey_eq, incrementCounter_eq]
    by_cases hGe : InternalSpec.SilentPayments.lookupCounter code.scan counters ≥
        InternalSpec.SilentPayments.spMaxOutputsPerScanKey
    · simp [hGe]
    · simp only [hGe, decide_false, ↓reduceIte]
      rw [assignKLoop_eq rest _]
      cases InternalSpec.SilentPayments.assignKLoop rest _ <;> rfl

theorem assignK_refines_spec {Affine : Type} [DecidableEq Affine]
    (recipients : List (SilentPaymentCode Affine)) :
    BitcoinLedger.SilentPayments.assignK recipients =
      InternalSpec.SilentPayments.assignK recipients :=
  assignKLoop_eq recipients []

theorem receiverSpendingKey_refines_spec (bSpend tweak : Nat) :
    BitcoinLedger.SilentPayments.receiverSpendingKey bSpend tweak =
      InternalSpec.SilentPayments.receiverSpendingKey bSpend tweak := by
  unfold BitcoinLedger.SilentPayments.receiverSpendingKey
    InternalSpec.SilentPayments.receiverSpendingKey
  dsimp only
  rw [secp256k1Order_eq, nat_beq_eq_decide]

theorem dleqChallenge_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (aPub b cPt g r1 r2 : Affine) (msg : Option Bytes32) :
    BitcoinLedger.SilentPayments.dleqChallenge c aPub b cPt g r1 r2 msg =
      InternalSpec.SilentPayments.dleqChallenge c aPub b cPt g r1 r2 msg := rfl

theorem splitDleqProof_eq (proof : Bytes64) :
    BitcoinLedger.SilentPayments.splitDleqProof proof =
      InternalSpec.SilentPayments.splitDleqProof proof := rfl

theorem dleqVerify_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (aPub b cPt : Affine) (proof : Bytes64) (g : Affine) (msg : Option Bytes32) :
    BitcoinLedger.SilentPayments.dleqVerify c aPub b cPt proof g msg =
      InternalSpec.SilentPayments.dleqVerify c aPub b cPt proof g msg := by
  unfold BitcoinLedger.SilentPayments.dleqVerify InternalSpec.SilentPayments.dleqVerify
  rw [splitDleqProof_eq]
  cases InternalSpec.SilentPayments.splitDleqProof proof with
  | mk eBytes sBytes =>
    dsimp only
    rw [parseScalarStrict_eq, parseScalarStrict_eq]
    cases InternalSpec.SilentPayments.parseScalarStrict eBytes with
    | none => rfl
    | some e =>
      cases InternalSpec.SilentPayments.parseScalarStrict sBytes with
      | none => rfl
      | some s =>
        dsimp only
        rw [secp256k1Order_eq]
        cases c.pointAdd (c.pointMul s (.affine g))
            (c.pointMul ((InternalSpec.SilentPayments.secp256k1Order - e % InternalSpec.SilentPayments.secp256k1Order) % InternalSpec.SilentPayments.secp256k1Order) (.affine aPub)) with
        | infinity => rfl
        | affine r1 =>
          cases c.pointAdd (c.pointMul s (.affine b))
              (c.pointMul ((InternalSpec.SilentPayments.secp256k1Order - e % InternalSpec.SilentPayments.secp256k1Order) % InternalSpec.SilentPayments.secp256k1Order) (.affine cPt)) with
          | infinity => rfl
          | affine r2 =>
            dsimp only
            rw [dleqChallenge_refines_spec, nat_beq_eq_decide]

theorem dleqNonce_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (aPub cPt : Affine) (auxRand : Bytes32) (msg : Option Bytes32) :
    BitcoinLedger.SilentPayments.dleqNonce c a aPub cPt auxRand msg =
      InternalSpec.SilentPayments.dleqNonce c a aPub cPt auxRand msg := by
  unfold BitcoinLedger.SilentPayments.dleqNonce InternalSpec.SilentPayments.dleqNonce
  dsimp only
  rw [scalarToBytes32_eq, xorBytes32_eq, concatBytes_eq, parseScalarModN_eq]
  cases msg <;> rfl

theorem dleqProve_refines_spec {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (b : Affine) (auxRand : Bytes32) (g : Affine) (msg : Option Bytes32) :
    BitcoinLedger.SilentPayments.dleqProve c a b auxRand g msg =
      InternalSpec.SilentPayments.dleqProve c a b auxRand g msg := by
  unfold BitcoinLedger.SilentPayments.dleqProve InternalSpec.SilentPayments.dleqProve
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [secp256k1Order_eq]
  cases (!(decide (0 < a) && decide (a < InternalSpec.SilentPayments.secp256k1Order))) with
  | true => rfl
  | false =>
    cases c.pointMul a (.affine g) with
    | infinity => rfl
    | affine aPub =>
      dsimp only [Bind.bind, Except.bind]
      cases c.pointMul a (.affine b) with
      | infinity => rfl
      | affine cPt =>
        dsimp only [Bind.bind, Except.bind]
        rw [dleqNonce_refines_spec, nat_beq_eq_decide]
        cases decide (InternalSpec.SilentPayments.dleqNonce c a aPub cPt auxRand msg = 0) with
        | true => rfl
        | false =>
          cases c.pointMul (InternalSpec.SilentPayments.dleqNonce c a aPub cPt auxRand msg) (.affine g) with
          | infinity => rfl
          | affine r1 =>
            dsimp only [Bind.bind, Except.bind]
            cases c.pointMul (InternalSpec.SilentPayments.dleqNonce c a aPub cPt auxRand msg) (.affine b) with
            | infinity => rfl
            | affine r2 =>
              dsimp only [Bind.bind, Except.bind]
              rw [dleqChallenge_refines_spec, scalarToBytes32_eq, scalarToBytes32_eq,
                  appendSized_eq, dleqVerify_refines_spec]

theorem impl_dleqProve_implies_dleqVerify {Affine : Type} (c : SpCrypto Affine)
    (a : Nat) (b g : Affine) (auxRand : Bytes32) (msg : Option Bytes32) (proof : Bytes64)
    (hProve : BitcoinLedger.SilentPayments.dleqProve c a b auxRand g msg = .ok proof) :
    ∃ (aPub cPt : Affine),
      c.pointMul a (.affine g) = .affine aPub ∧
      c.pointMul a (.affine b) = .affine cPt ∧
      BitcoinLedger.SilentPayments.dleqVerify c aPub b cPt proof g msg = true := by
  rw [dleqProve_refines_spec] at hProve
  rcases InternalSpec.SilentPayments.dleqProve_implies_dleqVerify c a b g auxRand msg proof hProve with
    ⟨aPub, cPt, hAG, hAB, hVer⟩
  exact ⟨aPub, cPt, hAG, hAB, by rw [dleqVerify_refines_spec]; exact hVer⟩

/-! ## 4. BIP-375 PSBT Silent Payment Validation, Finalization & Security Theorems -/

theorem mapM_congr_except {α β ε : Type} {f g : α → Except ε β} (hfg : ∀ x, f x = g x) :
    ∀ xs : List α, List.mapM (m := Except ε) f xs = List.mapM (m := Except ε) g xs := by
  have hFun : f = g := funext hfg
  rw [hFun]
  intro _
  rfl

theorem foldlM_congr_except {α β ε : Type} {f g : β → α → Except ε β} (hfg : ∀ b a, f b a = g b a) :
    ∀ (init : β) (xs : List α),
      List.foldlM (m := Except ε) f init xs = List.foldlM (m := Except ε) g init xs := by
  have hFun : f = g := funext fun b => funext fun a => hfg b a
  rw [hFun]
  intro _ _
  rfl

theorem forIn'_loop_ignore_mem {α β ε : Type}
    (f : α → β → Except ε (ForInStep β)) (xs1 xs2 : List α) :
    ∀ (as : List α) (b : β) (h1 : ∃ bs, bs ++ as = xs1) (h2 : ∃ bs, bs ++ as = xs2),
      List.forIn'.loop (m := Except ε) xs1 (fun a _ b => f a b) as b h1 =
      List.forIn'.loop (m := Except ε) xs2 (fun a _ b => f a b) as b h2
  | [], _, _, _ => rfl
  | a :: as, b, ⟨bs1, hbs1⟩, ⟨bs2, hbs2⟩ => by
    unfold List.forIn'.loop
    dsimp only [Bind.bind, Except.bind]
    cases f a b with
    | error _ => rfl
    | ok step =>
      cases step with
      | done _ => rfl
      | yield b' =>
        exact forIn'_loop_ignore_mem f xs1 xs2 as b'
          ⟨bs1 ++ [a], by rw [List.append_assoc, List.singleton_append, hbs1]⟩
          ⟨bs2 ++ [a], by rw [List.append_assoc, List.singleton_append, hbs2]⟩

theorem validatePsbtSpOutputsLoop_eq_forIn (modFlag : Bool) :
    ∀ outs : List PsbtSpOutput,
      BitcoinLedger.SilentPayments.validatePsbtSpOutputsLoop modFlag outs =
        (do
          for out in outs do
            match out.script, out.spV0Info with
            | none, none => Except.error SpError.missingOutputScript
            | some _, some _ =>
              if modFlag then Except.error SpError.invalidSilentPaymentField else pure ()
            | _, _ => pure ()
            if out.spV0Label.isSome && out.spV0Info.isNone then
              Except.error SpError.invalidSilentPaymentField
            if out.spV0Info.isSome && (out.hasAccountCoordinates || out.hasIdAuthProofs) then
              Except.error SpError.invalidSilentPaymentField)
  | [] => rfl
  | out :: rest => by
    have ih := validatePsbtSpOutputsLoop_eq_forIn modFlag rest
    dsimp only [ForIn'.forIn', ForIn.forIn, List.forIn'] at ih ⊢
    unfold List.forIn'.loop
    unfold BitcoinLedger.SilentPayments.validatePsbtSpOutputsLoop
      BitcoinLedger.SilentPayments.validatePsbtSpOutputOne
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
    cases out.script <;> cases out.spV0Info <;> cases modFlag <;>
      cases out.spV0Label <;> cases out.hasAccountCoordinates <;> cases out.hasIdAuthProofs <;>
      first
      | rfl
      | (simp only [Option.isSome, Option.isNone, Bool.and_false, Bool.and_true,
           Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte];
         rw [forIn'_loop_ignore_mem _ (out :: rest) rest];
         exact ih)

theorem nat_bne_zero_eq_decide (n : Nat) : (n != 0) = decide (n ≠ 0) := by
  show (!(n == 0)) = decide (n ≠ 0)
  rw [nat_beq_eq_decide]
  by_cases h : n = 0 <;> simp [h]

theorem validatePsbtSpOutputs_refines_spec (outputs : List PsbtSpOutput)
    (txModifiable : Option UInt8) :
    BitcoinLedger.SilentPayments.validatePsbtSpOutputs outputs txModifiable =
      InternalSpec.SilentPayments.validatePsbtSpOutputs outputs txModifiable := by
  unfold BitcoinLedger.SilentPayments.validatePsbtSpOutputs
    InternalSpec.SilentPayments.validatePsbtSpOutputs
  dsimp only
  rw [nat_bne_zero_eq_decide, validatePsbtSpOutputsLoop_eq_forIn]
  rfl

theorem findAccountByScanKey_eq {Affine : Type} [DecidableEq Affine] (c : SpCrypto Affine)
    (scanPt : Affine) :
    ∀ accounts : List (SilentPaymentAccount Affine),
      BitcoinLedger.SilentPayments.findAccountByScanKey c scanPt accounts =
        accounts.find? (fun acc =>
          match c.pointMul acc.scanKey (.affine c.generator) with
          | .affine scanPub => decide (scanPub = scanPt)
          | .infinity => false)
  | [] => rfl
  | acc :: rest => by
    have ih := findAccountByScanKey_eq c scanPt rest
    unfold BitcoinLedger.SilentPayments.findAccountByScanKey List.find?
    dsimp only
    cases hMul : c.pointMul acc.scanKey (.affine c.generator) with
    | infinity =>
      dsimp only
      exact ih
    | affine pub =>
      dsimp only
      by_cases hEq : pub = scanPt
      · simp [hEq]
      · simp [hEq, ih]

theorem verifyOutputSpLabel_refines_spec {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (accounts : List (SilentPaymentAccount Affine))
    (code : SilentPaymentCode Affine) (labelOpt : Option UInt32) :
    BitcoinLedger.SilentPayments.verifyOutputSpLabel c accounts code labelOpt =
      InternalSpec.SilentPayments.verifyOutputSpLabel c accounts code labelOpt := by
  unfold BitcoinLedger.SilentPayments.verifyOutputSpLabel
    InternalSpec.SilentPayments.verifyOutputSpLabel
  cases labelOpt with
  | none => rfl
  | some m =>
    dsimp only
    rw [findAccountByScanKey_eq]
    cases accounts.find? _ with
    | none => rfl
    | some acc =>
      dsimp only [Bind.bind, Except.bind]
      rw [labeledSpendKey_refines_spec]
      cases InternalSpec.SilentPayments.labeledSpendKey c acc.spendKey acc.scanKey m <;> rfl

theorem collectSpRecipients_refines_spec {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (accounts : List (SilentPaymentAccount Affine)) :
    ∀ (idx : Nat) (outs : List PsbtSpOutput),
      BitcoinLedger.SilentPayments.collectSpRecipients c accounts idx outs =
        InternalSpec.SilentPayments.collectSpRecipients c accounts idx outs
  | _, [] => rfl
  | idx, out :: rest => by
    unfold BitcoinLedger.SilentPayments.collectSpRecipients
      InternalSpec.SilentPayments.collectSpRecipients
    rw [collectSpRecipients_refines_spec c accounts (idx + 1) rest]
    cases InternalSpec.SilentPayments.collectSpRecipients c accounts (idx + 1) rest with
    | error e => rfl
    | ok tail =>
      dsimp only [Bind.bind, Except.bind]
      cases out.spV0Info with
      | none => rfl
      | some raw66 =>
        dsimp only [Bind.bind, Except.bind]
        rw [deserializeSpCode_eq]
        cases SilentPaymentCode.fromBytes c raw66 with
        | error e => rfl
        | ok code =>
          dsimp only [Bind.bind, Except.bind]
          rw [verifyOutputSpLabel_refines_spec]
          cases InternalSpec.SilentPayments.verifyOutputSpLabel c accounts code out.spV0Label <;> rfl

theorem eq_of_foldlM_eq {ε α β : Type} {f1 f2 : β → α → Except ε β} {init : β} {xs : List α}
    {r1 r2 : Except ε β} (h1 : List.foldlM f1 init xs = r1) (h2 : List.foldlM f2 init xs = r2)
    (hf : ∀ b a, f1 b a = f2 b a) : r1 = r2 := by
  have h := foldlM_congr_except hf init xs
  rw [h1, h2] at h
  exact h

theorem eq_of_mapM_eq {ε α β : Type} {f1 f2 : α → Except ε β} {xs : List α}
    {r1 r2 : Except ε (List β)} (h1 : List.mapM f1 xs = r1) (h2 : List.mapM f2 xs = r2)
    (hf : ∀ a, f1 a = f2 a) : r1 = r2 := by
  have h := mapM_congr_except hf xs
  rw [h1, h2] at h
  exact h

theorem checkScanKeysInRecipients_eq_forIn {β : Type} (recipientScanKeys : List Bytes33) :
    ∀ pairs : List (Bytes33 × β),
      BitcoinLedger.SilentPayments.checkScanKeysInRecipients recipientScanKeys pairs =
        (do
          for (scanK, _) in pairs do
            if !InternalSpec.SilentPayments.spListMem scanK recipientScanKeys then
              Except.error SpError.silentPaymentShareMismatch)
  | [] => rfl
  | (scanK, v) :: rest => by
    have ih := checkScanKeysInRecipients_eq_forIn recipientScanKeys rest
    dsimp only [ForIn'.forIn', ForIn.forIn, List.forIn'] at ih ⊢
    unfold List.forIn'.loop
    unfold BitcoinLedger.SilentPayments.checkScanKeysInRecipients
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
    rw [spListMem_eq]
    cases (!InternalSpec.SilentPayments.spListMem scanK recipientScanKeys) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [forIn'_loop_ignore_mem _ ((scanK, v) :: rest) rest]
      exact ih

theorem analyzeSpInputStep_eq {Affine : Type} (c : SpCrypto Affine)
    (acc : List Nat) (inp : PsbtSpInput) :
    BitcoinLedger.SilentPayments.analyzeSpInputStep c acc inp =
      (match inp.prevoutWitnessVersion with
       | some v =>
         if decide (1 < v) then Except.error SpError.silentPaymentSegwitVersion
         else if decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) then
           Except.error SpError.silentPaymentSighashType
         else if inp.hasInputSpEcdhShare || inp.hasInputSpDleq then
           Except.error SpError.silentPaymentShareMismatch
         else if !inp.isEligible then
           Except.ok acc
         else
           match inp.deviceEligiblePrivKey with
           | none => Except.error SpError.silentPaymentInputNotHeld
           | some rawPriv =>
             match InternalSpec.SilentPayments.normalizeInputPrivKey c rawPriv
                 (match inp.scriptKind with | .tr _ => true | _ => false) with
             | .error err => Except.error err
             | .ok v => Except.ok (acc ++ [v])
       | none =>
         if decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) then
           Except.error SpError.silentPaymentSighashType
         else if inp.hasInputSpEcdhShare || inp.hasInputSpDleq then
           Except.error SpError.silentPaymentShareMismatch
         else if !inp.isEligible then
           Except.ok acc
         else
           match inp.deviceEligiblePrivKey with
           | none => Except.error SpError.silentPaymentInputNotHeld
           | some rawPriv =>
             match InternalSpec.SilentPayments.normalizeInputPrivKey c rawPriv
                 (match inp.scriptKind with | .tr _ => true | _ => false) with
             | .error err => Except.error err
             | .ok v => Except.ok (acc ++ [v])) := by
  unfold BitcoinLedger.SilentPayments.analyzeSpInputStep
  dsimp only
  rw [effectiveInputSighashType_eq, sighashAll_eq, isInputEligible_eq]
  cases inp.prevoutWitnessVersion with
  | none =>
    dsimp only
    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) with
    | true => rfl
    | false =>
      cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) with
      | true => rfl
      | false =>
        cases (!inp.isEligible) with
        | true => rfl
        | false =>
          cases inp.deviceEligiblePrivKey with
          | none => rfl
          | some rawPriv =>
            dsimp only
            rw [normalizeInputPrivKey_refines_spec]
            cases InternalSpec.SilentPayments.normalizeInputPrivKey c rawPriv _ <;> rfl
  | some v =>
    dsimp only
    cases decide (1 < v) with
    | true => rfl
    | false =>
      cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) with
      | true => rfl
      | false =>
        cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) with
        | true => rfl
        | false =>
          cases (!inp.isEligible) with
          | true => rfl
          | false =>
            cases inp.deviceEligiblePrivKey with
            | none => rfl
            | some rawPriv =>
              dsimp only
              rw [normalizeInputPrivKey_refines_spec]
              cases InternalSpec.SilentPayments.normalizeInputPrivKey c rawPriv _ <;> rfl

theorem analyzePsbtSilentPayments_refines_spec {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (psbt : PsbtSpTx Affine) :
    BitcoinLedger.SilentPayments.analyzePsbtSilentPayments c psbt =
      InternalSpec.SilentPayments.analyzePsbtSilentPayments c psbt := by
  unfold BitcoinLedger.SilentPayments.analyzePsbtSilentPayments
    InternalSpec.SilentPayments.analyzePsbtSilentPayments
  rw [validatePsbtSpOutputs_refines_spec]
  cases InternalSpec.SilentPayments.validatePsbtSpOutputs psbt.outputs psbt.txModifiable with
  | error e => rfl
  | ok u =>
    cases u
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [collectSpRecipients_refines_spec]
    cases InternalSpec.SilentPayments.collectSpRecipients c psbt.spAccounts 0 psbt.outputs with
    | error e => rfl
    | ok indexedCodes =>
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      cases indexedCodes.isEmpty with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [assignK_refines_spec]
        cases InternalSpec.SilentPayments.assignK (indexedCodes.map Prod.snd) with
        | error e => rfl
        | ok ks =>
          dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          split <;> rename_i x1 h1
          · apply Eq.symm; split <;> rename_i x2 h2 <;> apply Eq.symm
            · have hErr := eq_of_foldlM_eq h1 h2 (by
                intro acc inp
                unfold BitcoinLedger.SilentPayments.analyzeSpInputStep
                dsimp only
                rw [effectiveInputSighashType_eq, sighashAll_eq, isInputEligible_eq]
                cases inp.prevoutWitnessVersion with
                | none =>
                  cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl
                | some v =>
                  dsimp only
                  by_cases hv : (1 : UInt8) < v <;> simp only [hv, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
                    cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl)
              injection hErr with hE
              subst hE
              rfl
            · exfalso
              have hEq := eq_of_foldlM_eq h1 h2 (by
                intro acc inp
                unfold BitcoinLedger.SilentPayments.analyzeSpInputStep
                dsimp only
                rw [effectiveInputSighashType_eq, sighashAll_eq, isInputEligible_eq]
                cases inp.prevoutWitnessVersion with
                | none =>
                  cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl
                | some v =>
                  dsimp only
                  by_cases hv : (1 : UInt8) < v <;> simp only [hv, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
                    cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl)
              cases hEq
          · apply Eq.symm; split <;> rename_i x2 h2 <;> apply Eq.symm
            · exfalso
              have hEq := eq_of_foldlM_eq h1 h2 (by
                intro acc inp
                unfold BitcoinLedger.SilentPayments.analyzeSpInputStep
                dsimp only
                rw [effectiveInputSighashType_eq, sighashAll_eq, isInputEligible_eq]
                cases inp.prevoutWitnessVersion with
                | none =>
                  cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl
                | some v =>
                  dsimp only
                  by_cases hv : (1 : UInt8) < v <;> simp only [hv, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
                    cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl)
              cases hEq
            · have hEq := eq_of_foldlM_eq h1 h2 (by
                intro acc inp
                unfold BitcoinLedger.SilentPayments.analyzeSpInputStep
                dsimp only
                rw [effectiveInputSighashType_eq, sighashAll_eq, isInputEligible_eq]
                cases inp.prevoutWitnessVersion with
                | none =>
                  cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl
                | some v =>
                  dsimp only
                  by_cases hv : (1 : UInt8) < v <;> simp only [hv, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] <;>
                    cases inp.scriptKind <;> dsimp only <;>
                    cases decide (inp.effectiveSighashType ≠ InternalSpec.SilentPayments.sighashAll) <;>
                    cases (inp.hasInputSpEcdhShare || inp.hasInputSpDleq) <;>
                    cases (!inp.isEligible) <;>
                    cases inp.deviceEligiblePrivKey <;>
                    simp only [normalizeInputPrivKey_refines_spec] <;>
                    (try cases InternalSpec.SilentPayments.normalizeInputPrivKey c _ _) <;>
                    rfl)
              injection hEq with hKeysEq
              subst hKeysEq
              cases x1.isEmpty with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                have hChk1 := checkScanKeysInRecipients_eq_forIn
                  (indexedCodes.map (fun (_, code) => c.compress code.scan)) psbt.globalEcdhShares
                dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hChk1
                rw [hChk1]
                cases forIn (m := Except SpError) psbt.globalEcdhShares PUnit.unit
                    (fun x _ => if !InternalSpec.SilentPayments.spListMem x.fst
                        (indexedCodes.map (fun x => c.compress x.snd.scan)) then
                      Except.error SpError.silentPaymentShareMismatch
                    else Except.ok (ForInStep.yield PUnit.unit)) with
                | error e => rfl
                | ok u2 =>
                  cases u2
                  dsimp only
                  have hChk2 := checkScanKeysInRecipients_eq_forIn
                    (indexedCodes.map (fun (_, code) => c.compress code.scan)) psbt.globalDleqProofs
                  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at hChk2
                  rw [hChk2]
                  cases forIn (m := Except SpError) psbt.globalDleqProofs PUnit.unit
                      (fun x _ => if !InternalSpec.SilentPayments.spListMem x.fst
                          (indexedCodes.map (fun x => c.compress x.snd.scan)) then
                        Except.error SpError.silentPaymentShareMismatch
                      else Except.ok (ForInStep.yield PUnit.unit)) <;> rfl

theorem lookupByScanBytes_eq {β : Type} (scanBytes : Bytes33) :
    ∀ pairs : List (Bytes33 × β),
      BitcoinLedger.SilentPayments.lookupByScanBytes scanBytes pairs =
        (pairs.find? (fun p => p.1 == scanBytes)).map Prod.snd
  | [] => rfl
  | (k, v) :: rest => by
    simp only [BitcoinLedger.SilentPayments.lookupByScanBytes, List.find?]
    have hBeq : (k == scanBytes) = decide (k = scanBytes) := rfl
    rw [hBeq]
    cases decide (k = scanBytes) <;> simp [lookupByScanBytes_eq scanBytes rest]

theorem lookupShareTuple_eq {Affine : Type} [DecidableEq Affine] (scanPt : Affine) :
    ∀ entries : List (Affine × Affine × SilentPaymentShareOut),
      BitcoinLedger.SilentPayments.lookupShareTuple scanPt entries =
        entries.find? (fun (s, _, _) => s == scanPt)
  | [] => rfl
  | (s, sh, out) :: rest => by
    simp only [BitcoinLedger.SilentPayments.lookupShareTuple, List.find?]
    have hBeq : (s == scanPt) = decide (s = scanPt) := rfl
    rw [hBeq]
    cases decide (s = scanPt) <;> simp [lookupShareTuple_eq scanPt rest]

theorem finalizePsbtSilentPayments_refines_spec {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (psbt : PsbtSpTx Affine) (dleqAuxRand : Bytes32) :
    BitcoinLedger.SilentPayments.finalizePsbtSilentPayments c psbt dleqAuxRand =
      InternalSpec.SilentPayments.finalizePsbtSilentPayments c psbt dleqAuxRand := by
  unfold BitcoinLedger.SilentPayments.finalizePsbtSilentPayments
    InternalSpec.SilentPayments.finalizePsbtSilentPayments
  rw [analyzePsbtSilentPayments_refines_spec]
  cases InternalSpec.SilentPayments.analyzePsbtSilentPayments c psbt with
  | error e => rfl
  | ok opt =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases opt with
    | none => rfl
    | some triple =>
      rcases triple with ⟨indexedCodes, ks, eligibleKeys⟩
      dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
      rw [secp256k1Order_eq, nat_beq_eq_decide]
      cases decide
        (eligibleKeys.foldl (fun acc k => (acc + k) % InternalSpec.SilentPayments.secp256k1Order) 0 = 0) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases c.pointMul
          (eligibleKeys.foldl (fun acc k => (acc + k) % InternalSpec.SilentPayments.secp256k1Order) 0)
          (.affine c.generator) with
        | infinity => rfl
        | affine aPub =>
          dsimp only [Bind.bind, Except.bind]
          rw [computeInputHash_refines_spec]
          cases InternalSpec.SilentPayments.computeInputHash c (psbt.inputs.map (·.outpoint)) (.affine aPub) with
          | error e => rfl
          | ok inHash =>
            dsimp only [Bind.bind, Except.bind]
            have hDistinct :
                (indexedCodes.foldl (fun acc (_, code) =>
                  if BitcoinLedger.SilentPayments.spListMem code.scan acc then acc
                  else acc ++ [code.scan]) []) =
                (indexedCodes.foldl (fun acc x =>
                  if InternalSpec.SilentPayments.spListMem x.snd.scan acc then acc
                  else acc ++ [x.snd.scan]) []) := by
              congr 1
              funext acc pair
              rcases pair with ⟨_, code⟩
              dsimp only
              rw [spListMem_eq]
            rw [hDistinct]
            split <;> rename_i sharePairs hs1
            · apply Eq.symm; split <;> rename_i _ hs2 <;> apply Eq.symm
              · have hErr := eq_of_mapM_eq hs1 hs2 (by
                  intro scanPt
                  rw [ecdhShare_refines_spec]
                  cases InternalSpec.SilentPayments.ecdhShare c _ scanPt with
                  | infinity => rfl
                  | affine sharePt =>
                    dsimp only
                    rw [lookupByScanBytes_eq, lookupByScanBytes_eq]
                    cases (psbt.globalEcdhShares.find? _).map Prod.snd with
                    | none =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none =>
                        dsimp only
                        rw [dleqProve_refines_spec]
                        cases InternalSpec.SilentPayments.dleqProve c _ scanPt dleqAuxRand c.generator none <;> rfl
                      | some _ => rfl
                    | some exShare =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none => rfl
                      | some exProof =>
                        dsimp only
                        rw [dleqVerify_refines_spec]
                        have hEqShare : (exShare == c.compress sharePt) = decide (exShare = c.compress sharePt) := rfl
                        rw [hEqShare]
                        cases (decide (exShare = c.compress sharePt) &&
                          InternalSpec.SilentPayments.dleqVerify c aPub scanPt sharePt exProof c.generator none) <;> rfl)
                injection hErr with hE
                subst hE
                rfl
              · exfalso
                have hBad := eq_of_mapM_eq hs1 hs2 (by
                  intro scanPt
                  rw [ecdhShare_refines_spec]
                  cases InternalSpec.SilentPayments.ecdhShare c _ scanPt with
                  | infinity => rfl
                  | affine sharePt =>
                    dsimp only
                    rw [lookupByScanBytes_eq, lookupByScanBytes_eq]
                    cases (psbt.globalEcdhShares.find? _).map Prod.snd with
                    | none =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none =>
                        dsimp only
                        rw [dleqProve_refines_spec]
                        cases InternalSpec.SilentPayments.dleqProve c _ scanPt dleqAuxRand c.generator none <;> rfl
                      | some _ => rfl
                    | some exShare =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none => rfl
                      | some exProof =>
                        dsimp only
                        rw [dleqVerify_refines_spec]
                        have hEqShare : (exShare == c.compress sharePt) = decide (exShare = c.compress sharePt) := rfl
                        rw [hEqShare]
                        cases (decide (exShare = c.compress sharePt) &&
                          InternalSpec.SilentPayments.dleqVerify c aPub scanPt sharePt exProof c.generator none) <;> rfl)
                cases hBad
            · apply Eq.symm; split <;> rename_i _ hs2 <;> apply Eq.symm
              · exfalso
                have hBad := eq_of_mapM_eq hs1 hs2 (by
                  intro scanPt
                  rw [ecdhShare_refines_spec]
                  cases InternalSpec.SilentPayments.ecdhShare c _ scanPt with
                  | infinity => rfl
                  | affine sharePt =>
                    dsimp only
                    rw [lookupByScanBytes_eq, lookupByScanBytes_eq]
                    cases (psbt.globalEcdhShares.find? _).map Prod.snd with
                    | none =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none =>
                        dsimp only
                        rw [dleqProve_refines_spec]
                        cases InternalSpec.SilentPayments.dleqProve c _ scanPt dleqAuxRand c.generator none <;> rfl
                      | some _ => rfl
                    | some exShare =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none => rfl
                      | some exProof =>
                        dsimp only
                        rw [dleqVerify_refines_spec]
                        have hEqShare : (exShare == c.compress sharePt) = decide (exShare = c.compress sharePt) := rfl
                        rw [hEqShare]
                        cases (decide (exShare = c.compress sharePt) &&
                          InternalSpec.SilentPayments.dleqVerify c aPub scanPt sharePt exProof c.generator none) <;> rfl)
                cases hBad
              · have hSpOk := eq_of_mapM_eq hs1 hs2 (by
                  intro scanPt
                  rw [ecdhShare_refines_spec]
                  cases InternalSpec.SilentPayments.ecdhShare c _ scanPt with
                  | infinity => rfl
                  | affine sharePt =>
                    dsimp only
                    rw [lookupByScanBytes_eq, lookupByScanBytes_eq]
                    cases (psbt.globalEcdhShares.find? _).map Prod.snd with
                    | none =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none =>
                        dsimp only
                        rw [dleqProve_refines_spec]
                        cases InternalSpec.SilentPayments.dleqProve c _ scanPt dleqAuxRand c.generator none <;> rfl
                      | some _ => rfl
                    | some exShare =>
                      cases (psbt.globalDleqProofs.find? _).map Prod.snd with
                      | none => rfl
                      | some exProof =>
                        dsimp only
                        rw [dleqVerify_refines_spec]
                        have hEqShare : (exShare == c.compress sharePt) = decide (exShare = c.compress sharePt) := rfl
                        rw [hEqShare]
                        cases (decide (exShare = c.compress sharePt) &&
                          InternalSpec.SilentPayments.dleqVerify c aPub scanPt sharePt exProof c.generator none) <;> rfl)
                injection hSpOk with hSpEq
                subst hSpEq
                split <;> rename_i _ ho1
                · apply Eq.symm; split <;> rename_i _ ho2 <;> apply Eq.symm
                  · have hErr := eq_of_mapM_eq ho1 ho2 (by
                      intro x
                      rcases x with ⟨⟨outIdx, code⟩, k⟩
                      dsimp only
                      rw [lookupShareTuple_eq]
                      cases sharePairs.find? (fun x_1 => x_1.fst == code.scan) with
                      | none => rfl
                      | some entry =>
                        rcases entry with ⟨_, sharePt, _⟩
                        dsimp only
                        rw [sharedSecret_refines_spec]
                        cases InternalSpec.SilentPayments.sharedSecret c inHash (.affine sharePt) with
                        | error e => rfl
                        | ok secret =>
                          dsimp only
                          rw [outputKey_refines_spec]
                          cases InternalSpec.SilentPayments.outputKey c secret code.spend k with
                          | error e => rfl
                          | ok outPt =>
                            dsimp only
                            rw [mkP2trScript_eq]
                            cases psbt.outputs[outIdx]? with
                            | none => rfl
                            | some psbtOut =>
                              dsimp only
                              cases psbtOut.script with
                              | none => rfl
                              | some existing =>
                                dsimp only
                                rw [bytesEq_not_eq_bne])
                    injection hErr with hE
                    subst hE
                    rfl
                  · exfalso
                    have hBad := eq_of_mapM_eq ho1 ho2 (by
                      intro x
                      rcases x with ⟨⟨outIdx, code⟩, k⟩
                      dsimp only
                      rw [lookupShareTuple_eq]
                      cases sharePairs.find? (fun x_1 => x_1.fst == code.scan) with
                      | none => rfl
                      | some entry =>
                        rcases entry with ⟨_, sharePt, _⟩
                        dsimp only
                        rw [sharedSecret_refines_spec]
                        cases InternalSpec.SilentPayments.sharedSecret c inHash (.affine sharePt) with
                        | error e => rfl
                        | ok secret =>
                          dsimp only
                          rw [outputKey_refines_spec]
                          cases InternalSpec.SilentPayments.outputKey c secret code.spend k with
                          | error e => rfl
                          | ok outPt =>
                            dsimp only
                            rw [mkP2trScript_eq]
                            cases psbt.outputs[outIdx]? with
                            | none => rfl
                            | some psbtOut =>
                              dsimp only
                              cases psbtOut.script with
                              | none => rfl
                              | some existing =>
                                dsimp only
                                rw [bytesEq_not_eq_bne])
                    cases hBad
                · apply Eq.symm; split <;> rename_i _ ho2 <;> apply Eq.symm
                  · exfalso
                    have hBad := eq_of_mapM_eq ho1 ho2 (by
                      intro x
                      rcases x with ⟨⟨outIdx, code⟩, k⟩
                      dsimp only
                      rw [lookupShareTuple_eq]
                      cases sharePairs.find? (fun x_1 => x_1.fst == code.scan) with
                      | none => rfl
                      | some entry =>
                        rcases entry with ⟨_, sharePt, _⟩
                        dsimp only
                        rw [sharedSecret_refines_spec]
                        cases InternalSpec.SilentPayments.sharedSecret c inHash (.affine sharePt) with
                        | error e => rfl
                        | ok secret =>
                          dsimp only
                          rw [outputKey_refines_spec]
                          cases InternalSpec.SilentPayments.outputKey c secret code.spend k with
                          | error e => rfl
                          | ok outPt =>
                            dsimp only
                            rw [mkP2trScript_eq]
                            cases psbt.outputs[outIdx]? with
                            | none => rfl
                            | some psbtOut =>
                              dsimp only
                              cases psbtOut.script with
                              | none => rfl
                              | some existing =>
                                dsimp only
                                rw [bytesEq_not_eq_bne])
                    cases hBad
                  · have hOkEq := eq_of_mapM_eq ho1 ho2 (by
                      intro x
                      rcases x with ⟨⟨outIdx, code⟩, k⟩
                      dsimp only
                      rw [lookupShareTuple_eq]
                      cases sharePairs.find? (fun x_1 => x_1.fst == code.scan) with
                      | none => rfl
                      | some entry =>
                        rcases entry with ⟨_, sharePt, _⟩
                        dsimp only
                        rw [sharedSecret_refines_spec]
                        cases InternalSpec.SilentPayments.sharedSecret c inHash (.affine sharePt) with
                        | error e => rfl
                        | ok secret =>
                          dsimp only
                          rw [outputKey_refines_spec]
                          cases InternalSpec.SilentPayments.outputKey c secret code.spend k with
                          | error e => rfl
                          | ok outPt =>
                            dsimp only
                            rw [mkP2trScript_eq]
                            cases psbt.outputs[outIdx]? with
                            | none => rfl
                            | some psbtOut =>
                              dsimp only
                              cases psbtOut.script with
                              | none => rfl
                              | some existing =>
                                dsimp only
                                rw [bytesEq_not_eq_bne])
                    injection hOkEq with hOutEq
                    subst hOutEq
                    rfl

/-! ## 5. Security Rejection Theorems & Non-Vacuity Witness on `BitcoinLedger.SilentPayments` -/

/-- `deriveAccountSpAddress` strictly forbids handing out the reserved change label `m = 0`. -/
theorem impl_deriveAccountSpAddress_rejects_change_label {Affine : Type}
    (c : SpCrypto Affine) (bech : Bech32mCodec) (hrp : SpAddressHrp)
    (account : SilentPaymentAccount Affine) :
    BitcoinLedger.SilentPayments.deriveAccountSpAddress c bech hrp account (.code (some 0)) =
      .error .silentPaymentChangeLabel := rfl

/-- `exportSpScanKey` never exports a scan key without explicit `userApproved = true`. -/
theorem impl_exportSpScanKey_requires_user_consent {Affine : Type}
    (c : SpCrypto Affine) (bech : Bech32mCodec) (hrp : SpScanHrp)
    (deriveAccount : UInt32 → Except SpError (SilentPaymentAccount Affine))
    (accountIndex : UInt32) :
    ∀ s, BitcoinLedger.SilentPayments.exportSpScanKey c bech hrp deriveAccount accountIndex false ≠ .ok s := by
  rw [exportSpScanKey_refines_spec]
  exact InternalSpec.SilentPayments.exportSpScanKey_requires_user_consent c bech hrp deriveAccount accountIndex

/-- `validatePsbtSpOutputs` rejects modifiable PSBTs carrying pre-computed `script` + `spV0Info`,
    orphan `spV0Label`, or `spV0Info` combined with account coordinates / identity auth. -/
theorem impl_validatePsbtSpOutputs_exclusion_rules (raw66 : Bytes66) (scr : ByteArray) :
    BitcoinLedger.SilentPayments.validatePsbtSpOutputs
      [{ amount := 1000, script := some scr, spV0Info := some raw66, spV0Label := none }]
      (some 0x01) = .error .invalidSilentPaymentField ∧
    BitcoinLedger.SilentPayments.validatePsbtSpOutputs
      [{ amount := 1000, script := some scr, spV0Info := none, spV0Label := some 1 }]
      none = .error .invalidSilentPaymentField ∧
    BitcoinLedger.SilentPayments.validatePsbtSpOutputs
      [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none,
         hasAccountCoordinates := true }]
      none = .error .invalidSilentPaymentField ∧
    BitcoinLedger.SilentPayments.validatePsbtSpOutputs
      [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none,
         hasIdAuthProofs := true }]
      none = .error .invalidSilentPaymentField :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `analyzePsbtSilentPayments` rejects Taproot inputs with implicit `SIGHASH_DEFAULT` (`sighashType = none`). -/
theorem impl_analyzePsbtSilentPayments_rejects_taproot_implicit_sighash_default
    {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (code : SilentPaymentCode Affine) (raw66 : Bytes66)
    (hCode : BitcoinLedger.SilentPayments.deserializeSpCode c raw66 = .ok code) (op : OutPoint) :
    BitcoinLedger.SilentPayments.analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := [{
        outpoint := op
        prevoutWitnessVersion := some 1
        sighashType := none
        hasInputSpEcdhShare := false
        hasInputSpDleq := false
        scriptKind := .tr false
        deviceEligiblePrivKey := some 1
      }]
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none }]
    } = .error .silentPaymentSighashType := by
  rw [analyzePsbtSilentPayments_refines_spec]
  rw [deserializeSpCode_eq] at hCode
  exact InternalSpec.SilentPayments.analyzePsbtSilentPayments_rejects_taproot_implicit_sighash_default
    c code raw66 hCode op

/-- `analyzePsbtSilentPayments` excludes Taproot inputs with BIP-341 NUMS internal key `H`. -/
theorem impl_analyzePsbtSilentPayments_excludes_bip341_nums
    {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (code : SilentPaymentCode Affine) (raw66 : Bytes66)
    (hCode : BitcoinLedger.SilentPayments.deserializeSpCode c raw66 = .ok code) (op : OutPoint) :
    BitcoinLedger.SilentPayments.analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := [{
        outpoint := op
        prevoutWitnessVersion := some 1
        sighashType := some BitcoinLedger.SilentPayments.sighashAll
        hasInputSpEcdhShare := false
        hasInputSpDleq := false
        scriptKind := .tr false
        tapInternalKey := some BitcoinLedger.SilentPayments.bip341NumsXOnly
        deviceEligiblePrivKey := some 1
      }]
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := none }]
    } = .error .silentPaymentNoEligibleInputs := by
  rw [analyzePsbtSilentPayments_refines_spec, sighashAll_eq, bip341NumsXOnly_eq]
  rw [deserializeSpCode_eq] at hCode
  exact InternalSpec.SilentPayments.analyzePsbtSilentPayments_excludes_literal_bip341_nums
    c code raw66 hCode op

/-- `analyzePsbtSilentPayments` rejects outputs with mismatched `PSBT_OUT_SP_V0_LABEL`. -/
theorem impl_analyzePsbtSilentPayments_rejects_mismatched_spV0Label
    {Affine : Type} [DecidableEq Affine]
    (c : SpCrypto Affine) (acc : SilentPaymentAccount Affine)
    (code : SilentPaymentCode Affine) (expectedBm : Affine) (raw66 : Bytes66) (m : UInt32)
    (hCode : BitcoinLedger.SilentPayments.deserializeSpCode c raw66 = .ok code)
    (hScan : c.pointMul acc.scanKey (.affine c.generator) = .affine code.scan)
    (hLbl : BitcoinLedger.SilentPayments.labeledSpendKey c acc.spendKey acc.scanKey m = .ok expectedBm)
    (hMismatch : expectedBm ≠ code.spend) :
    BitcoinLedger.SilentPayments.analyzePsbtSilentPayments c {
      txModifiable := some 0
      globalEcdhShares := []
      globalDleqProofs := []
      inputs := []
      outputs := [{ amount := 1000, script := none, spV0Info := some raw66, spV0Label := some m }]
      spAccounts := [acc]
    } = .error .invalidSilentPaymentField := by
  rw [analyzePsbtSilentPayments_refines_spec]
  rw [deserializeSpCode_eq] at hCode
  rw [labeledSpendKey_refines_spec] at hLbl
  exact InternalSpec.SilentPayments.analyzePsbtSilentPayments_rejects_mismatched_spV0Label
    c acc code expectedBm raw66 m hCode hScan hLbl hMismatch

/-- **Non-Vacuity Witness**: `BitcoinLedger.SilentPayments.finalizePsbtSilentPayments` succeeds
    on a valid BIP-375 PSBT, producing a verified DLEQ ECDH share and P2TR output script. -/
theorem impl_nonvacuous_finalizePsbtSilentPayments_ok :
    ∃ (psbt : PsbtSpTx Unit) (shares : List SilentPaymentShareOut)
      (scripts : List SilentPaymentOutputScriptOut),
      BitcoinLedger.SilentPayments.finalizePsbtSilentPayments
        nonVacuousSpCrypto psbt spFiveByte32 = .ok (shares, scripts) ∧
      shares.length = 1 ∧
      scripts.length = 1 := by
  rcases InternalSpec.SilentPayments.nonvacuous_finalizePsbtSilentPayments_ok with
    ⟨psbt, shares, scripts, hFin, hS, hSc⟩
  refine ⟨psbt, shares, scripts, ?_, hS, hSc⟩
  rw [finalizePsbtSilentPayments_refines_spec]
  exact hFin

end Proofs.SilentPayments

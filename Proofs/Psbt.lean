import InternalSpec
import BitcoinLedger.Psbt

namespace Proofs.Psbt

open InternalSpec.Psbt

/-!
# `Proofs.Psbt` — Machine-Checked Refinement & Security Theorems for `BitcoinLedger.Psbt`

Proves constructive (`0 sorryAx`, `0 Classical.choice`, `0 native_decide`) refinement and
security theorems linking `BitcoinLedger.Psbt` to `InternalSpec.Psbt`:
1. Structural equality & encoding primitives agreement (`eqBytes`, `eqBytes32`, `computeTxid`).
2. Exact PSBTv0-to-PSBTv2 normalization refinement (`normalizePsbtV0ToV2_eq_spec`).
3. Single-pass BIP-370 `determineLocktime` equivalence (`determineLocktime_eq_spec`) & conflict/fallback theorems.
4. Checked `UInt64` satoshi arithmetic refinement (`checkedAddSats?`, `checkedSubSats?`, `scanOutputsChecked`, `scanInputsCheckedLoop`).
5. Exact equivalence `BitcoinLedger.Psbt.validatePsbtTransaction = InternalSpec.Psbt.validatePsbt` and `authorizePsbtSigning_eq_spec`.
6. Sighash digest exact agreement (`computeSighashLegacy`, `computeSighashSegwitV0`, `computeSighashTaproot`).
7. Security & conservation theorems:
   - Fee conservation (`totalIn = totalOut + fee`),
   - Dual-UTXO mismatch rejection (CVE-2020-14199 defense),
   - Unverified change & receive-branch output rejection from silent elision,
   - High-fee warning in both `full` and `selfTransfer` display modes,
   - `TxDisplayMode.unavailable` on open/mixed sighashes,
   - Ledger Swap mismatch rejection (fee, amount, destination, extra outputs),
   - BIP-322 `to_spend` challenge binding & Swap isolation,
   - Concrete non-vacuous execution witnesses.
-/

/-! ## 1. Primitive Equality, Encoding & `computeTxid` Agreement -/

theorem eqByteList_eq_spec (xs ys : List UInt8) :
    BitcoinLedger.Psbt.eqByteList xs ys = InternalSpec.Psbt.byteListEq xs ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          unfold BitcoinLedger.Psbt.eqByteList InternalSpec.Psbt.byteListEq
          rw [ih ys]

theorem eqBytes_eq_spec (a b : ByteArray) :
    BitcoinLedger.Psbt.eqBytes a b = InternalSpec.Psbt.bytesEq a b :=
  eqByteList_eq_spec a.data.toList b.data.toList

theorem eqBytes32_eq_spec (a b : Bytes32) :
    BitcoinLedger.Psbt.eqBytes32 a b = InternalSpec.Psbt.bytes32Eq a b :=
  eqBytes_eq_spec a.bytes b.bytes

theorem eqOptU8_eq_spec (a b : Option UInt8) :
    BitcoinLedger.Psbt.eqOptU8 a b = InternalSpec.Psbt.optUInt8Eq a b := by
  cases a <;> cases b <;> rfl

theorem eqOptU32_eq_spec (a b : Option UInt32) :
    BitcoinLedger.Psbt.eqOptU32 a b = InternalSpec.Psbt.optUInt32Eq a b := by
  cases a <;> cases b <;> rfl

theorem eqOptBytes_eq_spec (a b : Option ByteArray) :
    BitcoinLedger.Psbt.eqOptBytes a b = InternalSpec.Psbt.optBytesEq a b := by
  cases a <;> cases b <;> simp [BitcoinLedger.Psbt.eqOptBytes, InternalSpec.Psbt.optBytesEq, eqBytes_eq_spec]

theorem eqOptString_eq_spec (a b : Option String) :
    BitcoinLedger.Psbt.eqOptString a b = InternalSpec.Psbt.optStringEq a b := by
  cases a <;> cases b <;> rfl

theorem eqU32List_eq_spec (xs ys : List UInt32) :
    BitcoinLedger.Psbt.eqU32List xs ys = InternalSpec.Psbt.u32ListEq xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          unfold BitcoinLedger.Psbt.eqU32List InternalSpec.Psbt.u32ListEq
          rw [ih ys]

theorem eqTxOut_eq_spec (a b : TxOut) :
    BitcoinLedger.Psbt.eqTxOut a b = InternalSpec.Psbt.txOutEq a b := by
  unfold BitcoinLedger.Psbt.eqTxOut InternalSpec.Psbt.txOutEq
  rw [eqBytes_eq_spec]

theorem putU16LE_eq_spec (v : UInt16) :
    BitcoinLedger.Psbt.putU16LE v = InternalSpec.Psbt.encodeU16LE v := rfl

theorem putU32LE_eq_spec (v : UInt32) :
    BitcoinLedger.Psbt.putU32LE v = InternalSpec.Psbt.encodeU32LE v := rfl

theorem putU64LE_eq_spec (v : UInt64) :
    BitcoinLedger.Psbt.putU64LE v = InternalSpec.Psbt.encodeU64LE v := rfl

theorem putVarInt_eq_spec (n : Nat) :
    BitcoinLedger.Psbt.putVarInt n = InternalSpec.Psbt.encodeVarInt n := rfl

theorem joinByteArrays_eq_spec (xs : List ByteArray) :
    BitcoinLedger.Psbt.joinByteArrays xs = InternalSpec.Psbt.concatBytes xs := rfl

theorem hash256d_eq_spec (sha256 : ByteArray → Bytes32) (bs : ByteArray) :
    BitcoinLedger.Psbt.hash256d sha256 bs = InternalSpec.Psbt.doubleSha256 sha256 bs := rfl

theorem bip340TaggedHash_eq_spec (sha256 : ByteArray → Bytes32) (tag : String) (msg : ByteArray) :
    BitcoinLedger.Psbt.bip340TaggedHash sha256 tag msg = InternalSpec.Psbt.taggedHash sha256 tag msg := rfl

theorem computeTxid_eq_spec (sha256 : ByteArray → Bytes32) (tx : RawTx) :
    BitcoinLedger.Psbt.computeTxid sha256 tx = InternalSpec.Psbt.computeTxid sha256 tx := rfl

/-! ## 2. PSBTv0-to-PSBTv2 Normalization Refinement -/

private theorem checkUnsignedVinEmptyScripts_neg_eq_any (xs : List RawTxIn) :
    (!BitcoinLedger.Psbt.checkUnsignedVinEmptyScripts xs) =
      xs.any (fun txin => !decide (txin.scriptSig.size = 0) || !decide (txin.witness.size = 0)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      unfold BitcoinLedger.Psbt.checkUnsignedVinEmptyScripts
      rw [List.any_cons, ← ih]
      cases decide (x.scriptSig.size = 0) <;> cases decide (x.witness.size = 0) <;> rfl

private def buildV2InputAt
    (vin : Array RawTxIn)
    (v0Ins : Array PsbtV0Input)
    (i : Nat)
    (hVin : i < vin.size)
    (hV0 : i < v0Ins.size) : PsbtInput :=
  let rawIn := vin[i]'hVin
  let mIn := v0Ins[i]'hV0
  { prevout := rawIn.prevout
    sequence := some rawIn.sequence
    requiredTimeLocktime := mIn.requiredTimeLocktime
    requiredHeightLocktime := mIn.requiredHeightLocktime
    nonWitnessUtxo := mIn.nonWitnessUtxo
    witnessUtxo := mIn.witnessUtxo
    sighashType := mIn.sighashType
    redeemScript := mIn.redeemScript
    witnessScript := mIn.witnessScript
    derivations := mIn.derivations
    tapInternalKey := mIn.tapInternalKey
    tapMerkleRoot := mIn.tapMerkleRoot }

private theorem dite_true_constructive {α : Sort u} {p : Prop} [Decidable p]
    (h : p) (t : p → α) (e : ¬p → α) : (if hp : p then t hp else e hp) = t h := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hnp => exact absurd h hnp

private theorem dite_false_constructive {α : Sort u} {p : Prop} [Decidable p]
    (h : ¬p) (t : p → α) (e : ¬p → α) : (if hp : p then t hp else e hp) = e h := by
  cases ‹Decidable p› with
  | isTrue hp => exact absurd hp h
  | isFalse _ => rfl

private theorem sub_step_index {fuel idx n : Nat} (hSum : (fuel + 1) + idx = n) :
    n - fuel - 1 = idx := by
  have h1 : n = (idx + 1) + fuel := by
    rw [← hSum, Nat.add_comm (fuel + 1) idx, Nat.add_assoc, Nat.add_comm 1 fuel]
  rw [h1, Nat.add_sub_cancel, Nat.add_sub_cancel]

private theorem fin_app_sub_eq {α : Type} {n fuel idx : Nat}
    (f : Fin n → α) (hSum : (fuel + 1) + idx = n) (hSubLt : n - fuel - 1 < n) (hLt : idx < n) :
    f ⟨n - fuel - 1, hSubLt⟩ = f ⟨idx, hLt⟩ :=
  congrArg f (Fin.ext (sub_step_index hSum))

private theorem buildV2InputsLoop_eq_ofFn_go
    (vin : Array RawTxIn)
    (v0Ins : Array PsbtV0Input)
    (hSz : v0Ins.size = vin.size) :
    let f : Fin v0Ins.size → PsbtInput := fun x => buildV2InputAt vin v0Ins x.1 (hSz ▸ x.2) x.2
    ∀ (fuel idx : Nat) (acc : Array PsbtInput)
      (_hSum : fuel + idx = v0Ins.size)
      (hLe : fuel ≤ v0Ins.size),
      BitcoinLedger.Psbt.buildV2InputsLoop vin v0Ins fuel idx acc =
        Array.ofFn.go f acc fuel hLe := by
  intro f fuel
  induction fuel with
  | zero =>
      intro idx acc _ hLe
      unfold BitcoinLedger.Psbt.buildV2InputsLoop
      rw [Array.ofFn.go.eq_2]
  | succ fuel ih =>
      intro idx acc hSum hLe
      have hLt : idx < v0Ins.size := by
        rw [← hSum, Nat.add_comm]
        exact Nat.lt_add_of_pos_right (Nat.succ_pos fuel)
      have hVin : idx < vin.size := hSz ▸ hLt
      have hSum' : fuel + (idx + 1) = v0Ins.size := by
        rw [← Nat.add_assoc, Nat.add_right_comm, hSum]
      have hUnfold :
          BitcoinLedger.Psbt.buildV2InputsLoop vin v0Ins (fuel + 1) idx acc =
          BitcoinLedger.Psbt.buildV2InputsLoop vin v0Ins fuel (idx + 1)
            (acc.push (f ⟨idx, hLt⟩)) := by
        conv => lhs; unfold BitcoinLedger.Psbt.buildV2InputsLoop
        rw [dite_true_constructive hLt, dite_true_constructive hVin]
        rfl
      rw [hUnfold, Array.ofFn.go.eq_1, fin_app_sub_eq f hSum _ hLt]
      exact ih (idx + 1) _ hSum' _

private theorem buildV2InputsLoop_eq_ofFn
    (vin : Array RawTxIn)
    (v0Ins : Array PsbtV0Input)
    (hSz : v0Ins.size = vin.size) :
    BitcoinLedger.Psbt.buildV2InputsLoop vin v0Ins v0Ins.size 0 #[] =
      Array.ofFn (n := v0Ins.size) fun ⟨i, hi⟩ =>
        buildV2InputAt vin v0Ins i (hSz ▸ hi) hi := by
  unfold Array.ofFn
  exact buildV2InputsLoop_eq_ofFn_go vin v0Ins hSz v0Ins.size 0 #[]
    (Nat.add_zero _) (Nat.le_refl _)

private def buildV2OutputAt
    (vout : Array TxOut)
    (v0Outs : Array PsbtV0Output)
    (i : Nat)
    (hVout : i < vout.size)
    (hV0 : i < v0Outs.size) : PsbtOutput :=
  let rawOut := vout[i]'hVout
  let mOut := v0Outs[i]'hV0
  { amount := rawOut.amount
    scriptPubKey := some rawOut.scriptPubKey
    redeemScript := mOut.redeemScript
    witnessScript := mOut.witnessScript
    derivations := mOut.derivations
    tapInternalKey := mOut.tapInternalKey }

private theorem buildV2OutputsLoop_eq_ofFn_go
    (vout : Array TxOut)
    (v0Outs : Array PsbtV0Output)
    (hSz : v0Outs.size = vout.size) :
    let f : Fin v0Outs.size → PsbtOutput := fun x => buildV2OutputAt vout v0Outs x.1 (hSz ▸ x.2) x.2
    ∀ (fuel idx : Nat) (acc : Array PsbtOutput)
      (_hSum : fuel + idx = v0Outs.size)
      (hLe : fuel ≤ v0Outs.size),
      BitcoinLedger.Psbt.buildV2OutputsLoop vout v0Outs fuel idx acc =
        Array.ofFn.go f acc fuel hLe := by
  intro f fuel
  induction fuel with
  | zero =>
      intro idx acc _ hLe
      unfold BitcoinLedger.Psbt.buildV2OutputsLoop
      rw [Array.ofFn.go.eq_2]
  | succ fuel ih =>
      intro idx acc hSum hLe
      have hLt : idx < v0Outs.size := by
        rw [← hSum, Nat.add_comm]
        exact Nat.lt_add_of_pos_right (Nat.succ_pos fuel)
      have hVout : idx < vout.size := hSz ▸ hLt
      have hSum' : fuel + (idx + 1) = v0Outs.size := by
        rw [← Nat.add_assoc, Nat.add_right_comm, hSum]
      have hUnfold :
          BitcoinLedger.Psbt.buildV2OutputsLoop vout v0Outs (fuel + 1) idx acc =
          BitcoinLedger.Psbt.buildV2OutputsLoop vout v0Outs fuel (idx + 1)
            (acc.push (f ⟨idx, hLt⟩)) := by
        conv => lhs; unfold BitcoinLedger.Psbt.buildV2OutputsLoop
        rw [dite_true_constructive hLt, dite_true_constructive hVout]
        rfl
      rw [hUnfold, Array.ofFn.go.eq_1, fin_app_sub_eq f hSum _ hLt]
      exact ih (idx + 1) _ hSum' _

private theorem buildV2OutputsLoop_eq_ofFn
    (vout : Array TxOut)
    (v0Outs : Array PsbtV0Output)
    (hSz : v0Outs.size = vout.size) :
    BitcoinLedger.Psbt.buildV2OutputsLoop vout v0Outs v0Outs.size 0 #[] =
      Array.ofFn (n := v0Outs.size) fun ⟨i, hi⟩ =>
        buildV2OutputAt vout v0Outs i (hSz ▸ hi) hi := by
  unfold Array.ofFn
  exact buildV2OutputsLoop_eq_ofFn_go vout v0Outs hSz v0Outs.size 0 #[]
    (Nat.add_zero _) (Nat.le_refl _)

/-- Exact refinement theorem for `normalizePsbtV0ToV2`. -/
theorem normalizePsbtV0ToV2_eq_spec (v0 : PsbtV0) :
    BitcoinLedger.Psbt.normalizePsbtV0ToV2 v0 = InternalSpec.Psbt.normalizePsbtV0ToV2 v0 := by
  unfold BitcoinLedger.Psbt.normalizePsbtV0ToV2 InternalSpec.Psbt.normalizePsbtV0ToV2
  dsimp only
  rw [checkUnsignedVinEmptyScripts_neg_eq_any]
  cases hVer : (!match v0.version with | some ver => decide (ver = 0) | none => true)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hWit : v0.unsignedTxHasWitness
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hGlob : v0.hasV2ExclusiveGlobals
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hScr : (v0.unsignedTx.vin.toList.any fun txin => !decide (txin.scriptSig.size = 0) || !decide (txin.witness.size = 0))
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases decEq v0.inputs.size v0.unsignedTx.vin.size with
          | isFalse hIn =>
              have hInD : (!decide (v0.inputs.size = v0.unsignedTx.vin.size)) = true := by
                rw [decide_eq_false hIn]; rfl
              rw [hInD, dite_false_constructive hIn]
              rfl
          | isTrue hIn =>
              have hInD : (!decide (v0.inputs.size = v0.unsignedTx.vin.size)) = false := by
                rw [decide_eq_true hIn]; rfl
              rw [hInD, dite_true_constructive hIn]
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases decEq v0.outputs.size v0.unsignedTx.vout.size with
              | isFalse hOut =>
                  have hOutD : (!decide (v0.outputs.size = v0.unsignedTx.vout.size)) = true := by
                    rw [decide_eq_false hOut]; rfl
                  rw [hOutD, dite_false_constructive hOut]
                  rfl
              | isTrue hOut =>
                  have hOutD : (!decide (v0.outputs.size = v0.unsignedTx.vout.size)) = false := by
                    rw [decide_eq_true hOut]; rfl
                  rw [hOutD, dite_true_constructive hOut]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  cases (v0.inputs.toList.any (·.hasV2ExclusiveFields) || v0.outputs.toList.any (·.hasV2ExclusiveFields))
                  · simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [buildV2InputsLoop_eq_ofFn v0.unsignedTx.vin v0.inputs hIn]
                    rw [buildV2OutputsLoop_eq_ofFn v0.unsignedTx.vout v0.outputs hOut]
                    rfl
                  · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-! ## 3. Single-Pass BIP-370 `determineLocktime` Refinement -/

theorem checkInputLocktimeBounds_eq_spec (inp : PsbtInput) :
    BitcoinLedger.Psbt.checkInputLocktimeBounds inp = InternalSpec.Psbt.validateInputLocktimeFields inp := rfl

private theorem foldl_maxHeight_eq
    (stMax : UInt32)
    (inputs : List PsbtInput) :
    UInt32.ofNat (inputs.foldl (fun acc i =>
      match i.requiredHeightLocktime with
      | some h => if acc < h.toNat then h.toNat else acc
      | none => acc) stMax.toNat) =
    (inputs.foldl (fun (cur : UInt32) i =>
      match i.requiredHeightLocktime with
      | some h => if cur.toNat < h.toNat then h else cur
      | none => cur) stMax) := by
  induction inputs generalizing stMax with
  | nil => exact UInt32.ofNat_toNat
  | cons inp rest ih =>
      simp only [List.foldl_cons]
      cases inp.requiredHeightLocktime with
      | none => exact ih stMax
      | some h =>
          by_cases hLt : stMax.toNat < h.toNat
          · simp only [hLt, ↓reduceIte]
            exact ih h
          · simp only [hLt, ↓reduceIte]
            exact ih stMax

private theorem foldl_maxTime_eq
    (stMax : UInt32)
    (inputs : List PsbtInput) :
    UInt32.ofNat (inputs.foldl (fun acc i =>
      match i.requiredTimeLocktime with
      | some t => if acc < t.toNat then t.toNat else acc
      | none => acc) stMax.toNat) =
    (inputs.foldl (fun (cur : UInt32) i =>
      match i.requiredTimeLocktime with
      | some t => if cur.toNat < t.toNat then t else cur
      | none => cur) stMax) := by
  induction inputs generalizing stMax with
  | nil => exact UInt32.ofNat_toNat
  | cons inp rest ih =>
      simp only [List.foldl_cons]
      cases inp.requiredTimeLocktime with
      | none => exact ih stMax
      | some t =>
          by_cases hLt : stMax.toNat < t.toNat
          · simp only [hLt, ↓reduceIte]
            exact ih t
          · simp only [hLt, ↓reduceIte]
            exact ih stMax

private theorem scanLocktimeInputs_eq
    (st : BitcoinLedger.Psbt.LocktimeScanState)
    (inputs : List PsbtInput) :
    BitcoinLedger.Psbt.scanLocktimeInputs st inputs =
      if inputs.all InternalSpec.Psbt.validateInputLocktimeFields then
        some {
          hasHeightOnly := st.hasHeightOnly || inputs.any (fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone)
          hasTimeOnly := st.hasTimeOnly || inputs.any (fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone)
          anyHeight := st.anyHeight || inputs.any (fun i => i.requiredHeightLocktime.isSome)
          anyTime := st.anyTime || inputs.any (fun i => i.requiredTimeLocktime.isSome)
          maxHeight := inputs.foldl (fun cur i =>
            match i.requiredHeightLocktime with
            | some h => if cur.toNat < h.toNat then h else cur
            | none => cur) st.maxHeight
          maxTime := inputs.foldl (fun cur i =>
            match i.requiredTimeLocktime with
            | some t => if cur.toNat < t.toNat then t else cur
            | none => cur) st.maxTime
        }
      else
        none := by
  induction inputs generalizing st with
  | nil =>
      simp [BitcoinLedger.Psbt.scanLocktimeInputs]
  | cons inp rest ih =>
      unfold BitcoinLedger.Psbt.scanLocktimeInputs
      rw [checkInputLocktimeBounds_eq_spec]
      cases hVal : InternalSpec.Psbt.validateInputLocktimeFields inp with
      | false =>
          simp [hVal]
      | true =>
          simp only [hVal, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.all_cons, Bool.true_and]
          rw [ih]
          cases rest.all InternalSpec.Psbt.validateInputLocktimeFields with
          | false => rfl
          | true =>
              simp only [↓reduceIte, List.any_cons, List.foldl_cons, Bool.or_assoc]
              rfl

/-- Exact refinement theorem for single-pass `determineLocktime`. -/
theorem determineLocktime_eq_spec
    (fallbackLocktime : Option UInt32)
    (inputs : List PsbtInput) :
    BitcoinLedger.Psbt.determineLocktime fallbackLocktime inputs =
      InternalSpec.Psbt.determineLocktime fallbackLocktime inputs := by
  unfold BitcoinLedger.Psbt.determineLocktime InternalSpec.Psbt.determineLocktime
  rw [scanLocktimeInputs_eq {} inputs]
  cases hAll : inputs.all InternalSpec.Psbt.validateInputLocktimeFields with
  | false =>
      simp
  | true =>
      dsimp only
      simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, Bool.false_or]
      have hMH :
          UInt32.ofNat (inputs.foldl (fun acc i =>
            match i.requiredHeightLocktime with
            | some h => if acc < h.toNat then h.toNat else acc
            | none => acc) 0) =
          inputs.foldl (fun (cur : UInt32) i =>
            match i.requiredHeightLocktime with
            | some h => if cur.toNat < h.toNat then h else cur
            | none => cur) 0 :=
        foldl_maxHeight_eq 0 inputs
      have hMT :
          UInt32.ofNat (inputs.foldl (fun acc i =>
            match i.requiredTimeLocktime with
            | some t => if acc < t.toNat then t.toNat else acc
            | none => acc) 0) =
          inputs.foldl (fun (cur : UInt32) i =>
            match i.requiredTimeLocktime with
            | some t => if cur.toNat < t.toNat then t else cur
            | none => cur) 0 :=
        foldl_maxTime_eq 0 inputs
      cases ((inputs.any fun i => i.requiredHeightLocktime.isSome && i.requiredTimeLocktime.isNone) &&
             (inputs.any fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone))
      · cases ((!inputs.any fun i => i.requiredHeightLocktime.isSome) &&
               (!inputs.any fun i => i.requiredTimeLocktime.isSome))
        · cases ((!inputs.any fun i => i.requiredTimeLocktime.isSome && i.requiredHeightLocktime.isNone) &&
                 (inputs.any fun i => i.requiredHeightLocktime.isSome))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrArg Except.ok hMT.symm
          · simp only [↓reduceIte]
            exact congrArg Except.ok hMH.symm
        · rfl
      · rfl

/-! ## 4. Sighash Classification, Script Templates, Dual-UTXO & Derivation Matching Agreement -/

theorem buildP2SHScript_eq_spec (h20 : ByteArray) :
    BitcoinLedger.Psbt.buildP2SHScript h20 = InternalSpec.Psbt.mkP2SHScript h20 := rfl

theorem buildP2WSHScript_eq_spec (h32 : Bytes32) :
    BitcoinLedger.Psbt.buildP2WSHScript h32 = InternalSpec.Psbt.mkP2WSHScript h32 := rfl

theorem checkP2WPKH_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.checkP2WPKH s = InternalSpec.Psbt.isP2WPKHScript s := by
  unfold BitcoinLedger.Psbt.checkP2WPKH InternalSpec.Psbt.isP2WPKHScript
  rw [eqOptU8_eq_spec, eqOptU8_eq_spec]
  rfl

theorem checkP2WSH_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.checkP2WSH s = InternalSpec.Psbt.isP2WSHScript s := by
  unfold BitcoinLedger.Psbt.checkP2WSH InternalSpec.Psbt.isP2WSHScript
  rw [eqOptU8_eq_spec, eqOptU8_eq_spec]
  rfl

theorem checkP2TR_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.checkP2TR s = InternalSpec.Psbt.isP2TRScript s := by
  unfold BitcoinLedger.Psbt.checkP2TR InternalSpec.Psbt.isP2TRScript
  rw [eqOptU8_eq_spec, eqOptU8_eq_spec]
  rfl

theorem checkUnknownSegwit_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.checkUnknownSegwit s = InternalSpec.Psbt.isUnknownSegwitScript s := by
  unfold BitcoinLedger.Psbt.checkUnknownSegwit InternalSpec.Psbt.isUnknownSegwitScript
  rw [checkP2WPKH_eq_spec, checkP2WSH_eq_spec, checkP2TR_eq_spec]
  rfl

theorem classifyInputSpendClass_eq_spec (spk : ByteArray) (rs : Option ByteArray) :
    BitcoinLedger.Psbt.classifyInputSpendClass spk rs = InternalSpec.Psbt.detectInputSpendClass spk rs := by
  unfold BitcoinLedger.Psbt.classifyInputSpendClass InternalSpec.Psbt.detectInputSpendClass
  dsimp only
  rw [checkP2WPKH_eq_spec, checkP2WSH_eq_spec, checkP2TR_eq_spec, checkUnknownSegwit_eq_spec]

theorem classifySighashType_eq_spec (sc : SpendClass) (rawOpt : Option UInt32) :
    BitcoinLedger.Psbt.classifySighashType sc rawOpt = InternalSpec.Psbt.classifySighash sc rawOpt := rfl

theorem sighashHasAnyoneCanPay_eq_spec (b : UInt8) :
    BitcoinLedger.Psbt.sighashHasAnyoneCanPay b = InternalSpec.Psbt.sighashOpensInputs b := rfl

theorem sighashLeavesOutputsOpen_eq_spec (b : UInt8) :
    BitcoinLedger.Psbt.sighashLeavesOutputsOpen b = InternalSpec.Psbt.sighashOpensOutputs b := rfl

theorem sighashBaseIsSingle_eq_spec (b : UInt8) :
    BitcoinLedger.Psbt.sighashBaseIsSingle b = InternalSpec.Psbt.sighashIsSingle b := rfl

theorem sighashCommitsAllProvidedOutputs_eq_spec (b : UInt8) (nOutputs : Nat) :
    BitcoinLedger.Psbt.sighashCommitsAllProvidedOutputs b nOutputs =
      InternalSpec.Psbt.sighashCommitsProvidedOutputs b nOutputs := rfl

/-- Exact refinement for `extractInputPrevout` (including dual-UTXO cross-check). -/
theorem extractInputPrevout_eq_spec (sha256 : ByteArray → Bytes32) (inp : PsbtInput) :
    BitcoinLedger.Psbt.extractInputPrevout sha256 inp = InternalSpec.Psbt.extractInputPrevout sha256 inp := by
  unfold BitcoinLedger.Psbt.extractInputPrevout InternalSpec.Psbt.extractInputPrevout
  cases inp.nonWitnessUtxo <;> cases inp.witnessUtxo
  · rfl
  · rfl
  · simp only [computeTxid_eq_spec, eqBytes32_eq_spec]
  · simp only [computeTxid_eq_spec, eqBytes32_eq_spec, eqTxOut_eq_spec]

theorem natToValidSats?_eq (amt : Nat) :
    BitcoinLedger.Psbt.natToValidSats? amt =
      if decide (amt > MAX_MONEY) then none else some (UInt64.ofNat amt) := rfl

theorem validateExternalInputUtxo_eq_spec
    (crypto : CryptoOracles)
    (inp : PsbtInput) :
    BitcoinLedger.Psbt.validateExternalInputUtxo crypto inp =
      InternalSpec.Psbt.validateExternalInputUtxo crypto inp := by
  unfold BitcoinLedger.Psbt.validateExternalInputUtxo InternalSpec.Psbt.validateExternalInputUtxo
  rw [extractInputPrevout_eq_spec]
  cases InternalSpec.Psbt.extractInputPrevout crypto.sha256 inp with
  | error _ => rfl
  | ok pair =>
      rcases pair with ⟨txOut, _⟩
      dsimp only
      unfold BitcoinLedger.Psbt.natToValidSats?
      rw [classifyInputSpendClass_eq_spec]
      cases decide (txOut.amount > MAX_MONEY) <;> rfl

theorem validateInternalInputUtxo_eq_spec
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (exempt : Bool) :
    BitcoinLedger.Psbt.validateInternalInputUtxo crypto inp exempt =
      InternalSpec.Psbt.validateInputUtxo crypto inp exempt := by
  unfold BitcoinLedger.Psbt.validateInternalInputUtxo InternalSpec.Psbt.validateInputUtxo
  rw [extractInputPrevout_eq_spec]
  cases InternalSpec.Psbt.extractInputPrevout crypto.sha256 inp with
  | error _ => rfl
  | ok pair =>
      rcases pair with ⟨txOut, hasNw⟩
      dsimp only
      rw [classifyInputSpendClass_eq_spec, checkP2WSH_eq_spec]
      unfold BitcoinLedger.Psbt.natToValidSats?
      cases inp.redeemScript <;> cases inp.witnessScript <;>
        simp only [eqBytes_eq_spec, buildP2SHScript_eq_spec, buildP2WSHScript_eq_spec] <;>
        (cases decide (txOut.amount > MAX_MONEY) <;> rfl)

theorem matchOriginPrefix_eq_spec (orig entryOrig : KeyOrigin) :
    BitcoinLedger.Psbt.matchOriginPrefix orig entryOrig = InternalSpec.Psbt.matchOriginSteps orig entryOrig := by
  unfold BitcoinLedger.Psbt.matchOriginPrefix InternalSpec.Psbt.matchOriginSteps
  rw [eqU32List_eq_spec]
  rfl

theorem findFirstSome?_eq_spec {α β : Type} (f : α → Option β) (xs : List α) :
    BitcoinLedger.Psbt.findFirstSome? f xs = InternalSpec.Psbt.findSomePure? f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      unfold BitcoinLedger.Psbt.findFirstSome? InternalSpec.Psbt.findSomePure?
      cases f x with
      | some _ => rfl
      | none => exact ih

theorem matchPlaceholderDerivation_eq_spec
    (mfpr : Option UInt32)
    (ph : InternalKeyPlaceholder)
    (entry : KeyDerivationEntry) :
    BitcoinLedger.Psbt.matchPlaceholderDerivation mfpr ph entry =
      InternalSpec.Psbt.derivationMatchesPlaceholderWithMaster mfpr ph entry := by
  unfold BitcoinLedger.Psbt.matchPlaceholderDerivation InternalSpec.Psbt.derivationMatchesPlaceholderWithMaster
  cases ph.isMusig <;> cases ph.expectedOrigin <;>
    simp only [↓reduceIte, Bool.false_eq_true, matchOriginPrefix_eq_spec, findFirstSome?_eq_spec]
    <;> rfl

theorem gatherCandidateCoordinates_eq_spec
    (mfpr : Option UInt32)
    (policy : WalletPolicySpec)
    (derivations : List KeyDerivationEntry) :
    BitcoinLedger.Psbt.gatherCandidateCoordinates mfpr policy derivations =
      InternalSpec.Psbt.collectMatchingCoordinatesWithMaster mfpr policy derivations := by
  unfold BitcoinLedger.Psbt.gatherCandidateCoordinates InternalSpec.Psbt.collectMatchingCoordinatesWithMaster
  congr 1
  funext entry acc
  congr 1
  funext ph innerAcc
  rw [matchPlaceholderDerivation_eq_spec]
  rfl

theorem evalInternalInputCandidates_eq_spec
    (policy : WalletPolicySpec)
    (inp : PsbtInput)
    (utxo : TxOut)
    (coords : List (Bool × UInt32)) :
    BitcoinLedger.Psbt.evalInternalInputCandidates policy inp utxo coords =
      InternalSpec.Psbt.checkInternalInputCandidates policy inp utxo coords := by
  induction coords with
  | nil => rfl
  | cons hd rest ih =>
      rcases hd with ⟨isChange, addrIdx⟩
      unfold BitcoinLedger.Psbt.evalInternalInputCandidates InternalSpec.Psbt.checkInternalInputCandidates
      cases policy.deriveScripts isChange addrIdx with
      | none => exact ih
      | some triple =>
          rcases triple with ⟨expectedSpk, expectedRedeem, expectedWitness⟩
          dsimp only
          rw [eqBytes_eq_spec, ih]
          cases expectedRedeem <;> cases inp.redeemScript <;>
            cases expectedWitness <;> cases inp.witnessScript <;>
            simp only [eqBytes_eq_spec] <;> rfl

theorem classifyInternalInput_eq_spec
    (mfpr : Option UInt32)
    (policy : WalletPolicySpec)
    (inp : PsbtInput)
    (utxo : TxOut) :
    BitcoinLedger.Psbt.classifyInternalInput mfpr policy inp utxo =
      InternalSpec.Psbt.classifyInternalInputWithMaster mfpr policy inp utxo := by
  unfold BitcoinLedger.Psbt.classifyInternalInput InternalSpec.Psbt.classifyInternalInputWithMaster
  rw [gatherCandidateCoordinates_eq_spec, evalInternalInputCandidates_eq_spec]

theorem checkOutputDerivedScripts_eq_spec
    (policy : WalletPolicySpec)
    (out : PsbtOutput)
    (spk : ByteArray)
    (isChange : Bool)
    (addrIdx : UInt32) :
    BitcoinLedger.Psbt.checkOutputDerivedScripts policy out spk isChange addrIdx =
      InternalSpec.Psbt.outputMatchesDerivedAt policy out spk isChange addrIdx := by
  unfold BitcoinLedger.Psbt.checkOutputDerivedScripts InternalSpec.Psbt.outputMatchesDerivedAt
  cases policy.deriveScripts isChange addrIdx with
  | none => rfl
  | some triple =>
      rcases triple with ⟨expectedSpk, expectedRedeem, expectedWitness⟩
      dsimp only
      cases out.redeemScript <;> cases expectedRedeem <;>
        cases out.witnessScript <;> cases expectedWitness <;>
        simp only [eqBytes_eq_spec] <;> rfl

theorem isInternalOutput_eq_spec
    (mfpr : Option UInt32)
    (treatReceive : Bool)
    (policy : WalletPolicySpec)
    (out : PsbtOutput) :
    BitcoinLedger.Psbt.isInternalOutput mfpr treatReceive policy out =
      InternalSpec.Psbt.isInternalOutputWithOptions mfpr treatReceive policy out := by
  unfold BitcoinLedger.Psbt.isInternalOutput InternalSpec.Psbt.isInternalOutputWithOptions
  cases out.silentPayment.isSome
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases out.scriptPubKey with
    | none => rfl
    | some spk =>
        dsimp only
        rw [gatherCandidateCoordinates_eq_spec]
        congr 1
        funext pair
        rcases pair with ⟨isChange, addrIdx⟩
        rw [checkOutputDerivedScripts_eq_spec]
  · rfl

theorem isVerifiedChangeOutput_eq_spec
    (policy : WalletPolicySpec)
    (out : PsbtOutput) :
    BitcoinLedger.Psbt.isVerifiedChangeOutput policy out =
      InternalSpec.Psbt.isVerifiedChange policy out :=
  isInternalOutput_eq_spec none false policy out

/-! ## 5. Checked `UInt64` Satoshi Arithmetic & Input/Output Scan Refinement -/

private theorem max_money_lt_u64 : MAX_MONEY < 2 ^ 64 := by decide

private theorem two_max_money_lt_u64 : MAX_MONEY + MAX_MONEY < 2 ^ 64 := by decide

private theorem uint64_ofNat_toNat_of_le_max_money (amt : Nat) (hLe : amt ≤ MAX_MONEY) :
    (UInt64.ofNat amt).toNat = amt := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hLe max_money_lt_u64)

private theorem uint64_add_toNat_of_le_max_money (a b : UInt64)
    (ha : a.toNat ≤ MAX_MONEY) (hb : b.toNat ≤ MAX_MONEY) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  have hSumLe : a.toNat + b.toNat ≤ MAX_MONEY + MAX_MONEY := Nat.add_le_add ha hb
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hSumLe two_max_money_lt_u64)

theorem checkedAddSats?_spec (a b : UInt64) (ha : a.toNat ≤ MAX_MONEY) (hb : b.toNat ≤ MAX_MONEY) :
    BitcoinLedger.Psbt.checkedAddSats? a b =
      if decide (a.toNat + b.toNat > MAX_MONEY) then none else some (a + b) := by
  unfold BitcoinLedger.Psbt.checkedAddSats?
  have hDa : decide (a.toNat ≤ MAX_MONEY) = true := decide_eq_true ha
  have hDb : decide (b.toNat ≤ MAX_MONEY) = true := decide_eq_true hb
  dsimp only
  rw [hDa, hDb, Bool.and_self, uint64_add_toNat_of_le_max_money a b ha hb]
  rfl

theorem checkedSubSats?_spec (total part : UInt64) (ht : total.toNat ≤ MAX_MONEY) :
    (BitcoinLedger.Psbt.checkedSubSats? total part).map UInt64.toNat =
      if decide (total.toNat < part.toNat) then none else some (total.toNat - part.toNat) := by
  unfold BitcoinLedger.Psbt.checkedSubSats?
  have hDt : decide (total.toNat ≤ MAX_MONEY) = true := decide_eq_true ht
  rw [hDt, Bool.true_and]
  cases hLt : decide (total.toNat < part.toNat)
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, Option.map_some]
    have hLeNat : part.toNat ≤ total.toNat := Nat.le_of_not_lt (of_decide_eq_false hLt)
    have hLeU64 : part ≤ total := UInt64.le_iff_toNat_le.mpr hLeNat
    rw [UInt64.toNat_sub_of_le total part hLeU64]
  · rfl

theorem scanOpReturnPushes_eq_spec (s : ByteArray) (fuel pos nPushes : Nat) :
    BitcoinLedger.Psbt.scanOpReturnPushes s fuel pos nPushes =
      InternalSpec.Psbt.verifyOpReturnPushes s fuel pos nPushes := by
  induction fuel generalizing pos nPushes with
  | zero => rfl
  | succ f ih =>
      unfold BitcoinLedger.Psbt.scanOpReturnPushes InternalSpec.Psbt.verifyOpReturnPushes
      have hByte : BitcoinLedger.Psbt.getByte? s pos = InternalSpec.Psbt.byteAt? s pos := rfl
      have hByte1 : BitcoinLedger.Psbt.getByte? s (pos + 1) = InternalSpec.Psbt.byteAt? s (pos + 1) := rfl
      have hMin : ∀ b, BitcoinLedger.Psbt.isNonMinimalOneBytePush b = InternalSpec.Psbt.isNonMinimalSingleByteOpReturnPush b := fun _ => rfl
      dsimp only
      rw [hByte, hByte1]
      cases decide (pos ≥ s.size)
      · cases decide (nPushes ≥ 5)
        · cases InternalSpec.Psbt.byteAt? s pos with
          | none => rfl
          | some opByte =>
              dsimp only
              cases (decide (opByte.toNat = 0x00) || decide (opByte.toNat = 0x4f) || decide (0x51 ≤ opByte.toNat ∧ opByte.toNat ≤ 0x60))
              · cases decide (1 ≤ opByte.toNat ∧ opByte.toNat ≤ 75)
                · cases decide (opByte.toNat = 0x4c)
                  · rfl
                  · cases InternalSpec.Psbt.byteAt? s (pos + 1) with
                    | none => rfl
                    | some lenByte =>
                        dsimp only
                        cases (decide (lenByte.toNat > 75) && decide (pos + 2 + lenByte.toNat ≤ s.size))
                        · rfl
                        · simp only [Bool.false_eq_true, ↓reduceIte, ih]
                · cases decide (pos + 1 + opByte.toNat ≤ s.size)
                  · rfl
                  · cases decide (opByte.toNat = 1)
                    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      cases InternalSpec.Psbt.byteAt? s (pos + 1) with
                      | none => rfl
                      | some pushedByte =>
                          dsimp only
                          rw [hMin]
                          cases InternalSpec.Psbt.isNonMinimalSingleByteOpReturnPush pushedByte <;> simp [ih]
              · simp only [Bool.false_eq_true, ↓reduceIte, ih]
        · rfl
      · rfl

theorem checkValidOpReturn_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.checkValidOpReturn s = InternalSpec.Psbt.isValidOpReturnScript s := by
  unfold BitcoinLedger.Psbt.checkValidOpReturn InternalSpec.Psbt.isValidOpReturnScript
  rw [eqOptU8_eq_spec, scanOpReturnPushes_eq_spec]
  rfl

theorem checkIsOpReturn_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.checkIsOpReturn s = InternalSpec.Psbt.isOpReturnScript s := by
  unfold BitcoinLedger.Psbt.checkIsOpReturn InternalSpec.Psbt.isOpReturnScript
  rw [eqOptU8_eq_spec]
  rfl

theorem checkMusig2SessionIdOpt_eq_spec (opt : Option ByteArray) :
    BitcoinLedger.Psbt.checkMusig2SessionIdOpt opt = InternalSpec.Psbt.validateMusig2SessionIdOpt opt := rfl

theorem checkPolicyHeader_eq_spec (policy : WalletPolicySpec) :
    BitcoinLedger.Psbt.checkPolicyHeader policy = InternalSpec.Psbt.validatePolicyHeader policy := by
  unfold BitcoinLedger.Psbt.checkPolicyHeader InternalSpec.Psbt.validatePolicyHeader
  rw [eqByteList_eq_spec]

theorem validateOutputScript_eq_spec
    (crypto : CryptoOracles)
    (allowOpReturn : Bool)
    (out : PsbtOutput) :
    BitcoinLedger.Psbt.validateOutputScript crypto allowOpReturn out =
      InternalSpec.Psbt.validateSingleOutputScriptWithOptions crypto allowOpReturn out := by
  unfold BitcoinLedger.Psbt.validateOutputScript InternalSpec.Psbt.validateSingleOutputScriptWithOptions
  cases out.scriptPubKey <;> cases out.silentPayment
  · rfl
  · rfl
  · simp only [checkIsOpReturn_eq_spec, checkValidOpReturn_eq_spec]
  · simp only [checkIsOpReturn_eq_spec, checkValidOpReturn_eq_spec]

private def mapOutTupleToNat
    (t : List (Nat × PsbtOutput) × List (Nat × PsbtOutput) × UInt64 × UInt64) :
    List (Nat × PsbtOutput) × List (Nat × PsbtOutput) × Nat × Nat :=
  (t.1, t.2.1, t.2.2.1.toNat, t.2.2.2.toNat)

private theorem scanOutputsCheckedLoop_refines
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (isBip322 : Bool)
    (policy : WalletPolicySpec)
    (idx : Nat)
    (rem : List PsbtOutput)
    (dispAcc chgAcc : List (Nat × PsbtOutput))
    (sumOutSats sumChgSats : UInt64)
    (hOutBound : sumOutSats.toNat ≤ MAX_MONEY)
    (hChgBound : sumChgSats.toNat ≤ sumOutSats.toNat) :
    (BitcoinLedger.Psbt.scanOutputsCheckedLoop crypto cfg isBip322 policy idx rem dispAcc chgAcc sumOutSats sumChgSats).map
      (fun t => (t.1, t.2.1, t.2.2.1.toNat, t.2.2.2.toNat)) =
    InternalSpec.Psbt.classifyAndValidateOutputsLoopWithConfig crypto cfg isBip322 policy idx rem dispAcc chgAcc
      sumOutSats.toNat sumChgSats.toNat ∧
    (∀ disp chg finalOut finalChg,
      BitcoinLedger.Psbt.scanOutputsCheckedLoop crypto cfg isBip322 policy idx rem dispAcc chgAcc sumOutSats sumChgSats =
        .ok (disp, chg, finalOut, finalChg) →
      finalOut.toNat ≤ MAX_MONEY ∧ finalChg.toNat ≤ finalOut.toNat) := by
  induction rem generalizing idx dispAcc chgAcc sumOutSats sumChgSats with
  | nil =>
      unfold BitcoinLedger.Psbt.scanOutputsCheckedLoop InternalSpec.Psbt.classifyAndValidateOutputsLoopWithConfig
      dsimp only
      cases cfg.maxChangeOutputs with
      | none =>
          refine ⟨rfl, ?_⟩
          intro disp chg finalOut finalChg hOk
          injection hOk with hEq
          rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
          rcases Prod.mk.inj hEq2 with ⟨_, hEq3⟩
          rcases Prod.mk.inj hEq3 with ⟨hO, hC⟩
          subst hO; subst hC
          exact ⟨hOutBound, hChgBound⟩
      | some cap =>
          dsimp only
          by_cases hGt : chgAcc.length > cap
          · simp only [decide_eq_true hGt, ↓reduceIte]
            refine ⟨rfl, ?_⟩
            intro _ _ _ _ hOk
            contradiction
          · simp only [decide_eq_false hGt, Bool.false_eq_true, ↓reduceIte]
            refine ⟨rfl, ?_⟩
            intro disp chg finalOut finalChg hOk
            injection hOk with hEq
            rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
            rcases Prod.mk.inj hEq2 with ⟨_, hEq3⟩
            rcases Prod.mk.inj hEq3 with ⟨hO, hC⟩
            subst hO; subst hC
            exact ⟨hOutBound, hChgBound⟩
  | cons out rest ih =>
      unfold BitcoinLedger.Psbt.scanOutputsCheckedLoop InternalSpec.Psbt.classifyAndValidateOutputsLoopWithConfig
      unfold BitcoinLedger.Psbt.natToValidSats?
      cases hAmtGt : decide (out.amount > MAX_MONEY) with
      | true =>
          refine ⟨rfl, ?_⟩
          intro _ _ _ _ hOk
          contradiction
      | false =>
          have hAmtLe : out.amount ≤ MAX_MONEY := Nat.le_of_not_lt (of_decide_eq_false hAmtGt)
          have hOutSatsNat : (UInt64.ofNat out.amount).toNat = out.amount :=
            uint64_ofNat_toNat_of_le_max_money out.amount hAmtLe
          have hOutSatsLe : (UInt64.ofNat out.amount).toNat ≤ MAX_MONEY := by
            rw [hOutSatsNat]; exact hAmtLe
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [checkedAddSats?_spec sumOutSats (UInt64.ofNat out.amount) hOutBound hOutSatsLe]
          rw [hOutSatsNat]
          cases hSumGt : decide (sumOutSats.toNat + out.amount > MAX_MONEY) with
          | true =>
              refine ⟨rfl, ?_⟩
              intro _ _ _ _ hOk
              contradiction
          | false =>
              have hNextOutLe : sumOutSats.toNat + out.amount ≤ MAX_MONEY :=
                Nat.le_of_not_lt (of_decide_eq_false hSumGt)
              have hNextOutNat : (sumOutSats + UInt64.ofNat out.amount).toNat = sumOutSats.toNat + out.amount := by
                rw [uint64_add_toNat_of_le_max_money sumOutSats (UInt64.ofNat out.amount) hOutBound hOutSatsLe, hOutSatsNat]
              have hNextOutBound : (sumOutSats + UInt64.ofNat out.amount).toNat ≤ MAX_MONEY := by
                rw [hNextOutNat]; exact hNextOutLe
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [validateOutputScript_eq_spec]
              cases InternalSpec.Psbt.validateSingleOutputScriptWithOptions crypto (cfg.allowOpReturnOutputs || isBip322) out with
              | error e =>
                  refine ⟨rfl, ?_⟩
                  intro _ _ _ _ hOk
                  contradiction
              | ok u =>
                  cases u
                  dsimp only
                  rw [isInternalOutput_eq_spec]
                  cases InternalSpec.Psbt.isInternalOutputWithOptions cfg.masterFingerprint cfg.treatReceiveBranchAsInternal policy out with
                  | true =>
                      simp only [↓reduceIte]
                      have hChgBoundMax : sumChgSats.toNat ≤ MAX_MONEY := Nat.le_trans hChgBound hOutBound
                      have hNextChgNat : (sumChgSats + UInt64.ofNat out.amount).toNat = sumChgSats.toNat + out.amount := by
                        rw [uint64_add_toNat_of_le_max_money sumChgSats (UInt64.ofNat out.amount) hChgBoundMax hOutSatsLe, hOutSatsNat]
                      have hNextChgBound : (sumChgSats + UInt64.ofNat out.amount).toNat ≤ (sumOutSats + UInt64.ofNat out.amount).toNat := by
                        rw [hNextChgNat, hNextOutNat]
                        exact Nat.add_le_add_right hChgBound out.amount
                      have ⟨hRef, hBnd⟩ := ih (idx + 1) dispAcc ((idx, out) :: chgAcc)
                        (sumOutSats + UInt64.ofNat out.amount) (sumChgSats + UInt64.ofNat out.amount)
                        hNextOutBound hNextChgBound
                      rw [hNextOutNat, hNextChgNat] at hRef
                      exact ⟨hRef, hBnd⟩
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      have hNextChgBound : sumChgSats.toNat ≤ (sumOutSats + UInt64.ofNat out.amount).toNat := by
                        rw [hNextOutNat]
                        exact Nat.le_trans hChgBound (Nat.le_add_right _ _)
                      have ⟨hRef, hBnd⟩ := ih (idx + 1) ((idx, out) :: dispAcc) chgAcc
                        (sumOutSats + UInt64.ofNat out.amount) sumChgSats
                        hNextOutBound hNextChgBound
                      rw [hNextOutNat] at hRef
                      exact ⟨hRef, hBnd⟩

theorem scanOutputsChecked_refines
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (isBip322 : Bool)
    (policy : WalletPolicySpec)
    (outputs : List PsbtOutput) :
    (BitcoinLedger.Psbt.scanOutputsChecked crypto cfg isBip322 policy outputs).map
      (fun t => (t.1, t.2.1, t.2.2.1.toNat, t.2.2.2.toNat)) =
    InternalSpec.Psbt.classifyAndValidateOutputsWithConfig crypto cfg isBip322 policy outputs ∧
    (∀ disp chg finalOut finalChg,
      BitcoinLedger.Psbt.scanOutputsChecked crypto cfg isBip322 policy outputs =
        .ok (disp, chg, finalOut, finalChg) →
      finalOut.toNat ≤ MAX_MONEY ∧ finalChg.toNat ≤ finalOut.toNat) :=
  scanOutputsCheckedLoop_refines crypto cfg isBip322 policy 0 outputs [] [] 0 0 (Nat.zero_le _) (Nat.zero_le _)

private theorem reject_if_true_eq_ok {ε α : Type} {c : Bool} {e : ε} {rest : Except ε α} {v : α}
    (h : (if c then Except.error e else rest) = Except.ok v) : rest = Except.ok v := by
  cases c with
  | true => contradiction
  | false => exact h

private theorem validateInputUtxo_amount_le_max_money
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (exempt : Bool)
    (utxoInfo : ValidatedInputUtxo)
    (hOk : InternalSpec.Psbt.validateInputUtxo crypto inp exempt = .ok utxoInfo) :
    utxoInfo.prevoutTxOut.amount ≤ MAX_MONEY := by
  unfold InternalSpec.Psbt.validateInputUtxo at hOk
  cases hExt : InternalSpec.Psbt.extractInputPrevout crypto.sha256 inp with
  | error _ => rw [hExt] at hOk; contradiction
  | ok pair =>
      rcases pair with ⟨txOut, hasNw⟩
      rw [hExt] at hOk
      dsimp only at hOk
      have h1 := reject_if_true_eq_ok hOk
      have h2 := reject_if_true_eq_ok h1
      have h3 := reject_if_true_eq_ok h2
      have h4 := reject_if_true_eq_ok h3
      have h5 := reject_if_true_eq_ok h4
      cases hGt : decide (txOut.amount > MAX_MONEY) with
      | true => rw [hGt] at h5; contradiction
      | false =>
          rw [hGt] at h5
          simp only [Bool.false_eq_true, ↓reduceIte] at h5
          injection h5 with hEq
          subst hEq
          exact Nat.le_of_not_lt (of_decide_eq_false hGt)

private theorem validateExternalInputUtxo_amount_le_max_money
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (utxoInfo : ValidatedInputUtxo)
    (hOk : InternalSpec.Psbt.validateExternalInputUtxo crypto inp = .ok utxoInfo) :
    utxoInfo.prevoutTxOut.amount ≤ MAX_MONEY := by
  unfold InternalSpec.Psbt.validateExternalInputUtxo at hOk
  cases hExt : InternalSpec.Psbt.extractInputPrevout crypto.sha256 inp with
  | error _ => rw [hExt] at hOk; contradiction
  | ok pair =>
      rcases pair with ⟨txOut, _⟩
      rw [hExt] at hOk
      dsimp only at hOk
      cases hGt : decide (txOut.amount > MAX_MONEY) with
      | true => rw [hGt] at hOk; contradiction
      | false =>
          rw [hGt] at hOk
          simp only [Bool.false_eq_true, ↓reduceIte] at hOk
          injection hOk with hEq
          subst hEq
          exact Nat.le_of_not_lt (of_decide_eq_false hGt)

private def checkedInputStateToSpec (st : BitcoinLedger.Psbt.CheckedInputScanState) : InternalSpec.Psbt.InputScanAcc := {
  valInputs := st.valInputs
  sumIn := st.sumInSats.toNat
  sumInternalIn := st.sumInternalInSats.toNat
  nInternal := st.nInternal
  nExternal := st.nExternal
  anyTaprootInternal := st.anyTaprootInternal
  anyExternalMissingNw := st.anyExternalMissingNw
  warnMissingNw := st.warnMissingNw
  warnNonDefaultSighash := st.warnNonDefaultSighash
  sighashInputsOpen := st.sighashInputsOpen
  sighashOutputsOpen := st.sighashOutputsOpen
  firstSighash := st.firstSighash
  sighashMixed := st.sighashMixed
}

private theorem scanInputsCheckedLoop_refines
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (isBip322 : Bool)
    (nOutputs idx : Nat)
    (rem : List PsbtInput)
    (st : BitcoinLedger.Psbt.CheckedInputScanState)
    (hInBound : st.sumInSats.toNat ≤ MAX_MONEY)
    (hIntBound : st.sumInternalInSats.toNat ≤ st.sumInSats.toNat) :
    (BitcoinLedger.Psbt.scanInputsCheckedLoop crypto cfg policy isBip322 nOutputs idx rem st).map
      checkedInputStateToSpec =
    InternalSpec.Psbt.validateInputsLoop crypto cfg policy isBip322 nOutputs idx rem (checkedInputStateToSpec st) ∧
    (∀ finalSt,
      BitcoinLedger.Psbt.scanInputsCheckedLoop crypto cfg policy isBip322 nOutputs idx rem st = .ok finalSt →
      finalSt.sumInSats.toNat ≤ MAX_MONEY ∧ finalSt.sumInternalInSats.toNat ≤ finalSt.sumInSats.toNat) := by
  induction rem generalizing idx st with
  | nil =>
      unfold BitcoinLedger.Psbt.scanInputsCheckedLoop InternalSpec.Psbt.validateInputsLoop checkedInputStateToSpec
      dsimp only
      by_cases hZero : st.nInternal = 0
      · simp only [decide_eq_true hZero, ↓reduceIte]
        refine ⟨rfl, ?_⟩
        intro _ hOk; contradiction
      · simp only [decide_eq_false hZero, Bool.false_eq_true, ↓reduceIte]
        refine ⟨rfl, ?_⟩
        intro finalSt hOk
        injection hOk with hEq
        subst hEq
        exact ⟨hInBound, hIntBound⟩
  | cons inp rest ih =>
      unfold BitcoinLedger.Psbt.scanInputsCheckedLoop InternalSpec.Psbt.validateInputsLoop
      have hConfEq : BitcoinLedger.Psbt.MAX_CLEARTEXT_CONFUSION = InternalSpec.Psbt.MAX_CLEARTEXT_CONFUSION_SCORE := rfl
      rw [hConfEq]
      by_cases hConf : inp.cleartextConfusionScore > InternalSpec.Psbt.MAX_CLEARTEXT_CONFUSION_SCORE
      · simp only [decide_eq_true hConf, ↓reduceIte]
        exact ⟨rfl, fun _ hOk => by cases hOk⟩
      · simp only [decide_eq_false hConf, Bool.false_eq_true, ↓reduceIte]
        rw [extractInputPrevout_eq_spec]
        cases InternalSpec.Psbt.extractInputPrevout crypto.sha256 inp with
        | error e =>
            exact ⟨rfl, fun _ hOk => by cases hOk⟩
        | ok prevPair =>
            rcases prevPair with ⟨prevTxOut, _⟩
            dsimp only
            rw [classifyInternalInput_eq_spec]
            cases InternalSpec.Psbt.classifyInternalInputWithMaster cfg.masterFingerprint policy inp prevTxOut with
            | redeemMismatch =>
                exact ⟨rfl, fun _ hOk => by cases hOk⟩
            | witnessMismatch =>
                exact ⟨rfl, fun _ hOk => by cases hOk⟩
            | matched _ _ =>
                dsimp only
                rw [validateInternalInputUtxo_eq_spec]
                cases hUtxo : InternalSpec.Psbt.validateInputUtxo crypto inp (isBip322 && decide (idx = 0)) with
                | error e =>
                    exact ⟨rfl, fun _ hOk => by cases hOk⟩
                | ok utxoInfo =>
                    dsimp only
                    have hAmtLe : utxoInfo.prevoutTxOut.amount ≤ MAX_MONEY :=
                      validateInputUtxo_amount_le_max_money crypto inp _ utxoInfo hUtxo
                    have hInSatsNat : (UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat = utxoInfo.prevoutTxOut.amount :=
                      uint64_ofNat_toNat_of_le_max_money utxoInfo.prevoutTxOut.amount hAmtLe
                    have hInSatsLe : (UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat ≤ MAX_MONEY := by
                      rw [hInSatsNat]; exact hAmtLe
                    rw [checkedAddSats?_spec st.sumInSats (UInt64.ofNat utxoInfo.prevoutTxOut.amount) hInBound hInSatsLe]
                    rw [hInSatsNat]
                    have hAccSumEq : (checkedInputStateToSpec st).sumIn = st.sumInSats.toNat := rfl
                    rw [hAccSumEq]
                    cases hSumGt : decide (st.sumInSats.toNat + utxoInfo.prevoutTxOut.amount > MAX_MONEY) with
                    | true =>
                        exact ⟨rfl, fun _ hOk => by cases hOk⟩
                    | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        have hNextInLe : st.sumInSats.toNat + utxoInfo.prevoutTxOut.amount ≤ MAX_MONEY :=
                          Nat.le_of_not_lt (of_decide_eq_false hSumGt)
                        have hNextInNat : (st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat =
                            st.sumInSats.toNat + utxoInfo.prevoutTxOut.amount := by
                          rw [uint64_add_toNat_of_le_max_money st.sumInSats (UInt64.ofNat utxoInfo.prevoutTxOut.amount) hInBound hInSatsLe, hInSatsNat]
                        have hNextInBound : (st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat ≤ MAX_MONEY := by
                          rw [hNextInNat]; exact hNextInLe
                        have hIntMax : st.sumInternalInSats.toNat ≤ MAX_MONEY := Nat.le_trans hIntBound hInBound
                        have hNextIntNat : (st.sumInternalInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat =
                            st.sumInternalInSats.toNat + utxoInfo.prevoutTxOut.amount := by
                          rw [uint64_add_toNat_of_le_max_money st.sumInternalInSats (UInt64.ofNat utxoInfo.prevoutTxOut.amount) hIntMax hInSatsLe, hInSatsNat]
                        have hNextIntBound : (st.sumInternalInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat ≤
                            (st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat := by
                          rw [hNextIntNat, hNextInNat]
                          exact Nat.add_le_add_right hIntBound utxoInfo.prevoutTxOut.amount
                        cases (!decide (utxoInfo.spendClass = policy.spendClass)) with
                        | true =>
                            exact ⟨rfl, fun _ hOk => by cases hOk⟩
                        | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            rw [classifySighashType_eq_spec]
                            rcases hSh : InternalSpec.Psbt.classifySighash policy.spendClass inp.sighashType with ⟨safety, shByte⟩
                            cases safety with
                            | unsupported =>
                                exact ⟨rfl, fun _ hOk => by cases hOk⟩
                            | nonSafe =>
                                cases (!cfg.allowNonDefaultSighash) with
                                | true =>
                                    exact ⟨rfl, fun _ hOk => by cases hOk⟩
                                | false =>
                                    simp only [Bool.false_eq_true, ↓reduceIte, sighashBaseIsSingle_eq_spec]
                                    cases hSingleOob : InternalSpec.Psbt.sighashIsSingle shByte && decide (idx ≥ nOutputs) with
                                    | true =>
                                        exact ⟨rfl, fun _ hOk => by cases hOk⟩
                                    | false =>
                                        simp only [Bool.false_eq_true, ↓reduceIte, sighashHasAnyoneCanPay_eq_spec, sighashLeavesOutputsOpen_eq_spec]
                                        let nextSt : BitcoinLedger.Psbt.CheckedInputScanState := {
                                          valInputs := st.valInputs.push (utxoInfo, true, shByte)
                                          sumInSats := st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount
                                          sumInternalInSats := st.sumInternalInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount
                                          nInternal := st.nInternal + 1
                                          nExternal := st.nExternal
                                          anyTaprootInternal := st.anyTaprootInternal || decide (utxoInfo.spendClass = .taprootV1)
                                          anyExternalMissingNw := st.anyExternalMissingNw
                                          warnMissingNw := st.warnMissingNw || utxoInfo.missingNonWitnessUtxoWarning
                                          warnNonDefaultSighash := true
                                          sighashInputsOpen := st.sighashInputsOpen || InternalSpec.Psbt.sighashOpensInputs shByte
                                          sighashOutputsOpen := st.sighashOutputsOpen || InternalSpec.Psbt.sighashOpensOutputs shByte
                                          firstSighash := (match st.firstSighash with
                                            | none => (some (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte), st.sighashMixed)
                                            | some prev => (some prev, st.sighashMixed || !decide (prev = (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte)))).1
                                          sighashMixed := (match st.firstSighash with
                                            | none => (some (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte), st.sighashMixed)
                                            | some prev => (some prev, st.sighashMixed || !decide (prev = (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte)))).2
                                        }
                                        have ⟨hRef, hBnd⟩ := ih (idx + 1) nextSt hNextInBound hNextIntBound
                                        refine ⟨?_, hBnd⟩
                                        refine Eq.trans hRef ?_
                                        unfold checkedInputStateToSpec nextSt
                                        dsimp only
                                        rw [hNextInNat, hNextIntNat]
                                        rfl
                            | safe =>
                                simp only [sighashBaseIsSingle_eq_spec]
                                cases hSingleOob : InternalSpec.Psbt.sighashIsSingle shByte && decide (idx ≥ nOutputs) with
                                | true =>
                                    exact ⟨rfl, fun _ hOk => by cases hOk⟩
                                | false =>
                                    simp only [Bool.false_eq_true, ↓reduceIte, sighashHasAnyoneCanPay_eq_spec, sighashLeavesOutputsOpen_eq_spec]
                                    let nextSt : BitcoinLedger.Psbt.CheckedInputScanState := {
                                      valInputs := st.valInputs.push (utxoInfo, true, shByte)
                                      sumInSats := st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount
                                      sumInternalInSats := st.sumInternalInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount
                                      nInternal := st.nInternal + 1
                                      nExternal := st.nExternal
                                      anyTaprootInternal := st.anyTaprootInternal || decide (utxoInfo.spendClass = .taprootV1)
                                      anyExternalMissingNw := st.anyExternalMissingNw
                                      warnMissingNw := st.warnMissingNw || utxoInfo.missingNonWitnessUtxoWarning
                                      warnNonDefaultSighash := st.warnNonDefaultSighash
                                      sighashInputsOpen := st.sighashInputsOpen || InternalSpec.Psbt.sighashOpensInputs shByte
                                      sighashOutputsOpen := st.sighashOutputsOpen || InternalSpec.Psbt.sighashOpensOutputs shByte
                                      firstSighash := (match st.firstSighash with
                                        | none => (some (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte), st.sighashMixed)
                                        | some prev => (some prev, st.sighashMixed || !decide (prev = (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte)))).1
                                      sighashMixed := (match st.firstSighash with
                                        | none => (some (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte), st.sighashMixed)
                                        | some prev => (some prev, st.sighashMixed || !decide (prev = (if decide (shByte = SIGHASH_DEFAULT) then SIGHASH_ALL else shByte)))).2
                                    }
                                    have ⟨hRef, hBnd⟩ := ih (idx + 1) nextSt hNextInBound hNextIntBound
                                    refine ⟨?_, hBnd⟩
                                    refine Eq.trans hRef ?_
                                    unfold checkedInputStateToSpec nextSt
                                    dsimp only
                                    rw [hNextInNat, hNextIntNat]
                                    rfl
            | notInternal =>
                cases (!cfg.allowExternalInputs) with
                | true =>
                    exact ⟨rfl, fun _ hOk => by cases hOk⟩
                | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [validateExternalInputUtxo_eq_spec]
                    cases hExtUtxo : InternalSpec.Psbt.validateExternalInputUtxo crypto inp with
                    | error e =>
                        exact ⟨rfl, fun _ hOk => by cases hOk⟩
                    | ok utxoInfo =>
                        dsimp only
                        have hAmtLe : utxoInfo.prevoutTxOut.amount ≤ MAX_MONEY :=
                          validateExternalInputUtxo_amount_le_max_money crypto inp utxoInfo hExtUtxo
                        have hInSatsNat : (UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat = utxoInfo.prevoutTxOut.amount :=
                          uint64_ofNat_toNat_of_le_max_money utxoInfo.prevoutTxOut.amount hAmtLe
                        have hInSatsLe : (UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat ≤ MAX_MONEY := by
                          rw [hInSatsNat]; exact hAmtLe
                        rw [checkedAddSats?_spec st.sumInSats (UInt64.ofNat utxoInfo.prevoutTxOut.amount) hInBound hInSatsLe]
                        rw [hInSatsNat]
                        have hAccSumEq : (checkedInputStateToSpec st).sumIn = st.sumInSats.toNat := rfl
                        rw [hAccSumEq]
                        cases hSumGt : decide (st.sumInSats.toNat + utxoInfo.prevoutTxOut.amount > MAX_MONEY) with
                        | true =>
                            exact ⟨rfl, fun _ hOk => by cases hOk⟩
                        | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            have hNextInLe : st.sumInSats.toNat + utxoInfo.prevoutTxOut.amount ≤ MAX_MONEY :=
                              Nat.le_of_not_lt (of_decide_eq_false hSumGt)
                            have hNextInNat : (st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat =
                                st.sumInSats.toNat + utxoInfo.prevoutTxOut.amount := by
                              rw [uint64_add_toNat_of_le_max_money st.sumInSats (UInt64.ofNat utxoInfo.prevoutTxOut.amount) hInBound hInSatsLe, hInSatsNat]
                            have hNextInBound : (st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat ≤ MAX_MONEY := by
                              rw [hNextInNat]; exact hNextInLe
                            have hNextIntBound : st.sumInternalInSats.toNat ≤ (st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount).toNat := by
                              rw [hNextInNat]
                              exact Nat.le_trans hIntBound (Nat.le_add_right _ _)
                            let nextSt : BitcoinLedger.Psbt.CheckedInputScanState := {
                              valInputs := st.valInputs.push (utxoInfo, false, SIGHASH_ALL)
                              sumInSats := st.sumInSats + UInt64.ofNat utxoInfo.prevoutTxOut.amount
                              sumInternalInSats := st.sumInternalInSats
                              nInternal := st.nInternal
                              nExternal := st.nExternal + 1
                              anyTaprootInternal := st.anyTaprootInternal
                              anyExternalMissingNw := st.anyExternalMissingNw || inp.nonWitnessUtxo.isNone
                              warnMissingNw := st.warnMissingNw
                              warnNonDefaultSighash := st.warnNonDefaultSighash
                              sighashInputsOpen := st.sighashInputsOpen
                              sighashOutputsOpen := st.sighashOutputsOpen
                              firstSighash := st.firstSighash
                              sighashMixed := st.sighashMixed
                            }
                            have ⟨hRef, hBnd⟩ := ih (idx + 1) nextSt hNextInBound hNextIntBound
                            refine ⟨?_, hBnd⟩
                            refine Eq.trans hRef ?_
                            unfold checkedInputStateToSpec nextSt
                            dsimp only
                            rw [hNextInNat]

theorem computeCheckedFeeSats_refines
    (inputsOpen outputsOpen : Bool)
    (sumInSats sumOutSats : UInt64)
    (hInBound : sumInSats.toNat ≤ MAX_MONEY) :
    (BitcoinLedger.Psbt.computeCheckedFeeSats inputsOpen outputsOpen sumInSats sumOutSats).map
      (fun opt => opt.map UInt64.toNat) =
    InternalSpec.Psbt.computeClosedFee inputsOpen outputsOpen sumInSats.toNat sumOutSats.toNat := by
  unfold BitcoinLedger.Psbt.computeCheckedFeeSats InternalSpec.Psbt.computeClosedFee
  cases (!inputsOpen && !outputsOpen) with
  | false => rfl
  | true =>
      simp only [↓reduceIte]
      unfold BitcoinLedger.Psbt.checkedSubSats?
      have hDt : decide (sumInSats.toNat ≤ MAX_MONEY) = true := decide_eq_true hInBound
      rw [hDt, Bool.true_and]
      by_cases hLt : sumInSats.toNat < sumOutSats.toNat
      · simp only [decide_eq_true hLt, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rfl
      · simp only [decide_eq_false hLt, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
        have hLeNat : sumOutSats.toNat ≤ sumInSats.toNat := Nat.le_of_not_lt hLt
        have hLeU64 : sumOutSats ≤ sumInSats := UInt64.le_iff_toNat_le.mpr hLeNat
        dsimp [Except.map]
        rw [UInt64.toNat_sub_of_le sumInSats sumOutSats hLeU64]

theorem selectTxDisplayMode_eq_spec
    (warnNonDefaultSighash sighashMixed : Bool)
    (firstSighash : Option UInt8)
    (nOutputs nExternal : Nat)
    (externalAmountUnverified displayedOutsEmpty : Bool) :
    BitcoinLedger.Psbt.selectTxDisplayMode warnNonDefaultSighash sighashMixed firstSighash
      nOutputs nExternal externalAmountUnverified displayedOutsEmpty =
    InternalSpec.Psbt.decideDisplayMode warnNonDefaultSighash sighashMixed firstSighash
      nOutputs nExternal externalAmountUnverified displayedOutsEmpty := rfl

/-- **MAIN REFINEMENT THEOREM**:
    `BitcoinLedger.Psbt.validatePsbtTransaction` (using fixed-width checked `UInt64` satoshi arithmetic,
    single-pass `determineLocktime`, and freestanding equality checks) is extensionally equal to
    `InternalSpec.Psbt.validatePsbt` on ALL inputs, configurations, and wallet policies! -/
theorem validatePsbtTransaction_eq_spec
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx) :
    BitcoinLedger.Psbt.validatePsbtTransaction crypto cfg policy psbt =
      InternalSpec.Psbt.validatePsbt crypto cfg policy psbt := by
  unfold BitcoinLedger.Psbt.validatePsbtTransaction InternalSpec.Psbt.validatePsbt
  rw [checkMusig2SessionIdOpt_eq_spec, checkPolicyHeader_eq_spec]
  cases (!InternalSpec.Psbt.validateMusig2SessionIdOpt cfg.musig2SessionId) with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases InternalSpec.Psbt.validatePolicyHeader policy with
      | error _ => rfl
      | ok u =>
          cases u
          dsimp only
          cases (psbt.inputs.isEmpty || psbt.outputs.isEmpty) with
          | true => rfl
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              rw [determineLocktime_eq_spec]
              cases InternalSpec.Psbt.determineLocktime psbt.fallbackLocktime psbt.inputs.toList with
              | error _ => rfl
              | ok locktime =>
                  dsimp only
                  have ⟨hInRef, hInBnd⟩ := scanInputsCheckedLoop_refines
                    crypto cfg policy psbt.bip322Message.isSome psbt.outputs.size 0 psbt.inputs.toList {}
                    (Nat.zero_le _) (Nat.zero_le _)
                  have hInitSpec : checkedInputStateToSpec {} = ({} : InternalSpec.Psbt.InputScanAcc) := rfl
                  rw [hInitSpec] at hInRef
                  cases hInRun : BitcoinLedger.Psbt.scanInputsCheckedLoop
                      crypto cfg policy psbt.bip322Message.isSome psbt.outputs.size 0 psbt.inputs.toList {} with
                  | error e =>
                      rw [hInRun] at hInRef
                      dsimp [Except.map] at hInRef
                      rw [← hInRef]
                  | ok inSt =>
                      rw [hInRun] at hInRef
                      dsimp [Except.map] at hInRef
                      rw [← hInRef]
                      dsimp only
                      have ⟨hInMax, _⟩ := hInBnd inSt hInRun
                      have ⟨hOutRef, _⟩ := scanOutputsChecked_refines
                        crypto cfg psbt.bip322Message.isSome policy psbt.outputs.toList
                      cases hOutRun : BitcoinLedger.Psbt.scanOutputsChecked
                          crypto cfg psbt.bip322Message.isSome policy psbt.outputs.toList with
                      | error e =>
                          rw [hOutRun] at hOutRef
                          dsimp [Except.map] at hOutRef
                          rw [← hOutRef]
                      | ok outTup =>
                          rcases outTup with ⟨displayedOuts, changeOuts, sumOutSats, sumChgSats⟩
                          rw [hOutRun] at hOutRef
                          dsimp [Except.map] at hOutRef
                          rw [← hOutRef]
                          dsimp only
                          have hFeeRef := computeCheckedFeeSats_refines
                            inSt.sighashInputsOpen inSt.sighashOutputsOpen inSt.sumInSats sumOutSats hInMax
                          cases hFeeRun : BitcoinLedger.Psbt.computeCheckedFeeSats
                              inSt.sighashInputsOpen inSt.sighashOutputsOpen inSt.sumInSats sumOutSats with
                          | error e =>
                              rw [hFeeRun] at hFeeRef
                              dsimp [Except.map] at hFeeRef
                              unfold checkedInputStateToSpec at *
                              dsimp only at *
                              rw [← hFeeRef]
                          | ok feeSats? =>
                              rw [hFeeRun] at hFeeRef
                              dsimp [Except.map] at hFeeRef
                              unfold checkedInputStateToSpec at *
                              dsimp only at *
                              rw [← hFeeRef]
                              dsimp only
                              rw [selectTxDisplayMode_eq_spec]
                              cases feeSats? <;>
                                (cases InternalSpec.Psbt.decideDisplayMode inSt.warnNonDefaultSighash inSt.sighashMixed
                                   inSt.firstSighash psbt.outputs.size inSt.nExternal
                                   (inSt.anyExternalMissingNw && !(inSt.anyTaprootInternal && !inSt.sighashInputsOpen))
                                   displayedOuts.isEmpty <;> rfl)

/-- Alias agreement `validatePsbt = InternalSpec.Psbt.validatePsbt`. -/
theorem validatePsbt_eq_spec
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx) :
    BitcoinLedger.Psbt.validatePsbt crypto cfg policy psbt =
      InternalSpec.Psbt.validatePsbt crypto cfg policy psbt :=
  validatePsbtTransaction_eq_spec crypto cfg policy psbt

/-! ## 6. Sighash Digest, BIP-322, Ledger Swap & `authorizePsbtSigning` Refinement -/

theorem computeTxHashes_eq_spec
    (sha256 : ByteArray → Bytes32)
    (inputs : List (PsbtInput × TxOut))
    (outputs : List TxOut) :
    BitcoinLedger.Psbt.computeTxHashes sha256 inputs outputs =
      InternalSpec.Psbt.computeTxHashes sha256 inputs outputs := rfl

theorem computeSighashLegacy_eq_spec
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (inputs : Array PsbtInput)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (scriptCode : ByteArray)
    (sighashByte : UInt8) :
    BitcoinLedger.Psbt.computeSighashLegacy sha256 txVersion locktime inputs outputs inputIndex scriptCode sighashByte =
      InternalSpec.Psbt.sighashLegacy sha256 txVersion locktime inputs outputs inputIndex scriptCode sighashByte := rfl

theorem buildSegwitV0ScriptCode_eq_spec
    (activeScript : ByteArray)
    (witnessScript : Option ByteArray) :
    BitcoinLedger.Psbt.buildSegwitV0ScriptCode activeScript witnessScript =
      InternalSpec.Psbt.segwitV0ScriptCode activeScript witnessScript := by
  unfold BitcoinLedger.Psbt.buildSegwitV0ScriptCode InternalSpec.Psbt.segwitV0ScriptCode
  rw [checkP2WPKH_eq_spec, checkP2WSH_eq_spec]
  rfl

theorem computeSighashSegwitV0_eq_spec
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (hashes : TxHashes)
    (inp : PsbtInput)
    (utxoAmount : Nat)
    (scriptCodeWithLen : ByteArray)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (sighashByte : UInt8) :
    BitcoinLedger.Psbt.computeSighashSegwitV0 sha256 txVersion locktime hashes inp utxoAmount scriptCodeWithLen outputs inputIndex sighashByte =
      InternalSpec.Psbt.sighashSegwitV0 sha256 txVersion locktime hashes inp utxoAmount scriptCodeWithLen outputs inputIndex sighashByte := rfl

theorem computeSighashTaproot_eq_spec
    (sha256 : ByteArray → Bytes32)
    (txVersion : UInt32)
    (locktime : UInt32)
    (hashes : TxHashes)
    (inp : PsbtInput)
    (utxo : TxOut)
    (outputs : Array TxOut)
    (inputIndex : Nat)
    (tapleafHash : Option Bytes32)
    (sighashByte : UInt8) :
    BitcoinLedger.Psbt.computeSighashTaproot sha256 txVersion locktime hashes inp utxo outputs inputIndex tapleafHash sighashByte =
      InternalSpec.Psbt.sighashTaproot sha256 txVersion locktime hashes inp utxo outputs inputIndex tapleafHash sighashByte := rfl

theorem formatSignatureWithSighash_eq_spec
    (isSchnorr : Bool)
    (rawSig : ByteArray)
    (sighashByte : UInt8) :
    BitcoinLedger.Psbt.formatSignatureWithSighash isSchnorr rawSig sighashByte =
      InternalSpec.Psbt.appendSighashSuffix isSchnorr rawSig sighashByte := rfl

theorem buildBip322ToSpendTx_eq_spec
    (sha256 : ByteArray → Bytes32)
    (message challengeScript : ByteArray) :
    BitcoinLedger.Psbt.buildBip322ToSpendTx sha256 message challengeScript =
      InternalSpec.Psbt.bip322ToSpendTx sha256 message challengeScript := rfl

theorem computeBip322ToSpendTxid_eq_spec
    (sha256 : ByteArray → Bytes32)
    (message challengeScript : ByteArray) :
    BitcoinLedger.Psbt.computeBip322ToSpendTxid sha256 message challengeScript =
      InternalSpec.Psbt.bip322ToSpendTxid sha256 message challengeScript := rfl

theorem checkBip322PrintableAscii_eq_spec (msg : ByteArray) :
    BitcoinLedger.Psbt.checkBip322PrintableAscii msg =
      InternalSpec.Psbt.isBip322MessagePrintable msg := rfl

theorem checkBip322ProofOfFundsSequence_eq_spec (inp : PsbtInput) :
    BitcoinLedger.Psbt.checkBip322ProofOfFundsSequence inp =
      InternalSpec.Psbt.bip322ProofOfFundsSequenceValid inp := rfl

theorem validateBip322Psbt_eq_spec
    (sha256 : ByteArray → Bytes32)
    (inSwapMode : Bool)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (message : ByteArray) :
    BitcoinLedger.Psbt.validateBip322Psbt sha256 inSwapMode psbt validated message =
      InternalSpec.Psbt.validateBip322Psbt sha256 inSwapMode psbt validated message := by
  unfold BitcoinLedger.Psbt.validateBip322Psbt InternalSpec.Psbt.validateBip322Psbt
  cases inSwapMode with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases (!decide (psbt.txVersion = 0) && !decide (psbt.txVersion = 2)) with
      | true => rfl
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases (!decide (validated.locktime = 0)) with
          | true => rfl
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases (!decide (psbt.outputs.size = 1) || !validated.changeOutputs.isEmpty) with
              | true => rfl
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  if hOut : 0 < psbt.outputs.size then
                    simp only [hOut, ↓reduceDIte, eqOptBytes_eq_spec]
                    cases (!decide ((psbt.outputs[0]'hOut).amount = 0) ||
                           !InternalSpec.Psbt.optBytesEq (psbt.outputs[0]'hOut).scriptPubKey (some (ByteArray.mk #[0x6a]))) with
                    | true => rfl
                    | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        cases (validated.warnings.externalInputs || validated.warnings.nonDefaultSighash) with
                        | true => rfl
                        | false =>
                            simp only [Bool.false_eq_true, ↓reduceIte]
                            if hIn : 0 < psbt.inputs.size ∧ 0 < validated.validatedInputs.size then
                              simp only [hIn, eqOptU32_eq_spec, eqBytes32_eq_spec,
                                computeBip322ToSpendTxid_eq_spec]
                              rfl
                            else
                              simp only [hIn, ↓reduceDIte]
                  else
                    simp only [hOut, ↓reduceDIte]

theorem parseSwapOpReturnPayload_eq_spec (s : ByteArray) :
    BitcoinLedger.Psbt.parseSwapOpReturnPayload s =
      InternalSpec.Psbt.extractSwapOpReturnData s := by
  unfold BitcoinLedger.Psbt.parseSwapOpReturnPayload InternalSpec.Psbt.extractSwapOpReturnData
  rw [eqOptU8_eq_spec]
  rfl

theorem resolveSwapRecipientOutput_eq_spec
    (crypto : CryptoOracles)
    (mode : SwapMode)
    (displayedOutputs : List (Nat × PsbtOutput)) :
    BitcoinLedger.Psbt.resolveSwapRecipientOutput crypto mode displayedOutputs =
      InternalSpec.Psbt.extractSwapDestOutput crypto mode displayedOutputs := by
  unfold BitcoinLedger.Psbt.resolveSwapRecipientOutput InternalSpec.Psbt.extractSwapDestOutput
  cases mode with
  | standard => rfl
  | crossChain expectedHash =>
      cases displayedOutputs with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest2 =>
              cases rest2 with
              | cons _ _ => rfl
              | nil =>
                  rcases first with ⟨_, opOut⟩
                  rcases second with ⟨_, dOut⟩
                  dsimp only
                  cases (!decide (opOut.amount = 0)) with
                  | true => rfl
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases opOut.scriptPubKey with
                      | none => rfl
                      | some spk =>
                          dsimp only
                          rw [parseSwapOpReturnPayload_eq_spec]
                          cases InternalSpec.Psbt.extractSwapOpReturnData spk with
                          | none => rfl
                          | some payinData =>
                              dsimp only
                              rw [eqBytes32_eq_spec]

theorem validateSwapPsbt_eq_spec
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams) :
    BitcoinLedger.Psbt.validateSwapPsbt crypto policy psbt validated swap =
      InternalSpec.Psbt.validateSwapPsbt crypto policy psbt validated swap := by
  unfold BitcoinLedger.Psbt.validateSwapPsbt InternalSpec.Psbt.validateSwapPsbt
  rw [resolveSwapRecipientOutput_eq_spec]
  cases psbt.bip322Message.isSome with
  | true => rfl
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases (!policy.isDefault || validated.warnings.externalInputs ||
             validated.warnings.missingNonWitnessUtxo || validated.warnings.nonDefaultSighash) with
      | true => rfl
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases InternalSpec.Psbt.extractSwapDestOutput crypto swap.mode validated.displayedOutputs with
          | error _ => rfl
          | ok destOut =>
              dsimp only
              cases validated.fee with
              | none => rfl
              | some actualFee =>
                  dsimp only
                  cases (!decide (actualFee = swap.fees)) with
                  | true => rfl
                  | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases (!decide ((validated.sumOutputs - validated.sumChangeOutputs) = swap.amount) ||
                             !decide (destOut.amount = swap.amount)) with
                      | true => rfl
                      | false =>
                          simp only [Bool.false_eq_true, ↓reduceIte]
                          cases destOut.silentPayment.isSome with
                          | true => rfl
                          | false =>
                              simp only [Bool.false_eq_true, ↓reduceIte]
                              cases destOut.scriptPubKey with
                              | none => rfl
                              | some destSpk =>
                                  dsimp only
                                  rw [eqOptString_eq_spec]

/-- Top-level signing authorization refinement: `BitcoinLedger.Psbt.authorizePsbtSigning`
    agrees identically with `InternalSpec.Psbt.authorizePsbtSigning`. -/
theorem authorizePsbtSigning_eq_spec
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (swapParams : Option SwapParams) :
    BitcoinLedger.Psbt.authorizePsbtSigning crypto cfg policy psbt swapParams =
      InternalSpec.Psbt.authorizePsbtSigning crypto cfg policy psbt swapParams := by
  unfold BitcoinLedger.Psbt.authorizePsbtSigning InternalSpec.Psbt.authorizePsbtSigning
  rw [validatePsbtTransaction_eq_spec]
  cases InternalSpec.Psbt.validatePsbt crypto cfg policy psbt with
  | error _ => rfl
  | ok validated =>
      dsimp only
      cases psbt.bip322Message with
      | none =>
          dsimp only
          cases swapParams with
          | none => rfl
          | some swap =>
              dsimp only
              rw [validateSwapPsbt_eq_spec]
              rfl
      | some msg =>
          dsimp only
          rw [validateBip322Psbt_eq_spec]
          cases InternalSpec.Psbt.validateBip322Psbt crypto.sha256 swapParams.isSome psbt validated msg with
          | error _ => rfl
          | ok u =>
              cases u
              dsimp only
              cases swapParams with
              | none => rfl
              | some swap =>
                  dsimp only
                  rw [validateSwapPsbt_eq_spec]
                  rfl

/-! ## 7. Security, Fee Conservation & Non-Vacuity Theorems on `BitcoinLedger.Psbt` -/

/-- **Fee Conservation & Non-Negativity (`totalIn = totalOut + fee`)**:
    Whenever `BitcoinLedger.Psbt.validatePsbtTransaction` accepts a PSBT and produces a closed
    fee `v.fee = some f`, output satoshis never exceed input satoshis (`v.sumOutputs ≤ v.sumInputs`),
    `f = v.sumInputs - v.sumOutputs`, and exact value conservation `v.sumInputs = v.sumOutputs + f` holds. -/
theorem validated_psbt_fee_conservation
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (v : ValidatedPsbt)
    (f : Nat)
    (hValid : BitcoinLedger.Psbt.validatePsbtTransaction crypto cfg policy psbt = .ok v)
    (hFee : v.fee = some f) :
    v.sumOutputs ≤ v.sumInputs ∧
    f = v.sumInputs - v.sumOutputs ∧
    v.sumInputs = v.sumOutputs + f := by
  rw [validatePsbtTransaction_eq_spec] at hValid
  have ⟨hLe, hSub⟩ := InternalSpec.Psbt.validated_psbt_fee_non_negative crypto cfg policy psbt v f hValid hFee
  refine ⟨hLe, hSub, ?_⟩
  rw [hSub, Nat.add_comm, Nat.sub_add_cancel hLe]

/-- **Checked Fee Underflow Rejection**:
    When input and output sets are closed (`!inputsOpen && !outputsOpen`), if `sumInSats < sumOutSats`
    (with valid satoshi bounds `≤ MAX_MONEY`), `BitcoinLedger.Psbt.computeCheckedFeeSats` strictly
    rejects with `.negativeFeeOutputsExceedInputs`. -/
theorem computeCheckedFeeSats_negative_rejected
    (sumInSats sumOutSats : UInt64)
    (hInMax : sumInSats.toNat ≤ MAX_MONEY)
    (hLt : sumInSats.toNat < sumOutSats.toNat) :
    BitcoinLedger.Psbt.computeCheckedFeeSats false false sumInSats sumOutSats =
      .error .negativeFeeOutputsExceedInputs := by
  have hRef := computeCheckedFeeSats_refines false false sumInSats sumOutSats hInMax
  rw [InternalSpec.Psbt.negative_fee_rejected sumInSats.toNat sumOutSats.toNat hLt] at hRef
  cases hRes : BitcoinLedger.Psbt.computeCheckedFeeSats false false sumInSats sumOutSats with
  | ok _ =>
      rw [hRes] at hRef
      contradiction
  | error e =>
      rw [hRes] at hRef
      dsimp [Except.map] at hRef
      injection hRef with hEq
      rw [hEq]

/-- **Dual-UTXO Cross-Check Rejection on `extractInputPrevout` (CVE-2020-14199 Defense)**:
    Whenever an input supplies both `nonWitnessUtxo` and `witnessUtxo`, if `nonWitnessUtxo.vout[vout]`
    differs from `witnessUtxo` in either amount or `scriptPubKey`, `BitcoinLedger.Psbt.extractInputPrevout`
    strictly rejects with `.dualUtxoMismatch`. -/
theorem extractInputPrevout_dual_utxo_mismatch_rejected
    (sha256 : ByteArray → Bytes32)
    (inp : PsbtInput)
    (rawTx : RawTx)
    (wUtxo : TxOut)
    (hNw : inp.nonWitnessUtxo = some rawTx)
    (hW : inp.witnessUtxo = some wUtxo)
    (hTxid : BitcoinLedger.Psbt.computeTxid sha256 rawTx = inp.prevout.txid)
    (hBounds : inp.prevout.vout.toNat < rawTx.vout.size)
    (hDiff : rawTx.vout[inp.prevout.vout.toNat]'hBounds ≠ wUtxo) :
    BitcoinLedger.Psbt.extractInputPrevout sha256 inp = .error .dualUtxoMismatch := by
  rw [extractInputPrevout_eq_spec]
  unfold InternalSpec.Psbt.extractInputPrevout
  rw [computeTxid_eq_spec] at hTxid
  have hTxEq : InternalSpec.Psbt.bytes32Eq (InternalSpec.Psbt.computeTxid sha256 rawTx) inp.prevout.txid = true :=
    (InternalSpec.Psbt.bytes32Eq_iff _ _).mpr hTxid
  have hOutFalse : InternalSpec.Psbt.txOutEq (rawTx.vout[inp.prevout.vout.toNat]'hBounds) wUtxo = false := by
    cases hEq : InternalSpec.Psbt.txOutEq (rawTx.vout[inp.prevout.vout.toNat]'hBounds) wUtxo with
    | false => rfl
    | true => exact absurd ((InternalSpec.Psbt.txOutEq_iff _ _).mp hEq) hDiff
  simp only [hNw, hW, hTxEq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hBounds, ↓reduceDIte,
             hOutFalse, Bool.not_false]

/-- **Dual-UTXO Cross-Check Rejection on `validateInternalInputUtxo` (CVE-2020-14199 Defense)**: -/
theorem dual_utxo_mismatch_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (rawTx : RawTx)
    (wUtxo : TxOut)
    (exempt : Bool)
    (hNw : inp.nonWitnessUtxo = some rawTx)
    (hW : inp.witnessUtxo = some wUtxo)
    (hTxid : BitcoinLedger.Psbt.computeTxid crypto.sha256 rawTx = inp.prevout.txid)
    (hBounds : inp.prevout.vout.toNat < rawTx.vout.size)
    (hDiff : rawTx.vout[inp.prevout.vout.toNat]'hBounds ≠ wUtxo) :
    BitcoinLedger.Psbt.validateInternalInputUtxo crypto inp exempt = .error .dualUtxoMismatch := by
  rw [validateInternalInputUtxo_eq_spec]
  exact InternalSpec.Psbt.dual_utxo_mismatch_rejected crypto inp rawTx wUtxo exempt hNw hW hTxid hBounds hDiff

/-- **Missing UTXO Rejection**: -/
theorem missing_utxo_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (exempt : Bool)
    (hNoNw : inp.nonWitnessUtxo = none)
    (hNoW : inp.witnessUtxo = none) :
    BitcoinLedger.Psbt.validateInternalInputUtxo crypto inp exempt = .error .missingUtxo := by
  rw [validateInternalInputUtxo_eq_spec]
  exact InternalSpec.Psbt.missing_utxo_rejected crypto inp exempt hNoNw hNoW

/-- **Mismatched `nonWitnessUtxo` Txid Rejection**: -/
theorem mismatched_non_witness_utxo_txid_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (rawTx : RawTx)
    (exempt : Bool)
    (hNw : inp.nonWitnessUtxo = some rawTx)
    (hMismatch : BitcoinLedger.Psbt.computeTxid crypto.sha256 rawTx ≠ inp.prevout.txid) :
    BitcoinLedger.Psbt.validateInternalInputUtxo crypto inp exempt = .error .nonWitnessUtxoTxidMismatch := by
  rw [validateInternalInputUtxo_eq_spec]
  exact InternalSpec.Psbt.mismatched_non_witness_utxo_txid_rejected crypto inp rawTx exempt hNw hMismatch

/-- **Legacy Internal Input With `witnessUtxo` Rejected**: -/
theorem legacy_input_with_witness_utxo_rejected
    (crypto : CryptoOracles)
    (inp : PsbtInput)
    (wUtxo : TxOut)
    (exempt : Bool)
    (hNoNw : inp.nonWitnessUtxo = none)
    (hW : inp.witnessUtxo = some wUtxo)
    (hNoRedeem : inp.redeemScript = none)
    (hLegacy : BitcoinLedger.Psbt.classifyInputSpendClass wUtxo.scriptPubKey none = .legacy) :
    BitcoinLedger.Psbt.validateInternalInputUtxo crypto inp exempt = .error .legacyHasWitnessUtxo := by
  rw [validateInternalInputUtxo_eq_spec]
  rw [classifyInputSpendClass_eq_spec] at hLegacy
  exact InternalSpec.Psbt.legacy_input_with_witness_utxo_rejected crypto inp wUtxo exempt hNoNw hW hNoRedeem hLegacy

/-- **Unverified Change Never Hidden (`scanOutputsChecked`)**:
    Under default `SigningConfig`, every output `out` at index `k` with
    `BitcoinLedger.Psbt.isVerifiedChangeOutput policy out = false` MUST appear in `displayedOutputs`
    (never silently elided as change). -/
theorem unverified_change_never_hidden
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (outputs : List PsbtOutput)
    (dispOuts chgOuts : List (Nat × PsbtOutput))
    (sumOutSats sumChgSats : UInt64)
    (hOk : BitcoinLedger.Psbt.scanOutputsChecked crypto {} false policy outputs =
           .ok (dispOuts, chgOuts, sumOutSats, sumChgSats))
    (k : Nat) (out : PsbtOutput)
    (hGet : outputs[k]? = some out)
    (hUnverified : BitcoinLedger.Psbt.isVerifiedChangeOutput policy out = false) :
    (k, out) ∈ dispOuts := by
  have ⟨hRef, _⟩ := scanOutputsChecked_refines crypto {} false policy outputs
  rw [hOk] at hRef
  dsimp [Except.map] at hRef
  rw [isVerifiedChangeOutput_eq_spec] at hUnverified
  exact InternalSpec.Psbt.unverified_change_never_hidden crypto policy outputs
    dispOuts chgOuts sumOutSats.toNat sumChgSats.toNat hRef.symm k out hGet hUnverified

/-- **Receive-Branch Output Never Classified as Verified Change**:
    If every matching derivation coordinate for `out` uses the receive branch (`isChange = false`),
    `BitcoinLedger.Psbt.isVerifiedChangeOutput policy out = false`. -/
theorem receive_branch_output_not_verified_change
    (policy : WalletPolicySpec)
    (out : PsbtOutput)
    (hAllReceive : ∀ c idx,
      (c, idx) ∈ BitcoinLedger.Psbt.gatherCandidateCoordinates none policy out.derivations → c = false) :
    BitcoinLedger.Psbt.isVerifiedChangeOutput policy out = false := by
  rw [isVerifiedChangeOutput_eq_spec]
  apply InternalSpec.Psbt.receive_branch_output_not_verified_change
  intro c idx hMem
  rw [← gatherCandidateCoordinates_eq_spec] at hMem
  exact hAllReceive c idx hMem

/-- **Verified Change Requires `numSecond` Internal Change Branch (`isChange = true`)**: -/
theorem verified_change_requires_numSecond_branch
    (policy : WalletPolicySpec)
    (out : PsbtOutput)
    (hVer : BitcoinLedger.Psbt.isVerifiedChangeOutput policy out = true) :
    out.silentPayment = none ∧
    ∃ (spk : ByteArray) (entry : KeyDerivationEntry) (ph : InternalKeyPlaceholder) (addrIdx : UInt32),
      out.scriptPubKey = some spk ∧
      entry ∈ out.derivations ∧
      ph ∈ policy.internalPlaceholders ∧
      InternalSpec.Psbt.derivationMatchesPlaceholder ph entry = some (true, addrIdx) ∧
      ph.numFirst ≠ ph.numSecond ∧
      InternalSpec.Psbt.outputMatchesDerivedAt policy out spk true addrIdx = true ∧
      (∀ orig, ph.isMusig = false → ph.expectedOrigin = some orig →
        entry.origin.path.drop orig.path.length = [ph.numSecond, addrIdx]) := by
  rw [isVerifiedChangeOutput_eq_spec] at hVer
  exact InternalSpec.Psbt.verified_change_requires_numSecond_branch policy out hVer

/-- **`TxDisplayMode.unavailable` on Open/Mixed Sighashes & Self-Transfer Invariants**:
    1. Mixed sighashes across signed inputs force `TxDisplayMode.unavailable`.
    2. `SIGHASH_NONE` forces `TxDisplayMode.unavailable`.
    3. `SIGHASH_SINGLE` with `nOutputs ≠ 1` forces `TxDisplayMode.unavailable`.
    4. `TxDisplayMode.selfTransfer` requires zero external inputs (`nExternal = 0`). -/
theorem display_mode_unavailable_and_self_transfer_invariants :
    (∀ warn firstSh nOut nExt extUnv dispEmpty,
      BitcoinLedger.Psbt.selectTxDisplayMode warn true firstSh nOut nExt extUnv dispEmpty = .unavailable) ∧
    (∀ nOut nExt extUnv dispEmpty,
      BitcoinLedger.Psbt.selectTxDisplayMode true false (some SIGHASH_NONE) nOut nExt extUnv dispEmpty = .unavailable) ∧
    (∀ nOut nExt extUnv dispEmpty,
      nOut ≠ 1 →
      BitcoinLedger.Psbt.selectTxDisplayMode true false (some SIGHASH_SINGLE) nOut nExt extUnv dispEmpty = .unavailable) ∧
    (∀ warn mixed firstSh nOut nExt extUnv dispEmpty,
      BitcoinLedger.Psbt.selectTxDisplayMode warn mixed firstSh nOut nExt extUnv dispEmpty = .selfTransfer →
      nExt = 0) := by
  simp only [selectTxDisplayMode_eq_spec]
  exact InternalSpec.Psbt.display_mode_unavailable_and_self_transfer_invariants

/-- **High-Fee Warning Detection in BOTH `full` and `selfTransfer` Display Modes**: -/
theorem high_fee_warning_in_full_and_self_transfer
    (crypto : CryptoOracles)
    (cfg : SigningConfig)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (v : ValidatedPsbt)
    (f : Nat)
    (hValid : BitcoinLedger.Psbt.validatePsbtTransaction crypto cfg policy psbt = .ok v)
    (hMode : v.displayMode = .selfTransfer ∨ v.displayMode = .full)
    (hFee : v.fee = some f)
    (hTen : 10 * f ≥ v.sumInputs)
    (hAbove100k : v.sumInputs > 100000) :
    v.warnings.highFee = true := by
  rw [validatePsbtTransaction_eq_spec] at hValid
  exact InternalSpec.Psbt.self_transfer_high_fee_triggers_warning crypto cfg policy psbt v f
    hValid hMode hFee hTen hAbove100k

/-- **Ledger Exchange Swap Rejects Fee Mismatch**: -/
theorem swap_rejects_fee_mismatch
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (hFeeMismatch : validated.fee ≠ some swap.fees) :
    ∀ u, BitcoinLedger.Psbt.validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  rw [validateSwapPsbt_eq_spec]
  exact InternalSpec.Psbt.swap_rejects_fee_mismatch crypto policy psbt validated swap hFeeMismatch

/-- **Ledger Exchange Swap Rejects Amount Mismatch**: -/
theorem swap_rejects_amount_mismatch
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (hAmtMismatch : validated.sumOutputs - validated.sumChangeOutputs ≠ swap.amount) :
    ∀ u, BitcoinLedger.Psbt.validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  rw [validateSwapPsbt_eq_spec]
  exact InternalSpec.Psbt.swap_rejects_amount_mismatch crypto policy psbt validated swap hAmtMismatch

/-- **Ledger Exchange Swap Rejects Recipient Address Mismatch**: -/
theorem swap_rejects_recipient_mismatch
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (idx : Nat) (destOut : PsbtOutput)
    (hStd : swap.mode = .standard)
    (hOuts : validated.displayedOutputs = [(idx, destOut)])
    (hAddrMismatch : ∀ spk, destOut.scriptPubKey = some spk → crypto.formatAddress spk ≠ some swap.destinationAddress) :
    ∀ u, BitcoinLedger.Psbt.validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  rw [validateSwapPsbt_eq_spec]
  exact InternalSpec.Psbt.swap_rejects_recipient_mismatch crypto policy psbt validated swap idx destOut hStd hOuts hAddrMismatch

/-- **Ledger Exchange Swap Rejects Extra External Outputs**: -/
theorem swap_standard_rejects_extra_external_outputs
    (crypto : CryptoOracles)
    (policy : WalletPolicySpec)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (swap : SwapParams)
    (hStd : swap.mode = .standard)
    (hLen : validated.displayedOutputs.length ≠ 1) :
    ∀ u, BitcoinLedger.Psbt.validateSwapPsbt crypto policy psbt validated swap ≠ .ok u := by
  rw [validateSwapPsbt_eq_spec]
  exact InternalSpec.Psbt.swap_standard_rejects_extra_external_outputs crypto policy psbt validated swap hStd hLen

/-- **BIP-370 Locktime Rejects Height-Only vs Time-Only Conflicts**: -/
theorem bip370_locktime_conflict_rejected
    (fallback : Option UInt32)
    (inHeightOnly inTimeOnly : PsbtInput)
    (hValid1 : BitcoinLedger.Psbt.checkInputLocktimeBounds inHeightOnly = true)
    (hValid2 : BitcoinLedger.Psbt.checkInputLocktimeBounds inTimeOnly = true)
    (hH : inHeightOnly.requiredHeightLocktime = some 100 ∧ inHeightOnly.requiredTimeLocktime = none)
    (hT : inTimeOnly.requiredTimeLocktime = some 600000000 ∧ inTimeOnly.requiredHeightLocktime = none) :
    BitcoinLedger.Psbt.determineLocktime fallback [inHeightOnly, inTimeOnly] =
      .error .locktimeConflictOrInvalid := by
  rw [determineLocktime_eq_spec]
  exact InternalSpec.Psbt.bip370_locktime_conflict_rejected fallback inHeightOnly inTimeOnly hValid1 hValid2 hH hT

/-- **BIP-370 Locktime Ignores Fallback When Constrained by Required Height**: -/
theorem bip370_locktime_ignores_fallback_when_constrained
    (fb1 fb2 : Option UInt32)
    (inp : PsbtInput)
    (hReq : inp.requiredHeightLocktime = some 800000)
    (hNoTime : inp.requiredTimeLocktime = none) :
    BitcoinLedger.Psbt.determineLocktime fb1 [inp] = .ok 800000 ∧
    BitcoinLedger.Psbt.determineLocktime fb1 [inp] = BitcoinLedger.Psbt.determineLocktime fb2 [inp] := by
  rw [determineLocktime_eq_spec fb1, determineLocktime_eq_spec fb2]
  exact InternalSpec.Psbt.bip370_locktime_ignores_fallback_when_constrained fb1 fb2 inp hReq hNoTime

/-- **PSBTv0 Normalization Rejects Non-Empty `scriptSig`**: -/
theorem psbt_v0_nonempty_scriptsig_rejected
    (v0 : PsbtV0)
    (hVer : v0.version = none)
    (hNoWit : v0.unsignedTxHasWitness = false)
    (hNoV2 : v0.hasV2ExclusiveGlobals = false)
    (txin : RawTxIn)
    (hVin : v0.unsignedTx.vin = #[txin])
    (hNonEmpty : txin.scriptSig.size ≠ 0) :
    BitcoinLedger.Psbt.normalizePsbtV0ToV2 v0 = .error .psbtV0NonEmptyScriptSig := by
  rw [normalizePsbtV0ToV2_eq_spec]
  exact InternalSpec.Psbt.psbt_v0_nonempty_scriptsig_rejected v0 hVer hNoWit hNoV2 txin hVin hNonEmpty

/-- **BIP-322 Message Signing Rejected in Swap Mode**: -/
theorem bip322_rejected_in_swap_mode
    (sha256 : ByteArray → Bytes32)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (msg : ByteArray) :
    BitcoinLedger.Psbt.validateBip322Psbt sha256 true psbt validated msg =
      .error .bip322ForbiddenInSwap := rfl

/-- **BIP-322 Virtual `to_sign` Enforces `to_spend` Challenge Txid Binding**: -/
theorem bip322_enforces_to_spend_binding
    (sha256 : ByteArray → Bytes32)
    (psbt : PsbtTx)
    (validated : ValidatedPsbt)
    (msg : ByteArray)
    (hOk : BitcoinLedger.Psbt.validateBip322Psbt sha256 false psbt validated msg = .ok ()) :
    validated.locktime = 0 ∧
    psbt.outputs.size = 1 ∧
    validated.changeOutputs = [] ∧
    ∃ (hIn0 : 0 < psbt.inputs.size) (hVal0 : 0 < validated.validatedInputs.size),
      (psbt.inputs[0]'hIn0).sequence = some 0 ∧
      (psbt.inputs[0]'hIn0).prevout.txid =
        BitcoinLedger.Psbt.computeBip322ToSpendTxid sha256 msg
          (validated.validatedInputs[0]'hVal0).1.prevoutTxOut.scriptPubKey := by
  rw [validateBip322Psbt_eq_spec] at hOk
  exact InternalSpec.Psbt.bip322_enforces_to_spend_binding sha256 psbt validated msg hOk

/-- **Non-Vacuous Execution Witness 1: Valid Standard Taproot Swap PSBT Accepted End-to-End**: -/
theorem non_vacuity_valid_swap_psbt_accepted :
    ∃ (crypto : CryptoOracles) (policy : WalletPolicySpec) (psbt : PsbtTx) (swap : SwapParams) (res : ValidatedPsbt),
      BitcoinLedger.Psbt.authorizePsbtSigning crypto {} policy psbt (some swap) = .ok res ∧
      res.fee = some 1 ∧
      res.displayedOutputs.length = 1 ∧
      res.changeOutputs.length = 1 := by
  rcases InternalSpec.Psbt.non_vacuity_valid_swap_psbt_accepted with ⟨crypto, policy, psbt, swap, res, hOk, hFee, hDisp, hChg⟩
  refine ⟨crypto, policy, psbt, swap, res, ?_, hFee, hDisp, hChg⟩
  rw [authorizePsbtSigning_eq_spec]
  exact hOk

/-- **Non-Vacuous Execution Witness 2: Valid BIP-322 Message-Signing PSBT Accepted End-to-End**: -/
theorem non_vacuity_valid_bip322_psbt_accepted :
    ∃ (crypto : CryptoOracles) (policy : WalletPolicySpec) (psbt : PsbtTx) (res : ValidatedPsbt),
      psbt.bip322Message = some ("Hello Ledger".toUTF8) ∧
      BitcoinLedger.Psbt.authorizePsbtSigning crypto {} policy psbt none = .ok res := by
  rcases InternalSpec.Psbt.non_vacuity_valid_bip322_psbt_accepted with ⟨crypto, policy, psbt, res, hMsg, hOk⟩
  refine ⟨crypto, policy, psbt, res, hMsg, ?_⟩
  rw [authorizePsbtSigning_eq_spec]
  exact hOk

end Proofs.Psbt

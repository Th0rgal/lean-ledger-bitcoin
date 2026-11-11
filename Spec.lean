/-
  Spec.lean — Minimal, Human-Auditable Top-Level Formal Specification of the Ledger Bitcoin App

  A reviewer auditing the security contract of `lean-ledger-bitcoin` only needs to read `Spec.lean`
  and its three orthogonal, non-overlapping domain modules (~450 LOC total):
    1. `Spec.KeyPolicy`         — BIP-32 path depth bounds, silent xpub export whitelists, Wallet Policy
                                  Proof-of-Registration & internal-key ownership, and receive/change separation.
    2. `Spec.TransactionSafety` — Overflow-free satoshi value conservation (`≤ 21,000,000 BTC`), verified
                                  change elision, BIP-322 / `SIGN_MESSAGE` isolation, and Swap exact-match locks.
    3. `Spec.SessionSecurity`   — Universal UI user-consent gating before secret-derived emission, read-only
                                  purity & atomic error rollback, MuSig2 single-use nonce anti-replay, and
                                  Silent Payment (BIP-352/375) explicit `SIGHASH_ALL` & non-NUMS input rules.

  All wire-level framing (BOLOS Merkleized APDUs, Vanadium CBOR, Base58Check, Bech32/Bech32m,
  BIP-379 Miniscript ASTs, BIP-143/341/342 sighash serialization, BIP-327 KeyAgg, BIP-374 DLEQ)
  resides in `InternalSpec/` and is machine-proved in `Proofs/UserSpecRefinement.lean` (together
  with `BitcoinLedger/`) to refine this top-level `Spec` with `0 sorryAx` and `0 Classical.choice`.
-/

import Spec.KeyPolicy
import Spec.TransactionSafety
import Spec.SessionSecurity

namespace Spec

/-- Semantic version of the Ledger Bitcoin target specification. -/
structure AppVersion where
  major : UInt8
  minor : UInt8
  patch : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- Pinned Ledger Bitcoin target specification version (`2.4.1`). -/
def ledgerBitcoinTargetVersion : AppVersion :=
  { major := 2, minor := 4, patch := 1 }

/-- Top-level end-to-end transaction signing contract combining all three orthogonal specification domains:
    A `SIGN_PSBT` execution on `platform` is user-spec-valid iff:
    1. **Key & Policy Domain (`Spec.KeyPolicy`)**: The wallet policy is well-formed, owns at least one
       device key, separates receive/change branches, and has valid Proof-of-Registration (or BOLOS default status),
    2. **Transaction Accounting Domain (`Spec.TransactionSafety`)**: Input/output satoshi sums are `≤ 21M BTC`
       without overflow, `inputs = externalRecipients + verifiedChange + fee` (unless BOLOS open sighash),
       and if Swap mode is active, `satisfiesSwapContract` holds,
    3. **Session, Consent, MuSig2 & Silent Payments Domain (`Spec.SessionSecurity`)**: Secret-derived outputs
       are gated by explicit UI user approval (or Swap exact match), Silent Payment outputs enforce explicit
       `SIGHASH_ALL` and eligible non-NUMS inputs, and session state transitions obey `respectsSessionAtomicity`. -/
def validEndToEndPsbtExecution
    (platform : Platform)
    (policy : PolicySummary)
    (hasPor validPorHmac porIsAllZeros : Bool)
    (allowOpenSighashUnderflow hasInternalInput utxosConsistent : Bool)
    (inputAmounts : List UInt64)
    (outputs : List ReviewedOutput)
    (reportedFee : Option UInt64)
    (swapContractOpt : Option SwapContract)
    (isBip322 hasExternalInputs : Bool)
    (hasSpOutputs outputsModifiable hasEligibleNonNumsInput hasSegwitV2OrHigher allInputsExplicitSighashAll : Bool)
    (swapAborted userApprovedOnScreen emitsSecretDerivedMaterial : Bool) : Bool :=
  let inSwapMode := swapContractOpt.isSome
  let validSwapMatch :=
    match swapContractOpt with
    | none => false
    | some lock => satisfiesSwapContract lock isBip322 hasExternalInputs outputs reportedFee
  canUseWalletPolicy platform inSwapMode policy hasPor validPorHmac porIsAllZeros &&
  validTransactionAccounting allowOpenSighashUnderflow hasInternalInput utxosConsistent
    inputAmounts outputs reportedFee &&
  (match swapContractOpt with | none => true | some _ => validSwapMatch) &&
  validSilentPaymentPsbtGate hasSpOutputs outputsModifiable hasEligibleNonNumsInput
    hasSegwitV2OrHigher allInputsExplicitSighashAll &&
  authorizedSecretEmission .signPsbtSigning inSwapMode swapAborted validSwapMatch
    userApprovedOnScreen emitsSecretDerivedMaterial

/-- **Master User-Facing Security Theorem**:
    Every `validEndToEndPsbtExecution` that emits secret-derived signing material (`emitsSecretDerivedMaterial = true`)
    under closed sighashes (`allowOpenSighashUnderflow = false`) simultaneously guarantees:
    1. Device internal-key ownership & receive/change non-collision (`0 < policy.nInternalKeys`),
    2. Overflow-free satoshi conservation (`exactSatoshiSum inputAmounts = externalRecipientSum outputs + verifiedChangeSum outputs + fee`),
    3. Explicit user UI approval OR an active, un-aborted Exchange `SwapContract` pinning the exact recipient, amount, and fee,
    4. Silent Payment explicit `SIGHASH_ALL` & eligible-input enforcement whenever `hasSpOutputs = true`. -/
theorem master_psbt_execution_security
    (platform : Platform)
    (policy : PolicySummary)
    (hasPor validPorHmac porIsAllZeros : Bool)
    (hasInternalInput utxosConsistent : Bool)
    (inputAmounts : List UInt64)
    (outputs : List ReviewedOutput)
    (reportedFee : Option UInt64)
    (swapContractOpt : Option SwapContract)
    (isBip322 hasExternalInputs : Bool)
    (hasSpOutputs outputsModifiable hasEligibleNonNumsInput hasSegwitV2OrHigher allInputsExplicitSighashAll : Bool)
    (swapAborted userApprovedOnScreen : Bool)
    (hExec : validEndToEndPsbtExecution platform policy hasPor validPorHmac porIsAllZeros
               false hasInternalInput utxosConsistent inputAmounts outputs reportedFee
               swapContractOpt isBip322 hasExternalInputs
               hasSpOutputs outputsModifiable hasEligibleNonNumsInput hasSegwitV2OrHigher allInputsExplicitSighashAll
               swapAborted userApprovedOnScreen true = true) :
    0 < policy.nInternalKeys ∧
    (∀ idxRx idxChg : UInt32,
      (policy.receiveBranchStep, idxRx) ≠ (policy.changeBranchStep, idxChg)) ∧
    (∃ fee : UInt64,
      reportedFee = some fee ∧
      exactSatoshiSum inputAmounts ≤ MAX_SATOSHIS ∧
      exactSatoshiSum inputAmounts =
        externalRecipientSum outputs + verifiedChangeSum outputs + fee.toNat) ∧
    (userApprovedOnScreen = true ∨
      ∃ lock : SwapContract,
        swapContractOpt = some lock ∧
        swapAborted = false ∧
        satisfiesSwapContract lock isBip322 hasExternalInputs outputs reportedFee = true) ∧
    (hasSpOutputs = true →
      outputsModifiable = false ∧
      hasEligibleNonNumsInput = true ∧
      hasSegwitV2OrHigher = false ∧
      allInputsExplicitSighashAll = true) := by
  unfold validEndToEndPsbtExecution at hExec
  dsimp only at hExec
  simp only [Bool.and_eq_true] at hExec
  rcases hExec with ⟨⟨⟨⟨hPol, hTx⟩, _hSwapGate⟩, hSp⟩, hConsent⟩
  have hOwn := fun rx chg =>
    authorized_policy_owns_key_and_separates_change platform swapContractOpt.isSome policy
      hasPor validPorHmac porIsAllZeros rx chg hPol
  have hNInt : 0 < policy.nInternalKeys := (hOwn 0 0).1
  have hNoColl : ∀ rx chg : UInt32, (policy.receiveBranchStep, rx) ≠ (policy.changeBranchStep, chg) :=
    fun rx chg => (hOwn rx chg).2
  have hCons := closed_tx_conserves_satoshis hasInternalInput utxosConsistent inputAmounts outputs reportedFee hTx
  have hUiOrSwap :
      userApprovedOnScreen = true ∨
        ∃ lock : SwapContract,
          swapContractOpt = some lock ∧
          swapAborted = false ∧
          satisfiesSwapContract lock isBip322 hasExternalInputs outputs reportedFee = true := by
    cases userApprovedOnScreen with
    | true => exact Or.inl rfl
    | false =>
      have ⟨_, hLockSome, hNotAborted, hMatch⟩ :=
        secret_emission_requires_consent_or_valid_swap .signPsbtSigning swapContractOpt.isSome swapAborted _ hConsent
      cases swapContractOpt with
      | none => simp at hLockSome
      | some lock =>
        exact Or.inr ⟨lock, rfl, hNotAborted, hMatch⟩
  refine ⟨hNInt, hNoColl, hCons, hUiOrSwap, ?_⟩
  intro hHasSp
  subst hHasSp
  exact silent_payment_enforces_sighash_all_and_eligible_input
    outputsModifiable hasEligibleNonNumsInput hasSegwitV2OrHigher allInputsExplicitSighashAll hSp

end Spec

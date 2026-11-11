/-
  Spec/SessionSecurity.lean — Domain 3: Session Atomicity, User-Consent Gating, MuSig2 Anti-Replay & Silent Payments

  Self-contained, human-auditable specification of stateful session security across all Ledger Bitcoin
  commands (`GET_VERSION`, `GET_MASTER_FINGERPRINT`, `GET_EXTENDED_PUBKEY`, `REGISTER_WALLET`,
  `GET_WALLET_ADDRESS`, `SIGN_MESSAGE`, `EXPORT_SP_SCAN_KEY`, `SIGN_PSBT` including MuSig2 & Silent Payments):
  1. **Universal Secret-Material User-Consent Gate**:
     - No secret-derived cryptographic material (ECDSA/Schnorr signature, BIP-137 message signature,
       MuSig2 partial signature, Silent Payment ECDH share, or BIP-392 `spscan` private scan key) is
       ever emitted unless the user explicitly approved the operation on the Secure Screen OR an active
       `SwapLock` matched every transaction parameter.
  2. **Read-Only Purity & Atomic Error Rollback**:
     - Read-only queries (`GET_VERSION`, `GET_MASTER_FINGERPRINT`, `GET_EXTENDED_PUBKEY`, `GET_WALLET_ADDRESS`)
       never mutate persistent accounts, resident keys, swap locks, or MuSig2 nonce sessions,
     - Any failed command (`Except.error`) leaves registered accounts, swap lock, and resident keys untouched,
       and latches `swapAborted = true` if Swap signing fails (`finalize_exchange_sign_transaction(false)`).
  3. **MuSig2 Single-Use Nonce Linearity (Anti-Replay)**:
     - Every MuSig2 Round-1 session draws a fresh 32-byte `randRoot`; Round-2 partial signing atomically
       deletes the session slot and permanently marks `randRoot` consumed BEFORE emitting any partial signature,
       preventing catastrophic Schnorr secret-key extraction under two-message nonce reuse.
  4. **Silent Payment (BIP-352 / BIP-374 / BIP-375) Input & Sighash Integrity**:
     - Any PSBT containing Silent Payment outputs requires `txModifiable` output flags cleared (`0`), at least
       one eligible input (`P2PKH`, `P2SH-P2WPKH`, `P2WPKH`, or non-NUMS `P2TR`), SegWit version `≤ 1`, and
       explicit `SIGHASH_ALL (0x01)` on every input (rejecting implicit Taproot `SIGHASH_DEFAULT = 0x00`).
-/

namespace Spec

/-- High-level classification of every top-level command supported by the Ledger Bitcoin app. -/
inductive CommandKind where
  | readOnlyQuery
  | registerPolicyOrIdentity
  | exportSilentPaymentScanKey
  | signMessage
  | signPsbtRound1Only (emitsSpShares : Bool)
  | signPsbtSigning
  deriving Repr, DecidableEq

/-- Whether a command is purely observational (`GET_VERSION`, `GET_MASTER_FINGERPRINT`, `GET_EXTENDED_PUBKEY`, `GET_WALLET_ADDRESS`). -/
def CommandKind.isReadOnly : CommandKind → Bool
  | .readOnlyQuery => true
  | _ => false

/-- Abstract persistent security state of the hardware wallet session. -/
structure SessionSecurityState where
  registeredAccountIds : List ByteArray
  residentTreeActive : Bool
  swapLockActive : Bool
  swapAborted : Bool
  activeMusigRandRoots : List ByteArray
  consumedMusigRandRoots : List ByteArray
  deriving DecidableEq

/-- Pure recursive `ByteArray` list membership (`0 Classical.choice`). -/
def memBytes (target : ByteArray) : List ByteArray → Bool
  | [] => false
  | x :: xs => decide (target = x) || memBytes target xs

/-- Remove the first occurrence of `target` from a `ByteArray` list. -/
def eraseBytes (target : ByteArray) : List ByteArray → List ByteArray
  | [] => []
  | x :: xs => if decide (target = x) then xs else x :: eraseBytes target xs

/-- Secret-material emission authorization contract:
    Whenever `emitsSecretDerivedMaterial = true` (any signature, MuSig2 partial sig, SP ECDH share,
    or `spscan` private scan key), either:
    - `userApprovedOnScreen = true`, OR
    - `cmd = .signPsbtSigning`, `swapLockActive = true`, `!swapAborted`, and `validSwapMatch = true`. -/
def authorizedSecretEmission
    (cmd : CommandKind)
    (swapLockActive swapAborted validSwapMatch userApprovedOnScreen : Bool)
    (emitsSecretDerivedMaterial : Bool) : Bool :=
  if !emitsSecretDerivedMaterial then
    true
  else if userApprovedOnScreen && !swapLockActive then
    true
  else
    match cmd with
    | .signPsbtSigning => swapLockActive && !swapAborted && validSwapMatch
    | _ => false

/-- Consume a MuSig2 Round-1 `randRoot` for Round-2 signing:
    Succeeds ONLY if `randRoot` is currently in `activeMusigRandRoots` AND NOT in `consumedMusigRandRoots`,
    returning the updated state with `randRoot` removed from `activeMusigRandRoots` and appended to
    `consumedMusigRandRoots`. -/
def consumeMusigNonce (s : SessionSecurityState) (randRoot : ByteArray) : Option SessionSecurityState :=
  if memBytes randRoot s.activeMusigRandRoots && !memBytes randRoot s.consumedMusigRandRoots then
    some {
      s with
      activeMusigRandRoots := eraseBytes randRoot s.activeMusigRandRoots
      consumedMusigRandRoots := randRoot :: s.consumedMusigRandRoots
    }
  else
    none

/-- BIP-375 Silent Payment PSBT security gate:
    When a transaction contains Silent Payment outputs (`hasSpOutputs = true`), signing is permitted ONLY if:
    - Outputs are non-modifiable (`outputsModifiable = false`),
    - At least one BIP-352-eligible non-NUMS input exists (`hasEligibleNonNumsInput = true`),
    - No input spends SegWit version `≥ 2` (`hasSegwitV2OrHigher = false`),
    - Every input explicitly commits to `SIGHASH_ALL = 0x01` (`allInputsExplicitSighashAll = true`). -/
def validSilentPaymentPsbtGate
    (hasSpOutputs outputsModifiable hasEligibleNonNumsInput hasSegwitV2OrHigher allInputsExplicitSighashAll : Bool) : Bool :=
  if !hasSpOutputs then
    true
  else
    !outputsModifiable &&
    hasEligibleNonNumsInput &&
    !hasSegwitV2OrHigher &&
    allInputsExplicitSighashAll

/-- Session transition invariant relating pre-state `s` and post-state `s'` on command outcome `ok : Bool`:
    - Successful read-only commands (`cmd.isReadOnly = true ∧ ok = true`) preserve the entire `SessionSecurityState` (`s' = s`),
    - Failed commands (`ok = false`, including read-only queries whose Swap PoR check aborts and latches `swapAborted`)
      preserve `registeredAccountIds`, `swapLockActive`, and `residentTreeActive`, and monotonically preserve
      all `consumedMusigRandRoots`. -/
def respectsSessionAtomicity (cmd : CommandKind) (ok : Bool) (s s' : SessionSecurityState) : Prop :=
  (cmd.isReadOnly = true → ok = true → s' = s) ∧
  (ok = false →
    s'.registeredAccountIds = s.registeredAccountIds ∧
    s'.swapLockActive = s.swapLockActive ∧
    s'.residentTreeActive = s.residentTreeActive ∧
    (∀ rr, memBytes rr s.consumedMusigRandRoots = true → memBytes rr s'.consumedMusigRandRoots = true))

/-- **Theorem 3.1 (No Unapproved Secret-Derived Signature or Key Export)**:
    If the user rejects all on-device prompts (`userApprovedOnScreen = false`), no command can ever
    emit secret-derived cryptographic material unless it is a `.signPsbtSigning` command executing under
    an active, non-aborted `SwapLock` whose exact swap parameters matched (`validSwapMatch = true`). -/
theorem secret_emission_requires_consent_or_valid_swap
    (cmd : CommandKind)
    (swapLockActive swapAborted validSwapMatch : Bool)
    (hAuth : authorizedSecretEmission cmd swapLockActive swapAborted validSwapMatch false true = true) :
    cmd = .signPsbtSigning ∧ swapLockActive = true ∧ swapAborted = false ∧ validSwapMatch = true := by
  unfold authorizedSecretEmission at hAuth
  cases cmd <;> simp at hAuth
  rcases hAuth with ⟨⟨hLock, hNotAborted⟩, hMatch⟩
  exact ⟨rfl, hLock, hNotAborted, hMatch⟩

/-- **Theorem 3.2 (MuSig2 Nonce Single-Use Anti-Replay)**:
    Once `consumeMusigNonce` consumes `randRoot` (`s → s₁`), any second attempt to sign with the same
    `randRoot` (`consumeMusigNonce s₁ randRoot`) is unconditionally rejected (`none`), preventing
    catastrophic BIP-327 two-signature secret-key recovery. -/
theorem musig_nonce_never_reused
    (s s₁ : SessionSecurityState) (randRoot : ByteArray)
    (hFirst : consumeMusigNonce s randRoot = some s₁) :
    consumeMusigNonce s₁ randRoot = none := by
  unfold consumeMusigNonce at hFirst ⊢
  by_cases hCond : (memBytes randRoot s.activeMusigRandRoots && !memBytes randRoot s.consumedMusigRandRoots) = true
  · simp only [hCond, ↓reduceIte, Option.some.injEq] at hFirst
    subst hFirst
    have hMem : memBytes randRoot (randRoot :: s.consumedMusigRandRoots) = true := by
      simp [memBytes]
    simp [hMem]
  · simp [hCond] at hFirst

/-- **Theorem 3.3 (Silent Payment PSBTs Reject Implicit Taproot `SIGHASH_DEFAULT` & NUMS-Only Inputs)**:
    Any transaction with Silent Payment outputs (`hasSpOutputs = true`) is rejected unless every input
    carries explicit `SIGHASH_ALL (0x01)` and at least one eligible non-NUMS input is present. -/
theorem silent_payment_enforces_sighash_all_and_eligible_input
    (outputsModifiable hasEligibleNonNumsInput hasSegwitV2OrHigher allInputsExplicitSighashAll : Bool)
    (hOk : validSilentPaymentPsbtGate true outputsModifiable hasEligibleNonNumsInput
             hasSegwitV2OrHigher allInputsExplicitSighashAll = true) :
    outputsModifiable = false ∧
    hasEligibleNonNumsInput = true ∧
    hasSegwitV2OrHigher = false ∧
    allInputsExplicitSighashAll = true := by
  unfold validSilentPaymentPsbtGate at hOk
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hOk
  rcases hOk with ⟨⟨⟨hMod, hElig⟩, hV2⟩, hSig⟩
  exact ⟨hMod, hElig, hV2, hSig⟩

end Spec

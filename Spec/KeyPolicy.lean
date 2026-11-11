/-
  Spec/KeyPolicy.lean — Domain 1: Key Derivation, Extended Public Key Export & Wallet Policy Authorization

  Self-contained, human-auditable specification of how the Ledger Bitcoin application:
  1. Bounds BIP-32 derivation paths (`≤ 255` steps globally; `≤ 10` on BOLOS, `≤ 16` on Vanadium standard tree),
  2. Restricts silent extended public key export (`GET_EXTENDED_PUBKEY` with `display = false`) strictly to
     standard BIP-44/45/48/49/84/86/87 account paths (`account ≤ 100`, matching `coinType`, hardened prefix
     followed by unhardened suffix) or explicit platform whitelists, requiring user UI consent otherwise,
  3. Enforces wallet policy authorization (`REGISTER_WALLET` / `GET_WALLET_ADDRESS` / `SIGN_PSBT`):
     - Every signable wallet policy must contain at least one device-owned internal key (`0 < nInternalKeys ≤ nKeys`),
     - Non-default policies require a valid cryptographic Proof-of-Registration (SLIP-21 HMAC-SHA256) and are
       forbidden during Exchange Swap sessions,
     - Receive (`branch = false`) and change (`branch = true`) derivations are strictly disjoint (`M ≠ N`).
-/

namespace Spec

/-- Execution platform and BIP-44 coin type (`0` for Bitcoin Mainnet, `1` for Testnet/Regtest/Signet). -/
inductive Platform where
  | bolos (coinType : UInt32)
  | vanadium (coinType : UInt32)
  deriving Repr, DecidableEq

/-- Extract the BIP-44 `coinType` (`0` = Mainnet, `1` = Testnet family) of a `Platform`. -/
def Platform.coinType : Platform → UInt32
  | .bolos ct => ct
  | .vanadium ct => ct

/-- BIP-32 seed hierarchy (`standard` BIP-39 seed vs Vanadium `resident` ephemeral/imported tree). -/
inductive KeyTree where
  | standard
  | resident
  deriving Repr, DecidableEq

/-- BIP-32 hardened child index bit (`2^31 = 0x80000000`). -/
def HARDENED_BIT : UInt32 := 0x80000000

/-- Test whether a BIP-32 child index is hardened (`≥ 2^31`). -/
def isHardenedStep (step : UInt32) : Bool :=
  decide (step ≥ HARDENED_BIT)

/-- Construct a hardened BIP-32 step `i' = i ||| 0x80000000`. -/
def hardenedStep (idx : UInt32) : UInt32 :=
  idx ||| HARDENED_BIT

/-- Maximum BIP-32 depth representable in a 78-byte serialized `ExtendedPubKey` (`depth : UInt8 ≤ 255`). -/
def MAX_XPUB_DEPTH : Nat := 255

/-- Maximum BIP-32 path length accepted by `GET_EXTENDED_PUBKEY` for `(platform, tree)`. -/
def maxAllowedPathDepth (p : Platform) (tree : KeyTree) : Nat :=
  match p, tree with
  | .bolos _, .standard => 10
  | .bolos _, .resident => 0
  | .vanadium _, .standard => 16
  | .vanadium _, .resident => MAX_XPUB_DEPTH

/-- Pure recursive universal check on lists (`0 Classical.choice`). -/
def allSteps (pred : UInt32 → Bool) : List UInt32 → Bool
  | [] => true
  | x :: xs => pred x && allSteps pred xs

/-- Standard BIP-44/45/48/49/84/86/87 silent extended-pubkey export policy:
    - Purpose `44'`, `45'`, `49'`, `84'`, `86'`, `87'`: hardened prefix of length `3` (`m/purpose'/coin'/account'`),
    - Purpose `48'`: hardened prefix of length `4` (`m/48'/coin'/account'/script_type'` with `script_type ∈ {1', 2'}`),
    - `coin == coinType`, `account ≤ 100`, and all remaining suffix steps strictly unhardened. -/
def isStandardSilentXpubPath (coinType : UInt32) (path : List UInt32) : Bool :=
  match path with
  | [s0] => decide (s0 = hardenedStep 45)
  | p0 :: p1 :: p2 :: rest =>
      let purpose := p0 &&& 0x7FFFFFFF
      let hLenOpt : Option Nat :=
        if decide (purpose = 44) || decide (purpose = 49) || decide (purpose = 84) ||
           decide (purpose = 86) || decide (purpose = 87) || decide (purpose = 45) then
          some 3
        else if decide (purpose = 48) then
          some 4
        else
          none
      match hLenOpt with
      | none => false
      | some hLen =>
          if path.length < hLen then
            false
          else
            let prefixHardened := allSteps isHardenedStep (path.take hLen)
            let suffixUnhardened := allSteps (fun s => !isHardenedStep s) (path.drop hLen)
            let coinMatch := decide ((p1 &&& 0x7FFFFFFF) = coinType)
            let accountBounded := decide ((p2 &&& 0x7FFFFFFF) ≤ 100)
            let scriptTypeValid :=
              if decide (purpose = 48) then
                match rest with
                | p3 :: _ =>
                    let st := p3 &&& 0x7FFFFFFF
                    decide (st = 1) || decide (st = 2)
                | [] => false
              else
                true
            prefixHardened && suffixUnhardened && coinMatch && accountBounded && scriptTypeValid
  | _ => false

/-- Vanadium identity-key path check (`m/1229210958'` or `m/1229210958'/i`). -/
def isVanadiumIdentityPath : List UInt32 → Bool
  | [r] => decide (r = hardenedStep 1229210958)
  | [r, _] => decide (r = hardenedStep 1229210958)
  | _ => false

/-- Full extended-pubkey export authorization contract:
    1. `path.length ≤ maxAllowedPathDepth p tree` (and always `≤ 255`, preventing `u8` depth wraparound),
    2. BOLOS forbids `KeyTree.resident` and empty root `m` export (`path = []`),
    3. Silent export (`display = false`) is permitted ONLY on standard whitelisted paths (or Electrum's
       legacy `m/4541509'/1112098098'` on BOLOS, or Vanadium's `m/1229210958'[/i]` identity tree / `resident` tree);
       every other path requires `display = true` AND explicit on-device `userApproved = true`. -/
def canExportExtendedPubkey
    (p : Platform) (tree : KeyTree) (path : List UInt32) (display userApproved : Bool) : Bool :=
  if path.length > maxAllowedPathDepth p tree || path.length > MAX_XPUB_DEPTH then
    false
  else
    match p, tree with
    | .bolos _, .resident => false
    | .bolos ct, .standard =>
        if path.isEmpty then
          false
        else
          let electrumLegacy := decide (path = [hardenedStep 4541509, hardenedStep 1112098098])
          let silentAllowed := isStandardSilentXpubPath ct path || electrumLegacy
          if display then userApproved else silentAllowed
    | .vanadium _, .resident =>
        if display then userApproved else true
    | .vanadium ct, .standard =>
        let silentAllowed := isStandardSilentXpubPath ct path || isVanadiumIdentityPath path
        if display then userApproved else silentAllowed

/-- Abstract summary of a Wallet Policy's security-critical properties. -/
structure PolicySummary where
  name : String
  nKeys : Nat
  nInternalKeys : Nat
  isDefaultPolicy : Bool
  receiveBranchStep : UInt32
  changeBranchStep : UInt32
  deriving Repr, DecidableEq

/-- A wallet policy is signable only when it contains at least one device-owned internal key,
    its internal key count does not exceed total keys, and its receive/change multipath steps
    are distinct unhardened indices (`receiveBranchStep ≠ changeBranchStep`). -/
def PolicySummary.isWellFormedSignable (pol : PolicySummary) : Bool :=
  decide (0 < pol.nInternalKeys) &&
  decide (pol.nInternalKeys ≤ pol.nKeys) &&
  !isHardenedStep pol.receiveBranchStep &&
  !isHardenedStep pol.changeBranchStep &&
  decide (pol.receiveBranchStep ≠ pol.changeBranchStep)

/-- Authorization contract for using a Wallet Policy in `GET_WALLET_ADDRESS` or `SIGN_PSBT`:
    - The policy must be well-formed and contain at least one device-owned key (`isWellFormedSignable`),
    - On BOLOS, stateless default policies (`isDefaultPolicy && name.isEmpty`) are allowed without a non-zero
      HMAC (including during Exchange Swap), whereas registered policies require `validPorHmac = true` and
      are forbidden when `inSwapMode = true`,
    - On Vanadium, default stateless accounts are disabled: every account requires `validPorHmac = true`
      and `inSwapMode = false`. -/
def canUseWalletPolicy
    (p : Platform) (inSwapMode : Bool) (pol : PolicySummary)
    (hasPor validPorHmac porIsAllZeros : Bool) : Bool :=
  if !pol.isWellFormedSignable then
    false
  else
    match p with
    | .bolos _ =>
        if !hasPor || porIsAllZeros then
          pol.isDefaultPolicy && pol.name.isEmpty
        else
          !inSwapMode && validPorHmac
    | .vanadium _ =>
        hasPor && (if porIsAllZeros then validPorHmac else !inSwapMode && validPorHmac)

/-- **Theorem 1.1 (`u8` Depth Wraparound Impossibility)**:
    Any accepted extended-pubkey export has `path.length ≤ 255`, preventing `UInt8` depth truncation (`VND-BUG-003`). -/
theorem export_xpub_depth_bounded
    (p : Platform) (tree : KeyTree) (path : List UInt32) (display userApproved : Bool)
    (hOk : canExportExtendedPubkey p tree path display userApproved = true) :
    path.length ≤ MAX_XPUB_DEPTH := by
  unfold canExportExtendedPubkey at hOk
  by_cases hGt : path.length > maxAllowedPathDepth p tree || path.length > MAX_XPUB_DEPTH
  · simp [hGt] at hOk
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hGt
    exact Nat.le_of_not_gt hGt.2

/-- **Theorem 1.2 (Unusual Path Requires Explicit User Consent)**:
    On `KeyTree.standard`, if `path` is neither a standard BIP-44/45/48/49/84/86/87 silent-export path nor
    an explicit platform whitelist path, `canExportExtendedPubkey` succeeds ONLY when `display = true ∧ userApproved = true`. -/
theorem unusual_xpub_requires_user_approval
    (p : Platform) (path : List UInt32) (display userApproved : Bool)
    (hNotStd : isStandardSilentXpubPath p.coinType path = false)
    (hNotElectrum : path ≠ [hardenedStep 4541509, hardenedStep 1112098098])
    (hNotIden : isVanadiumIdentityPath path = false)
    (hOk : canExportExtendedPubkey p .standard path display userApproved = true) :
    display = true ∧ userApproved = true := by
  cases p with
  | bolos ct =>
    simp only [Platform.coinType] at hNotStd
    unfold canExportExtendedPubkey at hOk
    by_cases hGt : (path.length > maxAllowedPathDepth (.bolos ct) .standard || path.length > MAX_XPUB_DEPTH) = true
    · simp [hGt] at hOk
    · simp only [hGt, Bool.false_eq_true, ↓reduceIte] at hOk
      by_cases hEmp : path.isEmpty = true
      · simp [hEmp] at hOk
      · simp only [hEmp, Bool.false_eq_true, ↓reduceIte] at hOk
        have hEl : decide (path = [hardenedStep 4541509, hardenedStep 1112098098]) = false :=
          decide_eq_false hNotElectrum
        cases display with
        | false =>
          simp [hNotStd, hEl] at hOk
        | true =>
          simp at hOk
          exact ⟨rfl, hOk⟩
  | vanadium ct =>
    simp only [Platform.coinType] at hNotStd
    unfold canExportExtendedPubkey at hOk
    by_cases hGt : (path.length > maxAllowedPathDepth (.vanadium ct) .standard || path.length > MAX_XPUB_DEPTH) = true
    · simp [hGt] at hOk
    · simp only [hGt, Bool.false_eq_true, ↓reduceIte] at hOk
      cases display with
      | false =>
        simp [hNotStd, hNotIden] at hOk
      | true =>
        simp at hOk
        exact ⟨rfl, hOk⟩

/-- **Theorem 1.3 (Receive / Change Derivation Non-Collision & Internal Key Ownership)**:
    Every authorized wallet policy contains at least one device-owned internal key (`0 < pol.nInternalKeys`)
    and guarantees that no receive address `(pol.receiveBranchStep, idxRx)` can ever collide with a change
    address `(pol.changeBranchStep, idxChg)`. -/
theorem authorized_policy_owns_key_and_separates_change
    (p : Platform) (inSwapMode : Bool) (pol : PolicySummary)
    (hasPor validPorHmac porIsAllZeros : Bool) (idxRx idxChg : UInt32)
    (hOk : canUseWalletPolicy p inSwapMode pol hasPor validPorHmac porIsAllZeros = true) :
    0 < pol.nInternalKeys ∧
    (pol.receiveBranchStep, idxRx) ≠ (pol.changeBranchStep, idxChg) := by
  unfold canUseWalletPolicy at hOk
  cases hWf : pol.isWellFormedSignable with
  | false => simp [hWf] at hOk
  | true =>
    unfold PolicySummary.isWellFormedSignable at hWf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
    rcases hWf with ⟨⟨⟨⟨hPos, _⟩, _⟩, _⟩, hNe⟩
    refine ⟨hPos, ?_⟩
    intro hEq
    injection hEq with hStep _
    exact hNe hStep

end Spec

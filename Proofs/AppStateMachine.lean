import InternalSpec
import BitcoinLedger.AppStateMachine
import Proofs.Musig2
import Proofs.SilentPayments

/-!
# `Proofs.AppStateMachine` — Refinement, Purity, Consent, Anti-Replay, Swap & Verified `SIGN_PSBT`

Connects every executable operation in `BitcoinLedger.AppStateMachine` to `InternalSpec.AppStateMachine`
and `InternalSpec.Unified`:
1. Exact refinement of BOLOS APDU (`CLA=0xE1`/`0xB0`/`0xF8`) and Vanadium CBOR wire classification,
   `SIGN_MESSAGE`, BIP-32 export policy, Vanadium `IDEN` identity signatures & cosigner auth,
   `SwapLock` validation, `stepAppCommand`, and multi-step `runAppTrace`.
2. Exact refinement of end-to-end verified `SIGN_PSBT` (`verifyPsbtMerkleBundle`,
   `buildVerifiedPsbtSignRequest`, `stepVerifiedPsbtSign`).
3. Security, purity, atomic error rollback, user-consent gates, MuSig2 Round-2 anti-replay,
   Swap termination latching, and end-to-end `SIGN_PSBT` & BIP-322 `verifyPsbtSignMessage`
   soundness theorems on `BitcoinLedger.AppStateMachine`.

All theorems satisfy `0 sorryAx`, `0 native_decide`, and `0 Classical.choice`.
-/

namespace Proofs.AppStateMachine

open InternalSpec.Musig2 (
  CompressedPubKey SchnorrSig PsbtSessionId RandRoot
  MusigSignTask MusigRound1Output MusigRound2TaskInput MusigRound2Output
  MusigError NonceAggPkMode MusigSessionStore
)
open InternalSpec.SilentPayments (
  SpError SpAddressHrp SpScanHrp Bech32mCodec
  SilentPaymentAccount SilentPaymentCoordinates PsbtSpTx
  SilentPaymentShareOut SilentPaymentOutputScriptOut
)
open InternalSpec.AppStateMachine (
  TargetProfile AppVersion BolosApduHeader BolosWireCommand VanadiumRequestTag
  CompactSigHeaderBase MessageDisplayForm KeyTree
  IdentitySignature RegisteredIdentityEntry
  WalletPolicySpec AccountSpec AddressCoordinates
  SwapMode SwapLock ExternalOutputView
  StandardInputSigRequest StandardInputSignature PsbtMusigPlan PsbtSignRequest
  AppCommand AppResponse AppError AppPersistentState
  UserPrompt UserApprovalOracle HardwareOracle AppTraceOutcome
)
open InternalSpec.Unified (
  PsbtMerkleOpeningBundle VerifiedPsbtSignError
)

/-! ## 1. Primitive, Wire, `SIGN_MESSAGE`, Identity & Swap Refinement Lemmas -/

theorem decide_ite_eq {α : Type} (P : Prop) [Decidable P] (a b : α) :
    (if decide P then a else b) = (if P then a else b) := by
  by_cases h : P <;> simp [h]

theorem sizedBytes32_beq_eq_decide (a b : InternalSpec.Musig2.Bytes32) :
    (a == b) = decide (a = b) := rfl

theorem sizedBytes32_bne_eq_decide_ne (a b : InternalSpec.Musig2.Bytes32) :
    (a != b) = decide (a ≠ b) := by
  show (!(a == b)) = decide (a ≠ b)
  rw [sizedBytes32_beq_eq_decide]
  by_cases h : a = b <;> simp [h]

theorem string_beq_eq_decide (a b : String) : (a == b) = decide (a = b) := by
  cases h : decide (a = b)
  · exact beq_eq_false_iff_ne.mpr (of_decide_eq_false h)
  · exact beq_iff_eq.mpr (of_decide_eq_true h)

theorem optString_beq_some_eq_decide (o : Option String) (s : String) :
    (o == some s) = decide (o = some s) := by
  cases o with
  | none => rfl
  | some x =>
    show (x == s) = decide (some x = some s)
    rw [string_beq_eq_decide]
    by_cases h : x = s <;> simp [h]

theorem keyTree_bne_standard_eq (t : KeyTree) :
    decide (t ≠ .standard) = (t != .standard) := by
  cases t <;> rfl

theorem profileCoinType_eq (p : TargetProfile) :
    BitcoinLedger.AppStateMachine.profileCoinType p = p.coinType := by
  cases p <;> rfl

theorem profileMaxPathSteps_eq (p : TargetProfile) :
    BitcoinLedger.AppStateMachine.profileMaxPathSteps p = p.maxPathSteps := by
  cases p <;> rfl

theorem profileMusigAggPkMode_eq (p : TargetProfile) :
    BitcoinLedger.AppStateMachine.profileMusigAggPkMode p = p.musigAggPkMode := by
  cases p <;> rfl

theorem profileSpScanHrp_eq (p : TargetProfile) :
    BitcoinLedger.AppStateMachine.profileSpScanHrp p = p.spScanHrp := by
  unfold BitcoinLedger.AppStateMachine.profileSpScanHrp TargetProfile.spScanHrp
  rw [profileCoinType_eq]

theorem emptyMusigStoreForProfile_eq (p : TargetProfile) :
    BitcoinLedger.AppStateMachine.emptyMusigStoreForProfile p =
      MusigSessionStore.emptyForProfile p := by
  cases p <;> rfl

theorem emptyStateForProfile_eq (p : TargetProfile) :
    BitcoinLedger.AppStateMachine.emptyStateForProfile p =
      AppPersistentState.emptyForProfile p := by
  unfold BitcoinLedger.AppStateMachine.emptyStateForProfile AppPersistentState.emptyForProfile
  rw [emptyMusigStoreForProfile_eq]

theorem appListAll_eq_listAll {α : Type} (p : α → Bool) :
    ∀ xs : List α, BitcoinLedger.AppStateMachine.appListAll p xs = InternalSpec.Musig2.listAll p xs
  | [] => rfl
  | x :: xs => by
    simp only [BitcoinLedger.AppStateMachine.appListAll, InternalSpec.Musig2.listAll,
      appListAll_eq_listAll p xs]

theorem appListAll_eq_List_all {α : Type} (p : α → Bool) :
    ∀ xs : List α, BitcoinLedger.AppStateMachine.appListAll p xs = xs.all p
  | [] => rfl
  | x :: xs => by
    simp only [BitcoinLedger.AppStateMachine.appListAll, List.all,
      appListAll_eq_List_all p xs]

theorem appListMem_eq_listMem {α : Type} [DecidableEq α] (x : α) :
    ∀ xs : List α, BitcoinLedger.AppStateMachine.appListMem x xs = InternalSpec.Musig2.listMem x xs
  | [] => rfl
  | y :: ys => by
    simp only [BitcoinLedger.AppStateMachine.appListMem, InternalSpec.Musig2.listMem,
      appListMem_eq_listMem x ys]

theorem appListAny_eq_List_any {α : Type} (p : α → Bool) :
    ∀ xs : List α, BitcoinLedger.AppStateMachine.appListAny p xs = xs.any p
  | [] => rfl
  | x :: xs => by
    simp only [BitcoinLedger.AppStateMachine.appListAny, List.any,
      appListAny_eq_List_any p xs]

theorem encodeVarint_eq (n : Nat) :
    BitcoinLedger.AppStateMachine.encodeVarint n = InternalSpec.AppStateMachine.encodeVarint n := by
  unfold BitcoinLedger.AppStateMachine.encodeVarint InternalSpec.AppStateMachine.encodeVarint
  rw [decide_ite_eq, decide_ite_eq, decide_ite_eq]
  rfl

theorem isPrintableAsciiMessage_eq (msg : ByteArray) :
    BitcoinLedger.AppStateMachine.isPrintableAsciiMessage msg =
      InternalSpec.AppStateMachine.isPrintableAsciiMessage msg := by
  unfold BitcoinLedger.AppStateMachine.isPrintableAsciiMessage
    InternalSpec.AppStateMachine.isPrintableAsciiMessage
  rw [appListAll_eq_listAll]
  rfl

theorem bitcoinSignedMessagePreimage_eq (msg : ByteArray) :
    BitcoinLedger.AppStateMachine.bitcoinSignedMessagePreimage msg =
      InternalSpec.AppStateMachine.bitcoinSignedMessagePreimage msg := by
  unfold BitcoinLedger.AppStateMachine.bitcoinSignedMessagePreimage
    InternalSpec.AppStateMachine.bitcoinSignedMessagePreimage
  rw [encodeVarint_eq]
  rfl

theorem bitcoinSignedMessageDigest_eq (sha256 : ByteArray → InternalSpec.Musig2.Bytes32) (msg : ByteArray) :
    BitcoinLedger.AppStateMachine.bitcoinSignedMessageDigest sha256 msg =
      InternalSpec.AppStateMachine.bitcoinSignedMessageDigest sha256 msg := by
  unfold BitcoinLedger.AppStateMachine.bitcoinSignedMessageDigest
    InternalSpec.AppStateMachine.bitcoinSignedMessageDigest
  dsimp only
  rw [bitcoinSignedMessagePreimage_eq]

theorem compactHeaderBaseByte_eq (h : CompactSigHeaderBase) :
    BitcoinLedger.AppStateMachine.compactHeaderBaseByte h = h.baseByte := by
  cases h <;> rfl

theorem formatCompactRecoverableSig_eq (headerBase : CompactSigHeaderBase) (recId : UInt8)
    (r s : InternalSpec.Musig2.Bytes32) :
    BitcoinLedger.AppStateMachine.formatCompactRecoverableSig headerBase recId r s =
      InternalSpec.AppStateMachine.formatCompactRecoverableSig headerBase recId r s := by
  unfold BitcoinLedger.AppStateMachine.formatCompactRecoverableSig
    InternalSpec.AppStateMachine.formatCompactRecoverableSig
  rw [decide_ite_eq, compactHeaderBaseByte_eq]
  rfl

theorem formatBolosSignMessageSig_eq (recId : UInt8) (r s : InternalSpec.Musig2.Bytes32) :
    BitcoinLedger.AppStateMachine.formatBolosSignMessageSig recId r s =
      InternalSpec.AppStateMachine.formatBolosSignMessageSig recId r s := by
  unfold BitcoinLedger.AppStateMachine.formatBolosSignMessageSig
    InternalSpec.AppStateMachine.formatBolosSignMessageSig
  rw [decide_ite_eq]
  rfl

theorem isPathSafeForPubkeyExport_eq (coinType : UInt32) (path : List UInt32) :
    BitcoinLedger.AppStateMachine.isPathSafeForPubkeyExport coinType path =
      InternalSpec.AppStateMachine.isPathSafeForPubkeyExport coinType path := by
  unfold BitcoinLedger.AppStateMachine.isPathSafeForPubkeyExport
    InternalSpec.AppStateMachine.isPathSafeForPubkeyExport
  cases path with
  | nil => rfl
  | cons p0 t1 =>
    cases t1 with
    | nil => rfl
    | cons p1 t2 =>
      cases t2 with
      | nil => rfl
      | cons p2 rest =>
        dsimp only
        have hPurp : ∀ n : Option Nat,
            (match n with
             | none => false
             | some hLen =>
               if decide ((p0 :: p1 :: p2 :: rest).length < hLen) then false
               else
                 BitcoinLedger.AppStateMachine.appListAll
                   (fun step => decide (step ≥ BitcoinLedger.AppStateMachine.hardenedFlag))
                   ((p0 :: p1 :: p2 :: rest).take hLen) &&
                 BitcoinLedger.AppStateMachine.appListAll
                   (fun step => decide (step < BitcoinLedger.AppStateMachine.hardenedFlag))
                   ((p0 :: p1 :: p2 :: rest).drop hLen) &&
                 decide ((p1 &&& 0x7FFFFFFF) = coinType) &&
                 decide ((p2 &&& 0x7FFFFFFF) ≤ BitcoinLedger.AppStateMachine.maxBip44AccountRecommended) &&
                 (if decide ((p0 &&& 0x7FFFFFFF) = 48) then
                    match rest with
                    | p3 :: _ => decide ((p3 &&& 0x7FFFFFFF) = 1) || decide ((p3 &&& 0x7FFFFFFF) = 2)
                    | [] => false
                  else true)) =
            (match n with
             | none => false
             | some hLen =>
               if (p0 :: p1 :: p2 :: rest).length < hLen then false
               else
                 InternalSpec.Musig2.listAll (fun step => step >= InternalSpec.AppStateMachine.hardenedFlag)
                   ((p0 :: p1 :: p2 :: rest).take hLen) &&
                 InternalSpec.Musig2.listAll (fun step => step < InternalSpec.AppStateMachine.hardenedFlag)
                   ((p0 :: p1 :: p2 :: rest).drop hLen) &&
                 decide ((p1 &&& 0x7FFFFFFF) = coinType) &&
                 ((p2 &&& 0x7FFFFFFF) ≤ InternalSpec.AppStateMachine.maxBip44AccountRecommended) &&
                 (if decide ((p0 &&& 0x7FFFFFFF) = 48) then
                    match rest with
                    | p3 :: _ => decide ((p3 &&& 0x7FFFFFFF) = 1) || decide ((p3 &&& 0x7FFFFFFF) = 2)
                    | [] => false
                  else true)) := by
          intro n
          cases n with
          | none => rfl
          | some hLen =>
            dsimp only
            rw [decide_ite_eq, appListAll_eq_listAll, appListAll_eq_listAll]
            rfl
        exact hPurp _

theorem classifyIdentityPath_eq (path : List UInt32) :
    BitcoinLedger.AppStateMachine.classifyIdentityPath path =
      InternalSpec.AppStateMachine.classifyIdentityPath path := by
  cases path with
  | nil => rfl
  | cons a t =>
    cases t with
    | nil => rfl
    | cons b t2 =>
      cases t2 <;> rfl

theorem isValidCompressedSec1Prefix_eq (pk : CompressedPubKey) :
    BitcoinLedger.AppStateMachine.isValidCompressedSec1Prefix pk =
      InternalSpec.AppStateMachine.isValidCompressedSec1Prefix pk := rfl

theorem buildIdentityMessage_eq (msgType object : ByteArray) :
    BitcoinLedger.AppStateMachine.buildIdentityMessage msgType object =
      InternalSpec.AppStateMachine.buildIdentityMessage msgType object := rfl

theorem computeIdentityRegistrationId_eq (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (name : String) (pubkey : CompressedPubKey) :
    BitcoinLedger.AppStateMachine.computeIdentityRegistrationId sha256 name pubkey =
      InternalSpec.AppStateMachine.computeIdentityRegistrationId sha256 name pubkey := by
  unfold BitcoinLedger.AppStateMachine.computeIdentityRegistrationId
    InternalSpec.AppStateMachine.computeIdentityRegistrationId
  dsimp only
  rw [Proofs.SilentPayments.nat_beq_eq_decide]
  rfl

theorem validCrossChainOpReturn_eq (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (out : ExternalOutputView) (expectedPayinHash : InternalSpec.Musig2.Bytes32) :
    BitcoinLedger.AppStateMachine.validCrossChainOpReturn sha256 out expectedPayinHash =
      InternalSpec.AppStateMachine.validCrossChainOpReturn sha256 out expectedPayinHash := by
  unfold BitcoinLedger.AppStateMachine.validCrossChainOpReturn
    InternalSpec.AppStateMachine.validCrossChainOpReturn
  cases decide (out.amount ≠ 0) with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases out.script.data.toList with
    | nil => rfl
    | cons b0 t0 =>
      by_cases hb0 : b0 = 0x6A
      · subst hb0
        cases t0 with
        | nil => rfl
        | cons secondByte rest =>
          cases rest with
          | nil =>
            simp only [Proofs.Musig2.nat_bne_eq_decide_ne, sizedBytes32_beq_eq_decide]
          | cons lenByte payloadList =>
            simp only [Proofs.Musig2.nat_bne_eq_decide_ne, sizedBytes32_beq_eq_decide]
      · simp [hb0]

theorem isDefaultPor_eq (porOpt : Option InternalSpec.Musig2.Bytes32) :
    BitcoinLedger.AppStateMachine.isDefaultPor porOpt =
      InternalSpec.AppStateMachine.isDefaultPor porOpt := by
  cases porOpt with
  | none => rfl
  | some por => exact Proofs.Musig2.isAllZeros_eq por

theorem validSwapPsbt_eq {Affine : Type} (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (lock : SwapLock) (req : PsbtSignRequest Affine) :
    BitcoinLedger.AppStateMachine.validSwapPsbt sha256 lock req =
      InternalSpec.AppStateMachine.validSwapPsbt sha256 lock req := by
  unfold BitcoinLedger.AppStateMachine.validSwapPsbt InternalSpec.AppStateMachine.validSwapPsbt
  cases req.account with
  | silentPayment _ _ _ => rfl
  | walletPolicy wp =>
    dsimp only
    rw [isDefaultPor_eq, decide_ite_eq (req.nExternalInputs > 0),
        decide_ite_eq (req.inputsTotalAmount < req.outputsTotalAmount),
        decide_ite_eq (req.outputsTotalAmount < req.changeOutputsTotalAmount)]
    cases lock.mode with
    | invalidMode => rfl
    | standard =>
      cases req.externalOutputs with
      | nil => rfl
      | cons d rest =>
        cases rest with
        | nil => dsimp only; rw [optString_beq_some_eq_decide]
        | cons _ _ => rfl
    | crossChain expectedPayinHash =>
      cases req.externalOutputs with
      | nil => rfl
      | cons o1 r1 =>
        cases r1 with
        | nil => rfl
        | cons o2 r2 =>
          cases r2 with
          | nil => dsimp only; rw [validCrossChainOpReturn_eq, optString_beq_some_eq_decide]
          | cons _ _ => rfl

/-! ## 2. Wire Classification, Auth, `stepAppCommand`, Trace & End-to-End `SIGN_PSBT` Refinement -/

theorem classifyBolosApdu_refines_spec (inSwapMode : Bool) (hdr : BolosApduHeader) :
    BitcoinLedger.AppStateMachine.classifyBolosApdu inSwapMode hdr =
      InternalSpec.AppStateMachine.classifyBolosApdu inSwapMode hdr := by
  unfold BitcoinLedger.AppStateMachine.classifyBolosApdu InternalSpec.AppStateMachine.classifyBolosApdu
  have hVer : BitcoinLedger.AppStateMachine.bolosCurrentProtocolVersion =
      InternalSpec.AppStateMachine.bolosCurrentProtocolVersion := rfl
  rw [hVer]
  cases inSwapMode with
  | true =>
    simp only [↓reduceIte]
    rw [decide_ite_eq (hdr.p2 > InternalSpec.AppStateMachine.bolosCurrentProtocolVersion)]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [decide_ite_eq (hdr.p2 > InternalSpec.AppStateMachine.bolosCurrentProtocolVersion)]
    rfl

theorem decodeVanadiumRequestTag_refines_spec (tag : Nat) :
    BitcoinLedger.AppStateMachine.decodeVanadiumRequestTag tag =
      InternalSpec.AppStateMachine.decodeVanadiumRequestTag tag := by
  unfold BitcoinLedger.AppStateMachine.decodeVanadiumRequestTag
    InternalSpec.AppStateMachine.decodeVanadiumRequestTag
  rfl

theorem isCommandReadOnly_eq {Affine : Type} (cmd : AppCommand Affine) :
    BitcoinLedger.AppStateMachine.isCommandReadOnly cmd = cmd.isReadOnly := by
  cases cmd <;> rfl

theorem isAllowedInSwap_eq {Affine : Type} (cmd : AppCommand Affine) :
    BitcoinLedger.AppStateMachine.isAllowedInSwap cmd =
      InternalSpec.AppStateMachine.isAllowedInSwap cmd := by
  cases cmd <;> rfl

theorem checkSelfPubnonce_eq {Affine : Type} (hw : HardwareOracle Affine) (profile : TargetProfile) :
    BitcoinLedger.AppStateMachine.checkSelfPubnonce hw profile = hw.checkSelfPubnonce profile := by
  cases profile <;> rfl

theorem validateAccountAuth_refines_spec {Affine : Type}
    (profile : TargetProfile) (hw : HardwareOracle Affine)
    (inSwapMode : Bool) (account : AccountSpec Affine) (porOpt : Option InternalSpec.Musig2.Bytes32) :
    BitcoinLedger.AppStateMachine.validateAccountAuth profile hw inSwapMode account porOpt =
      InternalSpec.AppStateMachine.validateAccountAuth profile hw inSwapMode account porOpt := by
  unfold BitcoinLedger.AppStateMachine.validateAccountAuth InternalSpec.AppStateMachine.validateAccountAuth
  cases account with
  | walletPolicy wp =>
    cases porOpt with
    | none => rfl
    | some por =>
      dsimp only
      rw [Proofs.Musig2.isAllZeros_eq, sizedBytes32_beq_eq_decide]
      rfl
  | silentPayment _ spAcc accId =>
    cases profile with
    | bolos _ => rfl
    | vanadium _ =>
      cases inSwapMode with
      | true => rfl
      | false =>
        cases porOpt with
        | none => rfl
        | some por =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hH : BitcoinLedger.AppStateMachine.hardenedFlag =
              InternalSpec.AppStateMachine.hardenedFlag := rfl
          rw [hH, sizedBytes32_beq_eq_decide]

theorem maybeSignIdentityObject_refines_spec {Affine : Type}
    (profile : TargetProfile) (hw : HardwareOracle Affine)
    (identityIndex : Option UInt32) (msgType object : ByteArray) :
    BitcoinLedger.AppStateMachine.maybeSignIdentityObject profile hw identityIndex msgType object =
      InternalSpec.AppStateMachine.maybeSignIdentityObject profile hw identityIndex msgType object := by
  unfold BitcoinLedger.AppStateMachine.maybeSignIdentityObject
    InternalSpec.AppStateMachine.maybeSignIdentityObject
  cases identityIndex with
  | none => rfl
  | some idx =>
    cases profile with
    | bolos _ => rfl
    | vanadium _ =>
      dsimp only
      have hH : BitcoinLedger.AppStateMachine.hardenedFlag =
          InternalSpec.AppStateMachine.hardenedFlag := rfl
      rw [hH, decide_ite_eq (idx ≥ InternalSpec.AppStateMachine.hardenedFlag), buildIdentityMessage_eq]
      cases decide (idx ≥ InternalSpec.AppStateMachine.hardenedFlag) with
      | true => rfl
      | false =>
        cases InternalSpec.AppStateMachine.buildIdentityMessage msgType object with
        | none => rfl
        | some msg =>
          cases hw.signWithIdentityKey idx msg <;> rfl

private theorem verifyIdentityEntriesLoop_err_iff_mapM {Affine : Type}
    (hw : HardwareOracle Affine)
    (f : RegisteredIdentityEntry → Except AppError CompressedPubKey)
    (hf : ∀ entry, f entry =
      if !BitcoinLedger.AppStateMachine.isValidCompressedSec1Prefix entry.pubkey then
        Except.error AppError.signatureFail
      else
        match BitcoinLedger.AppStateMachine.computeIdentityRegistrationId
                hw.musigCrypto.sha256 entry.name entry.pubkey with
        | none => Except.error AppError.signatureFail
        | some regId =>
          if decide (hw.computePorHmac regId ≠ entry.por) then
            Except.error AppError.signatureFail
          else
            Except.ok entry.pubkey)
    (entries : List RegisteredIdentityEntry) (acc : List CompressedPubKey) :
    (∀ e, BitcoinLedger.AppStateMachine.verifyIdentityEntriesLoop hw entries = .error e →
      List.mapM.loop f entries acc = .error e) ∧
    (BitcoinLedger.AppStateMachine.verifyIdentityEntriesLoop hw entries = .ok () →
      ∃ l, List.mapM.loop f entries acc = .ok l) := by
  induction entries generalizing acc with
  | nil =>
    constructor
    · intro _ h; cases h
    · intro _; exact ⟨acc.reverse, rfl⟩
  | cons entry rest ih =>
    simp only [BitcoinLedger.AppStateMachine.verifyIdentityEntriesLoop, List.mapM.loop]
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [hf entry]
    cases (!BitcoinLedger.AppStateMachine.isValidCompressedSec1Prefix entry.pubkey) with
    | true =>
      simp only [↓reduceIte]
      constructor
      · intro _ h; injection h with he; subst he; rfl
      · intro h; cases h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases BitcoinLedger.AppStateMachine.computeIdentityRegistrationId
              hw.musigCrypto.sha256 entry.name entry.pubkey with
      | none =>
        dsimp only
        constructor
        · intro _ h; injection h with he; subst he; rfl
        · intro h; cases h
      | some regId =>
        dsimp only
        cases decide (hw.computePorHmac regId ≠ entry.por) with
        | true =>
          simp only [↓reduceIte]
          constructor
          · intro _ h; injection h with he; subst he; rfl
          · intro h; cases h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih (entry.pubkey :: acc)

private theorem verifyKeySigsLoop_eq_forIn {Affine : Type}
    (hw : HardwareOracle Affine) :
    ∀ pairs : List (ByteArray × Option IdentitySignature),
      BitcoinLedger.AppStateMachine.verifyKeySigsLoop hw pairs =
        (do
          for (keyPayload, sigOpt) in pairs do
            match sigOpt with
            | none => pure ()
            | some sig =>
              if !InternalSpec.AppStateMachine.isValidCompressedSec1Prefix sig.identityPubkey then
                Except.error AppError.signatureFail
              let msg ← match InternalSpec.AppStateMachine.buildIdentityMessage
                                InternalSpec.AppStateMachine.identityMsgTypeXpub keyPayload with
                | some m => Except.ok m
                | none => Except.error AppError.incorrectData
              if !hw.verifySchnorr sig.identityPubkey msg sig.signature then
                Except.error AppError.signatureFail)
  | [] => rfl
  | (keyPayload, sigOpt) :: rest => by
    have ih := verifyKeySigsLoop_eq_forIn hw rest
    dsimp only [ForIn'.forIn', ForIn.forIn, List.forIn'] at ih ⊢
    unfold List.forIn'.loop
    unfold BitcoinLedger.AppStateMachine.verifyKeySigsLoop
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
    cases sigOpt with
    | none =>
      dsimp only
      rw [Proofs.SilentPayments.forIn'_loop_ignore_mem _ ((keyPayload, none) :: rest) rest]
      exact ih
    | some sig =>
      dsimp only
      have hX : BitcoinLedger.AppStateMachine.identityMsgTypeXpub =
          InternalSpec.AppStateMachine.identityMsgTypeXpub := rfl
      rw [isValidCompressedSec1Prefix_eq, hX, buildIdentityMessage_eq]
      cases (!InternalSpec.AppStateMachine.isValidCompressedSec1Prefix sig.identityPubkey) with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        cases InternalSpec.AppStateMachine.buildIdentityMessage
                InternalSpec.AppStateMachine.identityMsgTypeXpub keyPayload with
        | none => rfl
        | some msg =>
          dsimp only
          cases (!hw.verifySchnorr sig.identityPubkey msg sig.signature) with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [Proofs.SilentPayments.forIn'_loop_ignore_mem _ ((keyPayload, some sig) :: rest) rest]
            exact ih

theorem verifyRegisteredIdentityAuth_refines_spec {Affine : Type}
    (hw : HardwareOracle Affine)
    (entries : List RegisteredIdentityEntry)
    (keyInfos : List ByteArray)
    (keySigs : List (Option IdentitySignature)) :
    BitcoinLedger.AppStateMachine.verifyRegisteredIdentityAuth hw entries keyInfos keySigs =
      InternalSpec.AppStateMachine.verifyRegisteredIdentityAuth hw entries keyInfos keySigs := by
  unfold BitcoinLedger.AppStateMachine.verifyRegisteredIdentityAuth
    InternalSpec.AppStateMachine.verifyRegisteredIdentityAuth
  have hTail : BitcoinLedger.AppStateMachine.verifyKeySigsLoop hw (keyInfos.zip keySigs) =
      (do
        for (keyPayload, sigOpt) in keyInfos.zip keySigs do
          match sigOpt with
          | none => pure ()
          | some sig =>
            if !InternalSpec.AppStateMachine.isValidCompressedSec1Prefix sig.identityPubkey then
              Except.error AppError.signatureFail
            let msg ← match InternalSpec.AppStateMachine.buildIdentityMessage
                              InternalSpec.AppStateMachine.identityMsgTypeXpub keyPayload with
              | some m => Except.ok m
              | none => Except.error AppError.incorrectData
            if !hw.verifySchnorr sig.identityPubkey msg sig.signature then
              Except.error AppError.signatureFail) :=
    verifyKeySigsLoop_eq_forIn hw (keyInfos.zip keySigs)
  dsimp only [List.mapM, Bind.bind, Except.bind, Pure.pure, Except.pure] at hTail ⊢
  have hfStep :
      ∀ entry : RegisteredIdentityEntry,
        (if !InternalSpec.AppStateMachine.isValidCompressedSec1Prefix entry.pubkey then
           Except.error AppError.signatureFail
         else
           match InternalSpec.AppStateMachine.computeIdentityRegistrationId
                   hw.musigCrypto.sha256 entry.name entry.pubkey with
           | some id =>
             if hw.computePorHmac id != entry.por then
               Except.error AppError.signatureFail
             else
               Except.ok entry.pubkey
           | none => Except.error AppError.signatureFail) =
        (if !BitcoinLedger.AppStateMachine.isValidCompressedSec1Prefix entry.pubkey then
           Except.error AppError.signatureFail
         else
           match BitcoinLedger.AppStateMachine.computeIdentityRegistrationId
                   hw.musigCrypto.sha256 entry.name entry.pubkey with
           | none => Except.error AppError.signatureFail
           | some regId =>
             if decide (hw.computePorHmac regId ≠ entry.por) then
               Except.error AppError.signatureFail
             else
               Except.ok entry.pubkey) := by
    intro entry
    rw [isValidCompressedSec1Prefix_eq, computeIdentityRegistrationId_eq]
    cases (!InternalSpec.AppStateMachine.isValidCompressedSec1Prefix entry.pubkey) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases InternalSpec.AppStateMachine.computeIdentityRegistrationId
              hw.musigCrypto.sha256 entry.name entry.pubkey with
      | none => rfl
      | some regId =>
        dsimp only
        rw [sizedBytes32_bne_eq_decide_ne]
  have hLoop := verifyIdentityEntriesLoop_err_iff_mapM hw _ hfStep entries []
  split
  · rename_i e hEnt
    apply Eq.symm
    split
    · rename_i e' hMap
      have hEqErr := hLoop.1 e hEnt
      injection hMap.symm.trans hEqErr with he
      subst he
      rfl
    · rename_i v hMap
      have hEqErr := hLoop.1 e hEnt
      cases hMap.symm.trans hEqErr
  · rename_i hEnt
    apply Eq.symm
    split
    · rename_i e' hMap
      obtain ⟨l, hEqOk⟩ := hLoop.2 hEnt
      cases hMap.symm.trans hEqOk
    · exact hTail.symm

theorem allowUnderfundedInputs_eq {Affine : Type} (profile : TargetProfile) (inSwap : Bool)
    (psbt : PsbtSignRequest Affine) :
    BitcoinLedger.AppStateMachine.allowUnderfundedInputs profile inSwap psbt =
      InternalSpec.AppStateMachine.allowUnderfundedInputs profile inSwap psbt := rfl

theorem round1NeedsApproval_eq (profile : TargetProfile) (spShares : List SilentPaymentShareOut) :
    BitcoinLedger.AppStateMachine.round1NeedsApproval profile spShares =
      InternalSpec.AppStateMachine.round1NeedsApproval profile spShares := rfl

theorem authorizePsbtStep_eq {Affine : Type} (sha256 : ByteArray → InternalSpec.Musig2.Bytes32)
    (swapLock : Option SwapLock) (ui : UserApprovalOracle Affine)
    (psbt : PsbtSignRequest Affine) :
    BitcoinLedger.AppStateMachine.authorizePsbtStep sha256 swapLock ui psbt =
      InternalSpec.AppStateMachine.authorizePsbtStep sha256 swapLock ui psbt := by
  unfold BitcoinLedger.AppStateMachine.authorizePsbtStep InternalSpec.AppStateMachine.authorizePsbtStep
  cases swapLock with
  | none => rfl
  | some lock => dsimp only; rw [validSwapPsbt_eq]

theorem computePsbtSpOutputs_eq {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine)
    (spTxOpt : Option (PsbtSpTx Affine)) :
    BitcoinLedger.AppStateMachine.computePsbtSpOutputs profile hw spTxOpt =
      InternalSpec.AppStateMachine.computePsbtSpOutputs profile hw spTxOpt := by
  unfold BitcoinLedger.AppStateMachine.computePsbtSpOutputs
    InternalSpec.AppStateMachine.computePsbtSpOutputs
  cases spTxOpt with
  | none => rfl
  | some spTx =>
    cases profile with
    | bolos _ => rfl
    | vanadium _ =>
      dsimp only
      rw [Proofs.SilentPayments.finalizePsbtSilentPayments_refines_spec]
      cases InternalSpec.SilentPayments.finalizePsbtSilentPayments hw.spCrypto spTx hw.freshDleqAuxRand <;> rfl

theorem abortSwapIfFailed_eq (e : AppError) (s : AppPersistentState) :
    BitcoinLedger.AppStateMachine.abortSwapIfFailed e s =
      InternalSpec.AppStateMachine.abortSwapIfFailed e s := rfl

private theorem signStandardInputs_loop_eq {Affine : Type} (hw : HardwareOracle Affine)
    (f : StandardInputSigRequest → Except AppError StandardInputSignature)
    (hf : ∀ req, f req =
      match hw.signPsbtInput req with
      | none => Except.error AppError.badState
      | some (sigBytes, pk) =>
        Except.ok {
          inputIndex := req.inputIndex
          signature := sigBytes
          pubkey := pk
          leafHash := req.leafHash
        }) :
    ∀ (tasks : List StandardInputSigRequest) (acc : List StandardInputSignature),
      List.mapM.loop f tasks acc =
      match BitcoinLedger.AppStateMachine.signStandardInputs hw tasks with
      | .error e => .error e
      | .ok tail => .ok (acc.reverse ++ tail)
  | [], acc => by simp [BitcoinLedger.AppStateMachine.signStandardInputs, List.mapM.loop]; rfl
  | req :: rest, acc => by
    simp only [BitcoinLedger.AppStateMachine.signStandardInputs, List.mapM.loop]
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [hf req]
    cases hw.signPsbtInput req with
    | none => rfl
    | some pair =>
      rcases pair with ⟨sigBytes, pk⟩
      dsimp only
      rw [signStandardInputs_loop_eq hw f hf rest _]
      cases BitcoinLedger.AppStateMachine.signStandardInputs hw rest with
      | error e => rfl
      | ok tail => simp [List.reverse_cons, List.append_assoc]

theorem signStandardInputs_eq {Affine : Type} (hw : HardwareOracle Affine)
    (tasks : List StandardInputSigRequest) :
    BitcoinLedger.AppStateMachine.signStandardInputs hw tasks =
      InternalSpec.AppStateMachine.signStandardInputs hw tasks := by
  unfold InternalSpec.AppStateMachine.signStandardInputs
  dsimp only [List.mapM]
  rw [signStandardInputs_loop_eq hw _ (by
    intro req
    cases hw.signPsbtInput req with
    | none => rfl
    | some pair => cases pair; rfl) tasks []]
  cases BitcoinLedger.AppStateMachine.signStandardInputs hw tasks <;> rfl

theorem stepAppCommand_refines_spec {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine)
    (s : AppPersistentState) :
    BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui cmd s =
      InternalSpec.AppStateMachine.stepAppCommand profile hw ui cmd s := by
  unfold BitcoinLedger.AppStateMachine.stepAppCommand InternalSpec.AppStateMachine.stepAppCommand
  rw [isAllowedInSwap_eq]
  cases (s.swapLock.isSome && s.swapAborted) with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases (s.swapLock.isSome && !InternalSpec.AppStateMachine.isAllowedInSwap cmd) with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases cmd with
      | unexpectedContinue => rfl
      | getVersion => cases profile <;> rfl
      | getMasterFingerprint tree =>
        cases profile <;> cases tree <;> rfl
      | getExtendedPubkey tree display path identityIndex =>
        dsimp only
        rw [profileMaxPathSteps_eq, decide_ite_eq (path.length > profile.maxPathSteps)]
        by_cases hLen : path.length > profile.maxPathSteps
        · simp [hLen]
        · simp only [hLen, ↓reduceIte]
          have hIdXpub : BitcoinLedger.AppStateMachine.identityMsgTypeXpub =
              InternalSpec.AppStateMachine.identityMsgTypeXpub := rfl
          have hVanMax : BitcoinLedger.AppStateMachine.vanadiumStandardMaxBip32PathSteps =
              InternalSpec.AppStateMachine.vanadiumStandardMaxBip32PathSteps := rfl
          cases profile with
          | bolos ct =>
            cases tree with
            | resident => rfl
            | standard =>
              dsimp only
              simp only [keyTree_bne_standard_eq, isPathSafeForPubkeyExport_eq,
                  hIdXpub, maybeSignIdentityObject_refines_spec]
              cases (identityIndex.isSome && KeyTree.standard != KeyTree.standard) with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                by_cases hSafe : (!InternalSpec.AppStateMachine.isPathSafeForPubkeyExport ct path && !display) = true
                · simp [hSafe]
                · simp only [hSafe]
                  cases hw.deriveExtendedPubkey .standard s.residentKeys path with
                  | none => rfl
                  | some p =>
                    rcases p with ⟨xpub, _pk⟩
                    dsimp only
                    cases (display && !ui.approve (.confirmExtendedPubkey .standard path xpub)) with
                    | true => rfl
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases InternalSpec.AppStateMachine.maybeSignIdentityObject (.bolos ct) hw identityIndex
                        InternalSpec.AppStateMachine.identityMsgTypeXpub xpub <;> rfl
          | vanadium ct =>
            cases tree with
            | resident =>
              dsimp only
              simp only [keyTree_bne_standard_eq, hIdXpub, maybeSignIdentityObject_refines_spec]
              cases (identityIndex.isSome && KeyTree.resident != KeyTree.standard) with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases hw.deriveExtendedPubkey .resident s.residentKeys path with
                | none => rfl
                | some p =>
                  rcases p with ⟨xpub, _pk⟩
                  dsimp only
                  cases (display && !ui.approve (.confirmExtendedPubkey .resident path xpub)) with
                  | true => rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    cases InternalSpec.AppStateMachine.maybeSignIdentityObject (.vanadium ct) hw identityIndex
                      InternalSpec.AppStateMachine.identityMsgTypeXpub xpub <;> rfl
            | standard =>
              dsimp only
              simp only [keyTree_bne_standard_eq, hVanMax, classifyIdentityPath_eq,
                  hIdXpub, maybeSignIdentityObject_refines_spec]
              cases (identityIndex.isSome && KeyTree.standard != KeyTree.standard) with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases decide (path.length > InternalSpec.AppStateMachine.vanadiumStandardMaxBip32PathSteps) with
                | true => rfl
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  cases hw.deriveExtendedPubkey .standard s.residentKeys path with
                  | none => rfl
                  | some p =>
                    rcases p with ⟨xpub, _pk⟩
                    dsimp only
                    have hPromptEq :
                        (match TargetProfile.vanadium ct, KeyTree.standard,
                               InternalSpec.AppStateMachine.classifyIdentityPath path with
                         | .vanadium _, .standard, some idKind =>
                           UserPrompt.confirmIdentityPubkey (Affine := Affine) idKind xpub
                         | _, _, _ => UserPrompt.confirmExtendedPubkey .standard path xpub) =
                        (match InternalSpec.AppStateMachine.classifyIdentityPath path with
                         | some idKind => UserPrompt.confirmIdentityPubkey idKind xpub
                         | none => UserPrompt.confirmExtendedPubkey .standard path xpub) := by
                      cases InternalSpec.AppStateMachine.classifyIdentityPath path <;> rfl
                    cases InternalSpec.AppStateMachine.classifyIdentityPath path <;> dsimp only <;> (
                      cases (display && !ui.approve _) with
                      | true => rfl
                      | false =>
                        simp only [Bool.false_eq_true, ↓reduceIte]
                        cases InternalSpec.AppStateMachine.maybeSignIdentityObject (.vanadium ct) hw identityIndex
                          InternalSpec.AppStateMachine.identityMsgTypeXpub xpub <;> rfl)
      | getAddress display account porOpt coordinates identityIndex =>
        dsimp only
        rw [validateAccountAuth_refines_spec]
        cases InternalSpec.AppStateMachine.validateAccountAuth profile hw s.swapLock.isSome account porOpt with
        | error _ => rfl
        | ok _ =>
          dsimp only
          cases account with
          | walletPolicy wp =>
            cases coordinates with
            | silentPayment _ => rfl
            | walletPolicy isChange addrIdx =>
              dsimp only
              have hH : BitcoinLedger.AppStateMachine.hardenedFlag =
                  InternalSpec.AppStateMachine.hardenedFlag := rfl
              have hMaxDef : BitcoinLedger.AppStateMachine.maxDefaultAddressIndex =
                  InternalSpec.AppStateMachine.maxDefaultAddressIndex := rfl
              have hIdOut : BitcoinLedger.AppStateMachine.identityMsgTypeOutput =
                  InternalSpec.AppStateMachine.identityMsgTypeOutput := rfl
              rw [hH, hMaxDef, hIdOut, decide_ite_eq (addrIdx ≥ InternalSpec.AppStateMachine.hardenedFlag),
                  isDefaultPor_eq]
              by_cases hHard : addrIdx ≥ InternalSpec.AppStateMachine.hardenedFlag
              · simp [hHard]
              · simp only [hHard, ↓reduceIte]
                by_cases hDef : InternalSpec.AppStateMachine.isDefaultPor porOpt = true
                · by_cases hCap : addrIdx > InternalSpec.AppStateMachine.maxDefaultAddressIndex
                  · simp [hDef, hCap]
                  · simp only [hDef, hCap, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
                    cases hw.deriveWalletPolicyOutput wp isChange addrIdx with
                    | none => rfl
                    | some pair =>
                      rcases pair with ⟨addr, scriptBytes⟩
                      dsimp only
                      rw [maybeSignIdentityObject_refines_spec]
                      cases InternalSpec.AppStateMachine.maybeSignIdentityObject profile hw identityIndex
                        InternalSpec.AppStateMachine.identityMsgTypeOutput scriptBytes <;> rfl
                · simp only [Bool.not_eq_true] at hDef
                  simp only [hDef, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
                  cases hw.deriveWalletPolicyOutput wp isChange addrIdx with
                  | none => rfl
                  | some pair =>
                    rcases pair with ⟨addr, scriptBytes⟩
                    dsimp only
                    rw [maybeSignIdentityObject_refines_spec]
                    cases InternalSpec.AppStateMachine.maybeSignIdentityObject profile hw identityIndex
                      InternalSpec.AppStateMachine.identityMsgTypeOutput scriptBytes <;> rfl
          | silentPayment name spAcc accId =>
            cases coordinates with
            | walletPolicy _ _ => rfl
            | silentPayment spCoords =>
              dsimp only
              cases identityIndex.isSome with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                rw [profileCoinType_eq, Proofs.SilentPayments.deriveAccountSpAddress_refines_spec]
                cases InternalSpec.SilentPayments.deriveAccountSpAddress hw.spCrypto hw.bech32m
                  (if decide (profile.coinType = 0) then .sp else .tsp) spAcc spCoords <;> rfl
      | registerAccount account regIdentities keySigs showCleartext =>
        dsimp only
        cases account with
        | walletPolicy wp =>
          dsimp only
          have hCond1 :
              (wp.name.isEmpty || decide (wp.name.utf8ByteSize > 64) ||
               decide (wp.nInternalKeys < 1) || !wp.isSignable) =
              (wp.name.isEmpty || (wp.name.utf8ByteSize > 64 : Bool) ||
               (wp.nInternalKeys < 1 : Bool) || !wp.isSignable) := rfl
          have hCond2 :
              (decide (wp.version = 1) && decide (wp.nInternalKeys ≠ 1)) =
              (decide (wp.version = 1) && (wp.nInternalKeys != 1)) := by
            rw [Proofs.Musig2.nat_bne_eq_decide_ne]
          rw [hCond1, hCond2]
          cases (wp.name.isEmpty || (wp.name.utf8ByteSize > 64 : Bool) ||
                 (wp.nInternalKeys < 1 : Bool) || !wp.isSignable) with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases (decide (wp.version = 1) && (wp.nInternalKeys != 1)) with
            | true => rfl
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases profile with
              | bolos _ =>
                dsimp only
                cases (!regIdentities.isEmpty || !keySigs.isEmpty) with
                | true => rfl
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [appListMem_eq_listMem]
              | vanadium _ =>
                dsimp only
                rw [verifyRegisteredIdentityAuth_refines_spec]
                cases InternalSpec.AppStateMachine.verifyRegisteredIdentityAuth
                        hw regIdentities wp.keysInfoPayloads keySigs with
                | error _ => rfl
                | ok _ =>
                  dsimp only
                  rw [appListMem_eq_listMem]
        | silentPayment name spAcc accId =>
          cases profile with
          | bolos _ => rfl
          | vanadium ct =>
            dsimp only
            have hSpCond :
                (name.isEmpty || decide (name.utf8ByteSize > 64) || !regIdentities.isEmpty || !keySigs.isEmpty) =
                (name.isEmpty || (name.utf8ByteSize > 64 : Bool) || !regIdentities.isEmpty || !keySigs.isEmpty) := rfl
            rw [hSpCond]
            cases (name.isEmpty || (name.utf8ByteSize > 64 : Bool) || !regIdentities.isEmpty || !keySigs.isEmpty) with
            | true => rfl
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases hw.deriveSpAccount spAcc.accountIndex with
              | error _ => rfl
              | ok derivedAcc =>
                dsimp only
                cases decide (derivedAcc ≠ spAcc) with
                | true => rfl
                | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [profileCoinType_eq, Proofs.SilentPayments.deriveAccountSpAddress_refines_spec]
                  cases InternalSpec.SilentPayments.deriveAccountSpAddress hw.spCrypto hw.bech32m
                    (if decide ((TargetProfile.vanadium ct).coinType = 0) then .sp else .tsp) spAcc (.code none) with
                  | error _ => rfl
                  | ok _ =>
                    dsimp only
                    rw [appListMem_eq_listMem]
      | registerIdentityKey name pubkey =>
        cases profile with
        | bolos _ => rfl
        | vanadium _ =>
          dsimp only
          rw [isValidCompressedSec1Prefix_eq, computeIdentityRegistrationId_eq]
          cases (!InternalSpec.AppStateMachine.isValidCompressedSec1Prefix pubkey) with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases InternalSpec.AppStateMachine.computeIdentityRegistrationId hw.musigCrypto.sha256 name pubkey <;> rfl
      | exportSpScanKey callerHrp accountIndex =>
        cases profile with
        | bolos _ => rfl
        | vanadium ct =>
          dsimp only
          rw [profileSpScanHrp_eq, Proofs.SilentPayments.exportSpScanKey_refines_spec]
          cases InternalSpec.SilentPayments.exportSpScanKey hw.spCrypto hw.bech32m (TargetProfile.vanadium ct).spScanHrp
            hw.deriveSpAccount accountIndex (ui.approve (.confirmExportSpScanKey accountIndex)) with
          | ok _ => rfl
          | error spErr => cases spErr <;> rfl
      | signMessage path message headerBase =>
        cases profile with
        | vanadium _ => rfl
        | bolos _ =>
          dsimp only
          have hBMax : BitcoinLedger.AppStateMachine.bolosMaxBip32PathSteps =
              InternalSpec.AppStateMachine.bolosMaxBip32PathSteps := rfl
          have hMMax : BitcoinLedger.AppStateMachine.maxSignMessageLength =
              InternalSpec.AppStateMachine.maxSignMessageLength := rfl
          rw [hBMax, hMMax,
              decide_ite_eq (path.length > InternalSpec.AppStateMachine.bolosMaxBip32PathSteps),
              decide_ite_eq (message.size ≥ InternalSpec.AppStateMachine.maxSignMessageLength),
              isPrintableAsciiMessage_eq, bitcoinSignedMessageDigest_eq]
          by_cases h1 : path.length > InternalSpec.AppStateMachine.bolosMaxBip32PathSteps
          · simp [h1]
          · simp only [h1, ↓reduceIte]
            by_cases h2 : message.size ≥ InternalSpec.AppStateMachine.maxSignMessageLength
            · simp [h2]
            · simp only [h2, ↓reduceIte]
              cases (!ui.approve (.confirmSignMessage path
                (if InternalSpec.AppStateMachine.isPrintableAsciiMessage message then .cleartextAscii message
                 else .sha256Digest (hw.musigCrypto.sha256 message)))) with
              | true => rfl
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte]
                cases hw.signRecoverableEcdsa path
                  (InternalSpec.AppStateMachine.bitcoinSignedMessageDigest hw.musigCrypto.sha256 message) with
                | none => rfl
                | some triple =>
                  rcases triple with ⟨recId, r, sScalar⟩
                  dsimp only
                  rw [formatBolosSignMessageSig_eq]
                  cases InternalSpec.AppStateMachine.formatBolosSignMessageSig recId r sScalar <;> rfl
      | signPsbt psbt =>
        dsimp only
        cases (s.swapLock.isSome && psbt.isBip322MessageSigning) with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [validateAccountAuth_refines_spec]
          cases InternalSpec.AppStateMachine.validateAccountAuth profile hw s.swapLock.isSome psbt.account psbt.por with
          | error _ => rfl
          | ok _ =>
            dsimp only
            rw [allowUnderfundedInputs_eq, computePsbtSpOutputs_eq]
            have hAmtCond :
                ((!InternalSpec.AppStateMachine.allowUnderfundedInputs profile s.swapLock.isSome psbt &&
                  decide (psbt.inputsTotalAmount < psbt.outputsTotalAmount)) ||
                 decide (psbt.outputsTotalAmount < psbt.changeOutputsTotalAmount)) =
                ((!InternalSpec.AppStateMachine.allowUnderfundedInputs profile s.swapLock.isSome psbt &&
                  (psbt.inputsTotalAmount < psbt.outputsTotalAmount : Bool)) ||
                 (psbt.outputsTotalAmount < psbt.changeOutputsTotalAmount : Bool)) := rfl
            rw [hAmtCond]
            cases ((!InternalSpec.AppStateMachine.allowUnderfundedInputs profile s.swapLock.isSome psbt &&
                    (psbt.inputsTotalAmount < psbt.outputsTotalAmount : Bool)) ||
                   (psbt.outputsTotalAmount < psbt.changeOutputsTotalAmount : Bool)) with
            | true => rfl
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              cases InternalSpec.AppStateMachine.computePsbtSpOutputs profile hw psbt.silentPaymentTx with
              | error _ => rfl
              | ok spPair =>
                rcases spPair with ⟨spShares, spScripts⟩
                dsimp only
                cases psbt.musigPlan with
                | round1Only sid r1Tasks =>
                  dsimp only
                  rw [round1NeedsApproval_eq, profileMusigAggPkMode_eq,
                      Proofs.Musig2.executeRound1Pass_refines_spec]
                  cases (!psbt.standardSignTasks.isEmpty || s.swapLock.isSome) with
                  | true => rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    cases (InternalSpec.AppStateMachine.round1NeedsApproval profile spShares &&
                           !ui.approve (.confirmSignPsbt psbt)) with
                    | true => rfl
                    | false =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      cases InternalSpec.Musig2.executeRound1Pass hw.musigCrypto profile.musigAggPkMode
                              s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                      | error p => cases p; rfl
                      | ok p => cases p; rfl
                | none =>
                  dsimp only
                  rw [authorizePsbtStep_eq, signStandardInputs_eq]
                  cases InternalSpec.AppStateMachine.authorizePsbtStep hw.musigCrypto.sha256 s.swapLock ui psbt with
                  | error _ => rfl
                  | ok isSwap =>
                    dsimp only
                    cases InternalSpec.AppStateMachine.signStandardInputs hw psbt.standardSignTasks <;> rfl
                | round1AndStandard sid r1Tasks =>
                  dsimp only
                  rw [authorizePsbtStep_eq, signStandardInputs_eq,
                      profileMusigAggPkMode_eq, Proofs.Musig2.executeRound1Pass_refines_spec]
                  cases InternalSpec.AppStateMachine.authorizePsbtStep hw.musigCrypto.sha256 s.swapLock ui psbt with
                  | error _ => rfl
                  | ok isSwap =>
                    dsimp only
                    cases InternalSpec.AppStateMachine.signStandardInputs hw psbt.standardSignTasks with
                    | error _ => rfl
                    | ok stdSigs =>
                      dsimp only
                      cases InternalSpec.Musig2.executeRound1Pass hw.musigCrypto profile.musigAggPkMode
                              s.musigSessions sid hw.freshMusigRandRoot r1Tasks with
                      | error p => cases p; rfl
                      | ok p => cases p; rfl
                | round2 sid r2Inputs =>
                  dsimp only
                  rw [Proofs.Musig2.lookupActive_refines_spec, authorizePsbtStep_eq,
                      profileMusigAggPkMode_eq, checkSelfPubnonce_eq,
                      Proofs.Musig2.executeRound2Pass_refines_spec, signStandardInputs_eq]
                  cases (s.musigSessions.lookupActive sid).isNone with
                  | true => rfl
                  | false =>
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    cases InternalSpec.AppStateMachine.authorizePsbtStep hw.musigCrypto.sha256 s.swapLock ui psbt with
                    | error _ => rfl
                    | ok isSwap =>
                      dsimp only
                      cases InternalSpec.Musig2.executeRound2Pass hw.musigCrypto profile.musigAggPkMode
                              s.musigSessions sid r2Inputs (hw.checkSelfPubnonce profile) with
                      | error p => cases p; rfl
                      | ok p =>
                        cases p
                        dsimp only
                        cases InternalSpec.AppStateMachine.signStandardInputs hw psbt.standardSignTasks <;> rfl

theorem extractPostState_eq
    (res : Except (AppError × AppPersistentState) (AppResponse × AppPersistentState)) :
    BitcoinLedger.AppStateMachine.extractPostState res =
      InternalSpec.AppStateMachine.extractPostState res := by
  cases res <;> rfl

theorem stepPostState_eq {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s : AppPersistentState) :
    BitcoinLedger.AppStateMachine.stepPostState profile hw ui cmd s =
      InternalSpec.AppStateMachine.stepPostState profile hw ui cmd s := by
  unfold BitcoinLedger.AppStateMachine.stepPostState InternalSpec.AppStateMachine.stepPostState
  rw [extractPostState_eq, stepAppCommand_refines_spec]

theorem runAppTrace_refines_spec {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine) :
    ∀ (cmds : List (AppCommand Affine)) (s : AppPersistentState),
      BitcoinLedger.AppStateMachine.runAppTrace profile hw ui cmds s =
        InternalSpec.AppStateMachine.runAppTrace profile hw ui cmds s
  | [], _ => rfl
  | cmd :: rest, s => by
    simp only [BitcoinLedger.AppStateMachine.runAppTrace, InternalSpec.AppStateMachine.runAppTrace,
      stepAppCommand_refines_spec]
    cases InternalSpec.AppStateMachine.stepAppCommand profile hw ui cmd s with
    | ok pair =>
      rcases pair with ⟨resp, s'⟩
      simp only [runAppTrace_refines_spec profile hw ui rest s']
    | error pair =>
      rcases pair with ⟨err, s'⟩
      simp only [runAppTrace_refines_spec profile hw ui rest s']

theorem stepUsedMusigRandRoot_eq {Affine : Type} [DecidableEq Affine]
    (cmd : AppCommand Affine)
    (res : Except (AppError × AppPersistentState) (AppResponse × AppPersistentState))
    (s : AppPersistentState) (rr : RandRoot) :
    BitcoinLedger.AppStateMachine.stepUsedMusigRandRoot cmd res s rr =
      InternalSpec.AppStateMachine.stepUsedMusigRandRoot cmd res s rr := by
  unfold BitcoinLedger.AppStateMachine.stepUsedMusigRandRoot
    InternalSpec.AppStateMachine.stepUsedMusigRandRoot
  cases cmd with
  | signPsbt psbt =>
    cases res with
    | error _ => rfl
    | ok pair =>
      rcases pair with ⟨resp, _⟩
      cases resp with
      | psbtSigned _ _ _ _ _ _ =>
        dsimp only
        cases psbt.musigPlan with
        | round2 sid _ =>
          dsimp only
          rw [Proofs.Musig2.lookupActive_refines_spec]
        | _ => rfl
      | _ => rfl
  | _ => rfl

theorem countMusigRound2StepsForRandRoot_eq {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (rr : RandRoot) :
    ∀ (cmds : List (AppCommand Affine)) (s : AppPersistentState),
      BitcoinLedger.AppStateMachine.countMusigRound2StepsForRandRoot profile hw ui rr cmds s =
        InternalSpec.AppStateMachine.countMusigRound2StepsForRandRoot profile hw ui rr cmds s
  | [], _ => rfl
  | cmd :: rest, s => by
    simp only [BitcoinLedger.AppStateMachine.countMusigRound2StepsForRandRoot,
      InternalSpec.AppStateMachine.countMusigRound2StepsForRandRoot,
      stepUsedMusigRandRoot_eq, stepAppCommand_refines_spec, stepPostState_eq,
      countMusigRound2StepsForRandRoot_eq profile hw ui rr rest]

theorem responseEmitsSecretDerivedMaterial_eq (resp : AppResponse) :
    BitcoinLedger.AppStateMachine.responseEmitsSecretDerivedMaterial resp =
      InternalSpec.AppStateMachine.responseEmitsSecretDerivedMaterial resp := by
  cases resp <;> rfl

theorem verifyPsbtMerkleBundle_refines_spec
    (sha256 : ByteArray → InternalSpec.Psbt.Bytes32) (nInputs nOutputs : Nat)
    (bundle : PsbtMerkleOpeningBundle) :
    BitcoinLedger.AppStateMachine.verifyPsbtMerkleBundle sha256 nInputs nOutputs bundle =
      InternalSpec.Unified.verifyPsbtMerkleBundle sha256 nInputs nOutputs bundle := by
  unfold BitcoinLedger.AppStateMachine.verifyPsbtMerkleBundle InternalSpec.Unified.verifyPsbtMerkleBundle
  rw [appListAll_eq_List_all, appListAll_eq_List_all]

theorem buildVerifiedPsbtSignRequest_refines_spec
    {Affine : Type}
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (allowNonDefaultSighash : Bool)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (swapLockOpt : Option SwapLock)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (silentPaymentTx : Option (PsbtSpTx Affine)) :
    BitcoinLedger.AppStateMachine.buildVerifiedPsbtSignRequest profile net hw dev policyOra hash160
      allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
      swapLockOpt standardSignTasks musigPlan silentPaymentTx =
    InternalSpec.Unified.buildVerifiedPsbtSignRequest profile net hw dev policyOra hash160
      allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
      swapLockOpt standardSignTasks musigPlan silentPaymentTx := by
  unfold BitcoinLedger.AppStateMachine.buildVerifiedPsbtSignRequest
    InternalSpec.Unified.buildVerifiedPsbtSignRequest
  have hPolProf : BitcoinLedger.AppStateMachine.policyProfileOfTarget profile =
      InternalSpec.Unified.policyProfileOfTarget profile := by
    cases profile <;> rfl
  have hPsbtCrypto : BitcoinLedger.AppStateMachine.mkPsbtCryptoOracles profile net hw hash160 =
      InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160 := by
    cases profile <;> rfl
  have hCfg : BitcoinLedger.AppStateMachine.signingConfigOfTarget profile allowNonDefaultSighash =
      InternalSpec.Unified.signingConfigOfTarget profile allowNonDefaultSighash := by
    cases profile <;> rfl
  have hPsbtPol : ∀ p, BitcoinLedger.AppStateMachine.toPsbtWalletPolicySpec p dev policyOra policy =
      InternalSpec.Unified.toPsbtWalletPolicySpec p dev policyOra policy := fun _ => rfl
  have hAppPol : ∀ p, BitcoinLedger.AppStateMachine.toAppWalletPolicySpec p dev
      descriptorTemplate walletId keysInfoPayloads policy =
      InternalSpec.Unified.toAppWalletPolicySpec p dev
        descriptorTemplate walletId keysInfoPayloads policy := fun _ => rfl
  have hSwapMap : ∀ l, BitcoinLedger.AppStateMachine.appSwapLockToPsbtSwapParams l =
      InternalSpec.Unified.appSwapLockToPsbtSwapParams l := by
    intro l; cases l.mode <;> rfl
  dsimp only
  rw [hPolProf]
  cases InternalSpec.WalletPolicy.checkPolicyWellFormed (InternalSpec.Unified.policyProfileOfTarget profile) policy with
  | error _ => rfl
  | ok _ =>
    dsimp only
    rw [hPsbtCrypto]
    have hMerkleBranch :
        ∀ k1 k2 : Except VerifiedPsbtSignError (InternalSpec.Psbt.ValidatedPsbt × PsbtSignRequest Affine),
          k1 = k2 →
          (if !(match merkleOpt with
                | none => true
                | some bundle =>
                  BitcoinLedger.AppStateMachine.verifyPsbtMerkleBundle
                    (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160).sha256
                    psbt.inputs.size psbt.outputs.size bundle) then
             Except.error VerifiedPsbtSignError.merkleVerificationFailed
           else k1) =
          (if !(match merkleOpt with
                | none => true
                | some bundle =>
                  InternalSpec.Unified.verifyPsbtMerkleBundle
                    (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160).sha256
                    psbt.inputs.size psbt.outputs.size bundle) then
             Except.error VerifiedPsbtSignError.merkleVerificationFailed
           else k2) := by
      intro k1 k2 hk
      rw [hk]
      cases merkleOpt with
      | none => rfl
      | some b =>
        simp only [verifyPsbtMerkleBundle_refines_spec]
    apply hMerkleBranch
    cases swapLockOpt with
    | none =>
      dsimp only
      rw [hCfg, hPsbtPol]
      cases InternalSpec.Psbt.authorizePsbtSigning
        (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160)
        (InternalSpec.Unified.signingConfigOfTarget profile allowNonDefaultSighash)
        (InternalSpec.Unified.toPsbtWalletPolicySpec (InternalSpec.Unified.policyProfileOfTarget profile) dev policyOra policy)
        psbt none with
      | error _ => rfl
      | ok validated =>
        dsimp only
        rw [hAppPol, appListAny_eq_List_any, appListAny_eq_List_any]
    | some lock =>
      dsimp only
      rw [hSwapMap]
      cases InternalSpec.Unified.appSwapLockToPsbtSwapParams lock with
      | none => rfl
      | some sp =>
        dsimp only
        rw [hCfg, hPsbtPol]
        cases InternalSpec.Psbt.authorizePsbtSigning
          (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160)
          (InternalSpec.Unified.signingConfigOfTarget profile allowNonDefaultSighash)
          (InternalSpec.Unified.toPsbtWalletPolicySpec (InternalSpec.Unified.policyProfileOfTarget profile) dev policyOra policy)
          psbt (some sp) with
        | error _ => rfl
        | ok validated =>
          dsimp only
          rw [hAppPol, appListAny_eq_List_any, appListAny_eq_List_any]

theorem stepVerifiedPsbtSign_refines_spec
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (allowNonDefaultSighash : Bool)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (silentPaymentTx : Option (PsbtSpTx Affine))
    (s : AppPersistentState) :
    BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign profile net hw ui dev policyOra hash160
      allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
      standardSignTasks musigPlan silentPaymentTx s =
    InternalSpec.Unified.stepVerifiedPsbtSign profile net hw ui dev policyOra hash160
      allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
      standardSignTasks musigPlan silentPaymentTx s := by
  unfold BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign InternalSpec.Unified.stepVerifiedPsbtSign
  rw [buildVerifiedPsbtSignRequest_refines_spec]
  cases InternalSpec.Unified.buildVerifiedPsbtSignRequest profile net hw dev policyOra hash160
          allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt
          merkleOpt s.swapLock standardSignTasks musigPlan silentPaymentTx with
  | error vErr =>
    dsimp only
    cases s.swapLock <;> cases vErr <;> (try cases ‹InternalSpec.Psbt.PsbtError›) <;> rfl
  | ok pair =>
    rcases pair with ⟨validated, req⟩
    dsimp only
    rw [stepAppCommand_refines_spec]
    cases InternalSpec.AppStateMachine.stepAppCommand profile hw ui (.signPsbt req) s with
    | error p => cases p; rfl
    | ok p => cases p; rfl

/-! ## 3. Security, Purity, Rollback, User-Consent, Anti-Replay, Swap & `verifyPsbtSignMessage` Theorems -/

/-- Forward-compatibility on `CLA = 0xE1`: `classifyBolosApdu` accepts arbitrary `hdr.p1`. -/
theorem impl_classifyBolosApdu_allows_arbitrary_p1
    (inSwapMode : Bool) (ins p1 p1' p2 : UInt8) :
    BitcoinLedger.AppStateMachine.classifyBolosApdu inSwapMode
      { cla := BitcoinLedger.AppStateMachine.bolosClaApp, ins := ins, p1 := p1, p2 := p2 } =
    BitcoinLedger.AppStateMachine.classifyBolosApdu inSwapMode
      { cla := BitcoinLedger.AppStateMachine.bolosClaApp, ins := ins, p1 := p1', p2 := p2 } := by
  rw [classifyBolosApdu_refines_spec, classifyBolosApdu_refines_spec]
  exact InternalSpec.AppStateMachine.classifyBolosApdu_allows_arbitrary_p1 inSwapMode ins p1 p1' p2

/-- **Read-Only Purity (`s' = s`)**:
    Every `.ok` execution of `GET_VERSION`, `GET_MASTER_FINGERPRINT`, `GET_EXTENDED_PUBKEY`, or `GET_ADDRESS`
    leaves `AppPersistentState` identically unchanged (`s' = s`), and every `.error` execution preserves
    `registeredAccounts`, `musigSessions`, `swapLock`, and `residentKeys`. -/
theorem impl_readOnly_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s s' : AppPersistentState)
    (hRO : BitcoinLedger.AppStateMachine.isCommandReadOnly cmd = true) :
    ((∃ resp, BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui cmd s = .ok (resp, s')) → s' = s) ∧
    ((∃ err, BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui cmd s = .error (err, s')) →
      s'.registeredAccounts = s.registeredAccounts ∧
      s'.musigSessions = s.musigSessions ∧
      s'.swapLock = s.swapLock ∧
      s'.residentKeys = s.residentKeys) := by
  rw [isCommandReadOnly_eq] at hRO
  simp only [stepAppCommand_refines_spec]
  exact InternalSpec.AppStateMachine.readOnly_purity profile hw ui cmd s s' hRO

theorem impl_getVersion_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (s s' : AppPersistentState) (resp : AppResponse)
    (h : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui .getVersion s = .ok (resp, s')) :
    s' = s :=
  (impl_readOnly_purity profile hw ui .getVersion s s' rfl).1 ⟨resp, h⟩

theorem impl_getMasterFingerprint_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (tree : KeyTree) (s s' : AppPersistentState) (resp : AppResponse)
    (h : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.getMasterFingerprint tree) s =
          .ok (resp, s')) : s' = s :=
  (impl_readOnly_purity profile hw ui (.getMasterFingerprint tree) s s' rfl).1 ⟨resp, h⟩

theorem impl_getExtendedPubkey_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (tree : KeyTree) (display : Bool) (path : List UInt32) (idIdx : Option UInt32)
    (s s' : AppPersistentState) (resp : AppResponse)
    (h : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui
          (.getExtendedPubkey tree display path idIdx) s = .ok (resp, s')) : s' = s :=
  (impl_readOnly_purity profile hw ui (.getExtendedPubkey tree display path idIdx) s s' rfl).1 ⟨resp, h⟩

theorem impl_getAddress_purity {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (display : Bool) (acc : AccountSpec Affine) (por : Option InternalSpec.Musig2.Bytes32)
    (coords : AddressCoordinates) (idIdx : Option UInt32)
    (s s' : AppPersistentState) (resp : AppResponse)
    (h : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui
          (.getAddress display acc por coords idIdx) s = .ok (resp, s')) : s' = s :=
  (impl_readOnly_purity profile hw ui (.getAddress display acc por coords idIdx) s s' rfl).1 ⟨resp, h⟩

/-- **Atomic Error Rollback**:
    Any command returning `.error (e, s')` leaves `registeredAccounts`, `swapLock`, and `residentKeys`
    unchanged and monotonically preserves consumed MuSig2 `RandRoot`s. -/
theorem impl_atomic_error_rollback {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s s' : AppPersistentState) (e : AppError)
    (hErr : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui cmd s = .error (e, s')) :
    s'.registeredAccounts = s.registeredAccounts ∧
    s'.swapLock = s.swapLock ∧
    s'.residentKeys = s.residentKeys ∧
    (∀ rr, BitcoinLedger.Musig2.isRandRootConsumed s.musigSessions rr = true →
      BitcoinLedger.Musig2.isRandRootConsumed s'.musigSessions rr = true) := by
  rw [stepAppCommand_refines_spec] at hErr
  have hSpec := InternalSpec.AppStateMachine.atomic_error_rollback profile hw ui cmd s s' e hErr
  refine ⟨hSpec.1, hSpec.2.1, hSpec.2.2.1, ?_⟩
  intro rr hC
  rw [Proofs.Musig2.isRandRootConsumed_eq] at hC ⊢
  exact hSpec.2.2.2 rr hC

/-- **User-Consent Gate for `SIGN_MESSAGE`**:
    Without user approval, `SIGN_MESSAGE` never succeeds. -/
theorem impl_user_consent_gate_signMessage {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (path : List UInt32) (msg : ByteArray) (hdrBase : CompactSigHeaderBase)
    (s s' : AppPersistentState) (resp : AppResponse)
    (hDeny : ∀ p, ui.approve p = false) :
    BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.signMessage path msg hdrBase) s ≠
      .ok (resp, s') := by
  rw [stepAppCommand_refines_spec]
  exact InternalSpec.AppStateMachine.user_consent_gate_signMessage profile hw ui path msg hdrBase s s' resp hDeny

/-- **User-Consent Gate for `SIGN_PSBT`**:
    Without user approval, `SIGN_PSBT` never emits any standard signature, MuSig2 partial signature,
    or Silent Payment ECDH share unless `s.swapLock = some lock` and `validSwapPsbt` succeeded. -/
theorem impl_user_consent_gate_signPsbt {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (psbt : PsbtSignRequest Affine) (s s' : AppPersistentState) (resp : AppResponse)
    (hDeny : ∀ p, ui.approve p = false)
    (hOk : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.signPsbt psbt) s = .ok (resp, s'))
    (hSig : BitcoinLedger.AppStateMachine.responseEmitsSecretDerivedMaterial resp = true) :
    ∃ lock : SwapLock,
      s.swapLock = some lock ∧
      BitcoinLedger.AppStateMachine.validSwapPsbt hw.musigCrypto.sha256 lock psbt = true := by
  rw [stepAppCommand_refines_spec] at hOk
  rw [responseEmitsSecretDerivedMaterial_eq] at hSig
  obtain ⟨lock, hLock, hVal⟩ :=
    InternalSpec.AppStateMachine.user_consent_gate_signPsbt profile hw ui psbt s s' resp hDeny hOk hSig
  rw [← validSwapPsbt_eq] at hVal
  exact ⟨lock, hLock, hVal⟩

/-- **User-Consent Gate for Vanadium MuSig2 Round 1**:
    On Vanadium, pure MuSig2 Round 1 never succeeds without explicit user approval. -/
theorem impl_vanadium_round1Only_requires_user_consent {Affine : Type} [DecidableEq Affine]
    (ct : UInt32) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (psbt : PsbtSignRequest Affine) (sid : PsbtSessionId) (r1Tasks : List MusigSignTask)
    (s s' : AppPersistentState) (resp : AppResponse)
    (hPlan : psbt.musigPlan = .round1Only sid r1Tasks)
    (hDeny : ∀ p, ui.approve p = false) :
    BitcoinLedger.AppStateMachine.stepAppCommand (.vanadium ct) hw ui (.signPsbt psbt) s ≠
      .ok (resp, s') := by
  rw [stepAppCommand_refines_spec]
  exact InternalSpec.AppStateMachine.vanadium_round1Only_requires_user_consent ct hw ui psbt sid r1Tasks s s' resp hPlan hDeny

/-- **User-Consent Gate for BIP-392 `exportSpScanKey`**:
    `exportSpScanKey` never exports a secret scan key unless `ui.approve (.confirmExportSpScanKey accountIndex) = true`. -/
theorem impl_exportSpScanKey_requires_user_consent {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (hrp : SpScanHrp) (accountIndex : UInt32)
    (s s' : AppPersistentState) (resp : AppResponse)
    (hDeny : ui.approve (.confirmExportSpScanKey accountIndex) = false) :
    BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.exportSpScanKey hrp accountIndex) s ≠
      .ok (resp, s') := by
  intro hOk
  unfold BitcoinLedger.AppStateMachine.stepAppCommand at hOk
  cases hCond1 : (s.swapLock.isSome && s.swapAborted) with
  | true => rw [hCond1] at hOk; contradiction
  | false =>
    rw [hCond1] at hOk
    simp only [Bool.false_eq_true, ↓reduceIte] at hOk
    cases hCond2 : (s.swapLock.isSome && !BitcoinLedger.AppStateMachine.isAllowedInSwap (.exportSpScanKey hrp accountIndex)) with
    | true => rw [hCond2] at hOk; contradiction
    | false =>
      rw [hCond2] at hOk
      simp only [Bool.false_eq_true, ↓reduceIte] at hOk
      cases profile with
      | bolos _ => contradiction
      | vanadium ct =>
        dsimp only at hOk
        rw [hDeny] at hOk
        cases hExp : BitcoinLedger.SilentPayments.exportSpScanKey hw.spCrypto hw.bech32m
                       (BitcoinLedger.AppStateMachine.profileSpScanHrp (.vanadium ct))
                       hw.deriveSpAccount accountIndex false with
        | ok encoded =>
          exact Proofs.SilentPayments.impl_exportSpScanKey_requires_user_consent
            hw.spCrypto hw.bech32m (BitcoinLedger.AppStateMachine.profileSpScanHrp (.vanadium ct))
            hw.deriveSpAccount accountIndex encoded hExp
        | error spErr =>
          rw [hExp] at hOk
          cases spErr <;> contradiction

/-- **MuSig2 Nonce Anti-Replay Across Arbitrary Multi-Step Traces**:
    Every `RandRoot` produces Round-2 partial signatures in at most one step across any trace `cmds`. -/
theorem impl_musig2_nonce_anti_replay {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (rr : RandRoot) (cmds : List (AppCommand Affine)) (s : AppPersistentState) :
    BitcoinLedger.AppStateMachine.countMusigRound2StepsForRandRoot profile hw ui rr cmds s ≤ 1 := by
  rw [countMusigRound2StepsForRandRoot_eq]
  exact InternalSpec.AppStateMachine.musig2_nonce_anti_replay profile hw ui rr cmds s

/-- **Immediate MuSig2 Round-2 Replay Rejected with `.musigError .missingSession`**: -/
theorem impl_app_musig2_immediate_replay_missingSession {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (psbt1 psbt2 : PsbtSignRequest Affine) (sid : PsbtSessionId)
    (r2Inputs1 r2Inputs2 : List MusigRound2TaskInput)
    (s s' : AppPersistentState) (resp : AppResponse)
    (hNoSwap : s'.swapLock = none)
    (hPlan1 : psbt1.musigPlan = .round2 sid r2Inputs1)
    (hPlan2 : psbt2.musigPlan = .round2 sid r2Inputs2)
    (hAuth2 : BitcoinLedger.AppStateMachine.validateAccountAuth profile hw false psbt2.account psbt2.por = .ok ())
    (hAmt2 : ((!BitcoinLedger.AppStateMachine.allowUnderfundedInputs profile false psbt2 &&
               decide (psbt2.inputsTotalAmount < psbt2.outputsTotalAmount)) ||
              decide (psbt2.outputsTotalAmount < psbt2.changeOutputsTotalAmount)) = false)
    (hSp2 : psbt2.silentPaymentTx = none)
    (hOk1 : BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.signPsbt psbt1) s = .ok (resp, s')) :
    BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.signPsbt psbt2) s' =
      .error (.musigError .missingSession, s') := by
  rw [stepAppCommand_refines_spec] at hOk1 ⊢
  rw [validateAccountAuth_refines_spec] at hAuth2
  exact InternalSpec.AppStateMachine.app_musig2_immediate_replay_missingSession profile hw ui psbt1 psbt2
    sid r2Inputs1 r2Inputs2 s s' resp hNoSwap hPlan1 hPlan2 hAuth2 hAmt2 hSp2 hOk1

/-- **Swap Session Lock Termination on Failure**:
    Once `s.swapLock = some lock` and `s.swapAborted = true`, EVERY command immediately terminates
    with `.error (.failSwap, s)`. -/
theorem impl_swap_aborted_terminates_all_commands {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile) (hw : HardwareOracle Affine) (ui : UserApprovalOracle Affine)
    (cmd : AppCommand Affine) (s : AppPersistentState) (lock : SwapLock)
    (hLock : s.swapLock = some lock) (hAborted : s.swapAborted = true) :
    BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui cmd s = .error (.failSwap, s) := by
  unfold BitcoinLedger.AppStateMachine.stepAppCommand
  simp [hLock, hAborted]

/-- **Swap BIP-322 Rejection & Failure Latching**:
    Attempting BIP-322 in Swap mode returns `.notSupported`, failing a Swap fee/amount check sets
    `swapAborted := true` with `.failSwap`, and subsequent commands terminate with `.failSwap`. -/
theorem impl_swap_bip322_rejected_and_abort_latches :
    let lock : SwapLock := {
      amount := 90000, fees := 1000, destinationAddress := "bc1qswapdest", mode := .standard
    }
    let defaultWp : WalletPolicySpec := {
      name := "", version := 2, descriptorTemplate := "wpkh(@0/**)",
      nKeys := 1, nInternalKeys := 1, isDefaultPolicy := true, isSignable := true,
      walletId := InternalSpec.Musig2.oneByte32, keysInfoPayloads := []
    }
    let bip322Req : PsbtSignRequest Unit := {
      account := .walletPolicy defaultWp, por := none, isBip322MessageSigning := true,
      inputsTotalAmount := 100000, outputsTotalAmount := 99000, changeOutputsTotalAmount := 9000,
      nExternalInputs := 0, missingNonWitnessUtxo := false, nonDefaultSighash := false,
      externalOutputs := [], standardSignTasks := [], musigPlan := .none, silentPaymentTx := none
    }
    let wrongFeeReq : PsbtSignRequest Unit := {
      bip322Req with isBip322MessageSigning := false, outputsTotalAmount := 98000
    }
    let s0 : AppPersistentState := { swapLock := some lock }
    let sAborted : AppPersistentState := { swapLock := some lock, swapAborted := true }
    BitcoinLedger.AppStateMachine.stepAppCommand (.bolos 0) InternalSpec.AppStateMachine.toyHardwareOracle
      ⟨fun _ => false⟩ (.signPsbt bip322Req) s0 = .error (.notSupported, s0) ∧
    BitcoinLedger.AppStateMachine.stepAppCommand (.bolos 0) InternalSpec.AppStateMachine.toyHardwareOracle
      ⟨fun _ => false⟩ (.signPsbt wrongFeeReq) s0 = .error (.failSwap, sAborted) ∧
    BitcoinLedger.AppStateMachine.stepAppCommand (.bolos 0) InternalSpec.AppStateMachine.toyHardwareOracle
      ⟨fun _ => false⟩ (.getMasterFingerprint .standard) sAborted = .error (.failSwap, sAborted) := by
  simp only [stepAppCommand_refines_spec]
  exact InternalSpec.AppStateMachine.swap_bip322_rejected_and_abort_latches

/-- **End-to-End `stepVerifiedPsbtSign` Soundness on `BitcoinLedger.AppStateMachine`**: -/
theorem impl_stepVerifiedPsbtSign_soundness
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (allowNonDefaultSighash : Bool)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (silentPaymentTx : Option (PsbtSpTx Affine))
    (s s' : AppPersistentState)
    (validated : InternalSpec.Psbt.ValidatedPsbt)
    (resp : AppResponse)
    (hStep : BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign profile net hw ui dev policyOra hash160
               allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt
               merkleOpt standardSignTasks musigPlan silentPaymentTx s = .ok (validated, resp, s')) :
    let polProf := InternalSpec.Unified.policyProfileOfTarget profile
    let psbtCrypto := InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160
    let psbtPolicy := InternalSpec.Unified.toPsbtWalletPolicySpec polProf dev policyOra policy
    let cfg := InternalSpec.Unified.signingConfigOfTarget profile allowNonDefaultSighash
    InternalSpec.WalletPolicy.checkPolicyWellFormed polProf policy = .ok () ∧
    (∀ bundle, merkleOpt = some bundle →
      BitcoinLedger.AppStateMachine.verifyPsbtMerkleBundle
        psbtCrypto.sha256 psbt.inputs.size psbt.outputs.size bundle = true) ∧
    (∃ (req : PsbtSignRequest Affine) (swapParamsOpt : Option InternalSpec.Psbt.SwapParams),
      InternalSpec.Psbt.authorizePsbtSigning psbtCrypto cfg psbtPolicy psbt swapParamsOpt = .ok validated ∧
      BitcoinLedger.AppStateMachine.stepAppCommand profile hw ui (.signPsbt req) s = .ok (resp, s') ∧
      (BitcoinLedger.AppStateMachine.responseEmitsSecretDerivedMaterial resp = true →
       (∀ p, ui.approve p = false) →
       ∃ (lock : SwapLock) (sp : InternalSpec.Psbt.SwapParams),
         s.swapLock = some lock ∧
         BitcoinLedger.AppStateMachine.appSwapLockToPsbtSwapParams lock = some sp ∧
         swapParamsOpt = some sp ∧
         InternalSpec.Psbt.validateSwapPsbt psbtCrypto psbtPolicy psbt validated sp = .ok () ∧
         BitcoinLedger.AppStateMachine.validSwapPsbt hw.musigCrypto.sha256 lock req = true)) := by
  rw [stepVerifiedPsbtSign_refines_spec] at hStep
  obtain ⟨hWf, hMerkle, ⟨req, swapParamsOpt, hAuth, hApp, hGate⟩⟩ :=
    InternalSpec.Unified.stepVerifiedPsbtSign_soundness profile net hw ui dev policyOra hash160
      allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
      standardSignTasks musigPlan silentPaymentTx s s' validated resp hStep
  refine ⟨hWf, ?_, ⟨req, swapParamsOpt, hAuth, ?_, ?_⟩⟩
  · intro bundle hSome
    rw [verifyPsbtMerkleBundle_refines_spec]
    exact hMerkle bundle hSome
  · rw [stepAppCommand_refines_spec]; exact hApp
  · intro hEmits hDeny
    rw [responseEmitsSecretDerivedMaterial_eq] at hEmits
    obtain ⟨lock, sp, hL, hSp, hOpt, hValPsbt, hValApp⟩ := hGate hEmits hDeny
    have hSpImpl : BitcoinLedger.AppStateMachine.appSwapLockToPsbtSwapParams lock = some sp := by
      have hEq : BitcoinLedger.AppStateMachine.appSwapLockToPsbtSwapParams lock =
          InternalSpec.Unified.appSwapLockToPsbtSwapParams lock := by
        cases lock.mode <;> rfl
      rw [hEq]; exact hSp
    rw [← validSwapPsbt_eq] at hValApp
    exact ⟨lock, sp, hL, hSpImpl, hOpt, hValPsbt, hValApp⟩

/-- **End-to-End `stepVerifiedPsbtSign` Atomic Error Rollback on `BitcoinLedger.AppStateMachine`**: -/
theorem impl_stepVerifiedPsbtSign_error_rollback
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (allowNonDefaultSighash : Bool)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (silentPaymentTx : Option (PsbtSpTx Affine))
    (s s' : AppPersistentState)
    (err : VerifiedPsbtSignError)
    (hErr : BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign profile net hw ui dev policyOra hash160
              allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt
              merkleOpt standardSignTasks musigPlan silentPaymentTx s = .error (err, s')) :
    s'.registeredAccounts = s.registeredAccounts ∧
    s'.swapLock = s.swapLock ∧
    s'.residentKeys = s.residentKeys ∧
    (∀ rr, BitcoinLedger.Musig2.isRandRootConsumed s.musigSessions rr = true →
      BitcoinLedger.Musig2.isRandRootConsumed s'.musigSessions rr = true) := by
  rw [stepVerifiedPsbtSign_refines_spec] at hErr
  have hSpec := InternalSpec.Unified.stepVerifiedPsbtSign_error_rollback profile net hw ui dev policyOra
    hash160 allowNonDefaultSighash descriptorTemplate walletId keysInfoPayloads por policy psbt
    merkleOpt standardSignTasks musigPlan silentPaymentTx s s' err hErr
  refine ⟨hSpec.1, hSpec.2.1, hSpec.2.2.1, ?_⟩
  intro rr hC
  rw [Proofs.Musig2.isRandRootConsumed_eq] at hC ⊢
  exact hSpec.2.2.2 rr hC

/-- **End-to-End BIP-322 `verifyPsbtSignMessage` Soundness & Mandatory User-Consent Theorem**:
    Whenever `verifyPsbtSignMessage` succeeds with `.ok (validated, resp, s')`:
    1. Swap mode was inactive (`s.swapLock = none`),
    2. `psbt.bip322Message = some message`,
    3. BIP-388 `checkPolicyWellFormed` accepted `policy`,
    4. Any supplied `PsbtMerkleOpeningBundle` passed `verifyPsbtMerkleBundle`,
    5. `InternalSpec.Psbt.validateBip322Psbt` verified `psbt` & `message` (including `bip322ToSpendTxid` challenge!),
    6. **Unconditional User Consent** (no Swap bypass exists for BIP-322): if `resp` emits any secret-derived
       material, the user CANNOT have rejected all prompts (`¬(∀ p, ui.approve p = false)`). -/
theorem impl_verifyPsbtSignMessage_soundness
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (message : ByteArray)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (s s' : AppPersistentState)
    (validated : InternalSpec.Psbt.ValidatedPsbt)
    (resp : AppResponse)
    (hOk : BitcoinLedger.AppStateMachine.verifyPsbtSignMessage profile net hw ui dev policyOra hash160
             descriptorTemplate walletId keysInfoPayloads por policy message psbt merkleOpt
             standardSignTasks musigPlan s = .ok (validated, resp, s')) :
    let polProf := InternalSpec.Unified.policyProfileOfTarget profile
    let psbtCrypto := InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160
    s.swapLock = none ∧
    psbt.bip322Message = some message ∧
    InternalSpec.WalletPolicy.checkPolicyWellFormed polProf policy = .ok () ∧
    (∀ bundle, merkleOpt = some bundle →
      BitcoinLedger.AppStateMachine.verifyPsbtMerkleBundle
        psbtCrypto.sha256 psbt.inputs.size psbt.outputs.size bundle = true) ∧
    InternalSpec.Psbt.validateBip322Psbt psbtCrypto.sha256 false psbt validated message = .ok () ∧
    (BitcoinLedger.AppStateMachine.responseEmitsSecretDerivedMaterial resp = true →
      ¬(∀ p, ui.approve p = false)) := by
  unfold BitcoinLedger.AppStateMachine.verifyPsbtSignMessage at hOk
  cases hSwap : s.swapLock with
  | some _ =>
    have hIf : (if s.swapLock.isSome then
                  Except.error (VerifiedPsbtSignError.psbtRejected .bip322ForbiddenInSwap, s)
                else if !decide (psbt.bip322Message = some message) then
                  Except.error (VerifiedPsbtSignError.psbtRejected .bip322InvalidStructure, s)
                else
                  BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign profile net hw ui dev policyOra hash160 false
                    descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
                    standardSignTasks musigPlan none s) = .ok (validated, resp, s') := hOk
    rw [hSwap] at hIf
    contradiction
  | none =>
    have hStep :
        BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign profile net hw ui dev policyOra hash160 false
          descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
          standardSignTasks musigPlan none s = .ok (validated, resp, s') ∧
        psbt.bip322Message = some message := by
      have hIf := hOk
      rw [hSwap] at hIf
      simp only [Option.isSome, Bool.false_eq_true, ↓reduceIte] at hIf
      cases hMsgDec : decide (psbt.bip322Message = some message) with
      | false => rw [hMsgDec] at hIf; contradiction
      | true =>
        rw [hMsgDec] at hIf
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hIf
        exact ⟨hIf, of_decide_eq_true hMsgDec⟩
    rcases hStep with ⟨hStepOk, hMsgEq⟩
    obtain ⟨hWf, hMerkle, ⟨req, swapParamsOpt, hAuth, hApp, hGate⟩⟩ :=
      impl_stepVerifiedPsbtSign_soundness profile net hw ui dev policyOra hash160 false
        descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
        standardSignTasks musigPlan none s s' validated resp hStepOk
    -- Extract `validateBip322Psbt ... = .ok ()` directly from `hBuild` when `swapLockOpt = none`:
    have hBip322Ok : InternalSpec.Psbt.validateBip322Psbt
        (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160).sha256
        false psbt validated message = .ok () := by
      rw [stepVerifiedPsbtSign_refines_spec] at hStepOk
      unfold InternalSpec.Unified.stepVerifiedPsbtSign at hStepOk
      rw [hSwap] at hStepOk
      cases hBuild : InternalSpec.Unified.buildVerifiedPsbtSignRequest profile net hw dev policyOra hash160
                       false descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt
                       none standardSignTasks musigPlan none with
      | error _ => rw [hBuild] at hStepOk; contradiction
      | ok pair =>
        rcases pair with ⟨val0, req0⟩
        rw [hBuild] at hStepOk
        dsimp only at hStepOk
        have hVal0Eq : val0 = validated := by
          cases hStepApp : InternalSpec.AppStateMachine.stepAppCommand profile hw ui (.signPsbt req0) s with
          | error _ => rw [hStepApp] at hStepOk; contradiction
          | ok ap =>
            rw [hStepApp] at hStepOk
            injection hStepOk with hT
            exact congrArg Prod.fst hT
        subst val0
        obtain ⟨_, _, ⟨sp0, hRel0, hAuth0⟩, _⟩ :=
          InternalSpec.Unified.buildVerifiedPsbtSignRequest_soundness profile net hw dev policyOra hash160
            false descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt none
            standardSignTasks musigPlan none validated req0 hBuild
        have hSp0None : sp0 = none := by
          cases hRel0 with
          | inl hN => exact hN.2
          | inr hS => rcases hS with ⟨_, _, hC, _⟩; cases hC
        subst sp0
        unfold InternalSpec.Psbt.authorizePsbtSigning at hAuth0
        cases hVp : InternalSpec.Psbt.validatePsbt
            (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160)
            (InternalSpec.Unified.signingConfigOfTarget profile false)
            (InternalSpec.Unified.toPsbtWalletPolicySpec (InternalSpec.Unified.policyProfileOfTarget profile) dev policyOra policy)
            psbt with
        | error _ => rw [hVp] at hAuth0; contradiction
        | ok v1 =>
          rw [hVp, hMsgEq] at hAuth0
          dsimp only [Option.isSome] at hAuth0
          cases hB322 : InternalSpec.Psbt.validateBip322Psbt
              (InternalSpec.Unified.mkPsbtCryptoOracles profile net hw hash160).sha256
              false psbt v1 message with
          | error _ => rw [hB322] at hAuth0; contradiction
          | ok u =>
            cases u
            rw [hB322] at hAuth0
            injection hAuth0 with hV1Eq
            subst hV1Eq
            exact hB322
    refine ⟨rfl, hMsgEq, hWf, hMerkle, hBip322Ok, ?_⟩
    intro hEmits hDeny
    obtain ⟨lock, _, hLockSome, _⟩ := hGate hEmits hDeny
    rw [hSwap] at hLockSome
    cases hLockSome

/-- **End-to-End BIP-322 `verifyPsbtSignMessage` Atomic Error Rollback**: -/
theorem impl_verifyPsbtSignMessage_error_rollback
    {Affine : Type} [DecidableEq Affine]
    (profile : TargetProfile)
    (net : InternalSpec.Network)
    (hw : HardwareOracle Affine)
    (ui : UserApprovalOracle Affine)
    (dev : InternalSpec.WalletPolicy.DeviceRegistrationOracle)
    (policyOra : InternalSpec.WalletPolicy.CryptoPolicyOracle)
    (hash160 : ByteArray → ByteArray)
    (descriptorTemplate : String)
    (walletId : InternalSpec.Musig2.Bytes32)
    (keysInfoPayloads : List ByteArray)
    (por : Option InternalSpec.Musig2.Bytes32)
    (policy : InternalSpec.WalletPolicy.WalletPolicy)
    (message : ByteArray)
    (psbt : InternalSpec.Psbt.PsbtTx)
    (merkleOpt : Option PsbtMerkleOpeningBundle)
    (standardSignTasks : List StandardInputSigRequest)
    (musigPlan : PsbtMusigPlan)
    (s s' : AppPersistentState)
    (err : VerifiedPsbtSignError)
    (hErr : BitcoinLedger.AppStateMachine.verifyPsbtSignMessage profile net hw ui dev policyOra hash160
              descriptorTemplate walletId keysInfoPayloads por policy message psbt merkleOpt
              standardSignTasks musigPlan s = .error (err, s')) :
    s'.registeredAccounts = s.registeredAccounts ∧
    s'.swapLock = s.swapLock ∧
    s'.residentKeys = s.residentKeys ∧
    (∀ rr, BitcoinLedger.Musig2.isRandRootConsumed s.musigSessions rr = true →
      BitcoinLedger.Musig2.isRandRootConsumed s'.musigSessions rr = true) := by
  unfold BitcoinLedger.AppStateMachine.verifyPsbtSignMessage at hErr
  cases hSwap : s.swapLock.isSome with
  | true =>
    rw [hSwap] at hErr
    injection hErr with hP
    have hs : s = s' := congrArg Prod.snd hP
    subst hs
    exact ⟨rfl, rfl, rfl, fun _ h => h⟩
  | false =>
    rw [hSwap] at hErr
    simp only [Bool.false_eq_true, ↓reduceIte] at hErr
    cases hMsg : (!decide (psbt.bip322Message = some message)) with
    | true =>
      rw [hMsg] at hErr
      injection hErr with hP
      have hs : s = s' := congrArg Prod.snd hP
      subst hs
      exact ⟨rfl, rfl, rfl, fun _ h => h⟩
    | false =>
      rw [hMsg] at hErr
      simp only [Bool.false_eq_true, ↓reduceIte] at hErr
      exact impl_stepVerifiedPsbtSign_error_rollback profile net hw ui dev policyOra hash160 false
        descriptorTemplate walletId keysInfoPayloads por policy psbt merkleOpt standardSignTasks
        musigPlan none s s' err hErr

/-- **Concrete End-to-End Non-Vacuity Witness on `BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign`**: -/
theorem impl_nonvacuous_stepVerifiedPsbtSign_ok :
    ∃ validated resp s',
      let prof := TargetProfile.bolos 0
      let hw := InternalSpec.AppStateMachine.toyHardwareOracle
      let dev := InternalSpec.WalletPolicy.witnessDeviceOracle
      let polOra := InternalSpec.WalletPolicy.witnessCryptoOracle
      let hash160 := polOra.hash160
      let policy := InternalSpec.WalletPolicy.witnessBip84Policy
      let psbtSha256 : ByteArray → InternalSpec.Psbt.Bytes32 :=
        fun bs => BitcoinLedger.AppStateMachine.musigBytes32ToPsbt (hw.musigCrypto.sha256 bs)
      let k0 := ByteArray.mk #[0x01]
      let v0 := ByteArray.mk #[0xAA]
      let singleMap := InternalSpec.MerkleProtocol.commitMerkleMap psbtSha256 [(k0, v0)]
      let singleOp : InternalSpec.MerkleProtocol.MerkleElementOpening := {
        element := k0
        leafHash := InternalSpec.MerkleProtocol.merkleLeafHash psbtSha256 k0
        siblingsBottomUp := []
      }
      let merkleBundle : PsbtMerkleOpeningBundle := {
        globalMap := singleMap
        globalKeyOpenings := [singleOp]
        inputMaps := [(singleMap, [singleOp])]
        outputMaps := [(singleMap, [singleOp]), (singleMap, [singleOp])]
      }
      let inSpk : ByteArray :=
        InternalSpec.mkP2WPKH (hash160 (ByteArray.mk (#[0x02, 0x01, 0x00] ++ Array.replicate 30 0x44)))
      let chgSpk : ByteArray :=
        InternalSpec.mkP2WPKH (hash160 (ByteArray.mk (#[0x02, 0x01, 0x01] ++ Array.replicate 30 0x44)))
      let inp0 : InternalSpec.Psbt.PsbtInput := {
        prevout := { txid := InternalSpec.Psbt.zeroBytes32, vout := 0 }
        witnessUtxo := some { amount := 100000, scriptPubKey := inSpk }
        derivations := [{
          pubkey := ByteArray.mk (#[0x02, 0x01, 0x00] ++ Array.replicate 30 0x44)
          origin := {
            fingerprint := 0x73C5DA0A
            path := [InternalSpec.WalletPolicy.hardened 84, InternalSpec.WalletPolicy.hardened 0, InternalSpec.WalletPolicy.hardened 0, 0, 0]
          }
        }]
      }
      let outDest : InternalSpec.Psbt.PsbtOutput := { amount := 0, scriptPubKey := some (ByteArray.mk #[0x6a]) }
      let outChg : InternalSpec.Psbt.PsbtOutput := {
        amount := 99000
        scriptPubKey := some chgSpk
        derivations := [{
          pubkey := ByteArray.mk (#[0x02, 0x01, 0x01] ++ Array.replicate 30 0x44)
          origin := {
            fingerprint := 0x73C5DA0A
            path := [InternalSpec.WalletPolicy.hardened 84, InternalSpec.WalletPolicy.hardened 0, InternalSpec.WalletPolicy.hardened 0, 1, 0]
          }
        }]
      }
      let psbt : InternalSpec.Psbt.PsbtTx := {
        txVersion := 2, fallbackLocktime := some 0, inputs := #[inp0], outputs := #[outDest, outChg]
      }
      let stdTask : StandardInputSigRequest := {
        inputIndex := 0
        derivationPath := [InternalSpec.WalletPolicy.hardened 84, InternalSpec.WalletPolicy.hardened 0, InternalSpec.WalletPolicy.hardened 0, 0, 0]
        sighash := InternalSpec.Musig2.sighashByte32
        isSchnorr := false
        leafHash := none
      }
      BitcoinLedger.AppStateMachine.stepVerifiedPsbtSign prof .mainnet hw ⟨fun _ => true⟩ dev polOra
        hash160 false "wpkh(@0/<0;1>/*)" InternalSpec.Musig2.oneByte32 [] none policy psbt (some merkleBundle)
        [stdTask] .none none (BitcoinLedger.AppStateMachine.emptyStateForProfile prof) =
        .ok (validated, resp, s') ∧
      validated.fee = some 1000 ∧
      validated.changeOutputs.length = 1 ∧
      BitcoinLedger.AppStateMachine.responseEmitsSecretDerivedMaterial resp = true := by
  obtain ⟨validated, resp, s', hOk, hFee, hChg, hEmits⟩ := InternalSpec.Unified.nonvacuous_stepVerifiedPsbtSign_ok
  refine ⟨validated, resp, s', ?_, hFee, hChg, ?_⟩
  · rw [emptyStateForProfile_eq, stepVerifiedPsbtSign_refines_spec]
    exact hOk
  · rw [responseEmitsSecretDerivedMaterial_eq]
    exact hEmits

/-- **Concrete Multi-Step MuSig2 Round-1 -> GetVersion -> Round-2 -> Replay -> Re-Register Witness**: -/
theorem impl_nonvacuous_multistep_musig_trace :
    ∃ (_sid : PsbtSessionId) (rr1 _rr2 : RandRoot) (hw1 hw2 : HardwareOracle Unit)
      (cmd1 cmd3 : AppCommand Unit) (r1Resp r2Resp r1Resp2 r2Resp2 : AppResponse)
      (sAfter4 sAfter6 : AppPersistentState),
      let s0 := BitcoinLedger.AppStateMachine.emptyStateForProfile (.bolos 0)
      let (outcomes, sMid) := BitcoinLedger.AppStateMachine.runAppTrace (.bolos 0) hw1 ⟨fun _ => true⟩
        [cmd1, .getVersion, cmd3, cmd3] s0
      let (outcomes2, sEnd) := BitcoinLedger.AppStateMachine.runAppTrace (.bolos 0) hw2 ⟨fun _ => true⟩
        [cmd1, cmd3] sMid
      outcomes.length = 4 ∧
      sMid = sAfter4 ∧
      sEnd = sAfter6 ∧
      BitcoinLedger.AppStateMachine.countMusigRound2StepsForRandRoot (.bolos 0) hw1 ⟨fun _ => true⟩
        rr1 [cmd1, .getVersion, cmd3, cmd3] s0 = 1 ∧
      BitcoinLedger.Musig2.isRandRootConsumed sMid.musigSessions rr1 = true ∧
      outcomes = [
        .ok cmd1 r1Resp,
        .ok .getVersion (.version BitcoinLedger.AppStateMachine.targetAppVersion),
        .ok cmd3 r2Resp,
        .error cmd3 (.musigError .missingSession)
      ] ∧
      outcomes2 = [
        .ok cmd1 r1Resp2,
        .ok cmd3 r2Resp2
      ] := by
  rcases InternalSpec.AppStateMachine.nonvacuous_multistep_musig_trace with
    ⟨sid, rr1, rr2, hw1, hw2, cmd1, cmd3, r1Resp, r2Resp, r1Resp2, r2Resp2, sAfter4, sAfter6, hRest⟩
  refine ⟨sid, rr1, rr2, hw1, hw2, cmd1, cmd3, r1Resp, r2Resp, r1Resp2, r2Resp2, sAfter4, sAfter6, ?_⟩
  dsimp only at hRest ⊢
  rw [emptyStateForProfile_eq, runAppTrace_refines_spec, runAppTrace_refines_spec,
      countMusigRound2StepsForRandRoot_eq]
  simp only [Proofs.Musig2.isRandRootConsumed_eq]
  exact hRest

end Proofs.AppStateMachine

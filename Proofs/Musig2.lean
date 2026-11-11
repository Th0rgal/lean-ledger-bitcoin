import InternalSpec
import BitcoinLedger.Musig2

/-!
# `Proofs.Musig2` — Refinement & Security Proofs for `BitcoinLedger.Musig2`

Connects every executable operation in `BitcoinLedger.Musig2` to `InternalSpec.Musig2`:
1. Exact refinement of BIP-327 `keySort`, `secondUniqueKey`, `keyAgg`, `applyTweak`, `applyTweaks`,
   BIP-328 synthetic xpub chaincode (`868087ca02a6f974c4598924c36b57762d32cb45717167e300622c7167e38965`),
   and per-input `(placeholderIdx, inputIdx)` derivation (`deriveMusigPerInputInfo`).
2. Exact refinement of BOLOS vs Vanadium `psbt_session_id` computation (`computeBolosPsbtSessionId`,
   `computeVanadiumPsbtSessionId`), synthetic nonce generation (`syntheticRandIJ`, `nonceGen`),
   `nonceAgg`, `getSessionValues`, `partialSign`, and `partialSigAgg`.
3. Exact Round-1/Round-2 session store equivalence (`capacity = 32` / `28B` on BOLOS,
   `capacity = 1` / `32B` on Vanadium), single-use nonce consumption / anti-replay across arbitrary
   traces, re-registration after Round-2 completion, and self-pubnonce verification.

All theorems satisfy `0 sorryAx`, `0 native_decide`, and `0 Classical.choice`.
-/

namespace Proofs.Musig2

open InternalSpec.Musig2

/-! ## 1. Primitive & Constant Refinement Lemmas -/

theorem secp256k1Order_eq :
    BitcoinLedger.Musig2.secp256k1Order = InternalSpec.Musig2.secp256k1Order := rfl

theorem bip328Chaincode_eq :
    BitcoinLedger.Musig2.bip328Chaincode = InternalSpec.Musig2.bip328Chaincode := by
  decide

theorem byteListEq_eq :
    BitcoinLedger.Musig2.byteListEq = InternalSpec.Musig2.byteListEq := by
  funext xs ys
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons a as ih =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      simp only [BitcoinLedger.Musig2.byteListEq, InternalSpec.Musig2.byteListEq, ih]

theorem listAll_eq {α : Type} (p : α → Bool) :
    ∀ xs, BitcoinLedger.Musig2.listAll p xs = InternalSpec.Musig2.listAll p xs
  | [] => rfl
  | x :: xs => by
    simp only [BitcoinLedger.Musig2.listAll, InternalSpec.Musig2.listAll, listAll_eq p xs]

theorem listMem_eq {α : Type} [DecidableEq α] (x : α) :
    ∀ xs, BitcoinLedger.Musig2.listMem x xs = InternalSpec.Musig2.listMem x xs
  | [] => rfl
  | y :: ys => by
    simp only [BitcoinLedger.Musig2.listMem, InternalSpec.Musig2.listMem, listMem_eq x ys]

theorem isAllZeros_eq {n : Nat} (b : SizedBytes n) :
    BitcoinLedger.Musig2.isAllZeros b = b.isAllZeros := by
  unfold BitcoinLedger.Musig2.isAllZeros SizedBytes.isAllZeros
  exact listAll_eq _ _

theorem sessionIdPrefixEq_eq (idMatchBytes : Nat) (a b : PsbtSessionId) :
    BitcoinLedger.Musig2.sessionIdPrefixEq idMatchBytes a b =
      InternalSpec.Musig2.sessionIdPrefixEq idMatchBytes a b := by
  unfold BitcoinLedger.Musig2.sessionIdPrefixEq InternalSpec.Musig2.sessionIdPrefixEq
  rw [byteListEq_eq]

theorem appendBytes_eq (a b : ByteArray) :
    BitcoinLedger.Musig2.appendBytes a b = InternalSpec.Musig2.appendBytes a b := rfl

theorem concatBytes_eq (xs : List ByteArray) :
    BitcoinLedger.Musig2.concatBytes xs = InternalSpec.Musig2.concatBytes xs := rfl

theorem appendSized_eq {m n : Nat} (a : SizedBytes m) (b : SizedBytes n) :
    BitcoinLedger.Musig2.appendSized a b = SizedBytes.append a b := rfl

theorem pubNonceR1_eq (pn : PubNonce) :
    BitcoinLedger.Musig2.pubNonceR1 pn = PubNonce.r1Bytes pn := rfl

theorem pubNonceR2_eq (pn : PubNonce) :
    BitcoinLedger.Musig2.pubNonceR2 pn = PubNonce.r2Bytes pn := rfl

theorem mkPubNonce_eq (r1 r2 : CompressedPubKey) :
    BitcoinLedger.Musig2.mkPubNonce r1 r2 = PubNonce.ofParts r1 r2 := rfl

theorem xOnlyOfCompressed_eq (pk : CompressedPubKey) :
    BitcoinLedger.Musig2.xOnlyOfCompressed pk = pk.xOnly := rfl

theorem encodeU32BE_eq (v : UInt32) :
    BitcoinLedger.Musig2.encodeU32BE v = InternalSpec.Musig2.encodeU32BE v := rfl

theorem natToBytesBEAux_eq (k v : Nat) (acc : List UInt8) :
    BitcoinLedger.Musig2.natToBytesBEAux k v acc = InternalSpec.Musig2.natToBytesBEAux k v acc := by
  induction k generalizing v acc with
  | zero => rfl
  | succ k ih =>
    simp only [BitcoinLedger.Musig2.natToBytesBEAux, InternalSpec.Musig2.natToBytesBEAux, ih]

theorem sizedBytes_eq_of_bytes {n : Nat} {a b : SizedBytes n} (h : a.bytes = b.bytes) :
    a = b := by
  cases a; cases b; simp at h; subst h; rfl

theorem scalarToBytes32_eq (v : Nat) :
    BitcoinLedger.Musig2.scalarToBytes32 v = InternalSpec.Musig2.scalarToBytes32 v := by
  apply sizedBytes_eq_of_bytes
  unfold BitcoinLedger.Musig2.scalarToBytes32 InternalSpec.Musig2.scalarToBytes32
  dsimp only
  rw [natToBytesBEAux_eq]

theorem bytes32ToNat_eq (b : Bytes32) :
    BitcoinLedger.Musig2.bytes32ToNat b = InternalSpec.Musig2.bytes32ToNat b := rfl

theorem parseScalarStrict_eq (b : Bytes32) :
    BitcoinLedger.Musig2.parseScalarStrict b = InternalSpec.Musig2.parseScalarStrict b := by
  unfold BitcoinLedger.Musig2.parseScalarStrict InternalSpec.Musig2.parseScalarStrict
  rw [bytes32ToNat_eq, secp256k1Order_eq]
  by_cases h : InternalSpec.Musig2.bytes32ToNat b < InternalSpec.Musig2.secp256k1Order <;> simp [h]

theorem parseNonZeroScalar_eq (b : Bytes32) :
    BitcoinLedger.Musig2.parseNonZeroScalar b = InternalSpec.Musig2.parseNonZeroScalar b := rfl

theorem parseScalarModN_eq (b : Bytes32) :
    BitcoinLedger.Musig2.parseScalarModN b = InternalSpec.Musig2.parseScalarModN b := rfl

/-! ## 2. `keySort`, `secondUniqueKey`, `keyAgg` & Tweaking Refinement -/

theorem listLexLe_eq :
    BitcoinLedger.Musig2.listLexLe = InternalSpec.Musig2.listLexLe := by
  funext xs ys
  induction xs generalizing ys with
  | nil => rfl
  | cons a as ih =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      simp only [BitcoinLedger.Musig2.listLexLe, InternalSpec.Musig2.listLexLe, ih]

theorem pubKeyLe_eq (a b : CompressedPubKey) :
    BitcoinLedger.Musig2.pubKeyLe a b = InternalSpec.Musig2.pubKeyLe a b := by
  unfold BitcoinLedger.Musig2.pubKeyLe InternalSpec.Musig2.pubKeyLe
  rw [listLexLe_eq]

theorem insertPubKey_eq (x : CompressedPubKey) (xs : List CompressedPubKey) :
    BitcoinLedger.Musig2.insertPubKey x xs = InternalSpec.Musig2.insertPubKey x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [BitcoinLedger.Musig2.insertPubKey, InternalSpec.Musig2.insertPubKey, pubKeyLe_eq, ih]

theorem keySort_refines_spec (pks : List CompressedPubKey) :
    BitcoinLedger.Musig2.keySort pks = InternalSpec.Musig2.keySort pks := by
  induction pks with
  | nil => rfl
  | cons x xs ih =>
    simp only [BitcoinLedger.Musig2.keySort, InternalSpec.Musig2.keySort, ih, insertPubKey_eq]

theorem findSecondUnique_eq_find (first : CompressedPubKey) :
    ∀ rest : List CompressedPubKey,
      BitcoinLedger.Musig2.findSecondUnique first rest =
        rest.find? (fun pk => pk != first)
  | [] => rfl
  | pk :: rest => by
    simp only [BitcoinLedger.Musig2.findSecondUnique, List.find?]
    have hBne : (pk != first) = decide (pk ≠ first) := by
      show (!(decide (pk = first))) = decide (pk ≠ first)
      by_cases h : pk = first
      · subst h; rfl
      · simp [h]
    rw [hBne]
    cases decide (pk ≠ first) <;> simp [findSecondUnique_eq_find first rest]

theorem secondUniqueKey_refines_spec (pks : List CompressedPubKey) :
    BitcoinLedger.Musig2.secondUniqueKey pks = InternalSpec.Musig2.secondUniqueKey pks := by
  cases pks with
  | nil => rfl
  | cons first rest =>
    unfold BitcoinLedger.Musig2.secondUniqueKey InternalSpec.Musig2.secondUniqueKey
    exact findSecondUnique_eq_find first rest

theorem cpoint_eq {Affine : Type} (c : MusigCrypto Affine) (pk : CompressedPubKey) :
    BitcoinLedger.Musig2.cpoint c pk = InternalSpec.Musig2.cpoint c pk := rfl

theorem cpointExt_eq {Affine : Type} (c : MusigCrypto Affine) (pk : CompressedPubKey) :
    BitcoinLedger.Musig2.cpointExt c pk = InternalSpec.Musig2.cpointExt c pk := by
  unfold BitcoinLedger.Musig2.cpointExt InternalSpec.Musig2.cpointExt
  rw [isAllZeros_eq]
  rfl

theorem hashKeys_eq {Affine : Type} (c : MusigCrypto Affine) (pks : List CompressedPubKey) :
    BitcoinLedger.Musig2.hashKeys c pks = InternalSpec.Musig2.hashKeys c pks := rfl

theorem keyAggCoeffInternal_eq {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) (pk : CompressedPubKey) (pk2 : Option CompressedPubKey) :
    BitcoinLedger.Musig2.keyAggCoeffInternal c pubkeys pk pk2 =
      InternalSpec.Musig2.keyAggCoeffInternal c pubkeys pk pk2 := by
  unfold BitcoinLedger.Musig2.keyAggCoeffInternal InternalSpec.Musig2.keyAggCoeffInternal
  have hBeq : (pk2 == some pk) = decide (pk2 = some pk) := by
    cases pk2 with
    | none => rfl
    | some q =>
      show decide (q = pk) = decide (some q = some pk)
      by_cases h : q = pk
      · subst h; simp
      · simp [h]
  rw [hBeq]
  rfl

theorem keyAggCoeff_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) (pk : CompressedPubKey) :
    BitcoinLedger.Musig2.keyAggCoeff c pubkeys pk =
      InternalSpec.Musig2.keyAggCoeff c pubkeys pk := by
  unfold BitcoinLedger.Musig2.keyAggCoeff InternalSpec.Musig2.keyAggCoeff
  rw [secondUniqueKey_refines_spec, keyAggCoeffInternal_eq]

theorem keyAggCoeff_second_unique_optimization {Affine : Type}
    (c : MusigCrypto Affine) (pubkeys : List CompressedPubKey) (pk2 : CompressedPubKey)
    (h : BitcoinLedger.Musig2.secondUniqueKey pubkeys = some pk2) :
    BitcoinLedger.Musig2.keyAggCoeff c pubkeys pk2 = 1 := by
  rw [keyAggCoeff_refines_spec]
  rw [secondUniqueKey_refines_spec] at h
  exact InternalSpec.Musig2.keyAggCoeff_second_unique_is_one c pubkeys pk2 h

theorem keyAggLoop_eq {Affine : Type} (c : MusigCrypto Affine)
    (allPks : List CompressedPubKey) (pk2 : Option CompressedPubKey) :
    ∀ (rem : List CompressedPubKey) (acc : CurvePoint Affine),
      BitcoinLedger.Musig2.keyAggLoop c allPks pk2 rem acc =
        InternalSpec.Musig2.keyAggLoop c allPks pk2 rem acc
  | [], _ => rfl
  | pk :: rest, acc => by
    unfold BitcoinLedger.Musig2.keyAggLoop InternalSpec.Musig2.keyAggLoop
    rw [cpoint_eq]
    cases InternalSpec.Musig2.cpoint c pk with
    | error e => rfl
    | ok p =>
      dsimp only [Bind.bind, Except.bind]
      rw [keyAggCoeffInternal_eq]
      exact keyAggLoop_eq c allPks pk2 rest _

theorem keyAgg_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (pubkeys : List CompressedPubKey) :
    BitcoinLedger.Musig2.keyAgg c pubkeys = InternalSpec.Musig2.keyAgg c pubkeys := by
  unfold BitcoinLedger.Musig2.keyAgg InternalSpec.Musig2.keyAgg
  cases pubkeys.isEmpty with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [secondUniqueKey_refines_spec, keyAggLoop_eq]
    cases InternalSpec.Musig2.keyAggLoop c pubkeys (InternalSpec.Musig2.secondUniqueKey pubkeys) pubkeys .infinity with
    | error e => rfl
    | ok qPt =>
      cases qPt <;> rfl

theorem applyTweak_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (ctx : KeyAggContext Affine) (tweak : MusigTweak) :
    BitcoinLedger.Musig2.applyTweak c ctx tweak = InternalSpec.Musig2.applyTweak c ctx tweak := by
  unfold BitcoinLedger.Musig2.applyTweak InternalSpec.Musig2.applyTweak
  rw [parseScalarStrict_eq, secp256k1Order_eq]
  cases InternalSpec.Musig2.parseScalarStrict tweak.scalar with
  | none => rfl
  | some t =>
    dsimp only [Bind.bind, Except.bind]
    cases c.pointAdd
      (c.pointMul (if tweak.isXOnly && !c.hasEvenY ctx.q then InternalSpec.Musig2.secp256k1Order - 1 else 1) (.affine ctx.q))
      (c.pointMul t (.affine c.generator)) <;> rfl

theorem applyTweaks_refines_spec {Affine : Type} (c : MusigCrypto Affine) :
    ∀ (ctx : KeyAggContext Affine) (tweaks : List MusigTweak),
      BitcoinLedger.Musig2.applyTweaks c ctx tweaks = InternalSpec.Musig2.applyTweaks c ctx tweaks
  | _, [] => rfl
  | ctx, tw :: rest => by
    unfold BitcoinLedger.Musig2.applyTweaks InternalSpec.Musig2.applyTweaks
    rw [applyTweak_refines_spec]
    cases InternalSpec.Musig2.applyTweak c ctx tw with
    | error e => rfl
    | ok ctx' => exact applyTweaks_refines_spec c ctx' rest

theorem deriveMusigPerInputInfo_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (participantPubkeys : List CompressedPubKey)
    (numFirst numSecond : UInt32)
    (isChange : Bool)
    (addressIndex : UInt32)
    (spend : MusigSpendPath) :
    BitcoinLedger.Musig2.deriveMusigPerInputInfo c participantPubkeys numFirst numSecond isChange addressIndex spend =
      InternalSpec.Musig2.deriveMusigPerInputInfo c participantPubkeys numFirst numSecond isChange addressIndex spend := by
  unfold BitcoinLedger.Musig2.deriveMusigPerInputInfo InternalSpec.Musig2.deriveMusigPerInputInfo
  cases participantPubkeys.isEmpty with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hMax : BitcoinLedger.Musig2.maxPubkeysPerMusig = InternalSpec.Musig2.maxPubkeysPerMusig := rfl
    rw [hMax]
    by_cases hGt : participantPubkeys.length > InternalSpec.Musig2.maxPubkeysPerMusig
    · simp [hGt]
    · simp only [hGt, decide_false, ↓reduceIte]
      have hHard : BitcoinLedger.Musig2.bip32HardenedBit = InternalSpec.Musig2.bip32HardenedBit := rfl
      rw [hHard]
      cases (decide (InternalSpec.Musig2.bip32HardenedBit ≤ if isChange then numSecond else numFirst) ||
             decide (InternalSpec.Musig2.bip32HardenedBit ≤ addressIndex)) with
      | true => rfl
      | false =>
        rw [keySort_refines_spec, keyAgg_refines_spec, bip328Chaincode_eq]
        cases InternalSpec.Musig2.keyAgg c (InternalSpec.Musig2.keySort participantPubkeys) with
        | error e => rfl
        | ok baseCtx =>
          dsimp only [Bind.bind, Except.bind]
          cases c.ckdPubUnhardened (c.compress baseCtx.q) InternalSpec.Musig2.bip328Chaincode
              (if isChange then numSecond else numFirst) with
          | none => rfl
          | some res1 =>
            rcases res1 with ⟨child1Pk, child1Cc, t0⟩
            dsimp only [Bind.bind, Except.bind]
            cases c.ckdPubUnhardened child1Pk child1Cc addressIndex with
            | none => rfl
            | some res2 =>
              rcases res2 with ⟨child2Pk, child2Cc, t1⟩
              dsimp only [Bind.bind, Except.bind]
              cases spend with
              | tapscript lh => rfl
              | keypath treeOpt =>
                dsimp only
                unfold BitcoinLedger.Musig2.computeTapTweakScalar
                dsimp only
                rw [cpoint_eq]
                cases InternalSpec.Musig2.cpoint c child2Pk with
                | error e => rfl
                | ok child2Pt =>
                  dsimp only [Bind.bind, Except.bind]
                  cases treeOpt with
                  | none =>
                    have hTweak := applyTweak_refines_spec c
                      { q := child2Pt, gacc := 1, tacc := 0 }
                      { scalar := c.taggedHash "TapTweak" child2Pk.xOnly.bytes, isXOnly := true }
                    have hX : (BitcoinLedger.Musig2.xOnlyOfCompressed child2Pk).bytes = child2Pk.xOnly.bytes := rfl
                    simp only [hX]
                    rw [hTweak]
                    cases InternalSpec.Musig2.applyTweak c { q := child2Pt, gacc := 1, tacc := 0 }
                      { scalar := c.taggedHash "TapTweak" child2Pk.xOnly.bytes, isXOnly := true } <;> rfl
                  | some h =>
                    have hTweak := applyTweak_refines_spec c
                      { q := child2Pt, gacc := 1, tacc := 0 }
                      { scalar := c.taggedHash "TapTweak" (InternalSpec.Musig2.appendBytes child2Pk.xOnly.bytes h.bytes), isXOnly := true }
                    have hX : (BitcoinLedger.Musig2.xOnlyOfCompressed child2Pk).bytes = child2Pk.xOnly.bytes := rfl
                    simp only [hX, appendBytes_eq]
                    rw [hTweak]
                    cases InternalSpec.Musig2.applyTweak c { q := child2Pt, gacc := 1, tacc := 0 }
                      { scalar := c.taggedHash "TapTweak" (InternalSpec.Musig2.appendBytes child2Pk.xOnly.bytes h.bytes), isXOnly := true } <;> rfl

/-! ## 3. Nonce Generation, Nonce Aggregation, `partialSign` & `partialSigAgg` Refinement -/

theorem nonceHash_eq {Affine : Type} (c : MusigCrypto Affine)
    (rand : ByteArray) (pk : CompressedPubKey) (aggpk : XOnlyPubKey) (idx : UInt8) :
    BitcoinLedger.Musig2.nonceHash c rand pk aggpk idx =
      InternalSpec.Musig2.nonceHash c rand pk aggpk idx := rfl

theorem nat_beq_zero_eq_decide (n : Nat) : (n == 0) = decide (n = 0) := by
  cases n <;> rfl

theorem nonceGen_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (rand : Bytes32) (pk : CompressedPubKey) (aggpk : XOnlyPubKey) :
    BitcoinLedger.Musig2.nonceGen c rand pk aggpk =
      InternalSpec.Musig2.nonceGen c rand pk aggpk := by
  unfold BitcoinLedger.Musig2.nonceGen InternalSpec.Musig2.nonceGen
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [nonceHash_eq, nonceHash_eq, parseScalarModN_eq, parseScalarModN_eq]
  rw [nat_beq_zero_eq_decide, nat_beq_zero_eq_decide]
  cases (decide (InternalSpec.Musig2.parseScalarModN (InternalSpec.Musig2.nonceHash c rand.bytes pk aggpk 0) = 0) ||
         decide (InternalSpec.Musig2.parseScalarModN (InternalSpec.Musig2.nonceHash c rand.bytes pk aggpk 1) = 0)) with
  | true => rfl
  | false =>
    cases c.pointMul (InternalSpec.Musig2.parseScalarModN (InternalSpec.Musig2.nonceHash c rand.bytes pk aggpk 0)) (.affine c.generator) <;>
      cases c.pointMul (InternalSpec.Musig2.parseScalarModN (InternalSpec.Musig2.nonceHash c rand.bytes pk aggpk 1)) (.affine c.generator) <;> rfl

theorem sumNonceComponent_eq {Affine : Type} (c : MusigCrypto Affine)
    (sel1 sel2 : PubNonce → CompressedPubKey) (hSel : sel1 = sel2) :
    ∀ (idx : Nat) (pns : List PubNonce) (acc : CurvePoint Affine),
      BitcoinLedger.Musig2.sumNonceComponent c sel1 idx pns acc =
        InternalSpec.Musig2.sumNonceComponent c sel2 idx pns acc
  | _, [], acc => by
    unfold BitcoinLedger.Musig2.sumNonceComponent InternalSpec.Musig2.sumNonceComponent
    cases acc <;> rfl
  | idx, pn :: rest, acc => by
    subst hSel
    unfold BitcoinLedger.Musig2.sumNonceComponent InternalSpec.Musig2.sumNonceComponent
    cases c.decompress (sel1 pn) with
    | none => rfl
    | some rij => exact sumNonceComponent_eq c sel1 sel1 rfl (idx + 1) rest _

theorem nonceAgg_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (pubnonces : List PubNonce) :
    BitcoinLedger.Musig2.nonceAgg c pubnonces = InternalSpec.Musig2.nonceAgg c pubnonces := by
  unfold BitcoinLedger.Musig2.nonceAgg InternalSpec.Musig2.nonceAgg
  cases pubnonces.isEmpty with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hR1 : BitcoinLedger.Musig2.pubNonceR1 = PubNonce.r1Bytes := rfl
    have hR2 : BitcoinLedger.Musig2.pubNonceR2 = PubNonce.r2Bytes := rfl
    rw [sumNonceComponent_eq c _ _ hR1, sumNonceComponent_eq c _ _ hR2]
    cases InternalSpec.Musig2.sumNonceComponent c PubNonce.r1Bytes 0 pubnonces .infinity with
    | error e => rfl
    | ok r1 =>
      dsimp only
      cases InternalSpec.Musig2.sumNonceComponent c PubNonce.r2Bytes 0 pubnonces .infinity <;> rfl

theorem getSessionValues_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (ctx : SessionContext) :
    BitcoinLedger.Musig2.getSessionValues c ctx = InternalSpec.Musig2.getSessionValues c ctx := by
  unfold BitcoinLedger.Musig2.getSessionValues InternalSpec.Musig2.getSessionValues
  rw [keyAgg_refines_spec]
  cases InternalSpec.Musig2.keyAgg c ctx.pubkeys with
  | error e => rfl
  | ok baseCtx =>
    dsimp only [Bind.bind, Except.bind]
    rw [applyTweaks_refines_spec]
    cases InternalSpec.Musig2.applyTweaks c baseCtx ctx.tweaks with
    | error e => rfl
    | ok tweakedCtx =>
      dsimp only
      rw [pubNonceR1_eq, pubNonceR2_eq, cpointExt_eq, cpointExt_eq,
          concatBytes_eq, parseScalarModN_eq]
      cases InternalSpec.Musig2.cpointExt c (PubNonce.r1Bytes ctx.aggnonce) with
      | error e => rfl
      | ok r1 =>
        dsimp only
        cases InternalSpec.Musig2.cpointExt c (PubNonce.r2Bytes ctx.aggnonce) with
        | error e => rfl
        | ok r2 =>
          dsimp only
          rfl

theorem partialSign_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (secnonce : SecNonce) (skBytes : Bytes32) (ctx : SessionContext) :
    BitcoinLedger.Musig2.partialSign c secnonce skBytes ctx =
      InternalSpec.Musig2.partialSign c secnonce skBytes ctx := by
  unfold BitcoinLedger.Musig2.partialSign InternalSpec.Musig2.partialSign
  rw [getSessionValues_refines_spec]
  cases InternalSpec.Musig2.getSessionValues c ctx with
  | error e => rfl
  | ok vals =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [secp256k1Order_eq]
    cases (!(decide (0 < secnonce.k1) && decide (secnonce.k1 < InternalSpec.Musig2.secp256k1Order))) with
    | true => rfl
    | false =>
      cases (!(decide (0 < secnonce.k2) && decide (secnonce.k2 < InternalSpec.Musig2.secp256k1Order))) with
      | true => rfl
      | false =>
        rw [parseNonZeroScalar_eq]
        cases InternalSpec.Musig2.parseNonZeroScalar skBytes with
        | none => rfl
        | some sk =>
          dsimp only [Bind.bind, Except.bind]
          cases c.pointMul sk (.affine c.generator) with
          | infinity => rfl
          | affine pubPoint =>
            dsimp only [Bind.bind, Except.bind]
            have hBne : (c.compress pubPoint != secnonce.pk) = decide (c.compress pubPoint ≠ secnonce.pk) := by
              show (!(decide (c.compress pubPoint = secnonce.pk))) = decide (c.compress pubPoint ≠ secnonce.pk)
              by_cases h : c.compress pubPoint = secnonce.pk <;> simp [h]
            rw [hBne]
            cases decide (c.compress pubPoint ≠ secnonce.pk) with
            | true => rfl
            | false =>
              rw [listMem_eq]
              cases (!InternalSpec.Musig2.listMem (c.compress pubPoint) ctx.pubkeys) with
              | true => rfl
              | false =>
                rw [keyAggCoeff_refines_spec, scalarToBytes32_eq]

theorem sumPartialSigsLoop_eq_foldlM :
    ∀ (psigs : List PartialSig) (acc : Nat),
      BitcoinLedger.Musig2.sumPartialSigsLoop psigs acc =
        psigs.foldlM (fun a psig =>
          match InternalSpec.Musig2.parseScalarStrict psig with
          | some s_i => .ok ((a + s_i) % InternalSpec.Musig2.secp256k1Order)
          | none => .error .invalidPartialSignature) acc
  | [], _ => rfl
  | psig :: rest, acc => by
    unfold BitcoinLedger.Musig2.sumPartialSigsLoop
    simp only [List.foldlM]
    rw [parseScalarStrict_eq, secp256k1Order_eq]
    cases InternalSpec.Musig2.parseScalarStrict psig with
    | none => rfl
    | some s_i => exact sumPartialSigsLoop_eq_foldlM rest _

theorem nat_bne_eq_decide_ne (a b : Nat) : (a != b) = decide (a ≠ b) := by
  show (!(a == b)) = decide (a ≠ b)
  by_cases h : a = b
  · subst h
    have hRefl : (a == a) = true := Nat.beq_refl a
    rw [hRefl]
    simp
  · have hFalse : (a == b) = false := by
      cases hEq : (a == b) with
      | false => rfl
      | true => exact absurd (Nat.eq_of_beq_eq_true hEq) h
    rw [hFalse]
    simp [h]

theorem partialSigAgg_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (ctx : SessionContext) (psigs : List PartialSig) :
    BitcoinLedger.Musig2.partialSigAgg c ctx psigs =
      InternalSpec.Musig2.partialSigAgg c ctx psigs := by
  unfold BitcoinLedger.Musig2.partialSigAgg InternalSpec.Musig2.partialSigAgg
  rw [nat_bne_eq_decide_ne]
  cases decide (psigs.length ≠ ctx.pubkeys.length) with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [getSessionValues_refines_spec]
    cases InternalSpec.Musig2.getSessionValues c ctx with
    | error e => rfl
    | ok vals =>
      dsimp only [Bind.bind, Except.bind]
      rw [sumPartialSigsLoop_eq_foldlM]
      cases (psigs.foldlM (fun acc psig =>
          match InternalSpec.Musig2.parseScalarStrict psig with
          | some s_i => Except.ok ((acc + s_i) % InternalSpec.Musig2.secp256k1Order)
          | none => Except.error MusigError.invalidPartialSignature) 0 : Except MusigError Nat) with
      | error e => rfl
      | ok sumS =>
        dsimp only [Bind.bind, Except.bind]
        rw [secp256k1Order_eq, scalarToBytes32_eq, appendSized_eq]

/-! ## 4. `psbt_session_id`, Session Store & Round-1/Round-2 Equivalence -/

theorem syntheticRandIJ_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (randRoot : RandRoot) (inputIndex placeholderIndex : UInt32) :
    BitcoinLedger.Musig2.syntheticRandIJ c randRoot inputIndex placeholderIndex =
      InternalSpec.Musig2.syntheticRandIJ c randRoot inputIndex placeholderIndex := rfl

theorem computeBolosPsbtSessionId_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (descSha256 merkleRoot : Bytes32) (musig2SessionId : Option ByteArray) :
    BitcoinLedger.Musig2.computeBolosPsbtSessionId c descSha256 merkleRoot musig2SessionId =
      InternalSpec.Musig2.computeBolosPsbtSessionId c descSha256 merkleRoot musig2SessionId := rfl

theorem computeVanadiumPsbtSessionId_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (walletId unsignedTxId : Bytes32) :
    BitcoinLedger.Musig2.computeVanadiumPsbtSessionId c walletId unsignedTxId =
      InternalSpec.Musig2.computeVanadiumPsbtSessionId c walletId unsignedTxId := rfl

theorem selectNonceAggPk_refines_spec (mode : NonceAggPkMode)
    (untweaked tweaked : CompressedPubKey) :
    BitcoinLedger.Musig2.selectNonceAggPk mode untweaked tweaked =
      InternalSpec.Musig2.selectNonceAggPk mode untweaked tweaked := by
  cases mode <;> rfl

theorem bolosDefaultStore_eq :
    BitcoinLedger.Musig2.bolosDefaultStore = MusigSessionStore.bolosDefault := rfl

theorem vanadiumDefaultStore_eq :
    BitcoinLedger.Musig2.vanadiumDefaultStore = MusigSessionStore.vanadiumDefault := rfl

theorem isRandRootConsumed_eq (store : MusigSessionStore) (rr : RandRoot) :
    BitcoinLedger.Musig2.isRandRootConsumed store rr = store.isRandRootConsumed rr := by
  unfold BitcoinLedger.Musig2.isRandRootConsumed MusigSessionStore.isRandRootConsumed
  exact listMem_eq _ _

theorem findActiveEntry_eq (idMatchBytes : Nat) (sid : PsbtSessionId) :
    ∀ entries : List (PsbtSessionId × RandRoot),
      BitcoinLedger.Musig2.findActiveEntry idMatchBytes sid entries =
        entries.find? (fun p => InternalSpec.Musig2.sessionIdPrefixEq idMatchBytes p.1 sid)
  | [] => rfl
  | p :: rest => by
    simp only [BitcoinLedger.Musig2.findActiveEntry, List.find?, sessionIdPrefixEq_eq]
    cases InternalSpec.Musig2.sessionIdPrefixEq idMatchBytes p.1 sid <;>
      simp [findActiveEntry_eq idMatchBytes sid rest]

theorem lookupActive_refines_spec (store : MusigSessionStore) (sid : PsbtSessionId) :
    BitcoinLedger.Musig2.lookupActive store sid = store.lookupActive sid := by
  unfold BitcoinLedger.Musig2.lookupActive MusigSessionStore.lookupActive
  rw [findActiveEntry_eq]
  rfl

theorem sessionStatus_refines_spec (store : MusigSessionStore) (sid : PsbtSessionId) :
    BitcoinLedger.Musig2.sessionStatus store sid = store.status sid := by
  unfold BitcoinLedger.Musig2.sessionStatus MusigSessionStore.status
  rw [lookupActive_refines_spec]
  rfl

theorem trimToCapacity_eq (cap : Option Nat) (entries : List (PsbtSessionId × RandRoot)) :
    BitcoinLedger.Musig2.trimToCapacity cap entries = InternalSpec.Musig2.trimToCapacity cap entries := by
  cases cap with
  | none => rfl
  | some m =>
    cases m with
    | zero => rfl
    | succ k =>
      unfold BitcoinLedger.Musig2.trimToCapacity InternalSpec.Musig2.trimToCapacity
      by_cases hLe : entries.length ≤ k + 1 <;> simp [hLe]

theorem filterOutMatchingSid_eq (idMatchBytes : Nat) (sid : PsbtSessionId) :
    ∀ entries : List (PsbtSessionId × RandRoot),
      BitcoinLedger.Musig2.filterOutMatchingSid idMatchBytes sid entries =
        entries.filter (fun p => !InternalSpec.Musig2.sessionIdPrefixEq idMatchBytes p.1 sid)
  | [] => rfl
  | p :: rest => by
    simp only [BitcoinLedger.Musig2.filterOutMatchingSid, List.filter, sessionIdPrefixEq_eq]
    cases (!InternalSpec.Musig2.sessionIdPrefixEq idMatchBytes p.1 sid) <;>
      simp [filterOutMatchingSid_eq idMatchBytes sid rest]

theorem registerRound1_refines_spec (store : MusigSessionStore)
    (sid : PsbtSessionId) (randRoot : RandRoot) :
    BitcoinLedger.Musig2.registerRound1 store sid randRoot =
      store.registerRound1 sid randRoot := by
  unfold BitcoinLedger.Musig2.registerRound1 MusigSessionStore.registerRound1
  dsimp only
  rw [isAllZeros_eq, isAllZeros_eq, isRandRootConsumed_eq, filterOutMatchingSid_eq, trimToCapacity_eq]

theorem consumeRound2_refines_spec (store : MusigSessionStore) (sid : PsbtSessionId) :
    BitcoinLedger.Musig2.consumeRound2 store sid = store.consumeRound2 sid := by
  unfold BitcoinLedger.Musig2.consumeRound2 MusigSessionStore.consumeRound2
  rw [findActiveEntry_eq]
  cases store.activeEntries.find? (fun p => InternalSpec.Musig2.sessionIdPrefixEq store.idMatchBytes p.1 sid) with
  | none => rfl
  | some pair =>
    rcases pair with ⟨_, rr⟩
    dsimp only
    rw [isRandRootConsumed_eq, filterOutMatchingSid_eq]

theorem evictUnconsumed_refines_spec (store : MusigSessionStore) (sid : PsbtSessionId) :
    BitcoinLedger.Musig2.evictUnconsumed store sid = store.evictUnconsumed sid := by
  unfold BitcoinLedger.Musig2.evictUnconsumed MusigSessionStore.evictUnconsumed
  rw [filterOutMatchingSid_eq]

theorem distinctTaskCoordinates_eq :
    ∀ cs, BitcoinLedger.Musig2.distinctTaskCoordinates cs = InternalSpec.Musig2.distinctTaskCoordinates cs
  | [] => rfl
  | c :: cs => by
    simp only [BitcoinLedger.Musig2.distinctTaskCoordinates, InternalSpec.Musig2.distinctTaskCoordinates,
      listMem_eq, distinctTaskCoordinates_eq cs]

theorem round1ProduceTaskNonce_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (task : MusigSignTask) :
    BitcoinLedger.Musig2.round1ProduceTaskNonce c mode randRoot task =
      InternalSpec.Musig2.round1ProduceTaskNonce c mode randRoot task := by
  unfold BitcoinLedger.Musig2.round1ProduceTaskNonce InternalSpec.Musig2.round1ProduceTaskNonce
  cases task.sortedPubkeys.isEmpty with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hMax : BitcoinLedger.Musig2.maxPubkeysPerMusig = InternalSpec.Musig2.maxPubkeysPerMusig := rfl
    rw [hMax]
    by_cases hGt : task.sortedPubkeys.length > InternalSpec.Musig2.maxPubkeysPerMusig
    · simp [hGt]
    · simp only [hGt, decide_false, ↓reduceIte]
      rw [syntheticRandIJ_refines_spec, selectNonceAggPk_refines_spec, nonceGen_refines_spec]
      cases InternalSpec.Musig2.nonceGen c
        (InternalSpec.Musig2.syntheticRandIJ c randRoot task.inputIndex task.placeholderIndex)
        task.internalPk (InternalSpec.Musig2.selectNonceAggPk mode task.untweakedAggPk task.tweakedAggPk) <;> rfl

theorem mapM_congr_except {α β ε : Type} {f g : α → Except ε β} (hfg : ∀ x, f x = g x) :
    ∀ xs : List α, xs.mapM f = xs.mapM g := by
  have hFun : f = g := funext hfg
  rw [hFun]
  intro _
  rfl

theorem executeRound1Pass_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (freshRandRoot : RandRoot) (tasks : List MusigSignTask) :
    BitcoinLedger.Musig2.executeRound1Pass c mode store sid freshRandRoot tasks =
      InternalSpec.Musig2.executeRound1Pass c mode store sid freshRandRoot tasks := by
  unfold BitcoinLedger.Musig2.executeRound1Pass InternalSpec.Musig2.executeRound1Pass
  dsimp only
  rw [isAllZeros_eq, isAllZeros_eq, isRandRootConsumed_eq,
      evictUnconsumed_refines_spec, distinctTaskCoordinates_eq,
      mapM_congr_except (round1ProduceTaskNonce_refines_spec c mode freshRandRoot) tasks]
  cases (sid.isAllZeros || freshRandRoot.isAllZeros || store.isRandRootConsumed freshRandRoot) with
  | true => rfl
  | false =>
    cases (!InternalSpec.Musig2.distinctTaskCoordinates (tasks.map (fun t => (t.inputIndex, t.placeholderIndex, t.internalPk)))) with
    | true => rfl
    | false =>
      cases tasks.mapM (InternalSpec.Musig2.round1ProduceTaskNonce c mode freshRandRoot) with
      | error err => rfl
      | ok outputs =>
        dsimp only
        rw [registerRound1_refines_spec]
        rfl

theorem round2SignTask_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (inp : MusigRound2TaskInput)
    (checkSelfPubnonce : Bool) :
    BitcoinLedger.Musig2.round2SignTask c mode randRoot inp checkSelfPubnonce =
      InternalSpec.Musig2.round2SignTask c mode randRoot inp checkSelfPubnonce := by
  unfold BitcoinLedger.Musig2.round2SignTask InternalSpec.Musig2.round2SignTask
  cases inp.task.sortedPubkeys.isEmpty with
  | true => rfl
  | false =>
    dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hMax : BitcoinLedger.Musig2.maxPubkeysPerMusig = InternalSpec.Musig2.maxPubkeysPerMusig := rfl
    rw [hMax]
    by_cases hGt : inp.task.sortedPubkeys.length > InternalSpec.Musig2.maxPubkeysPerMusig
    · simp [hGt]
    · simp only [hGt, decide_false, ↓reduceIte]
      cases inp.psbtMyPubnonce with
      | none => rfl
      | some myPn =>
        dsimp only [Bind.bind, Except.bind]
        rw [nat_bne_eq_decide_ne]
        cases decide (inp.cosignerPubnonces.length ≠ inp.task.sortedPubkeys.length) with
        | true => rfl
        | false =>
          rw [nonceAgg_refines_spec]
          cases InternalSpec.Musig2.nonceAgg c inp.cosignerPubnonces with
          | error e => rfl
          | ok aggnonce =>
            dsimp only [Bind.bind, Except.bind]
            rw [syntheticRandIJ_refines_spec, selectNonceAggPk_refines_spec, nonceGen_refines_spec]
            cases InternalSpec.Musig2.nonceGen c
              (InternalSpec.Musig2.syntheticRandIJ c randRoot inp.task.inputIndex inp.task.placeholderIndex)
              inp.task.internalPk
              (InternalSpec.Musig2.selectNonceAggPk mode inp.task.untweakedAggPk inp.task.tweakedAggPk) with
            | error e => rfl
            | ok pair =>
              rcases pair with ⟨secnonce, recomputedPn⟩
              dsimp only [Bind.bind, Except.bind]
              cases (checkSelfPubnonce && decide (recomputedPn ≠ myPn)) with
              | true => rfl
              | false =>
                rw [partialSign_refines_spec]
                cases InternalSpec.Musig2.partialSign c secnonce inp.secretKey
                  { aggnonce := aggnonce
                    pubkeys := inp.task.sortedPubkeys
                    tweaks := inp.task.tweaks
                    msg := inp.sighash.bytes } <;> rfl

theorem executeRound2Pass_refines_spec {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store : MusigSessionStore)
    (sid : PsbtSessionId) (inputs : List MusigRound2TaskInput)
    (checkSelfPubnonce : Bool) :
    BitcoinLedger.Musig2.executeRound2Pass c mode store sid inputs checkSelfPubnonce =
      InternalSpec.Musig2.executeRound2Pass c mode store sid inputs checkSelfPubnonce := by
  unfold BitcoinLedger.Musig2.executeRound2Pass InternalSpec.Musig2.executeRound2Pass
  rw [consumeRound2_refines_spec]
  cases store.consumeRound2 sid with
  | error err => rfl
  | ok pair =>
    rcases pair with ⟨rr, consumedStore⟩
    dsimp only
    rw [distinctTaskCoordinates_eq,
        mapM_congr_except (fun inp => round2SignTask_refines_spec c mode rr inp checkSelfPubnonce) inputs]
    rfl

theorem stepMusigOp_refines_spec {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (store : MusigSessionStore) (op : MusigOp) (checkSelfPubnonce : Bool) :
    BitcoinLedger.Musig2.stepMusigOp c mode store op checkSelfPubnonce =
      InternalSpec.Musig2.stepMusigOp c mode store op checkSelfPubnonce := by
  cases op with
  | round1 sid freshRand tasks =>
    simp only [BitcoinLedger.Musig2.stepMusigOp, InternalSpec.Musig2.stepMusigOp, executeRound1Pass_refines_spec]
    rfl
  | round2 sid inputs =>
    simp only [BitcoinLedger.Musig2.stepMusigOp, InternalSpec.Musig2.stepMusigOp,
      lookupActive_refines_spec, executeRound2Pass_refines_spec]
    rfl
  | evict sid =>
    simp only [BitcoinLedger.Musig2.stepMusigOp, InternalSpec.Musig2.stepMusigOp, evictUnconsumed_refines_spec]

theorem runMusigTrace_refines_spec {Affine : Type} (c : MusigCrypto Affine) (mode : NonceAggPkMode)
    (checkSelfPubnonce : Bool) :
    ∀ (ops : List MusigOp) (store : MusigSessionStore),
      BitcoinLedger.Musig2.runMusigTrace c mode store ops checkSelfPubnonce =
        InternalSpec.Musig2.runMusigTrace c mode store ops checkSelfPubnonce
  | [], _ => rfl
  | op :: restOps, store => by
    simp only [BitcoinLedger.Musig2.runMusigTrace, InternalSpec.Musig2.runMusigTrace, stepMusigOp_refines_spec]
    cases InternalSpec.Musig2.stepMusigOp c mode store op checkSelfPubnonce with
    | mk ev store' =>
      simp only [runMusigTrace_refines_spec c mode checkSelfPubnonce restOps store']

/-! ## 5. Security Theorems on `BitcoinLedger.Musig2` -/

/-- **Single-Use Nonce Linearity / Anti-Replay on `BitcoinLedger.Musig2`**:
    Across any arbitrary sequence of Round-1, Round-2, and eviction operations `ops`,
    every `RandRoot` produces Round-2 partial signatures at most once. -/
theorem impl_musig_nonce_single_use_linearity {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (rr : RandRoot) (checkSelfPubnonce : Bool := true)
    (ops : List MusigOp) (store : MusigSessionStore) :
    countRound2SuccessForRandRoot rr
      (BitcoinLedger.Musig2.runMusigTrace c mode store ops checkSelfPubnonce).1 ≤ 1 := by
  rw [runMusigTrace_refines_spec]
  exact InternalSpec.Musig2.musig_nonce_single_use_linearity c mode rr checkSelfPubnonce ops store

/-- **Immediate Round-2 Replay Rejection**:
    Any immediate Round-2 replay on `sid` after a successful `BitcoinLedger.Musig2.executeRound2Pass`
    is rejected with `.missingSession`. -/
theorem impl_round2_replay_rejected_missingSession {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (store store' : MusigSessionStore)
    (sid : PsbtSessionId) (inputs replayInputs : List MusigRound2TaskInput)
    (checkSelfPubnonce replayCheck : Bool) (sigs : List MusigRound2Output)
    (hOk : BitcoinLedger.Musig2.executeRound2Pass c mode store sid inputs checkSelfPubnonce = .ok (sigs, store')) :
    BitcoinLedger.Musig2.executeRound2Pass c mode store' sid replayInputs replayCheck =
      .error (.missingSession, store') := by
  rw [executeRound2Pass_refines_spec] at hOk ⊢
  exact InternalSpec.Musig2.round2_replay_without_round1_missingSession
    c mode store store' sid inputs replayInputs checkSelfPubnonce replayCheck sigs hOk

/-- **Self-Pubnonce Mismatch Rejection**:
    When `checkSelfPubnonce = true` (mandatory on BOLOS), `BitcoinLedger.Musig2.round2SignTask`
    rejects any mismatched `psbtMyPubnonce` with `.pubnonceMismatch` before emitting any signature. -/
theorem impl_round2SignTask_rejects_mismatched_self_pubnonce {Affine : Type} (c : MusigCrypto Affine)
    (mode : NonceAggPkMode) (randRoot : RandRoot) (inp : MusigRound2TaskInput)
    (myPn recomputedPn aggnonce : PubNonce) (sec : SecNonce)
    (hNonEmpty : inp.task.sortedPubkeys.isEmpty = false)
    (hBound : !(inp.task.sortedPubkeys.length > maxPubkeysPerMusig))
    (hMyPn : inp.psbtMyPubnonce = some myPn)
    (hLen : inp.cosignerPubnonces.length = inp.task.sortedPubkeys.length)
    (hAgg : BitcoinLedger.Musig2.nonceAgg c inp.cosignerPubnonces = .ok aggnonce)
    (hGen : BitcoinLedger.Musig2.nonceGen c
              (BitcoinLedger.Musig2.syntheticRandIJ c randRoot inp.task.inputIndex inp.task.placeholderIndex)
              inp.task.internalPk
              (BitcoinLedger.Musig2.selectNonceAggPk mode inp.task.untweakedAggPk inp.task.tweakedAggPk)
            = .ok (sec, recomputedPn))
    (hMismatch : recomputedPn ≠ myPn) :
    BitcoinLedger.Musig2.round2SignTask c mode randRoot inp true = .error .pubnonceMismatch := by
  rw [round2SignTask_refines_spec]
  rw [nonceAgg_refines_spec] at hAgg
  rw [nonceGen_refines_spec, syntheticRandIJ_refines_spec, selectNonceAggPk_refines_spec] at hGen
  exact InternalSpec.Musig2.round2SignTask_rejects_mismatched_self_pubnonce
    c mode randRoot inp myPn recomputedPn aggnonce sec hNonEmpty hBound hMyPn hLen hAgg hGen hMismatch

/-- **Re-Registration After Round-2 Completion & Replay Rejection Witness**:
    On `BitcoinLedger.Musig2`, Round 1 -> Round 2 succeeds, immediate Round-2 replay fails with
    `.missingSession`, and a fresh Round 1 on the SAME `sid` with a fresh `RandRoot` succeeds
    followed by a second Round 2 pass! -/
theorem impl_re_registration_after_round2_completion :
    ∃ (sid : PsbtSessionId) (rr1 rr2 : RandRoot)
      (t1 : MusigSignTask) (t2 : MusigRound2TaskInput)
      (r1Out : List MusigRound1Output) (s1 : MusigSessionStore)
      (r2Out : List MusigRound2Output) (s2 : MusigSessionStore)
      (r1Out2 : List MusigRound1Output) (s3 : MusigSessionStore)
      (r2Out2 : List MusigRound2Output) (s4 : MusigSessionStore),
      BitcoinLedger.Musig2.executeRound1Pass nonVacuousToyCrypto .untweakedBolos
        BitcoinLedger.Musig2.bolosDefaultStore sid rr1 [t1] = .ok (r1Out, s1) ∧
      r1Out.length = 1 ∧
      BitcoinLedger.Musig2.executeRound2Pass nonVacuousToyCrypto .untweakedBolos
        s1 sid [t2] = .ok (r2Out, s2) ∧
      r2Out.length = 1 ∧
      BitcoinLedger.Musig2.executeRound2Pass nonVacuousToyCrypto .untweakedBolos
        s2 sid [t2] = .error (.missingSession, s2) ∧
      BitcoinLedger.Musig2.executeRound1Pass nonVacuousToyCrypto .untweakedBolos
        s2 sid rr2 [t1] = .ok (r1Out2, s3) ∧
      BitcoinLedger.Musig2.executeRound2Pass nonVacuousToyCrypto .untweakedBolos
        s3 sid [t2] = .ok (r2Out2, s4) ∧
      r2Out2.length = 1 := by
  rcases InternalSpec.Musig2.nonvacuous_round1_then_round2_and_replay_rejected with
    ⟨sid, rr1, rr2, t1, t2, r1Out, s1, r2Out, s2, r1Out2, s3, r2Out2, s4,
     h1, hLen1, h2, hLen2, hRep, h3, h4, hLen4⟩
  refine ⟨sid, rr1, rr2, t1, t2, r1Out, s1, r2Out, s2, r1Out2, s3, r2Out2, s4, ?_⟩
  rw [bolosDefaultStore_eq,
      executeRound1Pass_refines_spec,
      executeRound2Pass_refines_spec,
      executeRound2Pass_refines_spec,
      executeRound1Pass_refines_spec,
      executeRound2Pass_refines_spec]
  exact ⟨h1, hLen1, h2, hLen2, hRep, h3, h4, hLen4⟩

end Proofs.Musig2


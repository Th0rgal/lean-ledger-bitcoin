import Spec
import BitcoinLedger.Basic
import BitcoinLedger.Script
import Proofs.Basic

namespace Proofs.Script

/-!
# `Proofs.Script` — Refinement, Roundtrip & Segregation Proofs for `BitcoinLedger.Script`

Constructive (`0 Classical.choice`, `0 sorryAx`, `0 native_decide`) refinement theorems connecting
`BitcoinLedger.Script` to `Spec.Script`:
1. Witness version opcode codec & standard script constructors/classifier equivalence & roundtrips
   (`P2PKH`, `P2SH`, `P2WPKH`, `P2WSH`, `P2TR`, `UnknownWitness` `v0..v16`, `OpReturn`)
2. `MINIMALDATA` pushdata encoder/decoder equivalence, canonicality soundness (`isMinimalPush`),
   streaming prefix roundtrip (`decodeMinimalPushPrefix? (enc ++ tail)`), and `OP_RETURN` canonicality
3. Base58 & Base58Check equivalence with `Spec.Script`
4. BIP-173 / BIP-350 Bech32 vs Bech32m polymod & raw codec equivalence, **universal 8↔5 bit conversion
   roundtrip** (`convertBits5to8? (convertBits8to5 bs) = some bs` for ALL `ByteArray`), SegWit
   witness-version segregation (`v0 ↔ Bech32` 20/32B; `v1..v16 ↔ Bech32m` 2..40B), target-aware
   `scriptToAddress?` equivalence, and concrete official BIP-173/BIP-350 witnesses
-/

open BitcoinLedger.Script

/-! ## 1. Witness Version Opcodes & Standard Script Constructors / Classifier -/

theorem encodeWitnessVersionOpcode?_eq (ver : UInt8) :
    BitcoinLedger.Script.encodeWitnessVersionOpcode? ver = Spec.encodeWitnessVersionOpcode? ver := by
  unfold BitcoinLedger.Script.encodeWitnessVersionOpcode? Spec.encodeWitnessVersionOpcode?
  unfold OP_0 Spec.OP_0
  cases h0 : decide (ver = 0)
  · have hn0 := of_decide_eq_false h0
    simp only [Bool.false_eq_true, hn0, ↓reduceIte]
    cases h16 : decide (ver ≤ 16)
    · have hn16 := of_decide_eq_false h16
      simp [hn16]
    · have hy16 := of_decide_eq_true h16
      simp [hy16]
  · have hy0 := of_decide_eq_true h0
    simp [hy0]

theorem decodeWitnessVersionOpcode?_eq (op : UInt8) :
    BitcoinLedger.Script.decodeWitnessVersionOpcode? op = Spec.decodeWitnessVersionOpcode? op := by
  unfold BitcoinLedger.Script.decodeWitnessVersionOpcode? Spec.decodeWitnessVersionOpcode?
  unfold OP_0 Spec.OP_0 OP_1 Spec.OP_1 OP_16 Spec.OP_16
  cases h0 : decide (op = 0)
  · have hn0 := of_decide_eq_false h0
    simp [hn0]
  · have hy0 := of_decide_eq_true h0
    simp [hy0]

theorem decode_encodeWitnessVersionOpcode {ver op : UInt8}
    (h : BitcoinLedger.Script.encodeWitnessVersionOpcode? ver = some op) :
    BitcoinLedger.Script.decodeWitnessVersionOpcode? op = some ver := by
  unfold BitcoinLedger.Script.encodeWitnessVersionOpcode? at h
  cases hv0 : decide (ver = 0)
  · rw [hv0] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hv16 : decide (ver ≤ 16)
    · rw [hv16] at h
      cases h
    · rw [hv16] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      have hn0 : ver ≠ 0 := of_decide_eq_false hv0
      have hle16 : ver.toNat ≤ 16 := UInt8.le_iff_toNat_le.mp (of_decide_eq_true hv16)
      have hge1 : 1 ≤ ver.toNat := by
        cases hvn : ver.toNat with
        | zero => exfalso; exact hn0 (UInt8.toNat_inj.mp hvn)
        | succ m => exact Nat.succ_le_succ (Nat.zero_le m)
      have hsumLt : 80 + ver.toNat < 256 :=
        Nat.lt_of_le_of_lt (Nat.add_le_add_left hle16 80) (by decide)
      have hopNat : ((0x50 : UInt8) + ver).toNat = 80 + ver.toNat := by
        rw [UInt8.toNat_add]
        change (80 + ver.toNat) % 256 = 80 + ver.toNat
        exact Nat.mod_eq_of_lt hsumLt
      unfold BitcoinLedger.Script.decodeWitnessVersionOpcode? OP_0 OP_1 OP_16
      have hd0 : decide ((0x50 : UInt8) + ver = 0) = false := by
        apply decide_eq_false
        intro heq
        have htn := congrArg UInt8.toNat heq
        rw [hopNat] at htn
        change 80 + ver.toNat = 0 at htn
        exact absurd (by rw [← htn]; exact Nat.le_add_right 80 _ : 80 ≤ 0) (by decide)
      have hd1 : decide ((0x51 : UInt8) ≤ (0x50 : UInt8) + ver) = true := by
        apply decide_eq_true
        rw [UInt8.le_iff_toNat_le, hopNat]
        exact Nat.add_le_add_left hge1 80
      have hd16 : decide ((0x50 : UInt8) + ver ≤ 0x60) = true := by
        apply decide_eq_true
        rw [UInt8.le_iff_toNat_le, hopNat]
        exact Nat.add_le_add_left hle16 80
      rw [hd0, hd1, hd16]
      simp only [Bool.false_eq_true, Bool.and_self, ↓reduceIte, Option.some.injEq]
      apply UInt8.toNat_inj.mp
      have hle80 : (0x50 : UInt8) ≤ (0x50 : UInt8) + ver := by
        rw [UInt8.le_iff_toNat_le, hopNat]
        exact Nat.le_add_right 80 ver.toNat
      rw [UInt8.toNat_sub_of_le _ _ hle80, hopNat]
      change (80 + ver.toNat) - 80 = ver.toNat
      exact Nat.add_sub_cancel_left 80 ver.toNat
  · have hy0 := of_decide_eq_true hv0
    subst hy0
    simp only [decide_true, ↓reduceIte, Option.some.injEq] at h
    subst h
    rfl

theorem mkP2PKH_eq (h : ByteArray) : BitcoinLedger.Script.mkP2PKH h = Spec.mkP2PKH h := rfl
theorem mkP2SH_eq (h : ByteArray) : BitcoinLedger.Script.mkP2SH h = Spec.mkP2SH h := rfl
theorem mkP2WPKH_eq (h : ByteArray) : BitcoinLedger.Script.mkP2WPKH h = Spec.mkP2WPKH h := rfl
theorem mkP2WSH_eq (h : ByteArray) : BitcoinLedger.Script.mkP2WSH h = Spec.mkP2WSH h := rfl
theorem mkP2TR_eq (k : ByteArray) : BitcoinLedger.Script.mkP2TR k = Spec.mkP2TR k := rfl

theorem standardScriptToPubKey_eq (sc : StandardScript) :
    standardScriptToPubKey sc = sc.toScriptPubKey := by
  cases sc with
  | p2pkh _ | p2sh _ | p2wpkh _ | p2wsh _ | p2tr _ | opReturn _ => rfl
  | unknownWitness v prog =>
      unfold standardScriptToPubKey Spec.StandardScript.toScriptPubKey OP_0 Spec.OP_0
      cases hv0 : decide (v = 0)
      · have hn0 := of_decide_eq_false hv0
        simp [hn0]
      · have hy0 := of_decide_eq_true hv0
        simp [hy0]

private theorem classifyP2PKHRest_eq (rest : List UInt8) :
    (if decide (rest.length = 22) = true then
       if BitcoinLedger.Basic.eqByteList (rest.drop 20) [0x88, 0xAC] = true then
         some (Spec.StandardScript.p2pkh (ByteArray.mk (rest.take 20).toArray))
       else none
     else none) =
    (if rest.length = 22 then
       if rest.drop 20 = [0x88, 0xAC] then
         some (Spec.StandardScript.p2pkh (ByteArray.mk (rest.take 20).toArray))
       else none
     else none) := by
  cases hl : decide (rest.length = 22)
  · have hnl := of_decide_eq_false hl
    simp [hnl]
  · have hyl := of_decide_eq_true hl
    simp only [hyl, ↓reduceIte]
    cases hs : BitcoinLedger.Basic.eqByteList (rest.drop 20) [0x88, 0xAC]
    · have hns : rest.drop 20 ≠ [0x88, 0xAC] := fun heq => by
        have ht := (Proofs.Basic.eqByteList_iff _ _).mpr heq
        rw [hs] at ht; cases ht
      simp [hns]
    · have hys : rest.drop 20 = [0x88, 0xAC] := (Proofs.Basic.eqByteList_iff _ _).mp hs
      simp [hys]

private theorem classifyP2SHRest_eq (rest : List UInt8) :
    (if decide (rest.length = 21) = true then
       if BitcoinLedger.Basic.eqByteList (rest.drop 20) [0x87] = true then
         some (Spec.StandardScript.p2sh (ByteArray.mk (rest.take 20).toArray))
       else none
     else none) =
    (if rest.length = 21 then
       if rest.drop 20 = [0x87] then
         some (Spec.StandardScript.p2sh (ByteArray.mk (rest.take 20).toArray))
       else none
     else none) := by
  cases hl : decide (rest.length = 21)
  · have hnl := of_decide_eq_false hl
    simp [hnl]
  · have hyl := of_decide_eq_true hl
    simp only [hyl, ↓reduceIte]
    cases hs : BitcoinLedger.Basic.eqByteList (rest.drop 20) [0x87]
    · have hns : rest.drop 20 ≠ [0x87] := fun heq => by
        have ht := (Proofs.Basic.eqByteList_iff _ _).mpr heq
        rw [hs] at ht; cases ht
      simp [hns]
    · have hys : rest.drop 20 = [0x87] := (Proofs.Basic.eqByteList_iff _ _).mp hs
      simp [hys]

private theorem classifyWitnessArm_eq (op pushLen : UInt8) (prog : List UInt8) :
    (match BitcoinLedger.Script.decodeWitnessVersionOpcode? op with
     | none => none
     | some ver =>
         if (decide (pushLen.toNat = prog.length) && decide (2 ≤ prog.length) && decide (prog.length ≤ 40)) = true then
           let progBytes := ByteArray.mk prog.toArray
           if (decide (ver = 0) && decide (prog.length = 20)) = true then some (Spec.StandardScript.p2wpkh progBytes)
           else if (decide (ver = 0) && decide (prog.length = 32)) = true then some (Spec.StandardScript.p2wsh progBytes)
           else if (decide (ver = 1) && decide (prog.length = 32)) = true then some (Spec.StandardScript.p2tr progBytes)
           else some (Spec.StandardScript.unknownWitness ver progBytes)
         else none) =
    (match Spec.decodeWitnessVersionOpcode? op with
     | none => none
     | some ver =>
         if pushLen.toNat = prog.length ∧ 2 ≤ prog.length ∧ prog.length ≤ 40 then
           let progBytes := ByteArray.mk prog.toArray
           if ver = 0 ∧ prog.length = 20 then some (Spec.StandardScript.p2wpkh progBytes)
           else if ver = 0 ∧ prog.length = 32 then some (Spec.StandardScript.p2wsh progBytes)
           else if ver = 1 ∧ prog.length = 32 then some (Spec.StandardScript.p2tr progBytes)
           else some (Spec.StandardScript.unknownWitness ver progBytes)
         else none) := by
  rw [decodeWitnessVersionOpcode?_eq]
  cases Spec.decodeWitnessVersionOpcode? op with
  | none => rfl
  | some ver =>
      dsimp only
      cases c1 : decide (pushLen.toNat = prog.length)
      · have n1 := of_decide_eq_false c1
        simp [n1]
      · have y1 := of_decide_eq_true c1
        cases c2 : decide (2 ≤ prog.length)
        · have n2 := of_decide_eq_false c2
          simp [y1, n2]
        · have y2 := of_decide_eq_true c2
          cases c3 : decide (prog.length ≤ 40)
          · have n3 := of_decide_eq_false c3
            simp [y1, y2, n3]
          · have y3 := of_decide_eq_true c3
            simp only [Bool.true_and, y1, y2, y3, and_self, ↓reduceIte]
            cases v0 : decide (ver = 0)
            · have nv0 := of_decide_eq_false v0
              simp only [Bool.false_and, Bool.false_eq_true, nv0, false_and, ↓reduceIte]
              cases v1 : decide (ver = 1)
              · have nv1 := of_decide_eq_false v1
                simp [nv1]
              · have yv1 := of_decide_eq_true v1
                cases l32 : decide (prog.length = 32)
                · have nl32 := of_decide_eq_false l32
                  simp [yv1, nl32]
                · have yl32 := of_decide_eq_true v1
                  have yl32' := of_decide_eq_true l32
                  simp [yv1, yl32']
            · have yv0 := of_decide_eq_true v0
              subst yv0
              cases l20 : decide (prog.length = 20)
              · have nl20 := of_decide_eq_false l20
                cases l32 : decide (prog.length = 32)
                · have nl32 := of_decide_eq_false l32
                  simp [nl20, nl32]
                · have yl32 := of_decide_eq_true l32
                  simp [yl32]
              · have yl20 := of_decide_eq_true l20
                simp [yl20]

/-- Executable `classifyScript?` refines `Spec.classifyScript?` for all `ByteArray` inputs. -/
theorem classifyScript?_eq (script : ByteArray) :
    BitcoinLedger.Script.classifyScript? script = Spec.classifyScript? script := by
  unfold BitcoinLedger.Script.classifyScript? Spec.classifyScript?
  cases hlist : script.data.toList with
  | nil => rfl
  | cons b0 tail0 =>
      cases h6a : decide (b0 = 0x6A)
      · have hn6a : b0 ≠ 0x6A := of_decide_eq_false h6a
        cases tail0 with
        | nil =>
            simp [hn6a]
        | cons b1 tail1 =>
            cases h76 : decide (b0 = 0x76)
            · have hn76 : b0 ≠ 0x76 := of_decide_eq_false h76
              cases ha9 : decide (b0 = 0xA9)
              · have hna9 : b0 ≠ 0xA9 := of_decide_eq_false ha9
                simp [hn76, hna9, decodeWitnessVersionOpcode?_eq, and_assoc]
                rfl
              · have hya9 : b0 = 0xA9 := of_decide_eq_true ha9
                subst hya9
                cases h14 : decide (b1 = 0x14)
                · have hn14 : b1 ≠ 0x14 := of_decide_eq_false h14
                  simp [hn14, decodeWitnessVersionOpcode?_eq, and_assoc]
                  rfl
                · have hy14 : b1 = 0x14 := of_decide_eq_true h14
                  subst hy14
                  exact classifyP2SHRest_eq tail1
            · have hy76 : b0 = 0x76 := of_decide_eq_true h76
              subst hy76
              cases hb1 : decide (b1 = 0xA9)
              · have hnb1 : b1 ≠ 0xA9 := of_decide_eq_false hb1
                simp [hnb1, decodeWitnessVersionOpcode?_eq, and_assoc]
                rfl
              · have hyb1 : b1 = 0xA9 := of_decide_eq_true hb1
                subst hyb1
                cases tail1 with
                | nil => exact classifyWitnessArm_eq 0x76 0xA9 []
                | cons b2 tail2 =>
                    cases hb2 : decide (b2 = 0x14)
                    · have hnb2 : b2 ≠ 0x14 := of_decide_eq_false hb2
                      simp [hnb2, decodeWitnessVersionOpcode?_eq, and_assoc]
                      rfl
                    · have hyb2 : b2 = 0x14 := of_decide_eq_true hb2
                      subst hyb2
                      exact classifyP2PKHRest_eq tail2
      · have hy6a : b0 = 0x6A := of_decide_eq_true h6a
        subst hy6a
        rfl

theorem classifyScript?_mkP2PKH {h : ByteArray} (h20 : BitcoinLedger.Basic.isBytes20 h = true) :
    BitcoinLedger.Script.classifyScript? (BitcoinLedger.Script.mkP2PKH h) =
      some (Spec.StandardScript.p2pkh h) := by
  rw [classifyScript?_eq, mkP2PKH_eq]
  exact Spec.classifyScript?_mkP2PKH ((Proofs.Basic.isBytes20_iff h).mp h20)

theorem classifyScript?_mkP2SH {h : ByteArray} (h20 : BitcoinLedger.Basic.isBytes20 h = true) :
    BitcoinLedger.Script.classifyScript? (BitcoinLedger.Script.mkP2SH h) =
      some (Spec.StandardScript.p2sh h) := by
  rw [classifyScript?_eq, mkP2SH_eq]
  exact Spec.classifyScript?_mkP2SH ((Proofs.Basic.isBytes20_iff h).mp h20)

theorem classifyScript?_mkP2WPKH {h : ByteArray} (h20 : BitcoinLedger.Basic.isBytes20 h = true) :
    BitcoinLedger.Script.classifyScript? (BitcoinLedger.Script.mkP2WPKH h) =
      some (Spec.StandardScript.p2wpkh h) := by
  rw [classifyScript?_eq, mkP2WPKH_eq]
  exact Spec.classifyScript?_mkP2WPKH ((Proofs.Basic.isBytes20_iff h).mp h20)

theorem classifyScript?_mkP2WSH {h : ByteArray} (h32 : BitcoinLedger.Basic.isBytes32 h = true) :
    BitcoinLedger.Script.classifyScript? (BitcoinLedger.Script.mkP2WSH h) =
      some (Spec.StandardScript.p2wsh h) := by
  rw [classifyScript?_eq, mkP2WSH_eq]
  exact Spec.classifyScript?_mkP2WSH ((Proofs.Basic.isBytes32_iff h).mp h32)

theorem classifyScript?_mkP2TR {k : ByteArray} (h32 : BitcoinLedger.Basic.isBytes32 k = true) :
    BitcoinLedger.Script.classifyScript? (BitcoinLedger.Script.mkP2TR k) =
      some (Spec.StandardScript.p2tr k) := by
  rw [classifyScript?_eq, mkP2TR_eq]
  exact Spec.classifyScript?_mkP2TR ((Proofs.Basic.isBytes32_iff k).mp h32)

/-! ## 2. `MINIMALDATA` Pushdata Soundness, Roundtrip & `OP_RETURN` Canonicality -/

theorem minimalScriptNumPushSize_eq (n : UInt32) :
    BitcoinLedger.Script.minimalScriptNumPushSize n = Spec.minimalScriptNumPushSize n := by
  unfold BitcoinLedger.Script.minimalScriptNumPushSize Spec.minimalScriptNumPushSize
  cases h1 : decide (n ≤ 16)
  · simp only [Bool.false_eq_true, of_decide_eq_false h1, ↓reduceIte]
    cases h2 : decide (n < 0x80)
    · simp only [Bool.false_eq_true, of_decide_eq_false h2, ↓reduceIte]
      cases h3 : decide (n < 0x8000)
      · simp only [Bool.false_eq_true, of_decide_eq_false h3, ↓reduceIte]
        cases h4 : decide (n < 0x800000)
        · simp only [Bool.false_eq_true, of_decide_eq_false h4, ↓reduceIte]
          cases h5 : decide (n < 0x80000000)
          · simp [of_decide_eq_false h5]
          · simp [of_decide_eq_true h5]
        · simp [of_decide_eq_true h4]
      · simp [of_decide_eq_true h3]
    · simp [of_decide_eq_true h2]
  · simp [of_decide_eq_true h1]

theorem encodeMinimalPush?_eq (payload : ByteArray) :
    BitcoinLedger.Script.encodeMinimalPush? payload = Spec.encodeMinimalPush? payload := by
  unfold BitcoinLedger.Script.encodeMinimalPush? Spec.encodeMinimalPush?
  unfold OP_0 Spec.OP_0 OP_1NEGATE Spec.OP_1NEGATE
  unfold OP_PUSHDATA1 Spec.OP_PUSHDATA1 OP_PUSHDATA2 Spec.OP_PUSHDATA2 OP_PUSHDATA4 Spec.OP_PUSHDATA4
  match payload.data.toList with
  | [] => rfl
  | [b] =>
      dsimp only
      cases hb81 : decide (b = 0x81)
      · simp [of_decide_eq_false hb81]
      · simp [of_decide_eq_true hb81]
  | _ :: _ :: _ =>
      dsimp only
      rw [Proofs.Basic.encodeU16LE_eq, Proofs.Basic.encodeU32LE_eq]
      cases c1 : decide (payload.size ≤ 75)
      · simp only [Bool.false_eq_true, of_decide_eq_false c1, ↓reduceIte]
        cases c2 : decide (payload.size ≤ 255)
        · simp only [Bool.false_eq_true, of_decide_eq_false c2, ↓reduceIte]
          cases c3 : decide (payload.size ≤ 65535)
          · simp only [Bool.false_eq_true, of_decide_eq_false c3, ↓reduceIte]
            cases c4 : decide (payload.size ≤ 0xFFFFFFFF)
            · simp [of_decide_eq_false c4]
            · simp [of_decide_eq_true c4]
          · simp [of_decide_eq_true c3]
        · simp [of_decide_eq_true c2]
      · simp [of_decide_eq_true c1]

theorem decodeMinimalPushPrefix?_eq (script : ByteArray) :
    BitcoinLedger.Script.decodeMinimalPushPrefix? script = Spec.decodeMinimalPushPrefix? script := by
  unfold BitcoinLedger.Script.decodeMinimalPushPrefix? Spec.decodeMinimalPushPrefix?
  unfold OP_0 Spec.OP_0 OP_1NEGATE Spec.OP_1NEGATE OP_1 Spec.OP_1 OP_16 Spec.OP_16
  unfold OP_PUSHDATA1 Spec.OP_PUSHDATA1 OP_PUSHDATA2 Spec.OP_PUSHDATA2 OP_PUSHDATA4 Spec.OP_PUSHDATA4
  match script.data.toList with
  | [] => rfl
  | op :: rest =>
      dsimp only
      cases c0 : decide (op = 0)
      · simp only [Bool.false_eq_true, of_decide_eq_false c0, ↓reduceIte]
        cases c1n : decide (op = 0x4F)
        · simp only [Bool.false_eq_true, of_decide_eq_false c1n, ↓reduceIte]
          cases csmall : (decide ((0x51 : UInt8) ≤ op) && decide (op ≤ 0x60))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases cop1 : decide (op = 1)
            · simp only [Bool.false_eq_true, of_decide_eq_false cop1, ↓reduceIte]
              cases cdir : (decide (2 ≤ op.toNat) && decide (op.toNat ≤ 75))
              · simp only [Bool.false_eq_true, ↓reduceIte]
                cases cpd1 : decide (op = 0x4C)
                · simp only [Bool.false_eq_true, of_decide_eq_false cpd1, ↓reduceIte]
                  cases cpd2 : decide (op = 0x4D)
                  · simp only [Bool.false_eq_true, of_decide_eq_false cpd2, ↓reduceIte]
                    cases cpd4 : decide (op = 0x4E)
                    · simp [of_decide_eq_false cpd4]
                    · simp only [of_decide_eq_true cpd4, ↓reduceIte]
                      match rest with
                      | b0 :: b1 :: b2 :: b3 :: tail => rfl
                      | [] | [_] | [_, _] | [_, _, _] => rfl
                  · simp only [of_decide_eq_true cpd2, ↓reduceIte]
                    match rest with
                    | b0 :: b1 :: tail => rfl
                    | [] | [_] => rfl
                · simp only [of_decide_eq_true cpd1, ↓reduceIte]
                  match rest with
                  | [] => rfl
                  | lenByte :: tail => rfl
              · simp only [↓reduceIte]
                cases clt : decide (rest.length < op.toNat)
                · simp [of_decide_eq_false clt]
                · simp [of_decide_eq_true clt]
            · simp only [of_decide_eq_true cop1, ↓reduceIte]
              match rest with
              | [] => rfl
              | b :: tail => rfl
          · rfl
        · simp [of_decide_eq_true c1n]
      · simp [of_decide_eq_true c0]

theorem checkMinimalPushesBounded_eq (budget : Nat) (bytes : List UInt8) :
    BitcoinLedger.Script.checkMinimalPushesBounded budget bytes =
      Spec.checkMinimalPushesBounded budget bytes := by
  induction budget generalizing bytes with
  | zero =>
      cases bytes <;> rfl
  | succ b ih =>
      cases bytes with
      | nil => rfl
      | cons x xs =>
          unfold BitcoinLedger.Script.checkMinimalPushesBounded Spec.checkMinimalPushesBounded
          rw [decodeMinimalPushPrefix?_eq]
          cases Spec.decodeMinimalPushPrefix? (ByteArray.mk (x :: xs).toArray) with
          | none => rfl
          | some pair => exact ih pair.2.data.toList

theorem isValidOpReturnScript_eq (script : ByteArray) :
    BitcoinLedger.Script.isValidOpReturnScript script = Spec.isValidOpReturnScript script := by
  unfold BitcoinLedger.Script.isValidOpReturnScript Spec.isValidOpReturnScript
  unfold MAX_STANDARD_OP_RETURN_LEN Spec.MAX_STANDARD_OP_RETURN_LEN
  unfold MAX_STANDARD_OP_RETURN_PUSHES Spec.MAX_STANDARD_OP_RETURN_PUSHES
  cases script.data.toList with
  | nil => simp
  | cons b0 tail =>
      cases hb : decide (b0 = 0x6A)
      · have hnb := of_decide_eq_false hb
        simp [hnb]
      · have hyb := of_decide_eq_true hb
        subst hyb
        simp [checkMinimalPushesBounded_eq]

/-- Soundness of `encodeMinimalPush?`: whenever `encodeMinimalPush? payload = some enc`,
    `Spec.isMinimalPush payload enc` holds! -/
theorem encodeMinimalPush?_sound {payload enc : ByteArray}
    (h : BitcoinLedger.Script.encodeMinimalPush? payload = some enc) :
    Spec.isMinimalPush payload enc := by
  unfold BitcoinLedger.Script.encodeMinimalPush? at h
  cases payload with
  | mk arr =>
      cases hl : arr.toList with
      | nil =>
          rw [hl] at h
          dsimp only at h
          injection h with hEq
          subst hEq
          left
          have hsz : (ByteArray.mk arr).size = 0 := by
            change arr.toList.length = 0
            rw [hl]; rfl
          exact ⟨hsz, rfl⟩
      | cons b0 rest0 =>
          cases rest0 with
          | nil =>
              rw [hl] at h
              dsimp only at h
              have hpEq : ByteArray.mk arr = ByteArray.mk #[b0] := by
                apply congrArg ByteArray.mk
                apply Array.ext'
                exact hl
              right; left
              refine ⟨b0, hpEq, ?_⟩
              cases c16 : (decide (1 ≤ b0.toNat) && decide (b0.toNat ≤ 16))
              · rw [c16] at h
                simp only [Bool.false_eq_true, ↓reduceIte] at h
                cases c81 : decide (b0 = 0x81)
                · rw [c81] at h
                  simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  right; right
                  refine ⟨?_, rfl⟩
                  have hn81 : b0 ≠ 0x81 := of_decide_eq_false c81
                  cases hb0 : decide (b0 = 0)
                  · right
                    refine ⟨?_, hn81⟩
                    have hne0 : b0.toNat ≠ 0 := fun hz => of_decide_eq_false hb0 (UInt8.toNat_inj.mp hz)
                    have hge1 : 1 ≤ b0.toNat := Nat.pos_of_ne_zero hne0
                    have hd1 : decide (1 ≤ b0.toNat) = true := decide_eq_true hge1
                    rw [hd1, Bool.true_and] at c16
                    exact Nat.lt_of_not_le (of_decide_eq_false c16)
                  · exact Or.inl (of_decide_eq_true hb0)
                · rw [c81] at h
                  simp only [↓reduceIte, Option.some.injEq] at h
                  subst h
                  exact Or.inr (Or.inl ⟨of_decide_eq_true c81, rfl⟩)
              · rw [c16] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                simp only [Bool.and_eq_true, decide_eq_true_iff] at c16
                exact Or.inl ⟨c16.1, c16.2, rfl⟩
          | cons b1 rest1 =>
              rw [hl] at h
              dsimp only at h
              have hge2 : 2 ≤ (ByteArray.mk arr).size := by
                change 2 ≤ arr.toList.length
                rw [hl]
                exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
              cases c75 : decide ((ByteArray.mk arr).size ≤ 75)
              · rw [c75] at h
                simp only [Bool.false_eq_true, ↓reduceIte] at h
                have hge76 : 76 ≤ (ByteArray.mk arr).size :=
                  Nat.lt_of_not_le (of_decide_eq_false c75)
                cases c255 : decide ((ByteArray.mk arr).size ≤ 255)
                · rw [c255] at h
                  simp only [Bool.false_eq_true, ↓reduceIte] at h
                  have hge256 : 256 ≤ (ByteArray.mk arr).size :=
                    Nat.lt_of_not_le (of_decide_eq_false c255)
                  cases c65k : decide ((ByteArray.mk arr).size ≤ 65535)
                  · rw [c65k] at h
                    simp only [Bool.false_eq_true, ↓reduceIte] at h
                    have hge65k : 65536 ≤ (ByteArray.mk arr).size :=
                      Nat.lt_of_not_le (of_decide_eq_false c65k)
                    cases c4g : decide ((ByteArray.mk arr).size ≤ 0xFFFFFFFF)
                    · rw [c4g] at h; cases h
                    · rw [c4g] at h
                      simp only [↓reduceIte, Option.some.injEq] at h
                      subst h
                      right; right; right; right; right
                      rw [Proofs.Basic.encodeU32LE_eq]
                      exact ⟨hge65k, of_decide_eq_true c4g, rfl⟩
                  · rw [c65k] at h
                    simp only [↓reduceIte, Option.some.injEq] at h
                    subst h
                    right; right; right; right; left
                    rw [Proofs.Basic.encodeU16LE_eq]
                    exact ⟨hge256, of_decide_eq_true c65k, rfl⟩
                · rw [c255] at h
                  simp only [↓reduceIte, Option.some.injEq] at h
                  subst h
                  right; right; right; left
                  exact ⟨hge76, of_decide_eq_true c255, rfl⟩
              · rw [c75] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                right; right; left
                exact ⟨hge2, of_decide_eq_true c75, rfl⟩

private theorem byteArray_toList_append (a b : ByteArray) :
    (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  cases a; cases b
  simp [ByteArray.data_append]

private theorem list_take_drop_prefix (p t : List UInt8) :
    (p ++ t).take p.length = p ∧ (p ++ t).drop p.length = t := by
  constructor
  · rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
  · rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length]
    rfl

/-- Compositional streaming prefix roundtrip theorem for `MINIMALDATA`:
    whenever `encodeMinimalPush? payload = some enc`, decoding `enc ++ tail` yields `some (payload, tail)`! -/
theorem decodeMinimalPushPrefix?_encodeMinimalPush? {payload enc : ByteArray} (tail : ByteArray)
    (henc : BitcoinLedger.Script.encodeMinimalPush? payload = some enc) :
    BitcoinLedger.Script.decodeMinimalPushPrefix? (enc ++ tail) = some (payload, tail) := by
  have hsound := encodeMinimalPush?_sound henc
  have htailMk : ByteArray.mk tail.data.toList.toArray = tail := by
    cases tail; rfl
  have hpayMk : ByteArray.mk payload.data.toList.toArray = payload := by
    cases payload; rfl
  have hpayLen : payload.data.toList.length = payload.size := rfl
  rcases hsound with h0 | h1 | h75 | h255 | h65k | h4g
  · rcases h0 with ⟨hsz, rfl⟩
    have hempty : payload = ByteArray.empty := by
      cases payload with
      | mk arr =>
          apply congrArg ByteArray.mk
          apply Array.ext'
          exact List.eq_nil_of_length_eq_zero hsz
    subst hempty
    unfold BitcoinLedger.Script.decodeMinimalPushPrefix? Spec.OP_0 OP_0
    rw [byteArray_toList_append]
    simp only [List.cons_append, List.nil_append]
    change (if decide ((0 : UInt8) = 0) = true then
              some (ByteArray.empty, ByteArray.mk tail.data.toList.toArray)
            else _) = some (ByteArray.empty, tail)
    rw [htailMk]
    rfl
  · rcases h1 with ⟨b, rfl, hb16 | hb81 | hbother⟩
    · rcases hb16 with ⟨hge1, hle16, rfl⟩
      unfold BitcoinLedger.Script.decodeMinimalPushPrefix?
      rw [byteArray_toList_append]
      simp only [List.cons_append, List.nil_append]
      let op := UInt8.ofNat (0x50 + b.toNat)
      have hopNat : op.toNat = 80 + b.toNat := by
        dsimp [op]
        rw [UInt8.toNat_ofNat']
        have hlt : 80 + b.toNat < 256 :=
          Nat.lt_of_le_of_lt (Nat.add_le_add_left hle16 80) (by decide)
        exact Nat.mod_eq_of_lt hlt
      have hd0 : decide (op = OP_0) = false := by
        apply decide_eq_false
        intro heq; have htn := congrArg UInt8.toNat heq; rw [hopNat] at htn
        change 80 + b.toNat = 0 at htn
        exact absurd (by rw [← htn]; exact Nat.le_add_right 80 _ : 80 ≤ 0) (by decide)
      have hd1n : decide (op = OP_1NEGATE) = false := by
        apply decide_eq_false
        intro heq; have htn := congrArg UInt8.toNat heq; rw [hopNat] at htn
        change 80 + b.toNat = 79 at htn
        have : 80 + 1 ≤ 79 := by rw [← htn]; exact Nat.add_le_add_left hge1 80
        exact absurd this (by decide)
      have hdge1 : decide (OP_1 ≤ op) = true := by
        apply decide_eq_true
        rw [UInt8.le_iff_toNat_le, hopNat]
        exact Nat.add_le_add_left hge1 80
      have hdle16 : decide (op ≤ OP_16) = true := by
        apply decide_eq_true
        rw [UInt8.le_iff_toNat_le, hopNat]
        exact Nat.add_le_add_left hle16 80
      have hsub : op - 0x50 = b := by
        apply UInt8.toNat_inj.mp
        have hle80 : (0x50 : UInt8) ≤ op := by
          rw [UInt8.le_iff_toNat_le, hopNat]; exact Nat.le_add_right 80 b.toNat
        rw [UInt8.toNat_sub_of_le _ _ hle80, hopNat]
        exact Nat.add_sub_cancel_left 80 b.toNat
      change (match op :: tail.data.toList with | [] => none | op' :: rest => _) = _
      dsimp only
      rw [hd0, hd1n, hdge1, hdle16, hsub, htailMk]
      rfl
    · rcases hb81 with ⟨rfl, rfl⟩
      unfold BitcoinLedger.Script.decodeMinimalPushPrefix? Spec.OP_1NEGATE
      rw [byteArray_toList_append]
      simp only [List.cons_append, List.nil_append]
      change (match (0x4F : UInt8) :: tail.data.toList with | [] => none | op' :: rest => _) = _
      dsimp only
      rw [htailMk]
      rfl
    · rcases hbother with ⟨hcond, rfl⟩
      unfold BitcoinLedger.Script.decodeMinimalPushPrefix?
      rw [byteArray_toList_append]
      simp only [List.cons_append, List.nil_append]
      change (match (0x01 : UInt8) :: b :: tail.data.toList with | [] => none | op' :: rest => _) = _
      dsimp only
      have hbad : ((decide (1 ≤ b.toNat) && decide (b.toNat ≤ 16)) || decide (b = 0x81)) = false := by
        rcases hcond with rfl | ⟨hge17, hne81⟩
        · decide
        · rw [decide_eq_false (Nat.not_le_of_gt hge17), Bool.and_false, decide_eq_false hne81]
          rfl
      rw [hbad, htailMk]
      rfl
  · rcases h75 with ⟨hge2, hle75, rfl⟩
    unfold BitcoinLedger.Script.decodeMinimalPushPrefix?
    rw [ByteArray.append_assoc, byteArray_toList_append, byteArray_toList_append]
    simp only [List.cons_append, List.nil_append]
    let op := UInt8.ofNat payload.size
    have hopNat : op.toNat = payload.size := by
      dsimp [op]; rw [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle75 (by decide))
    have hd0 : decide (op = OP_0) = false := by
      apply decide_eq_false; intro heq
      have htn := congrArg UInt8.toNat heq; rw [hopNat] at htn
      change payload.size = 0 at htn
      have : 2 ≤ 0 := by rw [← htn]; exact hge2
      exact absurd this (by decide)
    have hd1n : decide (op = OP_1NEGATE) = false := by
      apply decide_eq_false; intro heq
      have htn := congrArg UInt8.toNat heq; rw [hopNat] at htn
      change payload.size = 79 at htn
      have : 79 ≤ 75 := by rw [← htn]; exact hle75
      exact absurd this (by decide)
    have hdsmall : (decide (OP_1 ≤ op) && decide (op ≤ OP_16)) = false := by
      have hn : ¬ (OP_1 ≤ op) := by
        rw [UInt8.le_iff_toNat_le, hopNat]
        exact fun h => absurd (Nat.le_trans h hle75) (by decide)
      rw [decide_eq_false hn, Bool.false_and]
    have hd1 : decide (op = 0x01) = false := by
      apply decide_eq_false; intro heq
      have htn := congrArg UInt8.toNat heq; rw [hopNat] at htn
      change payload.size = 1 at htn
      have : 2 ≤ 1 := by rw [← htn]; exact hge2
      exact absurd this (by decide)
    have hddir : (decide (2 ≤ op.toNat) && decide (op.toNat ≤ 75)) = true := by
      rw [hopNat, decide_eq_true hge2, decide_eq_true hle75]; rfl
    have hnlt : decide ((payload.data.toList ++ tail.data.toList).length < op.toNat) = false := by
      rw [List.length_append, hpayLen, hopNat]
      exact decide_eq_false (Nat.not_lt_of_ge (Nat.le_add_right _ _))
    obtain ⟨htk, hdr⟩ := list_take_drop_prefix payload.data.toList tail.data.toList
    rw [hpayLen] at htk hdr
    change (match op :: (payload.data.toList ++ tail.data.toList) with | [] => none | op' :: rest => _) = _
    dsimp only
    rw [hd0, hd1n, hdsmall, hd1, hddir, hnlt]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hopNat, htk, hdr, hpayMk, htailMk]
  · rcases h255 with ⟨hge76, hle255, rfl⟩
    unfold BitcoinLedger.Script.decodeMinimalPushPrefix? Spec.OP_PUSHDATA1
    unfold OP_0 OP_1NEGATE OP_1 OP_16 OP_PUSHDATA1 OP_PUSHDATA2 OP_PUSHDATA4
    rw [ByteArray.append_assoc, byteArray_toList_append, byteArray_toList_append]
    simp only [List.cons_append, List.nil_append]
    let lb := UInt8.ofNat payload.size
    have hlbNat : lb.toNat = payload.size := by
      dsimp [lb]; rw [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le hle255)
    have hn76 : decide (lb.toNat < 76) = false := by
      rw [hlbNat]; exact decide_eq_false (Nat.not_lt_of_ge hge76)
    have hnlt : decide ((payload.data.toList ++ tail.data.toList).length < lb.toNat) = false := by
      rw [List.length_append, hpayLen, hlbNat]
      exact decide_eq_false (Nat.not_lt_of_ge (Nat.le_add_right _ _))
    obtain ⟨htk, hdr⟩ := list_take_drop_prefix payload.data.toList tail.data.toList
    rw [hpayLen] at htk hdr
    change (match (0x4C : UInt8) :: lb :: (payload.data.toList ++ tail.data.toList) with
      | [] => none | op' :: rest => _) = _
    dsimp only
    rw [hn76, hnlt]
    have h4c :
        (if decide ((0x4C : UInt8) = 0) = true then
           some (ByteArray.empty, ByteArray.mk (lb :: (payload.data.toList ++ tail.data.toList)).toArray)
         else if decide ((0x4C : UInt8) = 0x4F) = true then
           some (ByteArray.mk #[0x81], ByteArray.mk (lb :: (payload.data.toList ++ tail.data.toList)).toArray)
         else if (decide ((0x51 : UInt8) ≤ 0x4C) && decide ((0x4C : UInt8) ≤ 0x60)) = true then
           some (ByteArray.mk #[0x4C - 0x50], ByteArray.mk (lb :: (payload.data.toList ++ tail.data.toList)).toArray)
         else if decide ((0x4C : UInt8) = 0x01) = true then
           if ((decide (1 ≤ lb.toNat) && decide (lb.toNat ≤ 16)) || decide (lb = 0x81)) = true then none
           else some (ByteArray.mk #[lb], ByteArray.mk (payload.data.toList ++ tail.data.toList).toArray)
         else if (decide (2 ≤ (0x4C : UInt8).toNat) && decide ((0x4C : UInt8).toNat ≤ 75)) = true then
           if decide ((lb :: (payload.data.toList ++ tail.data.toList)).length < (0x4C : UInt8).toNat) = true then none
           else some (ByteArray.mk (List.take (0x4C : UInt8).toNat (lb :: (payload.data.toList ++ tail.data.toList))).toArray,
                      ByteArray.mk (List.drop (0x4C : UInt8).toNat (lb :: (payload.data.toList ++ tail.data.toList))).toArray)
         else if decide ((0x4C : UInt8) = 0x4C) = true then
           if (false || false) = true then none
           else some (ByteArray.mk (List.take lb.toNat (payload.data.toList ++ tail.data.toList)).toArray,
                      ByteArray.mk (List.drop lb.toNat (payload.data.toList ++ tail.data.toList)).toArray)
         else none) =
        some (ByteArray.mk (List.take lb.toNat (payload.data.toList ++ tail.data.toList)).toArray,
              ByteArray.mk (List.drop lb.toNat (payload.data.toList ++ tail.data.toList)).toArray) := rfl
    -- simplify directly by evaluating the literal opcode guards:
    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    rw [hlbNat, htk, hdr, hpayMk, htailMk]
    rfl
  · rcases h65k with ⟨hge256, hle65k, rfl⟩
    unfold BitcoinLedger.Script.decodeMinimalPushPrefix? Spec.OP_PUSHDATA2
    unfold OP_0 OP_1NEGATE OP_1 OP_16 OP_PUSHDATA1 OP_PUSHDATA2 OP_PUSHDATA4
    rw [← Proofs.Basic.encodeU16LE_eq]
    let v16 := UInt16.ofNat payload.size
    have hv16Nat : v16.toNat = payload.size := by
      dsimp [v16]; rw [UInt16.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le hle65k)
    have hdec16 := Proofs.Basic.decodeU16LE?_roundtrip v16
    rw [Proofs.Basic.decodeU16LE?_eq, Proofs.Basic.encodeU16LE_eq] at hdec16
    unfold Spec.encodeU16LEBytes Spec.decodeU16LE? at hdec16
    dsimp only at hdec16
    let b0 := UInt8.ofNat (v16.toNat % 256)
    let b1 := UInt8.ofNat ((v16.toNat / 256) % 256)
    have hsum16 : b0.toNat + 256 * b1.toNat = payload.size := by
      have hlt65 : b0.toNat + 256 * b1.toNat < 65536 := by
        have h1 : 256 * b1.toNat ≤ 256 * 255 := Nat.mul_le_mul_left 256 (Nat.le_of_lt_succ b1.toNat_lt)
        exact Nat.lt_of_le_of_lt (Nat.add_le_add (Nat.le_of_lt_succ b0.toNat_lt) h1) (by decide)
      have heqV := congrArg UInt16.toNat (Option.some.inj hdec16)
      rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hlt65, hv16Nat] at heqV
      exact heqV
    have henc16List : (BitcoinLedger.Basic.encodeU16LE v16).data.toList = [b0, b1] := by
      rw [Proofs.Basic.encodeU16LE_eq]; rfl
    rw [ByteArray.append_assoc, ByteArray.append_assoc,
        byteArray_toList_append, byteArray_toList_append, byteArray_toList_append, henc16List]
    simp only [List.cons_append, List.nil_append]
    obtain ⟨htk, hdr⟩ := list_take_drop_prefix payload.data.toList tail.data.toList
    rw [hpayLen] at htk hdr
    change (match (0x4D : UInt8) :: b0 :: b1 :: (payload.data.toList ++ tail.data.toList) with
      | [] => none | op' :: rest => _) = _
    dsimp only
    rw [hsum16]
    have hn256 : decide (payload.size < 256) = false := decide_eq_false (Nat.not_lt_of_ge hge256)
    have hnlt : decide ((payload.data.toList ++ tail.data.toList).length < payload.size) = false := by
      rw [List.length_append, hpayLen]
      exact decide_eq_false (Nat.not_lt_of_ge (Nat.le_add_right _ _))
    rw [hn256, hnlt]
    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, htk, hdr, hpayMk, htailMk]
    rfl
  · rcases h4g with ⟨hge65k, hle4g, rfl⟩
    unfold BitcoinLedger.Script.decodeMinimalPushPrefix? Spec.OP_PUSHDATA4
    unfold OP_0 OP_1NEGATE OP_1 OP_16 OP_PUSHDATA1 OP_PUSHDATA2 OP_PUSHDATA4
    rw [← Proofs.Basic.encodeU32LE_eq]
    let v32 := UInt32.ofNat payload.size
    have hv32Nat : v32.toNat = payload.size := by
      dsimp [v32]; rw [UInt32.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_succ_of_le hle4g)
    have hdec32 := Proofs.Basic.decodeU32LE?_roundtrip v32
    rw [Proofs.Basic.decodeU32LE?_eq, Proofs.Basic.encodeU32LE_eq] at hdec32
    unfold Spec.encodeU32LEBytes Spec.decodeU32LE? at hdec32
    dsimp only at hdec32
    let b0 := UInt8.ofNat (v32.toNat % 256)
    let b1 := UInt8.ofNat ((v32.toNat / 256) % 256)
    let b2 := UInt8.ofNat ((v32.toNat / 65536) % 256)
    let b3 := UInt8.ofNat ((v32.toNat / 16777216) % 256)
    have hsum32 : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat = payload.size := by
      have hlt32 : b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat < 2 ^ 32 := by
        have h1 : 256 * b1.toNat ≤ 256 * 255 := Nat.mul_le_mul_left 256 (Nat.le_of_lt_succ b1.toNat_lt)
        have h2 : 65536 * b2.toNat ≤ 65536 * 255 := Nat.mul_le_mul_left 65536 (Nat.le_of_lt_succ b2.toNat_lt)
        have h3 : 16777216 * b3.toNat ≤ 16777216 * 255 := Nat.mul_le_mul_left 16777216 (Nat.le_of_lt_succ b3.toNat_lt)
        have s1 := Nat.add_le_add (Nat.le_of_lt_succ b0.toNat_lt) h1
        have s2 := Nat.add_le_add s1 h2
        have s3 := Nat.add_le_add s2 h3
        exact Nat.lt_of_le_of_lt s3 (by decide)
      have heqV := congrArg UInt32.toNat (Option.some.inj hdec32)
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt32, hv32Nat] at heqV
      exact heqV
    have henc32List : (BitcoinLedger.Basic.encodeU32LE v32).data.toList = [b0, b1, b2, b3] := by
      rw [Proofs.Basic.encodeU32LE_eq]; rfl
    rw [ByteArray.append_assoc, ByteArray.append_assoc,
        byteArray_toList_append, byteArray_toList_append, byteArray_toList_append, henc32List]
    simp only [List.cons_append, List.nil_append]
    obtain ⟨htk, hdr⟩ := list_take_drop_prefix payload.data.toList tail.data.toList
    rw [hpayLen] at htk hdr
    change (match (0x4E : UInt8) :: b0 :: b1 :: b2 :: b3 :: (payload.data.toList ++ tail.data.toList) with
      | [] => none | op' :: rest => _) = _
    dsimp only
    rw [hsum32]
    have hn65k : decide (payload.size < 65536) = false := decide_eq_false (Nat.not_lt_of_ge hge65k)
    have hnlt : decide ((payload.data.toList ++ tail.data.toList).length < payload.size) = false := by
      rw [List.length_append, hpayLen]
      exact decide_eq_false (Nat.not_lt_of_ge (Nat.le_add_right _ _))
    rw [hn65k, hnlt]
    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, htk, hdr, hpayMk, htailMk]
    rfl

/-! ## 3. Base58 & Base58Check Equivalence -/

theorem asciiCharsOfString?_eq (s : String) :
    BitcoinLedger.Script.asciiCharsOfString? s = Spec.asciiCharsOfString? s := rfl

theorem encodeBase58?_eq (raw : ByteArray) :
    BitcoinLedger.Script.encodeBase58? raw = Spec.encodeBase58? raw := rfl

theorem encodeBase58Check?_eq
    (doubleSha256 : ByteArray → ByteArray) (version payload : ByteArray) :
    BitcoinLedger.Script.encodeBase58Check? doubleSha256 version payload =
      Spec.encodeBase58Check? doubleSha256 version payload := by
  unfold BitcoinLedger.Script.encodeBase58Check? Spec.encodeBase58Check?
  dsimp only
  cases c : decide ((doubleSha256 (version ++ payload)).size < 4)
  · simp [of_decide_eq_false c, encodeBase58?_eq]
  · simp [of_decide_eq_true c]

theorem decodeBase58?_eq (encoded : String) :
    BitcoinLedger.Script.decodeBase58? encoded = Spec.decodeBase58? encoded := rfl

theorem decodeBase58Check?_eq (doubleSha256 : ByteArray → ByteArray) (addr : String) :
    BitcoinLedger.Script.decodeBase58Check? doubleSha256 addr =
      Spec.decodeBase58Check? doubleSha256 addr := by
  unfold BitcoinLedger.Script.decodeBase58Check? Spec.decodeBase58Check?
  rw [decodeBase58?_eq]
  cases Spec.decodeBase58? addr with
  | none => rfl
  | some raw =>
      dsimp only
      cases c1 : decide (raw.size < 4)
      · simp only [Bool.false_eq_true, of_decide_eq_false c1, ↓reduceIte]
        cases c2 : decide ((doubleSha256 (ByteArray.mk (raw.data.toList.take (raw.size - 4)).toArray)).size < 4)
        · simp only [Bool.false_eq_true, of_decide_eq_false c2, ↓reduceIte]
          cases ceq : BitcoinLedger.Basic.eqBytes
              (ByteArray.mk (raw.data.toList.drop (raw.size - 4)).toArray)
              (ByteArray.mk ((doubleSha256 (ByteArray.mk (raw.data.toList.take (raw.size - 4)).toArray)).data.toList.take 4).toArray)
          · have hne : ByteArray.mk (raw.data.toList.drop (raw.size - 4)).toArray ≠
                ByteArray.mk ((doubleSha256 (ByteArray.mk (raw.data.toList.take (raw.size - 4)).toArray)).data.toList.take 4).toArray :=
              fun heq => by
                have ht := (Proofs.Basic.eqBytes_iff _ _).mpr heq
                rw [ceq] at ht; cases ht
            simp [hne]
          · have hy := (Proofs.Basic.eqBytes_iff _ _).mp ceq
            simp [hy]
        · simp [of_decide_eq_true c2]
      · simp [of_decide_eq_true c1]

/-! ## 4. Bech32 / Bech32m Polymod & Raw Codec Equivalence -/

theorem bech32FinalConstant_eq (enc : Bech32Encoding) :
    BitcoinLedger.Script.bech32FinalConstant enc = Spec.bech32FinalConstant enc := by
  cases enc <;> rfl

private theorem if_not_decide_eq_zero_eq (x : UInt32) (k : UInt32) :
    (if (!decide (x = 0)) = true then k else 0) = (if x ≠ 0 then k else 0) := by
  cases c : decide (x = 0)
  · simp [of_decide_eq_false c]
  · simp [of_decide_eq_true c]

theorem bech32PolymodStep_eq (pre : UInt32) (val : UInt8) :
    BitcoinLedger.Script.bech32PolymodStep pre val = Spec.bech32PolymodStep pre val := by
  unfold BitcoinLedger.Script.bech32PolymodStep Spec.bech32PolymodStep
  dsimp only
  have hv : val.toUInt32 = UInt32.ofNat val.toNat := by
    apply UInt32.toNat_inj.mp
    rw [UInt8.toNat_toUInt32, UInt32.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (Nat.lt_trans val.toNat_lt (by decide))).symm
  rw [hv,
      if_not_decide_eq_zero_eq ((pre >>> 25) &&& 1),
      if_not_decide_eq_zero_eq ((pre >>> 25) &&& 2),
      if_not_decide_eq_zero_eq ((pre >>> 25) &&& 4),
      if_not_decide_eq_zero_eq ((pre >>> 25) &&& 8),
      if_not_decide_eq_zero_eq ((pre >>> 25) &&& 16)]

theorem bech32Polymod_eq (values : List UInt8) :
    BitcoinLedger.Script.bech32Polymod values = Spec.bech32Polymod values := by
  unfold BitcoinLedger.Script.bech32Polymod Spec.bech32Polymod
  have hstep : BitcoinLedger.Script.bech32PolymodStep = Spec.bech32PolymodStep := by
    funext pre val
    exact bech32PolymodStep_eq pre val
  rw [hstep]

theorem bech32HrpExpand_eq (hrpLower : List Char) :
    BitcoinLedger.Script.bech32HrpExpand hrpLower = Spec.bech32HrpExpand hrpLower := rfl

theorem bech32CreateChecksum_eq (enc : Bech32Encoding) (hrpLower : List Char) (data5 : List UInt8) :
    BitcoinLedger.Script.bech32CreateChecksum enc hrpLower data5 =
      Spec.bech32CreateChecksum enc hrpLower data5 := by
  unfold BitcoinLedger.Script.bech32CreateChecksum Spec.bech32CreateChecksum
  rw [bech32Polymod_eq, bech32HrpExpand_eq, bech32FinalConstant_eq]

theorem bech32VerifyChecksum?_eq (hrpLower : List Char) (dataAndChecksum5 : List UInt8) :
    BitcoinLedger.Script.bech32VerifyChecksum? hrpLower dataAndChecksum5 =
      Spec.bech32VerifyChecksum? hrpLower dataAndChecksum5 := by
  unfold BitcoinLedger.Script.bech32VerifyChecksum? Spec.bech32VerifyChecksum?
  have hall : (dataAndChecksum5.all (fun v => decide (v < 32))) =
      (dataAndChecksum5.all (fun v => v < 32)) := rfl
  rw [hall, bech32Polymod_eq, bech32HrpExpand_eq, bech32FinalConstant_eq, bech32FinalConstant_eq]
  cases c1 : decide (dataAndChecksum5.length < 6)
  · simp only [Bool.false_eq_true, of_decide_eq_false c1, ↓reduceIte]
    cases c2 : dataAndChecksum5.all (fun v => v < 32)
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases cb : decide (Spec.bech32Polymod (Spec.bech32HrpExpand hrpLower ++ dataAndChecksum5) =
          Spec.bech32FinalConstant .bech32)
      · simp only [Bool.false_eq_true, of_decide_eq_false cb, ↓reduceIte]
        cases cbm : decide (Spec.bech32Polymod (Spec.bech32HrpExpand hrpLower ++ dataAndChecksum5) =
            Spec.bech32FinalConstant .bech32m)
        · simp [of_decide_eq_false cbm]
        · simp [of_decide_eq_true cbm]
      · simp [of_decide_eq_true cb]
  · simp [of_decide_eq_true c1]

theorem decodeBech32Raw?_eq (maxLen : Nat) (input : String) :
    BitcoinLedger.Script.decodeBech32Raw? maxLen input = Spec.decodeBech32Raw? maxLen input := rfl

theorem encodeBech32Raw?_eq (maxLen : Nat) (enc : Bech32Encoding) (hrp : String) (data5 : List UInt8) :
    BitcoinLedger.Script.encodeBech32Raw? maxLen enc hrp data5 =
      Spec.encodeBech32Raw? maxLen enc hrp data5 := rfl

/-! ## 5. Universal 8↔5 Bit Conversion Roundtrip (`0 Classical.choice`) -/

private theorem literal_mask_testBit (m k i : Nat) (hm : m < 2 ^ k) (hi : k ≤ i) :
    m.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))

private theorem and31_not_ge32 (x : UInt32) : decide ((x &&& 31).toUInt8 ≥ 32) = false := by
  apply decide_eq_false
  apply UInt8.not_le.mpr
  rw [UInt8.lt_iff_toNat_lt, UInt32.toNat_toUInt8, UInt32.toNat_and]
  change (x.toNat &&& 31) % 256 < 32
  have hlt : x.toNat &&& 31 < 32 := Nat.and_lt_two_pow _ (n := 5) (by decide)
  rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))]
  exact hlt

private theorem eq_u8_of_bits (lhs b : UInt8)
    (h : ∀ i, i < 8 → lhs.toNat.testBit i = b.toNat.testBit i) : lhs = b := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  cases hlt : decide (i < 8)
  · have hge : 8 ≤ i := Nat.le_of_not_lt (of_decide_eq_false hlt)
    rw [literal_mask_testBit lhs.toNat 8 i lhs.toNat_lt hge,
        literal_mask_testBit b.toNat 8 i b.toNat_lt hge]
  · exact h i (of_decide_eq_true hlt)

private theorem convert5to8_end_ok (bits acc : UInt32) (hb : decide (bits ≥ 5) = false)
    (hm : acc = 0) :
    (if (decide (bits ≥ 5) || !decide (acc = 0)) = true then (none : Option (List UInt8)) else some []) =
      some [] := by
  rw [hb, hm]
  rfl

private theorem eq_zero_u32_and_small (x m : UInt32) (hm : m.toNat < 2 ^ 8)
    (h : ∀ i, i < 8 → (x &&& m).toNat.testBit i = false) : x &&& m = 0 := by
  apply UInt32.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  change (x &&& m).toNat.testBit i = (0 : Nat).testBit i
  rw [Nat.zero_testBit]
  cases hlt : decide (i < 8)
  · have hge : 8 ≤ i := Nat.le_of_not_lt (of_decide_eq_false hlt)
    rw [UInt32.toNat_and, Nat.testBit_and, literal_mask_testBit m.toNat 8 i hm hge, Bool.and_false]
  · exact h i (of_decide_eq_true hlt)

private theorem convert8to5_cons_0 (b : UInt8) (bs : List UInt8) (acc : UInt32) :
    convert8to5Loop (b :: bs) 0 acc =
      (((acc <<< 8 ||| b.toUInt32) >>> 3) &&& 31).toUInt8 ::
        convert8to5Loop bs 3 ((acc <<< 8 ||| b.toUInt32) &&& 7) := rfl

private theorem convert8to5_cons_3 (b : UInt8) (bs : List UInt8) (acc : UInt32) :
    convert8to5Loop (b :: bs) 3 acc =
      (((acc <<< 8 ||| b.toUInt32) >>> 6) &&& 31).toUInt8 ::
      ((((acc <<< 8 ||| b.toUInt32) &&& 63) >>> 1) &&& 31).toUInt8 ::
        convert8to5Loop bs 1 ((acc <<< 8 ||| b.toUInt32) &&& 1) := rfl

private theorem convert8to5_cons_1 (b : UInt8) (bs : List UInt8) (acc : UInt32) :
    convert8to5Loop (b :: bs) 1 acc =
      (((acc <<< 8 ||| b.toUInt32) >>> 4) &&& 31).toUInt8 ::
        convert8to5Loop bs 4 ((acc <<< 8 ||| b.toUInt32) &&& 15) := rfl

private theorem convert8to5_cons_4 (b : UInt8) (bs : List UInt8) (acc : UInt32) :
    convert8to5Loop (b :: bs) 4 acc =
      (((acc <<< 8 ||| b.toUInt32) >>> 7) &&& 31).toUInt8 ::
      ((((acc <<< 8 ||| b.toUInt32) &&& 127) >>> 2) &&& 31).toUInt8 ::
        convert8to5Loop bs 2 ((acc <<< 8 ||| b.toUInt32) &&& 3) := rfl

private theorem convert8to5_cons_2 (b : UInt8) (bs : List UInt8) (acc : UInt32) :
    convert8to5Loop (b :: bs) 2 acc =
      (((acc <<< 8 ||| b.toUInt32) >>> 5) &&& 31).toUInt8 ::
      ((((acc <<< 8 ||| b.toUInt32) &&& 31) >>> 0) &&& 31).toUInt8 ::
        convert8to5Loop bs 0 0 := by
  have hz : (acc <<< 8 ||| b.toUInt32) &&& ((1 : UInt32) <<< ((2 + 8) % 5) - 1) = 0 := by
    change (acc <<< 8 ||| b.toUInt32) &&& 0 = 0
    exact UInt32.and_zero
  conv => lhs; unfold convert8to5Loop; dsimp only; rw [hz]
  rfl

private theorem convert8to5_nil_1 (acc : UInt32) :
    convert8to5Loop [] 1 acc = [((acc <<< 4) &&& 31).toUInt8] := rfl
private theorem convert8to5_nil_2 (acc : UInt32) :
    convert8to5Loop [] 2 acc = [((acc <<< 3) &&& 31).toUInt8] := rfl
private theorem convert8to5_nil_3 (acc : UInt32) :
    convert8to5Loop [] 3 acc = [((acc <<< 2) &&& 31).toUInt8] := rfl
private theorem convert8to5_nil_4 (acc : UInt32) :
    convert8to5Loop [] 4 acc = [((acc <<< 1) &&& 31).toUInt8] := rfl

private theorem u32_and_zero_mask (x : UInt32) : x &&& ((1 : UInt32) <<< 0 - 1) = 0 := by
  change x &&& 0 = 0
  exact UInt32.and_zero

private theorem u8_shr_ge8_false (b : UInt8) (k : Nat) (hk : 8 ≤ k) :
    (1 &&& b.toNat >>> k != 0) = false := by
  change b.toNat.testBit k = false
  exact literal_mask_testBit b.toNat 8 k b.toNat_lt hk

@[simp] private theorem mask_1_toNat  : ((1 : UInt32) <<< 1 - 1).toNat = 1   := rfl
@[simp] private theorem mask_2_toNat  : ((1 : UInt32) <<< 2 - 1).toNat = 3   := rfl
@[simp] private theorem mask_3_toNat  : ((1 : UInt32) <<< 3 - 1).toNat = 7   := rfl
@[simp] private theorem mask_4_toNat  : ((1 : UInt32) <<< 4 - 1).toNat = 15  := rfl
@[simp] private theorem mask_5_toNat  : ((1 : UInt32) <<< 5 - 1).toNat = 31  := rfl
@[simp] private theorem mask_6_toNat  : ((1 : UInt32) <<< 6 - 1).toNat = 63  := rfl
@[simp] private theorem mask_7_toNat  : ((1 : UInt32) <<< 7 - 1).toNat = 127 := rfl
@[simp] private theorem lit31_toNat   : (31 : UInt32).toNat = 31   := rfl
@[simp] private theorem lit255_toNat  : (255 : UInt32).toNat = 255 := rfl

@[simp] private theorem u8_s8  (b : UInt8) : (1 &&& b.toNat >>> 8  != 0) = false := u8_shr_ge8_false b 8  (by decide)
@[simp] private theorem u8_s9  (b : UInt8) : (1 &&& b.toNat >>> 9  != 0) = false := u8_shr_ge8_false b 9  (by decide)
@[simp] private theorem u8_s10 (b : UInt8) : (1 &&& b.toNat >>> 10 != 0) = false := u8_shr_ge8_false b 10 (by decide)
@[simp] private theorem u8_s11 (b : UInt8) : (1 &&& b.toNat >>> 11 != 0) = false := u8_shr_ge8_false b 11 (by decide)
@[simp] private theorem u8_s12 (b : UInt8) : (1 &&& b.toNat >>> 12 != 0) = false := u8_shr_ge8_false b 12 (by decide)
@[simp] private theorem u8_s13 (b : UInt8) : (1 &&& b.toNat >>> 13 != 0) = false := u8_shr_ge8_false b 13 (by decide)
@[simp] private theorem u8_s14 (b : UInt8) : (1 &&& b.toNat >>> 14 != 0) = false := u8_shr_ge8_false b 14 (by decide)
@[simp] private theorem u8_s15 (b : UInt8) : (1 &&& b.toNat >>> 15 != 0) = false := u8_shr_ge8_false b 15 (by decide)

macro "crush_u8_bits" : tactic => `(tactic| (
  apply eq_u8_of_bits
  intro i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp only [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_or,
                 UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, UInt8.toNat_toUInt32,
                 mask_1_toNat, mask_2_toNat, mask_3_toNat, mask_4_toNat,
                 mask_5_toNat, mask_6_toNat, mask_7_toNat, lit31_toNat, lit255_toNat,
                 Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or,
                 Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      dsimp [Nat.testBit, decide, Nat.ble]
      simp only [u8_s8, u8_s9, u8_s10, u8_s11, u8_s12, u8_s13, u8_s14, u8_s15,
                 Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
                 Bool.or_false, Bool.false_or, Bool.or_self]
))

macro "crush_u32_rem0" : tactic => `(tactic| (
  apply eq_zero_u32_and_small _ _ (by decide)
  intro i hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp only [UInt32.toNat_toUInt8, UInt32.toNat_and, UInt32.toNat_or,
                 UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight, UInt8.toNat_toUInt32,
                 mask_1_toNat, mask_2_toNat, mask_3_toNat, mask_4_toNat,
                 mask_5_toNat, mask_6_toNat, mask_7_toNat, lit31_toNat, lit255_toNat,
                 Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or,
                 Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      dsimp [Nat.testBit, decide, Nat.ble]
      simp only [u8_s8, u8_s9, u8_s10, u8_s11, u8_s12, u8_s13, u8_s14, u8_s15,
                 Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
                 Bool.or_false, Bool.false_or, Bool.or_self]
))

private theorem roundtrip_1byte (b0 : UInt8) :
    convert5to8Loop (convert8to5Loop [b0] 0 0) 0 0 = some [b0] := by
  rw [convert8to5_cons_0, convert8to5_nil_3]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop
  rw [convert5to8_end_ok _ _ rfl (by crush_u32_rem0)]
  dsimp only
  congr 2
  crush_u8_bits

private theorem roundtrip_2byte (b0 b1 : UInt8) :
    convert5to8Loop (convert8to5Loop [b0, b1] 0 0) 0 0 = some [b0, b1] := by
  rw [convert8to5_cons_0, convert8to5_cons_3, convert8to5_nil_1]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop
  rw [convert5to8_end_ok _ _ rfl (by crush_u32_rem0)]
  dsimp only
  congr 1; congr 1
  · crush_u8_bits
  · congr 1; crush_u8_bits

private theorem roundtrip_3byte (b0 b1 b2 : UInt8) :
    convert5to8Loop (convert8to5Loop [b0, b1, b2] 0 0) 0 0 = some [b0, b1, b2] := by
  rw [convert8to5_cons_0, convert8to5_cons_3, convert8to5_cons_1, convert8to5_nil_4]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop
  rw [convert5to8_end_ok _ _ rfl (by crush_u32_rem0)]
  dsimp only
  congr 1; congr 1
  · crush_u8_bits
  · congr 1
    · crush_u8_bits
    · congr 1; crush_u8_bits

private theorem roundtrip_4byte (b0 b1 b2 b3 : UInt8) :
    convert5to8Loop (convert8to5Loop [b0, b1, b2, b3] 0 0) 0 0 = some [b0, b1, b2, b3] := by
  rw [convert8to5_cons_0, convert8to5_cons_3, convert8to5_cons_1, convert8to5_cons_4, convert8to5_nil_2]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop; rw [and31_not_ge32]; dsimp [extract8BitChunks]
  unfold convert5to8Loop
  rw [convert5to8_end_ok _ _ rfl (by crush_u32_rem0)]
  dsimp only
  congr 1; congr 1
  · crush_u8_bits
  · congr 1
    · crush_u8_bits
    · congr 1
      · crush_u8_bits
      · congr 1; crush_u8_bits

private theorem convert5to8_step (x : UInt32) (vs : List UInt8) (bits acc : UInt32) :
    convert5to8Loop ((x &&& 31).toUInt8 :: vs) bits acc =
      match convert5to8Loop vs ((bits + 5) % 8)
              (((acc <<< 5) ||| (x &&& 31).toUInt8.toUInt32) &&& ((1 : UInt32) <<< ((bits + 5) % 8) - 1)) with
      | none => none
      | some rest =>
          some (extract8BitChunks 2 (bits + 5) ((acc <<< 5) ||| (x &&& 31).toUInt8.toUInt32) ++ rest) := by
  conv => lhs; unfold convert5to8Loop
  rw [and31_not_ge32]
  rfl

private theorem roundtrip_5byte_step (b0 b1 b2 b3 b4 : UInt8) (rest : List UInt8) :
    convert5to8Loop (convert8to5Loop (b0 :: b1 :: b2 :: b3 :: b4 :: rest) 0 0) 0 0 =
      (convert5to8Loop (convert8to5Loop rest 0 0) 0 0).map
        (fun tail => b0 :: b1 :: b2 :: b3 :: b4 :: tail) := by
  rw [convert8to5_cons_0, convert8to5_cons_3, convert8to5_cons_1, convert8to5_cons_4, convert8to5_cons_2]
  rw [convert5to8_step, convert5to8_step, convert5to8_step, convert5to8_step,
      convert5to8_step, convert5to8_step, convert5to8_step, convert5to8_step]
  have hmod0 : (((((((0 + 5) % 8 + 5) % 8 + 5) % 8 + 5) % 8 + 5) % 8 + 5) % 8 + 5) % 8 + 5 = (8 : UInt32) := rfl
  rw [hmod0, show ((8 : UInt32) % 8) = 0 from rfl, u32_and_zero_mask]
  cases convert5to8Loop (convert8to5Loop rest 0 0) 0 0 with
  | none => rfl
  | some tail =>
      dsimp [extract8BitChunks]
      congr 1; congr 1
      · crush_u8_bits
      · congr 1
        · crush_u8_bits
        · congr 1
          · crush_u8_bits
          · congr 1
            · crush_u8_bits
            · congr 1; crush_u8_bits

theorem convert8to5_5to8_list : ∀ bs : List UInt8,
    convert5to8Loop (convert8to5Loop bs 0 0) 0 0 = some bs
  | [] => rfl
  | [b0] => roundtrip_1byte b0
  | [b0, b1] => roundtrip_2byte b0 b1
  | [b0, b1, b2] => roundtrip_3byte b0 b1 b2
  | [b0, b1, b2, b3] => roundtrip_4byte b0 b1 b2 b3
  | b0 :: b1 :: b2 :: b3 :: b4 :: rest => by
      rw [roundtrip_5byte_step, convert8to5_5to8_list rest]
      rfl

/-- Universal 8↔5 bit conversion roundtrip (`0 Classical.choice`, holds for ALL `ByteArray`s!):
    encoding any byte array into 5-bit BIP-173 groups and strictly decoding back recovers `some bs`. -/
theorem convertBits5to8?_convertBits8to5 (bs : ByteArray) :
    BitcoinLedger.Script.convertBits5to8? (BitcoinLedger.Script.convertBits8to5 bs) = some bs := by
  unfold BitcoinLedger.Script.convertBits5to8? BitcoinLedger.Script.convertBits8to5
  rw [convert8to5_5to8_list]
  cases bs
  rfl

/-! ## 6. SegWit Witness-Version Segregation & Concrete Witnesses (`0 Classical.choice`) -/

theorem requiredSegwitEncoding?_eq (witver : UInt8) :
    BitcoinLedger.Script.requiredSegwitEncoding? witver = Spec.requiredSegwitEncoding? witver := by
  unfold BitcoinLedger.Script.requiredSegwitEncoding? Spec.requiredSegwitEncoding?
  cases h0 : decide (witver = 0)
  · have hne0 : ¬ (witver = 0) := of_decide_eq_false h0
    simp only [Bool.false_eq_true, ↓reduceIte, hne0]
    cases h16 : decide (witver ≤ 16)
    · have hnot16 : ¬ (witver ≤ 16) := of_decide_eq_false h16
      simp [hnot16]
    · have hle16 : witver ≤ 16 := of_decide_eq_true h16
      simp [hle16]
  · have heq0 : witver = 0 := of_decide_eq_true h0
    simp [heq0]

theorem isValidSegwitProgram_eq (witver : UInt8) (witprog : ByteArray) :
    BitcoinLedger.Script.isValidSegwitProgram witver witprog =
      Spec.isValidSegwitProgram witver witprog := by
  unfold BitcoinLedger.Script.isValidSegwitProgram Spec.isValidSegwitProgram
  cases h0 : decide (witver = 0)
  · have hne0 : ¬ (witver = 0) := of_decide_eq_false h0
    simp only [Bool.false_eq_true, ↓reduceIte, hne0]
    cases h16 : decide (witver ≤ 16)
    · have hnot16 : ¬ (witver ≤ 16) := of_decide_eq_false h16
      simp [hnot16]
    · have hle16 : witver ≤ 16 := of_decide_eq_true h16
      simp [hle16, Bool.decide_and]
  · have heq0 : witver = 0 := of_decide_eq_true h0
    simp [heq0, Bool.decide_or]

theorem bech32VerifyChecksum_unique_variant
    (hrpLower : List Char) (data5 : List UInt8) (e1 e2 : Bech32Encoding)
    (h1 : BitcoinLedger.Script.bech32VerifyChecksum? hrpLower data5 = some e1)
    (h2 : BitcoinLedger.Script.bech32VerifyChecksum? hrpLower data5 = some e2) :
    e1 = e2 := by
  rw [h1] at h2
  exact Option.some.inj h2

/-- Witness `v0` Segregation (`0 Classical.choice`): every accepted SegWit `v0` address MUST use
    **Bech32** (never Bech32m) and MUST have witness program length `20` or `32`. -/
theorem decodeSegwitAddr?_v0_segregation
    {expectedHrp addr : String} {prog : ByteArray}
    (hdec : BitcoinLedger.Script.decodeSegwitAddr? expectedHrp addr = some (0, prog)) :
    (∃ payload5,
      BitcoinLedger.Script.decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr =
        some (.bech32, expectedHrp, 0 :: payload5)) ∧
    (prog.size = 20 ∨ prog.size = 32) := by
  unfold BitcoinLedger.Script.decodeSegwitAddr? at hdec
  cases hraw : BitcoinLedger.Script.decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr with
  | none => simp [hraw] at hdec
  | some triple =>
      rcases triple with ⟨enc, hrp, payload5⟩
      simp only [hraw] at hdec
      cases hhrp : decide (hrp = expectedHrp)
      · simp [hhrp] at hdec
      · have hhrpEq : hrp = expectedHrp := of_decide_eq_true hhrp
        subst hhrpEq
        simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hdec
        cases payload5 with
        | nil => simp at hdec
        | cons witver prog5 =>
            simp only at hdec
            cases hvgt : decide (witver > 16)
            · rw [hvgt] at hdec
              simp only [Bool.false_eq_true, ↓reduceIte] at hdec
              cases henc : decide (BitcoinLedger.Script.requiredSegwitEncoding? witver = some enc)
              · simp [henc] at hdec
              · rw [henc] at hdec
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hdec
                cases hconv : BitcoinLedger.Script.convertBits5to8? prog5 with
                | none => simp [hconv] at hdec
                | some witprog =>
                    simp only [hconv] at hdec
                    cases hval : BitcoinLedger.Script.isValidSegwitProgram witver witprog
                    · simp [hval] at hdec
                    · rw [hval] at hdec
                      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                      rcases hdec with ⟨rfl, rfl⟩
                      have hencProp := of_decide_eq_true henc
                      have hencEq : enc = .bech32 := by
                        unfold BitcoinLedger.Script.requiredSegwitEncoding? at hencProp
                        simp at hencProp
                        exact hencProp.symm
                      subst hencEq
                      refine ⟨⟨prog5, rfl⟩, ?_⟩
                      unfold BitcoinLedger.Script.isValidSegwitProgram at hval
                      simp only [decide_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] at hval
                      exact hval
            · simp [hvgt] at hdec

private theorem u8_pos_of_ne_zero {v : UInt8} (hne : v ≠ 0) : 1 ≤ v.toNat := by
  cases h : v.toNat with
  | zero => exact False.elim (hne (UInt8.toNat_inj.mp h))
  | succ k => exact Nat.succ_le_succ (Nat.zero_le k)

/-- Witness `v1..v16` Segregation (`0 Classical.choice`): every accepted SegWit `v1..v16` address (`ver ≠ 0`)
    MUST use **Bech32m** (never Bech32), with `1 ≤ ver.toNat ≤ 16` and `2 ≤ prog.size ≤ 40`. -/
theorem decodeSegwitAddr?_v1_to_16_segregation
    {expectedHrp addr : String} {ver : UInt8} {prog : ByteArray}
    (hne0 : ver ≠ 0)
    (hdec : BitcoinLedger.Script.decodeSegwitAddr? expectedHrp addr = some (ver, prog)) :
    1 ≤ ver.toNat ∧ ver.toNat ≤ 16 ∧
    (∃ payload5,
      BitcoinLedger.Script.decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr =
        some (.bech32m, expectedHrp, ver :: payload5)) ∧
    2 ≤ prog.size ∧ prog.size ≤ 40 := by
  unfold BitcoinLedger.Script.decodeSegwitAddr? at hdec
  cases hraw : BitcoinLedger.Script.decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr with
  | none => simp [hraw] at hdec
  | some triple =>
      rcases triple with ⟨enc, hrp, payload5⟩
      simp only [hraw] at hdec
      cases hhrp : decide (hrp = expectedHrp)
      · simp [hhrp] at hdec
      · have hhrpEq : hrp = expectedHrp := of_decide_eq_true hhrp
        subst hhrpEq
        simp only [decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hdec
        cases payload5 with
        | nil => simp at hdec
        | cons witver prog5 =>
            simp only at hdec
            cases hvgt : decide (witver > 16)
            · rw [hvgt] at hdec
              simp only [Bool.false_eq_true, ↓reduceIte] at hdec
              cases henc : decide (BitcoinLedger.Script.requiredSegwitEncoding? witver = some enc)
              · simp [henc] at hdec
              · rw [henc] at hdec
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hdec
                cases hconv : BitcoinLedger.Script.convertBits5to8? prog5 with
                | none => simp [hconv] at hdec
                | some witprog =>
                    simp only [hconv] at hdec
                    cases hval : BitcoinLedger.Script.isValidSegwitProgram witver witprog
                    · simp [hval] at hdec
                    · rw [hval] at hdec
                      simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hdec
                      rcases hdec with ⟨rfl, rfl⟩
                      have hnotgt : ¬ (16 < witver.toNat) := of_decide_eq_false hvgt
                      have hv16Nat : witver.toNat ≤ 16 := Nat.le_of_not_lt hnotgt
                      have hvLe16 : witver ≤ 16 := hv16Nat
                      have hv1 : 1 ≤ witver.toNat := u8_pos_of_ne_zero hne0
                      have hencProp := of_decide_eq_true henc
                      have hencEq : enc = .bech32m := by
                        unfold BitcoinLedger.Script.requiredSegwitEncoding? at hencProp
                        simp [hne0, hvLe16] at hencProp
                        exact hencProp.symm
                      subst hencEq
                      unfold BitcoinLedger.Script.isValidSegwitProgram at hval
                      simp only [hne0, decide_false, Bool.false_eq_true, ↓reduceIte,
                        hvLe16, decide_true, Bool.and_eq_true, decide_eq_true_eq] at hval
                      exact ⟨hv1, hv16Nat, ⟨prog5, rfl⟩, hval.1, hval.2⟩
            · simp [hvgt] at hdec

theorem segwit_rejects_v0_with_bech32m
    (expectedHrp addr hrp : String) (prog5 : List UInt8)
    (hraw : BitcoinLedger.Script.decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr =
      some (.bech32m, hrp, 0 :: prog5)) :
    BitcoinLedger.Script.decodeSegwitAddr? expectedHrp addr = none := by
  unfold BitcoinLedger.Script.decodeSegwitAddr?
  rw [hraw]
  cases hhrp : decide (hrp = expectedHrp)
  · simp [of_decide_eq_false hhrp]
  · simp [of_decide_eq_true hhrp, BitcoinLedger.Script.requiredSegwitEncoding?]

theorem segwit_rejects_v1_to_16_with_bech32
    (expectedHrp addr hrp : String) (ver : UInt8) (prog5 : List UInt8)
    (hne0 : ver ≠ 0)
    (hraw : BitcoinLedger.Script.decodeBech32Raw? SEGWIT_BECH32_MAX_LEN addr =
      some (.bech32, hrp, ver :: prog5)) :
    BitcoinLedger.Script.decodeSegwitAddr? expectedHrp addr = none := by
  unfold BitcoinLedger.Script.decodeSegwitAddr?
  rw [hraw]
  dsimp only
  cases hhrp : decide (hrp = expectedHrp)
  · rfl
  · cases hvgt : decide (ver > 16)
    · have hnotgt : ¬ (16 < ver.toNat) := of_decide_eq_false hvgt
      have hvLe16 : ver ≤ 16 := Nat.le_of_not_lt hnotgt
      simp [BitcoinLedger.Script.requiredSegwitEncoding?, hne0, hvLe16]
    · rfl

theorem encodeSegwitAddr?_rejects_v0_bad_length
    (hrp : String) (prog : ByteArray)
    (hne20 : prog.size ≠ 20) (hne32 : prog.size ≠ 32) :
    BitcoinLedger.Script.encodeSegwitAddr? hrp 0 prog = none := by
  unfold BitcoinLedger.Script.encodeSegwitAddr? BitcoinLedger.Script.isValidSegwitProgram
  simp [hne20, hne32]

theorem standardScriptToAddress?_bolos_rejects_unknownWitness
    (dsha : ByteArray → ByteArray)
    (net : BitcoinLedger.Basic.Network) (snet : Spec.Network)
    (ver : UInt8) (prog : ByteArray) :
    BitcoinLedger.Script.standardScriptToAddress? .bolos dsha net (.unknownWitness ver prog) = none ∧
    Spec.standardScriptToAddress? .bolos dsha snet (.unknownWitness ver prog) = none := by
  refine ⟨rfl, ?_⟩
  unfold Spec.standardScriptToAddress?
  cases h2 : decide (2 ≤ ver.toNat)
  · simp [of_decide_eq_false h2]
  · simp [of_decide_eq_true h2]

set_option maxRecDepth 16384 in
/-- Concrete Witness 1 (BIP-173 `v0`): Mainnet P2WPKH roundtrip, uppercase decode, mixed-case rejection,
    and Bech32m segregation rejection. -/
theorem witness_bip173_v0_roundtrip_and_segregation :
    let prog20 := ByteArray.mk #[
      0x75, 0x1e, 0x76, 0xe8, 0x19, 0x91, 0x96, 0xd4, 0x54, 0x94,
      0x1c, 0x45, 0xd1, 0xb3, 0xa3, 0x23, 0xf1, 0x43, 0x3b, 0xd6
    ]
    BitcoinLedger.Script.encodeSegwitAddr? "bc" 0 prog20 =
      some "bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" ∧
    BitcoinLedger.Script.decodeSegwitAddr? "bc" "BC1QW508D6QEJXTDG4Y5R3ZARVARY0C5XW7KV8F3T4" =
      some (0, prog20) ∧
    BitcoinLedger.Script.decodeSegwitAddr? "bc" "bc1qW508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4" = none ∧
    (BitcoinLedger.Script.encodeBech32Raw? 90 .bech32m "bc"
      (0 :: BitcoinLedger.Script.convertBits8to5 prog20)).map
        (BitcoinLedger.Script.decodeSegwitAddr? "bc") = some none := by
  decide

set_option maxRecDepth 16384 in
/-- Concrete Witness 2 (BIP-350 `v1`): Mainnet Taproot P2TR roundtrip and Bech32 segregation rejection. -/
theorem witness_bip350_v1_roundtrip_and_segregation :
    let key32 := ByteArray.mk #[
      0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac,
      0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b, 0x07,
      0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9,
      0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8, 0x17, 0x98
    ]
    BitcoinLedger.Script.encodeSegwitAddr? "bc" 1 key32 =
      some "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" ∧
    BitcoinLedger.Script.decodeSegwitAddr? "bc"
      "bc1p0xlxvlhemja6c4dqv22uapctqupfhlxm9h8z3k2e72q4k9hcz7vqzk5jj0" =
      some (1, key32) ∧
    (BitcoinLedger.Script.encodeBech32Raw? 90 .bech32 "bc"
      (1 :: BitcoinLedger.Script.convertBits8to5 key32)).map
        (BitcoinLedger.Script.decodeSegwitAddr? "bc") = some none := by
  decide

/-- Concrete Witness 3 (`MINIMALDATA` & `OP_RETURN`): canonical pushes accepted, non-minimal 1-byte pushes
    (`0x01 0x05`, `0x01 0x81`), short `OP_PUSHDATA1`, and `> 5` pushes rejected. -/
theorem witness_minimaldata_and_op_return :
    BitcoinLedger.Script.isValidOpReturnScript (ByteArray.mk #[0x6a]) = true ∧
    BitcoinLedger.Script.isValidOpReturnScript (ByteArray.mk #[0x6a, 0x55]) = true ∧
    BitcoinLedger.Script.isValidOpReturnScript (ByteArray.mk #[0x6a, 0x4f]) = true ∧
    BitcoinLedger.Script.isValidOpReturnScript (ByteArray.mk #[0x6a, 0x01, 0x05]) = false ∧
    BitcoinLedger.Script.isValidOpReturnScript (ByteArray.mk #[0x6a, 0x01, 0x81]) = false ∧
    BitcoinLedger.Script.isValidOpReturnScript (ByteArray.mk #[0x6a, 0x4c, 0x01, 0x42]) = false ∧
    BitcoinLedger.Script.isValidOpReturnScript
      (ByteArray.mk #[0x6a, 0x51, 0x51, 0x51, 0x51, 0x51, 0x51]) = false := by
  decide

set_option maxRecDepth 32768 in
/-- Concrete Witness 4 (BOLOS vs Vanadium `v2..v16` SegWit address encoding):
    BOLOS rejects `v2..v16` witness scripts while Vanadium encodes them as BIP-350 Bech32m. -/
theorem witness_bolos_vs_vanadium_segwit_v2_v16 :
    let dummyDSha := fun (_ : ByteArray) => ByteArray.mk (List.replicate 32 0).toArray
    let v2Script := ByteArray.mk #[0x52, 0x02, 0x00, 0x01]
    let v16Script := ByteArray.mk (#[0x60, 0x14] ++ (List.replicate 20 0x11).toArray)
    BitcoinLedger.Script.scriptToAddress? .bolos dummyDSha .mainnet v2Script = none ∧
    BitcoinLedger.Script.scriptToAddress? .bolos dummyDSha .mainnet v16Script = none ∧
    (BitcoinLedger.Script.scriptToAddress? .vanadium dummyDSha .mainnet v2Script).bind
      (BitcoinLedger.Script.decodeSegwitAddr? "bc") =
      some (2, ByteArray.mk #[0x00, 0x01]) ∧
    (BitcoinLedger.Script.scriptToAddress? .vanadium dummyDSha .mainnet v16Script).bind
      (BitcoinLedger.Script.decodeSegwitAddr? "bc") =
      some (16, ByteArray.mk (List.replicate 20 0x11).toArray) := by
  decide

end Proofs.Script

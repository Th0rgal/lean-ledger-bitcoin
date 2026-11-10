import Spec
import BitcoinLedger.FreestandingKernels

namespace Proofs.FreestandingKernels

theorem llbVersionPacked_bytes :
    (BitcoinLedger.FreestandingKernels.llbVersionPacked >>> 16).toUInt8 =
      Spec.ledgerBitcoinTargetVersion.major ∧
    ((BitcoinLedger.FreestandingKernels.llbVersionPacked >>> 8) &&& 0xff).toUInt8 =
      Spec.ledgerBitcoinTargetVersion.minor ∧
    (BitcoinLedger.FreestandingKernels.llbVersionPacked &&& 0xff).toUInt8 =
      Spec.ledgerBitcoinTargetVersion.patch := by
  exact ⟨rfl, rfl, rfl⟩

end Proofs.FreestandingKernels

import Spec
import BitcoinLedger
import Proofs.Basic
import Proofs.Bip32
import Proofs.Script
import Proofs.WalletPolicy
import Proofs.Psbt
import Proofs.MerkleProtocol
import Proofs.Musig2
import Proofs.SilentPayments
import Proofs.AppStateMachine
import Proofs.FreestandingKernels

namespace Proofs

theorem appVersion_matches_spec :
    BitcoinLedger.appVersion = Spec.ledgerBitcoinTargetVersion := by
  rfl

end Proofs

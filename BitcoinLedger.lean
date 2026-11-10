import Spec
import BitcoinLedger.Basic
import BitcoinLedger.Bip32
import BitcoinLedger.Script
import BitcoinLedger.WalletPolicy
import BitcoinLedger.Psbt
import BitcoinLedger.MerkleProtocol
import BitcoinLedger.Musig2
import BitcoinLedger.SilentPayments
import BitcoinLedger.AppStateMachine
import BitcoinLedger.FreestandingKernels

namespace BitcoinLedger

def appVersion : Spec.AppVersion :=
  Spec.ledgerBitcoinTargetVersion

end BitcoinLedger

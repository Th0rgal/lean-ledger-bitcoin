import InternalSpec
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

/-- Semantic version of the upstream Ledger Bitcoin app this project tracks. -/
structure AppVersion where
  major : UInt8
  minor : UInt8
  patch : UInt8
  deriving Repr, DecidableEq, Inhabited

/-- Pinned upstream version (`2.4.1`). -/
def appVersion : AppVersion :=
  { major := 2, minor := 4, patch := 1 }

end BitcoinLedger

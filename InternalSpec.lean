import InternalSpec.Basic
import InternalSpec.Bip32
import InternalSpec.Script
import InternalSpec.WalletPolicy
import InternalSpec.Psbt
import InternalSpec.MerkleProtocol
import InternalSpec.Musig2
import InternalSpec.SilentPayments
import InternalSpec.AppStateMachine
import InternalSpec.Unified

namespace InternalSpec

structure AppVersion where
  major : UInt8
  minor : UInt8
  patch : UInt8
  deriving Repr, DecidableEq, Inhabited

def ledgerBitcoinTargetVersion : AppVersion :=
  { major := 2, minor := 4, patch := 1 }

end InternalSpec

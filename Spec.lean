import Spec.Basic
import Spec.Bip32
import Spec.Script
import Spec.WalletPolicy
import Spec.Psbt
import Spec.MerkleProtocol
import Spec.Musig2
import Spec.SilentPayments
import Spec.AppStateMachine
import Spec.Unified

namespace Spec

structure AppVersion where
  major : UInt8
  minor : UInt8
  patch : UInt8
  deriving Repr, DecidableEq, Inhabited

def ledgerBitcoinTargetVersion : AppVersion :=
  { major := 2, minor := 4, patch := 1 }

end Spec

import Spec
import BitcoinLedger

namespace Proofs

theorem appVersion_matches_spec :
    BitcoinLedger.appVersion = Spec.ledgerBitcoinTargetVersion := by
  rfl

end Proofs

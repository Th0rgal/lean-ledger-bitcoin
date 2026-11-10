namespace Spec

structure AppVersion where
  major : UInt8
  minor : UInt8
  patch : UInt8
  deriving Repr, DecidableEq, Inhabited

def ledgerBitcoinTargetVersion : AppVersion :=
  { major := 2, minor := 4, patch := 1 }

end Spec

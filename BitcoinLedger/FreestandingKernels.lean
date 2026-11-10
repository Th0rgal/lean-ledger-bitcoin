namespace BitcoinLedger.FreestandingKernels

@[export llb_version_packed]
def llbVersionPacked : UInt32 :=
  ((2 : UInt32) <<< 16) ||| ((4 : UInt32) <<< 8) ||| (1 : UInt32)

end BitcoinLedger.FreestandingKernels

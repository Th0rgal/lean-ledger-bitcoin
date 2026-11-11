import Spec
import InternalSpec
import Proofs
import Lean

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  let mut specCount := 0
  let mut specThmCount := 0
  let mut internalSpecCount := 0
  let mut internalSpecThmCount := 0
  let mut proofCount := 0
  let mut proofThmCount := 0
  let mut bad : List (Name × List Name) := []
  for (n, ci) in env.constants.map₁.toList do
    let s := n.toString
    if (s.startsWith "Spec." || s.startsWith "InternalSpec." || s.startsWith "Proofs.") && !n.isInternal then
      if s.startsWith "Spec." then
        specCount := specCount + 1
        if ci matches .thmInfo _ then specThmCount := specThmCount + 1
      else if s.startsWith "InternalSpec." then
        internalSpecCount := internalSpecCount + 1
        if ci matches .thmInfo _ then internalSpecThmCount := internalSpecThmCount + 1
      else
        proofCount := proofCount + 1
        if ci matches .thmInfo _ then proofThmCount := proofThmCount + 1
      let axs ← collectAxioms n
      let disallowed := axs.toList.filter fun ax =>
        ax != ``propext && ax != ``Quot.sound
      if !disallowed.isEmpty then
        bad := (n, disallowed) :: bad
  IO.println s!"Audited {specCount} Spec.* ({specThmCount} thms), {internalSpecCount} InternalSpec.* ({internalSpecThmCount} thms), and {proofCount} Proofs.* ({proofThmCount} thms) declarations."
  if bad.isEmpty then
    IO.println "PASS: 0 sorryAx, 0 ofReduceBool, 0 trustCompiler, 0 Classical.choice across all Spec.*, InternalSpec.*, and Proofs.* declarations!"
  else
    for (n, axs) in bad do
      IO.println s!"FAIL: {n} uses disallowed axioms {axs}"
    throwError "Disallowed axioms detected!"

import Spec
import InternalSpec
import Proofs
import Lean

open Lean

/-!
Axiom audit. Fails the build if any declaration of the compiled kernel, of `Spec`, of
`Proofs` or of `InternalSpec` depends on an axiom other than `propext` and `Quot.sound`
(so no `sorryAx`, no `Classical.choice`, no `ofReduceBool`), and prints the axioms of the
headline theorem `Proofs.KernelSpec.kernel_meets_spec`.
-/

#eval show CoreM Unit from do
  let env ← getEnv
  let prefixes := ["BitcoinLedger.FreestandingKernels.", "Spec.", "Proofs.", "InternalSpec."]
  let mut counts : Std.HashMap String (Nat × Nat) := {}
  let mut bad : List (Name × List Name) := []
  for (n, ci) in env.constants.map₁.toList do
    let s := n.toString
    if n.isInternal then continue
    match prefixes.find? (fun p => s.startsWith p) with
    | none => pure ()
    | some p =>
      let (decls, thms) := counts.getD p (0, 0)
      counts := counts.insert p (decls + 1, if ci matches .thmInfo _ then thms + 1 else thms)
      let axs ← collectAxioms n
      let disallowed := axs.toList.filter fun ax => ax != ``propext && ax != ``Quot.sound
      if !disallowed.isEmpty then
        bad := (n, disallowed) :: bad
  for p in prefixes do
    let (decls, thms) := counts.getD p (0, 0)
    IO.println s!"Audited {p}* : {decls} declarations, {thms} theorems"
  let headline ← collectAxioms ``Proofs.KernelSpec.kernel_meets_spec
  IO.println s!"Proofs.KernelSpec.kernel_meets_spec depends on axioms: {headline.toList}"
  if bad.isEmpty then
    IO.println "PASS: 0 sorryAx, 0 ofReduceBool, 0 trustCompiler, 0 Classical.choice across the kernel, Spec.*, Proofs.* and InternalSpec.*"
  else
    for (n, axs) in bad do
      IO.println s!"FAIL: {n} uses disallowed axioms {axs}"
    throwError "Disallowed axioms detected!"

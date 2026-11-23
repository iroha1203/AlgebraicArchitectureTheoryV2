import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! # Standard kernel axioms

Audit declarations in a named namespace of the current module, including
private declarations and nested namespaces. Lean computes their transitive
kernel dependencies, including dependencies from imported modules.
-/

open Lean Elab Command

namespace SHIGURE

/-- Kernel assumptions permitted in audited declarations. -/
private def standardAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Reject an empty audit or a declaration depending on a nonstandard kernel assumption. -/
elab "#shigure_assert_standard_axioms_only " target:ident : command => do
  let namespaceName := target.getId
  let env ← getEnv
  -- Stage two contains the current module's declarations, including pending proofs.
  let declarations := env.constants.foldStage2 (s := #[]) fun names name _ =>
    let userName := privateToUserName name
    if namespaceName != userName && namespaceName.isPrefixOf userName then names.push name else names
  if declarations.isEmpty then
    throwErrorAt target "No declarations in namespace '{namespaceName}' in the current module"
  for name in declarations do
    let unexpected := (← collectAxioms name).filter (!standardAxioms.contains ·)
    unless unexpected.isEmpty do
      let unexpectedNames := unexpected.toList.map privateToUserName
      throwErrorAt target
        "Declaration '{privateToUserName name}' depends on nonstandard kernel assumptions: {unexpectedNames}"

end SHIGURE

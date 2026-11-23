module

public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms

/-! # Standard kernel axioms

Audit declarations in a named namespace of the current module, including
private declarations and nested namespaces. Lean computes their transitive
kernel dependencies, including dependencies from imported modules.

## Implementation notes

Start from the current environment, which contains the bodies of local
declarations. A walk using only that environment can report an imported
theorem as an assumption when its module exports the statement alone. A
private import supplies the original proof bodies for those reported
dependencies.
-/

open Lean Elab Command

public meta section

namespace SHIGURE

/-- Recognize the three standard kernel assumptions permitted in SHIGURE. -/
def isStandardAxiom (name : Name) : Bool :=
  #[``propext, ``Classical.choice, ``Quot.sound].contains name

/-- Load the proof bodies of imported modules when the current view exports only statements. -/
def importProofEnvironment (env : Environment) : IO (Option Environment) :=
  if env.header.isModule then
    some <$> importModules env.header.imports {} (level := .private)
  else pure none

/-- Collect kernel dependencies and follow imported theorem bodies hidden by module exports. -/
def kernelAxioms (env : Environment) (proofImports : Option Environment) (names : Array Name) :
    Array Name := Id.run do
  let (_, dependencies) := ((names.forM CollectAxioms.collect).run env).run {}
  let some proofImports := proofImports | return dependencies.axioms
  let (imported, retained) := dependencies.axioms.partition fun name =>
    env.isImportedConst name && (proofImports.find? name).isSome
  let (_, resolved) := ((imported.forM CollectAxioms.collect).run proofImports).run {}
  return retained ++ resolved.axioms

/-- Reject an empty audit or a declaration depending on a nonstandard kernel assumption. -/
elab (name := assertStandardAxiomsOnly) "#shigure_assert_standard_axioms_only " target:ident :
    command => do
  let namespaceName := target.getId
  let env ← getEnv
  -- Stage two contains the current module's declarations, including pending proofs.
  let declarations := env.constants.foldStage2 (s := #[]) fun names name _ =>
    let userName := privateToUserName name
    if namespaceName != userName && namespaceName.isPrefixOf userName then names.push name else names
  if declarations.isEmpty then
    throwErrorAt target "No declarations in namespace '{namespaceName}' in the current module"
  let proofImports ← importProofEnvironment env
  for name in declarations do
    let unexpected := (kernelAxioms env proofImports #[name]).filter (!isStandardAxiom ·)
    unless unexpected.isEmpty do
      let unexpectedNames := unexpected.toList.map privateToUserName
      throwErrorAt target
        "Declaration '{privateToUserName name}' depends on nonstandard kernel assumptions: {unexpectedNames}"

end SHIGURE

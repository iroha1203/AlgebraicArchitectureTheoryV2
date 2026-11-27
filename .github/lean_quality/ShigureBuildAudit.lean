import Lean.Elab.Frontend
import Lean.Server.InfoUtils
import Lean.Util.CollectAxioms

/-! # Source validation in the SHIGURE build frontend -/

open Lean Elab Command

private def standardAxiom (name : Name) : Bool :=
  #[``propext, ``Classical.choice, ``Quot.sound].contains name

private partial def checkSyntax (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | .node _ _ children =>
    if children[0]?.any (·.getAtomVal == "set_option") &&
        children[1]?.any (fun ident => ident.getId.eraseMacroScopes == `debug.skipKernelTC) &&
        children[3]?.any (·.getAtomVal == "true") then
      logErrorAt stx "disallowed syntax debug.skipKernelTC"
    children.forM checkSyntax
  | .atom _ value =>
    if ["axiom", "admit", "sorry", "unsafe", "native_decide"].contains value then
      logErrorAt stx m!"disallowed syntax {value}"
  | _ => pure ()

private unsafe def ptrAddrOfImpl {α : Type u} (a : α) : USize :=
  ptrAddrUnsafe a

@[implemented_by ptrAddrOfImpl]
private opaque ptrAddrOf {α : Type u} (a : α) : USize := 0

private def survivesChecked (current final : Environment) (name : Name) : Bool :=
  match current.checked.get.find? name, final.checked.get.find? name with
  | some earlier, some later =>
    ptrAddrOf earlier == ptrAddrOf later ||
      (earlier.type == later.type && earlier.value? true == later.value? true)
  | _, _ => false

/-- Collect kernel axioms from local declarations in `current` that do not survive unchanged in `final`. -/
private def collectEnvTransientAxioms (current final : Environment) (found : NameSet) : NameSet :=
  if ptrAddrOf current == ptrAddrOf final ||
      ptrAddrOf current.constants.map₂ == ptrAddrOf final.constants.map₂ then
    found
  else
    let temporary := current.constants.foldStage2 (s := #[]) fun acc name earlier =>
      match final.constants.map₂.find? name with
      | some later =>
        if ptrAddrOf earlier == ptrAddrOf later || survivesChecked current final name then acc
        else acc.push name
      | none => acc.push name
    if temporary.isEmpty then found
    else
      let (_, dependencies) := ((temporary.forM CollectAxioms.collect).run current).run {}
      dependencies.axioms.foldl (fun names name => names.insert name) found

private def transientAxioms (trees : PersistentArray InfoTree) (final : Environment) : NameSet := Id.run do
  let mut seen : Std.HashSet USize := {}
  seen := seen.insert (ptrAddrOf final)
  let mut found : NameSet := {}
  for tree in trees do
    (seen, found) := tree.foldInfo (init := (seen, found)) fun ctx _ (seen, found) =>
      let addr := ptrAddrOf ctx.env
      if seen.contains addr then (seen, found)
      else (seen.insert addr, collectEnvTransientAxioms ctx.env final found)
  return found

private def checkTransient (stx : Syntax) : CommandElabM Unit := do
  let final ← getEnv
  let info ← getInfoState
  if info.trees.any (fun tree =>
      tree.foldInfo (init := false) fun ctx _ found => found || debug.skipKernelTC.get ctx.options) then
    logErrorAt stx "kernel checking was disabled during elaboration"
  let dependencies := transientAxioms info.trees final
  let unexpected := dependencies.toList.filter (!standardAxiom ·)
  unless unexpected.isEmpty do
    let unexplained ← if final.header.isModule then do
      let proofImports ← importModules final.header.imports {} (level := .private)
      let (imported, localAxioms) := unexpected.partition fun name =>
        final.isImportedConst name && (proofImports.find? name).isSome
      let (_, resolved) := ((imported.forM CollectAxioms.collect).run proofImports).run {}
      pure (localAxioms ++ resolved.axioms.toList.filter (!standardAxiom ·))
    else pure unexpected
    for axiomName in unexplained do
      logErrorAt stx m!"nonstandard kernel assumption {axiomName}"

private def runSourceAudit (stx : Syntax) : CommandElabM Unit := do
  let name := (← getEnv).mainModule
  unless name == `Formal.SHIGURE || (`Formal.SHIGURE).isPrefixOf name do return
  let some stampDirectory ← IO.getEnv "SHIGURE_AUDIT_STAMPS" | return
  checkSyntax stx
  checkTransient stx
  if stx.isOfKind ``Parser.Command.eoi then
    let content ← IO.FS.readFile (← read).fileName
    let guard := content.contains "#guard_msgs"
    IO.FS.writeFile (System.FilePath.mk stampDirectory / name.toString)
      (if guard then "frontend" else "checked")

initialize addLinter { name := `shigureBuildAudit, run := runSourceAudit }

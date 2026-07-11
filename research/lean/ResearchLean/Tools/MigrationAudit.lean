import Lean

namespace ResearchLean.Tools.MigrationAudit

open Lean Elab Command

private def normalizeName (name : Name) : String :=
  let userName := privateToUserName name
  let oldPrefix := Name.mkStr `Formal.AG "Research"
  let newPrefix := `ResearchLean.AG
  let sentinel := Name.mkSimple "$RESEARCH"
  let normalized := if oldPrefix.isPrefixOf userName then
    userName.replacePrefix oldPrefix sentinel
  else if newPrefix.isPrefixOf userName then
    userName.replacePrefix newPrefix sentinel
  else
    userName
  -- Lean-generated private binder names can embed the declaring module path
  -- as a string (for example a private binder with an embedded legacy path).
  -- Canonicalize those embedded paths as well so a package-root move does
  -- not alter the declaration digest.
  (normalized.toString.replace "«$RESEARCH»" "$RESEARCH")
    |>.replace ("Formal.AG.Resear" ++ "ch.") "$RESEARCH."
    |>.replace "ResearchLean.AG." "$RESEARCH."

mutual
  private partial def serializeLevel : Level → String
    | .zero => "z"
    | .succ level => s!"s({serializeLevel level})"
    | .max left right => s!"m({serializeLevel left},{serializeLevel right})"
    | .imax left right => s!"i({serializeLevel left},{serializeLevel right})"
    | .param name => s!"p({normalizeName name})"
    | .mvar id => s!"u({id.name})"

  private partial def serializeExpr : Expr → String
    | .bvar index => s!"b({index})"
    | .fvar id => s!"f({id.name})"
    | .mvar id => s!"?({id.name})"
    | .sort level => s!"S({serializeLevel level})"
    | .const name levels =>
        s!"c({normalizeName name};{String.intercalate "," (levels.map serializeLevel)})"
    | .app function argument => s!"a({serializeExpr function},{serializeExpr argument})"
    | .lam name type body binderInfo =>
        s!"l({normalizeName name};{reprStr binderInfo};{serializeExpr type};{serializeExpr body})"
    | .forallE name type body binderInfo =>
        s!"P({normalizeName name};{reprStr binderInfo};{serializeExpr type};{serializeExpr body})"
    | .letE name type value body nondep =>
        s!"L({normalizeName name};{nondep};{serializeExpr type};{serializeExpr value};{serializeExpr body})"
    | .lit literal => s!"v({reprStr literal})"
    | .mdata _ expression => serializeExpr expression
    | .proj typeName index structureExpr =>
        s!"r({normalizeName typeName};{index};{serializeExpr structureExpr})"
end

private def tabSafe (value : String) : String :=
  value.replace "\t" "\\t" |>.replace "\n" "\\n" |>.replace "\r" "\\r"

elab "#emit_migration_audit " moduleName:ident : command => do
  let env ← getEnv
  let moduleId := moduleName.getId
  let some moduleIdx := env.getModuleIdx? moduleId
    | throwError "E_MIGRATION_MODULE: module not imported: {moduleId}"
  let mut declarations : Array (Name × ConstantInfo) := #[]
  for name in env.const2ModIdx.keysArray do
    if env.getModuleIdxFor? name == some moduleIdx then
      if let some info := env.find? name then
        declarations := declarations.push (name, info)
  if declarations.isEmpty then
    throwError "E_MIGRATION_EMPTY: no declarations for {moduleId}"
  let sortedDeclarations := declarations.qsort fun left right => left.1.toString < right.1.toString
  for (name, info) in sortedDeclarations do
    let axioms ← liftCoreM <| collectAxioms name
    let axiomNames := axioms.toList.map normalizeName |>.mergeSort
    let axiomPayload := if axiomNames.isEmpty then "$NO_AXIOMS" else String.intercalate "," axiomNames
    let levels := info.levelParams.map normalizeName
    let value := info.value? (allowOpaque := true) |>.map serializeExpr |>.getD "$NO_VALUE"
    let fields := [
      "MIGRATION_DECL",
      normalizeName moduleId,
      normalizeName name,
      String.intercalate "," levels,
      serializeExpr info.type,
      value,
      axiomPayload
    ].map tabSafe
    liftIO <| IO.println (String.intercalate "\t" fields)

end ResearchLean.Tools.MigrationAudit

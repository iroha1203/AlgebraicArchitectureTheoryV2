import Lean

/-! Completion evidence extraction. References are syntactic, never a semantic proof-use verdict. -/
open Lean

private def obj (xs : List (String × Json)) : Json := Json.mkObj xs
private def str (s : String) : Json := toJson s

private partial def refs (e : Expr) (site : String) (pos : String := "") : Array Json :=
  match e with
  | .const n _ => #[obj [("name", str n.toString), ("site", str site), ("position", str pos)]]
  | .app f a => refs f site (pos ++ "/function") ++ refs a site (pos ++ "/argument")
  | .lam _ t b _ | .forallE _ t b _ =>
    refs t "type" (pos ++ "/binder") ++ refs b site (pos ++ "/body")
  | .letE _ t v b _ => refs t "type" (pos ++ "/binder") ++
    refs v site (pos ++ "/value") ++ refs b site (pos ++ "/body")
  | .mdata _ b => refs b site pos
  | .proj n i b => #[obj [("name", str n.toString), ("site", str "projection"),
      ("position", str (pos ++ "/" ++ toString i))]] ++ refs b site (pos ++ "/structure")
  | _ => #[]

-- The literal AST below makes every branch of refs independently inspectable.
-- Its expected names, sites and positions are written independently in Python.
private def referenceFixture : Json := Id.run do
  let c (s : String) := Expr.const s.toName []
  let cases : List (String × Expr) := [
    ("const", c "C"),
    ("app", .app (c "F") (c "A")),
    ("lambda", .lam `x (c "T") (c "B") .default),
    ("forall", .forallE `x (c "T") (c "B") .default),
    ("let", .letE `x (c "T") (c "Unused") (c "B") false),
    ("projection", .proj `Record 2 (c "R")),
    ("metadata", .mdata {} (c "M")),
    ("bvar", .bvar 0), ("fvar", .fvar ⟨`x⟩), ("mvar", .mvar ⟨`x⟩),
    ("sort", .sort .zero), ("literal", .lit (.natVal 3))]
  return obj (cases.map fun (label, expression) => (label, toJson (refs expression "term")))

private def row (env : Environment) (n : Name) (info : ConstantInfo) : CoreM Json := do
  let axs ← collectAxioms n
  let owner := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  let value := info.value? (allowOpaque := true)
  let display ← (Meta.ppExpr info.type).run'
  let ranges ← findDeclarationRanges? n
  let sourceRange := ranges.map fun r => obj [
    ("start_line", toJson r.range.pos.line), ("start_column", toJson r.range.pos.column),
    ("end_line", toJson r.range.endPos.line), ("end_column", toJson r.range.endPos.column)]
  let kind := match info with
    | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
    | .axiomInfo _ => (reprStr (ConstantKind.ofConstantInfo info)).splitOn "." |>.getLast!
    | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
  let typeEdges := (refs info.type "type").map (fun e => e.setObjVal! "origin" (str "type"))
  let valueEdges := (value.map (fun v => refs v "term") |>.getD #[]).map (fun e => e.setObjVal! "origin" (str "value"))
  let edges := typeEdges ++ valueEdges
  -- Independent upstream traversal checks complete constant-name coverage.
  -- Projection labels are additional metadata, not Expr.const occurrences.
  let typeNames := info.type.getUsedConstants.toList.map Name.toString |>.mergeSort
  let valueNames := (value.map Expr.getUsedConstants |>.getD #[]).toList.map Name.toString |>.mergeSort
  return obj [("name", str n.toString), ("owner", str (owner.getD env.mainModule).toString),
    ("kind", str kind), ("universe_parameters", toJson (info.levelParams.map Name.toString)),
    ("type_display", str display.pretty), ("source_range", sourceRange.getD Json.null),
    ("type", str (reprStr info.type)), ("value", value.map (fun v => str (reprStr v)) |>.getD Json.null),
    ("axioms", toJson (axs.toList.map Name.toString |>.mergeSort)),
    ("constant_names", obj [("type", toJson typeNames), ("value", toJson valueNames)]),
    ("references", toJson edges)]

/-- Extract exact requested declarations and their reachable values within the selected owners.
External references remain typed terminal records. No build is performed by this program. -/
def main (args : List String) : IO UInt32 := do
  if args == ["--reference-fixture"] then
    IO.println referenceFixture.compress
    return 0
  let modules := args.toArray.map String.toName
  if modules.isEmpty then
    IO.eprintln "usage: CompletionAudit.lean OWNER_MODULE ..."
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun n => { module := n }) {} 0
  let action : CoreM Json := do
    let mut rows := #[]
    let mut terminals : NameSet := {}
    let names := env.constants.toList.map Prod.fst |>.mergeSort (fun a b => a.toString ≤ b.toString)
    for n in names do
      let some idx := env.getModuleIdxFor? n | continue
      if modules.contains env.header.moduleNames[idx.toNat]! then
        let some info := env.find? n | continue
        rows := rows.push (← row env n info)
        for edge in refs info.type "type" ++ (info.value? (allowOpaque := true) |>.map (fun v => refs v "term") |>.getD #[]) do
          if let .ok name := edge.getObjValAs? String "name" then
            let dep := name.toName
            let external := (env.getModuleIdxFor? dep).map (fun i => !modules.contains env.header.moduleNames[i.toNat]!) |>.getD true
            if external then terminals := terminals.insert dep
    let mut externalRows := #[]
    for n in terminals.toList.mergeSort (fun a b => a.toString ≤ b.toString) do
      if let some info := env.find? n then
        let owner := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
        externalRows := externalRows.push (obj [("name", str n.toString),
          ("owner", str (owner.getD env.mainModule).toString), ("type", str (reprStr info.type))])
    return obj [("schema_version", toJson (3 : Nat)), ("modules", toJson (modules.map Name.toString)),
      ("declarations", toJson rows), ("terminals", toJson externalRows)]
  let (result, _) ← (action.toIO { fileName := "CompletionAudit", fileMap := default } { env := env })
  IO.println result.compress
  return 0

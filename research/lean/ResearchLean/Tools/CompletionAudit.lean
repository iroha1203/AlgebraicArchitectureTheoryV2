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

private def row (env : Environment) (n : Name) (info : ConstantInfo) : CoreM Json := do
  let axs ← collectAxioms n
  let owner := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  let value := info.value? (allowOpaque := true)
  let edges := refs info.type "type" ++ (value.map (fun v => refs v "term") |>.getD #[])
  return obj [("name", str n.toString), ("owner", str (owner.getD env.mainModule).toString),
    ("type", str (reprStr info.type)), ("value", value.map (fun v => str (reprStr v)) |>.getD Json.null),
    ("axioms", toJson (axs.toList.map Name.toString |>.mergeSort)),
    ("references", toJson edges)]

/-- Extract exact requested declarations and their reachable values within the selected owners.
External references remain typed terminal records. No build is performed by this program. -/
def main (args : List String) : IO UInt32 := do
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
    return obj [("schema_version", toJson (2 : Nat)), ("modules", toJson (modules.map Name.toString)),
      ("declarations", toJson rows), ("terminals", toJson externalRows)]
  let (result, _) ← (action.toIO { fileName := "CompletionAudit", fileMap := default } { env := env })
  IO.println result.compress
  return 0

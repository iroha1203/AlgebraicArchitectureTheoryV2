import Lean

/-! Print the transitive module names loaded for explicit owner modules.
This performs no build and is used only to inventory already-built artifacts. -/
open Lean

/-- Load explicit modules and report their complete imported-module set. -/
def main (args : List String) : IO UInt32 := do
  let modules := args.toArray.map String.toName
  if modules.isEmpty then
    IO.eprintln "usage: CompletionRegistry.lean OWNER_MODULE ..."
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun n => { module := n }) {} 0
  let names := env.header.moduleNames.map Name.toString |>.qsort (fun a b => a < b)
  IO.println (toJson names).compress
  return 0

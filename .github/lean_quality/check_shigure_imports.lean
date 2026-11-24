import Lean.Elab.Import

/-! # SHIGURE import validation -/

open Lean

/-- Allow dependencies on the toolchain, mathlib, and production SHIGURE modules. -/
private def allowedImport (name : Name) : Bool :=
  name != `Formal.SHIGURE.AssertStandardAxiomsTest &&
    [`Mathlib, `Std, `Lean, `Formal.SHIGURE].any (fun root =>
      root.isPrefixOf name && root != name)

/-- Validate explicit imports using the same header parser as the Lean frontend. -/
private def checkSource (file : System.FilePath) : IO (Option (Array Name)) := do
  let text ← IO.FS.readFile file
  let fileName := file.toString
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext text fileName)
  for message in messages.toList do
    IO.eprint (← message.toString)
  let mut valid := !messages.hasErrors
  let imports := Elab.HeaderSyntax.imports header (includeInit := false)
  for entry in imports do
    unless allowedImport entry.module do
      IO.eprintln s!"{file}: disallowed import {entry.module}"
      valid := false
  return if valid then some (imports.map (·.module)) else none

/-- Validate the SHIGURE import boundary and optionally list cache roots. -/
def main (args : List String) : IO UInt32 := do
  unless args.isEmpty || args == ["--mathlib-imports"] do
    IO.eprintln "usage: lean --run check_shigure_imports.lean [--mathlib-imports]"
    return 1
  let files ← (System.FilePath.mk "Formal/SHIGURE").walkDir
  let files := (files.filter (·.extension == some "lean")).push "Formal/SHIGURE.lean"
  let mut valid := true
  let mut mathlib : NameSet := {}
  for file in files do
    if let some imports ← checkSource file then
      for name in imports do
        if name.getRoot == `Mathlib then
          mathlib := mathlib.insert name
    else
      valid := false
  if valid && !args.isEmpty then
    for name in mathlib.toList.mergeSort Name.quickLt do
      IO.println name
  return if valid then 0 else 1

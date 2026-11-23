import Lean.Elab.Import

open Lean

private def allowedImport (name : Name) : Bool :=
  [`Mathlib, `Std, `Lean, `Formal.SHIGURE].any (fun root =>
    root.isPrefixOf name && root != name)

private def forbiddenWords : List String :=
  ["sorry", "admit", "axiom", "unsafe", "native_decide"]

private def checkSource (file : System.FilePath) : IO Bool := do
  let text ← IO.FS.readFile file
  let fileName := file.toString
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext text fileName)
  for message in messages.toList do
    IO.eprint (← message.toString)
  let mut valid := !messages.hasErrors
  for entry in Elab.HeaderSyntax.imports header (includeInit := false) do
    unless allowedImport entry.module do
      IO.eprintln s!"{file}: disallowed import {entry.module}"
      valid := false
  for (line, index) in (text.splitOn "\n").zipIdx do
    -- A single named declaration is reserved for the rejection regression.
    unless fileName == "Formal/SHIGURE/AssertStandardAxiomsTest.lean" &&
        line == "axiom SHIGURE.KernelAuditTest.nonstandard : False" do
      let words := line.splitToList (fun ch => !(ch.isAlphanum || ch == '_'))
      for word in forbiddenWords do
        if words.contains word then
          IO.eprintln s!"{file}:{index + 1}: disallowed source token {word}"
          valid := false
  return valid

/-- Run from the repository root with `lean --run`. -/
def main : IO UInt32 := do
  let files ← (System.FilePath.mk "Formal/SHIGURE").walkDir
  let files := (files.filter (·.extension == some "lean")).push "Formal/SHIGURE.lean"
  let mut valid := true
  for file in files do
    unless ← checkSource file do
      valid := false
  return if valid then 0 else 1

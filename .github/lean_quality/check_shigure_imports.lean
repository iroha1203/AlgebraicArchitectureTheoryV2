import Lean.Elab.Import

/-! # SHIGURE import validation -/

open Lean

/-- Allow dependencies on the toolchain, mathlib, and production SHIGURE modules. -/
private def allowedImport (name : Name) : Bool :=
  name != `Formal.SHIGURE.AssertStandardAxiomsTest &&
    [`Mathlib, `Std, `Lean, `Formal.SHIGURE].any (fun root =>
      root.isPrefixOf name && root != name)

/-- Validate explicit imports using the same header parser as the Lean frontend. -/
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

import Lean.Elab.Frontend
import Lean.Server.InfoUtils
import Formal.SHIGURE.AssertStandardAxioms

/-! # SHIGURE source and kernel validation

Audit named production declarations in the build outputs, including private declarations.
The standalone frontend also checks source syntax, transient proofs, and
elaboration controls. Use it for the independent audit, its negative fixtures,
and sources that need an exact elaboration environment.
-/

open Lean Elab

/-- Find forbidden syntax and changes to kernel checking, preserving source positions. -/
private partial def forbiddenSyntax : Syntax → Array (String × String.Pos.Raw)
  | .node _ _ children =>
    if children[0]?.any (·.getAtomVal == "set_option") &&
        children[1]?.any (fun stx => stx.getId.eraseMacroScopes == `debug.skipKernelTC) &&
        children[3]?.any (·.getAtomVal == "true") then
      #[("debug.skipKernelTC", children[1]!.getPos?.getD 0)] ++ children.flatMap forbiddenSyntax
    else children.flatMap forbiddenSyntax
  | stx@(.atom _ value) =>
    if ["axiom", "admit", "sorry", "unsafe", "native_decide"].contains value then
      #[(value, stx.getPos?.getD 0)]
    else #[]
  | _ => #[]

/-- The scope of the single negative fixture allowed by the source check. -/
private def isAuditTest (moduleName : Name) : Bool :=
  moduleName == `Formal.SHIGURE.AssertStandardAxiomsTest

/-- Test declarations deliberately responsible for the custom assumption. -/
private def isRejectionFixture (moduleName name : Name) : Bool :=
  isAuditTest moduleName && isPrivateName name &&
    [`SHIGURE.KernelAuditTest.nonstandard, `SHIGURE.KernelAuditTest.Rejected.derived].contains
      (privateToUserName name)

/-- Check that the frontend processed the whole file and ran the final audit command directly. -/
private def checkTermination (fileName : String) (moduleName : Name) (commands : Array Syntax) :
    IO Bool := do
  unless commands.back?.any (·.isOfKind `Lean.Parser.Command.eoi) do
    IO.eprintln s!"{fileName}: the Lean frontend did not reach the end of the file"
    return false
  if moduleName == `Formal.SHIGURE.AxiomAudit then
    let lastCommand := commands[commands.size - 2]?.getD .missing
    unless lastCommand.isOfKind `SHIGURE.assertStandardAxiomsOnly &&
        lastCommand[1].getId == `SHIGURE.AxiomAudit do
      IO.eprintln s!"{fileName}: the final command must run the SHIGURE audit at top level"
      return false
  return true

/-- Reject forbidden command and term syntax, with one exact fixture exception. -/
private def checkSyntax (input : Parser.InputContext) (moduleName : Name)
    (commands : Array Syntax) : IO Bool := do
  let lines := (input.inputString.splitOn "\n").toArray
  let mut valid := true
  let mut allowedFixture := false
  for (token, offset) in commands.flatMap forbiddenSyntax do
    let pos := input.fileMap.toPosition offset
    let line := lines[pos.line - 1]?.getD ""
    if isAuditTest moduleName && !allowedFixture && token == "axiom" &&
        line == "private axiom SHIGURE.KernelAuditTest.nonstandard : False" then
      allowedFixture := true
    else
      IO.eprintln s!"{input.fileName}:{pos.line}:{pos.column}: disallowed syntax {token}"
      valid := false
  return valid

private unsafe def ptrAddrOfImpl {α : Type u} (a : α) : USize :=
  ptrAddrUnsafe a

@[implemented_by ptrAddrOfImpl]
private opaque ptrAddrOf {α : Type u} (a : α) : USize := 0

/-- A name reused after an anonymous declaration can refer to a different kernel proof. -/
private def survivesChecked (current final : Environment) (name : Name) : Bool :=
  match current.checked.get.find? name, final.checked.get.find? name with
  | some earlier, some later =>
    ptrAddrOf earlier == ptrAddrOf later ||
      (earlier.type == later.type && earlier.value? true == later.value? true)
  | _, _ => false

/-- Check proof terms in temporary environments that do not survive their command. -/
private def transientAxioms (state : Frontend.State) (proofImports : Option Environment) :
    NameSet := Id.run do
  let env := state.commandState.env
  let mut seen : Std.HashSet USize := {}
  seen := seen.insert (ptrAddrOf env)
  let mut found : NameSet := {}
  for tree in state.commandState.infoState.trees do
    (seen, found) := tree.foldInfo (init := (seen, found)) fun ctx _ (seen, found) =>
      let addr := ptrAddrOf ctx.env
      if seen.contains addr then (seen, found)
      else
        let seen := seen.insert addr
        if ptrAddrOf ctx.env.constants.map₂ == ptrAddrOf env.constants.map₂ then
          (seen, found)
        else
          let temporary := ctx.env.constants.foldStage2 (s := #[]) fun acc name earlier =>
            match env.constants.map₂.find? name with
            | some later =>
              if ptrAddrOf earlier == ptrAddrOf later || survivesChecked ctx.env env name then acc
              else acc.push name
            | none => acc.push name
          if temporary.isEmpty then (seen, found)
          else
            let discovered := SHIGURE.kernelAxioms ctx.env proofImports temporary
            (seen, discovered.foldl (fun acc name => acc.insert name) found)
  return found

/-- Check the effective kernel setting during elaboration, including options set by macros. -/
private def keepsKernelChecking (fileName : String) (state : Frontend.State) : IO Bool := do
  let disabled := state.commandState.infoState.trees.any fun tree =>
    tree.foldInfo (init := false) fun ctx _ found => found || debug.skipKernelTC.get ctx.options
  if disabled then
    IO.eprintln s!"{fileName}: kernel checking was disabled during elaboration"
  return !disabled

/-- Follow transitive kernel dependencies for named declarations and anonymous proofs. -/
private def checkDependencies (fileName : String) (moduleName : Name) (state : Frontend.State) :
    IO Bool := do
  let env := state.commandState.env
  let declarations := env.constants.foldStage2 (fun names name _ => names.push name) #[]
  let proofImports ← SHIGURE.importProofEnvironment env
  let mut valid := true
  for name in declarations do
    if (env.find? name).any (·.isUnsafe) then
      IO.eprintln s!"{fileName}: unsafe declaration {name}"
      valid := false
  let (fixtures, production) := declarations.partition (isRejectionFixture moduleName)
  let named := SHIGURE.kernelAxioms env proofImports production
  let fixtureDependencies := (SHIGURE.kernelAxioms env proofImports fixtures).filter fun name =>
    !(isPrivateName name && privateToUserName name == `SHIGURE.KernelAuditTest.nonstandard)
  for dependency in named ++ fixtureDependencies ++ (transientAxioms state proofImports).toArray do
    unless SHIGURE.isStandardAxiom dependency do
      IO.eprintln s!"{fileName}: nonstandard kernel assumption {dependency}"
      valid := false
  return valid

/-- Run the Lean frontend and syntax and kernel checks for one file in a disposable process. -/
private unsafe def checkFile (file : System.FilePath) : IO Bool := do
  let input := Parser.mkInputContext (← IO.FS.readFile file) file.toString
  let moduleName ← moduleNameOfFileName file none
  let (header, parserState, messages) ← Parser.parseHeader input
  -- This is the frontend's startup step. Imported tactic extensions need their initializers.
  Lean.enableInitializersExecution
  let (env, messages) ← processHeader header {} messages input (leakEnv := true) (mainModule := moduleName)
  let state ← Elab.IO.processCommands input parserState (Command.mkState env messages {})
  let messages := state.commandState.messages
  for message in messages.toList do
    if message.severity == .error then
      IO.eprint (← message.toString)
  let complete ← checkTermination file.toString moduleName state.commands
  let syntaxValid ← checkSyntax input moduleName state.commands
  let kernelEnabled ← keepsKernelChecking file.toString state
  let kernelValid ← checkDependencies file.toString moduleName state
  return !messages.hasErrors && complete && syntaxValid && kernelEnabled && kernelValid

/-- These files are read independently, including the deliberately rejected declarations. -/
private def isAuditSource (name : Name) : Bool :=
  name == `Formal.SHIGURE.AxiomAudit || isAuditTest name

/-- Audit all production declarations from the same build in one private import.
If `separateOut?` is provided, record modules with cross-module name collisions to that NUL-delimited
file so the caller can audit them after this process releases the combined environment. -/
private unsafe def checkCompiled (files : List String)
    (separateOut? : Option System.FilePath := none) (isolated : Bool := false) : IO Bool := do
  let mut sources : NameMap System.FilePath := {}
  for file in files do
    let path := System.FilePath.mk file
    let name ← moduleNameOfFileName path none
    unless isAuditSource name do
      sources := sources.insert name path
  let modules := sources.toList.toArray.map Prod.fst
  if modules.isEmpty then
    IO.eprintln "no SHIGURE production modules to audit"
    return false
  let env ← importModules (modules.map fun name => {module := name}) {} (level := .private)
  let mut seen : NameSet := {}
  let mut roots := #[]
  let mut separate := #[]
  for index in [:env.header.modules.size] do
    let name := env.header.modules[index]!.module
    if let some path := sources.find? name then
      seen := seen.insert name
      let data := env.header.moduleData[index]!
      roots := roots ++ data.constNames
      -- Lean can merge synthesized theorems with the same name and different proofs.
      if data.constants.any (fun original =>
          !(env.find? original.name).any (fun combined =>
            ptrAddrOf original == ptrAddrOf combined ||
              (original.type == combined.type && original.value? true == combined.value? true))) then
        separate := separate.push path
  let absent := modules.filter (!seen.contains ·)
  if !absent.isEmpty then
    IO.eprintln s!"missing compiled SHIGURE modules: {absent}"
    return false
  let mut valid := true
  for name in roots do
    if (env.find? name).any (·.isUnsafe) then
      IO.eprintln s!"unsafe declaration {name}"
      valid := false
  for dependency in SHIGURE.kernelAxioms env none roots do
    unless SHIGURE.isStandardAxiom dependency do
      IO.eprintln s!"nonstandard kernel assumption {dependency}"
      valid := false
  if let some outPath := separateOut? then
    let mut bytes := ByteArray.empty
    for path in separate do
      IO.println s!"Deferring original proof environment check for {path}."
      bytes := bytes ++ path.toString.toUTF8
      bytes := bytes.push 0
    IO.FS.writeBinFile outPath bytes
  else
    let exe ← IO.appPath
    let checker := (← IO.getEnv "SHIGURE_CHECKER_SCRIPT").getD ".github/lean_quality/check_shigure_declarations.lean"
    for path in separate do
      IO.println s!"Checking the original proof environment for {path}."
      let childArgs :=
        if isolated || modules.size == 1 then
          #["--run", checker, path.toString]
        else
          #["--run", checker, "--compiled-isolated", path.toString]
      let child ← IO.Process.spawn { cmd := exe.toString, args := childArgs }
      unless (← child.wait) == 0 do
        valid := false
  IO.println s!"Checked {modules.size} compiled modules and {roots.size} declarations."
  return valid

/-- Run from the repository root after the SHIGURE build. Paths optionally select local fixtures. -/
unsafe def main (args : List String) : IO UInt32 := do
  if let "--compiled" :: "--separate-out" :: outPath :: files := args then
    return if ← checkCompiled files (separateOut? := some (System.FilePath.mk outPath)) then 0 else 1
  if let "--compiled" :: files := args then
    return if ← checkCompiled files then 0 else 1
  if let ["--compiled-isolated", file] := args then
    return if ← checkCompiled [file] (isolated := true) then 0 else 1
  if let [file] := args then
    return if ← checkFile file then 0 else 1
  let files ← if args.isEmpty then do
    let files ← (System.FilePath.mk "Formal/SHIGURE").walkDir
    pure ((files.filter (·.extension == some "lean")).push "Formal/SHIGURE.lean")
  else pure (args.toArray.map System.FilePath.mk)
  let exe ← IO.appPath
  let checker := (← IO.getEnv "SHIGURE_CHECKER_SCRIPT").getD ".github/lean_quality/check_shigure_declarations.lean"
  let mut valid := true
  for file in files do
    -- Extension caches can keep imported environments alive. Release them at process exit.
    let child ← IO.Process.spawn {
      cmd := exe.toString
      args := #["--run", checker, file.toString]
    }
    unless (← child.wait) == 0 do
      valid := false
  return if valid then 0 else 1

import Lean

/-!
Kernel axiom allowlist command for audit entrypoints.

`#assert_standard_axioms_only ns` collects the kernel axiom dependencies of
every declaration defined in the current module under namespace `ns`, and
fails elaboration unless all of them are within the standard mathlib axiom
set (`propext`, `Classical.choice`, `Quot.sound`). In particular `sorryAx`,
`Lean.ofReduceBool` (`native_decide`), and any custom `axiom` declaration in
the dependency tree are rejected.

Design notes:

- Only declarations of the current module (`Environment.constants.map₂`) are
  scanned, so imported declarations are never audited by accident.
- Auto-generated auxiliary declarations are skipped via
  `Name.isInternalDetail`; their axiom dependencies are still reachable from
  the parent declaration.
- Matching zero declarations is an error, so a namespace typo cannot pass as
  a vacuous audit.
- Declarations elaborated after the command are not checked. The audited file
  must keep this command as its last non-empty line; CI enforces the tail
  position textually.
- The audit runs in two phases. The success path collects the axioms
  reachable from all targets in a single traversal with a shared visited set
  (per-declaration `collectAxioms` calls would re-walk the shared proof DAG
  once per target). Only when non-standard axioms are reachable does the
  audit fall back to per-declaration collection to attribute offenders.
-/

namespace AAT.Util

open Lean Elab Command

/-- 許容 kernel 公理: mathlib 標準の3つ。 -/
def standardAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

elab "#assert_standard_axioms_only " ns:ident : command => do
  let env ← getEnv
  let prefixNs := ns.getId
  let mut targets : Array Name := #[]
  for (name, _) in env.constants.map₂ do
    if prefixNs.isPrefixOf name && !name.isInternalDetail then
      targets := targets.push name
  if targets.isEmpty then
    throwError "#assert_standard_axioms_only: no declarations found under {prefixNs}"
  let sorted := targets.qsort fun a b => a.toString < b.toString
  let (_, shared) := ((sorted.forM fun name => CollectAxioms.collect name).run env).run {}
  let mut offenders : Nat := 0
  unless shared.axioms.all standardAxioms.contains do
    for name in sorted do
      let axioms ← liftCoreM <| collectAxioms name
      let bad := axioms.toList.filter fun a => !standardAxioms.contains a
      unless bad.isEmpty do
        offenders := offenders + 1
        logError m!"{name} depends on non-standard axioms: {bad}"
  if offenders > 0 then
    throwError "#assert_standard_axioms_only: {offenders} offending declaration(s)"
  logInfo m!"axiom audit: {sorted.size} declarations under {prefixNs}, standard axioms only"

end AAT.Util

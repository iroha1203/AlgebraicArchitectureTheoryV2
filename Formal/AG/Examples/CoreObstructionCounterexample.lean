import Formal.AG.Atom.AATCore

/-!
# Counterexample to unconditional obstruction realization

An all-holding law cannot supply the law failure required by an actual
`ObstructionCircuit`. This witnesses why obstruction data is separated from
the unconditional AAT core.
-/

namespace AAT.AG.CoreObstructionCounterexample

universe u

/-- A law that holds on every architecture object. -/
def allHoldingLaw (U : AtomCarrier.{u}) : Law U where
  holds := fun _ => True

/--
An all-holding law admits no obstruction circuit. This separates the
unconditional AAT core from the additional data of an obstructed core.
-/
theorem allHoldingLaw_has_no_obstructionCircuit {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) :
    ¬ Nonempty (ObstructionCircuit (allHoldingLaw U) A) := by
  rintro ⟨circuit⟩
  exact circuit.law_failure trivial

end AAT.AG.CoreObstructionCounterexample

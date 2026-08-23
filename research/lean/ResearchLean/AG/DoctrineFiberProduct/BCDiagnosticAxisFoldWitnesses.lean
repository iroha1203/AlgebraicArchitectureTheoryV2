import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFold
import ResearchLean.AG.TransportCoherence.FiniteWitnesses

/-!
# Finite witness for the diagnostic axis fold

The three-axis transport-coherence fixture supplies an object-fixing diagnostic
automorphism that moves axis `0`.  The generic constructor therefore produces
a concrete noninvertible package endomorphism without accepting one from the
caller.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation TransportCoherence

/-- The adjacent transposition has the internal data required by the fold. -/
noncomputable def finiteSwap01AxisFoldWitness :
    PackageFiberAut.AxisFoldWitness finiteWitnessSwap01 where
  source := (0 : Fin 3)
  axisDecidableEq := Classical.decEq _
  moved := by
    change (Equiv.swap (0 : Fin 3) 1) 0 ≠ 0
    decide
  objectMap_eq := rfl

/-- The finite diagnostic fold is visibly noninjective on its three axes. -/
theorem finiteSwap01AxisFold_not_injective :
    ¬ Function.Injective finiteSwap01AxisFoldWitness.axisMap :=
  finiteSwap01AxisFoldWitness.not_injective_axisMap

/-- Hence the finite diagnostic fold cannot be an automorphism twist. -/
theorem finiteSwap01AxisFold_not_isIso :
    ¬ IsIso
      (show finiteWitnessTargetPackage ⟶ finiteWitnessTargetPackage from
        finiteSwap01AxisFoldWitness.total) :=
  finiteSwap01AxisFoldWitness.total_not_isIso

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

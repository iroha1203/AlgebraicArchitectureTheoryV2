import ResearchLean.AG.DoctrineFiberProduct.BCAxisFoldSwapSymmetryNoGo

/-!
# Comparator-induction obstruction for the fixed authored swap

An operation induced only by the authored adjacent transposition must commute
with that transposition and must keep every axis inside the orbit supplied by
it.  These two equations are the finite naturality and no-new-axis laws for a
comparator-only axis operation.  On the fixed three-axis lax witness they force
injectivity, so they cannot coexist with the noninjective axis collapse used by
the direct or pairwise diagnostic fold route.

This is a fixed-target obstruction for that route class.  It does not define a
public K2 producer and does not classify constructions using additional input
structure beyond the authored comparator orbit.
-/

namespace AAT.AG.DoctrineFiberProduct

open AtomFoundation

/-- Naturality and no-new-axis laws for an operation induced by the fixed swap. -/
def FiniteAxisFoldComparatorInduced (axisMap : Fin 3 → Fin 3) : Prop :=
  FiniteAxisFoldSwapEquivariant axisMap ∧
    FiniteAxisFoldSwapOrbitLocal axisMap

/-- The non-twist fold route requires a genuine collapse of signature axes. -/
def FiniteAxisFoldCollapse (axisMap : Fin 3 → Fin 3) : Prop :=
  ¬ Function.Injective axisMap

/-- Every comparator-induced operation on the fixed authored swap is injective. -/
theorem finiteAxisFold_comparatorInduced_injective
    (axisMap : Fin 3 → Fin 3)
    (induced : FiniteAxisFoldComparatorInduced axisMap) :
    Function.Injective axisMap :=
  finiteAxisFold_swapEquivariant_orbitLocal_injective axisMap
    induced.1 induced.2

/-- Comparator induction and a non-twist axis collapse are incompatible. -/
theorem finiteAxisFold_not_comparatorInduced_and_collapse
    (axisMap : Fin 3 → Fin 3) :
    ¬ (FiniteAxisFoldComparatorInduced axisMap ∧
      FiniteAxisFoldCollapse axisMap) := by
  rintro ⟨induced, collapse⟩
  exact collapse (finiteAxisFold_comparatorInduced_injective axisMap induced)

/-- The actual choice-based generated fold has a noninjective axis action. -/
theorem finiteAxisFoldGeneratedAxisMap_collapse :
    FiniteAxisFoldCollapse finiteAxisFoldGeneratedAxisMap := by
  rw [finiteAxisFoldGeneratedAxisMap_eq_chosen]
  exact (Classical.choice finiteAxisFoldSwap_available).not_injective_axisMap

/-- The actual generated fold therefore fails comparator induction. -/
theorem finiteAxisFoldGeneratedAxisMap_not_comparatorInduced :
    ¬ FiniteAxisFoldComparatorInduced finiteAxisFoldGeneratedAxisMap := by
  intro induced
  exact finiteAxisFoldGeneratedAxisMap_collapse
    (finiteAxisFold_comparatorInduced_injective
      finiteAxisFoldGeneratedAxisMap induced)

/-- An oriented fold witness together with comparator-induction laws. -/
structure FiniteAxisFoldInducedFold where
  /-- The one-axis diagnostic collapse supplied by the attempted route. -/
  witness : PackageFiberAut.AxisFoldWitness finiteAxisFoldSwap
  /-- The resulting axis operation is induced naturally and orbit-locally. -/
  induced : FiniteAxisFoldComparatorInduced witness.axisMap

/-- No oriented fold witness for the fixed swap can satisfy induction laws. -/
theorem finiteAxisFoldInducedFold_isEmpty : IsEmpty FiniteAxisFoldInducedFold := by
  constructor
  intro candidate
  exact candidate.witness.not_injective_axisMap
    (finiteAxisFold_comparatorInduced_injective
      candidate.witness.axisMap candidate.induced)

/-- Equivalent existential form used by the G-110 blocker ledger. -/
theorem finiteAxisFold_no_comparatorInduced_fold :
    ¬ ∃ witness : PackageFiberAut.AxisFoldWitness finiteAxisFoldSwap,
      FiniteAxisFoldComparatorInduced witness.axisMap := by
  rintro ⟨witness, induced⟩
  exact witness.not_injective_axisMap
    (finiteAxisFold_comparatorInduced_injective witness.axisMap induced)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

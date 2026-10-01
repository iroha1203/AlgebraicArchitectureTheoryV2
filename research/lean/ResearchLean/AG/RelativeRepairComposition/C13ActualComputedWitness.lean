import ResearchLean.AG.RelativeRepairComposition.C13ActualRangeRegression
import ResearchLean.AG.RelativeRepairComposition.C13FiniteDualRegression

/-! # Finite witness construction applied to the independent nonzero actual tower -/
namespace AAT.AG.RelativeRepairComposition.C13ActualComputedWitness
open TransportCoherence AbelianLiftingObstruction C13RangeInput C13ActualRangeRegression
/-- Decide equality on the original single face index. -/
instance originalFaceEquality : DecidableEq geometry.TwoCell :=
  inferInstanceAs (DecidableEq Unit)

/-- The complete original named edge list retains both separately authored loops. -/
def edgeValues : FiniteElimination.Enumeration (EdgeName (K := geometry)) where
  values := [⟨(),(),false⟩,⟨(),(),true⟩]
  complete e := by
    rcases e with ⟨i,j,e⟩
    cases i; cases j; cases e <;> simp

/-- The original single authored face is the entire face input list. -/
def faceValues : FiniteElimination.Enumeration geometry.TwoCell :=
  ⟨[()],by intro f; cases f; simp⟩

/-- The failed actual empty range produces a quotient dual from its computed full-coordinate row. -/
noncomputable def failedDual :=
  OriginalFiniteRepair.computedDual (k := k) tower fixed candidates outside linear fixed_coherent
    basis C13FiniteDualRegression.fieldValues faceValues ∅ empty_no_repair

/-- The finite constructed actual dual is nonzero on the same actual original obstruction. -/
theorem failed_dual_nonzero :
    failedDual.1 (OriginalRangeClassification.obstruction (k := k)
      tower fixed candidates linear fixed_coherent) ≠ 0 := failedDual.2.1

/-- Allowing the same original candidate produces a full actual repair from the finite original-edge search. -/
noncomputable def successfulRepair :=
  OriginalFiniteRepair.computedRepair (k := k) tower fixed candidates linear fixed_coherent
    basis C13FiniteDualRegression.fieldValues edgeValues Set.univ ⟨allRepair⟩

/-- The finite restoration keeps the actual original fixed morphism. -/
theorem successful_fixed :
    (selectedUpper geometry (GroupExtension.projection projection) (GroupExtension.terminal PUnit.{1})
      tower.original successfulRepair.1.choice).edgeLift (i := ()) (j := ()) false =
        tower.toTower.upper.edgeLift (i := ()) (j := ()) false :=
  successfulRepair.2 ⟨(),(),false⟩ (Or.inl rfl)

end AAT.AG.RelativeRepairComposition.C13ActualComputedWitness
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C13ActualComputedWitness
